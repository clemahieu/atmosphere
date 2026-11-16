// SPDX-License-Identifier: MIT

//! Shared-frame ring cold-cache RTT, pipelined send/poll/throughput, multi-producer `afanin` poll
//! scaling, and zero-copy vs `memcpy` bulk handoff benchmarks mapped from Barrelfish `usr/bench`
//! (`ump_bench/{latency_cache,send,receive,throughput}.c`, `channel_cost/channel_cost.c`,
//! `bulk_bench/bulkbench.c`; MIT) onto `aring` and `afanin` (`design/synthetic-benchmark-suite/`).

use alloc::vec::Vec;
use core::cell::UnsafeCell;
use core::hint::{black_box, spin_loop};
use core::mem::size_of;
use core::sync::atomic::{fence, AtomicU32, AtomicU64, Ordering};

use abench::runner::Registry;
use acall::capability::place;
use acall::memory::retype;
use acall::step::Caller;
use afanin::{scan, Heads, Scan};
use aring::{Consumer, Producer};
use asys::operation;
use vstd::prelude::Tracked;

use crate::core_bench::{core_count, stopped};
use crate::mmu_bench::{
    alloc_and_link_table, find_gigabyte_untyped, retype_large_frame_until_done,
};
use crate::{
    first_slot, inspect, set_frame_word, untyped_of_pages, window_clear, ARGUMENT_WORDS,
    EAGER_WINDOW, HEAP_WINDOW, LARGE_FRAME_BYTES, LEAF_BYTES, ROOT_ENTRIES, TABLE_PAGE_BYTES,
};

/// Virtual window mapping the two 2 MiB benchmark frames (`16..18` belong to `mmu_bench`, `19`
/// belongs to `ring_bench`).
const BENCH_UMP_WINDOW: u64 = 20 << 39;

/// Physical offset into the 1 GiB untyped (`mmu_bench` uses `64..102 MiB`, `cap_bench` uses
/// `128..185 MiB`, `ring_bench` uses `448..452 MiB`, and `flush_cost` uses top-512M).
const RING_POOL_OFFSET: u64 = 256 * 1024 * 1024;

/// First root capability table entry probed for `ump_bench`'s single table leaf (clear of
/// `mmu_bench`, `cap_bench`, and `ring_bench` leaves starting at `32`).
const RING_CAP_ENTRY_START: u64 = 256;

const PAGE_BYTES: u64 = 4096;
const PINGPONG_CAP: u32 = 64;
const PIPELINE_DEPTH: u32 = 16;
const FANIN_MAX_PRODUCERS: usize = 64;
const FANIN_RING_CAP: u32 = 4;
const FANIN_COUNTS: [usize; 4] = [1, 8, 32, 64];
const BULK_RING_CAP: u32 = 16;
const BULK_MAX_BYTES: usize = 1024 * 1024;
const L1D_EVICT_BYTES: usize = 128 * 1024;
const ARENA_OFFSET_BYTES: usize = BULK_MAX_BYTES + L1D_EVICT_BYTES;

const ECHO_MASK: u64 = 0xa5a5_5a5a_f00d_cafe;
const BULK_TAIL_MASK: u64 = 0x55aa_1122_3344_6677;
const BOGUS_STALLED_HEAD: u32 = 0xdead_beef;
const RING_POLL_MAX: u64 = 1 << 25;
const WORKER_ACK_POLL_MAX: u64 = 1 << 24;

const CMD_IDLE: u64 = 0;
const CMD_ECHO_PINGPONG: u64 = 1;
const CMD_FANIN_PRODUCER: u64 = 2;
const CMD_BULK_ZEROCOPY: u64 = 3;
const CMD_BULK_MEMCPY: u64 = 4;

/// 64-byte cache-line-aligned message slot matching Barrelfish UMP cacheline framing.
#[repr(C, align(64))]
#[derive(Clone, Copy)]
struct Msg64 {
    words: [u64; 8],
}

impl Msg64 {
    const fn new(seq: u64) -> Self {
        Self {
            words: [seq, seq ^ 1, seq ^ 2, seq ^ 3, seq ^ 4, seq ^ 5, seq ^ 6, seq ^ 7],
        }
    }
}

const _: () = assert!(size_of::<Msg64>() == 64);

/// 64-byte cache-line-aligned bulk transfer descriptor (`Frame` offset, length, sequence tag).
#[repr(C, align(64))]
#[derive(Clone, Copy)]
struct BulkDesc {
    offset: u64,
    len: u64,
    tag: u64,
    _pad: [u64; 5],
}

const _: () = assert!(size_of::<BulkDesc>() == 64);

#[repr(C, align(128))]
struct Line32(AtomicU32);

#[repr(C, align(128))]
struct Line64(AtomicU64);

/// Shared rings and Core 1 worker control block mapped in Frame 0 past `BULK_MAX_BYTES + L1D_EVICT_BYTES`.
#[repr(C, align(128))]
struct RingArena {
    cmd: Line64,
    gen: Line64,
    ack: Line64,
    err: Line64,
    fanin_active: Line64,
    bulk_bytes: Line64,
    ping_pong_tx_head: Line32,
    ping_pong_tx_tail: Line32,
    ping_pong_rx_head: Line32,
    ping_pong_rx_tail: Line32,
    ping_pong_tx_slots: UnsafeCell<[Msg64; PINGPONG_CAP as usize]>,
    ping_pong_rx_slots: UnsafeCell<[Msg64; PINGPONG_CAP as usize]>,
    fanin_heads: [Line32; FANIN_MAX_PRODUCERS],
    fanin_tails: [Line32; FANIN_MAX_PRODUCERS],
    fanin_slots: UnsafeCell<[[Msg64; FANIN_RING_CAP as usize]; FANIN_MAX_PRODUCERS]>,
    bulk_tx_head: Line32,
    bulk_tx_tail: Line32,
    bulk_rx_head: Line32,
    bulk_rx_tail: Line32,
    bulk_tx_slots: UnsafeCell<[BulkDesc; BULK_RING_CAP as usize]>,
    bulk_rx_slots: UnsafeCell<[BulkDesc; BULK_RING_CAP as usize]>,
}

const _: () = assert!(ARENA_OFFSET_BYTES + size_of::<RingArena>() <= LARGE_FRAME_BYTES as usize);

#[repr(C, align(16))]
struct WorkerStack(UnsafeCell<[u8; 16384]>);

// Safety: `WORKER_STACK` backs only the single Core 1 worker thread spawned in `threads_held`.
unsafe impl Sync for WorkerStack {}

static WORKER_STACK: WorkerStack = WorkerStack(UnsafeCell::new([0; 16384]));

static RING_CAP_ENTRY: AtomicU64 = AtomicU64::new(0);
static WORKER_SLOT: AtomicU64 = AtomicU64::new(0);
static RING_POOL_PHYS: AtomicU64 = AtomicU64::new(0);
static RING_ARENA_ADDR: AtomicU64 = AtomicU64::new(0);
static WORKER_GEN_SHADOW: AtomicU64 = AtomicU64::new(0);

// 96 KiB straight-line instruction-cache eviction sled exceeding 32-64 KiB L1I on both targets.
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".balign 64",
    ".global dom0_icache_evict",
    "dom0_icache_evict:",
    ".rept 1536",
    "jmp 1f",
    ".balign 64",
    "1:",
    ".endr",
    "ret",
);

#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(
    ".balign 64",
    ".global dom0_icache_evict",
    "dom0_icache_evict:",
    ".rept 1536",
    "b 1f",
    ".balign 64",
    "1:",
    ".endr",
    "ret",
);

#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".balign 16",
    ".global dom0_ump_worker_trampoline",
    "dom0_ump_worker_trampoline:",
    "and rsp, -16",
    "call dom0_ump_worker_main",
    "2: pause",
    "jmp 2b",
);

#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(
    ".balign 16",
    ".global dom0_ump_worker_trampoline",
    "dom0_ump_worker_trampoline:",
    "bl dom0_ump_worker_main",
    "2: wfe",
    "b 2b",
);

unsafe extern "C" {
    fn dom0_icache_evict();
    fn dom0_ump_worker_trampoline();
}

struct ArenaHeads<'a>(&'a [Line32; FANIN_MAX_PRODUCERS]);

impl Heads for ArenaHeads<'_> {
    fn load(&self, ring: usize) -> u32 {
        self.0[ring].0.load(Ordering::Acquire)
    }
}

fn make_producer(cap: u32) -> Option<Producer> {
    if cap == 0 || (0x1_0000_0000u64 % (cap as u64)) != 0 {
        return None;
    }
    Some(Producer::new(cap))
}

fn make_consumer(cap: u32) -> Option<Consumer> {
    if cap == 0 || (0x1_0000_0000u64 % (cap as u64)) != 0 {
        return None;
    }
    Some(Consumer::new(cap))
}

/// Publishes one element onto `slots_ptr[..cap]` using `aring::Producer` with volatile slot writes
/// so concurrent cross-core access avoids aliasing `&mut [T]` / `&[T]` references.
fn ring_try_send<T>(
    prod: &mut Producer,
    slots_ptr: *mut T,
    cap: usize,
    head_word: &Line32,
    tail_word: &Line32,
    val: T,
) -> bool {
    if cap == 0 || !cap.is_power_of_two() {
        return false;
    }
    let tail = tail_word.0.load(Ordering::Acquire);
    let _ = prod.observe(tail);
    if prod.free() == 0 {
        return false;
    }
    let s = prod.slot(0);
    if s >= cap {
        return false;
    }
    // Safety: `aring::Producer::slot(0)` ensures `s < cap` and `prod` uniquely owns slot `s`.
    unsafe { slots_ptr.add(s).write_volatile(val) };
    let new_head = prod.publish(1);
    head_word.0.store(new_head, Ordering::Release);
    true
}

fn ring_send_wait<T: Copy>(
    prod: &mut Producer,
    slots_ptr: *mut T,
    cap: usize,
    head_word: &Line32,
    tail_word: &Line32,
    val: T,
) -> bool {
    for _ in 0..RING_POLL_MAX {
        if ring_try_send(prod, slots_ptr, cap, head_word, tail_word, val) {
            return true;
        }
        spin_loop();
    }
    false
}

/// Consumes one already-observed slot (`cons.available() > 0`) after `afanin::scan`.
fn ring_consume_ready<T: Copy>(
    cons: &mut Consumer,
    slots_ptr: *const T,
    cap: usize,
    tail_word: &Line32,
) -> Option<T> {
    if cap == 0 || !cap.is_power_of_two() {
        return None;
    }
    if cons.available() == 0 {
        return None;
    }
    let s = cons.slot(0);
    if s >= cap {
        return None;
    }
    // Safety: `aring::Consumer::slot(0)` ensures `s < cap` and `cons` uniquely owns slot `s`.
    let val = unsafe { slots_ptr.add(s).read_volatile() };
    let new_tail = cons.consume(1);
    tail_word.0.store(new_tail, Ordering::Release);
    Some(val)
}

fn ring_try_recv<T: Copy>(
    cons: &mut Consumer,
    slots_ptr: *const T,
    cap: usize,
    head_word: &Line32,
    tail_word: &Line32,
) -> Option<T> {
    if cap == 0 || !cap.is_power_of_two() {
        return None;
    }
    let head = head_word.0.load(Ordering::Acquire);
    let _ = cons.observe(head);
    if cons.available() == 0 {
        return None;
    }
    ring_consume_ready(cons, slots_ptr, cap, tail_word)
}

fn ring_recv_wait<T: Copy>(
    cons: &mut Consumer,
    slots_ptr: *const T,
    cap: usize,
    head_word: &Line32,
    tail_word: &Line32,
) -> Option<T> {
    for _ in 0..RING_POLL_MAX {
        if let Some(val) = ring_try_recv(cons, slots_ptr, cap, head_word, tail_word) {
            return Some(val);
        }
        spin_loop();
    }
    None
}

fn fanin_scan_once(
    consumers: &mut [Consumer],
    heads: &ArenaHeads<'_>,
    start: usize,
) -> Option<usize> {
    if start >= consumers.len() {
        return None;
    }
    match scan(consumers, heads, start) {
        Scan::Ready(idx, _) => Some(idx),
        Scan::Idle(_) => None,
    }
}

fn arena_ref() -> &'static RingArena {
    let addr = RING_ARENA_ADDR.load(Ordering::Acquire);
    assert!(addr != 0, "ump_bench arena initialized");
    // Safety: `addr` points to the mapped, aligned `RingArena` in Frame 0.
    unsafe { &*(addr as *const RingArena) }
}

fn shared_bulk_ptr() -> *mut u8 {
    BENCH_UMP_WINDOW as *mut u8
}

fn evict_l1d_ptr() -> *const u8 {
    (BENCH_UMP_WINDOW + BULK_MAX_BYTES as u64) as *const u8
}

fn dst_bulk_ptr() -> *mut u8 {
    (BENCH_UMP_WINDOW + LARGE_FRAME_BYTES) as *mut u8
}

#[cfg(target_arch = "x86_64")]
#[inline]
fn clflush_range(start: usize, bytes: usize) {
    if (core::arch::x86_64::__cpuid(1).edx & (1 << 19)) == 0 {
        return;
    }
    let mut addr = start & !63usize;
    let end = start.saturating_add(bytes);
    while addr < end {
        // Safety: caller guarantees `start..start+bytes` is mapped and readable.
        unsafe {
            core::arch::asm!(
                "clflush [{addr}]",
                addr = in(reg) addr,
                options(nostack, preserves_flags)
            );
        }
        addr += 64;
    }
}

#[inline(never)]
fn flush_cold_caches(arena: &RingArena, hop_code_addr: usize) {
    let evict = evict_l1d_ptr();
    let mut sum = 0u64;
    let mut off = 0usize;
    while off < L1D_EVICT_BYTES {
        // Safety: `evict..evict+L1D_EVICT_BYTES` is mapped in Frame 0.
        sum = sum.wrapping_add(unsafe { evict.add(off).cast::<u64>().read_volatile() });
        off += 64;
    }
    black_box(sum);
    // Safety: `dom0_icache_evict` is a leaf sled in `.text` preserving callee-saved registers.
    unsafe { dom0_icache_evict() };

    #[cfg(target_arch = "x86_64")]
    {
        fence(Ordering::SeqCst);
        clflush_range(
            arena.ping_pong_tx_slots.get() as usize,
            size_of::<[Msg64; PINGPONG_CAP as usize]>(),
        );
        clflush_range(
            arena.ping_pong_rx_slots.get() as usize,
            size_of::<[Msg64; PINGPONG_CAP as usize]>(),
        );
        clflush_range(&arena.ping_pong_tx_head as *const Line32 as usize, 64);
        clflush_range(&arena.ping_pong_tx_tail as *const Line32 as usize, 64);
        clflush_range(&arena.ping_pong_rx_head as *const Line32 as usize, 64);
        clflush_range(&arena.ping_pong_rx_tail as *const Line32 as usize, 64);
        clflush_range(hop_code_addr, 64);
        fence(Ordering::SeqCst);
    }
    #[cfg(target_arch = "aarch64")]
    {
        let _ = (arena, hop_code_addr);
        // Safety: data/instruction barriers ensure eviction completes before the timed RTT.
        unsafe {
            core::arch::asm!("dsb sy", "isb", options(nostack, preserves_flags));
        }
    }
}

#[inline(never)]
fn cold_ping_pong_hop(
    tx: &mut Producer,
    rx: &mut Consumer,
    arena: &RingArena,
    seq: u64,
) -> bool {
    let tx_slots = arena.ping_pong_tx_slots.get() as *mut Msg64;
    let rx_slots = arena.ping_pong_rx_slots.get() as *const Msg64;
    if !ring_send_wait(
        tx,
        tx_slots,
        PINGPONG_CAP as usize,
        &arena.ping_pong_tx_head,
        &arena.ping_pong_tx_tail,
        Msg64::new(seq),
    ) {
        return false;
    }
    let Some(reply) = ring_recv_wait(
        rx,
        rx_slots,
        PINGPONG_CAP as usize,
        &arena.ping_pong_rx_head,
        &arena.ping_pong_rx_tail,
    ) else {
        return false;
    };
    black_box(reply.words[0]) == (seq ^ ECHO_MASK)
}

#[no_mangle]
extern "C" fn dom0_ump_worker_main() {
    let arena = arena_ref();
    let mut seen_gen = 0u64;
    loop {
        while arena.gen.0.load(Ordering::Acquire) == seen_gen {
            spin_loop();
        }
        seen_gen = arena.gen.0.load(Ordering::Acquire);
        let cmd = arena.cmd.0.load(Ordering::Acquire);
        match cmd {
            CMD_ECHO_PINGPONG => {
                let (Some(mut rx), Some(mut tx)) =
                    (make_consumer(PINGPONG_CAP), make_producer(PINGPONG_CAP))
                else {
                    arena.err.0.store(1, Ordering::Release);
                    arena.ack.0.store(seen_gen, Ordering::Release);
                    continue;
                };
                let rx_slots = arena.ping_pong_tx_slots.get() as *const Msg64;
                let tx_slots = arena.ping_pong_rx_slots.get() as *mut Msg64;
                arena.ack.0.store(seen_gen, Ordering::Release);
                while arena.gen.0.load(Ordering::Acquire) == seen_gen {
                    if let Some(msg) = ring_try_recv(
                        &mut rx,
                        rx_slots,
                        PINGPONG_CAP as usize,
                        &arena.ping_pong_tx_head,
                        &arena.ping_pong_tx_tail,
                    ) {
                        let reply = Msg64::new(msg.words[0] ^ ECHO_MASK);
                        if !ring_send_wait(
                            &mut tx,
                            tx_slots,
                            PINGPONG_CAP as usize,
                            &arena.ping_pong_rx_head,
                            &arena.ping_pong_rx_tail,
                            reply,
                        ) {
                            arena.err.0.store(2, Ordering::Release);
                            break;
                        }
                    } else {
                        spin_loop();
                    }
                }
            }
            CMD_FANIN_PRODUCER => {
                let active = arena.fanin_active.0.load(Ordering::Acquire) as usize;
                let (Some(mut trig_rx), Some(mut fan_tx)) =
                    (make_consumer(PINGPONG_CAP), make_producer(FANIN_RING_CAP))
                else {
                    arena.err.0.store(3, Ordering::Release);
                    arena.ack.0.store(seen_gen, Ordering::Release);
                    continue;
                };
                if active >= FANIN_MAX_PRODUCERS {
                    arena.err.0.store(4, Ordering::Release);
                    arena.ack.0.store(seen_gen, Ordering::Release);
                    continue;
                }
                let trig_slots = arena.ping_pong_tx_slots.get() as *const Msg64;
                let fan_slots = unsafe { (*arena.fanin_slots.get())[active].as_mut_ptr() };
                arena.ack.0.store(seen_gen, Ordering::Release);
                while arena.gen.0.load(Ordering::Acquire) == seen_gen {
                    if let Some(msg) = ring_try_recv(
                        &mut trig_rx,
                        trig_slots,
                        PINGPONG_CAP as usize,
                        &arena.ping_pong_tx_head,
                        &arena.ping_pong_tx_tail,
                    ) {
                        if !ring_send_wait(
                            &mut fan_tx,
                            fan_slots,
                            FANIN_RING_CAP as usize,
                            &arena.fanin_heads[active],
                            &arena.fanin_tails[active],
                            msg,
                        ) {
                            arena.err.0.store(5, Ordering::Release);
                            break;
                        }
                    } else {
                        spin_loop();
                    }
                }
            }
            CMD_BULK_ZEROCOPY | CMD_BULK_MEMCPY => {
                let do_copy = cmd == CMD_BULK_MEMCPY;
                let (Some(mut rx), Some(mut tx)) =
                    (make_consumer(BULK_RING_CAP), make_producer(BULK_RING_CAP))
                else {
                    arena.err.0.store(6, Ordering::Release);
                    arena.ack.0.store(seen_gen, Ordering::Release);
                    continue;
                };
                let rx_slots = arena.bulk_tx_slots.get() as *const BulkDesc;
                let tx_slots = arena.bulk_rx_slots.get() as *mut BulkDesc;
                let src_base = shared_bulk_ptr() as *const u8;
                let dst_base = dst_bulk_ptr();
                arena.ack.0.store(seen_gen, Ordering::Release);
                while arena.gen.0.load(Ordering::Acquire) == seen_gen {
                    if let Some(desc) = ring_try_recv(
                        &mut rx,
                        rx_slots,
                        BULK_RING_CAP as usize,
                        &arena.bulk_tx_head,
                        &arena.bulk_tx_tail,
                    ) {
                        let len = desc.len as usize;
                        let off = desc.offset as usize;
                        if len < 16 || off.saturating_add(len) > BULK_MAX_BYTES {
                            arena.err.0.store(7, Ordering::Release);
                            break;
                        }
                        // Safety: `off + len <= BULK_MAX_BYTES`, inside mapped Frame 0 and Frame 1.
                        let (first, last) = unsafe {
                            let src = src_base.add(off);
                            if do_copy {
                                let dst = dst_base.add(off);
                                core::ptr::copy_nonoverlapping(src, dst, len);
                                (
                                    dst.cast::<u64>().read_volatile(),
                                    dst.add(len - 8).cast::<u64>().read_volatile(),
                                )
                            } else {
                                (
                                    src.cast::<u64>().read_volatile(),
                                    src.add(len - 8).cast::<u64>().read_volatile(),
                                )
                            }
                        };
                        if first != desc.tag || last != (desc.tag ^ BULK_TAIL_MASK) {
                            arena.err.0.store(8, Ordering::Release);
                            break;
                        }
                        let reply = BulkDesc {
                            offset: desc.offset,
                            len: desc.len,
                            tag: desc.tag ^ ECHO_MASK,
                            _pad: [0; 5],
                        };
                        if !ring_send_wait(
                            &mut tx,
                            tx_slots,
                            BULK_RING_CAP as usize,
                            &arena.bulk_rx_head,
                            &arena.bulk_rx_tail,
                            reply,
                        ) {
                            arena.err.0.store(9, Ordering::Release);
                            break;
                        }
                    } else {
                        spin_loop();
                    }
                }
            }
            _ => {
                arena.ack.0.store(seen_gen, Ordering::Release);
            }
        }
    }
}

fn worker_set_mode(arena: &RingArena, cmd: u64) -> bool {
    let gen = WORKER_GEN_SHADOW.fetch_add(1, Ordering::AcqRel) + 1;
    arena.cmd.0.store(cmd, Ordering::Release);
    arena.gen.0.store(gen, Ordering::Release);
    for _ in 0..WORKER_ACK_POLL_MAX {
        if arena.ack.0.load(Ordering::Acquire) == gen {
            return arena.err.0.load(Ordering::Acquire) == 0;
        }
        spin_loop();
    }
    false
}

fn reset_arena_rings(arena: &RingArena) {
    arena.err.0.store(0, Ordering::Release);
    arena.ping_pong_tx_head.0.store(0, Ordering::Release);
    arena.ping_pong_tx_tail.0.store(0, Ordering::Release);
    arena.ping_pong_rx_head.0.store(0, Ordering::Release);
    arena.ping_pong_rx_tail.0.store(0, Ordering::Release);
    arena.bulk_tx_head.0.store(0, Ordering::Release);
    arena.bulk_tx_tail.0.store(0, Ordering::Release);
    arena.bulk_rx_head.0.store(0, Ordering::Release);
    arena.bulk_rx_tail.0.store(0, Ordering::Release);
    for i in 0..FANIN_MAX_PRODUCERS {
        arena.fanin_heads[i].0.store(0, Ordering::Release);
        arena.fanin_tails[i].0.store(0, Ordering::Release);
    }
    fence(Ordering::SeqCst);
}

fn start_worker_mode(arena: &RingArena, cmd: u64) -> bool {
    let worker = WORKER_SLOT.load(Ordering::Acquire);
    if worker == 0 {
        return false;
    }
    reset_arena_rings(arena);
    // `dom0_ump_worker_trampoline` runs dom0 code over mapped frames and changes no address space.
    if operation::status(unsafe { operation::invoke(operation::START, worker, [0; 5]) })
        != operation::STATUS_OK
    {
        return false;
    }
    if !worker_set_mode(arena, cmd) {
        let _ = stopped(worker);
        return false;
    }
    true
}

fn stop_worker(arena: &RingArena) -> bool {
    let ok_idle = worker_set_mode(arena, CMD_IDLE);
    let worker = WORKER_SLOT.load(Ordering::Acquire);
    let ok_stop = worker != 0 && stopped(worker);
    ok_idle && ok_stop && arena.err.0.load(Ordering::Acquire) == 0
}

/// Retypes the capability table leaf for `ump_bench` and, when 2+ cores are present, creates and
/// places the Core 1 worker thread while `caller` is still available (before `heap_source` consumes it).
pub(crate) fn threads_held(caller: &mut Tracked<Caller>, empty: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let region = block.base + RING_POOL_OFFSET;
    let leaf_phys = region + 2 * LARGE_FRAME_BYTES;
    let mut cap_entry = None;
    for entry in RING_CAP_ENTRY_START..ROOT_ENTRIES {
        if matches!(inspect(caller, first_slot(entry)), Err(operation::STATUS_REFUSED))
            && retype(caller, untyped, operation::RETYPE_LEAF, leaf_phys, entry, 0).status
                == operation::STATUS_OK
        {
            cap_entry = Some(entry);
            break;
        }
    }
    let Some(entry) = cap_entry else {
        return false;
    };
    RING_CAP_ENTRY.store(entry, Ordering::Release);
    RING_POOL_PHYS.store(region, Ordering::Release);

    if core_count() < 2 {
        return true;
    }

    let worker_slot = first_slot(entry);
    let worker_phys = leaf_phys + LEAF_BYTES;
    let stack_top = (WORKER_STACK.0.get() as u64) + 16384;
    if retype(
        caller,
        untyped,
        operation::RETYPE_THREAD,
        worker_phys,
        worker_slot,
        operation::ROOT_PROCESS_SLOT,
    )
    .status
        != operation::STATUS_OK
        || set_frame_word(
            caller,
            worker_slot,
            operation::PC_WORD,
            dom0_ump_worker_trampoline as *const () as u64,
        ) != operation::STATUS_OK
        || set_frame_word(caller, worker_slot, operation::SP_WORD, stack_top) != operation::STATUS_OK
        || set_frame_word(caller, worker_slot, ARGUMENT_WORDS[0], 0) != operation::STATUS_OK
        || place(caller, worker_slot, operation::ROOT_CORE_SLOT + 1, 0).status
            != operation::STATUS_OK
    {
        return false;
    }
    WORKER_SLOT.store(worker_slot, Ordering::Release);
    true
}

fn init_ring_frames() -> Option<&'static RingArena> {
    if !window_clear(
        BENCH_UMP_WINDOW,
        &[EAGER_WINDOW, HEAP_WINDOW, 16 << 39, 17 << 39, 18 << 39, 19 << 39],
    ) {
        return None;
    }
    let entry = RING_CAP_ENTRY.load(Ordering::Acquire);
    let region = RING_POOL_PHYS.load(Ordering::Acquire);
    if entry == 0 || region == 0 {
        return None;
    }
    let (untyped_slot, _) = find_gigabyte_untyped()?;
    // `retype_table_page` requires 32 KiB (`TABLE_PAGE_BYTES`, order 3) alignment, so place table
    // pages one `TABLE_PAGE_BYTES` past `leaf_phys` (clearing `leaf` + `worker` in `[+0..+16 KiB)`).
    let mut next_table = region + 2 * LARGE_FRAME_BYTES + TABLE_PAGE_BYTES;
    if !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_UMP_WINDOW, 3)
        || !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_UMP_WINDOW, 2)
    {
        return None;
    }
    let frame0_slot = first_slot(entry) + 1;
    let frame1_slot = first_slot(entry) + 2;
    if !retype_large_frame_until_done(untyped_slot, region, frame0_slot)
        || operation::map(
            operation::ROOT_PROCESS_SLOT,
            BENCH_UMP_WINDOW,
            2,
            frame0_slot,
            0,
        ) != operation::STATUS_OK
        || !retype_large_frame_until_done(untyped_slot, region + LARGE_FRAME_BYTES, frame1_slot)
        || operation::map(
            operation::ROOT_PROCESS_SLOT,
            BENCH_UMP_WINDOW + LARGE_FRAME_BYTES,
            2,
            frame1_slot,
            0,
        ) != operation::STATUS_OK
    {
        return None;
    }

    // Touch every page of Frame 0 and Frame 1 so backing tables are warm before iteration 0.
    let f0 = shared_bulk_ptr();
    let f1 = dst_bulk_ptr();
    let mut off = 0usize;
    while off < LARGE_FRAME_BYTES as usize {
        // Safety: both 2 MiB frames were just mapped RW at `BENCH_UMP_WINDOW..+4 MiB`.
        unsafe {
            f0.add(off).write_volatile(0);
            f1.add(off).write_volatile(0);
        }
        off += PAGE_BYTES as usize;
    }

    let arena_addr = BENCH_UMP_WINDOW + ARENA_OFFSET_BYTES as u64;
    assert_eq!(arena_addr % 128, 0);
    // Safety: `retype_large_frame` zeroed Frame 0, which matches the all-zero `RingArena` initial state.
    unsafe { core::ptr::write_bytes(arena_addr as *mut u8, 0, size_of::<RingArena>()) };
    RING_ARENA_ADDR.store(arena_addr, Ordering::Release);
    Some(arena_ref())
}

fn register_cold_cache_ping_pong(registry: &mut Registry, arena: &'static RingArena) -> bool {
    if registry
        .register("Ring/ColdCachePingPong/FlushBaseline", move |state| {
            let hop_addr = cold_ping_pong_hop as *const () as usize;
            while state.keep_running() {
                flush_cold_caches(arena, hop_addr);
            }
            true
        })
        .is_err()
    {
        return false;
    }
    if registry
        .register("Ring/ColdCachePingPong/Raw", move |state| {
            let (Some(mut tx), Some(mut rx)) =
                (make_producer(PINGPONG_CAP), make_consumer(PINGPONG_CAP))
            else {
                return false;
            };
            if !start_worker_mode(arena, CMD_ECHO_PINGPONG) {
                return false;
            }
            let hop_addr = cold_ping_pong_hop as *const () as usize;
            let mut seq = 1u64;
            let mut ok = true;
            while state.keep_running() {
                flush_cold_caches(arena, hop_addr);
                if !cold_ping_pong_hop(&mut tx, &mut rx, arena, seq) {
                    ok = false;
                    break;
                }
                seq += 1;
            }
            let stopped_ok = stop_worker(arena);
            ok && stopped_ok
        })
        .is_err()
    {
        return false;
    }
    registry
        .register_baseline_diff(
            "Ring/ColdCachePingPong",
            "Ring/ColdCachePingPong/Raw",
            "Ring/ColdCachePingPong/FlushBaseline",
        )
        .is_ok()
}

fn register_pipelined_rings(registry: &mut Registry, arena: &'static RingArena) -> bool {
    if registry
        .register("Ring/Pipelined/Send", move |state| {
            state.declare_primary_step();
            state.declare_step("drain_ignore");
            let (Some(mut tx), Some(mut rx)) =
                (make_producer(PINGPONG_CAP), make_consumer(PINGPONG_CAP))
            else {
                return false;
            };
            if !start_worker_mode(arena, CMD_ECHO_PINGPONG) {
                return false;
            }
            let tx_slots = arena.ping_pong_tx_slots.get() as *mut Msg64;
            let rx_slots = arena.ping_pong_rx_slots.get() as *const Msg64;
            let mut seq = 1u64;
            let mut ok = true;
            while state.keep_running() {
                if !ring_try_send(
                    &mut tx,
                    tx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_tx_head,
                    &arena.ping_pong_tx_tail,
                    Msg64::new(seq),
                ) {
                    ok = false;
                    break;
                }
                state.next_step();
                let Some(reply) = ring_recv_wait(
                    &mut rx,
                    rx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_rx_head,
                    &arena.ping_pong_rx_tail,
                ) else {
                    ok = false;
                    break;
                };
                if black_box(reply.words[0]) != (seq ^ ECHO_MASK) {
                    ok = false;
                    break;
                }
                seq += 1;
            }
            let stopped_ok = stop_worker(arena);
            ok && stopped_ok
        })
        .is_err()
    {
        return false;
    }

    if registry
        .register("Ring/Pipelined/ReceivePoll", move |state| {
            state.declare_step("send_wait_ignore");
            state.declare_primary_step();
            let (Some(mut tx), Some(mut rx)) =
                (make_producer(PINGPONG_CAP), make_consumer(PINGPONG_CAP))
            else {
                return false;
            };
            if !start_worker_mode(arena, CMD_ECHO_PINGPONG) {
                return false;
            }
            let tx_slots = arena.ping_pong_tx_slots.get() as *mut Msg64;
            let rx_slots = arena.ping_pong_rx_slots.get() as *const Msg64;
            let mut seq = 1u64;
            let mut ok = true;
            while state.keep_running() {
                let expected_head = rx.index().wrapping_add(1);
                if !ring_send_wait(
                    &mut tx,
                    tx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_tx_head,
                    &arena.ping_pong_tx_tail,
                    Msg64::new(seq),
                ) {
                    ok = false;
                    break;
                }
                let mut ready = false;
                for _ in 0..RING_POLL_MAX {
                    if arena.ping_pong_rx_head.0.load(Ordering::Acquire) == expected_head {
                        ready = true;
                        break;
                    }
                    spin_loop();
                }
                if !ready {
                    ok = false;
                    break;
                }
                state.next_step();
                let Some(reply) = ring_try_recv(
                    &mut rx,
                    rx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_rx_head,
                    &arena.ping_pong_rx_tail,
                ) else {
                    ok = false;
                    break;
                };
                if black_box(reply.words[0]) != (seq ^ ECHO_MASK) {
                    ok = false;
                    break;
                }
                seq += 1;
            }
            let stopped_ok = stop_worker(arena);
            ok && stopped_ok
        })
        .is_err()
    {
        return false;
    }

    registry
        .register("Ring/Pipelined/Throughput16InFlight", move |state| {
            let (Some(mut tx), Some(mut rx)) =
                (make_producer(PINGPONG_CAP), make_consumer(PINGPONG_CAP))
            else {
                return false;
            };
            if !start_worker_mode(arena, CMD_ECHO_PINGPONG) {
                return false;
            }
            let tx_slots = arena.ping_pong_tx_slots.get() as *mut Msg64;
            let rx_slots = arena.ping_pong_rx_slots.get() as *const Msg64;
            let mut send_seq = 1u64;
            let mut recv_seq = 1u64;
            for _ in 0..PIPELINE_DEPTH {
                if !ring_send_wait(
                    &mut tx,
                    tx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_tx_head,
                    &arena.ping_pong_tx_tail,
                    Msg64::new(send_seq),
                ) {
                    let _ = stop_worker(arena);
                    return false;
                }
                send_seq += 1;
            }
            let mut ok = true;
            while state.keep_running() {
                let Some(reply) = ring_recv_wait(
                    &mut rx,
                    rx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_rx_head,
                    &arena.ping_pong_rx_tail,
                ) else {
                    ok = false;
                    break;
                };
                if black_box(reply.words[0]) != (recv_seq ^ ECHO_MASK) {
                    ok = false;
                    break;
                }
                recv_seq += 1;
                if !ring_send_wait(
                    &mut tx,
                    tx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_tx_head,
                    &arena.ping_pong_tx_tail,
                    Msg64::new(send_seq),
                ) {
                    ok = false;
                    break;
                }
                send_seq += 1;
            }
            while recv_seq < send_seq {
                let Some(reply) = ring_recv_wait(
                    &mut rx,
                    rx_slots,
                    PINGPONG_CAP as usize,
                    &arena.ping_pong_rx_head,
                    &arena.ping_pong_rx_tail,
                ) else {
                    ok = false;
                    break;
                };
                if black_box(reply.words[0]) != (recv_seq ^ ECHO_MASK) {
                    ok = false;
                    break;
                }
                recv_seq += 1;
            }
            let stopped_ok = stop_worker(arena);
            ok && stopped_ok
        })
        .is_ok()
}

fn build_fanin_consumers(arena: &RingArena, count: usize) -> Option<Vec<Consumer>> {
    let mut consumers = Vec::with_capacity(count);
    for _ in 0..count {
        consumers.push(make_consumer(FANIN_RING_CAP)?);
    }
    if count > 1 {
        // Seed ring 0 with an out-of-range peer head so `afanin::scan` rejects it every pass
        // without stalling the active producer at ring `count - 1`.
        arena.fanin_heads[0]
            .0
            .store(BOGUS_STALLED_HEAD, Ordering::Release);
    }
    Some(consumers)
}

fn register_fanin(registry: &mut Registry, arena: &'static RingArena, cores: u64) -> bool {
    for &count in &FANIN_COUNTS {
        let name_1c = alloc::format!("FanIn/Poll/{count}Producers/1Core");
        if registry
            .register(name_1c, move |state| {
                reset_arena_rings(arena);
                let Some(mut consumers) = build_fanin_consumers(arena, count) else {
                    return false;
                };
                let Some(mut active_prod) = make_producer(FANIN_RING_CAP) else {
                    return false;
                };
                let active = count - 1;
                let active_slots = unsafe { (*arena.fanin_slots.get())[active].as_mut_ptr() };
                let heads = ArenaHeads(&arena.fanin_heads);
                let mut seq = 1u64;
                while state.keep_running() {
                    if !ring_send_wait(
                        &mut active_prod,
                        active_slots,
                        FANIN_RING_CAP as usize,
                        &arena.fanin_heads[active],
                        &arena.fanin_tails[active],
                        Msg64::new(seq),
                    ) {
                        return false;
                    }
                    let Some(ready_idx) = fanin_scan_once(&mut consumers, &heads, 0) else {
                        return false;
                    };
                    if ready_idx != active {
                        return false;
                    }
                    let Some(msg) = ring_consume_ready(
                        &mut consumers[active],
                        active_slots as *const Msg64,
                        FANIN_RING_CAP as usize,
                        &arena.fanin_tails[active],
                    ) else {
                        return false;
                    };
                    if black_box(msg.words[0]) != seq {
                        return false;
                    }
                    seq += 1;
                }
                true
            })
            .is_err()
        {
            return false;
        }

        if cores >= 2 {
            let name_2c = alloc::format!("FanIn/Poll/{count}Producers/2Core");
            if registry
                .register(name_2c, move |state| {
                    let active = count - 1;
                    arena.fanin_active.0.store(active as u64, Ordering::Release);
                    if !start_worker_mode(arena, CMD_FANIN_PRODUCER) {
                        return false;
                    }
                    let Some(mut consumers) = build_fanin_consumers(arena, count) else {
                        let _ = stop_worker(arena);
                        return false;
                    };
                    let Some(mut trig_tx) = make_producer(PINGPONG_CAP) else {
                        let _ = stop_worker(arena);
                        return false;
                    };
                    let trig_slots = arena.ping_pong_tx_slots.get() as *mut Msg64;
                    let active_slots = unsafe { (*arena.fanin_slots.get())[active].as_ptr() };
                    let heads = ArenaHeads(&arena.fanin_heads);
                    let mut seq = 1u64;
                    let mut ok = true;
                    while state.keep_running() {
                        if !ring_send_wait(
                            &mut trig_tx,
                            trig_slots,
                            PINGPONG_CAP as usize,
                            &arena.ping_pong_tx_head,
                            &arena.ping_pong_tx_tail,
                            Msg64::new(seq),
                        ) {
                            ok = false;
                            break;
                        }
                        let mut found = None;
                        for _ in 0..RING_POLL_MAX {
                            if let Some(idx) = fanin_scan_once(&mut consumers, &heads, 0) {
                                found = Some(idx);
                                break;
                            }
                            spin_loop();
                        }
                        if found != Some(active) {
                            ok = false;
                            break;
                        }
                        let Some(msg) = ring_consume_ready(
                            &mut consumers[active],
                            active_slots,
                            FANIN_RING_CAP as usize,
                            &arena.fanin_tails[active],
                        ) else {
                            ok = false;
                            break;
                        };
                        if black_box(msg.words[0]) != seq {
                            ok = false;
                            break;
                        }
                        seq += 1;
                    }
                    let stopped_ok = stop_worker(arena);
                    ok && stopped_ok
                })
                .is_err()
            {
                return false;
            }
        }
    }
    true
}

fn register_bulk_transfer(registry: &mut Registry, arena: &'static RingArena) -> bool {
    let sizes = [
        (4 * 1024usize, "4K"),
        (64 * 1024usize, "64K"),
        (1024 * 1024usize, "1M"),
    ];
    for (bytes, label_size) in sizes {
        for (do_copy, mode_label) in [(false, "ZeroCopyDescriptor"), (true, "Memcpy")] {
            let name = alloc::format!("Ring/BulkTransfer/{label_size}/{mode_label}");
            if registry
                .register(name, move |state| {
                    let (Some(mut tx), Some(mut rx)) =
                        (make_producer(BULK_RING_CAP), make_consumer(BULK_RING_CAP))
                    else {
                        return false;
                    };
                    let src_base = shared_bulk_ptr();
                    let dst_base = dst_bulk_ptr();
                    let mid = (bytes / 2) & !7usize;
                    let mut off = 0usize;
                    while off < bytes {
                        // Safety: `0..bytes` lies inside mapped Frame 0 and Frame 1 (`2 MiB` each).
                        unsafe {
                            src_base
                                .add(off)
                                .cast::<u64>()
                                .write_volatile(0x1122_3344_5566_7788 ^ (off as u64));
                            dst_base.add(off).cast::<u64>().write_volatile(0);
                        }
                        off += 64;
                    }
                    let expected_mid = 0x1122_3344_5566_7788 ^ (mid as u64);
                    // Safety: `mid < bytes`, aligned to 8 bytes inside mapped Frame 0/Frame 1.
                    unsafe {
                        src_base.add(mid).cast::<u64>().write_volatile(expected_mid);
                        dst_base.add(mid).cast::<u64>().write_volatile(0);
                    }
                    arena.bulk_bytes.0.store(bytes as u64, Ordering::Release);
                    let cmd = if do_copy {
                        CMD_BULK_MEMCPY
                    } else {
                        CMD_BULK_ZEROCOPY
                    };
                    if !start_worker_mode(arena, cmd) {
                        return false;
                    }
                    let tx_slots = arena.bulk_tx_slots.get() as *mut BulkDesc;
                    let rx_slots = arena.bulk_rx_slots.get() as *const BulkDesc;
                    let mut seq = 1u64;
                    let mut ok = true;
                    while state.keep_running() {
                        // Safety: `0` and `bytes - 8` lie inside mapped Frame 0 (`bytes >= 4096`).
                        unsafe {
                            src_base.cast::<u64>().write_volatile(seq);
                            src_base
                                .add(bytes - 8)
                                .cast::<u64>()
                                .write_volatile(seq ^ BULK_TAIL_MASK);
                        }
                        let desc = BulkDesc {
                            offset: 0,
                            len: bytes as u64,
                            tag: seq,
                            _pad: [0; 5],
                        };
                        if !ring_send_wait(
                            &mut tx,
                            tx_slots,
                            BULK_RING_CAP as usize,
                            &arena.bulk_tx_head,
                            &arena.bulk_tx_tail,
                            desc,
                        ) {
                            ok = false;
                            break;
                        }
                        let Some(reply) = ring_recv_wait(
                            &mut rx,
                            rx_slots,
                            BULK_RING_CAP as usize,
                            &arena.bulk_rx_head,
                            &arena.bulk_rx_tail,
                        ) else {
                            ok = false;
                            break;
                        };
                        if black_box(reply.tag) != (seq ^ ECHO_MASK) || reply.len != bytes as u64 {
                            ok = false;
                            break;
                        }
                        seq += 1;
                    }
                    let stopped_ok = stop_worker(arena);
                    if !ok || !stopped_ok {
                        return false;
                    }
                    if do_copy {
                        // Safety: `mid < bytes` lies inside mapped Frame 1 (`dst_base`).
                        let copied_mid = unsafe { dst_base.add(mid).cast::<u64>().read_volatile() };
                        if copied_mid != expected_mid {
                            return false;
                        }
                    }
                    true
                })
                .is_err()
            {
                return false;
            }
        }
    }
    true
}

/// Maps the ring benchmark frames and registers all cold-cache, pipelined, `afanin`, and bulk
/// transfer benchmarks with `registry`.
pub(crate) fn register(registry: &mut Registry) -> bool {
    let Some(arena) = init_ring_frames() else {
        return false;
    };
    let cores = core_count();
    if cores >= 2 {
        if !register_cold_cache_ping_pong(registry, arena)
            || !register_pipelined_rings(registry, arena)
            || !register_bulk_transfer(registry, arena)
        {
            return false;
        }
    }
    register_fanin(registry, arena, cores)
}
