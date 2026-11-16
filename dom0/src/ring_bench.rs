// SPDX-License-Identifier: MIT

//! Shared-frame ring (`aring`) and three-slot mailbox (`amailbox`) raw memory throughput
//! benchmarks (`design/synthetic-benchmark-suite/`, mapped from Fuchsia `fifos.cc`, `sockets.cc`,
//! and `channels.cc`, BSD-2-Clause).
//!
//! Registers:
//! - `Ring/SingleThread/{16,32,64}bytes_{1,4,64}batch` (two-step `"write"` and `"read"`)
//! - `Ring/Payload/{64,1024,32768,65536}bytes/{1Core,2Core}` (single-core and 2-core pinned)
//! - `Mailbox/ThreeSlot/PublishObserve`, `Mailbox/ThreeSlot/StaleObserve`, and
//!   `Mailbox/ThreeSlot/PublishObserve/2Core`
//!
//! All ring slots, cache-line-padded atomic indices, mailbox storage, scratch payload buffers, and
//! the core-1 worker stack reside inside a single 2 MiB large frame retyped from the 1 GiB untyped
//! and mapped into [`BENCH_RING_WINDOW`]. Zero syscalls occur inside any timed loop.

use core::cell::UnsafeCell;
use core::hint::black_box;
use core::mem::{size_of, MaybeUninit};
use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

use abench::runner::Registry;
use asys::operation;
use vstd::prelude::Tracked;

use crate::core_bench::{core_count, stopped, WAKE_READS};
use crate::mmu_bench::{
    alloc_and_link_table, find_gigabyte_untyped, retype_large_frame_until_done, BENCH_2M_WINDOW,
    BENCH_4K_WINDOW, BENCH_CAP_ENTRY_START, BENCH_SPAN_WINDOW,
};
use crate::{
    first_slot, window_clear, ARGUMENT_WORDS, EAGER_WINDOW, HEAP_WINDOW, LARGE_FRAME_BYTES,
    ROOT_ENTRIES, TABLE_PAGE_BYTES, THREAD_BYTES,
};

const PAGE_BYTES: u64 = 4096;

/// Physical offset into the 1 GiB untyped for this suite's 2 MiB shared frame, leaf, tables, and
/// worker thread, clear of `cap_bench` (128..384 MiB) and upper-half checks (`flush_cost` at 512 MiB).
const POOL_OFFSET_BYTES: u64 = 448 * 1024 * 1024;

/// Dedicated level-4 user address window mapping the 2 MiB shared frame.
const BENCH_RING_WINDOW: u64 = 19 << 39;

/// Layout within the mapped 2 MiB shared frame (`BENCH_RING_WINDOW`).
const SLOTS_OFFSET: u64 = 0;
const SLOTS_BYTES: usize = 1 << 20;
const CONTROL_OFFSET: u64 = 1 << 20;
const STACK_OFFSET: u64 = (1 << 20) + (64 << 10);
const STACK_BYTES: u64 = 64 << 10;
const PROD_BUF_OFFSET: u64 = (1 << 20) + (128 << 10);
const CONS_BUF_OFFSET: u64 = (1 << 20) + (192 << 10);
const BUF_BYTES: usize = 64 << 10;

const _: () = assert!(CONS_BUF_OFFSET + BUF_BYTES as u64 <= LARGE_FRAME_BYTES);

const SINGLE_THREAD_CAP: u32 = 128;
const PAYLOAD_CAP: u32 = 16;
const _: () = assert!((SINGLE_THREAD_CAP as usize) * 64 <= SLOTS_BYTES);
const _: () = assert!((PAYLOAD_CAP as usize) * 65536 <= SLOTS_BYTES);

const WORKER_MODE_RING: u64 = 1;
const WORKER_MODE_MAILBOX: u64 = 2;

const WORKER_STATUS_RUNNING: u64 = 0;
const WORKER_STATUS_OK: u64 = 1;
const WORKER_STATUS_ERR: u64 = 2;

const SINGLE_THREAD_SIZES: &[usize] = &[16, 32, 64];
const SINGLE_THREAD_BATCHES: &[u32] = &[1, 4, 64];
const PAYLOAD_SIZES: &[usize] = &[64, 1024, 32768, 65536];

#[repr(C, align(128))]
struct Line32(AtomicU32);

#[repr(C, align(128))]
struct Line64(AtomicU64);

#[repr(C, align(128))]
struct AlignedMailbox(MaybeUninit<amailbox::Mailbox<u64>>);

#[repr(C, align(4096))]
struct Control {
    head_pub: Line32,
    tail_pub: Line32,
    worker_ready: Line64,
    worker_stop: Line64,
    worker_ok: Line64,
    consumed: Line64,
    observed_seq: Line64,
    mode: AtomicU64,
    payload_bytes: AtomicU64,
    ring_cap: AtomicU64,
    slots_addr: AtomicU64,
    worker_buf_addr: AtomicU64,
    mailbox: AlignedMailbox,
    mailbox_consumer: UnsafeCell<Option<amailbox::Consumer<u64>>>,
}

const _: () = assert!(size_of::<Control>() <= 64 * 1024);

// Safety: `mailbox` and `mailbox_consumer` are initialized by core 0 before `START` hands them to
// core 1; all other shared fields use atomic operations on dedicated cache lines.
unsafe impl Sync for Control {}

#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".balign 16",
    ".global dom0_ring_worker_trampoline",
    "dom0_ring_worker_trampoline:",
    "call {entry}",
    "ud2",
    entry = sym dom0_ring_worker_entry,
);

#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(
    ".balign 16",
    ".global dom0_ring_worker_trampoline",
    "dom0_ring_worker_trampoline:",
    "bl {entry}",
    "brk #0",
    entry = sym dom0_ring_worker_entry,
);

unsafe extern "C" {
    fn dom0_ring_worker_trampoline();
}

#[derive(Clone, Copy)]
struct RingBenchFixture {
    worker_thread: Option<u64>,
    control: *const Control,
    slots: *mut u8,
    prod_buf: *mut u8,
    cons_buf: *mut u8,
    worker_stack_top: u64,
}

fn set_frame_word_raw(thread: u64, word: u64, value: u64) -> bool {
    let win = word & !3;
    // Safety: `READ_REGISTERS` inspects an inactive thread's saved registers without altering memory.
    let (status_word, r) =
        unsafe { operation::invoke_returning(operation::READ_REGISTERS, thread, [win, 0, 0, 0, 0]) };
    if operation::status(status_word) != operation::STATUS_OK {
        return false;
    }
    let mut words = [r[0], r[1], r[2], r[3]];
    words[(word & 3) as usize] = value;
    // Safety: `WRITE_REGISTERS` writes the inactive worker thread's initial PC/SP/arg registers.
    operation::status(unsafe {
        operation::invoke(
            operation::WRITE_REGISTERS,
            thread,
            [win, words[0], words[1], words[2], words[3]],
        )
    }) == operation::STATUS_OK
}

impl RingBenchFixture {
    fn init(cores: u64) -> Option<Self> {
        if !window_clear(
            BENCH_RING_WINDOW,
            &[
                EAGER_WINDOW,
                HEAP_WINDOW,
                BENCH_4K_WINDOW,
                BENCH_2M_WINDOW,
                BENCH_SPAN_WINDOW,
            ],
        ) {
            return None;
        }
        let (untyped_slot, block) = find_gigabyte_untyped()?;
        let block_end = block.base + (PAGE_BYTES << block.order);
        let region = block.base + POOL_OFFSET_BYTES;
        if block_end.saturating_sub(region) < 2 * LARGE_FRAME_BYTES {
            return None;
        }

        let leaf_phys = region + LARGE_FRAME_BYTES;
        let mut cap_entry = None;
        for entry in BENCH_CAP_ENTRY_START..ROOT_ENTRIES {
            if matches!(
                operation::inspect(first_slot(entry)),
                Err(operation::STATUS_REFUSED)
            ) && operation::retype_leaf(untyped_slot, leaf_phys, entry) == operation::STATUS_OK
            {
                cap_entry = Some(entry);
                break;
            }
        }
        let first = first_slot(cap_entry?);
        let frame_slot = first;
        let worker_slot = first + 1;

        let mut next_table = leaf_phys + TABLE_PAGE_BYTES;
        if !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_RING_WINDOW, 3)
            || !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_RING_WINDOW, 2)
            || !retype_large_frame_until_done(untyped_slot, region, frame_slot)
            || operation::map(operation::ROOT_PROCESS_SLOT, BENCH_RING_WINDOW, 2, frame_slot, 0)
                != operation::STATUS_OK
        {
            return None;
        }

        let worker_thread = if cores >= 2 {
            let thread_phys = next_table;
            if thread_phys + THREAD_BYTES > region + 2 * LARGE_FRAME_BYTES {
                return None;
            }
            // Safety: `RETYPE_THREAD` types an unmapped order-1 block into a fresh capability slot.
            let retyped = operation::status(unsafe {
                operation::invoke(
                    operation::RETYPE,
                    untyped_slot,
                    [
                        operation::RETYPE_THREAD,
                        thread_phys,
                        worker_slot,
                        operation::ROOT_PROCESS_SLOT,
                        0,
                    ],
                )
            });
            if retyped != operation::STATUS_OK {
                return None;
            }
            // Safety: `PLACE` assigns the newly retyped inactive thread to core 1.
            let placed = operation::status(unsafe {
                operation::invoke(
                    operation::PLACE,
                    worker_slot,
                    [operation::ROOT_CORE_SLOT + 1, 0, 0, 0, 0],
                )
            });
            if placed != operation::STATUS_OK {
                return None;
            }
            Some(worker_slot)
        } else {
            None
        };

        let control_ptr = (BENCH_RING_WINDOW + CONTROL_OFFSET) as *mut Control;
        // Safety: `control_ptr` lies in the freshly zeroed 2 MiB RW frame mapped at `BENCH_RING_WINDOW`;
        // `Control` is valid when zero-initialized (AtomicU32/64 = 0, MaybeUninit, Option::None = 0,
        // wait — initialize explicitly to avoid relying on Option niche layout).
        unsafe {
            control_ptr.write(Control {
                head_pub: Line32(AtomicU32::new(0)),
                tail_pub: Line32(AtomicU32::new(0)),
                worker_ready: Line64(AtomicU64::new(0)),
                worker_stop: Line64(AtomicU64::new(0)),
                worker_ok: Line64(AtomicU64::new(WORKER_STATUS_OK)),
                consumed: Line64(AtomicU64::new(0)),
                observed_seq: Line64(AtomicU64::new(0)),
                mode: AtomicU64::new(0),
                payload_bytes: AtomicU64::new(0),
                ring_cap: AtomicU64::new(0),
                slots_addr: AtomicU64::new(BENCH_RING_WINDOW + SLOTS_OFFSET),
                worker_buf_addr: AtomicU64::new(BENCH_RING_WINDOW + CONS_BUF_OFFSET),
                mailbox: AlignedMailbox(MaybeUninit::uninit()),
                mailbox_consumer: UnsafeCell::new(None),
            });
        }

        Some(Self {
            worker_thread,
            control: control_ptr as *const Control,
            slots: (BENCH_RING_WINDOW + SLOTS_OFFSET) as *mut u8,
            prod_buf: (BENCH_RING_WINDOW + PROD_BUF_OFFSET) as *mut u8,
            cons_buf: (BENCH_RING_WINDOW + CONS_BUF_OFFSET) as *mut u8,
            worker_stack_top: BENCH_RING_WINDOW + STACK_OFFSET + STACK_BYTES,
        })
    }
}

fn ring_new_producer(cap: u32) -> Option<aring::Producer> {
    if !(cap > 0 && 0x1_0000_0000u64 % u64::from(cap) == 0) {
        return None;
    }
    Some(aring::Producer::new(cap))
}

fn ring_new_consumer(cap: u32) -> Option<aring::Consumer> {
    if !(cap > 0 && 0x1_0000_0000u64 % u64::from(cap) == 0) {
        return None;
    }
    Some(aring::Consumer::new(cap))
}

fn ring_new_ends(cap: u32) -> Option<(aring::Producer, aring::Consumer)> {
    Some((ring_new_producer(cap)?, ring_new_consumer(cap)?))
}

#[inline]
fn stamp_buffer(buf: *mut u8, count: usize, stride: usize, seq_base: u64) {
    for k in 0..count {
        // Safety: `buf` spans `count * stride <= BUF_BYTES` with `stride >= 16` aligned to 8 bytes.
        unsafe {
            let slot = buf.add(k * stride);
            let seq = seq_base.wrapping_add(k as u64);
            slot.cast::<u64>().write(seq);
            #[cfg(not(feature = "bench"))]
            slot.add(stride - 8).cast::<u64>().write(!seq);
        }
    }
}

fn fill_pattern(buf: *mut u8, bytes: usize, seed: u8) {
    for i in 0..bytes {
        // Safety: `buf` spans at least `bytes <= BUF_BYTES`.
        unsafe {
            buf.add(i).write(seed.wrapping_add(i as u8));
        }
    }
}

#[inline]
fn ring_push_batch(
    producer: &mut aring::Producer,
    slots_base: *mut u8,
    slot_bytes: usize,
    batch: u32,
    src_base: *const u8,
    head_pub: &AtomicU32,
    tail_pub: &AtomicU32,
) -> bool {
    producer.observe(tail_pub.load(Ordering::Acquire));
    if producer.free() < batch {
        return false;
    }
    for k in 0..batch {
        let s = producer.slot(k);
        // Safety: `s < cap` and `cap * slot_bytes <= SLOTS_BYTES`; `src_base` and `slots_base` are
        // disjoint mapped regions within the 2 MiB arena.
        unsafe {
            let src = src_base.add((k as usize) * slot_bytes);
            let dst = slots_base.add(s * slot_bytes);
            core::ptr::copy_nonoverlapping(src, dst, slot_bytes);
        }
    }
    let new_head = producer.publish(batch);
    head_pub.store(new_head, Ordering::Release);
    true
}

#[inline]
fn ring_pop_count(
    consumer: &mut aring::Consumer,
    slots_base: *const u8,
    slot_bytes: usize,
    exact_batch: u32,
    dst_base: *mut u8,
    head_pub: &AtomicU32,
    tail_pub: &AtomicU32,
    expected_seq: &mut u64,
) -> Option<u32> {
    if !consumer.observe(head_pub.load(Ordering::Acquire)) {
        return None;
    }
    let avail = consumer.available();
    let count = if exact_batch > 0 {
        if avail < exact_batch {
            return None;
        }
        exact_batch
    } else {
        if avail == 0 {
            return Some(0);
        }
        avail
    };
    for k in 0..count {
        let s = consumer.slot(k);
        let dst_idx = if exact_batch > 0 { k as usize } else { 0 };
        // Safety: `s < cap` and `dst_idx * slot_bytes < BUF_BYTES`; `slots_base` and `dst_base` are
        // disjoint mapped regions.
        unsafe {
            let src = slots_base.add(s * slot_bytes);
            let dst = dst_base.add(dst_idx * slot_bytes);
            core::ptr::copy_nonoverlapping(src, dst, slot_bytes);
            let head_word = black_box(dst.cast::<u64>().read());
            #[cfg(not(feature = "bench"))]
            {
                let tail_word = dst.add(slot_bytes - 8).cast::<u64>().read();
                if head_word != *expected_seq || tail_word != !(*expected_seq) {
                    return None;
                }
            }
            #[cfg(feature = "bench")]
            let _ = head_word;
        }
        *expected_seq = expected_seq.wrapping_add(1);
    }
    let new_tail = consumer.consume(count);
    tail_pub.store(new_tail, Ordering::Release);
    Some(count)
}

#[inline]
fn mailbox_publish(producer: &mut amailbox::Producer<u64>, mailbox: &amailbox::Mailbox<u64>, value: u64) {
    amailbox::Producer::write(producer, mailbox, value);
    amailbox::Producer::publish(producer, mailbox);
}

#[inline]
fn mailbox_observe_read(
    consumer: &mut amailbox::Consumer<u64>,
    mailbox: &amailbox::Mailbox<u64>,
) -> (bool, u64) {
    let adopted = amailbox::Consumer::observe(consumer, mailbox, Tracked::assume_new());
    let val = *amailbox::Consumer::read(consumer, mailbox);
    (adopted, val)
}

extern "C" fn dom0_ring_worker_entry(control_addr: u64) -> ! {
    // Safety: `control_addr` points to the initialized `Control` struct mapped at `BENCH_RING_WINDOW`.
    let control = unsafe { &*(control_addr as *const Control) };
    let mode = control.mode.load(Ordering::Acquire);
    let ok = match mode {
        WORKER_MODE_RING => worker_ring_loop(control),
        WORKER_MODE_MAILBOX => worker_mailbox_loop(control),
        _ => false,
    };
    control.worker_ok.0.store(
        if ok { WORKER_STATUS_OK } else { WORKER_STATUS_ERR },
        Ordering::Release,
    );
    loop {
        core::hint::spin_loop();
    }
}

fn worker_ring_loop(control: &Control) -> bool {
    let cap = control.ring_cap.load(Ordering::Acquire) as u32;
    let payload_bytes = control.payload_bytes.load(Ordering::Acquire) as usize;
    let slots = control.slots_addr.load(Ordering::Acquire) as *const u8;
    let dst = control.worker_buf_addr.load(Ordering::Acquire) as *mut u8;
    let Some(mut consumer) = ring_new_consumer(cap) else {
        return false;
    };
    let mut expected_seq = 1u64;
    let mut total = 0u64;
    control.worker_ready.0.store(1, Ordering::Release);
    while control.worker_stop.0.load(Ordering::Acquire) == 0 {
        let head = control.head_pub.0.load(Ordering::Acquire);
        if head != consumer.index() {
            let Some(popped) = ring_pop_count(
                &mut consumer,
                slots,
                payload_bytes,
                0,
                dst,
                &control.head_pub.0,
                &control.tail_pub.0,
                &mut expected_seq,
            ) else {
                return false;
            };
            total += u64::from(popped);
        }
    }
    control.consumed.0.store(total, Ordering::Release);
    true
}

fn worker_mailbox_loop(control: &Control) -> bool {
    // Safety: core 0 initialized `mailbox` and `mailbox_consumer` before `START`.
    let mailbox = unsafe { control.mailbox.0.assume_init_ref() };
    // Safety: core 1 exclusively takes `mailbox_consumer` once before setting `worker_ready`.
    let Some(mut consumer) = (unsafe { (*control.mailbox_consumer.get()).take() }) else {
        return false;
    };
    control.worker_ready.0.store(1, Ordering::Release);
    while control.worker_stop.0.load(Ordering::Acquire) == 0 {
        let (adopted, val) = mailbox_observe_read(&mut consumer, mailbox);
        if adopted {
            control.observed_seq.0.store(val, Ordering::Release);
        }
    }
    true
}

struct WorkerGuard {
    thread: u64,
    control: *const Control,
}

impl WorkerGuard {
    fn start(fixture: RingBenchFixture, mode: u64) -> Option<Self> {
        let thread = fixture.worker_thread?;
        // Safety: `fixture.control` points to the mapped `Control` struct; worker is inactive.
        let control = unsafe { &*fixture.control };
        control.head_pub.0.store(0, Ordering::Release);
        control.tail_pub.0.store(0, Ordering::Release);
        control.worker_ready.0.store(0, Ordering::Release);
        control.worker_stop.0.store(0, Ordering::Release);
        control.worker_ok.0.store(WORKER_STATUS_RUNNING, Ordering::Release);
        control.consumed.0.store(0, Ordering::Release);
        control.observed_seq.0.store(0, Ordering::Release);
        control.mode.store(mode, Ordering::Release);

        let entry = dom0_ring_worker_trampoline as *const () as u64;
        if !set_frame_word_raw(thread, operation::PC_WORD, entry)
            || !set_frame_word_raw(thread, operation::SP_WORD, fixture.worker_stack_top)
            || !set_frame_word_raw(thread, ARGUMENT_WORDS[0], fixture.control as u64)
        {
            return None;
        }
        // Safety: `START` resumes the inactive worker thread already placed on core 1.
        if operation::status(unsafe { operation::invoke(operation::START, thread, [0; 5]) })
            != operation::STATUS_OK
        {
            return None;
        }
        if !(0..WAKE_READS).any(|_| control.worker_ready.0.load(Ordering::Acquire) == 1) {
            control.worker_stop.0.store(1, Ordering::Release);
            let _ = stopped(thread);
            return None;
        }
        Some(Self {
            thread,
            control: fixture.control,
        })
    }

    fn finish(self) -> bool {
        // Safety: `self.control` outlives the guard and `Control` is mapped for the whole boot.
        let control = unsafe { &*self.control };
        control.worker_stop.0.store(1, Ordering::Release);
        let exited = (0..WAKE_READS)
            .any(|_| control.worker_ok.0.load(Ordering::Acquire) != WORKER_STATUS_RUNNING);
        let status = control.worker_ok.0.load(Ordering::Acquire);
        let ok = exited && status == WORKER_STATUS_OK && stopped(self.thread);
        core::mem::forget(self);
        ok
    }
}

impl Drop for WorkerGuard {
    fn drop(&mut self) {
        // Safety: ensures core 1 is stopped cleanly if a benchmark closure exits early on error.
        let control = unsafe { &*self.control };
        control.worker_stop.0.store(1, Ordering::Release);
        let _ = (0..WAKE_READS)
            .any(|_| control.worker_ok.0.load(Ordering::Acquire) != WORKER_STATUS_RUNNING);
        let _ = stopped(self.thread);
    }
}

fn register_single_thread(registry: &mut Registry, fixture: RingBenchFixture) -> bool {
    for &entry_bytes in SINGLE_THREAD_SIZES {
        for &batch in SINGLE_THREAD_BATCHES {
            let name = alloc::format!("Ring/SingleThread/{entry_bytes}bytes_{batch}batch");
            let ok = registry.register(name, move |state| {
                state.declare_step("write");
                state.declare_step("read");
                let Some((mut prod, mut cons)) = ring_new_ends(SINGLE_THREAD_CAP) else {
                    return false;
                };
                // Safety: `fixture.control` points to the mapped `Control` struct.
                let control = unsafe { &*fixture.control };
                control.head_pub.0.store(0, Ordering::Release);
                control.tail_pub.0.store(0, Ordering::Release);
                fill_pattern(fixture.prod_buf, (batch as usize) * entry_bytes, 0x31);
                let mut tx_seq = 1u64;
                let mut rx_seq = 1u64;

                while state.keep_running() {
                    stamp_buffer(fixture.prod_buf, batch as usize, entry_bytes, tx_seq);
                    tx_seq = tx_seq.wrapping_add(u64::from(batch));
                    if !ring_push_batch(
                        &mut prod,
                        fixture.slots,
                        entry_bytes,
                        batch,
                        fixture.prod_buf,
                        &control.head_pub.0,
                        &control.tail_pub.0,
                    ) {
                        return false;
                    }
                    state.next_step();
                    if ring_pop_count(
                        &mut cons,
                        fixture.slots,
                        entry_bytes,
                        batch,
                        fixture.cons_buf,
                        &control.head_pub.0,
                        &control.tail_pub.0,
                        &mut rx_seq,
                    ) != Some(batch)
                    {
                        return false;
                    }
                }
                true
            });
            if ok.is_err() {
                return false;
            }
        }
    }
    true
}

fn register_payload_1core(registry: &mut Registry, fixture: RingBenchFixture) -> bool {
    for &payload_bytes in PAYLOAD_SIZES {
        let name = alloc::format!("Ring/Payload/{payload_bytes}bytes/1Core");
        let ok = registry.register(name, move |state| {
            let Some((mut prod, mut cons)) = ring_new_ends(PAYLOAD_CAP) else {
                return false;
            };
            // Safety: `fixture.control` points to the mapped `Control` struct.
            let control = unsafe { &*fixture.control };
            control.head_pub.0.store(0, Ordering::Release);
            control.tail_pub.0.store(0, Ordering::Release);
            fill_pattern(fixture.prod_buf, payload_bytes, 0x57);
            let mut tx_seq = 1u64;
            let mut rx_seq = 1u64;

            while state.keep_running() {
                stamp_buffer(fixture.prod_buf, 1, payload_bytes, tx_seq);
                tx_seq = tx_seq.wrapping_add(1);
                if !ring_push_batch(
                    &mut prod,
                    fixture.slots,
                    payload_bytes,
                    1,
                    fixture.prod_buf,
                    &control.head_pub.0,
                    &control.tail_pub.0,
                ) {
                    return false;
                }
                if ring_pop_count(
                    &mut cons,
                    fixture.slots,
                    payload_bytes,
                    1,
                    fixture.cons_buf,
                    &control.head_pub.0,
                    &control.tail_pub.0,
                    &mut rx_seq,
                ) != Some(1)
                {
                    return false;
                }
            }
            true
        });
        if ok.is_err() {
            return false;
        }
    }
    true
}

fn register_payload_2core(registry: &mut Registry, fixture: RingBenchFixture) -> bool {
    for &payload_bytes in PAYLOAD_SIZES {
        let name = alloc::format!("Ring/Payload/{payload_bytes}bytes/2Core");
        let ok = registry.register(name, move |state| {
            let Some((mut prod, _)) = ring_new_ends(PAYLOAD_CAP) else {
                return false;
            };
            // Safety: `fixture.control` points to the mapped `Control` struct.
            let control = unsafe { &*fixture.control };
            control.payload_bytes.store(payload_bytes as u64, Ordering::Release);
            control.ring_cap.store(u64::from(PAYLOAD_CAP), Ordering::Release);
            fill_pattern(fixture.prod_buf, payload_bytes, 0x79);

            let Some(worker) = WorkerGuard::start(fixture, WORKER_MODE_RING) else {
                return false;
            };
            let mut tx_seq = 1u64;
            let mut sent = 0u64;

            while state.keep_running() {
                stamp_buffer(fixture.prod_buf, 1, payload_bytes, tx_seq);
                tx_seq = tx_seq.wrapping_add(1);
                if !ring_push_batch(
                    &mut prod,
                    fixture.slots,
                    payload_bytes,
                    1,
                    fixture.prod_buf,
                    &control.head_pub.0,
                    &control.tail_pub.0,
                ) {
                    return false;
                }
                sent += 1;
                let target_tail = prod.index();
                if !(0..WAKE_READS).any(|_| control.tail_pub.0.load(Ordering::Acquire) == target_tail) {
                    return false;
                }
            }
            let finished = worker.finish();
            finished && control.consumed.0.load(Ordering::Acquire) == sent
        });
        if ok.is_err() {
            return false;
        }
    }
    true
}

fn register_mailbox(registry: &mut Registry, fixture: RingBenchFixture, cores: u64) -> bool {
    if registry
        .register("Mailbox/ThreeSlot/PublishObserve", move |state| {
            let (m, mut prod, mut cons) = amailbox::Mailbox::new(0u64, 0u64, 0u64);
            // Safety: `fixture.control` points to the mapped `Control` struct; exclusive during setup.
            let mailbox = unsafe {
                let ptr = fixture.control as *mut Control;
                (*ptr).mailbox.0.write(m)
            };
            let mut seq = 0u64;
            while state.keep_running() {
                seq += 1;
                mailbox_publish(&mut prod, mailbox, seq);
                let (adopted, got) = mailbox_observe_read(&mut cons, mailbox);
                if !adopted || black_box(got) != seq {
                    return false;
                }
            }
            true
        })
        .is_err()
    {
        return false;
    }

    if registry
        .register("Mailbox/ThreeSlot/StaleObserve", move |state| {
            let (m, mut prod, mut cons) = amailbox::Mailbox::new(0u64, 0u64, 0u64);
            // Safety: `fixture.control` points to the mapped `Control` struct; exclusive during setup.
            let mailbox = unsafe {
                let ptr = fixture.control as *mut Control;
                (*ptr).mailbox.0.write(m)
            };
            mailbox_publish(&mut prod, mailbox, 42);
            let (adopted, got) = mailbox_observe_read(&mut cons, mailbox);
            if !adopted || got != 42 {
                return false;
            }
            while state.keep_running() {
                let (stale_adopted, val) = mailbox_observe_read(&mut cons, mailbox);
                if stale_adopted || black_box(val) != 42 {
                    return false;
                }
            }
            true
        })
        .is_err()
    {
        return false;
    }

    if cores >= 2 {
        let ok = registry.register("Mailbox/ThreeSlot/PublishObserve/2Core", move |state| {
            let (m, mut prod, cons) = amailbox::Mailbox::new(0u64, 0u64, 0u64);
            // Safety: `fixture.control` points to the mapped `Control` struct and worker is inactive.
            let control = unsafe {
                let ptr = fixture.control as *mut Control;
                (*ptr).mailbox.0.write(m);
                *(*ptr).mailbox_consumer.get() = Some(cons);
                &*fixture.control
            };
            // Safety: `mailbox` was just initialized above before starting core 1.
            let mailbox = unsafe { control.mailbox.0.assume_init_ref() };
            let Some(worker) = WorkerGuard::start(fixture, WORKER_MODE_MAILBOX) else {
                return false;
            };
            let mut seq = 0u64;
            while state.keep_running() {
                seq += 1;
                mailbox_publish(&mut prod, mailbox, seq);
                if !(0..WAKE_READS).any(|_| control.observed_seq.0.load(Ordering::Acquire) == seq) {
                    return false;
                }
            }
            worker.finish() && control.observed_seq.0.load(Ordering::Acquire) == seq
        });
        if ok.is_err() {
            return false;
        }
    }
    true
}

/// Maps the shared-frame ring/mailbox arena and registers all `aring` and `amailbox` benchmarks.
pub(crate) fn register(registry: &mut Registry) -> bool {
    let cores = core_count();
    let Some(fixture) = RingBenchFixture::init(cores) else {
        return false;
    };
    if !register_single_thread(registry, fixture) || !register_payload_1core(registry, fixture) {
        return false;
    }
    if cores >= 2 && !register_payload_2core(registry, fixture) {
        return false;
    }
    register_mailbox(registry, fixture, cores)
}
