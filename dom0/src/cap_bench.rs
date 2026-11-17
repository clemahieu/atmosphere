// SPDX-License-Identifier: MIT

//! Capability table inspect, capability lifecycle, thread consumed-time inspect, scaled revocation
//! (`> REVOKE_BUDGET`), sibling/foreign delete, populated child process teardown, sibling-descendant
//! retype, and multi-core `QueueLock` capability contention benchmarks mapped from Fuchsia
//! `src/tests/microbenchmarks` (`handle.cc`, `handle_creation.cc`, `events.cc`, `syscalls.cc`,
//! `get_info.cc`; BSD-2-Clause) and Barrelfish `usr/bench` (`distops`, `xcorecap`; MIT) onto
//! Atmosphere's capability operations (`design/synthetic-benchmark-suite/`).

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec;
use core::hint::black_box;
use core::sync::atomic::{AtomicU64, Ordering};

use abench::runner::{Registry, RepeatState};
use asys::operation;

use crate::mmu_bench::retype_large_frame_until_done;
use crate::{
    core_bench, first_slot, ARGUMENT_WORDS, FIRST_LEAF_END, LEAF_BYTES, LEAF_INDICES, MAX_ORDER,
    PROCESS_ORDER, RIGHT_READ, ROOT_ENTRIES, THREAD_BYTES,
};

const PAGE_BYTES: u64 = 4096;
const LARGE_FRAME_BYTES: u64 = 2 * 1024 * 1024;
const PROCESS_BYTES: u64 = PAGE_BYTES << PROCESS_ORDER;
const LEAF_SLOTS: u64 = LEAF_INDICES - 1;
const BENCH_CAP_ENTRY_START: u64 = 32;

/// Physical offset into the 1 GiB untyped where this suite allocates its working blocks, above
/// `mmu_bench`'s `[64 MiB .. 102 MiB]` pool and below `flush_cost` / `core_bench` / `heap`.
const POOL_OFFSET_BYTES: u64 = 128 * 1024 * 1024;
const MIN_REGION_BYTES: u64 = 384 * 1024 * 1024;

/// Maximum core capabilities boot provides to dom0 (`ROOT_UNTYPED_SLOT - ROOT_CORE_SLOT`).
const MAX_CORES: usize = (operation::ROOT_UNTYPED_SLOT - operation::ROOT_CORE_SLOT) as usize;

/// Number of capability slots needed for the largest single-process and distributed revoke sweeps.
const MAX_REVOKE_CAPS: usize = 16384;
const DOM0_SCRATCH_LEAVES: usize = MAX_REVOKE_CAPS.div_ceil(LEAF_SLOTS as usize);

/// Number of child processes across which distributed revocation spreads its derived capabilities.
const DIST_PROCS: usize = 4;
const DIST_CAPS_PER_PROC: usize = MAX_REVOKE_CAPS / DIST_PROCS;
const DIST_LEAVES_PER_PROC: usize = DIST_CAPS_PER_PROC.div_ceil(LEAF_SLOTS as usize);

/// Number of leaves needed for a 1024-cap populated child process teardown.
const POP_128_LEAVES: usize = 128usize.div_ceil(LEAF_SLOTS as usize);
const POP_1024_LEAVES: usize = 1024usize.div_ceil(LEAF_SLOTS as usize);

/// Carved sibling count and derived descendants per sibling for `Capability/Retype/WithSiblingDescendants`.
const RETYPE_SIBLING_COUNT: usize = 256;

/// Per-core derived capability count for `Capability/Contended/Revoke/{n}Cores`.
const CONTEND_REVOKE_CAPS: usize = 256;
const _: () = assert!(MAX_CORES * CONTEND_REVOKE_CAPS <= DOM0_SCRATCH_LEAVES * (LEAF_SLOTS as usize));

#[cfg(not(feature = "bench"))]
const REVOKE_BUDGET: usize = 64;
const REVOKE_AGAIN_MAX: u64 = 512;
const FREE_AGAIN_MAX: u64 = 64;
const WAIT_SPINS: u64 = 1 << 26;
const STOP_AGAIN_MAX: u64 = 1 << 20;
const WORKER_STACK_U128S: usize = 512; // 8 KiB, 16-byte aligned

const MODE_RETYPE: u64 = 1;
const MODE_MOVE: u64 = 2;
const MODE_REVOKE: u64 = 3;
const MODE_INSPECT: u64 = 4;
const MODE_CONC_SWITCH: u64 = 5;

const EMPTY_REFUSED_META_IDX: usize = 9 + 6 * MAX_CORES;
const CONC_HIGH_META_IDX: usize = EMPTY_REFUSED_META_IDX + 1;
const _: () = assert!(CONC_HIGH_META_IDX < 2 * (LEAF_SLOTS as usize));

struct WorkerConfig {
    contend_4k_untyped: AtomicU64,
    contend_4k_phys: AtomicU64,
    contend_4k_slot: AtomicU64,
    proc_a: AtomicU64,
    proc_b: AtomicU64,
    revoke_frame: AtomicU64,
    revoke_phys: AtomicU64,
}

impl WorkerConfig {
    const fn new() -> Self {
        Self {
            contend_4k_untyped: AtomicU64::new(0),
            contend_4k_phys: AtomicU64::new(0),
            contend_4k_slot: AtomicU64::new(0),
            proc_a: AtomicU64::new(0),
            proc_b: AtomicU64::new(0),
            revoke_frame: AtomicU64::new(0),
            revoke_phys: AtomicU64::new(0),
        }
    }
}

static DOM0_ENTRIES: [AtomicU64; DOM0_SCRATCH_LEAVES] =
    [const { AtomicU64::new(0) }; DOM0_SCRATCH_LEAVES];
static WORKER_CONFIGS: [WorkerConfig; MAX_CORES] = [const { WorkerConfig::new() }; MAX_CORES];
static WORKER_MODE: AtomicU64 = AtomicU64::new(0);
static STOP_WORKERS: AtomicU64 = AtomicU64::new(0);
static WORKER_GO: [AtomicU64; MAX_CORES] = [const { AtomicU64::new(0) }; MAX_CORES];
static WORKER_DONE: [AtomicU64; MAX_CORES] = [const { AtomicU64::new(0) }; MAX_CORES];
static WORKER_ITERS: [AtomicU64; MAX_CORES] = [const { AtomicU64::new(0) }; MAX_CORES];
static WORKER_ERR: [AtomicU64; MAX_CORES] = [const { AtomicU64::new(0) }; MAX_CORES];
static INSPECT_FRAME_SLOT: AtomicU64 = AtomicU64::new(0);
static CONC_HIGH_SLOT: AtomicU64 = AtomicU64::new(0);
static CONC_HIGH_ITERS: AtomicU64 = AtomicU64::new(0);

#[inline]
fn dom0_slot(index: usize) -> u64 {
    let leaf = index / (LEAF_SLOTS as usize);
    let offset = (index % (LEAF_SLOTS as usize)) as u64;
    first_slot(DOM0_ENTRIES[leaf].load(Ordering::Relaxed)) + offset
}

#[inline]
const fn child_slot(index: usize) -> u64 {
    let leaf = (index / (LEAF_SLOTS as usize)) as u64;
    let offset = (index % (LEAF_SLOTS as usize)) as u64;
    first_slot(leaf) + offset
}

#[inline]
pub(crate) const fn align_up(value: u64, align: u64) -> u64 {
    (value + align - 1) & !(align - 1)
}

fn find_gigabyte_untyped() -> Option<(u64, operation::Capability)> {
    let min_pages = 1u64 << 18;
    let mut slot = operation::ROOT_UNTYPED_SLOT;
    let mut found = None;
    while slot <= FIRST_LEAF_END {
        match operation::inspect(slot) {
            Ok(cap) => {
                if cap.kind == operation::KIND_UNTYPED
                    && cap.order < MAX_ORDER
                    && (1u64 << cap.order) >= min_pages
                {
                    found = Some((slot, cap));
                }
            }
            Err(operation::STATUS_REFUSED) => break,
            Err(_) => return None,
        }
        slot += 1;
    }
    found
}

#[inline]
pub(crate) fn retype_process(untyped: u64, base: u64, destination: u64) -> u64 {
    // Process creation allocates an order-3 block and updates capability tables only.
    operation::status(unsafe {
        operation::invoke(
            operation::RETYPE,
            untyped,
            [operation::RETYPE_PROCESS, base, destination, 0, 0],
        )
    })
}

#[inline]
pub(crate) fn retype_thread(untyped: u64, base: u64, destination: u64, process: u64) -> u64 {
    // Thread creation allocates an order-1 block bound to `process`, changing no address space.
    operation::status(unsafe {
        operation::invoke(
            operation::RETYPE,
            untyped,
            [operation::RETYPE_THREAD, base, destination, process, 0],
        )
    })
}

#[inline]
fn destroy_cap(slot: u64) -> u64 {
    // Destroy marks a child process or thread dead without changing dom0's own address space.
    operation::status(unsafe { operation::invoke(operation::DESTROY, slot, [0; 5]) })
}

#[inline]
pub(crate) fn place_thread(thread: u64, core: u64, priority: u64) -> u64 {
    operation::status(unsafe {
        operation::invoke(operation::PLACE, thread, [core, priority, 0, 0, 0])
    })
}

#[inline]
pub(crate) fn start_thread(thread: u64) -> u64 {
    operation::status(unsafe { operation::invoke(operation::START, thread, [0; 5]) })
}

#[inline]
fn suspend_thread(thread: u64) -> u64 {
    operation::status(unsafe { operation::invoke(operation::SUSPEND, thread, [0; 5]) })
}

fn read_window(thread: u64, index: u64) -> Result<[u64; 4], u64> {
    let (word, results) = unsafe {
        operation::invoke_returning(operation::READ_REGISTERS, thread, [index, 0, 0, 0, 0])
    };
    match operation::status(word) {
        operation::STATUS_OK => Ok([results[0], results[1], results[2], results[3]]),
        err => Err(err),
    }
}

pub(crate) fn set_frame_word(thread: u64, word: u64, value: u64) -> u64 {
    match read_window(thread, word & !3) {
        Ok(mut words) => {
            words[(word & 3) as usize] = value;
            operation::status(unsafe {
                operation::invoke(
                    operation::WRITE_REGISTERS,
                    thread,
                    [word & !3, words[0], words[1], words[2], words[3]],
                )
            })
        }
        Err(status) => status,
    }
}

pub(crate) fn stopped(thread: u64) -> bool {
    let mut again = 0;
    loop {
        match suspend_thread(thread) {
            operation::STATUS_AGAIN if again < STOP_AGAIN_MAX => again += 1,
            status => return status == operation::STATUS_OK,
        }
    }
}

fn revoke_until_done(slot: u64) -> Option<u64> {
    let mut again = 0u64;
    for _ in 0..REVOKE_AGAIN_MAX {
        // Safety: cap_bench revokes only unmapped frame/untyped capabilities created for benchmarks.
        match unsafe { operation::revoke(slot) } {
            operation::STATUS_OK => return Some(again),
            operation::STATUS_AGAIN => again += 1,
            _ => return None,
        }
    }
    None
}

fn retype_free_until_done(untyped: u64, base: u64, order: u64) -> bool {
    for _ in 0..FREE_AGAIN_MAX {
        // Safety: freeing a dead unmapped frame changes no live mapping in dom0's address space.
        let status = operation::status(unsafe {
            operation::invoke(
                operation::RETYPE,
                untyped,
                [operation::RETYPE_FREE, base, 0, order, 0],
            )
        });
        match status {
            operation::STATUS_OK => return true,
            operation::STATUS_AGAIN => {}
            _ => return false,
        }
    }
    false
}

fn alloc_dom0_leaf(untyped: u64, cursor: &mut u64, next_entry: &mut u64) -> Option<u64> {
    *cursor = align_up(*cursor, LEAF_BYTES);
    while *next_entry < ROOT_ENTRIES {
        let entry = *next_entry;
        *next_entry += 1;
        if matches!(
            operation::inspect(first_slot(entry)),
            Err(operation::STATUS_REFUSED)
        ) {
            let leaf_phys = *cursor;
            if operation::retype_leaf(untyped, leaf_phys, entry) == operation::STATUS_OK {
                *cursor += LEAF_BYTES;
                return Some(entry);
            }
        }
    }
    None
}

fn worker_retype_step(core_idx: usize) -> bool {
    let cfg = &WORKER_CONFIGS[core_idx];
    let untyped = cfg.contend_4k_untyped.load(Ordering::Relaxed);
    let phys = cfg.contend_4k_phys.load(Ordering::Relaxed);
    let slot = cfg.contend_4k_slot.load(Ordering::Relaxed);
    operation::retype_frame(untyped, phys, slot) == operation::STATUS_OK
        && operation::delete(slot) == operation::STATUS_OK
        && retype_free_until_done(untyped, phys, 0)
}

fn worker_move_step(core_idx: usize) -> bool {
    let cfg = &WORKER_CONFIGS[core_idx];
    let proc_a = cfg.proc_a.load(Ordering::Relaxed);
    let proc_b = cfg.proc_b.load(Ordering::Relaxed);
    let slot_a = operation::through(proc_a, first_slot(0));
    let slot_b = operation::through(proc_b, first_slot(0));
    operation::move_capability(slot_a, slot_b) == operation::STATUS_OK
        && operation::move_capability(slot_b, slot_a) == operation::STATUS_OK
}

fn worker_revoke_step(core_idx: usize) -> bool {
    let cfg = &WORKER_CONFIGS[core_idx];
    let frame = cfg.revoke_frame.load(Ordering::Relaxed);
    let phys = cfg.revoke_phys.load(Ordering::Relaxed);
    let base_idx = core_idx * CONTEND_REVOKE_CAPS;
    for i in 0..CONTEND_REVOKE_CAPS {
        if operation::derive(frame, dom0_slot(base_idx + i), RIGHT_READ, phys, 0)
            != operation::STATUS_OK
        {
            return false;
        }
    }
    revoke_until_done(frame).is_some()
}

fn worker_inspect_step() -> bool {
    black_box(operation::inspect(INSPECT_FRAME_SLOT.load(Ordering::Relaxed))).is_ok()
}

fn worker_conc_switch_step() -> bool {
    let conc_slot = CONC_HIGH_SLOT.load(Ordering::Relaxed);
    let before = CONC_HIGH_ITERS.load(Ordering::Acquire);
    if start_thread(conc_slot) != operation::STATUS_OK {
        return false;
    }
    // Wait past the self-IPI delivery window until the higher-priority worker ran and self-suspended.
    (0..WAIT_SPINS).any(|_| CONC_HIGH_ITERS.load(Ordering::Acquire) != before)
}

extern "C" fn conc_high_worker(self_slot: u64) -> ! {
    loop {
        CONC_HIGH_ITERS.fetch_add(1, Ordering::Release);
        // Self-suspending hands core 1 straight back to the priority-0 partner thread.
        let _ = operation::status(unsafe {
            operation::invoke(operation::SUSPEND, self_slot, [0; 5])
        });
    }
}

fn init_worker_thread(
    untyped_slot: u64,
    thread_phys: u64,
    thread_slot: u64,
    entry: u64,
    arg0: u64,
    core_slot: u64,
    priority: u64,
) -> bool {
    let stack = Box::leak(vec![0u128; WORKER_STACK_U128S].into_boxed_slice());
    let top = stack.as_ptr() as u64 + (stack.len() * 16) as u64;
    #[cfg(target_arch = "x86_64")]
    let sp = top - 8;
    #[cfg(target_arch = "aarch64")]
    let sp = top;

    retype_thread(
        untyped_slot,
        thread_phys,
        thread_slot,
        operation::ROOT_PROCESS_SLOT,
    ) == operation::STATUS_OK
        && set_frame_word(thread_slot, operation::PC_WORD, entry) == operation::STATUS_OK
        && set_frame_word(thread_slot, operation::SP_WORD, sp) == operation::STATUS_OK
        && set_frame_word(thread_slot, ARGUMENT_WORDS[0], arg0) == operation::STATUS_OK
        && place_thread(thread_slot, core_slot, priority) == operation::STATUS_OK
}

extern "C" fn cap_bench_worker(core_idx: u64) -> ! {
    let idx = core_idx as usize;
    loop {
        while WORKER_GO[idx].load(Ordering::Acquire) == 0 {
            core::hint::spin_loop();
        }
        let mode = WORKER_MODE.load(Ordering::Acquire);
        while STOP_WORKERS.load(Ordering::Acquire) == 0 {
            let ok = match mode {
                MODE_RETYPE => worker_retype_step(idx),
                MODE_MOVE => worker_move_step(idx),
                MODE_REVOKE => worker_revoke_step(idx),
                MODE_INSPECT => worker_inspect_step(),
                MODE_CONC_SWITCH => worker_conc_switch_step(),
                _ => false,
            };
            if !ok {
                WORKER_ERR[idx].store(1, Ordering::Release);
                break;
            }
            WORKER_ITERS[idx].fetch_add(1, Ordering::Release);
        }
        WORKER_GO[idx].store(0, Ordering::Release);
        WORKER_DONE[idx].store(1, Ordering::Release);
    }
}

struct CapBenchFixture {
    cores: usize,
    untyped_slot: u64,
    frame_cap: u64,
    frame_phys: u64,
    claim_frame_cap: u64,
    claim_frame_phys: u64,
    empty_refused_slot: u64,
    conc_high_slot: u64,
    retype_4k_phys: u64,
    large_2m_phys: u64,
    retype_proc_base: u64,
    retype_thread_base: u64,
    retype_2m_untyped: u64,
    retype_2m_phys: u64,
    pop_proc_slot: u64,
    pop_claim_slot: u64,
    pop_128_proc_base: u64,
    pop_128_leaf_base: u64,
    pop_1024_proc_base: u64,
    pop_1024_leaf_base: u64,
    dist_procs: [u64; DIST_PROCS],
    worker_threads: [u64; MAX_CORES],
}

impl CapBenchFixture {
    fn init() -> Option<Self> {
        let cores = core_bench::core_count() as usize;
        if cores < 1 || cores > MAX_CORES {
            return None;
        }
        let (untyped_slot, block) = find_gigabyte_untyped()?;
        let block_end = block.base + (PAGE_BYTES << block.order);
        let mut cursor = block.base + POOL_OFFSET_BYTES;
        if block_end.saturating_sub(cursor) < MIN_REGION_BYTES {
            return None;
        }

        let mut next_entry = BENCH_CAP_ENTRY_START;
        let meta_entries = [
            alloc_dom0_leaf(untyped_slot, &mut cursor, &mut next_entry)?,
            alloc_dom0_leaf(untyped_slot, &mut cursor, &mut next_entry)?,
        ];
        let meta_slot = |idx: usize| -> u64 {
            let leaf = idx / (LEAF_SLOTS as usize);
            let off = (idx % (LEAF_SLOTS as usize)) as u64;
            first_slot(meta_entries[leaf]) + off
        };

        for entry_slot in &DOM0_ENTRIES {
            let entry = alloc_dom0_leaf(untyped_slot, &mut cursor, &mut next_entry)?;
            entry_slot.store(entry, Ordering::Release);
        }

        // 2 MiB-aligned child untyped for `Capability/Retype/WithSiblingDescendants`.
        cursor = align_up(cursor, LARGE_FRAME_BYTES);
        let retype_2m_phys = cursor;
        cursor += LARGE_FRAME_BYTES;

        // Distributed revocation child processes (4 processes x 33 leaves = 16,764 slots).
        cursor = align_up(cursor, PROCESS_BYTES);
        let mut dist_procs = [0u64; DIST_PROCS];
        for (p, proc_slot_out) in dist_procs.iter_mut().enumerate() {
            let slot = meta_slot(5 + p);
            if retype_process(untyped_slot, cursor, slot) != operation::STATUS_OK {
                return None;
            }
            cursor += PROCESS_BYTES;
            *proc_slot_out = slot;
        }
        for &proc_slot in &dist_procs {
            for l in 0..(DIST_LEAVES_PER_PROC as u64) {
                if operation::retype_leaf(untyped_slot, cursor, operation::through(proc_slot, l))
                    != operation::STATUS_OK
                {
                    return None;
                }
                cursor += LEAF_BYTES;
            }
        }

        // Populated process teardown pools (sized by `core_bench::POOL`).
        let pool = core_bench::POOL;
        cursor = align_up(cursor, PROCESS_BYTES);
        let pop_128_proc_base = cursor;
        cursor += pool * PROCESS_BYTES;
        let pop_128_leaf_base = cursor;
        cursor += pool * (POP_128_LEAVES as u64) * LEAF_BYTES;
        cursor = align_up(cursor, PROCESS_BYTES);
        let pop_1024_proc_base = cursor;
        cursor += pool * PROCESS_BYTES;
        let pop_1024_leaf_base = cursor;
        cursor += pool * (POP_1024_LEAVES as u64) * LEAF_BYTES;

        // Core metadata slots.
        let frame_cap = meta_slot(0);
        let claim_frame_cap = meta_slot(1);
        let retype_2m_untyped = meta_slot(2);
        let pop_proc_slot = meta_slot(3);
        let pop_claim_slot = meta_slot(4);
        let empty_refused_slot = meta_slot(EMPTY_REFUSED_META_IDX);
        let conc_high_slot = meta_slot(CONC_HIGH_META_IDX);

        let frame_phys = cursor;
        cursor += PAGE_BYTES;
        let claim_frame_phys = cursor;
        cursor += PAGE_BYTES;
        let retype_4k_phys = cursor;
        cursor += PAGE_BYTES;

        cursor = align_up(cursor, LARGE_FRAME_BYTES);
        let large_2m_phys = cursor;
        cursor += LARGE_FRAME_BYTES;

        cursor = align_up(cursor, PROCESS_BYTES);
        let retype_proc_base = cursor;
        cursor += pool * PROCESS_BYTES;
        cursor = align_up(cursor, THREAD_BYTES);
        let retype_thread_base = cursor;
        cursor += pool * THREAD_BYTES;

        if operation::retype_frame(untyped_slot, frame_phys, frame_cap) != operation::STATUS_OK
            || operation::retype_frame(untyped_slot, claim_frame_phys, claim_frame_cap)
                != operation::STATUS_OK
            || operation::derive(untyped_slot, retype_2m_untyped, block.rights, retype_2m_phys, 9)
                != operation::STATUS_OK
        {
            return None;
        }

        // Per-core resources for `Capability/Contended/*`.
        cursor = align_up(cursor, PROCESS_BYTES);
        let mut worker_threads = [0u64; MAX_CORES];
        for c in 0..cores {
            let proc_a = meta_slot(9 + c);
            let proc_b = meta_slot(9 + MAX_CORES + c);
            let contend_4k_untyped = meta_slot(9 + 2 * MAX_CORES + c);
            let contend_4k_slot = meta_slot(9 + 3 * MAX_CORES + c);
            let revoke_frame = meta_slot(9 + 4 * MAX_CORES + c);
            let move_frame_tmp = dom0_slot(0);

            let proc_a_phys = cursor;
            cursor += PROCESS_BYTES;
            let proc_b_phys = cursor;
            cursor += PROCESS_BYTES;
            let leaf_a_phys = cursor;
            cursor += LEAF_BYTES;
            let leaf_b_phys = cursor;
            cursor += LEAF_BYTES;
            let contend_4k_phys = cursor;
            cursor += PAGE_BYTES;
            let move_frame_phys = cursor;
            cursor += PAGE_BYTES;
            let revoke_phys = cursor;
            cursor += PAGE_BYTES;
            cursor = align_up(cursor, PROCESS_BYTES);

            if retype_process(untyped_slot, proc_a_phys, proc_a) != operation::STATUS_OK
                || retype_process(untyped_slot, proc_b_phys, proc_b) != operation::STATUS_OK
                || operation::retype_leaf(untyped_slot, leaf_a_phys, operation::through(proc_a, 0))
                    != operation::STATUS_OK
                || operation::retype_leaf(untyped_slot, leaf_b_phys, operation::through(proc_b, 0))
                    != operation::STATUS_OK
                || operation::derive(untyped_slot, contend_4k_untyped, block.rights, contend_4k_phys, 0)
                    != operation::STATUS_OK
                || operation::retype_frame(untyped_slot, move_frame_phys, move_frame_tmp)
                    != operation::STATUS_OK
                || operation::move_capability(move_frame_tmp, operation::through(proc_a, first_slot(0)))
                    != operation::STATUS_OK
                || operation::retype_frame(untyped_slot, revoke_phys, revoke_frame)
                    != operation::STATUS_OK
            {
                return None;
            }

            let cfg = &WORKER_CONFIGS[c];
            cfg.contend_4k_untyped.store(contend_4k_untyped, Ordering::Release);
            cfg.contend_4k_phys.store(contend_4k_phys, Ordering::Release);
            cfg.contend_4k_slot.store(contend_4k_slot, Ordering::Release);
            cfg.proc_a.store(proc_a, Ordering::Release);
            cfg.proc_b.store(proc_b, Ordering::Release);
            cfg.revoke_frame.store(revoke_frame, Ordering::Release);
            cfg.revoke_phys.store(revoke_phys, Ordering::Release);
        }

        cursor = align_up(cursor, THREAD_BYTES);
        for (c, thread_slot_out) in worker_threads.iter_mut().enumerate().take(cores).skip(1) {
            let thread_slot = meta_slot(9 + 5 * MAX_CORES + c);
            let thread_phys = cursor;
            cursor += THREAD_BYTES;
            if !init_worker_thread(
                untyped_slot,
                thread_phys,
                thread_slot,
                cap_bench_worker as *const () as u64,
                c as u64,
                operation::ROOT_CORE_SLOT + (c as u64),
                0,
            ) {
                return None;
            }
            *thread_slot_out = thread_slot;
        }

        let conc_high_phys = cursor;
        cursor += THREAD_BYTES;
        let conc_core = if cores >= 2 {
            operation::ROOT_CORE_SLOT + 1
        } else {
            operation::ROOT_CORE_SLOT
        };
        if !init_worker_thread(
            untyped_slot,
            conc_high_phys,
            conc_high_slot,
            conc_high_worker as *const () as u64,
            conc_high_slot,
            conc_core,
            1,
        ) {
            return None;
        }

        if cursor > block.base + MIN_REGION_BYTES {
            return None;
        }

        INSPECT_FRAME_SLOT.store(frame_cap, Ordering::Release);
        CONC_HIGH_SLOT.store(conc_high_slot, Ordering::Release);

        Some(Self {
            cores,
            untyped_slot,
            frame_cap,
            frame_phys,
            claim_frame_cap,
            claim_frame_phys,
            empty_refused_slot,
            conc_high_slot,
            retype_4k_phys,
            large_2m_phys,
            retype_proc_base,
            retype_thread_base,
            retype_2m_untyped,
            retype_2m_phys,
            pop_proc_slot,
            pop_claim_slot,
            pop_128_proc_base,
            pop_128_leaf_base,
            pop_1024_proc_base,
            pop_1024_leaf_base,
            dist_procs,
            worker_threads,
        })
    }
}

fn register_revoke_sweeps(registry: &mut Registry, fixture: &Rc<CapBenchFixture>) -> bool {
    for count in [1usize, 64, 256, 1024, 4096, 16384] {
        let f_local = Rc::clone(fixture);
        if registry
            .register(alloc::format!("Capability/Revoke/{count}"), move |state| {
                state.declare_step("setup_ignore");
                state.declare_step("revoke");
                while state.keep_running() {
                    for i in 0..count {
                        if operation::derive(
                            f_local.frame_cap,
                            dom0_slot(i),
                            RIGHT_READ,
                            f_local.frame_phys,
                            0,
                        ) != operation::STATUS_OK
                        {
                            return false;
                        }
                    }
                    state.next_step();

                    let Some(again) = revoke_until_done(f_local.frame_cap) else {
                        return false;
                    };
                    #[cfg(not(feature = "bench"))]
                    {
                        let expected_again = (count.div_ceil(REVOKE_BUDGET) - 1) as u64;
                        if again != expected_again
                            || operation::inspect(dom0_slot(0)).is_ok()
                            || operation::inspect(dom0_slot(count - 1)).is_ok()
                            || operation::inspect(f_local.frame_cap).is_err()
                        {
                            return false;
                        }
                    }
                    #[cfg(feature = "bench")]
                    let _ = again;
                }
                true
            })
            .is_err()
        {
            return false;
        }

        if count < 256 {
            continue;
        }

        let f_dist = Rc::clone(fixture);
        if registry
            .register(
                alloc::format!("Capability/Revoke/Distributed/{count}"),
                move |state| {
                    state.declare_step("setup_ignore");
                    state.declare_step("revoke");
                    while state.keep_running() {
                        for i in 0..count {
                            let proc_slot = f_dist.dist_procs[i % DIST_PROCS];
                            let dst = operation::through(proc_slot, child_slot(i / DIST_PROCS));
                            if operation::derive(
                                f_dist.frame_cap,
                                dst,
                                RIGHT_READ,
                                f_dist.frame_phys,
                                0,
                            ) != operation::STATUS_OK
                            {
                                return false;
                            }
                        }
                        state.next_step();

                        let Some(again) = revoke_until_done(f_dist.frame_cap) else {
                            return false;
                        };
                        #[cfg(not(feature = "bench"))]
                        {
                            let expected_again = ((count / REVOKE_BUDGET) - 1) as u64;
                            let last_proc = f_dist.dist_procs[(count - 1) % DIST_PROCS];
                            let last_slot =
                                operation::through(last_proc, child_slot((count - 1) / DIST_PROCS));
                            if again != expected_again
                                || operation::inspect(operation::through(
                                    f_dist.dist_procs[0],
                                    child_slot(0),
                                ))
                                .is_ok()
                                || operation::inspect(last_slot).is_ok()
                                || operation::inspect(f_dist.frame_cap).is_err()
                            {
                                return false;
                            }
                        }
                        #[cfg(feature = "bench")]
                        let _ = again;
                    }
                    true
                },
            )
            .is_err()
        {
            return false;
        }
    }
    true
}

fn register_delete_benchmarks(registry: &mut Registry, fixture: &Rc<CapBenchFixture>) -> bool {
    for siblings in [256usize, 4096] {
        let f = Rc::clone(fixture);
        if registry
            .register(
                alloc::format!("Capability/Delete/WithSiblings_{siblings}"),
                move |state| {
                    state.declare_step("setup_ignore");
                    state.declare_step("delete");
                    for i in 0..siblings {
                        if operation::derive(f.frame_cap, dom0_slot(i), RIGHT_READ, f.frame_phys, 0)
                            != operation::STATUS_OK
                        {
                            return false;
                        }
                    }
                    let target = dom0_slot(siblings);
                    let mut ok = true;
                    while state.keep_running() {
                        if operation::derive(f.frame_cap, target, RIGHT_READ, f.frame_phys, 0)
                            != operation::STATUS_OK
                        {
                            ok = false;
                            break;
                        }
                        state.next_step();
                        if operation::delete(target) != operation::STATUS_OK {
                            ok = false;
                            break;
                        }
                        #[cfg(not(feature = "bench"))]
                        if operation::inspect(target) != Err(operation::STATUS_REFUSED) {
                            ok = false;
                            break;
                        }
                    }
                    revoke_until_done(f.frame_cap).is_some() && ok
                },
            )
            .is_err()
        {
            return false;
        }
    }

    let f = Rc::clone(fixture);
    registry
        .register("Capability/Delete/ForeignVsLastDerived", move |state| {
            state.declare_step("setup_ignore");
            state.declare_step("foreign");
            state.declare_step("last_derived");
            let foreign_slot = operation::through(f.dist_procs[0], child_slot(0));
            let local_slot = dom0_slot(0);
            while state.keep_running() {
                if operation::derive(f.frame_cap, foreign_slot, RIGHT_READ, f.frame_phys, 0)
                    != operation::STATUS_OK
                    || operation::derive(f.frame_cap, local_slot, RIGHT_READ, f.frame_phys, 0)
                        != operation::STATUS_OK
                {
                    return false;
                }
                state.next_step();
                if operation::delete(foreign_slot) != operation::STATUS_OK {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(foreign_slot) != Err(operation::STATUS_REFUSED) {
                    return false;
                }
                state.next_step();
                if operation::delete(local_slot) != operation::STATUS_OK {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(local_slot) != Err(operation::STATUS_REFUSED)
                    || operation::delete(local_slot) != operation::STATUS_REFUSED
                {
                    return false;
                }
            }
            true
        })
        .is_ok()
}

fn register_populated_process_destroy(registry: &mut Registry, fixture: &Rc<CapBenchFixture>) -> bool {
    for (caps, leaves, proc_base, leaf_base) in [
        (
            128usize,
            POP_128_LEAVES,
            fixture.pop_128_proc_base,
            fixture.pop_128_leaf_base,
        ),
        (
            1024usize,
            POP_1024_LEAVES,
            fixture.pop_1024_proc_base,
            fixture.pop_1024_leaf_base,
        ),
    ] {
        let f = Rc::clone(fixture);
        if registry
            .register(
                alloc::format!("Capability/Destroy/PopulatedProcess/{caps}Caps"),
                move |state| {
                    state.declare_step("setup_ignore");
                    state.declare_step("destroy");
                    state.declare_step("move_revoke");
                    state.declare_step("teardown_ignore");
                    let mut iter = 0u64;
                    while state.keep_running() {
                        if iter >= core_bench::POOL {
                            return false;
                        }
                        let proc_phys = proc_base + iter * PROCESS_BYTES;
                        let iter_leaf_base = leaf_base + iter * (leaves as u64) * LEAF_BYTES;
                        iter += 1;

                        if retype_process(f.untyped_slot, proc_phys, f.pop_proc_slot)
                            != operation::STATUS_OK
                        {
                            return false;
                        }
                        for l in 0..(leaves as u64) {
                            if operation::retype_leaf(
                                f.untyped_slot,
                                iter_leaf_base + l * LEAF_BYTES,
                                operation::through(f.pop_proc_slot, l),
                            ) != operation::STATUS_OK
                            {
                                return false;
                            }
                        }
                        if operation::derive(
                            f.claim_frame_cap,
                            operation::through(f.pop_proc_slot, child_slot(0)),
                            RIGHT_READ,
                            f.claim_frame_phys,
                            0,
                        ) != operation::STATUS_OK
                        {
                            return false;
                        }
                        for i in 1..caps {
                            if operation::derive(
                                f.frame_cap,
                                operation::through(f.pop_proc_slot, child_slot(i)),
                                RIGHT_READ,
                                f.frame_phys,
                                0,
                            ) != operation::STATUS_OK
                            {
                                return false;
                            }
                        }
                        state.next_step();

                        if destroy_cap(f.pop_proc_slot) != operation::STATUS_OK {
                            return false;
                        }
                        #[cfg(not(feature = "bench"))]
                        if destroy_cap(f.pop_proc_slot) != operation::STATUS_REFUSED {
                            return false;
                        }
                        state.next_step();

                        if operation::move_capability(
                            operation::through(f.pop_proc_slot, child_slot(0)),
                            f.pop_claim_slot,
                        ) != operation::STATUS_OK
                        {
                            return false;
                        }
                        let Some(again) = revoke_until_done(f.frame_cap) else {
                            return false;
                        };
                        #[cfg(not(feature = "bench"))]
                        {
                            let expected_again = ((caps - 1).div_ceil(REVOKE_BUDGET) - 1) as u64;
                            if again != expected_again
                                || operation::inspect(f.pop_claim_slot).is_err()
                                || operation::inspect(operation::through(
                                    f.pop_proc_slot,
                                    child_slot(0),
                                ))
                                .is_ok()
                                || operation::inspect(operation::through(
                                    f.pop_proc_slot,
                                    child_slot(caps - 1),
                                ))
                                .is_ok()
                            {
                                return false;
                            }
                        }
                        #[cfg(feature = "bench")]
                        let _ = again;
                        state.next_step();

                        if operation::delete(f.pop_claim_slot) != operation::STATUS_OK
                            || operation::delete(f.pop_proc_slot) != operation::STATUS_OK
                        {
                            return false;
                        }
                        #[cfg(not(feature = "bench"))]
                        if operation::inspect(f.pop_proc_slot).is_ok() {
                            return false;
                        }
                    }
                    true
                },
            )
            .is_err()
        {
            return false;
        }
    }
    true
}

fn register_retype_with_siblings(registry: &mut Registry, fixture: &Rc<CapBenchFixture>) -> bool {
    let f = Rc::clone(fixture);
    registry
        .register("Capability/Retype/WithSiblingDescendants", move |state| {
            state.declare_step("retype");
            state.declare_step("teardown_ignore");
            for i in 0..RETYPE_SIBLING_COUNT {
                let page_phys = f.retype_2m_phys + (i as u64) * PAGE_BYTES;
                if operation::retype_frame(f.retype_2m_untyped, page_phys, dom0_slot(i))
                    != operation::STATUS_OK
                    || operation::derive(
                        dom0_slot(i),
                        dom0_slot(RETYPE_SIBLING_COUNT + i),
                        RIGHT_READ,
                        page_phys,
                        0,
                    ) != operation::STATUS_OK
                {
                    return false;
                }
            }
            let target_phys = f.retype_2m_phys + (RETYPE_SIBLING_COUNT as u64) * PAGE_BYTES;
            let target_slot = dom0_slot(2 * RETYPE_SIBLING_COUNT);
            let mut ok = true;
            while state.keep_running() {
                if operation::retype_frame(f.retype_2m_untyped, target_phys, target_slot)
                    != operation::STATUS_OK
                {
                    ok = false;
                    break;
                }
                #[cfg(not(feature = "bench"))]
                if !matches!(
                    operation::inspect(target_slot),
                    Ok(cap) if cap.kind == operation::KIND_FRAME && cap.base == target_phys
                ) {
                    ok = false;
                    break;
                }
                state.next_step();
                if operation::delete(target_slot) != operation::STATUS_OK
                    || !retype_free_until_done(f.retype_2m_untyped, target_phys, 0)
                {
                    ok = false;
                    break;
                }
            }
            let revoked = revoke_until_done(f.retype_2m_untyped).is_some();
            let mut freed = true;
            for i in 0..RETYPE_SIBLING_COUNT {
                let page_phys = f.retype_2m_phys + (i as u64) * PAGE_BYTES;
                if !retype_free_until_done(f.retype_2m_untyped, page_phys, 0) {
                    freed = false;
                }
            }
            revoked && freed && ok
        })
        .is_ok()
}

fn run_contended<F>(
    state: &mut RepeatState<'_>,
    fixture: &CapBenchFixture,
    n_cores: usize,
    mode: u64,
    mut body: F,
) -> bool
where
    F: FnMut(&mut RepeatState<'_>) -> bool,
{
    STOP_WORKERS.store(0, Ordering::Release);
    WORKER_MODE.store(mode, Ordering::Release);

    let mut started_count = 0usize;
    let mut start_ok = true;
    for c in 1..n_cores {
        WORKER_ERR[c].store(0, Ordering::Release);
        WORKER_DONE[c].store(0, Ordering::Release);
        WORKER_GO[c].store(1, Ordering::Release);
        let seen = WORKER_ITERS[c].load(Ordering::Acquire);
        if start_thread(fixture.worker_threads[c]) != operation::STATUS_OK {
            start_ok = false;
            break;
        }
        started_count = c;
        let progressed = (0..WAIT_SPINS).any(|_| {
            WORKER_ITERS[c].load(Ordering::Acquire) != seen
                || WORKER_ERR[c].load(Ordering::Acquire) != 0
        });
        if !progressed || WORKER_ERR[c].load(Ordering::Acquire) != 0 {
            start_ok = false;
            break;
        }
    }

    let body_ok = if start_ok { body(state) } else { false };

    STOP_WORKERS.store(1, Ordering::Release);
    let mut stop_ok = true;
    for c in 1..=started_count {
        let done = (0..WAIT_SPINS).any(|_| WORKER_DONE[c].load(Ordering::Acquire) == 1);
        if !done
            || !stopped(fixture.worker_threads[c])
            || WORKER_ERR[c].load(Ordering::Acquire) != 0
        {
            stop_ok = false;
        }
    }
    start_ok && body_ok && stop_ok
}

fn register_contended(registry: &mut Registry, fixture: &Rc<CapBenchFixture>) -> bool {
    for n in 2..=fixture.cores {
        let f_retype = Rc::clone(fixture);
        if registry
            .register(
                alloc::format!("Capability/Contended/Retype4K/{n}Cores"),
                move |state| {
                    state.declare_step("retype");
                    state.declare_step("teardown_ignore");
                    let untyped = WORKER_CONFIGS[0].contend_4k_untyped.load(Ordering::Relaxed);
                    let phys = WORKER_CONFIGS[0].contend_4k_phys.load(Ordering::Relaxed);
                    let slot = WORKER_CONFIGS[0].contend_4k_slot.load(Ordering::Relaxed);
                    run_contended(state, &f_retype, n, MODE_RETYPE, |state| {
                        while state.keep_running() {
                            if operation::retype_frame(untyped, phys, slot) != operation::STATUS_OK {
                                return false;
                            }
                            #[cfg(not(feature = "bench"))]
                            if operation::inspect(slot).is_err() {
                                return false;
                            }
                            state.next_step();
                            if operation::delete(slot) != operation::STATUS_OK
                                || !retype_free_until_done(untyped, phys, 0)
                            {
                                return false;
                            }
                            #[cfg(not(feature = "bench"))]
                            if operation::inspect(slot) != Err(operation::STATUS_REFUSED) {
                                return false;
                            }
                        }
                        true
                    })
                },
            )
            .is_err()
        {
            return false;
        }

        let f_move = Rc::clone(fixture);
        if registry
            .register(
                alloc::format!("Capability/Contended/MoveCrossProcess/{n}Cores"),
                move |state| {
                    state.declare_step("move");
                    state.declare_step("reset_ignore");
                    let proc_a = WORKER_CONFIGS[0].proc_a.load(Ordering::Relaxed);
                    let proc_b = WORKER_CONFIGS[0].proc_b.load(Ordering::Relaxed);
                    let slot_a = operation::through(proc_a, first_slot(0));
                    let slot_b = operation::through(proc_b, first_slot(0));
                    run_contended(state, &f_move, n, MODE_MOVE, |state| {
                        while state.keep_running() {
                            if operation::move_capability(slot_a, slot_b) != operation::STATUS_OK {
                                return false;
                            }
                            #[cfg(not(feature = "bench"))]
                            if operation::inspect(slot_a).is_ok()
                                || operation::inspect(slot_b).is_err()
                            {
                                return false;
                            }
                            state.next_step();
                            if operation::move_capability(slot_b, slot_a) != operation::STATUS_OK {
                                return false;
                            }
                            #[cfg(not(feature = "bench"))]
                            if operation::inspect(slot_b).is_ok()
                                || operation::inspect(slot_a).is_err()
                            {
                                return false;
                            }
                        }
                        true
                    })
                },
            )
            .is_err()
        {
            return false;
        }

        let f_revoke = Rc::clone(fixture);
        if registry
            .register(
                alloc::format!("Capability/Contended/Revoke/{n}Cores"),
                move |state| {
                    state.declare_step("setup_ignore");
                    state.declare_step("revoke");
                    let frame = WORKER_CONFIGS[0].revoke_frame.load(Ordering::Relaxed);
                    let phys = WORKER_CONFIGS[0].revoke_phys.load(Ordering::Relaxed);
                    run_contended(state, &f_revoke, n, MODE_REVOKE, |state| {
                        while state.keep_running() {
                            for i in 0..CONTEND_REVOKE_CAPS {
                                if operation::derive(frame, dom0_slot(i), RIGHT_READ, phys, 0)
                                    != operation::STATUS_OK
                                {
                                    return false;
                                }
                            }
                            state.next_step();
                            let Some(again) = revoke_until_done(frame) else {
                                return false;
                            };
                            #[cfg(not(feature = "bench"))]
                            {
                                let expected_again =
                                    ((CONTEND_REVOKE_CAPS / REVOKE_BUDGET) - 1) as u64;
                                if again != expected_again
                                    || operation::inspect(dom0_slot(0)).is_ok()
                                    || operation::inspect(dom0_slot(CONTEND_REVOKE_CAPS - 1))
                                        .is_ok()
                                {
                                    return false;
                                }
                            }
                            #[cfg(feature = "bench")]
                            let _ = again;
                        }
                        true
                    })
                },
            )
            .is_err()
        {
            return false;
        }
    }
    true
}

fn register_inspect_and_syscall(registry: &mut Registry, fixture: &Rc<CapBenchFixture>) -> bool {
    let inspect_cap = fixture.frame_cap;
    let inspect_phys = fixture.frame_phys;
    let empty_slot = fixture.empty_refused_slot;
    if registry
        .register_simple("Syscall/Inspect", move || {
            matches!(
                black_box(operation::inspect(inspect_cap)),
                Ok(cap) if cap.kind == operation::KIND_FRAME && cap.base == inspect_phys
            )
        })
        .is_err()
        || registry
            .register_simple("Syscall/Refused", move || {
                black_box(operation::inspect(empty_slot)) == Err(operation::STATUS_REFUSED)
            })
            .is_err()
        || registry
            .register_simple("Capability/Inspect/1Threads", move || {
                matches!(
                    black_box(operation::inspect(inspect_cap)),
                    Ok(cap) if cap.kind == operation::KIND_FRAME && cap.base == inspect_phys
                )
            })
            .is_err()
    {
        return false;
    }

    let f_cpu = Rc::clone(fixture);
    if registry
        .register("Capability/Inspect/CpuCountThreads", move |state| {
            run_contended(state, &f_cpu, f_cpu.cores, MODE_INSPECT, |state| {
                while state.keep_running() {
                    if !matches!(
                        black_box(operation::inspect(f_cpu.frame_cap)),
                        Ok(cap) if cap.kind == operation::KIND_FRAME && cap.base == f_cpu.frame_phys
                    ) {
                        return false;
                    }
                }
                true
            })
        })
        .is_err()
    {
        return false;
    }

    if registry
        .register("Thread/InspectConsumed/ThreadOnly", |state| {
            let mut prev = 0u64;
            while state.keep_running() {
                let Ok(cap) = operation::inspect(operation::ROOT_THREAD_SLOT) else {
                    return false;
                };
                let consumed = black_box(cap.consumed);
                if cap.kind != operation::KIND_THREAD || consumed == 0 || consumed < prev {
                    return false;
                }
                prev = consumed;
            }
            true
        })
        .is_err()
    {
        return false;
    }

    let f_conc = Rc::clone(fixture);
    registry
        .register("Thread/InspectConsumed/ConcurrentThreads", move |state| {
            let conc_slot = f_conc.conc_high_slot;
            let inspect_loop = |state: &mut RepeatState<'_>| -> bool {
                let Ok(first_cap) = operation::inspect(conc_slot) else {
                    return false;
                };
                let mut prev = first_cap.consumed;
                while state.keep_running() {
                    let Ok(cap) = operation::inspect(conc_slot) else {
                        return false;
                    };
                    let consumed = black_box(cap.consumed);
                    if cap.kind != operation::KIND_THREAD || consumed < prev {
                        return false;
                    }
                    prev = consumed;
                }
                CONC_HIGH_ITERS.load(Ordering::Acquire) > 0 && prev >= first_cap.consumed
            };
            if f_conc.cores >= 2 {
                let ok = run_contended(state, &f_conc, 2, MODE_CONC_SWITCH, inspect_loop);
                stopped(conc_slot) && ok
            } else {
                let before_iters = CONC_HIGH_ITERS.load(Ordering::Acquire);
                if start_thread(conc_slot) != operation::STATUS_OK
                    || !(0..WAIT_SPINS).any(|_| CONC_HIGH_ITERS.load(Ordering::Acquire) != before_iters)
                {
                    return false;
                }
                let ok = inspect_loop(state);
                stopped(conc_slot) && ok
            }
        })
        .is_ok()
}

fn register_derive_and_move(registry: &mut Registry, fixture: &Rc<CapBenchFixture>) -> bool {
    let f_derive = Rc::clone(fixture);
    if registry
        .register("Capability/DeriveDelete", move |state| {
            state.declare_step("derive");
            state.declare_step("delete");
            let target = dom0_slot(0);
            let mut ok = true;
            while state.keep_running() {
                if operation::derive(
                    f_derive.frame_cap,
                    target,
                    RIGHT_READ,
                    f_derive.frame_phys,
                    0,
                ) != operation::STATUS_OK
                {
                    ok = false;
                    break;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(target).is_err() {
                    ok = false;
                    break;
                }
                state.next_step();
                if operation::delete(target) != operation::STATUS_OK {
                    ok = false;
                    break;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(target) != Err(operation::STATUS_REFUSED) {
                    ok = false;
                    break;
                }
            }
            revoke_until_done(f_derive.frame_cap).is_some() && ok
        })
        .is_err()
    {
        return false;
    }

    let f_move = Rc::clone(fixture);
    registry
        .register("Capability/Move", move |state| {
            state.declare_primary_step();
            state.declare_step("reset_ignore");
            let slot_a = dom0_slot(0);
            let slot_b = dom0_slot(1);
            if operation::derive(f_move.frame_cap, slot_a, RIGHT_READ, f_move.frame_phys, 0)
                != operation::STATUS_OK
            {
                return false;
            }
            let mut ok = true;
            while state.keep_running() {
                if operation::move_capability(slot_a, slot_b) != operation::STATUS_OK {
                    ok = false;
                    break;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(slot_a).is_ok() || operation::inspect(slot_b).is_err() {
                    ok = false;
                    break;
                }
                state.next_step();
                if operation::move_capability(slot_b, slot_a) != operation::STATUS_OK {
                    ok = false;
                    break;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(slot_b).is_ok() || operation::inspect(slot_a).is_err() {
                    ok = false;
                    break;
                }
            }
            revoke_until_done(f_move.frame_cap).is_some() && ok
        })
        .is_ok()
}

fn register_retype_free_case<F>(
    registry: &mut Registry,
    name: &str,
    untyped_slot: u64,
    phys: u64,
    order: u64,
    retype_op: F,
) -> bool
where
    F: Fn(u64, u64, u64) -> bool + 'static,
{
    registry
        .register(name, move |state| {
            state.declare_step("retype");
            state.declare_step("delete");
            state.declare_step("retype_free");
            let target = dom0_slot(0);
            while state.keep_running() {
                if !retype_op(untyped_slot, phys, target) {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                if !matches!(
                    operation::inspect(target),
                    Ok(cap)
                        if cap.kind == operation::KIND_FRAME
                            && cap.base == phys
                            && cap.order == order
                ) {
                    return false;
                }
                state.next_step();
                if operation::delete(target) != operation::STATUS_OK {
                    return false;
                }
                state.next_step();
                if !retype_free_until_done(untyped_slot, phys, order) {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(target) != Err(operation::STATUS_REFUSED) {
                    return false;
                }
            }
            true
        })
        .is_ok()
}

fn register_retype_free(registry: &mut Registry, fixture: &CapBenchFixture) -> bool {
    register_retype_free_case(
        registry,
        "Capability/RetypeFree/Frame4K",
        fixture.untyped_slot,
        fixture.retype_4k_phys,
        0,
        |untyped, phys, target| operation::retype_frame(untyped, phys, target) == operation::STATUS_OK,
    ) && register_retype_free_case(
        registry,
        "Capability/RetypeFree/LargeFrame2M",
        fixture.untyped_slot,
        fixture.large_2m_phys,
        9,
        retype_large_frame_until_done,
    )
}

fn register_retype_destroy_case<F>(
    registry: &mut Registry,
    name: &str,
    untyped_slot: u64,
    pool_base: u64,
    stride: u64,
    expected_kind: u64,
    retype_op: F,
) -> bool
where
    F: Fn(u64, u64, u64) -> u64 + 'static,
{
    registry
        .register(name, move |state| {
            state.declare_step("retype");
            state.declare_step("destroy");
            state.declare_step("delete");
            let target = dom0_slot(0);
            let mut iter = 0u64;
            while state.keep_running() {
                if iter >= core_bench::POOL {
                    return false;
                }
                let phys = pool_base + iter * stride;
                iter += 1;
                if retype_op(untyped_slot, phys, target) != operation::STATUS_OK {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                if !matches!(
                    operation::inspect(target),
                    Ok(cap) if cap.kind == expected_kind && cap.base == phys
                ) {
                    return false;
                }
                state.next_step();
                if destroy_cap(target) != operation::STATUS_OK {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                if destroy_cap(target) != operation::STATUS_REFUSED {
                    return false;
                }
                state.next_step();
                if operation::delete(target) != operation::STATUS_OK {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                if operation::inspect(target) != Err(operation::STATUS_REFUSED) {
                    return false;
                }
            }
            #[cfg(feature = "bench")]
            let _ = expected_kind;
            true
        })
        .is_ok()
}

fn register_retype_destroy(registry: &mut Registry, fixture: &CapBenchFixture) -> bool {
    let bound_proc = fixture.dist_procs[0];
    register_retype_destroy_case(
        registry,
        "Capability/RetypeDestroy/Process",
        fixture.untyped_slot,
        fixture.retype_proc_base,
        PROCESS_BYTES,
        operation::KIND_PROCESS,
        retype_process,
    ) && register_retype_destroy_case(
        registry,
        "Capability/RetypeDestroy/Thread",
        fixture.untyped_slot,
        fixture.retype_thread_base,
        THREAD_BYTES,
        operation::KIND_THREAD,
        move |untyped, phys, target| retype_thread(untyped, phys, target, bound_proc),
    )
}

/// Sets up capability lifecycle, inspect, scaled, and contended fixtures and registers all benchmarks.
pub(crate) fn register(registry: &mut Registry) -> bool {
    let Some(fixture) = CapBenchFixture::init() else {
        return false;
    };
    let fixture = Rc::new(fixture);
    register_inspect_and_syscall(registry, &fixture)
        && register_derive_and_move(registry, &fixture)
        && register_revoke_sweeps(registry, &fixture)
        && register_delete_benchmarks(registry, &fixture)
        && register_retype_free(registry, &fixture)
        && register_retype_destroy(registry, &fixture)
        && register_populated_process_destroy(registry, &fixture)
        && register_retype_with_siblings(registry, &fixture)
        && register_contended(registry, &fixture)
}
