// SPDX-License-Identifier: MIT

//! MMU TLB reach, multi-order span map/remap-protect/unmap, 2M revoke+free teardown,
//! 64B shuffled pointer-chase, map/unmap/probe, cross-core TLB shootdown, 8192-page sweep,
//! map+read/write, and eager span lifecycle benchmarks mapped from Barrelfish `usr/bench`
//! (`largepage`, `vspace`, `mem_latency`; MIT) and Fuchsia `src/tests/microbenchmarks`
//! (`mmu.cc`, `vmar.cc`, `vmo.cc`; BSD-2-Clause; `design/synthetic-benchmark-suite/`) onto
//! Atmosphere's capability and `aeager` operations.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::hint::black_box;
use core::mem::{align_of, size_of};
use core::sync::atomic::{compiler_fence, Ordering};

use abench::runner::{Registry, RepeatState};
use asys::operation;

use crate::{
    cap_bench, core_bench, dom0_child_count, first_slot, window_clear, ARGUMENT_WORDS,
    EAGER_WINDOW, FIRST_LEAF_END, HEAP_WINDOW, LARGE_FRAME_BYTES, LARGE_FRAME_PAGES, LEAF_BYTES,
    MAX_ORDER, PROCESS_ORDER, RIGHT_EXECUTE, RIGHT_READ, ROOT_ENTRIES, TABLE_PAGE_BYTES,
    THREAD_BYTES,
};

const PAGE_BYTES: u64 = 4096;
const PROCESS_BYTES: u64 = PAGE_BYTES << PROCESS_ORDER;

/// Physical offset into the 1 GiB untyped where this suite allocates its 38 MiB working pool,
/// clear of the bottom 2 MiB check block and the upper 512 MiB checks/heap region.
const POOL_OFFSET_BYTES: u64 = 64 * 1024 * 1024;

/// Physical offset into the 1 GiB untyped where the extended MMU/eager benchmarks allocate their
/// 46 MiB working pool (`[384 MiB .. 430 MiB)`), clear of `cap_bench`'s `[128 .. 384 MiB]` pool
/// and `flush_cost`'s `[512 .. 1024 MiB)` top region.
const EXT_POOL_OFFSET_BYTES: u64 = 384 * 1024 * 1024;

/// First root capability table entry probed for placing this suite's single table leaf.
pub(crate) const BENCH_CAP_ENTRY_START: u64 = 32;

/// Distinct level-4 user address windows used by the 4K, 2M, span, map/unmap, sweep, probe, and
/// eager span lifecycle benchmarks (`ring_bench` and `ump_bench` occupy `19 << 39` and `20 << 39`).
pub(crate) const BENCH_4K_WINDOW: u64 = 16 << 39;
pub(crate) const BENCH_2M_WINDOW: u64 = 17 << 39;
pub(crate) const BENCH_SPAN_WINDOW: u64 = 18 << 39;
const BENCH_SPAN_4K_BASE: u64 = BENCH_SPAN_WINDOW;
const BENCH_SPAN_2M_BASE: u64 = BENCH_SPAN_WINDOW + LARGE_FRAME_BYTES;

const BENCH_MMU_WINDOW: u64 = 23 << 39;
const BENCH_MAP_UNMAP_4K_VA: u64 = BENCH_MMU_WINDOW;
const BENCH_MAP_RW_4K_VA: u64 = BENCH_MMU_WINDOW + PAGE_BYTES;
const BENCH_SCAN_VA: u64 = BENCH_MMU_WINDOW + 2 * PAGE_BYTES;
const BENCH_SYNC_VA: u64 = BENCH_MMU_WINDOW + 3 * PAGE_BYTES;
const BENCH_MAP_UNMAP_2M_VA: u64 = BENCH_MMU_WINDOW + LARGE_FRAME_BYTES;
const BENCH_MAP_RW_2M_VA: u64 = BENCH_MMU_WINDOW + 2 * LARGE_FRAME_BYTES;

const BENCH_MANY_WINDOW: u64 = 24 << 39;
const BENCH_PROBE_WINDOW: u64 = 25 << 39;
const EAGER_BENCH_WINDOW: u64 = 26 << 39;

const CHILD_BASE_VA: u64 = 2 << 39;
const CHILD_CODE_VA: u64 = CHILD_BASE_VA;
const CHILD_SYNC_VA: u64 = CHILD_BASE_VA + 2 * PAGE_BYTES;
const CHILD_REMOTE_VA: u64 = CHILD_BASE_VA + 3 * PAGE_BYTES;

const OTHER_EAGER_WINDOWS: [u64; 10] = [
    EAGER_WINDOW,
    HEAP_WINDOW,
    BENCH_4K_WINDOW,
    BENCH_2M_WINDOW,
    BENCH_SPAN_WINDOW,
    19 << 39,
    20 << 39,
    BENCH_MMU_WINDOW,
    BENCH_MANY_WINDOW,
    BENCH_PROBE_WINDOW,
];

/// Working-set size for `Mmu/TlbReach/{4K,2M}/{Seq,Random}/16M`: 8 x 2M = 4096 x 4K pages.
const TLB_REACH_LARGE_FRAMES: usize = 8;
const TLB_REACH_4K_PAGES: usize = TLB_REACH_LARGE_FRAMES * (LARGE_FRAME_PAGES as usize);

/// Sweep size for `Mmu/ManyMappingsReadWriteUnmap/8192`: 16 x 2M = 8192 x 4K pages.
const MANY_LARGE_FRAMES: usize = 16;
const MANY_PAGES: usize = MANY_LARGE_FRAMES * (LARGE_FRAME_PAGES as usize);

/// Entry count for `Mmu/Probe/64`.
const PROBE_COUNT: u64 = operation::PROBE_MAX;

/// Pages given to the child untyped of `Span/EagerReserveBackRelease` (order 6 = 64 pages).
const EAGER_BENCH_ORDER: u64 = 6;
const EAGER_BENCH_PAGES: usize = 1 << EAGER_BENCH_ORDER;

/// Number of `retype_large_frame` retries allowed before treating zeroing as stalled.
const RETYPE_LARGE_AGAIN_MAX: u64 = LARGE_FRAME_PAGES + 1;
const REVOKE_AGAIN_MAX: u64 = 64;
const FREE_AGAIN_MAX: u64 = 64;
const SHOOTDOWN_AGAIN_MAX: u64 = 1 << 20;
const REMOTE_WAIT_SPINS: u64 = 1 << 26;

/// Cache-line node size and chase hops per timed `keep_running()` iteration.
const CHASE_NODE_BYTES: usize = 64;
const CHASE_HOPS_PER_ITER: usize = 4096;
const CHASE_UNROLL: usize = 16;

#[repr(C, align(64))]
struct ChaseNode {
    next: *const ChaseNode,
    scratch: u64,
    _pad: [u64; 6],
}

const _: () = assert!(size_of::<ChaseNode>() == CHASE_NODE_BYTES);
const _: () = assert!(align_of::<ChaseNode>() == CHASE_NODE_BYTES);
const _: () = assert!(CHASE_HOPS_PER_ITER.is_multiple_of(CHASE_UNROLL));

#[derive(Clone, Copy)]
struct RemoteCoreFixture {
    loaded_proc: u64,
    unloaded_proc: u64,
    scratch_slot: u64,
    scratch_phys: u64,
}

#[derive(Clone, Copy)]
struct MmuBenchFixture {
    untyped_slot: u64,
    span_rw_slot: u64,
    span_ro_slot: u64,
    teardown_2m_slot: u64,
    teardown_2m_phys: u64,
    map_unmap_4k_slot: u64,
    map_unmap_2m_slot: u64,
    map_rw_4k_slot: u64,
    map_rw_2m_slot: u64,
    many_slots_base: u64,
    eager_untyped_slot: u64,
    eager_slots_start: u64,
    eager_mem_phys: u64,
    remote: Option<RemoteCoreFixture>,
}

pub(crate) fn find_gigabyte_untyped() -> Option<(u64, operation::Capability)> {
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

pub(crate) fn retype_large_frame_until_done(untyped: u64, base: u64, destination: u64) -> bool {
    for _ in 0..RETYPE_LARGE_AGAIN_MAX {
        match operation::retype_large_frame(untyped, base, destination) {
            operation::STATUS_OK => return true,
            operation::STATUS_AGAIN => {}
            _ => return false,
        }
    }
    false
}

fn revoke_until_done(slot: u64) -> bool {
    for _ in 0..REVOKE_AGAIN_MAX {
        // Safety: callers ensure no active pointer into mappings derived from `slot` is used after revoke.
        match unsafe { operation::revoke(slot) } {
            operation::STATUS_OK => return true,
            operation::STATUS_AGAIN => {}
            _ => return false,
        }
    }
    false
}

fn retype_free_once(untyped: u64, base: u64, order: u64) -> u64 {
    // Safety: freeing a dead physical block changes no live mapping in the caller's address space.
    operation::status(unsafe {
        operation::invoke(
            operation::RETYPE,
            untyped,
            [operation::RETYPE_FREE, base, 0, order, 0],
        )
    })
}

fn retype_free_until_done(untyped: u64, base: u64, order: u64) -> bool {
    for _ in 0..FREE_AGAIN_MAX {
        match retype_free_once(untyped, base, order) {
            operation::STATUS_OK => return true,
            operation::STATUS_AGAIN => {}
            _ => return false,
        }
    }
    false
}

pub(crate) fn alloc_and_link_table(untyped: u64, next_table: &mut u64, va: u64, level: u64) -> bool {
    alloc_and_link_proc_table(operation::ROOT_PROCESS_SLOT, untyped, next_table, va, level)
}

fn alloc_and_link_proc_table(
    process: u64,
    untyped: u64,
    next_table: &mut u64,
    va: u64,
    level: u64,
) -> bool {
    let base = cap_bench::align_up(*next_table, TABLE_PAGE_BYTES);
    *next_table = base + TABLE_PAGE_BYTES;
    operation::retype_table_page(untyped, base, level) == operation::STATUS_OK
        && operation::link(process, va, level + 1, untyped, base) == operation::STATUS_OK
}

fn alloc_empty_leaf(untyped: u64, leaf_phys: u64) -> Option<u64> {
    for entry in BENCH_CAP_ENTRY_START..ROOT_ENTRIES {
        if matches!(operation::inspect(first_slot(entry)), Err(operation::STATUS_REFUSED))
            && operation::retype_leaf(untyped, leaf_phys, entry) == operation::STATUS_OK
        {
            return Some(entry);
        }
    }
    None
}

fn link_table_range(process: u64, untyped: u64, cursor: &mut u64, window: u64, l1_tables: usize) -> bool {
    if !alloc_and_link_proc_table(process, untyped, cursor, window, 3)
        || !alloc_and_link_proc_table(process, untyped, cursor, window, 2)
    {
        return false;
    }
    for m in 0..(l1_tables as u64) {
        if !alloc_and_link_proc_table(process, untyped, cursor, window + m * LARGE_FRAME_BYTES, 1) {
            return false;
        }
    }
    true
}

fn find_image_page(scan_va: u64, page: u64) -> Option<(u64, u64)> {
    let mut slot = operation::ROOT_FRAME_SLOT;
    while let Ok(frame) = operation::inspect(slot) {
        if frame.kind != operation::KIND_FRAME {
            return None;
        }
        if frame.rights & RIGHT_EXECUTE != 0 {
            for k in 0..(1u64 << frame.order) {
                if operation::map(operation::ROOT_PROCESS_SLOT, scan_va, 1, slot, k)
                    != operation::STATUS_OK
                {
                    return None;
                }
                // Safety: `scan_va` maps page `k` of `slot` and `page` is an executable page of dom0.
                let same = unsafe {
                    core::slice::from_raw_parts(scan_va as *const u8, PAGE_BYTES as usize)
                        == core::slice::from_raw_parts(page as *const u8, PAGE_BYTES as usize)
                };
                if unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, scan_va, 1) }.is_err() {
                    return None;
                }
                if same {
                    return Some((slot, k));
                }
            }
        }
        slot += 1;
    }
    None
}

fn derive_child_untyped(untyped: u64, destination: u64, rights: u64, base: u64, order: u64) -> u64 {
    // Deriving a child untyped modifies capability tables only, never virtual mappings.
    operation::status(unsafe {
        operation::invoke(operation::DERIVE, untyped, [destination, rights, base, order, 0])
    })
}

fn init_remote_fixture(
    untyped: u64,
    cursor: &mut u64,
    first: u64,
    scratch_phys: u64,
) -> Option<RemoteCoreFixture> {
    if core_bench::core_count() < 2 {
        return None;
    }
    let loaded_proc = first + 40;
    let loaded_thread = first + 41;
    let loaded_sync = first + 42;
    let unloaded_proc = first + 43;
    let scratch_slot = first + 44;

    let proc_phys = cap_bench::align_up(*cursor, PROCESS_BYTES);
    *cursor = proc_phys + PROCESS_BYTES;
    let unloaded_proc_phys = cap_bench::align_up(*cursor, PROCESS_BYTES);
    *cursor = unloaded_proc_phys + PROCESS_BYTES;
    let thread_phys = cap_bench::align_up(*cursor, THREAD_BYTES);
    *cursor = thread_phys + THREAD_BYTES;
    let sync_phys = cap_bench::align_up(*cursor, PAGE_BYTES);
    *cursor = sync_phys + PAGE_BYTES;

    if cap_bench::retype_process(untyped, proc_phys, loaded_proc) != operation::STATUS_OK
        || cap_bench::retype_process(untyped, unloaded_proc_phys, unloaded_proc)
            != operation::STATUS_OK
        || !link_table_range(loaded_proc, untyped, cursor, CHILD_BASE_VA, 1)
        || !link_table_range(unloaded_proc, untyped, cursor, CHILD_BASE_VA, 1)
        || operation::retype_frame(untyped, sync_phys, loaded_sync) != operation::STATUS_OK
    {
        return None;
    }

    let count_fn = dom0_child_count as *const () as u64;
    let (img_slot, img_page) = find_image_page(BENCH_SCAN_VA, count_fn & !0xfff)?;
    if operation::map(loaded_proc, CHILD_CODE_VA, 1, img_slot, img_page) != operation::STATUS_OK
        || operation::map(loaded_proc, CHILD_SYNC_VA, 1, loaded_sync, 0) != operation::STATUS_OK
        || operation::map(operation::ROOT_PROCESS_SLOT, BENCH_SYNC_VA, 1, loaded_sync, 0)
            != operation::STATUS_OK
    {
        return None;
    }

    if cap_bench::retype_thread(untyped, thread_phys, loaded_thread, loaded_proc)
        != operation::STATUS_OK
        || cap_bench::set_frame_word(
            loaded_thread,
            operation::PC_WORD,
            CHILD_CODE_VA + (count_fn & 0xfff),
        ) != operation::STATUS_OK
        || cap_bench::set_frame_word(loaded_thread, ARGUMENT_WORDS[0], CHILD_SYNC_VA)
            != operation::STATUS_OK
        || cap_bench::place_thread(loaded_thread, operation::ROOT_CORE_SLOT + 1, 0)
            != operation::STATUS_OK
        || cap_bench::start_thread(loaded_thread) != operation::STATUS_OK
    {
        return None;
    }

    // Wait until core 1 enters `loaded_proc`'s address space and bumps `*sync_ptr`, then suspend
    // the worker so core 1 returns to idle for subsequent suites while `loaded_proc` remains listed.
    let sync_ptr = BENCH_SYNC_VA as *const u64;
    let seen = (0..REMOTE_WAIT_SPINS).any(|_| unsafe { sync_ptr.read_volatile() } != 0);
    if !seen || !cap_bench::stopped(loaded_thread) {
        return None;
    }

    Some(RemoteCoreFixture {
        loaded_proc,
        unloaded_proc,
        scratch_slot,
        scratch_phys,
    })
}

impl MmuBenchFixture {
    fn init() -> Option<Self> {
        let all_windows = [
            EAGER_WINDOW,
            HEAP_WINDOW,
            BENCH_4K_WINDOW,
            BENCH_2M_WINDOW,
            BENCH_SPAN_WINDOW,
            BENCH_MMU_WINDOW,
            BENCH_MANY_WINDOW,
            BENCH_PROBE_WINDOW,
            EAGER_BENCH_WINDOW,
        ];
        for (idx, &win) in all_windows[2..8].iter().enumerate() {
            let mut others = [0u64; 8];
            let mut out = 0usize;
            for (j, &cand) in all_windows.iter().enumerate() {
                if j != idx + 2 {
                    others[out] = cand;
                    out += 1;
                }
            }
            if !window_clear(win, &others) {
                return None;
            }
        }

        let (untyped_slot, block) = find_gigabyte_untyped()?;
        let block_end = block.base + (PAGE_BYTES << block.order);
        let region = block.base + POOL_OFFSET_BYTES;
        if block_end.saturating_sub(region) < 19 * LARGE_FRAME_BYTES {
            return None;
        }
        let ext_base = block.base + EXT_POOL_OFFSET_BYTES;
        if block_end.saturating_sub(ext_base) < 23 * LARGE_FRAME_BYTES {
            return None;
        }

        let leaf_phys = region + 18 * LARGE_FRAME_BYTES;
        let cap_entry = alloc_empty_leaf(untyped_slot, leaf_phys)?;
        let first = first_slot(cap_entry);

        let mut next_table = leaf_phys + TABLE_PAGE_BYTES;
        if !link_table_range(
            operation::ROOT_PROCESS_SLOT,
            untyped_slot,
            &mut next_table,
            BENCH_4K_WINDOW,
            TLB_REACH_LARGE_FRAMES,
        ) || !link_table_range(
            operation::ROOT_PROCESS_SLOT,
            untyped_slot,
            &mut next_table,
            BENCH_2M_WINDOW,
            0,
        ) || !link_table_range(
            operation::ROOT_PROCESS_SLOT,
            untyped_slot,
            &mut next_table,
            BENCH_SPAN_WINDOW,
            1,
        ) {
            return None;
        }

        // Retype and map 8 x 2M blocks as 4096 x 4K pages in `BENCH_4K_WINDOW`.
        for m in 0..(TLB_REACH_LARGE_FRAMES as u64) {
            let slot = first + m;
            let phys = region + m * LARGE_FRAME_BYTES;
            if !retype_large_frame_until_done(untyped_slot, phys, slot) {
                return None;
            }
            for p in 0..LARGE_FRAME_PAGES {
                let va = BENCH_4K_WINDOW + (m * LARGE_FRAME_PAGES + p) * PAGE_BYTES;
                if operation::map(operation::ROOT_PROCESS_SLOT, va, 1, slot, p)
                    != operation::STATUS_OK
                {
                    return None;
                }
            }
        }

        // Retype and map 8 x 2M blocks as 8 x 2M large pages in `BENCH_2M_WINDOW`.
        for m in 0..(TLB_REACH_LARGE_FRAMES as u64) {
            let slot = first + (TLB_REACH_LARGE_FRAMES as u64) + m;
            let phys = region + ((TLB_REACH_LARGE_FRAMES as u64) + m) * LARGE_FRAME_BYTES;
            if !retype_large_frame_until_done(untyped_slot, phys, slot) {
                return None;
            }
            let va = BENCH_2M_WINDOW + m * LARGE_FRAME_BYTES;
            if operation::map(operation::ROOT_PROCESS_SLOT, va, 2, slot, 0) != operation::STATUS_OK
            {
                return None;
            }
        }

        let span_rw_slot = first + 16;
        let span_ro_slot = first + 17;
        let span_phys = region + 16 * LARGE_FRAME_BYTES;
        if !retype_large_frame_until_done(untyped_slot, span_phys, span_rw_slot)
            || operation::derive(span_rw_slot, span_ro_slot, RIGHT_READ, span_phys, 9)
                != operation::STATUS_OK
        {
            return None;
        }

        let teardown_2m_slot = first + 18;
        let teardown_2m_phys = region + 17 * LARGE_FRAME_BYTES;

        // Extended pool (`[384 MiB .. 430 MiB)`) for Fuchsia-mapped MMU and eager span suites.
        let many_slots_base = first + 24;
        let map_unmap_4k_slot = first + 19;
        let map_unmap_2m_slot = first + 20;
        let probe_2m_slot = first + 21;
        let map_rw_4k_slot = first + 22;
        let map_rw_2m_slot = first + 23;

        let map_unmap_2m_phys = ext_base + (MANY_LARGE_FRAMES as u64) * LARGE_FRAME_BYTES;
        let map_rw_2m_phys = ext_base + ((MANY_LARGE_FRAMES as u64) + 1) * LARGE_FRAME_BYTES;
        let probe_2m_phys = ext_base + ((MANY_LARGE_FRAMES as u64) + 2) * LARGE_FRAME_BYTES;
        let remote_scratch_phys = ext_base + ((MANY_LARGE_FRAMES as u64) + 3) * LARGE_FRAME_BYTES;

        let mut ext_cursor = ext_base + ((MANY_LARGE_FRAMES as u64) + 4) * LARGE_FRAME_BYTES;
        let eager_mem_phys = ext_base + ((MANY_LARGE_FRAMES as u64) + 6) * LARGE_FRAME_BYTES;
        let eager_leaf_phys = eager_mem_phys - LEAF_BYTES;

        if !link_table_range(
            operation::ROOT_PROCESS_SLOT,
            untyped_slot,
            &mut ext_cursor,
            BENCH_MMU_WINDOW,
            1,
        ) || !link_table_range(
            operation::ROOT_PROCESS_SLOT,
            untyped_slot,
            &mut ext_cursor,
            BENCH_MANY_WINDOW,
            MANY_LARGE_FRAMES,
        ) || !link_table_range(
            operation::ROOT_PROCESS_SLOT,
            untyped_slot,
            &mut ext_cursor,
            BENCH_PROBE_WINDOW,
            1,
        ) {
            return None;
        }

        // Retype and map 16 x 2M blocks as 8192 x 4K pages in `BENCH_MANY_WINDOW`.
        for m in 0..(MANY_LARGE_FRAMES as u64) {
            let slot = many_slots_base + m;
            let phys = ext_base + m * LARGE_FRAME_BYTES;
            if !retype_large_frame_until_done(untyped_slot, phys, slot) {
                return None;
            }
            for p in 0..LARGE_FRAME_PAGES {
                let va = BENCH_MANY_WINDOW + (m * LARGE_FRAME_PAGES + p) * PAGE_BYTES;
                if operation::map(operation::ROOT_PROCESS_SLOT, va, 1, slot, p)
                    != operation::STATUS_OK
                {
                    return None;
                }
            }
        }

        // Retype 2M frames for `Mmu/MapUnmap/2M`, `Mmu/MapReadWrite/2M`, and `Mmu/Probe/64`.
        if !retype_large_frame_until_done(untyped_slot, map_unmap_2m_phys, map_unmap_2m_slot)
            || !retype_large_frame_until_done(untyped_slot, map_rw_2m_phys, map_rw_2m_slot)
            || !retype_large_frame_until_done(untyped_slot, probe_2m_phys, probe_2m_slot)
        {
            return None;
        }
        for p in 0..PROBE_COUNT {
            let va = BENCH_PROBE_WINDOW + p * PAGE_BYTES;
            if operation::map(operation::ROOT_PROCESS_SLOT, va, 1, probe_2m_slot, p)
                != operation::STATUS_OK
            {
                return None;
            }
        }

        // Retype 4K frames for `Mmu/MapUnmap/4K` and `Mmu/MapReadWrite/4K`.
        let map_unmap_4k_phys = ext_cursor;
        ext_cursor += PAGE_BYTES;
        let map_rw_4k_phys = ext_cursor;
        ext_cursor += PAGE_BYTES;
        if operation::retype_frame(untyped_slot, map_unmap_4k_phys, map_unmap_4k_slot)
            != operation::STATUS_OK
            || operation::retype_frame(untyped_slot, map_rw_4k_phys, map_rw_4k_slot)
                != operation::STATUS_OK
        {
            return None;
        }

        // Eager span benchmark leaf and order-6 child untyped (64 pages).
        let eager_entry = alloc_empty_leaf(untyped_slot, eager_leaf_phys)?;
        let eager_untyped_slot = first_slot(eager_entry);
        let eager_slots_start = eager_untyped_slot + 1;
        if derive_child_untyped(
            untyped_slot,
            eager_untyped_slot,
            block.rights,
            eager_mem_phys,
            EAGER_BENCH_ORDER,
        ) != operation::STATUS_OK
        {
            return None;
        }

        let remote = init_remote_fixture(
            untyped_slot,
            &mut ext_cursor,
            first,
            remote_scratch_phys,
        );
        if core_bench::core_count() >= 2 && remote.is_none() {
            return None;
        }
        if ext_cursor > eager_leaf_phys {
            return None;
        }

        Some(Self {
            untyped_slot,
            span_rw_slot,
            span_ro_slot,
            teardown_2m_slot,
            teardown_2m_phys,
            map_unmap_4k_slot,
            map_unmap_2m_slot,
            map_rw_4k_slot,
            map_rw_2m_slot,
            many_slots_base,
            eager_untyped_slot,
            eager_slots_start,
            eager_mem_phys,
            remote,
        })
    }
}

#[inline]
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

#[inline]
const fn tlb_page_byte_offset(page: usize) -> usize {
    // Stagger cache-line offsets across pages so 4K strides spread over all L1D sets.
    (page << 12) + ((page & 63) << 6)
}

#[inline]
const fn tlb_page_pattern(page: usize) -> u64 {
    (page as u64)
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(1)
}

fn init_tlb_buffer(base_addr: u64) -> u64 {
    let base = base_addr as *mut u8;
    let mut expected_sum = 0u64;
    for p in 0..TLB_REACH_4K_PAGES {
        let val = tlb_page_pattern(p);
        expected_sum = expected_sum.wrapping_add(val);
        // Safety: `base_addr` maps all 16 MiB (`TLB_REACH_4K_PAGES` 4K pages) RW in dom0's space.
        unsafe {
            base.add(tlb_page_byte_offset(p))
                .cast::<u64>()
                .write_volatile(val);
        }
    }
    expected_sum
}

fn tlb_offsets(random: bool, mut seed: u64) -> Vec<u32> {
    let mut offsets = Vec::with_capacity(TLB_REACH_4K_PAGES);
    for p in 0..TLB_REACH_4K_PAGES {
        offsets.push(tlb_page_byte_offset(p) as u32);
    }
    if random {
        for i in (1..offsets.len()).rev() {
            let j = (splitmix64(&mut seed) as usize) % (i + 1);
            offsets.swap(i, j);
        }
    }
    offsets
}

fn register_tlb_reach(
    registry: &mut Registry,
    name: &str,
    base_addr: u64,
    random: bool,
    seed: u64,
) -> bool {
    registry
        .register(name, move |state| {
            let expected_sum = init_tlb_buffer(base_addr);
            let offsets = tlb_offsets(random, seed);
            let base = base_addr as *const u8;
            while state.keep_running() {
                let mut sum = 0u64;
                for &off in &offsets {
                    // Safety: `off` is within the 16 MiB RW-mapped region at `base`.
                    let word = unsafe { base.add(off as usize).cast::<u64>().read_volatile() };
                    sum = sum.wrapping_add(word);
                }
                if black_box(sum) != expected_sum {
                    return false;
                }
            }
            true
        })
        .is_ok()
}

fn map_span(base_va: u64, pages: usize, frame_slot: u64) -> bool {
    for k in 0..pages {
        let va = base_va + (k as u64) * PAGE_BYTES;
        if operation::map(operation::ROOT_PROCESS_SLOT, va, 1, frame_slot, k as u64)
            != operation::STATUS_OK
        {
            return false;
        }
    }
    true
}

fn unmap_span(base_va: u64, pages: usize) -> bool {
    for k in 0..pages {
        let va = base_va + (k as u64) * PAGE_BYTES;
        // Safety: nothing outside this span check reads `base_va..base_va + pages * 4096`.
        if unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, va, 1) }.is_err() {
            return false;
        }
    }
    true
}

fn register_span_bench(
    registry: &mut Registry,
    name: &str,
    pages: usize,
    rw_slot: u64,
    ro_slot: u64,
) -> bool {
    registry
        .register(name, move |state| {
            state.declare_step("map");
            state.declare_step("remap_protect");
            state.declare_step("unmap");
            while state.keep_running() {
                if !map_span(BENCH_SPAN_4K_BASE, pages, rw_slot) {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    if operation::map(
                        operation::ROOT_PROCESS_SLOT,
                        BENCH_SPAN_4K_BASE,
                        1,
                        rw_slot,
                        0,
                    ) != operation::STATUS_REFUSED
                    {
                        return false;
                    }
                    let first_ptr = BENCH_SPAN_4K_BASE as *mut u64;
                    let last_ptr = (BENCH_SPAN_4K_BASE + (pages as u64) * PAGE_BYTES - 8)
                        as *mut u64;
                    // Safety: both offsets are within the RW span just mapped through `rw_slot`.
                    unsafe {
                        first_ptr.write_volatile(0x5a5a_0001_u64);
                        last_ptr.write_volatile(0x5a5a_0002_u64 ^ (pages as u64));
                    }
                }
                state.next_step();

                if !unmap_span(BENCH_SPAN_4K_BASE, pages)
                    || !map_span(BENCH_SPAN_4K_BASE, pages, ro_slot)
                {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    let first_ptr = BENCH_SPAN_4K_BASE as *const u64;
                    let last_ptr = (BENCH_SPAN_4K_BASE + (pages as u64) * PAGE_BYTES - 8)
                        as *const u64;
                    // Safety: both pages are mapped RO over the same backing frame pages.
                    let (first_val, last_val) =
                        unsafe { (first_ptr.read_volatile(), last_ptr.read_volatile()) };
                    if first_val != 0x5a5a_0001_u64 || last_val != (0x5a5a_0002_u64 ^ (pages as u64))
                    {
                        return false;
                    }
                }
                state.next_step();

                if !unmap_span(BENCH_SPAN_4K_BASE, pages) {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    if unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, BENCH_SPAN_4K_BASE, 1) }
                        != Err(operation::STATUS_REFUSED)
                    {
                        return false;
                    }
                }
            }
            true
        })
        .is_ok()
}

fn register_map_revoke_teardown_2m(registry: &mut Registry, fixture: MmuBenchFixture) -> bool {
    registry
        .register("Mmu/MapRevokeTeardown/2M", move |state| {
            state.declare_step("setup_ignore");
            state.declare_step("map");
            state.declare_step("revoke");
            state.declare_step("retype_free");
            while state.keep_running() {
                if !retype_large_frame_until_done(
                    fixture.untyped_slot,
                    fixture.teardown_2m_phys,
                    fixture.teardown_2m_slot,
                ) {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    if !matches!(
                        operation::inspect(fixture.teardown_2m_slot),
                        Ok(cap)
                            if cap.kind == operation::KIND_FRAME
                                && cap.base == fixture.teardown_2m_phys
                                && cap.order == 9
                    ) {
                        return false;
                    }
                }
                state.next_step();

                if operation::map(
                    operation::ROOT_PROCESS_SLOT,
                    BENCH_SPAN_2M_BASE,
                    2,
                    fixture.teardown_2m_slot,
                    0,
                ) != operation::STATUS_OK
                {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    if unsafe {
                        operation::unmap(operation::ROOT_PROCESS_SLOT, BENCH_SPAN_2M_BASE, 2)
                    } != Err(operation::STATUS_REFUSED)
                    {
                        return false;
                    }
                    let first_ptr = BENCH_SPAN_2M_BASE as *mut u64;
                    let last_ptr =
                        (BENCH_SPAN_2M_BASE + LARGE_FRAME_BYTES - 8) as *mut u64;
                    // Safety: level-2 mapping spans the 2 MiB RW frame zeroed by `retype_large_frame`.
                    let (z0, z1) = unsafe {
                        let a = first_ptr.read_volatile();
                        let b = last_ptr.read_volatile();
                        first_ptr.write_volatile(0xdead_beef_cafe_0001);
                        last_ptr.write_volatile(0xdead_beef_cafe_0002);
                        (a | b, (first_ptr.read_volatile(), last_ptr.read_volatile()))
                    };
                    if z0 != 0 || z1 != (0xdead_beef_cafe_0001, 0xdead_beef_cafe_0002) {
                        return false;
                    }
                }
                state.next_step();

                if !revoke_until_done(fixture.teardown_2m_slot) {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    if retype_free_once(fixture.untyped_slot, fixture.teardown_2m_phys, 9)
                        != operation::STATUS_REFUSED
                    {
                        return false;
                    }
                }
                state.next_step();

                if operation::delete(fixture.teardown_2m_slot) != operation::STATUS_OK
                    || !retype_free_until_done(fixture.untyped_slot, fixture.teardown_2m_phys, 9)
                {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    if operation::inspect(fixture.teardown_2m_slot).is_ok()
                        || retype_free_once(fixture.untyped_slot, fixture.teardown_2m_phys, 9)
                            != operation::STATUS_REFUSED
                    {
                        return false;
                    }
                }
            }
            true
        })
        .is_ok()
}

fn build_pointer_chase(base_addr: u64, bytes: usize, mut seed: u64) -> Option<*const ChaseNode> {
    let count = bytes / CHASE_NODE_BYTES;
    if count == 0 {
        return None;
    }
    let base = base_addr as *mut ChaseNode;
    for i in 0..count {
        // Safety: `base_addr..base_addr + bytes` lies within the 16 MiB RW-mapped benchmark window.
        unsafe {
            (*base.add(i)).scratch = i as u64;
        }
    }
    for i in (1..count).rev() {
        let j = (splitmix64(&mut seed) as usize) % (i + 1);
        // Safety: `i` and `j` are distinct or equal indices within `0..count`.
        unsafe {
            let tmp = (*base.add(i)).scratch;
            (*base.add(i)).scratch = (*base.add(j)).scratch;
            (*base.add(j)).scratch = tmp;
        }
    }
    for k in 0..count {
        // Safety: every `scratch` element holds a unique index in `0..count`.
        unsafe {
            let cur = (*base.add(k)).scratch as usize;
            let nxt = (*base.add((k + 1) % count)).scratch as usize;
            (*base.add(cur)).next = base.add(nxt);
        }
    }
    // Safety: `base` holds `count >= 1` initialized `ChaseNode` entries.
    let start = unsafe { base.add((*base.add(0)).scratch as usize) } as *const ChaseNode;
    #[cfg(not(feature = "bench"))]
    {
        let mut probe = start;
        for step in 1..=count {
            // Safety: every `next` in the permutation points to another `ChaseNode` in `0..count`.
            probe = unsafe { (*probe).next };
            if step < count && probe == start {
                return None;
            }
        }
        if probe != start {
            return None;
        }
    }
    Some(start)
}

#[inline(never)]
fn chase_4096(mut p: *const ChaseNode) -> *const ChaseNode {
    for _ in 0..(CHASE_HOPS_PER_ITER / CHASE_UNROLL) {
        // Safety: caller verified `p` belongs to a closed `ChaseNode` Hamiltonian cycle.
        unsafe {
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
            p = core::ptr::read_volatile(&(*p).next);
        }
    }
    p
}

fn register_pointer_chase(
    registry: &mut Registry,
    name: &str,
    base_addr: u64,
    bytes: usize,
    seed: u64,
) -> bool {
    registry
        .register(name, move |state| {
            let Some(mut cur) = build_pointer_chase(base_addr, bytes, seed) else {
                return false;
            };
            let start_addr = base_addr as usize;
            let end_addr = start_addr + bytes;
            while state.keep_running() {
                cur = chase_4096(cur);
                let addr = black_box(cur) as usize;
                if addr < start_addr || addr >= end_addr {
                    return false;
                }
            }
            true
        })
        .is_ok()
}

fn register_map_unmap(registry: &mut Registry, fixture: MmuBenchFixture) -> bool {
    let slot_4k = fixture.map_unmap_4k_slot;
    if registry
        .register("Mmu/MapUnmap/4K", move |state| {
            #[cfg(not(feature = "bench"))]
            {
                if operation::map(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_4K_VA, 1, slot_4k, 0)
                    != operation::STATUS_OK
                    || operation::map(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_4K_VA, 1, slot_4k, 0)
                        != operation::STATUS_REFUSED
                    || unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_4K_VA, 1) }
                        .is_err()
                    || unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_4K_VA, 1) }
                        != Err(operation::STATUS_REFUSED)
                {
                    return false;
                }
            }
            while state.keep_running() {
                if operation::map(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_4K_VA, 1, slot_4k, 0)
                    != operation::STATUS_OK
                    || unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_4K_VA, 1) }
                        .is_err()
                {
                    return false;
                }
            }
            true
        })
        .is_err()
    {
        return false;
    }

    let slot_2m = fixture.map_unmap_2m_slot;
    registry
        .register("Mmu/MapUnmap/2M", move |state| {
            #[cfg(not(feature = "bench"))]
            {
                if operation::map(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_2M_VA, 2, slot_2m, 0)
                    != operation::STATUS_OK
                    || operation::map(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_2M_VA, 2, slot_2m, 0)
                        != operation::STATUS_REFUSED
                    || unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_2M_VA, 2) }
                        != Err(operation::STATUS_REFUSED)
                    || !revoke_until_done(slot_2m)
                    || operation::inspect(slot_2m).is_err()
                {
                    return false;
                }
            }
            while state.keep_running() {
                if operation::map(operation::ROOT_PROCESS_SLOT, BENCH_MAP_UNMAP_2M_VA, 2, slot_2m, 0)
                    != operation::STATUS_OK
                    || !revoke_until_done(slot_2m)
                {
                    return false;
                }
            }
            true
        })
        .is_ok()
}

fn register_remote_shootdown(
    registry: &mut Registry,
    name: &str,
    untyped_slot: u64,
    proc_slot: u64,
    scratch_slot: u64,
    scratch_phys: u64,
    expect_immediate_free: bool,
) -> bool {
    registry
        .register(name, move |state| {
            state.declare_step("setup_ignore");
            state.declare_step("map");
            state.declare_step("unmap");
            state.declare_step("shootdown");
            while state.keep_running() {
                if operation::retype_frame(untyped_slot, scratch_phys, scratch_slot)
                    != operation::STATUS_OK
                {
                    return false;
                }
                state.next_step();

                if operation::map(proc_slot, CHILD_REMOTE_VA, 1, scratch_slot, 0)
                    != operation::STATUS_OK
                {
                    return false;
                }
                state.next_step();

                if unsafe { operation::unmap(proc_slot, CHILD_REMOTE_VA, 1) }.is_err() {
                    return false;
                }
                state.next_step();

                if operation::delete(scratch_slot) != operation::STATUS_OK {
                    return false;
                }
                let mut again = 0u64;
                loop {
                    match retype_free_once(untyped_slot, scratch_phys, 0) {
                        operation::STATUS_OK => break,
                        operation::STATUS_AGAIN if again < SHOOTDOWN_AGAIN_MAX => again += 1,
                        _ => return false,
                    }
                }
                #[cfg(not(feature = "bench"))]
                {
                    let _ = black_box(expect_immediate_free);
                    if expect_immediate_free && again != 0 {
                        return false;
                    }
                    if operation::inspect(scratch_slot).is_ok()
                        || retype_free_once(untyped_slot, scratch_phys, 0)
                            != operation::STATUS_REFUSED
                    {
                        return false;
                    }
                }
            }
            true
        })
        .is_ok()
}

fn register_probe_64(registry: &mut Registry) -> bool {
    registry
        .register("Mmu/Probe/64", |state| {
            #[cfg(not(feature = "bench"))]
            {
                let p0 = BENCH_PROBE_WINDOW as *mut u64;
                let p63 = (BENCH_PROBE_WINDOW + (PROBE_COUNT - 1) * PAGE_BYTES) as *mut u64;
                // Safety: `BENCH_PROBE_WINDOW` maps 64 RW 4K pages; both accessed pages are live.
                unsafe {
                    p0.write_volatile(0x1111_2222_3333_4444);
                    p63.write_volatile(0x5555_6666_7777_8888);
                    black_box(p0.read_volatile() ^ p63.read_volatile());
                }
                let Ok(first) =
                    operation::probe(operation::ROOT_PROCESS_SLOT, BENCH_PROBE_WINDOW, PROBE_COUNT)
                else {
                    return false;
                };
                let expected = 1u64 | (1u64 << (PROBE_COUNT - 1));
                if first.dirty_maintained && first.dirty != expected {
                    return false;
                }
                if first.accessed_maintained && (first.accessed & expected) != expected {
                    return false;
                }
                let Ok(second) =
                    operation::probe(operation::ROOT_PROCESS_SLOT, BENCH_PROBE_WINDOW, PROBE_COUNT)
                else {
                    return false;
                };
                if second.dirty_maintained && second.dirty != 0 {
                    return false;
                }
            }
            while state.keep_running() {
                let Ok(probed) =
                    operation::probe(operation::ROOT_PROCESS_SLOT, BENCH_PROBE_WINDOW, PROBE_COUNT)
                else {
                    return false;
                };
                black_box(probed);
            }
            true
        })
        .is_ok()
}

fn register_many_mappings_8192(registry: &mut Registry, many_slots_base: u64) -> bool {
    registry
        .register("Mmu/ManyMappingsReadWriteUnmap/8192", move |state| {
            state.declare_step("read");
            state.declare_step("write");
            state.declare_step("unmap");
            state.declare_step("remap_ignore");
            let mut seed = 0x51a7_8192_u64;
            while state.keep_running() {
                let idx = (splitmix64(&mut seed) as usize) & (MANY_PAGES - 1);
                let va = BENCH_MANY_WINDOW + (idx as u64) * PAGE_BYTES;
                let frame_slot = many_slots_base + ((idx as u64) / LARGE_FRAME_PAGES);
                let frame_page = (idx as u64) % LARGE_FRAME_PAGES;
                let ptr = va as *mut u64;

                // Safety: all 8192 4K pages in `BENCH_MANY_WINDOW` are mapped RW until unmap below.
                let read = unsafe { ptr.read_volatile() };
                black_box(read);
                state.next_step();

                let tag = seed ^ (idx as u64).wrapping_add(1);
                // Safety: `va` is mapped RW.
                unsafe { ptr.write_volatile(tag) };
                #[cfg(not(feature = "bench"))]
                {
                    if unsafe { ptr.read_volatile() } != tag {
                        return false;
                    }
                }
                state.next_step();

                // Safety: no Rust reference aliases `va`, and it is remapped before next access.
                let Ok(unmapped) =
                    (unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, va, 1) })
                else {
                    return false;
                };
                #[cfg(not(feature = "bench"))]
                {
                    if (unmapped.dirty_maintained && !unmapped.dirty)
                        || (unmapped.accessed_maintained && !unmapped.accessed)
                        || unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, va, 1) }
                            != Err(operation::STATUS_REFUSED)
                    {
                        return false;
                    }
                }
                let _ = black_box(unmapped);
                state.next_step();

                if operation::map(operation::ROOT_PROCESS_SLOT, va, 1, frame_slot, frame_page)
                    != operation::STATUS_OK
                {
                    return false;
                }
                #[cfg(not(feature = "bench"))]
                {
                    if unsafe { ptr.read_volatile() } != tag {
                        return false;
                    }
                }
            }
            true
        })
        .is_ok()
}

fn register_map_rw(
    registry: &mut Registry,
    name: &str,
    va: u64,
    level: u64,
    slot: u64,
    bytes: usize,
) -> bool {
    registry
        .register(name, move |state| {
            let mut seed = bytes as u64 ^ 0x42_u64;
            let words_len = bytes / size_of::<u64>();
            while state.keep_running() {
                if operation::map(operation::ROOT_PROCESS_SLOT, va, level, slot, 0)
                    != operation::STATUS_OK
                {
                    return false;
                }
                let tag = splitmix64(&mut seed) | 1;
                let expected = (words_len as u64).wrapping_mul(tag);
                // Safety: `va..va + bytes` was just mapped RW (`4K` or `2M`) and is unmapped after.
                let sum = unsafe {
                    let words = core::slice::from_raw_parts_mut(va as *mut u64, words_len);
                    words.fill(tag);
                    compiler_fence(Ordering::SeqCst);
                    black_box(words.as_mut_ptr());
                    words.iter().fold(0u64, |acc, &w| acc.wrapping_add(w))
                };
                let ok = black_box(sum) == expected;
                compiler_fence(Ordering::SeqCst);
                let unmapped_ok = if level == 1 {
                    unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, va, 1) }.is_ok()
                } else {
                    revoke_until_done(slot)
                };
                if !ok || !unmapped_ok {
                    return false;
                }
            }
            true
        })
        .is_ok()
}

#[inline(never)]
fn alloc_empty_heap_slot() -> Box<Option<aheap::allocator::Allocator<aeager::Eager>>> {
    Box::new(None)
}

#[inline(never)]
fn alloc_empty_bench_slot() -> Box<Option<aeager::Eager>> {
    Box::new(None)
}

#[inline(never)]
fn alloc_empty_paired_slot() -> Box<aeager::PairedEager> {
    Box::new(aeager::PairedEager::empty())
}

#[inline(never)]
fn run_eager_lifecycle(
    state: &mut RepeatState<'_>,
    paired: &mut aeager::PairedEager,
) -> bool {
    let verify_rw = cfg!(not(feature = "bench"));
    loop {
        if !paired.bench_reserve() {
            return false;
        }
        state.next_step();

        if !paired.bench_back(verify_rw) {
            return false;
        }
        state.next_step();

        if !paired.bench_release() {
            return false;
        }
        state.next_step();

        if !paired.bench_release_span() {
            return false;
        }

        if !state.keep_running() {
            return true;
        }
    }
}

fn register_eager_lifecycle(registry: &mut Registry, fixture: MmuBenchFixture) -> bool {
    registry
        .register("Span/EagerReserveBackRelease", move |state| {
            state.declare_step("reserve");
            state.declare_step("back");
            state.declare_step("release");
            state.declare_step("release_span");
            // Advance `keep_running()` once and heap-allocate empty slots before taking
            // `GLOBAL`'s allocator so no snapshot or box allocation runs while `GLOBAL` is empty.
            if !state.keep_running() {
                return false;
            }
            let mut alloc_slot = alloc_empty_heap_slot();
            let mut bench_slot = alloc_empty_bench_slot();
            let mut paired = alloc_empty_paired_slot();
            let untyped = fixture.eager_untyped_slot;
            let memory = fixture.eager_mem_phys;
            let slots = fixture.eager_slots_start;
            astd::heap::with_taken_allocator(&mut alloc_slot, |taken| {
                if !window_clear(EAGER_BENCH_WINDOW, &OTHER_EAGER_WINDOWS) {
                    return false;
                }
                if !paired.init_in(
                    taken,
                    &mut bench_slot,
                    untyped,
                    memory,
                    EAGER_BENCH_PAGES,
                    slots,
                    EAGER_BENCH_WINDOW as *mut u8,
                ) {
                    return false;
                }
                let ok = run_eager_lifecycle(state, &mut paired);
                paired.restore_into(taken) && ok
            }) == Some(true)
        })
        .is_ok()
}

/// Sets up the MMU/memory benchmark fixture and registers all 23 (21 on 1-core) benchmarks with
/// `registry`.
pub(crate) fn register(registry: &mut Registry) -> bool {
    let Some(fixture) = MmuBenchFixture::init() else {
        return false;
    };

    let tlb_cases = [
        ("Mmu/TlbReach/4K/Seq/16M", BENCH_4K_WINDOW, false, 0x1001_u64),
        (
            "Mmu/TlbReach/4K/Random/16M",
            BENCH_4K_WINDOW,
            true,
            0x2002_u64,
        ),
        ("Mmu/TlbReach/2M/Seq/16M", BENCH_2M_WINDOW, false, 0x3003_u64),
        (
            "Mmu/TlbReach/2M/Random/16M",
            BENCH_2M_WINDOW,
            true,
            0x4004_u64,
        ),
    ];
    for (name, base, random, seed) in tlb_cases {
        if !register_tlb_reach(registry, name, base, random, seed) {
            return false;
        }
    }

    for (name, pages) in [
        ("Mmu/SpanMapRemapUnmap/4K", 1usize),
        ("Mmu/SpanMapRemapUnmap/64K", 16usize),
        ("Mmu/SpanMapRemapUnmap/1M", 256usize),
    ] {
        if !register_span_bench(
            registry,
            name,
            pages,
            fixture.span_rw_slot,
            fixture.span_ro_slot,
        ) {
            return false;
        }
    }

    if !register_map_revoke_teardown_2m(registry, fixture) {
        return false;
    }

    if !register_map_unmap(registry, fixture) {
        return false;
    }
    if let Some(remote) = fixture.remote {
        if !register_remote_shootdown(
            registry,
            "Mmu/MapUnmap/LoadedRemoteCore",
            fixture.untyped_slot,
            remote.loaded_proc,
            remote.scratch_slot,
            remote.scratch_phys,
            false,
        ) || !register_remote_shootdown(
            registry,
            "Mmu/MapUnmap/UnloadedRemoteCore",
            fixture.untyped_slot,
            remote.unloaded_proc,
            remote.scratch_slot,
            remote.scratch_phys,
            true,
        ) {
            return false;
        }
    }
    if !register_probe_64(registry)
        || !register_many_mappings_8192(registry, fixture.many_slots_base)
        || !register_map_rw(
            registry,
            "Mmu/MapReadWrite/4K",
            BENCH_MAP_RW_4K_VA,
            1,
            fixture.map_rw_4k_slot,
            PAGE_BYTES as usize,
        )
        || !register_map_rw(
            registry,
            "Mmu/MapReadWrite/2M",
            BENCH_MAP_RW_2M_VA,
            2,
            fixture.map_rw_2m_slot,
            LARGE_FRAME_BYTES as usize,
        )
        || !register_eager_lifecycle(registry, fixture)
    {
        return false;
    }

    let chase_cases = [
        ("Memory/PointerChase/32K_4K", BENCH_4K_WINDOW, 32 * 1024, 0xa001_u64),
        ("Memory/PointerChase/32K_2M", BENCH_2M_WINDOW, 32 * 1024, 0xa002_u64),
        (
            "Memory/PointerChase/256K_4K",
            BENCH_4K_WINDOW,
            256 * 1024,
            0xb001_u64,
        ),
        (
            "Memory/PointerChase/256K_2M",
            BENCH_2M_WINDOW,
            256 * 1024,
            0xb002_u64,
        ),
        (
            "Memory/PointerChase/16M_4K",
            BENCH_4K_WINDOW,
            16 * 1024 * 1024,
            0xc001_u64,
        ),
        (
            "Memory/PointerChase/16M_2M",
            BENCH_2M_WINDOW,
            16 * 1024 * 1024,
            0xc002_u64,
        ),
    ];
    for (name, base, bytes, seed) in chase_cases {
        if !register_pointer_chase(registry, name, base, bytes, seed) {
            return false;
        }
    }

    true
}
