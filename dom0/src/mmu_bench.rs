// SPDX-License-Identifier: MIT

//! MMU TLB reach, multi-order span map/remap-protect/unmap, 2M revoke+free teardown, and
//! 64B shuffled pointer-chase benchmarks mapped from Barrelfish `usr/bench` (`largepage`,
//! `vspace`, `mem_latency`; MIT) onto Atmosphere's capability operations.

use alloc::vec::Vec;
use core::hint::black_box;
use core::mem::{align_of, size_of};

use abench::runner::Registry;
use asys::operation;

use crate::{
    first_slot, window_clear, EAGER_WINDOW, FIRST_LEAF_END, HEAP_WINDOW, LARGE_FRAME_BYTES,
    LARGE_FRAME_PAGES, MAX_ORDER, RIGHT_READ, ROOT_ENTRIES, TABLE_PAGE_BYTES,
};

const PAGE_BYTES: u64 = 4096;

/// Physical offset into the 1 GiB untyped where this suite allocates its 38 MiB working pool,
/// clear of the bottom 2 MiB check block and the upper 512 MiB checks/heap region.
const POOL_OFFSET_BYTES: u64 = 64 * 1024 * 1024;

/// First root capability table entry probed for placing this suite's single table leaf.
pub(crate) const BENCH_CAP_ENTRY_START: u64 = 32;

/// Distinct level-4 user address windows used by the 4K, 2M, and span/teardown benchmarks.
pub(crate) const BENCH_4K_WINDOW: u64 = 16 << 39;
pub(crate) const BENCH_2M_WINDOW: u64 = 17 << 39;
pub(crate) const BENCH_SPAN_WINDOW: u64 = 18 << 39;
const BENCH_SPAN_4K_BASE: u64 = BENCH_SPAN_WINDOW;
const BENCH_SPAN_2M_BASE: u64 = BENCH_SPAN_WINDOW + LARGE_FRAME_BYTES;

/// Working-set size for `Mmu/TlbReach/{4K,2M}/{Seq,Random}/16M`: 8 x 2M = 4096 x 4K pages.
const TLB_REACH_LARGE_FRAMES: usize = 8;
const TLB_REACH_4K_PAGES: usize = TLB_REACH_LARGE_FRAMES * (LARGE_FRAME_PAGES as usize);

/// Number of `retype_large_frame` retries allowed before treating zeroing as stalled.
const RETYPE_LARGE_AGAIN_MAX: u64 = LARGE_FRAME_PAGES + 1;
const REVOKE_AGAIN_MAX: u64 = 64;
const FREE_AGAIN_MAX: u64 = 64;

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
struct MmuBenchFixture {
    untyped_slot: u64,
    span_rw_slot: u64,
    span_ro_slot: u64,
    teardown_2m_slot: u64,
    teardown_2m_phys: u64,
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
    let base = *next_table;
    *next_table += TABLE_PAGE_BYTES;
    operation::retype_table_page(untyped, base, level) == operation::STATUS_OK
        && operation::link(operation::ROOT_PROCESS_SLOT, va, level + 1, untyped, base)
            == operation::STATUS_OK
}

impl MmuBenchFixture {
    fn init() -> Option<Self> {
        if !window_clear(
            BENCH_4K_WINDOW,
            &[EAGER_WINDOW, HEAP_WINDOW, BENCH_2M_WINDOW, BENCH_SPAN_WINDOW],
        ) || !window_clear(
            BENCH_2M_WINDOW,
            &[EAGER_WINDOW, HEAP_WINDOW, BENCH_4K_WINDOW, BENCH_SPAN_WINDOW],
        ) || !window_clear(
            BENCH_SPAN_WINDOW,
            &[EAGER_WINDOW, HEAP_WINDOW, BENCH_4K_WINDOW, BENCH_2M_WINDOW],
        ) {
            return None;
        }

        let (untyped_slot, block) = find_gigabyte_untyped()?;
        let block_end = block.base + (PAGE_BYTES << block.order);
        let region = block.base + POOL_OFFSET_BYTES;
        if block_end.saturating_sub(region) < 19 * LARGE_FRAME_BYTES {
            return None;
        }

        let leaf_phys = region + 18 * LARGE_FRAME_BYTES;
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

        let mut next_table = leaf_phys + TABLE_PAGE_BYTES;
        if !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_4K_WINDOW, 3)
            || !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_4K_WINDOW, 2)
        {
            return None;
        }
        for m in 0..(TLB_REACH_LARGE_FRAMES as u64) {
            if !alloc_and_link_table(
                untyped_slot,
                &mut next_table,
                BENCH_4K_WINDOW + m * LARGE_FRAME_BYTES,
                1,
            ) {
                return None;
            }
        }

        if !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_2M_WINDOW, 3)
            || !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_2M_WINDOW, 2)
        {
            return None;
        }

        if !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_SPAN_WINDOW, 3)
            || !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_SPAN_WINDOW, 2)
            || !alloc_and_link_table(untyped_slot, &mut next_table, BENCH_SPAN_4K_BASE, 1)
        {
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

        Some(Self {
            untyped_slot,
            span_rw_slot,
            span_ro_slot,
            teardown_2m_slot,
            teardown_2m_phys,
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

/// Sets up the MMU/memory benchmark fixture and registers all 14 benchmarks with `registry`.
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
