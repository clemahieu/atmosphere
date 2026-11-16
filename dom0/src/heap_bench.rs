// SPDX-License-Identifier: MIT

//! Heap allocator and working-set churn microbenchmarks mapped from Fuchsia
//! `src/tests/microbenchmarks` (`malloc.cc` and `mem_alloc.cc`, BSD-2-Clause) onto
//! `astd::heap` / `aheap` (`design/synthetic-benchmark-suite/`).
//!
//! `MallocFree/{100,1024,8192,65536}bytes` (plus `BLOCK_BYTES + PAGE_BYTES` covering the
//! `LargeMap` path) time separate `malloc` and `free` steps across small size-class slabs,
//! `PageBuddy` page runs, and large-object spans. `MemAlloc/Aheap/*` exercises `AllocAndFree`,
//! `RetainAndFreeOldest`, and `RetainAndFreeRandom` over `64`-byte slab objects and `8192`-byte
//! `PageBuddy` runs across `{8,32,128,512,2048}` KiB working sets.
//!
//! Benchmarks are parameterized over [`HeapAdapter`], which wraps `astd::heap::GLOBAL`
//! (`Allocator<aeager::Eager>`, holder of the process's single `Caller` token) today and accepts
//! `Rc<astd::heap::SourcedHeap<S>>` for any `aheap::source::SpanSource` `S` so a user-space pager
//! span source (`atmo-6x9.9.4`) drops in with no change to benchmark code.

use alloc::format;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};
use core::hint::black_box;

use abench::runner::{Registry, RepeatState};
use aheap::arch::{BLOCK_BYTES, PAGE_BYTES};
use aheap::source::SpanSource;
use astd::heap::SourcedHeap;

/// Allocation alignment shared across all `MallocFree` and `MemAlloc` cases (matches `SLOT_MIN`
/// and divides `PAGE_BYTES`, satisfying `aheap` layout preconditions).
const ALLOC_ALIGN: usize = 16;

/// Object sizes exercised by `MemAlloc/Aheap/*` (small slab class and multi-page buddy run).
const MEM_ALLOC_OBJECT_SIZES: [usize; 2] = [64, 8192];

/// Working-set sizes in KiB for `RetainAndFreeOldest` and `RetainAndFreeRandom`, capped at 2 MiB
/// to fit within `aeager::MAX_PAGES` alongside runner metadata and retained pointer storage.
const RETAIN_WORKING_SETS_KIB: [usize; 5] = [8, 32, 128, 512, 2048];

/// Span-source-backed allocator interface used by the heap benchmarks.
pub(crate) trait HeapAdapter: 'static {
    /// Allocates a block matching `layout`, returning null if the span source refuses.
    unsafe fn alloc(&self, layout: Layout) -> *mut u8;

    /// Frees `ptr` previously returned by [`Self::alloc`] with the exact same `layout`.
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout);
}

/// Adapter driving `astd::heap::GLOBAL` (`aheap::allocator::Allocator<aeager::Eager>`).
#[derive(Clone, Copy)]
struct GlobalHeap;

impl HeapAdapter for GlobalHeap {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // Safety: callers ensure non-zero layout size; `astd::heap::GLOBAL` returns null on refusal.
        unsafe { alloc::alloc::alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // Safety: callers return live pointers allocated through `Self::alloc` with identical `layout`.
        unsafe { alloc::alloc::dealloc(ptr, layout) }
    }
}

impl<S: SpanSource + 'static> HeapAdapter for Rc<SourcedHeap<S>> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // Safety: callers ensure non-zero layout size.
        unsafe { GlobalAlloc::alloc(&**self, layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // Safety: callers return live pointers allocated through `Self::alloc` with identical `layout`.
        unsafe { GlobalAlloc::dealloc(&**self, ptr, layout) }
    }
}

#[cfg(not(feature = "bench"))]
fn verify_rw_aligned(ptr: *mut u8, size: usize, align: usize) -> bool {
    if ptr.is_null() || !(ptr as usize).is_multiple_of(align) || size == 0 {
        return false;
    }
    let mut offset = 0usize;
    while offset < size {
        let tag = 0xa5u8 ^ (offset as u8);
        // Safety: `ptr..ptr + size` was returned by `HeapAdapter::alloc` and is mapped RW.
        unsafe {
            let slot = ptr.add(offset);
            slot.write_volatile(tag);
            if slot.read_volatile() != tag {
                return false;
            }
        }
        offset += PAGE_BYTES;
    }
    let last_tag = 0x5au8 ^ (size as u8);
    // Safety: `size - 1` lies inside the allocated `[0, size)` span.
    unsafe {
        let last = ptr.add(size - 1);
        last.write_volatile(last_tag);
        last.read_volatile() == last_tag
    }
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn shuffled_order(count: usize, mut seed: u64) -> Option<Vec<u16>> {
    if count == 0 || count > usize::from(u16::MAX) {
        return None;
    }
    let mut order = Vec::new();
    order.try_reserve_exact(count).ok()?;
    for i in 0..count {
        order.push(i as u16);
    }
    for i in (1..count).rev() {
        let j = (splitmix64(&mut seed) as usize) % (i + 1);
        order.swap(i, j);
    }
    Some(order)
}

struct RetainedSet<'a, A: HeapAdapter> {
    adapter: &'a A,
    layout: Layout,
    ptrs: Vec<*mut u8>,
}

impl<'a, A: HeapAdapter> RetainedSet<'a, A> {
    fn populate(adapter: &'a A, layout: Layout, count: usize) -> Option<Self> {
        let mut ptrs = Vec::new();
        ptrs.try_reserve_exact(count).ok()?;
        let mut guard = Self {
            adapter,
            layout,
            ptrs,
        };
        for _ in 0..count {
            // Safety: `layout` has non-zero size and alignment dividing `PAGE_BYTES`.
            let ptr = unsafe { guard.adapter.alloc(guard.layout) };
            if ptr.is_null() {
                return None;
            }
            #[cfg(not(feature = "bench"))]
            if !verify_rw_aligned(ptr, guard.layout.size(), guard.layout.align()) {
                // Safety: `ptr` was just returned by `guard.adapter.alloc(guard.layout)`.
                unsafe { guard.adapter.dealloc(ptr, guard.layout) };
                return None;
            }
            guard.ptrs.push(ptr);
        }
        Some(guard)
    }

    #[inline]
    fn replace(&mut self, index: usize, new_ptr: *mut u8) -> *mut u8 {
        let old = self.ptrs[index];
        self.ptrs[index] = new_ptr;
        old
    }
}

impl<A: HeapAdapter> Drop for RetainedSet<'_, A> {
    fn drop(&mut self) {
        for &ptr in &self.ptrs {
            if !ptr.is_null() {
                // Safety: every non-null element in `self.ptrs` is a live allocation from `self.adapter`.
                unsafe { self.adapter.dealloc(ptr, self.layout) };
            }
        }
    }
}

fn run_malloc_free<A: HeapAdapter>(
    adapter: &A,
    state: &mut RepeatState<'_>,
    size: usize,
) -> bool {
    let Ok(layout) = Layout::from_size_align(size, ALLOC_ALIGN) else {
        return false;
    };
    state.declare_step("malloc");
    state.declare_step("free");
    while state.keep_running() {
        // Safety: `size` is non-zero and `ALLOC_ALIGN` is a power of two dividing `PAGE_BYTES`.
        let ptr = unsafe { adapter.alloc(layout) };
        black_box(ptr);
        if ptr.is_null() {
            return false;
        }
        #[cfg(not(feature = "bench"))]
        if !verify_rw_aligned(ptr, size, ALLOC_ALIGN) {
            // Safety: `ptr` was just allocated with `layout`.
            unsafe { adapter.dealloc(ptr, layout) };
            return false;
        }
        state.next_step();
        // Safety: `ptr` was allocated above with `layout` and has not been freed.
        unsafe { adapter.dealloc(ptr, layout) };
    }
    true
}

fn run_alloc_and_free<A: HeapAdapter>(
    adapter: &A,
    state: &mut RepeatState<'_>,
    obj_size: usize,
) -> bool {
    let Ok(layout) = Layout::from_size_align(obj_size, ALLOC_ALIGN) else {
        return false;
    };
    while state.keep_running() {
        // Safety: `layout` has non-zero size and alignment dividing `PAGE_BYTES`.
        let ptr = unsafe { adapter.alloc(layout) };
        black_box(ptr);
        if ptr.is_null() {
            return false;
        }
        #[cfg(not(feature = "bench"))]
        if !verify_rw_aligned(ptr, obj_size, ALLOC_ALIGN) {
            // Safety: `ptr` was just allocated with `layout`.
            unsafe { adapter.dealloc(ptr, layout) };
            return false;
        }
        // Safety: `ptr` was allocated above with `layout`.
        unsafe { adapter.dealloc(ptr, layout) };
    }
    true
}

fn run_retain_and_free<A: HeapAdapter>(
    adapter: &A,
    state: &mut RepeatState<'_>,
    obj_size: usize,
    total_kib: usize,
    random_order: bool,
) -> bool {
    let Ok(layout) = Layout::from_size_align(obj_size, ALLOC_ALIGN) else {
        return false;
    };
    let count = (total_kib * 1024) / obj_size;
    if count == 0 {
        return false;
    }
    let order = if random_order {
        let seed = 0x517c_c1b7_2722_0a95_u64 ^ ((obj_size as u64) << 32) ^ (total_kib as u64);
        let Some(seq) = shuffled_order(count, seed) else {
            return false;
        };
        Some(seq)
    } else {
        None
    };
    let Some(mut retained) = RetainedSet::populate(adapter, layout, count) else {
        return false;
    };

    let mut pos = 0usize;
    while state.keep_running() {
        let slot = match order {
            Some(ref seq) => usize::from(seq[pos]),
            None => pos,
        };
        pos += 1;
        if pos == count {
            pos = 0;
        }

        // Safety: `layout` has non-zero size and valid alignment.
        let new_ptr = unsafe { adapter.alloc(layout) };
        black_box(new_ptr);
        if new_ptr.is_null() {
            return false;
        }
        #[cfg(not(feature = "bench"))]
        if !verify_rw_aligned(new_ptr, obj_size, ALLOC_ALIGN) {
            // Safety: `new_ptr` was just allocated with `layout`.
            unsafe { adapter.dealloc(new_ptr, layout) };
            return false;
        }
        let old_ptr = retained.replace(slot, new_ptr);
        // Safety: `old_ptr` was allocated from `adapter` with `layout` and just removed from `retained`.
        unsafe { adapter.dealloc(old_ptr, layout) };
    }
    true
}

/// Registers `MallocFree/*` and `MemAlloc/Aheap/*` over any [`HeapAdapter`].
pub(crate) fn register_with<A: HeapAdapter + Clone>(
    registry: &mut Registry,
    adapter: A,
) -> Result<(), &'static str> {
    let large_object_bytes = BLOCK_BYTES + PAGE_BYTES;
    for size in [100usize, 1024, 8192, 65536, large_object_bytes] {
        let a = adapter.clone();
        registry.register(format!("MallocFree/{size}bytes"), move |state| {
            run_malloc_free(&a, state, size)
        })?;
    }

    for obj_size in MEM_ALLOC_OBJECT_SIZES {
        let a = adapter.clone();
        registry.register(format!("MemAlloc/Aheap/AllocAndFree/{obj_size}bytes"), move |state| {
            run_alloc_and_free(&a, state, obj_size)
        })?;

        for total_kib in RETAIN_WORKING_SETS_KIB {
            let a_oldest = adapter.clone();
            registry.register(
                format!("MemAlloc/Aheap/RetainAndFreeOldest/{obj_size}bytes/{total_kib}Kbytes"),
                move |state| run_retain_and_free(&a_oldest, state, obj_size, total_kib, false),
            )?;

            let a_random = adapter.clone();
            registry.register(
                format!("MemAlloc/Aheap/RetainAndFreeRandom/{obj_size}bytes/{total_kib}Kbytes"),
                move |state| run_retain_and_free(&a_random, state, obj_size, total_kib, true),
            )?;
        }
    }

    Ok(())
}

/// Registers all heap allocator and working-set benchmarks against `astd::heap::GLOBAL`.
pub(crate) fn register(registry: &mut Registry) -> bool {
    register_with(registry, GlobalHeap).is_ok()
}
