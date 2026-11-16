// SPDX-License-Identifier: MIT

//! The global allocator: aheap's heap over an eager span source the process installs, so every
//! process that links the runtime allocates through the verified heap, and the keeper of the
//! process's one caller token, which the heap's source borrows for each call and the process for its
//! own.
//!
//! This module is glue at tier 3, and what it vouches for is what the heap's proof cannot see. The
//! heap is verified for one caller at a time, so the mutex serializes every call. `alloc` and `free`
//! thread the permission to an object's bytes, which the allocator interface does not carry: the
//! permission `alloc` returns is dropped here, and `dealloc` hands `free` one made up, on the
//! interface's promise that it gets back a pointer `alloc` returned for the same layout, which is what
//! `free` requires of that permission. `Allocator::alloc` decides which layouts reach the heap and
//! returns nothing when a layout does not fit or the caller token is lent out; the rest get a null
//! pointer. The interface carries no caller token either, so the verified `Allocator` keeps the
//! token beside the heap and source. `with_caller` lends that token only before the allocator is
//! installed. Once it is, the token stays there: an arbitrary call could delete, move or revoke a
//! frame the source holds, and nothing would then show that the source still serves the token.
//! `dealloc` stops the process if called with the token lent out.
#![allow(unsafe_code)]

use core::alloc::{GlobalAlloc, Layout};
use core::ptr::null_mut;

use acall::step::Caller;
use aeager::{AllocatorInit, Eager};
use aheap::allocator::Allocator;
use aheap::source::SpanSource;
use spin::Mutex;
use vstd::prelude::Tracked;

/// The idle spans the heap keeps rather than give back to its source: none, so a source with a small
/// window has every span it does not use free for a large object.
pub const SPARES: usize = 0;

/// What the allocator holds: the process's caller token until `install_with` moves it into the
/// verified `Allocator`, or while lent out before installation, and the installed allocator once
/// created.
struct Held {
    caller: Option<Tracked<Caller>>,
    allocator: Option<Allocator<Eager>>,
}

// The allocator's heap and source hold addresses in the process's own space, which every thread of
// the process shares, so the thread that holds the mutex may use them whichever thread installed
// them.
unsafe impl Send for Held {}

/// The process's caller token, its heap and the source the heap allocates from.
pub struct Global {
    held: Mutex<Held>,
}

/// The process's allocator. On a target with no operating system under it, the process's own, it is
/// the global allocator.
#[cfg_attr(target_os = "none", global_allocator)]
pub static GLOBAL: Global = Global { held: Mutex::new(Held { caller: None, allocator: None }) };

/// Keeps the process's caller token, which the process mints once at entry. `with_caller` borrows it
/// until the allocator is installed.
pub fn keep_caller(caller: Tracked<Caller>) {
    let mut held = GLOBAL.held.lock();
    assert!(held.caller.is_none() && held.allocator.is_none(), "a process keeps one caller token");
    held.caller = Some(caller);
}

/// Lends the process's caller token to `calls` before the heap's allocator is installed. The mutex
/// is released while it runs, and `calls` does not free while the token is lent out. Once the
/// allocator is installed the token stays in it, so this refuses to lend.
pub fn with_caller<R>(calls: impl FnOnce(&mut Tracked<Caller>) -> R) -> R {
    let mut caller = {
        let mut held = GLOBAL.held.lock();
        assert!(
            held.allocator.is_none(),
            "the caller token stays in the allocator once the heap is installed",
        );
        held.caller.take().expect("the caller token is kept and not lent out")
    };
    let r = calls(&mut caller);
    let mut held = GLOBAL.held.lock();
    assert!(held.allocator.is_none(), "the heap is not installed while the caller token is lent");
    held.caller = Some(caller);
    r
}

#[inline(never)]
fn store_allocator(init: AllocatorInit) -> bool {
    match init {
        AllocatorInit::Ready(allocator) => {
            let mut held = GLOBAL.held.lock();
            assert!(held.allocator.is_none(), "the heap's allocator is installed once");
            assert!(held.caller.is_none(), "caller token was moved into install_with");
            held.allocator = Some(allocator);
            true
        },
        AllocatorInit::Refused(caller) => {
            let mut held = GLOBAL.held.lock();
            assert!(held.caller.is_none(), "caller token was moved into install_with");
            held.caller = Some(caller);
            false
        },
    }
}

/// Gives the global allocator an empty heap and eager source built by `make` with the kept caller
/// token. A process installs one allocator once; returns `false` and restores the token if `make`
/// refuses.
pub fn install_with(make: impl FnOnce(Tracked<Caller>) -> AllocatorInit) -> bool {
    let caller = {
        let mut held = GLOBAL.held.lock();
        assert!(held.allocator.is_none(), "the heap's allocator is installed once");
        held.caller.take().expect("the caller token is kept and not lent out")
    };
    store_allocator(make(caller))
}

fn alloc_in<S: SpanSource>(allocator: &mut Allocator<S>, layout: Layout) -> *mut u8 {
    match allocator.alloc(layout.size(), layout.align()) {
        Some((object, _bytes)) => object,
        None => null_mut(),
    }
}

/// Frees `object` through `allocator` under `GlobalAlloc::dealloc`'s safety contract: `object` was
/// returned by `alloc_in` on `allocator` for the exact `layout`, and has not yet been freed.
unsafe fn free_in<S: SpanSource>(allocator: &mut Allocator<S>, object: *mut u8, layout: Layout) {
    assert!(allocator.has_token(), "no free while the caller token is lent out");
    allocator.free(object, layout.size(), layout.align(), Tracked::assume_new());
}

unsafe impl GlobalAlloc for Global {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut held = self.held.lock();
        let Some(allocator) = held.allocator.as_mut() else {
            return null_mut();
        };
        alloc_in(allocator, layout)
    }

    unsafe fn dealloc(&self, object: *mut u8, layout: Layout) {
        let mut held = self.held.lock();
        let allocator = held.allocator.as_mut().expect("an object to free came from an installed heap");
        // Safety: `GlobalAlloc::dealloc` guarantees `object` came from `alloc` with `layout`.
        unsafe { free_in(allocator, object, layout) };
    }
}

/// A serialized `GlobalAlloc` adapter around an `aheap` `Allocator<S>` for any `SpanSource` `S`,
/// allowing callers (such as benchmark harnesses) to swap `aeager::Eager` for another span source
/// without duplicating `alloc`/`free` glue.
pub struct SourcedHeap<S: SpanSource> {
    allocator: Mutex<Allocator<S>>,
}

// An `Allocator<S>` owns addresses and permissions in its process's address space, which every
// thread of that process shares under the mutex.
unsafe impl<S: SpanSource> Send for SourcedHeap<S> {}

impl<S: SpanSource> SourcedHeap<S> {
    /// Wraps an already-initialized `Allocator<S>` behind a `GlobalAlloc`-compatible lock.
    pub const fn new(allocator: Allocator<S>) -> Self {
        Self { allocator: Mutex::new(allocator) }
    }

    /// Unwraps the inner `Allocator<S>`, consuming the adapter.
    pub fn into_inner(self) -> Allocator<S> {
        self.allocator.into_inner()
    }
}

unsafe impl<S: SpanSource> GlobalAlloc for SourcedHeap<S> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut allocator = self.allocator.lock();
        alloc_in(&mut allocator, layout)
    }

    unsafe fn dealloc(&self, object: *mut u8, layout: Layout) {
        let mut allocator = self.allocator.lock();
        // Safety: `GlobalAlloc::dealloc` guarantees `object` came from `alloc` with `layout`.
        unsafe { free_in(&mut allocator, object, layout) };
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use core::alloc::{GlobalAlloc, Layout};
    use std::alloc::{alloc_zeroed, dealloc};
    use std::vec::Vec;

    use aheap::allocator::Allocator;
    use aheap::arch::{BLOCK_BYTES, PAGE_BYTES};
    use aheap::source::SpanSource;
    use vstd::prelude::{int, Ghost, Tracked};
    use vstd::raw_ptr::PointsToRaw;

    use super::SourcedHeap;

    struct SpanRecord {
        base: usize,
        blocks: usize,
        backed: Vec<bool>,
    }

    struct HostSpanSource {
        max_backed_pages: usize,
        backed_pages: usize,
        spans: Vec<SpanRecord>,
    }

    impl HostSpanSource {
        fn new(max_backed_pages: usize) -> Self {
            Self { max_backed_pages, backed_pages: 0, spans: Vec::new() }
        }
    }

    impl Drop for HostSpanSource {
        fn drop(&mut self) {
            for span in &self.spans {
                let layout = Layout::from_size_align(span.blocks * BLOCK_BYTES, BLOCK_BYTES).unwrap();
                unsafe { dealloc(span.base as *mut u8, layout) };
            }
        }
    }

    impl SpanSource for HostSpanSource {
        type Token = ();

        fn reserve(&mut self, _token: &mut Tracked<Self::Token>, blocks: usize) -> Option<*mut u8> {
            assert!(blocks > 0);
            let layout = Layout::from_size_align(blocks * BLOCK_BYTES, BLOCK_BYTES).ok()?;
            let ptr = unsafe { alloc_zeroed(layout) };
            if ptr.is_null() {
                return None;
            }
            let pages = blocks * (BLOCK_BYTES / PAGE_BYTES);
            self.spans.push(SpanRecord {
                base: ptr as usize,
                blocks,
                backed: std::vec![false; pages],
            });
            Some(ptr)
        }

        fn back(
            &mut self,
            _token: &mut Tracked<Self::Token>,
            span: Ghost<int>,
            start: usize,
            pages: usize,
        ) -> Option<Tracked<PointsToRaw>> {
            let _ = span;
            if self.backed_pages + pages > self.max_backed_pages {
                return None;
            }
            let rec = self.spans.iter_mut().find(|s| {
                start >= s.base && start + pages * PAGE_BYTES <= s.base + s.blocks * BLOCK_BYTES
            })?;
            let first = (start - rec.base) / PAGE_BYTES;
            for flag in &rec.backed[first..first + pages] {
                assert!(!*flag, "page already backed");
            }
            for flag in &mut rec.backed[first..first + pages] {
                *flag = true;
            }
            self.backed_pages += pages;
            Some(Tracked::assume_new())
        }

        fn release(
            &mut self,
            _token: &mut Tracked<Self::Token>,
            span: Ghost<int>,
            start: usize,
            pages: usize,
            _perm: Tracked<PointsToRaw>,
        ) {
            let _ = span;
            let rec = self
                .spans
                .iter_mut()
                .find(|s| start >= s.base && start + pages * PAGE_BYTES <= s.base + s.blocks * BLOCK_BYTES)
                .expect("span must exist");
            let first = (start - rec.base) / PAGE_BYTES;
            for flag in &mut rec.backed[first..first + pages] {
                assert!(*flag, "page not backed");
                *flag = false;
            }
            self.backed_pages -= pages;
        }

        fn release_span(&mut self, _token: &mut Tracked<Self::Token>, span: usize) {
            let pos = self.spans.iter().position(|s| s.base == span).expect("span exists");
            let rec = self.spans.remove(pos);
            assert!(rec.backed.iter().all(|&b| !b), "releasing span with backed pages");
            let layout = Layout::from_size_align(rec.blocks * BLOCK_BYTES, BLOCK_BYTES).unwrap();
            unsafe { dealloc(rec.base as *mut u8, layout) };
        }
    }

    #[test]
    fn sourced_heap_allocates_small_run_large_and_retains_without_leaks() {
        let src = HostSpanSource::new(2048);
        let alloc = Allocator::new(0, src, Tracked::assume_new());
        let heap = SourcedHeap::new(alloc);

        for size in [64usize, 100, 1024, 8192, 65536, BLOCK_BYTES + PAGE_BYTES] {
            let layout = Layout::from_size_align(size, 16).unwrap();
            let ptr = unsafe { heap.alloc(layout) };
            assert!(!ptr.is_null(), "alloc failed for size {size}");
            assert_eq!(ptr as usize % 16, 0);
            unsafe {
                ptr.write_volatile(0xa5);
                ptr.add(size - 1).write_volatile(0x5a);
                assert_eq!(ptr.read_volatile(), 0xa5);
                assert_eq!(ptr.add(size - 1).read_volatile(), 0x5a);
                heap.dealloc(ptr, layout);
            }
        }

        let mut retained = Vec::new();
        let retain_layout = Layout::from_size_align(64, 16).unwrap();
        let count = (512 * 1024) / 64;
        for _ in 0..count {
            let ptr = unsafe { heap.alloc(retain_layout) };
            assert!(!ptr.is_null());
            retained.push(ptr);
        }
        for i in 0..count {
            let new_ptr = unsafe { heap.alloc(retain_layout) };
            assert!(!new_ptr.is_null());
            let old_ptr = retained[i];
            retained[i] = new_ptr;
            unsafe { heap.dealloc(old_ptr, retain_layout) };
        }
        for ptr in retained {
            unsafe { heap.dealloc(ptr, retain_layout) };
        }

        let inner = heap.into_inner();
        assert_eq!(inner.source().backed_pages, 0);
        assert!(inner.source().spans.is_empty());
    }

    #[test]
    fn sourced_heap_returns_null_on_source_refusal_and_recovers_after_free() {
        let src = HostSpanSource::new(4);
        let alloc = Allocator::new(0, src, Tracked::assume_new());
        let heap = SourcedHeap::new(alloc);
        let layout = Layout::from_size_align(8192, 16).unwrap();

        let p1 = unsafe { heap.alloc(layout) };
        assert!(!p1.is_null());
        let p2 = unsafe { heap.alloc(layout) };
        assert!(p2.is_null(), "3rd/4th pages exhausted after metadata + first 2-page run");

        unsafe { heap.dealloc(p1, layout) };
        let p3 = unsafe { heap.alloc(layout) };
        assert!(!p3.is_null(), "allocation succeeds once freed pages return");
        unsafe { heap.dealloc(p3, layout) };

        let inner = heap.into_inner();
        assert_eq!(inner.source().backed_pages, 0);
        assert!(inner.source().spans.is_empty());
    }
}
