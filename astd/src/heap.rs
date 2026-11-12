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
//! `free` requires of that permission. `layout_fits`, which is verified, decides which layouts reach
//! the heap; the rest get a null pointer. The interface carries no caller token either, so the token
//! is kept here beside the heap and lent to each call. One thread per process maps and unmaps
//! (design/region-map-owns-the-address-space/), so while the process borrows the token it does not
//! allocate: an allocation then finds the token lent out and stops the process.
#![allow(unsafe_code)]

use core::alloc::{GlobalAlloc, Layout};
use core::ptr::null_mut;

use acall::step::Caller;
use aeager::Eager;
use aheap::heap::{layout_fits, Heap};
use spin::Mutex;
use vstd::prelude::Tracked;

/// The idle spans the heap keeps rather than give back to its source: none, so a source with a small
/// window has every span it does not use free for a large object.
const SPARES: usize = 0;

/// The heap and the source it allocates from.
struct Source {
    heap: Heap,
    eager: Eager,
}

/// What the allocator holds: the process's caller token, unless it is lent out, and the heap once the
/// process installed one.
struct Held {
    caller: Option<Tracked<Caller>>,
    source: Option<Source>,
}

// The heap and the source hold addresses in the process's own space, which every thread of the
// process shares, so the thread that holds the mutex may use them whichever thread installed them.
unsafe impl Send for Held {}

/// The process's caller token, its heap and the source the heap allocates from.
pub struct Global {
    held: Mutex<Held>,
}

/// The process's allocator. On a target with no operating system under it, the process's own, it is
/// the global allocator.
#[cfg_attr(target_os = "none", global_allocator)]
pub static GLOBAL: Global = Global { held: Mutex::new(Held { caller: None, source: None }) };

/// Keeps the process's caller token, which the process mints once at entry. Every later system call
/// borrows it from here.
pub fn keep_caller(caller: Tracked<Caller>) {
    let mut held = GLOBAL.held.lock();
    assert!(held.caller.is_none(), "a process keeps one caller token");
    held.caller = Some(caller);
}

/// Lends the process's caller token to `calls`. The mutex is released while it runs, and `calls`
/// does not allocate: the heap's source needs the token it holds.
pub fn with_caller<R>(calls: impl FnOnce(&mut Tracked<Caller>) -> R) -> R {
    let mut caller = GLOBAL.held.lock().caller.take().expect("the caller token is kept and not lent out");
    let r = calls(&mut caller);
    GLOBAL.held.lock().caller = Some(caller);
    r
}

/// Gives the global allocator an empty heap over `eager`, from which it serves every allocation
/// after. A process installs one source once; until then every allocation is refused.
pub fn install(eager: Eager) {
    let mut held = GLOBAL.held.lock();
    assert!(held.source.is_none(), "the heap's source is installed once");
    held.source = Some(Source { heap: Heap::new(SPARES), eager });
}

unsafe impl GlobalAlloc for Global {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut held = self.held.lock();
        let Held { caller, source } = &mut *held;
        let Some(Source { heap, eager }) = source.as_mut() else {
            return null_mut();
        };
        if !layout_fits(layout.size(), layout.align()) {
            return null_mut();
        }
        let caller = caller.as_mut().expect("no allocation while the caller token is lent out");
        match heap.alloc(eager, caller, layout.size(), layout.align()) {
            Some((object, _bytes)) => object,
            None => null_mut(),
        }
    }

    unsafe fn dealloc(&self, object: *mut u8, layout: Layout) {
        let mut held = self.held.lock();
        let Held { caller, source } = &mut *held;
        let Source { heap, eager } = source.as_mut().expect("an object to free came from an installed heap");
        let caller = caller.as_mut().expect("no free while the caller token is lent out");
        heap.free(eager, caller, object, layout.size(), layout.align(), Tracked::assume_new());
    }
}
