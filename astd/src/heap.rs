// SPDX-License-Identifier: MIT

//! The global allocator: aheap's heap over an eager span source the process installs, so every
//! process that links the runtime allocates through the verified heap.
//!
//! This module is glue at tier 3, and what it vouches for is what the heap's proof cannot see. The
//! heap is verified for one caller at a time, so the mutex serializes every call. `alloc` and `free`
//! thread the permission to an object's bytes, which the allocator interface does not carry: the
//! permission `alloc` returns is dropped here, and `dealloc` hands `free` one made up, on the
//! interface's promise that it gets back a pointer `alloc` returned for the same layout, which is what
//! `free` requires of that permission. `layout_fits`, which is verified, decides which layouts reach
//! the heap; the rest get a null pointer.
#![allow(unsafe_code)]

use core::alloc::{GlobalAlloc, Layout};
use core::ptr::null_mut;

use aeager::Eager;
use aheap::heap::{layout_fits, Heap};
use spin::Mutex;
use vstd::prelude::Tracked;

/// The idle spans the heap keeps rather than give back to its source: none, so a source with a small
/// window has every span it does not use free for a large object.
const SPARES: usize = 0;

/// The heap and the source it allocates from.
struct Held {
    heap: Heap,
    source: Eager,
}

// The heap and the source hold addresses in the process's own space, which every thread of the
// process shares, so the thread that holds the mutex may use them whichever thread installed them.
unsafe impl Send for Held {}

/// The heap and the source it allocates from, once the process installed one.
pub struct Global {
    held: Mutex<Option<Held>>,
}

/// The process's allocator. On a target with no operating system under it, the process's own, it is
/// the global allocator.
#[cfg_attr(target_os = "none", global_allocator)]
pub static GLOBAL: Global = Global { held: Mutex::new(None) };

/// Gives the global allocator an empty heap over `source`, from which it serves every allocation
/// after. A process installs one source once; until then every allocation is refused.
pub fn install(source: Eager) {
    let mut held = GLOBAL.held.lock();
    assert!(held.is_none(), "the heap's source is installed once");
    *held = Some(Held { heap: Heap::new(SPARES), source });
}

unsafe impl GlobalAlloc for Global {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut held = self.held.lock();
        let Some(Held { heap, source }) = held.as_mut() else {
            return null_mut();
        };
        if !layout_fits(layout.size(), layout.align()) {
            return null_mut();
        }
        match heap.alloc(source, layout.size(), layout.align()) {
            Some((object, _bytes)) => object,
            None => null_mut(),
        }
    }

    unsafe fn dealloc(&self, object: *mut u8, layout: Layout) {
        let mut held = self.held.lock();
        let Held { heap, source } = held.as_mut().expect("an object to free came from an installed heap");
        heap.free(source, object, layout.size(), layout.align(), Tracked::assume_new());
    }
}
