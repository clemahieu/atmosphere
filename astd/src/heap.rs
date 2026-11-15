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
//! token beside the heap and source, lends it to `with_caller` while not allocating, and `dealloc`
//! stops the process if called with the token lent out.
#![allow(unsafe_code)]

use core::alloc::{GlobalAlloc, Layout};
use core::ptr::null_mut;

use acall::step::Caller;
use aeager::{AllocatorInit, Eager};
use aheap::allocator::Allocator;
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

/// Keeps the process's caller token, which the process mints once at entry. Every later system call
/// borrows it from here.
pub fn keep_caller(caller: Tracked<Caller>) {
    let mut held = GLOBAL.held.lock();
    assert!(held.caller.is_none() && held.allocator.is_none(), "a process keeps one caller token");
    held.caller = Some(caller);
}

/// Lends the process's caller token to `calls`. The mutex is released while it runs, and `calls`
/// does not free while the token is lent out.
pub fn with_caller<R>(calls: impl FnOnce(&mut Tracked<Caller>) -> R) -> R {
    let mut caller = {
        let mut held = GLOBAL.held.lock();
        if let Some(allocator) = held.allocator.as_mut() {
            allocator.lend().expect("the caller token is kept and not lent out")
        } else {
            held.caller.take().expect("the caller token is kept and not lent out")
        }
    };
    let r = calls(&mut caller);
    let mut held = GLOBAL.held.lock();
    if let Some(allocator) = held.allocator.as_mut() {
        allocator.give_back(caller);
    } else {
        held.caller = Some(caller);
    }
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

unsafe impl GlobalAlloc for Global {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let mut held = self.held.lock();
        let Some(allocator) = held.allocator.as_mut() else {
            return null_mut();
        };
        match allocator.alloc(layout.size(), layout.align()) {
            Some((object, _bytes)) => object,
            None => null_mut(),
        }
    }

    unsafe fn dealloc(&self, object: *mut u8, layout: Layout) {
        let mut held = self.held.lock();
        let allocator = held.allocator.as_mut().expect("an object to free came from an installed heap");
        assert!(allocator.has_token(), "no free while the caller token is lent out");
        allocator.free(object, layout.size(), layout.align(), Tracked::assume_new());
    }
}
