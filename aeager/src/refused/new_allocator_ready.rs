// SPDX-License-Identifier: MIT

//! `new_allocator`'s Ready where `Eager::new_ok` is false. The ensures is the Ready arm's clause
//! at the output that arm excludes. design/refused-claim-per-way/.
//!
//! covers: aeager/src/allocator.rs	new_allocator	Ready
//! refused: wrong: Eager::new_ok(memory, pages, slots, window)

use vstd::prelude::*;

use acall::step::Caller;

use crate::allocator::AllocatorInit;

verus! {

impl super::NewAllocatorReady for () {
    proof fn wrong(
        caller: Tracked<Caller>,
        spares: usize,
        space: u64,
        untyped: u64,
        memory: u64,
        pages: usize,
        slots: u64,
        window: *mut u8,
        r: AllocatorInit,
    ) {
    }
}

} // verus!
