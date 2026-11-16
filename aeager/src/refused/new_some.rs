// SPDX-License-Identifier: MIT

//! `Eager::new`'s Some at an unchanged caller. The source the ensures describes has no spans and
//! `pages` frames free; the `Some` here is an arbitrary source. design/refused-claim-per-way/.
//!
//! covers: aeager/src/eager.rs	Eager::new	Some
//! refused: unchanged: r->0@.spans.is_empty()
//! refused: unchanged: r->0.free_frames() == pages as nat

use vstd::prelude::*;

use acall::step::Caller;

use crate::eager::Eager;

verus! {

impl super::NewSome for () {
    proof fn unchanged(
        old_caller: Tracked<Caller>,
        final_caller: Tracked<Caller>,
        space: u64,
        untyped: u64,
        memory: u64,
        pages: usize,
        slots: u64,
        window: *mut u8,
        r: Option<Eager>,
    ) {
    }
}

} // verus!
