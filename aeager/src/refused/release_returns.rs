// SPDX-License-Identifier: MIT

//! `Eager::release` at an unchanged source and token. Free capacity and free frames rise by
//! `pages`, so both equalities fail when nothing changed. design/refused-claim-per-way/.
//!
//! covers: aeager/src/eager.rs	Eager::release	returns
//! refused: unchanged: final_self.free_capacity() == old_self.free_capacity() + pages as int
//! refused: unchanged: final_self.free_frames() == old_self.free_frames() + pages as nat

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use acall::step::Caller;

use crate::eager::Eager;

verus! {

impl super::ReleaseReturns for () {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        span: int,
        start: usize,
        pages: usize,
        perm: Tracked<PointsToRaw>,
    ) {
    }
}

} // verus!
