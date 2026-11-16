// SPDX-License-Identifier: MIT

//! `Eager::back`'s Some at an unchanged source and token. The free-frame equation spends `pages`
//! frames, which an unchanged source still counts. design/refused-claim-per-way/.
//!
//! covers: aeager/src/eager.rs	Eager::back	Some
//! refused: unchanged: final_self.free_frames() + old_self.unlinked_tables_on(start as int, pages as nat) * TABLE_PAGES as nat + pages as nat == old_self.free_frames()

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use acall::step::Caller;

use crate::eager::Eager;

verus! {

impl super::BackSome for () {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        span: int,
        start: usize,
        pages: usize,
        r: Option<Tracked<PointsToRaw>>,
    ) {
    }
}

} // verus!
