// SPDX-License-Identifier: MIT

//! `Eager::reserve`'s Some at an unchanged source and token. `can_reserve` is the Some arm, and
//! the view is the one the trait's Some arm establishes, a span the unchanged source did not add.
//! design/refused-claim-per-way/.
//!
//! covers: aeager/src/eager.rs	Eager::reserve	Some
//! refused: unchanged: old_self.can_reserve(blocks as nat)
//! refused: unchanged: final_self@ == old_self@.reserved(r->0@.addr as int, blocks as nat)

use vstd::prelude::*;

use acall::step::Caller;

use crate::eager::Eager;

verus! {

impl super::ReserveSome for () {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        blocks: usize,
        r: Option<*mut u8>,
    ) {
    }
}

} // verus!
