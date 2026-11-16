// SPDX-License-Identifier: MIT

//! `Elements::get` at a value that is not the element at `i`. The ensures is
//! `t@ == self@[i as int]`; this is that ensures at the other output. The requires are the
//! operation's, so the index is one the sequence has.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/repeat.rs	Elements::get	returns
//! refused: wrong: t@ != e@[i as int]

use crate::*;

verus! {

impl<T: Copy + View, const N: usize> super::ElementsGet<T, N> for () {
    proof fn wrong(e: &Elements<T, N>, i: usize, t: T) {}
}

} // verus!
