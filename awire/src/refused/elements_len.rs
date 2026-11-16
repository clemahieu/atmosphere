// SPDX-License-Identifier: MIT

//! `Elements::len` at a count that is not the length. The ensures is `n == self@.len()`; this is
//! that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/repeat.rs	Elements::len	returns
//! refused: wrong: n != e@.len()

use crate::*;

verus! {

impl<T: Copy + View, const N: usize> super::ElementsLen<T, N> for () {
    proof fn wrong(e: &Elements<T, N>, n: usize) {}
}

} // verus!
