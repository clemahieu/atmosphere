// SPDX-License-Identifier: MIT

//! `Filled::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/repeat.rs	Filled::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'a, I: Combinator<'a>, const N: usize> super::FilledLength<'a, I, N> for () where I::T: Copy {
    proof fn wrong(c: &Filled<I, N>, v: Seq<I::V>, n: nat) {}
}

} // verus!
