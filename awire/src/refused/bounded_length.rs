// SPDX-License-Identifier: MIT

//! `Bounded::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/repeat.rs	Bounded::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'a, L: Length<'a>, I: Combinator<'a>, const N: usize> super::BoundedLength<'a, L, I, N> for () where I::T: Copy {
    proof fn wrong(c: &Bounded<L, I, N>, v: Seq<I::V>, n: nat) {}
}

} // verus!
