// SPDX-License-Identifier: MIT

//! `Pair::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/pair.rs	Pair::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'a, A: Combinator<'a>, B: Combinator<'a>> super::PairLength<'a, A, B> for () {
    proof fn wrong(c: &Pair<A, B>, v: (A::V, B::V), n: nat) {}
}

} // verus!
