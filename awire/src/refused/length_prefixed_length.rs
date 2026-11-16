// SPDX-License-Identifier: MIT

//! `LengthPrefixed::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/length.rs	LengthPrefixed::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'a, L: Length<'a>, I: Combinator<'a>> super::LengthPrefixedLength<'a, L, I> for () {
    proof fn wrong(c: &LengthPrefixed<L, I>, v: I::V, n: nat) {}
}

} // verus!
