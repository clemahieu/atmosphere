// SPDX-License-Identifier: MIT

//! `Mapped::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/mapped.rs	Mapped::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'a, I: Combinator<'a>, M: Mapping<I::T>> super::MappedLength<'a, I, M> for () {
    proof fn wrong(c: &Mapped<I, M>, v: <M::T as View>::V, n: nat) {}
}

} // verus!
