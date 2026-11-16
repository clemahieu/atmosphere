// SPDX-License-Identifier: MIT

//! `Choice::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/choice.rs	Choice::length	Some
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'a, A: Combinator<'a>, B: Combinator<'a>> super::ChoiceLength<'a, A, B> for () {
    proof fn wrong(c: &Choice<A, B>, v: Either<A::V, B::V>, n: nat) {}
}

} // verus!
