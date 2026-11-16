// SPDX-License-Identifier: MIT

//! `Choice`'s parse and serialize at the round trip they exclude. Each ensures the serialisation of
//! a parsed value is the bytes consumed, and that a serialised value parses back to itself. The
//! claim is that round trip at the other output, so an empty proof is refused there.
//! design/refused-claim-per-way/.
//!
//! covers: awire/src/choice.rs	Choice::parse	Some
//! covers: awire/src/choice.rs	Choice::serialize	Some
//! refused: parse_trip: c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int)
//! refused: serialize_trip: c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v))

use crate::*;

verus! {

impl<'a, A: Combinator<'a>, B: Combinator<'a>> super::ChoiceRound<'a, A, B> for () {
    proof fn parse_trip(c: &Choice<A, B>, s: Seq<u8>) {}

    proof fn serialize_trip(c: &Choice<A, B>, v: Either<A::V, B::V>, rest: Seq<u8>) {}
}

} // verus!
