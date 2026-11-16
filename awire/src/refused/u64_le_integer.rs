// SPDX-License-Identifier: MIT

//! `U64Le`'s parse and serialize at the round trip they exclude, and its length's Some at a
//! length that is not the serialisation's. Parse and serialize ensure the round trip; length
//! ensures `n == spec_serialize(v).len()`. The claim is each of those at the other output, so an
//! empty proof is refused there. design/refused-claim-per-way/.
//!
//! covers: awire/src/integer.rs	U64Le::parse	Some
//! covers: awire/src/integer.rs	U64Le::length	Some
//! covers: awire/src/integer.rs	U64Le::serialize	Some
//! refused: parse_trip: c.spec_parse(s) matches Some((n, v)) ==> c.spec_serialize(v) != s.take(n as int)
//! refused: serialize_trip: c.spec_parse(c.spec_serialize(v) + rest) != Some((c.spec_serialize(v).len(), v))
//! refused: wrong: n != c.spec_serialize(v).len()

use crate::*;

verus! {

impl<'a> super::IntegerCombinator<'a, U64Le> for () {
    proof fn parse_trip(c: &U64Le, s: Seq<u8>) {}

    proof fn serialize_trip(c: &U64Le, v: u64, rest: Seq<u8>) {}

    proof fn wrong(c: &U64Le, v: u64, n: nat) {}
}

} // verus!
