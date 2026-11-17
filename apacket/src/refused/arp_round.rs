// SPDX-License-Identifier: MIT

//! `Arp`'s parse and serialize at the round trip they exclude. Each ensures the serialisation of a
//! parsed value is the bytes consumed, and that a serialised value parses back to itself. The claim
//! is that round trip at the other output, so an empty proof is refused there.
//! design/refused-claim-per-way/.
//!
//! covers: apacket/src/arp.rs	Arp::parse	Some
//! covers: apacket/src/arp.rs	Arp::serialize	Some
//! refused: parse_trip: <Arp as Combinator<'a>>::spec_parse(c, s) matches Some((n, v)) ==> <Arp as Combinator<'a>>::spec_serialize(c, v) != s.take(n as int)
//! refused: serialize_trip: <Arp as Combinator<'a>>::spec_parse(c, <Arp as Combinator<'a>>::spec_serialize(c, v) + rest) != Some((<Arp as Combinator<'a>>::spec_serialize(c, v).len(), v))

use vstd::prelude::*;

use crate::*;

verus! {

impl<'a> super::ArpRound<'a> for () {
    proof fn parse_trip(c: &Arp, s: Seq<u8>) {}

    proof fn serialize_trip(c: &Arp, v: ArpPacketView, rest: Seq<u8>) {}
}

} // verus!
