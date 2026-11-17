// SPDX-License-Identifier: MIT

//! False claims, one module each, which Verus must refuse at the postconditions each names. Each
//! states its claim as a trait here and its body in the module, so the refusal's body span is the
//! module's. tools/check-refused.py runs them under cfg(refused), which nothing else sets, so they
//! are in no image and no verify count. design/refused-claim-per-way/.
pub mod arp_length;
pub mod arp_mapping;
pub mod arp_new;
pub mod arp_round;

use vstd::prelude::*;

use awire::*;

use crate::*;

verus! {

/// `Arp`'s parse and serialize at the round trip they exclude.
pub trait ArpRound<'a> {
    proof fn parse_trip(c: &Arp, s: Seq<u8>)
        requires
            <Arp as Combinator<'a>>::wf(c),
        ensures
            <Arp as Combinator<'a>>::spec_parse(c, s) matches Some((n, v)) ==> <Arp as Combinator<'a>>::spec_serialize(c, v) != s.take(n as int),
    ;

    proof fn serialize_trip(c: &Arp, v: ArpPacketView, rest: Seq<u8>)
        requires
            <Arp as Combinator<'a>>::wf(c),
            <Arp as Combinator<'a>>::valid(c, v),
        ensures
            <Arp as Combinator<'a>>::spec_parse(c, <Arp as Combinator<'a>>::spec_serialize(c, v) + rest) != Some((<Arp as Combinator<'a>>::spec_serialize(c, v).len(), v)),
    ;
}

/// `Arp::length`'s Some at a length that is not the serialisation's.
pub trait ArpLength<'a> {
    proof fn wrong(c: &Arp, v: ArpPacketView, n: nat)
        requires
            <Arp as Combinator<'a>>::wf(c),
        ensures
            n != <Arp as Combinator<'a>>::spec_serialize(c, v).len(),
    ;
}

/// `Arp::new` at a combinator that is not the format's.
pub trait ArpNew<'a> {
    proof fn wrong(c: &Arp)
        ensures
            !<Arp as Combinator<'a>>::wf(c),
    ;
}

/// `ArpMapping`'s conversions at a value other than the one their ensures gives.
pub trait ArpMappingReturns<'a> {
    proof fn into(m: &ArpMapping, s: ArpFields<'a>, t: ArpPacket<'a>)
        ensures
            t@ != m.spec_into(s@),
    ;

    proof fn from(m: &ArpMapping, t: &ArpPacket<'a>, s: ArpFields<'a>)
        ensures
            s@ != m.spec_from(t@),
    ;
}

} // verus!
