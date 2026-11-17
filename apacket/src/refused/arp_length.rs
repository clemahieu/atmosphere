// SPDX-License-Identifier: MIT

//! `Arp::length`'s Some at a length that is not the serialisation's. The ensures is
//! `n == spec_serialize(v).len()`; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: apacket/src/arp.rs	Arp::length	Some
//! refused: wrong: n != <Arp as Combinator<'a>>::spec_serialize(c, v).len()

use vstd::prelude::*;

use crate::*;

verus! {

impl<'a> super::ArpLength<'a> for () {
    proof fn wrong(c: &Arp, v: ArpPacketView, n: nat) {}
}

} // verus!
