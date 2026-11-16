// SPDX-License-Identifier: MIT

//! `Producer::observe` at `true` ensures the producer is `spec_observed(peer_tail)`, so
//! its tail moved to the consumer's. An unchanged producer (`post == pre`) that
//! accepts the peer tail meets every other conjunct and not the ones that say the tail moved.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Producer::observe	true
//! refused: unchanged: accepted ==> post == pre.spec_observed(peer_tail)
//! refused: unchanged: accepted ==> post.tail() == peer_tail

use vstd::prelude::*;

use crate::Producer;

verus! {

impl super::ProducerObserve for () {
    proof fn unchanged(pre: Producer, post: Producer, peer_tail: u32, accepted: bool) {}
}

} // verus!
