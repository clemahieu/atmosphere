// SPDX-License-Identifier: MIT

//! `Consumer::observe` at `true` ensures the consumer is `spec_observed(peer_head)`, so
//! its head moved to the producer's. An unchanged consumer (`post == pre`) that
//! accepts the peer head meets every other conjunct and not the ones that say the head moved.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Consumer::observe	true
//! refused: unchanged: accepted ==> post == pre.spec_observed(peer_head)
//! refused: unchanged: accepted ==> post.head() == peer_head

use vstd::prelude::*;

use crate::Consumer;

verus! {

impl super::ConsumerObserve for () {
    proof fn unchanged(pre: Consumer, post: Consumer, peer_head: u32, accepted: bool) {}
}

} // verus!
