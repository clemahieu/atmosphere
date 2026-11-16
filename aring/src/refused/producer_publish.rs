// SPDX-License-Identifier: MIT

//! `Producer::publish` ensures the producer is `spec_published(n)`, so the head has
//! advanced and the slots it handed over are no longer its. An unchanged producer
//! (`post == pre`), returning its own head, meets the conjuncts that say nothing
//! moved and not the ones that say it did. The ownership conjunct is its own function
//! because a function's check reports two failed postconditions, and this is the third.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Producer::publish	returns
//! refused: unchanged: post == pre.spec_published(n)
//! refused: unchanged: post.head() == advance(pre.head(), n as int)
//! refused: owns: forall|i: u32| #![trigger post.owns(i)] #![trigger pre.owns(i)] post.owns(i) <==> (pre.owns(i) && dist(i, pre.head()) >= n)

use vstd::prelude::*;

use crate::Producer;

verus! {

impl super::ProducerPublish for () {
    proof fn unchanged(pre: Producer, post: Producer, n: u32, index: u32) {}

    proof fn owns(pre: Producer, post: Producer, n: u32) {}
}

} // verus!
