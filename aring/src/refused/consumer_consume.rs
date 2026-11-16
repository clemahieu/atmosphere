// SPDX-License-Identifier: MIT

//! `Consumer::consume` ensures the consumer is `spec_consumed(n)`, so the tail has
//! advanced and the slots it handed back are no longer its. An unchanged consumer
//! (`post == pre`), returning its own tail, meets the conjuncts that say nothing
//! moved and not the ones that say it did. The ownership conjunct is its own function
//! because a function's check reports two failed postconditions, and this is the third.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Consumer::consume	returns
//! refused: unchanged: post == pre.spec_consumed(n)
//! refused: unchanged: post.tail() == advance(pre.tail(), n as int)
//! refused: owns: forall|i: u32| #![trigger post.owns(i)] #![trigger pre.owns(i)] post.owns(i) <==> (pre.owns(i) && dist(i, pre.tail()) >= n)

use vstd::prelude::*;

use crate::Consumer;

verus! {

impl super::ConsumerConsume for () {
    proof fn unchanged(pre: Consumer, post: Consumer, n: u32, index: u32) {}

    proof fn owns(pre: Consumer, post: Consumer, n: u32) {}
}

} // verus!
