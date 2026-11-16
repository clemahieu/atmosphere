// SPDX-License-Identifier: MIT

//! `Producer::write` ensures `final(slots)@ =~= old(slots)@.update(...)`. `pre` and
//! `post` are that buffer's view before and after, and `post@ == pre@` is the buffer
//! unchanged, so the ensures is the operation's at a buffer the write did not change.
//! The requires are the operation's, plus that unchanged buffer and the slot index in
//! range. design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Producer::write	returns
//! refused: unchanged: post@ =~= pre@.update(slot(advance(p.head(), k as int), p.cap()), v)

use vstd::prelude::*;

use crate::Producer;

verus! {

impl<T> super::ProducerWrite<T> for () {
    proof fn unchanged(p: &Producer, pre: &[T], post: &[T], k: u32, v: T) {}
}

} // verus!
