// SPDX-License-Identifier: MIT

//! `Producer::slot` ensures `s == slot(advance(self.head(), k as int), self.cap())`.
//! A well-formed producer and a `k` it may write are the state that gives that slot;
//! this is the ensures at another result. The requires are the operation's.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Producer::slot	returns
//! refused: wrong: s != slot(advance(p.head(), k as int), p.cap())

use vstd::prelude::*;

use crate::Producer;

verus! {

impl super::ProducerSlot for () {
    proof fn wrong(p: &Producer, k: u32, s: usize) {}
}

} // verus!
