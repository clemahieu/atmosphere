// SPDX-License-Identifier: MIT

//! `Producer::index` ensures `i == self.head()`. The producer is the state that gives
//! that head; this is the ensures at another result. design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Producer::index	returns
//! refused: wrong: i != p.head()

use vstd::prelude::*;

use crate::Producer;

verus! {

impl super::ProducerIndex for () {
    proof fn wrong(p: &Producer, i: u32) {}
}

} // verus!
