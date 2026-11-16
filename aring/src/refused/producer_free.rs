// SPDX-License-Identifier: MIT

//! `Producer::free` ensures `n == self.cap() - self.used()`. A well-formed producer is
//! the state that gives that count; this is the ensures at another result. The
//! requires are the operation's. design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Producer::free	returns
//! refused: wrong: n != p.cap() - p.used()

use vstd::prelude::*;

use crate::Producer;

verus! {

impl super::ProducerFree for () {
    proof fn wrong(p: &Producer, n: u32) {}
}

} // verus!
