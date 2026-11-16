// SPDX-License-Identifier: MIT

//! `Producer::new` ensures `p.head() == 0`. This is that ensures at a producer whose
//! head is not 0, the output it excludes. The requires are the operation's.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Producer::new	returns
//! refused: wrong: p.head() != 0

use vstd::prelude::*;

use crate::Producer;

verus! {

impl super::ProducerNew for () {
    proof fn wrong(cap: u32, p: Producer) {}
}

} // verus!
