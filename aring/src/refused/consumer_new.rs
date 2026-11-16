// SPDX-License-Identifier: MIT

//! `Consumer::new` ensures `c.head() == 0`. This is that ensures at a consumer whose
//! head is not 0, the output it excludes. The requires are the operation's.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Consumer::new	returns
//! refused: wrong: c.head() != 0

use vstd::prelude::*;

use crate::Consumer;

verus! {

impl super::ConsumerNew for () {
    proof fn wrong(cap: u32, c: Consumer) {}
}

} // verus!
