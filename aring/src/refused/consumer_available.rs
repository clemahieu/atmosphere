// SPDX-License-Identifier: MIT

//! `Consumer::available` ensures `n == self.avail()`. A well-formed consumer is the
//! state that gives that count; this is the ensures at another result. The requires
//! are the operation's. design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Consumer::available	returns
//! refused: wrong: n != c.avail()

use vstd::prelude::*;

use crate::Consumer;

verus! {

impl super::ConsumerAvailable for () {
    proof fn wrong(c: &Consumer, n: u32) {}
}

} // verus!
