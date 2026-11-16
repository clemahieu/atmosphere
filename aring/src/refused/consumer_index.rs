// SPDX-License-Identifier: MIT

//! `Consumer::index` ensures `i == self.tail()`. The consumer is the state that gives
//! that tail; this is the ensures at another result. design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Consumer::index	returns
//! refused: wrong: i != c.tail()

use vstd::prelude::*;

use crate::Consumer;

verus! {

impl super::ConsumerIndex for () {
    proof fn wrong(c: &Consumer, i: u32) {}
}

} // verus!
