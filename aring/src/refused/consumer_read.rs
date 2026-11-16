// SPDX-License-Identifier: MIT

//! `Consumer::read` ensures `v == slots@[slot(advance(self.tail(), k as int), self.cap())]`.
//! The consumer and the slots are the state that gives that value; this is the ensures
//! at another result. The requires are the operation's, plus the slot index in range
//! so the read is of an element the buffer holds. design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Consumer::read	returns
//! refused: wrong: v != slots@[slot(advance(c.tail(), k as int), c.cap())]

use vstd::prelude::*;

use crate::Consumer;

verus! {

impl<T: Copy> super::ConsumerRead<T> for () {
    proof fn wrong(c: &Consumer, slots: &[T], k: u32, v: T) {}
}

} // verus!
