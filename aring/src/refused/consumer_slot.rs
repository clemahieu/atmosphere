// SPDX-License-Identifier: MIT

//! `Consumer::slot` ensures `s == slot(advance(self.tail(), k as int), self.cap())`.
//! A well-formed consumer and a `k` it may read are the state that gives that slot;
//! this is the ensures at another result. The requires are the operation's.
//! design/refused-claim-per-way/.
//!
//! covers: aring/src/lib.rs	Consumer::slot	returns
//! refused: wrong: s != slot(advance(c.tail(), k as int), c.cap())

use vstd::prelude::*;

use crate::Consumer;

verus! {

impl super::ConsumerSlot for () {
    proof fn wrong(c: &Consumer, k: u32, s: usize) {}
}

} // verus!
