// SPDX-License-Identifier: MIT

//! `Consumer::read` ensures the result is the value in the consumer's slot. The consumer is the
//! state that gives that value; this is the ensures at another result. The requires are the
//! operation's. design/refused-claim-per-way/.
//!
//! covers: amailbox/src/lib.rs	Consumer::read	returns
//! refused: wrong: v != c.value()

use vstd::prelude::*;

use crate::{Consumer, Mailbox};

verus! {

impl<T> super::ConsumerRead<T> for () {
    proof fn wrong(c: &Consumer<T>, m: &Mailbox<T>, v: T) {}
}

} // verus!
