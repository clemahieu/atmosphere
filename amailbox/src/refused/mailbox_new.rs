// SPDX-License-Identifier: MIT

//! `Mailbox::new` ensures the producer's held slot, value, count, last publish and atomic count,
//! and the consumer's held slot, value, seen count and atomic count. This is that ensures at a
//! mailbox whose fields are not those. The requires are the operation's, which has none.
//! design/refused-claim-per-way/.
//!
//! covers: amailbox/src/lib.rs	Mailbox::new	returns
//! refused: wrong: !(r.1.held() == 0 && r.1.value() == v0 && r.1.count() == 0 && r.1.last() == v1 && r.1.atomics() == 0)
//! refused: wrong: !(r.2.held() == 1 && r.2.value() == v1 && r.2.seen() == 0 && r.2.atomics() == 0)

use vstd::prelude::*;

use crate::{Consumer, Mailbox, Producer};

verus! {

impl<T> super::MailboxNew<T> for () {
    proof fn wrong(v0: T, v1: T, v2: T, r: (Mailbox<T>, Producer<T>, Consumer<T>)) {}
}

} // verus!
