// SPDX-License-Identifier: MIT

//! `held_apart` ensures the producer and the consumer hold different slots. This is that ensures
//! at `p.held() == c.held()`. The requires are the operation's. design/refused-claim-per-way/.
//!
//! covers: amailbox/src/lib.rs	held_apart	returns
//! refused: wrong: p.held() == c.held()

use vstd::prelude::*;

use crate::{Consumer, Mailbox, Producer};

verus! {

impl<T> super::HeldApart<T> for () {
    proof fn wrong(m: &Mailbox<T>, p: &Producer<T>, c: &Consumer<T>) {}
}

} // verus!
