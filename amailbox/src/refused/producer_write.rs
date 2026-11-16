// SPDX-License-Identifier: MIT

//! `Producer::write` ensures the producer's slot holds `v` and that nothing else about the
//! producer changed. `final_self == old_self` is that producer, and the slot it writes is the
//! permission it holds, so the buffer is unchanged with it. The value conjunct is the one this
//! does not meet. design/refused-claim-per-way/.
//!
//! covers: amailbox/src/lib.rs	Producer::write	returns
//! refused: unchanged: final_self.value() == v

use vstd::prelude::*;

use crate::{Mailbox, Producer};

verus! {

impl<T> super::ProducerWrite<T> for () {
    proof fn unchanged(m: &Mailbox<T>, old_self: Producer<T>, final_self: Producer<T>, v: T) {}
}

} // verus!
