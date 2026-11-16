// SPDX-License-Identifier: MIT

//! `Producer::publish` ensures the producer holds a different slot, has published once more, and
//! records the value it held as its latest, after one more atomic. An unchanged producer
//! (`final_self == old_self`) meets `wf` and not those. The two that say what moved, and the two
//! that say what was recorded, are separate functions because a function's check reports two
//! failed postconditions. design/refused-claim-per-way/.
//!
//! covers: amailbox/src/lib.rs	Producer::publish	returns
//! refused: moved: final_self.held() != old_self.held()
//! refused: moved: final_self.count() == old_self.count() + 1
//! refused: recorded: final_self.last() == old_self.value()
//! refused: recorded: final_self.atomics() == old_self.atomics() + 1

use vstd::prelude::*;

use crate::{Mailbox, Producer};

verus! {

impl<T> super::ProducerPublish<T> for () {
    proof fn moved(m: &Mailbox<T>, old_self: Producer<T>, final_self: Producer<T>) {}

    proof fn recorded(m: &Mailbox<T>, old_self: Producer<T>, final_self: Producer<T>) {}
}

} // verus!
