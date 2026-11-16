// SPDX-License-Identifier: MIT

//! `Consumer::observe` at `true` ensures the consumer took a different slot, a later publish, and
//! two atomics, and, when the producer's token is passed, that its seen count and value are the
//! producer's. An unchanged consumer (`final_self == old_self`) that returns true meets `wf` and
//! the conjuncts guarded by `!adopted`, and not the ones that say it took a publish. Those are
//! split so each function carries two of them. design/refused-claim-per-way/.
//!
//! covers: amailbox/src/lib.rs	Consumer::observe	true
//! refused: moved: adopted ==> final_self.held() != old_self.held()
//! refused: moved: adopted ==> final_self.seen() > old_self.seen()
//! refused: counted: final_self.atomics() == old_self.atomics() + if adopted { 2nat } else { 1nat }
//! refused: counted: producer is Some ==> (adopted <==> old_self.seen() < producer.unwrap().count())
//! refused: taken: producer is Some ==> final_self.seen() == producer.unwrap().count()
//! refused: taken: producer is Some ==> final_self.value() == producer.unwrap().last()

use vstd::prelude::*;

use crate::{Consumer, Mailbox, ProducerToken};

verus! {

impl<T> super::ConsumerObserve<T> for () {
    proof fn moved(
        m: &Mailbox<T>,
        old_self: Consumer<T>,
        final_self: Consumer<T>,
        producer: Option<&ProducerToken<T>>,
        adopted: bool,
    ) {
    }

    proof fn counted(
        m: &Mailbox<T>,
        old_self: Consumer<T>,
        final_self: Consumer<T>,
        producer: Option<&ProducerToken<T>>,
        adopted: bool,
    ) {
    }

    proof fn taken(
        m: &Mailbox<T>,
        old_self: Consumer<T>,
        final_self: Consumer<T>,
        producer: Option<&ProducerToken<T>>,
        adopted: bool,
    ) {
    }
}

} // verus!
