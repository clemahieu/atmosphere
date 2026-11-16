// SPDX-License-Identifier: MIT

//! False claims for the mailbox. `Mailbox::new` is the ensures at a mailbox whose fields are not
//! the ones `new` ensures. `held_apart` is the ensures at a producer and a consumer that hold the
//! same slot. `Consumer::read` is the ensures at a value other than the one the consumer's slot
//! holds. `Producer::write`, `Producer::publish` and `Consumer::observe`'s true are the operation's
//! ensures at an unchanged end; the slot that end writes is the permission it holds, so the buffer
//! is unchanged with the end. The specification is the trait and the body is the module, so the
//! refusal's body span is the module's, which is the span the check joins to the clause.
//! tools/check-refused.py runs each module under cfg(refused), which nothing else sets, so the
//! claims are in no image and no verify count. design/refused-claim-per-way/.

pub mod consumer_observe;
pub mod consumer_read;
pub mod held_apart;
pub mod mailbox_new;
pub mod producer_publish;
pub mod producer_write;

use vstd::prelude::*;

use crate::{Consumer, Mailbox, Producer, ProducerToken};

verus! {

/// `Mailbox::new` at a mailbox whose producer and consumer fields are not the ones `new` ensures.
pub trait MailboxNew<T> {
    proof fn wrong(v0: T, v1: T, v2: T, r: (Mailbox<T>, Producer<T>, Consumer<T>))
        ensures
            !(r.1.held() == 0 && r.1.value() == v0 && r.1.count() == 0 && r.1.last() == v1 && r.1.atomics() == 0),
            !(r.2.held() == 1 && r.2.value() == v1 && r.2.seen() == 0 && r.2.atomics() == 0),
    ;
}

/// `Producer::write` at an unchanged producer. The ensures is the operation's.
pub trait ProducerWrite<T> {
    proof fn unchanged(m: &Mailbox<T>, old_self: Producer<T>, final_self: Producer<T>, v: T)
        requires
            m.wf(),
            old_self.wf(m),
            final_self == old_self,
        ensures
            final_self.wf(m),
            final_self.held() == old_self.held(),
            final_self.value() == v,
            final_self.count() == old_self.count(),
            final_self.last() == old_self.last(),
            final_self.atomics() == old_self.atomics(),
    ;
}

/// `Producer::publish` at an unchanged producer. The ensures is the operation's. The conjuncts that
/// say the end moved are split so each function carries two of them: a function's check reports two
/// failed postconditions.
pub trait ProducerPublish<T> {
    proof fn moved(m: &Mailbox<T>, old_self: Producer<T>, final_self: Producer<T>)
        requires
            m.wf(),
            old_self.wf(m),
            final_self == old_self,
        ensures
            final_self.wf(m),
            final_self.held() != old_self.held(),
            final_self.count() == old_self.count() + 1,
    ;

    proof fn recorded(m: &Mailbox<T>, old_self: Producer<T>, final_self: Producer<T>)
        requires
            m.wf(),
            old_self.wf(m),
            final_self == old_self,
        ensures
            final_self.last() == old_self.value(),
            final_self.atomics() == old_self.atomics() + 1,
    ;
}

/// `Consumer::read` at a value other than the one the state gives. The requires are the operation's.
pub trait ConsumerRead<T> {
    proof fn wrong(c: &Consumer<T>, m: &Mailbox<T>, v: T)
        requires
            m.wf(),
            c.wf(m),
        ensures
            v != c.value(),
    ;
}

/// `Consumer::observe`'s true at an unchanged consumer. The requires are the operation's, the
/// consumer unchanged and the result true. The conjuncts an unchanged consumer meets stay with
/// `moved`; each function carries at most two conjuncts the unchanged consumer does not meet.
pub trait ConsumerObserve<T> {
    proof fn moved(
        m: &Mailbox<T>,
        old_self: Consumer<T>,
        final_self: Consumer<T>,
        producer: Option<&ProducerToken<T>>,
        adopted: bool,
    )
        requires
            m.wf(),
            old_self.wf(m),
            producer is Some ==> producer.unwrap().wf(m),
            final_self == old_self,
            adopted,
        ensures
            final_self.wf(m),
            !adopted ==> final_self.held() == old_self.held(),
            !adopted ==> final_self.value() == old_self.value(),
            !adopted ==> final_self.seen() == old_self.seen(),
            adopted ==> final_self.held() != old_self.held(),
            adopted ==> final_self.seen() > old_self.seen(),
    ;

    proof fn counted(
        m: &Mailbox<T>,
        old_self: Consumer<T>,
        final_self: Consumer<T>,
        producer: Option<&ProducerToken<T>>,
        adopted: bool,
    )
        requires
            m.wf(),
            old_self.wf(m),
            producer is Some ==> producer.unwrap().wf(m),
            final_self == old_self,
            adopted,
        ensures
            final_self.atomics() == old_self.atomics() + if adopted { 2nat } else { 1nat },
            producer is Some ==> (adopted <==> old_self.seen() < producer.unwrap().count()),
    ;

    proof fn taken(
        m: &Mailbox<T>,
        old_self: Consumer<T>,
        final_self: Consumer<T>,
        producer: Option<&ProducerToken<T>>,
        adopted: bool,
    )
        requires
            m.wf(),
            old_self.wf(m),
            producer is Some ==> producer.unwrap().wf(m),
            final_self == old_self,
            adopted,
        ensures
            producer is Some ==> final_self.seen() == producer.unwrap().count(),
            producer is Some ==> final_self.value() == producer.unwrap().last(),
    ;
}

/// `held_apart` at a producer and a consumer that hold one slot. The requires are the operation's.
pub trait HeldApart<T> {
    proof fn wrong(m: &Mailbox<T>, p: &Producer<T>, c: &Consumer<T>)
        requires
            m.wf(),
            p.wf(m),
            c.wf(m),
        ensures
            p.held() == c.held(),
    ;
}

} // verus!
