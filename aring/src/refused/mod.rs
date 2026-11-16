// SPDX-License-Identifier: MIT

//! False claims for the ring. `new` is the ensures at a producer or consumer whose head is not 0.
//! A query is the ensures at the other result from the state that gives one. A write, publish,
//! consume or accepted observe is the operation's ensures at an unchanged component, and an
//! accepted observe's ensures says the end moved. The specification is the trait and the body is
//! the module, so the refusal's body span is the module's, which is the span the check joins to
//! the clause. tools/check-refused.py runs each module under cfg(refused), which nothing else
//! sets, so the claims are in no image and no verify count. design/refused-claim-per-way/.

pub mod producer_new;
pub mod producer_index;
pub mod producer_free;
pub mod producer_slot;
pub mod producer_write;
pub mod producer_publish;
pub mod producer_observe;
pub mod consumer_new;
pub mod consumer_index;
pub mod consumer_available;
pub mod consumer_slot;
pub mod consumer_read;
pub mod consumer_consume;
pub mod consumer_observe;

use vstd::prelude::*;

use crate::{Consumer, Producer, advance, capacity_ok, dist, slot};

verus! {

/// `Producer::new` at a producer whose head is not 0.
pub trait ProducerNew {
    proof fn wrong(cap: u32, p: Producer)
        requires
            capacity_ok(cap),
        ensures
            p.head() != 0,
    ;
}

/// `Producer::index` at a head other than the one the producer holds.
pub trait ProducerIndex {
    proof fn wrong(p: &Producer, i: u32)
        ensures
            i != p.head(),
    ;
}

/// `Producer::free` at a count other than the slots past the head.
pub trait ProducerFree {
    proof fn wrong(p: &Producer, n: u32)
        requires
            p.wf(),
        ensures
            n != p.cap() - p.used(),
    ;
}

/// `Producer::slot` at a slot other than the one `k` past the head names.
pub trait ProducerSlot {
    proof fn wrong(p: &Producer, k: u32, s: usize)
        requires
            p.wf(),
            k < p.cap() - p.used(),
        ensures
            s != slot(advance(p.head(), k as int), p.cap()),
    ;
}

/// `Producer::write` at an unchanged buffer.
pub trait ProducerWrite<T> {
    proof fn unchanged(p: &Producer, pre: &[T], post: &[T], k: u32, v: T)
        requires
            p.wf(),
            pre@.len() == p.cap(),
            k < p.cap() - p.used(),
            post@ == pre@,
            0 <= slot(advance(p.head(), k as int), p.cap()) < pre@.len(),
        ensures
            post@ =~= pre@.update(slot(advance(p.head(), k as int), p.cap()), v),
    ;
}

/// `Producer::publish` at an unchanged producer.
pub trait ProducerPublish {
    proof fn unchanged(pre: Producer, post: Producer, n: u32, index: u32)
        requires
            pre.wf(),
            n <= pre.cap() - pre.used(),
            post == pre,
            post.wf(),
            post.cap() == pre.cap(),
            post.tail() == pre.tail(),
            index == post.head(),
        ensures
            post == pre.spec_published(n),
            post.wf(),
            post.cap() == pre.cap(),
            post.head() == advance(pre.head(), n as int),
            post.tail() == pre.tail(),
            index == post.head(),
    ;

    proof fn owns(pre: Producer, post: Producer, n: u32)
        requires
            pre.wf(),
            n <= pre.cap() - pre.used(),
            post == pre,
        ensures
            forall|i: u32| #![trigger post.owns(i)] #![trigger pre.owns(i)] post.owns(i) <==> (pre.owns(i) && dist(i, pre.head()) >= n),
    ;
}

/// `Producer::observe`'s true at an unchanged producer, whose tail did not move.
pub trait ProducerObserve {
    proof fn unchanged(pre: Producer, post: Producer, peer_tail: u32, accepted: bool)
        requires
            pre.wf(),
            pre.accepts(peer_tail),
            post == pre,
            accepted,
            post.wf(),
            post.cap() == pre.cap(),
            post.head() == pre.head(),
            post.tail() == pre.tail(),
            forall|i: u32| pre.owns(i) ==> post.owns(i),
        ensures
            post.wf(),
            accepted == pre.accepts(peer_tail),
            accepted ==> post == pre.spec_observed(peer_tail),
            !accepted ==> post == pre,
            post.cap() == pre.cap(),
            post.head() == pre.head(),
            accepted ==> post.tail() == peer_tail,
            forall|i: u32| pre.owns(i) ==> post.owns(i),
    ;
}

/// `Consumer::new` at a consumer whose head is not 0.
pub trait ConsumerNew {
    proof fn wrong(cap: u32, c: Consumer)
        requires
            capacity_ok(cap),
        ensures
            c.head() != 0,
    ;
}

/// `Consumer::index` at a tail other than the one the consumer holds.
pub trait ConsumerIndex {
    proof fn wrong(c: &Consumer, i: u32)
        ensures
            i != c.tail(),
    ;
}

/// `Consumer::available` at a count other than the slots past the tail.
pub trait ConsumerAvailable {
    proof fn wrong(c: &Consumer, n: u32)
        requires
            c.wf(),
        ensures
            n != c.avail(),
    ;
}

/// `Consumer::slot` at a slot other than the one `k` past the tail names.
pub trait ConsumerSlot {
    proof fn wrong(c: &Consumer, k: u32, s: usize)
        requires
            c.wf(),
            k < c.avail(),
        ensures
            s != slot(advance(c.tail(), k as int), c.cap()),
    ;
}

/// `Consumer::read` at a value other than the slot `k` past the tail holds.
pub trait ConsumerRead<T: Copy> {
    proof fn wrong(c: &Consumer, slots: &[T], k: u32, v: T)
        requires
            c.wf(),
            slots@.len() == c.cap(),
            k < c.avail(),
            0 <= slot(advance(c.tail(), k as int), c.cap()) < slots@.len(),
        ensures
            v != slots@[slot(advance(c.tail(), k as int), c.cap())],
    ;
}

/// `Consumer::consume` at an unchanged consumer.
pub trait ConsumerConsume {
    proof fn unchanged(pre: Consumer, post: Consumer, n: u32, index: u32)
        requires
            pre.wf(),
            n <= pre.avail(),
            post == pre,
            post.wf(),
            post.cap() == pre.cap(),
            post.head() == pre.head(),
            index == post.tail(),
        ensures
            post == pre.spec_consumed(n),
            post.wf(),
            post.cap() == pre.cap(),
            post.head() == pre.head(),
            post.tail() == advance(pre.tail(), n as int),
            index == post.tail(),
    ;

    proof fn owns(pre: Consumer, post: Consumer, n: u32)
        requires
            pre.wf(),
            n <= pre.avail(),
            post == pre,
        ensures
            forall|i: u32| #![trigger post.owns(i)] #![trigger pre.owns(i)] post.owns(i) <==> (pre.owns(i) && dist(i, pre.tail()) >= n),
    ;
}

/// `Consumer::observe`'s true at an unchanged consumer, whose head did not move.
pub trait ConsumerObserve {
    proof fn unchanged(pre: Consumer, post: Consumer, peer_head: u32, accepted: bool)
        requires
            pre.wf(),
            pre.accepts(peer_head),
            post == pre,
            accepted,
            post.wf(),
            post.cap() == pre.cap(),
            post.tail() == pre.tail(),
            post.head() == pre.head(),
            forall|i: u32| pre.owns(i) ==> post.owns(i),
        ensures
            post.wf(),
            accepted == pre.accepts(peer_head),
            accepted ==> post == pre.spec_observed(peer_head),
            !accepted ==> post == pre,
            post.cap() == pre.cap(),
            post.tail() == pre.tail(),
            accepted ==> post.head() == peer_head,
            forall|i: u32| pre.owns(i) ==> post.owns(i),
    ;
}

} // verus!
