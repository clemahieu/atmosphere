// SPDX-License-Identifier: MIT

//! One single-producer, single-consumer ring over slots in frames the two ends share, proven with
//! Verus against a peer whose index is untrusted.
//!
//! The ring is the bulk path of design/syscall-abi-in-registers/: a message larger than five
//! register words goes through slots in shared frames, and an endpoint send wakes the other end.
//! A service uses two rings, one each way. One end may be the kernel; nothing here depends on it.
//!
//! Each end keeps its own index privately and publishes it to the peer; it reads the peer's index
//! as an arbitrary u32. Indices are free-running and wrap at 2^32; the capacity divides 2^32, so
//! index `i` names slot `i % cap` on both sides of the wrap.
//!
//! - The producer owns the indices from its head up to the last tail it accepted plus the
//!   capacity; the consumer owns the indices from its tail up to the last head it accepted.
//! - Every slot an end loads or stores is `slot(i, cap) < cap` for an index `i` it owns.
//! - Ownership moves only at `Producer::publish` (producer to consumer) and `Consumer::consume`
//!   (consumer to producer). Each end learns of the other's move by `observe`, which accepts a
//!   peer index only when it is one the peer could honestly have published, and otherwise leaves
//!   the end unchanged. Observing only adds to what an end owns.
//! - `coherent` relates an honest producer, an honest consumer, the slots and the values in flight.
//!   The lemmas show each operation keeps it, that the two ends never own one slot at once, and
//!   that what the producer wrote before a publish is what the consumer reads after it observes
//!   the new head (`lemma_publish_visible`).
//!
//! The slots are a slice in this crate. Placing them and the two indices in shared frames, with a
//! release store of an index after its slots and an acquire load before them, is the caller's.
#![no_std]

#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// Indices are u32 counters that wrap at this modulus.
pub open spec fn modulus() -> int {
    0x1_0000_0000 // not a page size: the u32 indices' modulus, 2^32
}

/// How far index `a` is ahead of index `b`, counting across the wrap.
pub open spec fn dist(a: u32, b: u32) -> int {
    if a >= b {
        a - b
    } else {
        a - b + modulus()
    }
}

/// Index `i` moved `n` places forward, wrapping.
pub open spec fn advance(i: u32, n: int) -> u32
    recommends
        0 <= n < modulus(),
{
    (if i + n < modulus() {
        i + n
    } else {
        i + n - modulus()
    }) as u32
}

/// A capacity the wrapping indices can use: one that divides 2^32, so that `i % cap` names the
/// same slot for an index and for that index plus 2^32.
pub open spec fn capacity_ok(cap: u32) -> bool {
    &&& cap > 0
    &&& modulus() % (cap as int) == 0
}

/// The slot index `i` names.
pub open spec fn slot(i: u32, cap: u32) -> int {
    (i as int) % (cap as int)
}

/// The producing end: its own head and the last consumer tail it accepted.
pub struct Producer {
    cap: u32,
    head: u32,
    tail: u32,
}

impl Producer {
    pub closed spec fn cap(&self) -> u32 {
        self.cap
    }

    pub closed spec fn head(&self) -> u32 {
        self.head
    }

    pub closed spec fn tail(&self) -> u32 {
        self.tail
    }

    pub closed spec fn spec_new(cap: u32) -> Producer {
        Producer { cap, head: 0, tail: 0 }
    }

    pub closed spec fn spec_published(self, n: u32) -> Producer {
        Producer { head: advance(self.head, n as int), ..self }
    }

    pub closed spec fn spec_observed(self, peer_tail: u32) -> Producer {
        Producer { tail: peer_tail, ..self }
    }

    /// Slots published and not yet seen released.
    pub open spec fn used(&self) -> int {
        dist(self.head(), self.tail())
    }

    pub open spec fn wf(&self) -> bool {
        &&& capacity_ok(self.cap())
        &&& self.used() <= self.cap()
    }

    /// The producer may write the slot of index `i`: at or past its head, before the accepted
    /// tail plus the capacity.
    pub open spec fn owns(&self, i: u32) -> bool {
        self.used() <= dist(i, self.tail()) < self.cap()
    }

    /// A consumer tail the producer accepts: one that moved forward, and not past the head.
    pub open spec fn accepts(&self, peer_tail: u32) -> bool {
        dist(peer_tail, self.tail()) <= self.used()
    }

    pub fn new(cap: u32) -> (p: Producer)
        requires
            capacity_ok(cap),
        ensures
            p == Producer::spec_new(cap),
            p.wf(),
            p.cap() == cap,
            p.head() == 0,
            p.tail() == 0,
    {
        Producer { cap, head: 0, tail: 0 }
    }

    /// The index this end publishes to the consumer.
    pub fn index(&self) -> (i: u32)
        ensures
            i == self.head(),
    {
        self.head
    }

    /// How many slots past the head the producer may write before it publishes.
    pub fn free(&self) -> (n: u32)
        requires
            self.wf(),
        ensures
            n == self.cap() - self.used(),
    {
        self.cap - self.head.wrapping_sub(self.tail)
    }

    /// The slot of the index `k` past the head, which the producer owns.
    pub fn slot(&self, k: u32) -> (s: usize)
        requires
            self.wf(),
            k < self.cap() - self.used(),
        ensures
            s == slot(advance(self.head(), k as int), self.cap()),
            s < self.cap(),
            self.owns(advance(self.head(), k as int)),
    {
        (self.head.wrapping_add(k) % self.cap) as usize
    }

    /// Stores `v` in the slot of the index `k` past the head.
    pub fn write<T>(&self, slots: &mut [T], k: u32, v: T)
        requires
            self.wf(),
            old(slots)@.len() == self.cap(),
            k < self.cap() - self.used(),
        ensures
            final(slots)@ =~= old(slots)@.update(slot(advance(self.head(), k as int), self.cap()), v),
    {
        let s = self.slot(k);
        slots[s] = v;
    }

    /// Hands the `n` slots past the head to the consumer; returns the head to publish.
    pub fn publish(&mut self, n: u32) -> (index: u32)
        requires
            old(self).wf(),
            n <= old(self).cap() - old(self).used(),
        ensures
            *final(self) == old(self).spec_published(n),
            final(self).wf(),
            final(self).cap() == old(self).cap(),
            final(self).head() == advance(old(self).head(), n as int),
            final(self).tail() == old(self).tail(),
            index == final(self).head(),
            forall|i: u32|
                #![trigger final(self).owns(i)]
                #![trigger old(self).owns(i)]
                final(self).owns(i) <==> (old(self).owns(i) && dist(i, old(self).head()) >= n),
    {
        self.head = self.head.wrapping_add(n);
        self.head
    }

    /// Takes the consumer's tail as read from shared memory, whatever its value. Accepts it only
    /// when it moved forward and not past the head; otherwise the producer is unchanged.
    pub fn observe(&mut self, peer_tail: u32) -> (accepted: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            accepted == old(self).accepts(peer_tail),
            accepted ==> *final(self) == old(self).spec_observed(peer_tail),
            !accepted ==> *final(self) == *old(self),
            final(self).cap() == old(self).cap(),
            final(self).head() == old(self).head(),
            accepted ==> final(self).tail() == peer_tail,
            forall|i: u32| old(self).owns(i) ==> final(self).owns(i),
    {
        if peer_tail.wrapping_sub(self.tail) <= self.head.wrapping_sub(self.tail) {
            self.tail = peer_tail;
            true
        } else {
            false
        }
    }
}

/// The consuming end: its own tail and the last producer head it accepted.
pub struct Consumer {
    cap: u32,
    head: u32,
    tail: u32,
}

impl Consumer {
    pub closed spec fn cap(&self) -> u32 {
        self.cap
    }

    pub closed spec fn head(&self) -> u32 {
        self.head
    }

    pub closed spec fn tail(&self) -> u32 {
        self.tail
    }

    pub closed spec fn spec_new(cap: u32) -> Consumer {
        Consumer { cap, head: 0, tail: 0 }
    }

    pub closed spec fn spec_consumed(self, n: u32) -> Consumer {
        Consumer { tail: advance(self.tail, n as int), ..self }
    }

    pub closed spec fn spec_observed(self, peer_head: u32) -> Consumer {
        Consumer { head: peer_head, ..self }
    }

    /// Slots seen published and not yet consumed.
    pub open spec fn avail(&self) -> int {
        dist(self.head(), self.tail())
    }

    pub open spec fn wf(&self) -> bool {
        &&& capacity_ok(self.cap())
        &&& self.avail() <= self.cap()
    }

    /// The consumer may read the slot of index `i`: at or past its tail, before the accepted head.
    pub open spec fn owns(&self, i: u32) -> bool {
        dist(i, self.tail()) < self.avail()
    }

    /// A producer head the consumer accepts: one that did not move back, and is at most the
    /// capacity past the tail.
    pub open spec fn accepts(&self, peer_head: u32) -> bool {
        self.avail() <= dist(peer_head, self.tail()) <= self.cap()
    }

    pub fn new(cap: u32) -> (c: Consumer)
        requires
            capacity_ok(cap),
        ensures
            c == Consumer::spec_new(cap),
            c.wf(),
            c.cap() == cap,
            c.head() == 0,
            c.tail() == 0,
    {
        Consumer { cap, head: 0, tail: 0 }
    }

    /// The index this end publishes to the producer.
    pub fn index(&self) -> (i: u32)
        ensures
            i == self.tail(),
    {
        self.tail
    }

    /// How many slots past the tail the consumer may read.
    pub fn available(&self) -> (n: u32)
        requires
            self.wf(),
        ensures
            n == self.avail(),
    {
        self.head.wrapping_sub(self.tail)
    }

    /// The slot of the index `k` past the tail, which the consumer owns.
    pub fn slot(&self, k: u32) -> (s: usize)
        requires
            self.wf(),
            k < self.avail(),
        ensures
            s == slot(advance(self.tail(), k as int), self.cap()),
            s < self.cap(),
            self.owns(advance(self.tail(), k as int)),
    {
        (self.tail.wrapping_add(k) % self.cap) as usize
    }

    /// Loads the slot of the index `k` past the tail.
    pub fn read<T: Copy>(&self, slots: &[T], k: u32) -> (v: T)
        requires
            self.wf(),
            slots@.len() == self.cap(),
            k < self.avail(),
        ensures
            v == slots@[slot(advance(self.tail(), k as int), self.cap())],
    {
        let s = self.slot(k);
        slots[s]
    }

    /// Hands the `n` slots past the tail back to the producer; returns the tail to publish.
    pub fn consume(&mut self, n: u32) -> (index: u32)
        requires
            old(self).wf(),
            n <= old(self).avail(),
        ensures
            *final(self) == old(self).spec_consumed(n),
            final(self).wf(),
            final(self).cap() == old(self).cap(),
            final(self).head() == old(self).head(),
            final(self).tail() == advance(old(self).tail(), n as int),
            index == final(self).tail(),
            forall|i: u32|
                #![trigger final(self).owns(i)]
                #![trigger old(self).owns(i)]
                final(self).owns(i) <==> (old(self).owns(i) && dist(i, old(self).tail()) >= n),
    {
        self.tail = self.tail.wrapping_add(n);
        self.tail
    }

    /// Takes the producer's head as read from shared memory, whatever its value. Accepts it only
    /// when it did not move back and is at most the capacity past the tail; otherwise the consumer
    /// is unchanged.
    pub fn observe(&mut self, peer_head: u32) -> (accepted: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            accepted == old(self).accepts(peer_head),
            accepted ==> *final(self) == old(self).spec_observed(peer_head),
            !accepted ==> *final(self) == *old(self),
            final(self).cap() == old(self).cap(),
            final(self).tail() == old(self).tail(),
            accepted ==> final(self).head() == peer_head,
            forall|i: u32| old(self).owns(i) ==> final(self).owns(i),
    {
        let seen = self.head.wrapping_sub(self.tail);
        let offered = peer_head.wrapping_sub(self.tail);
        if seen <= offered && offered <= self.cap {
            self.head = peer_head;
            true
        } else {
            false
        }
    }
}

/// An honest producer and an honest consumer over the same slots, with `q` the values published
/// and not yet consumed. The consumer's tail lies between the tail the producer accepted and the
/// producer's head, the head the consumer accepted is at most the producer's, and the slots from
/// the consumer's tail hold `q`.
pub open spec fn coherent<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>) -> bool {
    &&& p.wf()
    &&& c.wf()
    &&& p.cap() == c.cap()
    &&& slots.len() == p.cap()
    &&& dist(c.tail(), p.tail()) <= p.used()
    &&& c.avail() <= dist(p.head(), c.tail())
    &&& q.len() == dist(p.head(), c.tail())
    &&& forall|k: int|
        0 <= k < q.len() ==> slots[slot(advance(c.tail(), k), p.cap())] == #[trigger] q[k]
}

/// Integers 2^32 apart name the same slot.
proof fn lemma_mod_congruent(x: int, y: int, cap: u32)
    requires
        capacity_ok(cap),
        x == y || x == y + modulus() || x == y - modulus(),
    ensures
        x % (cap as int) == y % (cap as int),
{
    let c = cap as int;
    let m = modulus() / c;
    lemma_fundamental_div_mod(modulus(), c);
    assert(modulus() == c * m);
    if x == y + modulus() {
        lemma_mod_multiples_vanish(m, y, c);
    } else if x == y - modulus() {
        assert(c * (-m) == -(c * m)) by (nonlinear_arith);
        lemma_mod_multiples_vanish(-m, y, c);
    }
}

/// Distinct offsets below the capacity from one base name distinct slots.
proof fn lemma_slots_distinct(base: int, a: int, b: int, cap: u32)
    requires
        cap > 0,
        0 <= a < cap,
        0 <= b < cap,
        a != b,
    ensures
        (base + a) % (cap as int) != (base + b) % (cap as int),
{
    let c = cap as int;
    lemma_fundamental_div_mod(base + a, c);
    lemma_fundamental_div_mod(base + b, c);
    let qa = (base + a) / c;
    let qb = (base + b) / c;
    let r = (base + a) % c;
    if r == (base + b) % c {
        assert(c * (qb - qa) == b - a) by (nonlinear_arith)
            requires
                base + a == c * qa + r,
                base + b == c * qb + r,
        ;
        if qb - qa >= 1 {
            assert(c * (qb - qa) >= c) by (nonlinear_arith)
                requires
                    qb - qa >= 1,
                    c > 0,
            ;
        } else if qb - qa <= -1 {
            assert(c * (qb - qa) <= -c) by (nonlinear_arith)
                requires
                    qb - qa <= -1,
                    c > 0,
            ;
        } else {
            assert(c * (qb - qa) == 0) by (nonlinear_arith)
                requires
                    qb - qa == 0,
            ;
        }
    }
}

/// The slot of index `i` is its offset from `base`, taken from `base`.
proof fn lemma_slot_from(base: u32, i: u32, cap: u32)
    requires
        capacity_ok(cap),
    ensures
        slot(i, cap) == (base + dist(i, base)) % (cap as int),
{
    lemma_mod_congruent(base + dist(i, base), i as int, cap);
}

/// Measured from `b`, index `a` is index `m` and then the rest of the way.
proof fn lemma_dist_split(a: u32, m: u32, b: u32)
    requires
        dist(m, b) <= dist(a, b),
    ensures
        dist(a, m) == dist(a, b) - dist(m, b),
{
}

/// Both ends start at index 0 with nothing in flight.
pub proof fn lemma_start<T>(cap: u32, slots: Seq<T>)
    requires
        capacity_ok(cap),
        slots.len() == cap,
    ensures
        coherent(Producer::spec_new(cap), Consumer::spec_new(cap), slots, Seq::empty()),
{
}

/// The two ends never own one slot at once.
pub proof fn lemma_owned_disjoint<T>(
    p: Producer,
    c: Consumer,
    slots: Seq<T>,
    q: Seq<T>,
    i: u32,
    j: u32,
)
    requires
        coherent(p, c, slots, q),
        p.owns(i),
        c.owns(j),
    ensures
        slot(i, p.cap()) != slot(j, p.cap()),
{
    let cap = p.cap();
    let dct = dist(c.tail(), p.tail());
    let dj = dist(j, c.tail());
    lemma_dist_split(p.head(), c.tail(), p.tail());
    lemma_slot_from(p.tail(), i, cap);
    lemma_slot_from(c.tail(), j, cap);
    lemma_mod_congruent(c.tail() + dj, p.tail() + dct + dj, cap);
    lemma_slots_distinct(p.tail() as int, dct + dj, dist(i, p.tail()), cap);
}

/// A producer write leaves the values in flight as they were.
pub proof fn lemma_write<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>, k: u32, v: T)
    requires
        coherent(p, c, slots, q),
        k < p.cap() - p.used(),
    ensures
        coherent(p, c, slots.update(slot(advance(p.head(), k as int), p.cap()), v), q),
{
    let cap = p.cap();
    let used = p.used();
    let dct = dist(c.tail(), p.tail());
    let s = slot(advance(p.head(), k as int), cap);
    let slots2 = slots.update(s, v);
    lemma_dist_split(p.head(), c.tail(), p.tail());
    lemma_mod_congruent(advance(p.head(), k as int) as int, p.head() + k, cap);
    lemma_mod_congruent(p.head() + k, p.tail() + used + k, cap);
    lemma_mod_pos_bound(advance(p.head(), k as int) as int, cap as int);
    assert forall|j: int| 0 <= j < q.len() implies slots2[slot(advance(c.tail(), j), cap)]
        == #[trigger] q[j] by {
        lemma_mod_congruent(advance(c.tail(), j) as int, c.tail() + j, cap);
        lemma_mod_congruent(c.tail() + j, p.tail() + dct + j, cap);
        lemma_mod_pos_bound(advance(c.tail(), j) as int, cap as int);
        lemma_slots_distinct(p.tail() as int, dct + j, used + k, cap);
    }
}

/// Publishing `n` appends the `n` slots past the producer's head to the values in flight.
pub proof fn lemma_publish<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>, n: u32)
    requires
        coherent(p, c, slots, q),
        n <= p.cap() - p.used(),
    ensures
        coherent(
            p.spec_published(n),
            c,
            slots,
            q + Seq::new(n as nat, |k: int| slots[slot(advance(p.head(), k), p.cap())]),
        ),
{
}

/// The consumer accepts the producer's head and stays coherent with it.
pub proof fn lemma_consumer_observes<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>)
    requires
        coherent(p, c, slots, q),
    ensures
        c.accepts(p.head()),
        coherent(p, c.spec_observed(p.head()), slots, q),
{
}

/// What the consumer reads `k` past its tail is the `k`th value in flight.
pub proof fn lemma_read<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>, k: u32)
    requires
        coherent(p, c, slots, q),
        k < c.avail(),
    ensures
        k < q.len(),
        slots[slot(advance(c.tail(), k as int), c.cap())] == q[k as int],
{
}

/// Consuming `n` drops the first `n` values in flight.
pub proof fn lemma_consume<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>, n: u32)
    requires
        coherent(p, c, slots, q),
        n <= c.avail(),
    ensures
        coherent(p, c.spec_consumed(n), slots, q.subrange(n as int, q.len() as int)),
{
}

/// The producer accepts the consumer's tail and stays coherent with it.
pub proof fn lemma_producer_observes<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>)
    requires
        coherent(p, c, slots, q),
    ensures
        p.accepts(c.tail()),
        coherent(p.spec_observed(c.tail()), c, slots, q),
{
}

/// After the producer publishes `n` and the consumer observes the new head, the consumer reads at
/// `q.len() + k` past its tail what the producer held `k` past its old head.
pub proof fn lemma_publish_visible<T>(p: Producer, c: Consumer, slots: Seq<T>, q: Seq<T>, n: u32)
    requires
        coherent(p, c, slots, q),
        n <= p.cap() - p.used(),
    ensures
        ({
            let p2 = p.spec_published(n);
            let c2 = c.spec_observed(p2.head());
            &&& c.accepts(p2.head())
            &&& c2.avail() == q.len() + n
            &&& forall|k: int|
                0 <= k < n ==> #[trigger] slots[slot(advance(c2.tail(), q.len() + k), c2.cap())]
                    == slots[slot(advance(p.head(), k), p.cap())]
        }),
{
}

} // verus!
