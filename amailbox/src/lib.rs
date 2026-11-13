// SPDX-License-Identifier: MIT

//! A latest-value mailbox: one producer, one consumer, three slots and one shared atomic word,
//! proven with Verus. design/latest-value-by-three-slot-exchange/ says why this object and not a
//! seqlock or a one-slot ring.
//!
//! Each end holds one slot privately. The word holds the third slot's index in its low two bits
//! and, in the next bit, whether that slot is a publish the consumer has not taken.
//!
//! - `Producer::write` stores into the producer's slot. `Producer::publish` is one swap that
//!   installs the producer's index with the fresh bit set and takes the index that comes back,
//!   whatever the consumer is doing: its atomic count is one.
//! - `Consumer::observe` loads the word once. A stale word leaves the consumer's slot in place. A
//!   fresh word is followed by one swap that installs the consumer's index with the fresh bit clear
//!   and takes the fresh slot. There is no retry: one or two atomics.
//! - `Exchange` is the invariant every atomic step keeps: the three indices are a permutation of
//!   0, 1 and 2, so the producer never holds the slot the consumer holds; the word is fresh exactly
//!   when the producer has published past what the consumer took; a fresh word's slot holds the
//!   latest publish, and a stale word means the consumer holds it. Intermediate publishes may be
//!   overwritten before any observe.
//!
//! Both ends follow the protocol. A peer that can store an arbitrary word can hand back the slot
//! the other end holds, so across a distrust boundary the path is aring. Placing the slots and the
//! word in shared frames is the caller's.
#![no_std]
// A cargo build erases specifications and proofs, so there a variable only they read looks unused.
#![cfg_attr(not(verus_keep_ghost), allow(unused_variables))]

#[cfg(not(verus_keep_ghost))]
use core::marker::PhantomData;
use vstd::atomic_ghost::*;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::cell::CellId;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::ghost_var::GhostVar;
use vstd::resource::ghost_var::GhostVarAuth;
use vstd::resource::Loc;

verus! {

/// The bits of the word that name the shared slot.
pub const INDEX: u32 = 3;

/// The bit that marks the shared slot as a publish the consumer has not taken.
pub const FRESH: u32 = 4;

/// The slot a word names.
pub open spec fn index(w: u32) -> u32 {
    w & 3
}

/// Whether a word marks its slot as a publish the consumer has not taken.
pub open spec fn fresh(w: u32) -> bool {
    w & 4 != 0
}

/// A word the protocol writes: an index below three, the fresh bit, and no other bit.
pub open spec fn word_ok(w: u32) -> bool {
    &&& w < 8
    &&& index(w) < 3
}

/// Three slot indices that are 0, 1 and 2 in some order.
pub open spec fn permutation(a: u32, b: u32, c: u32) -> bool {
    &&& a < 3
    &&& b < 3
    &&& c < 3
    &&& a != b
    &&& b != c
    &&& a != c
}

/// The fixed names of one mailbox: its three cells and the two ends' ghost variables.
pub ghost struct Ids {
    pub cells: Seq<CellId>,
    pub producer: Loc,
    pub consumer: Loc,
}

/// The producer's ghost state: the slot it holds, how many times it has published, and the value
/// of its latest publish.
pub ghost struct ProducerView<T> {
    pub held: u32,
    pub count: nat,
    pub last: T,
}

/// The consumer's ghost state: the slot it holds, which publish that slot is, the value in it, and
/// whether its last load found the word fresh. Only the consumer clears the fresh bit, so a fresh
/// load stays fresh until its swap.
pub ghost struct ConsumerView<T> {
    pub held: u32,
    pub seen: nat,
    pub value: T,
    pub armed: bool,
}

/// The producer's ghost token, held in `Producer::token` so a caller holding `&Producer<T>` can
/// pass `Tracked(Some(p.token.borrow()))` to `Consumer::observe` with no runtime argument.
pub tracked struct ProducerToken<T> {
    // Only proofs read the variable, so only Verus compiles it.
    #[cfg(verus_keep_ghost)]
    tracked var: GhostVar<ProducerView<T>>,
    #[cfg(not(verus_keep_ghost))]
    v: PhantomData<T>,
}

impl<T> ProducerToken<T> {
    /// Whether this token belongs to `m`'s producer.
    pub closed spec fn wf(&self, m: &Mailbox<T>) -> bool {
        self.var.id() == m.ids().producer
    }

    /// How many times the producer has published.
    pub closed spec fn count(&self) -> nat {
        self.var@.count
    }

    /// The value of the latest publish.
    pub closed spec fn last(&self) -> T {
        self.var@.last
    }
}

/// What the word's invariant owns: the shared slot's permission and each end's authoritative ghost
/// state.
pub tracked struct Shared<T> {
    pub tracked slot: PointsTo<T>,
    pub tracked producer: GhostVarAuth<ProducerView<T>>,
    pub tracked consumer: GhostVarAuth<ConsumerView<T>>,
}

/// The invariant of the word, kept by every atomic step of either end.
pub struct Exchange;

impl<T> AtomicInvariantPredicate<Ids, u32, Shared<T>> for Exchange {
    open spec fn atomic_inv(k: Ids, w: u32, g: Shared<T>) -> bool {
        let p = g.producer@;
        let c = g.consumer@;
        &&& word_ok(w)
        &&& k.cells.len() == 3
        &&& g.slot.id() == k.cells[index(w) as int]
        &&& g.producer.id() == k.producer
        &&& g.consumer.id() == k.consumer
        // The producer, the consumer and the word name different slots.
        &&& permutation(index(w), p.held, c.held)
        // The word is fresh exactly when the producer has published past what the consumer took.
        &&& c.seen <= p.count
        &&& fresh(w) <==> c.seen < p.count
        // The latest publish is in the shared slot when the word is fresh, and with the consumer
        // when it is stale.
        &&& fresh(w) ==> *g.slot.value() == p.last
        &&& !fresh(w) ==> c.value == p.last && c.seen == p.count
        &&& c.armed ==> fresh(w)
    }
}

/// The word's bits for an index below three, with and without the fresh bit.
proof fn lemma_word(h: u32)
    requires
        h < 3,
    ensures
        index(h) == h,
        !fresh(h),
        word_ok(h),
        index(h | 4) == h,
        fresh(h | 4),
        word_ok(h | 4),
{
    assert(h & 3 == h && h & 4 == 0 && (h | 4) & 3 == h && (h | 4) & 4 != 0 && (h | 4) < 8)
        by (bit_vector)
        requires
            h < 3,
    ;
}

/// Three slots and the word between the two ends.
pub struct Mailbox<T> {
    word: AtomicU32<Ids, Shared<T>, Exchange>,
    s0: PCell<T>,
    s1: PCell<T>,
    s2: PCell<T>,
}

impl<T> Mailbox<T> {
    pub closed spec fn ids(&self) -> Ids {
        self.word.constant()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.word.well_formed()
        &&& self.ids().cells == seq![self.s0.id(), self.s1.id(), self.s2.id()]
    }

    /// The cell of slot `i`.
    fn cell(&self, i: u32) -> (c: &PCell<T>)
        requires
            self.wf(),
            i < 3,
        ensures
            c.id() == self.ids().cells[i as int],
    {
        if i == 0 {
            &self.s0
        } else if i == 1 {
            &self.s1
        } else {
            &self.s2
        }
    }

    /// A mailbox whose slots hold `v0`, `v1` and `v2`. The producer holds slot 0, the consumer
    /// holds slot 1 and takes `v1` as the latest value, and the word names slot 2, stale.
    pub fn new(v0: T, v1: T, v2: T) -> (r: (Mailbox<T>, Producer<T>, Consumer<T>))
        ensures
            r.0.wf(),
            r.1.wf(&r.0),
            r.2.wf(&r.0),
            r.1.held() == 0,
            r.1.value() == v0,
            r.1.count() == 0,
            r.1.last() == v1,
            r.1.atomics() == 0,
            r.2.held() == 1,
            r.2.value() == v1,
            r.2.seen() == 0,
            r.2.atomics() == 0,
    {
        let (s0, Tracked(p0)) = PCell::new(v0);
        let (s1, Tracked(p1)) = PCell::new(v1);
        let (s2, Tracked(p2)) = PCell::new(v2);
        let tracked (pa, pv) = GhostVarAuth::new(
            ProducerView { held: 0, count: 0, last: *p1.value() },
        );
        let tracked (ca, cv) = GhostVarAuth::new(
            ConsumerView { held: 1, seen: 0, value: *p1.value(), armed: false },
        );
        let ghost ids = Ids {
            cells: seq![s0.id(), s1.id(), s2.id()],
            producer: pa.id(),
            consumer: ca.id(),
        };
        proof {
            lemma_word(2);
        }
        let word = AtomicU32::new(
            Ghost(ids),
            2,
            Tracked(Shared { slot: p2, producer: pa, consumer: ca }),
        );
        let m = Mailbox { word, s0, s1, s2 };
        let p = Producer {
            slot: ProducerSlot {
                held: 0,
                #[cfg(verus_keep_ghost)]
                perm: Tracked(p0),
                #[cfg(not(verus_keep_ghost))]
                v: PhantomData,
                atomics: Ghost(0),
            },
            token: Tracked(ProducerToken { var: pv }),
        };
        let c = Consumer {
            held: 1,
            #[cfg(verus_keep_ghost)]
            perm: Tracked(p1),
            #[cfg(verus_keep_ghost)]
            token: Tracked(cv),
            #[cfg(not(verus_keep_ghost))]
            v: PhantomData,
            atomics: Ghost(0),
        };
        (m, p, c)
    }
}

/// The private slot state of `Producer<T>`, kept opaque so `Producer::token` can be borrowed in
/// ghost code without exposing the slot index or permission.
pub struct ProducerSlot<T> {
    held: u32,
    // Only proofs read the permission, so only Verus compiles it.
    #[cfg(verus_keep_ghost)]
    perm: Tracked<PointsTo<T>>,
    #[cfg(not(verus_keep_ghost))]
    v: PhantomData<T>,
    atomics: Ghost<nat>,
}

impl<T> ProducerSlot<T> {
    pub closed spec fn wf(&self, m: &Mailbox<T>, token: ProducerToken<T>) -> bool {
        &&& self.held < 3
        &&& self.perm@.id() == m.ids().cells[self.held as int]
        &&& token.var.id() == m.ids().producer
        &&& token.var@.held == self.held
    }
}

/// The producing end.
pub struct Producer<T> {
    pub slot: ProducerSlot<T>,
    /// The producer's ghost token, for `Consumer::observe` when the caller holds both ends.
    pub token: Tracked<ProducerToken<T>>,
}

impl<T> Producer<T> {
    /// The slot the producer holds and may write.
    pub closed spec fn held(&self) -> u32 {
        self.slot.held
    }

    /// The value in the producer's slot.
    pub closed spec fn value(&self) -> T {
        *self.slot.perm@.value()
    }

    /// How many times the producer has published.
    pub open spec fn count(&self) -> nat {
        self.token@.count()
    }

    /// The value of the latest publish.
    pub open spec fn last(&self) -> T {
        self.token@.last()
    }

    /// How many atomic operations on the word this end has performed.
    pub closed spec fn atomics(&self) -> nat {
        self.slot.atomics@
    }

    pub open spec fn wf(&self, m: &Mailbox<T>) -> bool {
        &&& self.slot.wf(m, self.token@)
        &&& self.token@.wf(m)
    }

    /// Stores `v` in the producer's slot. Nothing else changes: the slot is the producer's alone.
    pub fn write(&mut self, m: &Mailbox<T>, v: T)
        requires
            m.wf(),
            old(self).wf(m),
        ensures
            final(self).wf(m),
            final(self).held() == old(self).held(),
            final(self).value() == v,
            final(self).count() == old(self).count(),
            final(self).last() == old(self).last(),
            final(self).atomics() == old(self).atomics(),
    {
        let cell = m.cell(self.slot.held);
        cell.write(Tracked(self.slot.perm.borrow_mut()), v);
    }

    /// Hands the producer's slot to the consumer as the latest value, and takes the slot the word
    /// named. One swap, whatever the consumer is doing; the slot taken is not the consumer's.
    pub fn publish(&mut self, m: &Mailbox<T>)
        requires
            m.wf(),
            old(self).wf(m),
        ensures
            final(self).wf(m),
            final(self).held() != old(self).held(),
            final(self).count() == old(self).count() + 1,
            final(self).last() == old(self).value(),
            final(self).atomics() == old(self).atomics() + 1,
    {
        proof {
            lemma_word(self.slot.held);
        }
        let ghost held = self.slot.held;
        let ghost value = self.value();
        let back = atomic_with_ghost!(&m.word => swap(self.slot.held | FRESH);
            update prev -> next;
            ghost g => {
                g.producer.agree(&self.token.borrow().var);
                vstd::modes::tracked_swap(self.slot.perm.borrow_mut(), &mut g.slot);
                let count = self.token@.var@.count + 1;
                let tracked tok = self.token.borrow_mut();
                g.producer.update(
                    &mut tok.var,
                    ProducerView { held: index(prev), count, last: value },
                );
                let c = g.consumer@;
                if c.armed {
                    assert(fresh(next));
                }
            }
        );
        proof {
            assert(back & 3 == index(back));
        }
        self.slot.held = back & INDEX;
        self.slot.atomics = Ghost(self.slot.atomics@ + 1);
    }
}

/// The consuming end.
pub struct Consumer<T> {
    held: u32,
    // Only proofs read the permission and the token, so only Verus compiles them.
    #[cfg(verus_keep_ghost)]
    perm: Tracked<PointsTo<T>>,
    #[cfg(verus_keep_ghost)]
    token: Tracked<GhostVar<ConsumerView<T>>>,
    #[cfg(not(verus_keep_ghost))]
    v: PhantomData<T>,
    atomics: Ghost<nat>,
}

impl<T> Consumer<T> {
    /// The slot the consumer holds and may read.
    pub closed spec fn held(&self) -> u32 {
        self.held
    }

    /// The value in the consumer's slot.
    pub closed spec fn value(&self) -> T {
        *self.perm@.value()
    }

    /// Which publish the consumer's slot holds, counting from 1; 0 is the initial value.
    pub closed spec fn seen(&self) -> nat {
        self.token@@.seen
    }

    /// How many atomic operations on the word this end has performed.
    pub closed spec fn atomics(&self) -> nat {
        self.atomics@
    }

    pub closed spec fn wf(&self, m: &Mailbox<T>) -> bool {
        &&& self.held < 3
        &&& self.perm@.id() == m.ids().cells[self.held as int]
        &&& self.token@.id() == m.ids().consumer
        &&& self.token@@.held == self.held
        &&& self.token@@.value == *self.perm@.value()
        &&& !self.token@@.armed
    }

    /// The value in the consumer's slot, read in place.
    pub fn read<'a>(&'a self, m: &'a Mailbox<T>) -> (v: &'a T)
        requires
            m.wf(),
            self.wf(m),
        ensures
            *v == self.value(),
    {
        let cell = m.cell(self.held);
        cell.borrow(Tracked(self.perm.borrow()))
    }

    /// Takes the latest publish when the word is fresh. One load; when it finds the word stale the
    /// consumer's slot stays where it is, and when it finds it fresh one swap takes the fresh slot
    /// and returns the consumer's. Returns whether the consumer took a newer publish.
    ///
    /// A caller holding `&Producer<T>` passes `Tracked(Some(p.token.borrow()))` to connect `adopted`
    /// and the resulting slot to `p.count()` and `p.last()`; a caller without the producer passes
    /// `Tracked(None)`.
    pub fn observe(
        &mut self,
        m: &Mailbox<T>,
        Tracked(producer): Tracked<Option<&ProducerToken<T>>>,
    ) -> (adopted: bool)
        requires
            m.wf(),
            old(self).wf(m),
            producer is Some ==> producer.unwrap().wf(m),
        ensures
            final(self).wf(m),
            !adopted ==> final(self).held() == old(self).held(),
            !adopted ==> final(self).value() == old(self).value(),
            !adopted ==> final(self).seen() == old(self).seen(),
            adopted ==> final(self).held() != old(self).held(),
            adopted ==> final(self).seen() > old(self).seen(),
            final(self).atomics() == old(self).atomics() + if adopted {
                2nat
            } else {
                1nat
            },
            producer is Some ==> (adopted <==> old(self).seen() < producer.unwrap().count()),
            producer is Some ==> final(self).seen() == producer.unwrap().count(),
            producer is Some ==> final(self).value() == producer.unwrap().last(),
    {
        let w = atomic_with_ghost!(&m.word => load();
            returning r;
            ghost g => {
                g.consumer.agree(self.token.borrow());
                if let Some(pt) = &producer {
                    g.producer.agree(&pt.var);
                }
                if fresh(r) {
                    let c = g.consumer@;
                    g.consumer.update(self.token.borrow_mut(), ConsumerView { armed: true, ..c });
                }
            }
        );
        if w & FRESH == 0 {
            proof {
                assert(!fresh(w)) by (bit_vector)
                    requires
                        w & 4 == 0,
                ;
            }
            self.atomics = Ghost(self.atomics@ + 1);
            return false;
        }
        proof {
            assert(fresh(w)) by (bit_vector)
                requires
                    w & 4 != 0,
            ;
            lemma_word(self.held);
        }
        let ghost old_seen = self.seen();
        let back = atomic_with_ghost!(&m.word => swap(self.held);
            update prev -> next;
            ghost g => {
                g.consumer.agree(self.token.borrow());
                if let Some(pt) = &producer {
                    g.producer.agree(&pt.var);
                }
                let p = g.producer@;
                vstd::modes::tracked_swap(self.perm.borrow_mut(), &mut g.slot);
                g.consumer.update(
                    self.token.borrow_mut(),
                    ConsumerView { held: index(prev), seen: p.count, value: p.last, armed: false },
                );
            }
        );
        proof {
            assert(back & 3 == index(back));
        }
        self.held = back & INDEX;
        self.atomics = Ghost(self.atomics@ + 2);
        true
    }
}

/// For a producer and a consumer of one mailbox, the slots they hold differ. A ghost step on the
/// word, with no instruction.
pub fn held_apart<T>(m: &Mailbox<T>, p: &Producer<T>, c: &Consumer<T>)
    requires
        m.wf(),
        p.wf(m),
        c.wf(m),
    ensures
        p.held() != c.held(),
{
    atomic_with_ghost!(&m.word => no_op();
        ghost g => {
            g.producer.agree(&p.token.borrow().var);
            g.consumer.agree(c.token.borrow());
        }
    );
}

} // verus!

#[cfg(throwaway)]
pub mod throwaway;
#[cfg(verus_keep_ghost)]
pub mod witness;
