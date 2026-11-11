// SPDX-License-Identifier: MIT

//! Fan-in over private rings: several producers, one consumer, one aring per producer, proven with
//! Verus against peers whose indices are untrusted. design/fan-in-over-private-rings/ says why
//! this object and not one ring with a shared cursor.
//!
//! The consumer holds one `aring::Consumer` per producer. `scan` takes a start ring, wraps, and
//! examines each ring once: a ring that already has a slot available is returned without loading
//! anything; otherwise the scan loads that ring's producer head through `Heads::load`, passes it
//! through the ring's `observe`, and returns the ring if a slot is now available. The scan does not
//! publish, consume or copy a slot, and it claims no order across producers. The caller consumes
//! on the returned ring through aring and starts the next scan past it.
//!
//! - One pass: the rings before the returned one, in wrap order from the start, were examined and
//!   have nothing available; the rings after it were not touched. `None` means every ring was
//!   examined and has nothing available.
//! - Isolation: ring `j` ends the scan related to its own state and the one head loaded for it by
//!   `examined`, whatever was loaded for any other ring. A head ring `j` rejects leaves ring `j` as
//!   it was (`lemma_rejected_unchanged`).
//! - A stopped producer stalls only its own ring: when the head loaded for ring `j` is that of an
//!   honest producer with slots in flight, the scan does not return `None`, whatever every other
//!   producer did (`lemma_scan_finds_pending`).
//!
//! Where the producers' heads live and how they are loaded, with an acquire load before the
//! consumer reads the slots, is the caller's, through its `Heads`.
#![no_std]
#![allow(unused)]

use aring::*;
use vstd::prelude::*;

verus! {

/// The producers' published heads, as the consumer loads them from shared memory.
pub trait Heads {
    /// Loads ring `ring`'s producer head. Any value may come back: the producer is untrusted.
    fn load(&self, ring: usize) -> u32;
}

/// How many rings ring `j` comes after ring `start`, wrapping at `n`.
pub open spec fn order(start: int, n: int, j: int) -> int {
    if j >= start {
        j - start
    } else {
        j - start + n
    }
}

/// Ring `c` became `d` when the scan examined it with `h` loaded as its producer's head. A ring
/// with a slot available is left as it was, and nothing is loaded for it. Otherwise the consumer
/// observes `h`: an accepted head becomes the ring's head, and a rejected one leaves the ring as
/// it was. The consumer's tail and capacity never change.
pub open spec fn examined(c: Consumer, d: Consumer, h: u32) -> bool {
    &&& d.wf()
    &&& d.cap() == c.cap()
    &&& d.tail() == c.tail()
    &&& if c.avail() == 0 && c.accepts(h) {
        &&& d == c.spec_observed(h)
        &&& d.head() == h
    } else {
        d == c
    }
}

/// Every ring was examined, with `hs` the heads loaded, and none has a slot available.
pub open spec fn idle(old: Seq<Consumer>, new: Seq<Consumer>, hs: Seq<u32>) -> bool {
    &&& new.len() == old.len()
    &&& hs.len() == old.len()
    &&& forall|j: int|
        0 <= j < old.len() ==> #[trigger] examined(old[j], new[j], hs[j]) && new[j].avail() == 0
}

/// Ring `k` is the first ring from `start` that has a slot available: it and the rings before it
/// were examined, with `hs` the heads loaded, the rings before it have nothing available, and the
/// rings after it are as they were.
pub open spec fn ready(
    old: Seq<Consumer>,
    new: Seq<Consumer>,
    hs: Seq<u32>,
    start: int,
    k: int,
) -> bool {
    let n = old.len() as int;
    &&& new.len() == old.len()
    &&& hs.len() == old.len()
    &&& 0 <= k < n
    &&& examined(old[k], new[k], hs[k])
    &&& new[k].avail() > 0
    &&& forall|j: int|
        0 <= j < n && #[trigger] order(start, n, j) < order(start, n, k) ==> examined(
            old[j],
            new[j],
            hs[j],
        ) && new[j].avail() == 0
    &&& forall|j: int| 0 <= j < n && #[trigger] order(start, n, j) > order(start, n, k) ==> new[j] == old[j]
}

/// Examines each ring once, from `start` and wrapping, and returns the first on which the consumer
/// can take a slot, with the heads it loaded.
pub fn scan<H: Heads>(rings: &mut [Consumer], heads: &H, start: usize) -> (r: (Option<usize>, Ghost<Seq<u32>>))
    requires
        start < old(rings)@.len(),
        forall|j: int| 0 <= j < old(rings)@.len() ==> #[trigger] old(rings)@[j].wf(),
    ensures
        final(rings)@.len() == old(rings)@.len(),
        forall|j: int| 0 <= j < final(rings)@.len() ==> #[trigger] final(rings)@[j].wf(),
        match r.0 {
            None => idle(old(rings)@, final(rings)@, r.1@),
            Some(k) => ready(old(rings)@, final(rings)@, r.1@, start as int, k as int),
        },
{
    let n = rings.len();
    let ghost before = rings@;
    let ghost mut hs: Seq<u32> = Seq::new(n as nat, |j: int| 0u32);
    let mut t: usize = 0;
    let mut k: usize = start;
    while t < n
        invariant
            n == rings@.len(),
            n == before.len(),
            before == old(rings)@,
            start < n,
            t <= n,
            t < n ==> k == start + t || k == start + t - n,
            t < n ==> k < n,
            t < n ==> order(start as int, n as int, k as int) == t,
            hs.len() == n,
            forall|j: int| 0 <= j < n ==> #[trigger] rings@[j].wf(),
            forall|j: int|
                0 <= j < n && #[trigger] order(start as int, n as int, j) < t ==> examined(
                    before[j],
                    rings@[j],
                    hs[j],
                ) && rings@[j].avail() == 0,
            forall|j: int|
                0 <= j < n && #[trigger] order(start as int, n as int, j) >= t ==> rings@[j]
                    == before[j],
        decreases n - t,
    {
        if rings[k].available() > 0 {
            return (Some(k), Ghost(hs));
        }
        let h = heads.load(k);
        proof {
            hs = hs.update(k as int, h);
        }
        rings[k].observe(h);
        if rings[k].available() > 0 {
            return (Some(k), Ghost(hs));
        }
        t = t + 1;
        k = if k + 1 == n {
            0
        } else {
            k + 1
        };
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] examined(before[j], rings@[j], hs[j])
        && rings@[j].avail() == 0 by {
        assert(order(start as int, n as int, j) < n);
    }
    (None, Ghost(hs))
}

/// A head the ring rejects leaves the ring as it was.
pub proof fn lemma_rejected_unchanged(c: Consumer, d: Consumer, h: u32)
    requires
        examined(c, d, h),
        !c.accepts(h),
    ensures
        d == c,
{
}

/// The ring of an honest producer with slots in flight has a slot available once the scan has
/// examined it with that producer's head, whatever the scan loaded for any other ring.
pub proof fn lemma_examined_pending<T>(
    p: Producer,
    c: Consumer,
    d: Consumer,
    slots: Seq<T>,
    q: Seq<T>,
)
    requires
        coherent(p, c, slots, q),
        q.len() > 0,
        examined(c, d, p.head()),
    ensures
        d.avail() > 0,
{
}

/// A scan that loaded ring `j`'s honest head, with slots in flight on ring `j`, does not report
/// every ring idle: a producer that stopped, or published a head its ring rejects, stalls only its
/// own ring.
pub proof fn lemma_scan_finds_pending<T>(
    old: Seq<Consumer>,
    new: Seq<Consumer>,
    hs: Seq<u32>,
    j: int,
    p: Producer,
    slots: Seq<T>,
    q: Seq<T>,
)
    requires
        0 <= j < old.len(),
        hs.len() == old.len(),
        coherent(p, old[j], slots, q),
        q.len() > 0,
        hs[j] == p.head(),
    ensures
        !idle(old, new, hs),
{
    if idle(old, new, hs) {
        assert(examined(old[j], new[j], hs[j]));
        lemma_examined_pending(p, old[j], new[j], slots, q);
    }
}

} // verus!
