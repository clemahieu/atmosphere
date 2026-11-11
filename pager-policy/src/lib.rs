// SPDX-License-Identifier: MIT

//! The default pager's replacement policy, S3-FIFO (Yang et al., SOSP 2023) on sampled reference
//! bits, specified with Verus.
//!
//! The pager holds a pool of frames. Each frame it holds backs one resident page, which is in one
//! of two FIFO queues: the small queue, at most a tenth of the pool, where a page faulted in for the
//! first time waits to show it is used again; and the main queue. A third queue, the ghost queue,
//! holds the identities of pages evicted from the small queue, bounded by the main queue's share of
//! the pool, so that a page faulted in again soon after goes straight to the main queue.
//!
//! - A fault on a page that is not resident inserts it: into the main queue when its identity is in
//!   the ghost queue, which it then leaves, and otherwise into the small queue.
//! - The tail of the small queue is promoted to the main queue when its referenced count is above
//!   zero, and otherwise evicted, its identity entering the ghost queue (the oldest identity there
//!   leaving when it is full).
//! - The tail of the main queue is reinserted at the head with its count decremented when the count
//!   is above zero, and otherwise evicted.
//!
//! The referenced count is the number of sampling periods, capped at three, at whose end the page's
//! reference bit was found set, counting only periods after the one the page was inserted in. The
//! bit is what the pager sees of the hardware accessed bit: the probe reads and clears it once a
//! period, and an unmap returns it. A page that looks cold is confirmed by an unmap before it is
//! evicted; a refault of the unmapped page maps it again and sets the bit, so it counts as a
//! reference and the page cannot be evicted until a period's end has counted it.
//!
//! `Policy::next` is the transition relation over `Step`, guarded by `Policy::enabled`; `Policy::inv`
//! is what every reachable state keeps (`lemma_next_inv`, `lemma_run_inv`). `lemma_eviction` shows
//! that only an eviction takes a page out of the pool and that it takes a resident, confirmed page
//! whose count is zero. `lemma_reference_counted` is the observation model: a reference during a
//! period is seen as the bit set at the period's end, and the sample that ends the period counts it.
//!
//! The pager library implements this policy; this crate states it and proves its invariants.
#![no_std]
#![allow(unused)]

use vstd::prelude::*;

verus! {

/// A page's identity in the space the pager serves.
pub type Page = nat;

/// The referenced count saturates here.
pub open spec fn count_cap() -> nat {
    3
}

/// The small queue's share of a pool: a tenth, rounded down.
pub open spec fn small_cap(pool: nat) -> nat {
    pool / 10
}

/// The ghost queue's bound: the main queue's share of the pool.
pub open spec fn ghost_cap(pool: nat) -> nat {
    (pool - small_cap(pool)) as nat
}

/// What the pager records for a page.
pub ghost struct Meta {
    /// Periods after insertion at whose end the reference bit was set, capped at `count_cap()`.
    pub count: nat,
    /// The period the page was faulted in.
    pub inserted: nat,
    /// The page is mapped; an unmap to confirm it is cold clears this, a refault sets it.
    pub mapped: bool,
    /// The reference bit as the pager sees it this period.
    pub referenced: bool,
}

/// The count after a period's end: one more, capped, when the bit was set in a period after the
/// page's insertion; the bit is cleared either way.
pub open spec fn sampled(m: Meta, period: nat) -> Meta {
    if m.referenced && m.inserted < period {
        Meta {
            count: if m.count < count_cap() {
                m.count + 1
            } else {
                m.count
            },
            referenced: false,
            ..m
        }
    } else {
        Meta { referenced: false, ..m }
    }
}

/// The ghost queue after `p` enters it, the oldest identity leaving when it holds `cap`.
pub open spec fn ghost_push(ghosts: Seq<Page>, p: Page, cap: nat) -> Seq<Page> {
    if ghosts.len() < cap {
        ghosts.push(p)
    } else {
        ghosts.drop_first().push(p)
    }
}

/// One step of the pager or of the program it serves.
pub ghost enum Step {
    /// A fault on a page that is not resident.
    Fault(Page),
    /// A reference to a resident page; a refault when the page is unmapped.
    Access(Page),
    /// An unmap of a resident page to confirm it is cold.
    Unmap(Page),
    /// The small queue's tail is promoted or evicted.
    SmallTail,
    /// The main queue's tail is reinserted or evicted.
    MainTail,
    /// The end of a sampling period.
    Sample,
}

/// The pager's state: the pool size, the current period, the three queues (oldest first) and what
/// it records per page.
pub ghost struct Policy {
    pub pool: nat,
    pub period: nat,
    pub small: Seq<Page>,
    pub main: Seq<Page>,
    pub ghosts: Seq<Page>,
    pub meta: Map<Page, Meta>,
}

impl Policy {
    /// An empty pager over `pool` frames.
    pub open spec fn init(pool: nat) -> Policy {
        Policy {
            pool,
            period: 0,
            small: Seq::empty(),
            main: Seq::empty(),
            ghosts: Seq::empty(),
            meta: Map::empty(),
        }
    }

    /// A frame of the pool backs `p`.
    pub open spec fn resident(self, p: Page) -> bool {
        self.small.contains(p) || self.main.contains(p)
    }

    /// `p` looks cold and the unmap confirmed it: no reference counted, none seen this period.
    pub open spec fn evictable(self, p: Page) -> bool {
        &&& self.meta[p].count == 0
        &&& !self.meta[p].mapped
        &&& !self.meta[p].referenced
    }

    pub open spec fn inv(self) -> bool {
        &&& self.pool >= 10
        &&& self.small.no_duplicates()
        &&& self.main.no_duplicates()
        &&& self.ghosts.no_duplicates()
        &&& forall|p: Page| #[trigger] self.small.contains(p) ==> !self.main.contains(p)
        &&& self.small.len() <= small_cap(self.pool)
        &&& self.small.len() + self.main.len() <= self.pool
        &&& self.ghosts.len() <= ghost_cap(self.pool)
        &&& forall|p: Page| #[trigger] self.ghosts.contains(p) ==> !self.resident(p)
        &&& forall|p: Page| #[trigger]
            self.resident(p) ==> {
                &&& self.meta.contains_key(p)
                &&& self.meta[p].count <= count_cap()
                &&& self.meta[p].inserted <= self.period
            }
    }

    pub open spec fn enabled(self, step: Step) -> bool {
        match step {
            Step::Fault(p) => {
                &&& !self.resident(p)
                &&& self.small.len() + self.main.len() < self.pool
                &&& (self.ghosts.contains(p) || self.small.len() < small_cap(self.pool))
            },
            Step::Access(p) => self.resident(p),
            Step::Unmap(p) => self.resident(p) && self.meta[p].mapped,
            Step::SmallTail => self.small.len() > 0 && (self.meta[self.small[0]].count > 0
                || self.evictable(self.small[0])),
            Step::MainTail => self.main.len() > 0 && (self.meta[self.main[0]].count > 0
                || self.evictable(self.main[0])),
            Step::Sample => true,
        }
    }

    pub open spec fn next(self, step: Step) -> Policy {
        match step {
            Step::Fault(p) => {
                let meta = self.meta.insert(
                    p,
                    Meta { count: 0, inserted: self.period, mapped: true, referenced: true },
                );
                if self.ghosts.contains(p) {
                    Policy {
                        main: self.main.push(p),
                        ghosts: self.ghosts.remove(self.ghosts.index_of(p)),
                        meta,
                        ..self
                    }
                } else {
                    Policy { small: self.small.push(p), meta, ..self }
                }
            },
            Step::Access(p) => Policy {
                meta: self.meta.insert(p, Meta { mapped: true, referenced: true, ..self.meta[p] }),
                ..self
            },
            Step::Unmap(p) => Policy {
                meta: self.meta.insert(p, Meta { mapped: false, ..self.meta[p] }),
                ..self
            },
            Step::SmallTail => {
                let p = self.small[0];
                if self.meta[p].count > 0 {
                    Policy { small: self.small.drop_first(), main: self.main.push(p), ..self }
                } else {
                    Policy {
                        small: self.small.drop_first(),
                        ghosts: ghost_push(self.ghosts, p, ghost_cap(self.pool)),
                        ..self
                    }
                }
            },
            Step::MainTail => {
                let p = self.main[0];
                if self.meta[p].count > 0 {
                    Policy {
                        main: self.main.drop_first().push(p),
                        meta: self.meta.insert(
                            p,
                            Meta { count: (self.meta[p].count - 1) as nat, ..self.meta[p] },
                        ),
                        ..self
                    }
                } else {
                    Policy { main: self.main.drop_first(), ..self }
                }
            },
            Step::Sample => Policy {
                period: self.period + 1,
                meta: Map::new(self.meta.dom(), |p: Page| sampled(self.meta[p], self.period)),
                ..self
            },
        }
    }

    /// The transition relation.
    pub open spec fn transition(self, post: Policy) -> bool {
        exists|step: Step| self.enabled(step) && post == self.next(step)
    }

    /// The page a step evicts, if any.
    pub open spec fn evicted(self, step: Step) -> Option<Page> {
        match step {
            Step::SmallTail => if self.meta[self.small[0]].count == 0 {
                Some(self.small[0])
            } else {
                None
            },
            Step::MainTail => if self.meta[self.main[0]].count == 0 {
                Some(self.main[0])
            } else {
                None
            },
            _ => None,
        }
    }

    /// The state after `steps`, in order.
    pub open spec fn run(self, steps: Seq<Step>) -> Policy
        decreases steps.len(),
    {
        if steps.len() == 0 {
            self
        } else {
            self.run(steps.drop_last()).next(steps.last())
        }
    }

    /// Every step of `steps` is enabled where it is taken.
    pub open spec fn valid(self, steps: Seq<Step>) -> bool
        decreases steps.len(),
    {
        steps.len() == 0 || (self.valid(steps.drop_last()) && self.run(steps.drop_last()).enabled(
            steps.last(),
        ))
    }

    /// A reference to `p` this period is on record: a resident `p` has its bit set.
    pub open spec fn seen(self, p: Page) -> bool {
        self.resident(p) ==> self.meta[p].referenced
    }
}

proof fn lemma_push(s: Seq<Page>, a: Page)
    ensures
        s.push(a).len() == s.len() + 1,
        forall|x: Page| #[trigger] s.push(a).contains(x) <==> s.contains(x) || x == a,
        s.no_duplicates() && !s.contains(a) ==> s.push(a).no_duplicates(),
{
    assert forall|x: Page| #[trigger] s.push(a).contains(x) <==> s.contains(x) || x == a by {
        if s.push(a).contains(x) {
            let i = choose|i: int| 0 <= i < s.push(a).len() && s.push(a)[i] == x;
            if i < s.len() {
                assert(s[i] == x);
            }
        }
        if s.contains(x) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            assert(s.push(a)[i] == x);
        }
        if x == a {
            assert(s.push(a)[s.len() as int] == a);
        }
    }
    if s.no_duplicates() && !s.contains(a) {
        assert forall|i: int, j: int|
            0 <= i < s.push(a).len() && 0 <= j < s.push(a).len() && i != j implies s.push(a)[i]
            != s.push(a)[j] by {
            if i < s.len() {
                assert(s.push(a)[i] == s[i]);
            }
            if j < s.len() {
                assert(s.push(a)[j] == s[j]);
            }
        }
    }
}

proof fn lemma_drop_first(s: Seq<Page>)
    requires
        s.len() > 0,
        s.no_duplicates(),
    ensures
        s.drop_first().len() == s.len() - 1,
        s.drop_first().no_duplicates(),
        forall|x: Page| #[trigger] s.drop_first().contains(x) <==> s.contains(x) && x != s[0],
{
    assert forall|x: Page| #[trigger] s.drop_first().contains(x) <==> s.contains(x) && x != s[0] by {
        if s.drop_first().contains(x) {
            let i = choose|i: int| 0 <= i < s.drop_first().len() && s.drop_first()[i] == x;
            assert(s[i + 1] == x);
        }
        if s.contains(x) && x != s[0] {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            assert(i != 0);
            assert(s.drop_first()[i - 1] == x);
        }
    }
    assert forall|i: int, j: int|
        0 <= i < s.drop_first().len() && 0 <= j < s.drop_first().len() && i != j implies s.drop_first()[i]
        != s.drop_first()[j] by {
        assert(s.drop_first()[i] == s[i + 1]);
        assert(s.drop_first()[j] == s[j + 1]);
    }
}

proof fn lemma_remove(s: Seq<Page>, k: int)
    requires
        0 <= k < s.len(),
        s.no_duplicates(),
    ensures
        s.remove(k).len() == s.len() - 1,
        s.remove(k).no_duplicates(),
        forall|x: Page| #[trigger] s.remove(k).contains(x) <==> s.contains(x) && x != s[k],
{
    s.remove_ensures(k);
    let r = s.remove(k);
    assert forall|x: Page| #[trigger] r.contains(x) <==> s.contains(x) && x != s[k] by {
        if r.contains(x) {
            let i = choose|i: int| 0 <= i < r.len() && r[i] == x;
            if i < k {
                assert(s[i] == x);
            } else {
                assert(s[i + 1] == x);
            }
        }
        if s.contains(x) && x != s[k] {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
            assert(i != k);
            if i < k {
                assert(r[i] == x);
            } else {
                assert(r[i - 1] == x);
            }
        }
    }
    assert forall|i: int, j: int|
        0 <= i < r.len() && 0 <= j < r.len() && i != j implies r[i] != r[j] by {
        let si = if i < k {
            i
        } else {
            i + 1
        };
        let sj = if j < k {
            j
        } else {
            j + 1
        };
        assert(r[i] == s[si]);
        assert(r[j] == s[sj]);
    }
}

proof fn lemma_ghost_push(ghosts: Seq<Page>, p: Page, cap: nat)
    requires
        ghosts.no_duplicates(),
        !ghosts.contains(p),
        ghosts.len() <= cap,
        cap > 0,
    ensures
        ghost_push(ghosts, p, cap).no_duplicates(),
        ghost_push(ghosts, p, cap).len() <= cap,
        forall|x: Page| #[trigger]
            ghost_push(ghosts, p, cap).contains(x) ==> ghosts.contains(x) || x == p,
{
    if ghosts.len() < cap {
        lemma_push(ghosts, p);
    } else {
        lemma_drop_first(ghosts);
        lemma_push(ghosts.drop_first(), p);
    }
}

/// Every resident page is in exactly one of the small and main queues.
pub proof fn lemma_resident_in_one_queue(s: Policy, p: Page)
    requires
        s.inv(),
        s.resident(p),
    ensures
        s.small.contains(p) != s.main.contains(p),
{
}

/// The empty pager keeps the invariant.
pub proof fn lemma_init(pool: nat)
    requires
        pool >= 10,
    ensures
        Policy::init(pool).inv(),
{
    let s = Policy::init(pool);
    assert forall|p: Page| !s.small.contains(p) && !s.main.contains(p) && !s.ghosts.contains(p) by {
        if s.small.contains(p) {
            let i = choose|i: int| 0 <= i < s.small.len() && s.small[i] == p;
        }
        if s.main.contains(p) {
            let i = choose|i: int| 0 <= i < s.main.len() && s.main[i] == p;
        }
        if s.ghosts.contains(p) {
            let i = choose|i: int| 0 <= i < s.ghosts.len() && s.ghosts[i] == p;
        }
    }
}

/// Each enabled step keeps the invariant, and changes which pages are resident only as stated:
/// a fault adds its page, an eviction removes its page, and nothing else changes residency.
pub proof fn lemma_next_inv(s: Policy, step: Step)
    requires
        s.inv(),
        s.enabled(step),
    ensures
        s.next(step).inv(),
        s.next(step).pool == s.pool,
        forall|x: Page| #[trigger]
            s.next(step).resident(x) <==> match step {
                Step::Fault(p) => s.resident(x) || x == p,
                _ => match s.evicted(step) {
                    Some(p) => s.resident(x) && x != p,
                    None => s.resident(x),
                },
            },
{
    let t = s.next(step);
    match step {
        Step::Fault(p) => {
            if s.ghosts.contains(p) {
                let k = s.ghosts.index_of(p);
                lemma_push(s.main, p);
                lemma_remove(s.ghosts, k);
                assert(s.ghosts[k] == p);
            } else {
                lemma_push(s.small, p);
            }
            assert forall|x: Page| #[trigger] t.resident(x) <==> s.resident(x) || x == p by {}
            assert forall|x: Page| #[trigger] t.small.contains(x) implies !t.main.contains(x) by {
                assert(s.small.contains(x) || x == p);
            }
            assert forall|x: Page| #[trigger] t.ghosts.contains(x) implies !t.resident(x) by {
                assert(s.ghosts.contains(x));
            }
            assert forall|x: Page| #[trigger] t.resident(x) implies {
                &&& t.meta.contains_key(x)
                &&& t.meta[x].count <= count_cap()
                &&& t.meta[x].inserted <= t.period
            } by {
                if x != p {
                    assert(s.resident(x));
                }
            }
        },
        Step::Access(p) => {
            assert forall|x: Page| #[trigger] t.resident(x) implies {
                &&& t.meta.contains_key(x)
                &&& t.meta[x].count <= count_cap()
                &&& t.meta[x].inserted <= t.period
            } by {
                assert(s.resident(x));
            }
        },
        Step::Unmap(p) => {
            assert forall|x: Page| #[trigger] t.resident(x) implies {
                &&& t.meta.contains_key(x)
                &&& t.meta[x].count <= count_cap()
                &&& t.meta[x].inserted <= t.period
            } by {
                assert(s.resident(x));
            }
        },
        Step::SmallTail => {
            let p = s.small[0];
            assert(s.small.contains(p));
            lemma_drop_first(s.small);
            if s.meta[p].count > 0 {
                lemma_push(s.main, p);
                assert forall|x: Page| #[trigger] t.resident(x) <==> s.resident(x) by {}
                assert forall|x: Page| #[trigger] t.small.contains(x) implies !t.main.contains(x) by {
                    assert(s.small.contains(x));
                }
            } else {
                lemma_ghost_push(s.ghosts, p, ghost_cap(s.pool));
                assert forall|x: Page| #[trigger] t.resident(x) <==> s.resident(x) && x != p by {}
                assert forall|x: Page| #[trigger] t.small.contains(x) implies !t.main.contains(x) by {
                    assert(s.small.contains(x));
                }
                assert forall|x: Page| #[trigger] t.ghosts.contains(x) implies !t.resident(x) by {
                    assert(s.ghosts.contains(x) || x == p);
                }
            }
            assert forall|x: Page| #[trigger] t.resident(x) implies {
                &&& t.meta.contains_key(x)
                &&& t.meta[x].count <= count_cap()
                &&& t.meta[x].inserted <= t.period
            } by {
                assert(s.resident(x));
            }
        },
        Step::MainTail => {
            let p = s.main[0];
            assert(s.main.contains(p));
            lemma_drop_first(s.main);
            if s.meta[p].count > 0 {
                lemma_push(s.main.drop_first(), p);
                assert forall|x: Page| #[trigger] t.resident(x) <==> s.resident(x) by {}
            } else {
                assert forall|x: Page| #[trigger] t.resident(x) <==> s.resident(x) && x != p by {}
            }
            assert forall|x: Page| #[trigger] t.small.contains(x) implies !t.main.contains(x) by {
                assert(s.small.contains(x));
            }
            assert forall|x: Page| #[trigger] t.ghosts.contains(x) implies !t.resident(x) by {
                assert(s.ghosts.contains(x));
            }
            assert forall|x: Page| #[trigger] t.resident(x) implies {
                &&& t.meta.contains_key(x)
                &&& t.meta[x].count <= count_cap()
                &&& t.meta[x].inserted <= t.period
            } by {
                assert(s.resident(x));
            }
        },
        Step::Sample => {
            assert forall|x: Page| #[trigger] t.resident(x) implies {
                &&& t.meta.contains_key(x)
                &&& t.meta[x].count <= count_cap()
                &&& t.meta[x].inserted <= t.period
            } by {
                assert(s.resident(x));
                assert(t.meta[x] == sampled(s.meta[x], s.period));
            }
        },
    }
}

/// The transition relation keeps the invariant.
pub proof fn lemma_transition_inv(s: Policy, t: Policy)
    requires
        s.inv(),
        s.transition(t),
    ensures
        t.inv(),
{
    let step = choose|step: Step| s.enabled(step) && t == s.next(step);
    lemma_next_inv(s, step);
}

/// Every state a valid run reaches keeps the invariant.
pub proof fn lemma_run_inv(s: Policy, steps: Seq<Step>)
    requires
        s.inv(),
        s.valid(steps),
    ensures
        s.run(steps).inv(),
    decreases steps.len(),
{
    if steps.len() > 0 {
        lemma_run_inv(s, steps.drop_last());
        lemma_next_inv(s.run(steps.drop_last()), steps.last());
    }
}

/// An eviction takes a resident page whose count is zero and whose unmap confirmed it cold, and
/// only an eviction or a fault changes which pages are resident.
pub proof fn lemma_eviction(s: Policy, step: Step)
    requires
        s.inv(),
        s.enabled(step),
    ensures
        match s.evicted(step) {
            Some(p) => {
                &&& s.resident(p)
                &&& s.meta[p].count == 0
                &&& s.evictable(p)
                &&& !s.next(step).resident(p)
            },
            None => forall|x: Page| s.resident(x) ==> #[trigger] s.next(step).resident(x),
        },
{
    lemma_next_inv(s, step);
    match step {
        Step::SmallTail => {
            assert(s.small.contains(s.small[0]));
        },
        Step::MainTail => {
            assert(s.main.contains(s.main[0]));
        },
        _ => {},
    }
}

/// A reference to a resident page is on record at once, and a refault of an unmapped page maps it
/// again and keeps it from eviction until a period's end has counted it.
pub proof fn lemma_access_seen(s: Policy, p: Page)
    requires
        s.inv(),
        s.enabled(Step::Access(p)),
    ensures
        s.next(Step::Access(p)).seen(p),
        s.next(Step::Access(p)).meta[p].mapped,
        !s.next(Step::Access(p)).evictable(p),
{
}

/// A reference on record stays on record until the period ends.
pub proof fn lemma_seen_kept(s: Policy, step: Step, p: Page)
    requires
        s.inv(),
        s.enabled(step),
        step != Step::Sample,
        s.seen(p),
    ensures
        s.next(step).seen(p),
{
    lemma_next_inv(s, step);
    let t = s.next(step);
    if t.resident(p) {
        match step {
            Step::Fault(q) => {
                if q != p {
                    assert(s.resident(p));
                }
            },
            _ => {
                assert(s.resident(p));
            },
        }
    }
}

/// A reference during a period is on record at every later point of the period.
pub proof fn lemma_reference_seen(s: Policy, steps: Seq<Step>, i: int, p: Page)
    requires
        s.inv(),
        s.valid(steps),
        0 <= i < steps.len(),
        steps[i] == Step::Access(p),
        forall|j: int| 0 <= j < steps.len() ==> steps[j] != Step::Sample,
    ensures
        s.run(steps).seen(p),
    decreases steps.len(),
{
    let before = steps.drop_last();
    lemma_run_inv(s, before);
    if i == steps.len() - 1 {
        lemma_access_seen(s.run(before), p);
    } else {
        assert(before[i] == steps[i]);
        assert forall|j: int| 0 <= j < before.len() implies before[j] != Step::Sample by {
            assert(before[j] == steps[j]);
        }
        lemma_reference_seen(s, before, i, p);
        lemma_seen_kept(s.run(before), steps.last(), p);
    }
}

/// The observation model: a reference to a page during a period is seen as the bit set at the
/// period's end, and the sample that ends the period counts it, capped, when the page is still
/// resident and was inserted in an earlier period.
pub proof fn lemma_reference_counted(s: Policy, steps: Seq<Step>, i: int, p: Page)
    requires
        s.inv(),
        s.valid(steps.push(Step::Sample)),
        0 <= i < steps.len(),
        steps[i] == Step::Access(p),
        forall|j: int| 0 <= j < steps.len() ==> steps[j] != Step::Sample,
        s.run(steps).resident(p),
        s.run(steps).meta[p].inserted < s.run(steps).period,
    ensures
        s.run(steps).meta[p].referenced,
        s.run(steps.push(Step::Sample)).resident(p),
        s.run(steps.push(Step::Sample)).meta[p].count == if s.run(steps).meta[p].count
            < count_cap() {
            s.run(steps).meta[p].count + 1
        } else {
            s.run(steps).meta[p].count
        },
        s.run(steps.push(Step::Sample)).meta[p].count > 0,
{
    assert(steps.push(Step::Sample).drop_last() =~= steps);
    assert(steps.push(Step::Sample).last() == Step::Sample);
    lemma_reference_seen(s, steps, i, p);
    lemma_run_inv(s, steps);
}

} // verus!
