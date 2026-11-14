// SPDX-License-Identifier: MIT

//! Per-core priority run queues over the intrusive list in `ThreadRecord`, and the thread
//! selection function for each core. Every `Runnable` thread on a core sits in the doubly linked
//! FIFO queue of its priority on that core; `start` and `switch_out` append at the tail so a
//! thread put back goes behind every other of its priority, `suspend`, `switch_in`, `destroy_thread`
//! and revoke of a binding or placement unlink in O(1), and `select_thread` scans the 256-bit
//! per-core presence bitmap from the top down to return the head of the highest non-empty priority.
//! All queue state lives inside `CapKernel` (`self.threads.queues`), with no statics. See
//! design/cpu-time-as-capability/ and design/one-kernel-instance/.

use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::kernel::CapKernel;
use crate::capability::list::NONE;
use crate::capability::reach::MAX_PRIORITY;
use crate::capability::steps::Steps;
use crate::capability::thread::*;
use crate::define::*;
use crate::pptr::*;

/// Number of priorities (`0..=MAX_PRIORITY`).
pub const NUM_PRIORITIES: usize = MAX_PRIORITY + 1;

/// Number of 64-bit bitmap words covering `NUM_PRIORITIES` (`4 * 64 == 256`).
pub const PRIORITY_WORDS: usize = 4;

/// Total `(core, priority)` queue slots across all cores.
pub const QUEUE_SLOTS: usize = NUM_CPUS * NUM_PRIORITIES;

/// Total `(core, word)` bitmap slots across all cores.
pub const PRESENT_SLOTS: usize = NUM_CPUS * PRIORITY_WORDS;

/// Loop iterations taken by `RunQueues::init`.
pub const INIT_QUEUES_STEPS: usize = QUEUE_SLOTS + PRESENT_SLOTS;

/// Per-core priority queues of `Runnable` threads, stored flat by `(core, priority)` so
/// zero-initialised memory is valid before `CapKernel::init` runs in place.
pub struct RunQueues {
    pub heads: Array<usize, QUEUE_SLOTS>,
    pub tails: Array<usize, QUEUE_SLOTS>,
    pub present: Array<u64, PRESENT_SLOTS>,
    pub seqs: Ghost<Seq<Seq<Seq<usize>>>>,
}

/// The priority a thread runs and queues at: its placement's priority when placed, and `0`
/// otherwise (only a running thread whose placement went, with a stop pending, runs without one).
pub open spec fn thread_priority(r: ThreadRecord) -> usize {
    match r.placement {
        Some(pl) => pl.priority,
        None => 0,
    }
}

/// Bit `b` (`0..64`) is set in `w`.
pub open spec fn bit_is_set(w: u64, b: usize) -> bool {
    ((w >> (b as u64)) & 1u64) != 0u64
}

/// Flat `(core, priority)` index into `heads` and `tails`.
pub open spec fn queue_slot(c: int, p: int) -> int {
    c * (NUM_PRIORITIES as int) + p
}

/// Flat `(core, priority / 64)` index into `present`.
pub open spec fn present_word(c: int, p: int) -> int {
    c * (PRIORITY_WORDS as int) + (p / 64)
}

/// Bit offset (`0..64`) within `present[present_word(c, p)]` for priority `p`.
pub open spec fn present_bit(p: int) -> usize {
    (p % 64) as usize
}

impl RunQueues {
    /// The FIFO sequence of `Runnable` threads on core `c` at priority `p`, from front (`0`,
    /// next to be selected) to back (`len - 1`, most recently enqueued or put back).
    pub open spec fn queue(&self, c: int, p: int) -> Seq<usize> {
        self.seqs@[c][p]
    }

    /// Every `(core, priority)` queue is empty.
    pub open spec fn all_empty(&self) -> bool {
        &&& self.seqs@.len() == NUM_CPUS
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] self.seqs@[c]).len() == NUM_PRIORITIES
        &&& forall|c: int, p: int| 0 <= c < NUM_CPUS && 0 <= p < NUM_PRIORITIES
            ==> (#[trigger] self.queue(c, p)) == Seq::<usize>::empty()
    }

    /// Initialises every `(core, priority)` head and tail to `NONE` and every presence word to `0`
    /// in place, with no large stack temporaries.
    #[verifier::spinoff_prover]
    pub fn init(&mut self, Tracked(steps): Tracked<&mut Steps>)
        ensures
            final(steps).count <= old(steps).count + INIT_QUEUES_STEPS,
            final(self).all_empty(),
            queues_wf(final(self), Map::<usize, PointsTo<ThreadRecord>>::empty()),
    {
        self.heads.init();
        self.tails.init();
        self.present.init();
        let mut i: usize = 0;
        while i < QUEUE_SLOTS
            invariant
                0 <= i <= QUEUE_SLOTS,
                self.heads.wf(),
                self.tails.wf(),
                self.present.wf(),
                steps.count <= old(steps).count + i,
                forall|k: int| 0 <= k < i ==> #[trigger] self.heads@[k] == NONE,
                forall|k: int| 0 <= k < i ==> #[trigger] self.tails@[k] == NONE,
            decreases QUEUE_SLOTS - i,
        {
            self.heads.set(i, NONE);
            self.tails.set(i, NONE);
            i = i + 1;
            proof {
                steps.step();
            }
        }
        let mut j: usize = 0;
        while j < PRESENT_SLOTS
            invariant
                0 <= j <= PRESENT_SLOTS,
                self.heads.wf(),
                self.tails.wf(),
                self.present.wf(),
                steps.count <= old(steps).count + QUEUE_SLOTS + j,
                forall|k: int| 0 <= k < QUEUE_SLOTS ==> #[trigger] self.heads@[k] == NONE,
                forall|k: int| 0 <= k < QUEUE_SLOTS ==> #[trigger] self.tails@[k] == NONE,
                forall|k: int| 0 <= k < j ==> #[trigger] self.present@[k] == 0u64,
            decreases PRESENT_SLOTS - j,
        {
            self.present.set(j, 0u64);
            j = j + 1;
            proof {
                steps.step();
            }
        }
        let ghost empty_cpu: Seq<Seq<usize>> = Seq::new(
            NUM_PRIORITIES as nat,
            |_p: int| Seq::<usize>::empty(),
        );
        self.seqs = Ghost(Seq::new(NUM_CPUS as nat, |_c: int| empty_cpu));
        proof {
            reveal(queues_wf);
            let empty_records = Map::<usize, PointsTo<ThreadRecord>>::empty();
            assert forall|c: int, p: int| 0 <= c < NUM_CPUS && 0 <= p < NUM_PRIORITIES
                implies #[trigger] single_queue_wf(self, empty_records, c, p) by {
                lemma_queue_slot_bounds(c, p);
                lemma_present_slot_bounds(c, p);
                lemma_zero_word_no_bits(present_bit(p));
            }
        }
    }
}

/// Invariant of one `(core, priority)` doubly linked queue: `heads`/`tails` and the intrusive
/// `run_prev`/`run_next` links in `records` match `queues.queue(c, p)` without duplicates, its
/// `present` bit is set iff `queue(c, p)` is non-empty, and every member is a bound `Runnable`
/// thread on `c` at priority `p`.
pub open spec fn single_queue_wf(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: int,
    p: int,
) -> bool {
    let s = queues.queue(c, p);
    let slot = queue_slot(c, p);
    let w = present_word(c, p);
    let b = present_bit(p);
    &&& bit_is_set(queues.present@[w], b) == (s.len() > 0)
    &&& (s.len() == 0 ==> {
        &&& queues.heads@[slot] == NONE
        &&& queues.tails@[slot] == NONE
    })
    &&& (s.len() > 0 ==> {
        &&& queues.heads@[slot] == s[0]
        &&& queues.tails@[slot] == s[s.len() - 1]
        &&& records[s[0]].value().run_prev == NONE
        &&& records[s[s.len() - 1]].value().run_next == NONE
    })
    &&& forall|k: int| 0 <= k < s.len() ==> {
        let u = #[trigger] s[k];
        &&& u != NONE
        &&& records.contains_key(u)
        &&& records[u].is_init()
        &&& records[u].value().state == (ThreadState::Runnable { core: c as usize })
        &&& thread_priority(records[u].value()) == p as usize
        &&& records[u].value().process is Some
    }
    &&& forall|k: int| 0 <= k < s.len() - 1 ==> {
        records[#[trigger] s[k]].value().run_next == s[k + 1]
    }
    &&& forall|k: int| 1 <= k < s.len() ==> {
        records[#[trigger] s[k]].value().run_prev == s[k - 1]
    }
    &&& forall|i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j < s.len() ==> s[i] != s[j]
}

/// Invariant of all per-core priority queues: every `(core, priority)` queue is well formed and
/// every `Runnable` thread in `records` appears in the queue of its core and priority.
#[verifier::opaque]
pub open spec fn queues_wf(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
) -> bool {
    &&& queues.heads.wf()
    &&& queues.tails.wf()
    &&& queues.present.wf()
    &&& queues.seqs@.len() == NUM_CPUS
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] queues.seqs@[c]).len() == NUM_PRIORITIES
    &&& forall|c: int, p: int| 0 <= c < NUM_CPUS && 0 <= p < NUM_PRIORITIES
        ==> #[trigger] single_queue_wf(queues, records, c, p)
    &&& forall|t: usize| #[trigger] records.contains_key(t) && records[t].value().state is Runnable ==> {
        let r = records[t].value();
        let c = r.state->Runnable_core as int;
        let p = thread_priority(r) as int;
        &&& r.process is Some
        &&& 0 <= c < NUM_CPUS
        &&& 0 <= p < NUM_PRIORITIES
        &&& queues.queue(c, p).contains(t)
    }
}

/// Queue `(c, p)` grew by appending `t` at its tail, and every other `(core, priority)` queue is
/// unchanged.
pub open spec fn queued_at_back(
    pre: &RunQueues,
    post: &RunQueues,
    c: int,
    p: int,
    t: usize,
) -> bool {
    &&& post.seqs@.len() == NUM_CPUS
    &&& forall|d: int| 0 <= d < NUM_CPUS ==> (#[trigger] post.seqs@[d]).len() == NUM_PRIORITIES
    &&& post.queue(c, p) == pre.queue(c, p).push(t)
    &&& forall|d: int, q: int| 0 <= d < NUM_CPUS && 0 <= q < NUM_PRIORITIES && (d != c || q != p)
        ==> (#[trigger] post.queue(d, q)) == pre.queue(d, q)
}

/// Queue `(c, p)` shrank by removing `t` from its position, preserving the relative order of all
/// other threads at `(c, p)`, and every other `(core, priority)` queue is unchanged.
pub open spec fn dequeued_from(
    pre: &RunQueues,
    post: &RunQueues,
    c: int,
    p: int,
    t: usize,
) -> bool {
    &&& post.seqs@.len() == NUM_CPUS
    &&& forall|d: int| 0 <= d < NUM_CPUS ==> (#[trigger] post.seqs@[d]).len() == NUM_PRIORITIES
    &&& exists|idx: int| 0 <= idx < pre.queue(c, p).len()
        && pre.queue(c, p)[idx] == t
        && post.queue(c, p) == pre.queue(c, p).remove(idx)
    &&& forall|d: int, q: int| 0 <= d < NUM_CPUS && 0 <= q < NUM_PRIORITIES && (d != c || q != p)
        ==> (#[trigger] post.queue(d, q)) == pre.queue(d, q)
}

/// Thread `t` sits at the back of core `c`'s queue for `priority`, behind every other `Runnable`
/// thread on `c` of `priority` (each of which sits at an earlier index in `queue(c, priority)`).
pub open spec fn at_back_of_priority(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: int,
    priority: usize,
    t: usize,
) -> bool {
    let q = queues.queue(c, priority as int);
    &&& q.len() > 0
    &&& q[q.len() - 1] == t
    &&& forall|u: usize| #[trigger] records.contains_key(u)
        && records[u].value().state == (ThreadState::Runnable { core: c as usize })
        && thread_priority(records[u].value()) == priority
        && u != t
        ==> exists|k: int| 0 <= k < q.len() - 1 && q[k] == u
}

proof fn lemma_queue_slot_bounds(c: int, p: int)
    requires
        0 <= c < NUM_CPUS,
        0 <= p < NUM_PRIORITIES,
    ensures
        0 <= queue_slot(c, p) < QUEUE_SLOTS,
        forall|c2: int, p2: int| 0 <= c2 < NUM_CPUS && 0 <= p2 < NUM_PRIORITIES
            && (c2 != c || p2 != p) ==> #[trigger] queue_slot(c2, p2) != queue_slot(c, p),
{
}

proof fn lemma_present_slot_bounds(c: int, p: int)
    requires
        0 <= c < NUM_CPUS,
        0 <= p < NUM_PRIORITIES,
    ensures
        0 <= p / 64 < PRIORITY_WORDS,
        0 <= present_word(c, p) < PRESENT_SLOTS,
        present_bit(p) < 64,
        (p / 64) * 64 + (present_bit(p) as int) == p,
        forall|c2: int, p2: int| 0 <= c2 < NUM_CPUS && 0 <= p2 < NUM_PRIORITIES
            && (c2 != c || p2 != p) ==> (
                #[trigger] present_word(c2, p2) != present_word(c, p)
                || present_bit(p2) != present_bit(p)
            ),
{
}

proof fn lemma_zero_word_no_bits(b: usize)
    requires
        b < 64,
    ensures
        !bit_is_set(0u64, b),
{
    let bb: u64 = b as u64;
    assert(((0u64 >> bb) & 1u64) == 0u64) by (bit_vector)
        requires
            bb < 64u64,
    ;
}

proof fn lemma_or_bit_u64(w: u64, b: usize)
    requires
        b < 64,
    ensures
        bit_is_set(w | (1u64 << (b as u64)), b),
        forall|k: usize| k < 64 && k != b
            ==> #[trigger] bit_is_set(w | (1u64 << (b as u64)), k) == bit_is_set(w, k),
{
    let bb: u64 = b as u64;
    assert((((w | (1u64 << bb)) >> bb) & 1u64) == 1u64) by (bit_vector)
        requires
            bb < 64u64,
    ;
    assert forall|k: usize| k < 64 && k != b
        implies #[trigger] bit_is_set(w | (1u64 << (b as u64)), k) == bit_is_set(w, k) by {
        let kk: u64 = k as u64;
        assert((((w | (1u64 << bb)) >> kk) & 1u64) == ((w >> kk) & 1u64)) by (bit_vector)
            requires
                bb < 64u64,
                kk < 64u64,
                kk != bb,
        ;
    }
}

proof fn lemma_and_not_bit_u64(w: u64, b: usize)
    requires
        b < 64,
    ensures
        !bit_is_set(w & !(1u64 << (b as u64)), b),
        forall|k: usize| k < 64 && k != b
            ==> #[trigger] bit_is_set(w & !(1u64 << (b as u64)), k) == bit_is_set(w, k),
{
    let bb: u64 = b as u64;
    assert((((w & !(1u64 << bb)) >> bb) & 1u64) == 0u64) by (bit_vector)
        requires
            bb < 64u64,
    ;
    assert forall|k: usize| k < 64 && k != b
        implies #[trigger] bit_is_set(w & !(1u64 << (b as u64)), k) == bit_is_set(w, k) by {
        let kk: u64 = k as u64;
        assert((((w & !(1u64 << bb)) >> kk) & 1u64) == ((w >> kk) & 1u64)) by (bit_vector)
            requires
                bb < 64u64,
                kk < 64u64,
                kk != bb,
        ;
    }
}

/// Index (`0..64`) of the most significant set bit in a non-zero 64-bit word, computed by a
/// 6-step binary shift search with no loops or unverified intrinsics.
fn highest_bit_u64(w: u64) -> (pos: usize)
    requires
        w != 0u64,
    ensures
        pos < 64,
        bit_is_set(w, pos),
        forall|k: usize| pos < k && k < 64 ==> !#[trigger] bit_is_set(w, k),
{
    let (x1, b5): (u64, u64) = if (w >> 32u64) != 0u64 { (w >> 32u64, 32u64) } else { (w, 0u64) };
    let (x2, b4): (u64, u64) = if (x1 >> 16u64) != 0u64 { (x1 >> 16u64, 16u64) } else { (x1, 0u64) };
    let (x3, b3): (u64, u64) = if (x2 >> 8u64) != 0u64 { (x2 >> 8u64, 8u64) } else { (x2, 0u64) };
    let (x4, b2): (u64, u64) = if (x3 >> 4u64) != 0u64 { (x3 >> 4u64, 4u64) } else { (x3, 0u64) };
    let (x5, b1): (u64, u64) = if (x4 >> 2u64) != 0u64 { (x4 >> 2u64, 2u64) } else { (x4, 0u64) };
    let b0: u64 = if (x5 >> 1u64) != 0u64 { 1u64 } else { 0u64 };
    let p: u64 = b5 | b4 | b3 | b2 | b1 | b0;
    proof {
        assert(x1 == (w >> b5) && x1 != 0u64 && (x1 >> 32u64) == 0u64 && (b5 == 0u64 || b5 == 32u64))
            by (bit_vector)
            requires
                w != 0u64,
                x1 == (if (w >> 32u64) != 0u64 { w >> 32u64 } else { w }),
                b5 == (if (w >> 32u64) != 0u64 { 32u64 } else { 0u64 }),
        ;
        let p4: u64 = b5 | b4;
        assert(x2 == (w >> p4) && x2 != 0u64 && (x2 >> 16u64) == 0u64 && p4 < 64u64 && (p4 & 15u64) == 0u64)
            by (bit_vector)
            requires
                x1 == (w >> b5) && x1 != 0u64 && (x1 >> 32u64) == 0u64 && (b5 == 0u64 || b5 == 32u64),
                x2 == (if (x1 >> 16u64) != 0u64 { x1 >> 16u64 } else { x1 }),
                b4 == (if (x1 >> 16u64) != 0u64 { 16u64 } else { 0u64 }),
                p4 == (b5 | b4),
        ;
        let p3: u64 = p4 | b3;
        assert(x3 == (w >> p3) && x3 != 0u64 && (x3 >> 8u64) == 0u64 && p3 < 64u64 && (p3 & 7u64) == 0u64)
            by (bit_vector)
            requires
                x2 == (w >> p4) && x2 != 0u64 && (x2 >> 16u64) == 0u64 && p4 < 64u64 && (p4 & 15u64) == 0u64,
                x3 == (if (x2 >> 8u64) != 0u64 { x2 >> 8u64 } else { x2 }),
                b3 == (if (x2 >> 8u64) != 0u64 { 8u64 } else { 0u64 }),
                p3 == (p4 | b3),
        ;
        let p2: u64 = p3 | b2;
        assert(x4 == (w >> p2) && x4 != 0u64 && (x4 >> 4u64) == 0u64 && p2 < 64u64 && (p2 & 3u64) == 0u64)
            by (bit_vector)
            requires
                x3 == (w >> p3) && x3 != 0u64 && (x3 >> 8u64) == 0u64 && p3 < 64u64 && (p3 & 7u64) == 0u64,
                x4 == (if (x3 >> 4u64) != 0u64 { x3 >> 4u64 } else { x3 }),
                b2 == (if (x3 >> 4u64) != 0u64 { 4u64 } else { 0u64 }),
                p2 == (p3 | b2),
        ;
        let p1: u64 = p2 | b1;
        assert(x5 == (w >> p1) && x5 != 0u64 && (x5 >> 2u64) == 0u64 && p1 < 64u64 && (p1 & 1u64) == 0u64)
            by (bit_vector)
            requires
                x4 == (w >> p2) && x4 != 0u64 && (x4 >> 4u64) == 0u64 && p2 < 64u64 && (p2 & 3u64) == 0u64,
                x5 == (if (x4 >> 2u64) != 0u64 { x4 >> 2u64 } else { x4 }),
                b1 == (if (x4 >> 2u64) != 0u64 { 2u64 } else { 0u64 }),
                p1 == (p2 | b1),
        ;
        assert(p == (p1 | b0)) by (bit_vector)
            requires
                p4 == (b5 | b4),
                p3 == (p4 | b3),
                p2 == (p3 | b2),
                p1 == (p2 | b1),
                p == (b5 | b4 | b3 | b2 | b1 | b0),
        ;
        assert(p < 64u64 && (w >> p) == 1u64 && ((w >> p) & 1u64) == 1u64) by (bit_vector)
            requires
                x5 == (w >> p1) && x5 != 0u64 && (x5 >> 2u64) == 0u64 && p1 < 64u64 && (p1 & 1u64) == 0u64,
                b0 == (if (x5 >> 1u64) != 0u64 { 1u64 } else { 0u64 }),
                p == (p1 | b0),
        ;
        assert forall|k: usize| (p as usize) < k && k < 64 implies !#[trigger] bit_is_set(w, k) by {
            let kk: u64 = k as u64;
            assert(((w >> kk) & 1u64) == 0u64) by (bit_vector)
                requires
                    p < 64u64,
                    (w >> p) == 1u64,
                    p < kk,
                    kk < 64u64,
            ;
        }
    }
    p as usize
}

/// Under `queues_wf`, any thread at the tail of `queue(c, priority)` sits behind every other
/// `Runnable` thread on `c` of `priority`.
pub proof fn lemma_tail_is_behind_all(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: int,
    priority: usize,
    t: usize,
)
    requires
        queues_wf(queues, records),
        0 <= c < NUM_CPUS,
        priority <= MAX_PRIORITY,
        queues.queue(c, priority as int).len() > 0,
        queues.queue(c, priority as int)[queues.queue(c, priority as int).len() - 1] == t,
    ensures
        at_back_of_priority(queues, records, c, priority, t),
{
    reveal(queues_wf);
    let q = queues.queue(c, priority as int);
    assert forall|u: usize| #[trigger] records.contains_key(u)
        && records[u].value().state == (ThreadState::Runnable { core: c as usize })
        && thread_priority(records[u].value()) == priority
        && u != t
        implies exists|k: int| 0 <= k < q.len() - 1 && q[k] == u by {
        assert(q.contains(u));
        let k = choose|k: int| 0 <= k < q.len() && q[k] == u;
        assert(k != q.len() - 1);
    }
}

/// Dequeuing a distinct thread `t != o` from `(c, p_t)` preserves `o` at the tail of `(c, p_o)`.
pub proof fn lemma_tail_kept_after_other_dequeued(
    s1: &RunQueues,
    s5: &RunQueues,
    c: int,
    p_o: int,
    p_t: int,
    o: usize,
    t: usize,
)
    requires
        0 <= c < NUM_CPUS,
        0 <= p_o < NUM_PRIORITIES,
        0 <= p_t < NUM_PRIORITIES,
        o != t,
        s1.queue(c, p_o).len() > 0,
        s1.queue(c, p_o)[s1.queue(c, p_o).len() - 1] == o,
        dequeued_from(s1, s5, c, p_t, t),
    ensures
        s5.queue(c, p_o).len() > 0,
        s5.queue(c, p_o)[s5.queue(c, p_o).len() - 1] == o,
{
    if p_t == p_o {
        let q1 = s1.queue(c, p_o);
        let idx = choose|idx: int| 0 <= idx < q1.len()
            && q1[idx] == t
            && s5.queue(c, p_o) == q1.remove(idx);
        assert(idx != q1.len() - 1);
        assert(0 <= idx < q1.len() - 1);
    } else {
        assert(s5.queue(c, p_o) == s1.queue(c, p_o));
    }
}

/// Rewriting one thread's record from a non-`Runnable` state to a non-`Runnable` state leaves
/// `queues_wf` intact with the same `RunQueues`.
pub proof fn lemma_queues_unrunnable_written(
    queues: &RunQueues,
    pre: Map<usize, PointsTo<ThreadRecord>>,
    post: Map<usize, PointsTo<ThreadRecord>>,
    t: usize,
)
    requires
        queues_wf(queues, pre),
        pre.contains_key(t),
        !(pre[t].value().state is Runnable),
        post.dom() == pre.dom(),
        !(post[t].value().state is Runnable),
        forall|x: usize| x != t && #[trigger] post.contains_key(x) ==> post[x] == pre[x],
    ensures
        queues_wf(queues, post),
{
    reveal(queues_wf);
    assert forall|c: int, p: int| 0 <= c < NUM_CPUS && 0 <= p < NUM_PRIORITIES
        implies #[trigger] single_queue_wf(queues, post, c, p) by {
        assert(single_queue_wf(queues, pre, c, p));
        let s = queues.queue(c, p);
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != t by {
            let u = s[k];
            assert(pre[u].value().state is Runnable);
        }
        if s.len() > 0 {
            let h = s[0];
            let tl = s[s.len() - 1];
            assert(h != t);
            assert(tl != t);
            assert(post.contains_key(h) && post[h] == pre[h]);
            assert(post.contains_key(tl) && post[tl] == pre[tl]);
        }
        assert forall|k: int| 0 <= k < s.len() implies {
            let u = #[trigger] s[k];
            &&& u != NONE
            &&& post.contains_key(u)
            &&& post[u].is_init()
            &&& post[u].value().state == (ThreadState::Runnable { core: c as usize })
            &&& thread_priority(post[u].value()) == p as usize
            &&& post[u].value().process is Some
        } by {
            let u = s[k];
            assert(u != t);
            assert(post.contains_key(u) && post[u] == pre[u]);
        }
        assert forall|k: int| 0 <= k < s.len() - 1
            implies post[#[trigger] s[k]].value().run_next == s[k + 1] by {
            let u = s[k];
            assert(u != t);
            assert(post.contains_key(u) && post[u] == pre[u]);
        }
        assert forall|k: int| 1 <= k < s.len()
            implies post[#[trigger] s[k]].value().run_prev == s[k - 1] by {
            let u = s[k];
            assert(u != t);
            assert(post.contains_key(u) && post[u] == pre[u]);
        }
    }
    assert forall|u: usize| #[trigger] post.contains_key(u) && post[u].value().state is Runnable implies {
        let r = post[u].value();
        let c = r.state->Runnable_core as int;
        let p = thread_priority(r) as int;
        &&& r.process is Some
        &&& 0 <= c < NUM_CPUS
        &&& 0 <= p < NUM_PRIORITIES
        &&& queues.queue(c, p).contains(u)
    } by {
        assert(u != t);
        assert(pre.contains_key(u) && post[u] == pre[u]);
    }
}

/// Inserting a freshly typed non-`Runnable` thread leaves `queues_wf` intact.
pub proof fn lemma_queues_thread_added(
    queues: &RunQueues,
    pre: Map<usize, PointsTo<ThreadRecord>>,
    post: Map<usize, PointsTo<ThreadRecord>>,
    base: usize,
)
    requires
        queues_wf(queues, pre),
        !pre.contains_key(base),
        post == pre.insert(base, post[base]),
        !(post[base].value().state is Runnable),
    ensures
        queues_wf(queues, post),
{
    reveal(queues_wf);
    assert forall|c: int, p: int| 0 <= c < NUM_CPUS && 0 <= p < NUM_PRIORITIES
        implies #[trigger] single_queue_wf(queues, post, c, p) by {
        assert(single_queue_wf(queues, pre, c, p));
        let s = queues.queue(c, p);
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != base by {
            let u = s[k];
            assert(pre.contains_key(u));
        }
        if s.len() > 0 {
            let h = s[0];
            let tl = s[s.len() - 1];
            assert(h != base);
            assert(tl != base);
            assert(post[h] == pre[h]);
            assert(post[tl] == pre[tl]);
        }
        assert forall|k: int| 0 <= k < s.len() implies {
            let u = #[trigger] s[k];
            &&& u != NONE
            &&& post.contains_key(u)
            &&& post[u].is_init()
            &&& post[u].value().state == (ThreadState::Runnable { core: c as usize })
            &&& thread_priority(post[u].value()) == p as usize
            &&& post[u].value().process is Some
        } by {
            let u = s[k];
            assert(u != base);
            assert(post[u] == pre[u]);
        }
        assert forall|k: int| 0 <= k < s.len() - 1
            implies post[#[trigger] s[k]].value().run_next == s[k + 1] by {
            let u = s[k];
            assert(u != base);
            assert(post[u] == pre[u]);
        }
        assert forall|k: int| 1 <= k < s.len()
            implies post[#[trigger] s[k]].value().run_prev == s[k - 1] by {
            let u = s[k];
            assert(u != base);
            assert(post[u] == pre[u]);
        }
    }
    assert forall|u: usize| #[trigger] post.contains_key(u) && post[u].value().state is Runnable implies {
        let r = post[u].value();
        let c = r.state->Runnable_core as int;
        let p = thread_priority(r) as int;
        &&& r.process is Some
        &&& 0 <= c < NUM_CPUS
        &&& 0 <= p < NUM_PRIORITIES
        &&& queues.queue(c, p).contains(u)
    } by {
        assert(u != base);
        assert(pre.contains_key(u) && post[u] == pre[u]);
    }
}

/// Every `Runnable` thread under `queues_wf` is bound to a process (`process is Some`) and has a
/// valid core and priority.
pub proof fn lemma_runnable_is_bound(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    t: usize,
)
    requires
        queues_wf(queues, records),
        records.contains_key(t),
        records[t].value().state is Runnable,
    ensures
        records[t].value().process is Some,
        records[t].value().state->Runnable_core < NUM_CPUS,
        thread_priority(records[t].value()) <= MAX_PRIORITY,
{
    reveal(queues_wf);
}

/// Removing a non-`Runnable` thread from `records` leaves `queues_wf` intact.
pub proof fn lemma_queues_unrunnable_removed(
    queues: &RunQueues,
    pre: Map<usize, PointsTo<ThreadRecord>>,
    post: Map<usize, PointsTo<ThreadRecord>>,
    base: usize,
)
    requires
        queues_wf(queues, pre),
        pre.contains_key(base),
        !(pre[base].value().state is Runnable),
        post == pre.remove(base),
    ensures
        queues_wf(queues, post),
{
    reveal(queues_wf);
    assert forall|c: int, p: int| 0 <= c < NUM_CPUS && 0 <= p < NUM_PRIORITIES
        implies #[trigger] single_queue_wf(queues, post, c, p) by {
        assert(single_queue_wf(queues, pre, c, p));
        let s = queues.queue(c, p);
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != base by {
            let u = s[k];
            assert(pre[u].value().state is Runnable);
        }
        if s.len() > 0 {
            let h = s[0];
            let tl = s[s.len() - 1];
            assert(h != base);
            assert(tl != base);
            assert(post[h] == pre[h]);
            assert(post[tl] == pre[tl]);
        }
        assert forall|k: int| 0 <= k < s.len() implies {
            let u = #[trigger] s[k];
            &&& u != NONE
            &&& post.contains_key(u)
            &&& post[u].is_init()
            &&& post[u].value().state == (ThreadState::Runnable { core: c as usize })
            &&& thread_priority(post[u].value()) == p as usize
            &&& post[u].value().process is Some
        } by {
            let u = s[k];
            assert(u != base);
            assert(post.contains_key(u) && post[u] == pre[u]);
        }
        assert forall|k: int| 0 <= k < s.len() - 1
            implies post[#[trigger] s[k]].value().run_next == s[k + 1] by {
            let u = s[k];
            assert(u != base);
            assert(post[u] == pre[u]);
        }
        assert forall|k: int| 1 <= k < s.len()
            implies post[#[trigger] s[k]].value().run_prev == s[k - 1] by {
            let u = s[k];
            assert(u != base);
            assert(post[u] == pre[u]);
        }
    }
    assert forall|u: usize| #[trigger] post.contains_key(u) && post[u].value().state is Runnable implies {
        let r = post[u].value();
        let c = r.state->Runnable_core as int;
        let p = thread_priority(r) as int;
        &&& r.process is Some
        &&& 0 <= c < NUM_CPUS
        &&& 0 <= p < NUM_PRIORITIES
        &&& queues.queue(c, p).contains(u)
    } by {
        assert(pre.contains_key(u) && post[u] == pre[u]);
    }
}

/// What `enqueue_and_write` reads of `(c, p)` before it appends thread `t`, not `Runnable`: the
/// arrays it indexes are well formed, and the tail slot holds `NONE` exactly when the queue is
/// empty and otherwise its last thread, which has a record, is `Runnable` and so is not `t`.
proof fn lemma_enqueue_tail(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
)
    requires
        queues_wf(queues, records),
        c < NUM_CPUS,
        p < NUM_PRIORITIES,
        records.contains_key(t),
        !(records[t].value().state is Runnable),
    ensures
        queues.heads.wf(),
        queues.tails.wf(),
        queues.present.wf(),
        ({
            let s = queues.queue(c as int, p as int);
            let tail = queues.tails@[queue_slot(c as int, p as int)];
            &&& (tail == NONE <==> s.len() == 0)
            &&& tail != NONE ==> {
                &&& tail == s[s.len() - 1]
                &&& tail != t
                &&& records.contains_key(tail)
                &&& records[tail].value().state is Runnable
            }
        }),
{
    reveal(queues_wf);
    let s = queues.queue(c as int, p as int);
    assert(single_queue_wf(queues, records, c as int, p as int));
    if s.len() > 0 {
        let _ = s[s.len() - 1];
    }
}

/// The run queues after `enqueue_and_write` appended thread `t`, not `Runnable` before, to
/// `(c, p)`, whose tail slot held `old_tail` and whose presence word was `old_w`: `post_q` is `pre_q`
/// with `t` pushed onto `queue(c, p)`, its tail slot naming `t`, its head slot too when the queue was
/// empty, and its presence bit set; `post_records` is `pre_records` with `t`'s record `Runnable` on
/// `c` at `p`, linked behind `old_tail`, and `old_tail`'s `run_next` naming `t`.
#[verifier::spinoff_prover]
proof fn lemma_enqueue_post_wf(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    old_tail: usize,
    old_w: u64,
)
    requires
        queues_wf(pre_q, pre_records),
        c < NUM_CPUS,
        p < NUM_PRIORITIES,
        t != NONE,
        pre_records.contains_key(t),
        !(pre_records[t].value().state is Runnable),
        post_q.heads.wf(),
        post_q.tails.wf(),
        post_q.present.wf(),
        ({
            let s = pre_q.queue(c as int, p as int);
            let slot = queue_slot(c as int, p as int);
            let w_idx = present_word(c as int, p as int);
            let b_idx = present_bit(p as int);
            &&& old_tail == pre_q.tails@[slot]
            &&& old_w == pre_q.present@[w_idx]
            &&& post_q.seqs@ == pre_q.seqs@.update(
                c as int,
                pre_q.seqs@[c as int].update(p as int, s.push(t)),
            )
            &&& post_q.heads@ == (if old_tail == NONE {
                pre_q.heads@.update(slot, t)
            } else {
                pre_q.heads@
            })
            &&& post_q.tails@ == pre_q.tails@.update(slot, t)
            &&& post_q.present@ == pre_q.present@.update(w_idx, old_w | (1u64 << (b_idx as u64)))
        }),
        post_records.dom() == pre_records.dom(),
        post_records[t].is_init(),
        post_records[t].value().state == (ThreadState::Runnable { core: c }),
        thread_priority(post_records[t].value()) == p,
        post_records[t].value().process is Some,
        post_records[t].value().run_prev == old_tail,
        post_records[t].value().run_next == NONE,
        old_tail != NONE ==> {
            &&& same_record_perm_but_links(pre_records[old_tail], post_records[old_tail])
            &&& post_records[old_tail].value().run_prev == pre_records[old_tail].value().run_prev
            &&& post_records[old_tail].value().run_next == t
        },
        forall|x: usize| x != t && (old_tail == NONE || x != old_tail) && #[trigger] post_records.contains_key(x)
            ==> post_records[x] == pre_records[x],
    ensures
        queues_wf(post_q, post_records),
        queued_at_back(pre_q, post_q, c as int, p as int, t),
        at_back_of_priority(post_q, post_records, c as int, p, t),
{
    reveal(queues_wf);
    let s = pre_q.queue(c as int, p as int);
    let new_s = s.push(t);
    let b_idx = present_bit(p as int);
    lemma_queue_slot_bounds(c as int, p as int);
    lemma_present_slot_bounds(c as int, p as int);
    assert(single_queue_wf(pre_q, pre_records, c as int, p as int));
    lemma_or_bit_u64(old_w, b_idx);
    assert(post_q.queue(c as int, p as int) == new_s);
    if s.len() > 0 {
        let _ = s[s.len() - 1];
        assert(old_tail == s[s.len() - 1]);
        assert(old_tail != NONE);
        assert(pre_records[old_tail].value().state is Runnable);
        assert(old_tail != t);
    } else {
        assert(old_tail == NONE);
    }

    assert forall|c2: int, p2: int| 0 <= c2 < NUM_CPUS && 0 <= p2 < NUM_PRIORITIES
        implies #[trigger] single_queue_wf(post_q, post_records, c2, p2) by {
        lemma_queue_slot_bounds(c2, p2);
        lemma_present_slot_bounds(c2, p2);
        if c2 == c as int && p2 == p as int {
            assert(post_q.queue(c2, p2) == new_s);
            assert(new_s.len() == s.len() + 1);
            assert(new_s[new_s.len() - 1] == t);
            assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != t by {
                let u = s[k];
                assert(pre_records[u].value().state is Runnable);
            }
            if s.len() == 0 {
                assert(new_s[0] == t);
            } else {
                assert(new_s[0] == s[0]);
                assert(s[0] != t);
                if s.len() == 1 {
                    assert(s[0] == old_tail);
                    assert(post_records[s[0]].value().run_prev == pre_records[s[0]].value().run_prev);
                } else {
                    assert(s[0] != old_tail);
                    assert(post_records[s[0]] == pre_records[s[0]]);
                }
            }
            assert forall|k: int| 0 <= k < new_s.len() implies {
                let u = #[trigger] new_s[k];
                &&& u != NONE
                &&& post_records.contains_key(u)
                &&& post_records[u].is_init()
                &&& post_records[u].value().state == (ThreadState::Runnable { core: c2 as usize })
                &&& thread_priority(post_records[u].value()) == p2 as usize
                &&& post_records[u].value().process is Some
            } by {
                if k < s.len() {
                    let u = s[k];
                    assert(new_s[k] == u);
                    assert(u != t);
                    assert(pre_records.contains_key(u));
                    if u == old_tail {
                        assert(same_record_perm_but_links(pre_records[u], post_records[u]));
                    } else {
                        assert(post_records.contains_key(u));
                        assert(post_records[u] == pre_records[u]);
                    }
                } else {
                    assert(new_s[k] == t);
                }
            }
            assert forall|k: int| 0 <= k < new_s.len() - 1
                implies post_records[#[trigger] new_s[k]].value().run_next == new_s[k + 1] by {
                assert(new_s[k] == s[k]);
                if k < s.len() - 1 {
                    assert(new_s[k + 1] == s[k + 1]);
                    assert(s[k] != old_tail);
                    assert(s[k] != t);
                    assert(post_records.contains_key(s[k]));
                    assert(post_records[s[k]] == pre_records[s[k]]);
                } else {
                    assert(k == s.len() - 1);
                    assert(s[k] == old_tail);
                    assert(new_s[k + 1] == t);
                }
            }
            assert forall|k: int| 1 <= k < new_s.len()
                implies post_records[#[trigger] new_s[k]].value().run_prev == new_s[k - 1] by {
                if k < s.len() {
                    assert(new_s[k] == s[k]);
                    assert(new_s[k - 1] == s[k - 1]);
                    assert(s[k] != t);
                    if s[k] == old_tail {
                        assert(post_records[s[k]].value().run_prev == pre_records[s[k]].value().run_prev);
                    } else {
                        assert(post_records.contains_key(s[k]));
                        assert(post_records[s[k]] == pre_records[s[k]]);
                    }
                } else {
                    assert(k == s.len());
                    assert(new_s[k] == t);
                    assert(new_s[k - 1] == s[s.len() - 1]);
                    assert(old_tail == s[s.len() - 1]);
                }
            }
            assert forall|i: int, j: int| #![trigger new_s[i], new_s[j]]
                0 <= i < j < new_s.len() implies new_s[i] != new_s[j] by {
                if j < s.len() {
                    assert(new_s[i] == s[i] && new_s[j] == s[j]);
                } else {
                    assert(j == s.len());
                    assert(new_s[j] == t);
                    assert(new_s[i] == s[i]);
                    assert(s[i] != t);
                }
            }
        } else {
            assert(single_queue_wf(pre_q, pre_records, c2, p2));
            let s2 = pre_q.queue(c2, p2);
            assert(post_q.queue(c2, p2) == s2);
            assert forall|k: int| 0 <= k < s2.len()
                implies post_records[#[trigger] s2[k]] == pre_records[s2[k]] by {
                let u = s2[k];
                assert(pre_records[u].value().state == (ThreadState::Runnable { core: c2 as usize }));
                assert(thread_priority(pre_records[u].value()) == p2 as usize);
                assert(u != t);
                if old_tail != NONE {
                    assert(old_tail == s[s.len() - 1]);
                    assert(pre_records[old_tail].value().state == (ThreadState::Runnable { core: c }));
                    assert(thread_priority(pre_records[old_tail].value()) == p);
                    assert(u != old_tail);
                }
                assert(post_records.contains_key(u));
            }
            if s2.len() > 0 {
                let _ = s2[0];
                let _ = s2[s2.len() - 1];
            }
        }
    }

    assert forall|u: usize| #[trigger] post_records.contains_key(u)
        && post_records[u].value().state is Runnable implies {
        let r = post_records[u].value();
        let cu = r.state->Runnable_core as int;
        let pu = thread_priority(r) as int;
        &&& r.process is Some
        &&& 0 <= cu < NUM_CPUS
        &&& 0 <= pu < NUM_PRIORITIES
        &&& post_q.queue(cu, pu).contains(u)
    } by {
        if u == t {
            assert(new_s[new_s.len() - 1] == t);
            assert(post_q.queue(c as int, p as int).contains(t));
        } else {
            assert(pre_records.contains_key(u));
            if u == old_tail {
                assert(same_record_perm_but_links(pre_records[u], post_records[u]));
            } else {
                assert(post_records[u] == pre_records[u]);
            }
            let r0 = pre_records[u].value();
            let cu = r0.state->Runnable_core as int;
            let pu = thread_priority(r0) as int;
            assert(pre_q.queue(cu, pu).contains(u));
            if cu == c as int && pu == p as int {
                let ku = choose|ku: int| 0 <= ku < s.len() && s[ku] == u;
                assert(new_s[ku] == u);
            }
        }
    }
    assert(queues_wf(post_q, post_records));
    lemma_tail_is_behind_all(post_q, post_records, c as int, p, t);
}

impl CapKernel {
    /// Appends non-`Runnable` thread `t` at the tail of `(c, p)` and writes its record as
    /// `base_record` with the new queue links, updating the former tail's `run_next` when `(c, p)`
    /// was non-empty.
    #[verifier::spinoff_prover]
    pub(crate) fn enqueue_and_write(
        &mut self,
        c: usize,
        p: usize,
        t: usize,
        base_record: ThreadRecord,
    )
        requires
            queues_wf(&old(self).threads.queues, old(self).threads.records@),
            threads_wf(&old(self).list, &old(self).tables, &old(self).threads, &old(self).blocks),
            c < NUM_CPUS,
            p <= MAX_PRIORITY,
            old(self).threads.records@.contains_key(t),
            !(old(self).threads.records@[t].value().state is Runnable),
            base_record.state == (ThreadState::Runnable { core: c }),
            thread_priority(base_record) == p,
            base_record.process is Some,
            frame_save_wf(base_record),
        ensures
            queues_wf(&final(self).threads.queues, final(self).threads.records@),
            threads_wf(&final(self).list, &final(self).tables, &final(self).threads, &final(self).blocks),
            queued_at_back(&old(self).threads.queues, &final(self).threads.queues, c as int, p as int, t),
            at_back_of_priority(&final(self).threads.queues, final(self).threads.records@, c as int, p, t),
            final(self).threads.records@.dom() == old(self).threads.records@.dom(),
            forall|x: usize| x != t && #[trigger] final(self).threads.records@.contains_key(x)
                ==> same_record_perm_but_links(old(self).threads.records@[x], final(self).threads.records@[x]),
            final(self).threads.records@[t].addr() == old(self).threads.records@[t].addr(),
            final(self).threads.records@[t].is_init(),
            same_thread_but_links(final(self).threads.records@[t].value(), base_record),
            final(self).threads.holders == old(self).threads.holders,
            final(self).threads.boot_thread == old(self).threads.boot_thread,
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).mappings == old(self).mappings,
            final(self).table_pages == old(self).table_pages,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).spaces == old(self).spaces,
            final(self).processes == old(self).processes,
            final(self).endpoints == old(self).endpoints,
            final(self).replies == old(self).replies,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            final(self).tlb == old(self).tlb,
            final(self).cores == old(self).cores,
            final(self).stop_ipis == old(self).stop_ipis,
            final(self).flush_ipis == old(self).flush_ipis,
    {
        let ghost pre = *self;
        proof {
            lemma_enqueue_tail(&pre.threads.queues, pre.threads.records@, c, p, t);
            lemma_queue_slot_bounds(c as int, p as int);
            lemma_present_slot_bounds(c as int, p as int);
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
            assert(t != NONE);
        }
        let slot = c * NUM_PRIORITIES + p;
        let old_tail = *self.threads.queues.tails.get(slot);
        if old_tail == NONE {
            self.threads.queues.heads.set(slot, t);
            self.threads.queues.tails.set(slot, t);
        } else {
            proof {
                assert(pre.threads.records@.contains_key(old_tail));
                assert(old_tail != t);
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, old_tail));
            }
            let tracked mut perm_tail;
            proof {
                perm_tail = self.threads.records.borrow_mut().tracked_remove(old_tail);
            }
            let ptr_tail = PPtr::<ThreadRecord>::from_usize(old_tail + THREAD_RECORD_PAGE * PAGE_SZ);
            let rec_tail = ptr_tail.read(Tracked(&perm_tail));
            ptr_tail.write(Tracked(&mut perm_tail), ThreadRecord {
                run_next: t,
                ..rec_tail
            });
            proof {
                self.threads.records.borrow_mut().tracked_insert(old_tail, perm_tail);
            }
            self.threads.queues.tails.set(slot, t);
        }
        let w_idx = c * PRIORITY_WORDS + (p / 64);
        let b_idx = p % 64;
        let old_w = *self.threads.queues.present.get(w_idx);
        self.threads.queues.present.set(w_idx, old_w | (1u64 << (b_idx as u64)));

        let tracked mut perm_t;
        proof {
            assert(self.threads.records@.contains_key(t));
            assert(self.threads.records@[t] == pre.threads.records@[t]);
            perm_t = self.threads.records.borrow_mut().tracked_remove(t);
        }
        let ptr_t = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ);
        ptr_t.write(Tracked(&mut perm_t), ThreadRecord {
            run_prev: old_tail,
            run_next: NONE,
            ..base_record
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm_t);
        }
        self.threads.queues.seqs = Ghost(
            pre.threads.queues.seqs@.update(
                c as int,
                pre.threads.queues.seqs@[c as int].update(
                    p as int,
                    pre.threads.queues.queue(c as int, p as int).push(t),
                ),
            ),
        );
        proof {
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|x: usize| x != t && (old_tail == NONE || x != old_tail)
                && #[trigger] post.threads.records@.contains_key(x)
                implies post.threads.records@[x] == pre.threads.records@[x] by {
            }
            assert forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
                implies same_record_perm_but_links(pre.threads.records@[x], post.threads.records@[x]) by {
                if old_tail == NONE || x != old_tail {
                    assert(post.threads.records@[x] == pre.threads.records@[x]);
                }
            }
            lemma_threads_record_written(&post.list, &post.tables, &pre.threads, &post.threads, &post.blocks, t);
            lemma_enqueue_post_wf(
                &pre.threads.queues,
                &post.threads.queues,
                pre.threads.records@,
                post.threads.records@,
                c,
                p,
                t,
                old_tail,
                old_w,
            );
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_dequeue_neighbors(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
) -> (idx: int)
    requires
        queues_wf(queues, records),
        records.contains_key(t),
        records[t].value().state == (ThreadState::Runnable { core: c }),
        thread_priority(records[t].value()) == p,
    ensures
        c < NUM_CPUS,
        p < NUM_PRIORITIES,
        p <= MAX_PRIORITY,
        queues.heads.wf(),
        queues.tails.wf(),
        queues.present.wf(),
        queues.seqs@.len() == NUM_CPUS,
        forall|d: int| 0 <= d < NUM_CPUS ==> (#[trigger] queues.seqs@[d]).len() == NUM_PRIORITIES,
        ({
            let s = queues.queue(c as int, p as int);
            let prev = records[t].value().run_prev;
            let next = records[t].value().run_next;
            &&& 0 <= idx < s.len()
            &&& s[idx] == t
            &&& (idx == 0 <==> prev == NONE)
            &&& (idx > 0 ==> {
                &&& prev == s[idx - 1]
                &&& prev != NONE
                &&& prev != t
                &&& records.contains_key(prev)
                &&& records[prev].value().state == (ThreadState::Runnable { core: c })
                &&& thread_priority(records[prev].value()) == p
            })
            &&& (idx == s.len() - 1 <==> next == NONE)
            &&& (idx < s.len() - 1 ==> {
                &&& next == s[idx + 1]
                &&& next != NONE
                &&& next != t
                &&& records.contains_key(next)
                &&& records[next].value().state == (ThreadState::Runnable { core: c })
                &&& thread_priority(records[next].value()) == p
            })
            &&& (prev != NONE && next != NONE ==> prev != next)
        }),
{
    reveal(queues_wf);
    assert(0 <= c < NUM_CPUS);
    assert(0 <= p < NUM_PRIORITIES);
    let s = queues.queue(c as int, p as int);
    assert(s.contains(t));
    let idx = choose|idx: int| 0 <= idx < s.len() && s[idx] == t;
    assert(single_queue_wf(queues, records, c as int, p as int));
    let prev = records[t].value().run_prev;
    let next = records[t].value().run_next;
    if idx == 0 {
        assert(s[0] == t);
        assert(prev == NONE);
    } else {
        assert(1 <= idx < s.len());
        assert(s[idx] == t);
        assert(prev == s[idx - 1]);
        let _ = s[idx - 1];
        assert(prev != NONE);
        assert(s[idx - 1] != s[idx]);
        assert(prev != t);
    }
    if idx == s.len() - 1 {
        assert(s[s.len() - 1] == t);
        assert(next == NONE);
    } else {
        assert(0 <= idx < s.len() - 1);
        assert(s[idx] == t);
        assert(next == s[idx + 1]);
        let _ = s[idx + 1];
        assert(next != NONE);
        assert(s[idx] != s[idx + 1]);
        assert(next != t);
        if idx > 0 {
            assert(0 <= idx - 1 < idx + 1 < s.len());
            assert(s[idx - 1] != s[idx + 1]);
            assert(prev != next);
        }
    }
    idx
}

/// What `single_queue_wf` says of the member at index `k`, as one instantiation.
proof fn lemma_queue_member(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: int,
    p: int,
    k: int,
)
    requires
        single_queue_wf(queues, records, c, p),
        0 <= k < queues.queue(c, p).len(),
    ensures
        ({
            let s = queues.queue(c, p);
            let r = records[s[k]].value();
            &&& s[k] != NONE
            &&& records.contains_key(s[k])
            &&& records[s[k]].is_init()
            &&& r.state == (ThreadState::Runnable { core: c as usize })
            &&& thread_priority(r) == p as usize
            &&& r.process is Some
            &&& r.run_prev == (if k == 0 { NONE } else { s[k - 1] })
            &&& r.run_next == (if k == s.len() - 1 { NONE } else { s[k + 1] })
        }),
{
}

/// What `single_queue_wf` says of two different indices.
proof fn lemma_queue_distinct(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: int,
    p: int,
    i: int,
    j: int,
)
    requires
        single_queue_wf(queues, records, c, p),
        0 <= i < queues.queue(c, p).len(),
        0 <= j < queues.queue(c, p).len(),
        i != j,
    ensures
        queues.queue(c, p)[i] != queues.queue(c, p)[j],
{
}

/// What `single_queue_wf` says of the head, the tail and the presence bit.
proof fn lemma_queue_ends(
    queues: &RunQueues,
    records: Map<usize, PointsTo<ThreadRecord>>,
    c: int,
    p: int,
)
    requires
        single_queue_wf(queues, records, c, p),
    ensures
        ({
            let s = queues.queue(c, p);
            let slot = queue_slot(c, p);
            &&& bit_is_set(queues.present@[present_word(c, p)], present_bit(p)) == (s.len() > 0)
            &&& queues.heads@[slot] == (if s.len() == 0 { NONE } else { s[0] })
            &&& queues.tails@[slot] == (if s.len() == 0 { NONE } else { s[s.len() - 1] })
        }),
{
}

/// The element at index `k` of `s` with index `idx` removed.
proof fn lemma_removed_at(s: Seq<usize>, idx: int, k: int)
    requires
        0 <= idx < s.len(),
        0 <= k < s.len() - 1,
    ensures
        s.remove(idx).len() == s.len() - 1,
        s.remove(idx)[k] == s[if k < idx { k } else { k + 1 }],
{
    s.remove_ensures(idx);
}

/// One dequeue of `t`, at index `idx` of queue `(c, p)` between `prev` and `next`: what the step
/// leaves in that queue's fields and in the records.
spec fn dequeue_step(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
) -> bool {
    let s = pre_q.queue(c as int, p as int);
    let slot = queue_slot(c as int, p as int);
    let w_idx = present_word(c as int, p as int);
    let b_idx = present_bit(p as int);
    &&& c < NUM_CPUS
    &&& p < NUM_PRIORITIES
    &&& single_queue_wf(pre_q, pre_records, c as int, p as int)
    &&& 0 <= idx < s.len()
    &&& s[idx] == t
    &&& prev == (if idx == 0 { NONE } else { s[idx - 1] })
    &&& next == (if idx == s.len() - 1 { NONE } else { s[idx + 1] })
    &&& post_q.queue(c as int, p as int) == s.remove(idx)
    &&& post_q.heads@[slot] == (if prev == NONE { next } else { pre_q.heads@[slot] })
    &&& post_q.tails@[slot] == (if next == NONE { prev } else { pre_q.tails@[slot] })
    &&& (if prev == NONE && next == NONE {
        !bit_is_set(post_q.present@[w_idx], b_idx)
    } else {
        post_q.present@[w_idx] == pre_q.present@[w_idx]
    })
    &&& post_records.dom() == pre_records.dom()
    &&& forall|x: usize| x != t && #[trigger] post_records.contains_key(x)
        ==> same_record_perm_but_links(pre_records[x], post_records[x])
    &&& (prev != NONE ==> {
        &&& post_records[prev].value().run_prev == pre_records[prev].value().run_prev
        &&& post_records[prev].value().run_next == next
    })
    &&& (next != NONE ==> {
        &&& post_records[next].value().run_prev == prev
        &&& post_records[next].value().run_next == pre_records[next].value().run_next
    })
    &&& forall|x: usize| x != t && (prev == NONE || x != prev) && (next == NONE || x != next)
        && #[trigger] post_records.contains_key(x)
        ==> post_records[x] == pre_records[x]
}

/// After the step, the record of the member that was at index `k` of the queue, `k` not the
/// dequeued index: unchanged but for the links that pointed at the dequeued thread.
proof fn lemma_dequeue_step_member(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
    k: int,
)
    requires
        dequeue_step(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next),
        0 <= k < pre_q.queue(c as int, p as int).len(),
        k != idx,
    ensures
        ({
            let s = pre_q.queue(c as int, p as int);
            let r = post_records[s[k]].value();
            &&& s[k] != NONE
            &&& post_records.contains_key(s[k])
            &&& post_records[s[k]].is_init()
            &&& r.state == (ThreadState::Runnable { core: c })
            &&& thread_priority(r) == p
            &&& r.process is Some
            &&& r.run_prev == (if k == 0 {
                NONE
            } else if k == idx + 1 {
                prev
            } else {
                s[k - 1]
            })
            &&& r.run_next == (if k == s.len() - 1 {
                NONE
            } else if k == idx - 1 {
                next
            } else {
                s[k + 1]
            })
        }),
{
    hide(single_queue_wf);
    let s = pre_q.queue(c as int, p as int);
    let u = s[k];
    lemma_queue_member(pre_q, pre_records, c as int, p as int, k);
    lemma_queue_distinct(pre_q, pre_records, c as int, p as int, k, idx);
    assert(u != t);
    assert(pre_records.contains_key(u));
    assert(post_records.contains_key(u));
    assert(same_record_perm_but_links(pre_records[u], post_records[u]));
    if k == idx - 1 {
        assert(u == prev);
    } else if k == idx + 1 {
        assert(u == next);
    } else {
        if idx > 0 {
            lemma_queue_distinct(pre_q, pre_records, c as int, p as int, k, idx - 1);
        }
        if idx < s.len() - 1 {
            lemma_queue_distinct(pre_q, pre_records, c as int, p as int, k, idx + 1);
        }
        assert(prev == NONE || u != prev);
        assert(next == NONE || u != next);
        assert(post_records[u] == pre_records[u]);
    }
}

/// After the step, the member at index `k` of the queue the thread left, with its links.
proof fn lemma_dequeued_at(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
    k: int,
)
    requires
        dequeue_step(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next),
        0 <= k < pre_q.queue(c as int, p as int).len() - 1,
    ensures
        ({
            let s = pre_q.queue(c as int, p as int);
            let ns = post_q.queue(c as int, p as int);
            let r = post_records[ns[k]].value();
            &&& ns.len() == s.len() - 1
            &&& ns[k] != NONE
            &&& post_records.contains_key(ns[k])
            &&& post_records[ns[k]].is_init()
            &&& r.state == (ThreadState::Runnable { core: c })
            &&& thread_priority(r) == p
            &&& r.process is Some
            &&& r.run_prev == (if k == 0 { NONE } else { ns[k - 1] })
            &&& r.run_next == (if k == ns.len() - 1 { NONE } else { ns[k + 1] })
        }),
{
    hide(single_queue_wf);
    let s = pre_q.queue(c as int, p as int);
    let ns = post_q.queue(c as int, p as int);
    let o = if k < idx { k } else { k + 1 };
    lemma_removed_at(s, idx, k);
    assert(ns[k] == s[o]);
    lemma_dequeue_step_member(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next, o);
    if k > 0 {
        lemma_removed_at(s, idx, k - 1);
    }
    if k < s.len() - 2 {
        lemma_removed_at(s, idx, k + 1);
    }
}

/// After the step, two different indices of the queue the thread left hold different threads.
proof fn lemma_dequeued_distinct_at(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
    i: int,
    j: int,
)
    requires
        dequeue_step(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next),
        0 <= i < j < pre_q.queue(c as int, p as int).len() - 1,
    ensures
        post_q.queue(c as int, p as int)[i] != post_q.queue(c as int, p as int)[j],
{
    hide(single_queue_wf);
    let s = pre_q.queue(c as int, p as int);
    lemma_removed_at(s, idx, i);
    lemma_removed_at(s, idx, j);
    lemma_queue_distinct(
        pre_q,
        pre_records,
        c as int,
        p as int,
        if i < idx { i } else { i + 1 },
        if j < idx { j } else { j + 1 },
    );
}

/// After the step, the head, the tail and the presence bit of the queue the thread left.
proof fn lemma_dequeued_ends(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
)
    requires
        dequeue_step(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next),
    ensures
        ({
            let s = pre_q.queue(c as int, p as int);
            let ns = post_q.queue(c as int, p as int);
            let slot = queue_slot(c as int, p as int);
            &&& ns.len() == s.len() - 1
            &&& bit_is_set(post_q.present@[present_word(c as int, p as int)], present_bit(p as int))
                == (ns.len() > 0)
            &&& post_q.heads@[slot] == (if ns.len() == 0 { NONE } else { ns[0] })
            &&& post_q.tails@[slot] == (if ns.len() == 0 { NONE } else { ns[ns.len() - 1] })
        }),
{
    hide(single_queue_wf);
    let s = pre_q.queue(c as int, p as int);
    s.remove_ensures(idx);
    lemma_queue_ends(pre_q, pre_records, c as int, p as int);
    if s.len() >= 2 {
        if idx == 0 {
            lemma_queue_member(pre_q, pre_records, c as int, p as int, 1);
        } else {
            lemma_queue_member(pre_q, pre_records, c as int, p as int, idx - 1);
        }
        lemma_removed_at(s, idx, 0);
        if idx < s.len() - 1 {
            lemma_queue_member(pre_q, pre_records, c as int, p as int, idx + 1);
        }
        lemma_removed_at(s, idx, s.len() - 2);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_dequeued_target_queue_wf(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
)
    requires
        dequeue_step(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next),
    ensures
        single_queue_wf(post_q, post_records, c as int, p as int),
{
    hide(single_queue_wf);
    hide(dequeue_step);
    let ns = post_q.queue(c as int, p as int);
    lemma_dequeued_ends(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next);
    if ns.len() > 0 {
        lemma_dequeued_at(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next, 0);
        lemma_dequeued_at(
            pre_q,
            post_q,
            pre_records,
            post_records,
            c,
            p,
            t,
            idx,
            prev,
            next,
            ns.len() - 1,
        );
    }
    assert forall|k: int| 0 <= k < ns.len() implies {
        let u = #[trigger] ns[k];
        &&& u != NONE
        &&& post_records.contains_key(u)
        &&& post_records[u].is_init()
        &&& post_records[u].value().state == (ThreadState::Runnable { core: c })
        &&& thread_priority(post_records[u].value()) == p
        &&& post_records[u].value().process is Some
    } by {
        lemma_dequeued_at(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next, k);
    }
    assert forall|k: int| 0 <= k < ns.len() - 1
        implies post_records[#[trigger] ns[k]].value().run_next == ns[k + 1] by {
        lemma_dequeued_at(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next, k);
    }
    assert forall|k: int| 1 <= k < ns.len()
        implies post_records[#[trigger] ns[k]].value().run_prev == ns[k - 1] by {
        lemma_dequeued_at(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next, k);
    }
    assert forall|i: int, j: int| #![trigger ns[i], ns[j]]
        0 <= i < j < ns.len() implies ns[i] != ns[j] by {
        lemma_dequeued_distinct_at(
            pre_q,
            post_q,
            pre_records,
            post_records,
            c,
            p,
            t,
            idx,
            prev,
            next,
            i,
            j,
        );
    }
    assert(single_queue_wf(post_q, post_records, c as int, p as int)) by {
        reveal(single_queue_wf);
    }
}

/// A queue whose sequence, head, tail and presence bit are as they were, over records that are
/// as they were for its members, is still well formed.
proof fn lemma_single_queue_frame(
    q1: &RunQueues,
    q2: &RunQueues,
    r1: Map<usize, PointsTo<ThreadRecord>>,
    r2: Map<usize, PointsTo<ThreadRecord>>,
    c: int,
    p: int,
)
    requires
        single_queue_wf(q1, r1, c, p),
        q2.queue(c, p) == q1.queue(c, p),
        q2.heads@[queue_slot(c, p)] == q1.heads@[queue_slot(c, p)],
        q2.tails@[queue_slot(c, p)] == q1.tails@[queue_slot(c, p)],
        bit_is_set(q2.present@[present_word(c, p)], present_bit(p))
            == bit_is_set(q1.present@[present_word(c, p)], present_bit(p)),
        r2.dom() == r1.dom(),
        forall|k: int| 0 <= k < q1.queue(c, p).len()
            ==> r2[#[trigger] q1.queue(c, p)[k]] == r1[q1.queue(c, p)[k]],
    ensures
        single_queue_wf(q2, r2, c, p),
{
    hide(single_queue_wf);
    let s = q1.queue(c, p);
    lemma_queue_ends(q1, r1, c, p);
    if s.len() > 0 {
        lemma_queue_member(q1, r1, c, p, 0);
        lemma_queue_member(q1, r1, c, p, s.len() - 1);
    }
    assert forall|k: int| 0 <= k < s.len() implies {
        let u = #[trigger] s[k];
        &&& u != NONE
        &&& r2.contains_key(u)
        &&& r2[u].is_init()
        &&& r2[u].value().state == (ThreadState::Runnable { core: c as usize })
        &&& thread_priority(r2[u].value()) == p as usize
        &&& r2[u].value().process is Some
    } by {
        lemma_queue_member(q1, r1, c, p, k);
    }
    assert forall|k: int| 0 <= k < s.len() - 1
        implies r2[#[trigger] s[k]].value().run_next == s[k + 1] by {
        lemma_queue_member(q1, r1, c, p, k);
    }
    assert forall|k: int| 1 <= k < s.len()
        implies r2[#[trigger] s[k]].value().run_prev == s[k - 1] by {
        lemma_queue_member(q1, r1, c, p, k);
    }
    assert forall|i: int, j: int| #![trigger s[i], s[j]]
        0 <= i < j < s.len() implies s[i] != s[j] by {
        lemma_queue_distinct(q1, r1, c, p, i, j);
    }
    assert(single_queue_wf(q2, r2, c, p)) by {
        reveal(single_queue_wf);
    }
}

/// After the step, a queue other than the one the thread left is still well formed: none of its
/// members is the dequeued thread or one of its neighbours, so their records are as they were.
proof fn lemma_dequeue_other_queue_wf(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
    c2: int,
    p2: int,
)
    requires
        dequeue_step(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next),
        0 <= c2 < NUM_CPUS,
        0 <= p2 < NUM_PRIORITIES,
        c2 != c as int || p2 != p as int,
        single_queue_wf(pre_q, pre_records, c2, p2),
        post_q.queue(c2, p2) == pre_q.queue(c2, p2),
        post_q.heads@[queue_slot(c2, p2)] == pre_q.heads@[queue_slot(c2, p2)],
        post_q.tails@[queue_slot(c2, p2)] == pre_q.tails@[queue_slot(c2, p2)],
        bit_is_set(post_q.present@[present_word(c2, p2)], present_bit(p2))
            == bit_is_set(pre_q.present@[present_word(c2, p2)], present_bit(p2)),
    ensures
        single_queue_wf(post_q, post_records, c2, p2),
{
    hide(single_queue_wf);
    let s = pre_q.queue(c as int, p as int);
    let s2 = pre_q.queue(c2, p2);
    lemma_queue_member(pre_q, pre_records, c as int, p as int, idx);
    if idx > 0 {
        lemma_queue_member(pre_q, pre_records, c as int, p as int, idx - 1);
    }
    if idx < s.len() - 1 {
        lemma_queue_member(pre_q, pre_records, c as int, p as int, idx + 1);
    }
    assert forall|k: int| 0 <= k < s2.len()
        implies post_records[#[trigger] s2[k]] == pre_records[s2[k]] by {
        let u = s2[k];
        lemma_queue_member(pre_q, pre_records, c2, p2, k);
        assert(u != t);
        assert(prev == NONE || u != prev);
        assert(next == NONE || u != next);
        assert(post_records.contains_key(u));
    }
    lemma_single_queue_frame(pre_q, post_q, pre_records, post_records, c2, p2);
}

#[verifier::spinoff_prover]
proof fn lemma_dequeue_post_wf(
    pre_q: &RunQueues,
    post_q: &RunQueues,
    pre_records: Map<usize, PointsTo<ThreadRecord>>,
    post_records: Map<usize, PointsTo<ThreadRecord>>,
    c: usize,
    p: usize,
    t: usize,
    idx: int,
    prev: usize,
    next: usize,
    old_w: u64,
)
    requires
        queues_wf(pre_q, pre_records),
        c < NUM_CPUS,
        p < NUM_PRIORITIES,
        post_q.heads.wf(),
        post_q.tails.wf(),
        post_q.present.wf(),
        ({
            let s = pre_q.queue(c as int, p as int);
            let slot = queue_slot(c as int, p as int);
            let w_idx = present_word(c as int, p as int);
            let b_idx = present_bit(p as int);
            &&& 0 <= idx < s.len()
            &&& s[idx] == t
            &&& prev == (if idx == 0 { NONE } else { s[idx - 1] })
            &&& next == (if idx == s.len() - 1 { NONE } else { s[idx + 1] })
            &&& old_w == pre_q.present@[w_idx]
            &&& post_q.seqs@ == pre_q.seqs@.update(
                c as int,
                pre_q.seqs@[c as int].update(p as int, s.remove(idx)),
            )
            &&& post_q.heads@ == (if prev == NONE {
                pre_q.heads@.update(slot, next)
            } else {
                pre_q.heads@
            })
            &&& post_q.tails@ == (if next == NONE {
                pre_q.tails@.update(slot, prev)
            } else {
                pre_q.tails@
            })
            &&& post_q.present@ == (if prev == NONE && next == NONE {
                pre_q.present@.update(w_idx, old_w & !(1u64 << (b_idx as u64)))
            } else {
                pre_q.present@
            })
        }),
        post_records.dom() == pre_records.dom(),
        !(post_records[t].value().state is Runnable),
        forall|x: usize| x != t && #[trigger] post_records.contains_key(x)
            ==> same_record_perm_but_links(pre_records[x], post_records[x]),
        prev != NONE ==> {
            &&& post_records[prev].value().run_prev == pre_records[prev].value().run_prev
            &&& post_records[prev].value().run_next == next
        },
        next != NONE ==> {
            &&& post_records[next].value().run_prev == prev
            &&& post_records[next].value().run_next == pre_records[next].value().run_next
        },
        forall|x: usize| x != t && (prev == NONE || x != prev) && (next == NONE || x != next)
            && #[trigger] post_records.contains_key(x)
            ==> post_records[x] == pre_records[x],
    ensures
        queues_wf(post_q, post_records),
        dequeued_from(pre_q, post_q, c as int, p as int, t),
{
    hide(single_queue_wf);
    reveal(queues_wf);
    let s = pre_q.queue(c as int, p as int);
    let slot = queue_slot(c as int, p as int);
    let w_idx = present_word(c as int, p as int);
    let b_idx = present_bit(p as int);
    lemma_queue_slot_bounds(c as int, p as int);
    lemma_present_slot_bounds(c as int, p as int);
    assert(single_queue_wf(pre_q, pre_records, c as int, p as int));
    if prev == NONE && next == NONE {
        lemma_and_not_bit_u64(old_w, b_idx);
    }
    assert(post_q.queue(c as int, p as int) == s.remove(idx));
    assert(dequeue_step(pre_q, post_q, pre_records, post_records, c, p, t, idx, prev, next));
    lemma_dequeued_target_queue_wf(
        pre_q,
        post_q,
        pre_records,
        post_records,
        c,
        p,
        t,
        idx,
        prev,
        next,
    );

    assert forall|c2: int, p2: int| 0 <= c2 < NUM_CPUS && 0 <= p2 < NUM_PRIORITIES
        implies #[trigger] single_queue_wf(post_q, post_records, c2, p2) by {
        if c2 == c as int && p2 == p as int {
        } else {
            assert(single_queue_wf(pre_q, pre_records, c2, p2));
            lemma_queue_slot_bounds(c2, p2);
            lemma_present_slot_bounds(c2, p2);
            assert(queue_slot(c2, p2) != slot);
            assert(post_q.heads@[queue_slot(c2, p2)] == pre_q.heads@[queue_slot(c2, p2)]);
            assert(post_q.tails@[queue_slot(c2, p2)] == pre_q.tails@[queue_slot(c2, p2)]);
            if present_word(c2, p2) == w_idx {
                assert(present_bit(p2) != b_idx);
                if prev == NONE && next == NONE {
                    assert(bit_is_set(old_w & !(1u64 << (b_idx as u64)), present_bit(p2)) == bit_is_set(old_w, present_bit(p2)));
                    assert(bit_is_set(post_q.present@[w_idx], present_bit(p2)) == bit_is_set(old_w, present_bit(p2)));
                }
            } else {
                assert(post_q.present@[present_word(c2, p2)] == pre_q.present@[present_word(c2, p2)]);
            }
            assert(post_q.queue(c2, p2) == pre_q.queue(c2, p2));
            lemma_dequeue_other_queue_wf(
                pre_q,
                post_q,
                pre_records,
                post_records,
                c,
                p,
                t,
                idx,
                prev,
                next,
                c2,
                p2,
            );
        }
    }

    assert forall|u: usize| #[trigger] post_records.contains_key(u)
        && post_records[u].value().state is Runnable implies {
        let r = post_records[u].value();
        let cu = r.state->Runnable_core as int;
        let pu = thread_priority(r) as int;
        &&& r.process is Some
        &&& 0 <= cu < NUM_CPUS
        &&& 0 <= pu < NUM_PRIORITIES
        &&& post_q.queue(cu, pu).contains(u)
    } by {
        assert(u != t);
        assert(same_record_perm_but_links(pre_records[u], post_records[u]));
        assert(pre_records.contains_key(u));
        let r0 = pre_records[u].value();
        let cu = r0.state->Runnable_core as int;
        let pu = thread_priority(r0) as int;
        assert(pre_q.queue(cu, pu).contains(u));
        if cu == c as int && pu == p as int {
            let ku = choose|ku: int| 0 <= ku < s.len() && s[ku] == u;
            assert(ku != idx);
            let kn = if ku < idx { ku } else { ku - 1 };
            lemma_removed_at(s, idx, kn);
            assert(post_q.queue(c as int, p as int)[kn] == u);
        } else {
            assert(post_q.queue(cu, pu) == pre_q.queue(cu, pu));
        }
    }
    assert(0 <= idx < s.len() && s[idx] == t && post_q.queue(c as int, p as int) == s.remove(idx));
}

impl CapKernel {
    /// Unlinks `Runnable` thread `t` from `(c, p)` in O(1) and writes its record as non-`Runnable`
    /// `base_record` with `NONE` links, updating neighbor links, `heads`/`tails`, and clearing the
    /// `present` bit when `(c, p)` becomes empty.
    #[verifier::spinoff_prover]
    pub(crate) fn dequeue_and_write(
        &mut self,
        c: usize,
        p: usize,
        t: usize,
        base_record: ThreadRecord,
    )
        requires
            queues_wf(&old(self).threads.queues, old(self).threads.records@),
            threads_wf(&old(self).list, &old(self).tables, &old(self).threads, &old(self).blocks),
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().state == (ThreadState::Runnable { core: c }),
            thread_priority(old(self).threads.records@[t].value()) == p,
            !(base_record.state is Runnable),
            frame_save_wf(base_record),
        ensures
            c < NUM_CPUS,
            p <= MAX_PRIORITY,
            queues_wf(&final(self).threads.queues, final(self).threads.records@),
            threads_wf(&final(self).list, &final(self).tables, &final(self).threads, &final(self).blocks),
            dequeued_from(&old(self).threads.queues, &final(self).threads.queues, c as int, p as int, t),
            final(self).threads.records@.dom() == old(self).threads.records@.dom(),
            forall|x: usize| x != t && #[trigger] final(self).threads.records@.contains_key(x)
                ==> same_record_perm_but_links(old(self).threads.records@[x], final(self).threads.records@[x]),
            final(self).threads.records@[t].addr() == old(self).threads.records@[t].addr(),
            final(self).threads.records@[t].is_init(),
            same_thread_but_links(final(self).threads.records@[t].value(), base_record),
            final(self).threads.holders == old(self).threads.holders,
            final(self).threads.boot_thread == old(self).threads.boot_thread,
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).mappings == old(self).mappings,
            final(self).table_pages == old(self).table_pages,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).spaces == old(self).spaces,
            final(self).processes == old(self).processes,
            final(self).endpoints == old(self).endpoints,
            final(self).replies == old(self).replies,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            final(self).tlb == old(self).tlb,
            final(self).cores == old(self).cores,
            final(self).stop_ipis == old(self).stop_ipis,
            final(self).flush_ipis == old(self).flush_ipis,
    {
        let ghost pre = *self;
        let ghost s = pre.threads.queues.queue(c as int, p as int);
        let ghost idx: int;
        proof {
            idx = lemma_dequeue_neighbors(&pre.threads.queues, pre.threads.records@, c, p, t);
            lemma_queue_slot_bounds(c as int, p as int);
            lemma_present_slot_bounds(c as int, p as int);
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        let ptr_t = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ);
        let old_rec = *ptr_t.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let prev = old_rec.run_prev;
        let next = old_rec.run_next;
        let slot = c * NUM_PRIORITIES + p;

        if prev == NONE {
            self.threads.queues.heads.set(slot, next);
        } else {
            proof {
                assert(pre.threads.records@.contains_key(prev));
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, prev));
            }
            let tracked mut perm_prev;
            proof {
                perm_prev = self.threads.records.borrow_mut().tracked_remove(prev);
            }
            let ptr_prev = PPtr::<ThreadRecord>::from_usize(prev + THREAD_RECORD_PAGE * PAGE_SZ);
            let rec_prev = ptr_prev.read(Tracked(&perm_prev));
            ptr_prev.write(Tracked(&mut perm_prev), ThreadRecord {
                run_next: next,
                ..rec_prev
            });
            proof {
                self.threads.records.borrow_mut().tracked_insert(prev, perm_prev);
            }
        }

        let w_idx = c * PRIORITY_WORDS + (p / 64);
        let b_idx = p % 64;
        let ghost old_w = pre.threads.queues.present@[w_idx as int];
        if next == NONE {
            self.threads.queues.tails.set(slot, prev);
            if prev == NONE {
                let cur_w = *self.threads.queues.present.get(w_idx);
                self.threads.queues.present.set(w_idx, cur_w & !(1u64 << (b_idx as u64)));
            }
        } else {
            proof {
                assert(pre.threads.records@.contains_key(next));
                assert(self.threads.records@.contains_key(next));
                assert(self.threads.records@[next] == pre.threads.records@[next]);
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, next));
            }
            let tracked mut perm_next;
            proof {
                perm_next = self.threads.records.borrow_mut().tracked_remove(next);
            }
            let ptr_next = PPtr::<ThreadRecord>::from_usize(next + THREAD_RECORD_PAGE * PAGE_SZ);
            let rec_next = ptr_next.read(Tracked(&perm_next));
            ptr_next.write(Tracked(&mut perm_next), ThreadRecord {
                run_prev: prev,
                ..rec_next
            });
            proof {
                self.threads.records.borrow_mut().tracked_insert(next, perm_next);
            }
        }

        let tracked mut perm_t;
        proof {
            assert(self.threads.records@.contains_key(t));
            assert(self.threads.records@[t] == pre.threads.records@[t]);
            perm_t = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr_t.write(Tracked(&mut perm_t), ThreadRecord {
            run_prev: NONE,
            run_next: NONE,
            ..base_record
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm_t);
        }

        let ghost new_s = s.remove(idx);
        self.threads.queues.seqs = Ghost(
            pre.threads.queues.seqs@.update(
                c as int,
                pre.threads.queues.seqs@[c as int].update(p as int, new_s),
            ),
        );

        proof {
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|x: usize| x != t && (prev == NONE || x != prev) && (next == NONE || x != next)
                && #[trigger] post.threads.records@.contains_key(x)
                implies post.threads.records@[x] == pre.threads.records@[x] by {
            }
            assert forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
                implies same_record_perm_but_links(pre.threads.records@[x], post.threads.records@[x]) by {
                if (prev == NONE || x != prev) && (next == NONE || x != next) {
                    assert(post.threads.records@[x] == pre.threads.records@[x]);
                }
            }
            lemma_threads_record_written(&post.list, &post.tables, &pre.threads, &post.threads, &post.blocks, t);
            lemma_dequeue_post_wf(
                &pre.threads.queues,
                &post.threads.queues,
                pre.threads.records@,
                post.threads.records@,
                c,
                p,
                t,
                idx,
                prev,
                next,
                old_w,
            );
        }
    }

    proof fn lemma_queues_arrays_wf(&self)
        requires
            self.wf(),
        ensures
            self.threads.queues.heads.wf(),
            self.threads.queues.tails.wf(),
            self.threads.queues.present.wf(),
    {
        reveal(queues_wf);
    }

    /// Helper for `select_thread`: the highest set bit `bit` in the highest non-zero presence word
    /// `wi` on core `c` names a non-empty queue whose head is `Runnable` on `c` at the maximum
    /// priority of any `Runnable` thread on `c`.
    proof fn lemma_selected_from_word(&self, c: usize, wi: usize, bit: usize)
        requires
            self.wf(),
            c < NUM_CPUS,
            wi < PRIORITY_WORDS,
            bit < 64,
            forall|hi: int| wi < hi < PRIORITY_WORDS
                ==> #[trigger] self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + hi] == 0u64,
            bit_is_set(self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + wi as int], bit),
            forall|k: usize| bit < k && k < 64
                ==> !#[trigger] bit_is_set(self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + wi as int], k),
        ensures
            ({
                let p = (wi * 64 + bit) as usize;
                let slot = (c * NUM_PRIORITIES + p) as int;
                let t = self.threads.queues.heads@[slot];
                let r = self.threads.records@[t].value();
                &&& p <= MAX_PRIORITY
                &&& self.threads.records@.contains_key(t)
                &&& r.state == (ThreadState::Runnable { core: c })
                &&& r.process is Some
                &&& thread_priority(r) == p
                &&& self.threads.queues.queue(c as int, p as int).len() > 0
                &&& self.threads.queues.queue(c as int, p as int)[0] == t
                &&& forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
                    && self.threads.records@[u].value().state == (ThreadState::Runnable { core: c })
                    ==> thread_priority(self.threads.records@[u].value()) <= p
            }),
    {
        reveal(queues_wf);
        let p = (wi * 64 + bit) as usize;
        lemma_queue_slot_bounds(c as int, p as int);
        lemma_present_slot_bounds(c as int, p as int);
        assert(present_word(c as int, p as int) == c as int * (PRIORITY_WORDS as int) + wi as int);
        assert(present_bit(p as int) == bit);
        assert(single_queue_wf(&self.threads.queues, self.threads.records@, c as int, p as int));
        let s = self.threads.queues.queue(c as int, p as int);
        assert(s.len() > 0);
        let t = s[0];
        assert(self.threads.queues.heads@[queue_slot(c as int, p as int)] == t);

        assert forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
            && self.threads.records@[u].value().state == (ThreadState::Runnable { core: c })
            implies thread_priority(self.threads.records@[u].value()) <= p by {
            let pu = thread_priority(self.threads.records@[u].value()) as int;
            assert(0 <= pu < NUM_PRIORITIES);
            assert(self.threads.queues.queue(c as int, pu).contains(u));
            assert(self.threads.queues.queue(c as int, pu).len() > 0);
            lemma_present_slot_bounds(c as int, pu);
            assert(single_queue_wf(&self.threads.queues, self.threads.records@, c as int, pu));
            let wu = pu / 64;
            let bu = present_bit(pu);
            assert(bit_is_set(self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + wu], bu));
            if pu > p as int {
                if wu > wi as int {
                    assert(self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + wu] == 0u64);
                    lemma_zero_word_no_bits(bu);
                } else {
                    assert(wu == wi as int);
                    assert(bit < bu && bu < 64);
                }
            }
        }
    }

    proof fn lemma_selected_none(&self, c: usize)
        requires
            self.wf(),
            c < NUM_CPUS,
            self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + 0] == 0u64,
            self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + 1] == 0u64,
            self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + 2] == 0u64,
            self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + 3] == 0u64,
        ensures
            forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
                ==> self.threads.records@[u].value().state != (ThreadState::Runnable { core: c }),
    {
        reveal(queues_wf);
        assert forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
            implies self.threads.records@[u].value().state != (ThreadState::Runnable { core: c }) by {
            if self.threads.records@[u].value().state == (ThreadState::Runnable { core: c }) {
                let pu = thread_priority(self.threads.records@[u].value()) as int;
                assert(0 <= pu < NUM_PRIORITIES);
                assert(self.threads.queues.queue(c as int, pu).contains(u));
                assert(self.threads.queues.queue(c as int, pu).len() > 0);
                lemma_present_slot_bounds(c as int, pu);
                assert(single_queue_wf(&self.threads.queues, self.threads.records@, c as int, pu));
                let wu = pu / 64;
                let bu = present_bit(pu);
                assert(wu == 0 || wu == 1 || wu == 2 || wu == 3);
                assert(self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + wu] == 0u64);
                lemma_zero_word_no_bits(bu);
            }
        }
    }

    /// Selects the thread for core `c` to run next: `None` when no thread is `Runnable` on `c`,
    /// and otherwise the thread at the front of `c`'s queue for the highest priority at which any
    /// thread is `Runnable` on `c`. Equal priorities take turns because threads put back go to the
    /// tail of their priority's queue.
    #[verifier::spinoff_prover]
    pub fn select_thread(&self, c: usize) -> (ret: Option<usize>)
        requires
            self.wf(),
            c < NUM_CPUS,
        ensures
            ret is None <==> (forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
                ==> self.threads.records@[u].value().state != (ThreadState::Runnable { core: c })),
            ret matches Some(t) ==> {
                let r = self.threads.records@[t].value();
                let p = thread_priority(r);
                &&& self.threads.records@.contains_key(t)
                &&& r.state == (ThreadState::Runnable { core: c })
                &&& r.process is Some
                &&& p <= MAX_PRIORITY
                &&& self.threads.queues.queue(c as int, p as int).len() > 0
                &&& self.threads.queues.queue(c as int, p as int)[0] == t
                &&& forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
                    && self.threads.records@[u].value().state == (ThreadState::Runnable { core: c })
                    ==> thread_priority(self.threads.records@[u].value()) <= p
            },
    {
        proof {
            self.lemma_queues_arrays_wf();
        }
        let base_w = c * PRIORITY_WORDS;
        let w3 = *self.threads.queues.present.get(base_w + 3);
        if w3 != 0 {
            let bit = highest_bit_u64(w3);
            let p = 3 * 64 + bit;
            proof {
                lemma_queue_slot_bounds(c as int, p as int);
            }
            let t = *self.threads.queues.heads.get(c * NUM_PRIORITIES + p);
            proof {
                self.lemma_selected_from_word(c, 3, bit);
                assert(self.threads.records@.contains_key(t));
            }
            return Some(t);
        }
        let w2 = *self.threads.queues.present.get(base_w + 2);
        if w2 != 0 {
            let bit = highest_bit_u64(w2);
            let p = 2 * 64 + bit;
            proof {
                lemma_queue_slot_bounds(c as int, p as int);
            }
            let t = *self.threads.queues.heads.get(c * NUM_PRIORITIES + p);
            proof {
                assert forall|hi: int| 2 < hi < PRIORITY_WORDS
                    implies #[trigger] self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + hi] == 0u64 by {
                    assert(hi == 3);
                }
                self.lemma_selected_from_word(c, 2, bit);
                assert(self.threads.records@.contains_key(t));
            }
            return Some(t);
        }
        let w1 = *self.threads.queues.present.get(base_w + 1);
        if w1 != 0 {
            let bit = highest_bit_u64(w1);
            let p = 1 * 64 + bit;
            proof {
                lemma_queue_slot_bounds(c as int, p as int);
            }
            let t = *self.threads.queues.heads.get(c * NUM_PRIORITIES + p);
            proof {
                assert forall|hi: int| 1 < hi < PRIORITY_WORDS
                    implies #[trigger] self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + hi] == 0u64 by {
                    assert(hi == 2 || hi == 3);
                }
                self.lemma_selected_from_word(c, 1, bit);
                assert(self.threads.records@.contains_key(t));
            }
            return Some(t);
        }
        let w0 = *self.threads.queues.present.get(base_w);
        if w0 != 0 {
            let bit = highest_bit_u64(w0);
            let p = bit;
            proof {
                lemma_queue_slot_bounds(c as int, p as int);
            }
            let t = *self.threads.queues.heads.get(c * NUM_PRIORITIES + p);
            proof {
                assert forall|hi: int| 0 < hi < PRIORITY_WORDS
                    implies #[trigger] self.threads.queues.present@[c as int * (PRIORITY_WORDS as int) + hi] == 0u64 by {
                    assert(hi == 1 || hi == 2 || hi == 3);
                }
                self.lemma_selected_from_word(c, 0, bit);
                assert(self.threads.records@.contains_key(t));
            }
            return Some(t);
        }
        proof {
            self.lemma_selected_none(c);
        }
        None
    }
}

} // verus!
