// SPDX-License-Identifier: MIT

//! Endpoints and notifications as retyped objects, the objects threads wait on. Each is an order-0
//! block whose page holds its record: whether it is dead, the queue of threads waiting on it, and a
//! notification's word, all empty when it is made. A capability names one by its block's base, an
//! endpoint's carrying send, receive and grant and a notification's send and receive, and the
//! capabilities naming it hold its block's references. Both kinds are kept in one store, `Endpoints`,
//! by one invariant. See design/ipc-with-reply-object/ and
//! design/notification-word-reserves-the-waiter-bit/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arch::{lemma_partial_frame_idempotent, partial_frame};
use crate::arch::{partial_frame_of, FrameKind, Registers};
use crate::capability::block::*;
#[cfg(verus_keep_ghost)]
use crate::capability::derive::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reply::*;
#[cfg(verus_keep_ghost)]
use crate::capability::retype::*;
#[cfg(verus_keep_ghost)]
use crate::capability::schedule::{queues_wf, single_queue_wf, NUM_PRIORITIES, RunQueues};
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::steps::Steps;
use crate::capability::table::*;
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::layouts::*;
use crate::pptr::*;

/// retype_endpoint's and retype_notification's bound in the step counter: typing the block. See
/// design/one-lock-bounded-steps/.
pub const RETYPE_ENDPOINT_STEPS: usize = 2 * SMALL_PAGES_MAX;
pub const RETYPE_NOTIFICATION_STEPS: usize = 2 * SMALL_PAGES_MAX;

/// An endpoint capability carries send, receive and grant.
pub const ENDPOINT_RIGHTS: u32 = 112;

/// A notification capability carries send, to signal, and receive, to wait.
pub const NOTIFICATION_RIGHTS: u32 = 48;

/// What an endpoint or a notification keeps in its page.
#[derive(Clone, Copy)]
pub struct QueueRecord {
    /// Destroyed; its block waits for its references to go.
    pub dead: bool,
    /// The first and last thread its queue lists, `NONE` when it lists none.
    pub head: usize,
    pub tail: usize,
    /// The threads its queue lists, head first, linked through their `wait_prev` and `wait_next`:
    /// see `waits_wf`.
    pub waiters: Ghost<Seq<usize>>,
    /// An endpoint's waiting threads receive rather than send.
    pub receiving: bool,
    /// A notification's word: the badges signalled since the last wait, with bit 63 set while a thread
    /// waits. See design/notification-word-reserves-the-waiter-bit/.
    pub word: u64,
}

/// Bit 63 of a notification's word, which belongs to the kernel and is set exactly while a thread
/// waits. See design/notification-word-reserves-the-waiter-bit/.
pub const WAITER_BIT: u64 = 0x8000_0000_0000_0000; // not a page size: bit 63 of a notification's word

/// The word of r, the record of an object o: a notification's waiter bit is set exactly while its
/// queue lists a thread, and an endpoint's word is zero. See
/// design/notification-word-reserves-the-waiter-bit/.
pub open spec fn word_wf(r: QueueRecord, o: ObjectType) -> bool {
    if o is Notification {
        (r.word & WAITER_BIT != 0) == (r.waiters@.len() > 0)
    } else {
        r.word == 0
    }
}

/// A record with a zero word and an empty queue, as a fresh one has, has a well-formed word for either
/// object.
pub proof fn lemma_zero_word_wf(r: QueueRecord, o: ObjectType)
    requires
        r.word == 0,
        r.waiters@.len() == 0,
    ensures
        word_wf(r, o),
{
    assert(0u64 & 0x8000_0000_0000_0000u64 == 0) by (bit_vector); // not a page size: WAITER_BIT
}

/// A new endpoint's or notification's record: live, with no thread waiting and nothing signalled.
pub open spec fn fresh_record() -> QueueRecord {
    QueueRecord { dead: false, head: NONE, tail: NONE, waiters: Ghost(Seq::empty()), receiving: false, word: 0 }
}

/// An endpoint capability's payload.
pub open spec fn endpoint_of(base: usize) -> Payload {
    Payload { kind: CapKind::Endpoint, order: 0, rights: ENDPOINT_RIGHTS, base, badge: 0, priority: 0 }
}

/// A notification capability's payload, as its retype makes it: badge 0.
pub open spec fn notification_of(base: usize) -> Payload {
    Payload { kind: CapKind::Notification, order: 0, rights: NOTIFICATION_RIGHTS, base, badge: 0, priority: 0 }
}

/// The objects threads wait on, which `Endpoints` keeps: an endpoint or a notification.
pub open spec fn queue_object(o: ObjectType) -> bool {
    o is Endpoint || o is Notification
}

/// The capabilities naming them.
pub open spec fn queue_kind(k: CapKind) -> bool {
    k is Endpoint || k is Notification
}

/// The object a capability of a queue kind names.
pub open spec fn queue_object_of(k: CapKind) -> ObjectType {
    if k is Endpoint { ObjectType::Endpoint } else { ObjectType::Notification }
}

/// The payload a retype of a queue kind gives its capability.
pub open spec fn queue_of(k: CapKind, base: usize) -> Payload {
    if k is Endpoint { endpoint_of(base) } else { notification_of(base) }
}

/// Each endpoint's and notification's record by its block's address, and the capabilities holding its
/// block.
pub struct Endpoints {
    pub records: Tracked<Map<usize, PointsTo<QueueRecord>>>,
    pub holders: Ghost<IMap<usize, Set<usize>>>,
}

impl Endpoints {
    pub fn new() -> (ret: Self)
        ensures
            ret.records@ == Map::<usize, PointsTo<QueueRecord>>::empty(),
            ret.holders@ == IMap::<usize, Set<usize>>::empty(),
    {
        Endpoints { records: Tracked(Map::tracked_empty()), holders: Ghost(IMap::empty()) }
    }
}

/// The block at page b holds an endpoint or a notification.
pub open spec fn endpoint_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& queue_object(blocks.pages@[b as int].object)
}

/// Two distinct endpoints lie on distinct pages.
pub proof fn lemma_endpoint_pages_distinct(e: usize, u: usize)
    requires
        e % PAGE_SZ == 0,
        u % PAGE_SZ == 0,
        e != u,
    ensures
        e / PAGE_SZ != u / PAGE_SZ,
{
    lemma_fundamental_div_mod(e as int, PAGE_SZ as int);
    lemma_fundamental_div_mod(u as int, PAGE_SZ as int);
}

/// The endpoint or notification at e has its record in its block's page. Its block's references are
/// exactly its holders, it is dead at once when they go, and its word is as word_wf says.
pub open spec fn endpoint_wf(endpoints: &Endpoints, blocks: &BlockTable, e: usize) -> bool {
    &&& e % PAGE_SZ == 0
    &&& blocks.tracks_addr(e)
    &&& endpoints.records@[e].addr() == e
    &&& endpoints.records@[e].is_init()
    &&& blocks.pages@[(e / PAGE_SZ) as int].kind is Base
    &&& queue_object(blocks.pages@[(e / PAGE_SZ) as int].object)
    &&& blocks.pages@[(e / PAGE_SZ) as int].order == 0
    &&& endpoints.holders@.contains_key(e)
    &&& endpoints.holders@[e].len() == blocks.pages@[(e / PAGE_SZ) as int].refs
    &&& blocks.pages@[(e / PAGE_SZ) as int].refs == 0 ==> blocks.pages@[(e / PAGE_SZ) as int].dead
    &&& word_wf(endpoints.records@[e].value(), blocks.pages@[(e / PAGE_SZ) as int].object)
}

/// Each endpoint and notification is well formed, an endpoint's or a notification's block is one of
/// these, the capabilities of kind Endpoint or Notification are exactly the holders, and each names a
/// block typed as its kind's object: an endpoint capability an endpoint, a notification capability a
/// notification, so a signal or a wait never reaches an endpoint's queue.
pub open spec fn endpoints_wf(list: &Tree, tables: &Tables, endpoints: &Endpoints, blocks: &BlockTable) -> bool {
    &&& forall|e: usize| #[trigger] endpoints.records@.contains_key(e) ==> endpoint_wf(endpoints, blocks, e)
    &&& forall|b: usize| blocks.tracks(b as int) && #[trigger] endpoint_block(blocks, b)
        ==> endpoints.records@.contains_key((b * PAGE_SZ) as usize)
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && queue_kind(tables.payload_of(n).kind) ==> {
        &&& endpoints.records@.contains_key(tables.payload_of(n).base)
        &&& endpoints.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == 0
        &&& blocks.pages@[(tables.payload_of(n).base / PAGE_SZ) as int].object == queue_object_of(tables.payload_of(n).kind)
    }
    &&& forall|e: usize, n: usize| endpoints.records@.contains_key(e) && #[trigger] endpoints.holders@[e].contains(n) ==> {
        &&& tables.is_cap(list, n)
        &&& queue_kind(tables.payload_of(n).kind)
        &&& tables.payload_of(n).base == e
    }
}

/// Thread s[i], the i-th listed by the queue of the object at e, has a record naming e as the object
/// whose queue lists it, and links to its neighbours in s, `NONE` at either end.
pub open spec fn waiter_linked(s: Seq<usize>, threads: Map<usize, PointsTo<ThreadRecord>>, e: usize, i: int) -> bool {
    let t = s[i];
    &&& threads.contains_key(t)
    &&& threads[t].value().queued == e
    &&& threads[t].value().wait_prev == if i == 0 { NONE } else { s[i - 1] }
    &&& threads[t].value().wait_next == if i + 1 == s.len() { NONE } else { s[i + 1] }
}

/// The queue of r, the record of the object at e, which is not `NONE`: its head and tail are the
/// first and last thread it lists, `NONE` when it lists none, and each listed thread appears once and
/// is linked.
pub open spec fn wait_queue_wf(r: QueueRecord, threads: Map<usize, PointsTo<ThreadRecord>>, e: usize) -> bool {
    let s = r.waiters@;
    &&& e != NONE
    &&& s.no_duplicates()
    &&& r.head == if s.len() == 0 { NONE } else { s[0] }
    &&& r.tail == if s.len() == 0 { NONE } else { s.last() }
    &&& forall|i: int| 0 <= i < s.len() ==> #[trigger] waiter_linked(s, threads, e, i)
}

/// Every endpoint's and notification's queue is well formed; a thread naming an object as the one
/// whose queue lists it is listed there, so it is in one queue only; and a thread Blocked on an object
/// is listed in that object's queue, which makes the object an endpoint or a notification, so a match
/// can reach it. A listed thread need not be Blocked on the object: one suspended, unbound or
/// destroyed while Blocked stays listed, stale, until a match skips it. See
/// design/ipc-with-reply-object/. Opaque, as queues_wf is, so that its thread quantifiers do not fire
/// in every proof that mentions a record.
#[verifier::opaque]
pub open spec fn waits_wf(queues: Map<usize, PointsTo<QueueRecord>>, threads: Map<usize, PointsTo<ThreadRecord>>) -> bool {
    &&& forall|e: usize| #[trigger] queues.contains_key(e) ==> wait_queue_wf(queues[e].value(), threads, e)
    &&& forall|t: usize| #[trigger] threads.contains_key(t) && threads[t].value().queued != NONE ==> {
        &&& queues.contains_key(threads[t].value().queued)
        &&& queues[threads[t].value().queued].value().waiters@.contains(t)
    }
    &&& forall|t: usize| #[trigger] threads.contains_key(t) && threads[t].value().state is Blocked ==> {
        &&& threads[t].value().state->Blocked_object != NONE
        &&& threads[t].value().queued == threads[t].value().state->Blocked_object
    }
}

/// Thread record b keeps a's place in the wait queues: the same queue and links, and Blocked only as
/// a was.
pub open spec fn keeps_wait(a: ThreadRecord, b: ThreadRecord) -> bool {
    &&& b.queued == a.queued
    &&& b.wait_prev == a.wait_prev
    &&& b.wait_next == a.wait_next
    &&& b.state is Blocked ==> b.state == a.state
}

/// A queue record's queue as it was: the same head, tail and listed threads.
pub open spec fn same_queue(a: QueueRecord, b: QueueRecord) -> bool {
    &&& a.head == b.head
    &&& a.tail == b.tail
    &&& a.waiters@ == b.waiters@
}

/// A step that keeps every queue and every listed thread's place in it keeps the wait queues well
/// formed: each queue of a is in b as it was, a queue new in b lists nothing and is not at `NONE`, each thread of both
/// keeps its queue and links and is Blocked in b only as it was in a, a thread new in b is in no queue
/// and not Blocked, and a thread gone from b was in no queue.
pub proof fn lemma_waits_framed(
    qa: Map<usize, PointsTo<QueueRecord>>,
    qb: Map<usize, PointsTo<QueueRecord>>,
    ta: Map<usize, PointsTo<ThreadRecord>>,
    tb: Map<usize, PointsTo<ThreadRecord>>,
)
    requires
        waits_wf(qa, ta),
        forall|e: usize| #[trigger] qa.contains_key(e)
            ==> qb.contains_key(e) && same_queue(qa[e].value(), qb[e].value()),
        forall|e: usize| #[trigger] qb.contains_key(e) && !qa.contains_key(e)
            ==> e != NONE && same_queue(qb[e].value(), fresh_record()),
        forall|t: usize| #[trigger] tb.contains_key(t) && ta.contains_key(t) ==> keeps_wait(ta[t].value(), tb[t].value()),
        forall|t: usize| #[trigger] tb.contains_key(t) && !ta.contains_key(t)
            ==> tb[t].value().queued == NONE && !(tb[t].value().state is Blocked),
        forall|t: usize| #[trigger] ta.contains_key(t) && !tb.contains_key(t) ==> ta[t].value().queued == NONE,
    ensures
        waits_wf(qb, tb),
{
    reveal(waits_wf);
    assert forall|e: usize| #[trigger] qb.contains_key(e) implies wait_queue_wf(qb[e].value(), tb, e) by {
        let s = qb[e].value().waiters@;
        if qa.contains_key(e) {
            assert(wait_queue_wf(qa[e].value(), ta, e));
            assert forall|i: int| 0 <= i < s.len() implies #[trigger] waiter_linked(s, tb, e, i) by {
                assert(waiter_linked(s, ta, e, i));
                let t = s[i];
                assert(ta.contains_key(t) && ta[t].value().queued == e);
                assert(tb.contains_key(t));
            }
        } else {
            assert(s.len() == 0);
        }
    }
    assert forall|t: usize| #[trigger] tb.contains_key(t) && tb[t].value().queued != NONE implies {
        &&& qb.contains_key(tb[t].value().queued)
        &&& qb[tb[t].value().queued].value().waiters@.contains(t)
    } by {
        assert(ta.contains_key(t));
        assert(qa.contains_key(ta[t].value().queued));
    }
    assert forall|t: usize| #[trigger] tb.contains_key(t) && tb[t].value().state is Blocked implies {
        &&& tb[t].value().state->Blocked_object != NONE
        &&& tb[t].value().queued == tb[t].value().state->Blocked_object
    } by {
        assert(ta.contains_key(t));
    }
}

/// A thread typed at base, in no queue and not Blocked, keeps the wait queues well formed.
pub proof fn lemma_waits_thread_added(
    queues: Map<usize, PointsTo<QueueRecord>>,
    pre: Map<usize, PointsTo<ThreadRecord>>,
    post: Map<usize, PointsTo<ThreadRecord>>,
    base: usize,
)
    requires
        waits_wf(queues, pre),
        !pre.contains_key(base),
        post == pre.insert(base, post[base]),
        post[base].value().queued == NONE,
        !(post[base].value().state is Blocked),
    ensures
        waits_wf(queues, post),
{
    lemma_waits_framed(queues, queues, pre, post);
}

/// A step that writes thread t's record, keeping every thread's place in the wait queues, keeps them
/// well formed.
pub proof fn lemma_waits_written(
    queues: Map<usize, PointsTo<QueueRecord>>,
    pre: Map<usize, PointsTo<ThreadRecord>>,
    post: Map<usize, PointsTo<ThreadRecord>>,
    t: usize,
)
    requires
        waits_wf(queues, pre),
        pre.contains_key(t),
        post.dom() == pre.dom(),
        keeps_wait(pre[t].value(), post[t].value()),
        forall|x: usize| x != t && #[trigger] post.contains_key(x) ==> keeps_wait(pre[x].value(), post[x].value()),
    ensures
        waits_wf(queues, post),
{
    assert forall|x: usize| #[trigger] post.contains_key(x) && pre.contains_key(x)
        implies keeps_wait(pre[x].value(), post[x].value()) by {}
    lemma_waits_framed(queues, queues, pre, post);
}

/// With no queue object and no thread, the wait queues are well formed.
pub proof fn lemma_waits_empty()
    ensures
        waits_wf(Map::<usize, PointsTo<QueueRecord>>::empty(), Map::<usize, PointsTo<ThreadRecord>>::empty()),
{
    reveal(waits_wf);
}

/// The queue of the object at e has no head exactly when it lists no thread, since no thread is at
/// `NONE`.
pub proof fn lemma_waits_head(queues: Map<usize, PointsTo<QueueRecord>>, threads: Map<usize, PointsTo<ThreadRecord>>, e: usize)
    requires
        waits_wf(queues, threads),
        queues.contains_key(e),
        forall|t: usize| #[trigger] threads.contains_key(t) ==> t != NONE,
    ensures
        (queues[e].value().head == NONE) == (queues[e].value().waiters@.len() == 0),
{
    reveal(waits_wf);
    let s = queues[e].value().waiters@;
    assert(wait_queue_wf(queues[e].value(), threads, e));
    if s.len() > 0 {
        assert(waiter_linked(s, threads, e, 0));
    }
}

/// Dropping the record of an object whose queue lists no thread keeps the wait queues well formed: no
/// thread names it as the object whose queue lists it.
pub proof fn lemma_waits_queue_removed(queues: Map<usize, PointsTo<QueueRecord>>, threads: Map<usize, PointsTo<ThreadRecord>>, e: usize)
    requires
        waits_wf(queues, threads),
        queues.contains_key(e),
        queues[e].value().waiters@.len() == 0,
    ensures
        waits_wf(queues.remove(e), threads),
{
    reveal(waits_wf);
    let qb = queues.remove(e);
    assert forall|x: usize| #[trigger] qb.contains_key(x) implies wait_queue_wf(qb[x].value(), threads, x) by {
        assert(queues.contains_key(x));
    }
    assert forall|t: usize| #[trigger] threads.contains_key(t) && threads[t].value().queued != NONE implies {
        &&& qb.contains_key(threads[t].value().queued)
        &&& qb[threads[t].value().queued].value().waiters@.contains(t)
    } by {
        let q = threads[t].value().queued;
        assert(queues[q].value().waiters@.contains(t));
        if q == e {
            let i = choose|i: int| 0 <= i < queues[e].value().waiters@.len() && queues[e].value().waiters@[i] == t;
            assert(false);
        }
    }
}

/// Locates thread `t`, currently listed in `threads[t].value().queued`'s wait queue, and exposes
/// its `wait_prev` and `wait_next` neighbors.
#[verifier::spinoff_prover]
pub proof fn lemma_waits_neighbors(
    queues: Map<usize, PointsTo<QueueRecord>>,
    threads: Map<usize, PointsTo<ThreadRecord>>,
    t: usize,
) -> (idx: int)
    requires
        waits_wf(queues, threads),
        threads.contains_key(t),
        threads[t].value().queued != NONE,
        forall|u: usize| #[trigger] threads.contains_key(u) ==> u != NONE,
    ensures
        ({
            let e = threads[t].value().queued;
            let s = queues[e].value().waiters@;
            let prev = threads[t].value().wait_prev;
            let next = threads[t].value().wait_next;
            &&& queues.contains_key(e)
            &&& 0 <= idx < s.len()
            &&& s[idx] == t
            &&& (idx == 0 <==> prev == NONE)
            &&& (idx > 0 ==> {
                &&& prev == s[idx - 1]
                &&& prev != NONE
                &&& prev != t
                &&& threads.contains_key(prev)
                &&& threads[prev].value().queued == e
            })
            &&& (idx == s.len() - 1 <==> next == NONE)
            &&& (idx < s.len() - 1 ==> {
                &&& next == s[idx + 1]
                &&& next != NONE
                &&& next != t
                &&& threads.contains_key(next)
                &&& threads[next].value().queued == e
            })
            &&& (prev != NONE && next != NONE ==> prev != next)
        }),
{
    reveal(waits_wf);
    let e = threads[t].value().queued;
    let s = queues[e].value().waiters@;
    let idx = choose|k: int| 0 <= k < s.len() && s[k] == t;
    assert(waiter_linked(s, threads, e, idx));
    if idx > 0 {
        assert(waiter_linked(s, threads, e, idx - 1));
    }
    if idx + 1 < s.len() {
        assert(waiter_linked(s, threads, e, idx + 1));
    }
    idx
}

/// Inspects queue `e` before appending `t`, whose `queued` field is `NONE`: `t` is absent from `e`'s
/// queue, `tail` is `NONE` iff the queue is empty, and any existing `tail` differs from `t`.
pub proof fn lemma_waits_tail(
    queues: Map<usize, PointsTo<QueueRecord>>,
    threads: Map<usize, PointsTo<ThreadRecord>>,
    e: usize,
    t: usize,
)
    requires
        waits_wf(queues, threads),
        queues.contains_key(e),
        threads.contains_key(t),
        threads[t].value().queued == NONE,
        forall|u: usize| #[trigger] threads.contains_key(u) ==> u != NONE,
    ensures
        ({
            let r = queues[e].value();
            let s = r.waiters@;
            &&& !s.contains(t)
            &&& (r.head == NONE <==> s.len() == 0)
            &&& (r.tail == NONE <==> s.len() == 0)
            &&& r.tail != NONE ==> {
                &&& r.tail == s[s.len() - 1]
                &&& r.tail != t
                &&& threads.contains_key(r.tail)
                &&& threads[r.tail].value().queued == e
            }
        }),
{
    reveal(waits_wf);
    let r = queues[e].value();
    let s = r.waiters@;
    if s.contains(t) {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == t;
        assert(waiter_linked(s, threads, e, k));
    }
    if s.len() > 0 {
        assert(waiter_linked(s, threads, e, 0));
        assert(waiter_linked(s, threads, e, (s.len() - 1) as int));
    }
}

/// Unlinking `t` (at index `idx`, not `Blocked`) from `ta[t].value().queued` keeps `waits_wf`
/// across every queue and thread.
#[verifier::spinoff_prover]
pub proof fn lemma_waits_unlinked(
    qa: Map<usize, PointsTo<QueueRecord>>,
    qb: Map<usize, PointsTo<QueueRecord>>,
    ta: Map<usize, PointsTo<ThreadRecord>>,
    tb: Map<usize, PointsTo<ThreadRecord>>,
    t: usize,
    idx: int,
)
    requires
        waits_wf(qa, ta),
        ta.contains_key(t),
        ta[t].value().queued != NONE,
        !(ta[t].value().state is Blocked),
        forall|u: usize| #[trigger] ta.contains_key(u) ==> u != NONE,
        qa.contains_key(ta[t].value().queued),
        ({
            let q = ta[t].value().queued;
            let r0 = qa[q].value();
            let prev = ta[t].value().wait_prev;
            let next = ta[t].value().wait_next;
            &&& 0 <= idx < r0.waiters@.len()
            &&& r0.waiters@[idx] == t
            &&& (idx == 0 <==> prev == NONE)
            &&& (idx > 0 ==> prev == r0.waiters@[idx - 1] && prev != NONE && prev != t && ta.contains_key(prev) && ta[prev].value().queued == q)
            &&& (idx == r0.waiters@.len() - 1 <==> next == NONE)
            &&& (idx < r0.waiters@.len() - 1 ==> next == r0.waiters@[idx + 1] && next != NONE && next != t && ta.contains_key(next) && ta[next].value().queued == q)
            &&& (prev != NONE && next != NONE ==> prev != next)
            &&& tb.dom() == ta.dom()
            &&& forall|u: usize| u != t && u != prev && u != next && #[trigger] tb.contains_key(u) ==> tb[u] == ta[u]
            &&& tb[t].value() == (ThreadRecord { queued: NONE, wait_prev: NONE, wait_next: NONE, ..ta[t].value() })
            &&& (prev != NONE ==> tb[prev].value() == (ThreadRecord { wait_next: next, ..ta[prev].value() }))
            &&& (next != NONE ==> tb[next].value() == (ThreadRecord { wait_prev: prev, ..ta[next].value() }))
            &&& qb.dom() == qa.dom()
            &&& forall|x: usize| x != q && #[trigger] qb.contains_key(x) ==> qb[x] == qa[x]
            &&& qb[q].value() == (QueueRecord {
                head: if prev == NONE { next } else { r0.head },
                tail: if next == NONE { prev } else { r0.tail },
                waiters: Ghost(r0.waiters@.remove(idx)),
                word: if prev == NONE && next == NONE { r0.word & !WAITER_BIT } else { r0.word },
                ..r0
            })
        }),
    ensures
        waits_wf(qb, tb),
{
    reveal(waits_wf);
    let q = ta[t].value().queued;
    let r0 = qa[q].value();
    let s0 = r0.waiters@;
    let s1 = s0.remove(idx);
    let prev = ta[t].value().wait_prev;
    let next = ta[t].value().wait_next;
    assert(wait_queue_wf(qb[q].value(), tb, q)) by {
        assert(s1.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < j < s1.len() implies s1[i] != s1[j] by {
                let oi = if i < idx { i } else { i + 1 };
                let oj = if j < idx { j } else { j + 1 };
                assert(0 <= oi < oj < s0.len());
                assert(s0[oi] != s0[oj]);
            }
        }
        assert forall|j: int| 0 <= j < s1.len() implies #[trigger] waiter_linked(s1, tb, q, j) by {
            let m = if j < idx { j } else { j + 1 };
            assert(waiter_linked(s0, ta, q, m));
            assert(s1[j] == s0[m]);
            assert(s0[m] != t);
            if idx > 0 && j == idx - 1 {
                assert(m == idx - 1);
                assert(s0[m] == prev);
            } else if idx + 1 < s0.len() && j == idx {
                assert(m == idx + 1);
                assert(s0[m] == next);
            } else {
                if prev != NONE {
                    assert(m != idx - 1);
                    assert(s0[m] != prev);
                }
                if next != NONE {
                    assert(m != idx + 1);
                    assert(s0[m] != next);
                }
            }
        }
    }
    assert forall|x: usize| #[trigger] qb.contains_key(x) implies wait_queue_wf(qb[x].value(), tb, x) by {
        if x != q {
            let sx = qb[x].value().waiters@;
            assert forall|j: int| 0 <= j < sx.len() implies #[trigger] waiter_linked(sx, tb, x, j) by {
                assert(waiter_linked(sx, ta, x, j));
                let u = sx[j];
                assert(ta[u].value().queued == x);
                assert(u != t && u != prev && u != next);
            }
        }
    }
    assert forall|u: usize| #[trigger] tb.contains_key(u) && tb[u].value().queued != NONE implies {
        &&& qb.contains_key(tb[u].value().queued)
        &&& qb[tb[u].value().queued].value().waiters@.contains(u)
    } by {
        let qu = tb[u].value().queued;
        assert(ta[u].value().queued == qu);
        if qu == q {
            let k = choose|k: int| 0 <= k < s0.len() && s0[k] == u;
            if k < idx {
                assert(s1[k] == u);
            } else {
                assert(k > idx);
                assert(s1[k - 1] == u);
            }
        }
    }
    assert forall|u: usize| #[trigger] tb.contains_key(u) && tb[u].value().state is Blocked implies {
        &&& tb[u].value().queued == tb[u].value().state->Blocked_object
        &&& qb.contains_key(tb[u].value().queued)
        &&& qb[tb[u].value().queued].value().waiters@.contains(u)
    } by {
        assert(u != t);
        assert(ta[u].value().state is Blocked);
    }
}

/// Appending thread `t` (currently `queued == NONE` and not `Blocked`) at the tail of `e`'s queue
/// while setting `t`'s state to `Blocked { object: e }` keeps `waits_wf` across every queue and thread.
pub proof fn lemma_waits_appended(
    qa: Map<usize, PointsTo<QueueRecord>>,
    qb: Map<usize, PointsTo<QueueRecord>>,
    ta: Map<usize, PointsTo<ThreadRecord>>,
    tb: Map<usize, PointsTo<ThreadRecord>>,
    e: usize,
    t: usize,
    notify: bool,
)
    requires
        waits_wf(qa, ta),
        qa.contains_key(e),
        ta.contains_key(t),
        ta[t].value().queued == NONE,
        !(ta[t].value().state is Blocked),
        forall|u: usize| #[trigger] ta.contains_key(u) ==> u != NONE,
        ({
            let r0 = qa[e].value();
            let tail = r0.tail;
            &&& tail != NONE ==> tb.contains_key(tail)
                && tb[tail].value() == (ThreadRecord { wait_next: t, ..ta[tail].value() })
            &&& tb.dom() == ta.dom()
            &&& forall|u: usize| u != t && u != tail && #[trigger] tb.contains_key(u) ==> tb[u] == ta[u]
            &&& tb[t].value() == (ThreadRecord {
                state: ThreadState::Blocked { object: e },
                frame: tb[t].value().frame,
                saved: tb[t].value().saved,
                save: tb[t].value().save,
                queued: e,
                wait_prev: tail,
                wait_next: NONE,
                ..ta[t].value()
            })
            &&& qb.dom() == qa.dom()
            &&& forall|x: usize| x != e && #[trigger] qb.contains_key(x) ==> qb[x] == qa[x]
            &&& qb[e].value() == (QueueRecord {
                head: if tail == NONE { t } else { r0.head },
                tail: t,
                waiters: Ghost(r0.waiters@.push(t)),
                word: if notify { r0.word | WAITER_BIT } else { r0.word },
                ..r0
            })
        }),
    ensures
        waits_wf(qb, tb),
{
    reveal(waits_wf);
    lemma_waits_tail(qa, ta, e, t);
    let r0 = qa[e].value();
    let s0 = r0.waiters@;
    let s1 = s0.push(t);
    let tail = r0.tail;
    assert(wait_queue_wf(qb[e].value(), tb, e)) by {
        assert(s1.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < j < s1.len() implies s1[i] != s1[j] by {
                if j == s0.len() {
                    assert(s0[i] != t);
                }
            }
        }
        assert forall|j: int| 0 <= j < s1.len() implies #[trigger] waiter_linked(s1, tb, e, j) by {
            if j == s0.len() {
                assert(s1[j] == t);
                if j > 0 {
                    assert(s1[j - 1] == s0[s0.len() - 1]);
                    assert(s1[j - 1] == tail);
                }
            } else {
                assert(waiter_linked(s0, ta, e, j));
                assert(s1[j] == s0[j]);
                assert(s0[j] != t);
                if j + 1 < s0.len() {
                    assert(s0[j] != tail);
                }
            }
        }
    }
    assert forall|x: usize| #[trigger] qb.contains_key(x) implies wait_queue_wf(qb[x].value(), tb, x) by {
        if x != e {
            let sx = qb[x].value().waiters@;
            assert forall|j: int| 0 <= j < sx.len() implies #[trigger] waiter_linked(sx, tb, x, j) by {
                assert(waiter_linked(sx, ta, x, j));
                let u = sx[j];
                assert(ta[u].value().queued == x);
                assert(u != t && u != tail);
            }
        }
    }
    assert forall|u: usize| #[trigger] tb.contains_key(u) && tb[u].value().queued != NONE implies {
        &&& qb.contains_key(tb[u].value().queued)
        &&& qb[tb[u].value().queued].value().waiters@.contains(u)
    } by {
        if u == t {
            assert(s1[s0.len() as int] == t);
        } else {
            let qu = tb[u].value().queued;
            assert(ta[u].value().queued == qu);
            if qu == e {
                let k = choose|k: int| 0 <= k < s0.len() && s0[k] == u;
                assert(s1[k] == u);
            }
        }
    }
    assert forall|u: usize| #[trigger] tb.contains_key(u) && tb[u].value().state is Blocked implies {
        &&& tb[u].value().queued == tb[u].value().state->Blocked_object
        &&& qb.contains_key(tb[u].value().queued)
        &&& qb[tb[u].value().queued].value().waiters@.contains(u)
    } by {
        if u == t {
            assert(s1[s0.len() as int] == t);
        } else {
            assert(ta[u].value().state is Blocked);
        }
    }
}

/// Preserves `queues_wf` across updates that only touch wait-queue fields or non-`Runnable` thread
/// records.
#[verifier::spinoff_prover]
proof fn lemma_queues_same_wait(
    queues: &RunQueues,
    a: Map<usize, PointsTo<ThreadRecord>>,
    b: Map<usize, PointsTo<ThreadRecord>>,
)
    requires
        queues_wf(queues, a),
        b.dom() == a.dom(),
        forall|u: usize| #[trigger] b.contains_key(u) ==> {
            &&& b[u].is_init()
            &&& !(a[u].value().state is Runnable) ==> !(b[u].value().state is Runnable)
            &&& a[u].value().state is Runnable ==> {
                &&& b[u].value().state == a[u].value().state
                &&& b[u].value().placement == a[u].value().placement
                &&& b[u].value().process == a[u].value().process
                &&& b[u].value().run_prev == a[u].value().run_prev
                &&& b[u].value().run_next == a[u].value().run_next
            }
        },
    ensures
        queues_wf(queues, b),
{
    reveal(queues_wf);
    assert forall|c: int, p: int| 0 <= c < NUM_CPUS && 0 <= p < NUM_PRIORITIES
        implies #[trigger] single_queue_wf(queues, b, c, p) by {
        assert(single_queue_wf(queues, a, c, p));
    }
}

/// Each endpoint's and notification's holders after node i is renamed n.
pub open spec fn moved_endpoint_holders(holders: IMap<usize, Set<usize>>, i: usize, n: usize) -> IMap<usize, Set<usize>> {
    IMap::new(
        |e: usize| holders.contains_key(e),
        |e: usize| if holders[e].contains(i) { holders[e].remove(i).insert(n) } else { holders[e] },
    )
}

/// The endpoint and notification capabilities of a and b are the same, saying the same.
pub open spec fn same_endpoints(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    &&& forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && queue_kind(tables_b.payload_of(x).kind) ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
    &&& forall|x: usize| #[trigger] tables_a.is_cap(list_a, x) && queue_kind(tables_a.payload_of(x).kind) ==> {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x) == tables_a.payload_of(x)
    }
}

/// The endpoints read nothing of the capabilities but the endpoints'.
pub proof fn lemma_endpoints_same_caps(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    endpoints: &Endpoints,
    blocks: &BlockTable,
)
    requires
        endpoints_wf(list_a, tables_a, endpoints, blocks),
        same_endpoints(list_a, tables_a, list_b, tables_b),
    ensures
        endpoints_wf(list_b, tables_b, endpoints, blocks),
{
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && queue_kind(tables_b.payload_of(n).kind) implies {
        &&& endpoints.records@.contains_key(tables_b.payload_of(n).base)
        &&& endpoints.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == 0
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|e: usize, n: usize| endpoints.records@.contains_key(e) && #[trigger] endpoints.holders@[e].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& queue_kind(tables_b.payload_of(n).kind)
        &&& tables_b.payload_of(n).base == e
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_endpoints_same_pages(list: &Tree, tables: &Tables, endpoints: &Endpoints, a: &BlockTable, b: &BlockTable)
    requires
        b.pages@.len() == a.pages@.len(),
        endpoints_wf(list, tables, endpoints, a),
        b.pages@ == a.pages@,
    ensures
        endpoints_wf(list, tables, endpoints, b),
{
    assert forall|e: usize| #[trigger] endpoints.records@.contains_key(e) implies endpoint_wf(endpoints, b, e) by {
        assert(endpoint_wf(endpoints, a, e));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x) implies endpoints.records@.contains_key((x * PAGE_SZ) as usize) by {
        assert(endpoint_block(a, x));
    }
}

/// A step that changes the count of a block that is no endpoint's leaves every endpoint's block as it
/// was.
pub proof fn lemma_endpoints_refs_changed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    endpoints: &Endpoints,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        b.pages@.len() == a.pages@.len(),
        endpoints_wf(list_a, tables_a, endpoints, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !queue_object(a.pages@[x as int].object),
            _ => true,
        },
        same_endpoints(list_a, tables_a, list_b, tables_b),
    ensures
        endpoints_wf(list_b, tables_b, endpoints, b),
{
    lemma_endpoints_same_caps(list_a, tables_a, list_b, tables_b, endpoints, a);
    assert forall|e: usize| #[trigger] endpoints.records@.contains_key(e) implies endpoint_wf(endpoints, b, e) by {
        assert(endpoint_wf(endpoints, a, e));
        let x = BlockRef::Small(e / PAGE_SZ);
        assert(block_typed(a, x));
        assert(x != br);
        assert(block_refs(b, x) == block_refs(a, x));
        assert(block_dead(b, x) == block_dead(a, x));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x) implies endpoints.records@.contains_key((x * PAGE_SZ) as usize) by {
        assert(endpoint_block(a, x));
    }
}

/// The endpoints after a free small block is typed as something that is no endpoint: no endpoint lay
/// in it, and an endpoint block outside it was one before.
pub proof fn lemma_endpoints_small_typed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    endpoints: &Endpoints,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        b.pages@.len() == a.pages@.len(),
        endpoints_wf(list_a, tables_a, endpoints, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| a.tracks(i) && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
        forall|k: int| 0 <= k < size ==> !queue_object((#[trigger] b.pages@[base + k]).object),
        same_endpoints(list_a, tables_a, list_b, tables_b),
    ensures
        endpoints_wf(list_b, tables_b, endpoints, b),
{
    lemma_endpoints_same_caps(list_a, tables_a, list_b, tables_b, endpoints, a);
    assert forall|e: usize| #[trigger] endpoints.records@.contains_key(e) implies endpoint_wf(endpoints, b, e) by {
        assert(endpoint_wf(endpoints, a, e));
        let x = (e / PAGE_SZ) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && queue_kind(tables_b.payload_of(n).kind) implies
        b.pages@[(tables_b.payload_of(n).base / PAGE_SZ) as int].object == queue_object_of(tables_b.payload_of(n).kind) by {
        assert(tables_a.is_cap(list_a, n));
        let e = tables_a.payload_of(n).base;
        assert(endpoint_wf(endpoints, a, e));
        let x = (e / PAGE_SZ) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x) implies endpoints.records@.contains_key((x * PAGE_SZ) as usize) by {
        if base <= x < base + size {
            assert(!queue_object(b.pages@[base + (x - base)].object));
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(endpoint_block(a, x));
    }
}

/// No endpoint lies in a block of another kind: an endpoint's page is its own block's base.
pub proof fn lemma_endpoints_outside_block(list: &Tree, tables: &Tables, endpoints: &Endpoints, blocks: &BlockTable, base: usize)
    requires
        endpoints_wf(list, tables, endpoints, blocks),
        blocks.wf(),
        blocks.tracks(base as int),
        blocks.pages@[base as int].kind is Base,
        !queue_object(blocks.pages@[base as int].object),
    ensures
        forall|e: usize| #[trigger] endpoints.records@.contains_key(e) ==> !blocks.in_block(base as int, (e / PAGE_SZ) as int),
{
    assert forall|e: usize| #[trigger] endpoints.records@.contains_key(e) implies !blocks.in_block(base as int, (e / PAGE_SZ) as int) by {
        assert(endpoint_wf(endpoints, blocks, e));
        let x = (e / PAGE_SZ) as int;
        if blocks.in_block(base as int, x) && x != base {
            blocks.lemma_member_of(base as int, x);
        }
    }
}

/// The endpoints after a small block that is no endpoint's frees.
pub proof fn lemma_endpoints_small_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    endpoints: &Endpoints,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        b.pages@.len() == a.pages@.len(),
        endpoints_wf(list_a, tables_a, endpoints, a),
        a.wf(),
        a.tracks(base as int),
        a.pages@[base as int].kind is Base,
        !queue_object(a.pages@[base as int].object),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_endpoints(list_a, tables_a, list_b, tables_b),
    ensures
        endpoints_wf(list_b, tables_b, endpoints, b),
{
    lemma_endpoints_outside_block(list_a, tables_a, endpoints, a, base);
    lemma_endpoints_same_caps(list_a, tables_a, list_b, tables_b, endpoints, a);
    assert forall|e: usize| #[trigger] endpoints.records@.contains_key(e) implies endpoint_wf(endpoints, b, e) by {
        assert(endpoint_wf(endpoints, a, e));
        assert(!a.in_block(base as int, (e / PAGE_SZ) as int));
        assert(b.pages@[(e / PAGE_SZ) as int] == a.pages@[(e / PAGE_SZ) as int]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x) implies endpoints.records@.contains_key((x * PAGE_SZ) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(endpoint_block(a, x));
    }
}

/// The endpoints after the block of the endpoint or notification at page `base` frees, at zero
/// references, its record going with it. No capability names it, since its holders are as many as its
/// references, and every other endpoint lies outside its block.
pub proof fn lemma_endpoints_own_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    ea: &Endpoints,
    eb: &Endpoints,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        b.pages@.len() == a.pages@.len(),
        endpoints_wf(list_a, tables_a, ea, a),
        a.wf(),
        a.tracks(base as int),
        endpoint_block(a, base),
        a.pages@[base as int].refs == 0,
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        eb.records@ == ea.records@.remove((base * PAGE_SZ) as usize),
        eb.holders == ea.holders,
        same_endpoints(list_a, tables_a, list_b, tables_b),
    ensures
        endpoints_wf(list_b, tables_b, eb, b),
{
    let e0 = (base * PAGE_SZ) as usize;
    lemma_endpoints_same_caps(list_a, tables_a, list_b, tables_b, ea, a);
    assert(ea.records@.contains_key(e0));
    assert(endpoint_wf(ea, a, e0));
    lemma_fundamental_div_mod(e0 as int, PAGE_SZ as int);
    assert(e0 / PAGE_SZ == base);
    assert(ea.holders@[e0].len() == 0);
    ea.holders@[e0].lemma_len0_is_empty();
    assert forall|e: usize| #[trigger] eb.records@.contains_key(e) implies endpoint_wf(eb, b, e) by {
        assert(ea.records@.contains_key(e) && e != e0);
        assert(endpoint_wf(ea, a, e));
        lemma_endpoint_pages_distinct(e, e0);
        let x = (e / PAGE_SZ) as int;
        if a.in_block(base as int, x) && x != base {
            a.lemma_member_of(base as int, x);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x) implies eb.records@.contains_key((x * PAGE_SZ) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(endpoint_block(a, x));
        assert(x != base);
        assert(ea.records@.contains_key((x * PAGE_SZ) as usize));
        assert((x * PAGE_SZ) as usize != e0);
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && queue_kind(tables_b.payload_of(n).kind) implies {
        &&& eb.records@.contains_key(tables_b.payload_of(n).base)
        &&& eb.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == 0
    } by {
        assert(ea.holders@[tables_b.payload_of(n).base].contains(n));
    }
    assert forall|e: usize, n: usize| eb.records@.contains_key(e) && #[trigger] eb.holders@[e].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& queue_kind(tables_b.payload_of(n).kind)
        &&& tables_b.payload_of(n).base == e
    } by {
        assert(ea.records@.contains_key(e));
    }
}

impl CapKernel {
    /// An endpoint or notification capability names one, whose block holds its reference, lies in no
    /// typed region and so is read as the small block at its base.
    pub proof fn lemma_endpoint_cap(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            queue_kind(self.payload_of(n).kind),
        ensures
            self.endpoints.records@.contains_key(self.payload_of(n).base),
            self.endpoints.holders@[self.payload_of(n).base].contains(n),
            self.payload_of(n).base % PAGE_SZ == 0,
            self.blocks.tracks_addr(self.payload_of(n).base),
            self.payload_of(n).order == 0,
            queue_object(self.blocks.pages@[(self.payload_of(n).base / PAGE_SZ) as int].object),
            self.blocks.pages@[(self.payload_of(n).base / PAGE_SZ) as int].object == queue_object_of(self.payload_of(n).kind),
            block_typed(&self.blocks, BlockRef::Small(self.payload_of(n).base / PAGE_SZ)),
            block_refs(&self.blocks, BlockRef::Small(self.payload_of(n).base / PAGE_SZ)) > 0,
            block_ref(&self.blocks, self.payload_of(n).base / PAGE_SZ) == BlockRef::Small(self.payload_of(n).base / PAGE_SZ),
    {
        let e = self.payload_of(n).base;
        assert(self.tables.is_cap(&self.list, n));
        assert(endpoint_wf(&self.endpoints, &self.blocks, e));
        if self.endpoints.holders@[e].len() == 0 {
            self.endpoints.holders@[e].lemma_len0_is_empty();
        }
        self.blocks.lemma_not_free_uncovered((e / PAGE_SZ) as int);
    }

    /// The endpoints after endpoint or notification capability n, the only capability that changed,
    /// joins the object at e with one more reference on its block.
    pub proof fn lemma_endpoints_holder_added(pre: Self, post: Self, n: usize, e: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            !pre.is_cap(n),
            post.is_cap(n),
            queue_kind(post.payload_of(n).kind),
            post.payload_of(n).base == e,
            post.payload_of(n).order == 0,
            pre.endpoints.records@.contains_key(e),
            pre.blocks.pages@[(e / PAGE_SZ) as int].object == queue_object_of(post.payload_of(n).kind),
            block_refs(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) < usize::MAX,
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(e / PAGE_SZ),
                (block_refs(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) + 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(e / PAGE_SZ)),
            ),
            post.endpoints.records == pre.endpoints.records,
            post.endpoints.holders@ == pre.endpoints.holders@.insert(e, pre.endpoints.holders@[e].insert(n)),
        ensures
            endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks),
    {
        let ha = pre.endpoints.holders@;
        let hb = post.endpoints.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(e / PAGE_SZ);
        assert(endpoint_wf(&pre.endpoints, a, e));
        assert(!ha[e].contains(n));
        vstd::set::lemma_set_insert_len(ha[e], n);
        assert forall|u: usize| #[trigger] post.endpoints.records@.contains_key(u)
            implies endpoint_wf(&post.endpoints, b, u) by {
            assert(endpoint_wf(&pre.endpoints, a, u));
            if u != e {
                lemma_endpoint_pages_distinct(u, e);
                let x = BlockRef::Small(u / PAGE_SZ);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x)
            implies post.endpoints.records@.contains_key((x * PAGE_SZ) as usize) by {
            assert(endpoint_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && queue_kind(post.tables.payload_of(x).kind) implies {
            &&& post.endpoints.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == 0
        } by {
            if x != n {
                assert(pre.tables.is_cap(&pre.list, x));
            }
        }
        assert forall|u: usize, x: usize| post.endpoints.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& queue_kind(post.tables.payload_of(x).kind)
            &&& post.tables.payload_of(x).base == u
        } by {
            if !(u == e && x == n) {
                assert(ha[u].contains(x));
                assert(pre.tables.is_cap(&pre.list, x));
                assert(x != n);
            }
        }
    }

    /// The endpoints after endpoint or notification capability n, the only capability that changed,
    /// leaves the object at e, taking its reference on the block with it.
    pub proof fn lemma_endpoints_holder_dropped(pre: Self, post: Self, n: usize, e: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            pre.is_cap(n),
            queue_kind(pre.payload_of(n).kind),
            pre.payload_of(n).base == e,
            !post.is_cap(n),
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(e / PAGE_SZ),
                (block_refs(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) - 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) || block_refs(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) == 1,
            ),
            post.endpoints.records == pre.endpoints.records,
            post.endpoints.holders@ == pre.endpoints.holders@.insert(e, pre.endpoints.holders@[e].remove(n)),
        ensures
            endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks),
    {
        let ha = pre.endpoints.holders@;
        let hb = post.endpoints.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(e / PAGE_SZ);
        pre.lemma_endpoint_cap(n);
        assert(endpoint_wf(&pre.endpoints, a, e));
        assert(ha[e].contains(n));
        vstd::set::lemma_set_remove_len(ha[e], n);
        assert forall|u: usize| #[trigger] post.endpoints.records@.contains_key(u)
            implies endpoint_wf(&post.endpoints, b, u) by {
            assert(endpoint_wf(&pre.endpoints, a, u));
            if u != e {
                lemma_endpoint_pages_distinct(u, e);
                let x = BlockRef::Small(u / PAGE_SZ);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x)
            implies post.endpoints.records@.contains_key((x * PAGE_SZ) as usize) by {
            assert(endpoint_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && queue_kind(post.tables.payload_of(x).kind) implies {
            &&& post.endpoints.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == 0
        } by {
            assert(x != n);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|u: usize, x: usize| post.endpoints.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& queue_kind(post.tables.payload_of(x).kind)
            &&& post.tables.payload_of(x).base == u
        } by {
            assert(ha[u].contains(x));
            assert(pre.tables.is_cap(&pre.list, x));
            assert(x != n);
        }
    }

    /// What an endpoint's or a notification's retype does to the block table: the free page at `page`
    /// is typed as the object at `base`, the list gains no page, and no frame's holder changed.
    proof fn lemma_endpoint_blocks(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            same_mapping_nodes(&pre.list, &post.list),
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.blocks.wf(),
            base / PAGE_SZ == page,
            page * PAGE_SZ == base,
            pre.blocks.tracks(page as int),
            !pre.blocks.covered(page as int),
            pre.blocks.pages@[page as int].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && i != page ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[page as int].kind is Base,
            queue_object(post.blocks.pages@[page as int].object),
            post.blocks.pages@[page as int].order == 0,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            queue_kind(post.payload_of(child).kind),
        ensures
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            zeroing_typed(&post.zeroing, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!pre.is_cap(child));
        assert(a.member_bases_wf());
        assert forall|k: int| 0 <= k < 1 implies #[trigger] a.pages@[page + k].kind is Free by {
            assert(page + k == page);
        }
        assert forall|i: int| a.tracks(i) && !(page <= i < page + 1) implies #[trigger] b.pages@[i] == a.pages@[i] by {}
        assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] a.pages@[page + k].kind is Free by {
            assert(page + k == page);
        }
        assert forall|i: int| a.tracks(i) && !(page <= i < page + order_pages(0)) implies #[trigger] b.pages@[i] == a.pages@[i] by {}
        lemma_list_pages_used_small_typed(&pre.list, a, b, page, 1);
        lemma_list_pages_used_subset(&pre.list, &post.list, b);
        lemma_holders_small_typed(&pre.list, &pre.tables, a, b, &pre.zeroing, pre.holders@, page, 0);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, b, &pre.zeroing, pre.holders@);
        assert forall|br: BlockRef| #[trigger] pre.holders@.contains_key(br) implies block_typed(a, br) by {}
        lemma_objects_small_typed(&pre.tables, &post.tables, a, b, pre.holders@, page, 1);
        lemma_leaf_blocks_small_typed(&pre.list, &pre.tables, a, b, pre.holders@, page, 1);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            lemma_leaf_page(l);
            assert(page_of(l) == l);
            assert(pre.list.valid(l));
            assert(l != child);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, b));
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, b);
        lemma_table_pages_small_typed(&pre.list, &pre.table_pages, a, b, page, 1);
        assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x)
            implies pre.table_pages.maps@.contains_key((x * PAGE_SZ) as usize) by {
            if x == page {
                assert(queue_object(b.pages@[page as int].object));
            }
        }
        assert(table_pages_wf(&pre.list, &pre.table_pages, b));
        assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) implies {
            &&& post.list.nodes@[t as int].live == pre.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind == pre.list.nodes@[t as int].kind
        } by {
            pre.lemma_table_page_valid(t);
            assert(t != child);
        }
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, b);
    }

    /// The endpoints after an endpoint's or a notification's retype at base: the new one has its record
    /// and holds its one capability, and every other lay outside the page and keeps its holders.
    proof fn lemma_endpoints_endpoint_added(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            Self::space_step(pre, post, child),
            base % PAGE_SZ == 0,
            base / PAGE_SZ == page,
            page * PAGE_SZ == base,
            pre.blocks.tracks(page as int),
            pre.blocks.pages@[page as int].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && i != page ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            queue_object(post.blocks.pages@[page as int].object),
            post.blocks.pages@[page as int].object == queue_object_of(post.payload_of(child).kind),
            post.blocks.pages@[page as int].order == 0,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            post.endpoints.records@ == pre.endpoints.records@.insert(base, post.endpoints.records@[base]),
            post.endpoints.records@[base].addr() == base,
            post.endpoints.records@[base].is_init(),
            post.endpoints.records@[base].value().word == 0,
            post.endpoints.records@[base].value().waiters@.len() == 0,
            post.endpoints.holders@ == pre.endpoints.holders@.insert(base, set![child]),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            queue_kind(post.payload_of(child).kind),
            post.payload_of(child).base == base,
            post.payload_of(child).order == 0,
        ensures
            endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks),
            !pre.endpoints.records@.contains_key(base),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let ea = &pre.endpoints;
        let eb = &post.endpoints;
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!ea.records@.contains_key(base)) by {
            if ea.records@.contains_key(base) {
                assert(endpoint_wf(ea, a, base));
            }
        }
        assert(!pre.is_cap(child));
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), child);
        assert(set![child].len() == 1);
        assert forall|e: usize| #[trigger] eb.records@.contains_key(e) implies endpoint_wf(eb, b, e) by {
            if e == base {
                assert(eb.holders@[base] == set![child]);
                lemma_zero_word_wf(eb.records@[base].value(), b.pages@[page as int].object);
            } else {
                assert(ea.records@.contains_key(e));
                assert(endpoint_wf(ea, a, e));
                lemma_endpoint_pages_distinct(e, base);
                assert(b.pages@[(e / PAGE_SZ) as int] == a.pages@[(e / PAGE_SZ) as int]);
                assert(eb.records@[e] == ea.records@[e]);
                assert(eb.holders@[e] == ea.holders@[e]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] endpoint_block(b, x) implies eb.records@.contains_key((x * PAGE_SZ) as usize) by {
            if x == page {
                assert((x * PAGE_SZ) as usize == base);
            } else {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(endpoint_block(a, x));
            }
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && queue_kind(post.tables.payload_of(n).kind) implies {
            &&& eb.records@.contains_key(post.tables.payload_of(n).base)
            &&& eb.holders@[post.tables.payload_of(n).base].contains(n)
            &&& post.tables.payload_of(n).order == 0
        } by {
            if n == child {
                assert(eb.holders@[base].contains(child));
            } else {
                assert(pre.tables.is_cap(&pre.list, n));
                let e = pre.tables.payload_of(n).base;
                assert(ea.records@.contains_key(e));
                assert(e != base);
                assert(eb.holders@[e] == ea.holders@[e]);
            }
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && queue_kind(post.tables.payload_of(n).kind) implies
            b.pages@[(post.tables.payload_of(n).base / PAGE_SZ) as int].object == queue_object_of(post.tables.payload_of(n).kind) by {
            if n != child {
                assert(pre.tables.is_cap(&pre.list, n));
                let e = pre.tables.payload_of(n).base;
                assert(endpoint_wf(ea, a, e));
                lemma_endpoint_pages_distinct(e, base);
                assert(b.pages@[(e / PAGE_SZ) as int] == a.pages@[(e / PAGE_SZ) as int]);
            }
        }
        assert forall|e: usize, n: usize| eb.records@.contains_key(e) && #[trigger] eb.holders@[e].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& queue_kind(post.tables.payload_of(n).kind)
            &&& post.tables.payload_of(n).base == e
        } by {
            if e == base {
                assert(n == child);
            } else {
                assert(ea.records@.contains_key(e));
                assert(ea.holders@[e].contains(n));
                assert(pre.tables.is_cap(&pre.list, n));
                assert(n != child);
            }
        }
    }

    /// The view of an endpoint's or a notification's retype: one child under the untyped, naming the
    /// new object, which no table root is, so it holds nothing.
    proof fn lemma_endpoint_view(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize, kind: CapKind)
        requires
            !bound_threads(&pre.list, &pre.tables).dom().contains(base),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            blocked_on(&post.threads) == blocked_on(&pre.threads),
            post.frames@ == pre.frames@,
            Self::adds_cap(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(&pre.list, root, from),
            post.devices == pre.devices,
            pre.tables.has_slot(&pre.list, root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            post.payload_of(pre.tables.node_of(root, to)) == queue_of(kind, base),
            block_within(base, 0, pre.payload_of(pre.tables.node_of(root, from))),
            !pre.tables.roots@.contains_key(base),
            Self::same_tree(pre, post),
        ensures
            post.view().holds(root, pre.tables.node_of(root, to)),
            adds_object(
                pre.view(),
                post.view(),
                root,
                pre.tables.node_of(root, from),
                pre.tables.node_of(root, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
                base,
            ),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let (a, b) = (pre.view(), post.view());
        Self::lemma_places_node_view(pre, post, root, from, root, to);
        let pp = pre.payload_of(parent);
        lemma2_to64();
        assert(block_bytes(0) == PAGE_SZ);
        assert(block_bytes(pp.order) == a.pages[parent] * PAGE_SZ);
        assert(a.covers(parent, base)) by {
            assert(a.names.contains_key(parent));
            assert(a.pages.contains_key(parent));
            assert(a.names[parent] == pp.base);
            assert(block_within(base, 0, pp));
            assert(base % PAGE_SZ == 0);
            assert(base + PAGE_SZ <= pp.base + a.pages[parent] * PAGE_SZ);
            assert(a.names[parent] <= base < a.names[parent] + a.pages[parent] * PAGE_SZ);
        }
        assert forall|x: NodeId| !#[trigger] b.held.contains((base, x)) by {
            if b.held.contains((base, x)) {
                assert(post.tables.owner@.contains_key(page_of(x)));
                pre.tables.lemma_leaf(&pre.list, page_of(x));
                assert(pre.tables.owner@[page_of(x)].0 == base);
            }
        }
        assert(b.names[child] == base);
    }

    /// What an endpoint's or a notification's retype of the free page at `base`, under the untyped at
    /// index `from` of the table at `root`, with its capability at the empty index `to`, made of `pre`:
    /// the page is a live object of that kind with one reference, its record says it is live with no
    /// thread waiting and nothing signalled, the root holds its one capability, and the retype
    /// discharges the reach lemma.
    pub open spec fn queue_retyped(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize, kind: CapKind) -> bool {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let page = (base / PAGE_SZ) as int;
        &&& pre.view().holds_right(root, parent, Right::Retype)
        &&& post.blocks.pages@[page].kind is Base
        &&& post.blocks.pages@[page].object == queue_object_of(kind)
        &&& post.blocks.pages@[page].order == 0
        &&& post.blocks.pages@[page].refs == 1
        &&& !post.blocks.pages@[page].dead
        &&& forall|i: int| pre.blocks.tracks(i) && i != page ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i]
        &&& post.endpoints.records@.contains_key(base)
        &&& post.endpoints.records@[base].value() == fresh_record()
        &&& post.view().holds(root, child)
        &&& post.payload_of(child) == queue_of(kind, base)
        &&& post.list.is_child(parent, child)
        &&& post.list.parent@ == pre.list.parent@.insert(child, parent)
        &&& post.list.nodes@[child as int].depth == pre.list.nodes@[parent as int].depth + 1
        &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != child
            ==> post.list.nodes@[i].live == pre.list.nodes@[i].live
        &&& Self::retype_keeps(pre, post, child, page, 0, None)
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, pages: pow2(0), into: None })
    }

    /// What an endpoint's or a notification's retype leaves as it was.
    pub open spec fn queue_retype_keeps(pre: Self, post: Self) -> bool {
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
        &&& Self::same_tree(pre, post)
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.targeted == pre.targeted
        &&& post.core_tags == pre.core_tags
        &&& post.tlb_dirty == pre.tlb_dirty
        &&& post.cores == pre.cores
        &&& post.iommus == pre.iommus
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.processes == pre.processes
        &&& post.mappings == pre.mappings
    }

    /// Retypes the free page at `base` as an endpoint, under the untyped at index `from` of the table at
    /// `root`, with its capability at the empty index `to`: a record that says it is live, with no
    /// thread waiting. All of these come from user space, and a refusal changes nothing.
    pub fn retype_endpoint(&mut self, root: usize, from: usize, to: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(steps).count <= old(steps).count + RETYPE_ENDPOINT_STEPS,
            final(self).wf(),
            Self::queue_retype_keeps(*old(self), *final(self)),
            ret == old(self).can_retype_block(root, from, to, base, 0),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::queue_retyped(*old(self), *final(self), root, from, to, base, CapKind::Endpoint),
    {
        self.retype_queue(root, from, to, base, CapKind::Endpoint, Tracked(steps))
    }

    /// Retypes the free page at `base` as a notification, under the untyped at index `from` of the table
    /// at `root`, with its capability at the empty index `to`, carrying badge 0: a record that says it
    /// is live, with no thread waiting and a word of 0. All of these come from user space, and a
    /// refusal changes nothing.
    pub fn retype_notification(&mut self, root: usize, from: usize, to: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(steps).count <= old(steps).count + RETYPE_NOTIFICATION_STEPS,
            final(self).wf(),
            Self::queue_retype_keeps(*old(self), *final(self)),
            ret == old(self).can_retype_block(root, from, to, base, 0),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::queue_retyped(*old(self), *final(self), root, from, to, base, CapKind::Notification),
    {
        self.retype_queue(root, from, to, base, CapKind::Notification, Tracked(steps))
    }

    /// Retypes the free page at `base` as an object of `kind`, an endpoint or a notification, as
    /// retype_endpoint and retype_notification say.
    fn retype_queue(&mut self, root: usize, from: usize, to: usize, base: usize, kind: CapKind, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
            queue_kind(kind),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(steps).count <= old(steps).count + 2 * SMALL_PAGES_MAX,
            final(self).wf(),
            Self::queue_retype_keeps(*old(self), *final(self)),
            ret == old(self).can_retype_block(root, from, to, base, 0),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::queue_retyped(*old(self), *final(self), root, from, to, base, kind),
    {
        // try_type proves the block counts; this body only carries them.
        hide(BlockTable::counts_wf);
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, 0) {
            Some(found) => found,
            None => { return false; },
        };
        proof {
            // The parent is an untyped capability and the new block lies in its block.
            assert(pre.can_retype(root, from, to, base, 0));
            assert(parent == pre.tables.node_of(root, from));
            assert(pre.payload_of(parent).kind is Untyped);
            assert(block_within(base, 0, pre.payload_of(parent)));
        }
        if !self.blocks.page_tracked(base / PAGE_SZ) {
            return false;
        }
        let page = base / PAGE_SZ;
        proof {
            lemma2_to64();
            assert(base % PAGE_SZ == 0);
            assert(page * PAGE_SZ == base);
        }
        let (object, payload) = match kind {
            CapKind::Endpoint => (
                ObjectType::Endpoint,
                Payload { kind: CapKind::Endpoint, order: 0, rights: ENDPOINT_RIGHTS, base, badge: 0, priority: 0 },
            ),
            _ => (
                ObjectType::Notification,
                Payload { kind: CapKind::Notification, order: 0, rights: NOTIFICATION_RIGHTS, base, badge: 0, priority: 0 },
            ),
        };
        assert(object == queue_object_of(kind));
        assert(payload == queue_of(kind, base));
        let Tracked(perms) = match self.blocks.try_type(page, 0, object, Tracked(&mut *steps)) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked mut first;
        proof {
            assert(0usize < order_pages(0));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * PAGE_SZ);
            assert((page + 0usize) as usize == page);
            first = perms.tracked_remove(page);
            // The page's permission is ours, so no table root lies there.
            if pre.tables.roots@.contains_key(base) {
                lemma_thread_block_layouts();
                first.is_distinct(self.tables.roots.borrow().tracked_borrow(base));
                pre.tables.lemma_root(base);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(parent);
            pre.lemma_slot_bound(child);
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
            pre.list.lemma_seq_fits();
        }
        let tracked mut record = page_into_queue_record(first);
        PPtr::<QueueRecord>::from_usize(base).put(Tracked(&mut record), QueueRecord { dead: false, head: NONE, tail: NONE, waiters: Ghost(Seq::empty()), receiving: false, word: 0 });
        proof {
            self.endpoints.records.borrow_mut().tracked_insert(base, record);
        }
        let ghost mid = self.list;
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            self.tables.lemma_wf_same_pages(&mid, &self.list);
        }
        self.tables.set_payload(&self.list, root, to, payload);
        self.endpoints.holders = Ghost(pre.endpoints.holders@.insert(base, set![child]));
        proof {
            let post = *self;
            assert(mid == pre.list);
            assert(forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != child
                ==> post.list.nodes@[i].live == pre.list.nodes@[i].live);
            assert forall|x: usize| #[trigger] pre.list.valid(x) && x != child implies {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            } by {
                pre.list.lemma_valid_bound(x);
            }
            assert(Self::space_step(pre, post, child));
            assert(post.payload_of(child) == queue_of(kind, base));
            assert(payload_wf(post.payload_of(child)));
            assert(post.is_cap(child));
            assert(ENDPOINT_RIGHTS & 128 == 0) by (compute_only);
            assert(NOTIFICATION_RIGHTS & 128 == 0) by (compute_only);
            Self::lemma_space_caps_wf(pre, post, child);
            Self::lemma_tlb_same(pre, post);
            assert(list_grown(pre.list, mid));
            assert(post.payload_of(child).base == base && post.payload_of(child).order == 0);
            assert(block_within(post.payload_of(child).base, post.payload_of(child).order, pre.payload_of(parent)));
            assert(pre.payload_of(parent).kind is Untyped);
            Self::lemma_space_nodes(pre, post, mid, parent, child);
            Self::lemma_table_nodes_frame(pre, post, child, child);
            Self::lemma_space_nodes_frame(pre, post, child, child);
            lemma_mapping_nodes_grown(pre.list, mid, post.list, child, child);
            Self::lemma_endpoint_blocks(pre, post, base, page, child);
            assert forall|k: int| 0 <= k < 1 implies #[trigger] pre.blocks.pages@[page + k].kind is Free by {
                assert(page + k == page);
            }
            assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 1)
                implies #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i] by {}
            assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Space implies {
                &&& pre.is_cap(x)
                &&& pre.payload_of(x) == post.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] post.blocks.pages@[page + k]).object is Space) by {
                assert(page + k == page);
            }
            lemma_spaces_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] post.blocks.pages@[page + k]).object is Thread) by {
                assert(page + k == page);
            }
            lemma_threads_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] post.blocks.pages@[page + k]).object is Process) by {
                assert(page + k == page);
            }
            assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Process implies {
                &&& pre.tables.is_cap(&pre.list, x)
                &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Process implies {
                &&& post.tables.is_cap(&post.list, x)
                &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            lemma_processes_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] post.blocks.pages@[page + k]).object is Reply) by {
                assert(page + k == page);
            }
            lemma_replies_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, page, 1);
            assert(post.endpoints.records@ == pre.endpoints.records@.insert(base, post.endpoints.records@[base]));
            Self::lemma_endpoints_endpoint_added(pre, post, base, page, child);
            assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
                implies post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n] by {
                pre.lemma_mapping_node(n);
            }
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
                &&& post.is_cap(x)
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
                pre.lemma_slot_bound(x);
            }
            Self::lemma_mappings_grown(pre, post, page, 0);
            assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
                implies pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x) by {
                assert(x != child);
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            Self::lemma_devices_same_caps(pre, post);
            lemma_binding_nodes_grown(pre.list, mid, post.list, child, child);
            lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
            assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
            Self::lemma_binding_parents_same_caps(pre, post);
            assert(base != NONE) by {
                assert(base % PAGE_SZ == 0);
                assert(NONE % PAGE_SZ == PAGE_MASK);
            }
            assert(same_queue(post.endpoints.records@[base].value(), fresh_record()));
            lemma_waits_framed(pre.endpoints.records@, post.endpoints.records@, pre.threads.records@, post.threads.records@);
            assert(post.wf());
            Self::lemma_bound_threads_same(pre, post);
            assert(right_bit(Right::Retype) == 8);
            assert(!(pre.blocks.pages@[(base / PAGE_SZ) as int].kind is Base)) by {
                assert(pre.blocks.pages@[(base / PAGE_SZ) as int + 0].kind is Free);
            }
            pre.lemma_unbound_unless_thread(base);
            Self::lemma_endpoint_view(pre, post, root, from, to, base, kind);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            pre.lemma_retype_covers(root, from, base, 0);
            lemma_adds_object_discharges_retype(pre.view(), post.view(), root, parent, child, live, base, pow2(0));
            assert forall|r: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, r, i) implies {
                &&& post.tables.has_slot(&post.list, r, i)
                &&& post.tables.node_of(r, i) == pre.tables.node_of(r, i)
                &&& pre.tables.node_of(r, i) != child && !pre.list.nodes@[pre.tables.node_of(r, i) as int].live
                    ==> !post.list.nodes@[pre.tables.node_of(r, i) as int].live
            } by {
                pre.lemma_slot(r, i);
                let n = pre.tables.node_of(r, i);
                pre.lemma_slot_bound(n);
                let leaf = pre.tables.leaf(r, index_entry(i));
                assert(leaf == page_of(n));
                assert(leaf != child);
                assert(post.tables.leaf(r, index_entry(i)) == leaf);
                assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
            }
            assert forall|r: usize, e: int| pre.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES
                implies #[trigger] post.tables.leaf(r, e) == pre.tables.leaf(r, e) by {
                assert(post.tables.roots@[r] == pre.tables.roots@[r]);
            }
            assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(0))
                implies #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind by {
                assert(post.blocks.pages@[i] == pre.blocks.pages@[i]);
            }
            assert(Self::retype_keeps(pre, post, child, page as int, 0, None));
        }
        true
    }

    /// Rewriting wait links, queue records and at most core `c`'s current thread, while keeping every
    /// thread's process and placement, keeps `wf`. `ids_wf` is opaque, so the bound
    /// `next_pcid <= PCID_MAX` is stated here for a core whose current thread alone changed; the
    /// TLB, the IOMMU model and the binding parents read those fields and the thread records, so
    /// they are re-established rather than left for congruence on a kernel value that differs.
    #[verifier::spinoff_prover]
    proof fn lemma_queue_edit_wf(pre: Self, post: Self, c: int)
        requires
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            pre.wf(),
            0 <= c < NUM_CPUS,
            post == (CapKernel { endpoints: post.endpoints, threads: post.threads, cores: post.cores, ..pre }),
            post.threads == (Threads { records: post.threads.records, ..pre.threads }),
            post.endpoints == (Endpoints { records: post.endpoints.records, ..pre.endpoints }),
            post.cores.wf(),
            post.cores@.len() == pre.cores@.len(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d],
            post.cores@[c].generation == pre.cores@[c].generation,
            post.cores@[c].next_pcid == pre.cores@[c].next_pcid,
            post.cores@[c].space == pre.cores@[c].space,
            post.cores@[c].acked_epoch == pre.cores@[c].acked_epoch,
            post.threads.records@.dom() == pre.threads.records@.dom(),
            post.endpoints.records@.dom() == pre.endpoints.records@.dom(),
            forall|x: usize| #[trigger] post.threads.records@.contains_key(x)
                ==> thread_wf(&post.list, &post.threads, &post.blocks, x),
            forall|x: usize| #[trigger] post.endpoints.records@.contains_key(x)
                ==> endpoint_wf(&post.endpoints, &post.blocks, x),
            forall|t: usize| #[trigger] pre.threads.records@.contains_key(t) ==> {
                &&& post.threads.records@.contains_key(t)
                &&& post.threads.records@[t].value().process == pre.threads.records@[t].value().process
                &&& post.threads.records@[t].value().placement == pre.threads.records@[t].value().placement
            },
            forall|t: usize| #[trigger] post.threads.records@.contains_key(t) && post.threads.records@[t].value().process is Some
                ==> pre.threads.records@.contains_key(t),
            forall|t: usize| #[trigger] post.threads.records@.contains_key(t) && post.threads.records@[t].value().placement is Some
                ==> pre.threads.records@.contains_key(t),
            waits_wf(post.endpoints.records@, post.threads.records@),
            queues_wf(&post.threads.queues, post.threads.records@),
            current_wf(post.cores@, post.threads.records@),
            placed_running_wf(post.threads.records@),
            bindings_wf(&post.list, &post.threads, &post.processes),
            placements_wf(&post.list, &post.tables, &post.threads),
        ensures
            post.wf(),
    {
        assert(post.list == pre.list);
        assert(post.tables == pre.tables);
        assert(post.blocks == pre.blocks);
        assert(post.spaces == pre.spaces);
        assert(post.processes == pre.processes);
        assert(post.tlb == pre.tlb);
        assert(post.iommus == pre.iommus);
        assert(post.devices == pre.devices);
        assert(post.mapped == pre.mapped);
        assert(post.stale_epoch == pre.stale_epoch);
        assert(post.flush_epoch == pre.flush_epoch);
        assert(post.targeted == pre.targeted);
        assert(post.core_tags == pre.core_tags);
        assert(post.tlb_dirty == pre.tlb_dirty);
        assert(post.frames == pre.frames);
        assert(post.threads.holders == pre.threads.holders);
        assert(post.endpoints.holders == pre.endpoints.holders);
        reveal(ids_wf);
        assert(1 <= (#[trigger] pre.cores@[c]).generation <= ID_GENERATION_MAX);
        assert(1 <= pre.cores@[c].next_pcid <= PCID_MAX);
        assert(pre.cores@[c].next_pcid <= post.cores@[c].next_pcid <= PCID_MAX);
        lemma_ids_core_step(pre.cores@, post.cores@, pre.spaces.loaded@, c);
        assert forall|d: int| 0 <= d < NUM_CPUS implies (#[trigger] post.cores@[d]).space == pre.cores@[d].space by {
            if d != c {
                assert(post.cores@[d] == pre.cores@[d]);
            }
        }
        lemma_registers_kept(
            pre.spaces.registers@,
            pre.cores@,
            post.cores@,
            pre.spaces.loaded@,
            post.spaces.loaded@,
            pre.spaces.kernel_root@,
        );
        assert forall|b: usize| post.blocks.tracks(b as int) && #[trigger] thread_block(&post.blocks, b)
            implies post.threads.records@.contains_key((b * PAGE_SZ) as usize) by {
            assert(thread_block(&pre.blocks, b));
            assert(pre.threads.records@.contains_key((b * PAGE_SZ) as usize));
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && post.tables.payload_of(n).kind is Thread
            implies {
                &&& post.threads.records@.contains_key(post.tables.payload_of(n).base)
                &&& post.threads.holders@[post.tables.payload_of(n).base].contains(n)
                &&& post.tables.payload_of(n).order == THREAD_ORDER
            } by {
            assert(pre.tables.is_cap(&pre.list, n));
            let base = pre.tables.payload_of(n).base;
            assert(pre.threads.records@.contains_key(base));
            assert(pre.threads.holders@[base].contains(n));
        }
        assert forall|t: usize, n: usize|
            post.threads.records@.contains_key(t) && #[trigger] post.threads.holders@[t].contains(n)
            implies {
                &&& post.tables.is_cap(&post.list, n)
                &&& post.tables.payload_of(n).kind is Thread
                &&& post.tables.payload_of(n).base == t
            } by {
            assert(pre.threads.records@.contains_key(t));
            assert(pre.threads.holders@[t].contains(n));
        }
        assert(threads_wf(&post.list, &post.tables, &post.threads, &post.blocks));
        assert forall|b: usize| post.blocks.tracks(b as int) && #[trigger] endpoint_block(&post.blocks, b)
            implies post.endpoints.records@.contains_key((b * PAGE_SZ) as usize) by {
            assert(endpoint_block(&pre.blocks, b));
            assert(pre.endpoints.records@.contains_key((b * PAGE_SZ) as usize));
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && queue_kind(post.tables.payload_of(n).kind)
            implies {
                &&& post.endpoints.records@.contains_key(post.tables.payload_of(n).base)
                &&& post.endpoints.holders@[post.tables.payload_of(n).base].contains(n)
                &&& post.tables.payload_of(n).order == 0
                &&& post.blocks.pages@[(post.tables.payload_of(n).base / PAGE_SZ) as int].object
                    == queue_object_of(post.tables.payload_of(n).kind)
            } by {
            assert(pre.tables.is_cap(&pre.list, n));
            let base = pre.tables.payload_of(n).base;
            assert(pre.endpoints.records@.contains_key(base));
            assert(pre.endpoints.holders@[base].contains(n));
        }
        assert forall|e: usize, n: usize|
            post.endpoints.records@.contains_key(e) && #[trigger] post.endpoints.holders@[e].contains(n)
            implies {
                &&& post.tables.is_cap(&post.list, n)
                &&& queue_kind(post.tables.payload_of(n).kind)
                &&& post.tables.payload_of(n).base == e
            } by {
            assert(pre.endpoints.records@.contains_key(e));
            assert(pre.endpoints.holders@[e].contains(n));
        }
        assert(endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks));
        assert forall|t: usize|
            t < NODE_SPACE && (#[trigger] post.list.nodes@[t as int]).live && post.list.nodes@[t as int].kind is Binding
            implies pre.list.nodes@[t as int].live && pre.list.nodes@[t as int].kind is Binding by {
            assert(post.list.nodes@[t as int] == pre.list.nodes@[t as int]);
        }
        assert forall|x: usize|
            x < NODE_SPACE && pre.list.nodes@[x as int].live && #[trigger] pre.list.parent@.contains_key(x)
            implies post.list.parent@.contains_key(x) && post.list.parent@[x] == pre.list.parent@[x] by {
            assert(post.list.parent@ == pre.list.parent@);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Process
            implies {
                &&& post.tables.is_cap(&post.list, x)
                &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
            } by {
            assert(pre.is_cap(x));
        }
        lemma_binding_parents_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert(pre.iommus_wf());
        assert(post.iommus.commands.wf(post.iommus.present@));
        Self::lemma_iommus_same(pre, post);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) == pre.acked(d) by {
            if d != c {
                assert(post.cores@[d] == pre.cores@[d]);
            } else {
                assert(post.cores@[c].acked_epoch == pre.cores@[c].acked_epoch);
            }
        }
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) <= post.flush_epoch by {
            assert(pre.acked(d) <= pre.flush_epoch);
        }
        assert forall|d: int, p: usize| 0 <= d < NUM_CPUS && #[trigger] post.tlb@.tags(d).contains(p)
            implies p < post.cores@[d].next_pcid by {
            assert(pre.tlb@.tags(d).contains(p));
            assert(p < pre.cores@[d].next_pcid);
            if d != c {
                assert(post.cores@[d] == pre.cores@[d]);
            }
        }
        assert forall|d: int| 0 <= d < NUM_CPUS && !crate::arch::flush_target(post.tlb_dirty, d)
            implies #[trigger] post.tlb@[d] == Set::<TlbEntry>::empty() by {
            assert(!crate::arch::flush_target(pre.tlb_dirty, d));
            assert(pre.tlb@[d] == Set::<TlbEntry>::empty());
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e)
            implies post.space_may_hold(d, e.space) by {
            assert(pre.tlb@[d].contains(e));
            assert(pre.space_may_hold(d, e.space));
        }
        assert forall|d: int, e: TlbEntry|
            0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(d), e.page) by {
            assert(pre.tlb@[d].contains(e));
        }
        assert(post.tlb_wf());
        Self::lemma_targets_same(pre, post);
        assert(!pre.threads.records@.contains_key(pre.devices.page));
        assert(post.devices.page == pre.devices.page);
        assert(!post.threads.records@.contains_key(post.devices.page));
    }

    /// What unlinking thread `t` does. `NONE` in `queued` leaves the kernel as it was. Otherwise only
    /// that queue's links, head, tail and waiter bit change, and `t`'s place in it. The view does not
    /// read those links, so it stays the same, and the kernel stays well formed.
    #[verifier::opaque]
    pub open spec fn unlinked_waiter(pre: Self, post: Self, t: usize) -> bool
        recommends
            pre.wf(),
            pre.threads.records@.contains_key(t),
    {
        let r0 = pre.threads.records@[t].value();
        let q = r0.queued;
        let prev = r0.wait_prev;
        let next = r0.wait_next;
        &&& post.blocks.pages@.len() == pre.blocks.pages@.len()
        &&& post.wf()
        &&& post.view() == pre.view()
        &&& q == NONE ==> post == pre
        &&& q != NONE ==> {
            &&& post == (CapKernel { endpoints: post.endpoints, threads: post.threads, ..pre })
            &&& post.threads == (Threads { records: post.threads.records, ..pre.threads })
            &&& post.threads.records@.dom() == pre.threads.records@.dom()
            &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
            &&& post.threads.records@[t].is_init()
            &&& post.threads.records@[t].value() == (ThreadRecord {
                queued: NONE,
                wait_prev: NONE,
                wait_next: NONE,
                ..r0
            })
            &&& forall|u: usize| u != t && #[trigger] post.threads.records@.contains_key(u) ==> ({
                let ur = pre.threads.records@[u].value();
                let vr = post.threads.records@[u].value();
                &&& post.threads.records@[u].addr() == pre.threads.records@[u].addr()
                &&& post.threads.records@[u].is_init()
                &&& vr == (ThreadRecord { wait_prev: vr.wait_prev, wait_next: vr.wait_next, ..ur })
            })
            &&& post.endpoints.holders == pre.endpoints.holders
            &&& post.endpoints.records@.dom() == pre.endpoints.records@.dom()
            &&& forall|x: usize| x != q && #[trigger] post.endpoints.records@.contains_key(x)
                ==> post.endpoints.records@[x] == pre.endpoints.records@[x]
            &&& pre.endpoints.records@.contains_key(q)
            &&& post.endpoints.records@[q].addr() == pre.endpoints.records@[q].addr()
            &&& post.endpoints.records@[q].is_init()
            &&& post.endpoints.records@[q].value() == (QueueRecord {
                head: if prev == NONE { next } else { pre.endpoints.records@[q].value().head },
                tail: if next == NONE { prev } else { pre.endpoints.records@[q].value().tail },
                waiters: post.endpoints.records@[q].value().waiters,
                word: if prev == NONE && next == NONE {
                    pre.endpoints.records@[q].value().word & !WAITER_BIT
                } else {
                    pre.endpoints.records@[q].value().word
                },
                ..pre.endpoints.records@[q].value()
            })
        }
    }

    /// Unlinking a waiter rewrites queue links only, so the kernel stays well formed and the view,
    /// which does not read those links, stays the same.
    #[verifier::spinoff_prover]
    proof fn lemma_unlink_waiter_wf(pre: Self, post: Self, t: usize, idx: int)
        requires
            pre.wf(),
            pre.threads.records@.contains_key(t),
            pre.threads.records@[t].value().queued != NONE,
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post == (CapKernel { endpoints: post.endpoints, threads: post.threads, cores: post.cores, ..pre }),
            post.threads == (Threads { records: post.threads.records, ..pre.threads }),
            post.endpoints == (Endpoints { records: post.endpoints.records, ..pre.endpoints }),
            post.cores == pre.cores,
            post.threads.records@.dom() == pre.threads.records@.dom(),
            post.endpoints.records@.dom() == pre.endpoints.records@.dom(),
            !(pre.threads.records@[t].value().state is Blocked),
            forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) ==> u != NONE,
            ({
                let r0 = pre.threads.records@[t].value();
                let q = r0.queued;
                let prev = r0.wait_prev;
                let next = r0.wait_next;
                &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
                &&& post.threads.records@[t].is_init()
                &&& post.threads.records@[t].value() == (ThreadRecord {
                    queued: NONE,
                    wait_prev: NONE,
                    wait_next: NONE,
                    ..r0
                })
                &&& forall|u: usize| u != t && u != prev && u != next && #[trigger] post.threads.records@.contains_key(u)
                    ==> post.threads.records@[u] == pre.threads.records@[u]
                &&& (prev != NONE ==> post.threads.records@[prev].value() == (ThreadRecord { wait_next: next, ..pre.threads.records@[prev].value() }))
                &&& (next != NONE ==> post.threads.records@[next].value() == (ThreadRecord { wait_prev: prev, ..pre.threads.records@[next].value() }))
                &&& 0 <= idx < pre.endpoints.records@[q].value().waiters@.len()
                &&& pre.endpoints.records@[q].value().waiters@[idx] == t
                &&& (idx == 0 <==> prev == NONE)
                &&& (idx > 0 ==> {
                    &&& prev == pre.endpoints.records@[q].value().waiters@[idx - 1]
                    &&& prev != NONE
                    &&& prev != t
                    &&& pre.threads.records@.contains_key(prev)
                    &&& pre.threads.records@[prev].value().queued == q
                })
                &&& (idx == pre.endpoints.records@[q].value().waiters@.len() - 1 <==> next == NONE)
                &&& (idx < pre.endpoints.records@[q].value().waiters@.len() - 1 ==> {
                    &&& next == pre.endpoints.records@[q].value().waiters@[idx + 1]
                    &&& next != NONE
                    &&& next != t
                    &&& pre.threads.records@.contains_key(next)
                    &&& pre.threads.records@[next].value().queued == q
                })
                &&& (prev != NONE && next != NONE ==> prev != next)
                &&& post.endpoints.records@[q].value().waiters@ == pre.endpoints.records@[q].value().waiters@.remove(idx)
                &&& forall|u: usize| u != t && #[trigger] post.threads.records@.contains_key(u) ==> ({
                    let ur = pre.threads.records@[u].value();
                    let vr = post.threads.records@[u].value();
                    &&& post.threads.records@[u].addr() == pre.threads.records@[u].addr()
                    &&& post.threads.records@[u].is_init()
                    &&& vr == (ThreadRecord { wait_prev: vr.wait_prev, wait_next: vr.wait_next, ..ur })
                })
                &&& post.endpoints.holders == pre.endpoints.holders
                &&& pre.endpoints.records@.contains_key(q)
                &&& post.endpoints.records@[q].addr() == pre.endpoints.records@[q].addr()
                &&& post.endpoints.records@[q].is_init()
                &&& forall|x: usize| x != q && #[trigger] post.endpoints.records@.contains_key(x)
                    ==> post.endpoints.records@[x] == pre.endpoints.records@[x]
                &&& post.endpoints.records@[q].value() == (QueueRecord {
                    head: if prev == NONE { next } else { pre.endpoints.records@[q].value().head },
                    tail: if next == NONE { prev } else { pre.endpoints.records@[q].value().tail },
                    waiters: post.endpoints.records@[q].value().waiters,
                    word: if prev == NONE && next == NONE {
                        pre.endpoints.records@[q].value().word & !WAITER_BIT
                    } else {
                        pre.endpoints.records@[q].value().word
                    },
                    ..pre.endpoints.records@[q].value()
                })
            }),
        ensures
            Self::unlinked_waiter(pre, post, t),
    {
        let r0 = pre.threads.records@[t].value();
        let q = r0.queued;
        let prev = r0.wait_prev;
        let next = r0.wait_next;
        let ghost w0 = pre.endpoints.records@[q].value().word;
        assert(0u64 & !WAITER_BIT == 0u64) by (bit_vector)
            requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
        assert((w0 & !WAITER_BIT) & WAITER_BIT == 0u64) by (bit_vector)
            requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
        lemma_waits_unlinked(pre.endpoints.records@, post.endpoints.records@, pre.threads.records@, post.threads.records@, t, idx);
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u) implies {
            &&& post.threads.records@[u].is_init()
            &&& !(pre.threads.records@[u].value().state is Runnable) ==> !(post.threads.records@[u].value().state is Runnable)
            &&& pre.threads.records@[u].value().state is Runnable ==> {
                &&& post.threads.records@[u].value().state == pre.threads.records@[u].value().state
                &&& post.threads.records@[u].value().placement == pre.threads.records@[u].value().placement
                &&& post.threads.records@[u].value().process == pre.threads.records@[u].value().process
                &&& post.threads.records@[u].value().run_prev == pre.threads.records@[u].value().run_prev
                &&& post.threads.records@[u].value().run_next == pre.threads.records@[u].value().run_next
            }
        } by {
            if u != t && u != prev && u != next {
                assert(post.threads.records@[u] == pre.threads.records@[u]);
            }
        }
        lemma_queues_same_wait(&pre.threads.queues, pre.threads.records@, post.threads.records@);
        assert forall|x: usize| #[trigger] post.endpoints.records@.contains_key(x)
            implies endpoint_wf(&post.endpoints, &post.blocks, x) by {
            assert(endpoint_wf(&pre.endpoints, &pre.blocks, x));
        }
        assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x)
            implies thread_wf(&post.list, &post.threads, &post.blocks, x) by {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, x));
            if x == t || x == prev || x == next {
                assert(post.threads.records@[x].value().frame == pre.threads.records@[x].value().frame);
                assert(post.threads.records@[x].value().saved == pre.threads.records@[x].value().saved);
                assert(post.threads.records@[x].value().save == pre.threads.records@[x].value().save);
            }
        }
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u) implies {
            &&& post.threads.records@[u].value().frame == pre.threads.records@[u].value().frame
            &&& post.threads.records@[u].value().state == pre.threads.records@[u].value().state
            &&& post.threads.records@[u].value().pending_stop == pre.threads.records@[u].value().pending_stop
            &&& post.threads.records@[u].value().process == pre.threads.records@[u].value().process
            &&& post.threads.records@[u].value().placement == pre.threads.records@[u].value().placement
        } by {
            if u != t && u != prev && u != next {
                assert(post.threads.records@[u] == pre.threads.records@[u]);
            }
        }
        lemma_placed_running_same(pre.threads.records@, post.threads.records@);
        assert forall|d: int| 0 <= d < NUM_CPUS implies {
            &&& #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread
            &&& post.cores@[d].space == pre.cores@[d].space
        } by {
            assert(post.cores@[d] == pre.cores@[d]);
        }
        lemma_current_same(pre.cores@, post.cores@, pre.threads.records@, post.threads.records@);
        lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
        lemma_placements_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert(post.cores.wf());
        assert(post.cores@.len() == pre.cores@.len());
        assert forall|u: usize|
            #[trigger] post.threads.records@.contains_key(u) && post.threads.records@[u].value().process is Some
            implies pre.threads.records@.contains_key(u) by {}
        assert forall|u: usize|
            #[trigger] post.threads.records@.contains_key(u) && post.threads.records@[u].value().placement is Some
            implies pre.threads.records@.contains_key(u) by {}
        Self::lemma_queue_edit_wf(pre, post, 0);
        assert forall|o: ObjectId| #[trigger] saved_registers(&post.threads).contains_key(o)
            implies saved_registers(&post.threads)[o] == saved_registers(&pre.threads)[o] by {
            assert(post.threads.records@.contains_key(o));
            assert(post.threads.records@[o].value().frame == pre.threads.records@[o].value().frame);
        }
        assert(saved_registers(&post.threads) =~= saved_registers(&pre.threads));
        assert forall|o: usize| #[trigger] waits_on(&post.threads, o) == waits_on(&pre.threads, o) by {
            if post.threads.records@.contains_key(o) {
                assert(post.threads.records@[o].value().state == pre.threads.records@[o].value().state);
            }
        }
        lemma_blocked_on_same(&pre.threads, &post.threads);
        assert(post.view() =~= pre.view());
        assert(Self::unlinked_waiter(pre, post, t)) by {
            reveal(CapKernel::unlinked_waiter);
        }
    }

    pub(crate) fn unlink_waiter(&mut self, t: usize)
        requires
            old(self).wf(),
            old(self).threads.records@.contains_key(t),
            !(old(self).threads.records@[t].value().state is Blocked),
        ensures
            Self::unlinked_waiter(*old(self), *final(self), t),
    {
        let ghost pre = *self;
        proof {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
        }
        let ptr_t = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ);
        let record = *ptr_t.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let q = record.queued;
        if q == NONE {
            proof {
                assert(Self::unlinked_waiter(pre, *self, t)) by {
                    reveal(CapKernel::unlinked_waiter);
                }
            }
            return;
        }
        let prev = record.wait_prev;
        let next = record.wait_next;
        let ghost idx: int;
        proof {
            assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies u != NONE by {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, u));
            }
            idx = lemma_waits_neighbors(pre.endpoints.records@, pre.threads.records@, t);
            assert(endpoint_wf(&pre.endpoints, &pre.blocks, q));
            if prev != NONE {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, prev));
            }
            if next != NONE {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, next));
            }
        }
        let tracked mut perm_t = self.threads.records.borrow_mut().tracked_remove(t);
        let mut r_t = ptr_t.take(Tracked(&mut perm_t));
        r_t.queued = NONE;
        r_t.wait_prev = NONE;
        r_t.wait_next = NONE;
        ptr_t.put(Tracked(&mut perm_t), r_t);
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm_t);
        }
        if prev != NONE {
            let ptr_prev = PPtr::<ThreadRecord>::from_usize(prev + THREAD_RECORD_PAGE * PAGE_SZ);
            let tracked mut perm_prev = self.threads.records.borrow_mut().tracked_remove(prev);
            let mut r_prev = ptr_prev.take(Tracked(&mut perm_prev));
            r_prev.wait_next = next;
            ptr_prev.put(Tracked(&mut perm_prev), r_prev);
            proof {
                self.threads.records.borrow_mut().tracked_insert(prev, perm_prev);
            }
        }
        if next != NONE {
            let ptr_next = PPtr::<ThreadRecord>::from_usize(next + THREAD_RECORD_PAGE * PAGE_SZ);
            let tracked mut perm_next = self.threads.records.borrow_mut().tracked_remove(next);
            let mut r_next = ptr_next.take(Tracked(&mut perm_next));
            r_next.wait_prev = prev;
            ptr_next.put(Tracked(&mut perm_next), r_next);
            proof {
                self.threads.records.borrow_mut().tracked_insert(next, perm_next);
            }
        }
        let ptr_q = PPtr::<QueueRecord>::from_usize(q);
        let tracked mut perm_q = self.endpoints.records.borrow_mut().tracked_remove(q);
        let r0 = ptr_q.take(Tracked(&mut perm_q));
        let new_head = if prev == NONE { next } else { r0.head };
        let new_tail = if next == NONE { prev } else { r0.tail };
        let new_word = if prev == NONE && next == NONE { r0.word & !WAITER_BIT } else { r0.word };
        let ghost new_waiters = r0.waiters@.remove(idx);
        ptr_q.put(Tracked(&mut perm_q), QueueRecord {
            head: new_head,
            tail: new_tail,
            waiters: Ghost(new_waiters),
            word: new_word,
            ..r0
        });
        proof {
            self.endpoints.records.borrow_mut().tracked_insert(q, perm_q);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert(post.endpoints.records@.dom() =~= pre.endpoints.records@.dom());
            assert(post.cores == pre.cores);
            assert(post.threads == (Threads { records: post.threads.records, ..pre.threads }));
            assert(post.endpoints == (Endpoints { records: post.endpoints.records, ..pre.endpoints }));
            assert(post == (CapKernel { endpoints: post.endpoints, threads: post.threads, cores: post.cores, ..pre }));
            assert(post.blocks.pages@.len() == pre.blocks.pages@.len());
            let r0t = pre.threads.records@[t].value();
            assert(prev == r0t.wait_prev);
            assert(next == r0t.wait_next);
            assert(post.threads.records@[t].addr() == pre.threads.records@[t].addr());
            assert(post.threads.records@[t].is_init());
            assert(post.threads.records@[t].value() == (ThreadRecord {
                queued: NONE,
                wait_prev: NONE,
                wait_next: NONE,
                ..r0t
            }));
            assert forall|u: usize| u != t && u != prev && u != next && #[trigger] post.threads.records@.contains_key(u)
                implies post.threads.records@[u] == pre.threads.records@[u] by {}
            if prev != NONE {
                assert(post.threads.records@[prev].value() == (ThreadRecord { wait_next: next, ..pre.threads.records@[prev].value() }));
            }
            if next != NONE {
                assert(post.threads.records@[next].value() == (ThreadRecord { wait_prev: prev, ..pre.threads.records@[next].value() }));
            }
            assert(0 <= idx < pre.endpoints.records@[q].value().waiters@.len());
            assert(pre.endpoints.records@[q].value().waiters@[idx] == t);
            assert(post.endpoints.records@[q].value().waiters@ == pre.endpoints.records@[q].value().waiters@.remove(idx));
            assert forall|u: usize| u != t && #[trigger] post.threads.records@.contains_key(u) implies ({
                let ur = pre.threads.records@[u].value();
                let vr = post.threads.records@[u].value();
                &&& post.threads.records@[u].addr() == pre.threads.records@[u].addr()
                &&& post.threads.records@[u].is_init()
                &&& vr == (ThreadRecord { wait_prev: vr.wait_prev, wait_next: vr.wait_next, ..ur })
            }) by {
                if u != prev && u != next {
                    assert(post.threads.records@[u] == pre.threads.records@[u]);
                }
            }
            assert(post.endpoints.holders == pre.endpoints.holders);
            assert(pre.endpoints.records@.contains_key(q));
            assert(post.endpoints.records@[q].addr() == pre.endpoints.records@[q].addr());
            assert(post.endpoints.records@[q].is_init());
            assert forall|x: usize| x != q && #[trigger] post.endpoints.records@.contains_key(x)
                implies post.endpoints.records@[x] == pre.endpoints.records@[x] by {}
            assert(post.endpoints.records@[q].value() == (QueueRecord {
                head: if prev == NONE { next } else { pre.endpoints.records@[q].value().head },
                tail: if next == NONE { prev } else { pre.endpoints.records@[q].value().tail },
                waiters: post.endpoints.records@[q].value().waiters,
                word: if prev == NONE && next == NONE {
                    pre.endpoints.records@[q].value().word & !WAITER_BIT
                } else {
                    pre.endpoints.records@[q].value().word
                },
                ..pre.endpoints.records@[q].value()
            }));
            Self::lemma_unlink_waiter_wf(pre, post, t, idx);
        }
    }

    /// Saves core `c`'s current thread `t`'s partial `frame`, sets `t` to `Blocked { object: e }`,
    /// appends `t` at the tail of `e`'s queue (updating any old tail's `wait_next`), sets
    /// `WAITER_BIT` on `e`'s word if `notify`, and clears core `c`'s `current_thread` to `None`.
    pub(crate) fn append_waiter(&mut self, c: usize, e: usize, t: usize, frame: Registers, notify: bool)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).cores@[c as int].current_thread == Some(t),
            old(self).endpoints.records@.contains_key(e),
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().state == (ThreadState::Running { core: c }),
            old(self).threads.records@[t].value().placement is Some,
            old(self).threads.records@[t].value().process is Some,
            old(self).threads.records@[t].value().queued == NONE,
            !old(self).threads.records@[t].value().pending_stop,
            notify == (old(self).blocks.pages@[(e / PAGE_SZ) as int].object is Notification),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            *final(self) == (CapKernel {
                endpoints: final(self).endpoints,
                threads: final(self).threads,
                cores: final(self).cores,
                ..*old(self)
            }),
            final(self).cores@.len() == old(self).cores@.len(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).cores@[d] == old(self).cores@[d],
            final(self).cores@[c as int] == (CoreState { current_thread: None, ..old(self).cores@[c as int] }),
            final(self).threads == (Threads { records: final(self).threads.records, ..old(self).threads }),
            final(self).threads.records@.dom() == old(self).threads.records@.dom(),
            final(self).threads.records@[t].addr() == old(self).threads.records@[t].addr(),
            final(self).threads.records@[t].is_init(),
            final(self).threads.records@[t].value() == (ThreadRecord {
                state: ThreadState::Blocked { object: e },
                frame: partial_frame(frame),
                saved: FrameKind::Partial,
                save: Ghost(entry_frame_save(frame, FrameKind::Partial)),
                queued: e,
                wait_prev: old(self).endpoints.records@[e].value().tail,
                wait_next: NONE,
                ..old(self).threads.records@[t].value()
            }),
            old(self).endpoints.records@[e].value().tail != NONE ==> {
                let tl = old(self).endpoints.records@[e].value().tail;
                &&& final(self).threads.records@[tl].addr() == old(self).threads.records@[tl].addr()
                &&& final(self).threads.records@[tl].is_init()
                &&& final(self).threads.records@[tl].value() == (ThreadRecord {
                    wait_next: t,
                    ..old(self).threads.records@[tl].value()
                })
            },
            forall|u: usize| u != t && u != old(self).endpoints.records@[e].value().tail && #[trigger] final(self).threads.records@.contains_key(u)
                ==> final(self).threads.records@[u] == old(self).threads.records@[u],
            final(self).endpoints.holders == old(self).endpoints.holders,
            final(self).endpoints.records@.dom() == old(self).endpoints.records@.dom(),
            forall|x: usize| x != e && #[trigger] final(self).endpoints.records@.contains_key(x)
                ==> final(self).endpoints.records@[x] == old(self).endpoints.records@[x],
            final(self).endpoints.records@[e].addr() == old(self).endpoints.records@[e].addr(),
            final(self).endpoints.records@[e].is_init(),
            final(self).endpoints.records@[e].value() == (QueueRecord {
                head: if old(self).endpoints.records@[e].value().tail == NONE {
                    t
                } else {
                    old(self).endpoints.records@[e].value().head
                },
                tail: t,
                waiters: Ghost(old(self).endpoints.records@[e].value().waiters@.push(t)),
                word: if notify {
                    old(self).endpoints.records@[e].value().word | WAITER_BIT
                } else {
                    old(self).endpoints.records@[e].value().word
                },
                ..old(self).endpoints.records@[e].value()
            }),
    {
        let ghost pre = *self;
        proof {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
            assert(endpoint_wf(&self.endpoints, &self.blocks, e));
            assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies u != NONE by {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, u));
            }
            lemma_waits_tail(pre.endpoints.records@, pre.threads.records@, e, t);
            let tl = pre.endpoints.records@[e].value().tail;
            if tl != NONE {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, tl));
            }
        }
        let ptr_e = PPtr::<QueueRecord>::from_usize(e);
        let tracked mut perm_e = self.endpoints.records.borrow_mut().tracked_remove(e);
        let r0 = ptr_e.take(Tracked(&mut perm_e));
        let tail = r0.tail;
        let new_head = if tail == NONE { t } else { r0.head };
        let new_word = if notify { r0.word | WAITER_BIT } else { r0.word };
        ptr_e.put(Tracked(&mut perm_e), QueueRecord {
            head: new_head,
            tail: t,
            waiters: Ghost(r0.waiters@.push(t)),
            word: new_word,
            ..r0
        });
        proof {
            self.endpoints.records.borrow_mut().tracked_insert(e, perm_e);
        }
        if tail != NONE {
            let ptr_tail = PPtr::<ThreadRecord>::from_usize(tail + THREAD_RECORD_PAGE * PAGE_SZ);
            let tracked mut perm_tail = self.threads.records.borrow_mut().tracked_remove(tail);
            let mut r_tail = ptr_tail.take(Tracked(&mut perm_tail));
            r_tail.wait_next = t;
            ptr_tail.put(Tracked(&mut perm_tail), r_tail);
            proof {
                self.threads.records.borrow_mut().tracked_insert(tail, perm_tail);
            }
        }
        let partial = partial_frame_of(frame);
        let ptr_t = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ);
        let tracked mut perm_t = self.threads.records.borrow_mut().tracked_remove(t);
        let mut r_t = ptr_t.take(Tracked(&mut perm_t));
        r_t.state = ThreadState::Blocked { object: e };
        r_t.frame = partial;
        r_t.saved = FrameKind::Partial;
        r_t.save = Ghost(entry_frame_save(frame, FrameKind::Partial));
        r_t.queued = e;
        r_t.wait_prev = tail;
        r_t.wait_next = NONE;
        ptr_t.put(Tracked(&mut perm_t), r_t);
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm_t);
        }
        let mut cs = *self.cores.get(c);
        cs.current_thread = None;
        self.cores.set(c, cs);
        proof {
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert(post.endpoints.records@.dom() =~= pre.endpoints.records@.dom());
            lemma_waits_appended(pre.endpoints.records@, post.endpoints.records@, pre.threads.records@, post.threads.records@, e, t, notify);
            lemma_queues_same_wait(&pre.threads.queues, pre.threads.records@, post.threads.records@);
            reveal(frame_save_matches);
            lemma_partial_frame_idempotent(frame);
            let ghost w0 = r0.word;
            assert((w0 | WAITER_BIT) & WAITER_BIT != 0u64) by (bit_vector)
                requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert forall|x: usize| #[trigger] post.endpoints.records@.contains_key(x)
                implies endpoint_wf(&post.endpoints, &post.blocks, x) by {
                assert(endpoint_wf(&pre.endpoints, &pre.blocks, x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x)
                implies thread_wf(&post.list, &post.threads, &post.blocks, x) by {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, x));
            }
            assert(placed_running_wf(post.threads.records@)) by {
                reveal(placed_running_wf);
                assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x)
                    implies thread_placed_running(post.threads.records@[x].value()) by {
                    assert(thread_placed_running(pre.threads.records@[x].value()));
                }
            }
            let ghost old_tail = pre.endpoints.records@[e].value().tail;
            assert(post.cores@ =~= pre.cores@.update(c as int, CoreState { current_thread: None, ..pre.cores@[c as int] }));
            assert(post.cores@[c as int].current_thread is None);
            assert(post.cores@[c as int].space == pre.cores@[c as int].space);
            assert forall|d: int| 0 <= d < NUM_CPUS && d != (c as int) implies #[trigger] post.cores@[d] == pre.cores@[d] by {}
            reveal(current_wf);
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
                &&& !post.threads.records@[x].value().pending_stop ==> runs_in_space(post.cores@, post.threads.records@, d, x)
            } by {
                assert(d != c);
                assert(post.cores@[d] == pre.cores@[d]);
                assert(runs(pre.cores@, d, x));
                assert(x != t);
                if x != old_tail {
                    assert(post.threads.records@[x] == pre.threads.records@[x]);
                } else {
                    assert(post.threads.records@[x].value() == (ThreadRecord { wait_next: t, ..pre.threads.records@[x].value() }));
                }
                assert(pre.threads.records@[x].value().state == (ThreadState::Running { core: d as usize }));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let d = post.threads.records@[x].value().state->Running_core;
                &&& d < NUM_CPUS
                &&& post.cores@[d as int].current_thread == Some(x)
            } by {
                assert(x != t);
                if x != old_tail {
                    assert(post.threads.records@[x] == pre.threads.records@[x]);
                } else {
                    assert(post.threads.records@[x].value() == (ThreadRecord { wait_next: t, ..pre.threads.records@[x].value() }));
                }
                let d = pre.threads.records@[x].value().state->Running_core;
                assert(pre.threads.records@.contains_key(x));
                assert(d < NUM_CPUS);
                assert(pre.cores@[d as int].current_thread == Some(x));
                assert(d != c);
                assert(post.cores@[d as int] == pre.cores@[d as int]);
            }
            assert(!post.threads.records@[t].value().pending_stop);
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(x != t);
                assert(pre.threads.records@.contains_key(x));
                if x != old_tail {
                    assert(post.threads.records@[x] == pre.threads.records@[x]);
                } else {
                    assert(post.threads.records@[x].value() == (ThreadRecord { wait_next: t, ..pre.threads.records@[x].value() }));
                }
                assert(pre.threads.records@[x].value().pending_stop);
                assert(pre.threads.records@[x].value().state is Running);
            }
            assert(current_wf(post.cores@, post.threads.records@));
            lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
            lemma_placements_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
            assert(post.cores@ =~= pre.cores@.update(c as int, CoreState { current_thread: None, ..pre.cores@[c as int] }));
            assert(post.cores@[c as int] == (CoreState { current_thread: None, ..pre.cores@[c as int] }));
            assert(post.cores@[c as int].next_pcid == pre.cores@[c as int].next_pcid);
            assert(post.cores@[c as int].generation == pre.cores@[c as int].generation);
            assert(post.cores@[c as int].space == pre.cores@[c as int].space);
            assert(post.cores@[c as int].acked_epoch == pre.cores@[c as int].acked_epoch);
            assert(post.cores.wf());
            assert(post.threads == (Threads { records: post.threads.records, ..pre.threads }));
            assert(post.endpoints == (Endpoints { records: post.endpoints.records, ..pre.endpoints }));
            assert(post == (CapKernel { endpoints: post.endpoints, threads: post.threads, cores: post.cores, ..pre }));
            assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies {
                &&& post.threads.records@.contains_key(u)
                &&& post.threads.records@[u].value().process == pre.threads.records@[u].value().process
                &&& post.threads.records@[u].value().placement == pre.threads.records@[u].value().placement
            } by {
                if u != t && u != pre.endpoints.records@[e].value().tail {
                    assert(post.threads.records@[u] == pre.threads.records@[u]);
                }
            }
            assert forall|u: usize|
                #[trigger] post.threads.records@.contains_key(u) && post.threads.records@[u].value().process is Some
                implies pre.threads.records@.contains_key(u) by {}
            assert forall|u: usize|
                #[trigger] post.threads.records@.contains_key(u) && post.threads.records@[u].value().placement is Some
                implies pre.threads.records@.contains_key(u) by {}
            Self::lemma_queue_edit_wf(pre, post, c as int);
        }
    }
}

} // verus!
