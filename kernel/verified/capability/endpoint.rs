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
use crate::capability::space::*;
use crate::capability::steps::Steps;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
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
/// exactly its holders, and it is dead at once when they go.
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
}

/// Each endpoint and notification is well formed, an endpoint's or a notification's block is one of
/// these, and the capabilities of kind Endpoint or Notification are exactly the holders.
pub open spec fn endpoints_wf(list: &Tree, tables: &Tables, endpoints: &Endpoints, blocks: &BlockTable) -> bool {
    &&& forall|e: usize| #[trigger] endpoints.records@.contains_key(e) ==> endpoint_wf(endpoints, blocks, e)
    &&& forall|b: usize| blocks.tracks(b as int) && #[trigger] endpoint_block(blocks, b)
        ==> endpoints.records@.contains_key((b * PAGE_SZ) as usize)
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && queue_kind(tables.payload_of(n).kind) ==> {
        &&& endpoints.records@.contains_key(tables.payload_of(n).base)
        &&& endpoints.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == 0
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
            Self::space_step(pre, post, child),
            base % PAGE_SZ == 0,
            base / PAGE_SZ == page,
            page * PAGE_SZ == base,
            pre.blocks.tracks(page as int),
            pre.blocks.pages@[page as int].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && i != page ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            queue_object(post.blocks.pages@[page as int].object),
            post.blocks.pages@[page as int].order == 0,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            post.endpoints.records@ == pre.endpoints.records@.insert(base, post.endpoints.records@[base]),
            post.endpoints.records@[base].addr() == base,
            post.endpoints.records@[base].is_init(),
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
        &&& Self::retype_keeps(pre, post, child, page, 0, None)
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, pages: pow2(0), into: None })
    }

    /// What an endpoint's or a notification's retype leaves as it was.
    pub open spec fn queue_retype_keeps(pre: Self, post: Self) -> bool {
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
        &&& Self::same_tree(pre, post)
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
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
}

} // verus!
