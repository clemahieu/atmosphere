//! Threads as retyped objects. A thread is an order-1 block: a node page, whose nodes are its bindings
//! to its process, its fault endpoint and its placement, then a page holding its record at the start
//! and its extended register state, the XSAVE area, after it. A capability names a thread by its
//! block's base and carries control, and the capabilities naming it hold its block's references. See
//! design/process-holds-capabilities/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
#[cfg(verus_keep_ghost)]
use crate::capability::derive::*;
#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::steps::Steps;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
#[cfg(verus_keep_ghost)]
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::layouts::*;
use crate::pptr::*;
use crate::arch::*;

/// A thread's block is two pages.
pub const THREAD_ORDER: u8 = 1;

/// The page of a thread's block that holds its record and its XSAVE area. Page 0 is its node page.
pub const THREAD_RECORD_PAGE: usize = 1;

/// Where the XSAVE area starts in the record's page: past the record, and 64-byte aligned as XSAVE
/// requires.
pub const XSAVE_OFFSET: usize = 1024;

/// The bytes the XSAVE area has, to the end of the page. CPUID leaf 0xD, sub-leaf 0, reports 2440 for
/// every state component the reference host supports.
pub const XSAVE_BYTES: usize = 3072;

/// A thread capability carries control: it may start, stop and configure the thread.
pub const THREAD_RIGHTS: u32 = 128;

/// What a thread is doing. Only core c moves a thread into or out of Running on c: see
/// design/one-lock-bounded-steps/.
#[derive(Clone, Copy)]
pub enum ThreadState {
    /// Not runnable until started.
    Inactive,
    /// Waiting for core `core` to switch it in.
    Runnable { core: usize },
    /// Core `core`'s current thread.
    Running { core: usize },
    /// Waiting on the object at `object`.
    Blocked { object: usize },
    /// Destroyed; its block waits for its references to go.
    Dead,
}

/// What a thread keeps at the start of its record's page. Its XSAVE area lies after it in the same
/// page, inside the record's permission.
#[derive(Clone, Copy)]
pub struct ThreadRecord {
    pub state: ThreadState,
    /// The registers saved when it last left user mode.
    pub frame: Registers,
    /// Set when it must stop on its core's next kernel entry.
    pub pending_stop: bool,
    /// Set with a pending stop when it is destroyed while Running: the stop makes it Dead rather than
    /// Inactive.
    pub dying: bool,
    /// The process it is bound to: its node page's first node is then a binding under a capability to
    /// that process, holding a reference on the process's block.
    pub process: Option<usize>,
    /// The core it runs on once started. A placement is a binding under a capability to that core,
    /// design/cpu-time-as-capability/; no operation places a thread yet, so it is None.
    pub placement: Option<usize>,
}

/// What a suspend did.
pub enum SuspendStep {
    /// Nothing changed.
    Refused,
    /// The thread is Inactive.
    Suspended,
    /// The thread is Running on another core, which stops it at its next kernel entry. Suspend again
    /// to see it Inactive.
    Again,
}

/// A thread's record when it is typed: inactive, with zeroed registers and no stop pending.
pub open spec fn fresh_thread() -> ThreadRecord {
    ThreadRecord { state: ThreadState::Inactive, frame: zero_registers(), pending_stop: false, dying: false, process: None, placement: None }
}

pub fn new_thread_record() -> (ret: ThreadRecord)
    ensures
        ret == fresh_thread(),
{
    ThreadRecord {
        state: ThreadState::Inactive,
        frame: zero_frame(),
        pending_stop: false,
        dying: false,
        process: None,
        placement: None,
    }
}

/// A thread capability's payload.
pub open spec fn thread_of(base: usize) -> Payload {
    Payload { kind: CapKind::Thread, order: THREAD_ORDER, rights: THREAD_RIGHTS, base, badge: 0, reserved: 0 }
}

/// Each thread's record by its block's address, and the capabilities holding its block.
pub struct Threads {
    pub records: Tracked<Map<usize, PointsTo<ThreadRecord>>>,
    pub holders: Ghost<IMap<usize, Set<usize>>>,
}

impl Threads {
    pub fn new() -> (ret: Self)
        ensures
            ret.records@ == Map::<usize, PointsTo<ThreadRecord>>::empty(),
            ret.holders@ == IMap::<usize, Set<usize>>::empty(),
    {
        Threads { records: Tracked(Map::tracked_empty()), holders: Ghost(IMap::empty()) }
    }
}

/// Core c's current thread is t.
pub open spec fn runs(cores: Seq<CoreState>, c: int, t: usize) -> bool {
    cores[c].current_thread == Some(t)
}

/// Core c's current thread is t exactly when t is Running on c, so no thread is current on two cores
/// and no core's current thread is anything but a thread. A pending stop is on a Running thread, so
/// one its core has acted on cannot stop the thread again once it is started.
#[verifier::opaque]
pub open spec fn current_wf(cores: Seq<CoreState>, records: Map<usize, PointsTo<ThreadRecord>>) -> bool {
    &&& forall|c: int, t: usize| 0 <= c < NUM_CPUS && #[trigger] runs(cores, c, t) ==> {
        &&& records.contains_key(t)
        &&& records[t].value().state == (ThreadState::Running { core: c as usize })
    }
    &&& forall|t: usize| #[trigger] records.contains_key(t) && records[t].value().state is Running ==> {
        let c = records[t].value().state->Running_core;
        &&& c < NUM_CPUS
        &&& cores[c as int].current_thread == Some(t)
    }
    &&& forall|t: usize| #[trigger] records.contains_key(t) && records[t].value().pending_stop ==> records[t].value().state is Running
}

/// Each core runs what it ran and each thread is in the state it was in, with the stop it had pending.
pub proof fn lemma_current_same(pre: Seq<CoreState>, post: Seq<CoreState>, a: Map<usize, PointsTo<ThreadRecord>>, b: Map<usize, PointsTo<ThreadRecord>>)
    requires
        current_wf(pre, a),
        forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] post[c].current_thread == pre[c].current_thread,
        b.dom() == a.dom(),
        forall|t: usize| #[trigger] b.contains_key(t) ==> {
            &&& b[t].value().state == a[t].value().state
            &&& b[t].value().pending_stop == a[t].value().pending_stop
        },
    ensures
        current_wf(post, b),
{
    reveal(current_wf);
    assert forall|c: int, t: usize| 0 <= c < NUM_CPUS && #[trigger] runs(post, c, t) implies {
        &&& b.contains_key(t)
        &&& b[t].value().state == (ThreadState::Running { core: c as usize })
    } by {
        assert(runs(pre, c, t));
    }
    assert forall|t: usize| #[trigger] b.contains_key(t) && b[t].value().state is Running implies {
        let c = b[t].value().state->Running_core;
        &&& c < NUM_CPUS
        &&& post[c as int].current_thread == Some(t)
    } by {
        let c = a[t].value().state->Running_core;
        assert(a.contains_key(t));
        assert(c < NUM_CPUS);
        assert(post[c as int].current_thread == pre[c as int].current_thread);
    }
    assert forall|t: usize| #[trigger] b.contains_key(t) && b[t].value().pending_stop implies b[t].value().state is Running by {
        assert(a.contains_key(t));
    }
}

/// The block at page b holds a thread.
pub open spec fn thread_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& blocks.pages@[b as int].object is Thread
}

/// The thread at t has its record and its node page. Its block's references are exactly its holders,
/// and it is dead at once when they go.
pub open spec fn thread_wf(list: &Tree, threads: &Threads, blocks: &BlockTable, t: usize) -> bool {
    &&& t % 8192 == 0
    &&& blocks.tracks_addr_run(t, 2)
    &&& threads.records@[t].addr() == t + THREAD_RECORD_PAGE * 4096
    &&& threads.records@[t].is_init()
    &&& blocks.pages@[(t / 4096) as int].kind is Base
    &&& blocks.pages@[(t / 4096) as int].object is Thread
    &&& blocks.pages@[(t / 4096) as int].order == 1
    &&& list.pages@.dom().contains(t)
    &&& threads.holders@.contains_key(t)
    &&& threads.holders@[t].finite()
    &&& threads.holders@[t].len() == blocks.pages@[(t / 4096) as int].refs
    &&& blocks.pages@[(t / 4096) as int].refs == 0 ==> blocks.pages@[(t / 4096) as int].dead
}

/// Each thread is well formed, a thread's block is one of these, and the capabilities of kind Thread
/// are exactly the holders.
pub open spec fn threads_wf(list: &Tree, tables: &Tables, threads: &Threads, blocks: &BlockTable) -> bool {
    &&& forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> thread_wf(list, threads, blocks, t)
    &&& forall|b: usize| blocks.tracks(b as int) && #[trigger] thread_block(blocks, b)
        ==> threads.records@.contains_key((b * 4096) as usize)
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Thread ==> {
        &&& threads.records@.contains_key(tables.payload_of(n).base)
        &&& threads.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == THREAD_ORDER
    }
    &&& forall|t: usize, n: usize| threads.records@.contains_key(t) && #[trigger] threads.holders@[t].contains(n) ==> {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Thread
        &&& tables.payload_of(n).base == t
    }
}

/// Thread n's record names a process. Opaque so that the node quantifier of bindings_wf, which fires on
/// every node a proof mentions, does not reach into the thread records and through them the block table.
#[verifier::opaque]
pub open spec fn thread_bound(threads: &Threads, n: usize) -> bool {
    threads.records@.contains_key(n) && threads.records@[n].value().process is Some
}

/// A live binding node is a thread's binding to its process: node 0 of the thread's node page, live
/// exactly while the thread's record names a process, and counted by that process among the bindings
/// holding its block. So unlinking a binding node finds what to undo from the node alone. See
/// design/process-holds-capabilities/.
pub open spec fn bindings_wf(list: &Tree, threads: &Threads, processes: &Processes) -> bool {
    &&& forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Binding
        ==> thread_bound(threads, n)
    &&& forall|t: usize| #[trigger] threads.records@.contains_key(t) && threads.records@[t].value().process is Some ==> {
        let p = threads.records@[t].value().process->Some_0;
        &&& t < NODE_SPACE
        &&& list.nodes@[t as int].live
        &&& list.nodes@[t as int].kind is Binding
        &&& processes.records@.contains_key(p)
        &&& processes.bound@[p].contains(t)
    }
    &&& forall|p: usize, t: usize| processes.records@.contains_key(p) && #[trigger] processes.bound@[p].contains(t)
        ==> threads.records@.contains_key(t) && threads.records@[t].value().process == Some(p)
}

/// Binding node t's parent is a capability to the process t's record names, so the node alone says
/// which process its thread is bound to.
pub open spec fn binding_parent(list: &Tree, tables: &Tables, threads: &Threads, t: usize) -> bool {
    let n = list.parent@[t];
    &&& list.parent@.contains_key(t)
    &&& tables.is_cap(list, n)
    &&& tables.payload_of(n).kind is Process
    &&& threads.records@.contains_key(t)
    &&& threads.records@[t].value().process == Some(tables.payload_of(n).base)
}

/// Every live binding node's parent is a capability to its thread's process. Opaque, as thread_bound
/// is, so that its node quantifier does not chain into the tables in every proof that mentions a node.
/// See design/process-holds-capabilities/.
#[verifier::opaque]
pub open spec fn binding_parents(list: &Tree, tables: &Tables, threads: &Threads) -> bool {
    forall|t: usize| t < NODE_SPACE && (#[trigger] list.nodes@[t as int]).live && list.nodes@[t as int].kind is Binding
        ==> binding_parent(list, tables, threads, t)
}

/// The binding parents after a step that made no binding, kept every live node's parent, every process
/// capability saying the same, and every thread's process.
pub proof fn lemma_binding_parents_kept(la: &Tree, ta: &Tables, tha: &Threads, lb: &Tree, tb: &Tables, thb: &Threads)
    requires
        binding_parents(la, ta, tha),
        forall|t: usize| t < NODE_SPACE && (#[trigger] lb.nodes@[t as int]).live && lb.nodes@[t as int].kind is Binding
            ==> la.nodes@[t as int].live && la.nodes@[t as int].kind is Binding,
        forall|x: usize| x < NODE_SPACE && la.nodes@[x as int].live && #[trigger] la.parent@.contains_key(x)
            ==> lb.parent@.contains_key(x) && lb.parent@[x] == la.parent@[x],
        forall|x: usize| #[trigger] ta.is_cap(la, x) && ta.payload_of(x).kind is Process ==> {
            &&& tb.is_cap(lb, x)
            &&& tb.payload_of(x) == ta.payload_of(x)
        },
        forall|t: usize| #[trigger] tha.records@.contains_key(t) ==> {
            &&& thb.records@.contains_key(t)
            &&& thb.records@[t].value().process == tha.records@[t].value().process
        },
    ensures
        binding_parents(lb, tb, thb),
{
    reveal(binding_parents);
    assert forall|t: usize| t < NODE_SPACE && (#[trigger] lb.nodes@[t as int]).live && lb.nodes@[t as int].kind is Binding
        implies binding_parent(lb, tb, thb, t) by {
        assert(la.nodes@[t as int].live && la.nodes@[t as int].kind is Binding);
        assert(binding_parent(la, ta, tha, t));
        let n = la.parent@[t];
        assert(ta.is_cap(la, n) && ta.payload_of(n).kind is Process);
        assert(tha.records@.contains_key(t));
    }
}

/// The live binding nodes of a are those of b.
pub open spec fn same_bindings(list_a: &Tree, list_b: &Tree) -> bool {
    forall|n: usize| #![trigger list_a.nodes@[n as int]] #![trigger list_b.nodes@[n as int]] n < NODE_SPACE ==>
        (list_b.nodes@[n as int].live && list_b.nodes@[n as int].kind is Binding)
            == (list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Binding)
}

/// The bindings after a step that kept every binding node, every thread's process and every process's
/// bindings, and added only threads bound to nothing and processes with no bindings.
pub proof fn lemma_bindings_kept(list_a: &Tree, list_b: &Tree, ta: &Threads, tb: &Threads, pa: &Processes, pb: &Processes)
    requires
        bindings_wf(list_a, ta, pa),
        same_bindings(list_a, list_b),
        forall|t: usize| #[trigger] ta.records@.contains_key(t) ==> {
            &&& tb.records@.contains_key(t)
            &&& tb.records@[t].value().process == ta.records@[t].value().process
        },
        forall|t: usize| #[trigger] tb.records@.contains_key(t) && tb.records@[t].value().process is Some
            ==> ta.records@.contains_key(t),
        forall|p: usize| #[trigger] pa.records@.contains_key(p) ==> pb.records@.contains_key(p) && pb.bound@[p] == pa.bound@[p],
        forall|p: usize| #[trigger] pb.records@.contains_key(p) && !pa.records@.contains_key(p)
            ==> pb.bound@[p] == Set::<usize>::empty(),
    ensures
        bindings_wf(list_b, tb, pb),
{
    assert forall|n: usize| n < NODE_SPACE && (#[trigger] list_b.nodes@[n as int]).live && list_b.nodes@[n as int].kind is Binding
        implies thread_bound(tb, n) by {
        reveal(thread_bound);
        assert(list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Binding);
        assert(ta.records@.contains_key(n));
    }
    assert forall|t: usize| #[trigger] tb.records@.contains_key(t) && tb.records@[t].value().process is Some implies {
        let p = tb.records@[t].value().process->Some_0;
        &&& t < NODE_SPACE
        &&& list_b.nodes@[t as int].live
        &&& list_b.nodes@[t as int].kind is Binding
        &&& pb.records@.contains_key(p)
        &&& pb.bound@[p].contains(t)
    } by {
        assert(ta.records@.contains_key(t));
        let p = ta.records@[t].value().process->Some_0;
        assert(pa.records@.contains_key(p));
        assert(list_a.nodes@[t as int].live && list_a.nodes@[t as int].kind is Binding);
    }
    assert forall|p: usize, t: usize| pb.records@.contains_key(p) && #[trigger] pb.bound@[p].contains(t)
        implies tb.records@.contains_key(t) && tb.records@[t].value().process == Some(p) by {
        if pa.records@.contains_key(p) {
            assert(pa.bound@[p].contains(t));
            assert(ta.records@.contains_key(t));
        } else {
            assert(pb.bound@[p] == Set::<usize>::empty());
        }
    }
}

/// The bindings after a step that changed no thread's process and no process, and kept every binding
/// node.
pub proof fn lemma_bindings_same(list_a: &Tree, list_b: &Tree, threads: &Threads, processes: &Processes)
    requires
        bindings_wf(list_a, threads, processes),
        same_bindings(list_a, list_b),
    ensures
        bindings_wf(list_b, threads, processes),
{
    lemma_bindings_kept(list_a, list_b, threads, threads, processes, processes);
}

/// The bindings after thread t's binding to p, node t, goes: t names no process and p no longer
/// counts it.
pub proof fn lemma_bindings_unbound(
    list_a: &Tree,
    list_b: &Tree,
    ta: &Threads,
    tb: &Threads,
    pa: &Processes,
    pb: &Processes,
    t: usize,
    p: usize,
)
    requires
        bindings_wf(list_a, ta, pa),
        ta.records@.contains_key(t),
        ta.records@[t].value().process == Some(p),
        !list_b.nodes@[t as int].live,
        forall|x: usize| x < NODE_SPACE && x != t ==> {
            &&& (#[trigger] list_b.nodes@[x as int]).live == list_a.nodes@[x as int].live
            &&& list_b.nodes@[x as int].kind == list_a.nodes@[x as int].kind
        },
        tb.records@.dom() == ta.records@.dom(),
        forall|x: usize| x != t && #[trigger] tb.records@.contains_key(x) ==> tb.records@[x] == ta.records@[x],
        tb.records@[t].value().process is None,
        pb.records == pa.records,
        pb.bound@ == pa.bound@.insert(p, pa.bound@[p].remove(t)),
    ensures
        bindings_wf(list_b, tb, pb),
{
    assert forall|n: usize| n < NODE_SPACE && (#[trigger] list_b.nodes@[n as int]).live && list_b.nodes@[n as int].kind is Binding
        implies thread_bound(tb, n) by {
        reveal(thread_bound);
        assert(n != t);
        assert(list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Binding);
        assert(ta.records@.contains_key(n));
    }
    assert forall|x: usize| #[trigger] tb.records@.contains_key(x) && tb.records@[x].value().process is Some implies {
        let q = tb.records@[x].value().process->Some_0;
        &&& x < NODE_SPACE
        &&& list_b.nodes@[x as int].live
        &&& list_b.nodes@[x as int].kind is Binding
        &&& pb.records@.contains_key(q)
        &&& pb.bound@[q].contains(x)
    } by {
        assert(x != t);
        assert(ta.records@.contains_key(x));
        assert(tb.records@[x] == ta.records@[x]);
        let q = ta.records@[x].value().process->Some_0;
        assert(pa.bound@[q].contains(x));
        assert(list_b.nodes@[x as int].live == list_a.nodes@[x as int].live);
    }
    assert forall|q: usize, x: usize| pb.records@.contains_key(q) && #[trigger] pb.bound@[q].contains(x)
        implies tb.records@.contains_key(x) && tb.records@[x].value().process == Some(q) by {
        assert(pa.bound@[q].contains(x));
        assert(ta.records@.contains_key(x));
        assert(x != t);
        assert(tb.records@[x] == ta.records@[x]);
    }
}

/// The bindings after thread t, bound to nothing, is bound to p by node t.
pub proof fn lemma_bindings_bound(
    list_a: &Tree,
    list_b: &Tree,
    ta: &Threads,
    tb: &Threads,
    pa: &Processes,
    pb: &Processes,
    t: usize,
    p: usize,
)
    requires
        bindings_wf(list_a, ta, pa),
        ta.records@.contains_key(t),
        ta.records@[t].value().process is None,
        t < NODE_SPACE,
        list_b.nodes@[t as int].live,
        list_b.nodes@[t as int].kind is Binding,
        forall|x: usize| x < NODE_SPACE && x != t ==> {
            &&& (#[trigger] list_b.nodes@[x as int]).live == list_a.nodes@[x as int].live
            &&& list_b.nodes@[x as int].kind == list_a.nodes@[x as int].kind
        },
        tb.records@.dom() == ta.records@.dom(),
        forall|x: usize| x != t && #[trigger] tb.records@.contains_key(x) ==> tb.records@[x] == ta.records@[x],
        tb.records@[t].value().process == Some(p),
        pa.records@.contains_key(p),
        pb.records == pa.records,
        pb.bound@ == pa.bound@.insert(p, pa.bound@[p].insert(t)),
    ensures
        bindings_wf(list_b, tb, pb),
{
    assert forall|n: usize| n < NODE_SPACE && (#[trigger] list_b.nodes@[n as int]).live && list_b.nodes@[n as int].kind is Binding
        implies thread_bound(tb, n) by {
        reveal(thread_bound);
        if n != t {
            assert(list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Binding);
            assert(ta.records@.contains_key(n));
        }
    }
    assert forall|x: usize| #[trigger] tb.records@.contains_key(x) && tb.records@[x].value().process is Some implies {
        let q = tb.records@[x].value().process->Some_0;
        &&& x < NODE_SPACE
        &&& list_b.nodes@[x as int].live
        &&& list_b.nodes@[x as int].kind is Binding
        &&& pb.records@.contains_key(q)
        &&& pb.bound@[q].contains(x)
    } by {
        if x != t {
            assert(ta.records@.contains_key(x));
            assert(tb.records@[x] == ta.records@[x]);
            let q = ta.records@[x].value().process->Some_0;
            assert(pa.bound@[q].contains(x));
            assert(list_b.nodes@[x as int].live == list_a.nodes@[x as int].live);
        }
    }
    assert forall|q: usize, x: usize| pb.records@.contains_key(q) && #[trigger] pb.bound@[q].contains(x)
        implies tb.records@.contains_key(x) && tb.records@[x].value().process == Some(q) by {
        if !(q == p && x == t) {
            assert(pa.bound@[q].contains(x));
            assert(ta.records@.contains_key(x));
            assert(x != t);
            assert(tb.records@[x] == ta.records@[x]);
        }
    }
}

/// The threads after a step that rewrote one thread's record in place.
pub proof fn lemma_threads_record_written(list: &Tree, tables: &Tables, a: &Threads, b: &Threads, blocks: &BlockTable, t: usize)
    requires
        threads_wf(list, tables, a, blocks),
        b.holders == a.holders,
        b.records@.dom() == a.records@.dom(),
        forall|x: usize| x != t && #[trigger] b.records@.contains_key(x) ==> b.records@[x] == a.records@[x],
        a.records@.contains_key(t) ==> b.records@[t].addr() == a.records@[t].addr() && b.records@[t].is_init(),
    ensures
        threads_wf(list, tables, b, blocks),
{
    assert forall|x: usize| #[trigger] b.records@.contains_key(x) implies thread_wf(list, b, blocks, x) by {
        assert(a.records@.contains_key(x));
        assert(thread_wf(list, a, blocks, x));
    }
    assert forall|x: usize| blocks.tracks(x as int) && #[trigger] thread_block(blocks, x) implies b.records@.contains_key((x * 4096) as usize) by {
        assert(a.records@.contains_key((x * 4096) as usize));
    }
    assert forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Thread implies {
        &&& b.records@.contains_key(tables.payload_of(n).base)
        &&& b.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == THREAD_ORDER
    } by {
        assert(a.records@.contains_key(tables.payload_of(n).base));
    }
    assert forall|u: usize, n: usize| b.records@.contains_key(u) && #[trigger] b.holders@[u].contains(n) implies {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Thread
        &&& tables.payload_of(n).base == u
    } by {
        assert(a.records@.contains_key(u));
    }
}

/// A record with its process binding undone: no process, and Inactive unless it is Dead, or Running,
/// which only its core may change and so gets a pending stop its core acts on at its next entry.
pub open spec fn unbound_record(r: ThreadRecord) -> ThreadRecord {
    ThreadRecord {
        state: match r.state {
            ThreadState::Running { .. } => r.state,
            ThreadState::Dead => r.state,
            _ => ThreadState::Inactive,
        },
        frame: r.frame,
        pending_stop: r.state is Running,
        dying: r.dying,
        process: None,
        placement: r.placement,
    }
}

/// The binding nodes after a step that added pages, whose nodes are dead, then made x and y live as
/// something other than bindings.
pub proof fn lemma_binding_nodes_grown(a: Tree, mid: Tree, b: Tree, x: usize, y: usize)
    requires
        a.wf(),
        list_grown(a, mid),
        forall|i: int| #![trigger b.nodes@[i]] 0 <= i < NODE_SPACE && i != x && i != y ==> {
            &&& b.nodes@[i].live == mid.nodes@[i].live
            &&& b.nodes@[i].kind == mid.nodes@[i].kind
        },
        x < NODE_SPACE,
        y < NODE_SPACE,
        !a.nodes@[x as int].live,
        !a.nodes@[y as int].live,
        !(b.nodes@[x as int].kind is Binding),
        !(b.nodes@[y as int].kind is Binding),
    ensures
        same_bindings(&a, &b),
{
    assert forall|i: usize| i < NODE_SPACE implies
        ((#[trigger] b.nodes@[i as int]).live && b.nodes@[i as int].kind is Binding) == (a.nodes@[i as int].live && a.nodes@[i as int].kind is Binding) by {
        if i != x && i != y {
            assert(mid.nodes@[i as int].live == a.nodes@[i as int].live);
            if a.nodes@[i as int].live {
                a.lemma_live_valid(i);
                assert(mid.nodes@[i as int] == a.nodes@[i as int]);
            }
        }
    }
}

/// The binding nodes stay when only nodes n and m change in the pages a held, neither a binding before
/// or after, and any page b adds holds no binding.
pub proof fn lemma_same_bindings_frame(a: &Tree, b: &Tree, n: usize, m: usize)
    requires
        a.wf(),
        b.wf(),
        forall|x: usize| #[trigger] a.valid(x) && x != n && x != m ==> {
            &&& b.nodes@[x as int].live == a.nodes@[x as int].live
            &&& b.nodes@[x as int].kind == a.nodes@[x as int].kind
        },
        forall|x: usize| x < NODE_SPACE && #[trigger] b.valid(x) && !a.valid(x) && x != n && x != m
            ==> !(b.nodes@[x as int].live && b.nodes@[x as int].kind is Binding),
        !(a.nodes@[n as int].live && a.nodes@[n as int].kind is Binding),
        !(b.nodes@[n as int].live && b.nodes@[n as int].kind is Binding),
        !(a.nodes@[m as int].live && a.nodes@[m as int].kind is Binding),
        !(b.nodes@[m as int].live && b.nodes@[m as int].kind is Binding),
    ensures
        same_bindings(a, b),
{
    assert forall|x: usize| x < NODE_SPACE implies
        ((#[trigger] b.nodes@[x as int]).live && b.nodes@[x as int].kind is Binding)
            == (a.nodes@[x as int].live && a.nodes@[x as int].kind is Binding) by {
        if x != n && x != m {
            if a.valid(x) {
            } else {
                if a.nodes@[x as int].live {
                    a.lemma_live_valid(x);
                }
                if b.nodes@[x as int].live {
                    b.lemma_live_valid(x);
                }
            }
        }
    }
}

/// Each thread's holders after node i is renamed n.
pub open spec fn moved_thread_holders(holders: IMap<usize, Set<usize>>, i: usize, n: usize) -> IMap<usize, Set<usize>> {
    IMap::new(
        |t: usize| holders.contains_key(t),
        |t: usize| if holders[t].contains(i) { holders[t].remove(i).insert(n) } else { holders[t] },
    )
}

/// The thread capabilities of a and b are the same, saying the same.
pub open spec fn same_threads(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    &&& forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Thread ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
    &&& forall|x: usize| #[trigger] tables_a.is_cap(list_a, x) && tables_a.payload_of(x).kind is Thread ==> {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x) == tables_a.payload_of(x)
    }
}

/// The threads read nothing of the list but its pages, and nothing of the capabilities but the
/// threads'.
pub proof fn lemma_threads_same_caps(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    blocks: &BlockTable,
)
    requires
        threads_wf(list_a, tables_a, threads, blocks),
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        threads_wf(list_b, tables_b, threads, blocks),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, blocks, t) by {
        assert(thread_wf(list_a, threads, blocks, t));
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Thread implies {
        &&& threads.records@.contains_key(tables_b.payload_of(n).base)
        &&& threads.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == THREAD_ORDER
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|t: usize, n: usize| threads.records@.contains_key(t) && #[trigger] threads.holders@[t].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Thread
        &&& tables_b.payload_of(n).base == t
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_threads_same_pages(list: &Tree, tables: &Tables, threads: &Threads, a: &BlockTable, b: &BlockTable)
    requires
        threads_wf(list, tables, threads, a),
        b.pages@ == a.pages@,
    ensures
        threads_wf(list, tables, threads, b),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list, threads, b, t) by {
        assert(thread_wf(list, threads, a, t));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        assert(thread_block(a, x));
    }
}

/// A step that changes the count of a block that is no thread's leaves every thread's block as it was.
pub proof fn lemma_threads_refs_changed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        threads_wf(list_a, tables_a, threads, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !(a.pages@[x as int].object is Thread),
            _ => true,
        },
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        threads_wf(list_b, tables_b, threads, b),
{
    lemma_threads_same_caps(list_a, tables_a, list_b, tables_b, threads, a);
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, b, t) by {
        assert(thread_wf(list_b, threads, a, t));
        let x = BlockRef::Small(t / 4096);
        assert(block_typed(a, x));
        assert(x != br);
        assert(block_refs(b, x) == block_refs(a, x));
        assert(block_dead(b, x) == block_dead(a, x));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        assert(thread_block(a, x));
    }
}

/// The threads after a free small block is typed as something that is no thread: no thread lay in
/// it, and a thread block outside it was one before.
pub proof fn lemma_threads_small_typed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        threads_wf(list_a, tables_a, threads, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| a.tracks(i) && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
        forall|k: int| 0 <= k < size ==> !((#[trigger] b.pages@[base + k]).object is Thread),
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        threads_wf(list_b, tables_b, threads, b),
{
    lemma_threads_same_caps(list_a, tables_a, list_b, tables_b, threads, a);
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, b, t) by {
        assert(thread_wf(list_b, threads, a, t));
        let x = (t / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        if base <= x < base + size {
            assert(!(b.pages@[base + (x - base)].object is Thread));
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(thread_block(a, x));
    }
}

/// The threads after a small block frees: a thread's first page is the list's, so it was not in it,
/// and a freed page is no thread block.
pub proof fn lemma_threads_small_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        threads_wf(list_a, tables_a, threads, a),
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) && a.tracks_addr(p)
            ==> !a.in_block(base as int, (p / 4096) as int),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> list_b.pages@.dom().contains(t),
    ensures
        threads_wf(list_b, tables_b, threads, b),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, b, t) by {
        assert(thread_wf(list_a, threads, a, t));
        assert(list_b.pages@.dom().contains(t));
        assert(!a.in_block(base as int, (t / 4096) as int));
        assert(b.pages@[(t / 4096) as int] == a.pages@[(t / 4096) as int]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(thread_block(a, x));
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Thread implies {
        &&& threads.records@.contains_key(tables_b.payload_of(n).base)
        &&& threads.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == THREAD_ORDER
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|t: usize, n: usize| threads.records@.contains_key(t) && #[trigger] threads.holders@[t].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Thread
        &&& tables_b.payload_of(n).base == t
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// A thread's node page stays the list's when the page of a block of another kind leaves it.
pub proof fn lemma_thread_node_pages_kept(
    list_a: &Tree,
    list_b: &Tree,
    tables: &Tables,
    threads: &Threads,
    blocks: &BlockTable,
    base: usize,
)
    requires
        threads_wf(list_a, tables, threads, blocks),
        blocks.tracks_addr(base),
        !(blocks.pages@[(base / 4096) as int].object is Thread),
        list_b.pages@.dom() == list_a.pages@.dom().remove(base),
    ensures
        forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> list_b.pages@.dom().contains(t),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies list_b.pages@.dom().contains(t) by {
        assert(thread_wf(list_a, threads, blocks, t));
        assert(t != base);
    }
}

/// No thread lies in a block of another kind: a thread's first page is its own block's base.
pub proof fn lemma_threads_outside_block(list: &Tree, tables: &Tables, threads: &Threads, blocks: &BlockTable, base: usize)
    requires
        threads_wf(list, tables, threads, blocks),
        blocks.wf(),
        blocks.tracks(base as int),
        blocks.pages@[base as int].kind is Base,
        !(blocks.pages@[base as int].object is Thread),
    ensures
        forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> {
            &&& !blocks.in_block(base as int, (t / 4096) as int)
            &&& t % 4096 == 0
        },
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies {
        &&& !blocks.in_block(base as int, (t / 4096) as int)
        &&& t % 4096 == 0
    } by {
        assert(thread_wf(list, threads, blocks, t));
        let x = (t / 4096) as int;
        if blocks.in_block(base as int, x) && x != base {
            blocks.lemma_member_of(base as int, x);
        }
    }
}

impl CapKernel {
    /// The bindings after a step that changed no node but n and m, neither a binding before or after,
    /// no thread's record and no process's bindings, and renamed n to m in the parent map at most.
    pub proof fn lemma_bindings_caps_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            !(pre.list.nodes@[n as int].live && pre.list.nodes@[n as int].kind is Binding),
            !(post.list.nodes@[n as int].live && post.list.nodes@[n as int].kind is Binding),
            !(pre.list.nodes@[m as int].live && pre.list.nodes@[m as int].kind is Binding),
            !(post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Binding),
            post.threads.records == pre.threads.records,
            post.processes.records == pre.processes.records,
            post.processes.bound == pre.processes.bound,
            forall|x: usize| x != n && x != m && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == rename(pre.list.parent@[x], n, m),
            pre.is_cap(n) ==> pre.list.childless(n) || (post.is_cap(m) && post.payload_of(m) == pre.payload_of(n)),
            pre.is_cap(m) && m != n ==> pre.list.childless(m),
        ensures
            bindings_wf(&post.list, &post.threads, &post.processes),
            binding_parents(&post.list, &post.tables, &post.threads),
    {
        Self::lemma_binding_parents_caps_frame(pre, post, n, m);
        assert forall|x: usize| x < NODE_SPACE implies
            ((#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Binding)
                == (pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Binding) by {
            if x != n && x != m {
                assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
                assert(post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind);
            }
        }
        assert(same_bindings(&pre.list, &post.list));
        lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
    }

    /// The binding parents after a step that changed no node but n and m, neither a binding after it,
    /// kept every other thread's process, and renamed n to m in the parent map at most. A binding's
    /// parent is a capability with a child, so it is n or m only when n, renamed m, says the same.
    pub proof fn lemma_binding_parents_caps_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            !(post.list.nodes@[n as int].live && post.list.nodes@[n as int].kind is Binding),
            !(post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Binding),
            forall|x: usize| x != n && x != m && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == rename(pre.list.parent@[x], n, m),
            forall|x: usize| x != n && x != m && #[trigger] pre.threads.records@.contains_key(x) ==> {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().process == pre.threads.records@[x].value().process
            },
            pre.is_cap(n) ==> pre.list.childless(n) || (post.is_cap(m) && post.payload_of(m) == pre.payload_of(n)),
            pre.is_cap(m) && m != n ==> pre.list.childless(m),
        ensures
            binding_parents(&post.list, &post.tables, &post.threads),
    {
        reveal(binding_parents);
        assert forall|t: usize| t < NODE_SPACE && (#[trigger] post.list.nodes@[t as int]).live
            && post.list.nodes@[t as int].kind is Binding
            implies binding_parent(&post.list, &post.tables, &post.threads, t) by {
            assert(t != n && t != m);
            assert(pre.list.nodes@[t as int].live && pre.list.nodes@[t as int].kind is Binding);
            assert(binding_parent(&pre.list, &pre.tables, &pre.threads, t));
            let a = pre.list.parent@[t];
            assert(pre.is_cap(a));
            let s = pre.list.seq@;
            assert(has(s, t));
            lemma_has(s, t);
            assert(pre.list.nodes@[s[0] as int].kind is Capability);
            assert(pre.list.is_child(a, t));
            assert(pre.list.nodes@[a as int].live);
            if a == n {
                if pre.list.childless(n) {
                    pre.list.lemma_childless(n, t);
                }
                assert(post.is_cap(m) && post.payload_of(m) == pre.payload_of(n));
            } else if a == m {
                pre.list.lemma_childless(m, t);
            } else {
                Self::lemma_caps_frame(pre, post, n, m, a);
            }
        }
    }

    /// The binding parents after a step that made no binding, kept every live node's parent, every
    /// capability saying the same, and every thread's process.
    pub proof fn lemma_binding_parents_same_caps(pre: Self, post: Self)
        requires
            binding_parents(&pre.list, &pre.tables, &pre.threads),
            same_bindings(&pre.list, &post.list),
            forall|x: usize| x < NODE_SPACE && pre.list.nodes@[x as int].live && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == pre.list.parent@[x],
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.is_cap(x) && post.payload_of(x) == pre.payload_of(x),
            forall|t: usize| #[trigger] pre.threads.records@.contains_key(t) ==> {
                &&& post.threads.records@.contains_key(t)
                &&& post.threads.records@[t].value().process == pre.threads.records@[t].value().process
            },
        ensures
            binding_parents(&post.list, &post.tables, &post.threads),
    {
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Process implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            assert(pre.is_cap(x));
        }
        lemma_binding_parents_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
    }

    /// A live binding node's parent is a capability to the process its thread's record names.
    pub proof fn lemma_binding_parent(&self, t: usize)
        requires
            self.wf(),
            t < NODE_SPACE,
            self.list.nodes@[t as int].live,
            self.list.nodes@[t as int].kind is Binding,
        ensures
            self.list.parent@.contains_key(t),
            self.is_cap(self.list.parent@[t]),
            self.payload_of(self.list.parent@[t]).kind is Process,
            self.threads.records@.contains_key(t),
            self.threads.records@[t].value().process == Some(self.payload_of(self.list.parent@[t]).base),
    {
        reveal(binding_parents);
        assert(binding_parent(&self.list, &self.tables, &self.threads, t));
    }

    /// A capability with the control right names a typed thread or process: its base is that object's
    /// block, so a base no thread or process holds is named by no control capability.
    pub proof fn lemma_control_names_object(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            self.payload_of(n).rights & CONTROL_RIGHT != 0,
        ensures
            ({
                let base = self.payload_of(n).base;
                ||| self.payload_of(n).kind is Thread && self.threads.records@.contains_key(base)
                    && thread_block(&self.blocks, base / 4096)
                ||| self.payload_of(n).kind is Process && self.processes.records@.contains_key(base)
                    && process_block(&self.blocks, base / 4096)
            }),
    {
        let base = self.payload_of(n).base;
        assert(control_named(self.tables.payload_of(n)));
        if self.payload_of(n).kind is Thread {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, base));
        } else {
            assert(process_wf(&self.processes, &self.blocks, base));
        }
    }

    /// A bound thread's process is a process whose block counts the binding among its references.
    pub proof fn lemma_bound_process(&self, t: usize)
        requires
            self.wf(),
            self.threads.records@.contains_key(t),
            self.threads.records@[t].value().process is Some,
        ensures
            ({
                let p = self.threads.records@[t].value().process->Some_0;
                &&& self.processes.records@.contains_key(p)
                &&& self.processes.bound@[p].contains(t)
                &&& p % 32768 == 0
                &&& self.blocks.tracks_addr(p)
                &&& self.blocks.pages@[(p / 4096) as int].object is Process
                &&& block_typed(&self.blocks, BlockRef::Small(p / 4096))
                &&& block_refs(&self.blocks, BlockRef::Small(p / 4096)) > 0
            }),
    {
        let p = self.threads.records@[t].value().process->Some_0;
        assert(process_wf(&self.processes, &self.blocks, p));
        if self.processes.bound@[p].len() == 0 {
            self.processes.bound@[p].lemma_len0_is_empty();
        }
        self.blocks.lemma_not_free_uncovered((p / 4096) as int);
    }

    /// Thread t's binding to its process, node t, is undone: t names no process and is Inactive unless
    /// it is Running or Dead, and the process's block has one reference fewer, no longer counting t.
    pub open spec fn unbound(pre: Self, post: Self, t: usize) -> bool {
        let r = pre.threads.records@[t].value();
        let p = r.process->Some_0;
        let br = BlockRef::Small(p / 4096);
        &&& pre.threads.records@.contains_key(t)
        &&& r.process is Some
        &&& pre.processes.records@.contains_key(p)
        &&& pre.processes.bound@[p].contains(t)
        &&& blocks_refs_changed(
            &pre.blocks,
            &post.blocks,
            br,
            (block_refs(&pre.blocks, br) - 1) as usize,
            block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
        )
        &&& post.holders == pre.holders
        &&& post.processes.records == pre.processes.records
        &&& post.processes.spare == pre.processes.spare
        &&& post.processes.holders == pre.processes.holders
        &&& post.processes.bound@ == pre.processes.bound@.insert(p, pre.processes.bound@[p].remove(t))
        &&& post.threads.holders == pre.threads.holders
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
            ==> post.threads.records@[x] == pre.threads.records@[x]
        &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
        &&& post.threads.records@[t].is_init()
        &&& post.threads.records@[t].value() == unbound_record(r)
        &&& post.stop_ipis@ == match r.state {
            ThreadState::Running { core } => pre.stop_ipis@.push(core),
            _ => pre.stop_ipis@,
        }
    }

    /// Undoes thread t's binding to its process, node t, before revoke unlinks the node. A thread
    /// Running on a core gets a pending stop and that core an IPI, and is left to that core.
    pub fn unbind(&mut self, t: usize)
        requires
            old(self).wf(),
            t < NODE_SPACE,
            old(self).list.nodes@[t as int].live,
            old(self).list.nodes@[t as int].kind is Binding,
        ensures
            Self::unbound(*old(self), *final(self), t),
            final(self).blocks.wf(),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).devices == old(self).devices,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).tlb == old(self).tlb,
            final(self).iommus == old(self).iommus,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).table_pages == old(self).table_pages,
            final(self).spaces == old(self).spaces,
            final(self).mappings == old(self).mappings,
    {
        let ghost pre = *old(self);
        proof {
            reveal(thread_bound);
            assert(pre.threads.records@.contains_key(t));
            assert(pre.threads.records@[t].value().process is Some);
            pre.lemma_bound_process(t);
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let p = match record.process {
            Some(p) => p,
            None => {
                proof {
                    assert(false);
                }
                0
            },
        };
        let (state, running) = match record.state {
            ThreadState::Running { core } => {
                self.stop_ipis = Ghost(pre.stop_ipis@.push(core));
                (ThreadState::Running { core }, true)
            },
            ThreadState::Dead => (ThreadState::Dead, false),
            _ => (ThreadState::Inactive, false),
        };
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord { state, frame: record.frame, pending_stop: running, dying: record.dying, process: None, placement: record.placement });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            assert(self.threads.records@.dom() =~= pre.threads.records@.dom());
        }
        drop_block_ref(&mut self.blocks, BlockRef::Small(p / 4096));
        self.processes.bound = Ghost(pre.processes.bound@.insert(p, pre.processes.bound@[p].remove(t)));
    }

    /// A thread capability names a thread, whose block holds its reference, lies in no typed region
    /// and so is read as the small block at its base.
    pub proof fn lemma_thread_cap(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            self.payload_of(n).kind is Thread,
        ensures
            self.threads.records@.contains_key(self.payload_of(n).base),
            self.threads.holders@[self.payload_of(n).base].contains(n),
            self.payload_of(n).base % 8192 == 0,
            self.blocks.tracks_addr(self.payload_of(n).base),
            self.payload_of(n).order == THREAD_ORDER,
            self.blocks.pages@[(self.payload_of(n).base / 4096) as int].object is Thread,
            block_typed(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)),
            block_refs(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)) > 0,
            block_ref(&self.blocks, self.payload_of(n).base / 4096) == BlockRef::Small(self.payload_of(n).base / 4096),
    {
        let t = self.payload_of(n).base;
        assert(self.tables.is_cap(&self.list, n));
        assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
        if self.threads.holders@[t].len() == 0 {
            self.threads.holders@[t].lemma_len0_is_empty();
        }
        self.blocks.lemma_not_free_uncovered((t / 4096) as int);
    }

    /// The threads after thread capability n, the only capability that changed, joins thread t with
    /// one more reference on its block.
    pub proof fn lemma_threads_holder_added(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            !pre.is_cap(n),
            post.is_cap(n),
            post.payload_of(n).kind is Thread,
            post.payload_of(n).base == t,
            post.payload_of(n).order == THREAD_ORDER,
            pre.threads.records@.contains_key(t),
            block_refs(&pre.blocks, BlockRef::Small(t / 4096)) < usize::MAX,
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(t / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(t / 4096)) + 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(t / 4096)),
            ),
            post.threads.records == pre.threads.records,
            post.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].insert(n)),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
    {
        let ha = pre.threads.holders@;
        let hb = post.threads.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(t / 4096);
        assert(thread_wf(&pre.list, &pre.threads, a, t));
        assert(!ha[t].contains(n));
        vstd::set::lemma_set_insert_len(ha[t], n);
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u)
            implies thread_wf(&post.list, &post.threads, b, u) by {
            assert(thread_wf(&pre.list, &pre.threads, a, u));
            if u != t {
                lemma_leaf_pages_distinct(u, t);
                let x = BlockRef::Small(u / 4096);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(b, x)
            implies post.threads.records@.contains_key((x * 4096) as usize) by {
            assert(thread_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Thread implies {
            &&& post.threads.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == THREAD_ORDER
        } by {
            if x != n {
                assert(pre.tables.is_cap(&pre.list, x));
            }
        }
        assert forall|u: usize, x: usize| post.threads.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Thread
            &&& post.tables.payload_of(x).base == u
        } by {
            if !(u == t && x == n) {
                assert(ha[u].contains(x));
                assert(pre.tables.is_cap(&pre.list, x));
                assert(x != n);
            }
        }
    }

    /// The threads after thread capability n, the only capability that changed, leaves thread t,
    /// taking its reference on the block with it.
    pub proof fn lemma_threads_holder_dropped(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            pre.is_cap(n),
            pre.payload_of(n).kind is Thread,
            pre.payload_of(n).base == t,
            !post.is_cap(n),
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(t / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(t / 4096)) - 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(t / 4096)) || block_refs(&pre.blocks, BlockRef::Small(t / 4096)) == 1,
            ),
            post.threads.records == pre.threads.records,
            post.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].remove(n)),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
    {
        let ha = pre.threads.holders@;
        let hb = post.threads.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(t / 4096);
        pre.lemma_thread_cap(n);
        assert(thread_wf(&pre.list, &pre.threads, a, t));
        assert(ha[t].contains(n));
        vstd::set::lemma_set_remove_len(ha[t], n);
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u)
            implies thread_wf(&post.list, &post.threads, b, u) by {
            assert(thread_wf(&pre.list, &pre.threads, a, u));
            if u != t {
                lemma_leaf_pages_distinct(u, t);
                let x = BlockRef::Small(u / 4096);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(b, x)
            implies post.threads.records@.contains_key((x * 4096) as usize) by {
            assert(thread_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Thread implies {
            &&& post.threads.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == THREAD_ORDER
        } by {
            assert(x != n);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|u: usize, x: usize| post.threads.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Thread
            &&& post.tables.payload_of(x).base == u
        } by {
            assert(ha[u].contains(x));
            assert(pre.tables.is_cap(&pre.list, x));
            assert(x != n);
        }
    }

    /// What a thread's retype does to the block table: the free order-1 block at `page` is typed as the
    /// thread at `base`, its first page joins the list, and no holder changed.
    pub proof fn lemma_thread_blocks(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            same_mapping_nodes(&pre.list, &post.list),
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.blocks.wf(),
            base % 8192 == 0,
            base / 4096 == page,
            page * 4096 == base,
            page % 2 == 0,
            pre.blocks.tracks_run(page as int, 2),
            !pre.blocks.covered(page as int),
            forall|k: int| 0 <= k < 2 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Thread,
            post.blocks.pages@[page as int].order == 1,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 2 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            post.list.pages@.dom() == pre.list.pages@.dom().insert(base),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child).kind is Thread,
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
        assert forall|k: int| 0 < k < 2 implies {
            &&& (#[trigger] b.pages@[page + k]).kind is Member
            &&& b.pages@[page + k].base == page
        } by {
            b.lemma_member_of(page as int, page + k);
        }
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!pre.is_cap(child));
        lemma_list_pages_used_small_typed(&pre.list, a, b, page, 2);
        lemma_list_pages_used_page_added(&pre.list, &post.list, b, base);
        lemma_holders_small_typed(&pre.list, &pre.tables, a, b, &pre.zeroing, pre.holders@, page, 1);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, b, &pre.zeroing, pre.holders@);
        assert forall|br: BlockRef| #[trigger] pre.holders@.contains_key(br) implies block_typed(a, br) by {}
        lemma_objects_small_typed(&pre.tables, &post.tables, a, b, pre.holders@, page, 2);
        lemma_leaf_blocks_small_typed(&pre.list, &pre.tables, a, b, pre.holders@, page, 2);
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
        lemma_table_pages_small_typed(&pre.list, &pre.table_pages, a, b, page, 2);
        assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x)
            implies pre.table_pages.maps@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert(b.pages@[page as int].object is Thread);
            } else if page < x < page + 2 {
                assert(b.pages@[page + (x - page)].kind is Member);
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

    /// The threads after a thread's retype at base: the new one has its record and node page and
    /// holds its one capability, and every other lay outside the block and keeps its holders.
    pub proof fn lemma_threads_thread_added(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            base % 8192 == 0,
            base / 4096 == page,
            page * 4096 == base,
            pre.blocks.tracks_run(page as int, 2),
            forall|k: int| 0 <= k < 2 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Thread,
            post.blocks.pages@[page as int].order == 1,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 2 ==> (#[trigger] post.blocks.pages@[page + k]).kind is Member,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            post.list.pages@.dom().contains(base),
            post.threads.records@ == pre.threads.records@.insert(base, post.threads.records@[base]),
            post.threads.records@[base].addr() == base + THREAD_RECORD_PAGE * 4096,
            post.threads.records@[base].is_init(),
            post.threads.holders@ == pre.threads.holders@.insert(base, set![child]),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child) == thread_of(base),
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let ta = &pre.threads;
        let tb = &post.threads;
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!ta.records@.contains_key(base)) by {
            if ta.records@.contains_key(base) {
                assert(thread_wf(&pre.list, ta, a, base));
                assert(a.pages@[page + 0int].kind is Free);
            }
        }
        assert(!pre.is_cap(child));
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), child);
        assert(set![child].len() == 1);
        assert forall|t: usize| #[trigger] tb.records@.contains_key(t) implies thread_wf(&post.list, tb, b, t) by {
            if t == base {
                assert(tb.holders@[base] == set![child]);
                assert(tb.holders@[base].finite());
            } else {
                assert(ta.records@.contains_key(t));
                assert(thread_wf(&pre.list, ta, a, t));
                let x = (t / 4096) as int;
                if page <= x < page + 2 {
                    assert(a.pages@[page + (x - page)].kind is Free);
                }
                assert(b.pages@[x] == a.pages@[x]);
                assert(tb.records@[t] == ta.records@[t]);
                assert(tb.holders@[t] == ta.holders@[t]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(b, x) implies tb.records@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert((x * 4096) as usize == base);
            } else if page < x < page + 2 {
                assert(b.pages@[page + (x - page)].kind is Member);
            } else {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(thread_block(a, x));
            }
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && post.tables.payload_of(n).kind is Thread implies {
            &&& tb.records@.contains_key(post.tables.payload_of(n).base)
            &&& tb.holders@[post.tables.payload_of(n).base].contains(n)
            &&& post.tables.payload_of(n).order == THREAD_ORDER
        } by {
            if n == child {
                assert(tb.holders@[base].contains(child));
            } else {
                assert(pre.tables.is_cap(&pre.list, n));
                let t = pre.tables.payload_of(n).base;
                assert(ta.records@.contains_key(t));
                assert(t != base);
                assert(tb.holders@[t] == ta.holders@[t]);
            }
        }
        assert forall|t: usize, n: usize| tb.records@.contains_key(t) && #[trigger] tb.holders@[t].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& post.tables.payload_of(n).kind is Thread
            &&& post.tables.payload_of(n).base == t
        } by {
            if t == base {
                assert(n == child);
            } else {
                assert(ta.records@.contains_key(t));
                assert(ta.holders@[t].contains(n));
                assert(pre.tables.is_cap(&pre.list, n));
                assert(n != child);
            }
        }
    }

    /// The view of a thread's retype: one child under the untyped, naming the new thread, which no
    /// table root is, so it holds nothing.
    proof fn lemma_thread_view(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize)
        requires
            Self::adds_cap(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(&pre.list, root, from),
            pre.tables.has_slot(&pre.list, root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            post.payload_of(pre.tables.node_of(root, to)) == thread_of(base),
            block_within(base, THREAD_ORDER, pre.payload_of(pre.tables.node_of(root, from))),
            !pre.tables.roots@.contains_key(base),
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
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        Self::lemma_places_node_view(pre, post, root, from, root, to);
        let pp = pre.payload_of(parent);
        lemma2_to64();
        assert(block_bytes(THREAD_ORDER) == 8192);
        assert(block_bytes(pp.order) == a.pages[parent] * 4096);
        assert(a.covers(parent, base)) by {
            assert(a.names.contains_key(parent));
            assert(a.pages.contains_key(parent));
            assert(a.names[parent] == pp.base);
            assert(block_within(base, THREAD_ORDER, pp));
            assert(base as int % 8192 == 0);
            vstd::arithmetic::div_mod::lemma_mod_mod(base as int, 4096, 2);
            assert(base % 4096 == 0);
            assert(base + 8192 <= pp.base + a.pages[parent] * 4096);
            assert(a.names[parent] <= base < a.names[parent] + a.pages[parent] * 4096);
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

    /// Types the free order-1 block at `base` as a thread bound to no process, under the untyped at
    /// index `from` of the table at `root`, with its capability at the empty index `to`. A refusal
    /// changes nothing. Only retype_thread calls it, and binds the thread in the same step.
    fn type_thread(&mut self, root: usize, from: usize, to: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).spaces == old(self).spaces,
            ret == old(self).can_retype_block(root, from, to, base, THREAD_ORDER),
            !ret ==> *final(self) == *old(self),
            ret ==> base as int + 8192 <= NODE_SPACE as int,
            ret ==> final(self).processes == old(self).processes,
            ret ==> final(self).tables.roots == old(self).tables.roots,
            ret ==> forall|x: usize| x != base ==> #[trigger] thread_process(&final(self).threads, x) == thread_process(&old(self).threads, x),
            ret ==> forall|x: usize| #[trigger] old(self).is_cap(x) ==> {
                &&& final(self).is_cap(x)
                &&& final(self).payload_of(x) == old(self).payload_of(x)
                &&& final(self).list.nodes@[x as int].depth == old(self).list.nodes@[x as int].depth
            },
            ret ==> forall|q: int| old(self).blocks.tracks(q) && !(base / 4096 <= q < base / 4096 + 2)
                ==> #[trigger] final(self).blocks.pages@[q] == old(self).blocks.pages@[q],
            ret ==> Self::retype_keeps(*old(self), *final(self), old(self).tables.node_of(root, to), (base / 4096) as int, 1, None),
            ret ==> Self::typed_nodes(old(self).list, final(self).list, old(self).tables.node_of(root, to), base),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                let page = (base / 4096) as int;
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& old(self).blocks.pages@[page].kind is Free
                &&& old(self).blocks.pages@[page + 1].kind is Free
                &&& final(self).blocks.pages@[page].kind is Base
                &&& final(self).blocks.pages@[page].object is Thread
                &&& final(self).blocks.pages@[page].order == 1
                &&& final(self).blocks.pages@[page].refs == 1
                &&& final(self).threads.records@.contains_key(base)
                &&& final(self).threads.records@[base].value() == fresh_thread()
                &&& forall|i: int| base <= i < base + NODES_PER_PAGE ==> !#[trigger] final(self).list.nodes@[i].live
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == thread_of(base)
                &&& final(self).payload_of(child).rights & right_bit(Right::Control) != 0
                &&& final(self).list.is_child(parent, child)
                &&& final(self).list.parent@ == old(self).list.parent@.insert(child, parent)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base, into: None })
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, THREAD_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        if !self.blocks.run_tracked(base / 4096, 2) {
            return false;
        }
        let page = base / 4096;
        proof {
            lemma2_to64();
            assert(block_bytes(1) == 8192);
            assert(base % 8192 == 0);
            assert(page % 2 == 0 && page * 4096 == base) by (nonlinear_arith)
                requires
                    base % 8192 == 0,
                    page == base / 4096,
            ;
        }
        // The caller's work is not counted yet, so its counter starts here: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let Tracked(perms) = match self.blocks.try_type(page, 1, ObjectType::Thread, Tracked(&mut steps)) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked mut first;
        let tracked second;
        proof {
            assert(0usize < order_pages(1));
            assert(1usize < order_pages(1));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * 4096);
            assert(perms[(page + 1usize) as usize].addr() == (page + 1usize) * 4096);
            assert((page + 0usize) as usize == page);
            first = perms.tracked_remove(page);
            second = perms.tracked_remove((page + 1) as usize);
            // The node page's permission is ours, so no table root lies there.
            if pre.tables.roots@.contains_key(base) {
                lemma_thread_block_layouts();
                first.is_distinct(self.tables.roots.borrow().tracked_borrow(base));
                pre.tables.lemma_root(base);
            }
            assert(!pre.list.pages@.dom().contains(base)) by {
                assert(pre.blocks.pages@[page + 0int].kind is Free);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(parent);
            pre.lemma_slot_bound(child);
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
        }
        let nodes = init_node_page(base, Tracked(first), Tracked(&mut steps));
        self.list.add_page(base, nodes);
        let ghost mid = self.list;
        proof {
            mid.lemma_seq_fits();
            assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]);
            assert(mid.nodes@[child as int] == pre.list.nodes@[child as int]);
        }
        let tracked mut record = page_into_thread_record(second);
        PPtr::<ThreadRecord>::from_usize(base + THREAD_RECORD_PAGE * 4096).put(Tracked(&mut record), new_thread_record());
        proof {
            self.threads.records.borrow_mut().tracked_insert(base, record);
        }
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: CapKind::Thread, order: THREAD_ORDER, rights: THREAD_RIGHTS, base, badge: 0, reserved: 0 },
        );
        self.threads.holders = Ghost(pre.threads.holders@.insert(base, set![child]));
        proof {
            let post = *self;
            assert forall|x: usize| #[trigger] pre.list.valid(x) && x != child implies {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            } by {
                assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
                pre.list.lemma_valid_bound(x);
            }
            assert(Self::space_step(pre, post, child));
            assert(post.payload_of(child) == thread_of(base));
            assert(payload_wf(post.payload_of(child)));
            assert(post.is_cap(child));
            Self::lemma_space_caps_wf(pre, post, child);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_space_nodes(pre, post, mid, parent, child);
            Self::lemma_table_nodes_frame(pre, post, child, child);
            Self::lemma_space_nodes_frame(pre, post, child, child);
            lemma_mapping_nodes_grown(pre.list, mid, post.list, child, child);
            assert(post.list.pages@.dom() == pre.list.pages@.dom().insert(base));
            assert forall|k: int| 0 < k < 2 implies (#[trigger] post.blocks.pages@[page + k]).kind is Member by {
                post.blocks.lemma_member_of(page as int, page + k);
            }
            Self::lemma_thread_blocks(pre, post, base, page, child);
            assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Space) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is Thread);
                }
            }
            assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Space implies {
                &&& pre.tables.is_cap(&pre.list, x)
                &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Space implies {
                &&& post.tables.is_cap(&post.list, x)
                &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            lemma_spaces_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page, 2);
            assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Process) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is Thread);
                }
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
            lemma_processes_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page, 2);
            Self::lemma_threads_thread_added(pre, post, base, page, child);
            assert(!pre.threads.records@.contains_key(base)) by {
                if pre.threads.records@.contains_key(base) {
                    assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, base));
                }
            }
            assert(post.threads.records@ == pre.threads.records@.insert(base, post.threads.records@[base]));
            assert(post.cores == pre.cores);
            assert(current_wf(post.cores@, post.threads.records@)) by {
                reveal(current_wf);
                assert forall|c: int, x: usize| 0 <= c < NUM_CPUS && #[trigger] runs(post.cores@, c, x) implies {
                    &&& post.threads.records@.contains_key(x)
                    &&& post.threads.records@[x].value().state == (ThreadState::Running { core: c as usize })
                } by {
                    assert(runs(pre.cores@, c, x));
                    assert(x != base);
                }
                assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                    let e = post.threads.records@[x].value().state->Running_core;
                    &&& e < NUM_CPUS
                    &&& post.cores@[e as int].current_thread == Some(x)
                } by {
                    assert(x != base);
                    assert(pre.threads.records@.contains_key(x));
                }
                assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                    implies post.threads.records@[x].value().state is Running by {
                    if x == base {
                        assert(post.threads.records@[base].value() == fresh_thread());
                    } else {
                        assert(pre.threads.records@.contains_key(x));
                    }
                }
            }
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
                assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
            }
            Self::lemma_mappings_grown(pre, post, page, 1);
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
            assert(post.wf());
            assert forall|i: int| base <= i < base + NODES_PER_PAGE implies !#[trigger] post.list.nodes@[i].live by {
                assert(mid.valid(i as usize));
                assert(!mid.nodes@[i].live);
                assert(i != child) by {
                    assert(pre.list.valid(child));
                }
            }
            assert(THREAD_RIGHTS & 128 != 0) by (compute_only);
            assert(right_bit(Right::Control) == 128);
            assert(right_bit(Right::Retype) == 8);
            assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
            Self::lemma_thread_view(pre, post, root, from, to, base);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            lemma_adds_object_discharges_retype(pre.view(), post.view(), root, parent, child, live, base);
            Self::lemma_type_thread_keeps(pre, post, mid, root, to, page as int);
            Self::lemma_typed_nodes(pre.list, mid, post.list, child, base);
        }
        true
    }

    /// What a thread's retype does to the list's nodes between pre and post, making the capability
    /// child and the node page at base: the first entry is kept, no node but child and base changed its
    /// liveness, and no node there was before but child its kind or depth. base was no node: its page
    /// is new, so the kinds of its dead nodes are fresh.
    pub open spec fn typed_nodes(pre: Tree, post: Tree, child: usize, base: usize) -> bool {
        &&& !pre.valid(base)
        &&& post.seq@[0] == pre.seq@[0]
        &&& forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != child && i != base
            ==> post.nodes@[i].live == pre.nodes@[i].live
        &&& forall|x: usize| #![trigger post.nodes@[x as int]] pre.valid(x) && x != child ==> {
            &&& post.nodes@[x as int].kind == pre.nodes@[x as int].kind
            &&& post.nodes@[x as int].depth == pre.nodes@[x as int].depth
        }
    }

    /// Typing a thread adds the node page at base, which keeps every node there was, then derives
    /// child, which keeps every other node: so it keeps the nodes as typed_nodes says.
    proof fn lemma_typed_nodes(pre: Tree, mid: Tree, post: Tree, child: usize, base: usize)
        requires
            pre.wf(),
            base % 4096 == 0,
            !pre.pages@.dom().contains(base),
            mid.seq == pre.seq,
            forall|i: usize| #[trigger] pre.valid(i) ==> mid.valid(i) && mid.nodes@[i as int] == pre.nodes@[i as int],
            forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] mid.nodes@[i].live == pre.nodes@[i].live,
            mid.nodes@.len() == NODE_SPACE,
            post.seq@[0] == mid.seq@[0],
            forall|i: int| #![trigger post.nodes@[i]] 0 <= i < mid.nodes@.len() && i != child ==> {
                &&& post.nodes@[i].live == mid.nodes@[i].live
                &&& post.nodes@[i].kind == mid.nodes@[i].kind
                &&& post.nodes@[i].depth == mid.nodes@[i].depth
            },
        ensures
            Self::typed_nodes(pre, post, child, base),
    {
        assert(page_of(base) == base) by {
            assert(base % 4096 == 0);
        }
        assert forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != child && i != base
            implies post.nodes@[i].live == pre.nodes@[i].live by {
            assert(mid.nodes@[i].live == pre.nodes@[i].live);
        }
        assert forall|x: usize| #![trigger post.nodes@[x as int]] pre.valid(x) && x != child implies {
            &&& post.nodes@[x as int].kind == pre.nodes@[x as int].kind
            &&& post.nodes@[x as int].depth == pre.nodes@[x as int].depth
        } by {
            pre.lemma_valid_bound(x);
            assert(mid.nodes@[x as int] == pre.nodes@[x as int]);
        }
    }

    /// The bind that follows makes only base live, a binding, and changes no other node's kind or
    /// depth, so the retype and the bind together keep the nodes as typed_nodes says.
    proof fn lemma_bound_nodes(pre: Tree, mid: Tree, post: Tree, child: usize, base: usize)
        requires
            pre.wf(),
            Self::typed_nodes(pre, mid, child, base),
            post.seq@[0] == mid.seq@[0],
            forall|x: int| #![trigger post.nodes@[x]] 0 <= x < NODE_SPACE && x != base ==> {
                &&& post.nodes@[x].live == mid.nodes@[x].live
                &&& post.nodes@[x].kind == mid.nodes@[x].kind
            },
            forall|x: int| #![trigger post.nodes@[x]] 0 <= x < NODE_SPACE && x != base
                ==> post.nodes@[x].depth == mid.nodes@[x].depth,
        ensures
            Self::typed_nodes(pre, post, child, base),
    {
        assert forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != child && i != base
            implies post.nodes@[i].live == pre.nodes@[i].live by {
            assert(mid.nodes@[i].live == pre.nodes@[i].live);
        }
        assert forall|x: usize| #![trigger post.nodes@[x as int]] pre.valid(x) && x != child implies {
            &&& post.nodes@[x as int].kind == pre.nodes@[x as int].kind
            &&& post.nodes@[x as int].depth == pre.nodes@[x as int].depth
        } by {
            pre.lemma_valid_bound(x);
            assert(x != base);
            assert(mid.nodes@[x as int].kind == pre.nodes@[x as int].kind);
        }
    }

    /// What typing a thread leaves as it was: its new node page and its derive changed the liveness
    /// of the new capability alone and no capability's depth, the table roots are the ones there were,
    /// and the block table's pages outside the thread's block are as they were.
    proof fn lemma_type_thread_keeps(pre: Self, post: Self, mid: Tree, root: usize, to: usize, page: int)
        requires
            pre.wf(),
            pre.tables.has_slot(&pre.list, root, to),
            !pre.list.nodes@[pre.tables.node_of(root, to) as int].live,
            forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] mid.nodes@[i].live == pre.list.nodes@[i].live,
            mid.nodes@.len() == NODE_SPACE,
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < mid.nodes@.len() && i != pre.tables.node_of(root, to)
                ==> post.list.nodes@[i].live == mid.nodes@[i].live,
            forall|x: usize| #[trigger] pre.is_cap(x) ==> {
                &&& post.is_cap(x)
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
            },
            post.tables.roots == pre.tables.roots,
            post.processes == pre.processes,
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            Self::retype_keeps(pre, post, pre.tables.node_of(root, to), page, 1, None),
    {
        let child = pre.tables.node_of(root, to);
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
            assert(post.list.nodes@[leaf as int].live == mid.nodes@[leaf as int].live);
            assert(mid.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
            if n != child {
                assert(post.list.nodes@[n as int].live == mid.nodes@[n as int].live);
                assert(mid.nodes@[n as int].live == pre.list.nodes@[n as int].live);
            }
        }
        assert forall|r: usize, e: int| pre.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES
            implies #[trigger] post.tables.leaf(r, e) == pre.tables.leaf(r, e) by {
            assert(post.tables.roots@[r] == pre.tables.roots@[r]);
        }
        assert forall|p: usize| #[trigger] pre.processes.records@.contains_key(p) implies {
            &&& post.processes.records@.contains_key(p)
            &&& post.processes.records@[p].value().dead == pre.processes.records@[p].value().dead
        } by {}
        assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(1))
            implies #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind by {
            assert(order_pages(1) == 2) by (compute_only);
            assert(post.blocks.pages@[i] == pre.blocks.pages@[i]);
        }
    }

    /// Retypes the free order-1 block at `base` as a thread in the process whose capability is at
    /// index `j`, under the untyped at index `from` of the table at `root`, with its capability at the
    /// empty index `to`. In one step the thread is typed, its control capability derived under the
    /// untyped and its binding, node 0 of its node page, under the process capability. All of these
    /// come from user space; every refusal is read before the block is typed, and changes nothing.
    /// Nothing binds a thread after this, so its process is fixed for its life. See
    /// design/thread-bound-at-retype/.
    pub fn retype_thread(&mut self, root: usize, from: usize, to: usize, base: usize, j: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).spaces == old(self).spaces,
            !ret ==> *final(self) == *old(self),
            !ret ==> bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret == old(self).can_retype_thread(root, from, to, base, j),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                let n = old(self).tables.node_of(root, j);
                let p = old(self).payload_of(n).base;
                let page = (base / 4096) as int;
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& old(self).blocks.pages@[page].kind is Free
                &&& old(self).blocks.pages@[page + 1].kind is Free
                &&& final(self).blocks.pages@[page].kind is Base
                &&& final(self).blocks.pages@[page].object is Thread
                &&& final(self).blocks.pages@[page].order == 1
                &&& final(self).blocks.pages@[page].refs == 1
                &&& forall|i: int| old(self).blocks.tracks(i) && !(page <= i < page + 2) && i != p / 4096
                    ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i]
                &&& final(self).threads.records@.contains_key(base)
                &&& final(self).threads.records@[base].value() == ThreadRecord {
                    state: ThreadState::Inactive,
                    frame: zero_registers(),
                    pending_stop: false,
                    dying: false,
                    process: Some(p),
                    placement: None,
                }
                &&& final(self).list.is_child(n, base)
                &&& final(self).list.parent@ == old(self).list.parent@.insert(child, parent).insert(base, n)
                &&& final(self).list.nodes@[base as int].live
                &&& final(self).list.nodes@[base as int].kind is Binding
                &&& forall|i: int| base < i < base + NODES_PER_PAGE ==> !#[trigger] final(self).list.nodes@[i].live
                &&& block_refs(&final(self).blocks, BlockRef::Small(p / 4096))
                    == block_refs(&old(self).blocks, BlockRef::Small(p / 4096)) + 1
                &&& final(self).processes.bound@ == old(self).processes.bound@.insert(p, old(self).processes.bound@[p].insert(base))
                &&& !final(self).can_delete(root, j)
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == thread_of(base)
                &&& final(self).payload_of(child).rights & right_bit(Right::Control) != 0
                &&& final(self).list.is_child(parent, child)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base, into: None })
                &&& bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables).insert(base, p)
                &&& Self::retype_keeps(*old(self), *final(self), child, page, 1, None)
                &&& Self::typed_nodes(old(self).list, final(self).list, child, base)
            },
    {
        let ghost pre = *old(self);
        let n = match self.process_slot(root, j) {
            Some(found) => found,
            None => { return false; },
        };
        if !self.type_thread(root, from, to, base) {
            return false;
        }
        let ghost mid = *self;
        proof {
            pre.lemma_process_cap(n);
            let q = (pre.payload_of(n).base / 4096) as int;
            assert(pre.blocks.pages@[q].object is Process);
            assert(!(base / 4096 <= q < base / 4096 + 2)) by {
                assert(pre.blocks.pages@[(base / 4096) as int].kind is Free);
                assert(pre.blocks.pages@[(base / 4096) as int + 1].kind is Free);
            }
            assert(mid.blocks.pages@[q] == pre.blocks.pages@[q]);
            assert(mid.is_cap(n));
        }
        self.bind_thread(n, base);
        proof {
            let post = *self;
            let parent = pre.tables.node_of(root, from);
            let child = pre.tables.node_of(root, to);
            let p = pre.payload_of(n).base;
            let page = (base / 4096) as int;
            let q = (p / 4096) as int;
            mid.lemma_thread_node_apart(base);
            mid.lemma_process_cap(n);
            assert(mid.blocks.pages@[page].object is Thread);
            assert(block_typed(&mid.blocks, BlockRef::Small(page as usize)));
            assert(BlockRef::Small(page as usize) != BlockRef::Small(p / 4096));
            assert(block_refs(&post.blocks, BlockRef::Small(page as usize)) == block_refs(&mid.blocks, BlockRef::Small(page as usize)));
            assert forall|i: int| base < i < base + NODES_PER_PAGE implies !#[trigger] post.list.nodes@[i].live by {
                assert(!mid.list.nodes@[i].live);
            }
            assert(child != base);
            assert(mid.is_cap(child));
            assert(post.is_cap(child));
            assert(post.list.nodes@[child as int].live);
            lemma_has(post.list.seq@, child);
            assert(post.list.is_child(parent, child));
            assert(post.view().holds(root, child));
            Self::lemma_leaf_added_discharges(mid, post, root, n, base);
            assert forall|x: NodeId| #[trigger] mid.view().names.contains_key(x) implies post.view().names.contains_key(x) by {
                assert(post.is_cap(x) == mid.is_cap(x));
            }
            lemma_retype_then_local(pre.view(), mid.view(), post.view(), root, parent, base);
            assert(post.tables.node_of(root, j) == n);
            post.lemma_parent_undeletable(root, j, base);
            assert(mid.payload_of(n) == pre.payload_of(n));
            assert(thread_process(&post.threads, base) == Some(p));
            assert forall|x: usize| x != base implies #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x) by {
                assert(thread_process(&mid.threads, x) == thread_process(&pre.threads, x));
            }
            Self::lemma_bound_threads_insert(pre, post, base, p);
            Self::lemma_bind_keeps(pre, mid, post, child, page, n, base);
            Self::lemma_bound_nodes(pre.list, mid.list, post.list, child, base);
        }
        true
    }

    /// A bind after a retype leaves what the retype left as it was: it makes live only the binding,
    /// on the first node of a page no slot lies in, changes no capability or table, and of the block
    /// table changes only a reference count.
    proof fn lemma_bind_keeps(pre: Self, mid: Self, post: Self, child: usize, page: int, n: usize, t: usize)
        requires
            pre.wf(),
            Self::retype_keeps(pre, mid, child, page, 1, None),
            Self::bound_to(mid, post, n, t),
            t % 4096 == 0,
            !mid.list.nodes@[t as int].live,
            forall|x: usize| #[trigger] post.is_cap(x) == mid.is_cap(x),
            forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != t
                ==> post.list.nodes@[x].depth == mid.list.nodes@[x].depth,
            post.blocks.regions_2m@ == mid.blocks.regions_2m@,
            post.blocks.regions_1g@ == mid.blocks.regions_1g@,
        ensures
            Self::retype_keeps(pre, post, child, page, 1, None),
    {
        assert forall|r: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, r, i) implies {
            &&& post.tables.has_slot(&post.list, r, i)
            &&& post.tables.node_of(r, i) == pre.tables.node_of(r, i)
            &&& pre.tables.node_of(r, i) != child && !pre.list.nodes@[pre.tables.node_of(r, i) as int].live
                ==> !post.list.nodes@[pre.tables.node_of(r, i) as int].live
        } by {
            pre.lemma_slot(r, i);
            let x = pre.tables.node_of(r, i);
            pre.lemma_slot_bound(x);
            let leaf = pre.tables.leaf(r, index_entry(i));
            assert(mid.tables.has_slot(&mid.list, r, i));
            assert(mid.tables.leaf(r, index_entry(i)) == leaf);
            assert(mid.list.nodes@[leaf as int].live);
            assert(leaf != t);
            assert(leaf < NODE_SPACE);
            assert(post.list.nodes@[leaf as int].live == mid.list.nodes@[leaf as int].live);
            assert(x != t);
            assert(post.list.nodes@[x as int].live == mid.list.nodes@[x as int].live);
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
            &&& post.is_cap(x)
            &&& post.payload_of(x) == pre.payload_of(x)
            &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
        } by {
            pre.lemma_slot_bound(x);
            assert(mid.is_cap(x));
            assert(x != t);
            assert(post.list.nodes@[x as int].depth == mid.list.nodes@[x as int].depth);
        }
        assert forall|r: usize, e: int| pre.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES
            implies #[trigger] post.tables.leaf(r, e) == pre.tables.leaf(r, e) by {
            assert(mid.tables.leaf(r, e) == pre.tables.leaf(r, e));
        }
        assert forall|p: usize| #[trigger] pre.processes.records@.contains_key(p) implies {
            &&& post.processes.records@.contains_key(p)
            &&& post.processes.records@[p].value().dead == pre.processes.records@[p].value().dead
        } by {
            assert(mid.processes.records@.contains_key(p));
        }
        assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(1))
            implies #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind by {
            assert(mid.blocks.pages@[i].kind == pre.blocks.pages@[i].kind);
            assert(mid.blocks.tracks(i));
        }
    }

    /// A switch on core c touched only c's current thread and thread t's record: t's state, its saved
    /// frame and its pending stop. See design/one-lock-bounded-steps/.
    pub open spec fn switch_frame(pre: Self, post: Self, c: int, t: usize) -> bool {
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.table_pages == pre.table_pages
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.spaces == pre.spaces
        &&& post.processes == pre.processes
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.iommus == pre.iommus
        &&& post.devices == pre.devices
        &&& post.tlb == pre.tlb
        &&& post.threads.holders == pre.threads.holders
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
            ==> post.threads.records@[x] == pre.threads.records@[x]
        &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
        &&& post.threads.records@[t].is_init()
        &&& post.threads.records@[t].value().process == pre.threads.records@[t].value().process
        &&& post.threads.records@[t].value().placement == pre.threads.records@[t].value().placement
        &&& post.cores@.len() == pre.cores@.len()
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d]
        &&& post.cores@[c].acked_epoch == pre.cores@[c].acked_epoch
        &&& post.cores@[c].generation == pre.cores@[c].generation
        &&& post.cores@[c].next_pcid == pre.cores@[c].next_pcid
        &&& post.cores@[c].pcids_used == pre.cores@[c].pcids_used
    }

    /// A switch keeps wf when it leaves the current threads matching the Running states.
    proof fn lemma_switch_wf(pre: Self, post: Self, c: int, t: usize)
        requires
            pre.wf(),
            0 <= c < NUM_CPUS,
            pre.threads.records@.contains_key(t),
            Self::switch_frame(pre, post, c, t),
            post.cores.wf(),
            current_wf(post.cores@, post.threads.records@),
        ensures
            post.wf(),
    {
        reveal(ids_wf);
        lemma_ids_core_step(pre.cores@, post.cores@, pre.spaces.loaded@, c);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) == pre.acked(d) by {
            if d != c {
                assert(post.cores@[d] == pre.cores@[d]);
            }
        }
        assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x)
            implies thread_wf(&post.list, &post.threads, &post.blocks, x) by {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, x));
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && #[trigger] thread_block(&post.blocks, b)
            implies post.threads.records@.contains_key((b * 4096) as usize) by {
            assert(thread_block(&pre.blocks, b));
        }
        assert(threads_wf(&post.list, &post.tables, &post.threads, &post.blocks));
        assert forall|x: usize| #[trigger] pre.threads.records@.contains_key(x) implies {
            &&& post.threads.records@.contains_key(x)
            &&& post.threads.records@[x].value().process == pre.threads.records@[x].value().process
        } by {}
        lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
        Self::lemma_binding_parents_same_caps(pre, post);
        Self::lemma_iommus_same(pre, post);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) <= post.flush_epoch by {
            assert(pre.acked(d) <= pre.flush_epoch);
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) implies post.loaded(d, e.space) by {
            assert(pre.tlb@[d].contains(e));
        }
        assert forall|d: int, e: TlbEntry|
            0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(d), e.page) by {
            assert(pre.tlb@[d].contains(e));
        }
        assert(post.tlb_wf());
    }

    /// Core c, running nothing, makes thread t, Runnable on c, its current thread. Which thread is the
    /// scheduler's choice; loading its frame and its space is the caller's.
    pub fn switch_in(&mut self, c: usize, t: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).cores@[c as int].current_thread is None,
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().state == (ThreadState::Runnable { core: c }),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            Self::switch_frame(*old(self), *final(self), c as int, t),
            final(self).cores@[c as int].current_thread == Some(t),
            final(self).threads.records@[t].value().state == (ThreadState::Running { core: c }),
            final(self).threads.records@[t].value().frame == old(self).threads.records@[t].value().frame,
            final(self).threads.records@[t].value().pending_stop == old(self).threads.records@[t].value().pending_stop,
            final(self).stop_ipis == old(self).stop_ipis,
    {
        let ghost pre = *self;
        proof {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        let state = *self.cores.get(c);
        self.cores.set(c, CoreState {
            current_thread: Some(t),
            acked_epoch: state.acked_epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            pcids_used: state.pcids_used,
        });
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = ptr.read(Tracked(&perm));
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: ThreadState::Running { core: c },
            frame: record.frame,
            pending_stop: record.pending_stop,
            dying: record.dying,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
            } by {
                if d != c {
                    assert(post.cores@[d] == pre.cores@[d]);
                    assert(runs(pre.cores@, d, x));
                    if x == t {
                        assert(pre.threads.records@[t].value().state == (ThreadState::Running { core: d as usize }));
                    }
                }
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                if x != t {
                    let e = pre.threads.records@[x].value().state->Running_core;
                    assert(pre.threads.records@.contains_key(x));
                    assert(e != c) by {
                        assert(pre.cores@[c as int].current_thread is None);
                    }
                    assert(post.cores@[e as int] == pre.cores@[e as int]);
                }
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, c as int, t);
        }
    }

    /// Core c, running nothing, makes thread t, Inactive, its current thread: boot's entry into the
    /// root's thread, which no capability has started. Boot made the thread, so it runs on c without
    /// a placement, design/root-process-at-boot/. Loading its frame and its space is the caller's.
    pub fn enter_boot_thread(&mut self, c: usize, t: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).cores@[c as int].current_thread is None,
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().state is Inactive,
        ensures
            final(self).wf(),
            Self::switch_frame(*old(self), *final(self), c as int, t),
            final(self).cores@[c as int].current_thread == Some(t),
            final(self).threads.records@[t].value().state == (ThreadState::Running { core: c }),
            final(self).threads.records@[t].value().pending_stop == old(self).threads.records@[t].value().pending_stop,
            final(self).stop_ipis == old(self).stop_ipis,
    {
        let ghost pre = *self;
        proof {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        let record = ptr.read(Tracked(&perm));
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: ThreadState::Runnable { core: c },
            frame: record.frame,
            pending_stop: record.pending_stop,
            dying: record.dying,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
            } by {
                assert(runs(pre.cores@, d, x));
                assert(x != t);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(x != t);
                assert(pre.threads.records@.contains_key(x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, c as int, t);
        }
        self.switch_in(c, t);
    }

    /// Core c saves its current thread's frame and leaves it Runnable on c, running nothing until it
    /// switches in again. A thread that must leave is moved off instead, by check_current.
    pub fn switch_out(&mut self, c: usize, frame: Registers)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).cores@[c as int].current_thread is Some,
            !old(self).threads.records@[old(self).cores@[c as int].current_thread->Some_0].value().pending_stop,
        ensures
            ({
                let t = old(self).cores@[c as int].current_thread->Some_0;
                &&& Self::step_ok(*old(self), *final(self), c as int)
                &&& Self::switch_frame(*old(self), *final(self), c as int, t)
                &&& old(self).threads.records@.contains_key(t)
                &&& old(self).threads.records@[t].value().state == (ThreadState::Running { core: c })
                &&& final(self).cores@[c as int].current_thread is None
                &&& final(self).threads.records@[t].value().state == (ThreadState::Runnable { core: c })
                &&& final(self).threads.records@[t].value().frame == frame
                &&& !final(self).threads.records@[t].value().pending_stop
                &&& final(self).stop_ipis == old(self).stop_ipis
            }),
    {
        let ghost pre = *self;
        let state = *self.cores.get(c);
        let t = match state.current_thread {
            Some(t) => t,
            None => { proof { assert(false); } 0 },
        };
        proof {
            reveal(current_wf);
            assert(runs(pre.cores@, c as int, t));
            assert(pre.threads.records@.contains_key(t));
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        self.cores.set(c, CoreState {
            current_thread: None,
            acked_epoch: state.acked_epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            pcids_used: state.pcids_used,
        });
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = ptr.read(Tracked(&perm));
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: ThreadState::Runnable { core: c },
            frame,
            pending_stop: record.pending_stop,
            dying: record.dying,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
            } by {
                assert(d != c);
                assert(post.cores@[d] == pre.cores@[d]);
                assert(runs(pre.cores@, d, x));
                assert(runs(pre.cores@, c as int, t));
                assert(x != t);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(x != t);
                let e = pre.threads.records@[x].value().state->Running_core;
                assert(pre.threads.records@.contains_key(x));
                assert(pre.cores@[e as int].current_thread == Some(x));
                assert(e != c);
                assert(post.cores@[e as int] == pre.cores@[e as int]);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, c as int, t);
        }
    }
}

impl CapKernel {
    /// Index i of the table at root holds a capability with the control right naming a thread.
    pub open spec fn holds_control(&self, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Thread
        &&& self.payload_of(n).rights & right_bit(Right::Control) != 0
    }

    /// Index i of the table at root holds a control capability naming a thread that is not dead: not
    /// Dead, not dying and not bound to a dead process. Nothing starts, suspends or sets the registers
    /// of a dead thread: see design/teardown-driven-by-retype/.
    pub open spec fn can_control(&self, root: usize, i: usize) -> bool {
        &&& self.holds_control(root, i)
        &&& !self.cap_dead(self.tables.node_of(root, i))
    }

    /// The thread that capability names, which must be Inactive for its registers to be read or
    /// written: only its core touches a Running thread's frame.
    pub open spec fn can_set_registers(&self, root: usize, i: usize) -> bool {
        &&& self.can_control(root, i)
        &&& self.threads.records@[self.payload_of(self.tables.node_of(root, i)).base].value().state is Inactive
    }

    /// The step wrote thread t's saved frame and nothing else.
    pub open spec fn frame_written(pre: Self, post: Self, t: usize, frame: Registers) -> bool {
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.table_pages == pre.table_pages
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.spaces == pre.spaces
        &&& post.processes == pre.processes
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.iommus == pre.iommus
        &&& post.devices == pre.devices
        &&& post.tlb == pre.tlb
        &&& post.cores == pre.cores
        &&& post.threads.holders == pre.threads.holders
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
            ==> post.threads.records@[x] == pre.threads.records@[x]
        &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
        &&& post.threads.records@[t].is_init()
        &&& post.threads.records@[t].value() == ThreadRecord {
            state: pre.threads.records@[t].value().state,
            frame,
            pending_stop: pre.threads.records@[t].value().pending_stop,
            dying: pre.threads.records@[t].value().dying,
            process: pre.threads.records@[t].value().process,
            placement: pre.threads.records@[t].value().placement,
        }
    }

    /// Finds the thread the control capability at index i names, and whether it is dead. The index
    /// comes from user space.
    fn thread_control(&self, root: usize, i: usize) -> (ret: Option<(usize, usize, bool)>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret is Some == self.holds_control(root, i),
            ret is Some ==> {
                let (n, t, dead) = ret->0;
                &&& n == self.tables.node_of(root, i)
                &&& dead == self.cap_dead(n)
                &&& t == self.payload_of(n).base
                &&& self.threads.records@.contains_key(t)
                &&& thread_wf(&self.list, &self.threads, &self.blocks, t)
                &&& self.view().holds_right(root, n, Right::Control)
                &&& self.view().names[n] == t
            },
    {
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return None;
        }
        proof {
            self.lemma_slot(root, i);
            assert(self.tables.is_cap(&self.list, n));
            assert(payload == self.payload_of(n));
        }
        let thread = match payload.kind {
            CapKind::Thread => true,
            _ => false,
        };
        if !thread || payload.rights & 128 == 0 {
            return None;
        }
        proof {
            assert(right_bit(Right::Control) == 128);
            self.lemma_thread_cap(n);
            assert(thread_wf(&self.list, &self.threads, &self.blocks, payload.base));
        }
        let dead = self.is_cap_dead(n, payload);
        Some((n, payload.base, dead))
    }

    /// Reads the saved frame of the Inactive thread named at index i, through its control capability.
    /// The index comes from user space, so it can be refused.
    pub fn read_registers(&self, root: usize, i: usize) -> (ret: Option<Registers>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
            self.root_live(root),
        ensures
            ret is Some == self.can_set_registers(root, i),
            ret is Some ==> {
                let n = self.tables.node_of(root, i);
                let t = self.payload_of(n).base;
                &&& self.threads.records@.contains_key(t)
                &&& ret->0 == self.threads.records@[t].value().frame
                &&& discharges(self.view(), self.view(), root, Effect::Control { cap: n, thread: t })
            },
    {
        let (n, t, dead) = match self.thread_control(root, i) {
            Some(found) => found,
            None => { return None; },
        };
        if dead {
            return None;
        }
        let record = *PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096).borrow(
            Tracked(self.threads.records.borrow().tracked_borrow(t)),
        );
        match record.state {
            ThreadState::Inactive => Some(record.frame),
            _ => None,
        }
    }

    /// Writes the saved frame of the Inactive thread named at index i, through its control capability,
    /// as user_frame makes it. The index and the frame come from user space, so either can be refused,
    /// and a refusal changes nothing.
    pub fn write_registers(&mut self, root: usize, i: usize, frame: Registers) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            ret == (old(self).can_set_registers(root, i) && user_rip(frame.pc())),
            !ret ==> *final(self) == *old(self),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret ==> {
                let n = old(self).tables.node_of(root, i);
                let t = old(self).payload_of(n).base;
                &&& old(self).threads.records@.contains_key(t)
                &&& Self::frame_written(*old(self), *final(self), t, user_frame(frame))
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Control { cap: n, thread: t })
            },
    {
        let ghost pre = *self;
        if !is_user_rip(frame.pc()) {
            return false;
        }
        let (n, t, dead) = match self.thread_control(root, i) {
            Some(found) => found,
            None => { return false; },
        };
        if dead {
            return false;
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        match record.state {
            ThreadState::Inactive => {},
            _ => { return false; },
        }
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: record.state,
            frame: user_frame_of(frame),
            pending_stop: record.pending_stop,
            dying: record.dying,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert(Self::frame_written(pre, post, t, user_frame(frame)));
            lemma_current_same(pre.cores@, post.cores@, pre.threads.records@, post.threads.records@);
            Self::lemma_switch_wf(pre, post, 0, t);
            assert(post.view() == pre.view());
        }
        true
    }

    /// The thread the control capability at index i names can be suspended: it is not dead, and it is
    /// Inactive already, Runnable or Running. One destroyed while Running is dying, and its core's
    /// stop makes it Dead.
    pub open spec fn can_suspend(&self, root: usize, i: usize) -> bool {
        let t = self.payload_of(self.tables.node_of(root, i)).base;
        &&& self.can_control(root, i)
        &&& match self.threads.records@[t].value().state {
            ThreadState::Inactive => true,
            ThreadState::Runnable { .. } => true,
            ThreadState::Running { .. } => true,
            _ => false,
        }
    }

    /// The thread the control capability at index i names is Running on a core other than c, so a
    /// suspend from c stops it there, by a pending stop that core acts on: see
    /// design/one-lock-bounded-steps/.
    pub open spec fn stops_elsewhere(&self, c: usize, root: usize, i: usize) -> bool {
        let state = self.threads.records@[self.payload_of(self.tables.node_of(root, i)).base].value().state;
        &&& self.can_suspend(root, i)
        &&& state is Running
        &&& state->Running_core != c
    }

    /// The thread the control capability at index i names can be started: it is Inactive, bound to a
    /// process, and placed on a core. A thread with no placement cannot run: see
    /// design/cpu-time-as-capability/.
    pub open spec fn can_start(&self, root: usize, i: usize) -> bool {
        let r = self.threads.records@[self.payload_of(self.tables.node_of(root, i)).base].value();
        &&& self.can_control(root, i)
        &&& r.state is Inactive
        &&& r.process is Some
        &&& r.placement is Some
    }

    /// Starts the thread the control capability at index i names: it becomes Runnable on the core it
    /// is placed on, which switches it in. The index comes from user space, so it can be refused, and
    /// a refusal changes nothing.
    pub fn start(&mut self, root: usize, i: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            ret == old(self).can_start(root, i),
            !ret ==> *final(self) == *old(self),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret ==> {
                let n = old(self).tables.node_of(root, i);
                let t = old(self).payload_of(n).base;
                let core = old(self).threads.records@[t].value().placement->Some_0;
                &&& old(self).threads.records@.contains_key(t)
                &&& Self::state_written(*old(self), *final(self), t, ThreadState::Runnable { core })
                &&& final(self).cores == old(self).cores
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Control { cap: n, thread: t })
            },
    {
        let ghost pre = *self;
        let (n, t, dead) = match self.thread_control(root, i) {
            Some(found) => found,
            None => { return false; },
        };
        if dead {
            return false;
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        match record.state {
            ThreadState::Inactive => {},
            _ => { return false; },
        }
        match record.process {
            Some(_) => {},
            None => { return false; },
        }
        let core = match record.placement {
            Some(core) => core,
            None => { return false; },
        };
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: ThreadState::Runnable { core },
            frame: record.frame,
            pending_stop: record.pending_stop,
            dying: record.dying,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
            } by {
                assert(runs(pre.cores@, d, x));
                assert(x != t);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(x != t);
                assert(pre.threads.records@.contains_key(x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, 0, t);
            assert(post.view() == pre.view());
        }
        true
    }

    /// The step wrote thread t's record as r, left every other record as it was, and every object but
    /// the cores and the stop IPIs.
    pub open spec fn record_written(pre: Self, post: Self, t: usize, r: ThreadRecord) -> bool {
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.table_pages == pre.table_pages
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.spaces == pre.spaces
        &&& post.processes == pre.processes
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.iommus == pre.iommus
        &&& post.devices == pre.devices
        &&& post.tlb == pre.tlb
        &&& post.threads.holders == pre.threads.holders
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
            ==> post.threads.records@[x] == pre.threads.records@[x]
        &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
        &&& post.threads.records@[t].is_init()
        &&& post.threads.records@[t].value() == r
    }

    /// The step set thread t's state and nothing else of its record or of any other record, and left
    /// every object but the cores as it was.
    pub open spec fn state_written(pre: Self, post: Self, t: usize, state: ThreadState) -> bool {
        &&& Self::record_written(pre, post, t, ThreadRecord { state, ..pre.threads.records@[t].value() })
        &&& post.stop_ipis == pre.stop_ipis
    }

    /// Suspends, from core c, the thread the control capability at index i names. An Inactive or
    /// Runnable thread, or c's current thread, which leaves c running nothing, is Inactive after, with
    /// no stop pending; its saved frame is the one it left user mode with. A thread Running on another
    /// core gets a pending stop and that core an IPI, and the caller suspends again to see it Inactive:
    /// only that core writes its current thread, design/one-lock-bounded-steps/. The index comes from
    /// user space, so it can be refused, and a refusal changes nothing.
    pub fn suspend(&mut self, c: usize, root: usize, i: usize) -> (ret: SuspendStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            Self::writes_only_own_current(*old(self), *final(self), c as int),
            ret is Refused == !old(self).can_suspend(root, i),
            ret is Again == old(self).stops_elsewhere(c, root, i),
            ret is Refused ==> *final(self) == *old(self),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret is Suspended ==> {
                let n = old(self).tables.node_of(root, i);
                let t = old(self).payload_of(n).base;
                let r = old(self).threads.records@[t].value();
                &&& old(self).threads.records@.contains_key(t)
                &&& Self::record_written(*old(self), *final(self), t, ThreadRecord { state: ThreadState::Inactive, pending_stop: false, ..r })
                &&& final(self).stop_ipis == old(self).stop_ipis
                &&& final(self).cores@.len() == old(self).cores@.len()
                &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).cores@[d] == old(self).cores@[d]
                &&& final(self).cores@[c as int] == if old(self).cores@[c as int].current_thread == Some(t) {
                    CoreState { current_thread: None, ..old(self).cores@[c as int] }
                } else {
                    old(self).cores@[c as int]
                }
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Control { cap: n, thread: t })
            },
            ret is Again ==> {
                let n = old(self).tables.node_of(root, i);
                let t = old(self).payload_of(n).base;
                let r = old(self).threads.records@[t].value();
                &&& old(self).threads.records@.contains_key(t)
                &&& Self::record_written(*old(self), *final(self), t, ThreadRecord { pending_stop: true, ..r })
                &&& final(self).stop_ipis@ == old(self).stop_ipis@.push(r.state->Running_core)
                &&& final(self).cores == old(self).cores
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Control { cap: n, thread: t })
            },
    {
        let ghost pre = *self;
        let (n, t, dead) = match self.thread_control(root, i) {
            Some(found) => found,
            None => { return SuspendStep::Refused; },
        };
        if dead {
            return SuspendStep::Refused;
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let current = match record.state {
            ThreadState::Inactive => false,
            ThreadState::Runnable { .. } => false,
            ThreadState::Running { core } => {
                if core != c {
                    self.stop_elsewhere(t, core);
                    proof {
                        assert(self.view() == pre.view());
                    }
                    return SuspendStep::Again;
                }
                true
            },
            _ => { return SuspendStep::Refused; },
        };
        proof {
            reveal(current_wf);
            assert(current == (pre.cores@[c as int].current_thread == Some(t))) by {
                if pre.cores@[c as int].current_thread == Some(t) {
                    assert(runs(pre.cores@, c as int, t));
                }
            }
        }
        if current {
            let state = *self.cores.get(c);
            self.cores.set(c, CoreState {
                current_thread: None,
                acked_epoch: state.acked_epoch,
                generation: state.generation,
                next_pcid: state.next_pcid,
                pcids_used: state.pcids_used,
            });
        }
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: ThreadState::Inactive,
            frame: record.frame,
            pending_stop: false,
            dying: record.dying,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
            } by {
                assert(post.cores@[d] == pre.cores@[d]);
                assert(runs(pre.cores@, d, x));
                assert(x != t);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(x != t);
                let e = pre.threads.records@[x].value().state->Running_core;
                assert(pre.threads.records@.contains_key(x));
                assert(pre.cores@[e as int].current_thread == Some(x));
                if current && e == c {
                    assert(x == t);
                }
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(x != t);
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, c as int, t);
            assert(post.view() == pre.view());
        }
        SuspendStep::Suspended
    }

    /// Sets a pending stop on thread t, Running on core d, and sends d an IPI, so that d moves it off
    /// at its next kernel entry. Nothing on the caller's core writes d's current thread or t's frame.
    fn stop_elsewhere(&mut self, t: usize, d: usize)
        requires
            old(self).wf(),
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().state == (ThreadState::Running { core: d }),
        ensures
            final(self).wf(),
            Self::record_written(*old(self), *final(self), t, ThreadRecord { pending_stop: true, ..old(self).threads.records@[t].value() }),
            final(self).stop_ipis@ == old(self).stop_ipis@.push(d),
            final(self).cores == old(self).cores,
    {
        let ghost pre = *self;
        proof {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: record.state,
            frame: record.frame,
            pending_stop: true,
            dying: record.dying,
            process: record.process,
            placement: record.placement,
        });
        self.stop_ipis = Ghost(pre.stop_ipis@.push(d));
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|e: int, x: usize| 0 <= e < NUM_CPUS && #[trigger] runs(post.cores@, e, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: e as usize })
            } by {
                assert(runs(pre.cores@, e, x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(pre.threads.records@.contains_key(x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, d as int, t);
        }
    }

    /// The step destroyed thread t from core c and changed no core. A thread Running on a core gets a
    /// pending stop that makes it Dead, and that core, unless it is c, an IPI; only that core moves it
    /// out of Running, design/one-lock-bounded-steps/. Any other thread is Dead with no stop pending.
    pub open spec fn thread_destroyed(pre: Self, post: Self, c: usize, t: usize) -> bool {
        let r = pre.threads.records@[t].value();
        &&& post.cores == pre.cores
        &&& match r.state {
            ThreadState::Running { core } => {
                &&& Self::record_written(pre, post, t, ThreadRecord { pending_stop: true, dying: true, ..r })
                &&& post.stop_ipis@ == if core == c { pre.stop_ipis@ } else { pre.stop_ipis@.push(core) }
            },
            _ => {
                &&& Self::record_written(pre, post, t, ThreadRecord { state: ThreadState::Dead, pending_stop: false, dying: false, ..r })
                &&& post.stop_ipis == pre.stop_ipis
            },
        }
    }

    /// Destroys thread t from core c, in one bounded step: see thread_destroyed. Its references,
    /// capabilities, binding nodes and process stay as they were.
    pub fn destroy_thread(&mut self, c: usize, t: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).threads.records@.contains_key(t),
        ensures
            final(self).wf(),
            Self::thread_destroyed(*old(self), *final(self), c, t),
    {
        let ghost pre = *self;
        proof {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let (state, stop) = match record.state {
            ThreadState::Running { core } => {
                if core != c {
                    self.stop_ipis = Ghost(pre.stop_ipis@.push(core));
                }
                (record.state, true)
            },
            _ => (ThreadState::Dead, false),
        };
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state,
            frame: record.frame,
            pending_stop: stop,
            dying: stop,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|e: int, x: usize| 0 <= e < NUM_CPUS && #[trigger] runs(post.cores@, e, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: e as usize })
            } by {
                assert(runs(pre.cores@, e, x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(pre.threads.records@.contains_key(x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, c as int, t);
        }
    }

    /// Core c's current thread must leave user mode: a stop is pending on it, it is marked to die, its
    /// record names no process, or its process is dead.
    pub open spec fn must_leave(&self, c: int) -> bool {
        match self.cores@[c].current_thread {
            Some(t) => {
                let r = self.threads.records@[t].value();
                ||| r.pending_stop
                ||| r.dying
                ||| r.process is None
                ||| self.processes.records@[r.process->Some_0].value().dead
            },
            None => false,
        }
    }

    /// Core c's current thread, if any, may return to user mode: it is Running on c with no stop
    /// pending, not marked to die, and bound to a process that is not dead.
    pub open spec fn current_live(&self, c: int) -> bool {
        match self.cores@[c].current_thread {
            Some(t) => {
                let r = self.threads.records@[t].value();
                &&& self.threads.records@.contains_key(t)
                &&& r.state == (ThreadState::Running { core: c as usize })
                &&& !r.pending_stop
                &&& !r.dying
                &&& r.process is Some
                &&& self.processes.records@.contains_key(r.process->Some_0)
                &&& !self.processes.records@[r.process->Some_0].value().dead
            },
            None => true,
        }
    }

    /// The table at root is not a dead process's. A process's table is rooted at its base, so an
    /// operation on root's table acts within that process. The root comes from the current thread's
    /// process, not from user space, and check_current runs first in the same locked step, so no
    /// operation is reached for a dead process's table: see design/one-lock-bounded-steps/.
    pub open spec fn root_live(&self, root: usize) -> bool {
        self.processes.records@.contains_key(root) ==> !self.processes.records@[root].value().dead
    }

    /// The table of core c's current thread's process is a table, and live, once check_current has
    /// run: the root the dispatch passes to an operation.
    pub proof fn lemma_current_root_live(&self, c: int)
        requires
            self.wf(),
            self.current_live(c),
            self.cores@[c].current_thread is Some,
        ensures
            ({
                let p = self.threads.records@[self.cores@[c].current_thread->Some_0].value().process->Some_0;
                &&& self.tables.roots@.contains_key(p)
                &&& self.root_live(p)
            }),
    {
    }

    /// Core c's check of its current thread on kernel entry and before returning to user mode: one load
    /// of the thread's record and one of its process's. A thread that must leave is moved off: core c
    /// saves the frame it entered with, makes it Inactive, or Dead when it was destroyed while Running,
    /// with no stop pending, and runs nothing. So a thread that destroys itself or its own process does
    /// not return to user mode. Only core c moves its current thread off: see
    /// design/one-lock-bounded-steps/.
    pub fn check_current(&mut self, c: usize, frame: Registers) -> (ret: bool)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            ret == old(self).must_leave(c as int),
            !ret ==> *final(self) == *old(self),
            final(self).current_live(c as int),
            final(self).view() == old(self).view(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret ==> {
                let t = old(self).cores@[c as int].current_thread->Some_0;
                let r = old(self).threads.records@[t].value();
                &&& old(self).threads.records@.contains_key(t)
                &&& r.state == (ThreadState::Running { core: c })
                &&& Self::record_written(*old(self), *final(self), t, ThreadRecord {
                    state: if r.dying { ThreadState::Dead } else { ThreadState::Inactive },
                    frame,
                    pending_stop: false,
                    dying: false,
                    ..r
                })
                &&& final(self).stop_ipis == old(self).stop_ipis
                &&& final(self).cores@.len() == old(self).cores@.len()
                &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).cores@[d] == old(self).cores@[d]
                &&& final(self).cores@[c as int] == CoreState { current_thread: None, ..old(self).cores@[c as int] }
            },
    {
        let ghost pre = *self;
        let state = *self.cores.get(c);
        let t = match state.current_thread {
            Some(t) => t,
            None => { return false; },
        };
        proof {
            reveal(current_wf);
            assert(runs(pre.cores@, c as int, t));
            assert(pre.threads.records@.contains_key(t));
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let leave = if record.pending_stop || record.dying {
            true
        } else {
            match record.process {
                None => true,
                Some(p) => {
                    proof {
                        assert(pre.processes.records@.contains_key(p));
                        assert(process_wf(&pre.processes, &pre.blocks, p));
                    }
                    PPtr::<ProcessRecord>::from_usize(p + PROCESS_RECORD_PAGE * 4096).borrow(
                        Tracked(self.processes.records.borrow().tracked_borrow(p)),
                    ).dead
                },
            }
        };
        if !leave {
            return false;
        }
        self.cores.set(c, CoreState {
            current_thread: None,
            acked_epoch: state.acked_epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            pcids_used: state.pcids_used,
        });
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: if record.dying { ThreadState::Dead } else { ThreadState::Inactive },
            frame,
            pending_stop: false,
            dying: false,
            process: record.process,
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            reveal(current_wf);
            let post = *self;
            assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
            } by {
                assert(d != c);
                assert(post.cores@[d] == pre.cores@[d]);
                assert(runs(pre.cores@, d, x));
                assert(runs(pre.cores@, c as int, t));
                assert(x != t);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(x != t);
                let e = pre.threads.records@[x].value().state->Running_core;
                assert(pre.threads.records@.contains_key(x));
                assert(pre.cores@[e as int].current_thread == Some(x));
                assert(e != c);
                assert(post.cores@[e as int] == pre.cores@[e as int]);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(x != t);
                assert(pre.threads.records@.contains_key(x));
            }
            Self::lemma_switch_wf(pre, post, c as int, t);
            assert(post.view() == pre.view());
        }
        true
    }
}

impl CapKernel {
    /// A thread's base, its binding to its process, is in a page the list holds and in no leaf, table
    /// page or device space, whose blocks are of other objects.
    pub proof fn lemma_thread_node_apart(&self, t: usize)
        requires
            self.wf(),
            self.threads.records@.contains_key(t),
        ensures
            t < NODE_SPACE,
            t % 4096 == 0,
            page_of(t) == t,
            self.list.valid(t),
            !self.tables.owner@.contains_key(t),
            !self.table_pages.maps@.contains_key(t),
            forall|u: usize, k: usize, i: usize| #![trigger table_node(u, k, i)]
                self.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> table_node(u, k, i) != t,
            forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
                self.spaces.roots@.contains_key(s) && self.spaces.records@[s].value().kind is Device
                    && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> table_node(s, k, i) != t,
    {
        assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
        let b = (t / 4096) as int;
        assert(t % 4096 == 0);
        assert(page_of(t) == t);
        assert(t < NODE_SPACE);
        assert(self.blocks.pages@[b].kind is Base);
        assert(self.blocks.pages@[b].object is Thread);
        if self.tables.owner@.contains_key(t) {
            self.tables.lemma_leaf(&self.list, t);
            assert(self.blocks.pages@[(t / 4096) as int].object is TableLeaf);
        }
        if self.table_pages.maps@.contains_key(t) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        }
        assert forall|u: usize, k: usize, i: usize| #![trigger table_node(u, k, i)]
            self.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            implies table_node(u, k, i) != t by {
            if table_node(u, k, i) == t {
                self.lemma_table_node_in_block(u, k, i);
                assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, u));
                let q = (u / 4096) as int;
                assert(b == q + k);
                if k > 0 {
                    self.blocks.lemma_base(q);
                    assert(order_pages(3) == 8);
                    self.blocks.lemma_member_of(q, q + k);
                }
            }
        }
        assert forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
            self.spaces.roots@.contains_key(s) && self.spaces.records@[s].value().kind is Device
                && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            implies table_node(s, k, i) != t by {
            if table_node(s, k, i) == t {
                assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
                let q = (s / 4096) as int;
                self.blocks.lemma_base(q);
                assert(order_pages(3) == 8);
                lemma_table_node_place(s, k, i);
                assert(b == q + k);
                if k > 0 {
                    self.blocks.lemma_member_of(q, q + k);
                }
            }
        }
    }

    /// Index j of the table at root holds a capability to a live process with the control right, below
    /// the depth limit, and the process's block can take one more reference: a thread can be retyped
    /// into that process. A dead process gains no thread, since its block waits for its references to
    /// go: see design/teardown-driven-by-retype/.
    pub open spec fn can_hold_thread(&self, root: usize, j: usize) -> bool {
        let n = self.tables.node_of(root, j);
        &&& self.tables.has_slot(&self.list, root, j)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Process
        &&& !self.cap_dead(n)
        &&& self.payload_of(n).rights & right_bit(Right::Control) != 0
        &&& self.list.nodes@[n as int].depth < MAX_DEPTH
        &&& block_refs(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)) != usize::MAX
    }

    /// Thread t, bound to nothing, is bound to the process capability n names: node t is a binding,
    /// a child of n, the process's block has one reference more, counting t, and t's record names the
    /// process. Nothing else changed.
    pub open spec fn bound_to(pre: Self, post: Self, n: usize, t: usize) -> bool {
        let p = pre.payload_of(n).base;
        let br = BlockRef::Small(p / 4096);
        let r = pre.threads.records@[t].value();
        &&& pre.threads.records@.contains_key(t)
        &&& r.process is None
        &&& post.list.wf()
        &&& post.list.is_child(n, t)
        &&& post.list.parent@ == pre.list.parent@.insert(t, n)
        &&& post.list.pages@.dom() == pre.list.pages@.dom()
        &&& post.list.seq@[0] == pre.list.seq@[0]
        &&& post.list.nodes@[t as int].live
        &&& post.list.nodes@[t as int].kind is Binding
        &&& forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != t ==> {
            &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
            &&& post.list.nodes@[x].kind == pre.list.nodes@[x].kind
        }
        &&& post.blocks.wf()
        &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
        &&& post.processes.records == pre.processes.records
        &&& post.processes.spare == pre.processes.spare
        &&& post.processes.holders == pre.processes.holders
        &&& post.processes.bound@ == pre.processes.bound@.insert(p, pre.processes.bound@[p].insert(t))
        &&& post.threads.holders == pre.threads.holders
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
            ==> post.threads.records@[x] == pre.threads.records@[x]
        &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
        &&& post.threads.records@[t].is_init()
        &&& post.threads.records@[t].value() == ThreadRecord {
            state: r.state,
            frame: r.frame,
            pending_stop: r.pending_stop,
            dying: r.dying,
            process: Some(p),
            placement: r.placement,
        }
        &&& post.holders == pre.holders
        &&& post.tables == pre.tables
        &&& post.frames == pre.frames
        &&& post.zeroing == pre.zeroing
        &&& post.cores == pre.cores
        &&& post.devices == pre.devices
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.iommus == pre.iommus
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.table_pages == pre.table_pages
        &&& post.spaces == pre.spaces
        &&& post.mappings == pre.mappings
    }

    /// The kinds of node after a bind: the new node is a binding, outside every leaf, table page and
    /// device space, so no clause about capability, hidden, table or space nodes changes.
    proof fn lemma_bind_nodes(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            pre.is_cap(n),
            !pre.list.nodes@[t as int].live,
            Self::bound_to(pre, post, n, t),
        ensures
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            Self::caps_frame(pre, post, t, t),
            post.tables.wf(&post.list),
            post.tables.caps_wf(&post.list),
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
            capability_nodes_are_slots(&post.list, &post.tables),
            first_node_outside_leaves(&post.list, &post.tables),
            leaf_slots_are_capabilities(&post.list, &post.tables),
            table_nodes_are_mappings(&post.list, &post.table_pages),
            space_nodes_dead(&post.list, &post.spaces),
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        pre.lemma_thread_node_apart(t);
        pre.lemma_slot_bound(n);
        assert(Self::caps_frame(pre, post, t, t));
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            if x == t {
                assert(!(post.list.nodes@[x as int].kind is Capability));
            } else {
                Self::lemma_caps_frame(pre, post, t, t, x);
            }
        }
        pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x)
            implies cap_wf(post.tables.payload_of(x)) by {
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            assert(x != t);
            assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Hidden);
        }
        lemma_parents_derived(pre.list, post.list, n, t);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Capability
            && x != post.list.seq@[0] implies post.tables.is_cap(&post.list, x) by {
            assert(x != t);
            assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Capability);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|x: usize| #[trigger] post.list.nodes@[x as int].live && post.tables.owner@.contains_key(page_of(x))
            && x % 4096 != 0 && x % 4096 < NODES_PER_PAGE implies post.list.nodes@[x as int].kind is Capability by {
            assert(x != t);
            pre.lemma_slot_bound(x);
            assert(pre.list.nodes@[x as int].live);
        }
        assert forall|u: usize, k: usize, i: usize| #![trigger table_node(u, k, i)]
            post.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE && (k != 0 || i != 0)
                && post.list.nodes@[table_node(u, k, i) as int].live
            implies post.list.nodes@[table_node(u, k, i) as int].kind is Mapping by {
            pre.lemma_table_node_in_block(u, k, i);
            assert(table_node(u, k, i) != t);
        }
        assert forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
            post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device && k < TABLE_NODE_PAGES
                && i < NODES_PER_PAGE
            implies !post.list.nodes@[table_node(s, k, i) as int].live by {
            pre.lemma_space_node_in_block(s, k, i);
            assert(table_node(s, k, i) != t);
        }
        Self::lemma_devices_same_caps(pre, post);
    }

    /// The counted parts after a bind: the process's block has one reference more, counted among its
    /// bindings, and no capability, holder, leaf, table page or mapping changed.
    proof fn lemma_bind_objects(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            pre.is_cap(n),
            pre.payload_of(n).kind is Process,
            !pre.list.nodes@[t as int].live,
            block_refs(&pre.blocks, BlockRef::Small(pre.payload_of(n).base / 4096)) != usize::MAX,
            Self::bound_to(pre, post, n, t),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
            bindings_wf(&post.list, &post.threads, &post.processes),
            current_wf(post.cores@, post.threads.records@),
    {
        let p = pre.payload_of(n).base;
        let br = BlockRef::Small(p / 4096);
        let refs = (block_refs(&pre.blocks, br) + 1) as usize;
        let dead = block_dead(&pre.blocks, br);
        Self::lemma_bind_nodes(pre, post, n, t);
        pre.lemma_thread_node_apart(t);
        pre.lemma_process_cap(n);
        assert forall|x: usize| x != t implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, t, t, x);
        }
        assert(!pre.is_cap(t));
        assert(!post.is_cap(t));
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert(same_frames(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_threads(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_processes(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        assert(!pre.holders@.contains_key(br)) by {
            if pre.holders@.contains_key(br) {
                assert(pre.blocks.pages@[(p / 4096) as int].object is Frame);
            }
        }
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, p / 4096, refs, dead);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, p / 4096, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, p / 4096, refs, dead);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            pre.lemma_slot_bound(l);
            assert(l != t);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, p / 4096, refs, dead);
        assert forall|u: usize| #[trigger] pre.table_pages.maps@.contains_key(u) implies {
            &&& post.list.nodes@[u as int].live == pre.list.nodes@[u as int].live
            &&& post.list.nodes@[u as int].kind == pre.list.nodes@[u as int].kind
        } by {
            pre.lemma_table_page_valid(u);
            assert(u != t);
        }
        lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_threads_record_written(&post.list, &post.tables, &pre.threads, &post.threads, &post.blocks, t);
        lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
        assert(!pre.processes.bound@[p].contains(t)) by {
            if pre.processes.bound@[p].contains(t) {
                assert(pre.threads.records@[t].value().process == Some(p));
            }
        }
        lemma_processes_bound_added(&post.list, &post.tables, &pre.processes, &post.processes, &pre.blocks, &post.blocks, p, t);
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
            let c = pre.list.parent@[m];
            assert(m != t);
            assert(c != t);
            Self::lemma_caps_frame(pre, post, t, t, c);
        }
        Self::lemma_mappings_same_tree(pre, post);
        lemma_bindings_bound(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes, t, p);
        lemma_current_same(pre.cores@, post.cores@, pre.threads.records@, post.threads.records@);
    }

    /// The binding parents after a bind: the new binding's parent is the process capability n, whose
    /// process its thread's record now names, and no other binding, parent or capability changed.
    proof fn lemma_bind_parents(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            pre.is_cap(n),
            pre.payload_of(n).kind is Process,
            !pre.list.nodes@[t as int].live,
            Self::bound_to(pre, post, n, t),
        ensures
            binding_parents(&post.list, &post.tables, &post.threads),
    {
        reveal(binding_parents);
        Self::lemma_bind_nodes(pre, post, n, t);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Binding
            implies binding_parent(&post.list, &post.tables, &post.threads, x) by {
            if x == t {
                assert(post.is_cap(n));
                assert(post.list.parent@[t] == n);
                assert(post.threads.records@.contains_key(t));
            } else {
                assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Binding);
                assert(binding_parent(&pre.list, &pre.tables, &pre.threads, x));
                let a = pre.list.parent@[x];
                assert(pre.is_cap(a));
                assert(post.is_cap(a));
                assert(post.list.parent@[x] == a);
                assert(pre.threads.records@.contains_key(x));
                assert(post.threads.records@.contains_key(x));
                assert(post.threads.records@[x] == pre.threads.records@[x]);
            }
        }
    }

    /// Everything the invariant says after a bind.
    proof fn lemma_bind_wf(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            pre.is_cap(n),
            pre.payload_of(n).kind is Process,
            !pre.list.nodes@[t as int].live,
            block_refs(&pre.blocks, BlockRef::Small(pre.payload_of(n).base / 4096)) != usize::MAX,
            Self::bound_to(pre, post, n, t),
        ensures
            post.wf(),
    {
        Self::lemma_bind_nodes(pre, post, n, t);
        Self::lemma_bind_objects(pre, post, n, t);
        Self::lemma_bind_parents(pre, post, n, t);
        Self::lemma_tlb_same(pre, post);
        assert(process_tables_wf(&post.tables, &post.processes));
        assert(post.frames_wf());
    }

    /// Finds the process capability at index j, which a thread is retyped into. The index comes from
    /// user space.
    fn process_slot(&self, root: usize, j: usize) -> (ret: Option<usize>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret is Some == self.can_hold_thread(root, j),
            ret is Some ==> ret->0 == self.tables.node_of(root, j),
    {
        let (n, cap) = match self.tables.lookup(&self.list, root, j) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return None;
        }
        proof {
            self.lemma_slot(root, j);
            assert(self.tables.is_cap(&self.list, n));
            assert(cap == self.payload_of(n));
        }
        let process = match cap.kind {
            CapKind::Process => true,
            _ => false,
        };
        if !process || cap.rights & 128 == 0 || node.depth >= MAX_DEPTH {
            return None;
        }
        proof {
            assert(right_bit(Right::Control) == 128);
            self.lemma_process_cap(n);
        }
        if self.is_cap_dead(n, cap) {
            return None;
        }
        if self.blocks.pages.get(cap.base / 4096).refs == usize::MAX {
            return None;
        }
        Some(n)
    }

    /// Binds thread t, bound to nothing, to the process capability n names: node t, the first of the
    /// thread's node page, becomes a binding below n, holding a reference on the process's block. Only
    /// retype_thread and the boot step that makes the root thread call it, on the thread just typed.
    /// See design/thread-bound-at-retype/.
    pub fn bind_thread(&mut self, n: usize, t: usize)
        requires
            old(self).wf(),
            old(self).is_cap(n),
            old(self).payload_of(n).kind is Process,
            old(self).list.nodes@[n as int].depth < MAX_DEPTH,
            block_refs(&old(self).blocks, BlockRef::Small(old(self).payload_of(n).base / 4096)) != usize::MAX,
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().process is None,
            !old(self).list.nodes@[t as int].live,
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).spaces == old(self).spaces,
            final(self).wf(),
            Self::bound_to(*old(self), *final(self), n, t),
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            forall|x: int| #![trigger final(self).list.nodes@[x]] 0 <= x < NODE_SPACE && x != t
                ==> final(self).list.nodes@[x].depth == old(self).list.nodes@[x].depth,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|i: int| old(self).blocks.tracks(i) ==> (#[trigger] final(self).blocks.pages@[i]).dead == old(self).blocks.pages@[i].dead,
            forall|i: int| i != (old(self).payload_of(n).base / 4096) as int
                ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i],
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_process_cap(n);
            pre.lemma_thread_node_apart(t);
            pre.list.lemma_seq_fits();
            pre.lemma_slot_bound(n);
        }
        let p = self.tables.payload_at(&self.list, n).base;
        let added = add_block_ref(&mut self.blocks, BlockRef::Small(p / 4096));
        assert(added);
        self.list.derive(n, t, NodeKind::Binding);
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
        let tracked mut perm;
        proof {
            perm = self.threads.records.borrow_mut().tracked_remove(t);
        }
        ptr.write(Tracked(&mut perm), ThreadRecord {
            state: record.state,
            frame: record.frame,
            pending_stop: record.pending_stop,
            dying: record.dying,
            process: Some(p),
            placement: record.placement,
        });
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, perm);
            assert(self.threads.records@.dom() =~= pre.threads.records@.dom());
        }
        self.processes.bound = Ghost(pre.processes.bound@.insert(p, pre.processes.bound@[p].insert(t)));
        proof {
            let post = *self;
            assert(Self::bound_to(pre, post, n, t));
            Self::lemma_bind_wf(pre, post, n, t);
            Self::lemma_bind_nodes(pre, post, n, t);
        }
    }
}

} // verus!
