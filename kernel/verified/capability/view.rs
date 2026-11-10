//! The kernel as reach sees it. Every capability operation's spec states discharges over this view,
//! so what a process holds, what each capability names and which rights it carries are read from the
//! tables here and nowhere else. The fields for mappings, threads and object contents stay empty until
//! the objects behind them exist. See design/theorem-over-reach/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::define::*;

/// The bit of a capability's rights word that grants this right.
pub open spec fn right_bit(right: Right) -> u32 {
    match right {
        Right::Read => 1,
        Right::Write => 2,
        Right::Execute => 4,
        Right::Retype => 8,
        Right::Send => 16,
        Right::Receive => 32,
        Right::Grant => 64,
        Right::Control => 128,
    }
}

/// Each thread bound to a process, read from its binding node: a live binding node's parent is a
/// capability to the process the thread is bound to. Read from the list and the tables alone, as
/// view_of is. See design/process-holds-capabilities/.
pub open spec fn bound_threads(list: &Tree, tables: &Tables) -> Map<ObjectId, ObjectId> {
    Map::new(
        Set::range(0usize, NODE_SPACE).filter(|t: usize| list.nodes@[t as int].live && list.nodes@[t as int].kind is Binding),
        |t: usize| tables.payload_of(list.parent@[t]).base,
    )
}

/// The nodes live in list, as bound_threads reads them.
pub open spec fn live_nodes(list: &Tree) -> Set<usize> {
    Set::range(0usize, NODE_SPACE).filter(|t: usize| list.nodes@[t as int].live)
}

/// The process thread t's record names, if t has a record and it names one.
pub open spec fn thread_process(threads: &Threads, t: usize) -> Option<ObjectId> {
    if threads.records@.contains_key(t) { threads.records@[t].value().process } else { None }
}

/// The process each thread's record names.
pub open spec fn record_processes(threads: &Threads) -> Map<ObjectId, ObjectId> {
    Map::new(
        threads.records@.dom().filter(|t: usize| thread_process(threads, t) is Some),
        |t: usize| thread_process(threads, t)->Some_0,
    )
}

/// t is in the record-named map exactly when its record names a process, and maps to that process.
pub proof fn lemma_record_processes(threads: &Threads, t: usize)
    ensures
        record_processes(threads).dom().contains(t) == thread_process(threads, t) is Some,
        thread_process(threads, t) is Some ==> record_processes(threads)[t] == thread_process(threads, t)->Some_0,
{
    broadcast use vstd::set::lemma_set_filter;
}

/// The bound threads are those whose binding node is live.
pub proof fn lemma_bound_threads_live(list: &Tree, tables: &Tables)
    ensures
        bound_threads(list, tables) == bound_threads(list, tables).restrict(live_nodes(list)),
{
    broadcast use vstd::set::lemma_set_filter;
    assert(bound_threads(list, tables) =~= bound_threads(list, tables).restrict(live_nodes(list)));
}

/// What the view reads: nothing but the list and the tables, so a step that leaves those alone leaves
/// the view alone.
pub open spec fn view_of(list: &Tree, tables: &Tables) -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)|
            tables.is_cap(list, h.1) && tables.owner@[page_of(h.1)].0 == h.0),
        names: IMap::new(|n: NodeId| tables.is_cap(list, n), |n: NodeId| tables.payload_of(n).base),
        pages: IMap::new(|n: NodeId| tables.is_cap(list, n), |n: NodeId| pow2(tables.payload_of(n).order as nat)),
        rights: ISet::new(|h: (NodeId, Right)|
            tables.is_cap(list, h.0) && tables.payload_of(h.0).rights & right_bit(h.1) != 0),
        parent: list.parent@,
        maps: Set::empty(),
        process_of: Map::empty(),
        waiting: Set::empty(),
        bound: Map::empty(),
        shares: Set::empty(),
        binds: Map::empty(),
        contents: |o: ObjectId| Seq::empty(),
    }
}

impl CapKernel {
    pub open spec fn is_cap(&self, n: usize) -> bool {
        self.tables.is_cap(&self.list, n)
    }

    pub open spec fn payload_of(&self, n: usize) -> Payload {
        self.tables.payload_of(n)
    }

    pub open spec fn view(&self) -> State {
        view_of(&self.list, &self.tables)
    }

    /// Where a node in a leaf's page lies.
    pub proof fn lemma_slot_bound(&self, n: usize)
        requires
            self.wf(),
            self.tables.owner@.contains_key(page_of(n)),
            n % PAGE_SZ < NODES_PER_PAGE,
        ensures
            n < NODE_SPACE,
            self.list.valid(n),
    {
        self.tables.lemma_leaf(&self.list, page_of(n));
        self.list.lemma_valid_bound(n);
    }

    /// Where the node of a slot lies, and whose it is.
    pub proof fn lemma_slot(&self, root: usize, i: usize)
        requires
            self.wf(),
            self.tables.has_slot(&self.list, root, i),
        ensures
            self.tables.owner@.contains_key(page_of(self.tables.node_of(root, i))),
            self.tables.owner@[page_of(self.tables.node_of(root, i))].0 == root,
            self.tables.node_of(root, i) % PAGE_SZ == index_slot(i),
            0 < index_slot(i) < NODES_PER_PAGE,
            page_of(self.tables.node_of(root, i)) == self.tables.leaf(root, index_entry(i)),
    {
        let leaf = self.tables.leaf(root, index_entry(i));
        self.tables.lemma_entry(root, index_entry(i));
        self.tables.lemma_leaf(&self.list, leaf);
        let n = self.tables.node_of(root, i);
        assert(leaf % PAGE_SZ == 0);
        assert(n % PAGE_SZ == index_slot(i));
        assert(page_of(n) == leaf);
    }

    /// Index i of the table at root is a slot, of node n, and n is a capability saying p.
    pub open spec fn slot_holds(&self, root: usize, i: usize, n: usize, p: Payload) -> bool {
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.tables.node_of(root, i) == n
        &&& self.is_cap(n)
        &&& self.payload_of(n) == p
    }

    /// A slot stays a slot of the same node while the tables' roots stay and no live node dies.
    pub proof fn lemma_slot_stays(pre: Self, post: Self, root: usize, i: usize)
        requires
            pre.wf(),
            pre.tables.has_slot(&pre.list, root, i),
            post.tables.roots == pre.tables.roots,
            forall|j: int| 0 <= j < NODE_SPACE && #[trigger] pre.list.nodes@[j].live ==> post.list.nodes@[j].live,
        ensures
            post.tables.has_slot(&post.list, root, i),
            post.tables.node_of(root, i) == pre.tables.node_of(root, i),
    {
        pre.lemma_slot(root, i);
        let n = pre.tables.node_of(root, i);
        pre.lemma_slot_bound(n);
        let leaf = pre.tables.leaf(root, index_entry(i));
        assert(leaf == page_of(n));
        assert(leaf <= n);
        assert(pre.list.nodes@[leaf as int].live);
    }

    /// A live capability in a slot is held by that table's process.
    pub proof fn lemma_slot_is_held(&self, root: usize, i: usize)
        requires
            self.wf(),
            self.tables.has_slot(&self.list, root, i),
            self.list.nodes@[self.tables.node_of(root, i) as int].live,
            self.list.nodes@[self.tables.node_of(root, i) as int].kind is Capability,
        ensures
            self.view().holds(root, self.tables.node_of(root, i)),
    {
        self.lemma_slot(root, i);
    }

    /// Between pre and post, no node but n and m changed its liveness or kind, and no capability but
    /// those what it says.
    pub open spec fn caps_frame(pre: Self, post: Self, n: usize, m: usize) -> bool {
        &&& pre.wf()
        &&& post.tables.owner == pre.tables.owner
        &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != n && i != m ==> {
            &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
            &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
        }
        &&& forall|x: usize| #![trigger post.tables.payload_of(x)]
            x != n && x != m && x % PAGE_SZ < NODES_PER_PAGE && pre.tables.owner@.contains_key(page_of(x))
            ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
    }

    /// So any other node is a capability after exactly when it was before, saying the same.
    pub proof fn lemma_caps_frame(pre: Self, post: Self, n: usize, m: usize, x: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            x != n,
            x != m,
        ensures
            post.is_cap(x) == pre.is_cap(x),
            pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
    {
        if pre.tables.owner@.contains_key(page_of(x)) && x % PAGE_SZ < NODES_PER_PAGE {
            pre.lemma_slot_bound(x);
            assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
            assert(post.tables.payload_of(x) == pre.tables.payload_of(x));
        }
    }

    /// The step changed no node's kind or liveness but n's and m's. They are slots, so neither is a
    /// leaf's first node, and neither is now a live hidden node, so the hidden nodes are as they were.
    pub proof fn lemma_hidden_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            post.table_pages == pre.table_pages,
            n % PAGE_SZ != 0,
            m % PAGE_SZ != 0,
            !(post.list.nodes@[n as int].live && post.list.nodes@[n as int].kind is Hidden),
            !(post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Hidden),
            post.list.nodes@[n as int].live && post.list.nodes@[n as int].kind is Capability
                && n != post.list.seq@[0] ==> post.is_cap(n),
            post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Capability
                && m != post.list.seq@[0] ==> post.is_cap(m),
            post.list.seq@[0] == pre.list.seq@[0] || pre.list.seq@[0] == n || pre.list.seq@[0] == m,
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            capability_nodes_are_slots(&post.list, &post.tables),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            assert(x != n && x != m);
            assert(pre.list.nodes@[x as int].live);
        }
    }

    /// An ancestor by the list is an ancestor by the view: each link is a parent the map holds.
    pub proof fn lemma_anc_descends(&self, r: usize, n: nat)
        requires
            self.list.wf(),
            has(self.list.seq@, r),
            n <= self.list.d(r),
        ensures
            self.view().descends(self.list.anc(r, n), r, n),
        decreases n,
    {
        if n > 0 {
            let s = self.list.seq@;
            lemma_has(s, r);
            let k = choose|k: int| 0 <= k < s.len() && s[k] == r;
            assert(k != 0);
            assert(self.list.parent@.contains_key(s[k]));
            assert(has(s, self.list.parent@[s[k]]));
            assert(self.list.d(r) == self.list.d(self.list.parent@[r]) + 1);
            self.lemma_anc_descends(self.list.parent@[r], (n - 1) as nat);
        }
    }

    /// What the view holds, a table has: a slot that is not live is held by nobody.
    pub proof fn lemma_held_is_live(&self, p: ObjectId, n: NodeId)
        requires
            self.view().holds(p, n),
        ensures
            self.list.nodes@[n as int].live,
            self.tables.owner@.contains_key(page_of(n)),
            self.tables.owner@[page_of(n)].0 == p,
    {
    }

    /// A capability that names a block names one within the address space, so it covers no device, not
    /// the console and not power: each is reached only through its own capability.
    pub proof fn lemma_covers_no_device(&self, n: usize, o: ObjectId)
        requires
            self.wf(),
            self.is_cap(n),
            names_block(self.payload_of(n).kind),
            self.view().covers(n, o),
        ensures
            o < DEVICE_OBJECTS,
    {
    }

    /// The console's capability covers the console's page alone and a power capability power's page
    /// alone, each past memory and every device object, and no other capability covers either page.
    pub proof fn lemma_covers_console_or_power(&self, n: usize, o: ObjectId)
        requires
            self.wf(),
            self.is_cap(n),
            self.view().covers(n, o),
        ensures
            self.payload_of(n).kind is Console ==> o == CONSOLE_OBJECT,
            self.payload_of(n).kind is Power ==> o == POWER_OBJECT,
            self.payload_of(n).kind is Console || self.payload_of(n).kind is Power ==> DEVICE_OBJECTS <= o,
            self.payload_of(n).kind is Console || self.payload_of(n).kind is Power
                ==> forall|d: int| 0 <= d < MAX_DEVICES ==> o != #[trigger] device_object(d),
            !(self.payload_of(n).kind is Console) ==> o != CONSOLE_OBJECT,
            !(self.payload_of(n).kind is Power) ==> o != POWER_OBJECT,
    {
        let p = self.payload_of(n);
        if p.kind is Device {
            reveal(devices_wf);
            assert(devices_wf(&self.list, &self.tables, &self.devices));
            assert(self.devices.count <= MAX_DEVICES);
            let x = (p.base - DEVICE_OBJECTS) as int;
            assert(x / (PAGE_SZ as int) < MAX_DEVICES);
            assert(x < MAX_DEVICES * PAGE_SZ) by (nonlinear_arith)
                requires x / (PAGE_SZ as int) < MAX_DEVICES, x >= 0;
            assert(pow2(0) == 1) by { lemma2_to64(); }
        } else if p.kind is Console || p.kind is Power {
            assert(pow2(0) == 1) by { lemma2_to64(); }
        }
    }

    /// The binding nodes name what the thread records name: bindings_wf makes a live binding node
    /// exactly a bound thread, and binding_parents makes its parent a capability to that process.
    pub proof fn lemma_bound_threads(&self)
        requires
            self.wf(),
        ensures
            bound_threads(&self.list, &self.tables) == record_processes(&self.threads),
    {
        broadcast use vstd::set::lemma_set_filter;
        let b = bound_threads(&self.list, &self.tables);
        let r = record_processes(&self.threads);
        assert forall|t: usize| #[trigger] b.dom().contains(t) == r.dom().contains(t) by {
            lemma_record_processes(&self.threads, t);
            if t < NODE_SPACE && self.list.nodes@[t as int].live && self.list.nodes@[t as int].kind is Binding {
                self.lemma_binding_parent(t);
            }
            if self.threads.records@.contains_key(t) && self.threads.records@[t].value().process is Some {
                assert(t < NODE_SPACE && self.list.nodes@[t as int].live);
            }
        }
        assert forall|t: usize| #[trigger] b.dom().contains(t) implies b[t] == r[t] by {
            lemma_record_processes(&self.threads, t);
            self.lemma_binding_parent(t);
        }
        assert(b =~= r);
    }

    /// Two states whose thread records name the same process for every thread have the same bound
    /// threads.
    pub proof fn lemma_bound_threads_same(pre: Self, post: Self)
        requires
            pre.wf(),
            post.wf(),
            forall|t: usize| #[trigger] thread_process(&post.threads, t) == thread_process(&pre.threads, t),
        ensures
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
    {
        pre.lemma_bound_threads();
        post.lemma_bound_threads();
        assert forall|x: usize|
            #[trigger] record_processes(&post.threads).dom().contains(x) == record_processes(&pre.threads).dom().contains(x)
            && (record_processes(&post.threads).dom().contains(x)
                ==> record_processes(&post.threads)[x] == record_processes(&pre.threads)[x]) by {
            lemma_record_processes(&pre.threads, x);
            lemma_record_processes(&post.threads, x);
        }
        assert(record_processes(&post.threads) =~= record_processes(&pre.threads));
    }

    /// A step whose thread records gain exactly t bound to p gains exactly t -> p.
    pub proof fn lemma_bound_threads_insert(pre: Self, post: Self, t: usize, p: ObjectId)
        requires
            pre.wf(),
            post.wf(),
            thread_process(&post.threads, t) == Some(p),
            forall|x: usize| x != t ==> #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x),
        ensures
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables).insert(t, p),
    {
        pre.lemma_bound_threads();
        post.lemma_bound_threads();
        let a = record_processes(&pre.threads).insert(t, p);
        assert forall|x: usize|
            #[trigger] record_processes(&post.threads).dom().contains(x) == a.dom().contains(x)
            && (a.dom().contains(x) ==> record_processes(&post.threads)[x] == a[x]) by {
            lemma_record_processes(&pre.threads, x);
            lemma_record_processes(&post.threads, x);
        }
        assert(record_processes(&post.threads) =~= a);
    }

    /// A step whose thread records lose exactly t's process loses exactly t.
    pub proof fn lemma_bound_threads_remove(pre: Self, post: Self, t: usize)
        requires
            pre.wf(),
            post.wf(),
            thread_process(&post.threads, t) is None,
            forall|x: usize| x != t ==> #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x),
        ensures
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables).remove(t),
    {
        pre.lemma_bound_threads();
        post.lemma_bound_threads();
        let a = record_processes(&pre.threads).remove(t);
        assert forall|x: usize|
            #[trigger] record_processes(&post.threads).dom().contains(x) == a.dom().contains(x)
            && (a.dom().contains(x) ==> record_processes(&post.threads)[x] == a[x]) by {
            lemma_record_processes(&pre.threads, x);
            lemma_record_processes(&post.threads, x);
        }
        assert(record_processes(&post.threads) =~= a);
    }

    /// A step that changes nothing discharges the lemma.
    pub proof fn lemma_no_op_discharges(&self, p: ObjectId)
        ensures
            discharges(self.view(), self.view(), p, Effect::Local),
    {
    }
}

} // verus!
