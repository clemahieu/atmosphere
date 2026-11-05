//! The kernel as reach sees it. Every capability operation's spec states discharges over this view,
//! so what a process holds, what each capability names and which rights it carries are read from the
//! tables here and nowhere else. The fields for mappings, threads and object contents stay empty until
//! the objects behind them exist. See the design on atmo-6x9.6.7, section 15.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::table::*;

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

impl CapKernel {
    pub open spec fn is_cap(&self, n: usize) -> bool {
        self.tables.is_cap(&self.list, n)
    }

    pub open spec fn payload_of(&self, n: usize) -> Payload {
        self.tables.payload_of(n)
    }

    pub open spec fn view(&self) -> State {
        State {
            held: ISet::new(|h: (ObjectId, NodeId)|
                self.is_cap(h.1) && self.tables.owner@[page_of(h.1)].0 == h.0),
            names: IMap::new(|n: NodeId| self.is_cap(n), |n: NodeId| self.payload_of(n).base),
            pages: IMap::new(|n: NodeId| self.is_cap(n), |n: NodeId| pow2(self.payload_of(n).order as nat)),
            rights: ISet::new(|h: (NodeId, Right)|
                self.is_cap(h.0) && self.payload_of(h.0).rights & right_bit(h.1) != 0),
            parent: self.list.parent@,
            maps: Set::empty(),
            process_of: Map::empty(),
            waiting: Set::empty(),
            bound: Map::empty(),
            dead: Set::empty(),
            contents: |o: ObjectId| Seq::empty(),
        }
    }

    /// Where a node in a leaf's page lies.
    pub proof fn lemma_slot_bound(&self, n: usize)
        requires
            self.wf(),
            self.tables.owner@.contains_key(page_of(n)),
            n % 4096 < NODES_PER_PAGE,
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
            self.tables.has_slot(root, i),
        ensures
            self.tables.owner@.contains_key(page_of(self.tables.node_of(root, i))),
            self.tables.owner@[page_of(self.tables.node_of(root, i))].0 == root,
            self.tables.node_of(root, i) % 4096 == index_slot(i),
            0 < index_slot(i) < NODES_PER_PAGE,
            page_of(self.tables.node_of(root, i)) == self.tables.leaf(root, index_entry(i)),
    {
        let leaf = self.tables.leaf(root, index_entry(i));
        self.tables.lemma_entry(root, index_entry(i));
        self.tables.lemma_leaf(&self.list, leaf);
        let n = self.tables.node_of(root, i);
        assert(leaf % 4096 == 0);
        assert(n % 4096 == index_slot(i));
        assert(page_of(n) == leaf);
    }

    /// A live capability in a slot is held by that table's process.
    pub proof fn lemma_slot_is_held(&self, root: usize, i: usize)
        requires
            self.wf(),
            self.tables.has_slot(root, i),
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
            x != n && x != m && x % 4096 < NODES_PER_PAGE && pre.tables.owner@.contains_key(page_of(x))
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
        if pre.tables.owner@.contains_key(page_of(x)) && x % 4096 < NODES_PER_PAGE {
            pre.lemma_slot_bound(x);
            assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
            assert(post.tables.payload_of(x) == pre.tables.payload_of(x));
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

    /// A step that changes nothing discharges the lemma.
    pub proof fn lemma_no_op_discharges(&self, p: ObjectId)
        ensures
            discharges(self.view(), self.view(), p, Effect::Local),
    {
    }
}

} // verus!
