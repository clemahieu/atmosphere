//! Retype reclaiming a dead process's block: a retype cuts its address space root's child tables, then
//! detaches its capability table root's leaves, a slice per step, each detached two-way so the child's
//! parent record goes with the entry. Both roots are inside the process's block, so they go only with
//! the process, once no core has the space loaded. A root maps no frame, so it holds no mapping node to
//! unlink, and a detached leaf keeps its owner and its hidden node, inert until its own untyped's holder
//! retypes it. See design/teardown-driven-by-retype/.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::device::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::mapping::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// The entries of the capability table at `root` that name a leaf.
pub open spec fn leaf_entries(tables: &Tables, root: usize) -> Set<usize> {
    Set::<usize>::range(0, ROOT_ENTRIES).filter(|r: usize| tables.leaf(root, r as int) != NO_LEAF)
}

pub proof fn lemma_leaf_entries(tables: &Tables, root: usize, r: usize)
    ensures
        leaf_entries(tables, root).contains(r) <==> r < ROOT_ENTRIES && tables.leaf(root, r as int) != NO_LEAF,
{
    broadcast use vstd::set::lemma_set_filter;
    vstd::set_lib::range_set_properties::<usize>(0, ROOT_ENTRIES);
}

impl CapKernel {
    /// The process at `base` is dead with zero references: no capability names it and no thread is
    /// bound to it.
    pub open spec fn process_is_dead(&self, base: usize) -> bool {
        &&& self.processes.records@.contains_key(base)
        &&& self.blocks.pages@[(base / 4096) as int].refs == 0
    }

    /// No core has the space of the process at `base` on its loaded list, so none holds a translation
    /// of it.
    pub open spec fn process_unloaded(&self, base: usize) -> bool {
        self.spaces.loaded@[base].value().list == 0u32
    }

    /// A retype may cut a child table of the dead process at `base`'s space root: an untyped covers its
    /// block, no core has its space loaded, an entry of the root still names a child and the flush
    /// epoch can rise.
    pub open spec fn can_cut_process_space(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, PROCESS_ORDER)
        &&& self.process_is_dead(base)
        &&& self.process_unloaded(base)
        &&& exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
        &&& self.flush_epoch < usize::MAX
    }

    /// What cutting children of the dead process at `base`'s space root did to self: as for a table
    /// page; the kernel slots are as they were; every table page's parent record names a table or
    /// nothing; and the process is still dead and unloaded.
    pub open spec fn process_space_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let a = tree_of(&self.table_pages, &self.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        &&& self.table_children_cut(post, root, from, base)
        &&& forall|i: usize| #![trigger b.entry(base, i)] i < KERNEL_MEM_END_L4INDEX ==> b.entry(base, i) == a.entry(base, i)
        &&& forall|c: usize| #![trigger b.record(c)]
            b.is_page(c) && b.record(c).parent is Some ==> b.is_table(b.record(c).parent->Some_0.table)
        &&& post.process_is_dead(base)
        &&& post.process_unloaded(base)
    }

    /// A retype may detach a leaf of the dead process at `base`'s capability table: an untyped covers its
    /// block, no core has its space loaded, and an entry of the table's root still names a leaf.
    pub open spec fn can_detach_process_leaves(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, PROCESS_ORDER)
        &&& self.process_is_dead(base)
        &&& self.process_unloaded(base)
        &&& exists|r: int| 0 <= r < ROOT_ENTRIES && #[trigger] self.tables.leaf(base, r) != NO_LEAF
    }

    /// What detaching leaves of the dead process at `base`'s table did to self: only the tables
    /// changed, each leaf keeping its owner; fewer of the root's entries name a leaf, by at least one and
    /// by at most the budget, and no entry came to name one; every attached leaf's parent record names a
    /// root the tables hold; the view is as it was; and the process is still dead and unloaded.
    pub open spec fn process_leaves_detached(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let a = leaf_entries(&self.tables, base);
        let b = leaf_entries(&post.tables, base);
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& post == (CapKernel { tables: post.tables, ..*self })
        &&& post.tables.owner == self.tables.owner
        &&& post.tables.roots@.dom() == self.tables.roots@.dom()
        &&& b.subset_of(a)
        &&& b.len() < a.len()
        &&& a.len() - b.len() <= TABLE_SLICE_BUDGET
        &&& forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) && post.tables.attached(l)
            ==> post.tables.roots@.contains_key(post.tables.record(l).base)
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
        &&& post.process_is_dead(base)
        &&& post.process_unloaded(base)
    }

    /// A block at an order-3 base holds a process exactly when a process record is kept there, and a
    /// process's space is a root of kind Process with no parent at level 4, which no table page shares.
    pub proof fn lemma_process_block(&self, base: usize)
        requires
            self.wf(),
            base % 32768 == 0,
            base / 4096 < NUM_PAGES,
        ensures
            process_block(&self.blocks, base / 4096) == self.processes.records@.contains_key(base),
            self.processes.records@.contains_key(base) ==> {
                &&& self.spaces.roots@.contains_key(base)
                &&& self.spaces.records@[base].value().kind is Process
                &&& self.spaces.loaded@.contains_key(base)
                &&& self.spaces.loaded@[base].addr() == base + SPACE_CORES_PAGE * 4096
                &&& self.spaces.loaded@[base].is_init()
                &&& !self.table_pages.maps@.contains_key(base)
                &&& tree_of(&self.table_pages, &self.spaces).record(base).parent is None
                &&& tree_of(&self.table_pages, &self.spaces).record(base).level == 4
            },
    {
        assert(base % 32768 == 0 ==> base % 8192 == 0) by (bit_vector);
        lemma_leaf_page(base);
        if process_block(&self.blocks, base / 4096) {
            assert(self.processes.records@.contains_key(((base / 4096) * 4096) as usize));
        }
        if self.processes.records@.contains_key(base) {
            assert(process_wf(&self.processes, &self.blocks, base));
            assert(self.spaces.roots@.contains_key(base));
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
            self.lemma_space_block(base);
        }
    }

    /// A process record is kept only at a block typed as a process.
    pub proof fn lemma_process_object(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.processes.records@.contains_key(base) ==> {
                &&& base % 32768 == 0
                &&& base / 4096 < NUM_PAGES
                &&& self.blocks.pages@[(base / 4096) as int].object is Process
            },
    {
        if self.processes.records@.contains_key(base) {
            assert(process_wf(&self.processes, &self.blocks, base));
        }
    }

    /// No core has an unloaded process space loaded, so no core holds a translation of it.
    pub proof fn lemma_process_unloaded(&self, base: usize)
        requires
            self.wf(),
            self.spaces.loaded@.contains_key(base),
            self.process_unloaded(base),
        ensures
            forall|d: int| 0 <= d < NUM_CPUS ==> !#[trigger] self.loaded(d, base),
            forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base ==> !#[trigger] self.tlb@[d].contains(e),
    {
        assert forall|d: int| 0 <= d < NUM_CPUS implies !#[trigger] self.loaded(d, base) by {
            lemma_no_core_listed(d as u32);
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base implies !#[trigger] self.tlb@[d].contains(e) by {
            assert(!self.loaded(d, base));
        }
    }

    /// Cuts up to a budget of the child tables of the dead process at `base`'s space root, under the
    /// untyped at index `from` of the table at `root`, each from the entry naming it, with what that
    /// leaves stale, and leaves the kernel slots. Refused while a core has the space loaded. Returns
    /// whether it ran, and if not nothing changed.
    pub fn cut_process_space(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_cut_process_space(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).process_space_cut(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, PROCESS_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / 4096;
        if page >= NUM_PAGES || self.flush_epoch == usize::MAX {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_process = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Process) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_process_block(base);
        }
        if !dead_process {
            return false;
        }
        let list = PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * 4096).borrow(
            Tracked(self.spaces.loaded.borrow().tracked_borrow(base)),
        ).list;
        if list != 0u32 {
            return false;
        }
        proof {
            assert(a.is_root(base));
            assert(a.space_records[base].value().kind is Process);
        }
        let steps = self.cut_children(base, true);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            if steps != 0 {
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
                assert forall|i: usize| #![trigger b.entry(base, i)] i < KERNEL_MEM_END_L4INDEX implies b.entry(base, i) == a.entry(base, i) by {
                    assert(!a.child_slot(base, i));
                }
                assert forall|c: usize| #![trigger b.record(c)]
                    b.is_page(c) && b.record(c).parent is Some implies b.is_table(b.record(c).parent->Some_0.table) by {
                    assert(b.maps.contains_key(c));
                    let p = b.record(c).parent->Some_0;
                    assert(b.names_child(p.table, p.entry));
                }
                post.lemma_process_block(base);
                assert(post.processes.records@.contains_key(base));
            }
        }
        steps != 0
    }

    /// The kernel after a leaf is detached from its root entry: only the tables changed, and those only
    /// in the leaf's entry and its parent record, which no capability is, so every invariant holds and
    /// the view is as it was.
    proof fn lemma_leaf_detached_kernel(pre: Self, post: Self, leaf: usize)
        requires
            pre.wf(),
            post == (CapKernel { tables: post.tables, ..pre }),
            post.tables.wf(&post.list),
            post.tables.owner == pre.tables.owner,
            post.tables.roots@.dom() == pre.tables.roots@.dom(),
            pre.tables.owner@.contains_key(leaf),
            !post.tables.attached(leaf),
            forall|n: usize| n != leaf ==> #[trigger] post.tables.payload_of(n) == pre.tables.payload_of(n),
        ensures
            post.wf(),
            post.view() == pre.view(),
    {
        pre.tables.lemma_leaf(&pre.list, leaf);
        assert(leaf % 8192 == 0 ==> leaf % 4096 == 0) by (bit_vector);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            && (pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)) by {
            if pre.tables.is_cap(&pre.list, x) {
                assert(x != leaf);
            }
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) && post.tables.attached(l) implies {
            &&& l < NODE_SPACE
            &&& post.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind is Hidden
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(l % 8192 == 0 ==> l % 4096 == 0) by (bit_vector);
            assert(page_of(l) == l);
            assert(l != leaf);
            assert(post.tables.payload_of(l) == pre.tables.payload_of(l));
            assert(pre.tables.attached(l));
        }
        assert(hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages));
        assert(binding_parents(&post.list, &post.tables, &post.threads)) by {
            reveal(binding_parents);
        }
        assert(devices_wf(&post.list, &post.tables, &post.devices)) by {
            reveal(devices_wf);
        }
        Self::lemma_tlb_same(pre, post);
        let (a, b) = (pre.view(), post.view());
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) == a.held.contains(h) by {}
        assert(b.held =~= a.held);
        assert forall|n: NodeId| #[trigger] b.names.contains_key(n) == a.names.contains_key(n)
            && (a.names.contains_key(n) ==> b.names[n] == a.names[n]) by {}
        assert(b.names =~= a.names);
        assert forall|n: NodeId| #[trigger] b.pages.contains_key(n) == a.pages.contains_key(n)
            && (a.pages.contains_key(n) ==> b.pages[n] == a.pages[n]) by {}
        assert(b.pages =~= a.pages);
        assert forall|h: (NodeId, Right)| #[trigger] b.rights.contains(h) == a.rights.contains(h) by {}
        assert(b.rights =~= a.rights);
        assert(b == a);
    }

    /// Detaches up to a budget of the leaves of the dead process at `base`'s capability table, under the
    /// untyped at index `from` of the table at `root`, each from the root entry naming it with its parent
    /// record in the same step. Refused while a core has the process's space loaded. Returns whether it
    /// ran, and if not nothing changed. A detached entry stays empty, so a slice starts again from the
    /// first entry.
    pub fn detach_process_leaves(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_detach_process_leaves(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).process_leaves_detached(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, PROCESS_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / 4096;
        if page >= NUM_PAGES {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_process = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Process) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_process_block(base);
        }
        if !dead_process {
            return false;
        }
        let list = PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * 4096).borrow(
            Tracked(self.spaces.loaded.borrow().tracked_borrow(base)),
        ).list;
        if list != 0u32 {
            return false;
        }
        proof {
            assert(pre.tables.roots@.contains_key(base));
        }
        let mut steps: usize = 0;
        let mut r: usize = 0;
        while steps != TABLE_SLICE_BUDGET && r != ROOT_ENTRIES
            invariant
                self.wf(),
                pre == *old(self),
                pre.wf(),
                *self == (CapKernel { tables: self.tables, ..pre }),
                self.tables.owner == pre.tables.owner,
                self.tables.roots@.dom() == pre.tables.roots@.dom(),
                pre.tables.roots@.contains_key(base),
                self.view() == pre.view(),
                steps <= TABLE_SLICE_BUDGET,
                r <= ROOT_ENTRIES,
                steps == 0 ==> *self == pre,
                steps > 0 ==> exists|i: int| 0 <= i < ROOT_ENTRIES && #[trigger] pre.tables.leaf(base, i) != NO_LEAF,
                leaf_entries(&self.tables, base).subset_of(leaf_entries(&pre.tables, base)),
                leaf_entries(&pre.tables, base).len() == leaf_entries(&self.tables, base).len() + steps,
                forall|j: int| 0 <= j < r ==> #[trigger] self.tables.leaf(base, j) == NO_LEAF,
            decreases TABLE_SLICE_BUDGET - steps, ROOT_ENTRIES - r,
        {
            let ghost mid = *self;
            let leaf = self.tables.entry(base, r);
            if leaf == NO_LEAF {
                r = r + 1;
                continue;
            }
            proof {
                mid.tables.lemma_entry(base, r as int);
            }
            self.tables.detach_leaf(&self.list, leaf);
            proof {
                let post = *self;
                Self::lemma_leaf_detached_kernel(mid, post, leaf);
                let (ma, pa) = (leaf_entries(&mid.tables, base), leaf_entries(&post.tables, base));
                assert forall|j: usize| #[trigger] pa.contains(j) == ma.remove(r).contains(j) by {
                    lemma_leaf_entries(&mid.tables, base, j);
                    lemma_leaf_entries(&post.tables, base, j);
                    if j < ROOT_ENTRIES && j != r {
                        assert(post.tables.leaf(base, j as int) == mid.tables.leaf(base, j as int));
                    }
                }
                assert(pa =~= ma.remove(r));
                lemma_leaf_entries(&mid.tables, base, r);
                vstd::set::lemma_set_remove_len(ma, r);
                assert forall|j: int| 0 <= j < r + 1 implies #[trigger] post.tables.leaf(base, j) == NO_LEAF by {
                    if j != r {
                        assert(mid.tables.leaf(base, j) == NO_LEAF);
                    }
                }
                if steps == 0 {
                    assert(mid == pre);
                    assert(pre.tables.leaf(base, r as int) != NO_LEAF);
                }
            }
            steps = steps + 1;
            r = r + 1;
        }
        proof {
            let post = *self;
            Self::lemma_same_tree_shrunk(pre, post);
            if steps == 0 {
                assert forall|i: int| 0 <= i < ROOT_ENTRIES implies !(#[trigger] pre.tables.leaf(base, i) != NO_LEAF) by {
                    assert(post.tables.leaf(base, i) == NO_LEAF);
                }
            } else {
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
                assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) && post.tables.attached(l)
                    implies post.tables.roots@.contains_key(post.tables.record(l).base) by {
                    post.tables.lemma_leaf(&post.list, l);
                }
                assert(post.processes.records@.contains_key(base));
            }
        }
        steps != 0
    }
}

} // verus!
