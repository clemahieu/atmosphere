// SPDX-License-Identifier: MIT

//! Retype reclaiming memory. There is no kernel list of dead objects, and no revoke or delete drains
//! another's teardown: a retype naming a block, by a holder of an untyped covering it, does the work.
//! See design/teardown-driven-by-retype/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
#[cfg(verus_keep_ghost)]
use crate::capability::revoke::REVOKE_STEP_STEPS;
use crate::capability::revoke::UNLINK_ARM_STEPS;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
#[cfg(verus_keep_ghost)]
use crate::capability::zero::*;
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::pptr::PointsTo;

/// Every permission of a map, uninitialised. Handing a frame's pages back only forgets what they held, so
/// this is a proof with no run-time cost, whatever the block's size.
proof fn leak_all(tracked m: Map<usize, PagePerm4k>) -> (tracked ret: Map<usize, PagePerm4k>)
    ensures
        ret.dom() == m.dom(),
        forall|i: usize| #[trigger] m.contains_key(i) ==> ret[i].addr() == m[i].addr() && ret[i].is_uninit(),
    decreases m.dom().len(),
{
    let tracked mut m0 = m;
    if m0.dom().len() == 0 {
        assert(m0.dom() =~= Set::<usize>::empty());
        return m0;
    }
    let k = m0.dom().choose();
    assert(m0.dom().contains(k));
    let tracked mut perm = m0.tracked_remove(k);
    perm.leak_contents();
    let tracked mut rest = leak_all(m0);
    rest.tracked_insert(k, perm);
    assert(rest.dom() =~= m.dom());
    rest
}

/// A node with no child keeps none when nodes leave the list and none join it, the first staying first
/// and every parent as it was.
proof fn lemma_childless_kept(pre: &Tree, post: &Tree, x: usize)
    requires
        pre.wf(),
        post.wf(),
        x < NODE_SPACE,
        pre.nodes@[x as int].live,
        post.nodes@[x as int].live,
        pre.childless(x),
        post.parent@ == pre.parent@,
        post.seq@[0] == pre.seq@[0],
        forall|c: usize| post.seq@.contains(c) ==> pre.seq@.contains(c),
    ensures
        post.childless(x),
{
    if !post.childless(x) {
        post.lemma_next_is_child(x);
        pre.lemma_childless(x, post.nodes@[x as int].next);
    }
}

/// The most nodes one retype removes from a dead leaf's slots.
pub const LEAF_SLICE_BUDGET: usize = 64;

/// The most child tables one retype cuts from a dead table page or space root.
pub const TABLE_SLICE_BUDGET: usize = 64;

/// The units of one slice of cuts: a step per entry looked at and a stale note per child cut.
/// See design/one-lock-bounded-steps/.
pub const CUT_SLICE_STEPS: usize = ENTRIES + TABLE_SLICE_BUDGET * CUT_NOTE_STEPS;

/// The units of one slice of a dead table page's mappings: a step per entry looked at and a mapping
/// node's unlink per mapping. See design/one-lock-bounded-steps/.
pub const UNMAP_SLICE_STEPS: usize = ENTRIES + TABLE_SLICE_BUDGET * UNLINK_ARM_STEPS;

/// What a reclaim did.
pub enum ReclaimStep {
    /// Nothing changed: the caller may not name this block, or a capability or a core still depends on
    /// it.
    Refused,
    /// Nothing changed: a core may still hold a translation to it. Retype again later, since nothing
    /// waits under the lock.
    Again,
    /// The block is free.
    Freed,
    /// The block held a table leaf or table page whose hidden node is now gone, so it is dead, and its
    /// dismantling starts on a later retype.
    Unlinked,
    /// Some of a dead leaf's capabilities, of a dead table page's children or mappings, of a dead space
    /// root's children, or a dead thread's binding, went, and more may remain. Retype again.
    Slice,
}

/// A page the list holds is page aligned, in the node space and initialised at its own address.
pub proof fn lemma_list_page(list: &Tree, p: usize)
    requires
        list.store_wf(),
        list.pages@.dom().contains(p),
    ensures
        p % PAGE_SZ == 0,
        p + PAGE_SZ <= NODE_SPACE,
        list.pages@[p].addr() == p,
        list.pages@[p].is_init(),
{
    reveal(Tree::store_wf);
}

/// Two page-aligned addresses on one page are one address.
proof fn lemma_same_page(p: usize, base: usize)
    requires
        p % PAGE_SZ == 0,
        base % PAGE_SZ == 0,
        p / PAGE_SZ == base / PAGE_SZ,
    ensures
        p == base,
{
    lemma_fundamental_div_mod(p as int, PAGE_SZ as int);
    lemma_fundamental_div_mod(base as int, PAGE_SZ as int);
}

/// A permission something else holds is no page of the list: two permissions never share an address.
pub proof fn lemma_list_page_apart<V>(tracked pages: &mut Map<usize, PointsTo<NodePage>>, tracked other: &PointsTo<V>)
    requires
        vstd::layout::size_of::<V>() != 0,
        vstd::layout::size_of::<NodePage>() != 0,
        old(pages).contains_key(other.addr()) ==> old(pages)[other.addr()].addr() == other.addr(),
    ensures
        *final(pages) == *old(pages),
        !old(pages).contains_key(other.addr()),
{
    if pages.contains_key(other.addr()) {
        let tracked mut perm = pages.tracked_remove(other.addr());
        perm.is_disjoint(other);
        assert(false);
    }
}

/// perms holds page i's permission, at its address and uninitialised.
spec fn holds_free_page(perms: Map<usize, PagePerm4k>, i: usize) -> bool {
    &&& perms.contains_key(i)
    &&& perms[i].addr() == i * PAGE_SZ
    &&& perms[i].is_uninit()
}

/// Takes the five node pages of the table page at base off the list, each as its page's permission.
fn take_table_node_pages(list: &mut Tree, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: Tracked<Map<usize, PagePerm4k>>)
    requires
        old(list).wf(),
        base % TABLE_PAGE_BYTES == 0,
        base / PAGE_SZ + 8 <= NUM_PAGES,
        forall|k: usize| k < TABLE_NODE_PAGES ==> old(list).pages@.dom().contains(#[trigger] table_node_page(base, k)),
        forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            ==> !old(list).nodes@[table_node(base, k, i) as int].live,
    ensures
        final(steps).count <= old(steps).count + TABLE_NODE_PAGES,
        final(list).wf(),
        final(list).seq == old(list).seq,
        final(list).parent == old(list).parent,
        final(list).nodes == old(list).nodes,
        forall|p: usize| #[trigger] final(list).pages@.dom().contains(p)
            == (old(list).pages@.dom().contains(p) && !(base <= p < base + TABLE_NODE_PAGES * PAGE_SZ)),
        forall|i: usize| base / PAGE_SZ <= i < base / PAGE_SZ + TABLE_NODE_PAGES ==> #[trigger] holds_free_page(ret@, i),
{
    let ghost pre = *old(list);
    let ghost page = base / PAGE_SZ;
    proof {
        lemma_table_page_aligned(base);
    }
    let tracked mut perms = Map::<usize, PagePerm4k>::tracked_empty();
    let ghost steps0 = steps.count;
    let mut k: usize = 0;
    while k < TABLE_NODE_PAGES
        invariant
            k <= TABLE_NODE_PAGES,
            steps.count == steps0 + k,
            base % TABLE_PAGE_BYTES == 0,
            base % PAGE_SZ == 0,
            base as int == PAGE_SZ * page,
            page == base / PAGE_SZ,
            page + 8 <= NUM_PAGES,
            list.wf(),
            list.seq == pre.seq,
            list.parent == pre.parent,
            list.nodes == pre.nodes,
            pre.wf(),
            forall|j: usize| k <= j < TABLE_NODE_PAGES ==> pre.pages@.dom().contains(#[trigger] table_node_page(base, j)),
            forall|j: usize, i: usize| #![trigger table_node(base, j, i)] j < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> !pre.nodes@[table_node(base, j, i) as int].live,
            forall|p: usize| #[trigger] list.pages@.dom().contains(p)
                == (pre.pages@.dom().contains(p) && !(base <= p < base + k * PAGE_SZ)),
            forall|i: usize| page <= i < page + k ==> #[trigger] holds_free_page(perms, i),
        decreases TABLE_NODE_PAGES - k,
    {
        let ghost before = *list;
        let ghost held = perms;
        let p = base + k * PAGE_SZ;
        proof {
            lemma_table_node_page(base, k);
            assert(p == table_node_page(base, k));
            assert(pre.pages@.dom().contains(p));
            assert(list.pages@.dom().contains(p));
            assert forall|i: int| 0 <= i < NODES_PER_PAGE implies !(#[trigger] list.nodes@[p + i]).live by {
                assert(table_node(base, k, i as usize) == p + i);
                assert(!pre.nodes@[table_node(base, k, i as usize) as int].live);
            }
            lemma_list_page(list, p);
        }
        let Tracked(nodes) = list.remove_page(p);
        proof {
            let tracked mut nodes = nodes;
            nodes.leak_contents();
            let tracked free = crate::layouts::node_page_into_page(nodes);
            perms.tracked_insert((page + k) as usize, free);
            assert forall|q: usize| #[trigger] list.pages@.dom().contains(q)
                == (pre.pages@.dom().contains(q) && !(base <= q < base + (k + 1) * PAGE_SZ)) by {
                if pre.pages@.dom().contains(q) && p <= q < p + PAGE_SZ {
                    lemma_list_page(&pre, q);
                }
            }
            assert forall|i: usize| page <= i < page + k + 1 implies #[trigger] holds_free_page(perms, i) by {
                if i < page + k {
                    assert(holds_free_page(held, i));
                }
            }
        }
        k = k + 1;
        proof {
            steps.step();
        }
    }
    Tracked(perms)
}

impl CapKernel {
    /// A dead 4K frame at zero references: the block to be freed, by what the block table says.
    pub open spec fn frame_is_dead(&self, page: usize) -> bool {
        &&& self.blocks.tracks(page as int)
        &&& self.blocks.pages@[page as int].kind is Base
        &&& self.blocks.pages@[page as int].object is Frame
        &&& self.blocks.pages@[page as int].dead
        &&& self.blocks.pages@[page as int].refs == 0
    }

    /// What freeing the 4K frame at `base` did to self, under the untyped at index `from` of the table
    /// at `root`.
    pub open spec fn frame_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.frame_is_dead(page)
        &&& self.no_stale_translation(page)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& !post.frames@.contains_key(page)
        &&& Self::step_ok(*self, post, c as int)
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// A retype may unlink the hidden node of the leaf at `base`: an untyped covers its block, and the
    /// node is still live.
    pub open spec fn can_unlink_leaf(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 1)
        &&& self.tables.owner@.contains_key(base)
        &&& self.list.nodes@[base as int].live
    }

    /// What unlinking the hidden node of the leaf at `base` did to self: that node went and its block is
    /// dead at zero, every other block as it was. The parent map is as it was: the node leaves the list
    /// but keeps its entry. The tables are as they were, so the leaf stays in its root entry, where
    /// lookup now refuses it, and every capability, the leaf's slots among them, is as it was, so the
    /// view is too. No record, table page, epoch, core or IOMMU changed.
    pub open spec fn leaf_unlinked(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& !post.list.nodes@[base as int].live
        &&& post.list.parent@ == self.list.parent@
        &&& post.tables == self.tables
        &&& post.blocks.pages@[page as int].refs == 0
        &&& post.blocks.pages@[page as int].dead
        &&& blocks_refs_changed(&self.blocks, &post.blocks, BlockRef::Small(page), 0, true)
        &&& post.holders == self.holders
        &&& post.spaces == self.spaces
        &&& post.threads == self.threads
        &&& post.processes == self.processes
        &&& post.table_pages == self.table_pages
        &&& post.stale_epoch == self.stale_epoch
        &&& post.flush_epoch == self.flush_epoch
        &&& post.cores == self.cores
        &&& post.iommus == self.iommus
        &&& Self::caps_frame(*self, post, base, base)
        &&& forall|x: usize| #[trigger] post.is_cap(x) == self.is_cap(x)
        &&& post.view() == self.view()
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// A retype may unlink the hidden node of the table page at `base`: an untyped covers its block, the
    /// node is still live, and the epoch can rise to record the cut.
    pub open spec fn can_unlink_table(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 3)
        &&& self.table_pages.maps@.contains_key(base)
        &&& self.list.nodes@[base as int].live
        &&& self.flush_epoch < usize::MAX
    }

    /// What unlinking the hidden node of the table page at `base` did to self: as table_unlinked says.
    /// Every capability is as it was, and a device space shares no more, having lost the walks through
    /// the page: exactly what a walk not through the entry naming the page still finds, since another
    /// path may map the same frame.
    pub open spec fn table_page_unlinked(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let a = tree_of(&self.table_pages, &self.spaces);
        let q = a.record(base).parent;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& Self::table_unlinked(*self, post, base)
        &&& Self::caps_frame(*self, post, base, base)
        &&& forall|x: usize| #[trigger] post.is_cap(x) == self.is_cap(x)
        &&& sheds_shares(self.view(), post.view())
        &&& q is None ==> post.view().shares == self.view().shares
        &&& q is Some ==> post.view().shares
            == shares_surviving(a, |r: usize, p: SpacePath| passes_through(a, r, p, q->0.table, q->0.entry))
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// What freeing the empty table page at `base` did to self. Its children and mappings went earlier,
    /// so the view is as it was.
    pub open spec fn table_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.table_is_empty(base)
        &&& self.blocks.pages@[page as int].refs == 0
        &&& self.no_stale_translation(page)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& !post.table_pages.maps@.contains_key(base)
        &&& forall|k: usize| k < TABLE_NODE_PAGES ==> !post.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// The leaf at `base` is owned and no node in its page is live, so nothing is left of it but its two
    /// pages.
    pub open spec fn leaf_is_empty(&self, base: usize) -> bool {
        &&& self.tables.owner@.contains_key(base)
        &&& forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] self.list.nodes@[base + k]).live
    }

    /// What freeing the empty leaf at `base` did to self: its block is free, and the root entry its
    /// owner names is cleared with it, every other entry as it was. Its capabilities went earlier, so the
    /// view is as it was, and every node, every capability outside the leaf, every tracked page outside
    /// its block, the epochs, the cores, the IOMMUs and the records are as they were.
    pub open spec fn leaf_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        let (owner, r) = self.tables.owner@[base];
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.leaf_is_empty(base)
        &&& self.no_stale_translation(page)
        &&& self.no_stale_translation((page + 1) as usize)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& post.blocks.pages@[page + 1int].kind is Free
        &&& post.tables.owner@ == self.tables.owner@.remove(base)
        &&& post.tables.roots@.dom() == self.tables.roots@.dom()
        &&& post.tables.leaf(owner, r) == NO_LEAF
        &&& forall|t: usize, s: int| #![trigger post.tables.leaf(t, s)] self.tables.roots@.contains_key(t) && 0 <= s < ROOT_ENTRIES
            && !(t == owner && s == r) ==> post.tables.leaf(t, s) == self.tables.leaf(t, s)
        &&& !post.list.pages@.dom().contains(base)
        &&& post.list.seq == self.list.seq
        &&& post.list.parent == self.list.parent
        &&& post.list.nodes == self.list.nodes
        &&& post.list.pages@.dom() == self.list.pages@.dom().remove(base)
        &&& post.tables.payloads@.dom() == self.tables.payloads@.dom().remove(base)
        &&& forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) == self.tables.is_cap(&self.list, n)
        &&& forall|n: usize| page_of(n) != base ==> #[trigger] post.tables.payload_of(n) == self.tables.payload_of(n)
        &&& forall|i: int| self.blocks.tracks(i) && !(page as int <= i < page + 2)
            ==> #[trigger] post.blocks.pages@[i] == self.blocks.pages@[i]
        &&& post.stale_epoch == self.stale_epoch
        &&& post.flush_epoch == self.flush_epoch
        &&& post.cores == self.cores
        &&& post.iommus == self.iommus
        &&& post.spaces == self.spaces
        &&& post.processes == self.processes
        &&& post.threads == self.threads
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// An empty table page has nothing left to unlink or slice.
    proof fn lemma_empty_table_no_work(&self, root: usize, from: usize, base: usize)
        requires
            self.wf(),
        ensures
            self.table_is_empty(base) ==> !self.can_unlink_table(root, from, base) && !self.can_slice_table(root, from, base),
    {
        if self.table_is_empty(base) {
            let tree = tree_of(&self.table_pages, &self.spaces);
            self.lemma_empty_table(base);
            if exists|e: usize| #[trigger] tree.names_child(base, e) {
                let e = choose|e: usize| #[trigger] tree.names_child(base, e);
                self.lemma_table_with_entry_not_empty(base, e);
            }
            if exists|e: usize| #[trigger] frame_slot(tree, base, e) {
                let e = choose|e: usize| #[trigger] frame_slot(tree, base, e);
                self.lemma_table_with_entry_not_empty(base, e);
            }
        }
    }

    /// The dead table page at `base` has nothing left to slice: no entry names a child and none maps a
    /// frame.
    pub open spec fn table_is_spent(&self, base: usize) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        &&& self.table_pages.maps@.contains_key(base)
        &&& !self.list.nodes@[base as int].live
        &&& !exists|e: usize| #[trigger] tree.names_child(base, e)
        &&& !exists|e: usize| #[trigger] frame_slot(tree, base, e)
    }

    /// A spent table page is empty, so slicing it to the end leaves what a free takes. A present entry
    /// either names a child or maps a frame, any other entry is empty, and a live node in its node pages
    /// other than its hidden node is the mapping of one of its entries.
    pub proof fn lemma_spent_table_is_empty(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.table_is_spent(base) ==> self.table_is_empty(base),
    {
        if self.table_is_spent(base) {
            self.lemma_spent_entries_empty(base);
            self.lemma_spent_nodes_dead(base);
        }
    }

    /// A spent table page's entries are all empty.
    proof fn lemma_spent_entries_empty(&self, base: usize)
        requires
            self.wf(),
            self.table_is_spent(base),
        ensures
            forall|i: usize| #![trigger self.table_pages.maps@[base].value()[i]]
                i < ENTRIES ==> self.table_pages.maps@[base].value()[i].is_empty(),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert forall|i: usize| #![trigger self.table_pages.maps@[base].value()[i]]
            i < ENTRIES implies self.table_pages.maps@[base].value()[i].is_empty() by {
            if tree.entry(base, i).perm.present {
                if tree.record(base).level >= 2 {
                    if tree.entry(base, i).perm.ps {
                        assert(frame_slot(tree, base, i));
                    } else {
                        assert(tree.names_child(base, i));
                    }
                } else {
                    assert(frame_slot(tree, base, i));
                }
            }
        }
    }

    /// A spent table page's node pages hold no live node.
    proof fn lemma_spent_nodes_dead(&self, base: usize)
        requires
            self.wf(),
            self.table_is_spent(base),
        ensures
            forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> !self.list.nodes@[table_node(base, k, i) as int].live,
    {
        assert forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            implies !self.list.nodes@[table_node(base, k, i) as int].live by {
            if self.list.nodes@[table_node(base, k, i) as int].live {
                self.lemma_live_table_node_maps(base, k, i);
            }
        }
    }

    /// Node n is the mapping of an entry of a table page, placed in that page's node pages, and the entry
    /// is a frame slot.
    proof fn lemma_mapping_in_table(&self, n: usize)
        requires
            self.wf(),
            self.mappings@.contains_key(n),
        ensures
            self.table_pages.maps@.contains_key(self.mappings@[n].table),
            self.mappings@[n].table % TABLE_PAGE_BYTES == 0,
            self.mappings@[n].entry < ENTRIES,
            n == mapping_node(self.mappings@[n].table, self.mappings@[n].entry),
            frame_slot(tree_of(&self.table_pages, &self.spaces), self.mappings@[n].table, self.mappings@[n].entry),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let m = self.mappings@[n];
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        self.lemma_table_page_room(m.table);
        lemma_mapping_node_place(m.table, m.entry);
    }

    /// A live node in a table page's node pages, other than its hidden node, is the mapping of one of the
    /// page's entries, so the page has that frame_slot.
    proof fn lemma_live_table_node_maps(&self, base: usize, k: usize, i: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(base),
            k < TABLE_NODE_PAGES,
            i < NODES_PER_PAGE,
            k != 0 || i != 0,
            self.list.nodes@[table_node(base, k, i) as int].live,
        ensures
            exists|e: usize| #[trigger] frame_slot(tree_of(&self.table_pages, &self.spaces), base, e),
    {
        let n = table_node(base, k, i);
        self.lemma_table_page_room(base);
        lemma_table_node_place(base, k, i);
        assert(self.list.nodes@[n as int].kind is Mapping);
        assert(self.mappings@.contains_key(n));
        self.lemma_mapping_in_table(n);
        lemma_node_page_names_block(base, self.mappings@[n].table, n / PAGE_SZ);
    }

    /// A retype's parent carries the right: the capability it names holds Retype.
    proof fn lemma_retype_holds_right(&self, root: usize, from: usize, base: usize, order: u8)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            self.can_retype_under(root, from, base, order)
                ==> self.view().holds_right(root, self.tables.node_of(root, from), Right::Retype),
    {
        if self.can_retype_under(root, from, base, order) {
            self.lemma_slot(root, from);
            assert(right_bit(Right::Retype) == 8);
            assert(self.tables.is_cap(&self.list, self.tables.node_of(root, from)));
        }
    }

    /// A dead 4K frame has no page mapped, since a mapping would hold a reference on its block.
    proof fn lemma_dead_frame_unmapped(&self, page: usize)
        requires
            self.wf(),
            self.frame_is_dead(page),
        ensures
            !self.mapped@.contains(page),
    {
        if self.mapped@.contains(page) {
            let br = self.lemma_mapped_block(page);
            assert(self.holders@.contains_key(BlockRef::Small(page)));
            match br {
                BlockRef::Small(b) => {},
                BlockRef::Two(r) => { lemma_large_block_alone(&self.blocks, Large::Two, r, BlockRef::Small(page), page); },
                BlockRef::One(r) => { lemma_large_block_alone(&self.blocks, Large::One, r, BlockRef::Small(page), page); },
            }
        }
    }

    /// No page of a table leaf's block is mapped: the only blocks a mapping names are frames'.
    proof fn lemma_leaf_unmapped(&self, page: usize, g: usize)
        requires
            self.wf(),
            self.blocks.tracks(page as int),
            page % 2 == 0,
            self.blocks.pages@[page as int].kind is Base,
            self.blocks.pages@[page as int].object is TableLeaf,
            self.blocks.pages@[page as int].order == 1,
            g == page || g == page + 1,
        ensures
            !self.mapped@.contains(g),
    {
        if self.mapped@.contains(g) {
            let br = self.lemma_mapped_block(g);
            match br {
                BlockRef::Small(b) => {
                    assert(self.holders@.contains_key(BlockRef::Small(g)));
                    if g != page {
                        self.blocks.lemma_member_of(page as int, g as int);
                    }
                },
                BlockRef::Two(r) => {
                    // The block's two pages share every region, since it starts on an even page.
                    assert(r * PAGES_PER_2M <= page < (r + 1) * PAGES_PER_2M) by (nonlinear_arith)
                        requires
                            r * PAGES_PER_2M <= g < (r + 1) * PAGES_PER_2M,
                            g == page || g == page + 1,
                            page % 2 == 0,
                            PAGES_PER_2M % 2 == 0,
                    ;
                    lemma_large_block_alone(&self.blocks, Large::Two, r, BlockRef::Small(page), page);
                },
                BlockRef::One(r) => {
                    assert(r * PAGES_PER_1G <= page < (r + 1) * PAGES_PER_1G) by (nonlinear_arith)
                        requires
                            r * PAGES_PER_1G <= g < (r + 1) * PAGES_PER_1G,
                            g == page || g == page + 1,
                            page % 2 == 0,
                            PAGES_PER_1G % 2 == 0,
                    ;
                    lemma_large_block_alone(&self.blocks, Large::One, r, BlockRef::Small(page), page);
                },
            }
        }
    }

    /// A dead large block has no page mapped: a mapping of one holds a reference on the block, and no
    /// other block shares its pages.
    proof fn lemma_dead_region_unmapped(&self, level: Large, r: usize)
        requires
            self.wf(),
            r < level_regions(level),
            self.region_is_dead(level, r),
        ensures
            self.region_unmapped(level, r),
    {
        assert forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) implies !self.mapped@.contains(i) by {
            if self.mapped@.contains(i) {
                let br = self.lemma_mapped_block(i);
                if br != level_ref(level, r) {
                    lemma_large_block_alone(&self.blocks, level, r, br, i);
                }
            }
        }
    }

    /// A typed large block shares no page with another block, so the page at `base` in it is no small
    /// block's base, no small object lives at `base`, and the other level's region over it is not typed.
    proof fn lemma_large_excludes_small(&self, level: Large, base: usize)
        requires
            self.wf(),
            base / PAGE_SZ / level_pages(level) < level_regions(level),
            block_typed(&self.blocks, level_ref(level, base / PAGE_SZ / level_pages(level))),
        ensures
            !(self.blocks.pages@[(base / PAGE_SZ) as int].kind is Base),
            !self.tables.owner@.contains_key(base),
            !self.table_pages.maps@.contains_key(base),
            !self.spaces.roots@.contains_key(base),
            !self.threads.records@.contains_key(base),
            !self.processes.records@.contains_key(base),
            match level {
                Large::Two => !self.blocks.regions_1g@[(base / PAGE_SZ / PAGES_PER_1G) as int].typed,
                Large::One => !self.blocks.regions_2m@[(base / PAGE_SZ / PAGES_PER_2M) as int].typed,
            },
    {
        let page = base / PAGE_SZ;
        let r = page / level_pages(level);
        lemma_fundamental_div_mod(page as int, PAGES_PER_2M as int);
        lemma_fundamental_div_mod(page as int, PAGES_PER_1G as int);
        lemma_mod_pos_bound(page as int, PAGES_PER_2M as int);
        lemma_mod_pos_bound(page as int, PAGES_PER_1G as int);
        assert(block_has_page(level_ref(level, r), page));
        assert(self.blocks.tracks(page as int));
        if self.blocks.pages@[page as int].kind is Base {
            assert(block_typed(&self.blocks, BlockRef::Small(page)));
            lemma_large_block_alone(&self.blocks, level, r, BlockRef::Small(page), page);
        }
        if self.tables.owner@.contains_key(base) {
            assert(self.blocks.pages@[page as int].kind is Base);
        }
        if self.table_pages.maps@.contains_key(base) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        }
        if self.spaces.roots@.contains_key(base) {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
        }
        if self.threads.records@.contains_key(base) {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, base));
        }
        if self.processes.records@.contains_key(base) {
            assert(process_wf(&self.processes, &self.blocks, base));
        }
        match level {
            Large::Two => {
                let q = page / PAGES_PER_1G;
                if self.blocks.regions_1g@[q as int].typed {
                    assert(q < NUM_1G);
                    assert(block_has_page(BlockRef::One(q), page));
                    lemma_large_block_alone(&self.blocks, level, r, BlockRef::One(q), page);
                }
            },
            Large::One => {
                let q = page / PAGES_PER_2M;
                if self.blocks.regions_2m@[q as int].typed {
                    assert(q < NUM_2M);
                    assert(block_has_page(BlockRef::Two(q), page));
                    lemma_large_block_alone(&self.blocks, level, r, BlockRef::Two(q), page);
                }
            },
        }
    }

    /// A retype naming the block at `base`, under the untyped at index `from` of the table at `root`:
    /// what it does depends on what the block holds. A large block's state is in its region's entry,
    /// so the regions over the page come first, then the small block's object. All of these come from
    /// user space.
    pub fn reclaim(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            // The leaf's arm, a slice and then a free, is the largest.
            final(steps).count <= old(steps).count + (NODES_PER_PAGE - 1) + LEAF_SLICE_BUDGET * (REVOKE_STEP_STEPS + 1)
                + (NODES_PER_PAGE + 2 * (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX),
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused || ret is Again ==> *final(self) == *old(self),
            !((old(self).can_retype_under(root, from, base, 0) && old(self).frame_is_dead(base / PAGE_SZ))
                || old(self).can_unlink_leaf(root, from, base)
                || (old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base))
                || old(self).can_slice_leaf(root, from, base)
                || old(self).can_unlink_table(root, from, base)
                || old(self).can_slice_table(root, from, base)
                || (old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base))
                || old(self).can_cut_space(root, from, base)
                || (old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base))
                || old(self).can_retire_process(root, from, base)
                || old(self).can_cut_process_space(root, from, base)
                || (old(self).can_retype_under(root, from, base, PROCESS_ORDER) && old(self).process_is_spent(base))
                || old(self).can_unbind_thread(root, from, base)
                || (old(self).can_retype_under(root, from, base, 1) && old(self).thread_is_spent(base))
                || old(self).can_reclaim_large(root, from, base, 9)
                || old(self).can_reclaim_large(root, from, base, 18)) ==> ret is Refused,
            old(self).can_reclaim_large(root, from, base, 9)
                ==> if old(self).region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M) {
                    ret is Freed && old(self).large_frame_freed(*final(self), c, root, from, base, 9)
                } else {
                    ret is Again
                },
            old(self).can_reclaim_large(root, from, base, 18)
                ==> if old(self).region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G) {
                    ret is Freed && old(self).large_frame_freed(*final(self), c, root, from, base, 18)
                } else {
                    ret is Again
                },
            !old(self).view().holds_right(root, old(self).tables.node_of(root, from), Right::Retype) ==> ret is Refused,
            old(self).spaces.roots@.contains_key(base) && !old(self).dead_io_space(base)
                && !old(self).can_retire_process(root, from, base)
                && !old(self).can_cut_process_space(root, from, base)
                && !(old(self).can_retype_under(root, from, base, PROCESS_ORDER) && old(self).process_is_spent(base)) ==> ret is Refused,
            old(self).can_cut_space(root, from, base) ==> ret is Slice,
            old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            old(self).can_retype_under(root, from, base, 3) && old(self).space_is_spent(base) ==> ret is Again || ret is Freed,
            old(self).spaces.roots@.contains_key(base) && old(self).spaces.records@[base].value().kind is Device && ret is Slice
                ==> old(self).space_children_cut(*final(self), root, from, base),
            // A process with a reference, such as one a core's current thread is bound to, is refused. So is
            // one a core still depends on, as one that may hold a translation of it does, unless a retire
            // can run, which changes nothing but the epoch, the space's retire epoch and the flush IPIs.
            old(self).processes.records@.contains_key(base)
                && (old(self).blocks.pages@[(base / PAGE_SZ) as int].refs != 0
                    || (!old(self).process_released(base) && !old(self).can_retire_process(root, from, base)))
                ==> ret is Refused,
            old(self).processes.records@.contains_key(base)
                && (exists|d: int, t: usize| #![trigger old(self).cores@[d], old(self).threads.records@[t]] 0 <= d < NUM_CPUS && old(self).cores@[d].current_thread == Some(t)
                    && old(self).threads.records@[t].value().process == Some(base))
                ==> ret is Refused,
            old(self).processes.records@.contains_key(base)
                && (exists|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base && #[trigger] old(self).tlb@[d].contains(e))
                ==> !old(self).process_released(base) && (ret is Refused || ret is Slice && old(self).process_retired(*final(self), base)),
            old(self).can_retire_process(root, from, base) ==> ret is Slice && old(self).process_retired(*final(self), base),
            // A process whose space a core's base register names is refused: the core may walk the space, and
            // a retire, which ends a core's dependence when it flushes, would not end that.
            old(self).processes.records@.contains_key(base) && old(self).process_space_named(base) ==> ret is Refused,
            old(self).can_cut_process_space(root, from, base) ==> ret is Slice,
            old(self).processes.records@.contains_key(base) && ret is Slice
                ==> old(self).process_retired(*final(self), base) || old(self).process_space_cut(*final(self), root, from, base),
            old(self).can_retype_under(root, from, base, PROCESS_ORDER) && old(self).process_is_spent(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            old(self).processes.records@.contains_key(base) && ret is Freed
                ==> old(self).process_freed(*final(self), c, root, from, base),
            old(self).spaces.roots@.contains_key(base) && old(self).spaces.records@[base].value().kind is Device && ret is Freed
                ==> old(self).space_freed(*final(self), c, root, from, base),
            old(self).can_unlink_table(root, from, base) ==> ret is Unlinked,
            old(self).can_slice_table(root, from, base) ==> ret is Slice,
            old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            old(self).can_retype_under(root, from, base, 3) && old(self).table_is_spent(base) ==> ret is Again || ret is Freed,
            old(self).table_pages.maps@.contains_key(base) && ret is Unlinked ==> old(self).table_page_unlinked(*final(self), root, from, base),
            old(self).table_pages.maps@.contains_key(base) && ret is Slice ==> old(self).table_sliced(*final(self), root, from, base),
            old(self).table_pages.maps@.contains_key(base) && ret is Freed ==> old(self).table_freed(*final(self), c, root, from, base),
            old(self).can_unbind_thread(root, from, base) ==> ret is Slice,
            old(self).threads.records@.contains_key(base) && ret is Slice ==> old(self).thread_unbound(*final(self), root, from, base),
            old(self).threads.records@.contains_key(base) && ret is Freed ==> old(self).thread_freed(*final(self), c, root, from, base),
            old(self).can_unlink_leaf(root, from, base) ==> ret is Unlinked && old(self).leaf_unlinked(*final(self), root, from, base),
            old(self).can_slice_leaf(root, from, base) ==> ret is Slice && old(self).leaf_sliced(*final(self), root, from, base),
            old(self).can_slice_leaf(root, from, base) && old(self).leaf_slots_childless(base)
                ==> old(self).leaf_slice_kept(*final(self), base),
            old(self).can_slice_leaf(root, from, base) && old(self).leaf_slots_childless(base)
                && old(self).leaf_live_slots(base) <= LEAF_SLICE_BUDGET ==> final(self).leaf_is_empty(base),
            old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) && old(self).acknowledged((base / PAGE_SZ + 1) as usize) {
                    ret is Freed && old(self).leaf_freed(*final(self), c, root, from, base)
                } else {
                    ret is Again
                },
            ret is Again ==> !old(self).acknowledged(base / PAGE_SZ) || !old(self).acknowledged((base / PAGE_SZ + 1) as usize)
                || !old(self).region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M)
                || !old(self).region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G),
            ret is Freed ==> old(self).frame_freed(*final(self), c, root, from, base)
                || old(self).large_frame_freed(*final(self), c, root, from, base, 9)
                || old(self).large_frame_freed(*final(self), c, root, from, base, 18)
                || old(self).leaf_freed(*final(self), c, root, from, base)
                || old(self).table_freed(*final(self), c, root, from, base)
                || old(self).space_freed(*final(self), c, root, from, base)
                || old(self).thread_freed(*final(self), c, root, from, base)
                || old(self).process_freed(*final(self), c, root, from, base),
            ret is Slice ==> old(self).leaf_sliced(*final(self), root, from, base)
                || old(self).table_sliced(*final(self), root, from, base)
                || old(self).space_children_cut(*final(self), root, from, base)
                || old(self).thread_unbound(*final(self), root, from, base)
                || old(self).process_retired(*final(self), base)
                || old(self).process_space_cut(*final(self), root, from, base),
            ret is Unlinked ==> old(self).leaf_unlinked(*final(self), root, from, base)
                || old(self).table_page_unlinked(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            if pre.process_space_named(base) {
                let d = choose|d: int| 0 <= d < NUM_CPUS && #[trigger] pre.cores@[d].space == Some(base);
                pre.lemma_named_depends(d, base);
                assert(!pre.process_released(base));
            }
            pre.lemma_retype_holds_right(root, from, base, 0);
            pre.lemma_retype_holds_right(root, from, base, 1);
            pre.lemma_retype_holds_right(root, from, base, 3);
            pre.lemma_empty_table_no_work(root, from, base);
            pre.lemma_spent_table_is_empty(base);
            pre.lemma_spent_space_is_empty(base);
            pre.lemma_thread_object(base);
            pre.lemma_process_object(base);
            if pre.leaf_is_empty(base) {
                // An empty leaf's hidden node is dead, so neither its unlink nor its slice runs.
                assert(!pre.list.nodes@[base + 0int].live);
            }
            if pre.processes.records@.contains_key(base) {
                pre.lemma_process_block(base);
                pre.lemma_process_refused(base);
            }
            pre.lemma_retype_holds_right(root, from, base, 9);
            pre.lemma_retype_holds_right(root, from, base, 18);
            if pre.can_reclaim_large(root, from, base, 9) {
                pre.lemma_large_excludes_small(Large::Two, base);
            }
            if pre.can_reclaim_large(root, from, base, 18) {
                pre.lemma_large_excludes_small(Large::One, base);
            }
        }
        match self.reclaim_large_frame(c, root, from, base, 9, Tracked(&mut *steps)) {
            ReclaimStep::Refused => {},
            step => { return step; },
        }
        match self.reclaim_large_frame(c, root, from, base, 18, Tracked(&mut *steps)) {
            ReclaimStep::Refused => {},
            step => { return step; },
        }
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return ReclaimStep::Refused;
        }
        let object = self.blocks.pages.get(page).object;
        match object {
            ObjectType::Frame => self.reclaim_frame(c, root, from, base, Tracked(steps)),
            ObjectType::TableLeaf => {
                if self.unlink_leaf(root, from, base, Tracked(&mut *steps)) {
                    ReclaimStep::Unlinked
                } else if self.slice_leaf(root, from, base, Tracked(&mut *steps)) {
                    ReclaimStep::Slice
                } else {
                    self.free_leaf(c, root, from, base, Tracked(steps))
                }
            },
            ObjectType::TablePage => {
                if self.unlink_table(root, from, base, Tracked(&mut *steps)) {
                    ReclaimStep::Unlinked
                } else if self.slice_table(root, from, base, Tracked(&mut *steps)) {
                    ReclaimStep::Slice
                } else {
                    self.free_table(c, root, from, base, Tracked(steps))
                }
            },
            ObjectType::Space => {
                if self.cut_space_children(root, from, base, Tracked(&mut *steps)) {
                    ReclaimStep::Slice
                } else {
                    self.free_space(c, root, from, base, Tracked(steps))
                }
            },
            ObjectType::Thread => self.reclaim_thread(c, root, from, base, Tracked(steps)),
            ObjectType::Process => {
                if self.retire_process(root, from, base, Tracked(&mut *steps)) {
                    ReclaimStep::Slice
                } else if self.cut_process_space(root, from, base, Tracked(&mut *steps)) {
                    ReclaimStep::Slice
                } else {
                    self.free_process(c, root, from, base, Tracked(steps))
                }
            },
            ObjectType::None => ReclaimStep::Refused,
        }
    }

    /// A retype may take a slice of the leaf at `base`: an untyped covers its block, its hidden node has
    /// gone, a slot is still live, and the flush epoch has room to record what the slice unmaps.
    pub open spec fn can_slice_leaf(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 1)
        &&& self.tables.owner@.contains_key(base)
        &&& !self.list.nodes@[base as int].live
        &&& !self.leaf_is_empty(base)
        &&& self.flush_epoch < usize::MAX
    }

    /// What a slice of the leaf at `base` did to self: the list is shorter by a bounded number of nodes,
    /// all from what the leaf's process held, and the leaf's hidden node is still dead, its owner kept. A slot's run
    /// can hold binding nodes, so the bound threads are those before whose binding nodes are still live.
    pub open spec fn leaf_sliced(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let object = self.tables.owner@[base].0;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& post.list.seq@.len() < self.list.seq@.len()
        &&& self.list.seq@.len() - post.list.seq@.len() <= LEAF_SLICE_BUDGET
        &&& post.tables.owner == self.tables.owner
        &&& post.list.parent == self.list.parent
        &&& !post.list.nodes@[base as int].live
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables).restrict(live_nodes(&post.list))
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object })
    }

    /// How many of the leaf's slots from slot k on hold a live node.
    pub open spec fn live_slots_from(&self, base: usize, k: int) -> nat
        decreases NODES_PER_PAGE - k,
    {
        if k < 1 || k >= NODES_PER_PAGE {
            0
        } else {
            (if self.list.nodes@[base + k].live { 1nat } else { 0nat }) + self.live_slots_from(base, k + 1)
        }
    }

    /// How many of the leaf's slots hold a live node.
    pub open spec fn leaf_live_slots(&self, base: usize) -> nat {
        self.live_slots_from(base, 1)
    }

    /// Every live slot of the leaf at `base` has no child, so a slice deletes each slot it reaches
    /// rather than revoking below it.
    pub open spec fn leaf_slots_childless(&self, base: usize) -> bool {
        forall|j: int| 1 <= j < NODES_PER_PAGE && (#[trigger] self.list.nodes@[base + j]).live
            ==> self.list.childless((base + j) as usize)
    }

    /// Capability n is a frame capability on block br, or a space, thread or process capability whose
    /// object's block is br.
    pub open spec fn cap_names_block(&self, n: usize, br: BlockRef) -> bool {
        let p = self.payload_of(n);
        &&& self.is_cap(n)
        &&& {
            ||| p.kind is Frame && br == block_ref(&self.blocks, p.base / PAGE_SZ)
            ||| (p.kind is Space || p.kind is Thread || p.kind is Process) && br == BlockRef::Small(p.base / PAGE_SZ)
        }
    }

    /// A slot of the leaf at `base` holds a capability naming block br.
    pub open spec fn leaf_slot_names(&self, base: usize, br: BlockRef) -> bool {
        exists|n: usize| base < n < base + NODES_PER_PAGE && #[trigger] self.cap_names_block(n, br)
    }

    /// What a slice of a leaf whose live slots are childless leaves as it was: every typed block but
    /// those its slots' capabilities name keeps its references and its dead flag; every space but those
    /// its slots name keeps its holders, and the space roots, records, loaded cores, bindings and kernel
    /// entries are as they were; the thread and process records, the table pages, the stale epochs,
    /// the flush epoch, the cores and the IOMMUs are as they were. The tables are as they were, so is
    /// every root entry and every payload. Only the leaf's slots die, and every node keeps its depth,
    /// so every slot of every table, and every capability outside the leaf, is as it was.
    pub open spec fn leaf_slice_kept(&self, post: Self, base: usize) -> bool {
        &&& forall|br: BlockRef| #[trigger] block_typed(&post.blocks, br) == block_typed(&self.blocks, br)
        &&& forall|br: BlockRef| #![trigger block_refs(&post.blocks, br)] #![trigger block_dead(&post.blocks, br)]
            block_typed(&self.blocks, br) && !self.leaf_slot_names(base, br) ==> {
                &&& block_refs(&post.blocks, br) == block_refs(&self.blocks, br)
                &&& block_dead(&post.blocks, br) == block_dead(&self.blocks, br)
            }
        &&& post.spaces.roots == self.spaces.roots
        &&& post.spaces.records == self.spaces.records
        &&& post.spaces.loaded == self.spaces.loaded
        &&& post.spaces.bound == self.spaces.bound
        &&& post.spaces.kernel_entries == self.spaces.kernel_entries
        &&& post.spaces.registers == self.spaces.registers
        &&& post.spaces.kernel_root == self.spaces.kernel_root
        &&& forall|s: usize| !self.leaf_slot_names(base, BlockRef::Small(s / PAGE_SZ))
            ==> #[trigger] post.spaces.holders@[s] == self.spaces.holders@[s]
        &&& post.threads.records == self.threads.records
        &&& post.processes.records == self.processes.records
        &&& post.table_pages == self.table_pages
        &&& post.stale_epoch == self.stale_epoch
        &&& post.flush_epoch == self.flush_epoch
        &&& post.cores == self.cores
        &&& post.iommus == self.iommus
        &&& post.tables == self.tables
        &&& forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && !(base < x < base + NODES_PER_PAGE) ==> {
            &&& post.list.nodes@[x].live == self.list.nodes@[x].live
            &&& post.list.nodes@[x].kind == self.list.nodes@[x].kind
        }
        &&& forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] post.list.nodes@[x].depth == self.list.nodes@[x].depth
        &&& forall|x: usize| page_of(x) != base ==> #[trigger] post.is_cap(x) == self.is_cap(x)
        &&& forall|t: usize, i: usize| #[trigger] post.tables.has_slot(&post.list, t, i) == self.tables.has_slot(&self.list, t, i)
    }

    /// Takes a slice of the dead leaf at `base`, under the untyped at index `from` of the table at `root`:
    /// up to a budget of nodes from its slots' runs, each slot going itself once childless. Returns
    /// whether it ran, and if not nothing changed. Dead slots stay dead while the leaf's hidden node is,
    /// since lookup refuses such a leaf, so a
    /// slice can walk them once and the next starts again from the first.
    pub fn slice_leaf(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + (NODES_PER_PAGE - 1) + LEAF_SLICE_BUDGET * (REVOKE_STEP_STEPS + 1),
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_slice_leaf(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).leaf_sliced(*final(self), root, from, base),
            ret && old(self).leaf_slots_childless(base) ==> old(self).leaf_slice_kept(*final(self), base),
            ret && old(self).leaf_slots_childless(base) && old(self).leaf_live_slots(base) <= LEAF_SLICE_BUDGET
                ==> final(self).leaf_is_empty(base),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, 1) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        proof {
            lemma2_to64();
            pre.lemma_leaf_in_range(base);
        }
        if !self.blocks.page_tracked(page) {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_leaf = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::TableLeaf) => entry.refs == 0,
            _ => false,
        };
        proof {
            pre.lemma_dead_leaf_block(base);
        }
        if !dead_leaf {
            return false;
        }
        let ghost object = pre.tables.owner@[base].0;
        proof {
            lemma_no_change_discharges_teardown(pre.view(), root, untyped, object);
            assert(!pre.list.nodes@[base + 0int].live);
            lemma_bound_threads_live(&pre.list, &pre.tables);
            lemma_slot_in_leaf(base, (NODES_PER_PAGE - 1) as usize);
            pre.lemma_slot_bound((base + NODES_PER_PAGE - 1) as usize);
        }
        // With every live slot childless, each slot the slice reaches is deleted, and one step is one
        // live slot gone; few says the budget covers all of them.
        let ghost kept = pre.leaf_slots_childless(base);
        let ghost few = kept && pre.leaf_live_slots(base) <= LEAF_SLICE_BUDGET;
        // A slot skipped is one iteration; a slot revoked is one more and its revoke step's.
        let ghost start = steps.count;
        let mut taken = 0;
        let mut k = 1;
        while taken != LEAF_SLICE_BUDGET && k != NODES_PER_PAGE && self.flush_epoch != usize::MAX
            invariant
                start == old(steps).count,
                steps.count <= start + (k - 1) + taken * (REVOKE_STEP_STEPS + 1),
                Self::mappings_shrunk(*old(self), *self),
                self.wf(),
                pre == *old(self),
                taken <= LEAF_SLICE_BUDGET,
                1 <= k <= NODES_PER_PAGE,
                base % LEAF_BYTES == 0,
                pre.tables.owner@.contains_key(base),
                object == pre.tables.owner@[base].0,
                pre.view().holds_right(root, untyped, Right::Retype),
                self.tables.owner == pre.tables.owner,
                self.list.parent == pre.list.parent,
                pre.list.seq@.len() == self.list.seq@.len() + taken,
                !self.list.nodes@[base as int].live,
                taken == 0 ==> *self == pre,
                taken > 0 ==> !pre.leaf_is_empty(base) && pre.flush_epoch < usize::MAX,
                forall|j: int| 0 <= j < k ==> !(#[trigger] self.list.nodes@[base + j]).live,
                discharges(pre.view(), self.view(), root, Effect::Teardown { untyped, object }),
                forall|h: (ObjectId, NodeId)| #[trigger] self.view().held.contains(h) ==> pre.view().held.contains(h),
                bound_threads(&self.list, &self.tables) == bound_threads(&pre.list, &pre.tables).restrict(live_nodes(&self.list)),
                base + NODES_PER_PAGE <= NODE_SPACE,
                forall|x: usize| #[trigger] self.is_cap(x) ==> pre.is_cap(x),
                few ==> kept,
                kept ==> self.tables == pre.tables,
                kept ==> forall|j: int| k <= j < NODES_PER_PAGE
                    ==> (#[trigger] self.list.nodes@[base + j]).live == pre.list.nodes@[base + j].live,
                kept ==> self.leaf_slots_childless_from(base, k as int),
                kept ==> forall|i: usize| pre.blocks.tracks(i as int) ==> #[trigger] block_ref(&self.blocks, i) == block_ref(&pre.blocks, i),
                kept ==> pre.leaf_slice_kept(*self, base),
                few ==> taken + self.live_slots_from(base, k as int) == pre.leaf_live_slots(base),
            decreases LEAF_SLICE_BUDGET - taken, NODES_PER_PAGE - k,
        {
            proof {
                steps.step();
                self.lemma_leaf_slot_valid(base, k);
                lemma_slot_in_leaf(base, k);
                self.lemma_slot_bound((base + k) as usize);
            }
            let n = base + k;
            if !self.list.get(n).live {
                proof {
                    assert(!self.list.nodes@[base + k as int].live);
                }
                k = k + 1;
                continue;
            }
            proof {
                self.lemma_live_slot_is_cap(n);
                if taken == 0 {
                    assert(pre.list.nodes@[base + k as int].live);
                }
            }
            proof {
                assert(steps.count + REVOKE_STEP_STEPS <= start + (k - 1) + (taken + 1) * (REVOKE_STEP_STEPS + 1)) by (nonlinear_arith)
                    requires
                        steps.count <= start + (k - 1) + taken * (REVOKE_STEP_STEPS + 1) + 1,
                ;
            }
            let ghost mid = *self;
            if !self.revoke_step(Ghost(object), n, Tracked(&mut *steps)) {
                proof {
                    if kept {
                        // A childless slot's revoke has nothing to do.
                        assert(mid.list.nodes@[base + k as int].live);
                        assert(mid.list.childless(n));
                    }
                    let r = choose|r: usize| #[trigger] revoked_one(mid.list, self.list, n, r)
                        && (mid.list.nodes@[r as int].kind is Mapping ==> Self::mapping_unlinked(mid, *self, r))
                        && (mid.list.nodes@[r as int].kind is Mapping ==> Self::mapping_stale_noted(mid, *self, r))
                        && (mid.hidden_table(r) ==> Self::table_unlinked(mid, *self, r))
                        && (mid.list.nodes@[r as int].kind is Binding ==> bound_threads(&self.list, &self.tables)
                            == bound_threads(&mid.list, &mid.tables).remove(r))
                        && (!(mid.list.nodes@[r as int].kind is Binding) ==> bound_threads(&self.list, &self.tables)
                            == bound_threads(&mid.list, &mid.tables));
                    Self::lemma_revoke_bound_threads(bound_threads(&pre.list, &pre.tables), mid, *self, r);
                    assert(mid.view().holds(object, n));
                    lemma_revoke_is_teardown(mid.view(), self.view(), object, n);
                    Self::lemma_slice_step(pre, mid, *self, root, untyped, object);
                    Self::lemma_leaf_slots_stay_dead(mid, *self, base, k as int, r);
                }
                taken = taken + 1;
                continue;
            }
            self.unlink_childless_slot(n, Tracked(&mut *steps));
            proof {
                Self::lemma_revoke_bound_threads(bound_threads(&pre.list, &pre.tables), mid, *self, n);
                assert(mid.view().holds(object, n));
                lemma_delete_is_teardown(mid.view(), self.view(), object, n);
                Self::lemma_slice_step(pre, mid, *self, root, untyped, object);
                Self::lemma_leaf_slots_stay_dead(mid, *self, base, k as int, n);
                if kept {
                    let post = *self;
                    assert(mid.list.nodes@[base + k as int].live);
                    assert forall|j: int| k + 1 <= j < NODES_PER_PAGE
                        implies (#[trigger] post.list.nodes@[base + j]).live == pre.list.nodes@[base + j].live by {
                        assert(post.list.nodes@[base + j].live == mid.list.nodes@[base + j].live);
                    }
                    assert forall|j: int| k + 1 <= j < NODES_PER_PAGE && (#[trigger] post.list.nodes@[base + j]).live
                        implies post.list.childless((base + j) as usize) by {
                        assert(mid.list.nodes@[base + j].live);
                        assert(mid.list.nodes@[((base + j) as usize) as int].live);
                        assert(mid.list.childless((base + j) as usize));
                    }
                    Self::lemma_slice_kept_step(pre, mid, post, base, n);
                    if few {
                        assert(mid.live_slots_from(base, k as int) == 1 + mid.live_slots_from(base, k + 1));
                        Self::lemma_live_slots_same(mid, post, base, k + 1);
                    }
                }
            }
            taken = taken + 1;
            k = k + 1;
        }
        proof {
            assert(taken * (REVOKE_STEP_STEPS + 1) <= LEAF_SLICE_BUDGET * (REVOKE_STEP_STEPS + 1)) by (nonlinear_arith)
                requires
                    taken <= LEAF_SLICE_BUDGET,
            ;
            if few && taken != 0 {
                if k != NODES_PER_PAGE {
                    Self::lemma_live_slots_none(*self, base, k as int);
                }
                assert forall|j: int| 0 <= j < NODES_PER_PAGE implies !(#[trigger] self.list.nodes@[base + j]).live by {
                    if j >= k {
                        assert(!self.list.nodes@[base + j].live);
                    }
                }
            }
        }
        taken != 0
    }

    /// Every live slot of the leaf at `base` from slot k on has no child.
    pub open spec fn leaf_slots_childless_from(&self, base: usize, k: int) -> bool {
        forall|j: int| k <= j < NODES_PER_PAGE && (#[trigger] self.list.nodes@[base + j]).live
            ==> self.list.childless((base + j) as usize)
    }

    /// Counts that agree on which slots from k on are live agree.
    proof fn lemma_live_slots_same(a: Self, b: Self, base: usize, k: int)
        requires
            1 <= k <= NODES_PER_PAGE,
            forall|j: int| k <= j < NODES_PER_PAGE ==> (#[trigger] a.list.nodes@[base + j]).live == b.list.nodes@[base + j].live,
        ensures
            a.live_slots_from(base, k) == b.live_slots_from(base, k),
        decreases NODES_PER_PAGE - k,
    {
        if k < NODES_PER_PAGE {
            assert(a.list.nodes@[base + k].live == b.list.nodes@[base + k].live);
            Self::lemma_live_slots_same(a, b, base, k + 1);
        }
    }

    /// No slot from k on is live when none is counted.
    proof fn lemma_live_slots_none(s: Self, base: usize, k: int)
        requires
            1 <= k <= NODES_PER_PAGE,
            s.live_slots_from(base, k) == 0,
        ensures
            forall|j: int| k <= j < NODES_PER_PAGE ==> !(#[trigger] s.list.nodes@[base + j]).live,
        decreases NODES_PER_PAGE - k,
    {
        if k < NODES_PER_PAGE {
            Self::lemma_live_slots_none(s, base, k + 1);
        }
    }

    /// Deleting the childless capability in slot n of the leaf at `base` keeps what a childless slice
    /// keeps: the block it changes is one the leaf's slots name, and every page stays in its block.
    proof fn lemma_slice_kept_step(pre: Self, mid: Self, post: Self, base: usize, n: usize)
        requires
            mid.wf(),
            base % LEAF_BYTES == 0,
            base < n < base + NODES_PER_PAGE,
            mid.is_cap(n),
            pre.is_cap(n),
            mid.tables == pre.tables,
            forall|i: usize| pre.blocks.tracks(i as int) ==> #[trigger] block_ref(&mid.blocks, i) == block_ref(&pre.blocks, i),
            pre.leaf_slice_kept(mid, base),
            Self::object_dropped(mid, post, n),
            post.table_pages == mid.table_pages,
            post.stale_epoch == mid.stale_epoch,
            post.flush_epoch == mid.flush_epoch,
            post.tables == mid.tables,
            post.cores == mid.cores,
            post.iommus == mid.iommus,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==> #[trigger] post.list.nodes@[x].live == mid.list.nodes@[x].live,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==> #[trigger] post.list.nodes@[x].kind == mid.list.nodes@[x].kind,
            forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] post.list.nodes@[x].depth == mid.list.nodes@[x].depth,
        ensures
            forall|i: usize| pre.blocks.tracks(i as int) ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            pre.leaf_slice_kept(post, base),
    {
        let p = mid.payload_of(n);
        if p.kind is Frame {
            lemma_holder_refs(&mid.list, &mid.tables, &mid.blocks, &mid.zeroing, mid.holders@, n);
            let br = block_ref(&mid.blocks, p.base / PAGE_SZ);
            assert(pre.cap_names_block(n, br));
            assert(pre.leaf_slot_names(base, br));
        } else if p.kind is Space || p.kind is Thread || p.kind is Process {
            let br = BlockRef::Small(p.base / PAGE_SZ);
            assert(pre.cap_names_block(n, br));
            assert(pre.leaf_slot_names(base, br));
        }
        assert forall|s: usize| !pre.leaf_slot_names(base, BlockRef::Small(s / PAGE_SZ))
            implies #[trigger] post.spaces.holders@[s] == pre.spaces.holders@[s] by {
            assert(mid.spaces.holders@[s] == pre.spaces.holders@[s]);
            if p.kind is Space {
                assert(pre.cap_names_block(n, BlockRef::Small(p.base / PAGE_SZ)));
                assert(s != p.base);
            }
        }
        assert forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && !(base < x < base + NODES_PER_PAGE) implies {
            &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
            &&& post.list.nodes@[x].kind == pre.list.nodes@[x].kind
        } by {
            assert(x != n);
            assert(mid.list.nodes@[x].live == pre.list.nodes@[x].live);
        }
        assert forall|x: int| 0 <= x < NODE_SPACE implies #[trigger] post.list.nodes@[x].depth == pre.list.nodes@[x].depth by {
            assert(mid.list.nodes@[x].depth == pre.list.nodes@[x].depth);
        }
        Self::lemma_slice_kept_slots(mid, pre, post, base);
    }

    /// A step that kills only slots of the leaf at `base` and changes no node's kind outside them, with
    /// the tables as they were, leaves every slot of every table and every capability outside the leaf
    /// as it was: a slot's leaf is aligned, so its hidden node is no slot of `base`. Any state s that
    /// is well formed with the same tables bounds the nodes.
    proof fn lemma_slice_kept_slots(s: Self, pre: Self, post: Self, base: usize)
        requires
            s.wf(),
            s.tables == pre.tables,
            post.tables == pre.tables,
            base % LEAF_BYTES == 0,
            forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && !(base < x < base + NODES_PER_PAGE) ==> {
                &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
                &&& post.list.nodes@[x].kind == pre.list.nodes@[x].kind
            },
        ensures
            forall|x: usize| page_of(x) != base ==> #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|t: usize, i: usize| #[trigger] post.tables.has_slot(&post.list, t, i) == pre.tables.has_slot(&pre.list, t, i),
    {
        assert forall|x: usize| page_of(x) != base implies #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            if pre.tables.owner@.contains_key(page_of(x)) && x % PAGE_SZ < NODES_PER_PAGE {
                s.lemma_slot_bound(x);
                if base < x < base + NODES_PER_PAGE {
                    lemma_slot_in_leaf(base, (x - base) as usize);
                }
                assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
            }
        }
        assert forall|t: usize, i: usize| #[trigger] post.tables.has_slot(&post.list, t, i)
            == pre.tables.has_slot(&pre.list, t, i) by {
            let leaf = pre.tables.leaf(t, index_entry(i));
            if index_ok(i) && pre.tables.roots@.contains_key(t) && leaf != NO_LEAF {
                s.tables.lemma_entry(t, index_entry(i));
                s.tables.lemma_leaf(&s.list, leaf);
                lemma_slot_in_leaf(leaf, 0);
                s.lemma_slot_bound(leaf);
                if base < leaf < base + NODES_PER_PAGE {
                    lemma_slot_in_leaf(base, (leaf - base) as usize);
                }
                assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
            }
        }
    }

    /// An owned leaf's block is in the block table's range.
    proof fn lemma_leaf_in_range(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.tables.owner@.contains_key(base) ==> self.blocks.tracks_addr(base),
    {
    }

    /// A step that only removes capabilities, with the owners as they were, leaves every process holding
    /// a subset of what it held.
    proof fn lemma_held_shrinks(pre: Self, post: Self)
        requires
            post.tables.owner == pre.tables.owner,
            forall|x: usize| #[trigger] post.is_cap(x) ==> pre.is_cap(x),
        ensures
            forall|h: (ObjectId, NodeId)| #[trigger] post.view().held.contains(h) ==> pre.view().held.contains(h),
    {
        assert forall|h: (ObjectId, NodeId)| #[trigger] post.view().held.contains(h) implies pre.view().held.contains(h) by {
            assert(post.is_cap(h.1));
        }
    }

    /// One more slice of the object's teardown after a teardown under the untyped: the whole is a
    /// teardown under the untyped, and what is held still shrinks.
    proof fn lemma_slice_step(pre: Self, mid: Self, post: Self, root: usize, untyped: usize, object: usize)
        requires
            discharges(pre.view(), mid.view(), root, Effect::Teardown { untyped, object }),
            tears_down(mid.view(), post.view(), object),
            mid.list.parent == pre.list.parent,
            post.tables.owner == mid.tables.owner,
            forall|x: usize| #[trigger] post.is_cap(x) ==> mid.is_cap(x),
            forall|h: (ObjectId, NodeId)| #[trigger] mid.view().held.contains(h) ==> pre.view().held.contains(h),
        ensures
            discharges(pre.view(), post.view(), root, Effect::Teardown { untyped, object }),
            forall|h: (ObjectId, NodeId)| #[trigger] post.view().held.contains(h) ==> pre.view().held.contains(h),
    {
        Self::lemma_held_shrinks(mid, post);
        lemma_teardown_steps_compose(pre.view(), mid.view(), post.view(), root, untyped, object);
    }

    /// A step that removes node r alone keeps the leaf's hidden node and its first k slots dead.
    proof fn lemma_leaf_slots_stay_dead(pre: Self, post: Self, base: usize, k: int, r: usize)
        requires
            pre.wf(),
            pre.tables.owner@.contains_key(base),
            0 <= k <= NODES_PER_PAGE,
            !pre.list.nodes@[base as int].live,
            forall|j: int| 0 <= j < k ==> !(#[trigger] pre.list.nodes@[base + j]).live,
            !post.list.nodes@[r as int].live,
            forall|x: int| 0 <= x < NODE_SPACE && x != r ==> #[trigger] post.list.nodes@[x].live == pre.list.nodes@[x].live,
        ensures
            !post.list.nodes@[base as int].live,
            forall|j: int| 0 <= j < k ==> !(#[trigger] post.list.nodes@[base + j]).live,
    {
        pre.lemma_leaf_slot_valid(base, 0);
        pre.list.lemma_valid_bound(base);
        assert forall|j: int| 0 <= j < k implies !(#[trigger] post.list.nodes@[base + j]).live by {
            pre.lemma_leaf_slot_valid(base, j as usize);
            pre.list.lemma_valid_bound((base + j) as usize);
        }
    }

    /// Unlinks the childless capability in slot n, and nothing more.
    fn unlink_childless_slot(&mut self, n: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).is_cap(n),
            old(self).list.childless(n),
        ensures
            final(steps).count == old(steps).count,
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            final(self).tables.owner == old(self).tables.owner,
            final(self).list.parent == old(self).list.parent,
            final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            !final(self).list.nodes@[n as int].live,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==>
                #[trigger] final(self).list.nodes@[x].live == old(self).list.nodes@[x].live,
            forall|x: usize| #[trigger] final(self).is_cap(x) ==> old(self).is_cap(x),
            removes_cap(old(self).view(), final(self).view(), n),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            Self::object_dropped(*old(self), *final(self), n),
            final(self).tables == old(self).tables,
            final(self).table_pages == old(self).table_pages,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            forall|x: usize| x != n && x < NODE_SPACE && old(self).list.nodes@[x as int].live && old(self).list.childless(x)
                ==> #[trigger] final(self).list.childless(x),
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==>
                #[trigger] final(self).list.nodes@[x].kind == old(self).list.nodes@[x].kind,
            forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] final(self).list.nodes@[x].depth == old(self).list.nodes@[x].depth,
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_leaf_node_not_first(n);
        }
        self.unlink_arm(n, Tracked(steps));
        self.list.remove_leaf(n);
        proof {
            let post = *self;
            post.tables.lemma_wf_same_pages(&pre.list, &post.list);
            assert(Self::caps_frame(pre, post, n, n));
            Self::lemma_delete_caps_wf(pre, post, n);
            let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == n
                && post.list.seq@ == pre.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == pre.list.seq@[0]);
            lemma_parents_removed(pre.list, post.list, n);
            Self::lemma_revoke_hidden(pre, post, n);
            Self::lemma_bindings_caps_frame(pre, post, n, n);
            Self::lemma_delete_holders(pre, post, n);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_delete_removes(pre, post, n);
            assert forall|x: usize| #[trigger] post.is_cap(x) implies pre.is_cap(x) by {
                if x != n {
                    Self::lemma_caps_frame(pre, post, n, n, x);
                }
            }
            Self::lemma_bound_threads_same(pre, post);
            assert forall|c: usize| post.list.seq@.contains(c) implies pre.list.seq@.contains(c) by {
                let i = choose|i: int| 0 <= i < post.list.seq@.len() && post.list.seq@[i] == c;
                if i < p {
                    assert(pre.list.seq@[i] == c);
                } else {
                    assert(pre.list.seq@[i + 1] == c);
                }
            }
            assert forall|x: usize| x != n && x < NODE_SPACE && pre.list.nodes@[x as int].live && pre.list.childless(x)
                implies #[trigger] post.list.childless(x) by {
                lemma_childless_kept(&pre.list, &post.list, x);
            }
        }
    }

    /// Frees the leaf at `base`, under the untyped at index `from` of the table at `root`, once its block
    /// is at zero references and no node in its page is live. All of these come from user space, and
    /// anything but a free changes nothing.
    pub fn free_leaf(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + NODES_PER_PAGE + 2 * (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) && old(self).acknowledged((base / PAGE_SZ + 1) as usize) {
                    ret is Freed
                } else {
                    ret is Again
                },
            ret is Again ==> !old(self).acknowledged(base / PAGE_SZ) || !old(self).acknowledged((base / PAGE_SZ + 1) as usize),
            ret is Freed ==> old(self).leaf_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, 1) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            proof {
                pre.lemma_empty_leaf_in_range(base);
            }
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let leaf = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::TableLeaf) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_dead_leaf_block(base);
        }
        if !leaf || !self.leaf_nodes_dead(base, Tracked(&mut *steps)) {
            return ReclaimStep::Refused;
        }
        proof {
            // A leaf's block is 2 pages, aligned to them, so the second lies in the range too.
            assert(self.blocks.tracks_run(page as int, 2)) by {
                assert(base % LEAF_BYTES == 0);
                assert(page == base / PAGE_SZ);
            }
        }
        if !self.is_acknowledged(page, Tracked(&mut *steps)) || !self.is_acknowledged(page + 1, Tracked(&mut *steps)) {
            return ReclaimStep::Again;
        }
        proof {
            assert(pre.tables.owner@.contains_key(base));
            pre.lemma_leaf_unmapped(page, page);
            pre.lemma_leaf_unmapped(page, (page + 1) as usize);
            pre.lemma_acknowledged_is_clean(page);
            pre.lemma_acknowledged_is_clean((page + 1) as usize);
        }
        self.free_empty_leaf(base, Tracked(steps));
        proof {
            let post = *self;
            assert(post.view() == pre.view());
            let v = pre.view();
            let e = Effect::Teardown { untyped, object: base };
            assert(authorized(v, root, e));
        }
        ReclaimStep::Freed
    }

    /// Frees the empty table page at `base`, once every core and IOMMU has acknowledged the epoch that
    /// recorded its cut. It refuses a block that is anything else.
    // In a solver of its own: in the module's shared solver, the queries before it leave too little of
    // its budget.
    #[verifier::spinoff_prover]
    pub fn free_table(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + TABLE_NODE_PAGES * (NODES_PER_PAGE + 1) + ENTRIES + (NUM_CPUS + NUM_IOMMUS)
                + (TABLE_NODE_PAGES + SMALL_PAGES_MAX),
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            ret is Again ==> !old(self).acknowledged(base / PAGE_SZ),
            ret is Freed ==> old(self).table_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
            if pre.table_is_empty(base) {
                pre.lemma_empty_table(base);
            }
        }
        let untyped = match self.retype_parent(root, from, base, 3) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let table = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::TablePage) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_dead_table_block(base);
        }
        if !table || !self.table_nothing_left(base, Tracked(&mut *steps)) {
            return ReclaimStep::Refused;
        }
        if !self.is_acknowledged(page, Tracked(&mut *steps)) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_acknowledged_is_clean(page);
        }
        self.free_empty_table(base, Tracked(steps));
        proof {
            let post = *self;
            assert(post.view() == pre.view());
            let v = pre.view();
            let e = Effect::Teardown { untyped, object: base };
            assert(authorized(v, root, e));
            assert(pre.table_freed(post, c, root, from, base));
        }
        ReclaimStep::Freed
    }

    /// Whether every node of the table page at `base` is dead and every entry empty. A table page holds a
    /// constant number of each.
    fn table_nothing_left(&self, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(base),
        ensures
            final(steps).count <= old(steps).count + TABLE_NODE_PAGES * (NODES_PER_PAGE + 1) + ENTRIES,
            ret == self.table_is_empty(base),
    {
        let ghost tree = tree_of(&self.table_pages, &self.spaces);
        proof {
            self.lemma_table_page_room(base);
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        }
        if !self.block_nodes_dead(base, Tracked(&mut *steps)) {
            return false;
        }
        let ghost steps0 = steps.count;
        let mut e = 0;
        while e != ENTRIES
            invariant
                0 <= e <= ENTRIES,
                steps0 <= old(steps).count + TABLE_NODE_PAGES * (NODES_PER_PAGE + 1),
                steps.count == steps0 + e,
                self.wf(),
                self.table_pages.maps@.contains_key(base),
                tree == tree_of(&self.table_pages, &self.spaces),
                forall|j: usize, i: usize| #![trigger table_node(base, j, i)] j < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                    ==> !self.list.nodes@[table_node(base, j, i) as int].live,
                forall|j: usize| #![trigger self.table_pages.maps@[base].value()[j]]
                    j < e ==> self.table_pages.maps@[base].value()[j].is_empty(),
            decreases ENTRIES - e,
        {
            let entry = self.table_entry(base, false, e);
            proof {
                assert(tree.is_page(base));
                assert(tree.entry(base, e) == self.table_pages.maps@[base].value()[e]);
            }
            if !entry_is_empty(&entry) {
                return false;
            }
            e = e + 1;
            proof {
                steps.step();
            }
        }
        true
    }

    /// Whether every node in the node pages of the table page or space at `base` is dead. The pages hold a
    /// constant number.
    fn block_nodes_dead(&self, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            base % TABLE_PAGE_BYTES == 0,
            self.blocks.tracks_addr_run(base, 8),
            forall|k: usize| k < TABLE_NODE_PAGES ==> self.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
        ensures
            final(steps).count <= old(steps).count + TABLE_NODE_PAGES * (NODES_PER_PAGE + 1),
            ret == (forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> !self.list.nodes@[table_node(base, k, i) as int].live),
    {
        let ghost steps0 = steps.count;
        let mut k = 0;
        while k != TABLE_NODE_PAGES
            invariant
                0 <= k <= TABLE_NODE_PAGES,
                steps0 == old(steps).count,
                steps.count == steps0 + k * (NODES_PER_PAGE + 1),
                self.wf(),
                base % TABLE_PAGE_BYTES == 0,
                self.blocks.tracks_addr_run(base, 8),
                forall|k: usize| k < TABLE_NODE_PAGES ==> self.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
                forall|j: usize, i: usize| #![trigger table_node(base, j, i)] j < k && i < NODES_PER_PAGE
                    ==> !self.list.nodes@[table_node(base, j, i) as int].live,
            decreases TABLE_NODE_PAGES - k,
        {
            let mut i = 0;
            while i != NODES_PER_PAGE
                invariant
                    0 <= k < TABLE_NODE_PAGES,
                    0 <= i <= NODES_PER_PAGE,
                    steps0 == old(steps).count,
                    steps.count == steps0 + k * (NODES_PER_PAGE + 1) + i,
                    self.wf(),
                    base % TABLE_PAGE_BYTES == 0,
                    self.blocks.tracks_addr_run(base, 8),
                    forall|k: usize| k < TABLE_NODE_PAGES ==> self.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
                    forall|j: usize, m: usize| #![trigger table_node(base, j, m)] j < k && m < NODES_PER_PAGE
                        ==> !self.list.nodes@[table_node(base, j, m) as int].live,
                    forall|m: usize| #![trigger table_node(base, k, m)] m < i
                        ==> !self.list.nodes@[table_node(base, k, m) as int].live,
                decreases NODES_PER_PAGE - i,
            {
                proof {
                    lemma_table_node_place(base, k, i);
                    assert(self.list.pages@.dom().contains(table_node_page(base, k)));
                    assert(self.list.valid(table_node(base, k, i)));
                }
                if self.list.get(base + k * PAGE_SZ + i).live {
                    proof {
                        assert(k * (NODES_PER_PAGE + 1) + i <= TABLE_NODE_PAGES * (NODES_PER_PAGE + 1)) by (nonlinear_arith)
                            requires k < TABLE_NODE_PAGES, i <= NODES_PER_PAGE;
                    }
                    return false;
                }
                i = i + 1;
                proof {
                    steps.step();
                }
            }
            proof {
                assert((k + 1) * (NODES_PER_PAGE + 1) == k * (NODES_PER_PAGE + 1) + (NODES_PER_PAGE + 1)) by (nonlinear_arith);
            }
            k = k + 1;
            proof {
                steps.step();
            }
        }
        true
    }

    /// Whether the root of the device space at `base` has no entry. A space's node pages hold no live node.
    fn space_nothing_left(&self, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            self.dead_io_space(base),
            !self.table_pages.maps@.contains_key(base),
        ensures
            final(steps).count <= old(steps).count + ENTRIES,
            ret == self.space_is_empty(base),
    {
        let ghost tree = tree_of(&self.table_pages, &self.spaces);
        let ghost steps0 = steps.count;
        let mut e = 0;
        while e != ENTRIES
            invariant
                0 <= e <= ENTRIES,
                steps0 == old(steps).count,
                steps.count == steps0 + e,
                self.wf(),
                self.dead_io_space(base),
                !self.table_pages.maps@.contains_key(base),
                tree == tree_of(&self.table_pages, &self.spaces),
                forall|j: usize, i: usize| #![trigger table_node(base, j, i)] j < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                    ==> !self.list.nodes@[table_node(base, j, i) as int].live,
                forall|j: usize| #![trigger self.spaces.roots@[base].value()[j]]
                    j < e ==> self.spaces.roots@[base].value()[j].is_empty(),
            decreases ENTRIES - e,
        {
            let entry = self.table_entry(base, true, e);
            proof {
                assert(!tree.is_page(base));
                assert(tree.entry(base, e) == self.spaces.roots@[base].value()[e]);
            }
            if !entry_is_empty(&entry) {
                return false;
            }
            e = e + 1;
            proof {
                steps.step();
            }
        }
        true
    }

    /// Whether every node of the owned leaf at `base` is dead. A leaf's page holds a constant number.
    fn leaf_nodes_dead(&self, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            self.tables.owner@.contains_key(base),
        ensures
            final(steps).count <= old(steps).count + NODES_PER_PAGE,
            ret == self.leaf_is_empty(base),
    {
        let ghost steps0 = steps.count;
        let mut k = 0;
        while k != NODES_PER_PAGE
            invariant
                0 <= k <= NODES_PER_PAGE,
                steps0 == old(steps).count,
                steps.count == steps0 + k,
                self.wf(),
                self.tables.owner@.contains_key(base),
                forall|j: int| 0 <= j < k ==> !(#[trigger] self.list.nodes@[base + j]).live,
            decreases NODES_PER_PAGE - k,
        {
            proof {
                self.lemma_leaf_slot_valid(base, k);
            }
            if self.list.get(base + k).live {
                return false;
            }
            k = k + 1;
            proof {
                steps.step();
            }
        }
        true
    }

    /// Both pages of an empty leaf go back to the block table, its block's teardown being finished, and
    /// the root entry its parent record names is cleared in the same step.
    fn free_empty_leaf(&mut self, base: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).leaf_is_empty(base),
            old(self).blocks.pages@[(base / PAGE_SZ) as int].refs == 0,
            old(self).no_stale_translation(base / PAGE_SZ),
            old(self).no_stale_translation((base / PAGE_SZ + 1) as usize),
        ensures
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            final(self).blocks.pages@[(base / PAGE_SZ) as int].kind is Free,
            final(self).blocks.pages@[base / PAGE_SZ + 1int].kind is Free,
            final(self).tables.owner@ == old(self).tables.owner@.remove(base),
            final(self).tables.roots@.dom() == old(self).tables.roots@.dom(),
            final(self).tables.leaf(old(self).tables.owner@[base].0, old(self).tables.owner@[base].1) == NO_LEAF,
            forall|t: usize, s: int| #![trigger final(self).tables.leaf(t, s)] old(self).tables.roots@.contains_key(t)
                && 0 <= s < ROOT_ENTRIES && !(t == old(self).tables.owner@[base].0 && s == old(self).tables.owner@[base].1)
                ==> final(self).tables.leaf(t, s) == old(self).tables.leaf(t, s),
            !final(self).list.pages@.dom().contains(base),
            final(self).list.seq == old(self).list.seq,
            final(self).list.parent == old(self).list.parent,
            final(self).list.nodes == old(self).list.nodes,
            final(self).list.pages@.dom() == old(self).list.pages@.dom().remove(base),
            final(self).tables.payloads@.dom() == old(self).tables.payloads@.dom().remove(base),
            forall|n: usize| #[trigger] final(self).tables.is_cap(&final(self).list, n) == old(self).tables.is_cap(&old(self).list, n),
            forall|n: usize| page_of(n) != base ==> #[trigger] final(self).tables.payload_of(n) == old(self).tables.payload_of(n),
            forall|i: int| old(self).blocks.tracks(i) && !((base / PAGE_SZ) as int <= i < base / PAGE_SZ + 2)
                ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i],
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).spaces == old(self).spaces,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).view() == old(self).view(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let page = base / PAGE_SZ;
        proof {
            pre.lemma_empty_leaf(base);
        }
        self.blocks.mark_torn_down(page);
        let ghost mid = *self;
        let Tracked(payloads) = self.tables.give_back_leaf(&self.list, base);
        let Tracked(nodes) = self.list.remove_page(base);
        let tracked mut perms = Map::<usize, PagePerm4k>::tracked_empty();
        proof {
            let tracked mut nodes = nodes;
            nodes.leak_contents();
            let tracked first = crate::layouts::node_page_into_page(nodes);
            perms.tracked_insert(page, first);
            perms.tracked_insert((page + 1) as usize, payloads);
            Self::lemma_leaf_perms(perms, base);
        }
        self.blocks.free_block(page, Tracked(perms), Tracked(steps));
        proof {
            let post = *self;
            assert forall|i: int| pre.blocks.tracks(i) implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            Self::lemma_leaf_freed(pre, post, base);
            Self::lemma_leaf_freed_caps(pre, post, base);
            Self::lemma_bound_threads_same(pre, post);
            assert(pre.blocks.in_block(page as int, page as int));
            assert(pre.blocks.in_block(page as int, page + 1int));
            assert forall|i: int| pre.blocks.tracks(i) && !(page as int <= i < page + 2)
                implies #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i] by {
                assert(!pre.blocks.in_block(page as int, i));
            }
        }
    }

    /// An empty leaf's block is in the block table's range, so a block outside it is not one.
    proof fn lemma_empty_leaf_in_range(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.leaf_is_empty(base) ==> self.blocks.tracks_addr(base),
    {
    }

    /// The block test free_leaf makes reads as the node does: a table leaf block at zero references is
    /// an owned leaf's whose hidden node is dead, and such a leaf's block is a dead table leaf block at
    /// zero. An empty leaf is one.
    proof fn lemma_dead_leaf_block(&self, base: usize)
        requires
            self.wf(),
            base % LEAF_BYTES == 0,
            self.blocks.tracks_addr(base),
        ensures
            (leaf_block(&self.blocks, base / PAGE_SZ) && self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0)
                == (self.tables.owner@.contains_key(base) && !self.list.nodes@[base as int].live),
            self.leaf_is_empty(base) ==> !self.list.nodes@[base as int].live,
    {
        lemma_leaf_page(base);
        if leaf_block(&self.blocks, base / PAGE_SZ) {
            assert(self.tables.owner@.contains_key(((base / PAGE_SZ) * PAGE_SZ) as usize));
        }
        if self.leaf_is_empty(base) {
            assert(!self.list.nodes@[base + 0int].live);
        }
    }

    /// Slot k of an owned leaf is a node the list holds.
    proof fn lemma_leaf_slot_valid(&self, base: usize, k: usize)
        requires
            self.wf(),
            self.tables.owner@.contains_key(base),
            k < NODES_PER_PAGE,
        ensures
            base + k <= usize::MAX,
            self.list.valid((base + k) as usize),
            (base + k) as usize as int == base + k as int,
    {
        self.tables.lemma_leaf(&self.list, base);
        lemma_list_page(&self.list, base);
        lemma_slot_in_leaf(base, k);
    }

    /// What the invariant says of an empty leaf's block and pages, before it frees.
    proof fn lemma_empty_leaf(&self, base: usize)
        requires
            self.wf(),
            self.leaf_is_empty(base),
        ensures
            base % LEAF_BYTES == 0,
            base % PAGE_SZ == 0,
            self.blocks.tracks_addr(base),
            self.blocks.tracks_addr_run(base, 2),
            (base / PAGE_SZ) * PAGE_SZ == base,
            self.blocks.pages@[(base / PAGE_SZ) as int].kind is Base,
            self.blocks.pages@[(base / PAGE_SZ) as int].object is TableLeaf,
            self.blocks.pages@[(base / PAGE_SZ) as int].order == 1,
            self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0,
            self.blocks.pages@[(base / PAGE_SZ) as int].dead,
            self.blocks.pages@[base / PAGE_SZ + 1int].kind is Member,
            !self.list.nodes@[base as int].live,
            self.list.pages@.dom().contains(base),
            self.list.pages@[base].addr() == base,
            self.list.pages@[base].is_init(),
    {
        let page = base / PAGE_SZ;
        self.tables.lemma_leaf(&self.list, base);
        lemma_leaf_page(base);
        lemma_list_page(&self.list, base);
        assert(!self.list.nodes@[base + 0int].live);
        self.blocks.lemma_base(page as int);
        self.blocks.lemma_member_of(page as int, page + 1int);
    }

    /// The two pages of the leaf at `base` are what its block's free needs: the first and the second,
    /// each at its own address and uninitialised.
    proof fn lemma_leaf_perms(perms: Map<usize, PagePerm4k>, base: usize)
        requires
            base % PAGE_SZ == 0,
            (base / PAGE_SZ) * PAGE_SZ == base,
            perms.contains_key(base / PAGE_SZ),
            perms.contains_key((base / PAGE_SZ + 1) as usize),
            perms[base / PAGE_SZ].addr() == base,
            perms[base / PAGE_SZ].is_uninit(),
            perms[(base / PAGE_SZ + 1) as usize].addr() == base + PAGE_SZ,
            perms[(base / PAGE_SZ + 1) as usize].is_uninit(),
        ensures
            forall|k: usize| k < order_pages(1) ==> {
                &&& perms.contains_key((base / PAGE_SZ + k) as usize)
                &&& #[trigger] perms[(base / PAGE_SZ + k) as usize].addr() == (base / PAGE_SZ + k) * PAGE_SZ
                &&& perms[(base / PAGE_SZ + k) as usize].is_uninit()
            },
    {
        let page = base / PAGE_SZ;
        assert forall|k: usize| k < order_pages(1) implies {
            &&& perms.contains_key((page + k) as usize)
            &&& #[trigger] perms[(page + k) as usize].addr() == (page + k) * PAGE_SZ
            &&& perms[(page + k) as usize].is_uninit()
        } by {
            if k == 0 {
                assert((page + k) as usize == page);
            } else {
                assert(k == 1);
                assert((page + k) as usize == (page + 1) as usize);
            }
        }
    }

    /// The block of the empty leaf at `base` is its two pages, and nothing else the invariant tracks
    /// lies in it: no other leaf, no other list page and no holder's block.
    proof fn lemma_leaf_block_alone(&self, base: usize)
        requires
            self.wf(),
            self.leaf_is_empty(base),
        ensures
            forall|l: usize| #[trigger] self.tables.owner@.contains_key(l) && l != base
                ==> !self.blocks.in_block((base / PAGE_SZ) as int, (l / PAGE_SZ) as int),
            forall|p: usize| #[trigger] self.list.pages@.dom().contains(p) && p != base
                ==> !self.blocks.in_block((base / PAGE_SZ) as int, (p / PAGE_SZ) as int),
            forall|b: usize| #[trigger] self.holders@.contains_key(BlockRef::Small(b))
                ==> !self.blocks.in_block((base / PAGE_SZ) as int, b as int),
    {
        let page = base / PAGE_SZ;
        self.lemma_empty_leaf(base);
        assert forall|l: usize| #[trigger] self.tables.owner@.contains_key(l) && l != base
            implies !self.blocks.in_block(page as int, (l / PAGE_SZ) as int) by {
            self.tables.lemma_leaf(&self.list, l);
            lemma_leaf_pages_distinct(l, base);
            assert(self.blocks.pages@[(l / PAGE_SZ) as int].kind is Base);
        }
        assert forall|p: usize| #[trigger] self.list.pages@.dom().contains(p) && p != base
            implies !self.blocks.in_block(page as int, (p / PAGE_SZ) as int) by {
            lemma_list_page(&self.list, p);
            if p / PAGE_SZ == page {
                lemma_same_page(p, base);
            }
            if self.blocks.in_block(page as int, (p / PAGE_SZ) as int) {
                self.blocks.lemma_member_of(page as int, (p / PAGE_SZ) as int);
                assert(self.blocks.pages@[page as int].object is TablePage);
            }
        }
        assert forall|b: usize| #[trigger] self.holders@.contains_key(BlockRef::Small(b))
            implies !self.blocks.in_block(page as int, b as int) by {
            assert(block_typed(&self.blocks, BlockRef::Small(b)));
            assert(self.blocks.pages@[b as int].object is Frame);
        }
    }

    /// The tables and the view after the empty leaf at `base` goes: its owner entry went, no capability
    /// was in it, so every capability is as it was and says the same.
    proof fn lemma_leaf_freed_caps(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            pre.leaf_is_empty(base),
            post.tables.wf(&pre.list),
            post.tables.owner@ == pre.tables.owner@.remove(base),
            post.tables.payloads@ == pre.tables.payloads@.remove(base),
            forall|n: usize| #[trigger] post.tables.is_cap(&pre.list, n) == pre.tables.is_cap(&pre.list, n),
            forall|n: usize| page_of(n) != base ==> #[trigger] post.tables.payload_of(n) == pre.tables.payload_of(n),
            post.list.nodes == pre.list.nodes,
            post.list.parent == pre.list.parent,
            post.list.pages@.dom() == pre.list.pages@.dom().remove(base),
            Self::same_tree(pre, post),
            post.devices == pre.devices,
        ensures
            post.tables.wf(&post.list),
            post.tables.caps_wf(&post.list),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x)
                ==> page_of(x) != base && post.tables.payload_of(x) == pre.tables.payload_of(x),
            post.view() == pre.view(),
    {
        assert(post.tables.leaves_wf(&post.list)) by {
            reveal(Tables::leaves_wf);
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies post.tables.leaf_wf(&post.list, l) by {
                assert(post.tables.leaf_wf(&pre.list, l));
                assert(post.list.pages@.dom().contains(l));
            }
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x) by {
            assert(post.tables.is_cap(&post.list, x) == post.tables.is_cap(&pre.list, x));
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x)
            implies page_of(x) != base && post.tables.payload_of(x) == pre.tables.payload_of(x) by {
            if page_of(x) == base {
                assert(x as int == base + (x % PAGE_SZ) as int);
                assert(!pre.list.nodes@[base + (x % PAGE_SZ) as int].live);
            }
        }
        let (a, b) = (pre.view(), post.view());
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) == a.held.contains(h) by {
            if pre.tables.is_cap(&pre.list, h.1) {
                assert(post.tables.owner@[page_of(h.1)] == pre.tables.owner@[page_of(h.1)]);
            }
        }
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

    /// The block table's invariants after the empty leaf at `base` goes: its two pages are free, and
    /// every other block, leaf and list page is as it was.
    proof fn lemma_leaf_freed_blocks(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            pre.leaf_is_empty(base),
            post.blocks.wf(),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / PAGE_SZ) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.tables.owner@ == pre.tables.owner@.remove(base),
            post.list.nodes == pre.list.nodes,
            post.list.parent == pre.list.parent,
            post.list.pages@.dom() == pre.list.pages@.dom().remove(base),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.mappings == pre.mappings,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            zeroing_typed(&post.zeroing, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let page = base / PAGE_SZ;
        pre.lemma_empty_leaf(base);
        pre.lemma_leaf_block_alone(base);
        lemma_leaf_block_unkeyed(&pre.tables, &pre.blocks, pre.holders@, base);
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
            pre.lemma_mapping_node_page(m);
            assert(leaf_block(&pre.blocks, page));
            assert(page_of(m) != base);
            assert(post.list.valid(m));
            assert(block_ref(&pre.blocks, pre.mappings@[m].frame) != BlockRef::Small(page));
            lemma_block_ref_small_freed(&pre.blocks, &post.blocks, page, pre.mappings@[m].frame);
        }
        Self::lemma_mappings_same_tree(pre, post);
        lemma_holders_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, page);
        assert(pre.holders@.remove(BlockRef::Small(page)) =~= pre.holders@);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@);
        assert forall|b: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(b))
            implies post.blocks.pages@[b as int].object is Frame by {
            assert(block_typed(&pre.blocks, BlockRef::Small(b)));
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && (#[trigger] post.blocks.pages@[b as int]).kind is Base
            && post.blocks.pages@[b as int].object is Frame implies {
            &&& post.blocks.pages@[b as int].order == 0
            &&& post.blocks.pages@[b as int].refs == 0 ==> post.holders@.contains_key(BlockRef::Small(b))
        } by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& post.blocks.tracks_addr(l)
            &&& post.blocks.pages@[(l / PAGE_SZ) as int] == pre.blocks.pages@[(l / PAGE_SZ) as int]
        } by {
            assert(pre.tables.owner@.contains_key(l));
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && #[trigger] leaf_block(&post.blocks, b)
            implies post.tables.owner@.contains_key((b * PAGE_SZ) as usize) by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
            assert(leaf_block(&pre.blocks, b));
            lemma_page_base(b);
        }
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
            implies !pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) by {
            assert(pre.list.pages@.dom().contains(p));
            assert(p != base);
        }
        lemma_list_pages_used_subset(&pre.list, &post.list, &pre.blocks);
        lemma_list_pages_used_small_freed(&post.list, &pre.blocks, &post.blocks, page);
        lemma_table_node_pages_kept(&pre.list, &post.list, &pre.table_pages, &pre.blocks, base);
        lemma_table_pages_small_freed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, page);
        lemma_space_node_pages_kept(&pre.list, &post.list, &pre.tables, &pre.spaces, &pre.blocks, base);
        lemma_spaces_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page);
        lemma_thread_node_pages_kept(&pre.list, &post.list, &pre.tables, &pre.threads, &pre.blocks, base);
        lemma_threads_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page);
        lemma_processes_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page);
    }

    /// The kernel after the empty leaf at `base` frees: nothing but its block, its owner entry and its
    /// list page changed, and the view is as it was.
    proof fn lemma_leaf_freed(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            pre.leaf_is_empty(base),
            post.blocks.wf(),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / PAGE_SZ) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.tables.wf(&pre.list),
            post.tables.owner@ == pre.tables.owner@.remove(base),
            post.tables.payloads@ == pre.tables.payloads@.remove(base),
            post.tables.roots@.dom() == pre.tables.roots@.dom(),
            forall|n: usize| #[trigger] post.tables.is_cap(&pre.list, n) == pre.tables.is_cap(&pre.list, n),
            forall|n: usize| page_of(n) != base ==> #[trigger] post.tables.payload_of(n) == pre.tables.payload_of(n),
            post.list.wf(),
            post.list.seq == pre.list.seq,
            post.list.parent == pre.list.parent,
            post.list.nodes == pre.list.nodes,
            post.list.pages@.dom() == pre.list.pages@.dom().remove(base),
            post.holders == pre.holders,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
        ensures
            post.wf(),
            post.view() == pre.view(),
    {
        pre.lemma_empty_leaf(base);
        Self::lemma_leaf_freed_caps(pre, post, base);
        Self::lemma_devices_same_caps(pre, post);
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Process implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            assert(post.tables.is_cap(&pre.list, x));
        }
        lemma_binding_parents_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert forall|x: usize| #[trigger] pre.is_cap(x) && pre.payload_of(x).kind is Space
            implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            assert(post.tables.is_cap(&pre.list, x));
        }
        Self::lemma_device_bindings_space_caps(pre, post);
        Self::lemma_leaf_freed_blocks(pre, post, base);
        Self::lemma_tlb_same(pre, post);
        assert forall|n: usize| n < NODE_SPACE && (#[trigger] post.list.nodes@[n as int]).live
            && post.list.nodes@[n as int].kind is Hidden
            implies post.tables.owner@.contains_key(n) || post.table_pages.maps@.contains_key(n) by {
            assert(pre.tables.owner@.contains_key(n) || pre.table_pages.maps@.contains_key(n));
            assert(n != base);
        }
        assert forall|n: usize| n < NODE_SPACE && (#[trigger] post.list.nodes@[n as int]).live
            && post.list.nodes@[n as int].kind is Capability && n != post.list.seq@[0]
            implies post.tables.is_cap(&post.list, n) by {
            assert(pre.tables.is_cap(&pre.list, n));
        }
    }

    /// The table page at `base` has no live node and no entry, so its block holds nothing the kernel
    /// still uses.
    pub open spec fn table_is_empty(&self, base: usize) -> bool {
        &&& self.table_pages.maps@.contains_key(base)
        &&& forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            ==> !self.list.nodes@[table_node(base, k, i) as int].live
        &&& forall|i: usize| #![trigger self.table_pages.maps@[base].value()[i]]
            i < ENTRIES ==> self.table_pages.maps@[base].value()[i].is_empty()
    }

    /// The block at `base` holds a table page or a space, with no reference and no live node.
    pub open spec fn empty_node_block(&self, base: usize) -> bool {
        &&& base % TABLE_PAGE_BYTES == 0
        &&& self.blocks.tracks_addr_run(base, 8)
        &&& self.blocks.pages@[(base / PAGE_SZ) as int].kind is Base
        &&& self.blocks.pages@[(base / PAGE_SZ) as int].object is TablePage
            || self.blocks.pages@[(base / PAGE_SZ) as int].object is Space
        &&& self.blocks.pages@[(base / PAGE_SZ) as int].order == 3
        &&& self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0
        &&& forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            ==> !self.list.nodes@[table_node(base, k, i) as int].live
        &&& forall|k: usize| k < TABLE_NODE_PAGES ==> self.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
    }

    /// A table page with a frame's entry or a child's entry present is not empty.
    pub proof fn lemma_table_with_entry_not_empty(&self, base: usize, e: usize)
        requires
            frame_slot(tree_of(&self.table_pages, &self.spaces), base, e)
                || tree_of(&self.table_pages, &self.spaces).names_child(base, e),
        ensures
            !self.table_is_empty(base),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        if self.table_is_empty(base) {
            assert(e < ENTRIES);
            assert(self.table_pages.maps@[base].value()[e].is_empty());
            assert(tree.is_page(base));
            assert(tree.entry(base, e) == self.table_pages.maps@[base].value()[e]);
        }
    }

    /// What the invariant says of an empty table page's block and pages, before it frees.
    proof fn lemma_empty_table(&self, base: usize)
        requires
            self.wf(),
            self.table_is_empty(base),
        ensures
            base % TABLE_PAGE_BYTES == 0,
            base % PAGE_SZ == 0,
            base as int == PAGE_SZ * (base / PAGE_SZ) as int,
            (base / PAGE_SZ) % 8 == 0,
            self.blocks.tracks_addr_run(base, 8),
            self.blocks.pages@[(base / PAGE_SZ) as int].kind is Base,
            self.blocks.pages@[(base / PAGE_SZ) as int].object is TablePage,
            self.blocks.pages@[(base / PAGE_SZ) as int].order == 3,
            self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0,
            self.blocks.pages@[(base / PAGE_SZ) as int].dead,
            !self.list.nodes@[base as int].live,
            self.table_pages.records@[base].value().parent is None,
            !self.spaces.roots@.contains_key(base),
            self.table_pages.maps@[base].addr() == base + 5 * PAGE_SZ,
            self.table_pages.records@.contains_key(base),
            self.table_pages.records@[base].addr() == base + 6 * PAGE_SZ,
            self.table_pages.spare@.contains_key((base + 7 * PAGE_SZ) as usize),
            self.table_pages.spare@[(base + 7 * PAGE_SZ) as usize].addr() == base + 7 * PAGE_SZ,
            self.table_pages.spare@[(base + 7 * PAGE_SZ) as usize].is_uninit(),
            forall|k: usize| k < TABLE_NODE_PAGES ==> self.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            self.empty_node_block(base),
    {
        let page = base / PAGE_SZ;
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        lemma_table_page_aligned(base);
        self.blocks.lemma_base(page as int);
        assert(order_pages(3) == 8);
        assert(table_node(base, 0, 0) == base);
        assert(!self.list.nodes@[table_node(base, 0, 0) as int].live);
        if self.spaces.roots@.contains_key(base) {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
        }
    }

    /// A live node of the list is in no node page of an empty block.
    proof fn lemma_live_node_outside_block(&self, base: usize, n: usize)
        requires
            self.wf(),
            self.empty_node_block(base),
            self.list.valid(n),
            self.list.nodes@[n as int].live,
        ensures
            !(base <= page_of(n) < base + TABLE_NODE_PAGES * PAGE_SZ),
    {
        lemma_table_page_aligned(base);
        lemma_list_page(&self.list, page_of(n));
        if base <= page_of(n) < base + TABLE_NODE_PAGES * PAGE_SZ {
            let k = ((page_of(n) - base) / PAGE_SZ as int) as usize;
            let i = (n % PAGE_SZ) as usize;
            assert(page_of(n) == base + k * PAGE_SZ);
            assert(n == page_of(n) + i);
            assert(k < TABLE_NODE_PAGES);
            assert(table_node(base, k, i) == n);
            assert(!self.list.nodes@[table_node(base, k, i) as int].live);
        }
    }

    /// No leaf and no holder's block lies in the empty block at `base`.
    proof fn lemma_node_block_alone(&self, base: usize)
        requires
            self.wf(),
            self.empty_node_block(base),
        ensures
            forall|l: usize| #[trigger] self.tables.owner@.contains_key(l)
                ==> !self.blocks.in_block((base / PAGE_SZ) as int, (l / PAGE_SZ) as int) && !(base <= l < base + TABLE_NODE_PAGES * PAGE_SZ),
            forall|b: usize| #[trigger] self.holders@.contains_key(BlockRef::Small(b))
                ==> !self.blocks.in_block((base / PAGE_SZ) as int, b as int),
    {
        let page = base / PAGE_SZ;
        lemma_table_page_aligned(base);
        assert(order_pages(3) == 8);
        assert forall|l: usize| #[trigger] self.tables.owner@.contains_key(l) implies
            !self.blocks.in_block(page as int, (l / PAGE_SZ) as int) && !(base <= l < base + TABLE_NODE_PAGES * PAGE_SZ) by {
            self.tables.lemma_leaf(&self.list, l);
            let x = (l / PAGE_SZ) as int;
            assert(self.blocks.pages@[x].kind is Base);
            assert(self.blocks.pages@[x].object is TableLeaf);
            if self.blocks.in_block(page as int, x) && x != page {
                self.blocks.lemma_member_of(page as int, x);
            }
        }
        assert forall|b: usize| #[trigger] self.holders@.contains_key(BlockRef::Small(b))
            implies !self.blocks.in_block(page as int, b as int) by {
            assert(block_typed(&self.blocks, BlockRef::Small(b)));
            assert(self.blocks.pages@[b as int].object is Frame);
            if self.blocks.in_block(page as int, b as int) && b != page {
                self.blocks.lemma_member_of(page as int, b as int);
            }
        }
    }

    /// What an empty table page's or space's block going does alike: the block is free, its node pages are
    /// off the list, and nothing else changed but what held its other three pages. The list held none of
    /// them.
    pub open spec fn node_block_freed_step(pre: Self, post: Self, base: usize) -> bool {
        let page = base / PAGE_SZ;
        &&& pre.wf()
        &&& pre.empty_node_block(base)
        &&& post.blocks.wf()
        &&& forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
            if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] })
        &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@
        &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@
        &&& post.tables == pre.tables
        &&& post.list.wf()
        &&& post.list.seq == pre.list.seq
        &&& post.list.parent == pre.list.parent
        &&& post.list.nodes == pre.list.nodes
        &&& forall|p: usize| #[trigger] post.list.pages@.dom().contains(p)
            == (pre.list.pages@.dom().contains(p) && !(base <= p < base + TABLE_NODE_PAGES * PAGE_SZ))
        &&& forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> !(base + 5 * PAGE_SZ <= p < base + 8 * PAGE_SZ)
        &&& post.holders == pre.holders
        &&& post.cores == pre.cores
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.iommus == pre.iommus
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.mappings == pre.mappings
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.processes == pre.processes
    }

    /// One step of an empty table page going: its table, record and spare page go with its block.
    pub open spec fn table_freed_step(pre: Self, post: Self, base: usize) -> bool {
        &&& Self::node_block_freed_step(pre, post, base)
        &&& pre.table_is_empty(base)
        &&& post.table_pages.maps@ == pre.table_pages.maps@.remove(base)
        &&& post.table_pages.records@ == pre.table_pages.records@.remove(base)
        &&& post.table_pages.spare@ == pre.table_pages.spare@.remove((base + 7 * PAGE_SZ) as usize)
        &&& post.spaces == pre.spaces
    }

    /// The tree after the empty table page at `base` goes.
    proof fn lemma_table_freed_tree(pre: Self, post: Self, base: usize)
        requires
            Self::table_freed_step(pre, post, base),
        ensures
            table_removed(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base),
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        pre.lemma_empty_table(base);
        assert(a.is_page(base));
        assert forall|i: usize| i < ENTRIES implies #[trigger] a.entry(base, i).is_empty() by {
            assert(pre.table_pages.maps@[base].value()[i].is_empty());
        }
        assert(table_removed(a, b, base));
        lemma_links_table_removed(a, b, base);
        assert forall|t: usize, e: usize| #[trigger] frame_slot(a, t, e) implies {
            &&& frame_slot(b, t, e)
            &&& b.record(t).level == a.record(t).level
            &&& b.entry(t, e) == a.entry(t, e)
        } by {
            if t == base {
                assert(a.entry(base, e).is_empty());
            }
            lemma_table_removed_others(a, b, base, t);
            assert(b.entry(t, e) == a.entry(t, e));
        }
        assert forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) implies frame_slot(a, t, e) by {
            assert(t != base);
            lemma_table_removed_others(a, b, base, t);
            assert(b.entry(t, e) == a.entry(t, e));
        }
    }

    /// The threads and the processes after a table page's or a space's block frees: every thread and
    /// every process lies outside it, and no capability naming one changed.
    proof fn lemma_node_block_threads(pre: Self, post: Self, base: usize)
        requires
            Self::node_block_freed_step(pre, post, base),
            pre.blocks.pages@[(base / PAGE_SZ) as int].kind is Base,
            !(pre.blocks.pages@[(base / PAGE_SZ) as int].object is Thread),
            !(pre.blocks.pages@[(base / PAGE_SZ) as int].object is Process),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / PAGE_SZ) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        let page = base / PAGE_SZ;
        Self::lemma_node_block_list_pages(pre, post, base);
        lemma_table_page_aligned(base);
        assert(order_pages(3) == 8);
        lemma_threads_outside_block(&pre.list, &pre.tables, &pre.threads, &pre.blocks, page);
        assert forall|t: usize| #[trigger] pre.threads.records@.contains_key(t) implies post.list.pages@.dom().contains(t) by {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
            assert(!pre.blocks.in_block(page as int, (t / PAGE_SZ) as int));
            assert(!(base <= t < base + TABLE_NODE_PAGES * PAGE_SZ));
        }
        lemma_threads_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page);
        lemma_processes_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page);
    }

    /// A list page after the step is in no page of the freed block.
    proof fn lemma_node_block_list_pages(pre: Self, post: Self, base: usize)
        requires
            Self::node_block_freed_step(pre, post, base),
        ensures
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                ==> !pre.blocks.in_block((base / PAGE_SZ) as int, (p / PAGE_SZ) as int),
    {
        let page = base / PAGE_SZ;
        lemma_table_page_aligned(base);
        assert(order_pages(3) == 8);
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
            implies !pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) by {
            assert(pre.list.pages@.dom().contains(p));
            lemma_list_page(&pre.list, p);
            assert(!(base <= p < base + 5 * PAGE_SZ));
            assert(!(base + 5 * PAGE_SZ <= p < base + 8 * PAGE_SZ));
        }
    }

    /// The table pages and the spaces after the empty table page at `base` goes: every other one's node
    /// pages lie in its own block.
    proof fn lemma_table_freed_pages(pre: Self, post: Self, base: usize)
        requires
            Self::table_freed_step(pre, post, base),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
    {
        let page = base / PAGE_SZ;
        pre.lemma_empty_table(base);
        Self::lemma_node_block_list_pages(pre, post, base);
        assert(order_pages(3) == 8);
        Self::lemma_table_freed_table_pages(pre, post, base);
        assert forall|s: usize, k: usize| #[trigger] pre.spaces.roots@.contains_key(s) && pre.spaces.records@[s].value().kind is Device
            && k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
            assert(pre.list.pages@.dom().contains(table_node_page(s, k)));
            assert(s != base);
            pre.blocks.lemma_base((s / PAGE_SZ) as int);
            lemma_table_node_page(s, k);
        }
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_spaces_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page);
        Self::lemma_node_block_threads(pre, post, base);
        lemma_list_pages_used_subset(&pre.list, &post.list, &pre.blocks);
        lemma_list_pages_used_small_freed(&post.list, &pre.blocks, &post.blocks, page);
    }

    /// The table pages after the empty table page at `base` goes: every other one keeps its block, its
    /// node pages and its empty entries.
    proof fn lemma_table_freed_table_pages(pre: Self, post: Self, base: usize)
        requires
            Self::table_freed_step(pre, post, base),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        let page = base / PAGE_SZ;
        pre.lemma_empty_table(base);
        Self::lemma_node_block_list_pages(pre, post, base);
        assert(order_pages(3) == 8);
        assert forall|t: usize| #[trigger] post.table_pages.maps@.contains_key(t)
            implies table_page_wf(&post.list, &post.table_pages, &post.blocks, t) by {
            assert(t != base);
            assert(pre.table_pages.maps@.contains_key(t));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
            lemma_table_pages_distinct(t, base);
            pre.blocks.lemma_base((t / PAGE_SZ) as int);
            if pre.blocks.in_block(page as int, (t / PAGE_SZ) as int) && t / PAGE_SZ != page {
                pre.blocks.lemma_member_of(page as int, (t / PAGE_SZ) as int);
            }
            assert(post.blocks.pages@[(t / PAGE_SZ) as int] == pre.blocks.pages@[(t / PAGE_SZ) as int]);
            assert(post.table_pages.spare@[(t + 7 * PAGE_SZ) as usize] == pre.table_pages.spare@[(t + 7 * PAGE_SZ) as usize]);
            assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
                assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
                lemma_table_node_page(t, k);
            }
            assert forall|i: usize| #![trigger post.table_pages.maps@[t].value()[i]]
                i < ENTRIES && !post.table_pages.records@[t].value().written implies post.table_pages.maps@[t].value()[i].is_empty() by {
                assert(pre.table_pages.maps@[t].value()[i].is_empty());
            }
        }
        assert forall|x: usize| post.blocks.tracks(x as int) && #[trigger] table_block(&post.blocks, x)
            implies post.table_pages.maps@.contains_key((x * PAGE_SZ) as usize) by {
            if pre.blocks.in_block(page as int, x as int) {
                assert(post.blocks.pages@[x as int] == free_entry());
            }
            assert(post.blocks.pages@[x as int] == pre.blocks.pages@[x as int]);
            assert(table_block(&pre.blocks, x));
            assert(x != page);
            assert((x * PAGE_SZ) as usize != base);
        }
    }

    /// The holders, the objects and the mappings after the empty block at `base` goes: no holder is on it,
    /// no capability names it, and no mapping is in it.
    proof fn lemma_node_block_objects(pre: Self, post: Self, base: usize)
        requires
            Self::node_block_freed_step(pre, post, base),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            zeroing_typed(&post.zeroing, &post.blocks),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let page = base / PAGE_SZ;
        lemma_table_page_aligned(base);
        pre.lemma_node_block_alone(base);
        assert(order_pages(3) == 8);
        assert(pre.blocks.in_block(page as int, page as int));
        assert(!pre.holders@.contains_key(BlockRef::Small(page)));
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m
        ) by {
            pre.lemma_mapping_node(m);
            pre.lemma_live_node_outside_block(base, m);
            assert(post.list.pages@.dom().contains(page_of(m)));
            assert(post.list.valid(m));
            if let BlockRef::Small(b) = block_ref(&pre.blocks, pre.mappings@[m].frame) {
                assert(pre.holders@.contains_key(BlockRef::Small(b)));
            }
            assert(block_ref(&pre.blocks, pre.mappings@[m].frame) != BlockRef::Small(page));
            lemma_block_ref_small_freed(&pre.blocks, &post.blocks, page, pre.mappings@[m].frame);
        }
        lemma_mappings_kept(&pre.list, &pre.tables, tree_of(&pre.table_pages, &pre.spaces), &pre.blocks, pre.holders@,
            &post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@);
        lemma_holders_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, page);
        assert(pre.holders@.remove(BlockRef::Small(page)) =~= pre.holders@);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@);
        assert forall|b: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(b))
            implies post.blocks.pages@[b as int].object is Frame by {
            assert(block_typed(&pre.blocks, BlockRef::Small(b)));
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && (#[trigger] post.blocks.pages@[b as int]).kind is Base
            && post.blocks.pages@[b as int].object is Frame implies {
            &&& post.blocks.pages@[b as int].order == 0
            &&& post.blocks.pages@[b as int].refs == 0 ==> post.holders@.contains_key(BlockRef::Small(b))
        } by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& post.blocks.tracks_addr(l)
            &&& post.blocks.pages@[(l / PAGE_SZ) as int] == pre.blocks.pages@[(l / PAGE_SZ) as int]
        } by {
            assert(pre.tables.owner@.contains_key(l));
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && #[trigger] leaf_block(&post.blocks, b)
            implies post.tables.owner@.contains_key((b * PAGE_SZ) as usize) by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
            assert(leaf_block(&pre.blocks, b));
            lemma_page_base(b);
        }
    }

    /// The capabilities and the view after the empty block at `base` goes: no capability was in a page of
    /// it. What the device spaces map is the tables' to say, which the step leaves to its caller.
    proof fn lemma_node_block_caps(pre: Self, post: Self, base: usize)
        requires
            Self::node_block_freed_step(pre, post, base),
        ensures
            post.tables.wf(&post.list),
            post.tables.caps_wf(&post.list),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            post.view() == (State { shares: post.view().shares, ..pre.view() }),
    {
        pre.lemma_node_block_alone(base);
        assert(post.tables.leaves_wf(&post.list)) by {
            reveal(Tables::leaves_wf);
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies post.tables.leaf_wf(&post.list, l) by {
                assert(pre.tables.leaf_wf(&pre.list, l));
                assert(post.list.pages@.dom().contains(l));
            }
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x) by {}
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
        assert(b == (State { shares: b.shares, ..a }));
    }

    /// The kernel after the empty table page at `base` frees.
    proof fn lemma_table_freed(pre: Self, post: Self, base: usize)
        requires
            Self::table_freed_step(pre, post, base),
        ensures
            post.wf(),
            post.view() == pre.view(),
    {
        pre.lemma_empty_table(base);
        Self::lemma_kernel_root_freed(pre, post, (base / PAGE_SZ) as int);
        Self::lemma_node_block_caps(pre, post, base);
        lemma_binding_parents_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert forall|x: usize| #[trigger] pre.is_cap(x) && pre.payload_of(x).kind is Space
            implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            assert(post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x));
        }
        Self::lemma_device_bindings_space_caps(pre, post);
        Self::lemma_devices_same_caps(pre, post);
        Self::lemma_table_freed_tree(pre, post, base);
        lemma_table_removed_same_shares(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base);
        assert(post.view() == pre.view());
        Self::lemma_table_freed_pages(pre, post, base);
        Self::lemma_node_block_objects(pre, post, base);
        Self::lemma_tlb_same(pre, post);
        assert forall|n: usize| n < NODE_SPACE && (#[trigger] post.list.nodes@[n as int]).live
            && post.list.nodes@[n as int].kind is Hidden
            implies post.tables.owner@.contains_key(n) || post.table_pages.maps@.contains_key(n) by {
            assert(pre.tables.owner@.contains_key(n) || pre.table_pages.maps@.contains_key(n));
            assert(n != base);
        }
    }

    /// The block of the empty table page at `base` goes back to the block table: its node pages off the
    /// list, and its table, record and spare page turned back into page permissions.
    pub fn free_empty_table(&mut self, base: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).table_is_empty(base),
            old(self).blocks.pages@[(base / PAGE_SZ) as int].refs == 0,
            old(self).no_stale_translation(base / PAGE_SZ),
        ensures
            final(steps).count <= old(steps).count + TABLE_NODE_PAGES + SMALL_PAGES_MAX,
            final(self).wf(),
            final(self).blocks.pages@[(base / PAGE_SZ) as int].kind is Free,
            !final(self).table_pages.maps@.contains_key(base),
            forall|k: usize| k < TABLE_NODE_PAGES ==> !final(self).list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            forall|r: usize, p: SpacePath| #[trigger] walk(tree_of(&final(self).table_pages, &final(self).spaces), r, p)
                == walk(tree_of(&old(self).table_pages, &old(self).spaces), r, p),
            final(self).cores == old(self).cores,
            final(self).view() == old(self).view(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let page = base / PAGE_SZ;
        proof {
            pre.lemma_empty_table(base);
            crate::layouts::lemma_table_block_layouts();
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies pre.list.pages@[p].addr() == p by {
                lemma_list_page(&pre.list, p);
            }
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.table_pages.maps.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.table_pages.records.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.table_pages.spare.borrow().tracked_borrow((base + 7 * PAGE_SZ) as usize));
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies !(base + 5 * PAGE_SZ <= p < base + 8 * PAGE_SZ) by {
                lemma_list_page(&pre.list, p);
            }
        }
        self.blocks.mark_torn_down(page);
        let ghost mid = *self;
        let Tracked(nodes) = take_table_node_pages(&mut self.list, base, Tracked(&mut *steps));
        let tracked mut perms = nodes;
        proof {
            let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(base);
            let tracked mut record = self.table_pages.records.borrow_mut().tracked_remove(base);
            let tracked spare = self.table_pages.spare.borrow_mut().tracked_remove((base + 7 * PAGE_SZ) as usize);
            map.leak_contents();
            record.leak_contents();
            perms.tracked_insert((page + 5) as usize, crate::layouts::page_map_into_page(map));
            perms.tracked_insert((page + 6) as usize, crate::layouts::table_record_into_page(record));
            perms.tracked_insert((page + 7) as usize, spare);
            assert(self.blocks.pages@[page as int].order == 3);
            assert(order_pages(3) == 8);
            assert forall|k: usize| #![trigger perms.contains_key((page + k) as usize)] #![trigger perms[(page + k) as usize]]
                k < order_pages(self.blocks.pages@[page as int].order) implies {
                &&& perms.contains_key((page + k) as usize)
                &&& perms[(page + k) as usize].addr() == (page + k) * PAGE_SZ
                &&& perms[(page + k) as usize].is_uninit()
            } by {
                if k < 5 {
                    assert(holds_free_page(nodes, (page + k) as usize));
                }
            }
        }
        self.blocks.free_block(page, Tracked(perms), Tracked(steps));
        proof {
            let post = *self;
            assert forall|i: int| pre.blocks.tracks(i) implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            assert(Self::table_freed_step(pre, post, base));
            Self::lemma_table_freed(pre, post, base);
            Self::lemma_bound_threads_same(pre, post);
            Self::lemma_table_freed_tree(pre, post, base);
            assert forall|r: usize, p: SpacePath| #[trigger] walk(tree_of(&post.table_pages, &post.spaces), r, p)
                == walk(tree_of(&pre.table_pages, &pre.spaces), r, p) by {
                lemma_walk_table_removed(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base, r, p);
            }
            assert(pre.blocks.in_block(page as int, page as int));
            assert forall|k: usize| k < TABLE_NODE_PAGES implies !post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)) by {
                lemma_table_node_page(base, k);
            }
        }
    }

    /// The dead device space at `base` has no live node and its root no entry, so its block holds nothing the
    /// kernel still uses.
    pub open spec fn space_is_empty(&self, base: usize) -> bool {
        &&& self.dead_io_space(base)
        &&& forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            ==> !self.list.nodes@[table_node(base, k, i) as int].live
        &&& forall|i: usize| #![trigger self.spaces.roots@[base].value()[i]]
            i < ENTRIES ==> self.spaces.roots@[base].value()[i].is_empty()
    }

    /// The dead device space at `base` has nothing left to cut: no entry of its root names a child.
    pub open spec fn space_is_spent(&self, base: usize) -> bool {
        &&& self.dead_io_space(base)
        &&& !exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
    }

    /// A spent device space is empty, so cutting it to the end leaves what a free takes. A device root has no
    /// kernel slot, a present entry of it names a child since a root maps no frame, any other entry is
    /// empty, and a space's node pages hold no live node.
    pub proof fn lemma_spent_space_is_empty(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.space_is_spent(base) ==> self.space_is_empty(base),
    {
        if self.space_is_spent(base) {
            let tree = tree_of(&self.table_pages, &self.spaces);
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
            assert forall|i: usize| #![trigger self.spaces.roots@[base].value()[i]]
                i < ENTRIES implies self.spaces.roots@[base].value()[i].is_empty() by {
                assert(tree.entry(base, i) == self.spaces.roots@[base].value()[i]);
            }
        }
    }

    /// What the invariant says of an empty space's block and pages, before it frees. Its block has no
    /// reference, so it has no holder and no device bound, and no core ever loaded it.
    proof fn lemma_empty_space(&self, base: usize)
        requires
            self.wf(),
            self.space_is_empty(base),
        ensures
            self.empty_node_block(base),
            base % PAGE_SZ == 0,
            base as int == PAGE_SZ * (base / PAGE_SZ) as int,
            self.blocks.pages@[(base / PAGE_SZ) as int].dead,
            !self.table_pages.maps@.contains_key(base),
            self.spaces.roots@[base].addr() == base + 5 * PAGE_SZ,
            self.spaces.records@.contains_key(base),
            self.spaces.records@[base].addr() == base + 6 * PAGE_SZ,
            self.spaces.loaded@.contains_key(base),
            self.spaces.loaded@[base].addr() == base + 7 * PAGE_SZ,
            self.spaces.holders@[base] == Set::<usize>::empty(),
            self.spaces.bound@[base] == Set::<usize>::empty(),
            forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && e.space == base ==> !#[trigger] self.tlb@[c].contains(e),
            forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] self.loaded(c, base),
    {
        let page = (base / PAGE_SZ) as int;
        assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
        lemma_table_page_aligned(base);
        self.blocks.lemma_base(page);
        assert(order_pages(3) == 8);
        self.lemma_space_block(base);
        self.spaces.holders@[base].lemma_len0_is_empty();
        self.spaces.bound@[base].lemma_len0_is_empty();
        self.lemma_io_space_unloaded(base);
    }

    /// One step of an empty space going: its root, record and list of cores go with its block, and it
    /// leaves the maps of its holders and devices, which are empty.
    pub open spec fn space_freed_step(pre: Self, post: Self, base: usize) -> bool {
        &&& Self::node_block_freed_step(pre, post, base)
        &&& pre.space_is_empty(base)
        &&& post.table_pages == pre.table_pages
        &&& post.spaces.roots@ == pre.spaces.roots@.remove(base)
        &&& post.spaces.records@ == pre.spaces.records@.remove(base)
        &&& post.spaces.loaded@ == pre.spaces.loaded@.remove(base)
        &&& post.spaces.holders@ == pre.spaces.holders@.remove(base)
        &&& post.spaces.bound@ == pre.spaces.bound@.remove(base)
        &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
        &&& post.spaces.registers == pre.spaces.registers
        &&& post.spaces.kernel_root == pre.spaces.kernel_root
    }

    /// The tree after the empty space at `base` goes.
    proof fn lemma_space_freed_tree(pre: Self, post: Self, base: usize)
        requires
            Self::space_freed_step(pre, post, base),
        ensures
            space_removed(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base),
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        pre.lemma_empty_space(base);
        assert(!a.is_page(base));
        assert forall|i: usize| !#[trigger] a.names_child(base, i) by {
            if i < ENTRIES {
                assert(pre.spaces.roots@[base].value()[i].is_empty());
            }
        }
        assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, base));
        assert(space_removed(a, b, base));
        lemma_links_space_removed(a, b, base);
        assert forall|t: usize, e: usize| #[trigger] frame_slot(a, t, e) implies {
            &&& frame_slot(b, t, e)
            &&& b.record(t).level == a.record(t).level
            &&& b.entry(t, e) == a.entry(t, e)
        } by {
            assert(t != base);
            lemma_space_removed_others(a, b, base, t);
            assert(b.entry(t, e) == a.entry(t, e));
        }
        assert forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) implies frame_slot(a, t, e) by {
            assert(t != base);
            lemma_space_removed_others(a, b, base, t);
            assert(b.entry(t, e) == a.entry(t, e));
        }
    }

    /// Every table page's and every other space's node pages stay the list's when the space at `base`
    /// goes: each lies in its own block, apart from the freed one.
    proof fn lemma_space_freed_node_pages(pre: Self, post: Self, base: usize)
        requires
            table_pages_wf(&pre.list, &pre.table_pages, &pre.blocks),
            spaces_wf(&pre.list, &pre.tables, &pre.spaces, &pre.blocks),
            base % TABLE_PAGE_BYTES == 0,
            !pre.table_pages.maps@.contains_key(base),
            post.table_pages == pre.table_pages,
            post.spaces.roots@ == pre.spaces.roots@.remove(base),
            post.spaces.records@ == pre.spaces.records@.remove(base),
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p)
                == (pre.list.pages@.dom().contains(p) && !(base <= p < base + TABLE_NODE_PAGES * PAGE_SZ)),
        ensures
            forall|t: usize, k: usize| #[trigger] post.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
                ==> post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)),
            forall|s: usize, k: usize| #[trigger] post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device
                && k < TABLE_NODE_PAGES ==> post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)),
    {
        assert forall|t: usize, k: usize| #[trigger] post.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
            assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
            lemma_node_pages_disjoint(t, base, k);
        }
        assert forall|s: usize, k: usize| #[trigger] post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device
            && k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
            assert(post.spaces.records@[s] == pre.spaces.records@[s]);
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
            assert(pre.list.pages@.dom().contains(table_node_page(s, k)));
            lemma_node_pages_disjoint(s, base, k);
        }
    }

    /// The table pages and the spaces after the empty space at `base` goes: every other one's node pages
    /// lie in its own block.
    proof fn lemma_space_freed_pages(pre: Self, post: Self, base: usize)
        requires
            Self::space_freed_step(pre, post, base),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
    {
        let page = base / PAGE_SZ;
        pre.lemma_empty_space(base);
        Self::lemma_node_block_list_pages(pre, post, base);
        assert(order_pages(3) == 8);
        assert(pre.blocks.in_block(page as int, page as int));
        Self::lemma_space_freed_node_pages(pre, post, base);
        lemma_table_pages_small_freed(&pre.list, &post.list, &post.table_pages, &pre.blocks, &post.blocks, page);
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_spaces_space_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &post.spaces, &pre.blocks, &post.blocks, base);
        Self::lemma_node_block_threads(pre, post, base);
        lemma_list_pages_used_subset(&pre.list, &post.list, &pre.blocks);
        lemma_list_pages_used_small_freed(&post.list, &pre.blocks, &post.blocks, page);
    }

    /// The kernel after the empty space at `base` frees.
    proof fn lemma_space_freed(pre: Self, post: Self, base: usize)
        requires
            Self::space_freed_step(pre, post, base),
        ensures
            post.wf(),
            post.view() == pre.view(),
    {
        pre.lemma_empty_space(base);
        Self::lemma_kernel_root_freed(pre, post, (base / PAGE_SZ) as int);
        Self::lemma_node_block_caps(pre, post, base);
        lemma_binding_parents_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert forall|x: usize| #[trigger] pre.is_cap(x) && pre.payload_of(x).kind is Space
            implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            assert(post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x));
        }
        lemma_bound_kept_empty(pre.spaces.bound@, base);
        Self::lemma_device_bindings_space_caps(pre, post);
        Self::lemma_devices_same_caps(pre, post);
        Self::lemma_space_freed_tree(pre, post, base);
        lemma_space_removed_same_shares(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base);
        assert(post.view() == pre.view());
        Self::lemma_space_freed_pages(pre, post, base);
        Self::lemma_node_block_objects(pre, post, base);
        Self::lemma_tlb_space_removed(pre, post, base);
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] pre.cores@[c].space != Some(base) by {
            if pre.cores@[c].space == Some(base) {
                pre.lemma_named_depends(c, base);
            }
        }
        lemma_ids_space_removed(pre.cores@, pre.spaces.loaded@, post.spaces.loaded@, base);
        lemma_registers_lists(pre.spaces.registers@, pre.cores@, pre.spaces.loaded@, post.spaces.loaded@, pre.spaces.kernel_root@);
    }

    /// The block of the empty space at `base` goes back to the block table: its node pages off the list,
    /// and its root, record and list of cores turned back into page permissions.
    pub fn free_empty_space(&mut self, base: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).space_is_empty(base),
            old(self).no_stale_translation(base / PAGE_SZ),
        ensures
            final(steps).count <= old(steps).count + TABLE_NODE_PAGES + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::space_freed_step(*old(self), *final(self), base),
            final(self).blocks.pages@[(base / PAGE_SZ) as int].kind is Free,
            !final(self).spaces.roots@.contains_key(base),
            forall|k: usize| k < TABLE_NODE_PAGES ==> !final(self).list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            forall|r: usize, p: SpacePath| #[trigger] walk(tree_of(&final(self).table_pages, &final(self).spaces), r, p)
                == walk(tree_of(&old(self).table_pages, &old(self).spaces), r, p),
            final(self).cores == old(self).cores,
            final(self).view() == old(self).view(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let page = base / PAGE_SZ;
        proof {
            pre.lemma_empty_space(base);
            crate::layouts::lemma_space_block_layouts();
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies pre.list.pages@[p].addr() == p by {
                lemma_list_page(&pre.list, p);
            }
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.roots.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.records.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.loaded.borrow().tracked_borrow(base));
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies !(base + 5 * PAGE_SZ <= p < base + 8 * PAGE_SZ) by {
                lemma_list_page(&pre.list, p);
            }
        }
        self.blocks.mark_torn_down(page);
        let ghost mid = *self;
        let Tracked(nodes) = take_table_node_pages(&mut self.list, base, Tracked(&mut *steps));
        let tracked mut perms = nodes;
        proof {
            let tracked mut root = self.spaces.roots.borrow_mut().tracked_remove(base);
            let tracked mut record = self.spaces.records.borrow_mut().tracked_remove(base);
            let tracked mut cores = self.spaces.loaded.borrow_mut().tracked_remove(base);
            root.leak_contents();
            record.leak_contents();
            cores.leak_contents();
            perms.tracked_insert((page + 5) as usize, crate::layouts::page_map_into_page(root));
            perms.tracked_insert((page + 6) as usize, crate::layouts::space_record_into_page(record));
            perms.tracked_insert((page + 7) as usize, crate::layouts::core_list_into_page(cores));
            self.spaces.holders = Ghost(pre.spaces.holders@.remove(base));
            self.spaces.bound = Ghost(pre.spaces.bound@.remove(base));
            assert(self.blocks.pages@[page as int].order == 3);
            assert(order_pages(3) == 8);
            assert forall|k: usize| #![trigger perms.contains_key((page + k) as usize)] #![trigger perms[(page + k) as usize]]
                k < order_pages(self.blocks.pages@[page as int].order) implies {
                &&& perms.contains_key((page + k) as usize)
                &&& perms[(page + k) as usize].addr() == (page + k) * PAGE_SZ
                &&& perms[(page + k) as usize].is_uninit()
            } by {
                if k < 5 {
                    assert(holds_free_page(nodes, (page + k) as usize));
                }
            }
        }
        self.blocks.free_block(page, Tracked(perms), Tracked(steps));
        proof {
            let post = *self;
            assert forall|i: int| pre.blocks.tracks(i) implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            assert(Self::space_freed_step(pre, post, base));
            Self::lemma_space_freed(pre, post, base);
            Self::lemma_bound_threads_same(pre, post);
            Self::lemma_space_freed_tree(pre, post, base);
            assert forall|r: usize, p: SpacePath| #[trigger] walk(tree_of(&post.table_pages, &post.spaces), r, p)
                == walk(tree_of(&pre.table_pages, &pre.spaces), r, p) by {
                lemma_walk_space_removed(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base, r, p);
            }
            assert(pre.blocks.in_block(page as int, page as int));
            assert forall|k: usize| k < TABLE_NODE_PAGES implies !post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)) by {
                lemma_table_node_page(base, k);
            }
        }
    }

    /// What freeing the empty device space at `base` did to self: one step of an empty space going, so its
    /// block's pages are free and the tables and the list's nodes are as they were. Its children and any
    /// device went earlier, so the view is as it was.
    pub open spec fn space_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.space_is_empty(base)
        &&& self.blocks.pages@[page as int].refs == 0
        &&& self.spaces.bound@[base] == Set::<usize>::empty()
        &&& self.no_stale_translation(page)
        &&& Self::space_freed_step(*self, post, base)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& !post.spaces.roots@.contains_key(base)
        &&& forall|k: usize| k < TABLE_NODE_PAGES ==> !post.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// Frees the empty device space at `base`, once every core and IOMMU has acknowledged the epoch of its
    /// block's last unmap. It refuses a block that is anything else, a process space included.
    // In a solver of its own: beside the rest of this module it runs past its budget.
    #[verifier::spinoff_prover]
    pub fn free_space(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + ENTRIES + (NUM_CPUS + NUM_IOMMUS) + (TABLE_NODE_PAGES + SMALL_PAGES_MAX),
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            ret is Again ==> !old(self).acknowledged(base / PAGE_SZ),
            ret is Freed ==> old(self).space_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
            if pre.space_is_empty(base) {
                pre.lemma_empty_space(base);
            }
        }
        let untyped = match self.retype_parent(root, from, base, 3) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_space = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Space) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_space_block(base);
        }
        if !dead_space {
            return ReclaimStep::Refused;
        }
        if !self.space_nothing_left(base, Tracked(&mut *steps)) {
            return ReclaimStep::Refused;
        }
        if !self.is_acknowledged(page, Tracked(&mut *steps)) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_acknowledged_is_clean(page);
        }
        self.free_empty_space(base, Tracked(steps));
        proof {
            let post = *self;
            assert(post.view() == pre.view());
            let v = pre.view();
            let e = Effect::Teardown { untyped, object: base };
            assert(authorized(v, root, e));
        }
        ReclaimStep::Freed
    }

    /// Unlinks the hidden node of the leaf at `base`, by the same undo as revoke's hidden arm, and
    /// nothing more. Refused, with nothing changed, unless an untyped held covers the block and the
    /// block holds a leaf with its hidden node still live.
    pub fn unlink_leaf(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count == old(steps).count,
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            ret == old(self).can_unlink_leaf(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).leaf_unlinked(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, 1) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let live_leaf = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::TableLeaf) => entry.refs == 1,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_live_leaf_block(base);
        }
        if !live_leaf {
            return false;
        }
        proof {
            pre.lemma_hidden_is_leaf(base);
        }
        self.unlink_arm(base, Tracked(steps));
        self.list.remove_leaf(base);
        proof {
            let post = *self;
            post.tables.lemma_wf_same_pages(&pre.list, &post.list);
            Self::lemma_delete_caps_wf(pre, post, base);
            let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == base
                && post.list.seq@ == pre.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == pre.list.seq@[0]);
            lemma_parents_removed(pre.list, post.list, base);
            Self::lemma_revoke_hidden(pre, post, base);
            Self::lemma_bindings_caps_frame(pre, post, base, base);
            Self::lemma_revoke_hidden_holders(pre, post, base);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_unlink_discharges(pre, post, root, untyped, base);
            Self::lemma_bound_threads_same(pre, post);
        }
        true
    }

    /// The block test unlink_leaf makes reads as the node does: a table leaf block at one reference
    /// is an owned leaf's whose hidden node is live, and such a leaf's block is a table leaf at one
    /// reference.
    proof fn lemma_live_leaf_block(&self, base: usize)
        requires
            self.wf(),
            base % LEAF_BYTES == 0,
            self.blocks.tracks_addr(base),
        ensures
            (leaf_block(&self.blocks, base / PAGE_SZ) && self.blocks.pages@[(base / PAGE_SZ) as int].refs == 1)
                == (self.tables.owner@.contains_key(base) && self.list.nodes@[base as int].live),
            self.tables.owner@.contains_key(base) && self.list.nodes@[base as int].live
                ==> self.list.nodes@[base as int].kind is Hidden,
    {
        lemma_leaf_page(base);
        if leaf_block(&self.blocks, base / PAGE_SZ) {
            assert(self.tables.owner@.contains_key(((base / PAGE_SZ) * PAGE_SZ) as usize));
        }
    }

    /// What unlinking a hidden node does to the view: nothing. The node was no capability, and every
    /// capability says what it did under the parent it had, so the step discharges as a teardown from
    /// the retype right alone.
    proof fn lemma_unlink_discharges(pre: Self, post: Self, root: usize, untyped: usize, base: usize)
        requires
            Self::caps_frame(pre, post, base, base),
            base % PAGE_SZ == 0,
            post.list.parent == pre.list.parent,
            pre.view().holds_right(root, untyped, Right::Retype),
            Self::same_tree(pre, post),
            post.devices == pre.devices,
        ensures
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            post.view() == pre.view(),
            discharges(pre.view(), post.view(), root, Effect::Teardown { untyped, object: base }),
    {
        let (a, b) = (pre.view(), post.view());
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x)
            && (pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x)) by {
            if x != base {
                Self::lemma_caps_frame(pre, post, base, base, x);
            }
        }
        assert(b.held =~= a.held);
        assert(b.names =~= a.names);
        assert(b.pages =~= a.pages);
        assert(b.rights =~= a.rights);
        assert(b == a);
    }

    /// The block test unlink_table makes reads as the node does: a table page block at one reference is
    /// a table page's whose hidden node is live, and the other way round.
    proof fn lemma_live_table_block(&self, base: usize)
        requires
            self.wf(),
            base % TABLE_PAGE_BYTES == 0,
            self.blocks.tracks_addr(base),
        ensures
            (table_block(&self.blocks, base / PAGE_SZ) && self.blocks.pages@[(base / PAGE_SZ) as int].refs == 1)
                == (self.table_pages.maps@.contains_key(base) && self.list.nodes@[base as int].live),
            self.table_pages.maps@.contains_key(base) && self.list.nodes@[base as int].live
                ==> self.list.nodes@[base as int].kind is Hidden,
    {
        assert(base % TABLE_PAGE_BYTES == 0 ==> base % LEAF_BYTES == 0) by (bit_vector);
        lemma_leaf_page(base);
        if table_block(&self.blocks, base / PAGE_SZ) {
            assert(self.table_pages.maps@.contains_key(((base / PAGE_SZ) * PAGE_SZ) as usize));
        }
        if self.table_pages.maps@.contains_key(base) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        }
    }

    /// Unlinks the hidden node of the table page at `base`: cuts it from the entry naming it, records what
    /// that leaves stale, and drops its reference, and nothing more. Refused, with nothing changed, unless
    /// an untyped held covers the block and the block holds a table page with its hidden node still live,
    /// and the epoch can still rise. A process's root is a space block, so it is refused.
    pub fn unlink_table(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + CUT_NOTE_STEPS,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_unlink_table(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).table_page_unlinked(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
            if pre.table_pages.maps@.contains_key(base) {
                assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, base));
            }
        }
        let untyped = match self.retype_parent(root, from, base, 3) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) || self.flush_epoch == usize::MAX {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let live_table = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::TablePage) => entry.refs == 1,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_live_table_block(base);
        }
        if !live_table {
            return false;
        }
        proof {
            pre.lemma_hidden_is_leaf(base);
        }
        self.detach_stale(base, Tracked(&mut *steps));
        let ghost cut = *self;
        proof {
            let b = tree_of(&cut.table_pages, &cut.spaces);
            assert(b.is_page(base));
        }
        self.unlink_arm(base, Tracked(steps));
        self.list.remove_leaf(base);
        proof {
            let post = *self;
            post.tables.lemma_wf_same_pages(&cut.list, &post.list);
            Self::lemma_delete_caps_wf(cut, post, base);
            let p = choose|p: int| 0 <= p < cut.list.seq@.len() && cut.list.seq@[p] == base
                && post.list.seq@ == cut.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == cut.list.seq@[0]);
            lemma_parents_removed(cut.list, post.list, base);
            Self::lemma_revoke_hidden(cut, post, base);
            Self::lemma_bindings_caps_frame(cut, post, base, base);
            Self::lemma_revoke_hidden_holders(cut, post, base);
            Self::lemma_tlb_same(cut, post);
            Self::lemma_cut_sheds(pre, cut, base);
            Self::lemma_cut_shares(pre, cut, base);
            assert(post.view().shares == cut.view().shares);
            Self::lemma_unlink_discharges(cut, post, root, untyped, base);
            Self::lemma_cut_recorded_same(pre, cut, post, base);
            Self::lemma_cut_shrunk(pre, cut, base);
            Self::lemma_same_tree_shrunk(cut, post);
            Self::lemma_shrunk_compose(pre, cut, post);
            lemma_sheds_shares_discharges_teardown(pre.view(), post.view(), root, untyped, base);
            Self::lemma_bound_threads_same(cut, post);
        }
        true
    }

    /// Child c of a dead table page or device space is cut: it has no parent and keeps its space, its page is
    /// not acknowledged, its word is above every acknowledgement that stood when the slices began, and its
    /// page is in the TLB of every core that loaded the space and, for a device space the kernel still holds,
    /// of every IOMMU.
    pub open spec fn child_cut(pre: Self, post: Self, c: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let s = a.record(c).space;
        &&& b.record(c).parent is None
        &&& b.record(c).space == s
        &&& s is Some
        &&& post.stale_epoch.above(pre.flush_epoch as int, c / PAGE_SZ)
        &&& !post.acknowledged(c / PAGE_SZ)
        &&& forall|d: int| #![trigger post.tlb@[d].contains(TlbEntry { space: s->Some_0, page: c / PAGE_SZ })]
            0 <= d < NUM_CPUS && pre.depends(d, s->Some_0)
            ==> post.tlb@[d].contains(TlbEntry { space: s->Some_0, page: c / PAGE_SZ })
        &&& forall|i: int| #![trigger post.iommus.tlb@[i].contains(TlbEntry { space: s->Some_0, page: c / PAGE_SZ })]
            0 <= i < NUM_IOMMUS && pre.iommu_present(i) && a.is_root(s->Some_0) && pre.spaces.records@[s->Some_0].value().kind is Device
            ==> post.iommus.tlb@[i].contains(TlbEntry { space: s->Some_0, page: c / PAGE_SZ })
    }

    /// What cutting children of the dead table at `base` keeps: only tables, the record of each cut and the
    /// TLBs changed. A table page's cuts leave every walk finding what it did, since no walk reaches it, and
    /// a root's end its walks through the entries they cut and leave every other walk. Each entry that
    /// stopped naming a child is empty and its child is cut. A page's stale word changes only if it is
    /// a cut child's page, so the table's own page keeps its word.
    pub open spec fn table_cuts_kept(pre: Self, post: Self, base: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.cores == pre.cores
        &&& post.mapped == pre.mapped
        &&& post.devices == pre.devices
        &&& post.processes == pre.processes
        &&& post.threads == pre.threads
        &&& post.iommus.acked == pre.iommus.acked
        &&& post.iommus.present == pre.iommus.present
        &&& post.iommus.commands == pre.iommus.commands
        &&& post.spaces.loaded == pre.spaces.loaded
        &&& pre.flush_epoch <= post.flush_epoch
        &&& b.maps.dom() == a.maps.dom()
        &&& b.roots.dom() == a.roots.dom()
        &&& forall|t: usize| #![trigger b.record(t)] a.is_table(t) ==> {
            &&& b.record(t).level == a.record(t).level
            &&& b.record(t).space == a.record(t).space
        }
        &&& forall|t: usize| #![trigger b.space_records[t]]
            a.is_root(t) ==> b.space_records[t].value().kind == a.space_records[t].value().kind
        &&& b.record(base).parent is None
        &&& forall|e: usize| #[trigger] b.names_child(base, e) ==> a.names_child(base, e) && b.entry(base, e) == a.entry(base, e)
        &&& forall|e: usize| #[trigger] a.names_child(base, e) && !b.names_child(base, e) ==> {
            &&& b.entry(base, e).is_empty()
            &&& Self::child_cut(pre, post, child_at(a, base, e))
        }
        &&& !a.is_root(base) ==> forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p) == walk(a, r, p)
        &&& a.is_root(base) ==> forall|r: usize, p: SpacePath| r != base ==> #[trigger] walk(b, r, p) == walk(a, r, p)
        &&& a.is_root(base) ==> forall|p: SpacePath| #[trigger] walk(b, base, p)
            == if cut_through(a, b, base, base, p) { None } else { walk(a, base, p) }
        &&& Self::mappings_shrunk(pre, post)
        &&& forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] pre.core_may_hold(c, e) ==> post.core_may_hold(c, e)
        &&& forall|g: int| #![trigger post.stale_epoch.pages@[g]]
            0 <= g < NUM_PAGES && post.stale_epoch.pages@[g] != pre.stale_epoch.pages@[g]
            ==> exists|e: usize| #[trigger] a.names_child(base, e) && !b.names_child(base, e) && g == child_at(a, base, e) / PAGE_SZ
        &&& base / PAGE_SZ < NUM_PAGES
            ==> post.stale_epoch.pages@[(base / PAGE_SZ) as int] == pre.stale_epoch.pages@[(base / PAGE_SZ) as int]
    }

    /// Such cuts share no more: they take walks away, make no space a device space and leave every
    /// capability. What they share is what a walk not through a cut entry finds.
    pub proof fn lemma_cuts_shed(pre: Self, post: Self, base: usize)
        requires
            Self::table_cuts_kept(pre, post, base),
        ensures
            sheds_shares(pre.view(), post.view()),
            post.view().shares == shares_surviving(
                tree_of(&pre.table_pages, &pre.spaces),
                |r: usize, q: SpacePath| cut_through(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base, r, q),
            ),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert forall|s: usize| #[trigger] is_device(b, s) && a.is_root(s) implies is_device(a, s) by {
            assert(b.space_records[s].value().kind == a.space_records[s].value().kind);
        }
        Self::lemma_shrunk_sheds(pre, post);
        assert(post.view() == (State { shares: post.view().shares, ..pre.view() }));
        let gone = |r: usize, q: SpacePath| cut_through(a, b, base, r, q);
        assert forall|s: usize, q: SpacePath| #[trigger] walk(b, s, q) == if gone(s, q) { None } else { walk(a, s, q) } by {
            if s == base && !a.is_root(base) {
                assert(walk(b, s, q) == walk(a, s, q));
            } else if s != base {
                assert(walk(b, s, q) == walk(a, s, q));
            }
        }
        assert forall|s: usize| #![trigger is_device(b, s)] #![trigger is_device(a, s)]
            a.is_root(s) && b.is_root(s) implies is_device(b, s) == is_device(a, s) by {
            assert(b.space_records[s].value().kind == a.space_records[s].value().kind);
        }
        lemma_walks_ended_shares(a, b, gone);
    }

    /// Cuts below a table that is no device space's root leave the view: no device space's walk passed
    /// through its entries.
    pub proof fn lemma_cuts_same_view(pre: Self, post: Self, base: usize)
        requires
            Self::table_cuts_kept(pre, post, base),
            !is_device(tree_of(&pre.table_pages, &pre.spaces), base),
        ensures
            post.view() == pre.view(),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        Self::lemma_cuts_shed(pre, post, base);
        assert forall|s: usize| #[trigger] b.is_root(s) == a.is_root(s) by {
            assert(b.roots.contains_key(s) == a.roots.contains_key(s));
        }
        assert forall|s: usize, p: SpacePath| is_device(a, s) && #[trigger] walk(a, s, p) is Some
            implies is_device(b, s) && walk(a, s, p) == walk(b, s, p) by {
            assert(b.space_records[s].value().kind == a.space_records[s].value().kind);
            assert(s != base);
            assert(walk(b, s, p) == walk(a, s, p));
        }
        lemma_shares_kept(b, a);
        assert(post.view().shares =~= pre.view().shares);
    }

    /// The table page at `base` has a child to cut: an untyped covers it, it is dead, an entry still names
    /// a child and the flush epoch can rise.
    pub open spec fn can_cut_table(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 3)
        &&& self.table_pages.maps@.contains_key(base)
        &&& !self.list.nodes@[base as int].live
        &&& exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
        &&& self.flush_epoch < usize::MAX
    }

    /// What cutting children of the dead table at `base` did to self: it cut at least one and no more than
    /// the budget, each taking one entry off the count, and every capability is as it was. A device space
    /// shares what a walk not through a cut entry still finds: a page leaves unless another path of the
    /// space maps it too.
    pub open spec fn children_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let ta = tree_of(&self.table_pages, &self.spaces);
        let tb = tree_of(&post.table_pages, &post.spaces);
        let a = child_entries(ta, base);
        let b = child_entries(tb, base);
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& Self::table_cuts_kept(*self, post, base)
        &&& b.subset_of(a)
        &&& b.len() < a.len()
        &&& a.len() - b.len() <= TABLE_SLICE_BUDGET
        &&& sheds_shares(self.view(), post.view())
        &&& post.view().shares == shares_surviving(ta, |r: usize, q: SpacePath| cut_through(ta, tb, base, r, q))
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// What cutting children of the dead table page at `base`, or of a process's space root, did to self:
    /// as children_cut says, and no device space's walk passed through its entries, so the view is as it
    /// was.
    pub open spec fn table_children_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        &&& self.children_cut(post, root, from, base)
        &&& post.view() == self.view()
    }

    /// The block test slice_table makes reads as the table page does.
    pub proof fn lemma_dead_table_block(&self, base: usize)
        requires
            self.wf(),
            base % TABLE_PAGE_BYTES == 0,
            self.blocks.tracks_addr(base),
        ensures
            (table_block(&self.blocks, base / PAGE_SZ) && self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0)
                == (self.table_pages.maps@.contains_key(base) && !self.list.nodes@[base as int].live),
            self.table_pages.maps@.contains_key(base) ==> !self.spaces.roots@.contains_key(base),
            self.table_pages.maps@.contains_key(base) && !self.list.nodes@[base as int].live
                ==> self.table_pages.records@[base].value().parent is None,
    {
        assert(base % TABLE_PAGE_BYTES == 0 ==> base % LEAF_BYTES == 0) by (bit_vector);
        lemma_leaf_page(base);
        if table_block(&self.blocks, base / PAGE_SZ) {
            assert(self.table_pages.maps@.contains_key(((base / PAGE_SZ) * PAGE_SZ) as usize));
        }
        if self.table_pages.maps@.contains_key(base) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
            if self.spaces.roots@.contains_key(base) {
                assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
            }
        }
    }

    /// Entry e of table page t names a child: the child's address is below the entry's, the child is a
    /// table page whose record names the entry, and it lies in the block table's range.
    proof fn lemma_child_of_entry(&self, t: usize, e: usize)
        requires
            self.wf(),
            tree_of(&self.table_pages, &self.spaces).names_child(t, e),
        ensures
            tree_of(&self.table_pages, &self.spaces).entry(t, e).addr >= TABLE_NODE_PAGES * PAGE_SZ,
            self.table_pages.maps@.contains_key(child_at(tree_of(&self.table_pages, &self.spaces), t, e)),
            tree_of(&self.table_pages, &self.spaces).record(child_at(tree_of(&self.table_pages, &self.spaces), t, e)).parent
                == Some(TableParent { table: t, entry: e }),
            tree_of(&self.table_pages, &self.spaces).record(child_at(tree_of(&self.table_pages, &self.spaces), t, e)).space is Some,
            self.blocks.tracks_addr(child_at(tree_of(&self.table_pages, &self.spaces), t, e)),
            child_at(tree_of(&self.table_pages, &self.spaces), t, e) % TABLE_PAGE_BYTES == 0,
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let c = child_at(tree, t, e);
        assert(tree.is_page(c));
        assert(tree.maps.contains_key(c));
        assert(tree.record(c).parent == Some(TableParent { table: t, entry: e }));
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, c));
        lemma_table_bound(c);
        assert(tree.entry(t, e).addr == table_addr(c));
    }

    /// One more cut after cuts of the same dead table page: what was kept stays kept, its entry comes off
    /// the count and its child is cut.
    proof fn lemma_table_cut_step(pre: Self, mid: Self, post: Self, base: usize, e: usize)
        requires
            pre.wf(),
            mid.wf(),
            Self::table_cuts_kept(pre, mid, base),
            tree_of(&pre.table_pages, &pre.spaces).is_table(base),
            !(tree_of(&pre.table_pages, &pre.spaces).is_page(base) && tree_of(&pre.table_pages, &pre.spaces).is_root(base)),
            tree_of(&mid.table_pages, &mid.spaces).names_child(base, e),
            Self::detach_recorded(mid, post, child_at(tree_of(&mid.table_pages, &mid.spaces), base, e)),
        ensures
            Self::table_cuts_kept(pre, post, base),
            child_entries(tree_of(&post.table_pages, &post.spaces), base)
                == child_entries(tree_of(&mid.table_pages, &mid.spaces), base).remove(e),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let m = tree_of(&mid.table_pages, &mid.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let c = child_at(m, base, e);
        mid.lemma_child_of_entry(base, e);
        assert(m.record(c).parent == Some(TableParent { table: base, entry: e }));
        assert(detached(m, b, base, e, c));
        assert(c != base);
        reveal(walks_detached);
        if !a.is_root(base) {
            assert forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p) == walk(a, r, p) by {
                assert(walk(b, r, p) == (if passes_through(m, r, p, base, e) { None } else { walk(m, r, p) }));
                assert(walk(m, r, p) == walk(a, r, p));
            }
        } else {
            assert(!m.is_page(base)) by {
                assert(m.maps.contains_key(base) == a.maps.contains_key(base));
            }
            assert forall|r: usize, p: SpacePath| r != base implies #[trigger] walk(b, r, p) == walk(a, r, p) by {
                lemma_root_entry_not_passed(m, base, e, r, p);
                assert(walk(b, r, p) == (if passes_through(m, r, p, base, e) { None } else { walk(m, r, p) }));
                assert(walk(m, r, p) == walk(a, r, p));
            }
        }
        assert forall|t: usize| #![trigger b.record(t)] a.is_table(t) implies {
            &&& b.record(t).level == a.record(t).level
            &&& b.record(t).space == a.record(t).space
        } by {
            assert(m.record(t).level == a.record(t).level);
            assert(m.is_table(t));
            assert(b.record(t).level == m.record(t).level);
        }
        assert forall|t: usize| #![trigger b.space_records[t]]
            a.is_root(t) implies b.space_records[t].value().kind == a.space_records[t].value().kind by {
            assert(m.space_records[t].value().kind == a.space_records[t].value().kind);
            assert(m.is_root(t));
            assert(b.space_records[t].value().kind == m.space_records[t].value().kind);
        }
        assert(b.record(base).parent == m.record(base).parent);
        assert forall|i: usize| #[trigger] b.child_slot(base, i) == m.child_slot(base, i) by {
            assert(b.record(base).level == m.record(base).level);
        }
        assert forall|i: usize| #[trigger] b.names_child(base, i) implies a.names_child(base, i) && b.entry(base, i) == a.entry(base, i) by {
            assert(b.child_slot(base, i) == m.child_slot(base, i));
            assert(i != e);
            assert(b.entry(base, i) == m.entry(base, i));
            assert(m.names_child(base, i));
        }
        let s = m.record(c).space;
        assert(a.record(c).space == s) by {
            assert(a.is_page(c));
        }
        assert(pre.acked(0) <= pre.flush_epoch);
        assert(post.acked(0) == pre.acked(0));
        assert forall|i: usize| #[trigger] a.names_child(base, i) && !b.names_child(base, i) implies {
            &&& b.entry(base, i).is_empty()
            &&& Self::child_cut(pre, post, child_at(a, base, i))
        } by {
            assert(b.child_slot(base, i) == m.child_slot(base, i));
            if i == e {
                assert(m.entry(base, e) == a.entry(base, e));
                assert(child_at(a, base, e) == c);
                Self::lemma_child_newly_cut(pre, mid, post, c);
            } else {
                if m.names_child(base, i) {
                    assert(b.entry(base, i) == m.entry(base, i));
                }
                assert(!m.names_child(base, i));
                Self::lemma_child_stays_cut(pre, mid, post, base, e, c, child_at(a, base, i), i);
            }
        }
        assert forall|d: int, h: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] pre.core_may_hold(d, h) implies post.core_may_hold(d, h) by {
            assert(mid.core_may_hold(d, h));
        }
        assert(Self::cut_stale_noted(mid, post, c));
        assert(child_at(a, base, e) == c) by {
            assert(m.entry(base, e) == a.entry(base, e));
        }
        assert(a.names_child(base, e) && !b.names_child(base, e));
        assert forall|g: int| #![trigger post.stale_epoch.pages@[g]]
            0 <= g < NUM_PAGES && post.stale_epoch.pages@[g] != pre.stale_epoch.pages@[g]
            implies exists|i: usize| #[trigger] a.names_child(base, i) && !b.names_child(base, i) && g == child_at(a, base, i) / PAGE_SZ by {
            if mid.stale_epoch.pages@[g] != pre.stale_epoch.pages@[g] {
                let i = choose|i: usize| #[trigger] a.names_child(base, i) && !m.names_child(base, i) && g == child_at(a, base, i) / PAGE_SZ;
                if b.names_child(base, i) {
                    assert(b.child_slot(base, i) == m.child_slot(base, i));
                    assert(i != e);
                    assert(b.entry(base, i) == m.entry(base, i));
                }
                assert(!b.names_child(base, i));
            } else {
                assert(g == (c / PAGE_SZ) as int);
                assert(a.names_child(base, e) && !b.names_child(base, e) && g == child_at(a, base, e) / PAGE_SZ);
            }
        }
        if base / PAGE_SZ < NUM_PAGES {
            assert(base % TABLE_PAGE_BYTES == 0) by {
                if pre.table_pages.maps@.contains_key(base) {
                    assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, base));
                } else {
                    assert(pre.spaces.roots@.contains_key(base));
                    assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, base));
                }
            }
            assert(c % TABLE_PAGE_BYTES == 0);
            assert(base % TABLE_PAGE_BYTES == 0 && c % TABLE_PAGE_BYTES == 0 && base != c ==> base / PAGE_SZ != c / PAGE_SZ) by (bit_vector);
            assert(post.stale_epoch.pages@[(base / PAGE_SZ) as int] == mid.stale_epoch.pages@[(base / PAGE_SZ) as int]);
        }
        assert forall|i: usize| #[trigger] child_entries(b, base).contains(i) == child_entries(m, base).remove(e).contains(i) by {
            lemma_child_entries(b, base, i);
            lemma_child_entries(m, base, i);
            assert(b.child_slot(base, i) == m.child_slot(base, i));
            if i != e {
                if i < ENTRIES {
                    assert(b.entry(base, i) == m.entry(base, i));
                } else {
                    assert(!b.names_child(base, i) && !m.names_child(base, i));
                }
            }
        }
        assert(child_entries(b, base) =~= child_entries(m, base).remove(e));
        if a.is_root(base) {
            assert forall|p: SpacePath| #[trigger] walk(b, base, p)
                == if cut_through(a, b, base, base, p) { None } else { walk(a, base, p) } by {
                lemma_root_entry_passed(m, base, e, p);
                assert(walk(b, base, p) == (if passes_through(m, base, p, base, e) { None } else { walk(m, base, p) }));
                assert(walk(m, base, p) == if cut_through(a, m, base, base, p) { None } else { walk(a, base, p) });
                lemma_child_entries(b, base, p.l4);
                lemma_child_entries(m, base, p.l4);
                if p.l4 == e {
                    assert(!b.names_child(base, e));
                } else {
                    assert(b.names_child(base, p.l4) == m.names_child(base, p.l4));
                }
            }
        }
    }

    /// The child this step cuts satisfies child_cut.
    proof fn lemma_child_newly_cut(pre: Self, mid: Self, post: Self, c: usize)
        requires
            pre.wf(),
            mid.wf(),
            pre.flush_epoch <= mid.flush_epoch,
            post.cores == pre.cores,
            post.iommus.acked == pre.iommus.acked,
            post.iommus.present == pre.iommus.present,
            post.iommus.commands == pre.iommus.commands,
            post.spaces.loaded == pre.spaces.loaded,
            mid.spaces.loaded == pre.spaces.loaded,
            mid.cores == pre.cores,
            Self::detach_recorded(mid, post, c),
            mid.table_pages.maps@.contains_key(c),
            mid.blocks.tracks_addr(c),
            tree_of(&mid.table_pages, &mid.spaces).record(c).parent is Some,
            tree_of(&mid.table_pages, &mid.spaces).record(c).space is Some,
            tree_of(&pre.table_pages, &pre.spaces).record(c).space == tree_of(&mid.table_pages, &mid.spaces).record(c).space,
            tree_of(&post.table_pages, &post.spaces).record(c).parent is None,
            tree_of(&post.table_pages, &post.spaces).record(c).space == tree_of(&mid.table_pages, &mid.spaces).record(c).space,
            tree_of(&pre.table_pages, &pre.spaces).is_root(tree_of(&mid.table_pages, &mid.spaces).record(c).space->Some_0)
                ==> tree_of(&mid.table_pages, &mid.spaces).space_records[tree_of(&mid.table_pages, &mid.spaces).record(c).space->Some_0].value().kind
                    == tree_of(&pre.table_pages, &pre.spaces).space_records[tree_of(&mid.table_pages, &mid.spaces).record(c).space->Some_0].value().kind,
        ensures
            Self::child_cut(pre, post, c),
    {
        let m = tree_of(&mid.table_pages, &mid.spaces);
        let s = m.record(c).space->Some_0;
        let g = c / PAGE_SZ;
        lemma_cut_pages(m, c, g);
        assert(cut_pages(m, c).contains(g));
        assert forall|d: int| #![trigger post.tlb@[d].contains(TlbEntry { space: s, page: g })]
            0 <= d < NUM_CPUS && pre.depends(d, s) implies post.tlb@[d].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.depends(d, s));
        }
        assert forall|i: int| #![trigger post.iommus.tlb@[i].contains(TlbEntry { space: s, page: g })]
            0 <= i < NUM_IOMMUS && pre.iommu_present(i) && tree_of(&pre.table_pages, &pre.spaces).is_root(s) && pre.spaces.records@[s].value().kind is Device
            implies post.iommus.tlb@[i].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.spaces.records@[s].value().kind is Device);
        }
        assert(post.stale_epoch.written(post.flush_epoch, g));
    }

    /// A child an earlier step cut stays cut through this one: its record is not this child's, and the
    /// epoch only rises.
    proof fn lemma_child_stays_cut(pre: Self, mid: Self, post: Self, base: usize, e: usize, c: usize, old_child: usize, i: usize)
        requires
            pre.wf(),
            mid.wf(),
            Self::table_cuts_kept(pre, mid, base),
            Self::child_cut(pre, mid, old_child),
            Self::detach_recorded(mid, post, c),
            tree_of(&pre.table_pages, &pre.spaces).names_child(base, i),
            old_child == child_at(tree_of(&pre.table_pages, &pre.spaces), base, i),
            tree_of(&mid.table_pages, &mid.spaces).record(c).parent == Some(TableParent { table: base, entry: e }),
            mid.table_pages.maps@.contains_key(c),
            tree_of(&mid.table_pages, &mid.spaces).record(old_child).parent is None,
        ensures
            Self::child_cut(pre, post, old_child),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let m = tree_of(&mid.table_pages, &mid.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        pre.lemma_child_of_entry(base, i);
        let s = a.record(old_child).space->Some_0;
        let g = old_child / PAGE_SZ;
        assert(old_child != c);
        assert(m.is_page(c));
        assert(detached(m, b, base, e, c));
        assert(a.is_page(old_child));
        assert(m.is_page(old_child));
        assert(b.record(old_child).parent == m.record(old_child).parent);
        assert(b.record(old_child).space == m.record(old_child).space);
        assert(post.stale_epoch.above(pre.flush_epoch as int, g));
        assert(pre.acked(0) <= pre.flush_epoch);
        assert(post.acked(0) == pre.acked(0));
        assert forall|d: int| #![trigger post.tlb@[d].contains(TlbEntry { space: s, page: g })]
            0 <= d < NUM_CPUS && pre.depends(d, s) implies post.tlb@[d].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.tlb@[d].contains(TlbEntry { space: s, page: g }));
        }
        assert forall|j: int| #![trigger post.iommus.tlb@[j].contains(TlbEntry { space: s, page: g })]
            0 <= j < NUM_IOMMUS && pre.iommu_present(j) && a.is_root(s) && pre.spaces.records@[s].value().kind is Device
            implies post.iommus.tlb@[j].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.iommus.tlb@[j].contains(TlbEntry { space: s, page: g }));
        }
    }

    /// Cuts up to a budget of the child tables of the dead table page at `base`, under the untyped at index
    /// `from` of the table at `root`, each from the entry naming it, with what that leaves stale. A cut
    /// entry stays empty, since can_link refuses a dead parent and no walk reaches a table with no parent,
    /// so the next slice can start again from the first entry. Returns whether it ran, and if not nothing
    /// changed.
    pub fn cut_table_children(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + CUT_SLICE_STEPS,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_cut_table(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).table_children_cut(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, 3) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) || self.flush_epoch == usize::MAX {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_table = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::TablePage) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_dead_table_block(base);
        }
        if !dead_table {
            return false;
        }
        let level = self.table_record(base, false).level;
        if level < 2 {
            proof {
                assert forall|e: usize| !#[trigger] a.names_child(base, e) by {}
            }
            return false;
        }
        proof {
            assert(a.is_page(base));
        }
        let cut = self.cut_children(base, false, Tracked(steps));
        proof {
            if cut != 0 {
                Self::lemma_cuts_shed(pre, *self, base);
                Self::lemma_cuts_same_view(pre, *self, base);
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
            }
        }
        cut != 0
    }

    /// Cuts up to a budget of the children of the table at `base`, a table page or a space's root with no
    /// parent, each from the entry naming it, with what that leaves stale, and returns how many. A kernel
    /// slot names no child, so it stays, as does every entry that named none. A slice starts again from
    /// the first entry, since a cut entry stays empty.
    pub fn cut_children(&mut self, base: usize, is_root: bool, Tracked(steps): Tracked<&mut Steps>) -> (cut: usize)
        requires
            old(self).wf(),
            old(self).flush_epoch < usize::MAX,
            tree_of(&old(self).table_pages, &old(self).spaces).is_table(base),
            is_root == tree_of(&old(self).table_pages, &old(self).spaces).is_root(base),
            is_root != tree_of(&old(self).table_pages, &old(self).spaces).is_page(base),
            tree_of(&old(self).table_pages, &old(self).spaces).record(base).parent is None,
            tree_of(&old(self).table_pages, &old(self).spaces).record(base).level >= 2,
        ensures
            final(steps).count <= old(steps).count + CUT_SLICE_STEPS,
            final(self).wf(),
            cut <= TABLE_SLICE_BUDGET,
            Self::table_cuts_kept(*old(self), *final(self), base),
            child_entries(tree_of(&final(self).table_pages, &final(self).spaces), base)
                .subset_of(child_entries(tree_of(&old(self).table_pages, &old(self).spaces), base)),
            child_entries(tree_of(&old(self).table_pages, &old(self).spaces), base).len()
                == child_entries(tree_of(&final(self).table_pages, &final(self).spaces), base).len() + cut,
            cut == 0 ==> *final(self) == *old(self),
            cut == 0 ==> forall|j: usize| !#[trigger] tree_of(&old(self).table_pages, &old(self).spaces).names_child(base, j),
            cut > 0 ==> exists|i: usize| #[trigger] tree_of(&old(self).table_pages, &old(self).spaces).names_child(base, i),
            forall|i: usize| #![trigger tree_of(&final(self).table_pages, &final(self).spaces).entry(base, i)]
                i < ENTRIES && !tree_of(&old(self).table_pages, &old(self).spaces).names_child(base, i)
                ==> tree_of(&final(self).table_pages, &final(self).spaces).entry(base, i)
                    == tree_of(&old(self).table_pages, &old(self).spaces).entry(base, i),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let ghost start = steps.count;
        let mut cut: usize = 0;
        let mut e: usize = 0;
        while cut != TABLE_SLICE_BUDGET && e != ENTRIES && self.flush_epoch != usize::MAX
            invariant
                start == old(steps).count,
                steps.count <= start + e + cut * CUT_NOTE_STEPS,
                self.wf(),
                pre == *old(self),
                pre.wf(),
                a == tree_of(&pre.table_pages, &pre.spaces),
                a.is_table(base),
                is_root == a.is_root(base),
                is_root != a.is_page(base),
                pre.flush_epoch < usize::MAX,
                a.record(base).level >= 2,
                cut <= TABLE_SLICE_BUDGET,
                e <= ENTRIES,
                Self::table_cuts_kept(pre, *self, base),
                cut == 0 ==> *self == pre,
                cut > 0 ==> exists|i: usize| #[trigger] a.names_child(base, i),
                child_entries(tree_of(&self.table_pages, &self.spaces), base).subset_of(child_entries(a, base)),
                child_entries(a, base).len() == child_entries(tree_of(&self.table_pages, &self.spaces), base).len() + cut,
                forall|j: usize| j < e ==> !#[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, j),
                forall|i: usize| #![trigger tree_of(&self.table_pages, &self.spaces).entry(base, i)]
                    i < ENTRIES && !a.names_child(base, i) ==> tree_of(&self.table_pages, &self.spaces).entry(base, i) == a.entry(base, i),
            decreases TABLE_SLICE_BUDGET - cut, ENTRIES - e,
        {
            proof {
                steps.step();
            }
            let ghost mid = *self;
            let ghost m = tree_of(&self.table_pages, &self.spaces);
            proof {
                assert(m.is_root(base) == is_root);
                assert(m.is_page(base) != is_root);
            }
            let kernel = self.is_kernel_slot(base, is_root, e);
            let entry = self.table_entry(base, is_root, e);
            let names = !kernel && entry.perm.present && !entry.perm.ps;
            proof {
                if is_root {
                    assert(m.space_records[base].value().kind == a.space_records[base].value().kind);
                }
                assert(m.record(base).level == a.record(base).level);
                assert(names == m.names_child(base, e));
            }
            if !names {
                e = e + 1;
                continue;
            }
            proof {
                mid.lemma_child_of_entry(base, e);
            }
            let child = entry.addr - TABLE_NODE_PAGES * PAGE_SZ;
            proof {
                assert(child == child_at(m, base, e));
            }
            self.detach_stale(child, Tracked(&mut *steps));
            proof {
                let post = *self;
                let b = tree_of(&post.table_pages, &post.spaces);
                Self::lemma_table_cut_step(pre, mid, post, base, e);
                assert(m.record(child).parent == Some(TableParent { table: base, entry: e }));
                assert(detached(m, b, base, e, child));
                assert(a.names_child(base, e)) by {
                    lemma_child_entries(m, base, e);
                    lemma_child_entries(a, base, e);
                }
                assert forall|i: usize| #![trigger b.entry(base, i)]
                    i < ENTRIES && !a.names_child(base, i) implies b.entry(base, i) == a.entry(base, i) by {
                    assert(m.entry(base, i) == a.entry(base, i));
                }
                lemma_child_entries(m, base, e);
                vstd::set::lemma_set_remove_len(child_entries(m, base), e);
                assert forall|j: usize| #[trigger] child_entries(b, base).contains(j) implies child_entries(a, base).contains(j) by {
                    assert(child_entries(m, base).contains(j));
                }
                assert forall|j: usize| j < e + 1 implies !#[trigger] b.names_child(base, j) by {
                    lemma_child_entries(b, base, j);
                    lemma_child_entries(m, base, j);
                    if j != e {
                        assert(!m.names_child(base, j));
                        assert(!child_entries(m, base).contains(j));
                        assert(!child_entries(b, base).contains(j));
                    } else {
                        assert(!child_entries(b, base).contains(j));
                    }
                }
                if cut == 0 {
                    assert(mid == pre);
                    assert(a.names_child(base, e));
                } else {
                    assert(exists|i: usize| #[trigger] a.names_child(base, i));
                }
            }
            cut = cut + 1;
            e = e + 1;
        }
        proof {
            if cut == 0 {
                assert(*self == pre);
                assert(e == ENTRIES);
                assert forall|j: usize| !#[trigger] a.names_child(base, j) by {
                    if j < ENTRIES {
                        assert(!tree_of(&self.table_pages, &self.spaces).names_child(base, j));
                    }
                }
            }
        }
        cut
    }

    /// A dead device space's block: nothing names the space and no device is bound to it. A process space
    /// goes with its process.
    pub open spec fn dead_io_space(&self, base: usize) -> bool {
        &&& self.spaces.roots@.contains_key(base)
        &&& self.spaces.records@[base].value().kind is Device
        &&& self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0
    }

    /// The device space at `base` has a child to cut: an untyped covers it, it is dead, an entry still names
    /// a child and the flush epoch can rise.
    pub open spec fn can_cut_space(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 3)
        &&& self.dead_io_space(base)
        &&& exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
        &&& self.flush_epoch < usize::MAX
    }

    /// What cutting children of the dead device space at `base` did to self: as children_cut says, the
    /// space sharing no more, and it is still there and still dead.
    pub open spec fn space_children_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        &&& self.children_cut(post, root, from, base)
        &&& post.dead_io_space(base)
    }

    /// Cuts up to a budget of the child tables of the dead device space at `base`, under the untyped at index
    /// `from` of the table at `root`, each from the entry naming it, with what that leaves stale. Returns
    /// whether it ran, and if not nothing changed.
    pub fn cut_space_children(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + CUT_SLICE_STEPS,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_cut_space(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).space_children_cut(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, 3) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) || self.flush_epoch == usize::MAX {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_space = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Space) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_space_block(base);
        }
        if !dead_space {
            return false;
        }
        let cut = self.cut_children(base, true, Tracked(steps));
        proof {
            if cut != 0 {
                Self::lemma_cuts_shed(pre, *self, base);
                lemma_sheds_shares_discharges_teardown(pre.view(), self.view(), root, untyped, base);
            }
        }
        cut != 0
    }

    /// A block that holds a space is that device space's: a device space's block is Base and Space, a process
    /// space's is its process's, and a space's root has no parent, is level 4 and is no table page.
    pub proof fn lemma_space_block(&self, base: usize)
        requires
            self.wf(),
            base % TABLE_PAGE_BYTES == 0,
            self.blocks.tracks_addr(base),
        ensures
            space_block(&self.blocks, base / PAGE_SZ)
                == (self.spaces.roots@.contains_key(base) && self.spaces.records@[base].value().kind is Device),
            self.spaces.roots@.contains_key(base) ==> !self.table_pages.maps@.contains_key(base),
            self.spaces.roots@.contains_key(base) ==> tree_of(&self.table_pages, &self.spaces).record(base).parent is None,
            self.spaces.roots@.contains_key(base) ==> tree_of(&self.table_pages, &self.spaces).record(base).level == 4,
    {
        assert(base % TABLE_PAGE_BYTES == 0 ==> base % LEAF_BYTES == 0) by (bit_vector);
        lemma_leaf_page(base);
        if self.spaces.roots@.contains_key(base) {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
        }
    }

    /// The table page at `base` has a mapping to unlink: an untyped covers it, it is dead, an entry maps a
    /// frame and the flush epoch can rise.
    pub open spec fn can_unmap_table(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 3)
        &&& self.table_pages.maps@.contains_key(base)
        &&& !self.list.nodes@[base as int].live
        &&& exists|e: usize| #[trigger] frame_slot(tree_of(&self.table_pages, &self.spaces), base, e)
        &&& self.flush_epoch < usize::MAX
    }

    /// One step of unlinking the dead table page's mappings: node n is a mapping of the page at `base`, its
    /// entry and its frame's reference go as mapping_unlinked says, its unmap is recorded as
    /// mapping_stale_noted says, and the list loses that node alone.
    pub open spec fn table_mapping_step(pre: Self, post: Self, base: usize, n: usize) -> bool {
        &&& pre.list.nodes@[n as int].live
        &&& pre.list.nodes@[n as int].kind is Mapping
        &&& pre.mappings@.contains_key(n)
        &&& pre.mappings@[n].table == base
        &&& Self::mapping_unlinked(pre, post, n)
        &&& Self::mapping_stale_noted(pre, post, n)
        &&& !post.list.nodes@[n as int].live
        &&& post.list.seq@.len() == pre.list.seq@.len() - 1
        &&& forall|x: int| 0 <= x < NODE_SPACE && x != n ==> #[trigger] post.list.nodes@[x].live == pre.list.nodes@[x].live
    }

    /// The states from pre to post, each reached from the last by one step that unlinks a mapping of the
    /// page at `base`.
    pub open spec fn table_mapping_steps(pre: Self, post: Self, base: usize, nodes: Seq<usize>, states: Seq<Self>) -> bool {
        &&& states.len() == nodes.len() + 1
        &&& states[0] == pre
        &&& states[nodes.len() as int] == post
        &&& forall|i: int| #![trigger nodes[i]] 0 <= i < nodes.len() ==> Self::table_mapping_step(states[i], states[i + 1], base, nodes[i])
    }

    /// What unlinking mappings of the dead table page at `base` keeps: the list falls by exactly the count,
    /// the capabilities and the view are as they were, and every walk finds what it did, since no walk
    /// reaches `base`.
    pub open spec fn table_unmaps_kept(pre: Self, post: Self, base: usize, count: int) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        &&& post.tables == pre.tables
        &&& post.spaces == pre.spaces
        &&& post.frames == pre.frames
        &&& post.zeroing == pre.zeroing
        &&& post.cores == pre.cores
        &&& post.iommus.acked == pre.iommus.acked
        &&& post.iommus.present == pre.iommus.present
        &&& post.iommus.commands == pre.iommus.commands
        &&& post.table_pages.records == pre.table_pages.records
        &&& post.table_pages.spare == pre.table_pages.spare
        &&& post.list.parent == pre.list.parent
        &&& b.maps.dom() == a.maps.dom()
        &&& post.list.seq@.len() == pre.list.seq@.len() - count
        &&& !post.list.nodes@[base as int].live
        &&& forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x)
        &&& post.view() == pre.view()
        &&& forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p) == walk(a, r, p)
    }

    /// What unlinking mappings of the dead table page at `base` did to self: at least one and no more than
    /// the budget, each step as table_mapping_step says.
    pub open spec fn table_unmapped(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& exists|nodes: Seq<usize>, states: Seq<Self>| {
            &&& #[trigger] Self::table_mapping_steps(*self, post, base, nodes, states)
            &&& 0 < nodes.len() <= TABLE_SLICE_BUDGET
            &&& Self::table_unmaps_kept(*self, post, base, nodes.len() as int)
        }
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// A slice of the table page at `base` can do something: cut a child or unlink a mapping.
    pub open spec fn can_slice_table(&self, root: usize, from: usize, base: usize) -> bool {
        self.can_cut_table(root, from, base) || self.can_unmap_table(root, from, base)
    }

    /// What a slice of the dead table page at `base` did to self.
    pub open spec fn table_sliced(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        self.table_children_cut(post, root, from, base) || self.table_unmapped(post, root, from, base)
    }

    /// A live mapping node has a parent and nothing below it.
    proof fn lemma_mapping_is_leaf(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Mapping,
        ensures
            n != self.list.seq@[0],
            self.list.childless(n),
    {
        if !self.list.childless(n) {
            self.list.lemma_next_is_child(n);
        }
    }

    /// A step that takes a mapping node away leaves the view as it was but for the pages the node put in
    /// a device space: the node was no capability, and every capability says what it did under the parent
    /// it had.
    pub proof fn lemma_mapping_view_same(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            pre.list.nodes@[n as int].kind is Mapping,
            !post.list.nodes@[n as int].live,
            post.list.parent == pre.list.parent,
            Self::mapping_unlinked(pre, post, n),
            post.spaces.records == pre.spaces.records,
            post.devices == pre.devices,
        ensures
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            sheds_shares(pre.view(), post.view()),
    {
        Self::lemma_unlinked_shrunk(pre, post, n);
        Self::lemma_shrunk_sheds(pre, post);
        let (a, b) = (pre.view(), post.view());
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x)
            && (pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x)) by {
            if x != n {
                Self::lemma_caps_frame(pre, post, n, n, x);
            }
        }
        assert(b.held =~= a.held);
        assert(b.names =~= a.names);
        assert(b.pages =~= a.pages);
        assert(b.rights =~= a.rights);
        assert(b == (State { shares: b.shares, ..a }));
    }

    /// Unlinks mapping node n with its entry and its frame's reference, and records the unmap. Returns the
    /// entry's word as read in the step that cleared it.
    pub fn unlink_mapping_node(&mut self, n: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            old(self).list.nodes@[n as int].kind is Mapping,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(steps).count <= old(steps).count + UNLINK_ARM_STEPS,
            final(self).wf(),
            Self::mapping_unlinked(*old(self), *final(self), n),
            Self::mapping_stale_noted(*old(self), *final(self), n),
            Self::mapping_word(*old(self), n, ret),
            Self::caps_frame(*old(self), *final(self), n, n),
            !final(self).list.nodes@[n as int].live,
            final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==> #[trigger] final(self).list.nodes@[x].live == old(self).list.nodes@[x].live,
            final(self).list.parent == old(self).list.parent,
            final(self).tables == old(self).tables,
            final(self).spaces == old(self).spaces,
            final(self).devices == old(self).devices,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).table_pages.records == old(self).table_pages.records,
            final(self).table_pages.spare == old(self).table_pages.spare,
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_mapping_is_leaf(n);
        }
        let word = self.unlink_arm(n, Tracked(steps));
        let ghost mid = *self;
        self.list.remove_leaf(n);
        proof {
            let post = *self;
            post.tables.lemma_wf_same_pages(&pre.list, &post.list);
            assert(Self::caps_frame(pre, post, n, n));
            Self::lemma_delete_caps_wf(pre, post, n);
            let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == n
                && post.list.seq@ == pre.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == pre.list.seq@[0]);
            lemma_parents_removed(pre.list, post.list, n);
            assert(pre.mappings@.contains_key(n));
            pre.lemma_mapping_node(n);
            assert(mapping_wf(&pre.list, &pre.tables, tree_of(&pre.table_pages, &pre.spaces), &pre.blocks, pre.holders@, pre.mappings@, n));
            assert(pre.table_pages.maps@.contains_key(pre.mappings@[n].table));
            assert(post.table_pages.maps@.dom() =~= pre.table_pages.maps@.dom());
            Self::lemma_revoke_hidden(pre, post, n);
            Self::lemma_bindings_caps_frame(pre, post, n, n);
            Self::lemma_revoke_mapping_holders(pre, post, n);
            Self::lemma_stale_noted_same(pre, mid, post, n);
            Self::lemma_tlb_same(mid, post);
            Self::lemma_bound_threads_same(pre, post);
        }
        word
    }

    /// One more unlinked mapping of a dead table page, with no walk reaching it: what was kept stays kept
    /// and the step joins the rest.
    proof fn lemma_table_unmap_step(pre: Self, mid: Self, post: Self, base: usize, e: usize, n: usize, count: int)
        requires
            pre.wf(),
            mid.wf(),
            Self::table_unmaps_kept(pre, mid, base, count),
            pre.table_pages.maps@.contains_key(base),
            !pre.spaces.roots@.contains_key(base),
            frame_slot(tree_of(&mid.table_pages, &mid.spaces), base, e),
            n == mapping_node(base, e),
            Self::mapping_unlinked(mid, post, n),
            Self::caps_frame(mid, post, n, n),
            !post.list.nodes@[n as int].live,
            post.list.seq@.len() == mid.list.seq@.len() - 1,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==> #[trigger] post.list.nodes@[x].live == mid.list.nodes@[x].live,
            post.list.parent == mid.list.parent,
            post.tables == mid.tables,
            post.spaces == mid.spaces,
            post.devices == mid.devices,
            post.frames == mid.frames,
            post.zeroing == mid.zeroing,
            post.cores == mid.cores,
            post.iommus.acked == mid.iommus.acked,
            post.iommus.present == mid.iommus.present,
            post.iommus.commands == mid.iommus.commands,
            post.table_pages.records == mid.table_pages.records,
            post.table_pages.spare == mid.table_pages.spare,
        ensures
            Self::table_unmaps_kept(pre, post, base, count + 1),
            mid.mappings@.contains_key(n),
            mid.mappings@[n].table == base,
            mid.mappings@[n].entry == e,
            forall|i: usize| i < ENTRIES && i != e ==> #[trigger] tree_of(&post.table_pages, &post.spaces).entry(base, i) == tree_of(&mid.table_pages, &mid.spaces).entry(base, i),
            tree_of(&post.table_pages, &post.spaces).entry(base, e).is_empty(),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let m = tree_of(&mid.table_pages, &mid.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(mid.mappings@.contains_key(n));
        assert(mid.mappings@[n].table == base);
        assert(mid.mappings@[n].entry == e);
        assert(m.record(base).parent is None);
        assert(!m.is_root(base));
        assert(n != base) by {
            assert(e < ENTRIES);
            assert((e + 1) / 128 > 0 || (e + 1) % 128 > 0);
        }
        reveal(walks_cut);
        assert forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p) == walk(a, r, p) by {
            assert(walk(b, r, p) == (if ends_at(m, r, p, base, e) { None } else { walk(m, r, p) }));
            assert(!ends_at(m, r, p, base, e)) by {
                assert(step(m, r, p.l4) != Some(base));
                if let Some(t3) = step(m, r, p.l4) {
                    assert(step(m, t3, p.l3) != Some(base));
                    if let Some(t2) = step(m, t3, p.l3) {
                        assert(step(m, t2, p.l2) != Some(base));
                    }
                }
            }
            assert(walk(m, r, p) == walk(a, r, p));
        }
        Self::lemma_table_unmap_entries(mid, post, base, e, n);
        Self::lemma_mapping_view_same(mid, post, n);
        // No walk reaches the page, so the device spaces map what they did.
        lemma_same_walks_same_shares(a, b);
        assert(post.view() == pre.view());
        assert(b.maps.dom() =~= m.maps.dom());
        assert(!post.list.nodes@[base as int].live) by {
            pre.lemma_dead_base_in_nodes(base);
        }
    }

    /// Clearing entry e of a table page leaves its other entries as they were and that one empty.
    proof fn lemma_table_unmap_entries(mid: Self, post: Self, base: usize, e: usize, n: usize)
        requires
            mid.mappings@.contains_key(n),
            mid.mappings@[n].table == base,
            mid.mappings@[n].entry == e,
            Self::mapping_unlinked(mid, post, n),
        ensures
            forall|i: usize| i < ENTRIES && i != e ==> #[trigger] tree_of(&post.table_pages, &post.spaces).entry(base, i) == tree_of(&mid.table_pages, &mid.spaces).entry(base, i),
            tree_of(&post.table_pages, &post.spaces).entry(base, e).is_empty(),
    {
        reveal(entries_cleared);
        let (m, b) = (tree_of(&mid.table_pages, &mid.spaces), tree_of(&post.table_pages, &post.spaces));
        assert forall|i: usize| i < ENTRIES && i != e implies #[trigger] b.entry(base, i) == m.entry(base, i) by {}
    }

    /// A table page's first node lies in the list's range.
    proof fn lemma_dead_base_in_nodes(&self, base: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(base),
        ensures
            base < NODE_SPACE,
    {
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        lemma_table_bound(base);
    }

    /// Unlinks up to a budget of the mappings of the dead table page at `base`, under the untyped at index
    /// `from` of the table at `root`, each with its entry and its frame's reference, and records each
    /// unmap. A mapping node is always a leaf of its capability's run, so nothing else need consent. A
    /// cleared entry stays empty, since nothing maps into a dead table, so the next slice can start again
    /// from the first entry. Returns whether it ran, and if not nothing changed.
    pub fn unlink_table_mappings(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + UNMAP_SLICE_STEPS,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_unmap_table(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).table_unmapped(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, 3) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) || self.flush_epoch == usize::MAX {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_table = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::TablePage) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_dead_table_block(base);
        }
        if !dead_table {
            return false;
        }
        let level = self.table_record(base, false).level;
        proof {
            assert(a.is_page(base));
            pre.lemma_dead_base_in_nodes(base);
        }
        let ghost mut nodes: Seq<usize> = Seq::empty();
        let ghost mut states: Seq<Self> = Seq::empty().push(pre);
        let ghost start = steps.count;
        let mut unlinked: usize = 0;
        let mut e: usize = 0;
        while unlinked != TABLE_SLICE_BUDGET && e != ENTRIES && self.flush_epoch != usize::MAX
            invariant
                start == old(steps).count,
                steps.count <= start + e + unlinked * UNLINK_ARM_STEPS,
                self.wf(),
                pre == *old(self),
                pre.wf(),
                a == tree_of(&pre.table_pages, &pre.spaces),
                a.is_page(base),
                !a.is_root(base),
                a.record(base).parent is None,
                pre.table_pages.maps@.contains_key(base),
                !pre.spaces.roots@.contains_key(base),
                pre.flush_epoch < usize::MAX,
                !pre.list.nodes@[base as int].live,
                base < NODE_SPACE,
                base % TABLE_PAGE_BYTES == 0,
                self.blocks.tracks_addr(base),
                level == a.record(base).level,
                unlinked <= TABLE_SLICE_BUDGET,
                e <= ENTRIES,
                nodes.len() == unlinked,
                Self::table_unmaps_kept(pre, *self, base, unlinked as int),
                Self::table_mapping_steps(pre, *self, base, nodes, states),
                bound_threads(&self.list, &self.tables) == bound_threads(&pre.list, &pre.tables),
                unlinked == 0 ==> *self == pre,
                unlinked > 0 ==> exists|i: usize| #[trigger] frame_slot(a, base, i),
                forall|j: usize| j < e ==> !#[trigger] frame_slot(tree_of(&self.table_pages, &self.spaces), base, j),
            decreases TABLE_SLICE_BUDGET - unlinked, ENTRIES - e,
        {
            proof {
                steps.step();
            }
            let ghost mid = *self;
            let ghost m = tree_of(&self.table_pages, &self.spaces);
            let entry = self.table_entry(base, false, e);
            let maps_frame = entry.perm.present && (level == 1 || (level == 2 && entry.perm.ps));
            proof {
                assert(m.is_page(base));
                assert(m.record(base).level == level);
                assert(!m.is_root(base));
                assert(maps_frame == frame_slot(m, base, e));
            }
            if !maps_frame {
                e = e + 1;
                continue;
            }
            let n = base + ((e + 1) / NODES_PER_PAGE) * PAGE_SZ + (e + 1) % NODES_PER_PAGE;
            proof {
                assert(n == mapping_node(base, e));
                assert(mid.mappings@.contains_key(n));
                mid.lemma_mapping_node(n);
            }
            self.unlink_mapping_node(n, Tracked(&mut *steps));
            proof {
                assert((unlinked + 1) * UNLINK_ARM_STEPS == unlinked * UNLINK_ARM_STEPS + UNLINK_ARM_STEPS) by (nonlinear_arith);
                let post = *self;
                let b = tree_of(&post.table_pages, &post.spaces);
                Self::lemma_table_unmap_step(pre, mid, post, base, e, n, unlinked as int);
                assert(Self::table_mapping_step(mid, post, base, n));
                let (old_nodes, old_states) = (nodes, states);
                nodes = old_nodes.push(n);
                states = old_states.push(post);
                assert forall|i: int| #![trigger nodes[i]] 0 <= i < nodes.len() implies Self::table_mapping_step(states[i], states[i + 1], base, nodes[i]) by {
                    if i < old_nodes.len() {
                        assert(old_nodes[i] == nodes[i]);
                        assert(old_states[i] == states[i]);
                        assert(old_states[i + 1] == states[i + 1]);
                    }
                }
                assert forall|j: usize| j < e + 1 implies !#[trigger] frame_slot(b, base, j) by {
                    assert(b.record(base).level == m.record(base).level);
                    if j != e {
                        if j < ENTRIES {
                            assert(b.entry(base, j) == m.entry(base, j));
                        }
                        assert(!frame_slot(m, base, j));
                    } else {
                        assert(!b.entry(base, e).perm.present);
                    }
                }
                if unlinked == 0 {
                    assert(mid == pre);
                    assert(frame_slot(a, base, e));
                }
            }
            unlinked = unlinked + 1;
            e = e + 1;
        }
        proof {
            assert(unlinked * UNLINK_ARM_STEPS <= TABLE_SLICE_BUDGET * UNLINK_ARM_STEPS) by (nonlinear_arith)
                requires
                    unlinked <= TABLE_SLICE_BUDGET,
            ;
            if unlinked == 0 {
                assert(*self == pre);
                assert(e == ENTRIES);
                assert forall|j: usize| !#[trigger] frame_slot(a, base, j) by {
                    if j < ENTRIES {
                        assert(!frame_slot(tree_of(&self.table_pages, &self.spaces), base, j));
                    }
                }
            } else {
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
                assert(Self::table_mapping_steps(pre, *self, base, nodes, states));
            }
        }
        unlinked != 0
    }

    /// Takes a slice of the dead table page at `base`, under the untyped at index `from` of the table at
    /// `root`: the entries naming child tables go first, then the entries mapping frames. Returns whether
    /// it ran, and if not nothing changed.
    pub fn slice_table(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + CUT_SLICE_STEPS + UNMAP_SLICE_STEPS,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_slice_table(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).table_sliced(*final(self), root, from, base),
    {
        if self.cut_table_children(root, from, base, Tracked(&mut *steps)) {
            return true;
        }
        self.unlink_table_mappings(root, from, base, Tracked(steps))
    }

    /// Reclaims the 4K block at `base`, under the untyped at index `from` of the table at `root`. All of
    /// these come from user space, and anything but a free changes nothing.
    pub fn reclaim_frame(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 0) && old(self).frame_is_dead(base / PAGE_SZ)) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / PAGE_SZ),
            ret is Freed ==> old(self).frame_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, 0) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let unreferenced = match entry.kind {
            PageKind::Base => entry.refs == 0,
            _ => false,
        };
        if !unreferenced {
            return ReclaimStep::Refused;
        }
        match entry.object {
            // A frame's block is dead once its references reach zero, which the invariant says.
            ObjectType::Frame => {},
            _ => { return ReclaimStep::Refused; },
        }
        proof {
            assert(pre.holders@.contains_key(BlockRef::Small(page)));
            assert(block_refs(&pre.blocks, BlockRef::Small(page)) == 0);
        }
        if !self.is_acknowledged(page, Tracked(&mut *steps)) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_dead_frame_unmapped(page);
            pre.lemma_acknowledged_is_clean(page);
        }
        self.free_frame(c, page, Tracked(steps));
        proof {
            let post = *self;
            assert(post.view() == pre.view());
            let v = pre.view();
            let e = Effect::Teardown { untyped, object: base };
            assert(authorized(v, root, e));
        }
        ReclaimStep::Freed
    }

    /// A dead large frame at zero references, by what the block table says.
    pub open spec fn region_is_dead(&self, level: Large, r: usize) -> bool {
        match level {
            Large::Two => {
                &&& self.blocks.regions_2m@[r as int].typed
                &&& self.blocks.regions_2m@[r as int].dead
                &&& self.blocks.regions_2m@[r as int].refs == 0
            },
            Large::One => {
                &&& self.blocks.regions_1g@[r as int].typed
                &&& self.blocks.regions_1g@[r as int].dead
                &&& self.blocks.regions_1g@[r as int].refs == 0
            },
        }
    }

    /// A retype of order 9 or 18 may free the large frame at `base`: an untyped covers the block, the
    /// block table has its region, and the frame is dead at zero references.
    pub open spec fn can_reclaim_large(&self, root: usize, from: usize, base: usize, order: u8) -> bool {
        let level = large_level(order);
        let r = base / PAGE_SZ / level_pages(level);
        &&& order == 9 || order == 18
        &&& self.can_retype_under(root, from, base, order)
        &&& r < level_regions(level)
        &&& self.region_is_dead(level, r)
    }

    /// What freeing the 2M or 1G frame at `base` did to self, as frame_freed says for a 4K one: every
    /// page of the region is out of frames and the block is no longer typed. The region is free and not
    /// being zeroed, and the tree, the tables, the processes and the spaces are as they were, so the next
    /// retype of the block can succeed. The epochs, the cores and the IOMMUs are as they were, and so
    /// is the block table but for the freed region, so what a caller knew of another block, or of an
    /// acknowledgement, holds after the free.
    pub open spec fn large_frame_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize, order: u8) -> bool {
        let untyped = self.tables.node_of(root, from);
        let level = large_level(order);
        let r = base / PAGE_SZ / level_pages(level);
        &&& order == 9 || order == 18
        &&& r < level_regions(level)
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.region_is_dead(level, r)
        &&& self.region_clean(level, r)
        &&& !block_typed(&post.blocks, level_ref(level, r))
        &&& post.blocks.large_free(level, r as int)
        &&& !post.zeroing.active(level, r)
        &&& post.list == self.list
        &&& post.tables == self.tables
        &&& post.processes == self.processes
        &&& post.spaces == self.spaces
        &&& post.stale_epoch == self.stale_epoch
        &&& post.cores == self.cores
        &&& post.iommus == self.iommus
        &&& post.blocks.pages@ == self.blocks.pages@
        &&& forall|j: int| 0 <= j < NUM_2M && !(level is Two && j == r)
            ==> #[trigger] post.blocks.regions_2m@[j] == self.blocks.regions_2m@[j]
        &&& forall|j: int| 0 <= j < NUM_1G && !(level is One && j == r)
            ==> #[trigger] post.blocks.regions_1g@[j] == self.blocks.regions_1g@[j]
        &&& forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> !post.frames@.contains_key(i)
        &&& Self::step_ok(*self, post, c as int)
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// Reclaims the 2M or 1G block at `base`, as reclaim_frame does a 4K one.
    pub fn reclaim_large_frame(&mut self, c: usize, root: usize, from: usize, base: usize, order: u8, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS + NUM_IOMMUS,
            ret is Refused ==> final(steps).count == old(steps).count,
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(ret is Unlinked),
            !(ret is Slice),
            !old(self).can_reclaim_large(root, from, base, order) ==> ret is Refused,
            old(self).can_reclaim_large(root, from, base, order) ==> {
                let level = large_level(order);
                if old(self).region_acknowledged(level, base / PAGE_SZ / level_pages(level)) { ret is Freed } else { ret is Again }
            },
            ret is Freed ==> old(self).large_frame_freed(*final(self), c, root, from, base, order),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, order) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let (level, r) = match large_region(base, order) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let entry = self.blocks.region(level, r);
        if !entry.typed || entry.refs != 0 {
            return ReclaimStep::Refused;
        }
        if !self.is_region_acknowledged(level, r, Tracked(steps)) {
            return ReclaimStep::Again;
        }
        proof {
            assert(pre.holders@.contains_key(level_ref(level, r)));
            assert(block_refs(&pre.blocks, level_ref(level, r)) == 0);
            pre.lemma_dead_region_unmapped(level, r);
            pre.lemma_region_acknowledged_is_clean(level, r);
            // A region being zeroed is typed and not dead, so a dead one is not being zeroed.
            let b = (r * level_pages(level)) as usize;
            if pre.zeroing.active(level, r) {
                assert(pre.zeroing.blocks@.contains_key(b));
            }
        }
        self.free_large(c, level, r);
        proof {
            let post = *self;
            assert(!post.zeroing.active(level, r));
            assert(post.view() == pre.view());
            let v = pre.view();
            let e = Effect::Teardown { untyped, object: base };
            assert(authorized(v, root, e));
        }
        ReclaimStep::Freed
    }

    /// A large frame has nothing to tear down either, so its block frees at once, every page's
    /// permission going back.
    fn free_large(&mut self, c: usize, level: Large, r: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            r < level_regions(level),
            old(self).region_is_dead(level, r),
            old(self).region_clean(level, r),
        ensures
            Self::same_tree(*old(self), *final(self)),
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).devices == old(self).devices,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            final(self).zeroing == old(self).zeroing,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).blocks.pages@ == old(self).blocks.pages@,
            forall|j: int| 0 <= j < NUM_2M && !(level is Two && j == r)
                ==> #[trigger] final(self).blocks.regions_2m@[j] == old(self).blocks.regions_2m@[j],
            forall|j: int| 0 <= j < NUM_1G && !(level is One && j == r)
                ==> #[trigger] final(self).blocks.regions_1g@[j] == old(self).blocks.regions_1g@[j],
            !block_typed(&final(self).blocks, level_ref(level, r)),
            final(self).blocks.large_free(level, r as int),
            forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> !final(self).frames@.contains_key(i),
    {
        let ghost pre = *old(self);
        let ghost keys = BlockTable::large_pages(level, r as int);
        self.blocks.mark_large_torn_down(level, r);
        let tracked taken;
        proof {
            lemma_level_pages(level, r);
            assert forall|i: usize| #[trigger] keys.contains(i) implies pre.frames@.dom().contains(i) by {
                assert(block_has_page(level_ref(level, r), i));
                assert(pre.holders@.contains_key(level_ref(level, r)));
            }
            taken = self.frames.borrow_mut().tracked_remove_keys(keys);
        }
        let tracked perms = leak_all(taken);
        proof {
            assert(perms.dom() =~= keys);
            assert forall|i: usize| keys.contains(i) implies #[trigger] holds(perms, i) by {
                assert(taken.contains_key(i));
                assert(pre.frames@.contains_key(i));
            }
        }
        match level {
            Large::Two => self.blocks.free_2m(r, Tracked(perms)),
            Large::One => self.blocks.free_1g(r, Tracked(perms)),
        }
        self.holders = Ghost(pre.holders@.remove(level_ref(level, r)));
        proof {
            let post = *self;
            match level {
                Large::Two => {
                    assert(post.blocks.regions_2m@ =~= pre.blocks.regions_2m@.update(r as int, post.blocks.regions_2m@[r as int]));
                },
                Large::One => {
                    assert(post.blocks.regions_1g@ =~= pre.blocks.regions_1g@.update(r as int, post.blocks.regions_1g@[r as int]));
                },
            }
            assert forall|i: usize| #[trigger] post.frames@.contains_key(i) implies post.frames@[i].addr() == i * PAGE_SZ by {
                assert(pre.frames@.contains_key(i));
            }
            assert forall|br: BlockRef, i: usize| #[trigger] post.holders@.contains_key(br) && #[trigger] block_has_page(br, i)
                implies post.frames@.contains_key(i) by {
                assert(pre.holders@.contains_key(br));
                assert(pre.frames@.contains_key(i));
                if keys.contains(i) {
                    assert(block_has_page(level_ref(level, r), i));
                    lemma_large_block_alone(&pre.blocks, level, r, br, i);
                }
            }
            Self::lemma_large_freed(pre, post, level, r);
        }
    }

    /// A frame has nothing to tear down, so its block frees at once, its permission going back.
    fn free_frame(&mut self, c: usize, page: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).frame_is_dead(page),
            old(self).no_stale_translation(page),
        ensures
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            Self::same_tree(*old(self), *final(self)),
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).devices == old(self).devices,
            final(self).blocks.pages@[page as int].kind is Free,
            !final(self).frames@.contains_key(page),
    {
        let ghost pre = *old(self);
        self.blocks.mark_torn_down(page);
        let tracked mut perm;
        proof {
            assert(pre.holders@.contains_key(BlockRef::Small(page)));
            assert(block_has_page(BlockRef::Small(page), page));
            perm = self.frames.borrow_mut().tracked_remove(page);
            perm.leak_contents();
            assert(perm.addr() == page * PAGE_SZ);
        }
        let tracked mut perms = Map::<usize, PagePerm4k>::tracked_empty();
        proof {
            perms.tracked_insert(page, perm);
            assert(pre.blocks.pages@[page as int].order == 0);
        }
        self.blocks.free_block(page, Tracked(perms), Tracked(steps));
        self.holders = Ghost(pre.holders@.remove(BlockRef::Small(page)));
        proof {
            let post = *self;
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                implies !pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) by {
                if pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) {
                    assert((p / PAGE_SZ) as int == page as int);
                }
            }
            Self::lemma_small_freed(pre, post, page);
        }
    }
}

} // verus!
