//! Retype reclaiming memory. There is no kernel list of dead objects, and no revoke or delete drains
//! another's teardown: a retype naming a block, by a holder of an untyped covering it, does the work.
//! See design/teardown-driven-by-retype/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

use crate::capability::link::*;
use crate::capability::mapping::*;
use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::capability::zero::*;
use crate::define::*;
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

/// The most nodes one retype removes from a dead leaf's slots.
pub const LEAF_SLICE_BUDGET: usize = 64;

/// The most child tables one retype cuts from a dead table page.
pub const TABLE_SLICE_BUDGET: usize = 64;

/// What a reclaim did.
pub enum ReclaimStep {
    /// Nothing changed: the caller may not name this block, or a capability still does.
    Refused,
    /// Nothing changed: a core may still hold a translation to it. Retype again later, since nothing
    /// waits under the lock.
    Again,
    /// The block is free.
    Freed,
    /// The block held a table leaf or table page whose hidden node is now gone, so it is dead, and its
    /// dismantling starts on a later retype.
    Unlinked,
    /// Some of a dead leaf's capabilities, or of a dead table page's children or mappings, went, and more
    /// may remain. Retype again.
    Slice,
}

/// A page the list holds is page aligned, in the node space and initialised at its own address.
proof fn lemma_list_page(list: &Tree, p: usize)
    requires
        list.store_wf(),
        list.pages@.dom().contains(p),
    ensures
        p % 4096 == 0,
        p + 4096 <= NODE_SPACE,
        list.pages@[p].addr() == p,
        list.pages@[p].is_init(),
{
    reveal(Tree::store_wf);
}

/// Two page-aligned addresses on one page are one address.
proof fn lemma_same_page(p: usize, base: usize)
    requires
        p % 4096 == 0,
        base % 4096 == 0,
        p / 4096 == base / 4096,
    ensures
        p == base,
{
    lemma_fundamental_div_mod(p as int, 4096);
    lemma_fundamental_div_mod(base as int, 4096);
}

/// A permission something else holds is no page of the list: two permissions never share an address.
proof fn lemma_list_page_apart<V>(tracked pages: &mut Map<usize, PointsTo<NodePage>>, tracked other: &PointsTo<V>)
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
    &&& perms[i].addr() == i * 4096
    &&& perms[i].is_uninit()
}

/// Takes the five node pages of the table page at base off the list, each as its page's permission.
fn take_table_node_pages(list: &mut Tree, base: usize) -> (ret: Tracked<Map<usize, PagePerm4k>>)
    requires
        old(list).wf(),
        base % 32768 == 0,
        base / 4096 + 8 <= NUM_PAGES,
        forall|k: usize| k < TABLE_NODE_PAGES ==> old(list).pages@.dom().contains(#[trigger] table_node_page(base, k)),
        forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            ==> !old(list).nodes@[table_node(base, k, i) as int].live,
    ensures
        final(list).wf(),
        final(list).seq == old(list).seq,
        final(list).parent == old(list).parent,
        final(list).nodes == old(list).nodes,
        forall|p: usize| #[trigger] final(list).pages@.dom().contains(p)
            == (old(list).pages@.dom().contains(p) && !(base <= p < base + TABLE_NODE_PAGES * 4096)),
        forall|i: usize| base / 4096 <= i < base / 4096 + TABLE_NODE_PAGES ==> #[trigger] holds_free_page(ret@, i),
{
    let ghost pre = *old(list);
    let ghost page = base / 4096;
    proof {
        lemma_table_page_aligned(base);
    }
    let tracked mut perms = Map::<usize, PagePerm4k>::tracked_empty();
    let mut k: usize = 0;
    while k < TABLE_NODE_PAGES
        invariant
            k <= TABLE_NODE_PAGES,
            base % 32768 == 0,
            base % 4096 == 0,
            base as int == 4096 * page,
            page == base / 4096,
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
                == (pre.pages@.dom().contains(p) && !(base <= p < base + k * 4096)),
            forall|i: usize| page <= i < page + k ==> #[trigger] holds_free_page(perms, i),
        decreases TABLE_NODE_PAGES - k,
    {
        let ghost before = *list;
        let ghost held = perms;
        let p = base + k * 4096;
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
                == (pre.pages@.dom().contains(q) && !(base <= q < base + (k + 1) * 4096)) by {
                if pre.pages@.dom().contains(q) && p <= q < p + 4096 {
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
    }
    Tracked(perms)
}

impl CapKernel {
    /// A dead 4K frame at zero references: the block to be freed, by what the block table says.
    pub open spec fn frame_is_dead(&self, page: usize) -> bool {
        &&& page < NUM_PAGES
        &&& self.blocks.pages@[page as int].kind is Base
        &&& self.blocks.pages@[page as int].object is Frame
        &&& self.blocks.pages@[page as int].dead
        &&& self.blocks.pages@[page as int].refs == 0
    }

    /// What freeing the 4K frame at `base` did to self, under the untyped at index `from` of the table
    /// at `root`.
    pub open spec fn frame_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / 4096;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.frame_is_dead(page)
        &&& self.no_stale_translation(page)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& !post.frames@.contains_key(page)
        &&& Self::step_ok(*self, post, c as int)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// A retype may unlink the hidden node of the leaf at `base`: an untyped covers its block, and the
    /// node is still live.
    pub open spec fn can_unlink_leaf(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 1)
        &&& self.tables.owner@.contains_key(base)
        &&& self.list.nodes@[base as int].live
    }

    /// What unlinking the hidden node of the leaf at `base` did to self: that node went, the leaf came
    /// out of its table, and its block is dead at zero. Every capability, the leaf's slots among them,
    /// is as it was, so the view is too.
    pub open spec fn leaf_unlinked(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / 4096;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& !post.list.nodes@[base as int].live
        &&& !post.tables.attached(base)
        &&& post.blocks.pages@[page as int].refs == 0
        &&& post.blocks.pages@[page as int].dead
        &&& Self::caps_frame(*self, post, base, base)
        &&& forall|x: usize| #[trigger] post.is_cap(x) == self.is_cap(x)
        &&& post.view() == self.view()
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
    /// Every capability is as it was, so the view is too.
    pub open spec fn table_page_unlinked(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& Self::table_unlinked(*self, post, base)
        &&& Self::caps_frame(*self, post, base, base)
        &&& forall|x: usize| #[trigger] post.is_cap(x) == self.is_cap(x)
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// What freeing the empty table page at `base` did to self. Its children and mappings went earlier,
    /// so the view is as it was.
    pub open spec fn table_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / 4096;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.table_is_empty(base)
        &&& self.blocks.pages@[page as int].refs == 0
        &&& self.no_stale_translation(page)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& !post.table_pages.maps@.contains_key(base)
        &&& forall|k: usize| k < TABLE_NODE_PAGES ==> !post.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// The leaf at `base` is owned and no node in its page is live, so nothing is left of it but its two
    /// pages.
    pub open spec fn leaf_is_empty(&self, base: usize) -> bool {
        &&& self.tables.owner@.contains_key(base)
        &&& forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] self.list.nodes@[base + k]).live
    }

    /// What freeing the empty leaf at `base` did to self. Its capabilities went earlier, so the view is
    /// as it was.
    pub open spec fn leaf_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / 4096;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.leaf_is_empty(base)
        &&& self.no_stale_translation(page)
        &&& self.no_stale_translation((page + 1) as usize)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& post.blocks.pages@[page + 1int].kind is Free
        &&& !post.tables.owner@.contains_key(base)
        &&& !post.list.pages@.dom().contains(base)
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
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
                i < 512 ==> self.table_pages.maps@[base].value()[i].is_empty(),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert forall|i: usize| #![trigger self.table_pages.maps@[base].value()[i]]
            i < 512 implies self.table_pages.maps@[base].value()[i].is_empty() by {
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
            self.mappings@[n].table % 32768 == 0,
            self.mappings@[n].entry < 512,
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
        lemma_node_page_names_block(base, self.mappings@[n].table, n / 4096);
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
            page < NUM_PAGES,
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
                BlockRef::Two(r) => { lemma_large_block_alone(&self.blocks, Large::Two, r, BlockRef::Small(page), page); },
                BlockRef::One(r) => { lemma_large_block_alone(&self.blocks, Large::One, r, BlockRef::Small(page), page); },
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

    /// A retype naming the block at `base`, under the untyped at index `from` of the table at `root`:
    /// what it does depends on what the block holds. All of these come from user space.
    pub fn reclaim(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused || ret is Again ==> *final(self) == *old(self),
            !((old(self).can_retype_under(root, from, base, 0) && old(self).frame_is_dead(base / 4096))
                || old(self).can_unlink_leaf(root, from, base)
                || (old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base))
                || old(self).can_slice_leaf(root, from, base)
                || old(self).can_unlink_table(root, from, base)
                || old(self).can_slice_table(root, from, base)
                || (old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base))
                || old(self).can_cut_space(root, from, base)
                || (old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base))) ==> ret is Refused,
            !old(self).view().holds_right(root, old(self).tables.node_of(root, from), Right::Retype) ==> ret is Refused,
            old(self).spaces.roots@.contains_key(base) && !old(self).dead_io_space(base) ==> ret is Refused,
            old(self).can_cut_space(root, from, base) ==> ret is Slice,
            old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base)
                ==> if old(self).acknowledged(base / 4096) { ret is Freed } else { ret is Again },
            old(self).can_retype_under(root, from, base, 3) && old(self).space_is_spent(base) ==> ret is Again || ret is Freed,
            old(self).spaces.roots@.contains_key(base) && ret is Slice ==> old(self).space_children_cut(*final(self), root, from, base),
            old(self).spaces.roots@.contains_key(base) && ret is Freed ==> old(self).space_freed(*final(self), c, root, from, base),
            old(self).can_unlink_table(root, from, base) ==> ret is Unlinked,
            old(self).can_slice_table(root, from, base) ==> ret is Slice,
            old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base)
                ==> if old(self).acknowledged(base / 4096) { ret is Freed } else { ret is Again },
            old(self).can_retype_under(root, from, base, 3) && old(self).table_is_spent(base) ==> ret is Again || ret is Freed,
            old(self).table_pages.maps@.contains_key(base) && ret is Unlinked ==> old(self).table_page_unlinked(*final(self), root, from, base),
            old(self).table_pages.maps@.contains_key(base) && ret is Slice ==> old(self).table_sliced(*final(self), root, from, base),
            old(self).table_pages.maps@.contains_key(base) && ret is Freed ==> old(self).table_freed(*final(self), c, root, from, base),
            ret is Again ==> !old(self).acknowledged(base / 4096) || !old(self).acknowledged((base / 4096 + 1) as usize),
            ret is Freed ==> old(self).frame_freed(*final(self), c, root, from, base)
                || old(self).leaf_freed(*final(self), c, root, from, base)
                || old(self).table_freed(*final(self), c, root, from, base)
                || old(self).space_freed(*final(self), c, root, from, base),
            ret is Slice ==> old(self).leaf_sliced(*final(self), root, from, base)
                || old(self).table_sliced(*final(self), root, from, base)
                || old(self).space_children_cut(*final(self), root, from, base),
            ret is Unlinked ==> old(self).leaf_unlinked(*final(self), root, from, base)
                || old(self).table_page_unlinked(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_retype_holds_right(root, from, base, 0);
            pre.lemma_retype_holds_right(root, from, base, 1);
            pre.lemma_retype_holds_right(root, from, base, 3);
            pre.lemma_empty_table_no_work(root, from, base);
            pre.lemma_spent_table_is_empty(base);
            pre.lemma_spent_space_is_empty(base);
        }
        let page = base / 4096;
        if page >= NUM_PAGES {
            return ReclaimStep::Refused;
        }
        let object = self.blocks.pages.get(page).object;
        match object {
            ObjectType::Frame => self.reclaim_frame(c, root, from, base),
            ObjectType::TableLeaf => {
                if self.unlink_leaf(root, from, base) {
                    ReclaimStep::Unlinked
                } else if self.slice_leaf(root, from, base) {
                    ReclaimStep::Slice
                } else {
                    self.free_leaf(c, root, from, base)
                }
            },
            ObjectType::TablePage => {
                if self.unlink_table(root, from, base) {
                    ReclaimStep::Unlinked
                } else if self.slice_table(root, from, base) {
                    ReclaimStep::Slice
                } else {
                    self.free_table(c, root, from, base)
                }
            },
            ObjectType::Space => {
                if self.cut_space_children(root, from, base) {
                    ReclaimStep::Slice
                } else {
                    self.free_space(c, root, from, base)
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
    /// all from what the leaf's process held, and the leaf is still detached with its owner.
    pub open spec fn leaf_sliced(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let object = self.tables.owner@[base].0;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& post.list.seq@.len() < self.list.seq@.len()
        &&& self.list.seq@.len() - post.list.seq@.len() <= LEAF_SLICE_BUDGET
        &&& post.tables.owner == self.tables.owner
        &&& post.list.parent == self.list.parent
        &&& !post.list.nodes@[base as int].live
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object })
    }

    /// Takes a slice of the dead leaf at `base`, under the untyped at index `from` of the table at `root`:
    /// up to a budget of nodes from its slots' runs, each slot going itself once childless. Returns
    /// whether it ran, and if not nothing changed. Dead slots stay dead while the leaf is detached, so a
    /// slice can walk them once and the next starts again from the first.
    pub fn slice_leaf(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_slice_leaf(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).leaf_sliced(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, 1) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / 4096;
        proof {
            lemma2_to64();
            pre.lemma_leaf_in_range(base);
        }
        if page >= NUM_PAGES {
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
        }
        let mut steps = 0;
        let mut k = 1;
        while steps != LEAF_SLICE_BUDGET && k != NODES_PER_PAGE && self.flush_epoch != usize::MAX
            invariant
                Self::mappings_shrunk(*old(self), *self),
                self.wf(),
                pre == *old(self),
                steps <= LEAF_SLICE_BUDGET,
                1 <= k <= NODES_PER_PAGE,
                base % 8192 == 0,
                pre.tables.owner@.contains_key(base),
                object == pre.tables.owner@[base].0,
                pre.view().holds_right(root, untyped, Right::Retype),
                self.tables.owner == pre.tables.owner,
                self.list.parent == pre.list.parent,
                pre.list.seq@.len() == self.list.seq@.len() + steps,
                !self.list.nodes@[base as int].live,
                steps == 0 ==> *self == pre,
                steps > 0 ==> !pre.leaf_is_empty(base) && pre.flush_epoch < usize::MAX,
                forall|j: int| 0 <= j < k ==> !(#[trigger] self.list.nodes@[base + j]).live,
                discharges(pre.view(), self.view(), root, Effect::Teardown { untyped, object }),
                forall|h: (ObjectId, NodeId)| #[trigger] self.view().held.contains(h) ==> pre.view().held.contains(h),
            decreases LEAF_SLICE_BUDGET - steps, NODES_PER_PAGE - k,
        {
            proof {
                self.lemma_leaf_slot_valid(base, k);
                lemma_slot_in_leaf(base, k);
                self.lemma_slot_bound((base + k) as usize);
            }
            let n = base + k;
            if !self.list.get(n).live {
                k = k + 1;
                continue;
            }
            proof {
                self.lemma_live_slot_is_cap(n);
                if steps == 0 {
                    assert(pre.list.nodes@[base + k as int].live);
                }
            }
            let ghost mid = *self;
            if !self.revoke_step(Ghost(object), n) {
                proof {
                    let r = choose|r: usize| #[trigger] revoked_one(mid.list, self.list, n, r)
                        && (mid.list.nodes@[r as int].kind is Hidden && mid.tables.owner@.contains_key(r)
                            ==> !self.tables.attached(r));
                    lemma_revoke_is_teardown(mid.view(), self.view(), object, n);
                    Self::lemma_slice_step(pre, mid, *self, root, untyped, object);
                    Self::lemma_leaf_slots_stay_dead(mid, *self, base, k as int, r);
                }
                steps = steps + 1;
                continue;
            }
            self.unlink_childless_slot(Ghost(object), n);
            proof {
                lemma_delete_is_teardown(mid.view(), self.view(), object);
                Self::lemma_slice_step(pre, mid, *self, root, untyped, object);
                Self::lemma_leaf_slots_stay_dead(mid, *self, base, k as int, n);
            }
            steps = steps + 1;
            k = k + 1;
        }
        steps != 0
    }

    /// An owned leaf's block is in the block table's range.
    proof fn lemma_leaf_in_range(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.tables.owner@.contains_key(base) ==> base / 4096 < NUM_PAGES,
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

    /// Unlinks the childless capability in slot n, which the object held, and nothing more.
    fn unlink_childless_slot(&mut self, Ghost(object): Ghost<usize>, n: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).is_cap(n),
            old(self).tables.owner@[page_of(n)].0 == object,
            old(self).list.childless(n),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            final(self).tables.owner == old(self).tables.owner,
            final(self).list.parent == old(self).list.parent,
            final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            !final(self).list.nodes@[n as int].live,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==>
                #[trigger] final(self).list.nodes@[x].live == old(self).list.nodes@[x].live,
            forall|x: usize| #[trigger] final(self).is_cap(x) ==> old(self).is_cap(x),
            discharges(old(self).view(), final(self).view(), object, Effect::Local),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_leaf_node_not_first(n);
        }
        self.unlink_arm(n);
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
            Self::lemma_delete_holders(pre, post, n);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_delete_discharges(pre, post, object, n);
            assert forall|x: usize| #[trigger] post.is_cap(x) implies pre.is_cap(x) by {
                if x != n {
                    Self::lemma_caps_frame(pre, post, n, n, x);
                }
            }
        }
    }

    /// Frees the leaf at `base`, under the untyped at index `from` of the table at `root`, once its block
    /// is at zero references and no node in its page is live. All of these come from user space, and
    /// anything but a free changes nothing.
    pub fn free_leaf(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base)) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / 4096) || !old(self).acknowledged((base / 4096 + 1) as usize),
            ret is Freed ==> old(self).leaf_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, 1) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / 4096;
        if page >= NUM_PAGES {
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
        if !leaf || !self.leaf_nodes_dead(base) {
            return ReclaimStep::Refused;
        }
        proof {
            // A leaf's block is 2 pages, aligned to them, so the second lies in the range too.
            assert(page + 1 < NUM_PAGES) by {
                assert(base % 8192 == 0);
                assert(page == base / 4096);
            }
        }
        if !self.is_acknowledged(page) || !self.is_acknowledged(page + 1) {
            return ReclaimStep::Again;
        }
        proof {
            assert(pre.tables.owner@.contains_key(base));
            pre.lemma_leaf_unmapped(page, page);
            pre.lemma_leaf_unmapped(page, (page + 1) as usize);
            pre.lemma_acknowledged_is_clean(page);
            pre.lemma_acknowledged_is_clean((page + 1) as usize);
        }
        self.free_empty_leaf(base);
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
    pub fn free_table(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, 3) && old(self).table_is_empty(base)
                ==> if old(self).acknowledged(base / 4096) { ret is Freed } else { ret is Again },
            ret is Again ==> !old(self).acknowledged(base / 4096),
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
        let page = base / 4096;
        if page >= NUM_PAGES {
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
        if !table || !self.table_nothing_left(base) {
            return ReclaimStep::Refused;
        }
        if !self.is_acknowledged(page) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_acknowledged_is_clean(page);
        }
        self.free_empty_table(base);
        proof {
            let post = *self;
            assert(post.view() == pre.view());
            let v = pre.view();
            let e = Effect::Teardown { untyped, object: base };
            assert(authorized(v, root, e));
        }
        ReclaimStep::Freed
    }

    /// Whether every node of the table page at `base` is dead and every entry empty. A table page holds a
    /// constant number of each.
    fn table_nothing_left(&self, base: usize) -> (ret: bool)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(base),
        ensures
            ret == self.table_is_empty(base),
    {
        let ghost tree = tree_of(&self.table_pages, &self.spaces);
        proof {
            self.lemma_table_page_room(base);
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        }
        if !self.block_nodes_dead(base) {
            return false;
        }
        let mut e = 0;
        while e != 512
            invariant
                0 <= e <= 512,
                self.wf(),
                self.table_pages.maps@.contains_key(base),
                tree == tree_of(&self.table_pages, &self.spaces),
                forall|j: usize, i: usize| #![trigger table_node(base, j, i)] j < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                    ==> !self.list.nodes@[table_node(base, j, i) as int].live,
                forall|j: usize| #![trigger self.table_pages.maps@[base].value()[j]]
                    j < e ==> self.table_pages.maps@[base].value()[j].is_empty(),
            decreases 512 - e,
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
        }
        true
    }

    /// Whether every node in the node pages of the table page or space at `base` is dead. The pages hold a
    /// constant number.
    fn block_nodes_dead(&self, base: usize) -> (ret: bool)
        requires
            self.wf(),
            base % 32768 == 0,
            base / 4096 + 8 <= NUM_PAGES,
            forall|k: usize| k < TABLE_NODE_PAGES ==> self.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
        ensures
            ret == (forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                ==> !self.list.nodes@[table_node(base, k, i) as int].live),
    {
        let mut k = 0;
        while k != TABLE_NODE_PAGES
            invariant
                0 <= k <= TABLE_NODE_PAGES,
                self.wf(),
                base % 32768 == 0,
                base / 4096 + 8 <= NUM_PAGES,
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
                    self.wf(),
                    base % 32768 == 0,
                    base / 4096 + 8 <= NUM_PAGES,
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
                if self.list.get(base + k * 4096 + i).live {
                    return false;
                }
                i = i + 1;
            }
            k = k + 1;
        }
        true
    }

    /// Whether the root of the IO space at `base` has no entry. A space's node pages hold no live node.
    fn space_nothing_left(&self, base: usize) -> (ret: bool)
        requires
            self.wf(),
            self.dead_io_space(base),
            !self.table_pages.maps@.contains_key(base),
        ensures
            ret == self.space_is_empty(base),
    {
        let ghost tree = tree_of(&self.table_pages, &self.spaces);
        let mut e = 0;
        while e != 512
            invariant
                0 <= e <= 512,
                self.wf(),
                self.dead_io_space(base),
                !self.table_pages.maps@.contains_key(base),
                tree == tree_of(&self.table_pages, &self.spaces),
                forall|j: usize, i: usize| #![trigger table_node(base, j, i)] j < TABLE_NODE_PAGES && i < NODES_PER_PAGE
                    ==> !self.list.nodes@[table_node(base, j, i) as int].live,
                forall|j: usize| #![trigger self.spaces.roots@[base].value()[j]]
                    j < e ==> self.spaces.roots@[base].value()[j].is_empty(),
            decreases 512 - e,
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
        }
        true
    }

    /// Whether every node of the owned leaf at `base` is dead. A leaf's page holds a constant number.
    fn leaf_nodes_dead(&self, base: usize) -> (ret: bool)
        requires
            self.wf(),
            self.tables.owner@.contains_key(base),
        ensures
            ret == self.leaf_is_empty(base),
    {
        let mut k = 0;
        while k != NODES_PER_PAGE
            invariant
                0 <= k <= NODES_PER_PAGE,
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
        }
        true
    }

    /// Both pages of an empty leaf go back to the block table, its block's teardown being finished.
    fn free_empty_leaf(&mut self, base: usize)
        requires
            old(self).wf(),
            old(self).leaf_is_empty(base),
            old(self).blocks.pages@[(base / 4096) as int].refs == 0,
            old(self).no_stale_translation(base / 4096),
            old(self).no_stale_translation((base / 4096 + 1) as usize),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            final(self).blocks.pages@[(base / 4096) as int].kind is Free,
            final(self).blocks.pages@[base / 4096 + 1int].kind is Free,
            !final(self).tables.owner@.contains_key(base),
            !final(self).list.pages@.dom().contains(base),
            final(self).cores == old(self).cores,
            final(self).view() == old(self).view(),
    {
        let ghost pre = *old(self);
        let page = base / 4096;
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
        self.blocks.free_block(page, Tracked(perms));
        proof {
            let post = *self;
            assert forall|i: int| 0 <= i < NUM_PAGES implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            Self::lemma_leaf_freed(pre, post, base);
            assert(pre.blocks.in_block(page as int, page as int));
            assert(pre.blocks.in_block(page as int, page + 1int));
        }
    }

    /// An empty leaf's block is in the block table's range, so a block outside it is not one.
    proof fn lemma_empty_leaf_in_range(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.leaf_is_empty(base) ==> base / 4096 < NUM_PAGES,
    {
    }

    /// The block test free_leaf makes reads as the node does: a table leaf block at zero references is
    /// an owned leaf's whose hidden node is dead, and such a leaf's block is a dead table leaf block at
    /// zero. An empty leaf is one.
    proof fn lemma_dead_leaf_block(&self, base: usize)
        requires
            self.wf(),
            base % 8192 == 0,
            base / 4096 < NUM_PAGES,
        ensures
            (leaf_block(&self.blocks, base / 4096) && self.blocks.pages@[(base / 4096) as int].refs == 0)
                == (self.tables.owner@.contains_key(base) && !self.list.nodes@[base as int].live),
            self.leaf_is_empty(base) ==> !self.list.nodes@[base as int].live,
    {
        lemma_leaf_page(base);
        if leaf_block(&self.blocks, base / 4096) {
            assert(self.tables.owner@.contains_key(((base / 4096) * 4096) as usize));
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
            base % 8192 == 0,
            base % 4096 == 0,
            base / 4096 < NUM_PAGES,
            base / 4096 + 1 < NUM_PAGES,
            (base / 4096) * 4096 == base,
            self.blocks.pages@[(base / 4096) as int].kind is Base,
            self.blocks.pages@[(base / 4096) as int].object is TableLeaf,
            self.blocks.pages@[(base / 4096) as int].order == 1,
            self.blocks.pages@[(base / 4096) as int].refs == 0,
            self.blocks.pages@[(base / 4096) as int].dead,
            self.blocks.pages@[base / 4096 + 1int].kind is Member,
            !self.list.nodes@[base as int].live,
            !self.tables.attached(base),
            self.list.pages@.dom().contains(base),
            self.list.pages@[base].addr() == base,
            self.list.pages@[base].is_init(),
    {
        let page = base / 4096;
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
            base % 4096 == 0,
            (base / 4096) * 4096 == base,
            perms.contains_key(base / 4096),
            perms.contains_key((base / 4096 + 1) as usize),
            perms[base / 4096].addr() == base,
            perms[base / 4096].is_uninit(),
            perms[(base / 4096 + 1) as usize].addr() == base + 4096,
            perms[(base / 4096 + 1) as usize].is_uninit(),
        ensures
            forall|k: usize| k < order_pages(1) ==> {
                &&& perms.contains_key((base / 4096 + k) as usize)
                &&& #[trigger] perms[(base / 4096 + k) as usize].addr() == (base / 4096 + k) * 4096
                &&& perms[(base / 4096 + k) as usize].is_uninit()
            },
    {
        let page = base / 4096;
        assert forall|k: usize| k < order_pages(1) implies {
            &&& perms.contains_key((page + k) as usize)
            &&& #[trigger] perms[(page + k) as usize].addr() == (page + k) * 4096
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
                ==> !self.blocks.in_block((base / 4096) as int, (l / 4096) as int),
            forall|p: usize| #[trigger] self.list.pages@.dom().contains(p) && p != base
                ==> !self.blocks.in_block((base / 4096) as int, (p / 4096) as int),
            forall|b: usize| #[trigger] self.holders@.contains_key(BlockRef::Small(b))
                ==> !self.blocks.in_block((base / 4096) as int, b as int),
    {
        let page = base / 4096;
        self.lemma_empty_leaf(base);
        assert forall|l: usize| #[trigger] self.tables.owner@.contains_key(l) && l != base
            implies !self.blocks.in_block(page as int, (l / 4096) as int) by {
            self.tables.lemma_leaf(&self.list, l);
            lemma_leaf_pages_distinct(l, base);
            assert(self.blocks.pages@[(l / 4096) as int].kind is Base);
        }
        assert forall|p: usize| #[trigger] self.list.pages@.dom().contains(p) && p != base
            implies !self.blocks.in_block(page as int, (p / 4096) as int) by {
            lemma_list_page(&self.list, p);
            if p / 4096 == page {
                lemma_same_page(p, base);
            }
            if self.blocks.in_block(page as int, (p / 4096) as int) {
                self.blocks.lemma_member_of(page as int, (p / 4096) as int);
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
                assert(x as int == base + (x % 4096) as int);
                assert(!pre.list.nodes@[base + (x % 4096) as int].live);
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
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / 4096) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
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
            post.mappings == pre.mappings,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            zeroing_typed(&post.zeroing, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let page = base / 4096;
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
        assert forall|b: usize| b < NUM_PAGES && (#[trigger] post.blocks.pages@[b as int]).kind is Base
            && post.blocks.pages@[b as int].object is Frame implies {
            &&& post.blocks.pages@[b as int].order == 0
            &&& post.blocks.pages@[b as int].refs == 0 ==> post.holders@.contains_key(BlockRef::Small(b))
        } by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& l / 4096 < NUM_PAGES
            &&& post.blocks.pages@[(l / 4096) as int] == pre.blocks.pages@[(l / 4096) as int]
        } by {
            assert(pre.tables.owner@.contains_key(l));
        }
        assert forall|b: usize| b < NUM_PAGES && #[trigger] leaf_block(&post.blocks, b)
            implies post.tables.owner@.contains_key((b * 4096) as usize) by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
            assert(leaf_block(&pre.blocks, b));
            lemma_page_base(b);
        }
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
            implies !pre.blocks.in_block(page as int, (p / 4096) as int) by {
            assert(pre.list.pages@.dom().contains(p));
            assert(p != base);
        }
        lemma_list_pages_used_subset(&pre.list, &post.list, &pre.blocks);
        lemma_list_pages_used_small_freed(&post.list, &pre.blocks, &post.blocks, page);
        lemma_table_node_pages_kept(&pre.list, &post.list, &pre.table_pages, &pre.blocks, base);
        lemma_table_pages_small_freed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, page);
        lemma_space_node_pages_kept(&pre.list, &post.list, &pre.tables, &pre.spaces, &pre.blocks, base);
        lemma_spaces_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page);
    }

    /// The kernel after the empty leaf at `base` frees: nothing but its block, its owner entry and its
    /// list page changed, and the view is as it was.
    proof fn lemma_leaf_freed(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            pre.leaf_is_empty(base),
            post.blocks.wf(),
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / 4096) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.tables.wf(&pre.list),
            post.tables.owner@ == pre.tables.owner@.remove(base),
            post.tables.payloads@ == pre.tables.payloads@.remove(base),
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
        ensures
            post.wf(),
            post.view() == pre.view(),
    {
        pre.lemma_empty_leaf(base);
        Self::lemma_leaf_freed_caps(pre, post, base);
        Self::lemma_leaf_freed_blocks(pre, post, base);
        Self::lemma_tlb_same(pre, post);
        assert forall|n: usize| n < NODE_SPACE && (#[trigger] post.list.nodes@[n as int]).live
            && post.list.nodes@[n as int].kind is Hidden
            implies post.tables.owner@.contains_key(n) || post.table_pages.maps@.contains_key(n) by {
            assert(pre.tables.owner@.contains_key(n) || pre.table_pages.maps@.contains_key(n));
            assert(n != base);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) && post.tables.attached(l) implies {
            &&& l < NODE_SPACE
            &&& post.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind is Hidden
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(post.tables.payloads@[l] == pre.tables.payloads@[l]);
            assert(pre.tables.attached(l));
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
            i < 512 ==> self.table_pages.maps@[base].value()[i].is_empty()
    }

    /// The block at `base` holds a table page or a space, with no reference and no live node.
    pub open spec fn empty_node_block(&self, base: usize) -> bool {
        &&& base % 32768 == 0
        &&& base / 4096 + 8 <= NUM_PAGES
        &&& self.blocks.pages@[(base / 4096) as int].kind is Base
        &&& self.blocks.pages@[(base / 4096) as int].object is TablePage
            || self.blocks.pages@[(base / 4096) as int].object is Space
        &&& self.blocks.pages@[(base / 4096) as int].order == 3
        &&& self.blocks.pages@[(base / 4096) as int].refs == 0
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
            assert(e < 512);
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
            base % 32768 == 0,
            base % 4096 == 0,
            base as int == 4096 * (base / 4096) as int,
            (base / 4096) % 8 == 0,
            base / 4096 + 8 <= NUM_PAGES,
            self.blocks.pages@[(base / 4096) as int].kind is Base,
            self.blocks.pages@[(base / 4096) as int].object is TablePage,
            self.blocks.pages@[(base / 4096) as int].order == 3,
            self.blocks.pages@[(base / 4096) as int].refs == 0,
            self.blocks.pages@[(base / 4096) as int].dead,
            !self.list.nodes@[base as int].live,
            self.table_pages.records@[base].value().parent is None,
            !self.spaces.roots@.contains_key(base),
            self.table_pages.maps@[base].addr() == base + 5 * 4096,
            self.table_pages.records@.contains_key(base),
            self.table_pages.records@[base].addr() == base + 6 * 4096,
            self.table_pages.spare@.contains_key((base + 7 * 4096) as usize),
            self.table_pages.spare@[(base + 7 * 4096) as usize].addr() == base + 7 * 4096,
            self.table_pages.spare@[(base + 7 * 4096) as usize].is_uninit(),
            forall|k: usize| k < TABLE_NODE_PAGES ==> self.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            self.empty_node_block(base),
    {
        let page = base / 4096;
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
            !(base <= page_of(n) < base + TABLE_NODE_PAGES * 4096),
    {
        lemma_table_page_aligned(base);
        lemma_list_page(&self.list, page_of(n));
        if base <= page_of(n) < base + TABLE_NODE_PAGES * 4096 {
            let k = ((page_of(n) - base) / 4096) as usize;
            let i = (n % 4096) as usize;
            assert(page_of(n) == base + k * 4096);
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
                ==> !self.blocks.in_block((base / 4096) as int, (l / 4096) as int) && !(base <= l < base + TABLE_NODE_PAGES * 4096),
            forall|b: usize| #[trigger] self.holders@.contains_key(BlockRef::Small(b))
                ==> !self.blocks.in_block((base / 4096) as int, b as int),
    {
        let page = base / 4096;
        lemma_table_page_aligned(base);
        assert(order_pages(3) == 8);
        assert forall|l: usize| #[trigger] self.tables.owner@.contains_key(l) implies
            !self.blocks.in_block(page as int, (l / 4096) as int) && !(base <= l < base + TABLE_NODE_PAGES * 4096) by {
            self.tables.lemma_leaf(&self.list, l);
            let x = (l / 4096) as int;
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
        let page = base / 4096;
        &&& pre.wf()
        &&& pre.empty_node_block(base)
        &&& post.blocks.wf()
        &&& forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] post.blocks.pages@[i] == (
            if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] })
        &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@
        &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@
        &&& post.tables == pre.tables
        &&& post.list.wf()
        &&& post.list.seq == pre.list.seq
        &&& post.list.parent == pre.list.parent
        &&& post.list.nodes == pre.list.nodes
        &&& forall|p: usize| #[trigger] post.list.pages@.dom().contains(p)
            == (pre.list.pages@.dom().contains(p) && !(base <= p < base + TABLE_NODE_PAGES * 4096))
        &&& forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> !(base + 5 * 4096 <= p < base + 8 * 4096)
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
    }

    /// One step of an empty table page going: its table, record and spare page go with its block.
    pub open spec fn table_freed_step(pre: Self, post: Self, base: usize) -> bool {
        &&& Self::node_block_freed_step(pre, post, base)
        &&& pre.table_is_empty(base)
        &&& post.table_pages.maps@ == pre.table_pages.maps@.remove(base)
        &&& post.table_pages.records@ == pre.table_pages.records@.remove(base)
        &&& post.table_pages.spare@ == pre.table_pages.spare@.remove((base + 7 * 4096) as usize)
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
        assert forall|i: usize| i < 512 implies #[trigger] a.entry(base, i).is_empty() by {
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

    /// A list page after the step is in no page of the freed block.
    proof fn lemma_node_block_list_pages(pre: Self, post: Self, base: usize)
        requires
            Self::node_block_freed_step(pre, post, base),
        ensures
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
                ==> !pre.blocks.in_block((base / 4096) as int, (p / 4096) as int),
    {
        let page = base / 4096;
        lemma_table_page_aligned(base);
        assert(order_pages(3) == 8);
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
            implies !pre.blocks.in_block(page as int, (p / 4096) as int) by {
            assert(pre.list.pages@.dom().contains(p));
            lemma_list_page(&pre.list, p);
            assert(!(base <= p < base + 5 * 4096));
            assert(!(base + 5 * 4096 <= p < base + 8 * 4096));
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
            list_pages_used(&post.list, &post.blocks),
    {
        let page = base / 4096;
        pre.lemma_empty_table(base);
        Self::lemma_node_block_list_pages(pre, post, base);
        assert(order_pages(3) == 8);
        assert forall|t: usize| #[trigger] post.table_pages.maps@.contains_key(t)
            implies table_page_wf(&post.list, &post.table_pages, &post.blocks, t) by {
            assert(t != base);
            assert(pre.table_pages.maps@.contains_key(t));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
            lemma_table_pages_distinct(t, base);
            pre.blocks.lemma_base((t / 4096) as int);
            if pre.blocks.in_block(page as int, (t / 4096) as int) && t / 4096 != page {
                pre.blocks.lemma_member_of(page as int, (t / 4096) as int);
            }
            assert(post.blocks.pages@[(t / 4096) as int] == pre.blocks.pages@[(t / 4096) as int]);
            assert(post.table_pages.spare@[(t + 7 * 4096) as usize] == pre.table_pages.spare@[(t + 7 * 4096) as usize]);
            assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
                assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
                lemma_table_node_page(t, k);
            }
            assert forall|i: usize| #![trigger post.table_pages.maps@[t].value()[i]]
                i < 512 && !post.table_pages.records@[t].value().written implies post.table_pages.maps@[t].value()[i].is_empty() by {
                assert(pre.table_pages.maps@[t].value()[i].is_empty());
            }
        }
        assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(&post.blocks, x)
            implies post.table_pages.maps@.contains_key((x * 4096) as usize) by {
            if pre.blocks.in_block(page as int, x as int) {
                assert(post.blocks.pages@[x as int] == free_entry());
            }
            assert(post.blocks.pages@[x as int] == pre.blocks.pages@[x as int]);
            assert(table_block(&pre.blocks, x));
            assert(x != page);
            assert((x * 4096) as usize != base);
        }
        assert forall|s: usize, k: usize| #[trigger] pre.spaces.roots@.contains_key(s) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
            assert(pre.list.pages@.dom().contains(table_node_page(s, k)));
            assert(s != base);
            pre.blocks.lemma_base((s / 4096) as int);
            lemma_table_node_page(s, k);
        }
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_spaces_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page);
        lemma_list_pages_used_subset(&pre.list, &post.list, &pre.blocks);
        lemma_list_pages_used_small_freed(&post.list, &pre.blocks, &post.blocks, page);
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
        let page = base / 4096;
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
        assert forall|b: usize| b < NUM_PAGES && (#[trigger] post.blocks.pages@[b as int]).kind is Base
            && post.blocks.pages@[b as int].object is Frame implies {
            &&& post.blocks.pages@[b as int].order == 0
            &&& post.blocks.pages@[b as int].refs == 0 ==> post.holders@.contains_key(BlockRef::Small(b))
        } by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& l / 4096 < NUM_PAGES
            &&& post.blocks.pages@[(l / 4096) as int] == pre.blocks.pages@[(l / 4096) as int]
        } by {
            assert(pre.tables.owner@.contains_key(l));
        }
        assert forall|b: usize| b < NUM_PAGES && #[trigger] leaf_block(&post.blocks, b)
            implies post.tables.owner@.contains_key((b * 4096) as usize) by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
            assert(leaf_block(&pre.blocks, b));
            lemma_page_base(b);
        }
    }

    /// The capabilities and the view after the empty block at `base` goes: no capability was in a page of
    /// it.
    proof fn lemma_node_block_caps(pre: Self, post: Self, base: usize)
        requires
            Self::node_block_freed_step(pre, post, base),
        ensures
            post.tables.wf(&post.list),
            post.tables.caps_wf(&post.list),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            post.view() == pre.view(),
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
        assert(b == a);
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
        Self::lemma_node_block_caps(pre, post, base);
        Self::lemma_table_freed_tree(pre, post, base);
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
    pub fn free_empty_table(&mut self, base: usize)
        requires
            old(self).wf(),
            old(self).table_is_empty(base),
            old(self).blocks.pages@[(base / 4096) as int].refs == 0,
            old(self).no_stale_translation(base / 4096),
        ensures
            final(self).wf(),
            final(self).blocks.pages@[(base / 4096) as int].kind is Free,
            !final(self).table_pages.maps@.contains_key(base),
            forall|k: usize| k < TABLE_NODE_PAGES ==> !final(self).list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            forall|r: usize, p: SpacePath| #[trigger] walk(tree_of(&final(self).table_pages, &final(self).spaces), r, p)
                == walk(tree_of(&old(self).table_pages, &old(self).spaces), r, p),
            final(self).cores == old(self).cores,
            final(self).view() == old(self).view(),
    {
        let ghost pre = *old(self);
        let page = base / 4096;
        proof {
            pre.lemma_empty_table(base);
            crate::layouts::lemma_table_block_layouts();
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies pre.list.pages@[p].addr() == p by {
                lemma_list_page(&pre.list, p);
            }
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.table_pages.maps.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.table_pages.records.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.table_pages.spare.borrow().tracked_borrow((base + 7 * 4096) as usize));
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies !(base + 5 * 4096 <= p < base + 8 * 4096) by {
                lemma_list_page(&pre.list, p);
            }
        }
        self.blocks.mark_torn_down(page);
        let ghost mid = *self;
        let Tracked(nodes) = take_table_node_pages(&mut self.list, base);
        let tracked mut perms = nodes;
        proof {
            let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(base);
            let tracked mut record = self.table_pages.records.borrow_mut().tracked_remove(base);
            let tracked spare = self.table_pages.spare.borrow_mut().tracked_remove((base + 7 * 4096) as usize);
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
                &&& perms[(page + k) as usize].addr() == (page + k) * 4096
                &&& perms[(page + k) as usize].is_uninit()
            } by {
                if k < 5 {
                    assert(holds_free_page(nodes, (page + k) as usize));
                }
            }
        }
        self.blocks.free_block(page, Tracked(perms));
        proof {
            let post = *self;
            assert forall|i: int| 0 <= i < NUM_PAGES implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            assert(Self::table_freed_step(pre, post, base));
            Self::lemma_table_freed(pre, post, base);
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

    /// The dead IO space at `base` has no live node and its root no entry, so its block holds nothing the
    /// kernel still uses.
    pub open spec fn space_is_empty(&self, base: usize) -> bool {
        &&& self.dead_io_space(base)
        &&& forall|k: usize, i: usize| #![trigger table_node(base, k, i)] k < TABLE_NODE_PAGES && i < NODES_PER_PAGE
            ==> !self.list.nodes@[table_node(base, k, i) as int].live
        &&& forall|i: usize| #![trigger self.spaces.roots@[base].value()[i]]
            i < 512 ==> self.spaces.roots@[base].value()[i].is_empty()
    }

    /// The dead IO space at `base` has nothing left to cut: no entry of its root names a child.
    pub open spec fn space_is_spent(&self, base: usize) -> bool {
        &&& self.dead_io_space(base)
        &&& !exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
    }

    /// A spent IO space is empty, so cutting it to the end leaves what a free takes. An IO root has no
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
                i < 512 implies self.spaces.roots@[base].value()[i].is_empty() by {
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
            base % 4096 == 0,
            base as int == 4096 * (base / 4096) as int,
            self.blocks.pages@[(base / 4096) as int].dead,
            !self.table_pages.maps@.contains_key(base),
            self.spaces.roots@[base].addr() == base + 5 * 4096,
            self.spaces.records@.contains_key(base),
            self.spaces.records@[base].addr() == base + 6 * 4096,
            self.spaces.loaded@.contains_key(base),
            self.spaces.loaded@[base].addr() == base + 7 * 4096,
            self.spaces.holders@[base] == Set::<usize>::empty(),
            self.spaces.bound@[base] == Set::<usize>::empty(),
            forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && e.space == base ==> !#[trigger] self.tlb@[c].contains(e),
    {
        let page = (base / 4096) as int;
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
        assert forall|i: usize| i < 512 implies #[trigger] a.entry(base, i).is_empty() by {
            assert(pre.spaces.roots@[base].value()[i].is_empty());
        }
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
            base % 32768 == 0,
            !pre.table_pages.maps@.contains_key(base),
            post.table_pages == pre.table_pages,
            post.spaces.roots@ == pre.spaces.roots@.remove(base),
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p)
                == (pre.list.pages@.dom().contains(p) && !(base <= p < base + TABLE_NODE_PAGES * 4096)),
        ensures
            forall|t: usize, k: usize| #[trigger] post.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
                ==> post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)),
            forall|s: usize, k: usize| #[trigger] post.spaces.roots@.contains_key(s) && k < TABLE_NODE_PAGES
                ==> post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)),
    {
        assert forall|t: usize, k: usize| #[trigger] post.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
            assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
            lemma_node_pages_disjoint(t, base, k);
        }
        assert forall|s: usize, k: usize| #[trigger] post.spaces.roots@.contains_key(s) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
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
            list_pages_used(&post.list, &post.blocks),
    {
        let page = base / 4096;
        pre.lemma_empty_space(base);
        Self::lemma_node_block_list_pages(pre, post, base);
        assert(order_pages(3) == 8);
        assert(pre.blocks.in_block(page as int, page as int));
        Self::lemma_space_freed_node_pages(pre, post, base);
        lemma_table_pages_small_freed(&pre.list, &post.list, &post.table_pages, &pre.blocks, &post.blocks, page);
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_spaces_space_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &post.spaces, &pre.blocks, &post.blocks, base);
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
        Self::lemma_node_block_caps(pre, post, base);
        Self::lemma_space_freed_tree(pre, post, base);
        Self::lemma_space_freed_pages(pre, post, base);
        Self::lemma_node_block_objects(pre, post, base);
        Self::lemma_tlb_space_removed(pre, post, base);
        lemma_ids_space_removed(pre.cores@, pre.spaces.loaded@, post.spaces.loaded@, base);
    }

    /// The block of the empty space at `base` goes back to the block table: its node pages off the list,
    /// and its root, record and list of cores turned back into page permissions.
    pub fn free_empty_space(&mut self, base: usize)
        requires
            old(self).wf(),
            old(self).space_is_empty(base),
            old(self).no_stale_translation(base / 4096),
        ensures
            final(self).wf(),
            final(self).blocks.pages@[(base / 4096) as int].kind is Free,
            !final(self).spaces.roots@.contains_key(base),
            forall|k: usize| k < TABLE_NODE_PAGES ==> !final(self).list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            forall|r: usize, p: SpacePath| #[trigger] walk(tree_of(&final(self).table_pages, &final(self).spaces), r, p)
                == walk(tree_of(&old(self).table_pages, &old(self).spaces), r, p),
            final(self).cores == old(self).cores,
            final(self).view() == old(self).view(),
    {
        let ghost pre = *old(self);
        let page = base / 4096;
        proof {
            pre.lemma_empty_space(base);
            crate::layouts::lemma_space_block_layouts();
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies pre.list.pages@[p].addr() == p by {
                lemma_list_page(&pre.list, p);
            }
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.roots.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.records.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.loaded.borrow().tracked_borrow(base));
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies !(base + 5 * 4096 <= p < base + 8 * 4096) by {
                lemma_list_page(&pre.list, p);
            }
        }
        self.blocks.mark_torn_down(page);
        let ghost mid = *self;
        let Tracked(nodes) = take_table_node_pages(&mut self.list, base);
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
                &&& perms[(page + k) as usize].addr() == (page + k) * 4096
                &&& perms[(page + k) as usize].is_uninit()
            } by {
                if k < 5 {
                    assert(holds_free_page(nodes, (page + k) as usize));
                }
            }
        }
        self.blocks.free_block(page, Tracked(perms));
        proof {
            let post = *self;
            assert forall|i: int| 0 <= i < NUM_PAGES implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            assert(Self::space_freed_step(pre, post, base));
            Self::lemma_space_freed(pre, post, base);
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

    /// What freeing the empty IO space at `base` did to self. Its children and any device went earlier,
    /// so the view is as it was.
    pub open spec fn space_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / 4096;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.space_is_empty(base)
        &&& self.blocks.pages@[page as int].refs == 0
        &&& self.spaces.bound@[base] == Set::<usize>::empty()
        &&& self.no_stale_translation(page)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& !post.spaces.roots@.contains_key(base)
        &&& forall|k: usize| k < TABLE_NODE_PAGES ==> !post.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// Frees the empty IO space at `base`, once every core and IOMMU has acknowledged the epoch of its
    /// block's last unmap. It refuses a block that is anything else, a process space included.
    pub fn free_space(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, 3) && old(self).space_is_empty(base)
                ==> if old(self).acknowledged(base / 4096) { ret is Freed } else { ret is Again },
            ret is Again ==> !old(self).acknowledged(base / 4096),
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
        let page = base / 4096;
        if page >= NUM_PAGES {
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
        match self.space_kind(base) {
            SpaceKind::Process => { return ReclaimStep::Refused; },
            SpaceKind::Io => {},
        }
        if !self.space_nothing_left(base) {
            return ReclaimStep::Refused;
        }
        if !self.is_acknowledged(page) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_acknowledged_is_clean(page);
        }
        self.free_empty_space(base);
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
    pub fn unlink_leaf(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
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
        let page = base / 4096;
        if page >= NUM_PAGES {
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
        self.unlink_arm(base);
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
            Self::lemma_revoke_hidden_holders(pre, post, base);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_unlink_discharges(pre, post, root, untyped, base);
        }
        true
    }

    /// The block test unlink_leaf makes reads as the node does: a table leaf block at one reference
    /// is an owned leaf's whose hidden node is live, and such a leaf's block is a table leaf at one
    /// reference.
    proof fn lemma_live_leaf_block(&self, base: usize)
        requires
            self.wf(),
            base % 8192 == 0,
            base / 4096 < NUM_PAGES,
        ensures
            (leaf_block(&self.blocks, base / 4096) && self.blocks.pages@[(base / 4096) as int].refs == 1)
                == (self.tables.owner@.contains_key(base) && self.list.nodes@[base as int].live),
            self.tables.owner@.contains_key(base) && self.list.nodes@[base as int].live
                ==> self.list.nodes@[base as int].kind is Hidden,
    {
        lemma_leaf_page(base);
        if leaf_block(&self.blocks, base / 4096) {
            assert(self.tables.owner@.contains_key(((base / 4096) * 4096) as usize));
        }
    }

    /// What unlinking a hidden node does to the view: nothing. The node was no capability, and every
    /// capability says what it did under the parent it had, so the step discharges as a teardown from
    /// the retype right alone.
    proof fn lemma_unlink_discharges(pre: Self, post: Self, root: usize, untyped: usize, base: usize)
        requires
            Self::caps_frame(pre, post, base, base),
            base % 4096 == 0,
            post.list.parent == pre.list.parent,
            pre.view().holds_right(root, untyped, Right::Retype),
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
            base % 32768 == 0,
            base / 4096 < NUM_PAGES,
        ensures
            (table_block(&self.blocks, base / 4096) && self.blocks.pages@[(base / 4096) as int].refs == 1)
                == (self.table_pages.maps@.contains_key(base) && self.list.nodes@[base as int].live),
            self.table_pages.maps@.contains_key(base) && self.list.nodes@[base as int].live
                ==> self.list.nodes@[base as int].kind is Hidden,
    {
        assert(base % 32768 == 0 ==> base % 8192 == 0) by (bit_vector);
        lemma_leaf_page(base);
        if table_block(&self.blocks, base / 4096) {
            assert(self.table_pages.maps@.contains_key(((base / 4096) * 4096) as usize));
        }
        if self.table_pages.maps@.contains_key(base) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        }
    }

    /// Unlinks the hidden node of the table page at `base`: cuts it from the entry naming it, records what
    /// that leaves stale, and drops its reference, and nothing more. Refused, with nothing changed, unless
    /// an untyped held covers the block and the block holds a table page with its hidden node still live,
    /// and the epoch can still rise. A process's root is a space block, so it is refused.
    pub fn unlink_table(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
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
        let page = base / 4096;
        if page >= NUM_PAGES || self.flush_epoch == usize::MAX {
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
        self.detach_stale(base);
        let ghost cut = *self;
        proof {
            let b = tree_of(&cut.table_pages, &cut.spaces);
            assert(b.is_page(base));
        }
        self.unlink_arm(base);
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
            Self::lemma_revoke_hidden_holders(cut, post, base);
            Self::lemma_tlb_same(cut, post);
            Self::lemma_unlink_discharges(cut, post, root, untyped, base);
            Self::lemma_cut_recorded_same(pre, cut, post, base);
            Self::lemma_cut_shrunk(pre, cut, base);
            Self::lemma_same_tree_shrunk(cut, post);
            Self::lemma_shrunk_compose(pre, cut, post);
            assert(cut.view() == pre.view());
        }
        true
    }

    /// Child c of a dead table page or IO space is cut: it has no parent and keeps its space, its page is not
    /// acknowledged, its word is above every acknowledgement that stood when the slices began, and its page
    /// is in the TLB of every core that loaded the space and, for an IO space the kernel still holds, of
    /// every IOMMU.
    pub open spec fn child_cut(pre: Self, post: Self, c: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let s = a.record(c).space;
        &&& b.record(c).parent is None
        &&& b.record(c).space == s
        &&& s is Some
        &&& post.stale_epoch.above(pre.flush_epoch as int, c / 4096)
        &&& !post.acknowledged(c / 4096)
        &&& forall|d: int| #![trigger post.tlb@[d].contains(TlbEntry { space: s->Some_0, page: c / 4096 })]
            0 <= d < NUM_CPUS && pre.loaded(d, s->Some_0)
            ==> post.tlb@[d].contains(TlbEntry { space: s->Some_0, page: c / 4096 })
        &&& forall|i: int| #![trigger post.iommus.tlb@[i].contains(TlbEntry { space: s->Some_0, page: c / 4096 })]
            0 <= i < NUM_IOMMUS && pre.iommu_present(i) && a.is_root(s->Some_0) && pre.spaces.records@[s->Some_0].value().kind is Io
            ==> post.iommus.tlb@[i].contains(TlbEntry { space: s->Some_0, page: c / 4096 })
    }

    /// What cutting children of the dead table at `base` keeps: only tables, the record of each cut and the
    /// TLBs changed. A table page's cuts leave every walk finding what it did, since no walk reaches it, and
    /// a root's end the walks through its entries. Each entry that stopped naming a child is empty and its
    /// child is cut.
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
        &&& Self::mappings_shrunk(pre, post)
        &&& forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] pre.core_may_hold(c, e) ==> post.core_may_hold(c, e)
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

    /// What cutting children of the dead table page at `base` did to self: it cut at least one and no more
    /// than the budget, each taking one entry off the count, and every capability is as it was.
    pub open spec fn table_children_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let a = child_entries(tree_of(&self.table_pages, &self.spaces), base);
        let b = child_entries(tree_of(&post.table_pages, &post.spaces), base);
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& Self::table_cuts_kept(*self, post, base)
        &&& b.subset_of(a)
        &&& b.len() < a.len()
        &&& a.len() - b.len() <= TABLE_SLICE_BUDGET
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// The block test slice_table makes reads as the table page does.
    pub proof fn lemma_dead_table_block(&self, base: usize)
        requires
            self.wf(),
            base % 32768 == 0,
            base / 4096 < NUM_PAGES,
        ensures
            (table_block(&self.blocks, base / 4096) && self.blocks.pages@[(base / 4096) as int].refs == 0)
                == (self.table_pages.maps@.contains_key(base) && !self.list.nodes@[base as int].live),
            self.table_pages.maps@.contains_key(base) ==> !self.spaces.roots@.contains_key(base),
            self.table_pages.maps@.contains_key(base) && !self.list.nodes@[base as int].live
                ==> self.table_pages.records@[base].value().parent is None,
    {
        assert(base % 32768 == 0 ==> base % 8192 == 0) by (bit_vector);
        lemma_leaf_page(base);
        if table_block(&self.blocks, base / 4096) {
            assert(self.table_pages.maps@.contains_key(((base / 4096) * 4096) as usize));
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
            tree_of(&self.table_pages, &self.spaces).entry(t, e).addr >= TABLE_NODE_PAGES * 4096,
            self.table_pages.maps@.contains_key(child_at(tree_of(&self.table_pages, &self.spaces), t, e)),
            tree_of(&self.table_pages, &self.spaces).record(child_at(tree_of(&self.table_pages, &self.spaces), t, e)).parent
                == Some(TableParent { table: t, entry: e }),
            tree_of(&self.table_pages, &self.spaces).record(child_at(tree_of(&self.table_pages, &self.spaces), t, e)).space is Some,
            child_at(tree_of(&self.table_pages, &self.spaces), t, e) / 4096 < NUM_PAGES,
            child_at(tree_of(&self.table_pages, &self.spaces), t, e) % 32768 == 0,
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
        assert forall|i: usize| #[trigger] child_entries(b, base).contains(i) == child_entries(m, base).remove(e).contains(i) by {
            lemma_child_entries(b, base, i);
            lemma_child_entries(m, base, i);
            assert(b.child_slot(base, i) == m.child_slot(base, i));
            if i != e {
                if i < 512 {
                    assert(b.entry(base, i) == m.entry(base, i));
                } else {
                    assert(!b.names_child(base, i) && !m.names_child(base, i));
                }
            }
        }
        assert(child_entries(b, base) =~= child_entries(m, base).remove(e));
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
            c / 4096 < NUM_PAGES,
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
        let g = c / 4096;
        lemma_cut_pages(m, c, g);
        assert(cut_pages(m, c).contains(g));
        assert forall|d: int| #![trigger post.tlb@[d].contains(TlbEntry { space: s, page: g })]
            0 <= d < NUM_CPUS && pre.loaded(d, s) implies post.tlb@[d].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.loaded(d, s));
        }
        assert forall|i: int| #![trigger post.iommus.tlb@[i].contains(TlbEntry { space: s, page: g })]
            0 <= i < NUM_IOMMUS && pre.iommu_present(i) && tree_of(&pre.table_pages, &pre.spaces).is_root(s) && pre.spaces.records@[s].value().kind is Io
            implies post.iommus.tlb@[i].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.spaces.records@[s].value().kind is Io);
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
        let g = old_child / 4096;
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
            0 <= d < NUM_CPUS && pre.loaded(d, s) implies post.tlb@[d].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.tlb@[d].contains(TlbEntry { space: s, page: g }));
        }
        assert forall|j: int| #![trigger post.iommus.tlb@[j].contains(TlbEntry { space: s, page: g })]
            0 <= j < NUM_IOMMUS && pre.iommu_present(j) && a.is_root(s) && pre.spaces.records@[s].value().kind is Io
            implies post.iommus.tlb@[j].contains(TlbEntry { space: s, page: g }) by {
            assert(mid.iommus.tlb@[j].contains(TlbEntry { space: s, page: g }));
        }
    }

    /// Cuts up to a budget of the child tables of the dead table page at `base`, under the untyped at index
    /// `from` of the table at `root`, each from the entry naming it, with what that leaves stale. A cut
    /// entry stays empty, since can_link refuses a dead parent and no walk reaches a table with no parent,
    /// so the next slice can start again from the first entry. Returns whether it ran, and if not nothing
    /// changed.
    pub fn cut_table_children(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
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
        let page = base / 4096;
        if page >= NUM_PAGES || self.flush_epoch == usize::MAX {
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
        let steps = self.cut_children(base, false);
        proof {
            if steps != 0 {
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
            }
        }
        steps != 0
    }

    /// Cuts up to a budget of the children of the table at `base`, a table page or an IO space's root with
    /// no parent, each from the entry naming it, with what that leaves stale, and returns how many. A slice
    /// starts again from the first entry, since a cut entry stays empty.
    fn cut_children(&mut self, base: usize, is_root: bool) -> (steps: usize)
        requires
            old(self).wf(),
            old(self).flush_epoch < usize::MAX,
            tree_of(&old(self).table_pages, &old(self).spaces).is_table(base),
            is_root == tree_of(&old(self).table_pages, &old(self).spaces).is_root(base),
            is_root != tree_of(&old(self).table_pages, &old(self).spaces).is_page(base),
            is_root ==> old(self).spaces.records@[base].value().kind is Io,
            tree_of(&old(self).table_pages, &old(self).spaces).record(base).parent is None,
            tree_of(&old(self).table_pages, &old(self).spaces).record(base).level >= 2,
        ensures
            final(self).wf(),
            steps <= TABLE_SLICE_BUDGET,
            Self::table_cuts_kept(*old(self), *final(self), base),
            child_entries(tree_of(&final(self).table_pages, &final(self).spaces), base)
                .subset_of(child_entries(tree_of(&old(self).table_pages, &old(self).spaces), base)),
            child_entries(tree_of(&old(self).table_pages, &old(self).spaces), base).len()
                == child_entries(tree_of(&final(self).table_pages, &final(self).spaces), base).len() + steps,
            steps == 0 ==> *final(self) == *old(self),
            steps == 0 ==> forall|j: usize| !#[trigger] tree_of(&old(self).table_pages, &old(self).spaces).names_child(base, j),
            steps > 0 ==> exists|i: usize| #[trigger] tree_of(&old(self).table_pages, &old(self).spaces).names_child(base, i),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let mut steps: usize = 0;
        let mut e: usize = 0;
        while steps != TABLE_SLICE_BUDGET && e != 512 && self.flush_epoch != usize::MAX
            invariant
                self.wf(),
                pre == *old(self),
                pre.wf(),
                a == tree_of(&pre.table_pages, &pre.spaces),
                a.is_table(base),
                is_root == a.is_root(base),
                is_root != a.is_page(base),
                is_root ==> a.space_records[base].value().kind is Io,
                pre.flush_epoch < usize::MAX,
                a.record(base).level >= 2,
                steps <= TABLE_SLICE_BUDGET,
                e <= 512,
                Self::table_cuts_kept(pre, *self, base),
                steps == 0 ==> *self == pre,
                steps > 0 ==> exists|i: usize| #[trigger] a.names_child(base, i),
                child_entries(tree_of(&self.table_pages, &self.spaces), base).subset_of(child_entries(a, base)),
                child_entries(a, base).len() == child_entries(tree_of(&self.table_pages, &self.spaces), base).len() + steps,
                forall|j: usize| j < e ==> !#[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, j),
            decreases TABLE_SLICE_BUDGET - steps, 512 - e,
        {
            let ghost mid = *self;
            let ghost m = tree_of(&self.table_pages, &self.spaces);
            let entry = self.table_entry(base, is_root, e);
            let names = entry.perm.present && !entry.perm.ps;
            proof {
                assert(m.is_root(base) == is_root);
                assert(m.is_page(base) != is_root);
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
            let child = entry.addr - TABLE_NODE_PAGES * 4096;
            proof {
                assert(child == child_at(m, base, e));
            }
            self.detach_stale(child);
            proof {
                let post = *self;
                let b = tree_of(&post.table_pages, &post.spaces);
                Self::lemma_table_cut_step(pre, mid, post, base, e);
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
                if steps == 0 {
                    assert(mid == pre);
                    assert(a.names_child(base, e));
                } else {
                    assert(exists|i: usize| #[trigger] a.names_child(base, i));
                }
            }
            steps = steps + 1;
            e = e + 1;
        }
        proof {
            if steps == 0 {
                assert(*self == pre);
                assert(e == 512);
                assert forall|j: usize| !#[trigger] a.names_child(base, j) by {
                    if j < 512 {
                        assert(!tree_of(&self.table_pages, &self.spaces).names_child(base, j));
                    }
                }
            }
        }
        steps
    }

    /// A dead IO space's block: nothing names the space and no device is bound to it. A process space goes
    /// with its process.
    pub open spec fn dead_io_space(&self, base: usize) -> bool {
        &&& self.spaces.roots@.contains_key(base)
        &&& self.spaces.records@[base].value().kind is Io
        &&& self.blocks.pages@[(base / 4096) as int].refs == 0
    }

    /// The IO space at `base` has a child to cut: an untyped covers it, it is dead, an entry still names a
    /// child and the flush epoch can rise.
    pub open spec fn can_cut_space(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 3)
        &&& self.dead_io_space(base)
        &&& exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
        &&& self.flush_epoch < usize::MAX
    }

    /// What cutting children of the dead IO space at `base` did to self: as for a table page, and the space
    /// is still there and still dead.
    pub open spec fn space_children_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        &&& self.table_children_cut(post, root, from, base)
        &&& post.dead_io_space(base)
    }

    /// Cuts up to a budget of the child tables of the dead IO space at `base`, under the untyped at index
    /// `from` of the table at `root`, each from the entry naming it, with what that leaves stale. Returns
    /// whether it ran, and if not nothing changed.
    pub fn cut_space_children(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
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
        let page = base / 4096;
        if page >= NUM_PAGES || self.flush_epoch == usize::MAX {
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
        match self.space_kind(base) {
            SpaceKind::Process => { return false; },
            SpaceKind::Io => {},
        }
        let steps = self.cut_children(base, true);
        proof {
            if steps != 0 {
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
            }
        }
        steps != 0
    }

    /// A block that holds a space is that space's: a space's block is Base and Space, and its root has no
    /// parent, is level 4 and is no table page.
    proof fn lemma_space_block(&self, base: usize)
        requires
            self.wf(),
            base % 32768 == 0,
            base / 4096 < NUM_PAGES,
        ensures
            space_block(&self.blocks, base / 4096) == self.spaces.roots@.contains_key(base),
            self.spaces.roots@.contains_key(base) ==> !self.table_pages.maps@.contains_key(base),
            self.spaces.roots@.contains_key(base) ==> tree_of(&self.table_pages, &self.spaces).record(base).parent is None,
            self.spaces.roots@.contains_key(base) ==> tree_of(&self.table_pages, &self.spaces).record(base).level == 4,
    {
        assert(base % 32768 == 0 ==> base % 8192 == 0) by (bit_vector);
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

    /// A step that takes a mapping node away leaves the view as it was: the node was no capability, and
    /// every capability says what it did under the parent it had.
    proof fn lemma_mapping_view_same(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            pre.list.nodes@[n as int].kind is Mapping,
            !post.list.nodes@[n as int].live,
            post.list.parent == pre.list.parent,
        ensures
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            post.view() == pre.view(),
    {
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
        assert(b == a);
    }

    /// Unlinks mapping node n with its entry and its frame's reference, and records the unmap.
    fn unlink_mapping_node(&mut self, n: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            old(self).list.nodes@[n as int].kind is Mapping,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(self).wf(),
            Self::mapping_unlinked(*old(self), *final(self), n),
            Self::mapping_stale_noted(*old(self), *final(self), n),
            Self::caps_frame(*old(self), *final(self), n, n),
            !final(self).list.nodes@[n as int].live,
            final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            forall|x: int| 0 <= x < NODE_SPACE && x != n ==> #[trigger] final(self).list.nodes@[x].live == old(self).list.nodes@[x].live,
            final(self).list.parent == old(self).list.parent,
            final(self).tables == old(self).tables,
            final(self).spaces == old(self).spaces,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).table_pages.records == old(self).table_pages.records,
            final(self).table_pages.spare == old(self).table_pages.spare,
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_mapping_is_leaf(n);
        }
        self.unlink_arm(n);
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
            Self::lemma_revoke_mapping_holders(pre, post, n);
            Self::lemma_stale_noted_same(pre, mid, post, n);
            Self::lemma_tlb_same(mid, post);
        }
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
            forall|i: usize| i < 512 && i != e ==> #[trigger] tree_of(&post.table_pages, &post.spaces).entry(base, i) == tree_of(&mid.table_pages, &mid.spaces).entry(base, i),
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
            assert(e < 512);
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
            forall|i: usize| i < 512 && i != e ==> #[trigger] tree_of(&post.table_pages, &post.spaces).entry(base, i) == tree_of(&mid.table_pages, &mid.spaces).entry(base, i),
            tree_of(&post.table_pages, &post.spaces).entry(base, e).is_empty(),
    {
        reveal(entries_cleared);
        let (m, b) = (tree_of(&mid.table_pages, &mid.spaces), tree_of(&post.table_pages, &post.spaces));
        assert forall|i: usize| i < 512 && i != e implies #[trigger] b.entry(base, i) == m.entry(base, i) by {}
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
    pub fn unlink_table_mappings(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
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
        let page = base / 4096;
        if page >= NUM_PAGES || self.flush_epoch == usize::MAX {
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
        let mut steps: usize = 0;
        let mut e: usize = 0;
        while steps != TABLE_SLICE_BUDGET && e != 512 && self.flush_epoch != usize::MAX
            invariant
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
                base % 32768 == 0,
                base / 4096 < NUM_PAGES,
                level == a.record(base).level,
                steps <= TABLE_SLICE_BUDGET,
                e <= 512,
                nodes.len() == steps,
                Self::table_unmaps_kept(pre, *self, base, steps as int),
                Self::table_mapping_steps(pre, *self, base, nodes, states),
                steps == 0 ==> *self == pre,
                steps > 0 ==> exists|i: usize| #[trigger] frame_slot(a, base, i),
                forall|j: usize| j < e ==> !#[trigger] frame_slot(tree_of(&self.table_pages, &self.spaces), base, j),
            decreases TABLE_SLICE_BUDGET - steps, 512 - e,
        {
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
            let n = base + ((e + 1) / NODES_PER_PAGE) * 4096 + (e + 1) % NODES_PER_PAGE;
            proof {
                assert(n == mapping_node(base, e));
                assert(mid.mappings@.contains_key(n));
                mid.lemma_mapping_node(n);
            }
            self.unlink_mapping_node(n);
            proof {
                let post = *self;
                let b = tree_of(&post.table_pages, &post.spaces);
                Self::lemma_table_unmap_step(pre, mid, post, base, e, n, steps as int);
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
                        if j < 512 {
                            assert(b.entry(base, j) == m.entry(base, j));
                        }
                        assert(!frame_slot(m, base, j));
                    } else {
                        assert(!b.entry(base, e).perm.present);
                    }
                }
                if steps == 0 {
                    assert(mid == pre);
                    assert(frame_slot(a, base, e));
                }
            }
            steps = steps + 1;
            e = e + 1;
        }
        proof {
            if steps == 0 {
                assert(*self == pre);
                assert(e == 512);
                assert forall|j: usize| !#[trigger] frame_slot(a, base, j) by {
                    if j < 512 {
                        assert(!frame_slot(tree_of(&self.table_pages, &self.spaces), base, j));
                    }
                }
            } else {
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
                assert(Self::table_mapping_steps(pre, *self, base, nodes, states));
            }
        }
        steps != 0
    }

    /// Takes a slice of the dead table page at `base`, under the untyped at index `from` of the table at
    /// `root`: the entries naming child tables go first, then the entries mapping frames. Returns whether
    /// it ran, and if not nothing changed.
    pub fn slice_table(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_slice_table(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).table_sliced(*final(self), root, from, base),
    {
        if self.cut_table_children(root, from, base) {
            return true;
        }
        self.unlink_table_mappings(root, from, base)
    }

    /// Reclaims the 4K block at `base`, under the untyped at index `from` of the table at `root`. All of
    /// these come from user space, and anything but a free changes nothing.
    pub fn reclaim_frame(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 0) && old(self).frame_is_dead(base / 4096)) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / 4096),
            ret is Freed ==> old(self).frame_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        let untyped = match self.retype_parent(root, from, base, 0) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / 4096;
        if page >= NUM_PAGES {
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
        if !self.is_acknowledged(page) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_dead_frame_unmapped(page);
            pre.lemma_acknowledged_is_clean(page);
        }
        self.free_frame(c, page);
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

    /// Reclaims the 2M or 1G block at `base`, as reclaim_frame does a 4K one.
    pub fn reclaim_large_frame(&mut self, c: usize, root: usize, from: usize, base: usize, order: u8) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Freed) ==> *final(self) == *old(self),
            !old(self).can_retype_under(root, from, base, order) ==> ret is Refused,
            ret is Again ==> {
                let level = if order == 9 { Large::Two } else { Large::One };
                !old(self).region_acknowledged(level, base / 4096 / level_pages(level))
            },
            ret is Freed ==> {
                let untyped = old(self).tables.node_of(root, from);
                let level = if order == 9 { Large::Two } else { Large::One };
                let r = base / 4096 / level_pages(level);
                &&& order == 9 || order == 18
                &&& r < level_regions(level)
                &&& old(self).view().holds_right(root, untyped, Right::Retype)
                &&& old(self).region_is_dead(level, r)
                &&& old(self).region_clean(level, r)
                &&& !block_typed(&final(self).blocks, level_ref(level, r))
                &&& forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> !final(self).frames@.contains_key(i)
                &&& Self::step_ok(*old(self), *final(self), c as int)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Teardown { untyped, object: base })
            },
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
        let page = base / 4096;
        if !self.is_region_acknowledged(level, r) {
            return ReclaimStep::Again;
        }
        proof {
            assert(pre.holders@.contains_key(level_ref(level, r)));
            assert(block_refs(&pre.blocks, level_ref(level, r)) == 0);
            pre.lemma_dead_region_unmapped(level, r);
            pre.lemma_region_acknowledged_is_clean(level, r);
        }
        self.free_large(c, level, r);
        proof {
            let post = *self;
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
            !block_typed(&final(self).blocks, level_ref(level, r)),
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
            assert forall|i: usize| #[trigger] post.frames@.contains_key(i) implies post.frames@[i].addr() == i * 4096 by {
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
    fn free_frame(&mut self, c: usize, page: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).frame_is_dead(page),
            old(self).no_stale_translation(page),
        ensures
            Self::same_tree(*old(self), *final(self)),
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
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
            assert(perm.addr() == page * 4096);
        }
        let tracked mut perms = Map::<usize, PagePerm4k>::tracked_empty();
        proof {
            perms.tracked_insert(page, perm);
            assert(pre.blocks.pages@[page as int].order == 0);
        }
        self.blocks.free_block(page, Tracked(perms));
        self.holders = Ghost(pre.holders@.remove(BlockRef::Small(page)));
        proof {
            let post = *self;
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
                implies !pre.blocks.in_block(page as int, (p / 4096) as int) by {
                if pre.blocks.in_block(page as int, (p / 4096) as int) {
                    assert((p / 4096) as int == page as int);
                }
            }
            Self::lemma_small_freed(pre, post, page);
        }
    }
}

} // verus!
