//! Retype reclaiming memory. There is no kernel list of dead objects, and no revoke or delete drains
//! another's teardown: a retype naming a block, by a holder of an untyped covering it, does the work.
//! See the design on atmo-6x9.6.7, section 6.
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

/// What a reclaim did.
pub enum ReclaimStep {
    /// Nothing changed: the caller may not name this block, or a capability still does.
    Refused,
    /// Nothing changed: a core may still hold a translation to it. Retype again later, since nothing
    /// waits under the lock.
    Again,
    /// The block is free.
    Freed,
    /// The block held a table leaf whose hidden node is now gone, so it is dead, and its dismantling
    /// starts on a later retype.
    Unlinked,
    /// Some of a dead leaf's capabilities went, and more may remain. Retype again.
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
        &&& post.blocks.pages@[page as int].kind is Free
        &&& post.blocks.pages@[page + 1int].kind is Free
        &&& !post.tables.owner@.contains_key(base)
        &&& !post.list.pages@.dom().contains(base)
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// A retype naming the block at `base`, under the untyped at index `from` of the table at `root`:
    /// what it does depends on what the block holds. All of these come from user space.
    pub fn reclaim(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            !old(self).mapped@.contains(base / 4096),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused || ret is Again ==> *final(self) == *old(self),
            !((old(self).can_retype_under(root, from, base, 0) && old(self).frame_is_dead(base / 4096))
                || old(self).can_unlink_leaf(root, from, base)
                || (old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base))
                || old(self).can_slice_leaf(root, from, base)) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / 4096),
            ret is Freed ==> old(self).frame_freed(*final(self), c, root, from, base)
                || old(self).leaf_freed(*final(self), c, root, from, base),
            ret is Slice ==> old(self).leaf_sliced(*final(self), root, from, base),
            ret is Unlinked ==> old(self).leaf_unlinked(*final(self), root, from, base),
    {
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
            ObjectType::None | ObjectType::TablePage | ObjectType::Space => ReclaimStep::Refused,
        }
    }

    /// A retype may take a slice of the leaf at `base`: an untyped covers its block, its hidden node has
    /// gone, and a slot is still live.
    pub open spec fn can_slice_leaf(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 1)
        &&& self.tables.owner@.contains_key(base)
        &&& !self.list.nodes@[base as int].live
        &&& !self.leaf_is_empty(base)
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
        while steps != LEAF_SLICE_BUDGET && k != NODES_PER_PAGE
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
                steps > 0 ==> !pre.leaf_is_empty(base),
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
            !old(self).mapped@.contains(base / 4096),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 1) && old(self).leaf_is_empty(base)) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / 4096),
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
        if !self.is_acknowledged(page) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_acknowledged_is_clean(page);
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
            !old(self).mapped@.contains(base / 4096),
            old(self).no_stale_translation(base / 4096),
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

    /// Reclaims the 4K block at `base`, under the untyped at index `from` of the table at `root`. All of
    /// these come from user space, and anything but a free changes nothing. That the frame is unmapped
    /// is atmo-6x9.16.8's to discharge, from its mapping nodes.
    pub fn reclaim_frame(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            !old(self).mapped@.contains(base / 4096),
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
            !old(self).mapped@.contains(base / 4096),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            !(ret is Freed) ==> *final(self) == *old(self),
            !old(self).can_retype_under(root, from, base, order) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / 4096),
            ret is Freed ==> {
                let untyped = old(self).tables.node_of(root, from);
                let level = if order == 9 { Large::Two } else { Large::One };
                let r = base / 4096 / level_pages(level);
                &&& order == 9 || order == 18
                &&& r < level_regions(level)
                &&& old(self).view().holds_right(root, untyped, Right::Retype)
                &&& old(self).region_is_dead(level, r)
                &&& old(self).no_stale_translation(base / 4096)
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
        if !self.is_acknowledged(page) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_acknowledged_is_clean(page);
            assert(pre.holders@.contains_key(level_ref(level, r)));
            assert(block_refs(&pre.blocks, level_ref(level, r)) == 0);
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
            !old(self).mapped@.contains(level_base(level, r)),
            old(self).no_stale_translation(level_base(level, r)),
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
            !old(self).mapped@.contains(page),
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
