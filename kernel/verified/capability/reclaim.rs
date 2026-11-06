//! Retype reclaiming memory. There is no kernel list of dead objects, and no revoke or delete drains
//! another's teardown: a retype naming a block, by a holder of an untyped covering it, does the work.
//! See the design on atmo-6x9.6.7, section 6.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
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
            ret is Refused || ret is Again ==> *final(self) == *old(self),
            !((old(self).can_retype_under(root, from, base, 0) && old(self).frame_is_dead(base / 4096))
                || old(self).can_unlink_leaf(root, from, base)) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / 4096),
            ret is Freed ==> old(self).frame_freed(*final(self), c, root, from, base),
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
                } else {
                    ReclaimStep::Refused
                }
            },
            ObjectType::None => ReclaimStep::Refused,
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
            !(ret is Unlinked),
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
