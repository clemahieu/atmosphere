//! Retype reclaiming memory. There is no kernel list of dead objects, and no revoke or delete drains
//! another's teardown: a retype naming a block, by a holder of an untyped covering it, does the work.
//! See the design on atmo-6x9.6.7, section 6.
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::table::*;
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
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 0) && old(self).frame_is_dead(base / 4096)) ==> ret is Refused,
            ret is Again ==> !old(self).acknowledged(base / 4096),
            ret is Freed ==> {
                let untyped = old(self).tables.node_of(root, from);
                let page = base / 4096;
                &&& old(self).view().holds_right(root, untyped, Right::Retype)
                &&& old(self).frame_is_dead(page)
                &&& old(self).no_stale_translation(page)
                &&& final(self).blocks.pages@[page as int].kind is Free
                &&& !final(self).frames@.contains_key(page)
                &&& Self::step_ok(*old(self), *final(self), c as int)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Teardown { untyped, object: base })
            },
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
