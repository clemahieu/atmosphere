// SPDX-License-Identifier: MIT

//! Retype reclaiming a dead endpoint's, notification's or reply's block. Once its references are gone
//! nothing names it, its page is no frame and no table so no core or IOMMU can hold a translation of
//! it, and so one retype frees its block at once, its record going with it. See
//! design/teardown-driven-by-retype/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::endpoint::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reply::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::reclaim::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
use crate::capability::steps::Steps;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::layouts::*;
use crate::capability::list::NONE;
use crate::pptr::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;

impl CapKernel {
    /// A dead endpoint or notification at zero references whose queue lists no thread: the block to be
    /// freed. A thread its queue still lists keeps its record, since nothing takes a thread off a queue
    /// yet (design/ipc-with-reply-object/).
    pub open spec fn queue_is_dead(&self, page: usize) -> bool {
        &&& self.blocks.tracks(page as int)
        &&& self.blocks.pages@[page as int].kind is Base
        &&& queue_object(self.blocks.pages@[page as int].object)
        &&& self.blocks.pages@[page as int].dead
        &&& self.blocks.pages@[page as int].refs == 0
        &&& self.endpoints.records@[(page * PAGE_SZ) as usize].value().waiters@.len() == 0
    }

    /// A dead reply at zero references.
    pub open spec fn reply_is_dead(&self, page: usize) -> bool {
        &&& self.blocks.tracks(page as int)
        &&& self.blocks.pages@[page as int].kind is Base
        &&& self.blocks.pages@[page as int].object is Reply
        &&& self.blocks.pages@[page as int].dead
        &&& self.blocks.pages@[page as int].refs == 0
    }

    /// What freeing a block holding no frame, at page `page`, kept of self: everything but the block
    /// table's entries for that page and the store of the object it held.
    pub open spec fn object_block_freed(&self, post: Self, c: usize, page: usize) -> bool {
        &&& post.blocks.pages@[page as int].kind is Free
        &&& post.blocks.small_free(page as int, 0)
        &&& post.frames@ == self.frames@
        &&& post.list == self.list
        &&& post.tables == self.tables
        &&& post.devices == self.devices
        &&& post.threads == self.threads
        &&& post.processes == self.processes
        &&& post.spaces == self.spaces
        &&& post.table_pages == self.table_pages
        &&& post.zeroing == self.zeroing
        &&& post.stale_epoch == self.stale_epoch
        &&& post.flush_epoch == self.flush_epoch
        &&& post.cores == self.cores
        &&& post.iommus == self.iommus
        &&& post.blocks.regions_2m@ == self.blocks.regions_2m@
        &&& post.blocks.regions_1g@ == self.blocks.regions_1g@
        &&& forall|i: int| self.blocks.tracks(i) && i != page ==> #[trigger] post.blocks.pages@[i] == self.blocks.pages@[i]
        &&& Self::same_tree(*self, post)
        &&& Self::step_ok(*self, post, c as int)
    }

    /// What freeing the endpoint or notification at `base` did to self, under the untyped at index
    /// `from` of the table at `root`: its page is free in the block table and its record is gone, and
    /// the rest is as it was, so the next retype of the page can succeed and what a caller knew of
    /// another block holds after the free. The state the reach theorem reads is unchanged.
    pub open spec fn queue_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.queue_is_dead(page)
        &&& self.object_block_freed(post, c, page)
        &&& post.endpoints.records@ == self.endpoints.records@.remove(base)
        &&& post.endpoints.holders == self.endpoints.holders
        &&& post.replies == self.replies
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, block: base, pages: 1, object: base })
    }

    /// The same for the reply at `base`.
    pub open spec fn reply_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.reply_is_dead(page)
        &&& self.object_block_freed(post, c, page)
        &&& post.replies.records@ == self.replies.records@.remove(base)
        &&& post.replies.holders == self.replies.holders
        &&& post.endpoints == self.endpoints
        &&& post.view() == self.view()
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, block: base, pages: 1, object: base })
    }

    /// A block typed as an endpoint, a notification or a reply holds no leaf, table page, space, thread
    /// or process.
    pub proof fn lemma_ipc_object(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.blocks.tracks_addr(base) && ({
                let o = self.blocks.pages@[(base / PAGE_SZ) as int].object;
                o is Endpoint || o is Notification || o is Reply
            }) ==> {
                &&& !self.tables.owner@.contains_key(base)
                &&& !self.table_pages.maps@.contains_key(base)
                &&& !self.spaces.roots@.contains_key(base)
                &&& !self.threads.records@.contains_key(base)
                &&& !self.processes.records@.contains_key(base)
            },
    {
        self.lemma_thread_object(base);
        self.lemma_process_object(base);
        if self.blocks.tracks_addr(base) {
            if self.tables.owner@.contains_key(base) {
                self.tables.lemma_leaf(&self.list, base);
            }
            if self.table_pages.maps@.contains_key(base) {
                assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
            }
            if self.spaces.roots@.contains_key(base) {
                assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
            }
        }
    }

    /// Frees the block of the dead endpoint or notification at `page`, its record's page going back.
    fn free_queue(&mut self, c: usize, page: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).queue_is_dead(page),
        ensures
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            old(self).object_block_freed(*final(self), c, page),
            final(self).endpoints.records@ == old(self).endpoints.records@.remove((page * PAGE_SZ) as usize),
            final(self).endpoints.holders == old(self).endpoints.holders,
            final(self).replies == old(self).replies,
    {
        let ghost pre = *old(self);
        let ghost e = (page * PAGE_SZ) as usize;
        proof {
            pre.blocks.lemma_not_free_uncovered(page as int);
            pre.lemma_untranslatable_clean(page);
            assert(endpoint_block(&pre.blocks, page));
            assert(pre.endpoints.records@.contains_key(e));
            assert(endpoint_wf(&pre.endpoints, &pre.blocks, e));
        }
        self.blocks.mark_torn_down(page);
        let tracked mut perm;
        proof {
            let tracked mut record = self.endpoints.records.borrow_mut().tracked_remove(e);
            record.leak_contents();
            perm = queue_record_into_page(record);
            assert(perm.addr() == page * PAGE_SZ);
            // The record's page is no page of the list: two permissions never share an address.
            crate::layouts::lemma_table_block_layouts();
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies pre.list.pages@[p].addr() == p by {
                lemma_list_page(&pre.list, p);
            }
            lemma_list_page_apart(self.list.pages.borrow_mut(), &perm);
            assert(!pre.list.pages@.dom().contains(e));
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
            assert(post.endpoints.records@ =~= pre.endpoints.records@.remove(e));
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                implies !pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) by {
                if pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) {
                    assert((p / PAGE_SZ) as int == page as int);
                    lemma_list_page(&pre.list, p);
                    lemma_fundamental_div_mod(p as int, PAGE_SZ as int);
                    assert(p == e);
                }
            }
            Self::lemma_small_freed(pre, post, page);
            assert(!post.blocks.covered(page as int));
            assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] post.blocks.pages@[page + k].kind is Free by {
                assert(k == 0);
            }
        }
    }

    /// Frees the block of the dead reply at `page`, its record's page going back.
    fn free_reply(&mut self, c: usize, page: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).reply_is_dead(page),
        ensures
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            old(self).object_block_freed(*final(self), c, page),
            final(self).replies.records@ == old(self).replies.records@.remove((page * PAGE_SZ) as usize),
            final(self).replies.holders == old(self).replies.holders,
            final(self).endpoints == old(self).endpoints,
    {
        let ghost pre = *old(self);
        let ghost e = (page * PAGE_SZ) as usize;
        proof {
            pre.blocks.lemma_not_free_uncovered(page as int);
            pre.lemma_untranslatable_clean(page);
            assert(reply_block(&pre.blocks, page));
            assert(pre.replies.records@.contains_key(e));
            assert(reply_wf(&pre.replies, &pre.blocks, e));
        }
        self.blocks.mark_torn_down(page);
        let tracked mut perm;
        proof {
            let tracked mut record = self.replies.records.borrow_mut().tracked_remove(e);
            record.leak_contents();
            perm = reply_record_into_page(record);
            assert(perm.addr() == page * PAGE_SZ);
            // The record's page is no page of the list: two permissions never share an address.
            crate::layouts::lemma_table_block_layouts();
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies pre.list.pages@[p].addr() == p by {
                lemma_list_page(&pre.list, p);
            }
            lemma_list_page_apart(self.list.pages.borrow_mut(), &perm);
            assert(!pre.list.pages@.dom().contains(e));
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
            assert(post.replies.records@ =~= pre.replies.records@.remove(e));
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                implies !pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) by {
                if pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) {
                    assert((p / PAGE_SZ) as int == page as int);
                    lemma_list_page(&pre.list, p);
                    lemma_fundamental_div_mod(p as int, PAGE_SZ as int);
                    assert(p == e);
                }
            }
            Self::lemma_small_freed(pre, post, page);
            assert(!post.blocks.covered(page as int));
            assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] post.blocks.pages@[page + k].kind is Free by {
                assert(k == 0);
            }
        }
    }

    /// A retype naming the block of the endpoint or notification at `base`, under the untyped at index
    /// `from` of the table at `root`: once its references are gone and its queue lists no thread, it
    /// frees the block. All of these come from user space, and anything but a free changes nothing.
    pub(crate) fn reclaim_queue(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused || ret is Freed,
            ret is Refused ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 0) && old(self).queue_is_dead(base / PAGE_SZ)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, 0) && old(self).queue_is_dead(base / PAGE_SZ) ==> ret is Freed,
            ret is Freed ==> old(self).queue_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, 0) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let dead = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Endpoint) | (PageKind::Base, ObjectType::Notification) => entry.refs == 0,
            _ => false,
        };
        if !dead {
            return ReclaimStep::Refused;
        }
        proof {
            lemma2_to64();
            assert(base % PAGE_SZ == 0);
            lemma_fundamental_div_mod(base as int, PAGE_SZ as int);
            assert((page * PAGE_SZ) as usize == base);
            assert(endpoint_block(&pre.blocks, page));
            assert(endpoint_wf(&pre.endpoints, &pre.blocks, base));
            assert forall|t: usize| #[trigger] pre.threads.records@.contains_key(t) implies t != NONE by {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
            }
            lemma_waits_head(pre.endpoints.records@, pre.threads.records@, base);
        }
        // A thread the queue lists keeps the endpoint until it is taken off.
        let head = PPtr::<QueueRecord>::from_usize(base).borrow(Tracked(self.endpoints.records.borrow().tracked_borrow(base))).head;
        if head != NONE {
            return ReclaimStep::Refused;
        }
        self.free_queue(c, page, Tracked(steps));
        proof {
            let post = *self;
            Self::lemma_same_tree_shrunk(pre, post);
            pre.lemma_retype_covers(root, from, base, 0);
            assert(authorized(pre.view(), root, Effect::Teardown { untyped, block: base, pages: 1, object: base }));
            assert(post.view() == pre.view());
            lemma_no_change_discharges_teardown(pre.view(), root, untyped, base, 1, base);
        }
        ReclaimStep::Freed
    }

    /// The same for the block of the reply at `base`.
    pub(crate) fn reclaim_reply(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused || ret is Freed,
            ret is Refused ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, 0) && old(self).reply_is_dead(base / PAGE_SZ)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, 0) && old(self).reply_is_dead(base / PAGE_SZ) ==> ret is Freed,
            ret is Freed ==> old(self).reply_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, 0) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let dead = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Reply) => entry.refs == 0,
            _ => false,
        };
        if !dead {
            return ReclaimStep::Refused;
        }
        proof {
            lemma2_to64();
            assert(base % PAGE_SZ == 0);
            lemma_fundamental_div_mod(base as int, PAGE_SZ as int);
            assert((page * PAGE_SZ) as usize == base);
            assert(reply_block(&pre.blocks, page));
            assert(reply_wf(&pre.replies, &pre.blocks, base));
        }
        self.free_reply(c, page, Tracked(steps));
        proof {
            let post = *self;
            Self::lemma_same_tree_shrunk(pre, post);
            pre.lemma_retype_covers(root, from, base, 0);
            assert(authorized(pre.view(), root, Effect::Teardown { untyped, block: base, pages: 1, object: base }));
            assert(post.view() == pre.view());
            lemma_no_change_discharges_teardown(pre.view(), root, untyped, base, 1, base);
        }
        ReclaimStep::Freed
    }
}

} // verus!
