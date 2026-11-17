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
use crate::arch::{outcome_written, Registers};
#[cfg(verus_keep_ghost)]
use crate::capability::operation::{status_only, Outcome};
use crate::capability::operation::{status_only_outcome, STATUS_ERROR};
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;

/// Maximum waiters removed from a dead queue in one reclaim slice.
/// See design/one-lock-bounded-steps/.
pub const QUEUE_SLICE_BUDGET: usize = 64;

impl CapKernel {
    /// A dead endpoint or notification at zero references whose queue lists no thread: the block to be
    /// freed. A queue that still lists threads is drained in slices before its block frees.
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
        &&& post.targeted == self.targeted
        &&& post.core_tags == self.core_tags
        &&& post.tlb_dirty == self.tlb_dirty
        &&& post.cores == self.cores
        &&& post.resched_ipis == self.resched_ipis
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
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
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
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
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

    /// A dead endpoint or notification at zero references, regardless of whether waiters remain.
    pub open spec fn queue_object_dead(&self, page: usize) -> bool {
        &&& self.blocks.tracks(page as int)
        &&& self.blocks.pages@[page as int].kind is Base
        &&& queue_object(self.blocks.pages@[page as int].object)
        &&& self.blocks.pages@[page as int].dead
        &&& self.blocks.pages@[page as int].refs == 0
    }

    /// Whether a dead endpoint or notification at `base` still lists waiters to wake in a slice.
    pub open spec fn can_slice_queue(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 0)
        &&& self.queue_object_dead(base / PAGE_SZ)
        &&& self.endpoints.records@[base].value().waiters@.len() > 0
    }

    /// Appends `pl.core` to `acc` when `t` is `Blocked` and its placement outranks that core's current thread.
    pub open spec fn queue_wake_step(pre: Self, t: usize, acc: Seq<usize>) -> Seq<usize> {
        if pre.threads.records@.contains_key(t)
            && pre.threads.records@[t].value().state is Blocked {
            let pl = pre.threads.records@[t].value().placement->Some_0;
            if pre.outranks_current(pl.core as int, pl.priority) {
                acc.push(pl.core)
            } else {
                acc
            }
        } else {
            acc
        }
    }

    /// Reschedule IPIs appended by waking each `Blocked` thread in `removed` whose placement
    /// outranks its core's current thread.
    pub open spec fn queue_wake_resched(pre: Self, removed: Seq<usize>, acc: Seq<usize>) -> Seq<usize>
        decreases removed.len(),
    {
        if removed.len() == 0 {
            acc
        } else {
            Self::queue_wake_resched(pre, removed.drop_first(), Self::queue_wake_step(pre, removed[0], acc))
        }
    }

    /// One teardown slice of the dead endpoint or notification at `base`: up to
    /// `QUEUE_SLICE_BUDGET` waiters are removed from the head of its queue; any still `Blocked` on
    /// it becomes `Runnable` on its placement's core with `STATUS_ERROR` in its saved frame and a
    /// reschedule IPI recorded when its priority outranks that core's current thread; stale waiters
    /// are unlinked; the waiter bit clears when the queue empties; and the step discharges
    /// `Effect::Teardown`.
    pub open spec fn queue_sliced(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let pre_q = self.endpoints.records@[base].value();
        let pre_w = pre_q.waiters@;
        let n: int = if pre_w.len() <= QUEUE_SLICE_BUDGET as int { pre_w.len() as int } else { QUEUE_SLICE_BUDGET as int };
        let removed = pre_w.subrange(0, n);
        let kept = pre_w.subrange(n, pre_w.len() as int);
        let untyped = self.tables.node_of(root, from);
        let wake_out = status_only(STATUS_ERROR);
        &&& self.can_slice_queue(root, from, base)
        &&& post.endpoints.records@.dom() == self.endpoints.records@.dom()
        &&& post.endpoints.holders == self.endpoints.holders
        &&& post.endpoints.records@[base].addr() == self.endpoints.records@[base].addr()
        &&& post.endpoints.records@[base].is_init()
        &&& post.endpoints.records@[base].value() == (QueueRecord {
            head: if kept.len() == 0 { NONE } else { kept[0] },
            tail: if kept.len() == 0 { NONE } else { pre_q.tail },
            waiters: Ghost(kept),
            word: if kept.len() == 0 { pre_q.word & !WAITER_BIT } else { pre_q.word },
            ..pre_q
        })
        &&& forall|x: usize| x != base && #[trigger] post.endpoints.records@.contains_key(x)
            ==> post.endpoints.records@[x] == self.endpoints.records@[x]
        &&& post.threads.records@.dom() == self.threads.records@.dom()
        &&& forall|x: usize| #[trigger] post.threads.records@.contains_key(x) ==> ({
            let r = self.threads.records@[x].value();
            let v = post.threads.records@[x].value();
            &&& post.threads.records@[x].addr() == self.threads.records@[x].addr()
            &&& post.threads.records@[x].is_init()
            &&& if removed.contains(x) {
                if r.state is Blocked {
                    let pl = r.placement->Some_0;
                    let new_frame = outcome_written(r.frame, wake_out);
                    same_thread_but_links(v, ThreadRecord {
                        state: ThreadState::Runnable { core: pl.core },
                        frame: new_frame,
                        save: Ghost(entry_frame_save(new_frame, r.saved)),
                        queued: NONE,
                        wait_prev: NONE,
                        wait_next: NONE,
                        ..r
                    })
                } else {
                    same_thread_but_links(v, ThreadRecord {
                        queued: NONE,
                        wait_prev: NONE,
                        wait_next: NONE,
                        ..r
                    })
                }
            } else if kept.len() > 0 && x == kept[0] {
                same_thread_but_links(v, ThreadRecord { wait_prev: NONE, ..r })
            } else {
                same_thread_but_links(v, r)
            }
        })
        &&& post.resched_ipis@ == Self::queue_wake_resched(*self, removed, self.resched_ipis@)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, block: base, pages: 0, object: base })
        &&& Self::queue_slice_keeps(*self, post)
    }

    /// Appending one waiter `t` to `removed` appends one reschedule IPI when `t` was `Blocked` on
    /// a placement that outranks its core's current thread.
    proof fn lemma_queue_wake_resched_push(pre: Self, s: Seq<usize>, t: usize, init: Seq<usize>)
        ensures
            Self::queue_wake_resched(pre, s.push(t), init)
                == Self::queue_wake_step(pre, t, Self::queue_wake_resched(pre, s, init)),
        decreases s.len(),
    {
        if s.len() == 0 {
            let st = Self::queue_wake_step(pre, t, init);
            assert(s.push(t).len() == 1);
            assert(s.push(t)[0] == t);
            assert(s.push(t).drop_first() =~= Seq::<usize>::empty());
            assert(Self::queue_wake_resched(pre, s.push(t).drop_first(), st) == st);
            assert(Self::queue_wake_resched(pre, s, init) == init);
        } else {
            let head = s[0];
            let step = Self::queue_wake_step(pre, head, init);
            assert(s.push(t).len() == s.len() + 1);
            assert(s.push(t)[0] == head);
            assert(s.push(t).drop_first() =~= s.drop_first().push(t));
            Self::lemma_queue_wake_resched_push(pre, s.drop_first(), t, step);
        }
    }

    /// Isolated step proof advancing the slice thread-record invariant across one popped head.
    #[verifier::spinoff_prover]
    proof fn lemma_queue_slice_threads_step(
        pre: Self,
        mid: Self,
        post: Self,
        base: usize,
        idx: int,
        taken: int,
        popped: usize,
        err_out: Outcome,
    )
        requires
            0 <= idx < pre.endpoints.records@[base].value().waiters@.len(),
            taken == idx + 1,
            pre.endpoints.records@[base].value().waiters@.no_duplicates(),
            mid.endpoints.records@.contains_key(base),
            mid.endpoints.records@[base].value().waiters@ == pre.endpoints.records@[base].value().waiters@.subrange(idx, pre.endpoints.records@[base].value().waiters@.len() as int),
            popped == pre.endpoints.records@[base].value().waiters@[idx],
            pre.threads.records@.contains_key(popped),
            mid.threads.records@.contains_key(popped),
            pre.threads.records@.dom() == mid.threads.records@.dom(),
            mid.threads.records@.dom() == post.threads.records@.dom(),
            forall|x: usize| #[trigger] mid.threads.records@.contains_key(x) ==> ({
                let pre_w = pre.endpoints.records@[base].value().waiters@;
                let r = pre.threads.records@[x].value();
                let v = mid.threads.records@[x].value();
                let removed = pre_w.subrange(0, idx);
                let kept = pre_w.subrange(idx, pre_w.len() as int);
                &&& mid.threads.records@[x].addr() == pre.threads.records@[x].addr()
                &&& mid.threads.records@[x].is_init()
                &&& if removed.contains(x) {
                    if r.state is Blocked {
                        let pl = r.placement->Some_0;
                        let new_frame = outcome_written(r.frame, err_out);
                        same_thread_but_links(v, ThreadRecord {
                            state: ThreadState::Runnable { core: pl.core },
                            frame: new_frame,
                            save: Ghost(entry_frame_save(new_frame, r.saved)),
                            queued: NONE,
                            wait_prev: NONE,
                            wait_next: NONE,
                            ..r
                        })
                    } else {
                        same_thread_but_links(v, ThreadRecord {
                            queued: NONE,
                            wait_prev: NONE,
                            wait_next: NONE,
                            ..r
                        })
                    }
                } else if kept.len() > 0 && x == kept[0] {
                    if idx == 0 {
                        same_thread_but_links(v, r)
                    } else {
                        same_thread_but_links(v, ThreadRecord { wait_prev: NONE, ..r })
                    }
                } else {
                    same_thread_but_links(v, r)
                }
            }),
            forall|x: usize| #[trigger] post.threads.records@.contains_key(x) ==> ({
                let r = mid.threads.records@[x].value();
                let v = post.threads.records@[x].value();
                let rem = mid.endpoints.records@[base].value().waiters@.drop_first();
                &&& post.threads.records@[x].addr() == mid.threads.records@[x].addr()
                &&& post.threads.records@[x].is_init()
                &&& if x == popped {
                    if r.state is Blocked {
                        let pl = r.placement->Some_0;
                        let new_frame = outcome_written(r.frame, err_out);
                        same_thread_but_links(v, ThreadRecord {
                            state: ThreadState::Runnable { core: pl.core },
                            frame: new_frame,
                            save: Ghost(entry_frame_save(new_frame, r.saved)),
                            queued: NONE,
                            wait_prev: NONE,
                            wait_next: NONE,
                            ..r
                        })
                    } else {
                        same_thread_but_links(v, ThreadRecord {
                            queued: NONE,
                            wait_prev: NONE,
                            wait_next: NONE,
                            ..r
                        })
                    }
                } else if rem.len() > 0 && x == rem[0] {
                    same_thread_but_links(v, ThreadRecord { wait_prev: NONE, ..r })
                } else {
                    same_thread_but_links(v, r)
                }
            }),
        ensures
            forall|x: usize| #[trigger] post.threads.records@.contains_key(x) ==> ({
                let pre_w = pre.endpoints.records@[base].value().waiters@;
                let r = pre.threads.records@[x].value();
                let v = post.threads.records@[x].value();
                let removed = pre_w.subrange(0, taken);
                let kept = pre_w.subrange(taken, pre_w.len() as int);
                &&& post.threads.records@[x].addr() == pre.threads.records@[x].addr()
                &&& post.threads.records@[x].is_init()
                &&& if removed.contains(x) {
                    if r.state is Blocked {
                        let pl = r.placement->Some_0;
                        let new_frame = outcome_written(r.frame, err_out);
                        same_thread_but_links(v, ThreadRecord {
                            state: ThreadState::Runnable { core: pl.core },
                            frame: new_frame,
                            save: Ghost(entry_frame_save(new_frame, r.saved)),
                            queued: NONE,
                            wait_prev: NONE,
                            wait_next: NONE,
                            ..r
                        })
                    } else {
                        same_thread_but_links(v, ThreadRecord {
                            queued: NONE,
                            wait_prev: NONE,
                            wait_next: NONE,
                            ..r
                        })
                    }
                } else if kept.len() > 0 && x == kept[0] {
                    same_thread_but_links(v, ThreadRecord { wait_prev: NONE, ..r })
                } else {
                    same_thread_but_links(v, r)
                }
            }),
            mid.threads.records@[popped].value().state == pre.threads.records@[popped].value().state,
            mid.threads.records@[popped].value().placement == pre.threads.records@[popped].value().placement,
    {
        let pre_w = pre.endpoints.records@[base].value().waiters@;
        let rem_mid = pre_w.subrange(idx, pre_w.len() as int);
        let rem_post = pre_w.subrange(taken, pre_w.len() as int);
        let removed_mid = pre_w.subrange(0, idx);
        let removed_post = pre_w.subrange(0, taken);
        assert(rem_mid.drop_first() =~= rem_post);
        assert(removed_post =~= removed_mid.push(popped));
        assert(!removed_mid.contains(popped)) by {
            if removed_mid.contains(popped) {
                let k = choose|k: int| 0 <= k < idx && removed_mid[k] == popped;
                assert(pre_w[k] == pre_w[idx]);
            }
        }
        assert(rem_mid[0] == popped);
        if rem_post.len() > 0 {
            assert(!removed_post.contains(rem_post[0])) by {
                if removed_post.contains(rem_post[0]) {
                    let k = choose|k: int| 0 <= k < taken && removed_post[k] == rem_post[0];
                    assert(pre_w[k] == pre_w[taken]);
                }
            }
        }
        assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) implies ({
            let r = pre.threads.records@[x].value();
            let v = post.threads.records@[x].value();
            &&& post.threads.records@[x].addr() == pre.threads.records@[x].addr()
            &&& post.threads.records@[x].is_init()
            &&& if removed_post.contains(x) {
                if r.state is Blocked {
                    let pl = r.placement->Some_0;
                    let new_frame = outcome_written(r.frame, err_out);
                    same_thread_but_links(v, ThreadRecord {
                        state: ThreadState::Runnable { core: pl.core },
                        frame: new_frame,
                        save: Ghost(entry_frame_save(new_frame, r.saved)),
                        queued: NONE,
                        wait_prev: NONE,
                        wait_next: NONE,
                        ..r
                    })
                } else {
                    same_thread_but_links(v, ThreadRecord {
                        queued: NONE,
                        wait_prev: NONE,
                        wait_next: NONE,
                        ..r
                    })
                }
            } else if rem_post.len() > 0 && x == rem_post[0] {
                same_thread_but_links(v, ThreadRecord { wait_prev: NONE, ..r })
            } else {
                same_thread_but_links(v, r)
            }
        }) by {
            assert(mid.threads.records@.contains_key(x));
            assert(pre.threads.records@.contains_key(x));
            if x == popped {
                assert(removed_post[idx] == popped);
                assert(removed_post.contains(x));
            } else if removed_mid.contains(x) {
                let k = choose|k: int| 0 <= k < idx && removed_mid[k] == x;
                assert(removed_post[k] == x);
                assert(removed_post.contains(x));
                assert(!(rem_post.len() > 0 && x == rem_post[0]));
            } else if rem_post.len() > 0 && x == rem_post[0] {
                assert(rem_post[0] == rem_mid.drop_first()[0]);
                assert(!removed_post.contains(x));
            } else {
                assert(!removed_post.contains(x));
            }
        }
    }

    /// Checking `outranks_current` on `mid` agrees with `pre`. A `Blocked` thread has a placement,
    /// so its core is in range, and a slice keeps every thread's placement and every core, so the
    /// thread that core runs has the same priority in `mid` as in `pre`.
    #[verifier::spinoff_prover]
    pub(crate) proof fn lemma_queue_slice_outranks(pre: Self, mid: Self, popped: usize)
        requires
            pre.wf(),
            pre.threads.records@.contains_key(popped),
            mid.threads.records@.contains_key(popped),
            mid.cores == pre.cores,
            pre.threads.records@.dom() == mid.threads.records@.dom(),
            forall|x: usize| #[trigger] pre.threads.records@.contains_key(x)
                ==> mid.threads.records@[x].value().placement == pre.threads.records@[x].value().placement,
            pre.threads.records@[popped].value().state is Blocked,
        ensures
            ({
                let pl = pre.threads.records@[popped].value().placement->Some_0;
                &&& pl.core < NUM_CPUS
                &&& mid.outranks_current(pl.core as int, pl.priority) == pre.outranks_current(pl.core as int, pl.priority)
            }),
    {
        let rec = pre.threads.records@[popped].value();
        assert(placed_running_wf(pre.threads.records@)) by {
            reveal(CapKernel::wf);
        };
        reveal(placed_running_wf);
        assert(thread_placed_running(rec));
        assert(rec.placement is Some);
        assert(placements_wf(&pre.list, &pre.tables, &pre.threads)) by {
            reveal(CapKernel::wf);
        };
        reveal(placements_wf);
        let pl = rec.placement->Some_0;
        assert(pl.core < NUM_CPUS);
        assert(current_wf(pre.cores@, pre.threads.records@)) by {
            reveal(CapKernel::wf);
        };
        reveal(current_wf);
        assert(mid.cores@[pl.core as int].current_thread == pre.cores@[pl.core as int].current_thread);
        if let Some(cur) = pre.cores@[pl.core as int].current_thread {
            assert(runs(pre.cores@, pl.core as int, cur));
            assert(pre.threads.records@.contains_key(cur));
            assert(mid.threads.records@.contains_key(cur));
            assert(mid.threads.records@[cur].value().placement == pre.threads.records@[cur].value().placement);
            assert(crate::capability::schedule::thread_priority(mid.threads.records@[cur].value())
                == crate::capability::schedule::thread_priority(pre.threads.records@[cur].value()));
        }
        assert(mid.outranks_current(pl.core as int, pl.priority) == pre.outranks_current(pl.core as int, pl.priority));
    }

    /// A retype naming the block of the endpoint or notification at `base`, under the untyped at index
    /// `from` of the table at `root`: while its queue lists threads, it removes up to
    /// `QUEUE_SLICE_BUDGET` waiters in one slice, waking each still `Blocked` on it to `Runnable`
    /// with `STATUS_ERROR`; once empty and dead with zero references, it frees the block.
    #[verifier::spinoff_prover]
    pub(crate) fn reclaim_queue(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(steps).count <= old(steps).count + QUEUE_SLICE_BUDGET,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused || ret is Slice || ret is Freed,
            ret is Refused ==> *final(self) == *old(self),
            !(old(self).can_slice_queue(root, from, base)
                || (old(self).can_retype_under(root, from, base, 0) && old(self).queue_is_dead(base / PAGE_SZ))) ==> ret is Refused,
            old(self).can_slice_queue(root, from, base)
                ==> ret is Slice && old(self).queue_sliced(*final(self), root, from, base),
            old(self).can_retype_under(root, from, base, 0) && old(self).queue_is_dead(base / PAGE_SZ)
                ==> ret is Freed && old(self).queue_freed(*final(self), c, root, from, base),
            ret is Slice ==> old(self).queue_sliced(*final(self), root, from, base),
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
        let mut head = PPtr::<QueueRecord>::from_usize(base).borrow(Tracked(self.endpoints.records.borrow().tracked_borrow(base))).head;
        if head != NONE {
            let ghost pre_q = pre.endpoints.records@[base].value();
            let ghost pre_w = pre_q.waiters@;
            let err_out = status_only_outcome(STATUS_ERROR);
            proof {
                reveal(CapKernel::wf);
                assert(pre.endpoints.records@.contains_key(base));
                assert(pre.endpoints.records@[base].is_init());
                pre.lemma_retype_covers(root, from, base, 0);
                assert(authorized(pre.view(), root, Effect::Teardown { untyped, block: base, pages: 0, object: base }));
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base, 0, base);
                assert(wait_queue_wf(pre_q, pre.threads.records@, base)) by {
                    reveal(CapKernel::wf);
                    reveal(waits_wf);
                }
                assert(forall|k: int| 0 <= k < pre_w.len() ==> #[trigger] pre_w[k] != NONE && pre.threads.records@.contains_key(pre_w[k])) by {
                    assert forall|k: int| 0 <= k < pre_w.len() implies #[trigger] pre_w[k] != NONE && pre.threads.records@.contains_key(pre_w[k]) by {
                        assert(waiter_linked(pre_w, pre.threads.records@, base, k));
                        assert(pre.threads.records@.contains_key(pre_w[k]));
                    }
                }
                assert(pre_w.subrange(0, 0) =~= Seq::<usize>::empty());
                assert(pre_w.subrange(0, pre_w.len() as int) =~= pre_w);
            }
            let mut taken: usize = 0;
            while head != NONE && taken < QUEUE_SLICE_BUDGET
                invariant
                    0 <= taken <= QUEUE_SLICE_BUDGET,
                    taken <= pre_w.len(),
                    steps.count <= old(steps).count + taken,
                    pre.wf(),
                    pre.can_slice_queue(root, from, base),
                    untyped == pre.tables.node_of(root, from),
                    pre.endpoints.records@.contains_key(base),
                    pre.endpoints.records@[base].is_init(),
                    pre_q == pre.endpoints.records@[base].value(),
                    pre_w == pre_q.waiters@,
                    pre_w.no_duplicates(),
                    forall|k: int| 0 <= k < pre_w.len() ==> #[trigger] pre_w[k] != NONE && pre.threads.records@.contains_key(pre_w[k]),
                    err_out == status_only(STATUS_ERROR),
                    self.wf(),
                    self.endpoints.records@.contains_key(base),
                    head != NONE <==> taken < pre_w.len(),
                    head != NONE ==> head == pre_w[taken as int],
                    self.endpoints.records@.dom() == pre.endpoints.records@.dom(),
                    self.endpoints.holders == pre.endpoints.holders,
                    self.endpoints.records@[base].addr() == pre.endpoints.records@[base].addr(),
                    self.endpoints.records@[base].is_init(),
                    ({
                        let kept = pre_w.subrange(taken as int, pre_w.len() as int);
                        self.endpoints.records@[base].value() == (QueueRecord {
                            head: if kept.len() == 0 { NONE } else { kept[0] },
                            tail: if kept.len() == 0 { NONE } else { pre_q.tail },
                            waiters: Ghost(kept),
                            word: if kept.len() == 0 { pre_q.word & !WAITER_BIT } else { pre_q.word },
                            ..pre_q
                        })
                    }),
                    forall|x: usize| x != base && #[trigger] self.endpoints.records@.contains_key(x)
                        ==> self.endpoints.records@[x] == pre.endpoints.records@[x],
                    self.threads.records@.dom() == pre.threads.records@.dom(),
                    forall|x: usize| #[trigger] self.threads.records@.contains_key(x) ==> ({
                        let r = pre.threads.records@[x].value();
                        let v = self.threads.records@[x].value();
                        let removed = pre_w.subrange(0, taken as int);
                        let kept = pre_w.subrange(taken as int, pre_w.len() as int);
                        &&& self.threads.records@[x].addr() == pre.threads.records@[x].addr()
                        &&& self.threads.records@[x].is_init()
                        &&& if removed.contains(x) {
                            if r.state is Blocked {
                                let pl = r.placement->Some_0;
                                let new_frame = outcome_written(r.frame, err_out);
                                same_thread_but_links(v, ThreadRecord {
                                    state: ThreadState::Runnable { core: pl.core },
                                    frame: new_frame,
                                    save: Ghost(entry_frame_save(new_frame, r.saved)),
                                    queued: NONE,
                                    wait_prev: NONE,
                                    wait_next: NONE,
                                    ..r
                                })
                            } else {
                                same_thread_but_links(v, ThreadRecord {
                                    queued: NONE,
                                    wait_prev: NONE,
                                    wait_next: NONE,
                                    ..r
                                })
                            }
                        } else if kept.len() > 0 && x == kept[0] {
                            if taken == 0 {
                                same_thread_but_links(v, r)
                            } else {
                                same_thread_but_links(v, ThreadRecord { wait_prev: NONE, ..r })
                            }
                        } else {
                            same_thread_but_links(v, r)
                        }
                    }),
                    self.resched_ipis@ == Self::queue_wake_resched(pre, pre_w.subrange(0, taken as int), pre.resched_ipis@),
                    discharges(pre.view(), self.view(), root, Effect::Teardown { untyped, block: base, pages: 0, object: base }),
                    Self::queue_slice_keeps(pre, *self),
                decreases QUEUE_SLICE_BUDGET - taken,
            {
                let ghost mid = *self;
                let popped = self.pop_and_wake_waiter(base, err_out);
                head = PPtr::<QueueRecord>::from_usize(base).borrow(Tracked(self.endpoints.records.borrow().tracked_borrow(base))).head;
                taken = taken + 1;
                proof {
                    steps.step();
                    let post = *self;
                    let idx = (taken - 1) as int;
                    let rem_mid = pre_w.subrange(idx, pre_w.len() as int);
                    let rem_post = pre_w.subrange(taken as int, pre_w.len() as int);
                    let removed_mid = pre_w.subrange(0, idx);
                    let removed_post = pre_w.subrange(0, taken as int);
                    assert(rem_mid.len() > 0 && rem_mid[0] == pre_w[idx]);
                    assert(mid.endpoints.records@[base].value().waiters@ == rem_mid);
                    assert(popped == pre_w[idx]);
                    assert(rem_mid.drop_first() =~= rem_post);
                    assert(removed_post =~= removed_mid.push(popped));
                    Self::lemma_queue_slice_threads_step(pre, mid, post, base, idx, taken as int, popped, err_out);
                    if pre.threads.records@[popped].value().state is Blocked {
                        Self::lemma_queue_slice_outranks(pre, mid, popped);
                    }
                    Self::lemma_queue_wake_resched_push(pre, removed_mid, popped, pre.resched_ipis@);
                    lemma_teardown_steps_compose(pre.view(), mid.view(), post.view(), root, untyped, base, 0, base);
                }
            }
            proof {
                let post = *self;
                Self::lemma_same_tree_shrunk(pre, post);
                let n: int = if pre_w.len() <= QUEUE_SLICE_BUDGET as int { pre_w.len() as int } else { QUEUE_SLICE_BUDGET as int };
                assert(taken as int == n);
                assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) implies ({
                    let r = pre.threads.records@[x].value();
                    let v = post.threads.records@[x].value();
                    let removed = pre_w.subrange(0, n);
                    let kept = pre_w.subrange(n, pre_w.len() as int);
                    &&& post.threads.records@[x].addr() == pre.threads.records@[x].addr()
                    &&& post.threads.records@[x].is_init()
                    &&& if removed.contains(x) {
                        if r.state is Blocked {
                            let pl = r.placement->Some_0;
                            let new_frame = outcome_written(r.frame, err_out);
                            same_thread_but_links(v, ThreadRecord {
                                state: ThreadState::Runnable { core: pl.core },
                                frame: new_frame,
                                save: Ghost(entry_frame_save(new_frame, r.saved)),
                                queued: NONE,
                                wait_prev: NONE,
                                wait_next: NONE,
                                ..r
                            })
                        } else {
                            same_thread_but_links(v, ThreadRecord {
                                queued: NONE,
                                wait_prev: NONE,
                                wait_next: NONE,
                                ..r
                            })
                        }
                    } else if kept.len() > 0 && x == kept[0] {
                        same_thread_but_links(v, ThreadRecord { wait_prev: NONE, ..r })
                    } else {
                        same_thread_but_links(v, r)
                    }
                }) by {
                    if taken == 0 {
                        assert(false);
                    }
                }
                assert(pre.queue_sliced(post, root, from, base));
            }
            return ReclaimStep::Slice;
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
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
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
