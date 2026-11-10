//! Retype reclaiming a dead thread's block: one retype unlinks its binding to its process, and the next
//! frees the block. A thread object is not retyped while a core depends on it, so a thread Running on a
//! core, which is also the only kind with a stop pending, is refused until that core has moved it off.
//! See design/teardown-driven-by-retype/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::device::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
use crate::capability::mapping::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::thread::ThreadState;
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// Removing node t from the list at position p, every parent as it was, leaves a node whose only child
/// was t with none: whatever follows it now is listed, so it was listed before and is not t.
proof fn lemma_only_child_gone(pre: Tree, post: Tree, t: usize, p: int)
    requires
        pre.wf(),
        post.wf(),
        0 < p < pre.seq@.len(),
        pre.seq@[p] == t,
        post.seq@ == pre.seq@.remove(p),
        post.parent@ == pre.parent@,
        !post.nodes@[t as int].live,
        forall|x: int| 0 <= x < NODE_SPACE && x != t ==> #[trigger] post.nodes@[x].live == pre.nodes@[x].live,
    ensures
        forall|x: usize| x < NODE_SPACE && x != t && pre.nodes@[x as int].live
            && (forall|c: usize| #[trigger] pre.is_child(x, c) ==> c == t)
            ==> #[trigger] post.childless(x),
{
    assert forall|x: usize| x < NODE_SPACE && x != t && pre.nodes@[x as int].live
        && (forall|c: usize| #[trigger] pre.is_child(x, c) ==> c == t)
        implies #[trigger] post.childless(x) by {
        if !post.childless(x) {
            post.lemma_next_is_child(x);
            let c = post.nodes@[x as int].next;
            let k = choose|k: int| 0 <= k < post.seq@.len() && post.seq@[k] == c;
            post.lemma_link(k);
            let j = if k < p { k } else { k + 1 };
            assert(c != t);
            assert(pre.seq@[j] == c);
            assert(pre.seq@.contains(c));
            assert(post.seq@[0] == pre.seq@[0]);
            assert(pre.is_child(x, c));
        }
    }
}

impl CapKernel {
    /// The thread at `base` is dead at zero references, so no capability names it, and is not Running,
    /// so no core has it as current thread and no stop is pending on it.
    pub open spec fn thread_is_dead(&self, base: usize) -> bool {
        &&& self.threads.records@.contains_key(base)
        &&& self.blocks.pages@[(base / 4096) as int].refs == 0
        &&& !(self.threads.records@[base].value().state is Running)
    }

    /// What is left of the teardown of the thread at `base`: its binding to its process, then its block.
    pub open spec fn thread_work(&self, base: usize) -> nat {
        if !self.threads.records@.contains_key(base) {
            0
        } else if self.threads.records@[base].value().process is Some {
            2
        } else {
            1
        }
    }

    /// A retype may unlink the binding of the dead thread at `base`: an untyped covers its block and its
    /// record names a process.
    pub open spec fn can_unbind_thread(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, THREAD_ORDER)
        &&& self.thread_is_dead(base)
        &&& self.threads.records@[base].value().process is Some
    }

    /// The dead thread at `base` is bound to nothing and no node in its node page is live, so nothing is
    /// left of it but its two pages.
    pub open spec fn thread_is_spent(&self, base: usize) -> bool {
        &&& self.thread_is_dead(base)
        &&& self.threads.records@[base].value().process is None
        &&& forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] self.list.nodes@[base + k]).live
    }

    /// What unlinking the binding of the dead thread at `base` did to self: its record names no process,
    /// the process's block lost the reference, and the list lost the binding node alone, so every other
    /// node keeps its kind and its depth, and a node whose only child was the binding has none. The node
    /// was no capability and no mapping, so the view is as it was, and so are the spaces, the table
    /// pages, the stale epochs, the flush epoch, the cores and the IOMMUs.
    pub open spec fn thread_unbound(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.thread_is_dead(base)
        &&& Self::unbound(*self, post, base)
        &&& !post.list.nodes@[base as int].live
        &&& post.list.seq@.len() == self.list.seq@.len() - 1
        &&& forall|x: int| 0 <= x < NODE_SPACE && x != base ==> #[trigger] post.list.nodes@[x].live == self.list.nodes@[x].live
        &&& forall|x: int| 0 <= x < NODE_SPACE && x != base ==> #[trigger] post.list.nodes@[x].kind == self.list.nodes@[x].kind
        &&& forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] post.list.nodes@[x].depth == self.list.nodes@[x].depth
        &&& forall|x: usize| x < NODE_SPACE && x != base && self.list.nodes@[x as int].live
            && (forall|c: usize| #[trigger] self.list.is_child(x, c) ==> c == base)
            ==> #[trigger] post.list.childless(x)
        &&& post.list.parent == self.list.parent
        &&& post.tables == self.tables
        &&& post.cores == self.cores
        &&& post.iommus == self.iommus
        &&& post.spaces == self.spaces
        &&& post.table_pages == self.table_pages
        &&& post.stale_epoch == self.stale_epoch
        &&& post.flush_epoch == self.flush_epoch
        &&& post.thread_is_dead(base)
        &&& post.thread_work(base) < self.thread_work(base)
        &&& post.view() == self.view()
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables).remove(base)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// What freeing the spent thread at `base` did to self: it was on no core with no stop pending, its
    /// block is free, its record gone and its node page out of the list. It held no capability, so the
    /// view is as it was.
    pub open spec fn thread_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / 4096;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.thread_is_spent(base)
        &&& self.blocks.pages@[page as int].dead
        &&& forall|d: int| 0 <= d < NUM_CPUS ==> #[trigger] self.cores@[d].current_thread != Some(base)
        &&& !self.threads.records@[base].value().pending_stop
        &&& self.no_stale_translation(page)
        &&& self.no_stale_translation((page + 1) as usize)
        &&& post.blocks.pages@[page as int].kind is Free
        &&& post.blocks.pages@[page + 1int].kind is Free
        &&& !post.threads.records@.contains_key(base)
        &&& !post.list.pages@.dom().contains(base)
        &&& post.thread_work(base) < self.thread_work(base)
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, object: base })
    }

    /// The block test reclaim_thread makes reads as the records do: the block at a thread-aligned base
    /// is a thread's exactly when a record is kept there, and a kept thread is laid out as thread_wf
    /// says.
    proof fn lemma_dead_thread_block(&self, base: usize)
        requires
            self.wf(),
            base % 8192 == 0,
            self.blocks.tracks_addr(base),
        ensures
            thread_block(&self.blocks, base / 4096) == self.threads.records@.contains_key(base),
            self.threads.records@.contains_key(base) ==> {
                &&& self.blocks.tracks_addr_run(base, 2)
                &&& self.blocks.pages@[(base / 4096) as int].order == 1
                &&& (self.blocks.pages@[(base / 4096) as int].refs == 0 ==> self.blocks.pages@[(base / 4096) as int].dead)
                &&& self.threads.records@[base].addr() == base + THREAD_RECORD_PAGE * 4096
                &&& self.threads.records@[base].is_init()
                &&& self.list.pages@.dom().contains(base)
                &&& base < NODE_SPACE
            },
    {
        let page = base / 4096;
        lemma_leaf_page(base);
        if thread_block(&self.blocks, page) {
            assert(self.threads.records@.contains_key((page * 4096) as usize));
        }
        if self.threads.records@.contains_key(base) {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, base));
            self.lemma_thread_node_apart(base);
        }
    }

    /// A thread's base is its block's, typed as a thread, and a block typed as a thread holds no leaf,
    /// table page or space.
    pub proof fn lemma_thread_object(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.threads.records@.contains_key(base) ==> {
                &&& self.blocks.tracks_addr(base)
                &&& self.blocks.pages@[(base / 4096) as int].object is Thread
            },
            self.blocks.tracks_addr(base) && self.blocks.pages@[(base / 4096) as int].object is Thread ==> {
                &&& !self.tables.owner@.contains_key(base)
                &&& !self.table_pages.maps@.contains_key(base)
                &&& !self.spaces.roots@.contains_key(base)
            },
    {
        if self.threads.records@.contains_key(base) {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, base));
        }
        if self.blocks.tracks_addr(base) && self.blocks.pages@[(base / 4096) as int].object is Thread {
            if self.tables.owner@.contains_key(base) {
                self.tables.lemma_leaf(&self.list, base);
                assert(self.blocks.pages@[(base / 4096) as int].object is TableLeaf);
            }
            if self.table_pages.maps@.contains_key(base) {
                assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
            }
            if self.spaces.roots@.contains_key(base) {
                assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
            }
        }
    }

    /// A live binding node is not the list's first and has nothing below it: only a capability has
    /// children.
    proof fn lemma_binding_is_leaf(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Binding,
        ensures
            n != self.list.seq@[0],
            self.list.childless(n),
    {
        if !self.list.childless(n) {
            self.list.lemma_next_is_child(n);
        }
    }

    /// A step that takes a binding node away leaves the view as it was: the node was no capability, and
    /// every capability says what it did under the parent it had.
    proof fn lemma_binding_view_same(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            pre.list.nodes@[n as int].kind is Binding,
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

    /// Unlinks binding node t with its thread's binding and its reference on the process's block.
    fn unlink_binding(&mut self, t: usize)
        requires
            old(self).wf(),
            t < NODE_SPACE,
            old(self).list.nodes@[t as int].live,
            old(self).list.nodes@[t as int].kind is Binding,
        ensures
            final(self).wf(),
            Self::unbound(*old(self), *final(self), t),
            Self::same_tree(*old(self), *final(self)),
            final(self).mappings == old(self).mappings,
            !final(self).list.nodes@[t as int].live,
            final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            forall|x: int| 0 <= x < NODE_SPACE && x != t ==> #[trigger] final(self).list.nodes@[x].live == old(self).list.nodes@[x].live,
            forall|x: int| 0 <= x < NODE_SPACE && x != t ==> #[trigger] final(self).list.nodes@[x].kind == old(self).list.nodes@[x].kind,
            forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] final(self).list.nodes@[x].depth == old(self).list.nodes@[x].depth,
            forall|x: usize| x < NODE_SPACE && x != t && old(self).list.nodes@[x as int].live
                && (forall|c: usize| #[trigger] old(self).list.is_child(x, c) ==> c == t)
                ==> #[trigger] final(self).list.childless(x),
            final(self).list.parent == old(self).list.parent,
            final(self).tables == old(self).tables,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).spaces == old(self).spaces,
            final(self).table_pages == old(self).table_pages,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).view() == old(self).view(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables).remove(t),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_binding_is_leaf(t);
        }
        self.unlink_arm(t);
        let ghost mid = *self;
        self.list.remove_leaf(t);
        proof {
            let post = *self;
            post.tables.lemma_wf_same_pages(&pre.list, &post.list);
            assert(Self::caps_frame(pre, post, t, t));
            Self::lemma_delete_caps_wf(pre, post, t);
            let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == t
                && post.list.seq@ == pre.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == pre.list.seq@[0]);
            lemma_parents_removed(pre.list, post.list, t);
            Self::lemma_revoke_hidden(pre, post, t);
            Self::lemma_revoke_binding_holders(pre, post, t);
            Self::lemma_same_tree_shrunk(pre, post);
            Self::lemma_tlb_same(mid, post);
            assert forall|x: usize| x != t implies #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x) by {}
            Self::lemma_bound_threads_remove(pre, post, t);
            Self::lemma_binding_view_same(pre, post, t);
            assert(!pre.is_cap(t));
            lemma_only_child_gone(pre.list, post.list, t, p);
        }
    }

    /// Whether no node in the node page of the thread at `base` is live. A page holds a constant number.
    fn thread_nodes_dead(&self, base: usize) -> (ret: bool)
        requires
            self.wf(),
            self.threads.records@.contains_key(base),
        ensures
            ret == (forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] self.list.nodes@[base + k]).live),
    {
        proof {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, base));
            self.lemma_thread_node_apart(base);
        }
        let mut k = 0;
        while k != NODES_PER_PAGE
            invariant
                0 <= k <= NODES_PER_PAGE,
                self.wf(),
                self.threads.records@.contains_key(base),
                base % 8192 == 0,
                base < NODE_SPACE,
                self.list.pages@.dom().contains(base),
                forall|j: int| 0 <= j < k ==> !(#[trigger] self.list.nodes@[base + j]).live,
            decreases NODES_PER_PAGE - k,
        {
            proof {
                lemma_slot_in_leaf(base, k);
                assert(self.list.valid((base + k) as usize));
            }
            if self.list.get(base + k).live {
                return false;
            }
            k = k + 1;
        }
        true
    }

    /// No page of a thread's block is mapped: the only blocks a mapping names are frames'.
    proof fn lemma_thread_unmapped(&self, page: usize, g: usize)
        requires
            self.wf(),
            self.blocks.tracks(page as int),
            page % 2 == 0,
            self.blocks.pages@[page as int].kind is Base,
            self.blocks.pages@[page as int].object is Thread,
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

    /// What the invariant says of a spent thread's block and pages, before it frees.
    proof fn lemma_spent_thread(&self, base: usize)
        requires
            self.wf(),
            self.thread_is_spent(base),
        ensures
            base % 8192 == 0,
            base % 4096 == 0,
            base < NODE_SPACE,
            self.blocks.tracks_addr(base),
            self.blocks.tracks_addr_run(base, 2),
            (base / 4096) * 4096 == base,
            self.blocks.pages@[(base / 4096) as int].kind is Base,
            self.blocks.pages@[(base / 4096) as int].object is Thread,
            self.blocks.pages@[(base / 4096) as int].order == 1,
            self.blocks.pages@[(base / 4096) as int].refs == 0,
            self.blocks.pages@[(base / 4096) as int].dead,
            self.blocks.pages@[base / 4096 + 1int].kind is Member,
            self.list.pages@.dom().contains(base),
            self.list.pages@[base].addr() == base,
            self.list.pages@[base].is_init(),
            self.threads.holders@[base] == Set::<usize>::empty(),
            forall|d: int| 0 <= d < NUM_CPUS ==> #[trigger] self.cores@[d].current_thread != Some(base),
            !self.threads.records@[base].value().pending_stop,
    {
        let page = base / 4096;
        assert(thread_wf(&self.list, &self.threads, &self.blocks, base));
        self.lemma_thread_node_apart(base);
        lemma_leaf_page(base);
        reveal(Tree::store_wf);
        self.blocks.lemma_base(page as int);
        self.blocks.lemma_member_of(page as int, page + 1int);
        self.threads.holders@[base].lemma_len0_is_empty();
        reveal(current_wf);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.cores@[d].current_thread != Some(base) by {
            if self.cores@[d].current_thread == Some(base) {
                assert(runs(self.cores@, d, base));
            }
        }
    }

    /// A mapping node lies in its table page's node pages, so in no thread's node page.
    proof fn lemma_mapping_outside_thread(&self, n: usize, base: usize)
        requires
            self.wf(),
            self.mappings@.contains_key(n),
            self.threads.records@.contains_key(base),
        ensures
            page_of(n) != base,
    {
        let m = self.mappings@[n];
        let t = m.table;
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        assert(thread_wf(&self.list, &self.threads, &self.blocks, base));
        let q = t / 4096;
        self.blocks.lemma_base(q as int);
        assert(order_pages(3) == 8);
        lemma_mapping_node_place(t, m.entry);
        let k = ((m.entry + 1) / (NODES_PER_PAGE as int)) as usize;
        assert(page_of(n) / 4096 == q + k);
        if k > 0 {
            self.blocks.lemma_member_of(q as int, q + k);
        }
    }

    /// The block of the spent thread at `base` is its two pages, and nothing else the invariant tracks
    /// lies in it: no leaf, no other list page, no other thread and no holder's block.
    proof fn lemma_thread_block_alone(&self, base: usize)
        requires
            self.wf(),
            self.thread_is_spent(base),
        ensures
            forall|l: usize| #[trigger] self.tables.owner@.contains_key(l)
                ==> !self.blocks.in_block((base / 4096) as int, (l / 4096) as int),
            forall|p: usize| #[trigger] self.list.pages@.dom().contains(p) && p != base
                ==> !self.blocks.in_block((base / 4096) as int, (p / 4096) as int),
            forall|t: usize| #[trigger] self.threads.records@.contains_key(t) && t != base
                ==> !self.blocks.in_block((base / 4096) as int, (t / 4096) as int),
            forall|b: usize| #[trigger] self.holders@.contains_key(BlockRef::Small(b))
                ==> !self.blocks.in_block((base / 4096) as int, b as int),
    {
        let page = base / 4096;
        self.lemma_spent_thread(base);
        assert forall|l: usize| #[trigger] self.tables.owner@.contains_key(l)
            implies !self.blocks.in_block(page as int, (l / 4096) as int) by {
            self.tables.lemma_leaf(&self.list, l);
            assert(self.blocks.pages@[(l / 4096) as int].kind is Base);
            assert(self.blocks.pages@[(l / 4096) as int].object is TableLeaf);
            if self.blocks.in_block(page as int, (l / 4096) as int) && l / 4096 != page {
                self.blocks.lemma_member_of(page as int, (l / 4096) as int);
            }
        }
        assert forall|p: usize| #[trigger] self.list.pages@.dom().contains(p) && p != base
            implies !self.blocks.in_block(page as int, (p / 4096) as int) by {
            reveal(Tree::store_wf);
            assert(p % 4096 == 0);
            if p / 4096 == page {
                lemma_fundamental_div_mod(p as int, 4096);
                lemma_fundamental_div_mod(base as int, 4096);
            }
            if self.blocks.in_block(page as int, (p / 4096) as int) && p / 4096 != page {
                self.blocks.lemma_member_of(page as int, (p / 4096) as int);
                assert(self.blocks.pages@[page as int].object is Thread);
            }
        }
        assert forall|t: usize| #[trigger] self.threads.records@.contains_key(t) && t != base
            implies !self.blocks.in_block(page as int, (t / 4096) as int) by {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
            lemma_leaf_page(t);
            if (t / 4096) == page {
                lemma_fundamental_div_mod(t as int, 4096);
                lemma_fundamental_div_mod(base as int, 4096);
            }
            if self.blocks.in_block(page as int, (t / 4096) as int) && t / 4096 != page {
                self.blocks.lemma_member_of(page as int, (t / 4096) as int);
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

    /// The threads after the spent thread at `base` goes with its block: every other thread, its block
    /// and its node page are as they were, and no capability named the one that went.
    proof fn lemma_threads_freed(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            pre.thread_is_spent(base),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / 4096) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.list.pages@.dom() == pre.list.pages@.dom().remove(base),
            post.list.nodes == pre.list.nodes,
            post.tables == pre.tables,
            post.threads.records@ == pre.threads.records@.remove(base),
            post.threads.holders == pre.threads.holders,
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
    {
        let page = base / 4096;
        pre.lemma_spent_thread(base);
        pre.lemma_thread_block_alone(base);
        assert forall|t: usize| #[trigger] post.threads.records@.contains_key(t) implies thread_wf(&post.list, &post.threads, &post.blocks, t) by {
            assert(pre.threads.records@.contains_key(t));
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
            assert(t != base);
            assert(!pre.blocks.in_block(page as int, (t / 4096) as int));
        }
        assert forall|x: usize| post.blocks.tracks(x as int) && #[trigger] thread_block(&post.blocks, x)
            implies post.threads.records@.contains_key((x * 4096) as usize) by {
            if pre.blocks.in_block(page as int, x as int) {
                assert(post.blocks.pages@[x as int] == free_entry());
            }
            assert(post.blocks.pages@[x as int] == pre.blocks.pages@[x as int]);
            assert(thread_block(&pre.blocks, x));
            assert(x != page);
            lemma_page_base(x);
            lemma_fundamental_div_mod(base as int, 4096);
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && post.tables.payload_of(n).kind is Thread implies {
            &&& post.threads.records@.contains_key(post.tables.payload_of(n).base)
            &&& post.threads.holders@[post.tables.payload_of(n).base].contains(n)
            &&& post.tables.payload_of(n).order == THREAD_ORDER
        } by {
            assert(pre.tables.is_cap(&pre.list, n));
            if pre.tables.payload_of(n).base == base {
                assert(pre.threads.holders@[base].contains(n));
            }
        }
        assert forall|t: usize, n: usize| post.threads.records@.contains_key(t) && #[trigger] post.threads.holders@[t].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& post.tables.payload_of(n).kind is Thread
            &&& post.tables.payload_of(n).base == t
        } by {
            assert(pre.threads.records@.contains_key(t));
            assert(pre.tables.is_cap(&pre.list, n));
        }
    }

    /// The block table's invariants and the objects' after the spent thread at `base` goes: its two
    /// pages are free, and every other block, leaf, list page and object is as it was.
    proof fn lemma_thread_freed_blocks(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            pre.thread_is_spent(base),
            post.blocks.wf(),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / 4096) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.tables == pre.tables,
            post.list.nodes == pre.list.nodes,
            post.list.parent == pre.list.parent,
            post.list.seq == pre.list.seq,
            post.list.pages@.dom() == pre.list.pages@.dom().remove(base),
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.threads.records@ == pre.threads.records@.remove(base),
            post.threads.holders == pre.threads.holders,
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
        let page = base / 4096;
        pre.lemma_spent_thread(base);
        pre.lemma_thread_block_alone(base);
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
            pre.lemma_mapping_node_page(m);
            pre.lemma_mapping_outside_thread(m, base);
            assert(post.list.valid(m));
            assert(block_ref(&pre.blocks, pre.mappings@[m].frame) != BlockRef::Small(page));
            lemma_block_ref_small_freed(&pre.blocks, &post.blocks, page, pre.mappings@[m].frame);
        }
        Self::lemma_mappings_same_tree(pre, post);
        lemma_holders_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, page);
        assert(pre.holders@.remove(BlockRef::Small(page)) =~= pre.holders@) by {
            assert(!pre.holders@.contains_key(BlockRef::Small(page))) by {
                if pre.holders@.contains_key(BlockRef::Small(page)) {
                    assert(block_typed(&pre.blocks, BlockRef::Small(page)));
                    assert(pre.blocks.pages@[page as int].object is Frame);
                }
            }
        }
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
            &&& post.blocks.pages@[(l / 4096) as int] == pre.blocks.pages@[(l / 4096) as int]
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && #[trigger] leaf_block(&post.blocks, b)
            implies post.tables.owner@.contains_key((b * 4096) as usize) by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
            assert(leaf_block(&pre.blocks, b));
        }
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
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
        Self::lemma_threads_freed(pre, post, base);
        lemma_processes_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page);
    }

    /// The kernel after the spent thread at `base` frees: nothing but its block, its record and its list
    /// page changed, and the view and the bound threads are as they were.
    proof fn lemma_thread_freed(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            pre.thread_is_spent(base),
            post.blocks.wf(),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block((base / 4096) as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.tables == pre.tables,
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
            post.threads.records@ == pre.threads.records@.remove(base),
            post.threads.holders == pre.threads.holders,
            post.processes == pre.processes,
            post.stop_ipis == pre.stop_ipis,
        ensures
            post.wf(),
            post.view() == pre.view(),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
    {
        pre.lemma_spent_thread(base);
        assert(post.tables.wf(&post.list)) by {
            reveal(Tables::leaves_wf);
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies post.tables.leaf_wf(&post.list, l) by {
                assert(pre.tables.leaf_wf(&pre.list, l));
                pre.lemma_thread_object(base);
                assert(l != base);
            }
        }
        let (a, b) = (pre.view(), post.view());
        assert(b.held =~= a.held);
        assert(b.names =~= a.names);
        assert(b.pages =~= a.pages);
        assert(b.rights =~= a.rights);
        assert(b == a);
        Self::lemma_devices_same_caps(pre, post);
        assert forall|t: usize| #[trigger] pre.threads.records@.contains_key(t) && t != base implies {
            &&& post.threads.records@.contains_key(t)
            &&& post.threads.records@[t].value().process == pre.threads.records@[t].value().process
        } by {}
        reveal(binding_parents);
        assert forall|t: usize| t < NODE_SPACE && (#[trigger] post.list.nodes@[t as int]).live && post.list.nodes@[t as int].kind is Binding
            implies binding_parent(&post.list, &post.tables, &post.threads, t) by {
            assert(binding_parent(&pre.list, &pre.tables, &pre.threads, t));
            assert(t != base);
        }
        reveal(thread_bound);
        assert forall|n: usize| n < NODE_SPACE && (#[trigger] post.list.nodes@[n as int]).live && post.list.nodes@[n as int].kind is Binding
            implies thread_bound(&post.threads, n) by {
            assert(thread_bound(&pre.threads, n));
            assert(n != base);
        }
        assert forall|p: usize, t: usize| post.processes.records@.contains_key(p) && #[trigger] post.processes.bound@[p].contains(t)
            implies post.threads.records@.contains_key(t) && post.threads.records@[t].value().process == Some(p) by {
            assert(pre.threads.records@.contains_key(t));
            assert(t != base);
        }
        assert(bindings_wf(&post.list, &post.threads, &post.processes));
        reveal(current_wf);
        assert forall|c: int, t: usize| 0 <= c < NUM_CPUS && #[trigger] runs(post.cores@, c, t) implies {
            &&& post.threads.records@.contains_key(t)
            &&& post.threads.records@[t].value().state == (ThreadState::Running { core: c as usize })
        } by {
            assert(runs(pre.cores@, c, t));
            assert(t != base);
        }
        assert(current_wf(post.cores@, post.threads.records@));
        Self::lemma_thread_freed_blocks(pre, post, base);
        Self::lemma_tlb_same(pre, post);
        assert forall|x: usize| x != base implies #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x) by {}
        assert(thread_process(&post.threads, base) == thread_process(&pre.threads, base));
        Self::lemma_bound_threads_same(pre, post);
    }

    /// Frees the spent thread at `base`: its node page leaves the list, its record goes, and both pages
    /// go back to the block table, its block's teardown being finished.
    fn free_spent_thread(&mut self, base: usize)
        requires
            old(self).wf(),
            old(self).thread_is_spent(base),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            final(self).mappings == old(self).mappings,
            final(self).blocks.pages@[(base / 4096) as int].kind is Free,
            final(self).blocks.pages@[base / 4096 + 1int].kind is Free,
            !final(self).threads.records@.contains_key(base),
            !final(self).list.pages@.dom().contains(base),
            final(self).cores == old(self).cores,
            final(self).view() == old(self).view(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let page = base / 4096;
        proof {
            pre.lemma_spent_thread(base);
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, base));
        }
        self.blocks.mark_torn_down(page);
        let ghost mid = *self;
        let Tracked(nodes) = self.list.remove_page(base);
        let tracked mut perms = Map::<usize, PagePerm4k>::tracked_empty();
        proof {
            let tracked mut nodes = nodes;
            nodes.leak_contents();
            let tracked first = crate::layouts::node_page_into_page(nodes);
            let tracked mut record = self.threads.records.borrow_mut().tracked_remove(base);
            record.leak_contents();
            let tracked second = crate::layouts::thread_record_into_page(record);
            perms.tracked_insert(page, first);
            perms.tracked_insert((page + 1) as usize, second);
            assert(base + THREAD_RECORD_PAGE * 4096 == base + 4096);
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
        // The caller's work is not counted yet, so its counter starts here: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        self.blocks.free_block(page, Tracked(perms), Tracked(&mut steps));
        proof {
            let post = *self;
            assert forall|i: int| pre.blocks.tracks(i) implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            assert(post.threads.records@ =~= pre.threads.records@.remove(base));
            Self::lemma_thread_freed(pre, post, base);
            assert(pre.blocks.in_block(page as int, page as int));
            assert(pre.blocks.in_block(page as int, page + 1int));
        }
    }

    /// A retype naming the block of the thread at `base`, under the untyped at index `from` of the table
    /// at `root`: once its references are gone and no core depends on it, one retype unlinks its binding
    /// to its process and the next frees its block. A thread Running on a core, which is also the only
    /// kind with a stop pending, is refused until that core moves it off. All of these come from user
    /// space, and anything but an unlink or a free changes nothing.
    pub fn reclaim_thread(&mut self, c: usize, root: usize, from: usize, base: usize) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused || ret is Again ==> *final(self) == *old(self),
            !(ret is Unlinked),
            !(old(self).can_unbind_thread(root, from, base)
                || (old(self).can_retype_under(root, from, base, THREAD_ORDER) && old(self).thread_is_spent(base))) ==> ret is Refused,
            !old(self).view().holds_right(root, old(self).tables.node_of(root, from), Right::Retype) ==> ret is Refused,
            old(self).can_unbind_thread(root, from, base) ==> ret is Slice,
            old(self).can_retype_under(root, from, base, THREAD_ORDER) && old(self).thread_is_spent(base)
                ==> if old(self).acknowledged(base / 4096) && old(self).acknowledged((base / 4096 + 1) as usize) {
                    ret is Freed
                } else {
                    ret is Again
                },
            ret is Again ==> !old(self).acknowledged(base / 4096) || !old(self).acknowledged((base / 4096 + 1) as usize),
            ret is Slice ==> old(self).thread_unbound(*final(self), root, from, base),
            ret is Freed ==> old(self).thread_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
            pre.lemma_retype_right(root, from, base);
        }
        let untyped = match self.retype_parent(root, from, base, THREAD_ORDER) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / 4096;
        proof {
            lemma2_to64();
            assert(block_bytes(1) == 8192);
        }
        if !self.blocks.page_tracked(page) {
            proof {
                if pre.threads.records@.contains_key(base) {
                    assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, base));
                }
            }
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_thread = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Thread) => entry.refs == 0,
            _ => false,
        };
        proof {
            pre.lemma_dead_thread_block(base);
        }
        if !dead_thread {
            return ReclaimStep::Refused;
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(base + THREAD_RECORD_PAGE * 4096);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(base)));
        let running = match record.state {
            ThreadState::Running { .. } => true,
            _ => false,
        };
        if running {
            return ReclaimStep::Refused;
        }
        let bound = match record.process {
            Some(_) => true,
            None => false,
        };
        if bound {
            proof {
                reveal(thread_bound);
                pre.lemma_bound_process(base);
            }
            self.unlink_binding(base);
            proof {
                let post = *self;
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
                assert(post.threads.records@.contains_key(base));
                assert(post.blocks.pages@[page as int].refs == 0) by {
                    let p = pre.threads.records@[base].value().process->Some_0;
                    pre.lemma_bound_process(base);
                    assert(p / 4096 != page);
                    assert(block_typed(&pre.blocks, BlockRef::Small(page)));
                    assert(block_refs(&post.blocks, BlockRef::Small(page)) == block_refs(&pre.blocks, BlockRef::Small(page)));
                }
                assert(pre.thread_unbound(post, root, from, base));
            }
            return ReclaimStep::Slice;
        }
        if !self.thread_nodes_dead(base) {
            return ReclaimStep::Refused;
        }
        proof {
            pre.lemma_spent_thread(base);
        }
        // The caller's work is not counted yet, so its counter starts here: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        if !self.is_acknowledged(page, Tracked(&mut steps)) || !self.is_acknowledged(page + 1, Tracked(&mut steps)) {
            return ReclaimStep::Again;
        }
        proof {
            // On its own, for the modulus: a thread's block is two pages, aligned to them.
            assert(page % 2 == 0) by (nonlinear_arith)
                requires
                    base % 8192 == 0,
                    page == base / 4096,
            ;
            pre.lemma_thread_unmapped(page, page);
            pre.lemma_thread_unmapped(page, (page + 1) as usize);
            pre.lemma_acknowledged_is_clean(page);
            pre.lemma_acknowledged_is_clean((page + 1) as usize);
        }
        self.free_spent_thread(base);
        proof {
            let post = *self;
            lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
            assert(pre.thread_freed(post, c, root, from, base));
        }
        ReclaimStep::Freed
    }

    /// A retype's parent carries the right: the capability it names holds Retype.
    proof fn lemma_retype_right(&self, root: usize, from: usize, base: usize)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            self.can_retype_under(root, from, base, THREAD_ORDER)
                ==> self.view().holds_right(root, self.tables.node_of(root, from), Right::Retype),
    {
        if self.can_retype_under(root, from, base, THREAD_ORDER) {
            self.lemma_slot(root, from);
            assert(right_bit(Right::Retype) == 8);
            assert(self.tables.is_cap(&self.list, self.tables.node_of(root, from)));
        }
    }
}

} // verus!
