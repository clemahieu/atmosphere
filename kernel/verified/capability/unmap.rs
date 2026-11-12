// SPDX-License-Identifier: MIT

//! Unmapping one 4K entry of a space by its address. The entry's mapping node sits at a fixed index in
//! its table page's block, so it is found in constant time, and it goes through the arm revoke uses: the
//! entry clears, the unmap's staleness is recorded and the frame's reference drops. The entry's word is
//! read in the step that clears it, so the accessed and dirty bits the processor set there come back to
//! the caller. See design/address-spaces-as-objects/, design/flush-without-waiting/ and
//! design/arch-module/.
use vstd::prelude::*;

verus! {

use crate::arch::*;
use crate::capability::destroy::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::revoke::UNLINK_ARM_STEPS;
use crate::capability::steps::Steps;
use crate::capability::map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// What an unmap returns: the unmapped entry's accessed and dirty bits in the word read as it was
/// cleared, and whether this target's walker maintains each bit, without which it says nothing. The word
/// read is ghost.
#[derive(Clone, Copy)]
pub struct Unmapped {
    pub accessed: bool,
    pub dirty: bool,
    pub accessed_maintained: bool,
    pub dirty_maintained: bool,
    pub read: Ghost<usize>,
}

// The most each part of an unmap adds to the step counter, the sum of what its callees state:
// design/one-lock-bounded-steps/.
/// send_flush's bound: one flush IPI per core.
pub const SEND_FLUSH_STEPS: usize = NUM_CPUS;
/// unmap_entry's bound: the mapping node's arm.
pub const UNMAP_ENTRY_STEPS: usize = UNLINK_ARM_STEPS;
/// unmap_kind's bound: clearing the entry, then the flush.
pub const UNMAP_KIND_STEPS: usize = UNMAP_ENTRY_STEPS + SEND_FLUSH_STEPS;
/// unmap's bound: one unmap_kind.
pub const UNMAP_STEPS: usize = UNMAP_KIND_STEPS;
/// unmap_at's bound: one unmap.
pub const UNMAP_AT_STEPS: usize = UNMAP_STEPS;

impl CapKernel {
    /// The refusals: an index that names no capability to a space of this kind, or none that may change
    /// it, or a process capability naming a dead process, whose space waits for retype's teardown (see
    /// design/teardown-driven-by-retype/); a path that reaches no live level 1 table, or an entry of it
    /// that maps nothing; a flush epoch at its limit, after 2^64 unmaps, so the unmap's staleness could
    /// not be recorded.
    pub open spec fn can_unmap(&self, root: usize, slot: usize, kind: SpaceKind, p: SpacePath) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let n = self.tables.node_of(root, slot);
        let t = walk_table(tree, self.payload_of(n).base, p)->0;
        &&& self.tables.has_slot(&self.list, root, slot)
        &&& self.is_cap(n)
        &&& writes_space(self.payload_of(n))
        &&& !self.cap_dead(n)
        &&& self.spaces.records@[self.payload_of(n).base].value().kind == kind
        &&& walk_table(tree, self.payload_of(n).base, p) is Some
        &&& p.l1 < ENTRIES
        &&& tree.entry(t, p.l1).perm.present
        &&& self.flush_epoch < usize::MAX
    }

    /// The cores an unmap in space s sends a flush IPI to: those on the space's list of cores, in
    /// increasing order.
    pub open spec fn flush_targets(&self, s: usize) -> Seq<usize> {
        listed_cores(self.spaces.loaded@[s].value().list, NUM_CPUS as int)
    }

    /// An unmap in space s sent a flush IPI to each of its targets, and its targets are exactly the
    /// cores that loaded s, so every core that may hold an entry of s is among them and a core that
    /// never loaded s is not. See design/flush-without-waiting/.
    pub open spec fn flush_sent(pre: Self, post: Self, s: usize) -> bool {
        &&& post.flush_ipis@ == pre.flush_ipis@ + pre.flush_targets(s)
        &&& forall|d: usize| #[trigger] pre.flush_targets(s).contains(d) <==> d < NUM_CPUS && pre.loaded(d as int, s)
        &&& forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == s && #[trigger] pre.core_may_hold(d, e)
            ==> pre.flush_targets(s).contains(d as usize)
    }

    /// What an unmap leaves: the entry is gone as entry_unmapped says, a flush IPI went to each core that
    /// loaded the space, and the processes are as they were.
    pub open spec fn unmap_done(pre: Self, post: Self, root: usize, slot: usize, p: SpacePath) -> bool {
        &&& Self::entry_unmapped(pre, post, root, slot, p)
        &&& Self::flush_sent(pre, post, pre.payload_of(pre.tables.node_of(root, slot)).base)
        &&& post.processes == pre.processes
    }

    /// What clearing the entry leaves: the entry the path reaches is empty, its mapping node is the only
    /// node that left the list, its record and its frame's reference went with it, its staleness is
    /// recorded, and no capability changed: the tables, the list's parents, every other node's kind and
    /// the bound threads are as they were. A device space shares what a walk other than the one ending
    /// at the entry still finds: the page leaves unless another path of the space maps it too.
    pub open spec fn entry_unmapped(pre: Self, post: Self, root: usize, slot: usize, p: SpacePath) -> bool {
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let t = walk_table(tree, pre.payload_of(pre.tables.node_of(root, slot)).base, p)->0;
        let node = mapping_node(t, p.l1);
        &&& pre.mappings@.contains_key(node)
        &&& pre.mappings@[node].table == t
        &&& pre.mappings@[node].entry == p.l1
        &&& tree_of(&post.table_pages, &post.spaces).entry(t, p.l1).is_empty()
        &&& Self::mapping_unlinked(pre, post, node)
        &&& Self::mapping_stale_noted(pre, post, node)
        &&& Self::mappings_shrunk(pre, post)
        &&& pre.list.nodes@[node as int].kind is Mapping
        &&& !post.list.nodes@[node as int].live
        &&& forall|x: int| 0 <= x < NODE_SPACE && x != node ==> #[trigger] post.list.nodes@[x].live == pre.list.nodes@[x].live
            && post.list.nodes@[x].kind == pre.list.nodes@[x].kind
        &&& post.list.parent == pre.list.parent
        &&& post.tables == pre.tables
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
        &&& post.list.seq@.len() == pre.list.seq@.len() - 1
        &&& sheds_shares(pre.view(), post.view())
        &&& post.view().shares == shares_surviving(tree, |r: usize, q: SpacePath| ends_at(tree, r, q, t, p.l1))
    }

    /// What an unmap at path p of the space named at index slot of the table at root returned: the word
    /// read decodes to the entry the path reached, the bits are that word's accessed and dirty bits as
    /// read before it was cleared, and the two facts are this target's.
    pub open spec fn unmapped_read(pre: Self, root: usize, slot: usize, p: SpacePath, r: Unmapped) -> bool {
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let t = walk_table(tree, pre.payload_of(pre.tables.node_of(root, slot)).base, p)->0;
        &&& spec_usize2page_entry(r.read@, tree.record(t).level) == tree.entry(t, p.l1)
        &&& r.accessed == spec_usize2page_entry_status(r.read@, tree.record(t).level).accessed
        &&& r.dirty == spec_usize2page_entry_status(r.read@, tree.record(t).level).dirty
        &&& r.accessed_maintained == maintains_accessed()
        &&& r.dirty_maintained == maintains_dirty()
    }

    /// The refusals of an unmap of the entry the address va and the level name, in the space of the
    /// capability at index slot of the table at root: a level other than 1, an address that names no
    /// level 1 entry, or can_unmap's at the path the address names.
    pub open spec fn can_unmap_at(&self, root: usize, slot: usize, va: u64, level: u64) -> bool {
        &&& level == 1
        &&& names_entry(va, level)
        &&& self.can_unmap(root, slot, SpaceKind::Process, address_path(va))
    }

    /// What an unmap of the entry the address va and the level name, in the space of the capability at
    /// index slot of the table at root, did and returned: va names a level 1 entry, the unmap was allowed
    /// at the path the address names, unmap_done holds there, and r is what unmapped_read says.
    pub open spec fn page_unmapped(pre: Self, post: Self, root: usize, slot: usize, va: u64, level: u64, r: Unmapped) -> bool {
        let p = address_path(va);
        &&& level == 1
        &&& names_entry(va, level)
        &&& pre.can_unmap(root, slot, SpaceKind::Process, p)
        &&& Self::unmap_done(pre, post, root, slot, p)
        &&& Self::unmapped_read(pre, root, slot, p, r)
        &&& discharges(pre.view(), post.view(), root, Effect::Local)
    }

    /// An unmap leaves the tables, the list's parents and the bound threads as they were, and changes the
    /// kind or the liveness of no node but the mapping node it unlinked.
    pub proof fn lemma_page_unmapped_frame(pre: Self, post: Self, root: usize, slot: usize, va: u64, level: u64, r: Unmapped)
        requires
            Self::page_unmapped(pre, post, root, slot, va, level, r),
        ensures
            post.tables == pre.tables,
            post.list.parent == pre.list.parent,
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
            forall|x: int| 0 <= x < NODE_SPACE && (#[trigger] post.list.nodes@[x].kind != pre.list.nodes@[x].kind
                || post.list.nodes@[x].live != pre.list.nodes@[x].live) ==> pre.list.nodes@[x].kind is Mapping
                && !post.list.nodes@[x].live,
    {
        let p = address_path(va);
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let t = walk_table(tree, pre.payload_of(pre.tables.node_of(root, slot)).base, p)->0;
        let node = mapping_node(t, p.l1);
        assert(Self::entry_unmapped(pre, post, root, slot, p));
        assert forall|x: int| 0 <= x < NODE_SPACE && (#[trigger] post.list.nodes@[x].kind != pre.list.nodes@[x].kind
            || post.list.nodes@[x].live != pre.list.nodes@[x].live) implies pre.list.nodes@[x].kind is Mapping
            && !post.list.nodes@[x].live by {
            if x != node {
                assert(post.list.nodes@[x].live == pre.list.nodes@[x].live);
            }
        }
    }

    /// Unmaps the entry the address `va` and the level `level` name in the space of the capability at
    /// index `slot` of the table at `root`. Level 1 is the only level accepted. All of these come from
    /// user space, and a refusal changes nothing. See design/syscall-abi-in-registers/.
    pub fn unmap_at(&mut self, root: usize, slot: usize, va: u64, level: u64, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Unmapped>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + UNMAP_AT_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            ret is Some == old(self).can_unmap_at(root, slot, va, level),
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> Self::page_unmapped(*old(self), *final(self), root, slot, va, level, ret->0),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        if level != 1 || !entry_named(va, level) {
            return None;
        }
        let (l4, l3, l2, l1) = address_indices(va);
        self.unmap(root, slot, l4, l3, l2, l1, Tracked(steps))
    }

    /// Unmaps entry `l1` of the level 1 table the path reaches in the space named at index `slot`. The
    /// index and the path come from user space, so either can be refused, and a refusal changes nothing.
    pub fn unmap(&mut self, root: usize, slot: usize, l4: usize, l3: usize, l2: usize, l1: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Unmapped>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + UNMAP_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            (ret is Some) == old(self).can_unmap(root, slot, SpaceKind::Process, SpacePath { l4, l3, l2, l1 }),
            final(self).spaces.loaded == old(self).spaces.loaded,
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> Self::unmap_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1 }),
            ret is Some ==> Self::unmapped_read(*old(self), root, slot, SpacePath { l4, l3, l2, l1 }, ret->0),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        self.unmap_kind(root, slot, SpaceKind::Process, l4, l3, l2, l1, Tracked(steps))
    }

    /// unmap, in a space that must be of this kind.
    #[verifier::spinoff_prover]
    pub fn unmap_kind(&mut self, root: usize, slot: usize, kind: SpaceKind, l4: usize, l3: usize, l2: usize, l1: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Unmapped>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + UNMAP_KIND_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            (ret is Some) == old(self).can_unmap(root, slot, kind, SpacePath { l4, l3, l2, l1 }),
            final(self).spaces.loaded == old(self).spaces.loaded,
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> Self::unmap_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1 }),
            ret is Some ==> Self::unmapped_read(*old(self), root, slot, SpacePath { l4, l3, l2, l1 }, ret->0),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        match self.unmap_entry(root, slot, kind, l4, l3, l2, l1, Tracked(steps)) {
            Some((s, r)) => {
                let ghost mid = *self;
                self.send_flush(s, Ghost(pre.flush_ipis@), Tracked(steps));
                proof {
                    pre.lemma_flush_targets(s);
                    assert(mid.flush_targets(s) == pre.flush_targets(s));
                    Self::lemma_flush_frame(pre, mid, *self, root, slot, SpacePath { l4, l3, l2, l1 });
                }
                Some(r)
            },
            None => None,
        }
    }

    /// The flush targets of space s are exactly the cores that loaded it, so each core that may hold an
    /// entry of s is among them.
    pub proof fn lemma_flush_targets(&self, s: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
        ensures
            forall|d: usize| #[trigger] self.flush_targets(s).contains(d) <==> d < NUM_CPUS && self.loaded(d as int, s),
            forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == s && #[trigger] self.core_may_hold(d, e)
                ==> self.flush_targets(s).contains(d as usize),
    {
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        assert forall|d: usize| #[trigger] self.flush_targets(s).contains(d) <==> d < NUM_CPUS && self.loaded(d as int, s) by {
            lemma_listed_cores(self.spaces.loaded@[s].value().list, NUM_CPUS as int, d);
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == s && #[trigger] self.core_may_hold(d, e)
            implies self.flush_targets(s).contains(d as usize) by {
            self.lemma_may_hold_loaded(d, e);
            lemma_listed_cores(self.spaces.loaded@[s].value().list, NUM_CPUS as int, d as usize);
        }
    }

    /// A change to the flush record alone keeps what clearing the entry left.
    pub proof fn lemma_flush_frame(pre: Self, mid: Self, post: Self, root: usize, slot: usize, p: SpacePath)
        requires
            Self::entry_unmapped(pre, mid, root, slot, p),
            post == (CapKernel { flush_ipis: post.flush_ipis, ..mid }),
        ensures
            Self::entry_unmapped(pre, post, root, slot, p),
            post.view() == mid.view(),
    {
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let t = walk_table(tree, pre.payload_of(pre.tables.node_of(root, slot)).base, p)->0;
        let node = mapping_node(t, p.l1);
        let pages = record_pages(pre.mappings@[node]);
        assert(tree_of(&post.table_pages, &post.spaces) == tree_of(&mid.table_pages, &mid.spaces));
        assert(Self::mapping_unlinked(pre, post, node));
        assert(post.cores == mid.cores && post.iommus == mid.iommus && post.stale_epoch == mid.stale_epoch && post.blocks == mid.blocks);
        if post.flush_awaited() {
            if exists|c: int| 0 <= c < NUM_CPUS && has_loaded(#[trigger] post.cores@[c]) {
                let c = choose|c: int| 0 <= c < NUM_CPUS && has_loaded(#[trigger] post.cores@[c]);
                assert(has_loaded(mid.cores@[c]));
            } else {
                let i = choose|i: int| 0 <= i < NUM_IOMMUS && #[trigger] post.iommu_present(i);
                assert(mid.iommu_present(i));
            }
            assert(mid.flush_awaited());
        }
        assert forall|g: usize| #[trigger] pages.contains(g) && post.flush_awaited() implies !post.acknowledged(g) by {
            assert(!mid.acknowledged(g));
            if post.acknowledged(g) {
                Self::lemma_acknowledged_kept(post, mid, g);
            }
        }
        assert(Self::mapping_stale_noted(pre, post, node));
        assert(Self::mappings_shrunk(pre, post));
        assert(post.view() == mid.view());
    }

    /// Records a flush IPI, after those in sent, to each core on space s's list of cores: one load of the
    /// list and a bounded loop over the cores. The send is ghost: see design/flush-without-waiting/.
    pub(crate) fn send_flush(&mut self, s: usize, Ghost(sent): Ghost<Seq<usize>>, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).spaces.roots@.contains_key(s),
        ensures
            final(steps).count <= old(steps).count + SEND_FLUSH_STEPS,
            final(self).wf(),
            *final(self) == (CapKernel { flush_ipis: Ghost(sent + old(self).flush_targets(s)), ..*old(self) }),
    {
        let ghost pre = *self;
        proof {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
        }
        let list = PPtr::<SpaceCores>::from_usize(s + SPACE_CORES_PAGE * PAGE_SZ).borrow(
            Tracked(self.spaces.loaded.borrow().tracked_borrow(s)),
        ).list;
        self.flush_ipis = send_to_listed(list, Ghost(sent), Tracked(steps));
        proof {
            Self::lemma_tlb_same(pre, *self);
        }
    }

    /// Clears the entry for unmap_kind and returns the space it was in and what the unmap returns.
    fn unmap_entry(&mut self, root: usize, slot: usize, kind: SpaceKind, l4: usize, l3: usize, l2: usize, l1: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<(usize, Unmapped)>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + UNMAP_ENTRY_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            ret is Some == old(self).can_unmap(root, slot, kind, SpacePath { l4, l3, l2, l1 }),
            final(self).spaces == old(self).spaces,
            final(self).processes == old(self).processes,
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> {
                &&& (ret->0).0 == old(self).payload_of(old(self).tables.node_of(root, slot)).base
                &&& old(self).spaces.roots@.contains_key((ret->0).0)
                &&& Self::entry_unmapped(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1 })
                &&& Self::unmapped_read(*old(self), root, slot, SpacePath { l4, l3, l2, l1 }, (ret->0).1)
            },
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        let ghost p = SpacePath { l4, l3, l2, l1 };
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (n, space) = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found,
            None => { return None; },
        };
        proof {
            pre.lemma_slot(root, slot);
            assert(space == pre.payload_of(n));
        }
        let n_node = self.list.get(n);
        let n_kind = match n_node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !n_node.live || !n_kind || !may_write_space(&space) {
            return None;
        }
        proof {
            assert(pre.is_cap(n));
            pre.lemma_written_space(n);
            pre.lemma_root_table(space.base);
        }
        if self.is_cap_dead(n, space) {
            return None;
        }
        let s = space.base;
        if !same_kind(self.space_kind(s), kind) {
            return None;
        }
        let t3 = match self.table_step(s, true, l4) {
            Some(t) => t,
            None => { return None; },
        };
        let t2 = match self.table_step(t3, false, l3) {
            Some(t) => t,
            None => { return None; },
        };
        let t = match self.table_step(t2, false, l2) {
            Some(t) => t,
            None => { return None; },
        };
        proof {
            assert(walk_table(tree, s, p) == Some(t));
            assert(tree.record(t).level == 1);
        }
        if l1 >= ENTRIES {
            return None;
        }
        let current = self.table_entry(t, false, l1);
        if !current.perm.present {
            return None;
        }
        if self.flush_epoch == usize::MAX {
            return None;
        }
        let node = self.map_node(t, l1);
        proof {
            assert(frame_slot(tree, t, l1));
            assert(pre.mappings@.contains_key(node));
            pre.lemma_mapping_node(node);
        }
        let word = self.unlink_mapping_node(node, Tracked(steps));
        proof {
            Self::lemma_mapping_view_same(pre, *self, node);
            lemma_sheds_shares_discharges_local(pre.view(), self.view(), root);
            Self::lemma_unlinked_shrunk(pre, *self, node);
            Self::lemma_unlinked_shares(pre, *self, node, t, l1);
        }
        let status = usize2page_entry_status(word, 1);
        Some((s, Unmapped {
            accessed: status.accessed,
            dirty: status.dirty,
            accessed_maintained: maintains_accessed(),
            dirty_maintained: maintains_dirty(),
            read: Ghost(word),
        }))
    }
}

} // verus!
