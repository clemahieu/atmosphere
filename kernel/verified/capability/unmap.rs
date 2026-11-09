//! Unmapping one 4K entry of a space by its address. The entry's mapping node sits at a fixed index in
//! its table page's block, so it is found in constant time, and it goes through the arm revoke uses: the
//! entry clears, the unmap's staleness is recorded and the frame's reference drops. The entry's word is
//! read in the step that clears it, so the accessed and dirty bits the processor set there come back to
//! the caller. See design/address-spaces-as-objects/, design/flush-without-waiting/ and
//! design/arch-module/.
use vstd::prelude::*;

verus! {

use crate::arch::{maintains_accessed, maintains_dirty, PAGE_ENTRY_ACCESSED_MASK, PAGE_ENTRY_DIRTY_MASK};
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::reach::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::define::*;
use crate::pagetable::entry::*;

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
        &&& p.l1 < 512
        &&& tree.entry(t, p.l1).perm.present
        &&& self.flush_epoch < usize::MAX
    }

    /// What an unmap leaves: the entry the path reaches is empty, its mapping node is the only node that
    /// left the list, its record and its frame's reference went with it, its staleness is recorded, and
    /// no capability changed.
    pub open spec fn unmap_done(pre: Self, post: Self, root: usize, slot: usize, p: SpacePath) -> bool {
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
        &&& !post.list.nodes@[node as int].live
        &&& forall|x: int| 0 <= x < NODE_SPACE && x != node ==> #[trigger] post.list.nodes@[x].live == pre.list.nodes@[x].live
        &&& post.list.seq@.len() == pre.list.seq@.len() - 1
        &&& post.view() == pre.view()
    }

    /// What an unmap at path p of the space named at index slot of the table at root returned: the word
    /// read decodes to the entry the path reached, the bits are that word's accessed and dirty bits as
    /// read before it was cleared, and the two facts are this target's.
    pub open spec fn unmapped_read(pre: Self, root: usize, slot: usize, p: SpacePath, r: Unmapped) -> bool {
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let t = walk_table(tree, pre.payload_of(pre.tables.node_of(root, slot)).base, p)->0;
        &&& spec_usize2page_entry(r.read@) == tree.entry(t, p.l1)
        &&& r.accessed == usize2accessed(r.read@)
        &&& r.dirty == usize2dirty(r.read@)
        &&& r.accessed_maintained == maintains_accessed()
        &&& r.dirty_maintained == maintains_dirty()
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

    /// Unmaps the entry the address `va` and the level `level` name in the space of the capability at
    /// index `slot` of the table at `root`. Level 1 is the only level accepted. All of these come from
    /// user space, and a refusal changes nothing. See design/syscall-abi-in-registers/.
    pub fn unmap_at(&mut self, root: usize, slot: usize, va: u64, level: u64) -> (ret: Option<Unmapped>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> Self::page_unmapped(*old(self), *final(self), root, slot, va, level, ret->0),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        if level != 1 || !entry_named(va, level) {
            return None;
        }
        let (l4, l3, l2, l1) = address_indices(va);
        self.unmap(root, slot, l4, l3, l2, l1)
    }

    /// Unmaps entry `l1` of the level 1 table the path reaches in the space named at index `slot`. The
    /// index and the path come from user space, so either can be refused, and a refusal changes nothing.
    pub fn unmap(&mut self, root: usize, slot: usize, l4: usize, l3: usize, l2: usize, l1: usize) -> (ret: Option<Unmapped>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
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
        self.unmap_kind(root, slot, SpaceKind::Process, l4, l3, l2, l1)
    }

    /// unmap, in a space that must be of this kind.
    pub fn unmap_kind(&mut self, root: usize, slot: usize, kind: SpaceKind, l4: usize, l3: usize, l2: usize, l1: usize) -> (ret: Option<Unmapped>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
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
        if l1 >= 512 {
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
        let word = self.unlink_mapping_node(node);
        proof {
            Self::lemma_mapping_view_same(pre, *self, node);
            Self::lemma_unlinked_shrunk(pre, *self, node);
        }
        Some(Unmapped {
            accessed: word & PAGE_ENTRY_ACCESSED_MASK as usize != 0,
            dirty: word & PAGE_ENTRY_DIRTY_MASK as usize != 0,
            accessed_maintained: maintains_accessed(),
            dirty_maintained: maintains_dirty(),
            read: Ghost(word),
        })
    }
}

} // verus!
