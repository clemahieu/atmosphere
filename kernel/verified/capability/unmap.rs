//! Unmapping one 4K entry of a space by its address. The entry's mapping node sits at a fixed index in
//! its table page's block, so it is found in constant time, and it goes through the arm revoke uses: the
//! entry clears, the unmap's staleness is recorded and the frame's reference drops. See
//! design/address-spaces-as-objects/ and design/flush-without-waiting/.
use vstd::prelude::*;

verus! {

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

    /// Unmaps entry `l1` of the level 1 table the path reaches in the space named at index `slot`. The
    /// index and the path come from user space, so either can be refused, and a refusal changes nothing.
    pub fn unmap(&mut self, root: usize, slot: usize, l4: usize, l3: usize, l2: usize, l1: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            ret == old(self).can_unmap(root, slot, SpaceKind::Process, SpacePath { l4, l3, l2, l1 }),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret ==> Self::unmap_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1 }),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        self.unmap_kind(root, slot, SpaceKind::Process, l4, l3, l2, l1)
    }

    /// unmap, in a space that must be of this kind.
    pub fn unmap_kind(&mut self, root: usize, slot: usize, kind: SpaceKind, l4: usize, l3: usize, l2: usize, l1: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret == old(self).can_unmap(root, slot, kind, SpacePath { l4, l3, l2, l1 }),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret ==> Self::unmap_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1 }),
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
            None => { return false; },
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
            return false;
        }
        proof {
            assert(pre.is_cap(n));
            pre.lemma_written_space(n);
            pre.lemma_root_table(space.base);
        }
        if self.is_cap_dead(n, space) {
            return false;
        }
        let s = space.base;
        if !same_kind(self.space_kind(s), kind) {
            return false;
        }
        let t3 = match self.table_step(s, true, l4) {
            Some(t) => t,
            None => { return false; },
        };
        let t2 = match self.table_step(t3, false, l3) {
            Some(t) => t,
            None => { return false; },
        };
        let t = match self.table_step(t2, false, l2) {
            Some(t) => t,
            None => { return false; },
        };
        proof {
            assert(walk_table(tree, s, p) == Some(t));
            assert(tree.record(t).level == 1);
        }
        if l1 >= 512 {
            return false;
        }
        let current = self.table_entry(t, false, l1);
        if !current.perm.present {
            return false;
        }
        if self.flush_epoch == usize::MAX {
            return false;
        }
        let node = self.map_node(t, l1);
        proof {
            assert(frame_slot(tree, t, l1));
            assert(pre.mappings@.contains_key(node));
            pre.lemma_mapping_node(node);
        }
        self.unlink_mapping_node(node);
        proof {
            Self::lemma_mapping_view_same(pre, *self, node);
            Self::lemma_unlinked_shrunk(pre, *self, node);
        }
        true
    }
}

} // verus!
