//! Deriving a capability, the only way to share one: the child's rights and range lie within its
//! parent's and its depth is one greater, so whoever derived it can always revoke it. The child goes
//! in a free slot of the caller's table, or of the table of a process the caller controls, which is
//! a grant through control. See design/sharing-by-derive/ and design/process-holds-capabilities/.
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

use crate::capability::device::*;
use crate::capability::mapping::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::position::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::process::*;
use crate::capability::thread::*;
use crate::capability::view::*;

/// The child a derive from `parent` makes.
pub open spec fn child_of(parent: Payload, rights: u32, base: usize, order: u8) -> Payload {
    Payload { kind: parent.kind, order, rights, base, badge: parent.badge, reserved: 0 }
}

/// A block of this order at this base is a whole block lying within the parent's.
pub open spec fn block_within(base: usize, order: u8, parent: Payload) -> bool {
    &&& order <= parent.order
    &&& parent.base <= base
    &&& base as int % block_bytes(order) == 0
    &&& base as int + block_bytes(order) <= parent.base as int + block_bytes(parent.order)
}

/// The child's rights and block lie within the parent's. Only a block of memory can be narrowed: any
/// other object is its block's base. And control reads a capability's name alone, so a child that
/// keeps control keeps the parent's block.
pub open spec fn narrows(child: Payload, parent: Payload) -> bool {
    &&& child.rights & !parent.rights == 0
    &&& block_within(child.base, child.order, parent)
    &&& (child.base != parent.base || child.order != parent.order) ==> {
        &&& parent.kind is Untyped || parent.kind is Frame
        &&& child.rights & right_bit(Right::Control) == 0
    }
}

/// A block of this order, in bytes, in constant time.
pub fn order_bytes(order: u8) -> (ret: usize)
    requires
        order <= MAX_ORDER,
    ensures
        ret as int == block_bytes(order),
        0 < ret <= NODE_SPACE,
{
    proof {
        lemma_pow2_pos(order as nat);
        lemma_pow2_order(order);
        lemma_usize_shl_is_mul(4096, order as usize);
    }
    4096usize << (order as usize)
}

/// A block of any order fits in the address space.
proof fn lemma_pow2_order(order: u8)
    requires
        order <= MAX_ORDER,
    ensures
        pow2(order as nat) * 4096 <= NODE_SPACE,
{
    lemma2_to64_rest();
    if order < MAX_ORDER {
        lemma_pow2_strictly_increases(order as nat, MAX_ORDER as nat);
    }
}

/// Decides whether a block lies within a capability's, in constant time. Base and order come from
/// user space.
pub fn is_block_within(parent: Payload, base: usize, order: u8) -> (ret: bool)
    requires
        payload_wf(parent),
    ensures
        ret == block_within(base, order, parent),
        ret ==> order <= MAX_ORDER,
        ret ==> base as int % block_bytes(order) == 0,
        ret ==> base as int + block_bytes(order) <= NODE_SPACE as int,
{
    if order > parent.order || base < parent.base || base >= NODE_SPACE {
        proof {
            lemma_pow2_pos(order as nat);
        }
        return false;
    }
    let size = order_bytes(order);
    let parent_size = order_bytes(parent.order);
    base + size <= parent.base + parent_size && base % size == 0
}

/// Decides whether a child with these fields may be derived from `parent`, in constant time. All of
/// rights, base and order come from user space.
fn may_derive(parent: Payload, rights: u32, base: usize, order: u8) -> (ret: bool)
    requires
        payload_wf(parent),
    ensures
        ret <==> narrows(child_of(parent, rights, base, order), parent),
        ret ==> payload_wf(child_of(parent, rights, base, order)),
{
    if rights & !parent.rights != 0 || !is_block_within(parent, base, order) {
        return false;
    }
    if base != parent.base || order != parent.order {
        let block = match parent.kind {
            CapKind::Untyped | CapKind::Frame => true,
            _ => false,
        };
        if !block || rights & 128 != 0 {
            return false;
        }
    }
    true
}

impl CapKernel {
    /// The refusals of a derive from index from of the table at src into index to of the table at dst:
    /// an index that names no slot, a parent that is no capability, a device's, the console's or
    /// power's, a dead process's or thread's, or at the deepest depth, a child's slot in use, or a child
    /// that does not narrow its parent.
    pub open spec fn can_derive_between(&self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8) -> bool {
        let parent = self.tables.node_of(src, from);
        let child = self.tables.node_of(dst, to);
        &&& self.tables.has_slot(&self.list, src, from)
        &&& self.tables.has_slot(&self.list, dst, to)
        &&& self.is_cap(parent)
        &&& names_block(self.payload_of(parent).kind)
        &&& !self.cap_dead(parent)
        &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
        &&& !self.list.nodes@[child as int].live
        &&& narrows(child_of(self.payload_of(parent), rights, base, order), self.payload_of(parent))
        &&& (self.payload_of(parent).kind is Frame || self.payload_of(parent).kind is Space
            || self.payload_of(parent).kind is Thread || self.payload_of(parent).kind is Process) ==>
            block_refs(&self.blocks, block_ref(&self.blocks, self.payload_of(parent).base / 4096)) != usize::MAX
    }

    /// The refusals of a derive from index from of the caller's table, at root, into a position: one
    /// in no table, or in the table of a dead process, to which nothing is given since it cannot use
    /// it, and then a derive's between the two tables.
    pub open spec fn can_derive_at(&self, root: usize, from: usize, to: Position, rights: u32, base: usize, order: u8) -> bool {
        let dst = self.table_at(root, to.through);
        &&& dst is Some
        &&& to.through is Some ==> !self.processes.records@[dst->0].value().dead
        &&& self.can_derive_between(root, from, dst->0, to.index, rights, base, order)
    }

    /// What a derive from the capability at index from of the table at src into the empty index to of
    /// the table at dst did: the derive was allowed, and the child, in dst's table, holds the parent's
    /// kind with these rights and this block, which narrow the parent's, one depth below it as its
    /// child.
    pub open spec fn cap_derived_between(pre: Self, post: Self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8) -> bool {
        let parent = pre.tables.node_of(src, from);
        let child = pre.tables.node_of(dst, to);
        &&& pre.can_derive_between(src, from, dst, to, rights, base, order)
        &&& pre.view().holds(src, parent)
        &&& post.view().holds(dst, child)
        &&& !pre.list.nodes@[child as int].live
        &&& narrows(post.payload_of(child), pre.payload_of(parent))
        &&& post.payload_of(child) == child_of(pre.payload_of(parent), rights, base, order)
        &&& post.list.is_child(parent, child)
        &&& post.list.nodes@[child as int].depth == pre.list.nodes@[parent as int].depth + 1
        &&& post.list.nodes@[child as int].depth <= MAX_DEPTH
    }

    /// What a derive into a position is to reach: a local step in the caller's own table, and through a
    /// process capability a placement through it of a child of the caller's capability.
    pub open spec fn derive_effect(&self, root: usize, from: usize, to: Position) -> Effect {
        match to.through {
            None => Effect::Local,
            Some(cap) => Effect::Place { cap: self.tables.node_of(root, cap), from: self.tables.node_of(root, from) },
        }
    }

    /// What a derive from the capability at index from of the caller's table, at root, into the empty
    /// position to did: the derive was allowed, the child is in the position's table, and the step
    /// discharges the derive's effect there, a local step in the caller's own table.
    pub open spec fn cap_derived_at(pre: Self, post: Self, root: usize, from: usize, to: Position, rights: u32, base: usize, order: u8) -> bool {
        &&& pre.can_derive_at(root, from, to, rights, base, order)
        &&& Self::cap_derived_between(pre, post, root, from, pre.table_at(root, to.through)->0, to.index, rights, base, order)
        &&& discharges(pre.view(), post.view(), root, pre.derive_effect(root, from, to))
    }

    /// Derives the capability at index `from` of the caller's table, at `root`, into the empty position
    /// `to`: an index of the caller's table, or of the table of a process the caller controls, which
    /// must not be dead. The index, the position, rights, base and order come from user space, so any
    /// of them can be refused, and a refusal changes nothing.
    pub fn derive(&mut self, root: usize, from: usize, to: Position, rights: u32, base: usize, order: u8) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).spaces.loaded == old(self).spaces.loaded,
            final(self).tables.roots == old(self).tables.roots,
            ret ==> Self::derive_step(*old(self), *final(self), old(self).tables.node_of(old(self).table_at(root, to.through)->0, to.index)),
            ret && !tracked_kind(old(self).payload_of(old(self).tables.node_of(root, from)).kind) ==> {
                &&& final(self).blocks == old(self).blocks
                &&& final(self).holders == old(self).holders
                &&& final(self).spaces.holders == old(self).spaces.holders
                &&& final(self).threads == old(self).threads
                &&& final(self).processes == old(self).processes
            },
            Self::same_tree(*old(self), *final(self)),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::cap_derived_at(*old(self), *final(self), root, from, to, rights, base, order),
            ret == old(self).can_derive_at(root, from, to, rights, base, order),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let dst = match self.find_table(root, to.through) {
            Some(table) => table,
            None => { return false; },
        };
        if let Some(cap) = to.through {
            proof {
                pre.lemma_process_cap(pre.tables.node_of(root, cap));
            }
            if self.is_process_dead(dst) {
                return false;
            }
        }
        let ret = self.derive_between(root, from, dst, to.index, rights, base, order);
        if ret {
            proof {
                match to.through {
                    None => {
                        Self::lemma_derive_discharges(pre, *self, root, from, to.index);
                    },
                    Some(cap) => {
                        pre.lemma_slot(root, cap);
                        Self::lemma_derive_into_discharges(pre, *self, root, pre.tables.node_of(root, cap), from, dst, to.index);
                    },
                }
            }
        }
        ret
    }

    /// Derives the capability at index `from` of the table at `src` into the empty index `to` of the
    /// table at `dst`: a derive when they are one table, a placement's step when not. A refusal changes
    /// nothing.
    fn derive_between(&mut self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(src),
            old(self).tables.roots@.contains_key(dst),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).spaces.loaded == old(self).spaces.loaded,
            final(self).tables.roots == old(self).tables.roots,
            ret && !tracked_kind(old(self).payload_of(old(self).tables.node_of(src, from)).kind) ==> {
                &&& final(self).blocks == old(self).blocks
                &&& final(self).holders == old(self).holders
                &&& final(self).spaces.holders == old(self).spaces.holders
                &&& final(self).threads == old(self).threads
                &&& final(self).processes == old(self).processes
            },
            Self::same_tree(*old(self), *final(self)),
            !ret ==> *final(self) == *old(self),
            ret == old(self).can_derive_between(src, from, dst, to, rights, base, order),
            ret ==> {
                let parent = old(self).tables.node_of(src, from);
                let child = old(self).tables.node_of(dst, to);
                &&& Self::cap_derived_between(*old(self), *final(self), src, from, dst, to, rights, base, order)
                &&& Self::derive_step(*old(self), *final(self), child)
                &&& final(self).list.parent@ == old(self).list.parent@.insert(child, parent)
            },
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let (parent, payload) = match self.tables.lookup(&self.list, src, from) {
            Some(found) => found,
            None => { return false; },
        };
        let child = match self.tables.lookup(&self.list, dst, to) {
            Some(found) => found.0,
            None => { return false; },
        };
        let node = self.list.get(parent);
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !node.live || !kind_ok || node.depth >= MAX_DEPTH || self.list.get(child).live {
            return false;
        }
        proof {
            pre.lemma_slot(src, from);
            assert(pre.tables.is_cap(&pre.list, parent));
            assert(payload == pre.payload_of(parent));
            if payload.kind is Space {
                pre.lemma_space_cap(parent);
            }
            if payload.kind is Thread {
                pre.lemma_thread_cap(parent);
            }
            if payload.kind is Process {
                pre.lemma_process_cap(parent);
            }
        }
        if self.is_cap_dead(parent, payload) {
            return false;
        }
        // A device is bound to one space at a time, so its capability has no children: it moves instead.
        // The console's and power's name no block for a child to narrow.
        if !is_block_kind(payload.kind) {
            return false;
        }
        if !may_derive(payload, rights, base, order) {
            return false;
        }
        let counted = match payload.kind {
            CapKind::Frame | CapKind::Space | CapKind::Thread | CapKind::Process => true,
            _ => false,
        };
        // A derived frame, space, thread or process holds a reference on the block its parent lies in.
        let block = if counted {
            let br = locate(&self.blocks, payload.base / 4096);
            if !add_block_ref(&mut self.blocks, br) {
                return false;
            }
            Some(br)
        } else {
            None
        };
        proof {
            self.list.lemma_seq_fits();
            self.list.lemma_valid_bound(parent);
            self.list.lemma_valid_bound(child);
        }
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
            // The new node is a slot, never the leaf's hidden node, so the slot is still found.
            pre.lemma_slot(dst, to);
            let leaf = pre.tables.leaf(dst, index_entry(to));
            pre.tables.lemma_leaf(&pre.list, leaf);
            lemma_slot_in_leaf(leaf, 0);
            pre.list.lemma_valid_bound(leaf);
            assert(self.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
        }
        self.tables.set_payload(
            &self.list,
            dst,
            to,
            Payload { kind: payload.kind, order, rights, base, badge: payload.badge, reserved: 0 },
        );
        match block {
            Some(br) => {
                match payload.kind {
                    CapKind::Space => {
                        self.spaces.holders = Ghost(pre.spaces.holders@.insert(base, pre.spaces.holders@[base].insert(child)));
                    },
                    CapKind::Thread => {
                        self.threads.holders = Ghost(pre.threads.holders@.insert(base, pre.threads.holders@[base].insert(child)));
                    },
                    CapKind::Process => {
                        self.processes.holders = Ghost(pre.processes.holders@.insert(base, pre.processes.holders@[base].insert(child)));
                    },
                    _ => { self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].insert(child))); },
                }
            },
            None => {},
        }
        proof {
            let post = *self;
            pre.lemma_slot(src, from);
            pre.lemma_slot(dst, to);
            assert(post.payload_of(child) == child_of(payload, rights, base, order));
            let parent_rights = payload.rights;
            assert(rights & !parent_rights == 0 && rights & 128 != 0 ==> parent_rights & 128 != 0) by (bit_vector);
            assert(control_named(pre.tables.payload_of(parent)));
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_hidden_frame(pre, post, child, child);
            Self::lemma_table_nodes_caps_frame(pre, post, child, child);
            Self::lemma_space_nodes_caps_frame(pre, post, child, child);
            Self::lemma_bindings_caps_frame(pre, post, child, child);
            Self::lemma_derive_holders(pre, post, parent, child, block);
            Self::lemma_devices_caps_frame(pre, post, child, child);
            lemma_parents_derived(pre.list, post.list, parent, child);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_bound_threads_same(pre, post);
            assert(pre.view().holds(src, parent));
            assert(post.is_cap(child));
            assert(post.view().holds(dst, child));
        }
        true
    }

    /// The holders after a derive: a frame child joins its parent's block, a space or thread child
    /// joins its parent's object, and any other child holds nothing. With them, what the blocks owe the rest of
    /// the invariant.
    proof fn lemma_derive_holders(pre: Self, post: Self, parent: usize, child: usize, block: Option<BlockRef>)
        requires
            Self::derive_step(pre, post, child),
            pre.is_cap(parent),
            post.is_cap(child),
            narrows(post.payload_of(child), pre.payload_of(parent)),
            post.payload_of(child).kind == pre.payload_of(parent).kind,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            block is Some == (pre.payload_of(parent).kind is Frame || pre.payload_of(parent).kind is Space
                || pre.payload_of(parent).kind is Thread || pre.payload_of(parent).kind is Process),
            block is Some ==> {
                let br = block->0;
                &&& br == block_ref(&pre.blocks, pre.payload_of(parent).base / 4096)
                &&& block_refs(&pre.blocks, br) < usize::MAX
                &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
            },
            block is Some && pre.payload_of(parent).kind is Frame ==> {
                &&& post.holders@ == pre.holders@.insert(block->0, pre.holders@[block->0].insert(child))
                &&& post.spaces == pre.spaces
                &&& post.threads == pre.threads
                &&& post.processes == pre.processes
            },
            block is Some && pre.payload_of(parent).kind is Space ==> {
                let s = pre.payload_of(parent).base;
                &&& post.holders == pre.holders
                &&& post.spaces.roots == pre.spaces.roots
                &&& post.spaces.records == pre.spaces.records
                &&& post.spaces.loaded == pre.spaces.loaded
                &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
                &&& post.spaces.bound == pre.spaces.bound
                &&& post.spaces.holders@ == pre.spaces.holders@.insert(s, pre.spaces.holders@[s].insert(child))
                &&& post.threads == pre.threads
                &&& post.processes == pre.processes
            },
            block is Some && pre.payload_of(parent).kind is Thread ==> {
                let t = pre.payload_of(parent).base;
                &&& post.holders == pre.holders
                &&& post.spaces == pre.spaces
                &&& post.threads.records == pre.threads.records
                &&& post.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].insert(child))
                &&& post.processes == pre.processes
            },
            block is Some && pre.payload_of(parent).kind is Process ==> {
                let p = pre.payload_of(parent).base;
                &&& post.holders == pre.holders
                &&& post.spaces == pre.spaces
                &&& post.threads == pre.threads
                &&& post.processes.records == pre.processes.records
                &&& post.processes.spare == pre.processes.spare
                &&& post.processes.bound == pre.processes.bound
                &&& post.processes.holders@ == pre.processes.holders@.insert(p, pre.processes.holders@[p].insert(child))
            },
            block is None ==> post.blocks == pre.blocks && post.holders == pre.holders && post.spaces == pre.spaces
                && post.threads == pre.threads && post.processes == pre.processes,
            post.table_pages == pre.table_pages,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        pre.lemma_slot_not_owned(child);
        Self::lemma_same_leaf_nodes(pre, post, child, child);
        pre.lemma_slot_not_table_page(child);
        Self::lemma_same_table_nodes(pre, post, child, child);
        let pp = pre.payload_of(parent);
        let cp = post.payload_of(child);
        match block {
            Some(br) => {
                if pp.kind is Frame {
                    lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, parent);
                    assert(frame_in_block(block_ref(&pre.blocks, pp.base / 4096), pp));
                    lemma_child_same_block(&pre.blocks, pp, cp);
                    lemma_holders_frame_added(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, child, br);
                    lemma_zeroing_typed_refs_changed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert forall|x: BlockRef| #[trigger] post.holders@.contains_key(x) == pre.holders@.contains_key(x) by {}
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_refs_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, post.holders@, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_refs_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    if let BlockRef::Small(x) = br {
                        assert(pre.blocks.pages@[x as int].object is Frame);
                    }
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                } else if pp.kind is Space {
                    // A space is its block's base, so the child names the parent's space.
                    pre.lemma_space_cap(parent);
                    let s = pp.base;
                    assert(br == BlockRef::Small(s / 4096));
                    assert(cp.base == s);
                    assert(cp.order == 3);
                    lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                    assert(!pre.holders@.contains_key(br)) by {
                        if pre.holders@.contains_key(br) {
                            assert(pre.blocks.pages@[(s / 4096) as int].object is Frame);
                        }
                    }
                    lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, s / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, s / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, s / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, s / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    Self::lemma_spaces_holder_added(pre, post, child, s);
                    lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                } else if pp.kind is Thread {
                    // A thread is its block's base, so the child names the parent's thread.
                    pre.lemma_thread_cap(parent);
                    let t = pp.base;
                    assert(br == BlockRef::Small(t / 4096));
                    assert(cp.base == t);
                    assert(cp.order == THREAD_ORDER);
                    lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                    assert(!pre.holders@.contains_key(br)) by {
                        if pre.holders@.contains_key(br) {
                            assert(pre.blocks.pages@[(t / 4096) as int].object is Frame);
                        }
                    }
                    lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, t / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, t / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, t / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, t / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    Self::lemma_threads_holder_added(pre, post, child, t);
                    lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                } else {
                    // A process is its block's base, so the child names the parent's process.
                    pre.lemma_process_cap(parent);
                    let p = pp.base;
                    assert(br == BlockRef::Small(p / 4096));
                    assert(cp.base == p);
                    assert(cp.order == PROCESS_ORDER);
                    lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                    assert(!pre.holders@.contains_key(br)) by {
                        if pre.holders@.contains_key(br) {
                            assert(pre.blocks.pages@[(p / 4096) as int].object is Frame);
                        }
                    }
                    lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, p / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, p / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, p / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, p / 4096, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    Self::lemma_processes_holder_added(pre, post, child, p);
                }
            },
            None => {
                lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
                lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
                lemma_spaces_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks);
                lemma_threads_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks);
                lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
            },
        }
    }

    /// What a derive does to the fields the view reads.
    pub open spec fn derive_step(pre: Self, post: Self, child: usize) -> bool {
        &&& Self::caps_frame(pre, post, child, child)
        &&& !pre.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].kind is Capability
    }

    /// Every capability still names a block.
    pub proof fn lemma_derive_caps_wf(pre: Self, post: Self, child: usize)
        requires
            Self::derive_step(pre, post, child),
            cap_wf(post.payload_of(child)),
            control_named(post.payload_of(child)),
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
    {
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) implies {
            &&& cap_wf(post.tables.payload_of(n))
            &&& control_named(post.tables.payload_of(n))
        } by {
            if n != child {
                Self::lemma_caps_frame(pre, post, child, child, n);
                assert(post.is_cap(n));
                assert(pre.tables.is_cap(&pre.list, n));
            }
        }
    }

    /// What a step that makes one capability, in a slot, does to the others: nothing. A derive is one,
    /// and so is a retype that adds node pages, which keeps every node the list held but says nothing
    /// of the kinds in the pages it adds.
    pub open spec fn adds_cap(pre: Self, post: Self, child: usize) -> bool {
        &&& pre.wf()
        &&& post.tables.owner == pre.tables.owner
        &&& forall|x: usize| #![trigger post.is_cap(x)] #![trigger pre.is_cap(x)]
            x != child ==> post.is_cap(x) == pre.is_cap(x)
        &&& forall|x: usize| x != child && #[trigger] pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x)
        &&& !pre.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].kind is Capability
    }

    pub proof fn lemma_derive_step_adds_cap(pre: Self, post: Self, child: usize)
        requires
            Self::derive_step(pre, post, child),
        ensures
            Self::adds_cap(pre, post, child),
    {
        assert forall|x: usize| #![trigger post.is_cap(x)] #![trigger pre.is_cap(x)]
            x != child implies post.is_cap(x) == pre.is_cap(x) by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        assert forall|x: usize| x != child && #[trigger] pre.is_cap(x) implies post.payload_of(x) == pre.payload_of(x) by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
    }

    /// The view of a step that adds one child, in a slot of the table at dst, under a capability held
    /// in the table at src, covering only what its parent does.
    #[verifier::spinoff_prover]
    pub proof fn lemma_places_node_view(pre: Self, post: Self, src: usize, from: usize, dst: usize, to: usize)
        requires
            Self::adds_cap(pre, post, pre.tables.node_of(dst, to)),
            pre.tables.has_slot(&pre.list, src, from),
            pre.tables.has_slot(&pre.list, dst, to),
            pre.is_cap(pre.tables.node_of(src, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(dst, to), pre.tables.node_of(src, from)),
            ({
                let cp = post.payload_of(pre.tables.node_of(dst, to));
                let pp = pre.payload_of(pre.tables.node_of(src, from));
                block_within(cp.base, cp.order, pp)
            }),
        ensures
            post.view().holds(dst, pre.tables.node_of(dst, to)),
            places_node(
                pre.view(),
                post.view(),
                src,
                dst,
                pre.tables.node_of(src, from),
                pre.tables.node_of(dst, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
            ),
    {
        // The proof reads the list's part of wf alone; the rest stays folded, out of the solver's search.
        hide(CapKernel::wf);
        assert(pre.list.wf()) by {
            reveal(CapKernel::wf);
        }
        let parent = pre.tables.node_of(src, from);
        let child = pre.tables.node_of(dst, to);
        let (a, b) = (pre.view(), post.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        pre.lemma_slot(src, from);
        pre.lemma_slot(dst, to);
        assert(a.holds(src, parent));
        assert(b.holds(dst, child));
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) by {
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies live(x) by {
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies live(a.parent[x]) by {
            pre.list.lemma_parent_live(x);
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) == (a.held.contains(h) || h == (dst, child)) by {
            if h.1 != child {
                assert(post.is_cap(h.1) == pre.is_cap(h.1));
            }
        }
        assert forall|x: NodeId| x != child implies {
            &&& #[trigger] b.names.contains_key(x) == a.names.contains_key(x)
            &&& b.pages.contains_key(x) == a.pages.contains_key(x)
            &&& a.names.contains_key(x) ==> b.names[x] == a.names[x]
            &&& a.pages.contains_key(x) ==> b.pages[x] == a.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| x != child implies #[trigger] b.rights.contains((x, r)) == a.rights.contains((x, r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        let (cp, pp) = (post.payload_of(child), pre.payload_of(parent));
        assert forall|o: ObjectId| #[trigger] b.covers(child, o) implies a.covers(parent, o) by {
            assert(block_bytes(cp.order) == b.pages[child] * 4096);
            assert(block_bytes(pp.order) == a.pages[parent] * 4096);
        }
        assert forall|o: ObjectId| #[trigger] (b.contents)(o) == (a.contents)(o) by {}
        pre.lemma_slot_bound(parent);
        pre.lemma_slot_bound(child);
        assert(live(parent));
        assert(!live(child));
        assert(b.parent == a.parent.insert(child, parent));
        assert(b.maps == a.maps);
        assert(places_node(a, b, src, dst, parent, child, live));
    }

    /// And has control only with its parent's name.
    pub proof fn lemma_places_child_view(pre: Self, post: Self, src: usize, from: usize, dst: usize, to: usize)
        requires
            Self::adds_cap(pre, post, pre.tables.node_of(dst, to)),
            pre.tables.has_slot(&pre.list, src, from),
            pre.tables.has_slot(&pre.list, dst, to),
            pre.is_cap(pre.tables.node_of(src, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(dst, to), pre.tables.node_of(src, from)),
            ({
                let cp = post.payload_of(pre.tables.node_of(dst, to));
                let pp = pre.payload_of(pre.tables.node_of(src, from));
                &&& block_within(cp.base, cp.order, pp)
                &&& cp.rights & right_bit(Right::Control) != 0 ==> {
                    &&& pp.rights & right_bit(Right::Control) != 0
                    &&& cp.base == pp.base
                }
            }),
        ensures
            post.view().holds(dst, pre.tables.node_of(dst, to)),
            places_child(
                pre.view(),
                post.view(),
                src,
                dst,
                pre.tables.node_of(src, from),
                pre.tables.node_of(dst, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
            ),
    {
        let parent = pre.tables.node_of(src, from);
        let child = pre.tables.node_of(dst, to);
        Self::lemma_places_node_view(pre, post, src, from, dst, to);
        pre.lemma_slot(src, from);
        pre.lemma_slot(dst, to);
    }

    /// What derive's child owes that view: control only with the parent's name, and all its other
    /// rights the parent's too.
    proof fn lemma_derive_discharges(pre: Self, post: Self, root: usize, from: usize, to: usize)
        requires
            Self::derive_step(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(&pre.list, root, from),
            pre.tables.has_slot(&pre.list, root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            narrows(post.payload_of(pre.tables.node_of(root, to)), pre.payload_of(pre.tables.node_of(root, from))),
        ensures
            post.view().holds(root, pre.tables.node_of(root, to)),
            discharges(pre.view(), post.view(), root, Effect::Local),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let (cp, pp) = (post.payload_of(child), pre.payload_of(parent));
        let (child_rights, parent_rights) = (cp.rights, pp.rights);
        assert(child_rights & !parent_rights == 0 && child_rights & 128 != 0 ==> parent_rights & 128 != 0) by (bit_vector);
        assert(right_bit(Right::Control) == 128);
        Self::lemma_derive_step_adds_cap(pre, post, child);
        Self::lemma_places_child_view(pre, post, root, from, root, to);
        lemma_adds_child_discharges(pre.view(), post.view(), root, parent, child, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live);
    }

    /// The view of a derive into a controlled process's table: the caller, holding control over the
    /// process at d through capability c, put a child of the capability at its own index from in the
    /// slot at index to of that process's table. Reach grows only for that process and what controls
    /// it, by what the caller reached.
    proof fn lemma_derive_into_discharges(pre: Self, post: Self, root: usize, c: usize, from: usize, d: usize, to: usize)
        requires
            Self::derive_step(pre, post, pre.tables.node_of(d, to)),
            pre.tables.has_slot(&pre.list, root, from),
            pre.tables.has_slot(&pre.list, d, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(d, to), pre.tables.node_of(root, from)),
            narrows(post.payload_of(pre.tables.node_of(d, to)), pre.payload_of(pre.tables.node_of(root, from))),
            pre.is_cap(c),
            pre.tables.owner@[page_of(c)].0 == root,
            pre.payload_of(c).rights & right_bit(Right::Control) != 0,
            pre.payload_of(c).base == d,
        ensures
            discharges(pre.view(), post.view(), root, Effect::Place { cap: c, from: pre.tables.node_of(root, from) }),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(d, to);
        let (cp, pp) = (post.payload_of(child), pre.payload_of(parent));
        let (child_rights, parent_rights) = (cp.rights, pp.rights);
        assert(child_rights & !parent_rights == 0 && child_rights & 128 != 0 ==> parent_rights & 128 != 0) by (bit_vector);
        assert(right_bit(Right::Control) == 128);
        Self::lemma_derive_step_adds_cap(pre, post, child);
        Self::lemma_places_child_view(pre, post, root, from, d, to);
        let a = pre.view();
        assert(a.holds_right(root, c, Right::Control));
        assert(a.names[c] == d);
        assert(!a.process_of.contains_key(d));
        assert(a.names.contains_key(parent));
        lemma_places_child_discharges(a, post.view(), root, d, c, parent, child, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live);
    }
}

} // verus!
