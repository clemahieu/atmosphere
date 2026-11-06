//! Deriving a capability, the only way to share one: the child's rights and range lie within its
//! parent's and its depth is one greater, so whoever derived it can always revoke it. The child goes
//! in a free slot of the same table; a grant across tables is atmo-6x9.16.11. See the design on
//! atmo-6x9.6.7, sections 1 to 4.
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::table::*;
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
fn order_bytes(order: u8) -> (ret: usize)
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
    /// The refusals: an index that names no slot, a parent that is no capability or is at the deepest
    /// depth, a child's slot in use, or a child that does not narrow its parent.
    pub open spec fn can_derive(&self, root: usize, from: usize, to: usize, rights: u32, base: usize, order: u8) -> bool {
        let parent = self.tables.node_of(root, from);
        let child = self.tables.node_of(root, to);
        &&& self.tables.has_slot(root, from)
        &&& self.tables.has_slot(root, to)
        &&& self.is_cap(parent)
        &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
        &&& !self.list.nodes@[child as int].live
        &&& narrows(child_of(self.payload_of(parent), rights, base, order), self.payload_of(parent))
        &&& self.payload_of(parent).kind is Frame ==>
            block_refs(&self.blocks, block_ref(&self.blocks, self.payload_of(parent).base / 4096)) != usize::MAX
    }

    /// Derives the capability at index `from` of the table at `root` into the empty index `to`. All of
    /// the indices, rights, base and order come from user space, so any of them can be refused, and a
    /// refusal changes nothing.
    pub fn derive(&mut self, root: usize, from: usize, to: usize, rights: u32, base: usize, order: u8) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                &&& old(self).view().holds(root, parent)
                &&& final(self).view().holds(root, child)
                &&& !old(self).list.nodes@[child as int].live
                &&& narrows(final(self).payload_of(child), old(self).payload_of(parent))
                &&& final(self).payload_of(child) == child_of(old(self).payload_of(parent), rights, base, order)
                &&& final(self).list.is_child(parent, child)
                &&& final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1
                &&& final(self).list.nodes@[child as int].depth <= MAX_DEPTH
            },
            ret == old(self).can_derive(root, from, to, rights, base, order),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (parent, payload) = match self.tables.lookup(&self.list, root, from) {
            Some(found) => found,
            None => { return false; },
        };
        let child = match self.tables.lookup(&self.list, root, to) {
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
            pre.lemma_slot(root, from);
            assert(pre.tables.is_cap(&pre.list, parent));
            assert(payload == pre.payload_of(parent));
        }
        if !may_derive(payload, rights, base, order) {
            return false;
        }
        let frame = match payload.kind {
            CapKind::Frame => true,
            _ => false,
        };
        // A derived frame holds a reference on the block its parent lies in.
        let block = if frame {
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
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: payload.kind, order, rights, base, badge: payload.badge, reserved: 0 },
        );
        match block {
            Some(br) => { self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].insert(child))); },
            None => {},
        }
        proof {
            let post = *self;
            pre.lemma_slot(root, to);
            assert(post.payload_of(child) == child_of(payload, rights, base, order));
            Self::lemma_derive_caps_wf(pre, post, child);
            pre.lemma_slot(root, to);
            Self::lemma_hidden_frame(pre, post, child, child);
            Self::lemma_derive_holders(pre, post, parent, child, block);
            Self::lemma_derive_discharges(pre, post, root, from, to);
            Self::lemma_tlb_same(pre, post);
        }
        true
    }

    /// The holders after a derive: a frame child joins its parent's block, and any other child holds
    /// nothing. With them, what the blocks owe the rest of the invariant.
    proof fn lemma_derive_holders(pre: Self, post: Self, parent: usize, child: usize, block: Option<BlockRef>)
        requires
            Self::derive_step(pre, post, child),
            pre.is_cap(parent),
            post.is_cap(child),
            narrows(post.payload_of(child), pre.payload_of(parent)),
            post.payload_of(child).kind == pre.payload_of(parent).kind,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            block is Some == (pre.payload_of(parent).kind is Frame),
            block is Some ==> {
                let br = block->0;
                &&& br == block_ref(&pre.blocks, pre.payload_of(parent).base / 4096)
                &&& block_refs(&pre.blocks, br) < usize::MAX
                &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
                &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].insert(child))
            },
            block is None ==> post.blocks == pre.blocks && post.holders == pre.holders,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        match block {
            Some(br) => {
                let pp = pre.payload_of(parent);
                let cp = post.payload_of(child);
                lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, parent);
                assert(frame_in_block(block_ref(&pre.blocks, pp.base / 4096), pp));
                lemma_child_same_block(&pre.blocks, pp, cp);
                lemma_holders_frame_added(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, child, br);
                lemma_zeroing_typed_refs_changed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
            },
            None => {
                lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
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
            payload_wf(post.payload_of(child)),
        ensures
            post.tables.caps_wf(&post.list),
    {
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) implies payload_wf(post.tables.payload_of(n)) by {
            if n != child {
                Self::lemma_caps_frame(pre, post, child, child, n);
                assert(post.is_cap(n));
                assert(pre.tables.is_cap(&pre.list, n));
            }
        }
    }

    /// The view of a step that adds one child, in a slot of the caller's table, under a capability the
    /// caller holds. The child covers only what its parent does, and has control only with its parent's
    /// name.
    pub proof fn lemma_adds_child_view(pre: Self, post: Self, root: usize, from: usize, to: usize)
        requires
            Self::derive_step(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(root, from),
            pre.tables.has_slot(root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            ({
                let cp = post.payload_of(pre.tables.node_of(root, to));
                let pp = pre.payload_of(pre.tables.node_of(root, from));
                &&& block_within(cp.base, cp.order, pp)
                &&& cp.rights & right_bit(Right::Control) != 0 ==> {
                    &&& pp.rights & right_bit(Right::Control) != 0
                    &&& cp.base == pp.base
                }
            }),
        ensures
            post.view().holds(root, pre.tables.node_of(root, to)),
            adds_child(
                pre.view(),
                post.view(),
                root,
                pre.tables.node_of(root, from),
                pre.tables.node_of(root, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
            ),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let (a, b) = (pre.view(), post.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        pre.lemma_slot(root, from);
        pre.lemma_slot(root, to);
        assert(a.holds(root, parent));
        assert(b.holds(root, child));
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) by {
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies live(x) by {
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies live(a.parent[x]) by {
            pre.list.lemma_parent_live(x);
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) == (a.held.contains(h) || h == (root, child)) by {
            if h.1 != child {
                Self::lemma_caps_frame(pre, post, child, child, h.1);
            }
        }
        assert forall|x: NodeId| x != child implies {
            &&& #[trigger] b.names.contains_key(x) == a.names.contains_key(x)
            &&& b.pages.contains_key(x) == a.pages.contains_key(x)
            &&& a.names.contains_key(x) ==> b.names[x] == a.names[x]
            &&& a.pages.contains_key(x) ==> b.pages[x] == a.pages[x]
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        assert forall|x: NodeId, r: Right| x != child implies #[trigger] b.rights.contains((x, r)) == a.rights.contains((x, r)) by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        let (cp, pp) = (post.payload_of(child), pre.payload_of(parent));
        assert forall|o: ObjectId| #[trigger] b.covers(child, o) implies a.covers(parent, o) by {
            assert(block_bytes(cp.order) == b.pages[child] * 4096);
            assert(block_bytes(pp.order) == a.pages[parent] * 4096);
        }
        assert forall|o: ObjectId| #[trigger] (b.contents)(o) == (a.contents)(o) by {}
        assert(adds_child(a, b, root, parent, child, live));
    }

    /// What derive's child owes that view: control only with the parent's name, and all its other
    /// rights the parent's too.
    proof fn lemma_derive_discharges(pre: Self, post: Self, root: usize, from: usize, to: usize)
        requires
            Self::derive_step(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(root, from),
            pre.tables.has_slot(root, to),
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
        Self::lemma_adds_child_view(pre, post, root, from, to);
        lemma_adds_child_discharges(pre.view(), post.view(), root, parent, child, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live);
    }
}

} // verus!
