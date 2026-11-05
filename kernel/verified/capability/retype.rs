//! Retyping free memory under an untyped. Here a 4K frame: the page is zeroed at once, and the frame
//! capability is a child of the untyped in a slot the caller names, so revoking the untyped reaches it.
//! See the design on atmo-6x9.6.7, sections 1, 3 and 6.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::derive::*;
use crate::capability::kernel::CapKernel;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::capability::zero::*;
use crate::define::*;
use crate::pptr::*;

/// Read, write and execute.
pub const FRAME_RIGHTS: u32 = 7;

/// A 4K frame capability's payload. It has every right a frame can have, whatever the untyped's, since
/// the untyped's holder already reaches the page.
pub open spec fn frame_of(base: usize) -> Payload {
    Payload { kind: CapKind::Frame, order: 0, rights: FRAME_RIGHTS, base, badge: 0, reserved: 0 }
}

impl CapKernel {
    /// The refusals before the block table is asked: an index that names no slot, a parent that is not
    /// a capability to an untyped, without the retype right or at the deepest depth, a slot in use, or
    /// a page outside the untyped's block or past the end of memory.
    pub open spec fn can_retype_frame(&self, root: usize, from: usize, to: usize, base: usize) -> bool {
        let parent = self.tables.node_of(root, from);
        let child = self.tables.node_of(root, to);
        &&& self.tables.has_slot(root, from)
        &&& self.tables.has_slot(root, to)
        &&& self.is_cap(parent)
        &&& self.payload_of(parent).kind is Untyped
        &&& self.payload_of(parent).rights & right_bit(Right::Retype) != 0
        &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
        &&& !self.list.nodes@[child as int].live
        &&& block_within(base, 0, self.payload_of(parent))
        &&& base / 4096 < NUM_PAGES
    }

    /// Retypes the free page at `base` as a frame, under the untyped at index `from` of the table at
    /// `root`, with the capability at the empty index `to`. All of these come from user space, and a
    /// refusal changes nothing. The block table refuses a page that is not free.
    pub fn retype_frame(&mut self, root: usize, from: usize, to: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret ==> old(self).can_retype_frame(root, from, to, base),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == frame_of(base)
                &&& final(self).list.is_child(parent, child)
                &&& final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1
                &&& holds_zero(final(self).frames@, base / 4096)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base })
            },
    {
        let ghost pre = *old(self);
        let (parent, payload) = match self.tables.lookup(&self.list, root, from) {
            Some(found) => found,
            None => { return false; },
        };
        let child = match self.tables.lookup(&self.list, root, to) {
            Some(found) => found.0,
            None => { return false; },
        };
        let node = self.list.get(parent);
        let node_ok = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !node_ok || node.depth >= MAX_DEPTH || self.list.get(child).live {
            return false;
        }
        proof {
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            assert(pre.tables.is_cap(&pre.list, parent));
            assert(payload == pre.payload_of(parent));
        }
        let untyped = match payload.kind {
            CapKind::Untyped => true,
            _ => false,
        };
        if !untyped || payload.rights & 8 == 0 || !is_block_within(payload, base, 0) || base / 4096 >= NUM_PAGES {
            return false;
        }
        let page = base / 4096;
        proof {
            lemma2_to64();
            assert(base % 4096 == 0);
            assert(page * 4096 == base);
        }
        let taken = self.blocks.try_type(page, 0);
        let Tracked(perms) = match taken {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked mut perm;
        proof {
            assert(0usize < order_pages(0));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * 4096);
            assert((page + 0usize) as usize == page);
            perm = perms.tracked_remove(page);
        }
        zero_page(base, Tracked(&mut perm));
        proof {
            self.frames.borrow_mut().tracked_insert(page, perm);
            pre.list.lemma_seq_fits();
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
        }
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: CapKind::Frame, order: 0, rights: FRAME_RIGHTS, base, badge: 0, reserved: 0 },
        );
        proof {
            let post = *self;
            assert(post.payload_of(child) == frame_of(base));
            assert(payload_wf(post.payload_of(child)));
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_tlb_same(pre, post);
            assert(FRAME_RIGHTS & 128 == 0) by (compute_only);
            assert(right_bit(Right::Control) == 128);
            assert(right_bit(Right::Retype) == 8);
            Self::lemma_adds_child_view(pre, post, root, from, to);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            lemma_adds_child_discharges_retype(pre.view(), post.view(), root, parent, child, live, base);
        }
        true
    }
}

} // verus!
