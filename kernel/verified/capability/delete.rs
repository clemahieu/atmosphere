//! Deleting a capability: one slot of the caller's table goes, refused while the capability has
//! children, mappings or bindings, which are all child nodes, so a holder revokes first. What the
//! capability said is returned, for reference counting to act on. See the design on atmo-6x9.6.7,
//! sections 1 to 5.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::table::*;

impl CapKernel {
    /// The refusals: an index that names no slot, a slot with no capability, the list's first node,
    /// which has depth 0, or a capability with something below it.
    pub open spec fn can_delete(&self, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(root, i)
        &&& self.is_cap(n)
        &&& self.list.nodes@[n as int].depth > 0
        &&& self.list.childless(n)
    }

    /// Deletes the capability at index i of the table at root. The index comes from user space, so it
    /// can be refused, and a refusal changes nothing.
    pub fn delete(&mut self, root: usize, i: usize) -> (ret: Option<Payload>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret is Some == old(self).can_delete(root, i),
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> {
                let n = old(self).tables.node_of(root, i);
                &&& ret.unwrap() == old(self).payload_of(n)
                &&& forall|c: usize| !#[trigger] old(self).list.is_child(n, c)
                &&& !final(self).is_cap(n)
                &&& Self::caps_frame(*old(self), *final(self), n, n)
            },
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(n);
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        proof {
            self.list.lemma_valid_bound(n);
        }
        if !node.live || !kind_ok || node.depth == 0 || !self.list.is_childless(n) {
            return None;
        }
        proof {
            pre.lemma_slot(root, i);
            assert(pre.tables.is_cap(&pre.list, n));
            assert(payload == pre.payload_of(n));
            // The list's first node has depth 0.
            assert(n != pre.list.seq@[0]);
        }
        self.list.remove_leaf(n);
        proof {
            let post = *self;
            pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
            assert(Self::caps_frame(pre, post, n, n));
            Self::lemma_delete_caps_wf(pre, post, n);
            Self::lemma_hidden_frame(pre, post, n, n);
            Self::lemma_delete_discharges(pre, post, root, n);
            Self::lemma_tlb_same(pre, post);
        }
        Some(payload)
    }

    /// Every capability left still names a block.
    pub proof fn lemma_delete_caps_wf(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            !post.list.nodes@[n as int].live,
        ensures
            post.tables.caps_wf(&post.list),
    {
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) implies payload_wf(post.tables.payload_of(x)) by {
            assert(x != n);
            Self::lemma_caps_frame(pre, post, n, n, x);
            assert(post.is_cap(x));
            assert(pre.tables.is_cap(&pre.list, x));
        }
    }

    /// The view of the step: one capability the caller held goes, and nothing else.
    proof fn lemma_delete_discharges(pre: Self, post: Self, root: usize, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            pre.is_cap(n),
            pre.tables.owner@[page_of(n)].0 == root,
            !post.list.nodes@[n as int].live,
            post.list.parent@ == pre.list.parent@,
        ensures
            discharges(pre.view(), post.view(), root, Effect::Local),
    {
        let (a, b) = (pre.view(), post.view());
        assert(a.holds(root, n));
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) implies a.held.contains(h) by {
            assert(h.1 != n);
            Self::lemma_caps_frame(pre, post, n, n, h.1);
        }
        assert forall|x: NodeId| x != n && #[trigger] a.names.contains_key(x) implies b.names.contains_key(x) by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert forall|x: NodeId| #[trigger] b.names.contains_key(x) implies {
            &&& a.names.contains_key(x)
            &&& b.names[x] == a.names[x]
        } by {
            assert(x != n);
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert forall|x: NodeId| #[trigger] b.pages.contains_key(x) implies {
            &&& a.pages.contains_key(x)
            &&& b.pages[x] == a.pages[x]
        } by {
            assert(x != n);
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert forall|h: (NodeId, Right)| #[trigger] b.rights.contains(h) implies a.rights.contains(h) by {
            assert(h.0 != n);
            Self::lemma_caps_frame(pre, post, n, n, h.0);
        }
        assert forall|o: ObjectId| #[trigger] (b.contents)(o) == (a.contents)(o) by {}
        assert(removes_cap(a, b, root, n));
        lemma_removes_cap_discharges(a, b, root, n);
    }
}

} // verus!
