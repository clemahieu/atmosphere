//! One step of revoking a capability: find a node of its run with no children, undo what that node's
//! kind holds, and unlink it. So revoke removes exactly the capability's lineage, leaf first. See the
//! design on atmo-6x9.6.7, section 5.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::table::*;

/// What a revoke step did.
pub enum RevokeStep {
    /// Nothing changed: the index names no capability.
    Refused,
    /// Nothing changed: the capability's run is empty.
    Done,
    /// One node of the run is gone. Revoke again to go on.
    Again,
}

impl CapKernel {
    /// Undoes what node n holds by its kind, before it is unlinked. Every arm meets this one spec: it
    /// changes no node's liveness and keeps the tables whole, and only what n itself held goes. A
    /// hidden node detaches its leaf. A capability's reference goes with atmo-6x9.16.22. No mapping
    /// or binding node exists until atmo-6x9.16.8 and atmo-6x9.16.9, which supply their arms.
    fn unlink_arm(&mut self, n: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
        ensures
            final(self).tables.wf(&old(self).list),
            final(self).list == old(self).list,
            final(self).blocks == old(self).blocks,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).tlb == old(self).tlb,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).tables.owner == old(self).tables.owner,
            forall|x: usize| x != n ==> #[trigger] final(self).tables.payload_of(x) == old(self).tables.payload_of(x),
            old(self).list.nodes@[n as int].kind is Hidden ==> !final(self).tables.attached(n),
            !(old(self).list.nodes@[n as int].kind is Hidden) ==> final(self).tables == old(self).tables,
    {
        proof {
            self.list.lemma_live_valid(n);
        }
        let node = self.list.get(n);
        match node.kind {
            NodeKind::Hidden => {
                self.tables.detach_leaf(&self.list, n);
            },
            NodeKind::Capability | NodeKind::Mapping | NodeKind::Binding => {},
        }
    }

    /// One step of revoking the capability at index i of the table at root. The index comes from user
    /// space, so it can be refused.
    pub fn revoke_step(&mut self, root: usize, i: usize) -> (ret: RevokeStep)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret is Refused == !(old(self).tables.has_slot(root, i) && old(self).is_cap(old(self).tables.node_of(root, i))),
            ret is Refused ==> *final(self) == *old(self),
            !(ret is Refused) ==> {
                let c = old(self).tables.node_of(root, i);
                &&& ret is Again ==> exists|r: usize| #[trigger] revoked_one(old(self).list, final(self).list, c, r)
                    && (old(self).list.nodes@[r as int].kind is Hidden ==> !final(self).tables.attached(r))
                &&& ret is Done == old(self).list.childless(c)
                &&& ret is Done ==> *final(self) == *old(self)
                &&& ret is Done ==> forall|x: usize| !#[trigger] old(self).list.is_child(c, x)
                &&& final(self).list.parent == old(self).list.parent
                &&& forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] final(self).list.nodes@[x].depth == old(self).list.nodes@[x].depth
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Revoke { cap: c })
            },
    {
        let ghost pre = *old(self);
        let c = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found.0,
            None => { return RevokeStep::Refused; },
        };
        let node = self.list.get(c);
        let kind_ok = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !kind_ok {
            return RevokeStep::Refused;
        }
        proof {
            pre.lemma_slot(root, i);
            assert(pre.tables.is_cap(&pre.list, c));
            pre.lemma_slot_bound(c);
            pre.lemma_no_change_discharges_revoke(root, c);
        }
        let r = match self.list.leaf_of_run(c) {
            Some(found) => found,
            None => { return RevokeStep::Done; },
        };
        self.unlink_arm(r);
        self.list.remove_leaf(r);
        proof {
            let post = *self;
            post.tables.lemma_wf_same_pages(&pre.list, &post.list);
            Self::lemma_revoke_step(pre, post, root, c, r);
            Self::lemma_delete_caps_wf(pre, post, r);
            Self::lemma_revoke_hidden(pre, post, r);
            Self::lemma_tlb_same(pre, post);
            assert(revoked_one(pre.list, post.list, c, r));
        }
        RevokeStep::Again
    }

    /// A step that changes nothing, with the capability held, discharges a revoke of it.
    proof fn lemma_no_change_discharges_revoke(&self, root: usize, c: usize)
        requires
            self.is_cap(c),
            self.tables.owner@[page_of(c)].0 == root,
        ensures
            discharges(self.view(), self.view(), root, Effect::Revoke { cap: c }),
    {
        assert(self.view().holds(root, c));
        assert(self.view().names.contains_key(c));
    }

    /// The hidden nodes after the step: r has gone, and if it was hidden its leaf is detached.
    proof fn lemma_revoke_hidden(pre: Self, post: Self, r: usize)
        requires
            Self::caps_frame(pre, post, r, r),
            !post.list.nodes@[r as int].live,
            pre.list.nodes@[r as int].kind is Hidden ==> !post.tables.attached(r),
            !(pre.list.nodes@[r as int].kind is Hidden) ==> post.tables.record(r) == pre.tables.record(r),
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden implies post.tables.owner@.contains_key(x) by {
            assert(x != r);
            assert(pre.list.nodes@[x as int].live);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) && post.tables.attached(l) implies {
            &&& l < NODE_SPACE
            &&& post.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind is Hidden
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            if l == r {
                assert(!(pre.list.nodes@[r as int].kind is Hidden));
                assert(pre.tables.attached(l));
                assert(false);
            } else {
                assert(post.tables.payload_of(l) == pre.tables.payload_of(l));
                assert(pre.tables.attached(l));
                assert(post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live);
            }
        }
    }

    /// What the step does to the view: only a node of c's run can leave it, and nothing is added.
    proof fn lemma_revoke_step(pre: Self, post: Self, root: usize, c: usize, r: usize)
        requires
            pre.wf(),
            post.list.wf(),
            pre.is_cap(c),
            pre.tables.owner@[page_of(c)].0 == root,
            post.tables.owner == pre.tables.owner,
            post.list.parent == pre.list.parent,
            !post.list.nodes@[r as int].live,
            has(pre.list.seq@, r),
            pre.list.d(r) > pre.list.d(c),
            pre.list.anc(r, (pre.list.d(r) - pre.list.d(c)) as nat) == c,
            forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != r ==> {
                &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
                &&& post.list.nodes@[x].kind == pre.list.nodes@[x].kind
            },
            forall|x: usize| x != r ==> #[trigger] post.tables.payload_of(x) == pre.tables.payload_of(x),
        ensures
            Self::caps_frame(pre, post, r, r),
            discharges(pre.view(), post.view(), root, Effect::Revoke { cap: c }),
    {
        let (a, b) = (post.view(), pre.view());
        let live = |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live;
        let f = |x: NodeId| x;
        assert(Self::caps_frame(pre, post, r, r));
        assert forall|x: usize| #[trigger] post.is_cap(x) implies pre.is_cap(x) && x != r && x < NODE_SPACE && post.payload_of(x) == pre.payload_of(x) by {
            assert(x != r);
            Self::lemma_caps_frame(pre, post, r, r, x);
            pre.lemma_slot_bound(x);
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, f(h.1))) by {
            assert(post.is_cap(h.1));
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(f(x))
            &&& b.names[f(x)] == a.names[x]
        } by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(f(x))
            &&& b.pages[f(x)] == a.pages[x]
        } by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId, q: Right| #[trigger] a.rights.contains((x, q)) implies b.rights.contains((f(x), q)) by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            post.list.lemma_parent_live(x);
        }
        assert(simulates(a, b, live, f));
        assert(b.holds(root, c));
        assert forall|x: NodeId| #[trigger] State::removed(b, a, x) implies exists|k: nat| k > 0 && #[trigger] b.descends(c, x, k) by {
            if x != r {
                Self::lemma_caps_frame(pre, post, r, r, x);
            }
            assert(x == r);
            let k = (pre.list.d(r) - pre.list.d(c)) as nat;
            pre.lemma_anc_descends(r, k);
            assert(b.descends(c, r, k));
        }
        assert forall|o: ObjectId| #[trigger] (a.contents)(o) == (b.contents)(o) by {}
        lemma_simulated_discharges_revoke(b, a, root, c, live, f);
    }
}

} // verus!
