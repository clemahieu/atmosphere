//! Revoking a capability, a bounded number of steps per kernel entry. A step finds a node of its run with
//! no children, undoes what that node's kind holds, and unlinks it, so revoke removes exactly the
//! capability's lineage, leaf first. See the design on atmo-6x9.6.7, section 5.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::table::*;
use crate::define::*;

/// How many steps a revoke does per kernel entry. No wait happens under the lock, so a revoke returns
/// and is called again. It is above the core count so the revoker outruns any number of deriving
/// threads, each core getting one entry per turn: reasoned in the design, not proven, since this
/// theorem is about safety.
pub const REVOKE_BUDGET: usize = 64;

pub proof fn lemma_budget_above_cores()
    ensures
        REVOKE_BUDGET > NUM_CPUS,
{
}

/// What a revoke did.
pub enum RevokeStep {
    /// Nothing changed: the index names no capability.
    Refused,
    /// The capability's run is empty.
    Done,
    /// Its budget ran out with some of the run left. Revoke again to go on.
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
            n != old(self).list.seq@[0],
        ensures
            final(self).tables.wf(&old(self).list),
            final(self).blocks.wf(),
            final(self).list == old(self).list,
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
            old(self).is_cap(n) && old(self).payload_of(n).kind is Frame ==> {
                let br = block_ref(&old(self).blocks, old(self).payload_of(n).base / 4096);
                &&& blocks_refs_changed(
                    &old(self).blocks,
                    &final(self).blocks,
                    br,
                    (block_refs(&old(self).blocks, br) - 1) as usize,
                    block_dead(&old(self).blocks, br) || block_refs(&old(self).blocks, br) == 1,
                )
                &&& final(self).holders@ == old(self).holders@.insert(br, old(self).holders@[br].remove(n))
            },
            old(self).list.nodes@[n as int].kind is Hidden ==> {
                &&& blocks_refs_changed(&old(self).blocks, &final(self).blocks, BlockRef::Small(n / 4096), 0, true)
                &&& final(self).holders == old(self).holders
            },
            !(old(self).is_cap(n) && old(self).payload_of(n).kind is Frame)
                && !(old(self).list.nodes@[n as int].kind is Hidden) ==> {
                &&& final(self).blocks == old(self).blocks
                &&& final(self).holders == old(self).holders
            },
    {
        let ghost pre = *old(self);
        proof {
            self.list.lemma_live_valid(n);
        }
        let node = self.list.get(n);
        match node.kind {
            NodeKind::Hidden => {
                self.tables.detach_leaf(&self.list, n);
                // The block's one reference was the hidden node's, so it is dead at once.
                proof {
                    pre.lemma_hidden_block(n);
                }
                drop_block_ref(&mut self.blocks, BlockRef::Small(n / 4096));
            },
            NodeKind::Capability => {
                proof {
                    assert(pre.is_cap(n));
                }
                let payload = self.tables.payload_at(&self.list, n);
                let frame = match payload.kind {
                    CapKind::Frame => true,
                    _ => false,
                };
                if frame {
                    proof {
                        lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, n);
                    }
                    let br = locate(&self.blocks, payload.base / 4096);
                    drop_block_ref(&mut self.blocks, br);
                    self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].remove(n)));
                }
            },
            NodeKind::Mapping | NodeKind::Binding => {},
        }
    }

    /// Revokes the capability at index i of the table at root, for at most REVOKE_BUDGET steps. The
    /// index comes from user space, so it can be refused. Its own slot can leave the table during the
    /// call, if the leaf holding it is in its run, so the steps name its node instead.
    pub fn revoke(&mut self, root: usize, i: usize) -> (ret: RevokeStep)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret is Refused == !(old(self).tables.has_slot(root, i) && old(self).is_cap(old(self).tables.node_of(root, i))),
            ret is Refused ==> *final(self) == *old(self),
            !(ret is Refused) ==> {
                let c = old(self).tables.node_of(root, i);
                &&& ret is Done == final(self).list.childless(c)
                &&& ret is Done ==> forall|x: usize| !#[trigger] final(self).list.is_child(c, x)
                &&& old(self).list.seq@.len() - final(self).list.seq@.len() <= REVOKE_BUDGET
                &&& final(self).list.parent == old(self).list.parent
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
        let mut steps = 0;
        while steps != REVOKE_BUDGET
            invariant
                steps <= REVOKE_BUDGET,
                self.wf(),
                pre == *old(self),
                pre.tables.has_slot(root, i),
                c == pre.tables.node_of(root, i),
                c < NODE_SPACE,
                self.is_cap(c),
                self.tables.owner == pre.tables.owner,
                self.list.parent == pre.list.parent,
                pre.list.seq@.len() - self.list.seq@.len() == steps,
                pre.tables.owner@[page_of(c)].0 == root,
                pre.is_cap(c),
                discharges(pre.view(), self.view(), root, Effect::Revoke { cap: c }),
            decreases REVOKE_BUDGET - steps,
        {
            let ghost mid = *self;
            if self.revoke_step(root, c) {
                proof {
                    assert(self.view() == mid.view());
                }
                return RevokeStep::Done;
            }
            proof {
                lemma_revoke_steps_compose(pre.view(), mid.view(), self.view(), root, c);
            }
            steps = steps + 1;
        }
        if self.list.is_childless(c) {
            RevokeStep::Done
        } else {
            RevokeStep::Again
        }
    }

    /// One step of revoking capability c, which root's table holds. Returns whether c's run was empty.
    fn revoke_step(&mut self, root: usize, c: usize) -> (done: bool)
        requires
            old(self).wf(),
            c < NODE_SPACE,
            old(self).is_cap(c),
            old(self).tables.owner@[page_of(c)].0 == root,
        ensures
            final(self).wf(),
            final(self).is_cap(c),
            final(self).tables.owner == old(self).tables.owner,
            final(self).list.parent == old(self).list.parent,
            done == old(self).list.childless(c),
            done ==> *final(self) == *old(self),
            done ==> forall|x: usize| !#[trigger] old(self).list.is_child(c, x),
            !done ==> final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            !done ==> exists|r: usize| #[trigger] revoked_one(old(self).list, final(self).list, c, r)
                && (old(self).list.nodes@[r as int].kind is Hidden ==> !final(self).tables.attached(r)),
            forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] final(self).list.nodes@[x].depth == old(self).list.nodes@[x].depth,
            discharges(old(self).view(), final(self).view(), root, Effect::Revoke { cap: c }),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_change_discharges_revoke(root, c);
        }
        let r = match self.list.leaf_of_run(c) {
            Some(found) => found,
            None => { return true; },
        };
        self.unlink_arm(r);
        self.list.remove_leaf(r);
        proof {
            let post = *self;
            post.tables.lemma_wf_same_pages(&pre.list, &post.list);
            Self::lemma_revoke_step(pre, post, root, c, r);
            Self::lemma_delete_caps_wf(pre, post, r);
            assert(revoked_one(pre.list, post.list, c, r));
            let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == r
                && post.list.seq@ == pre.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == pre.list.seq@[0]);
            Self::lemma_revoke_hidden(pre, post, r);
            if pre.list.nodes@[r as int].kind is Hidden {
                Self::lemma_revoke_hidden_holders(pre, post, r);
            } else {
                Self::lemma_delete_holders(pre, post, r);
            }
            Self::lemma_tlb_same(pre, post);
            assert(post.list.nodes@[c as int].live == pre.list.nodes@[c as int].live);
            Self::lemma_caps_frame(pre, post, r, r, c);
        }
        false
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

    /// The holders and the blocks after hidden node n goes with its leaf's one reference: no frame
    /// changed, the leaf's block was no holder's key, and it is dead at zero as its node is dead.
    proof fn lemma_revoke_hidden_holders(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Hidden,
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            blocks_refs_changed(&pre.blocks, &post.blocks, BlockRef::Small(n / 4096), 0, true),
            post.holders == pre.holders,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
    {
        let br = BlockRef::Small(n / 4096);
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        pre.lemma_hidden_block(n);
        assert(!pre.is_cap(n));
        assert(!post.is_cap(n));
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, n / 4096, 0, true);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, n / 4096, 0, true);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_leaf_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, n, 0, true);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) && l != n implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            pre.lemma_slot_bound(l);
        }
        lemma_leaf_blocks_leaf_dropped(&pre.list, &post.list, &pre.tables, &pre.blocks, &post.blocks, pre.holders@, n);
        assert(leaf_blocks_wf(&post.list, &post.tables, &post.blocks));
    }

    /// The hidden nodes after the step: r has gone, and if it was hidden its leaf is detached. And every
    /// other capability node is still in its slot.
    proof fn lemma_revoke_hidden(pre: Self, post: Self, r: usize)
        requires
            Self::caps_frame(pre, post, r, r),
            !post.list.nodes@[r as int].live,
            pre.list.nodes@[r as int].kind is Hidden ==> !post.tables.attached(r),
            !(pre.list.nodes@[r as int].kind is Hidden) ==> post.tables.record(r) == pre.tables.record(r),
            post.list.seq@[0] == pre.list.seq@[0],
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables),
            capability_nodes_are_slots(&post.list, &post.tables),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Capability && x != post.list.seq@[0]
            implies post.tables.is_cap(&post.list, x) by {
            assert(x != r);
            assert(pre.list.nodes@[x as int].live);
            assert(pre.tables.is_cap(&pre.list, x));
            Self::lemma_caps_frame(pre, post, r, r, x);
        }
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
