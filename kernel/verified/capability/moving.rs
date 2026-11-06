//! Moving a capability within its table. The node keeps its place and depth, so every child comes
//! along. A capability's identity in the view is its node id, which a move renames, so reach is carried
//! across by that renaming, in both directions. Claim out of another table is atmo-6x9.16.9. See the
//! design on atmo-6x9.6.7, section 4.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::table::*;
use crate::define::*;

impl CapKernel {
    /// The refusals: an index that names no slot, a source with no capability, or a target in use,
    /// which a source is, so a slot cannot move onto itself.
    pub open spec fn can_move(&self, root: usize, from: usize, to: usize) -> bool {
        &&& self.tables.has_slot(root, from)
        &&& self.tables.has_slot(root, to)
        &&& self.is_cap(self.tables.node_of(root, from))
        &&& !self.list.nodes@[self.tables.node_of(root, to) as int].live
    }

    /// Moves the capability at index `from` of the table at `root` to the empty index `to`. The indices
    /// come from user space, so either can be refused, and a refusal changes nothing.
    pub fn move_cap(&mut self, root: usize, from: usize, to: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret == old(self).can_move(root, from, to),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let i = old(self).tables.node_of(root, from);
                let n = old(self).tables.node_of(root, to);
                &&& exists|p: int| 0 <= p < old(self).list.seq@.len() && #[trigger] old(self).list.seq@[p] == i
                    && final(self).list.seq@ == old(self).list.seq@.update(p, n)
                &&& final(self).list.nodes@[n as int].depth == old(self).list.nodes@[i as int].depth
                &&& final(self).list.parent@ == moved_parent(old(self).list.parent@, i, n)
                &&& final(self).payload_of(n) == old(self).payload_of(i)
                &&& !final(self).is_cap(i)
                &&& final(self).view().holds(root, n)
                &&& Self::caps_frame(*old(self), *final(self), i, n)
                &&& forall|r: ObjectId, o: ObjectId| #[trigger] final(self).view().reach(r, o) == old(self).view().reach(r, o)
            },
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (i, payload) = match self.tables.lookup(&self.list, root, from) {
            Some(found) => found,
            None => { return false; },
        };
        let n = match self.tables.lookup(&self.list, root, to) {
            Some(found) => found.0,
            None => { return false; },
        };
        let node = self.list.get(i);
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !node.live || !kind_ok || self.list.get(n).live {
            return false;
        }
        proof {
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            assert(pre.tables.is_cap(&pre.list, i));
            assert(payload == pre.payload_of(i));
            self.list.lemma_valid_bound(i);
            self.list.lemma_valid_bound(n);
        }
        self.list.move_node(i, n);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(&self.list, root, to, payload);
        // A frame's holder has a new name; the count does not change.
        self.holders = Ghost(Self::moved_holders(pre.holders@, i, n));
        proof {
            let post = *self;
            assert(post.list.nodes@[n as int].kind == pre.list.nodes@[i as int].kind);
            assert(post.payload_of(n) == pre.payload_of(i));
            assert(Self::caps_frame(pre, post, i, n));
            Self::lemma_move_caps_wf(pre, post, i, n);
            Self::lemma_hidden_frame(pre, post, i, n);
            Self::lemma_move_holders(pre, post, i, n);
            Self::lemma_move_discharges(pre, post, root, i, n);
            Self::lemma_tlb_same(pre, post);
        }
        true
    }

    /// The holders after a move: the node a frame held its block by has a new name, and no count changed.
    proof fn lemma_move_holders(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            post.blocks == pre.blocks,
            post.zeroing == pre.zeroing,
            post.holders@ == Self::moved_holders(pre.holders@, i, n),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
    {
        let ha = pre.holders@;
        let hb = post.holders@;
        let blocks = &pre.blocks;
        assert(pre.tables.is_cap(&pre.list, i));
        assert(!pre.tables.is_cap(&pre.list, n));
        assert(!post.tables.is_cap(&post.list, i));
        assert forall|x: usize| x != i && x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, i, n, x);
        }
        assert forall|k: BlockRef| #[trigger] hb.contains_key(k) == ha.contains_key(k) by {}
        assert forall|k: BlockRef| ha.contains_key(k) implies {
            &&& #[trigger] hb[k] == (if ha[k].contains(i) { ha[k].remove(i).insert(n) } else { ha[k] })
            &&& !ha[k].contains(n)
        } by {
            if ha[k].contains(n) {
                assert(pre.tables.is_cap(&pre.list, n));
            }
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Frame implies {
            let p = post.tables.payload_of(x).base / 4096;
            &&& p < NUM_PAGES
            &&& frame_in_block(block_ref(blocks, p), post.tables.payload_of(x))
            &&& hb.contains_key(block_ref(blocks, p))
            &&& hb[block_ref(blocks, p)].contains(x)
        } by {
            let p = post.tables.payload_of(x).base / 4096;
            if x == n {
                assert(ha[block_ref(blocks, p)].contains(i));
            } else {
                assert(pre.tables.is_cap(&pre.list, x));
                assert(ha[block_ref(blocks, p)].contains(x));
            }
        }
        assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
            &&& hb[k].finite()
            &&& hb[k].len() == block_refs(blocks, k)
            &&& block_typed(blocks, k)
            &&& block_refs(blocks, k) == 0 ==> block_dead(blocks, k)
            &&& !block_active(&post.zeroing, k)
        } by {
            assert(ha.contains_key(k));
            if ha[k].contains(i) {
                vstd::set::lemma_set_remove_len(ha[k], i);
                vstd::set::lemma_set_insert_len(ha[k].remove(i), n);
            }
        }
        assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Frame
            &&& post.tables.payload_of(x).base / 4096 < NUM_PAGES
            &&& block_ref(blocks, post.tables.payload_of(x).base / 4096) == k
        } by {
            assert(ha.contains_key(k));
            if ha[k].contains(i) && x == n {
                assert(ha[k].contains(i));
            } else {
                assert(ha[k].contains(x));
                assert(x != i);
                assert(x != n);
            }
        }
    }

    /// Each block's holders after node i is renamed n.
    pub open spec fn moved_holders(holders: IMap<BlockRef, Set<usize>>, i: usize, n: usize) -> IMap<BlockRef, Set<usize>> {
        IMap::new(
            |br: BlockRef| holders.contains_key(br),
            |br: BlockRef| if holders[br].contains(i) { holders[br].remove(i).insert(n) } else { holders[br] },
        )
    }

    /// What a move does to the fields the view reads.
    pub open spec fn move_step(pre: Self, post: Self, i: usize, n: usize) -> bool {
        &&& Self::caps_frame(pre, post, i, n)
        &&& pre.is_cap(i)
        &&& !pre.list.nodes@[n as int].live
        &&& !post.list.nodes@[i as int].live
        &&& post.list.nodes@[n as int].live
        &&& post.list.nodes@[n as int].kind is Capability
        &&& n % 4096 != 0
        &&& n % 4096 < NODES_PER_PAGE
        &&& pre.tables.owner@.contains_key(page_of(n))
        &&& pre.tables.owner@[page_of(n)].0 == pre.tables.owner@[page_of(i)].0
        &&& post.payload_of(n) == pre.payload_of(i)
        &&& post.list.wf()
        &&& post.list.parent@ == moved_parent(pre.list.parent@, i, n)
    }

    /// Every capability still names a block.
    proof fn lemma_move_caps_wf(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
        ensures
            post.tables.caps_wf(&post.list),
    {
        assert(pre.tables.is_cap(&pre.list, i));
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) implies payload_wf(post.tables.payload_of(x)) by {
            if x != n {
                assert(x != i);
                Self::lemma_caps_frame(pre, post, i, n, x);
                assert(post.is_cap(x));
                assert(pre.tables.is_cap(&pre.list, x));
            }
        }
    }

    /// Every capability, parent and holding of pre is in post under its new name.
    proof fn lemma_move_simulates(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
        ensures
            simulates(
                pre.view(),
                post.view(),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
                |x: NodeId| rename(x, i, n),
            ),
    {
        let (a, b) = (pre.view(), post.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        let f = |x: NodeId| rename(x, i, n);
        assert forall|x: NodeId| #[trigger] pre.is_cap(x) implies {
            &&& live(x)
            &&& post.is_cap(f(x))
            &&& post.payload_of(f(x)) == pre.payload_of(x)
            &&& pre.tables.owner@[page_of(f(x))].0 == pre.tables.owner@[page_of(x)].0
        } by {
            pre.lemma_slot_bound(x);
            if x != i {
                assert(x != n);
                Self::lemma_caps_frame(pre, post, i, n, x);
            }
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, f(h.1))) by {
            assert(pre.is_cap(h.1));
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(f(x))
            &&& b.names[f(x)] == a.names[x]
        } by {
            assert(pre.is_cap(x));
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(f(x))
            &&& b.pages[f(x)] == a.pages[x]
        } by {
            assert(pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((f(x), r)) by {
            assert(pre.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            pre.list.lemma_parent_live(x);
            assert(x != n);
            assert(a.parent[x] != n);
            lemma_moved_parent(pre.list.parent@, i, n, x);
        }
        assert(simulates(a, b, live, f));
    }

    /// Every capability, parent and holding of post was in pre under its old name.
    proof fn lemma_move_simulated(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
        ensures
            simulates(
                post.view(),
                pre.view(),
                |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live,
                |x: NodeId| rename(x, n, i),
            ),
    {
        let (a, b) = (post.view(), pre.view());
        let live = |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live;
        let f = |x: NodeId| rename(x, n, i);
        pre.lemma_slot_bound(n);
        pre.lemma_slot_bound(i);
        assert forall|x: NodeId| #[trigger] post.is_cap(x) implies {
            &&& live(x)
            &&& pre.is_cap(f(x))
            &&& pre.payload_of(f(x)) == post.payload_of(x)
            &&& pre.tables.owner@[page_of(f(x))].0 == pre.tables.owner@[page_of(x)].0
        } by {
            pre.lemma_slot_bound(x);
            if x != n {
                assert(x != i);
                Self::lemma_caps_frame(pre, post, i, n, x);
            }
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
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((f(x), r)) by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            post.list.lemma_parent_live(x);
            assert(x != i);
            let old_x = f(x);
            assert(old_x < NODE_SPACE && pre.list.nodes@[old_x as int].live) by {
                if x != n {
                    assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
                }
            }
            lemma_moved_parent_back(pre.list.parent@, i, n, x);
            pre.list.lemma_parent_live(old_x);
            assert(pre.list.parent@[old_x] != n);
        }
        assert(simulates(a, b, live, f));
    }

    /// The view of the step: the capability the caller held has a new name, and that name is the only
    /// thing that went; reach is the same in both directions.
    proof fn lemma_move_discharges(pre: Self, post: Self, root: usize, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            pre.tables.owner@[page_of(i)].0 == root,
        ensures
            post.view().holds(root, n),
            forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o),
            discharges(pre.view(), post.view(), root, Effect::Local),
    {
        let (a, b) = (pre.view(), post.view());
        Self::lemma_move_simulates(pre, post, i, n);
        Self::lemma_move_simulated(pre, post, i, n);
        assert(a.holds(root, i));
        assert(post.is_cap(n));
        assert(b.holds(root, n));
        assert forall|r: ObjectId, o: ObjectId| #[trigger] b.reach(r, o) == a.reach(r, o) by {
            if b.reach(r, o) {
                lemma_simulates_reach(b, a, |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live, |x: NodeId| rename(x, n, i), r, o);
            }
            if a.reach(r, o) {
                lemma_simulates_reach(a, b, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live, |x: NodeId| rename(x, i, n), r, o);
            }
        }
        assert forall|x: NodeId| #[trigger] State::removed(a, b, x) implies may_remove(a, root, Effect::Local, x) by {
            if x != i {
                assert(x != n);
                Self::lemma_caps_frame(pre, post, i, n, x);
            }
        }
        assert forall|o: ObjectId| #[trigger] State::changed(a, b, o) implies may_change(a, Effect::Local, o) by {
            assert((a.contents)(o) == (b.contents)(o));
        }
    }
}

/// Where moved_parent puts a parent entry, renamed.
proof fn lemma_moved_parent(p: Map<usize, usize>, i: usize, n: usize, x: usize)
    requires
        p.contains_key(x),
        x != n,
        p.dom().finite(),
    ensures
        moved_parent(p, i, n).contains_key(rename(x, i, n)),
        moved_parent(p, i, n)[rename(x, i, n)] == rename(p[x], i, n),
{
    let q = moved_parent(p, i, n);
    if x == i {
        assert(rename(rename(x, i, n), n, i) == x);
    }
}

/// And which entry an entry of moved_parent came from.
proof fn lemma_moved_parent_back(p: Map<usize, usize>, i: usize, n: usize, x: usize)
    requires
        moved_parent(p, i, n).contains_key(x),
        p.dom().finite(),
    ensures
        p.contains_key(rename(x, n, i)),
        moved_parent(p, i, n)[x] == rename(p[rename(x, n, i)], i, n),
{
}

} // verus!
