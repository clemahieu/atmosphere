//! Deleting a capability: one slot of the caller's table goes, refused while the capability has
//! children, mappings or bindings, which are all child nodes, so a holder revokes first. What the
//! capability said is returned, for reference counting to act on. See the design on atmo-6x9.6.7,
//! sections 1 to 5.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
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
        proof {
            let post = *self;
            pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
            assert(Self::caps_frame(pre, post, n, n));
            Self::lemma_delete_caps_wf(pre, post, n);
            Self::lemma_hidden_frame(pre, post, n, n);
            Self::lemma_delete_holders(pre, post, n);
            let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == n
                && post.list.seq@ == pre.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == pre.list.seq@[0]);
            lemma_parents_removed(pre.list, post.list, n);
            Self::lemma_delete_discharges(pre, post, root, n);
            Self::lemma_tlb_same(pre, post);
        }
        Some(payload)
    }

    /// The holders after node n goes, the only node that changed: a frame capability leaves its block,
    /// and any other node held nothing. With them, what the blocks owe the rest of the invariant.
    pub proof fn lemma_delete_holders(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            pre.list.nodes@[n as int].live,
            !(pre.list.nodes@[n as int].kind is Hidden),
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.table_pages == pre.table_pages,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            pre.is_cap(n) && pre.payload_of(n).kind is Frame ==> {
                let br = block_ref(&pre.blocks, pre.payload_of(n).base / 4096);
                &&& blocks_refs_changed(
                    &pre.blocks,
                    &post.blocks,
                    br,
                    (block_refs(&pre.blocks, br) - 1) as usize,
                    block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
                )
                &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].remove(n))
            },
            !(pre.is_cap(n) && pre.payload_of(n).kind is Frame) ==> post.blocks == pre.blocks && post.holders == pre.holders,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        pre.lemma_unhidden_not_owned(n);
        Self::lemma_same_leaf_nodes(pre, post, n, n);
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        pre.lemma_unhidden_not_table_page(n);
        Self::lemma_same_table_nodes(pre, post, n, n);
        if pre.is_cap(n) && pre.payload_of(n).kind is Frame {
            let br = block_ref(&pre.blocks, pre.payload_of(n).base / 4096);
            lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, n);
            lemma_holders_frame_dropped(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, n, br);
            lemma_zeroing_typed_refs_changed(
                &pre.list,
                &pre.tables,
                &pre.blocks,
                &post.blocks,
                &pre.zeroing,
                pre.holders@,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            );
            lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
            assert forall|x: BlockRef| #[trigger] post.holders@.contains_key(x) == pre.holders@.contains_key(x) by {}
            assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
            lemma_objects_refs_changed(
                &post.tables,
                &pre.blocks,
                &post.blocks,
                pre.holders@,
                post.holders@,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            );
            lemma_leaf_blocks_refs_changed(
                &pre.list,
                &post.list,
                &post.tables,
                &pre.blocks,
                &post.blocks,
                pre.holders@,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            );
            if let BlockRef::Small(x) = br {
                assert(pre.blocks.pages@[x as int].object is Frame);
            }
            lemma_table_pages_refs_changed(
                &pre.list,
                &post.list,
                &pre.table_pages,
                &pre.blocks,
                &post.blocks,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            );
        } else {
            lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
            lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
            lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
        }
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
    pub proof fn lemma_delete_discharges(pre: Self, post: Self, root: usize, n: usize)
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
