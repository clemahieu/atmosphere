//! Deleting a capability: one slot of the caller's table goes, refused while the capability has
//! children, mappings or bindings, which are all child nodes, so a holder revokes first. What the
//! capability said is returned, for reference counting to act on. See design/sharing-by-derive/.
use vstd::prelude::*;

verus! {

use crate::capability::mapping::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::define::*;

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
            Self::same_tree(*old(self), *final(self)),
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
        match payload.kind {
            CapKind::Frame => {
                proof {
                    lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, n);
                }
                let br = locate(&self.blocks, payload.base / 4096);
                drop_block_ref(&mut self.blocks, br);
                self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].remove(n)));
            },
            CapKind::Space => {
                proof {
                    pre.lemma_space_cap(n);
                }
                drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / 4096));
                self.spaces.holders = Ghost(pre.spaces.holders@.insert(payload.base, pre.spaces.holders@[payload.base].remove(n)));
            },
            _ => {},
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
    /// a space capability leaves its space, and any other node held nothing. With them, what the
    /// blocks owe the rest of the invariant.
    pub proof fn lemma_delete_holders(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            !(pre.list.nodes@[n as int].kind is Hidden),
            !(pre.list.nodes@[n as int].kind is Mapping),
            pre.list.childless(n),
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.table_pages == pre.table_pages,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.list.parent@ == pre.list.parent@,
            post.mappings == pre.mappings,
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
                &&& post.spaces == pre.spaces
            },
            pre.is_cap(n) && pre.payload_of(n).kind is Space ==> {
                let s = pre.payload_of(n).base;
                let br = BlockRef::Small(s / 4096);
                &&& blocks_refs_changed(
                    &pre.blocks,
                    &post.blocks,
                    br,
                    (block_refs(&pre.blocks, br) - 1) as usize,
                    block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
                )
                &&& post.holders == pre.holders
                &&& post.spaces.roots == pre.spaces.roots
                &&& post.spaces.records == pre.spaces.records
                &&& post.spaces.loaded == pre.spaces.loaded
                &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
                &&& post.spaces.bound == pre.spaces.bound
                &&& post.spaces.holders@ == pre.spaces.holders@.insert(s, pre.spaces.holders@[s].remove(n))
            },
            !(pre.is_cap(n) && (pre.payload_of(n).kind is Frame || pre.payload_of(n).kind is Space))
                ==> post.blocks == pre.blocks && post.holders == pre.holders && post.spaces == pre.spaces,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert(same_mapping_nodes(&pre.list, &post.list));
        Self::lemma_delete_mappings(pre, post, n);
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
            lemma_spaces_refs_changed(
                &pre.list,
                &pre.tables,
                &post.list,
                &post.tables,
                &pre.spaces,
                &pre.blocks,
                &post.blocks,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            );
        } else if pre.is_cap(n) && pre.payload_of(n).kind is Space {
            let s = pre.payload_of(n).base;
            let br = BlockRef::Small(s / 4096);
            let refs = (block_refs(&pre.blocks, br) - 1) as usize;
            let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
            pre.lemma_space_cap(n);
            lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
            assert(!pre.holders@.contains_key(br)) by {
                if pre.holders@.contains_key(br) {
                    assert(pre.blocks.pages@[(s / 4096) as int].object is Frame);
                }
            }
            lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, s / 4096, refs, dead);
            lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, s / 4096, refs, dead);
            lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
            assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
            lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, s / 4096, refs, dead);
            lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, s / 4096, refs, dead);
            lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
            Self::lemma_spaces_holder_dropped(pre, post, n, s);
        } else {
            lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
            lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
            lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
            lemma_spaces_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks);
        }
    }

    /// The mappings after node n goes, the only node that changed: it was childless, so no mapping's
    /// parent, and it was no mapping, so no mapping's frame lost its holder.
    pub proof fn lemma_delete_mappings(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            !(pre.list.nodes@[n as int].kind is Mapping),
            pre.list.childless(n),
            !post.list.nodes@[n as int].live,
            post.table_pages == pre.table_pages,
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.list.parent@ == pre.list.parent@,
            post.mappings == pre.mappings,
            forall|i: usize| i < NUM_PAGES ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            forall|br: BlockRef, x: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(x) && x != n
                ==> post.holders@.contains_key(br) && post.holders@[br].contains(x),
            forall|br: BlockRef, x: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(x)
                ==> pre.holders@.contains_key(br) && pre.holders@[br].contains(x),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert(Self::same_tree(pre, post));
        pre.lemma_childless_no_mapping(n);
        Self::lemma_mapping_parents_kept(pre, post, n, n);
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
            assert(m != n);
        }
        Self::lemma_mappings_same_tree(pre, post);
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
