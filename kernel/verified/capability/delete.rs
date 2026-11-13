// SPDX-License-Identifier: MIT

//! Deleting a capability: one slot goes, of the caller's table or of the table of a process the caller
//! controls, refused while the capability has children, mappings or bindings, which are all child
//! nodes, so a holder revokes first. What the capability said is returned, for reference counting to
//! act on. See design/sharing-by-derive/ and design/process-holds-capabilities/.
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
use crate::capability::kernel::*;
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
use crate::capability::position::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;

impl CapKernel {
    /// The refusals: an index that names no slot, a slot with no capability, the list's first node,
    /// which has depth 0, or a capability with something below it.
    pub open spec fn can_delete(&self, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& self.list.nodes@[n as int].depth > 0
        &&& self.list.childless(n)
    }

    /// The refusals of a delete at a position: one that names no capability, the list's first node,
    /// which has depth 0, or a capability with something below it. In the caller's own table that is
    /// can_delete of the position's index.
    pub open spec fn can_delete_at(&self, root: usize, at: Position) -> bool {
        let n = self.cap_at(root, at)->0;
        &&& self.cap_at(root, at) is Some
        &&& self.list.nodes@[n as int].depth > 0
        &&& self.list.childless(n)
    }

    /// What a delete of the capability at a position did, by a thread of the process whose table is at
    /// root: the delete was allowed, the node had no child, it holds no capability now, every other
    /// node is as it was, every table and every node's parent are as they were, and the step
    /// discharges a local effect for the caller, which commands the slot.
    pub open spec fn cap_deleted_at(pre: Self, post: Self, root: usize, at: Position) -> bool {
        let n = pre.cap_at(root, at)->0;
        &&& pre.can_delete_at(root, at)
        &&& forall|c: usize| !#[trigger] pre.list.is_child(n, c)
        &&& !post.is_cap(n)
        &&& Self::caps_frame(pre, post, n, n)
        &&& post.tables == pre.tables
        &&& post.list.parent@ == pre.list.parent@
        &&& discharges(pre.view(), post.view(), root, Effect::Local)
    }

    /// What deleting node n did to the object it named: a frame capability's block, or a space, thread
    /// or process capability's object's block, has one reference fewer, with n gone from its holders and
    /// every record as it was; any other node held nothing, so the blocks and the objects are as they
    /// were.
    pub open spec fn object_dropped(pre: Self, post: Self, n: usize) -> bool {
        &&& pre.is_cap(n) && pre.payload_of(n).kind is Frame ==> {
            let br = block_ref(&pre.blocks, pre.payload_of(n).base / PAGE_SZ);
            &&& blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            )
            &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].remove(n))
            &&& post.spaces == pre.spaces
            &&& post.threads == pre.threads
            &&& post.processes == pre.processes
        }
        &&& pre.is_cap(n) && pre.payload_of(n).kind is Space ==> {
            let s = pre.payload_of(n).base;
            let br = BlockRef::Small(s / PAGE_SZ);
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
            &&& post.spaces.registers == pre.spaces.registers
            &&& post.spaces.kernel_root == pre.spaces.kernel_root
            &&& post.spaces.bound == pre.spaces.bound
            &&& post.spaces.holders@ == pre.spaces.holders@.insert(s, pre.spaces.holders@[s].remove(n))
            &&& post.threads == pre.threads
            &&& post.processes == pre.processes
        }
        &&& pre.is_cap(n) && pre.payload_of(n).kind is Thread ==> {
            let t = pre.payload_of(n).base;
            let br = BlockRef::Small(t / PAGE_SZ);
            &&& blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            )
            &&& post.holders == pre.holders
            &&& post.spaces == pre.spaces
            &&& post.threads.records == pre.threads.records
            &&& post.threads.boot_thread == pre.threads.boot_thread
            &&& post.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].remove(n))
            &&& post.processes == pre.processes
        }
        &&& pre.is_cap(n) && pre.payload_of(n).kind is Process ==> {
            let p = pre.payload_of(n).base;
            let br = BlockRef::Small(p / PAGE_SZ);
            &&& blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            )
            &&& post.holders == pre.holders
            &&& post.spaces == pre.spaces
            &&& post.threads == pre.threads
            &&& post.processes.records == pre.processes.records
            &&& post.processes.spare == pre.processes.spare
            &&& post.processes.bound == pre.processes.bound
            &&& post.processes.holders@ == pre.processes.holders@.insert(p, pre.processes.holders@[p].remove(n))
        }
        &&& !(pre.is_cap(n) && (pre.payload_of(n).kind is Frame || pre.payload_of(n).kind is Space || pre.payload_of(n).kind is Thread
            || pre.payload_of(n).kind is Process))
            ==> post.blocks == pre.blocks && post.holders == pre.holders && post.spaces == pre.spaces && post.threads == pre.threads
            && post.processes == pre.processes
    }

    /// Deletes the capability at a position: an index of the caller's table, at root, or of the table
    /// of a process the caller controls, live or dead. The position comes from user space, so it can
    /// be refused, and a refusal changes nothing.
    pub fn delete(&mut self, root: usize, at: Position) -> (ret: Option<Payload>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::same_tree(*old(self), *final(self)),
            final(self).list.parent@ == old(self).list.parent@,
            ret is Some == old(self).can_delete_at(root, at),
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> ret.unwrap() == old(self).payload_of(old(self).cap_at(root, at)->0),
            ret is Some ==> Self::cap_deleted_at(*old(self), *final(self), root, at),
            ret is Some ==> Self::object_dropped(*old(self), *final(self), old(self).cap_at(root, at)->0),
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).tlb == old(self).tlb,
            final(self).iommus == old(self).iommus,
            final(self).mapped == old(self).mapped,
            final(self).tables == old(self).tables,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).table_pages == old(self).table_pages,
            final(self).mappings == old(self).mappings,
            final(self).zeroing == old(self).zeroing,
            final(self).devices == old(self).devices,
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (n, payload) = match self.find_cap(root, at) {
            Some(found) => found,
            None => { return None; },
        };
        if self.list.get(n).depth == 0 || !self.list.is_childless(n) {
            return None;
        }
        proof {
            // The list's first node has depth 0.
            assert(n != pre.list.seq@[0]);
        }
        self.list.remove_leaf(n);
        match payload.kind {
            CapKind::Frame => {
                proof {
                    lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, n);
                }
                let br = locate(&self.blocks, payload.base / PAGE_SZ);
                drop_block_ref(&mut self.blocks, br);
                self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].remove(n)));
            },
            CapKind::Space => {
                proof {
                    pre.lemma_space_cap(n);
                }
                drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / PAGE_SZ));
                self.spaces.holders = Ghost(pre.spaces.holders@.insert(payload.base, pre.spaces.holders@[payload.base].remove(n)));
            },
            CapKind::Thread => {
                proof {
                    pre.lemma_thread_cap(n);
                }
                drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / PAGE_SZ));
                self.threads.holders = Ghost(pre.threads.holders@.insert(payload.base, pre.threads.holders@[payload.base].remove(n)));
            },
            CapKind::Process => {
                proof {
                    pre.lemma_process_cap(n);
                }
                drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / PAGE_SZ));
                self.processes.holders = Ghost(pre.processes.holders@.insert(payload.base, pre.processes.holders@[payload.base].remove(n)));
            },
            _ => {},
        }
        proof {
            let post = *self;
            pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
            assert(Self::caps_frame(pre, post, n, n));
            Self::lemma_delete_caps_wf(pre, post, n);
            Self::lemma_hidden_frame(pre, post, n, n);
            Self::lemma_bindings_caps_frame(pre, post, n, n);
            Self::lemma_delete_holders(pre, post, n);
            let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == n
                && post.list.seq@ == pre.list.seq@.remove(p);
            assert(p != 0);
            assert(post.list.seq@[0] == pre.list.seq@[0]);
            lemma_parents_removed(pre.list, post.list, n);
            Self::lemma_delete_removes(pre, post, n);
            lemma_removes_cap_discharges(pre.view(), post.view(), root, n);
            Self::lemma_tlb_same(pre, post);
        }
        Some(payload)
    }

    /// The holders after node n goes, the only node that changed: a frame capability leaves its block,
    /// a space, thread or process capability leaves its object, and any other node held nothing. With them, what the
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
            Self::object_dropped(pre, post, n),
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
            let br = block_ref(&pre.blocks, pre.payload_of(n).base / PAGE_SZ);
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
            lemma_threads_refs_changed(
                &pre.list,
                &pre.tables,
                &post.list,
                &post.tables,
                &pre.threads,
                &pre.blocks,
                &post.blocks,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            );
            lemma_processes_refs_changed(
                &pre.list,
                &pre.tables,
                &post.list,
                &post.tables,
                &pre.processes,
                &pre.blocks,
                &post.blocks,
                br,
                (block_refs(&pre.blocks, br) - 1) as usize,
                block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
            );
        } else if pre.is_cap(n) && pre.payload_of(n).kind is Space {
            let s = pre.payload_of(n).base;
            let br = BlockRef::Small(s / PAGE_SZ);
            let refs = (block_refs(&pre.blocks, br) - 1) as usize;
            let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
            pre.lemma_space_cap(n);
            lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
            assert(!pre.holders@.contains_key(br)) by {
                if pre.holders@.contains_key(br) {
                    assert(pre.blocks.pages@[(s / PAGE_SZ) as int].object is Frame);
                }
            }
            lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, s / PAGE_SZ, refs, dead);
            lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, s / PAGE_SZ, refs, dead);
            lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
            assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
            lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, refs, dead);
            lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, refs, dead);
            lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
            Self::lemma_spaces_holder_dropped(pre, post, n, s);
            lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
            lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, refs, dead);
        } else if pre.is_cap(n) && pre.payload_of(n).kind is Thread {
            let t = pre.payload_of(n).base;
            let br = BlockRef::Small(t / PAGE_SZ);
            let refs = (block_refs(&pre.blocks, br) - 1) as usize;
            let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
            pre.lemma_thread_cap(n);
            lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
            assert(!pre.holders@.contains_key(br)) by {
                if pre.holders@.contains_key(br) {
                    assert(pre.blocks.pages@[(t / PAGE_SZ) as int].object is Frame);
                }
            }
            lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, t / PAGE_SZ, refs, dead);
            lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, t / PAGE_SZ, refs, dead);
            lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
            assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
            lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, t / PAGE_SZ, refs, dead);
            lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, t / PAGE_SZ, refs, dead);
            lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
            lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, refs, dead);
            Self::lemma_threads_holder_dropped(pre, post, n, t);
            lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, refs, dead);
        } else if pre.is_cap(n) && pre.payload_of(n).kind is Process {
            let p = pre.payload_of(n).base;
            let br = BlockRef::Small(p / PAGE_SZ);
            let refs = (block_refs(&pre.blocks, br) - 1) as usize;
            let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
            pre.lemma_process_cap(n);
            lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
            assert(!pre.holders@.contains_key(br)) by {
                if pre.holders@.contains_key(br) {
                    assert(pre.blocks.pages@[(p / PAGE_SZ) as int].object is Frame);
                }
            }
            lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, p / PAGE_SZ, refs, dead);
            lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, p / PAGE_SZ, refs, dead);
            lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
            assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
            lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, p / PAGE_SZ, refs, dead);
            lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, p / PAGE_SZ, refs, dead);
            lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
            lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, refs, dead);
            lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
            Self::lemma_processes_holder_dropped(pre, post, n, p);
        } else {
            lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
            lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
            lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
            lemma_spaces_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks);
            lemma_threads_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks);
            lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
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
            forall|i: usize| pre.blocks.tracks(i as int) ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
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
            post.devices.count == pre.devices.count,
            post.devices.holder == pre.devices.holder,
            post.devices == pre.devices || post.devices.wf(),
            post.devices.page == pre.devices.page,
            post.list.parent@ == pre.list.parent@,
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Device implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            assert(x != n);
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        lemma_devices_kept(&pre.list, &pre.tables, &post.list, &post.tables, &pre.devices);
        if post.devices != pre.devices {
            lemma_devices_records(&post.list, &post.tables, &pre.devices, &post.devices);
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) implies {
            &&& cap_wf(post.tables.payload_of(x))
            &&& control_named(post.tables.payload_of(x))
        } by {
            assert(x != n);
            Self::lemma_caps_frame(pre, post, n, n, x);
            assert(post.is_cap(x));
            assert(pre.tables.is_cap(&pre.list, x));
        }
    }

    /// The view of the step: one capability goes, and nothing else.
    pub proof fn lemma_delete_removes(pre: Self, post: Self, n: usize)
        requires
            post.frames@ == pre.frames@,
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            Self::caps_frame(pre, post, n, n),
            pre.is_cap(n),
            !post.list.nodes@[n as int].live,
            post.list.parent@ == pre.list.parent@,
            Self::same_tree(pre, post),
            post.devices == pre.devices,
        ensures
            removes_cap(pre.view(), post.view(), n),
    {
        let (a, b) = (pre.view(), post.view());
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
    }

    /// A capability with a child, such as a process capability with a thread's binding below it, is not
    /// deleted: delete takes only a childless capability.
    pub proof fn lemma_parent_undeletable(&self, root: usize, i: usize, c: usize)
        requires
            self.wf(),
            self.list.is_child(self.tables.node_of(root, i), c),
        ensures
            !self.can_delete(root, i),
    {
        let n = self.tables.node_of(root, i);
        if self.can_delete(root, i) {
            self.lemma_slot(root, i);
            self.lemma_slot_bound(n);
            let s = self.list.seq@;
            assert(has(s, n));
            lemma_has(s, n);
            let j = choose|j: int| 0 <= j < s.len() && s[j] == n;
            self.list.lemma_link(j);
            if j + 1 < s.len() {
                self.list.lemma_link(j + 1);
                assert(s[j + 1] != NONE);
            }
            self.list.lemma_no_child(n, j);
            assert(!self.list.is_child(n, c));
        }
    }
}

} // verus!
