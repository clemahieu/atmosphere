// SPDX-License-Identifier: MIT

//! The rely: what steps the caller's process does not take leave of its view of its own table, so a
//! contract a syscall wrapper proves at one return still says something at the next entry. A process
//! no other process can name is sealed; while it stays sealed, its slots only leave its table, and a
//! slot that stays says what it said. Each kind of step gets a lemma that it keeps the rely. See
//! design/theorem-over-reach/ and design/process-holds-capabilities/.
use vstd::prelude::*;

verus! {

use crate::capability::caller::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::{page_of, NODE_SPACE};
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::operation::*;
use crate::capability::position::*;
use crate::capability::probe::*;
use crate::capability::reach::*;
use crate::capability::revoke::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::arch::Registers;

/// Two slots hold the same capability as the process reads it: kind, block and rights. The parent may
/// differ, since a move of an ancestor renames it.
pub open spec fn same_cap(a: SlotView, b: SlotView) -> bool {
    &&& a.kind == b.kind
    &&& a.base == b.base
    &&& a.order == b.order
    &&& a.rights == b.rights
}

impl CapKernel {
    /// A slot's capability gives authority over the process at root: it names that process, whatever
    /// its rights, or it controls a thread bound to that process.
    pub open spec fn names_process(&self, v: SlotView, root: usize) -> bool {
        let bound = bound_threads(&self.list, &self.tables);
        ||| v.kind is Process && v.base == root
        ||| {
            &&& v.kind is Thread
            &&& v.rights & right_bit(Right::Control) != 0
            &&& bound.contains_key(v.base)
            &&& bound[v.base] == root
        }
    }

    /// No table but root's holds a slot naming the process at root, so no other process can claim,
    /// delete, revoke or place through it, or make a thread of it act. What a process with no other
    /// thread waiting in the kernel holds then changes only by its own steps, or by a revoke of an
    /// ancestor it does not hold.
    pub open spec fn sealed(&self, root: usize) -> bool {
        forall|t: usize, j: usize| t != root && #[trigger] self.table_view(t).contains_key(j)
            ==> !self.names_process(self.table_view(t)[j], root)
    }

    /// From pre to post, as the process at root relies on steps it does not take: when pre is sealed
    /// for root, post is too, and every slot root's table holds in post it held in pre, with the same
    /// capability. Removal only: a slot removed and refilled would make any rule allowing additions
    /// fail to compose.
    pub open spec fn rely(pre: Self, post: Self, root: usize) -> bool {
        pre.sealed(root) ==> {
            &&& post.sealed(root)
            &&& forall|j: usize| #[trigger] post.table_view(root).contains_key(j)
                ==> pre.table_view(root).contains_key(j) && same_cap(post.table_view(root)[j], pre.table_view(root)[j])
        }
    }

    pub proof fn lemma_rely_reflexive(k: Self, root: usize)
        ensures
            Self::rely(k, k, root),
    {
    }

    pub proof fn lemma_rely_transitive(a: Self, b: Self, c: Self, root: usize)
        requires
            Self::rely(a, b, root),
            Self::rely(b, c, root),
        ensures
            Self::rely(a, c, root),
    {
        if a.sealed(root) {
            assert forall|j: usize| #[trigger] c.table_view(root).contains_key(j)
                implies a.table_view(root).contains_key(j) && same_cap(c.table_view(root)[j], a.table_view(root)[j]) by {
                assert(b.table_view(root).contains_key(j));
            }
        }
    }

    /// A revoke, by any caller, keeps the rely of every process: it takes slots and gives none, every
    /// slot it keeps says what it said, and the threads it leaves bound are bound as they were.
    pub proof fn lemma_revoke_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_revoked(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_revoke_contract(pre, post, caller, frame, out);
        let bound = bound_threads(&pre.list, &pre.tables);
        let after = bound_threads(&post.list, &post.tables);
        assert forall|x: usize| #[trigger] after.contains_key(x) implies bound.contains_key(x) && after[x] == bound[x] by {
            if post != pre {
                let at = spec_position(frame.slot());
                assert(Self::cap_revoking_at(pre, post, caller, at->0));
            }
        }
        assert forall|t: usize, j: usize| #[trigger] post.table_view(t).contains_key(j)
            implies pre.table_view(t).contains_key(j) && post.table_view(t)[j] == pre.table_view(t)[j] by {
            if !pre.revoke_allowed(caller, spec_position(frame.slot())) {
                assert(post.table_view(t) == pre.table_view(t));
            }
        }
        if pre.sealed(root) {
            assert forall|t: usize, j: usize| t != root && #[trigger] post.table_view(t).contains_key(j)
                implies !post.names_process(post.table_view(t)[j], root) by {
                let v = post.table_view(t)[j];
                assert(pre.table_view(t).contains_key(j));
                assert(!pre.names_process(pre.table_view(t)[j], root));
                if after.contains_key(v.base) {
                    assert(bound.contains_key(v.base) && after[v.base] == bound[v.base]);
                }
            }
        }
    }

    /// A delete, by any caller, keeps the rely of every process: it takes one slot and gives none, every
    /// other slot says what it said, and the bound threads are as they were.
    pub proof fn lemma_delete_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_deleted(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_delete_contract(pre, post, caller, frame, out);
        let at = spec_position(frame.slot());
        assert forall|t: usize, j: usize| #[trigger] post.table_view(t).contains_key(j)
            implies pre.table_view(t).contains_key(j) && post.table_view(t)[j] == pre.table_view(t)[j] by {
            if !pre.delete_allowed(caller, at) {
                assert(post.table_view(t) == pre.table_view(t));
            }
        }
        if pre.sealed(root) {
            assert forall|t: usize, j: usize| t != root && #[trigger] post.table_view(t).contains_key(j)
                implies !post.names_process(post.table_view(t)[j], root) by {
                assert(pre.table_view(t).contains_key(j));
                assert(!pre.names_process(pre.table_view(t)[j], root));
            }
        }
    }

    /// The table a position names, read from the view of a caller other than root, is not root's while
    /// root is sealed: reaching root's table takes a process capability naming root.
    pub proof fn lemma_sealed_table_not_root(&self, caller: usize, through: Option<usize>, root: usize)
        requires
            self.sealed(root),
            caller != root,
            self.view_table_at(caller, through) is Some,
        ensures
            self.view_table_at(caller, through)->0 != root,
    {
        if let Some(cap) = through {
            assert(self.table_view(caller).contains_key(cap));
            assert(!self.names_process(self.table_view(caller)[cap], root));
        }
    }

    /// A derive, by a caller other than root, keeps the rely of root's process: while root is sealed the
    /// caller reaches no slot of root's table, and the child it places narrows a capability naming
    /// another process, or a thread without control over root, so it names root no more than its
    /// parent did.
    pub proof fn lemma_derive_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_derive_contract(pre, post, caller, frame, out);
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        let rights = frame.argument(2);
        let base = frame.argument(3) as usize;
        let order = frame.argument(4);
        if pre.sealed(root) {
            if pre.derive_allowed(caller, from, to, rights, base, order) {
                let i = from->0.index;
                let v = pre.table_view(caller)[i];
                let table = pre.view_table_at(caller, to->0.through)->0;
                let child = derived_view(v, rights as u32, base, order as u8, pre.tables.node_of(caller, i));
                pre.lemma_sealed_table_not_root(caller, to->0.through, root);
                assert(!pre.names_process(v, root));
                let r = rights as u32;
                let b = right_bit(Right::Control);
                let vr = v.rights;
                if child.kind is Thread && r & b != 0 {
                    assert(vr & b != 0) by (bit_vector)
                        requires
                            r & !vr == 0u32,
                            r & b != 0u32;
                }
                assert(!post.names_process(child, root));
                assert forall|t: usize, j: usize| t != root && #[trigger] post.table_view(t).contains_key(j)
                    implies !post.names_process(post.table_view(t)[j], root) by {
                    if !(t == table && j == to->0.index) {
                        assert(pre.table_view(t).contains_key(j));
                        assert(!pre.names_process(pre.table_view(t)[j], root));
                    }
                }
            }
            assert(post.table_view(root) == pre.table_view(root));
        }
    }

    /// A move, by a caller other than root, keeps the rely of root's process: while root is sealed
    /// neither the source nor the destination is in root's table, root's slots say what they said but
    /// for the parent a child of the capability moved names, and the capability moved names root in its
    /// new slot no more than it did in its old one.
    pub proof fn lemma_move_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::rely(pre, post, root),
    {
        broadcast use vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;
        Self::lemma_move_contract(pre, post, caller, frame, out);
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        if pre.sealed(root) {
            if pre.move_allowed(caller, from, to) {
                let f = from->0;
                let d = to->0;
                let src = pre.view_table_at(caller, f.through)->0;
                let dst = pre.view_table_at(caller, d.through)->0;
                pre.lemma_sealed_table_not_root(caller, f.through, root);
                pre.lemma_sealed_table_not_root(caller, d.through, root);
                assert forall|j: usize| #[trigger] post.table_view(root).contains_key(j)
                    implies pre.table_view(root).contains_key(j) && same_cap(post.table_view(root)[j], pre.table_view(root)[j]) by {
                    assert(post.table_view(root) == pre.moved_table_view(src, f.index, dst, d.index, root));
                }
                assert forall|t: usize, j: usize| t != root && #[trigger] post.table_view(t).contains_key(j)
                    implies !post.names_process(post.table_view(t)[j], root) by {
                    assert(post.table_view(t) == pre.moved_table_view(src, f.index, dst, d.index, t));
                    if t == dst && j == d.index {
                        assert(!pre.names_process(pre.table_view(src)[f.index], root));
                    } else {
                        assert(pre.table_view(t).contains_key(j));
                        assert(!pre.names_process(pre.table_view(t)[j], root));
                    }
                }
            } else {
                assert(post.table_view(root) == pre.table_view(root));
            }
        }
    }

    /// A step that leaves every table's view as it was, and binds no thread it did not bind to the
    /// process it bound it to, keeps the rely of every process.
    pub proof fn lemma_views_kept_keeps_rely(pre: Self, post: Self, root: usize)
        requires
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
            ({
                let bound = bound_threads(&pre.list, &pre.tables);
                let after = bound_threads(&post.list, &post.tables);
                forall|x: usize| #[trigger] after.contains_key(x) ==> bound.contains_key(x) && after[x] == bound[x]
            }),
        ensures
            Self::rely(pre, post, root),
    {
        if pre.sealed(root) {
            assert forall|t: usize, j: usize| t != root && #[trigger] post.table_view(t).contains_key(j)
                implies !post.names_process(post.table_view(t)[j], root) by {
                assert(pre.table_view(t) == post.table_view(t));
                assert(!pre.names_process(pre.table_view(t)[j], root));
            }
        }
        assert(post.table_view(root) == pre.table_view(root));
    }

    /// A map, by any caller, keeps the rely of every process: it adds a mapping node, which is no
    /// capability and binds no thread, and leaves every slot and every other node as it was.
    pub proof fn lemma_map_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_mapped(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_map_contract(pre, post, caller, frame, out);
        let bound = bound_threads(&pre.list, &pre.tables);
        let after = bound_threads(&post.list, &post.tables);
        if pre.allows_map(caller, frame) {
            let slot = frame.slot() as usize;
            let from = frame.argument(3) as usize;
            let p = address_path(frame.argument(1));
            let a = tree_of(&pre.table_pages, &pre.spaces);
            let s = pre.payload_of(pre.tables.node_of(caller, slot)).base;
            let node = if frame.argument(2) == 1 {
                mapping_node(walk_table(a, s, p)->0, p.l1)
            } else {
                mapping_node(walk_large_table(a, s, p)->0, p.l2)
            };
            assert(post.list.nodes@[node as int].kind is Mapping);
            assert forall|x: usize| #[trigger] after.contains_key(x) implies bound.contains_key(x) && after[x] == bound[x] by {
                assert(x != node);
                assert(post.list.parent@[x] == pre.list.parent@[x]);
            }
        }
        Self::lemma_views_kept_keeps_rely(pre, post, root);
    }

    /// An unmap, by any caller, keeps the rely of every process: it kills one mapping node, which is no
    /// capability and no leaf, and leaves the tables, the parents and the bound threads as they were.
    pub proof fn lemma_unmap_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_unmapped(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_unmapped_frame(pre, post, caller, frame, out);
        Self::lemma_dead_mappings_keep_views(pre, post);
        Self::lemma_views_kept_keeps_rely(pre, post, root);
    }

    /// A step that changes the tables and the parents of no node, and changes the kind or the liveness
    /// of no node but mapping nodes it kills, leaves every table's view as it was: a mapping node is no
    /// capability, and no leaf, whose live node is hidden.
    pub proof fn lemma_dead_mappings_keep_views(pre: Self, post: Self)
        requires
            pre.wf(),
            post.tables == pre.tables,
            post.list.parent == pre.list.parent,
            forall|x: int| 0 <= x < NODE_SPACE && (#[trigger] post.list.nodes@[x].kind != pre.list.nodes@[x].kind
                || post.list.nodes@[x].live != pre.list.nodes@[x].live) ==> pre.list.nodes@[x].kind is Mapping
                && !post.list.nodes@[x].live,
        ensures
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
    {
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == pre.table_view(t).contains_key(j)
                && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == pre.table_view(t)[j]) by {
                pre.lemma_table_view(t, j);
                post.lemma_table_view(t, j);
                let leaf = pre.tables.leaf(t, index_entry(j));
                if index_ok(j) && pre.tables.roots@.contains_key(t) && leaf != NO_LEAF {
                    assert(0 <= index_entry(j) < ROOT_ENTRIES);
                    pre.tables.lemma_entry(t, index_entry(j));
                    pre.tables.lemma_leaf(&pre.list, leaf);
                    assert(page_of(leaf) == leaf);
                    pre.lemma_slot_bound(leaf);
                    if pre.list.nodes@[leaf as int].live && !(pre.list.nodes@[leaf as int].kind is Hidden) {
                        pre.lemma_unhidden_not_owned(leaf);
                    }
                    assert(post.list.nodes@[leaf as int].kind == pre.list.nodes@[leaf as int].kind
                        || !post.list.nodes@[leaf as int].live);
                    assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
                }
                if pre.tables.has_slot(&pre.list, t, j) {
                    pre.lemma_slot(t, j);
                    let x = pre.tables.node_of(t, j);
                    pre.lemma_slot_bound(x);
                    assert(post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
                        || !post.list.nodes@[x as int].live);
                    assert(post.is_cap(x) == pre.is_cap(x));
                    assert(post.list.parent@[x] == pre.list.parent@[x]);
                }
            }
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }

    /// A link, by any caller, keeps the rely of every process: it changes no node and no slot.
    pub proof fn lemma_link_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_linked(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_link_contract(pre, post, caller, frame, out);
        assert(post.list == pre.list && post.tables == pre.tables);
        Self::lemma_views_kept_keeps_rely(pre, post, root);
    }

    /// An inspect, by any caller, keeps the rely of every process: it changes nothing.
    pub proof fn lemma_inspect_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            Self::invoked(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_rely_reflexive(pre, root);
    }

    /// A probe, by any caller, keeps the rely of every process: it changes no node and no slot.
    pub proof fn lemma_probe_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_probed(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
    {
        if pre.allows_probe(caller, frame) {
            let read = choose|read: Seq<usize>| Self::probe_done(pre, post, caller, frame.slot() as usize, frame.argument(1), frame.argument(2), #[trigger] probed_of(out, read));
            assert(post.list == pre.list && post.tables == pre.tables);
        }
        Self::lemma_views_same(pre, post);
        Self::lemma_views_kept_keeps_rely(pre, post, root);
    }

    /// A retype, by a caller other than root, keeps the rely of root: the frame kinds add a frame
    /// capability to the caller's table alone, which names no process and no thread, every other kind
    /// leaves every table's view as it was, and no kind binds a thread it did not bind or rebinds one.
    pub proof fn lemma_retype_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_retype_contract(pre, post, caller, frame, out);
        let kind = frame.argument(1);
        let from = frame.slot() as usize;
        let base = frame.argument(2) as usize;
        let to = frame.argument(3) as usize;
        let parent = pre.tables.node_of(caller, from);
        let child = pre.tables.node_of(caller, to);
        let bound = bound_threads(&pre.list, &pre.tables);
        let after = bound_threads(&post.list, &post.tables);
        let added = out == status_only(STATUS_OK) && (kind == RETYPE_FRAME || kind == RETYPE_LARGE_FRAME);
        if out == status_only(STATUS_REFUSED) {
            assert(post == pre);
        } else if kind == RETYPE_FRAME || kind == RETYPE_LARGE_FRAME {
            if out == status_only(STATUS_AGAIN) {
                assert(post.list == pre.list && post.tables == pre.tables);
            } else {
                assert(pre.empty_slot(caller, to));
                assert(post.is_cap(child));
                assert(Self::caps_frame(pre, post, child, child));
                assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
                reveal(binding_parents);
                assert forall|x: usize| #[trigger] after.contains_key(x) implies bound.contains_key(x) && after[x] == bound[x] by {
                    assert(x < NODE_SPACE);
                    assert(post.list.nodes@[x as int].live && post.list.nodes@[x as int].kind is Binding);
                    assert(x != child);
                    assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Binding);
                    assert(binding_parent(&pre.list, &pre.tables, &pre.threads, x));
                    let p = pre.list.parent@[x];
                    assert(post.list.parent@[x] == p);
                    assert(pre.is_cap(p));
                    assert(p != child);
                    Self::lemma_caps_frame(pre, post, child, child, p);
                }
            }
        } else if kind == RETYPE_TABLE_PAGE {
            assert(after == bound);
        } else {
            reveal(binding_parents);
            assert forall|x: usize| #[trigger] after.contains_key(x) implies bound.contains_key(x) && after[x] == bound[x] by {
                assert(x < NODE_SPACE);
                assert(post.list.nodes@[x as int].live && post.list.nodes@[x as int].kind is Binding);
                assert(x != base);
                assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Binding);
                assert(binding_parent(&pre.list, &pre.tables, &pre.threads, x));
                let p = pre.list.parent@[x];
                assert(post.list.parent@[x] == p);
                assert(pre.is_cap(p));
                assert(post.payload_of(p) == pre.payload_of(p));
            }
        }
        if pre.sealed(root) {
            assert forall|t: usize, j: usize| t != root && #[trigger] post.table_view(t).contains_key(j)
                implies !post.names_process(post.table_view(t)[j], root) by {
                let v = post.table_view(t)[j];
                if added && t == caller && j == to {
                    assert(v.kind is Frame);
                } else {
                    assert(pre.table_view(t).contains_key(j) && v == pre.table_view(t)[j]);
                    assert(!pre.names_process(pre.table_view(t)[j], root));
                    if after.contains_key(v.base) {
                        assert(bound.contains_key(v.base) && after[v.base] == bound[v.base]);
                    }
                }
            }
        }
        assert(post.table_view(root) == pre.table_view(root));
    }

    /// A step that leaves the list and the tables as they were keeps the rely of every process: the
    /// rely reads nothing else.
    pub proof fn lemma_tables_kept_keeps_rely(pre: Self, post: Self, root: usize)
        requires
            post.list == pre.list,
            post.tables == pre.tables,
        ensures
            Self::rely(pre, post, root),
    {
        assert(bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables));
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }

    // The steps below are the kernel's entries that are no capability operation: each writes thread
    // records, cores or the TLB model and leaves the list and the tables as they were, so each keeps
    // the rely of every process, whichever core or thread took it. Thread control: start, suspend and
    // write_registers through a control capability. Scheduling: switch_in, switch_out and
    // enter_boot_thread. A flush's acknowledge. check_current, and dispatch when its caller must leave
    // or its core runs nothing. Timer and device interrupts write no state of the kernel's: their
    // handlers take no lock on it and call none of its functions.

    /// start, refused or setting the thread Runnable.
    pub proof fn lemma_start_keeps_rely(pre: Self, post: Self, t: usize, core: usize, root: usize)
        requires
            post == pre || Self::state_written(pre, post, t, ThreadState::Runnable { core }),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }

    /// suspend, refused, or with the thread's record written Inactive, or its stop pending.
    pub proof fn lemma_suspend_keeps_rely(pre: Self, post: Self, t: usize, r: ThreadRecord, root: usize)
        requires
            post == pre || Self::record_written(pre, post, t, r),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }

    /// write_registers, refused or with the thread's saved frame written.
    pub proof fn lemma_write_registers_keeps_rely(pre: Self, post: Self, t: usize, frame: Registers, root: usize)
        requires
            post == pre || Self::frame_written(pre, post, t, frame),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }

    /// switch_in, switch_out and enter_boot_thread, on any core.
    pub proof fn lemma_switch_keeps_rely(pre: Self, post: Self, c: int, t: usize, root: usize)
        requires
            Self::switch_frame(pre, post, c, t),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }

    /// acknowledge, on any core.
    pub proof fn lemma_acknowledge_keeps_rely(pre: Self, post: Self, c: int, root: usize)
        requires
            Self::only_core_changed(pre, post, c),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }

    /// check_current, on any core, and dispatch when it reaches no operation: the core's thread moved
    /// off, or nothing changed.
    pub proof fn lemma_check_current_keeps_rely(pre: Self, post: Self, c: int, frame: Registers, root: usize)
        requires
            post == pre || Self::moved_off(pre, post, c, frame),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }

    /// destroy of a process, by any caller: it sets the process's record dead and sends IPIs, and
    /// leaves the list and the tables as they were, so a destroyed process's table and every
    /// capability naming it stay until a retype tears it down.
    pub proof fn lemma_destroy_keeps_rely(pre: Self, post: Self, p: usize, root: usize)
        requires
            Self::process_destroyed(pre, post, p),
        ensures
            Self::rely(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }

    /// destroy of a thread, by any caller and from any core: it writes the thread's record Dead or
    /// dying, and leaves the list and the tables as they were.
    pub proof fn lemma_destroy_thread_keeps_rely(pre: Self, post: Self, c: usize, t: usize, root: usize)
        requires
            Self::thread_destroyed(pre, post, c, t),
        ensures
            Self::rely(pre, post, root),
    {
        assert(post.list == pre.list && post.tables == pre.tables);
        Self::lemma_tables_kept_keeps_rely(pre, post, root);
    }
}

} // verus!
