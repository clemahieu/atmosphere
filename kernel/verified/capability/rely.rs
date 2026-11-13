// SPDX-License-Identifier: MIT

//! The rely: what steps the caller's process does not take leave of what it holds, so a contract a
//! syscall wrapper proves at one return still says something at the next entry. A process no other
//! process can name is sealed; while it stays sealed, its slots only leave its table and a slot that
//! stays says what it said, its record stays, the entries of its space only leave and one that stays
//! maps what it mapped, and the count of a block only its capabilities hold does not rise. Each clause
//! has a lemma per kind of step, and each kind of step a lemma that it keeps the rely. See
//! design/theorem-over-reach/, design/process-holds-capabilities/ and
//! design/region-map-owns-the-address-space/.
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
use crate::capability::refs::*;
use crate::capability::revoke::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::arch::{FrameKind, Registers};
use crate::define::*;

/// The position a word names is reached through a process capability, in another process's table.
pub open spec fn reaches_through(word: u64) -> bool {
    spec_position(word) is Some && spec_position(word)->0.through is Some
}

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

    /// From pre to post, as the process at root relies on steps it does not take for its own table:
    /// when pre is sealed for root, post is too, and every slot root's table holds in post it held in
    /// pre, with the same capability. Removal only: a slot removed and refilled would make any rule
    /// allowing additions fail to compose.
    pub open spec fn slots_kept(pre: Self, post: Self, root: usize) -> bool {
        pre.sealed(root) ==> {
            &&& post.sealed(root)
            &&& forall|j: usize| #[trigger] post.table_view(root).contains_key(j)
                ==> pre.table_view(root).contains_key(j) && same_cap(post.table_view(root)[j], pre.table_view(root)[j])
        }
    }

    /// From pre to post, as the process at root relies on steps it does not take: while root is sealed,
    /// it stays sealed and its slots only leave its table (slots_kept), its record stays (record_kept),
    /// the entries of its space only leave (space_kept), and the count of a block that only its
    /// capabilities hold does not rise (count_kept). Every clause allows removal and no addition, an
    /// ancestor's revoke being a step root does not take, so the rely composes:
    /// lemma_rely_transitive. It says nothing of a process that is not sealed, whose holder may change
    /// all of these (design/region-map-owns-the-address-space/).
    pub open spec fn rely(pre: Self, post: Self, root: usize) -> bool {
        pre.sealed(root) ==> {
            &&& Self::slots_kept(pre, post, root)
            &&& Self::record_kept(pre, post, root)
            &&& Self::space_kept(pre, post, root)
            &&& Self::count_kept(pre, post, root)
        }
    }

    /// No capability another table holds has a slot of root's table, or the leaf holding that slot, in
    /// its run: root's capabilities and its table hang only from its own capabilities and from nodes no
    /// table holds, as the root process's hang from the list's synthetic root
    /// (design/root-process-at-boot/). No revoke by another caller then reaches them, and no move by
    /// one renames their parents.
    pub open spec fn framed(&self, root: usize) -> bool {
        forall|t: usize, i: usize, j: usize| t != root && #[trigger] self.table_view(t).contains_key(i)
            && #[trigger] self.table_view(root).contains_key(j) ==> {
                let c = self.tables.node_of(t, i);
                &&& !self.list.in_run(c, self.tables.node_of(root, j))
                &&& !self.list.in_run(c, self.tables.leaf(root, index_entry(j)))
            }
    }

    /// The root's frame fact, the special case of slots_kept: a step that keeps it for a sealed process
    /// whose table is also framed, and that its own threads did not take, leaves its table's view as
    /// it was, parents and all. Every lemma below that a kind of step keeps slots_kept, or the rely,
    /// ensures it.
    pub open spec fn root_kept(pre: Self, post: Self, root: usize) -> bool {
        pre.sealed(root) && pre.framed(root) ==> post.table_view(root) == pre.table_view(root)
    }

    pub proof fn lemma_slots_kept_reflexive(k: Self, root: usize)
        ensures
            Self::slots_kept(k, k, root),
    {
    }

    pub proof fn lemma_slots_kept_transitive(a: Self, b: Self, c: Self, root: usize)
        requires
            Self::slots_kept(a, b, root),
            Self::slots_kept(b, c, root),
        ensures
            Self::slots_kept(a, c, root),
    {
        if a.sealed(root) {
            assert forall|j: usize| #[trigger] c.table_view(root).contains_key(j)
                implies a.table_view(root).contains_key(j) && same_cap(c.table_view(root)[j], a.table_view(root)[j]) by {
                assert(b.table_view(root).contains_key(j));
            }
        }
    }

    /// A revoke, by any caller, keeps slots_kept of every process: it takes slots and gives none, every
    /// slot it keeps says what it said, and the threads it leaves bound are bound as they were.
    pub proof fn lemma_revoke_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_revoked(pre, post, caller, frame, out),
        ensures
            Self::slots_kept(pre, post, root),
            caller != root ==> Self::root_kept(pre, post, root),
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
        if caller != root && pre.sealed(root) && pre.framed(root) {
            let at = spec_position(frame.slot());
            if pre.revoke_allowed(caller, at) {
                let table = pre.view_table_at(caller, at->0.through)->0;
                let c = pre.tables.node_of(table, at->0.index);
                pre.lemma_sealed_table_not_root(caller, at->0.through, root);
                assert forall|j: usize| #[trigger] pre.table_view(root).contains_key(j)
                    implies post.table_view(root).contains_key(j) by {
                    assert(pre.table_view(table).contains_key(at->0.index));
                    assert(!pre.revokes_slot(c, root, j));
                }
            }
            assert(post.table_view(root) =~= pre.table_view(root));
        }
    }

    /// A delete, by any caller, keeps slots_kept of every process: it takes one slot and gives none, every
    /// other slot says what it said, and the bound threads are as they were.
    pub proof fn lemma_delete_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_deleted(pre, post, caller, frame, out),
        ensures
            Self::slots_kept(pre, post, root),
            caller != root ==> Self::root_kept(pre, post, root),
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

    /// A derive, by a caller other than root, keeps slots_kept of root's process: while root is sealed the
    /// caller reaches no slot of root's table, and the child it places narrows a capability naming
    /// another process, or a thread without control over root, so it names root no more than its
    /// parent did.
    pub proof fn lemma_derive_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_derive_keeps_sealed(pre, post, caller, frame, out, root);
        Self::lemma_derive_contract(pre, post, caller, frame, out);
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        if pre.sealed(root) && pre.derive_allowed(caller, from, to, frame.argument(2), frame.argument(3) as usize, frame.argument(4)) {
            pre.lemma_sealed_table_not_root(caller, to->0.through, root);
        }
    }

    /// A move, by a caller other than root, keeps slots_kept of root's process: while root is sealed
    /// neither the source nor the destination is in root's table, root's slots say what they said but
    /// for the parent a child of the capability moved names, and the capability moved names root in its
    /// new slot no more than it did in its old one.
    pub proof fn lemma_move_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        broadcast use vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;
        Self::lemma_move_keeps_sealed(pre, post, caller, frame, out, root);
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
                if pre.framed(root) {
                    let i = pre.tables.node_of(src, f.index);
                    let n = pre.tables.node_of(dst, d.index);
                    assert forall|j: usize| #[trigger] pre.table_view(root).contains_key(j)
                        implies moved_view(pre.table_view(root)[j], i, n) == pre.table_view(root)[j] by {
                        let x = pre.tables.node_of(root, j);
                        pre.lemma_table_view(root, j);
                        assert(pre.table_view(src).contains_key(f.index));
                        if pre.list.parent@[x] == i {
                            assert(pre.list.anc(pre.list.parent@[x], 0) == i);
                            assert(pre.list.anc(x, 1) == i);
                            assert(pre.list.in_run(i, x));
                        }
                    }
                    assert(post.table_view(root) == pre.moved_table_view(src, f.index, dst, d.index, root));
                    assert(post.table_view(root) =~= pre.table_view(root));
                }
            } else {
                assert(post.table_view(root) == pre.table_view(root));
            }
        }
    }

    /// A step that leaves every table's view as it was, and binds no thread it did not bind to the
    /// process it bound it to, keeps slots_kept of every process.
    pub proof fn lemma_views_kept_keeps_slots(pre: Self, post: Self, root: usize)
        requires
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
            ({
                let bound = bound_threads(&pre.list, &pre.tables);
                let after = bound_threads(&post.list, &post.tables);
                forall|x: usize| #[trigger] after.contains_key(x) ==> bound.contains_key(x) && after[x] == bound[x]
            }),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
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

    /// A map, by any caller, keeps slots_kept of every process: it adds a mapping node, which is no
    /// capability and binds no thread, and leaves every slot and every other node as it was.
    pub proof fn lemma_map_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_mapped(pre, post, caller, frame, out),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
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
        Self::lemma_views_kept_keeps_slots(pre, post, root);
    }

    /// An unmap, by any caller, keeps slots_kept of every process: it kills one mapping node, which is no
    /// capability and no leaf, and leaves the tables, the parents and the bound threads as they were.
    pub proof fn lemma_unmap_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_unmapped(pre, post, caller, frame, out),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_unmapped_frame(pre, post, caller, frame, out);
        Self::lemma_dead_mappings_keep_views(pre, post);
        Self::lemma_views_kept_keeps_slots(pre, post, root);
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

    /// A link, by any caller, keeps slots_kept of every process: it changes no node and no slot.
    pub proof fn lemma_link_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_linked(pre, post, caller, frame, out),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_link_contract(pre, post, caller, frame, out);
        assert(post.list == pre.list && post.tables == pre.tables);
        Self::lemma_views_kept_keeps_slots(pre, post, root);
    }

    /// An inspect, by any caller, keeps slots_kept of every process: it changes nothing.
    pub proof fn lemma_inspect_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            Self::invoked(pre, post, caller, frame, out),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_slots_kept_reflexive(pre, root);
    }

    /// A probe, by any caller, keeps slots_kept of every process: it changes no node and no slot.
    pub proof fn lemma_probe_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_probed(pre, post, caller, frame, out),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        if pre.allows_probe(caller, frame) {
            let read = choose|read: Seq<usize>| Self::probe_done(pre, post, caller, frame.slot() as usize, frame.argument(1), frame.argument(2), #[trigger] probed_of(out, read));
            assert(post.list == pre.list && post.tables == pre.tables);
        }
        Self::lemma_views_same(pre, post);
        Self::lemma_views_kept_keeps_slots(pre, post, root);
    }

    /// A retype, by a caller other than root, keeps slots_kept of root: the frame kinds add a frame
    /// capability to the caller's table alone, which names no process and no thread, every other kind
    /// leaves every table's view as it was, and no kind binds a thread it did not bind or rebinds one.
    pub proof fn lemma_retype_keeps_slots(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_retype_keeps_sealed(pre, post, caller, frame, out, root);
        Self::lemma_retype_contract(pre, post, caller, frame, out);
        assert(post.table_view(root) == pre.table_view(root));
    }

    /// A step that leaves the list and the tables as they were keeps slots_kept of every process: the
    /// clause reads nothing else.
    pub proof fn lemma_tables_kept_keeps_slots(pre: Self, post: Self, root: usize)
        requires
            post.list == pre.list,
            post.tables == pre.tables,
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        assert(bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables));
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }

    // The steps below are the kernel's entries that are no capability operation: each writes thread
    // records, cores or the TLB model and leaves the list and the tables as they were, so each keeps
    // slots_kept of every process, whichever core or thread took it. Thread control: start, suspend and
    // write_registers through a control capability. Scheduling: switch_in, switch_out and
    // enter_boot_thread. A flush's acknowledge. check_current, and dispatch when its caller must leave
    // or its core runs nothing. Timer and device interrupts write no state of the kernel's: their
    // handlers take no lock on it and call none of its functions.

    /// start, refused or setting the thread Runnable.
    pub proof fn lemma_start_keeps_slots(pre: Self, post: Self, t: usize, core: usize, root: usize)
        requires
            post == pre || Self::state_written(pre, post, t, ThreadState::Runnable { core }),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// suspend, refused, or with the thread's record written Inactive, or its stop pending.
    pub proof fn lemma_suspend_keeps_slots(pre: Self, post: Self, t: usize, r: ThreadRecord, root: usize)
        requires
            post == pre || Self::record_written(pre, post, t, r),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// write_registers, refused or with the thread's saved frame written.
    pub proof fn lemma_write_registers_keeps_slots(pre: Self, post: Self, t: usize, frame: Registers, root: usize)
        requires
            post == pre || Self::frame_written(pre, post, t, frame),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// switch_in, switch_out and enter_boot_thread, on any core.
    pub proof fn lemma_switch_keeps_slots(pre: Self, post: Self, c: int, t: usize, root: usize)
        requires
            Self::switch_frame(pre, post, c, t),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// acknowledge, on any core.
    pub proof fn lemma_acknowledge_keeps_slots(pre: Self, post: Self, c: int, root: usize)
        requires
            Self::only_core_changed(pre, post, c),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// check_current, on any core, and dispatch when it reaches no operation: the core's thread moved
    /// off, or nothing changed.
    pub proof fn lemma_check_current_keeps_slots(pre: Self, post: Self, c: int, frame: Registers, saved: FrameKind, root: usize)
        requires
            post == pre || Self::moved_off(pre, post, c, frame, saved),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// destroy of a process, by any caller: it sets the process's record dead and sends IPIs, and
    /// leaves the list and the tables as they were, so a destroyed process's table and every
    /// capability naming it stay until a retype tears it down.
    pub proof fn lemma_destroy_keeps_slots(pre: Self, post: Self, p: usize, root: usize)
        requires
            Self::process_destroyed(pre, post, p),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// destroy of a thread, by any caller and from any core: it writes the thread's record Dead or
    /// dying, and leaves the list and the tables as they were.
    pub proof fn lemma_destroy_thread_keeps_slots(pre: Self, post: Self, c: usize, t: usize, root: usize)
        requires
            Self::thread_destroyed(pre, post, c, t),
        ensures
            Self::slots_kept(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        assert(post.list == pre.list && post.tables == pre.tables);
        Self::lemma_tables_kept_keeps_slots(pre, post, root);
    }

    /// A derive or a move whose destination position reaches through a process capability into
    /// another table: the one kind of capability operation by which a process can unseal itself, by
    /// placing a capability that names it where another process holds it.
    pub open spec fn places_through(frame: Registers) -> bool {
        &&& spec_operation(frame.operation_number()) == Some(Operation::Derive)
            || spec_operation(frame.operation_number()) == Some(Operation::Move)
        &&& reaches_through(frame.argument(1))
    }

    /// A retype, by any caller, keeps every process sealed: the frame kinds add a frame capability,
    /// which names no process and no thread, every other kind adds no slot, and no kind binds a thread
    /// it did not bind or rebinds one.
    pub proof fn lemma_retype_keeps_sealed(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, caller, frame, out),
        ensures
            pre.sealed(root) ==> post.sealed(root),
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
        } else if kind == RETYPE_FREE {
            if out == status_only(STATUS_OK) {
                let c = choose|c: usize| c < crate::define::NUM_CPUS && #[trigger] pre.frame_freed_of(post, c, caller, from, base, frame.argument(4) as usize);
                assert(post.list == pre.list && post.tables == pre.tables);
            }
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
    }

    /// A derive keeps root sealed when the caller is another process, or root placing the child in its
    /// own table: the child goes into a table that is not root's only by another caller, which holds
    /// nothing naming root, or into root's own, which sealed does not read.
    pub proof fn lemma_derive_keeps_sealed(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, caller, frame, out),
            caller != root || !reaches_through(frame.argument(1)),
        ensures
            pre.sealed(root) ==> post.sealed(root),
    {
        Self::lemma_derive_contract(pre, post, caller, frame, out);
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        let rights = frame.argument(2);
        let base = frame.argument(3) as usize;
        let order = frame.argument(4);
        if pre.sealed(root) && pre.derive_allowed(caller, from, to, rights, base, order) {
            let i = from->0.index;
            let v = pre.table_view(caller)[i];
            let table = pre.view_table_at(caller, to->0.through)->0;
            let child = derived_view(v, rights as u32, base, order as u8, pre.tables.node_of(caller, i));
            if caller != root {
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
            } else {
                assert(table == root);
            }
            assert forall|t: usize, j: usize| t != root && #[trigger] post.table_view(t).contains_key(j)
                implies !post.names_process(post.table_view(t)[j], root) by {
                if !(t == table && j == to->0.index) {
                    assert(pre.table_view(t).contains_key(j));
                    assert(!pre.names_process(pre.table_view(t)[j], root));
                }
            }
        }
    }

    /// A move keeps root sealed when the caller is another process, or root moving into its own table,
    /// as for a derive.
    pub proof fn lemma_move_keeps_sealed(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, caller, frame, out),
            caller != root || !reaches_through(frame.argument(1)),
        ensures
            pre.sealed(root) ==> post.sealed(root),
    {
        broadcast use vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;
        Self::lemma_move_contract(pre, post, caller, frame, out);
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        if pre.sealed(root) && pre.move_allowed(caller, from, to) {
            let f = from->0;
            let d = to->0;
            let src = pre.view_table_at(caller, f.through)->0;
            let dst = pre.view_table_at(caller, d.through)->0;
            if caller != root {
                pre.lemma_sealed_table_not_root(caller, f.through, root);
                pre.lemma_sealed_table_not_root(caller, d.through, root);
            } else {
                assert(dst == root);
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
        }
    }

    /// The step a thread of the process at root takes keeps root sealed, unless it places a capability
    /// through a process capability into another table: what a call of acall's step changes in the
    /// kernel's own state between the call's entry and its return.
    pub proof fn lemma_own_step_keeps_sealed(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::invoked(pre, post, root, frame, out),
            !Self::places_through(frame),
        ensures
            pre.sealed(root) ==> post.sealed(root),
    {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Retype) => Self::lemma_retype_keeps_sealed(pre, post, root, frame, out, root),
            Some(Operation::Derive) => Self::lemma_derive_keeps_sealed(pre, post, root, frame, out, root),
            Some(Operation::Move) => Self::lemma_move_keeps_sealed(pre, post, root, frame, out, root),
            Some(Operation::Delete) => Self::lemma_delete_keeps_slots(pre, post, root, frame, out, root),
            Some(Operation::Revoke) => Self::lemma_revoke_keeps_slots(pre, post, root, frame, out, root),
            Some(Operation::Link) => Self::lemma_link_keeps_slots(pre, post, root, frame, out, root),
            Some(Operation::Map) => Self::lemma_map_keeps_slots(pre, post, root, frame, out, root),
            Some(Operation::Unmap) => Self::lemma_unmap_keeps_slots(pre, post, root, frame, out, root),
            Some(Operation::Probe) => Self::lemma_probe_keeps_slots(pre, post, root, frame, out, root),
            _ => {},
        }
    }

    /// From pre to post, as the process at root relies on steps it does not take for its own space:
    /// while root is sealed and a process, every entry its space's mapping holds in post it held in pre,
    /// with the same value. Removal only, as for its slots: an ancestor's revoke may take an entry, and
    /// no other caller can add or change one, so a page token's frame or none stays true
    /// (design/region-map-owns-the-address-space/). A process's space is keyed at its root.
    pub open spec fn space_kept(pre: Self, post: Self, root: usize) -> bool {
        pre.sealed(root) && pre.processes.records@.contains_key(root) ==> {
            let a = space_mapping(tree_of(&pre.table_pages, &pre.spaces), root);
            let b = space_mapping(tree_of(&post.table_pages, &post.spaces), root);
            forall|p: SpacePath| #[trigger] b.contains_key(p) ==> a.contains_key(p) && b[p] == a[p]
        }
    }

    pub proof fn lemma_space_kept_reflexive(k: Self, root: usize)
        ensures
            Self::space_kept(k, k, root),
    {
    }

    /// Composes where the middle state still has root sealed and a process, which slots_kept and
    /// record_kept give.
    pub proof fn lemma_space_kept_transitive(a: Self, b: Self, c: Self, root: usize)
        requires
            Self::space_kept(a, b, root),
            Self::space_kept(b, c, root),
            Self::slots_kept(a, b, root),
            a.processes.records@.contains_key(root) ==> b.processes.records@.contains_key(root),
        ensures
            Self::space_kept(a, c, root),
    {
        if a.sealed(root) && a.processes.records@.contains_key(root) {
            let ma = space_mapping(tree_of(&a.table_pages, &a.spaces), root);
            let mb = space_mapping(tree_of(&b.table_pages, &b.spaces), root);
            let mc = space_mapping(tree_of(&c.table_pages, &c.spaces), root);
            assert forall|p: SpacePath| #[trigger] mc.contains_key(p) implies ma.contains_key(p) && mc[p] == ma[p] by {
                assert(mb.contains_key(p));
            }
        }
    }

    /// A step under which no space's mapping gains or changes an entry keeps space_kept for every process.
    pub proof fn lemma_shrunk_keeps_space(pre: Self, post: Self, root: usize)
        requires
            Self::mappings_shrunk(pre, post),
        ensures
            Self::space_kept(pre, post, root),
    {
        let a = space_mapping(tree_of(&pre.table_pages, &pre.spaces), root);
        let b = space_mapping(tree_of(&post.table_pages, &post.spaces), root);
        assert forall|p: SpacePath| #[trigger] b.contains_key(p) implies a.contains_key(p) && b[p] == a[p] by {
            assert(walk(tree_of(&post.table_pages, &post.spaces), root, p) is Some);
        }
    }

    /// A step that keeps every space's mapping keeps space_kept for every process.
    pub proof fn lemma_mappings_kept_keeps_space(pre: Self, post: Self, root: usize)
        requires
            Self::mappings_kept(pre, post),
        ensures
            Self::space_kept(pre, post, root),
    {
        assert(space_mapping(tree_of(&post.table_pages, &post.spaces), root)
            == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root));
    }

    /// A revoke, by any caller, keeps space_kept of every process: it only removes entries.
    pub proof fn lemma_revoke_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_revoked(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
        Self::lemma_revoke_contract(pre, post, caller, frame, out);
        Self::lemma_shrunk_keeps_space(pre, post, root);
    }

    /// An unmap, by any caller, keeps space_kept of every process: it only removes an entry.
    pub proof fn lemma_unmap_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_unmapped(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
        Self::lemma_unmap_contract(pre, post, caller, frame, out);
        Self::lemma_shrunk_keeps_space(pre, post, root);
    }

    /// A map, by a caller other than root, keeps space_kept of root: while root is sealed the caller
    /// holds no capability naming root's process, and a space capability names no process's space, so
    /// the space it writes is another.
    pub proof fn lemma_map_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_mapped(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::space_kept(pre, post, root),
    {
        Self::lemma_map_contract(pre, post, caller, frame, out);
        if pre.sealed(root) && pre.processes.records@.contains_key(root) {
            let slot = frame.slot() as usize;
            if out == status_only(STATUS_OK) {
                let n = pre.tables.node_of(caller, slot);
                pre.lemma_table_view(caller, slot);
                assert(pre.table_view(caller).contains_key(slot));
                assert(!pre.names_process(pre.table_view(caller)[slot], root));
                pre.lemma_written_space(n);
                assert(pre.payload_of(n).base != root);
            }
        }
    }

    /// A link, by any caller, keeps space_kept of every process: it keeps every space's mapping.
    pub proof fn lemma_link_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_linked(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
        Self::lemma_link_contract(pre, post, caller, frame, out);
        Self::lemma_mappings_kept_keeps_space(pre, post, root);
    }

    /// An inspect, by any caller, keeps space_kept of every process: it changes nothing.
    pub proof fn lemma_inspect_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            Self::invoked(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// A probe, by any caller, keeps space_kept of every process: it writes nothing a mapping reads.
    pub proof fn lemma_probe_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_probed(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// A retype, by any caller, keeps space_kept of every process: it keeps every space's mapping.
    pub proof fn lemma_retype_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
        Self::lemma_retype_contract(pre, post, caller, frame, out);
        Self::lemma_mappings_kept_keeps_space(pre, post, root);
    }

    /// A derive, by any caller, keeps space_kept of every process: it leaves every space's tables as
    /// they were.
    pub proof fn lemma_derive_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// A delete, by any caller, keeps space_kept of every process: it leaves every space's tables as
    /// they were.
    pub proof fn lemma_delete_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_deleted(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// A move, by any caller, keeps space_kept of every process: it leaves every space's tables as
    /// they were.
    pub proof fn lemma_move_keeps_space(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, caller, frame, out),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    // The kernel's entries that are no capability operation, as for slots_kept above: each leaves the
    // table pages and the spaces' roots and records as they were.

    /// start, refused or setting the thread Runnable.
    pub proof fn lemma_start_keeps_space(pre: Self, post: Self, t: usize, core: usize, root: usize)
        requires
            post == pre || Self::state_written(pre, post, t, ThreadState::Runnable { core }),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// suspend, refused, or with the thread's record written Inactive, or its stop pending.
    pub proof fn lemma_suspend_keeps_space(pre: Self, post: Self, t: usize, r: ThreadRecord, root: usize)
        requires
            post == pre || Self::record_written(pre, post, t, r),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// write_registers, refused or with the thread's saved frame written.
    pub proof fn lemma_write_registers_keeps_space(pre: Self, post: Self, t: usize, frame: Registers, root: usize)
        requires
            post == pre || Self::frame_written(pre, post, t, frame),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// switch_in, switch_out and enter_boot_thread, on any core.
    pub proof fn lemma_switch_keeps_space(pre: Self, post: Self, c: int, t: usize, root: usize)
        requires
            Self::switch_frame(pre, post, c, t),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// acknowledge, on any core.
    pub proof fn lemma_acknowledge_keeps_space(pre: Self, post: Self, c: int, root: usize)
        requires
            Self::only_core_changed(pre, post, c),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// check_current, on any core, and dispatch when it reaches no operation.
    pub proof fn lemma_check_current_keeps_space(pre: Self, post: Self, c: int, frame: Registers, saved: FrameKind, root: usize)
        requires
            post == pre || Self::moved_off(pre, post, c, frame, saved),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// destroy of a process, by any caller.
    pub proof fn lemma_destroy_keeps_space(pre: Self, post: Self, p: usize, root: usize)
        requires
            Self::process_destroyed(pre, post, p),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// destroy of a thread, by any caller and from any core.
    pub proof fn lemma_destroy_thread_keeps_space(pre: Self, post: Self, c: usize, t: usize, root: usize)
        requires
            Self::thread_destroyed(pre, post, c, t),
        ensures
            Self::space_kept(pre, post, root),
    {
    }

    /// From pre to post, the process at root is still recorded: no step but the freeing of a process
    /// removes a record, and that is a step only a holder of the process's capability takes, so
    /// space_kept and count_kept, whose premise is that root is a process, compose across the steps of
    /// other callers.
    pub open spec fn record_kept(pre: Self, post: Self, root: usize) -> bool {
        pre.processes.records@.contains_key(root) ==> post.processes.records@.contains_key(root)
    }

    pub proof fn lemma_record_kept_reflexive(k: Self, root: usize)
        ensures
            Self::record_kept(k, k, root),
    {
    }

    pub proof fn lemma_record_kept_transitive(a: Self, b: Self, c: Self, root: usize)
        requires
            Self::record_kept(a, b, root),
            Self::record_kept(b, c, root),
        ensures
            Self::record_kept(a, c, root),
    {
    }

    // Each kind of step, by any caller, keeps record_kept of every process: its specification says
    // what it leaves of the records.

    pub proof fn lemma_revoke_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_revoked(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_unmap_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_unmapped(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_map_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_mapped(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_link_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_linked(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_inspect_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            Self::invoked(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_probe_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_probed(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_retype_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_derive_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_delete_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_deleted(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_move_keeps_record(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, caller, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_start_keeps_record(pre: Self, post: Self, t: usize, core: usize, root: usize)
        requires
            post == pre || Self::state_written(pre, post, t, ThreadState::Runnable { core }),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_suspend_keeps_record(pre: Self, post: Self, t: usize, r: ThreadRecord, root: usize)
        requires
            post == pre || Self::record_written(pre, post, t, r),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_write_registers_keeps_record(pre: Self, post: Self, t: usize, frame: Registers, root: usize)
        requires
            post == pre || Self::frame_written(pre, post, t, frame),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_switch_keeps_record(pre: Self, post: Self, c: int, t: usize, root: usize)
        requires
            Self::switch_frame(pre, post, c, t),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_acknowledge_keeps_record(pre: Self, post: Self, c: int, root: usize)
        requires
            Self::only_core_changed(pre, post, c),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_check_current_keeps_record(pre: Self, post: Self, c: int, frame: Registers, saved: FrameKind, root: usize)
        requires
            post == pre || Self::moved_off(pre, post, c, frame, saved),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_destroy_keeps_record(pre: Self, post: Self, p: usize, root: usize)
        requires
            Self::process_destroyed(pre, post, p),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    pub proof fn lemma_destroy_thread_keeps_record(pre: Self, post: Self, c: usize, t: usize, root: usize)
        requires
            Self::thread_destroyed(pre, post, c, t),
        ensures
            Self::record_kept(pre, post, root),
    {
    }

    /// The step a thread of the process at root takes keeps root recorded, whatever it invokes: no
    /// operation frees a process. What a call of acall's step changes in the kernel's own state between
    /// the call's entry and its return.
    pub proof fn lemma_own_step_keeps_record(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::invoked(pre, post, root, frame, out),
        ensures
            Self::record_kept(pre, post, root),
    {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Retype) => Self::lemma_retype_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Derive) => Self::lemma_derive_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Move) => Self::lemma_move_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Delete) => Self::lemma_delete_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Revoke) => Self::lemma_revoke_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Link) => Self::lemma_link_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Map) => Self::lemma_map_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Unmap) => Self::lemma_unmap_keeps_record(pre, post, root, frame, out, root),
            Some(Operation::Probe) => Self::lemma_probe_keeps_record(pre, post, root, frame, out, root),
            _ => {},
        }
    }

    /// No table but root's holds a frame capability with a page in the block br: every capability that
    /// holds br is root's, so no other caller can map a page of br or derive from a capability of it.
    pub open spec fn held_by(&self, br: BlockRef, root: usize) -> bool {
        forall|t: usize, j: usize, page: usize|
            t != root && self.table_view(t).contains_key(j) && self.table_view(t)[j].kind is Frame
                && (page as int) * PAGE_SZ < block_bytes(self.table_view(t)[j].order)
                ==> #[trigger] block_ref(&self.blocks, view_frame(self.table_view(t)[j], page)) != br
    }

    /// From pre to post, as the process at root relies on steps it does not take for the counts of its
    /// own blocks: while root is sealed, each page of a frame capability root's table holds in pre and
    /// still holds in post, whose block no other table holds a capability of, lies in that block in
    /// post, at a count no higher than it had, and still no other table holds a capability of it. A
    /// revoke of an ancestor may lower the count; no other caller can raise it, so a frame token's count
    /// stays true while its entry does (design/region-map-owns-the-address-space/).
    pub open spec fn count_kept(pre: Self, post: Self, root: usize) -> bool {
        pre.sealed(root) ==> forall|j: usize, page: usize|
            pre.table_view(root).contains_key(j) && post.table_view(root).contains_key(j)
                && pre.table_view(root)[j].kind is Frame
                && (page as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order)
                && pre.held_by(block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)), root) ==> {
                let br = block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page));
                &&& #[trigger] block_ref(&post.blocks, view_frame(pre.table_view(root)[j], page)) == br
                &&& block_refs(&post.blocks, br) <= block_refs(&pre.blocks, br)
                &&& post.held_by(br, root)
            }
    }

    /// A page of a frame capability in any table's view is tracked and lies in a typed block that
    /// counts it.
    pub proof fn lemma_view_frame_counted(&self, t: usize, j: usize, page: usize)
        requires
            self.wf(),
            self.table_view(t).contains_key(j),
            self.table_view(t)[j].kind is Frame,
            (page as int) * PAGE_SZ < block_bytes(self.table_view(t)[j].order),
        ensures
            self.blocks.tracks(view_frame(self.table_view(t)[j], page) as int),
            block_typed(&self.blocks, block_ref(&self.blocks, view_frame(self.table_view(t)[j], page))),
            block_refs(&self.blocks, block_ref(&self.blocks, view_frame(self.table_view(t)[j], page))) > 0,
    {
        self.lemma_table_view(t, j);
        let n = self.tables.node_of(t, j);
        self.lemma_frame_page(n, page);
        let br = block_ref(&self.blocks, view_frame(self.table_view(t)[j], page));
        assert(self.tables.is_cap(&self.list, n));
        assert(holders_wf(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@));
        assert(self.holders@[br].contains(n));
        if self.holders@[br].len() == 0 {
            self.holders@[br].lemma_len0_is_empty();
        }
    }

    pub proof fn lemma_count_kept_reflexive(k: Self, root: usize)
        ensures
            Self::count_kept(k, k, root),
    {
    }

    /// Composes under slots_kept, which keeps root sealed and each slot root still holds saying what
    /// it said.
    pub proof fn lemma_count_kept_transitive(a: Self, b: Self, c: Self, root: usize)
        requires
            Self::count_kept(a, b, root),
            Self::count_kept(b, c, root),
            Self::slots_kept(a, b, root),
            Self::slots_kept(b, c, root),
        ensures
            Self::count_kept(a, c, root),
    {
        if a.sealed(root) {
            assert forall|j: usize, page: usize|
                a.table_view(root).contains_key(j) && c.table_view(root).contains_key(j)
                    && a.table_view(root)[j].kind is Frame
                    && (page as int) * PAGE_SZ < block_bytes(a.table_view(root)[j].order)
                    && a.held_by(block_ref(&a.blocks, view_frame(a.table_view(root)[j], page)), root) implies {
                    let br = block_ref(&a.blocks, view_frame(a.table_view(root)[j], page));
                    &&& #[trigger] block_ref(&c.blocks, view_frame(a.table_view(root)[j], page)) == br
                    &&& block_refs(&c.blocks, br) <= block_refs(&a.blocks, br)
                    &&& c.held_by(br, root)
                } by {
                assert(b.table_view(root).contains_key(j));
                assert(same_cap(b.table_view(root)[j], a.table_view(root)[j]));
                assert(view_frame(b.table_view(root)[j], page) == view_frame(a.table_view(root)[j], page));
                assert(block_ref(&b.blocks, view_frame(a.table_view(root)[j], page))
                    == block_ref(&a.blocks, view_frame(a.table_view(root)[j], page)));
                assert(block_ref(&c.blocks, view_frame(b.table_view(root)[j], page))
                    == block_ref(&b.blocks, view_frame(b.table_view(root)[j], page)));
            }
        }
    }

    /// A step that leaves every table's view as it was and changes the block table at most in the count
    /// and the death of block x, raising a counted x's count only if some table but root's holds a
    /// capability of it, keeps count_kept for root.
    pub proof fn lemma_counted_keeps_count(pre: Self, post: Self, root: usize, x: BlockRef, refs: usize, dead: bool)
        requires
            pre.wf(),
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
            blocks_refs_changed(&pre.blocks, &post.blocks, x, refs, dead),
            (block_refs(&pre.blocks, x) > 0 ==> refs <= block_refs(&pre.blocks, x)) || !pre.held_by(x, root),
        ensures
            Self::count_kept(pre, post, root),
    {
        assert forall|j: usize, page: usize|
            pre.table_view(root).contains_key(j) && post.table_view(root).contains_key(j)
                && pre.table_view(root)[j].kind is Frame
                && (page as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order)
                && pre.held_by(block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)), root) implies {
                let br = block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page));
                &&& #[trigger] block_ref(&post.blocks, view_frame(pre.table_view(root)[j], page)) == br
                &&& block_refs(&post.blocks, br) <= block_refs(&pre.blocks, br)
                &&& post.held_by(br, root)
            } by {
            let br = block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page));
            pre.lemma_view_frame_counted(root, j, page);
            assert forall|t: usize, i: usize, p: usize|
                t != root && post.table_view(t).contains_key(i) && post.table_view(t)[i].kind is Frame
                    && (p as int) * PAGE_SZ < block_bytes(post.table_view(t)[i].order)
                    implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[i], p)) != br by {
                assert(post.table_view(t) == pre.table_view(t));
                pre.lemma_view_frame_counted(t, i, p);
                assert(block_ref(&pre.blocks, view_frame(pre.table_view(t)[i], p)) != br);
            }
        }
    }

    /// A step that leaves every table's view and the block table as they were keeps count_kept.
    pub proof fn lemma_blocks_kept_keeps_count(pre: Self, post: Self, root: usize)
        requires
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
            post.blocks == pre.blocks,
        ensures
            Self::count_kept(pre, post, root),
    {
        assert forall|j: usize, page: usize|
            pre.table_view(root).contains_key(j) && post.table_view(root).contains_key(j)
                && pre.table_view(root)[j].kind is Frame
                && (page as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order)
                && pre.held_by(#[trigger] block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)), root) implies
                post.held_by(block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)), root) by {
            let br = block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page));
            assert forall|t: usize, i: usize, p: usize|
                t != root && post.table_view(t).contains_key(i) && post.table_view(t)[i].kind is Frame
                    && (p as int) * PAGE_SZ < block_bytes(post.table_view(t)[i].order)
                    implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[i], p)) != br by {
                assert(post.table_view(t) == pre.table_view(t));
                assert(block_ref(&pre.blocks, view_frame(pre.table_view(t)[i], p)) != br);
            }
        }
    }

    /// A step that leaves the list, the tables and the block table as they were keeps count_kept.
    pub proof fn lemma_tables_blocks_kept_keeps_count(pre: Self, post: Self, root: usize)
        requires
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
        ensures
            Self::count_kept(pre, post, root),
    {
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert(post.table_view(t) =~= pre.table_view(t));
        }
        Self::lemma_blocks_kept_keeps_count(pre, post, root);
    }

    /// A map, by a caller other than root, keeps count_kept of root: the block whose count it raises
    /// holds the frame the caller maps from its own table, so some table but root's holds a
    /// capability of it.
    pub proof fn lemma_map_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_mapped(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::count_kept(pre, post, root),
    {
        let slot = frame.slot() as usize;
        let va = frame.argument(1);
        let level = frame.argument(2);
        let from = frame.argument(3) as usize;
        let page = frame.argument(4) as usize;
        Self::lemma_map_contract(pre, post, caller, frame, out);
        if pre.map_allowed(caller, slot, va, level, from, page) {
            let v = pre.table_view(caller);
            let br = block_ref(&pre.blocks, view_frame(v[from], page));
            if level == 2 {
                assert((page as int) * PAGE_SZ < (page as int) * PAGE_SZ + SIZE_2M);
            }
            assert(block_ref(&pre.blocks, view_frame(pre.table_view(caller)[from], page)) == br);
            Self::lemma_counted_keeps_count(pre, post, root, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
        } else {
            Self::lemma_blocks_kept_keeps_count(pre, post, root);
        }
    }

    /// An unmap, by any caller, keeps count_kept of every process: it lowers one block's count.
    pub proof fn lemma_unmap_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_unmapped(pre, post, caller, frame, out),
        ensures
            Self::count_kept(pre, post, root),
    {
        let slot = frame.slot() as usize;
        let va = frame.argument(1);
        let level = frame.argument(2);
        Self::lemma_unmap_contract(pre, post, caller, frame, out);
        if pre.unmap_allowed(caller, slot, va, level) {
            let s = pre.table_view(caller)[slot].base;
            let a = tree_of(&pre.table_pages, &pre.spaces);
            let br = block_ref(&pre.blocks, space_mapping(a, s)[address_path(va)].addr / PAGE_SZ);
            let refs = (block_refs(&pre.blocks, br) - 1) as usize;
            Self::lemma_counted_keeps_count(pre, post, root, br, refs, block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1);
        } else {
            Self::lemma_blocks_kept_keeps_count(pre, post, root);
        }
    }

    /// A link, by any caller, keeps count_kept of every process: it changes no slot and no block.
    pub proof fn lemma_link_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_linked(pre, post, caller, frame, out),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_link_contract(pre, post, caller, frame, out);
        Self::lemma_blocks_kept_keeps_count(pre, post, root);
    }

    /// An inspect, by any caller, keeps count_kept of every process: it changes nothing.
    pub proof fn lemma_inspect_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            Self::invoked(pre, post, caller, frame, out),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_count_kept_reflexive(pre, root);
    }

    /// A probe, by any caller, keeps count_kept of every process: it writes only accessed and dirty bits.
    pub proof fn lemma_probe_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_probed(pre, post, caller, frame, out),
        ensures
            Self::count_kept(pre, post, root),
    {
        if pre.allows_probe(caller, frame) {
            let read = choose|read: Seq<usize>| Self::probe_done(pre, post, caller, frame.slot() as usize, frame.argument(1), frame.argument(2), #[trigger] probed_of(out, read));
            assert(post.list == pre.list && post.tables == pre.tables && post.blocks == pre.blocks);
        }
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// A step keeps count_kept for root when it keeps every frame capability's pages in their blocks,
    /// raises the count of no block that only root holds and, while root is sealed, leaves in every
    /// other table only frame capabilities that some table but root's held, but for the slot at index
    /// xj of the table at xt, whose pages lie in no block that only root held.
    pub proof fn lemma_frames_kept_keeps_count(pre: Self, post: Self, root: usize, xt: usize, xj: usize)
        requires
            pre.wf(),
            forall|t: usize, j: usize, page: usize|
                pre.table_view(t).contains_key(j) && pre.table_view(t)[j].kind is Frame
                    && (page as int) * PAGE_SZ < block_bytes(pre.table_view(t)[j].order) ==> {
                    let br = block_ref(&pre.blocks, view_frame(pre.table_view(t)[j], page));
                    &&& #[trigger] block_ref(&post.blocks, view_frame(pre.table_view(t)[j], page)) == br
                    &&& block_refs(&post.blocks, br) <= block_refs(&pre.blocks, br) || !pre.held_by(br, root)
                },
            pre.sealed(root) ==> forall|t: usize, j: usize|
                t != root && !(t == xt && j == xj) && #[trigger] post.table_view(t).contains_key(j)
                    && post.table_view(t)[j].kind is Frame
                    ==> exists|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                        && same_cap(pre.table_view(t2)[j2], post.table_view(t)[j]),
            pre.sealed(root) && xt != root && post.table_view(xt).contains_key(xj) && post.table_view(xt)[xj].kind is Frame
                ==> forall|j: usize, page: usize, k: usize|
                    #![trigger block_ref(&post.blocks, view_frame(post.table_view(xt)[xj], k)), block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page))]
                    pre.table_view(root).contains_key(j) && pre.table_view(root)[j].kind is Frame
                        && (page as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order)
                        && pre.held_by(block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)), root)
                        && (k as int) * PAGE_SZ < block_bytes(post.table_view(xt)[xj].order)
                        ==> block_ref(&post.blocks, view_frame(post.table_view(xt)[xj], k))
                            != block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)),
        ensures
            Self::count_kept(pre, post, root),
    {
        if pre.sealed(root) {
            assert forall|j: usize, page: usize|
                pre.table_view(root).contains_key(j) && post.table_view(root).contains_key(j)
                    && pre.table_view(root)[j].kind is Frame
                    && (page as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order)
                    && pre.held_by(block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)), root) implies {
                    let br = block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page));
                    &&& #[trigger] block_ref(&post.blocks, view_frame(pre.table_view(root)[j], page)) == br
                    &&& block_refs(&post.blocks, br) <= block_refs(&pre.blocks, br)
                    &&& post.held_by(br, root)
                } by {
                let br = block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page));
                assert forall|t: usize, i: usize, p: usize|
                    t != root && post.table_view(t).contains_key(i) && post.table_view(t)[i].kind is Frame
                        && (p as int) * PAGE_SZ < block_bytes(post.table_view(t)[i].order)
                        implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[i], p)) != br by {
                    if !(t == xt && i == xj) {
                        let (t2, j2) = choose|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                            && same_cap(pre.table_view(t2)[j2], post.table_view(t)[i]);
                        let f = view_frame(pre.table_view(t2)[j2], p);
                        assert(f == view_frame(post.table_view(t)[i], p));
                        assert(block_ref(&pre.blocks, view_frame(pre.table_view(t2)[j2], p)) != br);
                        assert(block_ref(&post.blocks, view_frame(pre.table_view(t2)[j2], p)) == block_ref(&pre.blocks, f));
                    }
                }
            }
        }
    }

    /// A revoke, by any caller, keeps count_kept of every process: it takes slots and holders and
    /// gives none.
    pub proof fn lemma_revoke_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_revoked(pre, post, caller, frame, out),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_revoke_contract(pre, post, caller, frame, out);
        if pre.revoke_allowed(caller, spec_position(frame.slot())) {
            assert forall|t: usize, j: usize|
                t != root && #[trigger] post.table_view(t).contains_key(j) && post.table_view(t)[j].kind is Frame
                    implies exists|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                        && same_cap(pre.table_view(t2)[j2], post.table_view(t)[j]) by {
                assert(pre.table_view(t).contains_key(j));
            }
            Self::lemma_frames_kept_keeps_count(pre, post, root, root, 0);
        } else {
            Self::lemma_blocks_kept_keeps_count(pre, post, root);
        }
    }

    /// A delete, by any caller, keeps count_kept of every process: it takes one slot and at most one
    /// holder and gives none.
    pub proof fn lemma_delete_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_deleted(pre, post, caller, frame, out),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_delete_contract(pre, post, caller, frame, out);
        if pre.delete_allowed(caller, spec_position(frame.slot())) {
            assert forall|t: usize, j: usize|
                t != root && #[trigger] post.table_view(t).contains_key(j) && post.table_view(t)[j].kind is Frame
                    implies exists|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                        && same_cap(pre.table_view(t2)[j2], post.table_view(t)[j]) by {
                assert(pre.table_view(t).contains_key(j));
            }
            Self::lemma_frames_kept_keeps_count(pre, post, root, root, 0);
        } else {
            Self::lemma_blocks_kept_keeps_count(pre, post, root);
        }
    }

    /// A derive, by a caller other than root, keeps count_kept of root: the block whose count a frame's
    /// child raises holds the source, a frame of the caller's own table, and the child's pages are
    /// pages of that source, so no block that only root holds gains a count or a holder elsewhere.
    pub proof fn lemma_derive_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_derive_contract(pre, post, caller, frame, out);
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        let rights = frame.argument(2);
        let base = frame.argument(3) as usize;
        let order = frame.argument(4);
        if pre.derive_allowed(caller, from, to, rights, base, order) {
            let i = from->0.index;
            let source = pre.table_view(caller)[i];
            let table = pre.view_table_at(caller, to->0.through)->0;
            let slot = to->0.index;
            let child = derived_view(source, rights as u32, base, order as u8, pre.tables.node_of(caller, i));
            assert(post.table_view(table)[slot] == child);
            if source.kind is Frame {
                let br = block_ref(&pre.blocks, view_frame(source, 0));
                let n = vstd::arithmetic::power2::pow2(child.order as nat) as int;
                let m = vstd::arithmetic::power2::pow2(source.order as nat) as int;
                vstd::arithmetic::power2::lemma_pow2_pos(source.order as nat);
                assert(block_bytes(child.order) == n * PAGE_SZ);
                assert(block_bytes(source.order) == m * PAGE_SZ);
                assert((0usize as int) * PAGE_SZ < block_bytes(source.order));
                assert(block_ref(&pre.blocks, view_frame(pre.table_view(caller)[i], 0)) == br);
                assert(!pre.held_by(br, root));
                assert forall|t: usize, j: usize, page: usize|
                    pre.table_view(t).contains_key(j) && pre.table_view(t)[j].kind is Frame
                        && (page as int) * PAGE_SZ < block_bytes(pre.table_view(t)[j].order) implies {
                        let x = block_ref(&pre.blocks, view_frame(pre.table_view(t)[j], page));
                        &&& #[trigger] block_ref(&post.blocks, view_frame(pre.table_view(t)[j], page)) == x
                        &&& block_refs(&post.blocks, x) <= block_refs(&pre.blocks, x) || !pre.held_by(x, root)
                    } by {
                    pre.lemma_view_frame_counted(t, j, page);
                }
                if pre.sealed(root) {
                    assert forall|j: usize, page: usize, k: usize|
                        #![trigger block_ref(&post.blocks, view_frame(post.table_view(table)[slot], k)), block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page))]
                        pre.table_view(root).contains_key(j) && pre.table_view(root)[j].kind is Frame
                            && (page as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order)
                            && pre.held_by(block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)), root)
                            && (k as int) * PAGE_SZ < block_bytes(post.table_view(table)[slot].order)
                            implies block_ref(&post.blocks, view_frame(post.table_view(table)[slot], k))
                                != block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)) by {
                        // The child's page k is a page of the source, which the caller's table holds.
                        let q = (base / PAGE_SZ + k - source.base / PAGE_SZ) as usize;
                        assert(k < n);
                        assert((base + n * PAGE_SZ) / (PAGE_SZ as int) == base / PAGE_SZ + n);
                        assert((source.base + m * PAGE_SZ) / (PAGE_SZ as int) == source.base / PAGE_SZ + m);
                        assert(0 <= base / PAGE_SZ + k - source.base / PAGE_SZ < m);
                        assert((q as int) * PAGE_SZ < block_bytes(source.order));
                        assert(view_frame(child, k) == view_frame(source, q));
                        pre.lemma_view_frame_counted(caller, i, q);
                        assert(block_ref(&pre.blocks, view_frame(pre.table_view(caller)[i], q))
                            != block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], page)));
                    }
                }
            }
            assert forall|t: usize, j: usize|
                t != root && !(t == table && j == slot) && #[trigger] post.table_view(t).contains_key(j)
                    && post.table_view(t)[j].kind is Frame
                    implies exists|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                        && same_cap(pre.table_view(t2)[j2], post.table_view(t)[j]) by {
                assert(pre.table_view(t).contains_key(j));
            }
            Self::lemma_frames_kept_keeps_count(pre, post, root, table, slot);
        } else {
            Self::lemma_blocks_kept_keeps_count(pre, post, root);
        }
    }

    /// A move, by a caller other than root, keeps count_kept of root: the block table is as it was, and
    /// while root is sealed the capability moved goes from one table that is not root's to another.
    pub proof fn lemma_move_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::count_kept(pre, post, root),
    {
        broadcast use vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;
        Self::lemma_move_contract(pre, post, caller, frame, out);
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        if pre.move_allowed(caller, from, to) {
            let f = from->0;
            let d = to->0;
            let src = pre.view_table_at(caller, f.through)->0;
            let dst = pre.view_table_at(caller, d.through)->0;
            if pre.sealed(root) {
                pre.lemma_sealed_table_not_root(caller, f.through, root);
                pre.lemma_sealed_table_not_root(caller, d.through, root);
                assert forall|t: usize, j: usize|
                    t != root && #[trigger] post.table_view(t).contains_key(j) && post.table_view(t)[j].kind is Frame
                        implies exists|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                            && same_cap(pre.table_view(t2)[j2], post.table_view(t)[j]) by {
                    assert(post.table_view(t) == pre.moved_table_view(src, f.index, dst, d.index, t));
                    if t == dst && j == d.index {
                        assert(pre.table_view(src).contains_key(f.index));
                    } else {
                        assert(pre.table_view(t).contains_key(j));
                    }
                }
            }
            Self::lemma_frames_kept_keeps_count(pre, post, root, root, 0);
        } else {
            Self::lemma_blocks_kept_keeps_count(pre, post, root);
        }
    }

    /// A retype, by any caller, keeps count_kept of every process: every frame capability's block and
    /// count are as they were, and the frame it may add lies in a block no frame capability had a page
    /// in.
    pub proof fn lemma_retype_keeps_count(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, caller, frame, out),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_retype_contract(pre, post, caller, frame, out);
        let kind = frame.argument(1);
        let to = frame.argument(3) as usize;
        let added = out == status_only(STATUS_OK) && (kind == RETYPE_FRAME || kind == RETYPE_LARGE_FRAME);
        let (xt, xj) = if added { (caller, to) } else { (root, 0usize) };
        assert(post.blocks == pre.blocks || Self::frame_blocks_kept(pre, post));
        assert forall|t: usize, j: usize|
            t != root && !(t == xt && j == xj) && #[trigger] post.table_view(t).contains_key(j)
                && post.table_view(t)[j].kind is Frame
                implies exists|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                    && same_cap(pre.table_view(t2)[j2], post.table_view(t)[j]) by {
            assert(pre.table_view(t).contains_key(j));
        }
        if added {
            let v = post.table_view(caller)[to];
            assert(Self::frame_block_new(pre, post, v));
        }
        Self::lemma_frames_kept_keeps_count(pre, post, root, xt, xj);
    }

    // The kernel's entries that are no capability operation, as for slots_kept above: each leaves the
    // list, the tables and the block table as they were.

    /// start, refused or setting the thread Runnable.
    pub proof fn lemma_start_keeps_count(pre: Self, post: Self, t: usize, core: usize, root: usize)
        requires
            post == pre || Self::state_written(pre, post, t, ThreadState::Runnable { core }),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// suspend, refused, or with the thread's record written Inactive, or its stop pending.
    pub proof fn lemma_suspend_keeps_count(pre: Self, post: Self, t: usize, r: ThreadRecord, root: usize)
        requires
            post == pre || Self::record_written(pre, post, t, r),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// write_registers, refused or with the thread's saved frame written.
    pub proof fn lemma_write_registers_keeps_count(pre: Self, post: Self, t: usize, frame: Registers, root: usize)
        requires
            post == pre || Self::frame_written(pre, post, t, frame),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// switch_in, switch_out and enter_boot_thread, on any core.
    pub proof fn lemma_switch_keeps_count(pre: Self, post: Self, c: int, t: usize, root: usize)
        requires
            Self::switch_frame(pre, post, c, t),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// acknowledge, on any core.
    pub proof fn lemma_acknowledge_keeps_count(pre: Self, post: Self, c: int, root: usize)
        requires
            Self::only_core_changed(pre, post, c),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// check_current, on any core, and dispatch when it reaches no operation.
    pub proof fn lemma_check_current_keeps_count(pre: Self, post: Self, c: int, frame: Registers, saved: FrameKind, root: usize)
        requires
            post == pre || Self::moved_off(pre, post, c, frame, saved),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// destroy of a process, by any caller.
    pub proof fn lemma_destroy_keeps_count(pre: Self, post: Self, p: usize, root: usize)
        requires
            Self::process_destroyed(pre, post, p),
        ensures
            Self::count_kept(pre, post, root),
    {
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    /// destroy of a thread, by any caller and from any core.
    pub proof fn lemma_destroy_thread_keeps_count(pre: Self, post: Self, c: usize, t: usize, root: usize)
        requires
            Self::thread_destroyed(pre, post, c, t),
        ensures
            Self::count_kept(pre, post, root),
    {
        assert(post.list == pre.list && post.tables == pre.tables && post.blocks == pre.blocks);
        Self::lemma_tables_blocks_kept_keeps_count(pre, post, root);
    }

    pub proof fn lemma_rely_reflexive(k: Self, root: usize)
        ensures
            Self::rely(k, k, root),
    {
    }

    /// The rely composes: the first step keeps root sealed and its record in place, which is what the
    /// second step's clauses ask of the state they start from.
    pub proof fn lemma_rely_transitive(a: Self, b: Self, c: Self, root: usize)
        requires
            Self::rely(a, b, root),
            Self::rely(b, c, root),
        ensures
            Self::rely(a, c, root),
    {
        if a.sealed(root) {
            Self::lemma_slots_kept_transitive(a, b, c, root);
            Self::lemma_space_kept_transitive(a, b, c, root);
            Self::lemma_count_kept_transitive(a, b, c, root);
        }
    }

    // Each kind of step keeps the rely, from the lemmas above that it keeps each clause. A step that
    // adds a slot to its caller's table, an entry to the space it names or a count to a block its
    // caller holds keeps it for every process but the caller's.

    /// A revoke, by any caller: an ancestor's revoke is the step that takes root's slots, the entries of
    /// its space and the counts of its blocks, and it gives none.
    pub proof fn lemma_revoke_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_revoked(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
            caller != root ==> Self::root_kept(pre, post, root),
    {
        Self::lemma_revoke_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_revoke_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_revoke_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_revoke_keeps_count(pre, post, caller, frame, out, root);
    }

    /// A delete, by any caller.
    pub proof fn lemma_delete_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_deleted(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
            caller != root ==> Self::root_kept(pre, post, root),
    {
        Self::lemma_delete_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_delete_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_delete_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_delete_keeps_count(pre, post, caller, frame, out, root);
    }

    /// A derive, by a caller other than root: root's own derive adds a slot to its table.
    pub proof fn lemma_derive_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_derive_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_derive_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_derive_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_derive_keeps_count(pre, post, caller, frame, out, root);
    }

    /// A move, by a caller other than root: root's own move adds a slot to its table.
    pub proof fn lemma_move_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_move_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_move_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_move_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_move_keeps_count(pre, post, caller, frame, out, root);
    }

    /// A map, by a caller other than root: root's own map adds an entry to its space and raises the
    /// count of the block it maps.
    pub proof fn lemma_map_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_mapped(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_map_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_map_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_map_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_map_keeps_count(pre, post, caller, frame, out, root);
    }

    /// An unmap, by any caller.
    pub proof fn lemma_unmap_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_unmapped(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_unmap_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_unmap_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_unmap_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_unmap_keeps_count(pre, post, caller, frame, out, root);
    }

    /// A link, by any caller.
    pub proof fn lemma_link_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_linked(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_link_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_link_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_link_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_link_keeps_count(pre, post, caller, frame, out, root);
    }

    /// An inspect, by any caller.
    pub proof fn lemma_inspect_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            Self::invoked(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_inspect_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_inspect_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_inspect_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_inspect_keeps_count(pre, post, caller, frame, out, root);
    }

    /// A probe, by any caller.
    pub proof fn lemma_probe_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_probed(pre, post, caller, frame, out),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_probe_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_probe_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_probe_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_probe_keeps_count(pre, post, caller, frame, out, root);
    }

    /// A retype, by a caller other than root: root's own retype of a frame adds a slot to its table.
    pub proof fn lemma_retype_keeps_rely(pre: Self, post: Self, caller: usize, frame: Registers, out: Outcome, root: usize)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, caller, frame, out),
            caller != root,
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_retype_keeps_slots(pre, post, caller, frame, out, root);
        Self::lemma_retype_keeps_record(pre, post, caller, frame, out, root);
        Self::lemma_retype_keeps_space(pre, post, caller, frame, out, root);
        Self::lemma_retype_keeps_count(pre, post, caller, frame, out, root);
    }

    /// start, refused or setting the thread Runnable.
    pub proof fn lemma_start_keeps_rely(pre: Self, post: Self, t: usize, core: usize, root: usize)
        requires
            post == pre || Self::state_written(pre, post, t, ThreadState::Runnable { core }),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_start_keeps_slots(pre, post, t, core, root);
        Self::lemma_start_keeps_record(pre, post, t, core, root);
        Self::lemma_start_keeps_space(pre, post, t, core, root);
        Self::lemma_start_keeps_count(pre, post, t, core, root);
    }

    /// suspend, refused, or with the thread's record written Inactive, or its stop pending.
    pub proof fn lemma_suspend_keeps_rely(pre: Self, post: Self, t: usize, r: ThreadRecord, root: usize)
        requires
            post == pre || Self::record_written(pre, post, t, r),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_suspend_keeps_slots(pre, post, t, r, root);
        Self::lemma_suspend_keeps_record(pre, post, t, r, root);
        Self::lemma_suspend_keeps_space(pre, post, t, r, root);
        Self::lemma_suspend_keeps_count(pre, post, t, r, root);
    }

    /// write_registers, refused or with the thread's saved frame written.
    pub proof fn lemma_write_registers_keeps_rely(pre: Self, post: Self, t: usize, frame: Registers, root: usize)
        requires
            post == pre || Self::frame_written(pre, post, t, frame),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_write_registers_keeps_slots(pre, post, t, frame, root);
        Self::lemma_write_registers_keeps_record(pre, post, t, frame, root);
        Self::lemma_write_registers_keeps_space(pre, post, t, frame, root);
        Self::lemma_write_registers_keeps_count(pre, post, t, frame, root);
    }

    /// switch_in, switch_out and enter_boot_thread, on any core.
    pub proof fn lemma_switch_keeps_rely(pre: Self, post: Self, c: int, t: usize, root: usize)
        requires
            Self::switch_frame(pre, post, c, t),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_switch_keeps_slots(pre, post, c, t, root);
        Self::lemma_switch_keeps_record(pre, post, c, t, root);
        Self::lemma_switch_keeps_space(pre, post, c, t, root);
        Self::lemma_switch_keeps_count(pre, post, c, t, root);
    }

    /// acknowledge, on any core.
    pub proof fn lemma_acknowledge_keeps_rely(pre: Self, post: Self, c: int, root: usize)
        requires
            Self::only_core_changed(pre, post, c),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_acknowledge_keeps_slots(pre, post, c, root);
        Self::lemma_acknowledge_keeps_record(pre, post, c, root);
        Self::lemma_acknowledge_keeps_space(pre, post, c, root);
        Self::lemma_acknowledge_keeps_count(pre, post, c, root);
    }

    /// check_current, on any core, and dispatch when it reaches no operation.
    pub proof fn lemma_check_current_keeps_rely(pre: Self, post: Self, c: int, frame: Registers, saved: FrameKind, root: usize)
        requires
            post == pre || Self::moved_off(pre, post, c, frame, saved),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_check_current_keeps_slots(pre, post, c, frame, saved, root);
        Self::lemma_check_current_keeps_record(pre, post, c, frame, saved, root);
        Self::lemma_check_current_keeps_space(pre, post, c, frame, saved, root);
        Self::lemma_check_current_keeps_count(pre, post, c, frame, saved, root);
    }

    /// destroy of a process, by any caller.
    pub proof fn lemma_destroy_keeps_rely(pre: Self, post: Self, p: usize, root: usize)
        requires
            Self::process_destroyed(pre, post, p),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_destroy_keeps_slots(pre, post, p, root);
        Self::lemma_destroy_keeps_record(pre, post, p, root);
        Self::lemma_destroy_keeps_space(pre, post, p, root);
        Self::lemma_destroy_keeps_count(pre, post, p, root);
    }

    /// destroy of a thread, by any caller and from any core.
    pub proof fn lemma_destroy_thread_keeps_rely(pre: Self, post: Self, c: usize, t: usize, root: usize)
        requires
            Self::thread_destroyed(pre, post, c, t),
        ensures
            Self::rely(pre, post, root),
            Self::root_kept(pre, post, root),
    {
        Self::lemma_destroy_thread_keeps_slots(pre, post, c, t, root);
        Self::lemma_destroy_thread_keeps_record(pre, post, c, t, root);
        Self::lemma_destroy_thread_keeps_space(pre, post, c, t, root);
        Self::lemma_destroy_thread_keeps_count(pre, post, c, t, root);
    }

    /// A thread bound to the process at p, as bound_threads reads the binding, is one of the threads
    /// p's record counts as bound, and its record names p.
    pub proof fn lemma_bound_thread(&self, x: usize, p: usize)
        requires
            self.wf(),
            bound_threads(&self.list, &self.tables).contains_key(x),
            bound_threads(&self.list, &self.tables)[x] == p,
        ensures
            self.processes.records@.contains_key(p),
            self.processes.bound@[p].contains(x),
            self.threads.records@.contains_key(x),
            self.threads.records@[x].value().process == Some(p),
    {
        broadcast use vstd::set::lemma_set_filter, vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;
        assert(x < NODE_SPACE && self.list.nodes@[x as int].live && self.list.nodes@[x as int].kind is Binding);
        reveal(binding_parents);
        assert(binding_parent(&self.list, &self.tables, &self.threads, x));
    }

    /// The process at p is sealed when every capability naming it, and every capability to a thread
    /// bound to it, lies in a leaf of its own table: a slot of any other table holds a node of a leaf
    /// that table owns, so none of them.
    pub proof fn lemma_sealed_by_holders(&self, p: usize)
        requires
            self.wf(),
            forall|n: usize| #[trigger] self.processes.holders@[p].contains(n) ==> self.tables.owner@[page_of(n)].0 == p,
            forall|x: usize, n: usize| self.processes.bound@[p].contains(x) && #[trigger] self.threads.holders@[x].contains(n)
                ==> self.tables.owner@[page_of(n)].0 == p,
        ensures
            self.sealed(p),
    {
        assert forall|t: usize, j: usize| t != p && #[trigger] self.table_view(t).contains_key(j)
            implies !self.names_process(self.table_view(t)[j], p) by {
            self.lemma_table_view(t, j);
            let n = self.tables.node_of(t, j);
            self.lemma_slot(t, j);
            let v = self.table_view(t)[j];
            assert(self.is_cap(n));
            if v.kind is Process && v.base == p {
                assert(self.processes.holders@[p].contains(n));
            }
            let bound = bound_threads(&self.list, &self.tables);
            if v.kind is Thread && bound.contains_key(v.base) && bound[v.base] == p {
                self.lemma_bound_thread(v.base, p);
                assert(self.threads.holders@[v.base].contains(n));
            }
        }
    }
}

} // verus!
