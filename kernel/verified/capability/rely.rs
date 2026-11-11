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
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::operation::*;
use crate::capability::position::*;
use crate::capability::probe::*;
use crate::capability::reach::*;
use crate::capability::revoke::*;
use crate::capability::table::*;
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
}

} // verus!
