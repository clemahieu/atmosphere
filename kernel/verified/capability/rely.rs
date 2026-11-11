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
use crate::capability::operation::*;
use crate::capability::position::*;
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
}

} // verus!
