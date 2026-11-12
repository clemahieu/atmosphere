// SPDX-License-Identifier: MIT

//! The operations on the caller's own table, each a verified call of the kernel step whose ensures is
//! the operation's contract over the caller's view, proven from the step's ensures by the operation's
//! lemma in kernel/verified/capability/caller.rs.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verified::arch::Registers;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
use verified::capability::operation::*;
#[cfg(verus_keep_ghost)]
use verified::capability::position::spec_position;

use crate::step::*;

verus! {

/// Moves the capability at the position `from` names, in the caller's own table, into the empty
/// position `to` names.
pub fn move_cap(caller: &mut Tracked<Caller>, from: u64, to: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        CapKernel::move_contract(old(caller)@.kernel(), final(caller)@.kernel(), final(caller)@.root(), spec_position(from), spec_position(to), out),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_MOVE, from, to, 0, 0, 0, 0);
    proof {
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_MOVE, from, to, 0, 0, 0, 0)
                && #[trigger] entered(pre.kernel(), caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(pre.kernel(), caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Move);
        CapKernel::lemma_move_contract(pre.kernel(), mid, pre.root(), frame, out);
    }
    out
}

/// Deletes the capability at the position `at` names, in the caller's own table.
pub fn delete(caller: &mut Tracked<Caller>, at: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        CapKernel::delete_contract(old(caller)@.kernel(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_DELETE, at, 0, 0, 0, 0, 0);
    proof {
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_DELETE, at, 0, 0, 0, 0, 0)
                && #[trigger] entered(pre.kernel(), caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(pre.kernel(), caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Delete);
        CapKernel::lemma_delete_contract(pre.kernel(), mid, pre.root(), frame, out);
    }
    out
}

/// Takes a bounded number of steps of removing everything below the capability at the position `at`
/// names, in the caller's own table: again while some is left, ok once none is.
pub fn revoke(caller: &mut Tracked<Caller>, at: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        CapKernel::revoke_contract(old(caller)@.kernel(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_REVOKE, at, 0, 0, 0, 0, 0);
    proof {
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_REVOKE, at, 0, 0, 0, 0, 0)
                && #[trigger] entered(pre.kernel(), caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(pre.kernel(), caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Revoke);
        CapKernel::lemma_revoke_contract(pre.kernel(), mid, pre.root(), frame, out);
    }
    out
}

} // verus!
