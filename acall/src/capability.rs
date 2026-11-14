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
#[cfg(verus_keep_ghost)]
use verified::capability::rely::reaches_through;

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
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::move_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(from), spec_position(to), out),
        !reaches_through(to) ==> (old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root())),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_MOVE, from, to, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_MOVE, from, to, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Move);
        CapKernel::lemma_move_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        if !reaches_through(to) {
            CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        }
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
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::delete_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_DELETE, at, 0, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_DELETE, at, 0, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Delete);
        CapKernel::lemma_delete_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
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
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::revoke_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_REVOKE, at, 0, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_REVOKE, at, 0, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Revoke);
        CapKernel::lemma_revoke_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// Destroys the process or thread the control capability at index `slot` of the caller's own table
/// names. Its capabilities stay in its table, where a move whose source position names that table
/// claims them.
pub fn destroy(caller: &mut Tracked<Caller>, slot: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::destroy_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_DESTROY, slot, 0, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_DESTROY, slot, 0, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Destroy);
        CapKernel::lemma_destroy_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// Places the thread the position `slot` names, in the caller's own table, on the core whose
/// capability the position `core` names there, at `priority`.
pub fn place(caller: &mut Tracked<Caller>, slot: u64, core: u64, priority: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::place_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, core as usize, priority as usize, out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_PLACE, slot, core, priority, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_PLACE, slot, core, priority, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Place);
        CapKernel::lemma_place_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// Starts the thread the position `slot` names, in the caller's own table, on the core it is placed
/// on, at its placement's priority.
pub fn start(caller: &mut Tracked<Caller>, slot: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::start_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_START, slot, 0, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_START, slot, 0, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Start);
        CapKernel::lemma_start_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

} // verus!
