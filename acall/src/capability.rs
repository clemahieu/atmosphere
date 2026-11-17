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
use verified::capability::rely::{reaches_through, same_cap};

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
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() && !reaches_through(to) ==> final(caller)@.pages_wf(),
        CapKernel::move_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(from), spec_position(to), out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        !reaches_through(to) ==> CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        !reaches_through(to) ==> (old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root())),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                && ((!reaches_through(to) && (spec_position(to) is None || spec_position(to)->0.index != s))
                    || (!reaches_through(from) && spec_position(from) is Some
                        && slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), spec_position(from)->0.index))
                    || final(caller)@.entry().table_view(final(caller)@.root()).contains_key(s))
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
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
        if pre.kernel().sealed(pre.root()) {
            assert forall|s: usize|
                #[trigger] slot_names_own_space(pre.kernel(), pre.root(), s)
                    && ((!reaches_through(to) && (spec_position(to) is None || spec_position(to)->0.index != s))
                        || (!reaches_through(from) && spec_position(from) is Some
                            && slot_names_own_space(pre.kernel(), pre.root(), spec_position(from)->0.index))
                        || entry.table_view(pre.root()).contains_key(s))
                implies slot_names_own_space(caller@.kernel(), pre.root(), s) by {
                lemma_rely_keeps_slot_names_own_space(pre.kernel(), entry, pre.root(), s);
                assert(caller@.kernel().table_view(pre.root()) == mid.table_view(pre.root()));
                if mid.table_view(pre.root()).contains_key(s) {
                    if out == status_only(STATUS_OK) {
                        let f = spec_position(from)->0;
                        let d = spec_position(to)->0;
                        let src = entry.view_table_at(pre.root(), f.through)->0;
                        let dst = entry.view_table_at(pre.root(), d.through)->0;
                        if dst == pre.root() && d.index == s {
                            if entry.table_view(pre.root()).contains_key(s) {
                                entry.lemma_table_view(pre.root(), s);
                            } else {
                                assert(!reaches_through(from));
                                assert(src == pre.root());
                                lemma_rely_keeps_slot_names_own_space(pre.kernel(), entry, pre.root(), f.index);
                            }
                        } else {
                            assert(entry.table_view(pre.root()).contains_key(s));
                            assert(same_cap(mid.table_view(pre.root())[s], entry.table_view(pre.root())[s]));
                        }
                    }
                }
            };
        }
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        if !reaches_through(to) {
            if entry.move_allowed(pre.root(), spec_position(from), spec_position(to)) {
                let d = spec_position(to)->0;
                assert(d.through is None);
                entry.lemma_view_table_at(pre.root(), d.through);
                assert forall|t: usize, j: usize|
                    t != pre.root() && #[trigger] mid.table_view(t).contains_key(j)
                        && mid.table_view(t)[j].kind is Frame
                        implies exists|t2: usize, j2: usize| t2 != pre.root() && #[trigger] entry.table_view(t2).contains_key(j2)
                            && same_cap(entry.table_view(t2)[j2], mid.table_view(t)[j]) by {
                    assert(entry.table_view(t).contains_key(j));
                    assert(same_cap(entry.table_view(t)[j], mid.table_view(t)[j]));
                }
                CapKernel::lemma_frames_kept_keeps_count(entry, mid, pre.root(), pre.root(), 0);
            } else {
                CapKernel::lemma_blocks_kept_keeps_count(entry, mid, pre.root());
            }
            lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        }
        if pre.pages_wf() && !reaches_through(to) {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
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
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::delete_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
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
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_delete_keeps_count(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
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
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::revoke_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
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
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_revoke_keeps_count(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
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
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::destroy_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
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
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_destroyed_keeps_rely(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
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
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::place_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, core as usize, priority as usize, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
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
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_placed_keeps_rely(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
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
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::start_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
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
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_started_keeps_rely(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Suspends the thread the position `slot` names, in the caller's own table: a thread that is not
/// running is Inactive after, and one running on another core is stopped there, with the outcome
/// again until it is.
pub fn suspend(caller: &mut Tracked<Caller>, slot: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::suspend_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_SUSPEND, slot, 0, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_SUSPEND, slot, 0, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Suspend);
        CapKernel::lemma_suspend_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_suspended_keeps_rely(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Reads the four words of the saved frame from word `index` of the Inactive thread the control
/// capability at index `slot` of the caller's own table names, zero past the frame's end. `index` is
/// a multiple of four within the frame.
pub fn read_registers(caller: &mut Tracked<Caller>, slot: u64, index: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::read_registers_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, index, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_READ_REGISTERS, slot, index, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_READ_REGISTERS, slot, index, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::ReadRegisters);
        CapKernel::lemma_read_registers_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_blocks_kept_keeps_count(entry, mid, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Writes `words` into the saved frame from word `index` of the Inactive thread the control capability
/// at index `slot` of the caller's own table names, a word past the frame's end ignored, and makes the
/// whole frame a user frame. Refused when the program counter the frame would hold is not a user
/// address. `index` is a multiple of four within the frame.
pub fn write_registers(caller: &mut Tracked<Caller>, slot: u64, index: u64, words: [u64; 4]) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        tokens_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        old(caller)@.frames_wf() ==> final(caller)@.frames_wf(),
        CapKernel::write_registers_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, index, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_WRITE_REGISTERS, slot, index, words[0], words[1], words[2], words[3]);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_WRITE_REGISTERS, slot, index, words[0], words[1], words[2], words[3])
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::WriteRegisters);
        CapKernel::lemma_write_registers_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_registers_written_keeps_rely(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
            if pre.frames_wf() {
                lemma_frames_kept(pre, caller@);
            }
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

} // verus!
