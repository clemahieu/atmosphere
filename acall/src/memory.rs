// SPDX-License-Identifier: MIT

//! The memory operations, each a verified call of the kernel step whose ensures is the operation's
//! contract over the caller's view, proven from the step's ensures by the operation's lemma in
//! kernel/verified/capability/caller.rs.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verified::arch::Registers;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
use verified::capability::operation::*;
#[cfg(verus_keep_ghost)]
use verified::capability::position::*;
#[cfg(verus_keep_ghost)]
use verified::capability::rely::reaches_through;

use crate::step::*;

verus! {

/// The calling core's catching up, from `mid` to `post`, changes nothing the additional facts of
/// retype's contract for a frame read, so they hold of `post` when they hold of `mid`.
proof fn lemma_returned_retype_frame_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize, from: usize, base: usize, to: usize)
    requires
        CapKernel::only_core_changed(mid, post, c),
    ensures
        CapKernel::retype_frame_contract_fields(pre, mid, root, from, base, to)
            ==> CapKernel::retype_frame_contract_fields(pre, post, root, from, base, to),
{
    reveal(CapKernel::retype_frame_contract_fields);
}

/// The same of the additional facts of retype's contract for a table page.
proof fn lemma_returned_retype_table_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, base: usize)
    requires
        CapKernel::only_core_changed(mid, post, c),
    ensures
        CapKernel::retype_table_contract_fields(pre, mid, base) ==> CapKernel::retype_table_contract_fields(pre, post, base),
{
    reveal(CapKernel::retype_table_contract_fields);
}

/// The same of the additional facts of inspect's contract.
proof fn lemma_returned_inspect_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int)
    requires
        CapKernel::only_core_changed(mid, post, c),
    ensures
        CapKernel::inspect_contract_fields(pre, mid) ==> CapKernel::inspect_contract_fields(pre, post),
{
    reveal(CapKernel::inspect_contract_fields);
}

/// The same of the additional facts of link's contract.
proof fn lemma_returned_link_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int)
    requires
        CapKernel::only_core_changed(mid, post, c),
    ensures
        CapKernel::link_contract_fields(pre, mid) ==> CapKernel::link_contract_fields(pre, post),
{
    reveal(CapKernel::link_contract_fields);
}

/// The same of the additional facts of map's contract.
proof fn lemma_returned_map_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize)
    requires
        CapKernel::only_core_changed(mid, post, c),
    ensures
        CapKernel::map_contract_fields(pre, mid, root, slot, va, level, from, page)
            ==> CapKernel::map_contract_fields(pre, post, root, slot, va, level, from, page),
{
    reveal(CapKernel::map_contract_fields);
}

/// The same of the additional facts of unmap's contract.
proof fn lemma_returned_unmap_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize, slot: usize, va: u64)
    requires
        CapKernel::only_core_changed(mid, post, c),
    ensures
        CapKernel::unmap_contract_fields(pre, mid, root, slot, va) ==> CapKernel::unmap_contract_fields(pre, post, root, slot, va),
{
    reveal(CapKernel::unmap_contract_fields);
}

/// Retypes, on the authority of the untyped at index `untyped` of the caller's table, the block at
/// `base` as `kind`: a frame into the empty slot at index `word`, a 2M frame the same, a table page of
/// `level`, or a leaf into the root entry the position `word` names.
pub fn retype(caller: &mut Tracked<Caller>, untyped: u64, kind: u64, base: u64, word: u64, level: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::retype_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), kind, untyped as usize, base as usize, word, level as usize, out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_RETYPE, untyped, kind, base, word, level, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_RETYPE, untyped, kind, base, word, level, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Retype);
        CapKernel::lemma_retype_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_retype_frame_fields(entry, mid, caller@.kernel(), c, pre.root(), untyped as usize, base as usize, word as usize);
        lemma_returned_retype_table_fields(entry, mid, caller@.kernel(), c, base as usize);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// Derives from the capability at the position `from` names, in the caller's own table, a child with
/// `rights` and the block of `order` at `base` into the empty position `to` names.
pub fn derive(caller: &mut Tracked<Caller>, from: u64, to: u64, rights: u64, base: u64, order: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::derive_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(from), spec_position(to), rights, base as usize, order, out),
        !reaches_through(to) ==> (old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root())),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_DERIVE, from, to, rights, base, order, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_DERIVE, from, to, rights, base, order, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Derive);
        CapKernel::lemma_derive_contract(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        if !reaches_through(to) {
            CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        }
    }
    out
}

/// Reads the kind, the base, the order and the rights of the capability at the position `at` names.
pub fn inspect(caller: &mut Tracked<Caller>, at: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::inspect_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_INSPECT, at, 0, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_INSPECT, at, 0, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Inspect);
        CapKernel::lemma_inspect_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_inspect_fields(entry, mid, caller@.kernel(), c);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// Links the unlinked table page at `child`, covered by the untyped at index `from` of the caller's
/// table, into the entry at `level` that the address `va` names in the space of the capability at index
/// `slot`.
pub fn link(caller: &mut Tracked<Caller>, slot: u64, va: u64, level: u64, from: u64, child: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::link_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, level, from as usize, child as usize, out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_LINK, slot, va, level, from, child, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_LINK, slot, va, level, from, child, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Link);
        CapKernel::lemma_link_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_link_fields(entry, mid, caller@.kernel(), c);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// Maps the page at offset `page` of the frame capability at index `from` of the caller's table into
/// the entry at `level` that the address `va` names in the space of the capability at index `slot`.
pub fn map(caller: &mut Tracked<Caller>, slot: u64, va: u64, level: u64, from: u64, page: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::map_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, level, from as usize, page as usize, out),
        returned_on(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_MAP, slot, va, level, from, page, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_MAP, slot, va, level, from, page, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Map);
        CapKernel::lemma_map_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_map_fields(entry, mid, caller@.kernel(), c, pre.root(), slot as usize, va, level, from as usize, page as usize);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// Unmaps the level 1 entry at `level` that the address `va` names in the space of the capability at
/// index `slot`.
pub fn unmap(caller: &mut Tracked<Caller>, slot: u64, va: u64, level: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        CapKernel::unmap_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, level, out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_UNMAP, slot, va, level, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_UNMAP, slot, va, level, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Unmap);
        CapKernel::lemma_unmap_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_unmap_fields(entry, mid, caller@.kernel(), c, pre.root(), slot as usize, va);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
    }
    out
}

/// A word no wider than an index names the slot at that index of the caller's own table.
pub proof fn lemma_own_position(word: u64)
    requires
        word <= POSITION_INDEX_MASK,
    ensures
        spec_position(word) == Some(Position { through: None, index: word as usize }),
{
    assert(word >> 32u64 == 0) by (bit_vector)
        requires
            word <= 0xffffu64;
    assert((word >> 16u64) & 0xffffu64 == 0) by (bit_vector)
        requires
            word <= 0xffffu64;
    assert(word & 0xffffu64 == word) by (bit_vector)
        requires
            word <= 0xffffu64;
}

} // verus!
