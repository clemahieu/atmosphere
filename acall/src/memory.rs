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
use verified::capability::position::spec_position;

use crate::step::*;

verus! {

/// Retypes, on the authority of the untyped at index `untyped` of the caller's table, the block at
/// `base` as `kind`: a frame into the empty slot at index `word`, a 2M frame the same, a table page of
/// `level`, or a leaf into the root entry the position `word` names.
pub fn retype(caller: &mut Ghost<Caller>, untyped: u64, kind: u64, base: u64, word: u64, level: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root == old(caller)@.root,
        CapKernel::retype_contract(old(caller)@.kernel, final(caller)@.kernel, final(caller)@.root, kind, untyped as usize, base as usize, word, level as usize, out),
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_RETYPE, untyped, kind, base, word, level, 0);
    proof {
        let frame = choose|frame: Registers|
            carries(frame, OPERATION_RETYPE, untyped, kind, base, word, level, 0)
                && #[trigger] CapKernel::invoked(pre.kernel, caller@.kernel, pre.root, frame, out);
        lemma_number_names_one_operation(Operation::Retype);
        CapKernel::lemma_retype_contract(pre.kernel, caller@.kernel, pre.root, frame, out);
    }
    out
}

/// Derives from the capability at the position `from` names, in the caller's own table, a child with
/// `rights` and the block of `order` at `base` into the empty position `to` names.
pub fn derive(caller: &mut Ghost<Caller>, from: u64, to: u64, rights: u64, base: u64, order: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root == old(caller)@.root,
        CapKernel::derive_contract(old(caller)@.kernel, final(caller)@.kernel, final(caller)@.root, spec_position(from), spec_position(to), rights, base as usize, order, out),
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_DERIVE, from, to, rights, base, order, 0);
    proof {
        let frame = choose|frame: Registers|
            carries(frame, OPERATION_DERIVE, from, to, rights, base, order, 0)
                && #[trigger] CapKernel::invoked(pre.kernel, caller@.kernel, pre.root, frame, out);
        lemma_number_names_one_operation(Operation::Derive);
        CapKernel::lemma_derive_contract(pre.kernel, caller@.kernel, pre.root, frame, out);
    }
    out
}

/// Reads the kind, the base, the order and the rights of the capability at the position `at` names.
pub fn inspect(caller: &mut Ghost<Caller>, at: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root == old(caller)@.root,
        CapKernel::inspect_contract(old(caller)@.kernel, final(caller)@.kernel, final(caller)@.root, spec_position(at), out),
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_INSPECT, at, 0, 0, 0, 0, 0);
    proof {
        let frame = choose|frame: Registers|
            carries(frame, OPERATION_INSPECT, at, 0, 0, 0, 0, 0)
                && #[trigger] CapKernel::invoked(pre.kernel, caller@.kernel, pre.root, frame, out);
        lemma_number_names_one_operation(Operation::Inspect);
        CapKernel::lemma_inspect_contract(pre.kernel, caller@.kernel, pre.root, frame, out);
    }
    out
}

} // verus!
