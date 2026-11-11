// SPDX-License-Identifier: MIT

//! The kernel step: one system call, the one point of this crate no proof reaches. Its ensures is what
//! the kernel proves of the step it takes for a thread whose call returns to it, Kernel::dispatch in
//! kernel/verified: some frame carrying the operation number, the slot and the arguments passed takes
//! the kernel from the state before to the state after as `invoked` says, and the state after is well
//! formed. The ghost caller threads the kernel's state from one call to the next. See
//! design/divider-proven-by-invariant/.
use vstd::prelude::*;

use asys::operation;
#[cfg(verus_keep_ghost)]
use verified::arch::Registers;
use verified::capability::kernel::CapKernel;
use verified::capability::operation::Outcome;

verus! {

/// What a process knows of the kernel as it calls: the kernel's state, and the root of its own table,
/// which names the process to the kernel and never changes.
pub ghost struct Caller {
    pub kernel: CapKernel,
    pub root: usize,
}

impl Caller {
    /// The kernel's state is one its steps keep: every step starts from one.
    pub open spec fn wf(&self) -> bool {
        self.kernel.wf()
    }
}

/// The frame carries this operation number, this slot and these arguments 1 to 5 where the kernel
/// reads them.
pub open spec fn carries(frame: Registers, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> bool {
    &&& frame.operation_number() == number
    &&& frame.slot() == slot
    &&& frame.argument(1) == a1
    &&& frame.argument(2) == a2
    &&& frame.argument(3) == a3
    &&& frame.argument(4) == a4
    &&& frame.argument(5) == a5
}

/// Invokes the operation `number` on the capability at `slot` with arguments 1 to 5, and returns what
/// the kernel put in the status and result registers.
#[verifier::external_body]
// external_body(glue): the system call instruction, whose ensures is what Kernel::dispatch proves of a step that returns to the calling thread
pub fn step(caller: &mut Ghost<Caller>, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root == old(caller)@.root,
        exists|frame: Registers|
            carries(frame, number, slot, a1, a2, a3, a4, a5)
                && #[trigger] CapKernel::invoked(old(caller)@.kernel, final(caller)@.kernel, final(caller)@.root, frame, out),
{
    // The ABI's own: every operation may change the caller's address space, which no Rust value of
    // this crate's caller lives in unless it holds the permission the wrapper's contract speaks of.
    let (status, results) = unsafe { operation::invoke_returning(number, slot, [a1, a2, a3, a4, a5]) };
    Outcome { status, result_1: results[0], result_2: results[1], result_3: results[2], result_4: results[3] }
}

} // verus!
