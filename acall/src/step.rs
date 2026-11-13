// SPDX-License-Identifier: MIT

//! The kernel step: one system call, the one point of this crate no proof reaches. Its ensures is what
//! the kernel proves of the step it takes for a thread whose call returns to it, CapKernel::enter in
//! kernel/verified: some frame carrying the operation number, the slot and the arguments passed takes
//! the kernel from the state at entry to a middle state as `invoked` says, the calling core alone then
//! catches up on the flush epoch, and the state after is well formed, with that core holding nothing
//! stale of the caller's space. The state at entry is not the one the previous call returned: other
//! steps run between, another thread's or process's call, an ancestor's revoke, another core's
//! acknowledge, and the kernel proves of each that it keeps CapKernel::rely for every process whose
//! threads did not take it, and that the rely composes. So the step says only that the entry state is
//! well formed and one the rely relates to the state the caller token last held, and the token carries
//! that entry state so the wrappers can state their contracts from it. What stays unproven is that the
//! token was the kernel's state and the caller's root when the process was handed it, and that the
//! process's threads make every call through it. The step is the kernel-vouched form of
//! design/who-vouches-for-an-unproven-claim/.
use vstd::prelude::*;

use asys::operation;
#[cfg(verus_keep_ghost)]
use verified::arch::Registers;
#[cfg(verus_keep_ghost)]
use verified::define::NUM_CPUS;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::TlbEntry;
use verified::capability::operation::Outcome;

verus! {

/// What a process knows of the kernel as it calls: the kernel's state its last call returned, the state
/// that call entered from, and the root of its own table, which names the process to the kernel and
/// never changes. A token: its fields are private and it has
/// no constructor and no copy, so verified code holds only the one it was handed at the process's
/// start and cannot keep an old one to call with again. Only specifications read its fields, so only
/// Verus compiles them.
pub tracked struct Caller {
    #[cfg(verus_keep_ghost)]
    ghost kernel: CapKernel,
    #[cfg(verus_keep_ghost)]
    ghost entry: CapKernel,
    #[cfg(verus_keep_ghost)]
    ghost root: usize,
}

impl Caller {
    /// The kernel's state the last call returned, which the rely relates to the state the next call
    /// enters from.
    pub closed spec fn kernel(self) -> CapKernel {
        self.kernel
    }

    /// The kernel's state the last call entered from.
    pub closed spec fn entry(self) -> CapKernel {
        self.entry
    }

    /// The root of the calling process's table.
    pub closed spec fn root(self) -> usize {
        self.root
    }

    /// The kernel's state is one its steps keep: every step returns one.
    pub open spec fn wf(&self) -> bool {
        self.kernel().wf()
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

/// The core a call ran on, from `pre` to `post`: it had the space keyed at `root` loaded before the
/// call and still has it after, and it returns to the thread caught up on the flush epoch, holding no
/// translation of that space to a page no space maps. What CapKernel::enter proves of the core it runs
/// on for a call that returns to the thread, whose process's space is the one keyed at that process's
/// root. design/flush-without-waiting/.
pub open spec fn returned_on(pre: CapKernel, post: CapKernel, root: usize) -> bool {
    exists|c: int| 0 <= c < NUM_CPUS && #[trigger] pre.cores@[c].space == Some(root) && returned_clean(post, root, c)
}

/// Core `c` has the space keyed at `root` loaded in `post`, has acknowledged the flush epoch, and
/// holds no translation of that space to a page no space maps.
pub open spec fn returned_clean(post: CapKernel, root: usize, c: int) -> bool {
    &&& post.cores@[c].space == Some(root)
    &&& post.acked(c) == post.flush_epoch
    &&& forall|e: TlbEntry| #[trigger] post.tlb@[c].contains(e) && e.space == root ==> post.mapped@.contains(e.page)
}

/// What CapKernel::enter proves of core `c`'s step for a call by a thread of the process whose space
/// is keyed at `root`, with the operation in `frame`, that returns `out` to the thread: the core had
/// that space loaded, the operation took the kernel from `pre` to `mid` as `invoked` says with the space
/// still loaded, and then only core `c` changed, catching up on the flush epoch, to `post`.
pub open spec fn entered(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome, c: int, mid: CapKernel) -> bool {
    &&& 0 <= c < NUM_CPUS
    &&& pre.cores@[c].space == Some(root)
    &&& mid.cores@[c].space == Some(root)
    &&& CapKernel::invoked(pre, mid, root, frame, out)
    &&& CapKernel::only_core_changed(mid, post, c)
    &&& returned_clean(post, root, c)
}

/// The step's catching up changes nothing a contract over the caller's view reads, and the core the
/// call ran on returned clean.
pub proof fn lemma_entered(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome, c: int, mid: CapKernel)
    requires
        entered(pre, post, root, frame, out, c, mid),
    ensures
        returned_on(pre, post, root),
        forall|t: usize| #[trigger] post.table_view(t) == mid.table_view(t),
{
    assert(pre.cores@[c].space == Some(root));
}

/// Invokes the operation `number` on the capability at `slot` with arguments 1 to 5, and returns what
/// the kernel put in the status and result registers. The call enters from a well-formed state the rely
/// relates to the one the token last held, which the token now carries as its entry.
// kernel: kernel/verified/capability/operation.rs CapKernel::enter
// kernel: kernel/verified/capability/rely.rs CapKernel::lemma_rely_transitive
pub assume_specification[step](caller: &mut Tracked<Caller>, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        exists|frame: Registers, c: int, mid: CapKernel|
            carries(frame, number, slot, a1, a2, a3, a4, a5)
                && #[trigger] entered(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), frame, out, c, mid),
    no_unwind;

} // verus!

pub fn step(_caller: &mut Tracked<Caller>, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> Outcome {
    // The ABI's own: every operation may change the caller's address space, which no Rust value of
    // this crate's caller lives in unless it holds the permission the wrapper's contract speaks of.
    let (status, results) = unsafe { operation::invoke_returning(number, slot, [a1, a2, a3, a4, a5]) };
    Outcome { status, result_1: results[0], result_2: results[1], result_3: results[2], result_4: results[3] }
}
