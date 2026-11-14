// SPDX-License-Identifier: MIT

//! Inspect a capability the caller holds, or one a process it controls holds: its kind, base, order
//! and rights come back in the result words, with a thread's consumed cycles beside them for a thread
//! capability, and nothing the kernel holds changes. A process learns
//! what boot handed it, what its own retypes and derives made, and what a process it supervises holds,
//! this way, design/syscall-abi-in-registers/ and design/process-holds-capabilities/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::operation::*;
use crate::capability::position::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::steps::Steps;
use crate::capability::table::*;

/// The number inspect returns in result 1 for each kind of capability.
pub const CAP_KIND_UNTYPED: u64 = 0;
pub const CAP_KIND_FRAME: u64 = 1;
pub const CAP_KIND_PROCESS: u64 = 2;
pub const CAP_KIND_THREAD: u64 = 3;
pub const CAP_KIND_ENDPOINT: u64 = 4;
pub const CAP_KIND_REPLY: u64 = 5;
pub const CAP_KIND_NOTIFICATION: u64 = 6;
pub const CAP_KIND_SPACE: u64 = 7;
pub const CAP_KIND_DEVICE: u64 = 8;
pub const CAP_KIND_CONSOLE: u64 = 9;
pub const CAP_KIND_POWER: u64 = 10;
pub const CAP_KIND_CORE: u64 = 11;

/// inspect's bound in the step counter: none, since it runs no loop and calls nothing counted. See
/// design/one-lock-bounded-steps/.
pub const INSPECT_STEPS: usize = 0;

/// The number a kind has in inspect's result 1.
pub open spec fn spec_kind_number(kind: CapKind) -> u64 {
    match kind {
        CapKind::Untyped => CAP_KIND_UNTYPED,
        CapKind::Frame => CAP_KIND_FRAME,
        CapKind::Process => CAP_KIND_PROCESS,
        CapKind::Thread => CAP_KIND_THREAD,
        CapKind::Endpoint => CAP_KIND_ENDPOINT,
        CapKind::Reply => CAP_KIND_REPLY,
        CapKind::Notification => CAP_KIND_NOTIFICATION,
        CapKind::Space => CAP_KIND_SPACE,
        CapKind::Device => CAP_KIND_DEVICE,
        CapKind::Console => CAP_KIND_CONSOLE,
        CapKind::Power => CAP_KIND_POWER,
        CapKind::Core => CAP_KIND_CORE,
    }
}

/// The number a kind has in inspect's result 1.
pub fn kind_number(kind: CapKind) -> (ret: u64)
    ensures
        ret == spec_kind_number(kind),
{
    match kind {
        CapKind::Untyped => CAP_KIND_UNTYPED,
        CapKind::Frame => CAP_KIND_FRAME,
        CapKind::Process => CAP_KIND_PROCESS,
        CapKind::Thread => CAP_KIND_THREAD,
        CapKind::Endpoint => CAP_KIND_ENDPOINT,
        CapKind::Reply => CAP_KIND_REPLY,
        CapKind::Notification => CAP_KIND_NOTIFICATION,
        CapKind::Space => CAP_KIND_SPACE,
        CapKind::Device => CAP_KIND_DEVICE,
        CapKind::Console => CAP_KIND_CONSOLE,
        CapKind::Power => CAP_KIND_POWER,
        CapKind::Core => CAP_KIND_CORE,
    }
}

/// What inspect returns in the frame for a capability that says payload, whose thread has consumed
/// `consumed` cycles: ok, with its kind in result 1, base in result 2, order in result 3, rights in
/// result 4 and the consumed cycles in result 5.
pub open spec fn inspected(payload: Payload, consumed: u64) -> Outcome {
    Outcome {
        status: STATUS_OK,
        result_1: spec_kind_number(payload.kind),
        result_2: payload.base as u64,
        result_3: payload.order as u64,
        result_4: payload.rights as u64,
        result_5: consumed,
    }
}

/// The outcome of an inspect of a capability that says payload, whose thread has consumed `consumed`
/// cycles: ok, with its kind in result 1, base in result 2, order in result 3, rights in result 4 and
/// the consumed cycles in result 5.
pub fn inspect_outcome(payload: Payload, consumed: u64) -> (ret: Outcome)
    ensures
        ret == inspected(payload, consumed),
{
    Outcome {
        status: STATUS_OK,
        result_1: kind_number(payload.kind),
        result_2: payload.base as u64,
        result_3: payload.order as u64,
        result_4: payload.rights as u64,
        result_5: consumed,
    }
}

impl CapKernel {
    /// Index i of the table at root holds a live capability.
    pub open spec fn can_inspect(&self, root: usize, i: usize) -> bool {
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(self.tables.node_of(root, i))
    }

    /// The kind of the capability at index i of the table at root, for an operation whose whole
    /// authority is holding a capability of one kind. The index comes from user space, so it can name
    /// no slot or an empty one, and then there is none.
    pub fn held_kind(&self, root: usize, i: usize) -> (ret: Option<CapKind>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
            self.root_live(root),
        ensures
            ret is Some == self.can_inspect(root, i),
            ret is Some ==> ret->Some_0 == self.payload_of(self.tables.node_of(root, i)).kind,
    {
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return None;
        }
        proof {
            self.lemma_slot(root, i);
            assert(self.tables.is_cap(&self.list, n));
            assert(payload == self.payload_of(n));
        }
        Some(payload.kind)
    }

    /// ret names a capability exactly when the position holds one. inspect's ensures and
    /// spec_outcome_carried both call it: design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn inspect_found(&self, root: usize, at: Position, ret: Option<(Payload, u64)>) -> bool {
        ret is Some == self.cap_at(root, at) is Some
    }

    /// The cycles the thread a capability that says payload names has run, which inspect returns in
    /// result 5: that thread's consumed time for a thread capability, and 0 for every other kind.
    /// design/cpu-time-as-capability/.
    pub open spec fn consumed_named(&self, payload: Payload) -> u64 {
        if payload.kind is Thread {
            self.threads.records@[payload.base].value().consumed
        } else {
            0
        }
    }

    /// When ret names a capability, it is that capability's payload with the cycles consumed_named
    /// gives, and the caller commands it. inspect's ensures and spec_outcome_carried both call it:
    /// design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn inspect_reads(&self, root: usize, at: Position, ret: Option<(Payload, u64)>) -> bool {
        ret is Some ==> {
            &&& (ret->0).0 == self.payload_of(self.cap_at(root, at)->0)
            &&& (ret->0).1 == self.consumed_named((ret->0).0)
            &&& self.view().commands(root, self.cap_at(root, at)->0)
        }
    }

    /// What inspect returns in the frame for a position: the payload of the capability there, with the
    /// consumed cycles of the thread it names, and refused when the position names none.
    pub open spec fn spec_inspect_at(&self, root: usize, at: Position) -> Outcome {
        match self.cap_at(root, at) {
            Some(n) => inspected(self.payload_of(n), self.consumed_named(self.payload_of(n))),
            None => status_only(STATUS_REFUSED),
        }
    }

    /// Inspects the capability at a position: an index of the caller's table, at root, or of the table
    /// of a process the caller controls, live or dead. The position comes from user space, so it can
    /// name no capability, and then inspect returns None. Commanding the capability is the whole
    /// authority, holding it or controlling the process that does: inspect asks for no right of the
    /// capability itself. Beside the payload it returns the cycles consumed_named gives: a thread's
    /// consumed time for a thread capability, 0 for every other kind. Either way the kernel is
    /// unchanged.
    pub fn inspect(&self, root: usize, at: Position, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<(Payload, u64)>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
            self.root_live(root),
        ensures
            final(steps).count <= old(steps).count + INSPECT_STEPS,
            self.inspect_found(root, at, ret),
            self.inspect_reads(root, at, ret),
            discharges(self.view(), self.view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        let (n, payload) = match self.find_cap(root, at) {
            Some(found) => found,
            None => { return None; },
        };
        let consumed = match payload.kind {
            CapKind::Thread => {
                proof {
                    self.lemma_thread_cap(n);
                }
                self.thread_consumed(payload.base)
            },
            _ => 0,
        };
        Some((payload, consumed))
    }
}

} // verus!
