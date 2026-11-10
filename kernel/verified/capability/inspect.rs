//! Inspect a capability the caller holds, or one a process it controls holds: its kind, base, order
//! and rights come back in the result words, and nothing the kernel holds changes. A process learns
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
    }
}

/// What inspect returns for a capability that says payload: ok, with its kind in result 1, base in
/// result 2, order in result 3 and rights in result 4.
pub open spec fn inspected(payload: Payload) -> Outcome {
    Outcome {
        status: STATUS_OK,
        result_1: spec_kind_number(payload.kind),
        result_2: payload.base as u64,
        result_3: payload.order as u64,
        result_4: payload.rights as u64,
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

    /// What inspect returns for a position: the payload of the capability there, and refused when the
    /// position names none.
    pub open spec fn spec_inspect_at(&self, root: usize, at: Position) -> Outcome {
        match self.cap_at(root, at) {
            Some(n) => inspected(self.payload_of(n)),
            None => status_only(STATUS_REFUSED),
        }
    }

    /// Inspects the capability at a position: an index of the caller's table, at root, or of the table
    /// of a process the caller controls, live or dead. The position comes from user space, so it can
    /// name no capability, and then inspect is refused. Commanding the capability is the whole
    /// authority, holding it or controlling the process that does: inspect asks for no right of the
    /// capability itself. Either way the kernel is unchanged.
    pub fn inspect(&self, root: usize, at: Position) -> (ret: Outcome)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret == self.spec_inspect_at(root, at),
            self.cap_at(root, at) is Some ==> self.view().commands(root, self.cap_at(root, at)->0),
            discharges(self.view(), self.view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        let payload = match self.find_cap(root, at) {
            Some(found) => found.1,
            None => { return status_only_outcome(STATUS_REFUSED); },
        };
        Outcome {
            status: STATUS_OK,
            result_1: kind_number(payload.kind),
            result_2: payload.base as u64,
            result_3: payload.order as u64,
            result_4: payload.rights as u64,
        }
    }
}

} // verus!
