//! Inspect a capability the caller holds: its kind, base, order and rights come back in the result
//! words, and nothing the kernel holds changes. A process learns what boot handed it, and what its own
//! retypes and derives made, this way, design/syscall-abi-in-registers/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::operation::*;
use crate::capability::reach::*;
use crate::capability::table::*;

/// The number inspect returns in rdi for each kind of capability.
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

/// The number a kind has in inspect's rdi.
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
    }
}

/// The number a kind has in inspect's rdi.
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
    }
}

/// What inspect returns for a capability that says payload: ok, with its kind in rdi, base in rsi,
/// order in rdx and rights in r8.
pub open spec fn inspected(payload: Payload) -> Outcome {
    Outcome {
        status: STATUS_OK,
        rdi: spec_kind_number(payload.kind),
        rsi: payload.base as u64,
        rdx: payload.order as u64,
        r8: payload.rights as u64,
    }
}

impl CapKernel {
    /// Index i of the table at root holds a live capability.
    pub open spec fn can_inspect(&self, root: usize, i: usize) -> bool {
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(self.tables.node_of(root, i))
    }

    /// What inspect returns for index i of the table at root: the capability's payload when the index
    /// names a live capability, and refused otherwise.
    pub open spec fn spec_inspect(&self, root: usize, i: usize) -> Outcome {
        if self.can_inspect(root, i) {
            inspected(self.payload_of(self.tables.node_of(root, i)))
        } else {
            status_only(STATUS_REFUSED)
        }
    }

    /// Inspects the capability at index i of the table at root. The index comes from user space, so it
    /// can name no slot or an empty one, and then inspect is refused. Holding the capability is the
    /// whole authority: inspect asks for no right. Either way the kernel is unchanged.
    pub fn inspect(&self, root: usize, i: usize) -> (ret: Outcome)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret == self.spec_inspect(root, i),
            discharges(self.view(), self.view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return status_only_outcome(STATUS_REFUSED); },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return status_only_outcome(STATUS_REFUSED);
        }
        proof {
            self.lemma_slot(root, i);
            assert(self.tables.is_cap(&self.list, n));
            assert(payload == self.payload_of(n));
        }
        Outcome {
            status: STATUS_OK,
            rdi: kind_number(payload.kind),
            rsi: payload.base as u64,
            rdx: payload.order as u64,
            r8: payload.rights as u64,
        }
    }
}

} // verus!
