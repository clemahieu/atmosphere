// SPDX-License-Identifier: MIT

//! Power-off through a power capability: the authority to end the machine's run is a capability of
//! its own kind, which boot hands the root, design/root-process-at-boot/. The kernel accepts the
//! power-off for its entry to carry out, design/syscall-abi-in-registers/, and nothing it holds changes.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::steps::Steps;
use crate::capability::table::*;

/// A power capability's rights: power-off asks for none but the capability.
pub const POWER_RIGHTS: u32 = 0;

/// power_off's bound in the step counter: none, since it runs no loop and calls nothing counted. See
/// design/one-lock-bounded-steps/.
pub const POWER_OFF_STEPS: usize = 0;

/// The power capability, naming power's object.
pub open spec fn power_payload() -> Payload {
    Payload { kind: CapKind::Power, order: 0, rights: POWER_RIGHTS, base: POWER_OBJECT, badge: 0, priority: 0 }
}

impl CapKernel {
    /// Index i of the table at root holds a power capability.
    pub open spec fn holds_power(&self, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Power
    }

    /// Accepts a power-off through the power capability at index i of the table at root. The index
    /// comes from user space, so it can name no power capability, and then the power-off is refused. It
    /// reads the kernel and changes nothing: ending the run is the entry's, which calls the machine's
    /// shutdown once this returns true and the kernel's lock is released.
    /// design/witness-per-way-an-operation-succeeds/.
    pub fn power_off(&self, root: usize, i: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
            self.root_live(root),
        ensures
            final(steps).count <= old(steps).count + POWER_OFF_STEPS,
            ret == self.holds_power(root, i),
            discharges(self.view(), self.view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        match self.held_kind(root, i) {
            Some(CapKind::Power) => true,
            _ => false,
        }
    }
}

} // verus!
