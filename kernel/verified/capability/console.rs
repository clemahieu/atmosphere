//! Print through a console capability: the words of the invocation go to the serial port, and nothing
//! the kernel holds changes. Debug print is an operation on a console capability that takes words, as
//! design/syscall-abi-in-registers/ makes it; the root holds the console, design/root-process-at-boot/.
use vstd::prelude::*;

verus! {

use crate::arch::serial_write;
use crate::capability::inspect::*;
use crate::capability::kernel::*;
use crate::capability::operation::*;
use crate::capability::reach::*;
use crate::capability::steps::Steps;
use crate::capability::table::*;

/// A console capability's rights: print asks for none but the capability.
pub const CONSOLE_RIGHTS: u32 = 0;

/// The most bytes one print writes: five words of eight bytes. The serial write is a unit per byte.
pub const PRINT_BYTES: usize = 40;

/// The console capability, naming the console's object.
pub open spec fn console_payload() -> Payload {
    Payload { kind: CapKind::Console, order: 0, rights: CONSOLE_RIGHTS, base: CONSOLE_OBJECT, badge: 0, reserved: 0 }
}

impl CapKernel {
    /// Index i of the table at root holds a console capability.
    pub open spec fn holds_console(&self, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Console
    }

    /// Writes the bytes the five words carry to the serial port, through the console capability at index
    /// i of the table at root; asys's PRINT says how the words carry bytes. The index comes from user
    /// space, so it can name no console, and then print is refused. Either way the kernel is unchanged.
    pub fn print(&mut self, root: usize, i: usize, a: u64, b: u64, c: u64, d: u64, e: u64, Tracked(steps): Tracked<&mut Steps>) -> (status: u64)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(steps).count <= old(steps).count + PRINT_BYTES,
            *final(self) == *old(self),
            status == if old(self).holds_console(root, i) { STATUS_OK } else { STATUS_REFUSED },
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        match self.held_kind(root, i) {
            Some(CapKind::Console) => {
                serial_write(a, b, c, d, e, Tracked(steps));
                STATUS_OK
            },
            _ => STATUS_REFUSED,
        }
    }
}

} // verus!
