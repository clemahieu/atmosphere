//! Print and power-off through a console capability: print's words go to the serial port, a power-off
//! is accepted for the kernel's entry to carry out, and nothing the kernel holds changes. Both are
//! operations on a console capability, as design/syscall-abi-in-registers/ makes them; the root holds
//! the console, design/root-process-at-boot/.
use vstd::prelude::*;

verus! {

use crate::arch::serial_write;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::operation::*;
use crate::capability::reach::*;
use crate::capability::table::*;

/// A console capability's rights: print and power-off ask for none but the capability.
pub const CONSOLE_RIGHTS: u32 = 0;

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

    /// Whether index i of the table at root holds a console capability. The index comes from user
    /// space, so it can name no slot, an empty one or a capability of another kind.
    fn console_held(&self, root: usize, i: usize) -> (held: bool)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            held == self.holds_console(root, i),
    {
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return false; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return false;
        }
        proof {
            self.lemma_slot(root, i);
            assert(self.tables.is_cap(&self.list, n));
            assert(payload == self.payload_of(n));
        }
        match payload.kind {
            CapKind::Console => true,
            _ => false,
        }
    }

    /// Writes the bytes the five words carry to the serial port, through the console capability at index
    /// i of the table at root; asys's PRINT says how the words carry bytes. The index comes from user
    /// space, so it can name no console, and then print is refused. Either way the kernel is unchanged.
    pub fn print(&mut self, root: usize, i: usize, a: u64, b: u64, c: u64, d: u64, e: u64) -> (status: u64)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            *final(self) == *old(self),
            status == if old(self).holds_console(root, i) { STATUS_OK } else { STATUS_REFUSED },
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        if self.console_held(root, i) {
            serial_write(a, b, c, d, e);
            STATUS_OK
        } else {
            STATUS_REFUSED
        }
    }

    /// Accepts a power-off through the console capability at index i of the table at root, and refuses
    /// one through an index that names no console. It reads the kernel and changes nothing: ending the
    /// run is the entry's, which calls the machine's shutdown once this returns ok and the kernel's lock
    /// is released, design/syscall-abi-in-registers/.
    pub fn power_off(&self, root: usize, i: usize) -> (status: u64)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            status == if self.holds_console(root, i) { STATUS_OK } else { STATUS_REFUSED },
            discharges(self.view(), self.view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        if self.console_held(root, i) {
            STATUS_OK
        } else {
            STATUS_REFUSED
        }
    }
}

} // verus!
