//! Print through a console capability: the words of the invocation go to the serial port, and nothing
//! the kernel holds changes. Debug print is an operation on a console capability that takes words, as
//! design/syscall-abi-in-registers/ makes it; the root holds the console, design/root-process-at-boot/.
use vstd::prelude::*;

verus! {

use crate::arch::serial_write;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::operation::*;
use crate::capability::reach::*;
use crate::capability::table::*;

impl CapKernel {
    /// Index i of the table at root holds a console capability.
    pub open spec fn can_print(&self, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Console
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
            status == if old(self).can_print(root, i) { STATUS_OK } else { STATUS_REFUSED },
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return STATUS_REFUSED; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return STATUS_REFUSED;
        }
        proof {
            self.lemma_slot(root, i);
            assert(self.tables.is_cap(&self.list, n));
            assert(payload == self.payload_of(n));
        }
        match payload.kind {
            CapKind::Console => {
                serial_write(a, b, c, d, e);
                STATUS_OK
            },
            _ => STATUS_REFUSED,
        }
    }
}

} // verus!
