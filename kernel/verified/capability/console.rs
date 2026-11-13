// SPDX-License-Identifier: MIT

//! Print through a console capability: the words of the invocation go to the serial port, and nothing
//! the kernel holds changes. Debug print is an operation on a console capability that takes words, as
//! design/syscall-abi-in-registers/ makes it; the root holds the console, design/root-process-at-boot/.
use vstd::prelude::*;

verus! {

use crate::arch::serial_write_byte;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::steps::Steps;
use crate::capability::table::*;

/// A console capability's rights: print asks for none but the capability.
pub const CONSOLE_RIGHTS: u32 = 0;

/// The most bytes one print writes: five words of eight bytes. The serial write is a unit per byte.
pub const PRINT_BYTES: usize = 40;

/// Writes to the serial port the bytes words a to e carry: each word's eight bytes from its lowest, a's
/// first, up to the first zero byte. The arch module's serial_write_byte writes one byte, and each
/// iteration counts one unit, its wait on the device: design/one-lock-bounded-steps/.
pub fn serial_write(a: u64, b: u64, c: u64, d: u64, e: u64, Tracked(steps): Tracked<&mut Steps>)
    ensures
        final(steps).count <= old(steps).count + PRINT_BYTES,
{
    let ghost start = steps.count;
    let mut i: usize = 0;
    while i < PRINT_BYTES
        invariant
            i <= PRINT_BYTES,
            start == old(steps).count,
            steps.count == start + i,
        decreases PRINT_BYTES - i,
    {
        let word = if i < 8 {
            a
        } else if i < 16 {
            b
        } else if i < 24 {
            c
        } else if i < 32 {
            d
        } else {
            e
        };
        let byte = (word >> (8 * (i % 8)) as u64) as u8;
        if byte == 0 {
            return;
        }
        serial_write_byte(byte);
        proof {
            steps.step();
        }
        i += 1;
    }
}

/// The console capability, naming the console's object.
pub open spec fn console_payload() -> Payload {
    Payload { kind: CapKind::Console, order: 0, rights: CONSOLE_RIGHTS, base: CONSOLE_OBJECT, badge: 0, priority: 0 }
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
    /// design/witness-per-way-an-operation-succeeds/.
    pub fn print(&mut self, root: usize, i: usize, a: u64, b: u64, c: u64, d: u64, e: u64, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + PRINT_BYTES,
            *final(self) == *old(self),
            ret == old(self).holds_console(root, i),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        proof {
            self.lemma_no_op_discharges(root);
        }
        match self.held_kind(root, i) {
            Some(CapKind::Console) => {
                serial_write(a, b, c, d, e, Tracked(steps));
                true
            },
            _ => false,
        }
    }
}

} // verus!
