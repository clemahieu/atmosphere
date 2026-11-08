//! dom0 for the capability kernel. No operation is wired yet, so it cannot print: it checks that the
//! kernel refuses an operation and reports a number no operation has, and says which by its exit code.
//! The kernel logs each invocation in the serial log.

use asys::operation;

use crate::syscall_benchmark::{exit_qemu, EXIT_SUCCESS};

/// The exit code when an invocation returned a status other than the one expected.
const EXIT_UNEXPECTED_STATUS: u32 = 2;

/// A number past every operation's.
const NO_OPERATION: u64 = 0xffff;

/// The arguments of the first invocation, which the kernel logs: each word names its position, so
/// the log shows every argument register reached the kernel in its place, r10 last.
const FIRST_ARGUMENTS: [u64; 5] = [1, 2, 3, 4, 5];

#[no_mangle]
extern "C" fn main(_payload_base: *mut u8, _payload_size: usize) -> isize {
    let print = operation::status(unsafe { operation::invoke(operation::PRINT, 0, FIRST_ARGUMENTS) });
    let unknown = operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
    if print == operation::STATUS_REFUSED && unknown == operation::STATUS_UNKNOWN {
        exit_qemu(EXIT_SUCCESS)
    }
    exit_qemu(EXIT_UNEXPECTED_STATUS)
}
