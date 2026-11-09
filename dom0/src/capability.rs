//! dom0 for the capability kernel. It prints a line through its console capability, checks that the
//! kernel refuses print through a slot holding no console and reports a number no operation has, and
//! says which by its exit code. The kernel logs each invocation in the serial log.

use asys::operation;

use crate::syscall_benchmark::{exit_qemu, EXIT_SUCCESS};

/// The exit code when an invocation returned a status other than the one expected.
const EXIT_UNEXPECTED_STATUS: u32 = 2;

/// A number past every operation's.
const NO_OPERATION: u64 = 0xffff;

/// The arguments of the first invocation, which the kernel logs: each word names its position, so
/// the log shows every argument register reached the kernel in its place, r10 last.
const FIRST_ARGUMENTS: [u64; 5] = [1, 2, 3, 4, 5];

/// The slot of the first invocation, which holds no console: boot fills slots from ROOT_PROCESS_SLOT.
const NO_CONSOLE_SLOT: u64 = 0;

/// The line dom0 prints through its console, which the gate's capability boot looks for.
const CONSOLE_LINE: [u64; 5] = print_words(b"dom0 prints through its console\n");

/// The words of print's arguments carrying `text`, as asys's PRINT reads them: eight bytes a word from
/// its lowest, the rest zero. The text has no zero byte and is shorter than the 40 bytes they hold, so
/// a zero byte ends it.
const fn print_words(text: &[u8]) -> [u64; 5] {
    assert!(text.len() < 40, "print carries fewer than 40 bytes");
    let mut words = [0u64; 5];
    let mut k = 0;
    while k < text.len() {
        assert!(text[k] != 0, "a zero byte ends print's text");
        words[k / 8] |= (text[k] as u64) << (8 * (k % 8));
        k += 1;
    }
    words
}

#[no_mangle]
extern "C" fn main(_payload_base: *mut u8, _payload_size: usize) -> isize {
    let refused = operation::status(unsafe { operation::invoke(operation::PRINT, NO_CONSOLE_SLOT, FIRST_ARGUMENTS) });
    let printed = operation::status(unsafe { operation::invoke(operation::PRINT, operation::ROOT_CONSOLE_SLOT, CONSOLE_LINE) });
    let unknown = operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
    if refused == operation::STATUS_REFUSED && printed == operation::STATUS_OK && unknown == operation::STATUS_UNKNOWN {
        exit_qemu(EXIT_SUCCESS)
    }
    exit_qemu(EXIT_UNEXPECTED_STATUS)
}
