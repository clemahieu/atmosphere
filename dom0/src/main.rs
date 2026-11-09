//! The root process of its kernel instance. It treats what boot gave it as all there is and does
//! not assume it owns the machine, so several instances each with a root stay possible. Why, and
//! what to do about a change that breaks this: design/one-kernel-instance/.
//!
//! Print is the one wired operation, so each fixed slot is checked through it: the console accepts it
//! and the process, thread, untyped and frame slots refuse it. dom0 prints that result through the
//! console, then an exit marker, and exits with success only when every check held. The kernel logs
//! each invocation in the serial log.

#![no_std]
#![no_main]

use core::panic::PanicInfo;

use asys::operation;

/// The code dom0 exits with when every check held. The kernel's failure shutdown writes 0 to the
/// same port, so zero cannot mean success here.
const EXIT_SUCCESS: u32 = 0x10;

/// The exit code when an invocation returned a status other than the one expected.
const EXIT_UNEXPECTED_STATUS: u32 = 2;

/// The exit code when dom0 panicked.
const EXIT_PANIC: u32 = 3;

/// A number past every operation's.
const NO_OPERATION: u64 = 0xffff;

/// The arguments of the first invocation, which the kernel logs: each word names its position, so
/// the log shows every argument register reached the kernel in its place, r10 last.
const FIRST_ARGUMENTS: [u64; 5] = [1, 2, 3, 4, 5];

/// What dom0 prints through the console when the fixed-slot checks held, which the gate looks for.
const CHECKS_HELD: [u64; 5] = operation::print_words(b"dom0 slot checks held\n");

/// What dom0 prints through the console when a check did not hold.
const CHECKS_FAILED: [u64; 5] = operation::print_words(b"dom0 slot checks failed\n");

/// The line after the check line. dom0 exits with success only once this print is accepted.
const EXIT_MARKER: [u64; 5] = operation::print_words(b"dom0 capability done\n");

/// Print through `slot`. The status is the low half of what the invocation returns.
///
/// # Safety
///
/// `operation::invoke` may change the caller's address space. Print does not.
unsafe fn print_slot(slot: u64, arguments: [u64; 5]) -> u64 {
    operation::status(unsafe { operation::invoke(operation::PRINT, slot, arguments) })
}

#[no_mangle]
extern "C" fn main(_payload_base: *mut u8, _payload_size: usize) -> isize {
    let process = unsafe { print_slot(operation::ROOT_PROCESS_SLOT, FIRST_ARGUMENTS) };
    let thread = unsafe { print_slot(operation::ROOT_THREAD_SLOT, [0; 5]) };
    let untyped = unsafe { print_slot(operation::ROOT_UNTYPED_SLOT, [0; 5]) };
    let frame = unsafe { print_slot(operation::ROOT_FRAME_SLOT, [0; 5]) };
    let unknown = operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
    let slots_held = process == operation::STATUS_REFUSED
        && thread == operation::STATUS_REFUSED
        && untyped == operation::STATUS_REFUSED
        && frame == operation::STATUS_REFUSED
        && unknown == operation::STATUS_UNKNOWN;
    let console = unsafe {
        print_slot(
            operation::ROOT_CONSOLE_SLOT,
            if slots_held {
                CHECKS_HELD
            } else {
                CHECKS_FAILED
            },
        )
    };
    if slots_held && console == operation::STATUS_OK {
        let marked = unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, EXIT_MARKER) };
        if marked == operation::STATUS_OK {
            exit_qemu(EXIT_SUCCESS)
        }
    }
    exit_qemu(EXIT_UNEXPECTED_STATUS)
}

/// Ends the QEMU run through the isa-debug-exit device at port 0xf4 (dom0 runs with IOPL 3), which
/// exits with status `code << 1 | 1`.
fn exit_qemu(code: u32) -> ! {
    unsafe { core::arch::asm!("out dx, eax", in("dx") 0xf4u16, in("eax") code) };
    loop {}
}

/// dom0's panic handler. No console is reachable from here, so the run stops with a failure code.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    exit_qemu(EXIT_PANIC)
}
