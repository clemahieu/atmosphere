// SPDX-License-Identifier: MIT

//! The aarch64 table under Registers in design/syscall-abi-in-registers/: `svc #0`, with the operation
//! number and then the status word in x8, the slot and then result 1 in x0, arguments 1 to 4 and then
//! results 2 to 5 in x1 to x4, and argument 5 in x5. The kernel clobbers x5 to x7, x9 to x17 and x30.

use core::arch::asm;

/// How many words a thread's saved frame is, in the order the table under Thread and process operations
/// in design/syscall-abi-in-registers/ gives: the words read registers and write registers move.
pub const FRAME_WORDS: u64 = 34;

/// The word of the frame that holds the program counter, `elr_el1`.
pub const PC_WORD: u64 = 32;

/// The word of the frame that holds the user stack pointer, `sp_el0`.
pub const SP_WORD: u64 = 31;

/// Invokes `operation` on the capability at `slot` with arguments 1 to 5, and returns the status word
/// and result words 1 to 4.
///
/// # Safety
///
/// The operation may change the caller's address space, as a map or unmap does.
pub unsafe fn syscall(operation: u64, slot: u64, arguments: [u64; 5]) -> (u64, [u64; 4]) {
    let status_word: u64;
    let (x0, x1, x2, x3): (u64, u64, u64, u64);
    unsafe {
        asm!(
            "svc #0",
            inout("x8") operation => status_word,
            inout("x0") slot => x0,
            inout("x1") arguments[0] => x1,
            inout("x2") arguments[1] => x2,
            inout("x3") arguments[2] => x3,
            inout("x4") arguments[3] => _,
            inout("x5") arguments[4] => _,
            out("x6") _,
            out("x7") _,
            out("x9") _,
            out("x10") _,
            out("x11") _,
            out("x12") _,
            out("x13") _,
            out("x14") _,
            out("x15") _,
            out("x16") _,
            out("x17") _,
            out("x30") _,
        );
    }
    (status_word, [x0, x1, x2, x3])
}
