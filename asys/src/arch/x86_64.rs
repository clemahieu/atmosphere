// SPDX-License-Identifier: MIT

//! The x86_64 table under Registers in design/syscall-abi-in-registers/: `syscall`, with the operation
//! number and then the status word in rax, the slot and then result 1 in rdi, arguments 1 to 4 and then
//! results 2 to 5 in rsi, rdx, r8 and r9, and argument 5 in r10. The instruction takes rcx and r11, and
//! the kernel clobbers r10.

use core::arch::asm;

/// How many words a thread's saved frame is, in the order the table under Thread and process operations
/// in design/syscall-abi-in-registers/ gives: the words read registers and write registers move.
pub const FRAME_WORDS: u64 = 21;

/// The word of the frame that holds the program counter, `rip`.
pub const PC_WORD: u64 = 16;

/// The word of the frame that holds the user stack pointer, `rsp`.
pub const SP_WORD: u64 = 19;

/// Invokes `operation` on the capability at `slot` with arguments 1 to 5, and returns the status word
/// and result words 1 to 4.
///
/// # Safety
///
/// The operation may change the caller's address space, as a map or unmap does.
pub unsafe fn syscall(operation: u64, slot: u64, arguments: [u64; 5]) -> (u64, [u64; 4]) {
    let status_word: u64;
    let (rdi, rsi, rdx, r8): (u64, u64, u64, u64);
    unsafe {
        asm!(
            "syscall",
            inout("rax") operation => status_word,
            inout("rdi") slot => rdi,
            inout("rsi") arguments[0] => rsi,
            inout("rdx") arguments[1] => rdx,
            out("rcx") _,
            inout("r8") arguments[2] => r8,
            inout("r9") arguments[3] => _,
            inout("r10") arguments[4] => _,
            out("r11") _,
        );
    }
    (status_word, [rdi, rsi, rdx, r8])
}
