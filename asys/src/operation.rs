//! Invoking a capability through the one syscall entry: the operation's number in rax, the capability's
//! slot in rdi and arguments after it, with the status in the low 16 bits of the rax that returns. The
//! numbers are the kernel's, which checks at compile time that these match. See
//! design/syscall-abi-in-registers/.

use core::arch::asm;

/// The capability, its rights or the arguments do not allow the operation.
pub const STATUS_REFUSED: u64 = 1;

/// No operation has the number passed.
pub const STATUS_UNKNOWN: u64 = 2;

pub const RETYPE: u64 = 1;
pub const DERIVE: u64 = 2;
pub const MOVE: u64 = 3;
pub const CLAIM: u64 = 4;
pub const DELETE: u64 = 5;
pub const REVOKE: u64 = 6;
pub const MAP: u64 = 7;
pub const UNMAP: u64 = 8;
pub const DESTROY: u64 = 9;
pub const SEND: u64 = 10;
pub const RECEIVE: u64 = 11;
pub const CALL: u64 = 12;
pub const REPLY_RECV: u64 = 13;
pub const PRINT: u64 = 14;

/// The status in the rax an invocation returns.
pub fn status(rax: u64) -> u64 {
    rax & 0xffff
}

/// Invokes `operation` on the capability at `slot`, with the arguments in rsi, rdx, r8 and r9, and
/// returns rax.
///
/// # Safety
///
/// The operation may change the caller's address space, as a map or unmap does.
pub unsafe fn invoke(operation: u64, slot: u64, arguments: [u64; 4]) -> u64 {
    let rax: u64;
    asm!(
        "syscall",
        inout("rax") operation => rax,
        inout("rdi") slot => _,
        inout("rsi") arguments[0] => _,
        inout("rdx") arguments[1] => _,
        out("rcx") _,
        inout("r8") arguments[2] => _,
        inout("r9") arguments[3] => _,
        out("r10") _,
        out("r11") _,
    );
    rax
}
