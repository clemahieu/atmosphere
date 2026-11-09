//! Invoking a capability through the one syscall entry: the operation's number in rax, the capability's
//! slot in rdi and arguments after it, with the status in the low 16 bits of the rax that returns. The
//! numbers are the kernel's, which checks at compile time that these match. See
//! design/syscall-abi-in-registers/.

use core::arch::asm;

/// The operation was done.
pub const STATUS_OK: u64 = 0;

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
/// Writes to the serial port the bytes rsi, rdx, r8, r9 and r10 carry, through a console capability:
/// each word's eight bytes from its lowest, rsi's first, up to the first zero byte, so 40 bytes at most.
pub const PRINT: u64 = 14;

/// The root's slot holding its own process, with control, as boot leaves it. See
/// design/root-process-at-boot/.
pub const ROOT_PROCESS_SLOT: u64 = 1;

/// The root's slot holding its own thread, with control, as boot leaves it.
pub const ROOT_THREAD_SLOT: u64 = 2;

/// The root's slot holding its console capability, which print writes through, as boot leaves it.
pub const ROOT_CONSOLE_SLOT: u64 = 3;

/// The root's first slot holding an untyped capability, as boot leaves it: one per maximal aligned
/// block of free memory, at consecutive slots from here to the end of the table's first leaf.
pub const ROOT_UNTYPED_SLOT: u64 = 4;

/// The root's first slot holding a frame capability for dom0's image, as boot leaves it: one per
/// aligned block of at most 512 pages of each run the loader mapped, with the run's rights, at
/// consecutive slots from here, the first slot of the table's second leaf.
pub const ROOT_FRAME_SLOT: u64 = 129;

/// The status in the rax an invocation returns.
pub fn status(rax: u64) -> u64 {
    rax & 0xffff
}

/// Invokes `operation` on the capability at `slot`, with the arguments in rsi, rdx, r8, r9 and r10,
/// and returns rax.
///
/// # Safety
///
/// The operation may change the caller's address space, as a map or unmap does.
pub unsafe fn invoke(operation: u64, slot: u64, arguments: [u64; 5]) -> u64 {
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
        inout("r10") arguments[4] => _,
        out("r11") _,
    );
    rax
}
