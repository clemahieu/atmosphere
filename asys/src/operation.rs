//! Invoking a capability through the one syscall entry: the operation's number in rax, the capability's
//! slot in rdi and arguments after it, with the status in the low 16 bits of the rax that returns and
//! result words in rdi, rsi, rdx and r8. The
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
/// Returns the kind, base, order and rights of a capability the caller holds in rdi, rsi, rdx and r8;
/// refused for a slot that holds none. It asks for no right.
pub const INSPECT: u64 = 15;

/// The kind numbers inspect returns in rdi.
pub const KIND_UNTYPED: u64 = 0;
pub const KIND_FRAME: u64 = 1;
pub const KIND_PROCESS: u64 = 2;
pub const KIND_THREAD: u64 = 3;
pub const KIND_ENDPOINT: u64 = 4;
pub const KIND_REPLY: u64 = 5;
pub const KIND_NOTIFICATION: u64 = 6;
pub const KIND_SPACE: u64 = 7;
pub const KIND_DEVICE: u64 = 8;
pub const KIND_CONSOLE: u64 = 9;

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

/// The words of print's arguments carrying `text`, as PRINT reads them: eight bytes a word from
/// its lowest, the rest zero. The text has no zero byte and is shorter than the 40 bytes they hold, so
/// a zero byte ends it.
pub const fn print_words(text: &[u8]) -> [u64; 5] {
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
    unsafe { invoke_returning(operation, slot, arguments) }.0
}

/// Invokes `operation` on the capability at `slot`, with the arguments in rsi, rdx, r8, r9 and r10,
/// and returns rax and the result words in rdi, rsi, rdx and r8.
///
/// # Safety
///
/// The operation may change the caller's address space, as a map or unmap does.
pub unsafe fn invoke_returning(operation: u64, slot: u64, arguments: [u64; 5]) -> (u64, [u64; 4]) {
    let rax: u64;
    let words: [u64; 4];
    unsafe {
        let (rdi, rsi, rdx, r8): (u64, u64, u64, u64);
        asm!(
            "syscall",
            inout("rax") operation => rax,
            inout("rdi") slot => rdi,
            inout("rsi") arguments[0] => rsi,
            inout("rdx") arguments[1] => rdx,
            out("rcx") _,
            inout("r8") arguments[2] => r8,
            inout("r9") arguments[3] => _,
            inout("r10") arguments[4] => _,
            out("r11") _,
        );
        words = [rdi, rsi, rdx, r8];
    }
    (rax, words)
}

/// What inspect says of a capability: its kind number, the base of its block, its order and its
/// rights.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Capability {
    pub kind: u64,
    pub base: u64,
    pub order: u64,
    pub rights: u64,
}

/// Inspects the capability at `slot`: what it says, or the status inspect returned when the slot holds
/// none.
pub fn inspect(slot: u64) -> Result<Capability, u64> {
    // Inspect changes nothing, the caller's address space included.
    let (rax, [kind, base, order, rights]) = unsafe { invoke_returning(INSPECT, slot, [0; 5]) };
    match status(rax) {
        STATUS_OK => Ok(Capability { kind, base, order, rights }),
        refused => Err(refused),
    }
}
