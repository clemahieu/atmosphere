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

/// The operation took a bounded step and is not finished; the same invocation again goes on from where
/// it stopped.
pub const STATUS_AGAIN: u64 = 3;

pub const RETYPE: u64 = 1;
pub const DERIVE: u64 = 2;
/// Moves the capability in rdi to the empty slot in rsi, children and all, leaving rdi empty.
pub const MOVE: u64 = 3;
pub const CLAIM: u64 = 4;
pub const DELETE: u64 = 5;
pub const REVOKE: u64 = 6;
/// Maps into the entry of the space in rdi that the virtual address in rsi and the level in rdx name the
/// page at the page offset in r9 of the frame in r8: a 4K page at level 1, a 2M page at level 2, whose
/// offset is a multiple of 512. The entry must be empty and the tables above it linked.
pub const MAP: u64 = 7;
/// Clears the entry of the space in rdi that the virtual address in rsi and the level in rdx name, which
/// must map a page. Level 1 is the only level it accepts.
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
/// Links the unlinked table page at the physical base in r9 into the entry of the space in rdi that
/// the virtual address in rsi and the level in rdx name, on the authority of the untyped in r8 over the
/// page's block. The level is 2, 3 or 4 and the page's own level one below it.
pub const LINK: u64 = 16;

/// Retype's kind in rsi for a 4K frame: a frame capability of order 0 for the page at the base in rdx,
/// in the empty slot in r8.
pub const RETYPE_FRAME: u64 = 0;

/// Retype's kind in rsi for a 2M frame: a frame capability of order 9 for the 2M-aligned block at the
/// base in rdx, in the empty slot in r8. Retype returns again while the block is zeroed a slice at a
/// time and ok once the capability is in the slot.
pub const RETYPE_LARGE_FRAME: u64 = 1;

/// Retype's kind in rsi for a table page: an unlinked table page of the level in r9, 1 to 3, at the base
/// in rdx. No capability names it, so it takes no slot; link names it by its base.
pub const RETYPE_TABLE_PAGE: u64 = 2;

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

/// The indices a capability table has: 512 root entries of 128 positions. Every slot is below this.
pub const TABLE_INDICES: u64 = 65536;

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

/// Retypes the free 4K page at `base`, inside the block of the untyped at `untyped`, as a frame whose
/// capability goes in the empty slot `destination`. The status is the low half of what returns.
pub fn retype_frame(untyped: u64, base: u64, destination: u64) -> u64 {
    // A retype changes the caller's table and the page's memory, never its address space.
    status(unsafe { invoke(RETYPE, untyped, [RETYPE_FRAME, base, destination, 0, 0]) })
}

/// Takes one step of retyping the free 2M block at `base`, inside the block of the untyped at
/// `untyped`, as a frame whose capability goes in the empty slot `destination`: again while the block is
/// being zeroed, then ok once the capability is there. The status is the low half of what returns.
pub fn retype_large_frame(untyped: u64, base: u64, destination: u64) -> u64 {
    // A retype changes the caller's table and the block's memory, never its address space.
    status(unsafe { invoke(RETYPE, untyped, [RETYPE_LARGE_FRAME, base, destination, 0, 0]) })
}

/// Retypes the free order-3 block at `base`, inside the block of the untyped at `untyped`, as an
/// unlinked table page of `level`. The status is the low half of what returns.
pub fn retype_table_page(untyped: u64, base: u64, level: u64) -> u64 {
    // A retype changes the caller's table and the block's memory, never its address space.
    status(unsafe { invoke(RETYPE, untyped, [RETYPE_TABLE_PAGE, base, 0, level, 0]) })
}

/// Links the unlinked table page at `table`, covered by the untyped at `untyped`, into the entry at
/// `level` that `address` names in the space of the capability at `space`. The status is the low half of
/// what returns.
pub fn link(space: u64, address: u64, level: u64, untyped: u64, table: u64) -> u64 {
    // A link adds an empty table to the space and maps no page, so no address the caller reads changes.
    status(unsafe { invoke(LINK, space, [address, level, untyped, table, 0]) })
}

/// Maps the page at offset `page` of the frame capability at `frame` into the entry at `level` that
/// `address` names in the space of the capability at `space`. The status is the low half of what
/// returns.
pub fn map(space: u64, address: u64, level: u64, frame: u64, page: u64) -> u64 {
    // A map fills only an empty entry, so no address the caller already reads changes.
    status(unsafe { invoke(MAP, space, [address, level, frame, page, 0]) })
}

/// Clears the entry at `level` that `address` names in the space of the capability at `space`. The
/// status is the low half of what returns.
///
/// # Safety
///
/// Nothing the caller still uses may be at `address` in that space: once the entry is clear, an access
/// there faults.
pub unsafe fn unmap(space: u64, address: u64, level: u64) -> u64 {
    status(unsafe { invoke(UNMAP, space, [address, level, 0, 0, 0]) })
}

/// Moves the capability at `from` to the empty slot `to`, children and all, leaving `from` empty. The
/// status is the low half of what returns.
pub fn move_capability(from: u64, to: u64) -> u64 {
    // A move changes slots, not the caller's address space.
    status(unsafe { invoke(MOVE, from, [to, 0, 0, 0, 0]) })
}
