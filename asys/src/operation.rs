//! Invoking a capability through the one syscall entry: the operation number, the capability's slot
//! and arguments 1 to 5 in, the status word out, with the status in its low 16 bits, and result words
//! after it. The registers that carry each position are the target's, in `arch`. The numbers are the
//! kernel's, which checks at compile time that these match. See design/syscall-abi-in-registers/.

use crate::arch;

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
/// Derives from the capability in the slot a child into the empty slot in argument 1, with the rights in
/// argument 2 and the block of the order in argument 4 at the base in argument 3, which must lie within
/// the parent's rights and block.
pub const DERIVE: u64 = 2;
/// Moves the capability in the slot to the empty slot in argument 1, children and all, leaving the slot
/// empty.
pub const MOVE: u64 = 3;
pub const CLAIM: u64 = 4;
/// Deletes the capability in the slot, which must have nothing below it: no capability derived from it, no
/// mapping made through it and no binding. A holder revokes first.
pub const DELETE: u64 = 5;
/// Removes everything below the capability in the slot, the capabilities derived from it and the mappings
/// made through it or them, a bounded number of steps at a time: again while some is left, ok once none
/// is. The capability itself stays.
pub const REVOKE: u64 = 6;
/// Maps into the entry of the space in the slot that the virtual address in argument 1 and the level in
/// argument 2 name the page at the page offset in argument 4 of the frame in argument 3: a 4K page at
/// level 1, a 2M page at level 2, whose offset is a multiple of 512. The entry must be empty and the tables above it linked.
pub const MAP: u64 = 7;
/// Clears the entry of the space in the slot that the virtual address in argument 1 and the level in
/// argument 2 name, which must map a page. Level 1 is the only level it accepts. Returns the entry's
/// accessed and dirty bits as read when it was cleared in results 1 and 2, and in results 3 and 4 whether
/// the target maintains each bit, each 1 when it holds.
pub const UNMAP: u64 = 8;
pub const DESTROY: u64 = 9;
pub const SEND: u64 = 10;
pub const RECEIVE: u64 = 11;
pub const CALL: u64 = 12;
pub const REPLY_RECV: u64 = 13;
/// Writes to the serial port the bytes arguments 1 to 5 carry, through the console capability in the
/// slot: each word's eight bytes from its lowest, argument 1's first, up to the first zero byte, so 40
/// bytes at most.
pub const PRINT: u64 = 14;
/// Returns the kind, base, order and rights of the capability the caller holds in the slot in results 1
/// to 4; refused for a slot that holds none. It asks for no right.
pub const INSPECT: u64 = 15;
/// Links the unlinked table page at the physical base in argument 4 into the entry of the space in the
/// slot that the virtual address in argument 1 and the level in argument 2 name, on the authority of the
/// untyped in argument 3 over the page's block. The level is 2, 3 or 4 and the page's own level one below it.
pub const LINK: u64 = 16;
/// Reads and clears the accessed and dirty bits of the count in argument 2, 1 to PROBE_MAX, of level 1
/// entries from the one the virtual address in argument 1 names in the space of the capability in the
/// slot, which must allow writing it; the entries lie in one level 1 table. Returns the accessed mask in
/// result 1 and the dirty mask in result 2, bit i for entry i, a bit set only for a present entry, and in
/// results 3 and 4 whether the target maintains each bit, 1 when it does. It changes no mapping and does
/// not flush, so a translation still cached may hide a use until the next walk.
pub const PROBE: u64 = 17;
/// Ends the run through the power capability in the slot: the machine powers off, reporting a run that
/// succeeded when argument 1 is not zero and one that failed when it is zero. Refused unless the slot holds
/// a power capability; accepted, it does not return.
pub const POWER_OFF: u64 = 18;

/// The most entries one probe reads.
pub const PROBE_MAX: u64 = 64;

/// Retype's kind in argument 1 for a 4K frame: a frame capability of order 0 for the page at the base in
/// argument 2, in the empty slot in argument 3.
pub const RETYPE_FRAME: u64 = 0;

/// Retype's kind in argument 1 for a 2M frame: a frame capability of order 9 for the 2M-aligned block at
/// the base in argument 2, in the empty slot in argument 3. Retype returns again while the block is zeroed a slice at a
/// time and ok once the capability is in the slot.
pub const RETYPE_LARGE_FRAME: u64 = 1;

/// Retype's kind in argument 1 for a table page: an unlinked table page of the level in argument 4, 1 to
/// 3, at the base in argument 2. No capability names it, so it takes no slot; link names it by its base.
pub const RETYPE_TABLE_PAGE: u64 = 2;

/// The kind numbers inspect returns in result 1.
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
pub const KIND_POWER: u64 = 10;

/// The indices a capability table has: 512 root entries of 128 positions. Every slot is below this.
pub const TABLE_INDICES: u64 = 65536;

/// The root's slot holding its own process, with control, as boot leaves it. See
/// design/root-process-at-boot/.
pub const ROOT_PROCESS_SLOT: u64 = 1;

/// The root's slot holding its own thread, with control, as boot leaves it.
pub const ROOT_THREAD_SLOT: u64 = 2;

/// The root's slot holding its console capability, which print writes through, as boot leaves it.
pub const ROOT_CONSOLE_SLOT: u64 = 3;

/// The root's slot holding its power capability, which power-off ends the run through, as boot leaves
/// it.
pub const ROOT_POWER_SLOT: u64 = 4;

/// The root's first slot holding an untyped capability, as boot leaves it: one per maximal aligned
/// block of free memory, at consecutive slots from here to the end of the table's first leaf.
pub const ROOT_UNTYPED_SLOT: u64 = 5;

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

/// The status in the status word an invocation returns.
pub fn status(word: u64) -> u64 {
    word & 0xffff
}

/// Invokes `operation` on the capability at `slot` with arguments 1 to 5, and returns the status word.
///
/// # Safety
///
/// The operation may change the caller's address space, as a map or unmap does.
pub unsafe fn invoke(operation: u64, slot: u64, arguments: [u64; 5]) -> u64 {
    unsafe { invoke_returning(operation, slot, arguments) }.0
}

/// Invokes `operation` on the capability at `slot` with arguments 1 to 5, and returns the status word
/// and result words 1 to 4.
///
/// # Safety
///
/// The operation may change the caller's address space, as a map or unmap does.
pub unsafe fn invoke_returning(operation: u64, slot: u64, arguments: [u64; 5]) -> (u64, [u64; 4]) {
    unsafe { arch::syscall(operation, slot, arguments) }
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
    let (word, [kind, base, order, rights]) = unsafe { invoke_returning(INSPECT, slot, [0; 5]) };
    match status(word) {
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

/// What an unmap found in the entry it cleared: its accessed and dirty bits as read when it was cleared,
/// and whether the target maintains each bit, without which it says nothing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Unmapped {
    pub accessed: bool,
    pub dirty: bool,
    pub accessed_maintained: bool,
    pub dirty_maintained: bool,
}

/// Clears the entry at `level` that `address` names in the space of the capability at `space`: what the
/// entry held, or the status unmap returned when it was refused.
///
/// # Safety
///
/// Nothing the caller still uses may be at `address` in that space: once the entry is clear, an access
/// there faults.
pub unsafe fn unmap(space: u64, address: u64, level: u64) -> Result<Unmapped, u64> {
    let (word, [accessed, dirty, accessed_maintained, dirty_maintained]) =
        unsafe { invoke_returning(UNMAP, space, [address, level, 0, 0, 0]) };
    match status(word) {
        STATUS_OK => Ok(Unmapped {
            accessed: accessed == 1,
            dirty: dirty == 1,
            accessed_maintained: accessed_maintained == 1,
            dirty_maintained: dirty_maintained == 1,
        }),
        refused => Err(refused),
    }
}

/// What a probe found: bit i of each mask is entry i's accessed or dirty bit as read, and whether the
/// target maintains each bit, without which its mask says nothing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Probed {
    pub accessed: u64,
    pub dirty: u64,
    pub accessed_maintained: bool,
    pub dirty_maintained: bool,
}

/// Reads and clears the accessed and dirty bits of `count` level 1 entries from the one `address` names,
/// in the space of the capability at `space`: what it found, or the status probe returned when it was
/// refused.
pub fn probe(space: u64, address: u64, count: u64) -> Result<Probed, u64> {
    // A probe changes no mapping, so no address the caller reads changes.
    let (word, [accessed, dirty, accessed_maintained, dirty_maintained]) =
        unsafe { invoke_returning(PROBE, space, [address, count, 0, 0, 0]) };
    match status(word) {
        STATUS_OK => Ok(Probed {
            accessed,
            dirty,
            accessed_maintained: accessed_maintained == 1,
            dirty_maintained: dirty_maintained == 1,
        }),
        refused => Err(refused),
    }
}

/// Powers the machine off through the power capability at `power`, reporting whether the run
/// succeeded. It returns only when it was not accepted, with the status: the low half of what returns.
pub fn power_off(power: u64, success: bool) -> u64 {
    // A power-off the kernel refuses changes nothing, and one it accepts does not return.
    status(unsafe { invoke(POWER_OFF, power, [success as u64, 0, 0, 0, 0]) })
}

/// Moves the capability at `from` to the empty slot `to`, children and all, leaving `from` empty. The
/// status is the low half of what returns.
pub fn move_capability(from: u64, to: u64) -> u64 {
    // A move changes slots, not the caller's address space.
    status(unsafe { invoke(MOVE, from, [to, 0, 0, 0, 0]) })
}

/// Derives from the capability at `from` a child into the empty slot `to`, with `rights` and the block of
/// `order` at `base`, which must lie within the parent's. The status is the low half of what returns.
pub fn derive(from: u64, to: u64, rights: u64, base: u64, order: u64) -> u64 {
    // A derive changes slots, not the caller's address space.
    status(unsafe { invoke(DERIVE, from, [to, rights, base, order, 0]) })
}

/// Deletes the capability at `slot`, which must have nothing below it. The status is the low half of
/// what returns.
pub fn delete(slot: u64) -> u64 {
    // A delete of a capability with no mapping below it changes slots, not the caller's address space.
    status(unsafe { invoke(DELETE, slot, [0; 5]) })
}

/// Takes a bounded number of steps of removing everything below the capability at `slot`, the
/// capabilities derived from it and the mappings made through it or them: again while some is left, ok
/// once none is. The status is the low half of what returns.
///
/// # Safety
///
/// Nothing the caller still uses may be mapped through the capability at `slot` or one derived from it:
/// once its mapping is gone, an access there faults.
pub unsafe fn revoke(slot: u64) -> u64 {
    status(unsafe { invoke(REVOKE, slot, [0; 5]) })
}
