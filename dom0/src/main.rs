//! The root process of its kernel instance. It treats what boot gave it as all there is and does
//! not assume it owns the machine, so several instances each with a root stay possible. Why, and
//! what to do about a change that breaks this: design/one-kernel-instance/.
//!
//! Print, inspect, retype of a 4K frame, of a 2M frame and of a table page, derive, move, delete, revoke, link, map, unmap and probe are the wired
//! operations, so each fixed slot is checked through them: the console accepts print and the process,
//! thread, untyped and frame slots refuse it; inspect says the console slot holds a console, and each slot
//! from the first untyped holds an untyped whose base is aligned to its order, up to the first slot
//! that holds nothing, which inspect refuses. Retype under an empty slot, a slot past the table and
//! the console is refused, and retype of the last untyped's last page into that empty slot is
//! accepted, after which inspect says the slot holds a 4K frame at that page. dom0 then retypes
//! four table pages, after a table page of a level no table has is refused, and a retype of one of
//! them again is refused after; it links three of them, of levels 3, 2 and 1, under an address its
//! image does not use, through its own process capability, after a table of the wrong level, an
//! entry whose tables above are not linked and an unaligned address are refused, and the fourth is
//! refused at the entry the third took. It maps the frame it retyped under that path, after a map
//! at a kernel-half and at a non-canonical address is refused, writes a word through the mapping
//! and reads it back, and a second map at that entry is refused. It unmaps that page, after an unmap
//! at a kernel-half address, at the empty entry after it and at level 2 is refused; a second unmap
//! there is refused, and a map of the same frame there is accepted again, through which it reads the
//! word back. It moves the frame's capability, still mapped, to the slot after it, after a move from
//! that empty slot and onto the console's is refused; inspect then refuses the old slot and finds the
//! frame in the new one, and once the page is unmapped, a map through the old slot is refused and one
//! through the new slot accepted, through which it reads the word back. It retypes a 2M frame from an
//! untyped, after a retype at a base not aligned to 2M is refused, repeating while retype returns again,
//! prints how many again returns that took, reads the frame back with inspect, and a second retype of
//! the block is refused. It derives from that 2M frame a read-only child of one page inside it, after a
//! derive from a slot it does not hold, with rights wider than the frame's, of a page outside the frame
//! and into an occupied slot is refused, and inspect finds the child. It maps that child 64 times, so
//! the run under the 2M frame holds one node more than revoke's budget, reads the first mapping, and
//! revokes the 2M frame, repeating while revoke returns again, after a revoke of an empty slot and of a
//! slot past the table is refused; it prints how many again returns that took, and inspect then refuses
//! the child's slot, a map through it and an unmap at its first mapping are refused, and inspect still
//! finds the 2M frame. It derives a child from the 2M frame again; a delete of the frame is then
//! refused, the child's delete is accepted, and the frame's after it, after which inspect, a second
//! delete and a delete past the table are refused. It times one invocation of a number no operation has,
//! and one 4K map into each of 64 free entries of the level 1 table, and prints each cycle count beside
//! the before number from logs/cutover-before.log, 102 and 66926. It maps the frame at the entry after
//! those, and probes the 64 entries ending there after the map, after reading the page, again, and after
//! writing it, printing the mapped entry's accessed and dirty bits each time: both clear, then accessed
//! alone, then both clear, then dirty; the other 63 entries' bits stay clear and both bits are
//! maintained. A probe of 0 entries, of 65 and of a range leaving its level 1 table is refused. It maps
//! the frame at the next entry, writes the page and unmaps it, and the unmap returns accessed and dirty
//! set, both maintained, which it prints. dom0 prints that result through the console, then an exit marker, and exits with success only when every
//! check held.

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

/// The arguments of the first invocation. Each word names its position, r10 last.
const FIRST_ARGUMENTS: [u64; 5] = [1, 2, 3, 4, 5];

/// What dom0 prints through the console when the fixed-slot checks held, which the gate looks for.
const CHECKS_HELD: [u64; 5] = operation::print_words(b"dom0 slot checks held\n");

/// What dom0 prints through the console when a check did not hold.
const CHECKS_FAILED: [u64; 5] = operation::print_words(b"dom0 slot checks failed\n");

/// The line after the check line. dom0 exits with success only once this print is accepted.
const EXIT_MARKER: [u64; 5] = operation::print_words(b"dom0 capability done\n");

/// The largest order a capability's block has: 2^36 pages reach the end of the 48-bit space.
const MAX_ORDER: u64 = 36;

/// The last slot of the table's first leaf, where boot's untyped end.
const FIRST_LEAF_END: u64 = operation::ROOT_FRAME_SLOT - 2;

/// The first slot after the untyped, once inspect says the console slot holds a console, and every slot
/// from the first untyped holds an untyped whose base is aligned to its order, at least one, up to that
/// slot, which inspect refuses because it holds nothing. Boot fills the untyped slots from the first and
/// leaves the rest of the leaf empty, design/root-process-at-boot/; a leaf full of untyped leaves no
/// empty slot in it to read, and fails.
fn first_empty_slot() -> Option<u64> {
    let console = operation::inspect(operation::ROOT_CONSOLE_SLOT);
    if !matches!(console, Ok(capability) if capability.kind == operation::KIND_CONSOLE) {
        return None;
    }
    let mut slot = operation::ROOT_UNTYPED_SLOT;
    while slot <= FIRST_LEAF_END {
        match operation::inspect(slot) {
            Ok(capability) => {
                let aligned = capability.order <= MAX_ORDER && capability.base % (4096 << capability.order) == 0;
                if capability.kind != operation::KIND_UNTYPED || !aligned {
                    return None;
                }
            }
            Err(status) if status == operation::STATUS_REFUSED && slot > operation::ROOT_UNTYPED_SLOT => {
                return Some(slot);
            }
            Err(_) => return None,
        }
        slot += 1;
    }
    None
}

/// Whether retype of a 4K frame is refused under the empty slot `empty`, under a slot past the table and
/// under the console, which is no untyped, and then accepted for the last page of the last untyped, the
/// one before `empty`, into `empty`, which inspect then says holds a frame of order 0 at that page. Boot
/// pays for dom0's tables from the start of the first untyped and leaves the rest free, so that page is
/// free.
fn retyped_frame_held(empty: u64) -> bool {
    let untyped = empty - 1;
    let base = match operation::inspect(untyped) {
        Ok(block) => block.base + (4096 << block.order) - 4096,
        Err(_) => return false,
    };
    let refused = |slot| operation::retype_frame(slot, base, empty) == operation::STATUS_REFUSED;
    if !refused(empty) || !refused(operation::TABLE_INDICES) || !refused(operation::ROOT_CONSOLE_SLOT) {
        return false;
    }
    if operation::retype_frame(untyped, base, empty) != operation::STATUS_OK {
        return false;
    }
    matches!(
        operation::inspect(empty),
        Ok(frame) if frame.kind == operation::KIND_FRAME && frame.base == base && frame.order == 0
    )
}

/// Where dom0 builds a path of tables: the start of root entry 2, past the image's at entry 1
/// (`USERSPACE_BASE`), so linking there changes nothing dom0 reads.
const PATH_ADDRESS: u64 = 2 << 39;

/// The bytes of a table page's block, order 3.
const TABLE_PAGE_BYTES: u64 = 8 * 4096;

/// The last untyped from `empty` down whose block holds at least `pages` 4K pages, if any.
fn untyped_of_pages(empty: u64, pages: u64) -> Option<(u64, operation::Capability)> {
    let mut slot = empty;
    while slot > operation::ROOT_UNTYPED_SLOT {
        slot -= 1;
        match operation::inspect(slot) {
            Ok(block) if block.kind == operation::KIND_UNTYPED && block.order < MAX_ORDER && 1 << block.order >= pages => {
                return Some((slot, block));
            }
            _ => {}
        }
    }
    None
}

/// The untyped and the bases of four unlinked table pages, of levels 3, 2, 1 and 1, once retype has made
/// them from the top of an untyped of at least 64 pages, below the order-3 block holding its last page,
/// which the frame check may have taken; and retype of a table page of level 0 and 4, and of a block
/// already retyped, is refused. Boot pays for dom0's tables from the start of the first untyped, so that
/// top is free.
fn retyped_table_pages(empty: u64) -> Option<(u64, [u64; 4])> {
    let (untyped, block) = untyped_of_pages(empty, 64)?;
    let top = block.base + (4096 << block.order);
    let tables = [1, 2, 3, 4].map(|k| top - TABLE_PAGE_BYTES * (k + 1));
    let retype = |k: usize, level: u64| operation::retype_table_page(untyped, tables[k], level);
    let held = retype(0, 0) == operation::STATUS_REFUSED
        && retype(0, 4) == operation::STATUS_REFUSED
        && retype(0, 3) == operation::STATUS_OK
        && retype(1, 2) == operation::STATUS_OK
        && retype(2, 1) == operation::STATUS_OK
        && retype(3, 1) == operation::STATUS_OK
        && retype(0, 3) == operation::STATUS_REFUSED;
    held.then_some((untyped, tables))
}

/// Whether dom0 builds a path of the level 3, 2 and 1 tables at `tables`, under `untyped`, at
/// `PATH_ADDRESS` in its own space, through its process capability: link of the level 1 page into the
/// level 3 entry, of a table into a level 2 entry whose level 2 table is not linked yet, and at an
/// address not aligned to its level 2 entry is refused; the level 3, 2 and 1 tables link; and the fourth
/// page, of level 1, is refused at the level 2 entry the level 1 table took.
fn linked_path_held(untyped: u64, tables: [u64; 4]) -> bool {
    let link = |address: u64, level: u64, k: usize| {
        operation::link(operation::ROOT_PROCESS_SLOT, address, level, untyped, tables[k])
    };
    link(PATH_ADDRESS, 4, 0) == operation::STATUS_OK
        && link(PATH_ADDRESS, 3, 2) == operation::STATUS_REFUSED
        && link(PATH_ADDRESS, 2, 2) == operation::STATUS_REFUSED
        && link(PATH_ADDRESS, 3, 1) == operation::STATUS_OK
        && link(PATH_ADDRESS + 4096, 2, 2) == operation::STATUS_REFUSED
        && link(PATH_ADDRESS, 2, 2) == operation::STATUS_OK
        && link(PATH_ADDRESS, 2, 3) == operation::STATUS_REFUSED
}

/// An address in the kernel's half, canonical, where no map of dom0's may go.
const KERNEL_HALF_ADDRESS: u64 = 0xffff_8000_0000_0000;

/// An address past the lower half that is not canonical: the old kernel's range past the user half
/// started here. A map names one entry, so the old kernel's range that wraps has no map of its own; an
/// address it could wrap to is past the lower half as this one is.
const NON_CANONICAL_ADDRESS: u64 = 0x0000_ffff_ffff_f000;

/// What dom0 writes through the page it maps and reads back.
const MAPPED_WORD: u64 = 0x6174_6d6f_7370_6865;

/// Whether dom0 maps the 4K frame at `frame` into its own space at `PATH_ADDRESS`, under the level 1
/// table the path holds, and reads back a word written through the mapping: a map at a kernel-half and at
/// a non-canonical address is refused, the map at `PATH_ADDRESS` is accepted, and a second map at the
/// entry it took is refused.
fn mapped_frame_held(frame: u64) -> bool {
    let map = |address: u64| operation::map(operation::ROOT_PROCESS_SLOT, address, 1, frame, 0);
    if map(KERNEL_HALF_ADDRESS) != operation::STATUS_REFUSED
        || map(NON_CANONICAL_ADDRESS) != operation::STATUS_REFUSED
        || map(PATH_ADDRESS) != operation::STATUS_OK
    {
        return false;
    }
    let word = PATH_ADDRESS as *mut u64;
    // The map just made the page at PATH_ADDRESS the frame's, writable, and nothing else names it.
    let read = unsafe {
        word.write_volatile(MAPPED_WORD);
        word.read_volatile()
    };
    read == MAPPED_WORD && map(PATH_ADDRESS) == operation::STATUS_REFUSED
}

/// Whether dom0 unmaps the 4K frame at `frame` that it mapped at `PATH_ADDRESS` and maps it there again:
/// an unmap at a kernel-half address, at the empty entry after `PATH_ADDRESS` and at level 2 is refused,
/// the unmap at `PATH_ADDRESS` is accepted and a second one refused, and a map of the frame there is
/// accepted again and reads back the word written through the first mapping.
fn remapped_frame_held(frame: u64) -> bool {
    // Nothing dom0 uses is at these addresses but the word at PATH_ADDRESS, which it reads only after the
    // map that follows the unmap.
    let refused = |address: u64, level: u64| {
        matches!(
            unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, address, level) },
            Err(operation::STATUS_REFUSED)
        )
    };
    if !refused(KERNEL_HALF_ADDRESS, 1)
        || !refused(PATH_ADDRESS + 0x1000, 1)
        || !refused(PATH_ADDRESS, 2)
        || unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1) }.is_err()
        || !refused(PATH_ADDRESS, 1)
        || operation::map(operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1, frame, 0) != operation::STATUS_OK
    {
        return false;
    }
    // The map just made the page at PATH_ADDRESS the frame's again, and the frame kept the word.
    unsafe { (PATH_ADDRESS as *const u64).read_volatile() == MAPPED_WORD }
}

/// Whether dom0 moves the 4K frame capability at `frame`, mapped at `PATH_ADDRESS`, to the slot after it,
/// which boot left empty: a move from that empty slot and a move onto the console's slot are refused, the
/// move is accepted, inspect refuses the old slot and finds the frame at its base in the new one, and
/// once the page is unmapped, a map through the old slot is refused and one through the new slot is
/// accepted and reads back the word written through the first mapping.
fn moved_frame_held(frame: u64) -> bool {
    let moved = frame + 1;
    let base = match operation::inspect(frame) {
        Ok(capability) => capability.base,
        Err(_) => return false,
    };
    let map = |slot: u64| operation::map(operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1, slot, 0);
    let held = operation::move_capability(moved, moved) == operation::STATUS_REFUSED
        && operation::move_capability(frame, operation::ROOT_CONSOLE_SLOT) == operation::STATUS_REFUSED
        && operation::move_capability(frame, moved) == operation::STATUS_OK
        && matches!(operation::inspect(frame), Err(operation::STATUS_REFUSED))
        && matches!(
            operation::inspect(moved),
            Ok(capability) if capability.kind == operation::KIND_FRAME && capability.base == base && capability.order == 0
        )
        // Nothing dom0 uses is at PATH_ADDRESS but the word, which it reads only after the map that follows.
        && unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1) }.is_ok()
        && map(frame) == operation::STATUS_REFUSED
        && map(moved) == operation::STATUS_OK;
    // The map just made the page at PATH_ADDRESS the moved frame's, which kept the word.
    held && unsafe { (PATH_ADDRESS as *const u64).read_volatile() == MAPPED_WORD }
}

/// The pages of a 2M frame's block, order 9.
const LARGE_FRAME_PAGES: u64 = 512;

/// The start of the line dom0 prints once its 2M retype is done, before the number of again returns it
/// took.
const LARGE_FRAME_HEAD: &[u8] = b"dom0 2M retype done after ";

/// The start of the line dom0 prints once its revoke is done, before the number of again returns it took.
const REVOKE_HEAD: &[u8] = b"dom0 revoke done after ";

/// The end of a line that counts again returns.
const AGAIN_TAIL: &[u8] = b" again\n";

/// Prints through the console `head`, then `again` and AGAIN_TAIL: that an operation was done after
/// `again` again returns. The status is the low half of what the print returns.
fn print_done_after(head: &[u8], again: u64) -> u64 {
    print_count(head, again, AGAIN_TAIL)
}

/// Prints through the console `head`, then `count` in decimal, then `tail`. `head` and `tail` leave
/// room for twenty digits in the 39 bytes print carries. The status is the low half of what the print
/// returns.
fn print_count(head: &[u8], count: u64, tail: &[u8]) -> u64 {
    let mut text = [0u8; 39];
    let mut length = 0;
    for &byte in head {
        text[length] = byte;
        length += 1;
    }
    let mut digits = [0u8; 20];
    let mut pending = 0;
    let mut rest = count;
    loop {
        digits[pending] = b'0' + (rest % 10) as u8;
        pending += 1;
        rest /= 10;
        if rest == 0 {
            break;
        }
    }
    while pending > 0 {
        pending -= 1;
        text[length] = digits[pending];
        length += 1;
    }
    for &byte in tail {
        text[length] = byte;
        length += 1;
    }
    unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, operation::print_words(&text[..length])) }
}

/// The cycle counter.
fn rdtsc() -> u64 {
    let lo: u32;
    let hi: u32;
    unsafe {
        core::arch::asm!("rdtsc", out("eax") lo, out("edx") hi, options(nomem, nostack, preserves_flags));
    }
    ((hi as u64) << 32) | lo as u64
}

/// How many free entries of the level 1 table at PATH_ADDRESS the timed maps fill, one page each.
/// Entry 0 is the frame's existing mapping. Entries 1..=64 are free: revoke cleared them.
const TIMED_MAPS: u64 = 64;

/// The before number for an unassigned invocation, logs/cutover-before.log: 102 TSC cycles.
const NULL_TAIL: &[u8] = b" before 102\n";

/// The before number for a 4K map, one page per call, logs/cutover-before.log: 66926 TSC cycles per page.
const MAP_TAIL: &[u8] = b"/p before 66926\n";

/// Whether dom0 times one invocation of a number no operation has, which returns unknown, and one 4K
/// map of `frame` into each of TIMED_MAPS free entries of the level 1 table, and prints each cycle count
/// beside its before number. The counts are not checked against those numbers. The timed maps start at
/// the page after PATH_ADDRESS, which already holds `frame`.
fn timed_beside_before(frame: u64) -> bool {
    let start = rdtsc();
    let unknown = operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
    let null_cycles = rdtsc() - start;
    if unknown != operation::STATUS_UNKNOWN {
        return false;
    }
    let start = rdtsc();
    for k in 1..=TIMED_MAPS {
        let address = PATH_ADDRESS + 4096 * k;
        if operation::map(operation::ROOT_PROCESS_SLOT, address, 1, frame, 0) != operation::STATUS_OK {
            return false;
        }
    }
    let per_page = (rdtsc() - start) / TIMED_MAPS;
    print_count(b"null ", null_cycles, NULL_TAIL) == operation::STATUS_OK
        && print_count(b"4k ", per_page, MAP_TAIL) == operation::STATUS_OK
}

/// The entry of the level 1 table at PATH_ADDRESS that the probe check maps, the one after the timed
/// maps'.
const PROBED_ENTRY: u64 = TIMED_MAPS + 1;

/// The first of the operation::PROBE_MAX entries the probe check reads, which end at PROBED_ENTRY.
const PROBE_FIRST: u64 = PROBED_ENTRY + 1 - operation::PROBE_MAX;

/// The bit of each mask that is PROBED_ENTRY's.
const PROBED_BIT: u64 = 1 << (PROBED_ENTRY - PROBE_FIRST);

/// The address of entry `k` of the level 1 table at PATH_ADDRESS.
const fn entry_address(k: u64) -> u64 {
    PATH_ADDRESS + 4096 * k
}

/// Prints through the console each of `parts` in turn, which together are shorter than the 40 bytes
/// print carries. The status is the low half of what the print returns.
fn print_parts(parts: &[&[u8]]) -> u64 {
    let mut text = [0u8; 39];
    let mut length = 0;
    for part in parts {
        for &byte in *part {
            text[length] = byte;
            length += 1;
        }
    }
    unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, operation::print_words(&text[..length])) }
}

/// The digit for a bit.
fn bit_digit(bit: bool) -> &'static [u8] {
    if bit { b"1" } else { b"0" }
}

/// Whether a probe of the operation::PROBE_MAX entries ending at PROBED_ENTRY is accepted and finds
/// PROBED_ENTRY's dirty bit `dirty` and, when `accessed` is some, its accessed bit that, and every other
/// entry's bits clear, with both bits maintained; it prints `step` and PROBED_ENTRY's two bits.
fn probed_step_held(step: &[u8], accessed: Option<bool>, dirty: bool) -> bool {
    let probed = match operation::probe(operation::ROOT_PROCESS_SLOT, entry_address(PROBE_FIRST), operation::PROBE_MAX) {
        Ok(probed) => probed,
        Err(_) => return false,
    };
    let a = probed.accessed & PROBED_BIT != 0;
    let d = probed.dirty & PROBED_BIT != 0;
    let printed = print_parts(&[b"dom0 probe ", step, b": a", bit_digit(a), b" d", bit_digit(d), b"\n"]);
    printed == operation::STATUS_OK
        && probed.accessed_maintained
        && probed.dirty_maintained
        && (probed.accessed | probed.dirty) & !PROBED_BIT == 0
        && d == dirty
        && match accessed {
            Some(expected) => a == expected,
            None => true,
        }
}

/// Whether a probe of `count` entries from entry `first` of the level 1 table at PATH_ADDRESS is refused;
/// it prints `what` once it is.
fn probe_refused(first: u64, count: u64, what: &[u8]) -> bool {
    matches!(
        operation::probe(operation::ROOT_PROCESS_SLOT, entry_address(first), count),
        Err(operation::STATUS_REFUSED)
    ) && print_parts(&[b"dom0 probe ", what, b" refused\n"]) == operation::STATUS_OK
}

/// Whether the processor's accessed and dirty bits follow dom0's reads and writes through a page it maps
/// at PROBED_ENTRY from `frame`, as probe reads and clears them: after the map both are clear, after a read
/// accessed alone is set, after a probe with no access between both are clear, and after a write dirty is
/// set. A write sets dirty even through a translation still cached with dirty clear, since the processor
/// walks to set it, so that step does not depend on the TLB; whether it sets accessed again then does, and
/// is not checked. A probe of 0 entries, of 65 and of a range that leaves the level 1 table is refused.
fn probed_bits_held(frame: u64) -> bool {
    let page = entry_address(PROBED_ENTRY) as *mut u64;
    if operation::map(operation::ROOT_PROCESS_SLOT, page as u64, 1, frame, 0) != operation::STATUS_OK
        || !probed_step_held(b"mapped", Some(false), false)
    {
        return false;
    }
    // The map just made the page the frame's, writable; the frame holds MAPPED_WORD, which the write puts
    // back.
    let word = unsafe { page.read_volatile() };
    if !probed_step_held(b"read", Some(true), false) || !probed_step_held(b"again", Some(false), false) {
        return false;
    }
    unsafe { page.write_volatile(word) };
    probed_step_held(b"written", None, true)
        && probe_refused(PROBE_FIRST, 0, b"of 0")
        && probe_refused(PROBE_FIRST, operation::PROBE_MAX + 1, b"of 65")
        && probe_refused(512 - operation::PROBE_MAX / 2, operation::PROBE_MAX, b"across tables")
}

/// The entry of the level 1 table at PATH_ADDRESS that the unmap check maps, the one after PROBED_ENTRY.
const UNMAPPED_ENTRY: u64 = PROBED_ENTRY + 1;

/// Whether an unmap returns the processor's bits from the entry it clears: dom0 maps the page at
/// UNMAPPED_ENTRY from `frame`, writes it and unmaps it, and the unmap finds accessed and dirty set, with
/// both maintained; it prints the two bits. The entry was never mapped before, so no translation of it was
/// cached and the write walks to it and sets both.
fn unmapped_bits_held(frame: u64) -> bool {
    let page = entry_address(UNMAPPED_ENTRY) as *mut u64;
    if operation::map(operation::ROOT_PROCESS_SLOT, page as u64, 1, frame, 0) != operation::STATUS_OK {
        return false;
    }
    // The map just made the page the frame's, writable; the frame holds MAPPED_WORD, which the write puts
    // back.
    unsafe { page.write_volatile(MAPPED_WORD) };
    // dom0 uses nothing at the page after this write.
    let unmapped = match unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, page as u64, 1) } {
        Ok(unmapped) => unmapped,
        Err(_) => return false,
    };
    let printed = print_parts(&[
        b"dom0 unmap written: a",
        bit_digit(unmapped.accessed),
        b" d",
        bit_digit(unmapped.dirty),
        b"\n",
    ]);
    printed == operation::STATUS_OK
        && unmapped.accessed
        && unmapped.dirty
        && unmapped.accessed_maintained
        && unmapped.dirty_maintained
}

/// Whether dom0 retypes the 2M block at the bottom of the last untyped of at least 512 pages as a frame
/// into the empty slot `destination`, repeating while retype returns again, and prints how many again
/// returns that took: a retype at a base not aligned to 2M is refused, the retype returns again at least
/// once and then ok, inspect says the slot holds a frame of order 9 at that base, and a second retype of
/// the block into the empty slot after `destination` is refused. Each again zeroes at least one of the
/// block's pages, so a retype still returning again after 512 has stopped going on, and fails. Boot pays
/// for dom0's tables from the start of the first untyped and the other checks take pages from the top of
/// an untyped, so that bottom is free unless the untyped is the first.
fn retyped_large_frame_held(empty: u64, destination: u64) -> bool {
    let (untyped, block) = match untyped_of_pages(empty, LARGE_FRAME_PAGES) {
        Some(found) => found,
        None => return false,
    };
    let base = block.base;
    let retype = |base: u64, destination: u64| operation::retype_large_frame(untyped, base, destination);
    if retype(base + 4096, destination) != operation::STATUS_REFUSED {
        return false;
    }
    let mut again = 0;
    let status = loop {
        let status = retype(base, destination);
        if status != operation::STATUS_AGAIN || again == LARGE_FRAME_PAGES {
            break status;
        }
        again += 1;
    };
    let held = status == operation::STATUS_OK
        && again > 0
        && matches!(
            operation::inspect(destination),
            Ok(frame) if frame.kind == operation::KIND_FRAME && frame.base == base && frame.order == 9
        )
        && retype(base, destination + 1) == operation::STATUS_REFUSED;
    held && print_done_after(LARGE_FRAME_HEAD, again) == operation::STATUS_OK
}

/// The read right, as the kernel numbers rights.
const RIGHT_READ: u64 = 1;

/// The retype right, which no frame has.
const RIGHT_RETYPE: u64 = 8;

/// The bytes of a 2M frame's block.
const LARGE_FRAME_BYTES: u64 = LARGE_FRAME_PAGES * 4096;

/// Whether dom0 derives from the 2M frame at `large` a child with only the read right, for the second
/// page of its block, into the empty slot `child`: a derive from the empty slot `empty`, with the frame's
/// rights and the retype right, of the page past the frame's block and into the occupied slot `occupied`
/// is refused, the derive is accepted, and inspect finds a frame of order 0 at that page, with the read
/// right alone, in `child`.
fn derived_frame_held(large: u64, empty: u64, occupied: u64, child: u64) -> bool {
    let parent = match operation::inspect(large) {
        Ok(capability) => capability,
        Err(_) => return false,
    };
    let page = parent.base + 4096;
    operation::derive(empty, child, RIGHT_READ, page, 0) == operation::STATUS_REFUSED
        && operation::derive(large, child, parent.rights | RIGHT_RETYPE, page, 0) == operation::STATUS_REFUSED
        && operation::derive(large, child, RIGHT_READ, parent.base + LARGE_FRAME_BYTES, 0) == operation::STATUS_REFUSED
        && operation::derive(large, occupied, RIGHT_READ, page, 0) == operation::STATUS_REFUSED
        && operation::derive(large, child, RIGHT_READ, page, 0) == operation::STATUS_OK
        && matches!(
            operation::inspect(child),
            Ok(frame) if frame.kind == operation::KIND_FRAME && frame.base == page && frame.order == 0 && frame.rights == RIGHT_READ
        )
}

/// How many pages dom0 maps through the frame it derived before it revokes the frame's parent: one less
/// than the nodes of the run the revoke removes, the child and these mappings, and as many as the
/// kernel's revoke budget, REVOKE_BUDGET in kernel/verified/capability/revoke.rs, so the revoke returns
/// again at least once.
const REVOKED_MAPPINGS: u64 = 64;

/// Whether dom0 revokes the 2M frame at `large` once its child at `child` is mapped REVOKED_MAPPINGS
/// times, from the entry after PATH_ADDRESS up, repeating while revoke returns again, and prints how many
/// again returns that took: each map is accepted and the first mapping reads the zero the 2M retype left,
/// a revoke of the empty slot `empty` and of a slot past the table is refused, the revoke returns again
/// at least once and then ok, the child's slot is refused by inspect, a map through it and an unmap at
/// its first mapping are refused, and inspect still finds the 2M frame. Each again removes at least one
/// node of the run, so a revoke still returning again after REVOKED_MAPPINGS + 1 has stopped going on,
/// and fails.
fn revoked_frame_held(large: u64, empty: u64, child: u64) -> bool {
    let address = |k: u64| PATH_ADDRESS + 4096 * k;
    let map = |k: u64| operation::map(operation::ROOT_PROCESS_SLOT, address(k), 1, child, 0);
    if !(1..=REVOKED_MAPPINGS).all(|k| map(k) == operation::STATUS_OK) {
        return false;
    }
    // The map just made the page at address(1) the child's, readable, and the 2M retype zeroed it.
    if unsafe { (address(1) as *const u64).read_volatile() } != 0 {
        return false;
    }
    // Nothing dom0 uses is mapped through either slot: the first is empty, the second past the table.
    let revoke = |slot: u64| unsafe { operation::revoke(slot) };
    if revoke(empty) != operation::STATUS_REFUSED || revoke(operation::TABLE_INDICES) != operation::STATUS_REFUSED {
        return false;
    }
    let mut again = 0;
    let status = loop {
        // dom0 reads nothing through the child's mappings after the read above.
        let status = revoke(large);
        if status != operation::STATUS_AGAIN || again > REVOKED_MAPPINGS {
            break status;
        }
        again += 1;
    };
    // The revoke cleared the entry at address(1), so an unmap there finds none; dom0 uses nothing there.
    let held = status == operation::STATUS_OK
        && again > 0
        && matches!(operation::inspect(child), Err(operation::STATUS_REFUSED))
        && map(1) == operation::STATUS_REFUSED
        && matches!(unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, address(1), 1) }, Err(operation::STATUS_REFUSED))
        && matches!(operation::inspect(large), Ok(frame) if frame.kind == operation::KIND_FRAME && frame.order == 9);
    held && print_done_after(REVOKE_HEAD, again) == operation::STATUS_OK
}

/// Whether dom0 deletes the 2M frame at `large` and a child it derives from it into the empty slot
/// `child`: the derive is accepted, a delete of the frame with that child below it is refused, the
/// child's delete is accepted and inspect then refuses its slot, the frame's delete is accepted, and
/// inspect and a second delete then refuse the frame's slot, as does a delete of a slot past the table.
fn deleted_frames_held(large: u64, child: u64) -> bool {
    let parent = match operation::inspect(large) {
        Ok(capability) => capability,
        Err(_) => return false,
    };
    operation::derive(large, child, RIGHT_READ, parent.base, 0) == operation::STATUS_OK
        && operation::delete(large) == operation::STATUS_REFUSED
        && operation::delete(child) == operation::STATUS_OK
        && matches!(operation::inspect(child), Err(operation::STATUS_REFUSED))
        && operation::delete(large) == operation::STATUS_OK
        && matches!(operation::inspect(large), Err(operation::STATUS_REFUSED))
        && operation::delete(large) == operation::STATUS_REFUSED
        && operation::delete(operation::TABLE_INDICES) == operation::STATUS_REFUSED
}

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
        && unknown == operation::STATUS_UNKNOWN
        && first_empty_slot().is_some_and(|empty| {
            retyped_frame_held(empty)
                && retyped_table_pages(empty)
                    .is_some_and(|(untyped, tables)| {
                        linked_path_held(untyped, tables)
                            && mapped_frame_held(empty)
                            && remapped_frame_held(empty)
                            && moved_frame_held(empty)
                            && retyped_large_frame_held(empty, empty + 2)
                            && derived_frame_held(empty + 2, empty, empty + 1, empty + 3)
                            && revoked_frame_held(empty + 2, empty, empty + 3)
                            && deleted_frames_held(empty + 2, empty + 3)
                            && timed_beside_before(empty + 1)
                            && probed_bits_held(empty + 1)
                            && unmapped_bits_held(empty + 1)
                    })
        });
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
