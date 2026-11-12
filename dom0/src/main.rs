// SPDX-License-Identifier: MIT

//! The root process of its kernel instance. It treats what boot gave it as all there is and does
//! not assume it owns the machine, so several instances each with a root stay possible. Why, and
//! what to do about a change that breaks this: design/one-kernel-instance/.
//!
//! Print, inspect, retype of a 4K frame, of a 2M frame, of a table page and of a table leaf, derive, move, delete, revoke, link, map, unmap, probe and power-off are the wired
//! operations, so each fixed slot is checked through them: the console accepts print and the process,
//! thread, power, untyped and frame slots refuse it, and the process and console slots refuse a
//! power-off; inspect says the console slot holds a console and the power slot a power capability, and
//! each slot from the first untyped holds an untyped whose base is aligned to its order, up to the first
//! slot that holds nothing, which inspect refuses. Retype under an empty slot, a slot past the table and
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
//! delete and a delete past the table are refused. It derives its power capability into that freed
//! slot, after a derive naming another page and one with a right power's does not carry are refused;
//! inspect finds power's capability in both slots, and once the child is deleted a power-off through
//! its slot is refused. It times one invocation of a number no operation has,
//! and one 4K map into each of 64 free entries of the level 1 table, and prints each cycle count beside
//! the before number from logs/cutover-before.log, 102 and 66926. It maps the frame at the entry after
//! those, and probes the 64 entries from there after the map, after reading the page, again, and after
//! writing it, printing the mapped entry's accessed and dirty bits each time: both clear, then accessed
//! alone, then both clear, then dirty; the other 63 entries, none of them present, have no bit set, and
//! both bits are maintained. A probe of 0 entries, of 65 and of a range leaving its level 1 table is refused. It maps
//! the frame at the next entry, writes the page and unmaps it, and the unmap returns accessed and dirty
//! set, both maintained, which it prints. It retypes another 4K frame, maps it beside that page, writes a
//! word through it, maps it at the unmapped page and reads that word there, not the old frame's. It
//! retypes a table leaf into root entry 2 of its own table, the first boot leaves empty, after a retype into the occupied entry 1, into entry 512, past the root's, by
//! a word naming no position and of a block that is not free is refused, and a second leaf into entry 3
//! through its own process capability, after entry 2 named through it is refused; inspect refuses each
//! leaf's first slot until a derive of the power capability into it, after which inspect finds it there.
//! It retypes a third leaf into root entry 4 and derives into its first slot a child untyped of 64 pages
//! of the gigabyte untyped, from which aeager's eager span source backs page runs of a window in root
//! entry 3 of its space; aeager's verified exercise reserves a span, backs it a page at a time until the
//! source refuses, writes a byte through the run and reads it back, releases it, backs a page again and
//! gives the span back, and dom0 prints how many pages it backed. It then gives astd's global allocator
//! a second eager source, over a child untyped of as many pages as the source records, frame slots in
//! the leaves of the root entries after the first source's and a window in root entry 4 of its space,
//! and allocates through it a box of the smallest class, a vector between a page and a block and one
//! over a block, writing and reading each back; once all three are freed it allocates run-sized
//! objects until the allocator refuses one, frees them, allocates one again, and prints that the heap
//! held.
//! dom0 prints that result through the console, then an exit marker,
//! and ends the run with a power-off through its power capability, reporting success only when every
//! check held. On aarch64, where the instruction carries an immediate, a print through the console by
//! `svc #1` returns unknown and prints nothing.
//!
//! dom0 invokes retype, derive, inspect, move, delete, revoke, link and map through acall's wrappers,
//! whose ensures are the kernel's proven contracts, so the code those proofs speak of is the code that
//! boots. dom0 is not verified: the caller token it threads through them erases in its build, and
//! nothing here checks the wrappers' requires.

#![no_std]
#![no_main]

extern crate alloc;

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::panic::PanicInfo;

use acall::capability::{delete, move_cap, revoke};
use acall::memory::{derive, link, map, retype};
use acall::step::Caller;
use asys::operation;
use vstd::prelude::Tracked;

/// What inspect says of the capability at position `slot`, through acall's wrapper, or the status it
/// returned when the position holds none.
fn inspect(caller: &mut Tracked<Caller>, slot: u64) -> Result<operation::Capability, u64> {
    let out = acall::memory::inspect(caller, slot);
    match out.status {
        operation::STATUS_OK => Ok(operation::Capability {
            kind: out.result_1,
            base: out.result_2,
            order: out.result_3,
            rights: out.result_4,
        }),
        refused => Err(refused),
    }
}

/// A number past every operation's.
const NO_OPERATION: u64 = 0xffff;

/// The arguments of the first invocation. Each word names its position, r10 last.
const FIRST_ARGUMENTS: [u64; 5] = [1, 2, 3, 4, 5];

/// What dom0 prints through the console when the fixed-slot checks held, which the gate looks for.
const CHECKS_HELD: [u64; 5] = operation::print_words(b"dom0 slot checks held\n");

/// What dom0 prints through the console when a check did not hold.
const CHECKS_FAILED: [u64; 5] = operation::print_words(b"dom0 slot checks failed\n");

/// The line after the check line. dom0 reports success only once this print is accepted.
const EXIT_MARKER: [u64; 5] = operation::print_words(b"dom0 capability done\n");

/// The largest order a capability's block has: 2^36 pages reach the end of the 48-bit space.
const MAX_ORDER: u64 = 36;

/// The last slot of the table's first leaf, where boot's untyped end.
const FIRST_LEAF_END: u64 = operation::ROOT_FRAME_SLOT - 2;

/// A word with a bit set above those a table position uses, so it names no position.
const NO_POSITION: u64 = 1 << operation::POSITION_WIDTH;

/// The first slot after the untyped, once inspect says the console slot holds a console, also when named
/// through the root's own process capability, and refuses a word naming no position, the power slot
/// holds a power capability, and every slot from the first untyped holds an untyped whose base is
/// aligned to its order, at least one, up to that slot, which inspect refuses because it holds nothing.
/// Boot fills the untyped slots from the first and leaves the rest of the leaf empty,
/// design/root-process-at-boot/; a leaf full of untyped leaves no empty slot in it to read, and fails.
fn first_empty_slot(caller: &mut Tracked<Caller>) -> Option<u64> {
    let console = inspect(caller, operation::ROOT_CONSOLE_SLOT);
    if !matches!(console, Ok(capability) if capability.kind == operation::KIND_CONSOLE) {
        return None;
    }
    if inspect(caller, operation::through(operation::ROOT_PROCESS_SLOT, operation::ROOT_CONSOLE_SLOT)) != console
        || inspect(caller, NO_POSITION | operation::ROOT_CONSOLE_SLOT) != Err(operation::STATUS_REFUSED)
    {
        return None;
    }
    let power = inspect(caller, operation::ROOT_POWER_SLOT);
    if !matches!(power, Ok(capability) if capability.kind == operation::KIND_POWER) {
        return None;
    }
    let mut slot = operation::ROOT_UNTYPED_SLOT;
    while slot <= FIRST_LEAF_END {
        match inspect(caller, slot) {
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
fn retyped_frame_held(caller: &mut Tracked<Caller>, empty: u64) -> bool {
    let untyped = empty - 1;
    let base = match inspect(caller, untyped) {
        Ok(block) => block.base + (4096 << block.order) - 4096,
        Err(_) => return false,
    };
    let mut retype_frame = |slot| retype(caller, slot, operation::RETYPE_FRAME, base, empty, 0).status;
    if retype_frame(empty) != operation::STATUS_REFUSED
        || retype_frame(operation::TABLE_INDICES) != operation::STATUS_REFUSED
        || retype_frame(operation::ROOT_CONSOLE_SLOT) != operation::STATUS_REFUSED
        || retype_frame(untyped) != operation::STATUS_OK
    {
        return false;
    }
    matches!(
        inspect(caller, empty),
        Ok(frame) if frame.kind == operation::KIND_FRAME && frame.base == base && frame.order == 0
    )
}

/// Where dom0 builds a path of tables: the start of root entry 2, past the image's at entry 1
/// (`USERSPACE_BASE`), so linking there changes nothing dom0 reads.
const PATH_ADDRESS: u64 = 2 << 39;

/// The bytes of a table page's block, order 3.
const TABLE_PAGE_BYTES: u64 = 8 * 4096;

/// The last untyped from `empty` down whose block holds at least `pages` 4K pages, if any.
fn untyped_of_pages(caller: &mut Tracked<Caller>, empty: u64, pages: u64) -> Option<(u64, operation::Capability)> {
    let mut slot = empty;
    while slot > operation::ROOT_UNTYPED_SLOT {
        slot -= 1;
        match inspect(caller, slot) {
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
fn retyped_table_pages(caller: &mut Tracked<Caller>, empty: u64) -> Option<(u64, [u64; 4])> {
    let (untyped, block) = untyped_of_pages(caller, empty, 64)?;
    let top = block.base + (4096 << block.order);
    let tables = [1, 2, 3, 4].map(|k| top - TABLE_PAGE_BYTES * (k + 1));
    let mut retype_table = |k: usize, level: u64| {
        retype(caller, untyped, operation::RETYPE_TABLE_PAGE, tables[k], 0, level).status
    };
    let held = retype_table(0, 0) == operation::STATUS_REFUSED
        && retype_table(0, 4) == operation::STATUS_REFUSED
        && retype_table(0, 3) == operation::STATUS_OK
        && retype_table(1, 2) == operation::STATUS_OK
        && retype_table(2, 1) == operation::STATUS_OK
        && retype_table(3, 1) == operation::STATUS_OK
        && retype_table(0, 3) == operation::STATUS_REFUSED;
    held.then_some((untyped, tables))
}

/// Whether dom0 builds a path of the level 3, 2 and 1 tables at `tables`, under `untyped`, at
/// `PATH_ADDRESS` in its own space, through its process capability: link of the level 1 page into the
/// level 3 entry, of a table into a level 2 entry whose level 2 table is not linked yet, and at an
/// address not aligned to its level 2 entry is refused; the level 3, 2 and 1 tables link; and the fourth
/// page, of level 1, is refused at the level 2 entry the level 1 table took.
fn linked_path_held(caller: &mut Tracked<Caller>, untyped: u64, tables: [u64; 4]) -> bool {
    let mut link_table = |address: u64, level: u64, k: usize| {
        link(caller, operation::ROOT_PROCESS_SLOT, address, level, untyped, tables[k]).status
    };
    link_table(PATH_ADDRESS, 4, 0) == operation::STATUS_OK
        && link_table(PATH_ADDRESS, 3, 2) == operation::STATUS_REFUSED
        && link_table(PATH_ADDRESS, 2, 2) == operation::STATUS_REFUSED
        && link_table(PATH_ADDRESS, 3, 1) == operation::STATUS_OK
        && link_table(PATH_ADDRESS + 4096, 2, 2) == operation::STATUS_REFUSED
        && link_table(PATH_ADDRESS, 2, 2) == operation::STATUS_OK
        && link_table(PATH_ADDRESS, 2, 3) == operation::STATUS_REFUSED
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
fn mapped_frame_held(caller: &mut Tracked<Caller>, frame: u64) -> bool {
    let mut map_at = |address: u64| map(caller, operation::ROOT_PROCESS_SLOT, address, 1, frame, 0).status;
    if map_at(KERNEL_HALF_ADDRESS) != operation::STATUS_REFUSED
        || map_at(NON_CANONICAL_ADDRESS) != operation::STATUS_REFUSED
        || map_at(PATH_ADDRESS) != operation::STATUS_OK
    {
        return false;
    }
    let word = PATH_ADDRESS as *mut u64;
    // The map just made the page at PATH_ADDRESS the frame's, writable, and nothing else names it.
    let read = unsafe {
        word.write_volatile(MAPPED_WORD);
        word.read_volatile()
    };
    read == MAPPED_WORD && map_at(PATH_ADDRESS) == operation::STATUS_REFUSED
}

/// Whether dom0 unmaps the 4K frame at `frame` that it mapped at `PATH_ADDRESS` and maps it there again:
/// an unmap at a kernel-half address, at the empty entry after `PATH_ADDRESS` and at level 2 is refused,
/// the unmap at `PATH_ADDRESS` is accepted and a second one refused, and a map of the frame there is
/// accepted again and reads back the word written through the first mapping.
fn remapped_frame_held(caller: &mut Tracked<Caller>, frame: u64) -> bool {
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
        || map(caller, operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1, frame, 0).status != operation::STATUS_OK
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
fn moved_frame_held(caller: &mut Tracked<Caller>, frame: u64) -> bool {
    let moved = frame + 1;
    let base = match inspect(caller, frame) {
        Ok(capability) => capability.base,
        Err(_) => return false,
    };
    let map_from = |caller: &mut Tracked<Caller>, slot: u64| {
        map(caller, operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1, slot, 0).status
    };
    let held = move_cap(caller, moved, moved).status == operation::STATUS_REFUSED
        && move_cap(caller, frame, operation::ROOT_CONSOLE_SLOT).status == operation::STATUS_REFUSED
        && move_cap(caller, frame, moved).status == operation::STATUS_OK
        && matches!(inspect(caller, frame), Err(operation::STATUS_REFUSED))
        && matches!(
            inspect(caller, moved),
            Ok(capability) if capability.kind == operation::KIND_FRAME && capability.base == base && capability.order == 0
        )
        // Nothing dom0 uses is at PATH_ADDRESS but the word, which it reads only after the map that follows.
        && unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1) }.is_ok()
        && map_from(caller, frame) == operation::STATUS_REFUSED
        && map_from(caller, moved) == operation::STATUS_OK;
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

/// The cycle counter: the TSC on x86_64, the virtual counter on aarch64.
fn rdtsc() -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        let lo: u32;
        let hi: u32;
        unsafe {
            core::arch::asm!(
                "rdtsc",
                out("eax") lo,
                out("edx") hi,
                options(nomem, nostack, preserves_flags)
            );
        }
        ((hi as u64) << 32) | lo as u64
    }
    #[cfg(target_arch = "aarch64")]
    {
        let ticks: u64;
        unsafe {
            core::arch::asm!(
                "mrs {ticks}, cntvct_el0",
                ticks = out(reg) ticks,
                options(nomem, nostack, preserves_flags)
            );
        }
        ticks
    }
}

/// How many free entries of the level 1 table at PATH_ADDRESS the timed maps fill, one page each.
/// Entry 0 is the frame's existing mapping. Entries 1..=64 are free: revoke cleared them.
const TIMED_MAPS: u64 = 64;

/// The before number for an unassigned invocation, logs/cutover-before.log: 102 TSC cycles.
const NULL_TAIL: &[u8] = b" before 102\n";

/// The before number for a 4K map, one page per call, logs/cutover-before.log: 66926 TSC cycles per page.
const MAP_TAIL: &[u8] = b"/p before 66926\n";

/// Performance counters 0 to 3 as RDPMC reads them, where the kernel counts on them: cycles not in
/// halt, retired instructions, data cache fills, and the fills that came from another CCX's cache.
/// The kernel programs them at boot where CPUID offers the extended core counters, and dom0 tests the
/// same bit first, since RDPMC faults in a process where the kernel did not; aarch64 has none here.
fn counters() -> Option<[u64; 4]> {
    #[cfg(target_arch = "x86_64")]
    {
        /// CPUID Fn8000_0001 ECX bit 23, PerfCtrExtCore. AMD APM 2 §13.2.2.
        const PERF_CTR_EXT_CORE: u32 = 1 << 23;
        if core::arch::x86_64::__cpuid(0x8000_0001).ecx & PERF_CTR_EXT_CORE == 0 {
            return None;
        }
        let mut counts = [0; 4];
        for (n, count) in counts.iter_mut().enumerate() {
            let lo: u32;
            let hi: u32;
            unsafe {
                core::arch::asm!(
                    "rdpmc",
                    in("ecx") n as u32,
                    out("eax") lo,
                    out("edx") hi,
                    options(nomem, nostack, preserves_flags)
                );
            }
            *count = ((hi as u64) << 32) | lo as u64;
        }
        Some(counts)
    }
    #[cfg(target_arch = "aarch64")]
    {
        None
    }
}

/// The head of the line for each counter counters() reads, after the head of what was counted.
const COUNTER_HEADS: [&[u8]; 4] = [b"cycles ", b"instructions ", b"fills ", b"ccx fills "];

/// Whether, when both `before` and `after` are some, a line for each counter prints `what`, the
/// counter's head, how far it moved from `before` to `after`, and `tail`; or both are none, and
/// nothing is printed.
fn print_counters(what: &[u8], before: Option<[u64; 4]>, after: Option<[u64; 4]>, tail: &[u8]) -> bool {
    match (before, after) {
        (Some(before), Some(after)) => (0..4).all(|n| {
            let mut head = [0u8; 18];
            head[..what.len()].copy_from_slice(what);
            head[what.len()..what.len() + COUNTER_HEADS[n].len()].copy_from_slice(COUNTER_HEADS[n]);
            print_count(&head[..what.len() + COUNTER_HEADS[n].len()], after[n] - before[n], tail)
                == operation::STATUS_OK
        }),
        (None, None) => true,
        _ => false,
    }
}

/// The tail of a counter line for the timed maps: the count is over all TIMED_MAPS of them.
const MAPS_COUNTER_TAIL: &[u8] = b"/64\n";
const _: () = assert!(TIMED_MAPS == 64);

/// Whether dom0 times one invocation of a number no operation has, which returns unknown, and one 4K
/// map of `frame` into each of TIMED_MAPS free entries of the level 1 table, and prints each cycle count
/// beside its before number, then what the performance counters counted over each, where there are
/// any. The counts are not checked against those numbers. The timed maps start at the page after
/// PATH_ADDRESS, which already holds `frame`.
fn timed_beside_before(caller: &mut Tracked<Caller>, frame: u64) -> bool {
    let null_before = counters();
    let start = rdtsc();
    let unknown = operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
    let null_cycles = rdtsc() - start;
    let null_after = counters();
    if unknown != operation::STATUS_UNKNOWN {
        return false;
    }
    let maps_before = counters();
    let start = rdtsc();
    for k in 1..=TIMED_MAPS {
        let address = PATH_ADDRESS + 4096 * k;
        if map(caller, operation::ROOT_PROCESS_SLOT, address, 1, frame, 0).status != operation::STATUS_OK {
            return false;
        }
    }
    let maps_cycles = rdtsc() - start;
    let maps_after = counters();
    print_count(b"null ", null_cycles, NULL_TAIL) == operation::STATUS_OK
        && print_count(b"4k ", maps_cycles / TIMED_MAPS, MAP_TAIL) == operation::STATUS_OK
        && print_count(b"4k tsc ", maps_cycles, MAPS_COUNTER_TAIL) == operation::STATUS_OK
        && print_counters(b"null ", null_before, null_after, b"\n")
        && print_counters(b"4k ", maps_before, maps_after, MAPS_COUNTER_TAIL)
}

/// The entry of the level 1 table at PATH_ADDRESS that the probe check maps, the one after the timed
/// maps'.
const PROBED_ENTRY: u64 = TIMED_MAPS + 1;

/// The first of the operation::PROBE_MAX entries the probe check reads, which start at PROBED_ENTRY, so
/// that no other entry they cover is present while it probes. A present entry may have its accessed bit
/// set by a speculative or prefetching access no instruction asked for (Arm ARM D8.5.1.2, rules RLHQRX and
/// ILLCCB), which the timed maps' entries below PROBED_ENTRY took on the Orange Pi when dom0 read the
/// page above them; an entry that is not present has no bits for that to set.
const PROBE_FIRST: u64 = PROBED_ENTRY;

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

/// Whether a probe of the operation::PROBE_MAX entries from PROBED_ENTRY is accepted and finds
/// PROBED_ENTRY's dirty bit `dirty` and, when `accessed` is some, its accessed bit that, and every other
/// entry's bits clear, as none of them is present, with both bits maintained; it prints `step` and PROBED_ENTRY's two bits, and the
/// status of a refused probe, or both masks and the two facts of a step that does not hold.
fn probed_step_held(step: &[u8], accessed: Option<bool>, dirty: bool) -> bool {
    let probed = match operation::probe(operation::ROOT_PROCESS_SLOT, entry_address(PROBE_FIRST), operation::PROBE_MAX) {
        Ok(probed) => probed,
        Err(status) => {
            print_count(b"dom0 probe refused ", status, b"\n");
            return false;
        }
    };
    let a = probed.accessed & PROBED_BIT != 0;
    let d = probed.dirty & PROBED_BIT != 0;
    let printed = print_parts(&[b"dom0 probe ", step, b": a", bit_digit(a), b" d", bit_digit(d), b"\n"]);
    let held = probed.accessed_maintained
        && probed.dirty_maintained
        && (probed.accessed | probed.dirty) & !PROBED_BIT == 0
        && d == dirty
        && match accessed {
            Some(expected) => a == expected,
            None => true,
        };
    if !held {
        print_count(b"dom0 probe a mask ", probed.accessed, b"\n");
        print_count(b"dom0 probe d mask ", probed.dirty, b"\n");
        print_parts(&[
            b"dom0 probe maintained: a",
            bit_digit(probed.accessed_maintained),
            b" d",
            bit_digit(probed.dirty_maintained),
            b"\n",
        ]);
    }
    printed == operation::STATUS_OK && held
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
fn probed_bits_held(caller: &mut Tracked<Caller>, frame: u64) -> bool {
    let page = entry_address(PROBED_ENTRY) as *mut u64;
    if map(caller, operation::ROOT_PROCESS_SLOT, page as u64, 1, frame, 0).status != operation::STATUS_OK
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
fn unmapped_bits_held(caller: &mut Tracked<Caller>, frame: u64) -> bool {
    let page = entry_address(UNMAPPED_ENTRY) as *mut u64;
    if map(caller, operation::ROOT_PROCESS_SLOT, page as u64, 1, frame, 0).status != operation::STATUS_OK {
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

/// The word dom0 writes through the frame it maps where UNMAPPED_ENTRY's page was, unlike MAPPED_WORD.
const OTHER_WORD: u64 = 0x6b65_726e_656c_2032;

/// The pages below the top of the table check's untyped where the remap check takes its frame: the order-3
/// block below the table pages' four blocks, the block their own top one leaves free and the leaf check's
/// two leaves of two pages each.
const OTHER_FRAME_BELOW_TOP: u64 = 7 * 8 * 4096;

/// Whether a map after an unmap gives the new frame's bytes: dom0 retypes a page of `untyped`, the table
/// check's, OTHER_FRAME_BELOW_TOP below its top, into the empty slot `other`, maps it at the entry after
/// UNMAPPED_ENTRY and writes OTHER_WORD through it, then maps it at UNMAPPED_ENTRY, whose page
/// unmapped_bits_held wrote and unmapped, and reads OTHER_WORD there. A core that kept the unmapped
/// page's translation would read MAPPED_WORD from the old frame: the unmap's flush must reach the calling
/// core before the map returns. See design/flush-without-waiting/.
fn remapped_other_frame_held(caller: &mut Tracked<Caller>, untyped: u64, other: u64) -> bool {
    let base = match inspect(caller, untyped) {
        Ok(block) => block.base + (4096 << block.order) - OTHER_FRAME_BELOW_TOP,
        Err(_) => return false,
    };
    let beside = entry_address(UNMAPPED_ENTRY + 1) as *mut u64;
    let page = entry_address(UNMAPPED_ENTRY) as *const u64;
    if retype(caller, untyped, operation::RETYPE_FRAME, base, other, 0).status != operation::STATUS_OK
        || map(caller, operation::ROOT_PROCESS_SLOT, beside as u64, 1, other, 0).status != operation::STATUS_OK
    {
        return false;
    }
    // The map just made the page beside the new frame's, writable, and nothing else names it.
    unsafe { beside.write_volatile(OTHER_WORD) };
    if map(caller, operation::ROOT_PROCESS_SLOT, page as u64, 1, other, 0).status != operation::STATUS_OK {
        return false;
    }
    // The map just made the page the new frame's, which holds OTHER_WORD.
    unsafe { page.read_volatile() == OTHER_WORD }
}

/// Whether dom0 retypes the 2M block at the bottom of the last untyped of at least 512 pages as a frame
/// into the empty slot `destination`, repeating while retype returns again, and prints how many again
/// returns that took: a retype at a base not aligned to 2M is refused, the retype returns again at least
/// once and then ok, inspect says the slot holds a frame of order 9 at that base, and a second retype of
/// the block into the empty slot after `destination` is refused. Each again zeroes at least one of the
/// block's pages, so a retype still returning again after 512 has stopped going on, and fails. Boot pays
/// for dom0's tables from the start of the first untyped and the other checks take pages from the top of
/// an untyped, so that bottom is free unless the untyped is the first.
fn retyped_large_frame_held(caller: &mut Tracked<Caller>, empty: u64, destination: u64) -> bool {
    let (untyped, block) = match untyped_of_pages(caller, empty, LARGE_FRAME_PAGES) {
        Some(found) => found,
        None => return false,
    };
    let base = block.base;
    let retype_large = |caller: &mut Tracked<Caller>, base: u64, destination: u64| {
        retype(caller, untyped, operation::RETYPE_LARGE_FRAME, base, destination, 0).status
    };
    if retype_large(caller, base + 4096, destination) != operation::STATUS_REFUSED {
        return false;
    }
    let mut again = 0;
    let status = loop {
        let status = retype_large(caller, base, destination);
        if status != operation::STATUS_AGAIN || again == LARGE_FRAME_PAGES {
            break status;
        }
        again += 1;
    };
    let held = status == operation::STATUS_OK
        && again > 0
        && matches!(
            inspect(caller, destination),
            Ok(frame) if frame.kind == operation::KIND_FRAME && frame.base == base && frame.order == 9
        )
        && retype_large(caller, base, destination + 1) == operation::STATUS_REFUSED;
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
fn derived_frame_held(caller: &mut Tracked<Caller>, large: u64, empty: u64, occupied: u64, child: u64) -> bool {
    let parent = match inspect(caller, large) {
        Ok(capability) => capability,
        Err(_) => return false,
    };
    let page = parent.base + 4096;
    derive(caller, empty, child, RIGHT_READ, page, 0).status == operation::STATUS_REFUSED
        && derive(caller, large, child, parent.rights | RIGHT_RETYPE, page, 0).status == operation::STATUS_REFUSED
        && derive(caller, large, child, RIGHT_READ, parent.base + LARGE_FRAME_BYTES, 0).status == operation::STATUS_REFUSED
        && derive(caller, large, occupied, RIGHT_READ, page, 0).status == operation::STATUS_REFUSED
        && derive(caller, large, child, RIGHT_READ, page, 0).status == operation::STATUS_OK
        && matches!(
            inspect(caller, child),
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
/// a revoke of the empty slot `empty` and of a word naming no position is refused, the revoke returns again
/// at least once and then ok, the child's slot is refused by inspect, a map through it and an unmap at
/// its first mapping are refused, and inspect still finds the 2M frame. Each again removes at least one
/// node of the run, so a revoke still returning again after REVOKED_MAPPINGS + 1 has stopped going on,
/// and fails.
fn revoked_frame_held(caller: &mut Tracked<Caller>, large: u64, empty: u64, child: u64) -> bool {
    let address = |k: u64| PATH_ADDRESS + 4096 * k;
    let map_child = |caller: &mut Tracked<Caller>, k: u64| {
        map(caller, operation::ROOT_PROCESS_SLOT, address(k), 1, child, 0).status
    };
    if !(1..=REVOKED_MAPPINGS).all(|k| map_child(caller, k) == operation::STATUS_OK) {
        return false;
    }
    // The map just made the page at address(1) the child's, readable, and the 2M retype zeroed it.
    if unsafe { (address(1) as *const u64).read_volatile() } != 0 {
        return false;
    }
    // Nothing dom0 uses is mapped through either: the slot is empty, and the word names no position.
    if revoke(caller, empty).status != operation::STATUS_REFUSED
        || revoke(caller, NO_POSITION | large).status != operation::STATUS_REFUSED
    {
        return false;
    }
    let mut again = 0;
    let status = loop {
        // dom0 reads nothing through the child's mappings after the read above.
        let status = revoke(caller, large).status;
        if status != operation::STATUS_AGAIN || again > REVOKED_MAPPINGS {
            break status;
        }
        again += 1;
    };
    // The revoke cleared the entry at address(1), so an unmap there finds none; dom0 uses nothing there.
    let held = status == operation::STATUS_OK
        && again > 0
        && matches!(inspect(caller, child), Err(operation::STATUS_REFUSED))
        && map_child(caller, 1) == operation::STATUS_REFUSED
        && matches!(unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, address(1), 1) }, Err(operation::STATUS_REFUSED))
        && matches!(inspect(caller, large), Ok(frame) if frame.kind == operation::KIND_FRAME && frame.order == 9);
    held && print_done_after(REVOKE_HEAD, again) == operation::STATUS_OK
}

/// Whether dom0 deletes the 2M frame at `large` and a child it derives from it into the empty slot
/// `child`: the derive is accepted, a delete of the frame with that child below it is refused, the
/// child's delete is accepted and inspect then refuses its slot, the frame's delete is accepted, and
/// inspect and a second delete then refuse the frame's slot, as does a delete of a word naming no position.
fn deleted_frames_held(caller: &mut Tracked<Caller>, large: u64, child: u64) -> bool {
    let parent = match inspect(caller, large) {
        Ok(capability) => capability,
        Err(_) => return false,
    };
    derive(caller, large, child, RIGHT_READ, parent.base, 0).status == operation::STATUS_OK
        && delete(caller, large).status == operation::STATUS_REFUSED
        && delete(caller, child).status == operation::STATUS_OK
        && matches!(inspect(caller, child), Err(operation::STATUS_REFUSED))
        && delete(caller, large).status == operation::STATUS_OK
        && matches!(inspect(caller, large), Err(operation::STATUS_REFUSED))
        && delete(caller, large).status == operation::STATUS_REFUSED
        && delete(caller, NO_POSITION).status == operation::STATUS_REFUSED
}

/// Whether dom0 passes a copy of its power capability on and keeps its own: a derive from the power
/// slot into the empty slot `child` naming the page after power's, or with a right power's capability
/// does not carry, is refused; the derive naming power's page is accepted, after which inspect finds
/// the same power capability in `child` and in the power slot; the child's delete is accepted, and a
/// power-off through its slot is then refused.
fn derived_power_held(caller: &mut Tracked<Caller>, child: u64) -> bool {
    let power = match inspect(caller, operation::ROOT_POWER_SLOT) {
        Ok(capability) => capability,
        Err(_) => return false,
    };
    derive(caller, operation::ROOT_POWER_SLOT, child, power.rights, power.base + 4096, 0).status == operation::STATUS_REFUSED
        && derive(caller, operation::ROOT_POWER_SLOT, child, power.rights | RIGHT_READ, power.base, 0).status
            == operation::STATUS_REFUSED
        && derive(caller, operation::ROOT_POWER_SLOT, child, power.rights, power.base, 0).status == operation::STATUS_OK
        && inspect(caller, child) == Ok(power)
        && inspect(caller, operation::ROOT_POWER_SLOT) == Ok(power)
        && delete(caller, child).status == operation::STATUS_OK
        && operation::power_off(child, false) == operation::STATUS_REFUSED
}

/// The indices a table leaf gives its root entry: entry r holds those from r times this, of which the
/// first is the leaf's hidden node and no slot, as slot 0 and slot 128 are.
const LEAF_INDICES: u64 = 128;

/// The root entries of a capability table.
const ROOT_ENTRIES: u64 = operation::TABLE_INDICES / LEAF_INDICES;

/// The first slot of root entry `entry`, past its leaf's hidden node.
const fn first_slot(entry: u64) -> u64 {
    entry * LEAF_INDICES + 1
}

/// The first root entry boot leaves empty: it fills entry 0 with the fixed slots and the untyped and
/// entry 1 with the image's frames, design/root-process-at-boot/.
const FIRST_EMPTY_ENTRY: u64 = 2;

/// The bytes of a table leaf's block, order 1.
const LEAF_BYTES: u64 = 2 * 4096;

/// Whether the table leaf just retyped into root entry `entry` gives the entry its slots: inspect refuses
/// the entry's first slot while it is empty, a derive of the power capability into it, named by the
/// position word `slot`, is accepted, and inspect then finds power's capability there.
fn leaf_slot_held(caller: &mut Tracked<Caller>, entry: u64, slot: u64) -> bool {
    let first = first_slot(entry);
    let power = match inspect(caller, operation::ROOT_POWER_SLOT) {
        Ok(capability) => capability,
        Err(_) => return false,
    };
    matches!(inspect(caller, first), Err(operation::STATUS_REFUSED))
        && derive(caller, operation::ROOT_POWER_SLOT, slot, power.rights, power.base, 0).status == operation::STATUS_OK
        && inspect(caller, first) == Ok(power)
}

/// Whether dom0 retypes two table leaves under `untyped`, from the two order-1 blocks below the table
/// page at `table`, which retype took, into root entries FIRST_EMPTY_ENTRY and the one after it of its
/// own table: a retype into an occupied entry, into an entry past the root's, by a word naming no position
/// and of the table page's block, which is not free, is refused; the first leaf is retyped by its bare
/// entry and the second through dom0's own process capability, after which that entry named through it is
/// refused, being occupied; and each leaf's first slot takes a capability that inspect reads back, the
/// second's named through the process capability. Each check takes its pages from below the table pages,
/// which nothing else retypes.
fn retyped_leaves_held(caller: &mut Tracked<Caller>, untyped: u64, table: u64) -> bool {
    let first = FIRST_EMPTY_ENTRY;
    let second = FIRST_EMPTY_ENTRY + 1;
    let through = |entry: u64| operation::through(operation::ROOT_PROCESS_SLOT, entry);
    let retype_leaf = |caller: &mut Tracked<Caller>, base: u64, entry: u64| {
        retype(caller, untyped, operation::RETYPE_LEAF, base, entry, 0).status
    };
    let base = table - LEAF_BYTES;
    retype_leaf(caller, base, FIRST_EMPTY_ENTRY - 1) == operation::STATUS_REFUSED
        && retype_leaf(caller, base, ROOT_ENTRIES) == operation::STATUS_REFUSED
        && retype_leaf(caller, base, NO_POSITION | first) == operation::STATUS_REFUSED
        && retype_leaf(caller, table, first) == operation::STATUS_REFUSED
        && retype_leaf(caller, base, first) == operation::STATUS_OK
        && leaf_slot_held(caller, first, first_slot(first))
        && retype_leaf(caller, base - LEAF_BYTES, through(first)) == operation::STATUS_REFUSED
        && retype_leaf(caller, base - LEAF_BYTES, through(second)) == operation::STATUS_OK
        && leaf_slot_held(caller, second, through(first_slot(second)))
}

/// The root entry of dom0's table that takes the eager source's frame capabilities, the one after the
/// leaves the leaf check retypes.
const EAGER_ENTRY: u64 = FIRST_EMPTY_ENTRY + 2;

/// The pages of the block dom0 gives the eager source, whose frames all fit in the one leaf at
/// EAGER_ENTRY after the source's untyped.
const EAGER_PAGES: usize = 64;

/// The order of the block dom0 gives the eager source.
const EAGER_ORDER: u64 = EAGER_PAGES.trailing_zeros() as u64;

/// How far below the top of the gigabyte untyped the eager source's block starts, clear of the pages the
/// frame, table page and leaf checks take from that top.
const EAGER_BELOW_TOP: u64 = 256 * 4096;

/// The address of the eager source's window: the start of root entry 3 of dom0's space, past
/// PATH_ADDRESS's, which nothing maps.
const EAGER_WINDOW: u64 = 3 << 39;

/// The start of the line dom0 prints once its eager source is exercised, before how many pages it backed.
const EAGER_HEAD: &[u8] = b"dom0 eager backed ";

/// Whether dom0 runs aeager's verified exercise over an eager source of its own: from the untyped that is
/// a gigabyte, a table leaf into root entry EAGER_ENTRY and a child untyped of EAGER_ORDER below
/// EAGER_BELOW_TOP into its first slot, whose pages the source alone retypes, putting frame capabilities
/// in the slots after it, and the window at EAGER_WINDOW. The exercise reserves a span; backs, writes and
/// releases its first page, backs and writes its second, backs and writes its first again and reads the
/// second; backs the span a page at a time until the source refuses, writes a byte through the run and
/// reads it back, releases the run, backs a page again, backs the page it refused and writes and reads a
/// byte there, and gives the span back. dom0 prints how many pages it backed, and the check holds when
/// the second page read its own byte, so no translation of the first outlived its release, the source
/// refused before the block was full, the byte read back, a page was backed again, and the refused page
/// was backed once the run was released, with every page of the untyped then mapped or parked.
fn eager_source_held(caller: &mut Tracked<Caller>, empty: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let top = block.base + (4096 << block.order);
    let memory = top - EAGER_BELOW_TOP;
    let source = first_slot(EAGER_ENTRY);
    if retype(caller, untyped, operation::RETYPE_LEAF, memory - LEAF_BYTES, EAGER_ENTRY, 0).status != operation::STATUS_OK
        || derive(caller, untyped, source, block.rights, memory, EAGER_ORDER).status != operation::STATUS_OK
    {
        return false;
    }
    let Some(mut eager) = aeager::Eager::new(
        operation::ROOT_PROCESS_SLOT,
        source,
        memory,
        EAGER_PAGES,
        source + 1,
        EAGER_WINDOW as *mut u8,
    ) else {
        return false;
    };
    let seen = aeager::exercise(&mut eager, caller);
    print_count(EAGER_HEAD, seen.backed as u64, b"\n") == operation::STATUS_OK
        && seen.apart
        && seen.backed > 0
        && seen.refused
        && seen.read
        && seen.again
        && seen.fresh
}

/// The root entries of dom0's table whose leaves take the heap's source's capabilities: its untyped in
/// the first slot of the first, and the frames for its pages in the slots after it, which the source
/// carries on past each leaf's end into the next.
const HEAP_ENTRY: u64 = EAGER_ENTRY + 1;

/// The pages of the block dom0 gives the heap's source: as many as a source records, enough for an
/// object over a block beside the heap's other spans and the window's tables.
const HEAP_PAGES: usize = aeager::MAX_PAGES;

/// The order of the block dom0 gives the heap's source.
const HEAP_ORDER: u64 = HEAP_PAGES.trailing_zeros() as u64;

/// The leaves the heap's source's capabilities take: the untyped and HEAP_PAGES frames, at
/// LEAF_INDICES - 1 slots a leaf.
const HEAP_LEAVES: u64 = (HEAP_PAGES as u64 + 1).div_ceil(LEAF_INDICES - 1);

/// How far below the top of the gigabyte untyped the heap's source's block starts: below the eager
/// source's block and its leaf, and aligned to the block's order, with its leaves under it.
const HEAP_BELOW_TOP: u64 = 2 * (4096 << HEAP_ORDER);

/// The address of the heap's source's window: the start of root entry 4 of dom0's space, past the eager
/// source's, since a window links its own tables above its blocks.
const HEAP_WINDOW: u64 = 4 << 39;

/// The bytes of the run-sized objects dom0 allocates until its heap refuses one: a quarter of a block.
const RUN_OBJECT: usize = aheap::arch::BLOCK_BYTES / 4;

/// More run-sized objects than the heap's source has pages for, so a heap that never refuses fails.
const RUN_OBJECTS_MAX: usize = 4 * HEAP_PAGES * aheap::arch::PAGE_BYTES / RUN_OBJECT;

/// What dom0 prints through the console when its heap allocator check held, which the gate looks for.
const HEAP_HELD: [u64; 5] = operation::print_words(b"dom0 heap allocator held\n");

/// A vector of `bytes` bytes, each its index plus `seed`, or None when the allocator refuses it.
fn filled(bytes: usize, seed: u8) -> Option<Vec<u8>> {
    let mut vector = Vec::new();
    vector.try_reserve_exact(bytes).ok()?;
    vector.extend((0..bytes).map(|i| seed.wrapping_add(i as u8)));
    Some(vector)
}

/// Whether every byte of `vector` is its index plus `seed`.
fn reads_back(vector: &[u8], seed: u8) -> bool {
    vector.iter().enumerate().all(|(i, &byte)| byte == seed.wrapping_add(i as u8))
}

/// How many run-sized objects the global allocator gave before it refused one, chained through their
/// first words and then all freed; None when it gave RUN_OBJECTS_MAX without refusing.
fn run_objects_until_refused() -> Option<usize> {
    let layout = Layout::from_size_align(RUN_OBJECT, 8).ok()?;
    let mut head: *mut u8 = core::ptr::null_mut();
    let mut count = 0;
    let refused = loop {
        if count == RUN_OBJECTS_MAX {
            break false;
        }
        let object = unsafe { alloc::alloc::alloc(layout) };
        if object.is_null() {
            break true;
        }
        unsafe { (object as *mut *mut u8).write(head) };
        head = object;
        count += 1;
    };
    while !head.is_null() {
        let next = unsafe { (head as *mut *mut u8).read() };
        unsafe { alloc::alloc::dealloc(head, layout) };
        head = next;
    }
    refused.then_some(count)
}

/// The eager source over which astd's global allocator serves dom0, set up as heap_allocator_held
/// says, or None when a call was refused.
fn heap_source(caller: &mut Tracked<Caller>, empty: u64) -> Option<aeager::Eager> {
    let (untyped, block) = untyped_of_pages(caller, empty, 1 << 18)?;
    let memory = block.base + (4096 << block.order) - HEAP_BELOW_TOP;
    let source = first_slot(HEAP_ENTRY);
    for leaf in 0..HEAP_LEAVES {
        let base = memory - (leaf + 1) * LEAF_BYTES;
        if retype(caller, untyped, operation::RETYPE_LEAF, base, HEAP_ENTRY + leaf, 0).status != operation::STATUS_OK {
            return None;
        }
    }
    if derive(caller, untyped, source, block.rights, memory, HEAP_ORDER).status != operation::STATUS_OK {
        return None;
    }
    aeager::Eager::new(
        operation::ROOT_PROCESS_SLOT,
        source,
        memory,
        HEAP_PAGES,
        source + 1,
        HEAP_WINDOW as *mut u8,
    )
}

/// Whether astd's global allocator, given a heap over an eager source of dom0's own, serves dom0: from
/// the gigabyte untyped, table leaves into the HEAP_LEAVES root entries from HEAP_ENTRY and a child
/// untyped of HEAP_ORDER at HEAP_BELOW_TOP into the first's first slot, whose pages the source alone
/// retypes, and the window at HEAP_WINDOW. A box of the smallest class, a vector of a few pages and one
/// over a block are written and read back and freed; run-sized objects are then allocated until the
/// allocator refuses one, at least one given first, and all freed, after which one is given again.
fn heap_allocator_held(empty: u64) -> bool {
    let Some(eager) = astd::heap::with_caller(|caller| heap_source(caller, empty)) else {
        return false;
    };
    astd::heap::install(eager);
    let small = Box::new(0x5au8);
    let (Some(run), Some(large)) = (
        filled(2 * aheap::arch::PAGE_BYTES + 8, 0x11),
        filled(aheap::arch::BLOCK_BYTES + aheap::arch::PAGE_BYTES, 0x22),
    ) else {
        return false;
    };
    let objects_held = *small == 0x5a && reads_back(&run, 0x11) && reads_back(&large, 0x22);
    drop((small, run, large));
    objects_held
        && run_objects_until_refused().is_some_and(|count| count > 0)
        && filled(RUN_OBJECT, 0x33).is_some_and(|again| reads_back(&again, 0x33))
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, HEAP_HELD) } == operation::STATUS_OK
}

/// Print through `slot`. The status is the low half of what the invocation returns.
///
/// # Safety
///
/// `operation::invoke` may change the caller's address space. Print does not.
unsafe fn print_slot(slot: u64, arguments: [u64; 5]) -> u64 {
    operation::status(unsafe { operation::invoke(operation::PRINT, slot, arguments) })
}

/// Whether an invocation by an instruction the ABI does not name returns unknown: on aarch64 an `svc`
/// whose immediate is not 0, here asking for a print through the console, which `svc #0` accepts and
/// which would show on the serial log. x86_64's `syscall` has no immediate, so there is nothing to ask.
/// design/syscall-abi-in-registers/, the aarch64 table.
fn other_instruction_unknown() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        true
    }
    #[cfg(target_arch = "aarch64")]
    {
        let words = operation::print_words(b"dom0 svc 1 served\n");
        let status_word: u64;
        unsafe {
            core::arch::asm!(
                "svc #1",
                inout("x8") operation::PRINT => status_word,
                inout("x0") operation::ROOT_CONSOLE_SLOT => _,
                inout("x1") words[0] => _,
                inout("x2") words[1] => _,
                inout("x3") words[2] => _,
                inout("x4") words[3] => _,
                inout("x5") words[4] => _,
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
        operation::status(status_word) == operation::STATUS_UNKNOWN
    }
}

#[no_mangle]
extern "C" fn main(_payload_base: *mut u8, _payload_size: usize) -> isize {
    let process = unsafe { print_slot(operation::ROOT_PROCESS_SLOT, FIRST_ARGUMENTS) };
    let thread = unsafe { print_slot(operation::ROOT_THREAD_SLOT, [0; 5]) };
    let power = unsafe { print_slot(operation::ROOT_POWER_SLOT, [0; 5]) };
    let untyped = unsafe { print_slot(operation::ROOT_UNTYPED_SLOT, [0; 5]) };
    let frame = unsafe { print_slot(operation::ROOT_FRAME_SLOT, [0; 5]) };
    let unknown = operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
    // A power-off through a slot that holds no power capability is refused, the console's among them,
    // and the run goes on. Each reports a failure, so a kernel that took one would not end the run as a
    // success.
    let process_off = operation::power_off(operation::ROOT_PROCESS_SLOT, false);
    let console_off = operation::power_off(operation::ROOT_CONSOLE_SLOT, false);
    // dom0 is not verified, so it mints the caller token its calls start from, which erases here: the
    // kernel's proof that each of its steps keeps its state well formed is what stands behind it. It
    // is the process's one token: astd keeps it for the heap's source and lends it to dom0's calls.
    astd::heap::keep_caller(Tracked::<Caller>::assume_new());
    let slots_held = process == operation::STATUS_REFUSED
        && process_off == operation::STATUS_REFUSED
        && console_off == operation::STATUS_REFUSED
        && thread == operation::STATUS_REFUSED
        && power == operation::STATUS_REFUSED
        && untyped == operation::STATUS_REFUSED
        && frame == operation::STATUS_REFUSED
        && unknown == operation::STATUS_UNKNOWN
        && other_instruction_unknown()
        && astd::heap::with_caller(|caller| {
            first_empty_slot(caller).filter(|&empty| {
                retyped_frame_held(caller, empty)
                    && retyped_table_pages(caller, empty)
                        .is_some_and(|(untyped, tables)| {
                            linked_path_held(caller, untyped, tables)
                                && mapped_frame_held(caller, empty)
                                && remapped_frame_held(caller, empty)
                                && moved_frame_held(caller, empty)
                                && retyped_large_frame_held(caller, empty, empty + 2)
                                && derived_frame_held(caller, empty + 2, empty, empty + 1, empty + 3)
                                && revoked_frame_held(caller, empty + 2, empty, empty + 3)
                                && deleted_frames_held(caller, empty + 2, empty + 3)
                                && derived_power_held(caller, empty + 2)
                                && timed_beside_before(caller, empty + 1)
                                && probed_bits_held(caller, empty + 1)
                                && unmapped_bits_held(caller, empty + 1)
                                && remapped_other_frame_held(caller, untyped, empty + 2)
                                && retyped_leaves_held(caller, untyped, tables[3])
                                && eager_source_held(caller, empty)
                        })
            })
        })
        .is_some_and(heap_allocator_held);
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
            end_run(true)
        }
    }
    end_run(false)
}

/// Ends the run: a power-off through the power capability, reporting whether every check held. The
/// kernel does not return from one it accepts, and how the machine reports each ending is its glue's,
/// design/syscall-abi-in-registers/. When the power-off returns, dom0 waits for the run's timeout.
fn end_run(success: bool) -> ! {
    operation::power_off(operation::ROOT_POWER_SLOT, success);
    loop {}
}

/// dom0's panic handler. It prints nothing, and the run ends reporting a failure.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    end_run(false)
}
