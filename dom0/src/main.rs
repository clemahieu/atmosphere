// SPDX-License-Identifier: MIT

//! The root process of its kernel instance. It treats what boot gave it as all there is and does
//! not assume it owns the machine, so several instances each with a root stay possible. Why, and
//! what to do about a change that breaks this: design/one-kernel-instance/.
//!
//! Print, inspect, retype of a 4K frame, of a 2M frame, of a table page, of a table leaf, of a process and of a thread and its free of a dead frame, derive, move, delete, revoke, link, map, unmap, probe, destroy, read registers, write registers, place, start, suspend and power-off are the wired
//! operations, so each fixed slot is checked through them: the console accepts print and the process,
//! thread, power, untyped and frame slots refuse it, and the process and console slots refuse a
//! power-off; inspect says the console slot holds a console and the power slot a power capability, and
//! each slot from the first untyped holds an untyped whose base is aligned to its order, up to the first
//! slot that holds nothing, which inspect refuses. Inspect says dom0's own thread slot holds a thread that
//! has consumed cycles, and dom0 prints so. Retype under an empty slot, a slot past the table and
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
//! those, reads the page and probes the 64 entries from there, writes it and probes them, and probes them
//! again, printing the mapped entry's accessed and dirty bits each time: accessed without dirty, then
//! dirty, then dirty clear; the other 63 entries, none of them present, have no bit set, and both bits
//! are maintained. A probe of 0 entries, of 65 and of a range leaving its level 1 table is refused. It maps
//! the frame at the next entry, writes the page and unmaps it, and the unmap returns accessed and dirty
//! set, both maintained, which it prints. It retypes another 4K frame, maps it beside that page, writes a
//! word through it, maps it at the unmapped page and reads that word there, not the old frame's. It
//! retypes a third 4K frame, which it never maps; retype's free kind is refused while the capability
//! names the frame, and once the capability is deleted a retype of the page is refused, the free kind
//! frees the dead frame, a second free is refused, and the page is retyped again, which inspect finds
//! and dom0 prints. It retypes a child process from an order-3 block, after a retype at a base not
//! aligned to the block, of a table page's block and into the occupied console slot is refused; inspect
//! finds a process with control in the slot, an inspect through it is refused, its table having no
//! leaf, and a second retype of the block is refused, which dom0 prints. It
//! retypes a table leaf into root entry 2 of its own table, the first boot leaves empty, after a retype into the occupied entry 1, into entry 512, past the root's, by
//! a word naming no position and of a block that is not free is refused, and a second leaf into entry 3
//! through its own process capability, after entry 2 named through it is refused; inspect refuses each
//! leaf's first slot until a derive of the power capability into it, after which inspect finds it there.
//! It retypes 32 threads bound to the child process into the slots of root entry 2 after the first,
//! after a retype bound to the console slot or to an empty slot, neither holding a process, and one at a
//! base not aligned to the block are refused; inspect finds a thread with control in the first slot, a
//! second retype of its block is refused, and dom0 prints the best and the mean cycles of a thread's
//! retype beside new_thread's before numbers.
//! It reads and writes the saved frame of the first of those threads, before anything starts it: a read or a
//! write at an index not a multiple of four or past the frame, a write of a program counter above every
//! user address, and a read or a write through a copy of the thread's capability without control are
//! refused, and the frame reads back as it was; a write of an entry and a stack into the program
//! counter's and the stack pointer's words, each keeping the rest of its window, is accepted, they read
//! back, a read of the frame's last window gives zero past its end, and dom0 prints that they held.
//! It places the first of those threads on core 0 through its core capability at its own priority, 0,
//! after a place of the console slot, one whose core argument is the console slot and one at priority
//! 256 are refused, and after a copy of the core capability derived with maximum 0 refuses the thread
//! at priority 1 and is deleted; a second place of the thread is refused, and dom0 prints that it held.
//! It links a path of three tables into its child's space, maps a frame it retypes into both spaces, maps
//! the page of its own image that holds the child's code into the child's, which it finds by comparing
//! each page of its executable frames with it, and gives the fourth thread a capability to itself in a
//! leaf of the child's table. It writes that thread's entry and arguments, places it on core 0 above
//! itself, at priority 1, and starts it: core 0 takes a reschedule IPI and runs the thread in the child's
//! space, which writes a word into the shared frame and suspends itself, leaving the core to dom0, which
//! reads the word and prints that it held.
//! It gives the fifth thread a capability to itself in the same leaf, writes its entry and arguments,
//! places it through the root's capability for core 1 and starts it: CPU 1 takes a reschedule IPI and
//! runs the thread in the child's space, which writes a second word into the shared frame and suspends
//! itself, leaving core 1 running nothing; dom0 reads the word on core 0, never having left it, and
//! prints that it held.
//! It gives the seventh thread a capability to itself in the same leaf and places it through the root's
//! capability for core 1 with an entry that inspects that capability over and over, counting each
//! inspect in the shared frame, and suspends itself at a count dom0 gives it. While it does, dom0 inspects
//! its console capability over and over on core 0, until it has seen the thread's count reach that end
//! after seeing it change between two of its own inspects at least three times, and prints both counts.
//! It maps a new frame into the child's space and starts the eighth thread on core 1 the same way; the
//! thread writes the frame's page and spins in the child's space. dom0 unmaps the page and deletes the
//! frame's capability, and the free of the frame returns again until CPU 1, sent the unmap's flush IPI,
//! has acknowledged it; the frame is then freed and retyped, and the kernel's line for CPU 1's
//! acknowledgement comes between the two lines dom0 prints around it. dom0 then lets the thread suspend
//! itself.
//! On a kernel built with its flush_cost feature, dom0 then times what a flush IPI costs a thread of
//! its child walking pages on core 1, by the flush the target makes (flush_cost.rs); any other kernel
//! answers that module's test operation unknown, and dom0 goes on.
//! It gives the first thread an entry in its child's space that counts in the shared frame, and starts it,
//! Runnable behind dom0 at the same priority, after a start of the console slot and of the second
//! thread, not placed, are refused; a second start is refused, the thread being started, and dom0
//! places the third thread without starting it and prints that it held. dom0 then counts too, without
//! entering the kernel, until it has seen the thread's count change three times, each a turn the timer
//! gave the thread at core 0, and prints both counts.
//! It starts the sixth thread on core 1 with an entry that counts in the shared frame for good, never
//! entering the kernel, and stops it from core 0: the first suspend returns again, the stop pending and
//! CPU 1 sent the reschedule IPI, and dom0 suspends again until it returns ok. Once the count holds still
//! dom0 prints how many again returns the stop took, starts the thread again, and prints that it held
//! once the count moves.
//! It retypes a table leaf into root entry 0 of the child's table, through the child's process
//! capability, and derives its power capability into that entry's first slot, which inspect finds there.
//! A destroy of an empty slot, of the console and of the power capability is refused; the destroy of the
//! child is accepted and a second refused, and a destroy of a thread bound to the dead child, a start of
//! the placed third thread, bound to it too, and a derive into its table are refused. A move from the dead child's first slot into an empty slot of
//! dom0's own claims the capability: inspect finds it there and refuses the child's slot, and dom0 prints
//! that it held.
//! On x86_64, it retypes a thread bound to its own process from the gigabyte untyped into the second
//! empty root entry's leaf, places it on core 1 and starts it at dom0_child_entry to write a word into
//! a static in dom0's .bss (mapped no-execute) and suspend itself, reads the word change, waits for
//! suspend, and prints that it held.
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
//! With `abench`, it registers calibration, syscall, MMU (`mmu_bench`), memory pointer-chase,
//! core-scaling/placement (`core_bench`), scaled/contended capability (`cap_bench`), heap
//! allocator / working-set churn (`heap_bench`), shared-frame ring/mailbox (`ring_bench`), and
//! cold-cache/pipelined/fan-in/bulk ring (`ump_bench`) microbenchmarks
//! (`design/synthetic-benchmark-suite/`) and runs them in unit-test mode, or under the `bench`
//! feature prints the full results summary and `fuchsiaperf.json` block; `core_bench` and
//! `ump_bench` bind dom0-process bench threads before the heap claims the caller token, probing the
//! online core count with CAS helpers.
//! dom0 prints those results through the console, then an exit marker,
//! and ends the run with a power-off through its power capability, reporting success only when every
//! check held. On aarch64, where the instruction carries an immediate, a print through the console by
//! `svc #1` returns unknown and prints nothing.
//!
//! dom0 invokes retype, derive, inspect, move, delete, revoke, destroy, read registers, write registers,
//! place, start, suspend and link, and map and unmap in a child's space, through acall's wrappers,
//! whose ensures are the kernel's proven contracts, so the code those proofs speak of is the code that
//! boots. dom0 is not verified: the caller token it threads through them erases in its build, and
//! nothing here checks the wrappers' requires. It maps and unmaps in its own space through asys's raw
//! calls: acall maps there only against a page token, and a token dom0 made for itself would vouch for
//! nothing (design/boundary-into-verified-code-counted/).

#![no_std]
#![no_main]

mod cap_bench;
mod context;
mod core_bench;
mod flush_cost;
mod heap_bench;
mod mmu_bench;
mod registers;
mod ring_bench;
mod ump_bench;

extern crate alloc;

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::panic::PanicInfo;

use acall::capability::{delete, destroy, move_cap, place, read_registers, revoke, start, suspend, write_registers};
use acall::memory::{derive, link, map, retype, unmap};
use acall::step::Caller;
use astd::memory::{USERSPACE_BASE, USERSPACE_PAYLOAD_BASE};
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
            consumed: out.result_5,
        }),
        refused => Err(refused),
    }
}

/// Whether the capability at position `slot` names a space other than dom0's own, as acall's map and
/// unmap require of the slot whose space they write (slot_names_other_space): inspect finds one there
/// whose base is not the base of dom0's own process, whose capability boot leaves at ROOT_PROCESS_SLOT.
/// A capability that writes a space names it by the base of the process that owns it.
fn names_other_space(caller: &mut Tracked<Caller>, slot: u64) -> bool {
    matches!(
        (inspect(caller, slot), inspect(caller, operation::ROOT_PROCESS_SLOT)),
        (Ok(held), Ok(own)) if held.base != own.base
    )
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

/// What dom0 prints once inspect on its own thread, at root slot 2, reported consumed cycles, which the
/// gate looks for. design/cpu-time-as-capability/.
const OWN_CONSUMED_HELD: [u64; 5] = operation::print_words(b"dom0 own thread consumed cycles\n");

/// Whether inspect on dom0's own thread capability says it holds a thread that has consumed cycles. Every
/// kernel entry charges the thread its core ran, and dom0's thread has entered the kernel by now, so result
/// 5 is nonzero once it reaches dom0: on x86_64 in r9, design/syscall-abi-in-registers/.
fn own_consumed_held(caller: &mut Tracked<Caller>) -> bool {
    matches!(inspect(caller, operation::ROOT_THREAD_SLOT),
             Ok(held) if held.kind == operation::KIND_THREAD && held.consumed != 0)
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, OWN_CONSUMED_HELD) } == operation::STATUS_OK
}

/// The largest order a capability's block has: 2^36 pages reach the end of the 48-bit space.
pub(crate) const MAX_ORDER: u64 = 36;

/// The last slot of the table's first leaf, where boot's untyped end.
pub(crate) const FIRST_LEAF_END: u64 = operation::ROOT_FRAME_SLOT - 2;

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
pub(crate) const TABLE_PAGE_BYTES: u64 = 8 * 4096;

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
fn mapped_frame_held(frame: u64) -> bool {
    let map_at = |address: u64| operation::map(operation::ROOT_PROCESS_SLOT, address, 1, frame, 0);
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
fn moved_frame_held(caller: &mut Tracked<Caller>, frame: u64) -> bool {
    let moved = frame + 1;
    let base = match inspect(caller, frame) {
        Ok(capability) => capability.base,
        Err(_) => return false,
    };
    let map_from = |slot: u64| operation::map(operation::ROOT_PROCESS_SLOT, PATH_ADDRESS, 1, slot, 0);
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
        && map_from(frame) == operation::STATUS_REFUSED
        && map_from(moved) == operation::STATUS_OK;
    // The map just made the page at PATH_ADDRESS the moved frame's, which kept the word.
    held && unsafe { (PATH_ADDRESS as *const u64).read_volatile() == MAPPED_WORD }
}

/// The pages of a 2M frame's block, order 9.
pub(crate) const LARGE_FRAME_PAGES: u64 = 512;

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

/// Whether dom0 checks that an unassigned operation number returns unknown and times one 4K map of
/// `frame` into each of TIMED_MAPS free entries of the level 1 table, printing its cycle count
/// beside its before number and performance counter deltas where present. The counts are not
/// checked against those numbers. The timed maps start at the page after PATH_ADDRESS, which
/// already holds `frame`. The unassigned invocation itself is timed by `benchmarks_held`.
fn timed_beside_before(frame: u64) -> bool {
    let unknown = operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
    if unknown != operation::STATUS_UNKNOWN {
        return false;
    }
    let maps_before = counters();
    let start = rdtsc();
    for k in 1..=TIMED_MAPS {
        let address = PATH_ADDRESS + 4096 * k;
        if operation::map(operation::ROOT_PROCESS_SLOT, address, 1, frame, 0) != operation::STATUS_OK {
            return false;
        }
    }
    let maps_cycles = rdtsc() - start;
    let maps_after = counters();
    print_count(b"4k ", maps_cycles / TIMED_MAPS, MAP_TAIL) == operation::STATUS_OK
        && print_count(b"4k tsc ", maps_cycles, MAPS_COUNTER_TAIL) == operation::STATUS_OK
        && print_counters(b"4k ", maps_before, maps_after, MAPS_COUNTER_TAIL)
}

/// Chunked console writer flushing 39-byte slices over `ROOT_CONSOLE_SLOT`.
struct ConsoleWriter {
    buf: [u8; 39],
    len: usize,
}

impl ConsoleWriter {
    const fn new() -> Self {
        Self {
            buf: [0; 39],
            len: 0,
        }
    }

    fn flush(&mut self) -> core::fmt::Result {
        if self.len == 0 {
            return Ok(());
        }
        let status = unsafe {
            print_slot(
                operation::ROOT_CONSOLE_SLOT,
                operation::print_words(&self.buf[..self.len]),
            )
        };
        self.len = 0;
        if status == operation::STATUS_OK {
            Ok(())
        } else {
            Err(core::fmt::Error)
        }
    }
}

impl core::fmt::Write for ConsoleWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for &raw in s.as_bytes() {
            // `operation::print_words` forbids NUL bytes inside a message.
            let byte = if raw == 0 { b'?' } else { raw };
            self.buf[self.len] = byte;
            self.len += 1;
            if byte == b'\n' || self.len == self.buf.len() {
                self.flush()?;
            }
        }
        Ok(())
    }
}

/// Runs the user-space benchmark suite in unit-test check mode or `--features bench` perf mode.
fn benchmarks_held() -> bool {
    let mut registry = abench::runner::Registry::new();
    if abench::runner::register_calibration_benchmarks(&mut registry).is_err() {
        return false;
    }
    if registry
        .register_simple("Syscall/Null", || {
            let status =
                operation::status(unsafe { operation::invoke(NO_OPERATION, 0, [0; 5]) });
            core::hint::black_box(status) == operation::STATUS_UNKNOWN
        })
        .is_err()
    {
        return false;
    }
    if !mmu_bench::register(&mut registry) {
        return false;
    }
    if core_bench::register(&mut registry).is_err() {
        return false;
    }
    if !cap_bench::register(&mut registry) {
        return false;
    }
    if !heap_bench::register(&mut registry) {
        return false;
    }
    if !ring_bench::register(&mut registry) {
        return false;
    }
    if !ump_bench::register(&mut registry) {
        return false;
    }
    let mut console = ConsoleWriter::new();
    #[cfg(not(feature = "bench"))]
    let ok = registry
        .run_unit_test(&mut console, None)
        .is_ok_and(|report| {
            report.total > 0 && report.failed == 0 && report.passed == report.total
        });
    #[cfg(feature = "bench")]
    let ok = {
        let config = abench::runner::PerfConfig::default();
        assert_eq!(
            u64::from(config.warmup_iterations + config.batches * config.iterations_per_batch),
            core_bench::POOL,
            "a place case has a thread for each iteration",
        );
        let mut hw = abench::counter::HardwareCounters::new(true);
        registry.run_perf_test(&config, &mut hw, &mut console).is_ok()
    };
    console.flush().is_ok() && ok
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
pub(crate) fn print_parts(parts: &[&[u8]]) -> u64 {
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
/// at PROBED_ENTRY from `frame`, as probe reads and clears them: after a read accessed is set and dirty
/// clear, after a write dirty is set, and after a probe with no write between dirty is clear. A probe of 0
/// entries, of 65 and of a range that leaves the level 1 table is refused.
///
/// It expects of accessed only what an access the program performs guarantees. A present entry may have
/// its accessed bit set by a speculative access no instruction asked for (Arm ARM D8.5.1.2, rules RLHQRX
/// and ILLCCB; AMD APM volume 2, 5.4.2), so accessed is not expected clear at any step; on the Orange Pi
/// the probed entry took one between the map and the first probe. An access performed through the entry
/// sets it (Arm ARM D8.5.1.2, IGXGPN; AMD APM volume 2, 5.4.2: no entry is cached in a TLB with accessed
/// clear), and only probe clears it, so the read's step comes before any probe of the page: a probe
/// between the map and the read could clear a bit a speculative access set while the TLB kept the
/// translation, and the read would then hit the TLB and set nothing. Dirty is set by a write performed
/// through the entry and by no speculative one (Arm ARM D8.5.2.1, RRNMLQ and RDYCFD; AMD APM volume 2,
/// 5.4.2), so the steps expect it exactly. A write sets dirty even through a translation cached with
/// dirty clear, since the processor walks to set it, so that step does not depend on the TLB.
fn probed_bits_held(frame: u64) -> bool {
    let page = entry_address(PROBED_ENTRY) as *mut u64;
    if operation::map(operation::ROOT_PROCESS_SLOT, page as u64, 1, frame, 0) != operation::STATUS_OK {
        return false;
    }
    // The map just made the page the frame's, writable; the frame holds MAPPED_WORD, which the write puts
    // back.
    let word = unsafe { page.read_volatile() };
    if !probed_step_held(b"read", Some(true), false) {
        return false;
    }
    unsafe { page.write_volatile(word) };
    probed_step_held(b"written", None, true)
        && probed_step_held(b"again", None, false)
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
        || operation::map(operation::ROOT_PROCESS_SLOT, beside as u64, 1, other, 0) != operation::STATUS_OK
    {
        return false;
    }
    // The map just made the page beside the new frame's, writable, and nothing else names it.
    unsafe { beside.write_volatile(OTHER_WORD) };
    if operation::map(operation::ROOT_PROCESS_SLOT, page as u64, 1, other, 0) != operation::STATUS_OK {
        return false;
    }
    // The map just made the page the new frame's, which holds OTHER_WORD.
    unsafe { page.read_volatile() == OTHER_WORD }
}

/// How far below the top of the table check's untyped the page dom0 frees and retypes again is: between
/// the leaf check's pages and OTHER_FRAME_BELOW_TOP's, where nothing else retypes.
const FREED_FRAME_BELOW_TOP: u64 = 6 * 8 * 4096;

/// What dom0 prints through the console once it retyped a freed frame's page, which the gate looks for.
const FREED_HELD: [u64; 5] = operation::print_words(b"dom0 freed frame retyped\n");

/// The entry of the level 1 table at PATH_ADDRESS where the free check maps its frame, the one after the
/// remap check's two.
const FREED_ENTRY: u64 = UNMAPPED_ENTRY + 2;

/// How many again returns the free check allows its free. A free returns again while a core that has
/// loaded a space has not acknowledged the unmap's flush, and each such core acknowledges on its next
/// entry to the kernel, which the unmap's IPI forces. On this boot dom0's core alone has loaded a space
/// and it acknowledged on the unmap's own entry, so none is expected; a free still returning again
/// after this many is waiting for a core that will not acknowledge, and fails.
const FREED_AGAIN_MAX: u64 = 64;

/// Whether a frame that was mapped can be freed and its page retyped: dom0 retypes a page of `untyped`,
/// the table check's, FREED_FRAME_BELOW_TOP below its top, into the empty slot `slot`, maps it at
/// FREED_ENTRY, writes MAPPED_WORD through it and unmaps it, so the page's last unmap raised the flush
/// epoch. Retype's free kind is refused while the capability names the frame. dom0 deletes the
/// capability, the frame's last, after which a retype of the page is refused, since a dead page is not
/// free; the free kind then frees it within FREED_AGAIN_MAX again returns, and a second free is
/// refused, the page being free and no longer dead. The retype of the page into `slot` is then accepted,
/// inspect finds the frame there, and the page mapped at FREED_ENTRY again reads zero. The free waits
/// only for cores that have loaded a space: design/flush-without-waiting/. dom0 prints that it held.
fn freed_frame_retyped(caller: &mut Tracked<Caller>, untyped: u64, slot: u64) -> bool {
    let base = match inspect(caller, untyped) {
        Ok(block) => block.base + (4096 << block.order) - FREED_FRAME_BELOW_TOP,
        Err(_) => return false,
    };
    let page = entry_address(FREED_ENTRY) as *mut u64;
    let retype_frame = |caller: &mut Tracked<Caller>| {
        retype(caller, untyped, operation::RETYPE_FRAME, base, slot, 0).status
    };
    let free = |caller: &mut Tracked<Caller>| retype(caller, untyped, operation::RETYPE_FREE, base, 0, 0).status;
    let map_page = || operation::map(operation::ROOT_PROCESS_SLOT, page as u64, 1, slot, 0);
    if retype_frame(caller) != operation::STATUS_OK || map_page() != operation::STATUS_OK {
        return false;
    }
    // The map just made the page the frame's, writable, and nothing else names it.
    unsafe { page.write_volatile(MAPPED_WORD) };
    // dom0 uses nothing at the page between this unmap and the map below.
    if unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, page as u64, 1) }.is_err()
        || free(caller) != operation::STATUS_REFUSED
        || delete(caller, slot).status != operation::STATUS_OK
        || retype_frame(caller) != operation::STATUS_REFUSED
    {
        return false;
    }
    let mut again = 0;
    let freed = loop {
        let status = free(caller);
        if status != operation::STATUS_AGAIN || again == FREED_AGAIN_MAX {
            break status;
        }
        again += 1;
    };
    freed == operation::STATUS_OK
        && free(caller) == operation::STATUS_REFUSED
        && retype_frame(caller) == operation::STATUS_OK
        && matches!(
            inspect(caller, slot),
            Ok(frame) if frame.kind == operation::KIND_FRAME && frame.base == base && frame.order == 0
        )
        && map_page() == operation::STATUS_OK
        // The map just made the page the frame's, which the retype zeroed.
        && unsafe { page.read_volatile() } == 0
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, FREED_HELD) } == operation::STATUS_OK
}

/// How far below the top of the table check's untyped the block dom0 retypes as a child process is: the
/// order-3 block below OTHER_FRAME_BELOW_TOP's, where nothing else retypes.
const PROCESS_BELOW_TOP: u64 = 8 * 8 * 4096;

/// The order of a process's block.
pub(crate) const PROCESS_ORDER: u64 = 3;

/// The control right, the one right a process capability carries.
const RIGHT_CONTROL: u64 = 128;

/// What dom0 prints through the console once it retyped a child process and inspected it, which the
/// gate looks for.
const PROCESS_HELD: [u64; 5] = operation::print_words(b"dom0 process retyped\n");

/// Whether dom0 retypes a child process from `untyped`, the table check's, of the order-3 block
/// PROCESS_BELOW_TOP below its top, into the empty slot `slot`: a retype at a base inside the block but
/// not aligned to it, of the table page's block at `table`, which is not free, and into the occupied
/// console slot is refused; the retype is accepted, inspect finds a process with control at that base in
/// `slot`, an inspect through it is refused, since the child's table has no leaf yet, and a second retype
/// of the block, no longer free, is refused. dom0 prints that it held.
fn retyped_process_held(caller: &mut Tracked<Caller>, untyped: u64, table: u64, slot: u64) -> bool {
    let base = match inspect(caller, untyped) {
        Ok(block) => block.base + (4096 << block.order) - PROCESS_BELOW_TOP,
        Err(_) => return false,
    };
    let retype_process = |caller: &mut Tracked<Caller>, base: u64, slot: u64| {
        retype(caller, untyped, operation::RETYPE_PROCESS, base, slot, 0).status
    };
    retype_process(caller, base + 4096, slot) == operation::STATUS_REFUSED
        && retype_process(caller, table, slot) == operation::STATUS_REFUSED
        && retype_process(caller, base, operation::ROOT_CONSOLE_SLOT) == operation::STATUS_REFUSED
        && retype_process(caller, base, slot) == operation::STATUS_OK
        && matches!(
            inspect(caller, slot),
            Ok(process) if process.kind == operation::KIND_PROCESS
                && process.base == base
                && process.order == PROCESS_ORDER
                && process.rights == RIGHT_CONTROL
        )
        && inspect(caller, operation::through(slot, 1)) == Err(operation::STATUS_REFUSED)
        && retype_process(caller, base, slot + 1) == operation::STATUS_REFUSED
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, PROCESS_HELD) } == operation::STATUS_OK
}

/// How far below the top of the gigabyte untyped the thread check's blocks start: the 32 order-1 blocks
/// from there end at PROCESS_BELOW_TOP, below every page the checks before it may take from that top and
/// above the eager source's leaf and block, where nothing else retypes.
const THREADS_BELOW_TOP: u64 = PROCESS_BELOW_TOP + TIMED_THREADS * THREAD_BYTES;

/// The bytes of a thread's block, order 1.
pub(crate) const THREAD_BYTES: u64 = 2 * 4096;

/// The order of a thread's block.
const THREAD_ORDER: u64 = 1;

/// How many threads dom0 retypes into its child and times, as many as the before number's run made.
const TIMED_THREADS: u64 = 32;

/// The before numbers for a thread's creation, logs/cutover-before.log: new_thread took 57405 TSC cycles
/// at best and 59384 on average over 32 threads.
const THREAD_BEST_TAIL: &[u8] = b" before 57405\n";
const THREAD_MEAN_TAIL: &[u8] = b" before 59384\n";

/// What dom0 prints once the thread check held, which the gate looks for.
const THREADS_HELD: [u64; 5] = operation::print_words(b"dom0 threads retyped\n");

/// Whether dom0 retypes TIMED_THREADS threads under the gigabyte untyped, the last from `empty` down,
/// into the child process whose capability is in `process`, from the order-1 blocks from
/// THREADS_BELOW_TOP below the untyped's top, into the slots of
/// root entry FIRST_EMPTY_ENTRY after the first, which the leaf check filled: a retype bound to the
/// console slot or to an empty slot, neither holding a process, and one at a base not aligned to the
/// block, are refused; each of the threads is accepted, timed, and inspect finds the first a thread with
/// control at its block; and a second retype of the first block is refused. dom0 prints the best and the
/// mean cycles of a retype beside the before numbers.
fn retyped_threads_held(caller: &mut Tracked<Caller>, empty: u64, process: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let base = block.base + (4096 << block.order) - THREADS_BELOW_TOP;
    let first = first_slot(FIRST_EMPTY_ENTRY) + 1;
    let retype_thread = |caller: &mut Tracked<Caller>, base: u64, slot: u64, process: u64| {
        retype(caller, untyped, operation::RETYPE_THREAD, base, slot, process).status
    };
    if retype_thread(caller, base, first, operation::ROOT_CONSOLE_SLOT) != operation::STATUS_REFUSED
        || retype_thread(caller, base, first, first + 1) != operation::STATUS_REFUSED
        || retype_thread(caller, base + 4096, first, process) != operation::STATUS_REFUSED
    {
        return false;
    }
    let mut best = u64::MAX;
    let mut total = 0;
    for k in 0..TIMED_THREADS {
        let start = rdtsc();
        let status = retype_thread(caller, base + k * THREAD_BYTES, first + k, process);
        let cycles = rdtsc().wrapping_sub(start);
        if status != operation::STATUS_OK {
            return false;
        }
        best = best.min(cycles);
        total += cycles;
    }
    matches!(
        inspect(caller, first),
        Ok(thread) if thread.kind == operation::KIND_THREAD
            && thread.base == base
            && thread.order == THREAD_ORDER
            && thread.rights == RIGHT_CONTROL
    ) && retype_thread(caller, base, first + TIMED_THREADS, process) == operation::STATUS_REFUSED
        && print_count(b"thread best ", best, THREAD_BEST_TAIL) == operation::STATUS_OK
        && print_count(b"thread mean ", total / TIMED_THREADS, THREAD_MEAN_TAIL) == operation::STATUS_OK
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, THREADS_HELD) } == operation::STATUS_OK
}

/// What dom0 prints once the register check held, which the gate looks for.
const REGISTERS_HELD: [u64; 5] = operation::print_words(b"dom0 thread registers set\n");

/// The program counter and the stack pointer dom0 writes into its child's first thread: user addresses,
/// which the thread never runs at, since nothing starts it.
const THREAD_ENTRY: u64 = 0x40_1000;
const THREAD_STACK: u64 = 0x80_0000;

/// A program counter above every user address, on each target.
const KERNEL_ENTRY: u64 = 0xffff_8000_0000_1000;

/// The four words of `thread`'s saved frame from word `index`, or the status the read returned.
fn read_window(caller: &mut Tracked<Caller>, thread: u64, index: u64) -> Result<[u64; 4], u64> {
    let out = read_registers(caller, thread, index);
    if out.status == operation::STATUS_OK {
        Ok([out.result_1, out.result_2, out.result_3, out.result_4])
    } else {
        Err(out.status)
    }
}

/// Word `word` of `thread`'s saved frame, read in its window.
fn frame_word(caller: &mut Tracked<Caller>, thread: u64, word: u64) -> Option<u64> {
    read_window(caller, thread, word & !3).ok().map(|words| words[(word & 3) as usize])
}

/// Writes `value` into word `word` of `thread`'s saved frame, keeping the rest of its window: the status
/// of the write, or of the read before it when that was refused.
fn set_frame_word(caller: &mut Tracked<Caller>, thread: u64, word: u64, value: u64) -> u64 {
    match read_window(caller, thread, word & !3) {
        Ok(mut words) => {
            words[(word & 3) as usize] = value;
            write_registers(caller, thread, word & !3, words).status
        }
        Err(status) => status,
    }
}

/// Whether dom0 reads and writes the saved frame of the first thread the thread check bound to its child,
/// in the first slot after root entry FIRST_EMPTY_ENTRY's first, with the empty slot `spare` for a copy of
/// its capability: a read or a write at index 1 or at the first multiple of four past the frame is refused,
/// a write of the program counter's window with KERNEL_ENTRY in its word is refused and the window reads
/// back as it was, and a read or a write through a copy without control, derived into `spare`, is
/// refused, the copy then deleted; the writes of THREAD_ENTRY into the program counter's word and of
/// THREAD_STACK into the stack pointer's, each keeping the rest of its window, are accepted and read back,
/// and the frame's last window reads zero past the frame's end. dom0 prints that it held.
fn registers_held(caller: &mut Tracked<Caller>, spare: u64) -> bool {
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 1;
    let Ok(held) = inspect(caller, thread) else {
        return false;
    };
    let pc_window = operation::PC_WORD & !3;
    let past = (operation::FRAME_WORDS + 3) & !3;
    let last = (operation::FRAME_WORDS - 1) & !3;
    let Ok(before) = read_window(caller, thread, pc_window) else {
        return false;
    };
    let mut above = before;
    above[(operation::PC_WORD & 3) as usize] = KERNEL_ENTRY;
    read_registers(caller, thread, 1).status == operation::STATUS_REFUSED
        && read_registers(caller, thread, past).status == operation::STATUS_REFUSED
        && write_registers(caller, thread, 1, before).status == operation::STATUS_REFUSED
        && write_registers(caller, thread, past, before).status == operation::STATUS_REFUSED
        && write_registers(caller, thread, pc_window, above).status == operation::STATUS_REFUSED
        && read_window(caller, thread, pc_window) == Ok(before)
        && derive(caller, thread, spare, 0, held.base, held.order).status == operation::STATUS_OK
        && read_registers(caller, spare, pc_window).status == operation::STATUS_REFUSED
        && write_registers(caller, spare, pc_window, before).status == operation::STATUS_REFUSED
        && delete(caller, spare).status == operation::STATUS_OK
        && set_frame_word(caller, thread, operation::PC_WORD, THREAD_ENTRY) == operation::STATUS_OK
        && set_frame_word(caller, thread, operation::SP_WORD, THREAD_STACK) == operation::STATUS_OK
        && frame_word(caller, thread, operation::PC_WORD) == Some(THREAD_ENTRY)
        && frame_word(caller, thread, operation::SP_WORD) == Some(THREAD_STACK)
        && read_window(caller, thread, last)
            .is_ok_and(|words| (0..4).all(|k| last + k < operation::FRAME_WORDS || words[k as usize] == 0))
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, REGISTERS_HELD) } == operation::STATUS_OK
}

/// What dom0 prints once it placed a thread of its child on core 0, which the gate looks for.
const PLACED_HELD: [u64; 5] = operation::print_words(b"dom0 thread placed\n");

/// Whether dom0 places the first thread the thread check retyped on core 0 through ROOT_CORE_SLOT at
/// dom0's own priority, 0, using the empty slot `copy` for a derived core capability and freeing it
/// again. A place of the console slot, which holds no thread, is refused, and so are one whose core
/// argument is the console slot and one at priority 256, above any core capability's maximum. A copy of
/// core 0's capability derived with maximum 0 refuses the thread at priority 1 and is deleted. The place
/// through ROOT_CORE_SLOT is accepted and a second refused, the thread being placed already. dom0
/// prints that it held.
fn placed_thread_held(caller: &mut Tracked<Caller>, copy: u64) -> bool {
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 1;
    let Ok(core) = inspect(caller, operation::ROOT_CORE_SLOT) else {
        return false;
    };
    core.kind == operation::KIND_CORE
        && place(caller, operation::ROOT_CONSOLE_SLOT, operation::ROOT_CORE_SLOT, 0).status == operation::STATUS_REFUSED
        && place(caller, thread, operation::ROOT_CONSOLE_SLOT, 0).status == operation::STATUS_REFUSED
        && place(caller, thread, operation::ROOT_CORE_SLOT, 256).status == operation::STATUS_REFUSED
        && derive(caller, operation::ROOT_CORE_SLOT, copy, core.rights, core.base, 0).status == operation::STATUS_OK
        && place(caller, thread, copy, 1).status == operation::STATUS_REFUSED
        && delete(caller, copy).status == operation::STATUS_OK
        && place(caller, thread, operation::ROOT_CORE_SLOT, 0).status == operation::STATUS_OK
        && place(caller, thread, operation::ROOT_CORE_SLOT, 0).status == operation::STATUS_REFUSED
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, PLACED_HELD) } == operation::STATUS_OK
}

/// What dom0 prints once a thread of its child ran in the child's space and wrote dom0 a word, which the
/// gate looks for.
const SWITCHED_HELD: [u64; 5] = operation::print_words(b"dom0 thread switched\n");

/// The word the child's thread writes into the frame both spaces map.
const SWITCHED_WORD: u64 = 0x7377_6974_6368_6564;

/// Where the child's space maps the page of dom0's image that holds dom0_child_entry, and after it the
/// frame both spaces map: the start of root entry 2 of the child's space, as PATH_ADDRESS is of dom0's.
const CHILD_CODE_ADDRESS: u64 = PATH_ADDRESS;
const CHILD_DATA_ADDRESS: u64 = PATH_ADDRESS + 4096;

/// The entries of the level 1 table at PATH_ADDRESS where dom0 maps the frame it shares with its child,
/// and where it maps each page of its image's executable frames in turn while it looks for
/// dom0_child_entry's: past every entry the checks before it map.
const SHARED_ENTRY: u64 = 256;
const SCAN_ENTRY: u64 = 257;

/// The root entry of the child's table whose leaf holds the child's capability to its own thread: entry
/// 0 is destroyed_process_held's.
const CHILD_OWN_ENTRY: u64 = 1;

/// How far below the top of the gigabyte untyped the switch check's blocks start: the end of the eager
/// source's block. Three table pages, a 4K frame and a table leaf from there end below
/// CHILD_LEAF_BELOW_TOP, where nothing else retypes.
const SWITCH_BELOW_TOP: u64 = EAGER_BELOW_TOP - EAGER_PAGES as u64 * 4096;

/// The execute right, which a frame dom0 runs from carries.
const RIGHT_EXECUTE: u64 = 4;

/// The words of a thread's saved frame that hold its first three argument registers, in the order the
/// table under Thread and process operations in design/syscall-abi-in-registers/ gives: rdi, rsi and
/// rdx on x86_64, x0 to x2 on aarch64.
#[cfg(target_arch = "x86_64")]
pub(crate) const ARGUMENT_WORDS: [u64; 3] = [13, 12, 11];
#[cfg(target_arch = "aarch64")]
pub(crate) const ARGUMENT_WORDS: [u64; 3] = [0, 1, 2];

/// How many times dom0 reads the shared word before it gives up on the child's write. The reschedule
/// IPI that runs the child arrives as dom0 returns from the start, so the first read finds the word.
const SWITCH_READS: u64 = 1 << 24;

// The code the child's threads run, from the page of dom0's image that holds it, mapped into the
// child's space. From dom0_child_entry a thread stores its second argument at its first, then suspends
// its own thread through the slot its third names, which leaves its core running nothing; from
// dom0_child_count it adds one to the word at its first argument, for good, and enters the kernel only
// when the timer takes the core from it; from dom0_child_count_thread_pointer, on aarch64, it does the
// same and after each count stores the TPIDR_EL0 it finds in the word four after its first argument;
// from dom0_child_count_segments, on x86_64, it does the same and after each count stores the FS, DS and
// ES selectors it finds, packed as ES, DS, FS from the high bits, in the word four after its first
// argument, and what FS's base adds to its first argument, read as the word through FS less the word
// itself, in the word five after it; from dom0_child_invoke it inspects the capability at the slot its
// third argument names and adds one to the word at its first after each inspect accepted, until that word
// reaches its second argument or an inspect is refused, then suspends its own thread through that slot;
// from dom0_child_hold it stores its second argument at its first, then its first at its second, waits
// until the word at its second no longer holds its first, and suspends its own thread through the slot
// its third names. All of them fit in 256 bytes, aligned so they stay in one page. The invoking loop keeps
// its arguments in registers the invocation keeps: r12 to r14 on x86_64, x19 to x21 on aarch64.
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".balign 256",
    ".global dom0_child_entry",
    "dom0_child_entry:",
    "mov [rdi], rsi",
    "mov rdi, rdx",
    "mov eax, {suspend}",
    "syscall",
    "2: jmp 2b",
    ".global dom0_child_count",
    "dom0_child_count:",
    "inc qword ptr [rdi]",
    "jmp dom0_child_count",
    ".global dom0_child_count_segments",
    "dom0_child_count_segments:",
    "inc qword ptr [rdi]",
    "mov rax, es",
    "shl rax, 16",
    "mov rcx, ds",
    "or rax, rcx",
    "shl rax, 16",
    "mov rcx, fs",
    "or rax, rcx",
    "mov [rdi + {segments}], rax",
    "mov rax, fs:[rdi]",
    "sub rax, [rdi]",
    "mov [rdi + {fs_read}], rax",
    "jmp dom0_child_count_segments",
    ".global dom0_child_invoke",
    "dom0_child_invoke:",
    "mov r12, rdi",
    "mov r13, rsi",
    "mov r14, rdx",
    "3:",
    "mov rdi, r14",
    "mov eax, {inspect}",
    "syscall",
    "test ax, ax",
    "jnz 4f",
    "inc qword ptr [r12]",
    "cmp qword ptr [r12], r13",
    "jb 3b",
    "4:",
    "mov rdi, r14",
    "mov eax, {suspend}",
    "syscall",
    "5: jmp 5b",
    ".global dom0_child_hold",
    "dom0_child_hold:",
    "mov [rdi], rsi",
    "mov [rsi], rdi",
    "6: cmp [rsi], rdi",
    "je 6b",
    "mov rdi, rdx",
    "mov eax, {suspend}",
    "syscall",
    "7: jmp 7b",
    inspect = const operation::INSPECT,
    suspend = const operation::SUSPEND,
    segments = const CHILD_SEGMENTS_ADDRESS - CHILD_COUNT_ADDRESS,
    fs_read = const CHILD_FS_READ_ADDRESS - CHILD_COUNT_ADDRESS,
);
#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(
    ".balign 256",
    ".global dom0_child_entry",
    "dom0_child_entry:",
    "str x1, [x0]",
    "mov x0, x2",
    "mov x8, #{suspend}",
    "svc #0",
    "2: b 2b",
    ".global dom0_child_count",
    "dom0_child_count:",
    "ldr x3, [x0]",
    "add x3, x3, #1",
    "str x3, [x0]",
    "b dom0_child_count",
    ".global dom0_child_count_thread_pointer",
    "dom0_child_count_thread_pointer:",
    "ldr x3, [x0]",
    "add x3, x3, #1",
    "str x3, [x0]",
    "mrs x4, TPIDR_EL0",
    "str x4, [x0, #{thread_pointer}]",
    "b dom0_child_count_thread_pointer",
    ".global dom0_child_invoke",
    "dom0_child_invoke:",
    "mov x19, x0",
    "mov x20, x1",
    "mov x21, x2",
    "3:",
    "mov x0, x21",
    "mov x8, #{inspect}",
    "svc #0",
    "tst x8, #0xffff",
    "b.ne 4f",
    "ldr x3, [x19]",
    "add x3, x3, #1",
    "str x3, [x19]",
    "cmp x3, x20",
    "b.lo 3b",
    "4:",
    "mov x0, x21",
    "mov x8, #{suspend}",
    "svc #0",
    "5: b 5b",
    ".global dom0_child_hold",
    "dom0_child_hold:",
    "str x1, [x0]",
    "str x0, [x1]",
    "6: ldr x3, [x1]",
    "cmp x3, x0",
    "b.eq 6b",
    "mov x0, x2",
    "mov x8, #{suspend}",
    "svc #0",
    "7: b 7b",
    inspect = const operation::INSPECT,
    suspend = const operation::SUSPEND,
    thread_pointer = const CHILD_THREAD_POINTER_ADDRESS - CHILD_COUNT_ADDRESS,
);

unsafe extern "C" {
    /// The first instruction of the child's code above that writes a word and suspends.
    fn dom0_child_entry();
    /// The first instruction of the child's code above that counts.
    fn dom0_child_count();
    /// The first instruction of the child's code above that counts and stores the TPIDR_EL0 it finds.
    #[cfg(target_arch = "aarch64")]
    fn dom0_child_count_thread_pointer();
    /// The first instruction of the child's code above that counts and stores the data segments it finds.
    #[cfg(target_arch = "x86_64")]
    fn dom0_child_count_segments();
    /// The first instruction of the child's code above that invokes and counts its invocations.
    fn dom0_child_invoke();
    /// The first instruction of the child's code above that writes a page and waits for dom0.
    fn dom0_child_hold();
}

/// Where the child's thread that counts on core 0 keeps its count: the third word of the frame both
/// spaces map, after SWITCHED_WORD and CORE_1_WORD.
const CHILD_COUNT_ADDRESS: u64 = CHILD_DATA_ADDRESS + 16;

/// Where the child's thread that invokes on core 1 counts its invocations: the fifth word of the frame
/// both spaces map, after CORE_1_COUNT_ADDRESS's.
const CHILD_INVOKED_ADDRESS: u64 = CHILD_DATA_ADDRESS + 32;

/// The frame capability in dom0's table from ROOT_FRAME_SLOT, and the page in its block, that holds the
/// page of dom0's image at `page`. dom0 knows its image by address and the capabilities by physical
/// page, so it maps each page of each executable frame at SCAN_ENTRY in turn, compares it with the page,
/// and unmaps it. None when a map or an unmap is refused or no frame matches.
fn image_page(caller: &mut Tracked<Caller>, page: u64) -> Option<(u64, u64)> {
    let scan = entry_address(SCAN_ENTRY);
    let mut slot = operation::ROOT_FRAME_SLOT;
    while let Ok(frame) = inspect(caller, slot) {
        if frame.kind != operation::KIND_FRAME {
            return None;
        }
        if frame.rights & RIGHT_EXECUTE != 0 {
            for k in 0..1u64 << frame.order {
                if operation::map(operation::ROOT_PROCESS_SLOT, scan, 1, slot, k) != operation::STATUS_OK {
                    return None;
                }
                // The map just made the page at `scan` page k of the frame, readable; `page` is a page
                // of dom0's image, mapped since boot.
                let same = unsafe {
                    core::slice::from_raw_parts(scan as *const u8, 4096) == core::slice::from_raw_parts(page as *const u8, 4096)
                };
                // dom0 uses nothing at `scan` after the comparison above.
                if unsafe { operation::unmap(operation::ROOT_PROCESS_SLOT, scan, 1) }.is_err() {
                    return None;
                }
                if same {
                    return Some((slot, k));
                }
            }
        }
        slot += 1;
    }
    None
}

/// Whether a thread of dom0's child runs in the child's space above dom0 and writes dom0 a word. Under
/// the gigabyte untyped, the last from `empty` down, from SWITCH_BELOW_TOP below its top: three table
/// pages link a path at CHILD_CODE_ADDRESS in the space of the child whose capability is in `process`;
/// a 4K frame retyped into the empty slot `shared` is mapped at SHARED_ENTRY in dom0's space and at
/// CHILD_DATA_ADDRESS in the child's; the page of dom0's image holding dom0_child_entry is mapped at
/// CHILD_CODE_ADDRESS; and a table leaf in the child's root entry CHILD_OWN_ENTRY takes a capability with
/// control to the fourth thread the thread check bound to the child. That thread's frame gets the entry,
/// the shared word's address, SWITCHED_WORD and its own slot; dom0 places it on core 0 at priority 1,
/// above dom0's 0, reads the shared word as zero and starts the thread. The start makes the thread
/// Runnable above dom0, so core 0 takes a reschedule IPI and runs it in the child's space; it writes the
/// word and suspends itself, so the core runs dom0 again. dom0 reads the word and prints that it held.
fn switched_thread_held(caller: &mut Tracked<Caller>, empty: u64, process: u64, shared: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let low = block.base + (4096 << block.order) - SWITCH_BELOW_TOP;
    let frame = low + 3 * TABLE_PAGE_BYTES;
    let leaf = frame + LEAF_BYTES;
    let entry = dom0_child_entry as *const () as u64;
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 4;
    let own = first_slot(CHILD_OWN_ENTRY);
    let word = entry_address(SHARED_ENTRY) as *const u64;
    let Some((image, page)) = image_page(caller, entry & !0xfff) else {
        return false;
    };
    let Ok(held) = inspect(caller, thread) else {
        return false;
    };
    if !names_other_space(caller, process) {
        return false;
    }
    let linked = (0..3).all(|k| {
        let table = low + k * TABLE_PAGE_BYTES;
        retype(caller, untyped, operation::RETYPE_TABLE_PAGE, table, 0, 3 - k).status == operation::STATUS_OK
            && link(caller, process, CHILD_CODE_ADDRESS, 4 - k, untyped, table).status == operation::STATUS_OK
    });
    let arguments = [CHILD_DATA_ADDRESS, SWITCHED_WORD, own];
    linked
        && retype(caller, untyped, operation::RETYPE_FRAME, frame, shared, 0).status == operation::STATUS_OK
        && operation::map(operation::ROOT_PROCESS_SLOT, word as u64, 1, shared, 0) == operation::STATUS_OK
        && map(caller, process, CHILD_DATA_ADDRESS, 1, shared, 0).status == operation::STATUS_OK
        && map(caller, process, CHILD_CODE_ADDRESS, 1, image, page).status == operation::STATUS_OK
        && retype(caller, untyped, operation::RETYPE_LEAF, leaf, operation::through(process, CHILD_OWN_ENTRY), 0).status
            == operation::STATUS_OK
        && derive(caller, thread, operation::through(process, own), RIGHT_CONTROL, held.base, held.order).status
            == operation::STATUS_OK
        && set_frame_word(caller, thread, operation::PC_WORD, CHILD_CODE_ADDRESS + (entry & 0xfff)) == operation::STATUS_OK
        && (0..3).all(|k| set_frame_word(caller, thread, ARGUMENT_WORDS[k], arguments[k]) == operation::STATUS_OK)
        && place(caller, thread, operation::ROOT_CORE_SLOT, 1).status == operation::STATUS_OK
        // The map above made the page at `word` the shared frame's, which retype zeroed; the child's
        // thread is the only other writer.
        && unsafe { word.read_volatile() } == 0
        && start(caller, thread).status == operation::STATUS_OK
        && (0..SWITCH_READS).any(|_| unsafe { word.read_volatile() } == SWITCHED_WORD)
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, SWITCHED_HELD) } == operation::STATUS_OK
}

/// What dom0 prints once a thread of its child placed on core 1 ran there and wrote dom0 a word, which
/// the gate looks for.
const CORE_1_HELD: [u64; 5] = operation::print_words(b"dom0 thread ran on core 1\n");

/// The word the child's thread on core 1 writes, into the shared frame's second word.
const CORE_1_WORD: u64 = 0x636f_7265_5f6f_6e65;

/// The core the core 1 check places its thread on, through the root's capability for it.
const SECOND_CORE: u64 = 1;

/// Whether a thread of dom0's child placed on core 1 runs there and writes dom0 a word, which dom0 reads
/// on core 0. It reuses what switched_thread_held set up in the space of the child whose capability is in
/// `process`: the child's code at CHILD_CODE_ADDRESS, the frame both spaces map at CHILD_DATA_ADDRESS in
/// the child's and SHARED_ENTRY in dom0's, and the table leaf in the child's root entry CHILD_OWN_ENTRY,
/// whose second slot takes a capability with control to the fifth thread the thread check bound to the
/// child. That thread's frame gets the entry, the address of the shared frame's second word, CORE_1_WORD
/// and its own slot; dom0 places it through the root's capability for core 1, its slot ROOT_CORE_SLOT +
/// 1, reads the word as zero and starts the thread. Core 1 runs nothing, so the start makes its selection
/// due, and the reschedule IPI reaches CPU 1, which runs the thread in the child's space: it writes the
/// word and suspends itself, so core 1 runs nothing again. dom0 reads the word without entering the
/// kernel, so its core never left it and only core 1 can have run the thread; dom0 prints that it held.
fn core_1_thread_held(caller: &mut Tracked<Caller>, process: u64) -> bool {
    let entry = dom0_child_entry as *const () as u64;
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 5;
    let own = first_slot(CHILD_OWN_ENTRY) + 1;
    let word = (entry_address(SHARED_ENTRY) + 8) as *const u64;
    let Ok(held) = inspect(caller, thread) else {
        return false;
    };
    let arguments = [CHILD_DATA_ADDRESS + 8, CORE_1_WORD, own];
    derive(caller, thread, operation::through(process, own), RIGHT_CONTROL, held.base, held.order).status
        == operation::STATUS_OK
        && set_frame_word(caller, thread, operation::PC_WORD, CHILD_CODE_ADDRESS + (entry & 0xfff)) == operation::STATUS_OK
        && (0..3).all(|k| set_frame_word(caller, thread, ARGUMENT_WORDS[k], arguments[k]) == operation::STATUS_OK)
        && place(caller, thread, operation::ROOT_CORE_SLOT + SECOND_CORE, 1).status == operation::STATUS_OK
        // switched_thread_held mapped the page at `word`'s page, the shared frame's, which retype zeroed;
        // the child's thread on core 1 is the only other writer of this word.
        && unsafe { word.read_volatile() } == 0
        && start(caller, thread).status == operation::STATUS_OK
        && (0..SWITCH_READS).any(|_| unsafe { word.read_volatile() } == CORE_1_WORD)
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, CORE_1_HELD) } == operation::STATUS_OK
}

/// Where the child's thread that counts on core 1 keeps its count: the fourth word of the frame both
/// spaces map, after CHILD_COUNT_ADDRESS.
const CORE_1_COUNT_ADDRESS: u64 = CHILD_COUNT_ADDRESS + 8;

/// The count of the thread core_1_counting_held starts, read through the shared frame's mapping at
/// SHARED_ENTRY in dom0's space, which switched_thread_held made.
fn core_1_count() -> u64 {
    let count = (entry_address(SHARED_ENTRY) + (CORE_1_COUNT_ADDRESS - CHILD_DATA_ADDRESS)) as *const u64;
    // The page at `count` is the shared frame's, which retype zeroed; the thread on core 1 is the only
    // other writer of this word.
    unsafe { count.read_volatile() }
}

/// Whether a thread of dom0's child counts on core 1, for core_1_restarted_held to stop and start again
/// and destroyed_process_held to kill by destroying the child. The sixth thread the thread check bound
/// to the child gets the entry dom0_child_count in the child's space and CORE_1_COUNT_ADDRESS as its
/// first argument; dom0 places it through the root's capability for core 1, reads its count as zero
/// and starts it. Core 1 runs nothing, so the reschedule IPI reaches CPU 1, which runs the thread for
/// good: it never enters the kernel. dom0 reads the count moving on core 0 without entering the kernel.
fn core_1_counting_held(caller: &mut Tracked<Caller>) -> bool {
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 6;
    let count = dom0_child_count as *const () as u64;
    set_frame_word(caller, thread, operation::PC_WORD, CHILD_CODE_ADDRESS + (count & 0xfff)) == operation::STATUS_OK
        && set_frame_word(caller, thread, ARGUMENT_WORDS[0], CORE_1_COUNT_ADDRESS) == operation::STATUS_OK
        && place(caller, thread, operation::ROOT_CORE_SLOT + SECOND_CORE, 0).status == operation::STATUS_OK
        && core_1_count() == 0
        && start(caller, thread).status == operation::STATUS_OK
        && (0..SWITCH_READS).any(|_| core_1_count() != 0)
}

/// What dom0 prints once it started again the thread it stopped on core 1 and saw it count, which the
/// gate looks for after the line saying how many again returns the stop took.
const RESTARTED_HELD: [u64; 5] = operation::print_words(b"dom0 thread restarted on core 1\n");

/// The head of the line that says how many again returns dom0's suspend of the thread on core 1 took.
const CORE_1_STOP_HEAD: &[u8] = b"core 1 stop took ";

/// How many again returns dom0's suspend of the thread on core 1 may take before dom0 gives up on CPU 1
/// taking the reschedule IPI each one sends: far more than the IPI's latency in suspends.
const CORE_1_STOP_AGAIN_MAX: u64 = 1 << 20;

/// Whether dom0 stops the thread core_1_counting_held left counting on core 1, from core 0, and starts it
/// again, as a user-level scheduler stops and restarts a thread it placed, design/cpu-time-as-capability/.
/// The thread is Running on core 1, so the first suspend through dom0's capability to it returns again:
/// the stop is pending, and the entry sends core 1 the reschedule IPI. dom0 suspends again while it
/// returns again, within CORE_1_STOP_AGAIN_MAX, until it returns ok, CPU 1 having taken the thread off
/// at its entry, design/one-lock-bounded-steps/. The count then holds still for STILL_READS reads, and
/// dom0 prints how many again returns the stop took. A start then returns ok, core 1 running nothing, so
/// the reschedule IPI reaches CPU 1 and the thread counts on from where it stopped; once dom0 has seen
/// the count move it prints that it held, and destroyed_process_held finds the thread counting.
fn core_1_restarted_held(caller: &mut Tracked<Caller>) -> bool {
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 6;
    if suspend(caller, thread).status != operation::STATUS_AGAIN {
        return false;
    }
    let mut again = 1;
    let mut status = suspend(caller, thread).status;
    while status == operation::STATUS_AGAIN && again < CORE_1_STOP_AGAIN_MAX {
        again += 1;
        status = suspend(caller, thread).status;
    }
    if status != operation::STATUS_OK {
        return false;
    }
    let stopped = core_1_count();
    (0..STILL_READS).all(|_| core_1_count() == stopped)
        && print_count(CORE_1_STOP_HEAD, again, AGAIN_TAIL) == operation::STATUS_OK
        && start(caller, thread).status == operation::STATUS_OK
        && (0..SWITCH_READS).any(|_| core_1_count() != stopped)
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, RESTARTED_HELD) } == operation::STATUS_OK
}

/// What dom0 prints once the count on core 1 stopped after the destroy, which the gate looks for.
const KILLED_HELD: [u64; 5] = operation::print_words(b"dom0 thread killed on core 1\n");

/// How many reads of the count on core 1 in a row dom0 must find equal before it takes the count as
/// stopped: tens of milliseconds, many slices of core 1's tick.
const STILL_READS: u64 = 1 << 24;

/// How many reads dom0 makes before it gives up on the count on core 1 stopping: seconds.
const KILL_READS: u64 = 1 << 32;

/// Whether the count of the thread core_1_counting_held started on core 1 stops once dom0's destroy of
/// the thread's process returned, and dom0 prints how far it went past the value it read then. The
/// destroy's entry sends core 1 the reschedule IPI, its thread having to leave, and CPU 1's
/// check_current moves the thread off at that entry, so the count stops within the IPI's latency; a
/// thread left for core 1's next tick would count on for up to a slice.
fn core_1_count_stopped() -> bool {
    let destroyed = core_1_count();
    let mut last = destroyed;
    let mut still = 0;
    let mut reads = 0;
    while still < STILL_READS && reads < KILL_READS {
        reads += 1;
        let now = core_1_count();
        if now == last {
            still += 1;
        } else {
            still = 0;
            last = now;
        }
    }
    still == STILL_READS
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, KILLED_HELD) } == operation::STATUS_OK
        && print_count(b"core 1 lag ", last.wrapping_sub(destroyed), b" counts\n") == operation::STATUS_OK
}

/// How many inspects the child's thread on core 1 makes before it suspends itself.
const CORE_1_INVOCATIONS: u64 = 1 << 16;

/// How many inspects dom0 makes on core 0 before it gives up on the thread's reaching its count: far more
/// than the thread makes, the lock handing the two cores turns.
const CORE_0_INVOCATIONS: u64 = 1 << 22;

/// How many times dom0 must see the thread's count change between two of its own inspects.
const INVOKED_TURNS: u64 = 3;

/// The starts and the ends of the lines dom0 prints once it and the thread on core 1 both invoked, which
/// the gate looks for.
const INVOKED_DOM0_HEAD: &[u8] = b"dom0 invoked ";
const INVOKED_DOM0_TAIL: &[u8] = b" times on core 0\n";
const INVOKED_THREAD_HEAD: &[u8] = b"thread invoked ";
const INVOKED_THREAD_TAIL: &[u8] = b" times on core 1\n";

/// Whether a thread of dom0's child on core 1 makes invocations while dom0 makes its own on core 0. It
/// reuses what switched_thread_held set up in the space of the child whose capability is in `process`, as
/// core_1_thread_held does: the leaf in the child's root entry CHILD_OWN_ENTRY takes in its third slot a
/// capability with control to the seventh thread the thread check bound to the child. That thread's frame
/// gets the entry dom0_child_invoke, CHILD_INVOKED_ADDRESS, CORE_1_INVOCATIONS and its own slot; dom0
/// places it through the root's capability for core 1, the fifth thread having left that core running
/// nothing, reads its count as zero and starts it. dom0 then inspects its console capability, each inspect
/// accepted and naming a console, and after each reads the thread's count, until the count reaches
/// CORE_1_INVOCATIONS, at which the thread suspends itself. The thread counts only inspects the kernel
/// accepted, and dom0 must see its count change between two of its own inspects INVOKED_TURNS times, so
/// both cores were invoking at once. dom0 prints its own count and the thread's.
fn invoked_beside_core_1_held(caller: &mut Tracked<Caller>, process: u64) -> bool {
    let entry = dom0_child_entry as *const () as u64;
    let invoke = dom0_child_invoke as *const () as u64;
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 7;
    let own = first_slot(CHILD_OWN_ENTRY) + 2;
    let theirs = (entry_address(SHARED_ENTRY) + (CHILD_INVOKED_ADDRESS - CHILD_DATA_ADDRESS)) as *const u64;
    let Ok(held) = inspect(caller, thread) else {
        return false;
    };
    let arguments = [CHILD_INVOKED_ADDRESS, CORE_1_INVOCATIONS, own];
    let started = invoke & !0xfff == entry & !0xfff
        && derive(caller, thread, operation::through(process, own), RIGHT_CONTROL, held.base, held.order).status
            == operation::STATUS_OK
        && set_frame_word(caller, thread, operation::PC_WORD, CHILD_CODE_ADDRESS + (invoke & 0xfff)) == operation::STATUS_OK
        && (0..3).all(|k| set_frame_word(caller, thread, ARGUMENT_WORDS[k], arguments[k]) == operation::STATUS_OK)
        && place(caller, thread, operation::ROOT_CORE_SLOT + SECOND_CORE, 1).status == operation::STATUS_OK
        // switched_thread_held mapped the shared frame at SHARED_ENTRY, which retype zeroed; this thread
        // is the only other writer of its fifth word.
        && unsafe { theirs.read_volatile() } == 0
        && start(caller, thread).status == operation::STATUS_OK;
    if !started {
        return false;
    }
    let mut ours = 0;
    let mut turns = 0;
    let mut last = 0;
    while last < CORE_1_INVOCATIONS && ours < CORE_0_INVOCATIONS {
        if inspect(caller, operation::ROOT_CONSOLE_SLOT).map(|held| held.kind) != Ok(operation::KIND_CONSOLE) {
            return false;
        }
        ours += 1;
        // As above: the thread on core 1 is the only other writer of this word.
        let now = unsafe { theirs.read_volatile() };
        if now != last {
            turns += 1;
            last = now;
        }
    }
    last == CORE_1_INVOCATIONS
        && turns >= INVOKED_TURNS
        && print_count(INVOKED_DOM0_HEAD, ours, INVOKED_DOM0_TAIL) == operation::STATUS_OK
        && print_count(INVOKED_THREAD_HEAD, last, INVOKED_THREAD_TAIL) == operation::STATUS_OK
}

/// What dom0 prints before it unmaps a page in its child's space that a thread of the child on core 1
/// wrote, and once the page's frame was freed and retyped, between which the gate looks for the kernel's
/// line for CPU 1 acknowledging the unmap's flush.
const CORE_1_UNMAP: [u64; 5] = operation::print_words(b"dom0 unmaps a page core 1 wrote\n");
const CORE_1_FREED: [u64; 5] = operation::print_words(b"dom0 freed the page core 1 wrote\n");

/// Where the child's space maps the frame its thread on core 1 writes and dom0 unmaps: the entry after
/// CHILD_DATA_ADDRESS's, in the same level 1 table.
const CHILD_HELD_ADDRESS: u64 = CHILD_DATA_ADDRESS + 4096;

/// The word of the frame both spaces map through which dom0 and the thread on core 1 hand over: the
/// sixth, after CHILD_INVOKED_ADDRESS's.
const CHILD_HOLD_ADDRESS: u64 = CHILD_INVOKED_ADDRESS + 8;

/// Where the thread started_thread_held starts stores, on aarch64, the TPIDR_EL0 it finds: the seventh
/// word of the frame both spaces map, after CHILD_HOLD_ADDRESS's.
#[cfg(target_arch = "aarch64")]
const CHILD_THREAD_POINTER_ADDRESS: u64 = CHILD_HOLD_ADDRESS + 8;

/// Where the thread started_thread_held starts stores, on x86_64, the FS, DS and ES selectors it finds
/// and what FS's base adds to an address: the seventh and eighth words of the frame both spaces map,
/// after CHILD_HOLD_ADDRESS's.
#[cfg(target_arch = "x86_64")]
const CHILD_SEGMENTS_ADDRESS: u64 = CHILD_HOLD_ADDRESS + 8;
#[cfg(target_arch = "x86_64")]
const CHILD_FS_READ_ADDRESS: u64 = CHILD_SEGMENTS_ADDRESS + 8;

/// How far below the top of the gigabyte untyped the frame the thread on core 1 writes is: the page after
/// the switch check's table leaf, below CHILD_LEAF_BELOW_TOP, where nothing else retypes.
const CORE_1_FRAME_BELOW_TOP: u64 = SWITCH_BELOW_TOP - 3 * TABLE_PAGE_BYTES - 2 * LEAF_BYTES;

/// How many again returns the free of the frame the thread on core 1 wrote may take. It returns again
/// until CPU 1 has acknowledged the unmap's flush, which the flush IPI the unmap's glue sends it makes; a
/// free still returning again after this many is waiting for a core that does not take the IPI, and
/// fails.
const CORE_1_FREE_AGAIN_MAX: u64 = 1 << 16;

/// Whether dom0 unmaps a page of its child's space while a thread of the child that wrote it spins on core
/// 1, and frees the page's frame once CPU 1 acknowledged the unmap's flush. Under the gigabyte untyped, the
/// last from `empty` down, a 4K frame CORE_1_FRAME_BELOW_TOP below its top is retyped into the empty slot
/// `slot` and mapped at CHILD_HELD_ADDRESS in the space of the child whose capability is in `process`,
/// where switched_thread_held linked the path and mapped the child's code. The slot after the one
/// invoked_beside_core_1_held used in the child's leaf at CHILD_OWN_ENTRY takes a capability with control
/// to the eighth thread the thread check bound to the child; its frame gets the entry dom0_child_hold,
/// CHILD_HELD_ADDRESS, CHILD_HOLD_ADDRESS and its own slot, and dom0 places it through the root's
/// capability for core 1 and starts it. Once the thread wrote the page and dom0 reads CHILD_HELD_ADDRESS
/// in the hand-over word, so CPU 1 holds the page's translation and still spins in the child's space, dom0
/// prints CORE_1_UNMAP, unmaps the page through `process` and deletes the frame's capability, its last. The
/// unmap's flush IPI goes to CPU 1, which loaded the child's space and is behind the unmap's epoch; retype's
/// free kind returns again until CPU 1 acknowledged it, within CORE_1_FREE_AGAIN_MAX, and then frees the
/// frame, whose page is retyped into `slot` again. With the thread still spinning, dom0 prints
/// CORE_1_FREED, then clears the hand-over word, so the thread suspends itself and core 1 runs nothing.
/// design/flush-without-waiting/.
fn core_1_unmap_held(caller: &mut Tracked<Caller>, empty: u64, process: u64, slot: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let base = block.base + (4096 << block.order) - CORE_1_FRAME_BELOW_TOP;
    let entry = dom0_child_entry as *const () as u64;
    let hold = dom0_child_hold as *const () as u64;
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 8;
    let own = first_slot(CHILD_OWN_ENTRY) + 3;
    let word = (entry_address(SHARED_ENTRY) + (CHILD_HOLD_ADDRESS - CHILD_DATA_ADDRESS)) as *mut u64;
    let Ok(held) = inspect(caller, thread) else {
        return false;
    };
    if !names_other_space(caller, process) {
        return false;
    }
    let retype_frame = |caller: &mut Tracked<Caller>| retype(caller, untyped, operation::RETYPE_FRAME, base, slot, 0).status;
    let free = |caller: &mut Tracked<Caller>| retype(caller, untyped, operation::RETYPE_FREE, base, 0, 0).status;
    let arguments = [CHILD_HELD_ADDRESS, CHILD_HOLD_ADDRESS, own];
    let running = hold & !0xfff == entry & !0xfff
        && retype_frame(caller) == operation::STATUS_OK
        && map(caller, process, CHILD_HELD_ADDRESS, 1, slot, 0).status == operation::STATUS_OK
        && derive(caller, thread, operation::through(process, own), RIGHT_CONTROL, held.base, held.order).status
            == operation::STATUS_OK
        && set_frame_word(caller, thread, operation::PC_WORD, CHILD_CODE_ADDRESS + (hold & 0xfff)) == operation::STATUS_OK
        && (0..3).all(|k| set_frame_word(caller, thread, ARGUMENT_WORDS[k], arguments[k]) == operation::STATUS_OK)
        && place(caller, thread, operation::ROOT_CORE_SLOT + SECOND_CORE, 1).status == operation::STATUS_OK
        // switched_thread_held mapped the page at `word`'s page, the shared frame's, which retype zeroed;
        // the thread on core 1 is the only other writer of this word.
        && unsafe { word.read_volatile() } == 0
        && start(caller, thread).status == operation::STATUS_OK
        && (0..SWITCH_READS).any(|_| unsafe { word.read_volatile() } == CHILD_HELD_ADDRESS);
    if !running
        || unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, CORE_1_UNMAP) } != operation::STATUS_OK
        || unmap(caller, process, CHILD_HELD_ADDRESS, 1).status != operation::STATUS_OK
        || delete(caller, slot).status != operation::STATUS_OK
    {
        return false;
    }
    let mut again = 0;
    let freed = loop {
        let status = free(caller);
        if status != operation::STATUS_AGAIN || again == CORE_1_FREE_AGAIN_MAX {
            break status;
        }
        again += 1;
    };
    let held = freed == operation::STATUS_OK
        && retype_frame(caller) == operation::STATUS_OK
        && matches!(
            inspect(caller, slot),
            Ok(frame) if frame.kind == operation::KIND_FRAME && frame.base == base && frame.order == 0
        )
        // The thread writes the word only before dom0 read it there, and spins until dom0 changes it.
        && unsafe { word.read_volatile() } == CHILD_HELD_ADDRESS
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, CORE_1_FREED) } == operation::STATUS_OK;
    // The thread on core 1 reads the word until it no longer holds CHILD_HELD_ADDRESS, then suspends.
    unsafe { word.write_volatile(0) };
    held
}

/// What dom0 prints once it started a thread of its child, which the gate looks for.
const STARTED_HELD: [u64; 5] = operation::print_words(b"dom0 thread started\n");

/// Whether dom0 starts the thread the place check placed on core 0 at dom0's own priority, 0, so that
/// thread is Runnable behind dom0, which outranks it in nothing, and the core gets no reschedule IPI.
/// First its frame gets the entry dom0_child_count_segments in the child's space on x86_64,
/// dom0_child_count_thread_pointer on aarch64, where switched_thread_held mapped dom0's code and the
/// shared frame, and CHILD_COUNT_ADDRESS
/// as its first argument, so it counts whenever the timer gives it the core. A start of the console slot, which holds no thread, is refused,
/// and so is one of the second thread the thread check retyped, which is not placed. The start is
/// accepted and a second refused, the thread being Runnable. dom0 then places the third thread on core
/// 0 without starting it, for destroyed_process_held to find its start refused once the child is dead,
/// and prints that it held.
fn started_thread_held(caller: &mut Tracked<Caller>) -> bool {
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 1;
    #[cfg(target_arch = "x86_64")]
    let count = dom0_child_count_segments as *const () as u64;
    #[cfg(target_arch = "aarch64")]
    let count = dom0_child_count_thread_pointer as *const () as u64;
    let entry = dom0_child_entry as *const () as u64;
    count & !0xfff == entry & !0xfff
        && set_frame_word(caller, thread, operation::PC_WORD, CHILD_CODE_ADDRESS + (count & 0xfff)) == operation::STATUS_OK
        && set_frame_word(caller, thread, ARGUMENT_WORDS[0], CHILD_COUNT_ADDRESS) == operation::STATUS_OK
        && start(caller, operation::ROOT_CONSOLE_SLOT).status == operation::STATUS_REFUSED
        && start(caller, thread + 1).status == operation::STATUS_REFUSED
        && start(caller, thread).status == operation::STATUS_OK
        && start(caller, thread).status == operation::STATUS_REFUSED
        && place(caller, thread + 2, operation::ROOT_CORE_SLOT, 0).status == operation::STATUS_OK
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, STARTED_HELD) } == operation::STATUS_OK
}

/// How many times dom0 sees the count of the thread it started change before it prints both counts:
/// each change is a turn the thread had at core 0 between two of dom0's.
const PREEMPT_TURNS: u64 = 3;

/// How far dom0 counts before it gives up on the thread's turns: seconds of counting, many slices.
const PREEMPT_COUNTS: u64 = 1 << 32;

/// The starts and the end of the lines dom0 prints once the thread it started had PREEMPT_TURNS turns
/// at core 0, which the gate looks for.
const PREEMPTED_DOM0_HEAD: &[u8] = b"dom0 counted ";
const PREEMPTED_THREAD_HEAD: &[u8] = b"thread counted ";
const PREEMPTED_TAIL: &[u8] = b" in 3 turns\n";

/// Whether dom0 and the thread started_thread_held started, both at priority 0 on core 0, each count
/// while the timer hands the core between them. dom0 counts without entering the kernel, reading the
/// thread's count at CHILD_COUNT_ADDRESS through the shared frame's mapping at SHARED_ENTRY after each
/// of its own, until it saw that count change PREEMPT_TURNS times: the thread ran only while the timer
/// had taken the core from dom0, and dom0 saw the change only once the timer gave it back. It prints
/// its own count and the thread's.
fn preempted_thread_held() -> bool {
    let theirs = (entry_address(SHARED_ENTRY) + (CHILD_COUNT_ADDRESS - CHILD_DATA_ADDRESS)) as *const u64;
    // switched_thread_held mapped the shared frame at SHARED_ENTRY; the thread is its only other writer.
    let mut last = unsafe { theirs.read_volatile() };
    let mut turns = 0;
    let mut ours = 0;
    while turns < PREEMPT_TURNS && ours < PREEMPT_COUNTS {
        ours += 1;
        let now = unsafe { theirs.read_volatile() };
        if now != last {
            turns += 1;
            last = now;
        }
    }
    turns == PREEMPT_TURNS
        && print_count(PREEMPTED_DOM0_HEAD, ours, PREEMPTED_TAIL) == operation::STATUS_OK
        && print_count(PREEMPTED_THREAD_HEAD, last, PREEMPTED_TAIL) == operation::STATUS_OK
}

/// What dom0 prints once a thread of its child, resumed on core 0 after dom0 wrote TPIDR_EL0, found it
/// 0, which the gate looks for on aarch64.
#[cfg(target_arch = "aarch64")]
const THREAD_POINTER_CLEARED_HELD: [u64; 5] = operation::print_words(b"dom0 tpidr_el0 not passed on\n");

/// What dom0 writes in TPIDR_EL0, for the thread to find if a switch passed it on.
#[cfg(target_arch = "aarch64")]
const THREAD_POINTER_WRITTEN: u64 = 0x7470_6964_725f_656c;

/// What dom0 writes over the thread's word before it waits for the thread to store it again: neither 0
/// nor THREAD_POINTER_WRITTEN.
#[cfg(target_arch = "aarch64")]
const THREAD_POINTER_UNSEEN: u64 = u64::MAX;

/// Whether a process's TPIDR_EL0 ends with its thread's turn at a core, on aarch64. dom0 writes
/// THREAD_POINTER_WRITTEN in it, which the next thread the core resumes must not see
/// (design/thread-pointer-cleared-on-switch/). It then writes THREAD_POINTER_UNSEEN over the word the
/// thread started_thread_held started stores, and counts until the thread stored it again, which it
/// does only while the timer has taken core 0 from dom0; twice, since the thread may store at the
/// start of a turn what it read before dom0's write, but not at the start of the next. The thread is
/// of dom0's child, so each of its turns follows a switch between processes, and it must have found 0.
/// dom0 then writes 0 itself and prints that it held, or what the thread found. x86_64 has no
/// TPIDR_EL0.
fn thread_pointer_cleared_held() -> bool {
    #[cfg(target_arch = "aarch64")]
    {
        let found = (entry_address(SHARED_ENTRY) + (CHILD_THREAD_POINTER_ADDRESS - CHILD_DATA_ADDRESS)) as *mut u64;
        // TPIDR_EL0, Arm ARM D24.2.203: EL0 reads and writes it, and nothing of dom0's reads it.
        unsafe {
            core::arch::asm!("msr TPIDR_EL0, {0}", in(reg) THREAD_POINTER_WRITTEN, options(nomem, nostack, preserves_flags))
        };
        // switched_thread_held mapped the shared frame at SHARED_ENTRY; the thread is its only other writer.
        let stored = (0..2).all(|_| {
            unsafe { found.write_volatile(THREAD_POINTER_UNSEEN) };
            let mut ours = 0;
            while ours < PREEMPT_COUNTS && unsafe { found.read_volatile() } == THREAD_POINTER_UNSEEN {
                ours += 1;
            }
            ours < PREEMPT_COUNTS
        });
        let read = unsafe { found.read_volatile() };
        unsafe { core::arch::asm!("msr TPIDR_EL0, xzr", options(nomem, nostack, preserves_flags)) };
        if stored && read != 0 {
            print_count(b"tpidr_el0 found ", read, b"\n");
        }
        stored
            && read == 0
            && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, THREAD_POINTER_CLEARED_HELD) } == operation::STATUS_OK
    }
    #[cfg(target_arch = "x86_64")]
    {
        true
    }
}

/// What dom0 prints once it entered the kernel by a system call and by a tick with GS loaded with its
/// own data selector, which the gate looks for on x86_64.
#[cfg(target_arch = "x86_64")]
const GS_LOADED_HELD: [u64; 5] = operation::print_words(b"dom0 gs loaded across entries\n");

/// The selector of the ring 3 data segment, `GlobalDescriptorTable::USER_SS` in the kernel: a flat
/// segment of base 0, which ring 3 may load into GS (APM 2 §4.5.3).
#[cfg(target_arch = "x86_64")]
const USER_DATA_SELECTOR: u16 = 0x1b;

/// Whether the kernel keeps its own GS base apart from a process's. dom0 loads GS with its data
/// selector, which sets the GS base to 0, prints through its console, which must succeed, and counts
/// until the thread started_thread_held started has counted again, which it does only while the timer
/// has taken core 0 from dom0: a tick taken from dom0 with GS loaded. dom0 then loads GS's earlier
/// selector again and prints that it held. A kernel that reached its core's block through a GS base a
/// process set would take its stack and its core number from near address 0 of dom0's space and stop.
/// On aarch64 a process cannot reach the register that finds the core's block, so there is nothing to
/// load.
fn gs_loaded_held() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        let theirs = (entry_address(SHARED_ENTRY) + (CHILD_COUNT_ADDRESS - CHILD_DATA_ADDRESS)) as *const u64;
        let earlier: u16;
        unsafe {
            core::arch::asm!("mov {0:x}, gs", out(reg) earlier, options(nomem, nostack, preserves_flags));
            core::arch::asm!("mov gs, {0:x}", in(reg) USER_DATA_SELECTOR, options(nostack, preserves_flags));
        }
        let printed = unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, operation::print_words(b"dom0 gs loaded\n")) };
        // switched_thread_held mapped the shared frame at SHARED_ENTRY; the thread is its only other writer.
        let first = unsafe { theirs.read_volatile() };
        let mut ours = 0;
        while ours < PREEMPT_COUNTS && unsafe { theirs.read_volatile() } == first {
            ours += 1;
        }
        let ticked = unsafe { theirs.read_volatile() } != first;
        unsafe { core::arch::asm!("mov gs, {0:x}", in(reg) earlier, options(nostack, preserves_flags)) };
        printed == operation::STATUS_OK
            && ticked
            && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, GS_LOADED_HELD) } == operation::STATUS_OK
    }
    #[cfg(target_arch = "aarch64")]
    {
        true
    }
}

/// What dom0 prints once a thread of its child, resumed on core 0 after dom0 loaded FS, DS and ES with
/// its data selector, found them null with an FS base of 0, which the gate looks for on x86_64.
#[cfg(target_arch = "x86_64")]
const SEGMENTS_CLEARED_HELD: [u64; 5] = operation::print_words(b"dom0 segments not passed on\n");

/// What dom0 writes over the thread's two words before it waits for the thread to store them again: no
/// three selectors packed in 48 bits are all ones.
#[cfg(target_arch = "x86_64")]
const SEGMENTS_UNSEEN: u64 = u64::MAX;

/// Whether a process's FS, DS and ES end with its thread's turn at a core, on x86_64. dom0 loads all
/// three with its data selector, which the next thread the core resumes must not see
/// (design/gs-base-swapped-at-ring-3/). It then writes SEGMENTS_UNSEEN over the two words the thread
/// started_thread_held started stores, and counts until the thread stored both again, which it does
/// only while the timer has taken core 0 from dom0; twice, since the thread may store at the start of a
/// turn what it read before dom0's load, but not at the start of the next. The thread is of dom0's
/// child, so each of its turns follows a switch between processes, and it must have found null
/// selectors and an FS base of 0. dom0 then loads null selectors itself and prints that it held, or
/// what the thread found. aarch64 has no segment registers, so there is nothing to load.
fn segments_cleared_held() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        let shared = entry_address(SHARED_ENTRY);
        let segments = (shared + (CHILD_SEGMENTS_ADDRESS - CHILD_DATA_ADDRESS)) as *mut u64;
        let fs_read = (shared + (CHILD_FS_READ_ADDRESS - CHILD_DATA_ADDRESS)) as *mut u64;
        unsafe {
            core::arch::asm!(
                "mov ds, {0:x}",
                "mov es, {0:x}",
                "mov fs, {0:x}",
                in(reg) USER_DATA_SELECTOR,
                options(nostack, preserves_flags),
            );
        }
        // switched_thread_held mapped the shared frame at SHARED_ENTRY; the thread is its only other writer.
        let stored = (0..2).all(|_| {
            unsafe {
                segments.write_volatile(SEGMENTS_UNSEEN);
                fs_read.write_volatile(SEGMENTS_UNSEEN);
            }
            let mut ours = 0;
            while ours < PREEMPT_COUNTS
                && (unsafe { segments.read_volatile() } == SEGMENTS_UNSEEN
                    || unsafe { fs_read.read_volatile() } == SEGMENTS_UNSEEN)
            {
                ours += 1;
            }
            ours < PREEMPT_COUNTS
        });
        let (found, read) = unsafe { (segments.read_volatile(), fs_read.read_volatile()) };
        unsafe {
            core::arch::asm!(
                "mov ds, {0:x}",
                "mov es, {0:x}",
                "mov fs, {0:x}",
                in(reg) 0u16,
                options(nostack, preserves_flags),
            );
        }
        if stored && (found != 0 || read != 0) {
            print_count(b"thread found segments ", found, b"\n");
            print_count(b"thread found fs adding ", read, b"\n");
        }
        stored
            && found == 0
            && read == 0
            && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, SEGMENTS_CLEARED_HELD) } == operation::STATUS_OK
    }
    #[cfg(target_arch = "aarch64")]
    {
        true
    }
}

/// What dom0 prints once it suspended the thread it started and started it again, which the gate
/// looks for.
const SUSPENDED_HELD: [u64; 5] = operation::print_words(b"dom0 thread suspended\n");

/// Whether dom0 suspends the thread the start check started, Runnable on core 0 behind dom0, using the
/// empty slot `copy` for a derived thread capability and freeing it again. A suspend of the console
/// slot, which holds no thread, is refused, and so is one through a copy of the thread's capability
/// derived without control. The suspend is accepted, the thread being Runnable, and a second accepted
/// too, the thread being Inactive. A start of the thread is accepted again, so it is Runnable as before,
/// and dom0 prints that it held. dom0 suspends no thread it runs on: a suspend of the caller's own
/// thread leaves its core with nothing to run.
fn suspended_thread_held(caller: &mut Tracked<Caller>, copy: u64) -> bool {
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 1;
    let Ok(held) = inspect(caller, thread) else {
        return false;
    };
    held.kind == operation::KIND_THREAD
        && suspend(caller, operation::ROOT_CONSOLE_SLOT).status == operation::STATUS_REFUSED
        && derive(caller, thread, copy, 0, held.base, held.order).status == operation::STATUS_OK
        && suspend(caller, copy).status == operation::STATUS_REFUSED
        && delete(caller, copy).status == operation::STATUS_OK
        && suspend(caller, thread).status == operation::STATUS_OK
        && suspend(caller, thread).status == operation::STATUS_OK
        && start(caller, thread).status == operation::STATUS_OK
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, SUSPENDED_HELD) } == operation::STATUS_OK
}

/// How far below the top of the gigabyte untyped the child's table leaf starts: the order-1 block below the
/// thread check's, above the eager source's block, where nothing else retypes.
const CHILD_LEAF_BELOW_TOP: u64 = THREADS_BELOW_TOP + LEAF_BYTES;

/// How far below the top of the gigabyte untyped the own-process core 1 thread's order-1 block starts:
/// right below CHILD_LEAF_BELOW_TOP, clear of every other block taken from that top.
#[cfg(target_arch = "x86_64")]
const OWN_THREAD_BELOW_TOP: u64 = CHILD_LEAF_BELOW_TOP + THREAD_BYTES;

/// What dom0 prints once a thread bound to dom0's own process ran on core 1 and wrote a word on a
/// no-execute page of dom0's image, which the gate looks for on x86_64.
#[cfg(target_arch = "x86_64")]
const OWN_CORE_1_NX_HELD: [u64; 5] = operation::print_words(b"dom0 own thread wrote nx page\n");

/// The word in dom0's .bss (mapped no-execute, bit 63) that the own-process thread on core 1 writes.
#[cfg(target_arch = "x86_64")]
static OWN_CORE_1_WORD: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);

/// The non-zero value the own-process thread on core 1 writes into [`OWN_CORE_1_WORD`].
#[cfg(target_arch = "x86_64")]
const OWN_CORE_1_VALUE: u64 = 0x6f77_6e5f_6e78_6f6b;

/// Whether on x86_64 a thread bound to dom0's own process runs on core 1 and writes a word on a
/// no-execute page of dom0's image (.bss) and dom0 sees it change. The thread is retyped from the
/// gigabyte untyped at OWN_THREAD_BELOW_TOP below its top into the second slot of the leaf at
/// FIRST_EMPTY_ENTRY + 1, placed on core 1, and started at dom0_child_entry (which is in .text) with
/// OWN_CORE_1_WORD's address, OWN_CORE_1_VALUE, and its own slot. Without EFER.NXE set on the AP,
/// accessing dom0's no-execute .bss page on core 1 raises a reserved-bit page fault. Once dom0 sees
/// the word change, it suspends until the thread is Inactive so core 1 is idle again, and prints that
/// it held. On aarch64 the x86_64 EFER.NXE path is absent, so aarch64 returns true unchanged.
fn own_core_1_nx_held(caller: &mut Tracked<Caller>, empty: u64) -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        use core::sync::atomic::Ordering;

        let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
            return false;
        };
        let base = block.base + (4096 << block.order) - OWN_THREAD_BELOW_TOP;
        let thread = first_slot(FIRST_EMPTY_ENTRY + 1) + 1;
        let entry = dom0_child_entry as *const () as u64;
        let target = (&raw const OWN_CORE_1_WORD) as u64;
        let arguments = [target, OWN_CORE_1_VALUE, thread];
        if retype(
            caller,
            untyped,
            operation::RETYPE_THREAD,
            base,
            thread,
            operation::ROOT_PROCESS_SLOT,
        )
        .status
            != operation::STATUS_OK
            || set_frame_word(caller, thread, operation::PC_WORD, entry) != operation::STATUS_OK
            || !(0..3).all(|k| {
                set_frame_word(caller, thread, ARGUMENT_WORDS[k], arguments[k]) == operation::STATUS_OK
            })
            || place(caller, thread, operation::ROOT_CORE_SLOT + SECOND_CORE, 1).status
                != operation::STATUS_OK
            || OWN_CORE_1_WORD.load(Ordering::Acquire) != 0
            || start(caller, thread).status != operation::STATUS_OK
        {
            return false;
        }
        if !(0..SWITCH_READS).any(|_| OWN_CORE_1_WORD.load(Ordering::Acquire) == OWN_CORE_1_VALUE) {
            return false;
        }
        // Wait for the thread's own suspend (or force it) so core 1 is idle before continuing.
        let stopped = (0..SWITCH_READS).any(|_| suspend(caller, thread).status == operation::STATUS_OK);
        stopped
            && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, OWN_CORE_1_NX_HELD) }
                == operation::STATUS_OK
    }
    #[cfg(target_arch = "aarch64")]
    {
        let _ = (caller, empty);
        true
    }
}

/// What dom0 prints once it destroyed its child process and claimed a capability from the dead child's
/// table, which the gate looks for.
const DESTROYED_HELD: [u64; 5] = operation::print_words(b"dom0 process destroyed\n");

/// Whether dom0 destroys its child process, whose capability is in `process`, and claims a capability from
/// the dead child's table into the empty slot `claim`, under the gigabyte untyped, the last from `empty`
/// down. A table leaf CHILD_LEAF_BELOW_TOP below the untyped's top goes into root entry 0 of the child's
/// table, through `process`, and inspect finds the power capability derived into that entry's first slot.
/// A destroy of the empty slot `claim`, of the console slot and of the power slot, none holding a process
/// or a thread, is refused; the destroy of `process` is accepted, the count of the thread
/// core_1_counting_held started on core 1 stops, as core_1_count_stopped says, and a second destroy is
/// refused, the child being dead. A destroy of the first thread the thread check bound to the child is
/// refused, its process being dead, and so are a start of the third, placed and Inactive but bound to
/// the dead child, and a derive into the dead child's table. A move from the child's first slot into
/// `claim` is accepted, after which inspect finds power's capability in `claim` and refuses the child's
/// first slot. dom0 prints that it held.
fn destroyed_process_held(caller: &mut Tracked<Caller>, empty: u64, process: u64, claim: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let Ok(power) = inspect(caller, operation::ROOT_POWER_SLOT) else {
        return false;
    };
    let base = block.base + (4096 << block.order) - CHILD_LEAF_BELOW_TOP;
    let held = operation::through(process, first_slot(0));
    let thread = first_slot(FIRST_EMPTY_ENTRY) + 1;
    let derive_power = |caller: &mut Tracked<Caller>, to: u64| {
        derive(caller, operation::ROOT_POWER_SLOT, to, power.rights, power.base, 0).status
    };
    retype(caller, untyped, operation::RETYPE_LEAF, base, operation::through(process, 0), 0).status == operation::STATUS_OK
        && derive_power(caller, held) == operation::STATUS_OK
        && inspect(caller, held) == Ok(power)
        && destroy(caller, claim).status == operation::STATUS_REFUSED
        && destroy(caller, operation::ROOT_CONSOLE_SLOT).status == operation::STATUS_REFUSED
        && destroy(caller, operation::ROOT_POWER_SLOT).status == operation::STATUS_REFUSED
        && destroy(caller, process).status == operation::STATUS_OK
        && core_1_count_stopped()
        && destroy(caller, process).status == operation::STATUS_REFUSED
        && destroy(caller, thread).status == operation::STATUS_REFUSED
        && start(caller, thread + 2).status == operation::STATUS_REFUSED
        && derive_power(caller, operation::through(process, first_slot(0) + 1)) == operation::STATUS_REFUSED
        && move_cap(caller, held, claim).status == operation::STATUS_OK
        && inspect(caller, claim) == Ok(power)
        && inspect(caller, held) == Err(operation::STATUS_REFUSED)
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, DESTROYED_HELD) } == operation::STATUS_OK
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
pub(crate) const RIGHT_READ: u64 = 1;

/// The retype right, which no frame has.
const RIGHT_RETYPE: u64 = 8;

/// The bytes of a 2M frame's block.
pub(crate) const LARGE_FRAME_BYTES: u64 = LARGE_FRAME_PAGES * 4096;

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
    let map_child = |k: u64| operation::map(operation::ROOT_PROCESS_SLOT, address(k), 1, child, 0);
    if !(1..=REVOKED_MAPPINGS).all(|k| map_child(k) == operation::STATUS_OK) {
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
        && map_child(1) == operation::STATUS_REFUSED
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
pub(crate) const ROOT_ENTRIES: u64 = operation::TABLE_INDICES / LEAF_INDICES;

/// The first slot of root entry `entry`, past its leaf's hidden node.
pub(crate) const fn first_slot(entry: u64) -> u64 {
    entry * LEAF_INDICES + 1
}

/// The first root entry boot leaves empty: it fills entry 0 with the fixed slots and the untyped and
/// entry 1 with the image's frames, design/root-process-at-boot/.
const FIRST_EMPTY_ENTRY: u64 = 2;

/// The bytes of a table leaf's block, order 1.
pub(crate) const LEAF_BYTES: u64 = 2 * 4096;

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
/// frame, table page, leaf and thread checks take from that top.
const EAGER_BELOW_TOP: u64 = 256 * 4096;

/// The address of the eager source's window: the start of root entry 3 of dom0's space, past
/// PATH_ADDRESS's, which nothing maps.
pub(crate) const EAGER_WINDOW: u64 = 3 << 39;

/// The bytes a root entry of a space spans, on both targets.
const ROOT_ENTRY_BYTES: u64 = 1 << 39;

unsafe extern "C" {
    /// The end of dom0's image, which the linker places past its last section.
    static _end: u8;
}

/// Whether a source of dom0's may take the window at `window`, whose tables an eager source links into
/// the window's root entry whole: the window starts a root entry, and that entry is none that holds
/// what the loader mapped for dom0 or what dom0 maps itself, nor that of a window in `taken`. The loader
/// maps dom0's image from USERSPACE_BASE to `_end`, its payload from USERSPACE_PAYLOAD_BASE and its
/// stack, which holds this function's frame; dom0 maps and links pages of its own space under
/// PATH_ADDRESS, and its sources under their windows.
pub(crate) fn window_clear(window: u64, taken: &[u64]) -> bool {
    let entry = |address: u64| address / ROOT_ENTRY_BYTES;
    let here = 0u8;
    let image = entry(USERSPACE_BASE)..=entry(&raw const _end as u64 - 1);
    let own = entry(window);
    window % ROOT_ENTRY_BYTES == 0
        && !image.contains(&own)
        && own != entry(USERSPACE_PAYLOAD_BASE)
        && own != entry(&raw const here as u64)
        && own != entry(PATH_ADDRESS)
        && taken.iter().all(|&other| entry(other) != own)
}

/// The start of the line dom0 prints once its eager source is exercised, before how many pages it backed.
const EAGER_HEAD: &[u8] = b"dom0 eager backed ";

/// Whether dom0 runs aeager's verified exercise over an eager source of its own: from the untyped that is
/// a gigabyte, a table leaf into root entry EAGER_ENTRY and a child untyped of EAGER_ORDER below
/// EAGER_BELOW_TOP into its first slot, whose pages the source alone retypes, putting frame capabilities
/// in the slots after it, and the window at EAGER_WINDOW, which window_clear allows. The exercise
/// reserves a span; backs, writes and releases its first page, backs and writes its second, backs and
/// writes its first again and reads the second; backs the span a page at a time until the source refuses,
/// writes a byte through the run and reads it back, releases the run, backs a page again, backs the page
/// it refused and writes and reads a byte there, and gives the span back. dom0 prints how many pages it
/// backed, and the check holds when the second page read its own byte, so no translation of the first
/// outlived its release, the source refused before the block was full, the byte read back, a page was
/// backed again, and the refused page was backed once the run was released, with every page of the
/// untyped then mapped or parked.
fn eager_source_held(caller: &mut Tracked<Caller>, empty: u64) -> bool {
    if !window_clear(EAGER_WINDOW, &[]) {
        return false;
    }
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
    let Some(seen) = aeager::exercise_eager(
        caller,
        operation::ROOT_PROCESS_SLOT,
        source,
        memory,
        EAGER_PAGES,
        source + 1,
        EAGER_WINDOW as *mut u8,
    ) else {
        return false;
    };
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
pub(crate) const HEAP_WINDOW: u64 = 4 << 39;

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
fn heap_source(mut caller: Tracked<Caller>, empty: u64) -> aeager::AllocatorInit {
    if !window_clear(HEAP_WINDOW, &[EAGER_WINDOW]) {
        return aeager::AllocatorInit::Refused(caller);
    }
    let Some((untyped, block)) = untyped_of_pages(&mut caller, empty, 1 << 18) else {
        return aeager::AllocatorInit::Refused(caller);
    };
    let memory = block.base + (4096 << block.order) - HEAP_BELOW_TOP;
    let source = first_slot(HEAP_ENTRY);
    for leaf in 0..HEAP_LEAVES {
        let base = memory - (leaf + 1) * LEAF_BYTES;
        if retype(&mut caller, untyped, operation::RETYPE_LEAF, base, HEAP_ENTRY + leaf, 0).status != operation::STATUS_OK {
            return aeager::AllocatorInit::Refused(caller);
        }
    }
    if derive(&mut caller, untyped, source, block.rights, memory, HEAP_ORDER).status != operation::STATUS_OK {
        return aeager::AllocatorInit::Refused(caller);
    }
    aeager::new_allocator(
        caller,
        astd::heap::SPARES,
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
/// retypes, and the window at HEAP_WINDOW, which window_clear allows beside EAGER_WINDOW. A box of the
/// smallest class, a vector of a few pages and one over a block are written and read back and freed;
/// run-sized objects are then allocated until the allocator refuses one, at least one given first, and
/// all freed, after which one is given again.
fn heap_allocator_held(empty: u64) -> bool {
    if !astd::heap::install_with(|caller| heap_source(caller, empty)) {
        return false;
    }
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
pub(crate) unsafe fn print_slot(slot: u64, arguments: [u64; 5]) -> u64 {
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
    // dom0 is not verified, so it mints the caller token its calls start from, which erases here. It
    // stands for the kernel's state only while the process takes no kernel step outside acall, and
    // dom0's raw maps and unmaps of its own space are such steps, so nothing vouches for it: its line
    // in tools/boundary-list is debt. It is the process's one token: astd keeps it for the heap's
    // source and lends it to dom0's calls.
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
                own_consumed_held(caller)
                    && retyped_frame_held(caller, empty)
                    && retyped_table_pages(caller, empty)
                        .is_some_and(|(untyped, tables)| {
                            linked_path_held(caller, untyped, tables)
                                && mapped_frame_held(empty)
                                && remapped_frame_held(empty)
                                && moved_frame_held(caller, empty)
                                && retyped_large_frame_held(caller, empty, empty + 2)
                                && derived_frame_held(caller, empty + 2, empty, empty + 1, empty + 3)
                                && revoked_frame_held(caller, empty + 2, empty, empty + 3)
                                && deleted_frames_held(caller, empty + 2, empty + 3)
                                && derived_power_held(caller, empty + 2)
                                && timed_beside_before(empty + 1)
                                && probed_bits_held(empty + 1)
                                && unmapped_bits_held(empty + 1)
                                && remapped_other_frame_held(caller, untyped, empty + 2)
                                && freed_frame_retyped(caller, untyped, empty + 3)
                                && retyped_process_held(caller, untyped, tables[0], empty + 4)
                                && retyped_leaves_held(caller, untyped, tables[3])
                                && retyped_threads_held(caller, empty, empty + 4)
                                && registers_held(caller, empty + 5)
                                && placed_thread_held(caller, empty + 5)
                                && switched_thread_held(caller, empty, empty + 4, empty + 6)
                                && core_1_thread_held(caller, empty + 4)
                                && invoked_beside_core_1_held(caller, empty + 4)
                                && core_1_unmap_held(caller, empty, empty + 4, empty + 7)
                                && flush_cost::held(caller, empty, empty + 4, empty + 8)
                                && started_thread_held(caller)
                                && preempted_thread_held()
                                && thread_pointer_cleared_held()
                                && gs_loaded_held()
                                && segments_cleared_held()
                                && registers::syscall_registers_held()
                                && registers::preemption_registers_held(
                                    (entry_address(SHARED_ENTRY) + (CHILD_COUNT_ADDRESS - CHILD_DATA_ADDRESS))
                                        as *const u64,
                                )
                                && context::context_switch_held()
                                && suspended_thread_held(caller, empty + 5)
                                && core_1_counting_held(caller)
                                && core_1_restarted_held(caller)
                                && destroyed_process_held(caller, empty, empty + 4, empty + 5)
                                && own_core_1_nx_held(caller, empty)
                                && eager_source_held(caller, empty)
                                && core_bench::threads_held(caller, empty)
                                && ump_bench::threads_held(caller, empty)
                        })
            })
        })
        .is_some_and(heap_allocator_held)
        && benchmarks_held();
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
