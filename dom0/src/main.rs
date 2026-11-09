//! The root process of its kernel instance. It treats what boot gave it as all there is and does
//! not assume it owns the machine, so several instances each with a root stay possible. Why, and
//! what to do about a change that breaks this: design/one-kernel-instance/.
//!
//! Print, inspect, retype of a 4K frame and of a table page, and link are the wired operations, so each
//! fixed slot is checked through them: the console accepts print and the process, thread, untyped and
//! frame slots refuse it; inspect says the console slot holds a console, and each slot from the first
//! untyped holds an untyped whose base is aligned to its order, up to the first slot that holds
//! nothing, which inspect refuses. Retype under an empty slot, a slot past the table and the console is
//! refused, and retype of the last untyped's last page into that empty slot is accepted, after which
//! inspect says the slot holds a 4K frame at that page. dom0 then retypes four table pages, after a
//! table page of a level no table has is refused, and a retype of one of them again is refused after;
//! it links three of them, of levels 3, 2 and 1, under an address its image does not use, through its
//! own process capability, after a table of the wrong level, an entry whose tables above are not linked
//! and an unaligned address are refused, and the fourth is refused at the entry the third took. dom0
//! prints that result through the console, then an exit marker, and exits with success only when every
//! check held. The kernel logs each invocation, with what it returned, in the serial log.

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

/// The arguments of the first invocation, which the kernel logs: each word names its position, so
/// the log shows every argument register reached the kernel in its place, r10 last.
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
                && retyped_table_pages(empty).is_some_and(|(untyped, tables)| linked_path_held(untyped, tables))
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
