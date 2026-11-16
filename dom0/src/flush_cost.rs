// SPDX-License-Identifier: MIT

//! The target's side of a cross-core flush, for the flush design's numbers, on a kernel built with its
//! flush_cost feature, which answers the test operation [`OPERATION`]; any other kernel answers it
//! unknown, and dom0 then does nothing here. A thread of dom0's child on core 1 walks pages of the
//! child's space in passes, one load a page, each pass timed; between two passes dom0 on core 0 has the
//! kernel send CPU 1 one flush IPI while the thread spins in user mode, timed until CPU 1 acknowledges,
//! and CPU 1 makes the flush dom0 chose. The pass after it, against a pass after none, is what the flush
//! costs the thread in TLB refills. Every page the thread walks maps one frame, so each load hits the
//! cache once the line is in it and the refill is the translations alone. A flush naming another
//! context than the one CPU 1 runs is what a flush of an unrelated space's unmap costs a core running
//! this one. Under KVM a refill walks the guest's tables and the host's for each (a two-dimensional
//! walk), so a refill here costs more than on bare metal.

use core::fmt::Write;
use core::sync::atomic::{fence, Ordering};

use acall::capability::{place, start};
use acall::memory::{derive, link, map, retype, unmap};
use acall::step::Caller;
use asys::operation;
use vstd::prelude::Tracked;

use crate::{
    entry_address, first_slot, image_page, inspect, set_frame_word, untyped_of_pages, ConsoleWriter, ARGUMENT_WORDS,
    CHILD_CODE_ADDRESS, CHILD_DATA_ADDRESS, CHILD_OWN_ENTRY, FIRST_EMPTY_ENTRY, RIGHT_CONTROL, SECOND_CORE,
    SHARED_ENTRY, SWITCH_READS, TABLE_PAGE_BYTES,
};

/// The kernel's test operation that times one flush IPI to CPU 1: kernel/src/flush.rs
/// cost::USER_OPERATION, with its arguments and result.
const OPERATION: u64 = 0xfff0;

/// The flushes the operation chooses from, as kernel/src/flush.rs cost numbers them, and a kind past
/// them, which a kernel with the operation refuses.
const EVERY: u64 = 0;
const CONTEXT: u64 = 1;
const PAGE: u64 = 2;
const NONE: u64 = 3;
const UNKNOWN_KIND: u64 = NONE + 1;

/// What dom0 measures, each with its name in the line it prints: the flush, and whether it names
/// another context than the thread's. A flush of every context leaves nothing of the thread's
/// whichever space it is for.
const CASES: [(u64, bool, &str); 6] = [
    (EVERY, false, "every context"),
    (CONTEXT, false, "the space's context"),
    (CONTEXT, true, "another space's context"),
    (PAGE, false, "one page of the space"),
    (PAGE, true, "one page of another space"),
    (NONE, false, "no flush"),
];

/// The pages a pass walks, a run of each.
const WALKS: [u64; 3] = [64, 1024, 8192];

/// The most pages a pass walks, and the level 1 tables that map them, 512 pages each.
const WALK_PAGES: u64 = 8192;
const WALK_TABLES: u64 = WALK_PAGES / 512;

/// Rounds of each case at each walk, after WARM_PASSES passes that fill the TLB and caches; a round is
/// a pass after no flush and a pass after one.
const ROUNDS: u64 = 100;
const WARM_PASSES: u64 = 8;

/// Where the child's space maps the pages the thread walks: root entry 3, past the path at
/// CHILD_CODE_ADDRESS's entry 2. One table of level 3, one of level 2 and WALK_TABLES + 1 of level 1
/// map it, the last for UNWALKED_ADDRESS.
const WALK_ADDRESS: u64 = 3 << 39;

/// A page of the walked space mapped to the same frame that no pass walks: the page the one-page
/// flush names, in the level 1 table after the walked ones.
const UNWALKED_ADDRESS: u64 = WALK_ADDRESS + WALK_PAGES * 4096;

/// Where the child's space maps the page of dom0's image that holds dom0_child_walk: the entry after
/// CHILD_HELD_ADDRESS's, in the level 1 table at CHILD_CODE_ADDRESS.
const WALK_CODE_ADDRESS: u64 = CHILD_CODE_ADDRESS + 3 * 4096;

/// How far below the top of the gigabyte untyped the tables and the frame are: half of it, below every
/// block the other checks take from that top.
const WALK_BELOW_TOP: u64 = 1 << 29;

/// The thread that walks, the 21st the thread check bound to the child, and the slot of the child's
/// leaf at CHILD_OWN_ENTRY its capability to itself takes, after the four the other checks use.
const WALK_THREAD: u64 = first_slot(FIRST_EMPTY_ENTRY) + 20;
const WALK_OWN: u64 = first_slot(CHILD_OWN_ENTRY) + 4;

/// The control words, in the frame both spaces map, from its 64th word: the pass dom0 asks for, all
/// ones to have the thread suspend itself; the last pass the thread finished; that pass's cycles; the
/// first page it walks; how many; and whether each load's address depends on the one before.
const CONTROL: u64 = 512;
const GO: u64 = 0;
const DONE: u64 = 8;
const CYCLES: u64 = 16;
const BASE: u64 = 24;
const PAGES: u64 = 32;
const CHAIN: u64 = 40;
const STOP: u64 = u64::MAX;

// The code the walking thread runs, in a page of its own of dom0's image, which dom0 maps into the
// child's space at WALK_CODE_ADDRESS. From dom0_child_walk, with the control words' address as its first
// argument and its own slot as its second, it waits in user mode until GO differs from the last pass it
// made; when GO is STOP it suspends its own thread, and otherwise it loads one word from each of PAGES
// pages from BASE, reading the cycle counter before and after, stores the cycles at CYCLES and then
// GO's pass at DONE. With CHAIN zero the loads are independent, so the core walks for several misses at
// once, as a program streaming through its pages would; otherwise each load's address adds the word
// the last one read, zero in a frame retype zeroed, so each miss waits for the one before, as a program
// chasing pointers would.
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".balign 4096",
    ".global dom0_child_walk",
    "dom0_child_walk:",
    "xor r10d, r10d",
    "2: mov rax, [rdi + {go}]",
    "cmp rax, r10",
    "je 2b",
    "cmp rax, -1",
    "je 4f",
    "mov r10, rax",
    "mov r8, [rdi + {base}]",
    "mov rcx, [rdi + {pages}]",
    "mov r9, [rdi + {chain}]",
    "lfence",
    "rdtsc",
    "shl rdx, 32",
    "or rax, rdx",
    "mov r11, rax",
    "xor eax, eax",
    "test r9, r9",
    "jnz 6f",
    "3: mov rax, [r8]",
    "add r8, 4096",
    "dec rcx",
    "jnz 3b",
    "jmp 7f",
    "6: mov rax, [r8 + rax]",
    "add r8, 4096",
    "dec rcx",
    "jnz 6b",
    "7: lfence",
    "rdtsc",
    "shl rdx, 32",
    "or rax, rdx",
    "sub rax, r11",
    "mov [rdi + {cycles}], rax",
    "mov [rdi + {done}], r10",
    "jmp 2b",
    "4: mov rdi, rsi",
    "mov eax, {suspend}",
    "syscall",
    "5: jmp 5b",
    go = const GO,
    done = const DONE,
    cycles = const CYCLES,
    base = const BASE,
    pages = const PAGES,
    chain = const CHAIN,
    suspend = const operation::SUSPEND,
);
#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(
    ".balign 4096",
    ".global dom0_child_walk",
    "dom0_child_walk:",
    "mov x10, #0",
    "2: ldr x2, [x0, #{go}]",
    "cmp x2, x10",
    "b.eq 2b",
    "cmn x2, #1",
    "b.eq 4f",
    "mov x10, x2",
    "ldr x12, [x0, #{base}]",
    "ldr x9, [x0, #{pages}]",
    "ldr x13, [x0, #{chain}]",
    "isb",
    "mrs x11, cntvct_el0",
    "mov x3, #0",
    "cbnz x13, 6f",
    "3: ldr x3, [x12]",
    "add x12, x12, #4096",
    "subs x9, x9, #1",
    "b.ne 3b",
    "b 7f",
    "6: ldr x3, [x12, x3]",
    "add x12, x12, #4096",
    "subs x9, x9, #1",
    "b.ne 6b",
    "7: dsb ish",
    "isb",
    "mrs x3, cntvct_el0",
    "sub x3, x3, x11",
    "str x3, [x0, #{cycles}]",
    "dmb ish",
    "str x10, [x0, #{done}]",
    "b 2b",
    "4: mov x0, x1",
    "mov x8, #{suspend}",
    "svc #0",
    "5: b 5b",
    go = const GO,
    done = const DONE,
    cycles = const CYCLES,
    base = const BASE,
    pages = const PAGES,
    chain = const CHAIN,
    suspend = const operation::SUSPEND,
);

unsafe extern "C" {
    /// The first instruction of the walking thread's code above.
    fn dom0_child_walk();
}

/// The control word at `offset`, as dom0 sees it in the frame both spaces map.
fn control(offset: u64) -> *mut u64 {
    (entry_address(SHARED_ENTRY) + CONTROL + offset) as *mut u64
}

/// Has the thread make pass `pass` and returns its cycles, or None when it has not finished within
/// SWITCH_READS reads of DONE.
fn pass(pass: u64) -> Option<u64> {
    fence(Ordering::SeqCst);
    // dom0 and the walking thread share the control words through the frame both spaces map, which
    // switched_thread_held mapped at SHARED_ENTRY; dom0 writes GO, BASE and PAGES and the thread DONE
    // and CYCLES.
    unsafe { control(GO).write_volatile(pass) };
    (0..SWITCH_READS).any(|_| unsafe { control(DONE).read_volatile() } == pass).then(|| {
        fence(Ordering::SeqCst);
        unsafe { control(CYCLES).read_volatile() }
    })
}

/// One flush IPI to CPU 1, of `kind`, naming another context when `other`: the round trip in cycles,
/// or None when the kernel refused it.
fn flush(kind: u64, other: bool) -> Option<u64> {
    // The operation sends CPU 1 an IPI and changes nothing of dom0's.
    let (word, results) =
        unsafe { operation::invoke_returning(OPERATION, 0, [kind, other as u64, UNWALKED_ADDRESS, 0, 0]) };
    (operation::status(word) == operation::STATUS_OK).then_some(results[0])
}

/// The fastest and the total of what a run of rounds took.
#[derive(Clone, Copy)]
struct Times {
    fastest: u64,
    total: u64,
}

impl Times {
    const fn new() -> Self {
        Times { fastest: u64::MAX, total: 0 }
    }

    fn add(&mut self, cycles: u64) {
        self.fastest = self.fastest.min(cycles);
        self.total += cycles;
    }
}

/// Whether the child's space maps every page the thread walks and UNWALKED_ADDRESS to one 4K frame
/// retyped into the empty slot `slot`, through tables retyped from the gigabyte untyped, the last from
/// `empty` down, WALK_BELOW_TOP below its top, in the space of the child whose capability is in
/// `process`; and maps the page of dom0's image holding dom0_child_walk at WALK_CODE_ADDRESS.
fn walk_mapped(caller: &mut Tracked<Caller>, empty: u64, process: u64, slot: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let low = block.base + (4096 << block.order) - WALK_BELOW_TOP;
    let walk = dom0_child_walk as *const () as u64;
    let Some((image, page)) = image_page(caller, walk & !0xfff) else {
        return false;
    };
    let mut table = low;
    let mut table_at = |caller: &mut Tracked<Caller>, address: u64, level: u64| {
        let base = table;
        table += TABLE_PAGE_BYTES;
        retype(caller, untyped, operation::RETYPE_TABLE_PAGE, base, 0, level).status == operation::STATUS_OK
            && link(caller, process, address, level + 1, untyped, base).status == operation::STATUS_OK
    };
    let tables = table_at(caller, WALK_ADDRESS, 3)
        && table_at(caller, WALK_ADDRESS, 2)
        && (0..=WALK_TABLES).all(|k| table_at(caller, WALK_ADDRESS + k * 512 * 4096, 1));
    let frame = low + (WALK_TABLES + 3) * TABLE_PAGE_BYTES;
    tables
        && retype(caller, untyped, operation::RETYPE_FRAME, frame, slot, 0).status == operation::STATUS_OK
        && (0..=WALK_PAGES).all(|k| map(caller, process, WALK_ADDRESS + k * 4096, 1, slot, 0).status == operation::STATUS_OK)
        && map(caller, process, WALK_CODE_ADDRESS, 1, image, page).status == operation::STATUS_OK
}

/// Whether the walking thread runs on core 1: it gets a capability to itself with control in the child's
/// leaf, the entry dom0_child_walk at WALK_CODE_ADDRESS, the control words' address in the child's space
/// and its own slot; it is placed through the root's capability for core 1 above nothing there, and
/// started.
fn walker_started(caller: &mut Tracked<Caller>, process: u64) -> bool {
    let walk = dom0_child_walk as *const () as u64;
    let Ok(held) = inspect(caller, WALK_THREAD) else {
        return false;
    };
    let arguments = [CHILD_DATA_ADDRESS + CONTROL, WALK_OWN];
    // dom0 is the only writer of these control words until the thread starts.
    unsafe {
        control(GO).write_volatile(0);
        control(DONE).write_volatile(0);
        control(BASE).write_volatile(WALK_ADDRESS);
        control(PAGES).write_volatile(WALKS[0]);
        control(CHAIN).write_volatile(0);
    }
    derive(caller, WALK_THREAD, operation::through(process, WALK_OWN), RIGHT_CONTROL, held.base, held.order).status
        == operation::STATUS_OK
        && set_frame_word(caller, WALK_THREAD, operation::PC_WORD, WALK_CODE_ADDRESS + (walk & 0xfff))
            == operation::STATUS_OK
        && (0..2).all(|k| set_frame_word(caller, WALK_THREAD, ARGUMENT_WORDS[k], arguments[k]) == operation::STATUS_OK)
        && place(caller, WALK_THREAD, operation::ROOT_CORE_SLOT + SECOND_CORE, 1).status == operation::STATUS_OK
        && start(caller, WALK_THREAD).status == operation::STATUS_OK
}

/// Times every case at every walk, of independent loads and of chained ones, and prints a line for
/// each, the thread's passes numbered from `next`: the number after the last pass, or None when a pass
/// or a flush failed.
fn measured(mut next: u64) -> Option<u64> {
    for (chain, loads) in [(0, "independent loads"), (1, "chained loads")] {
        for &pages in &WALKS {
            // The thread reads PAGES and CHAIN only when GO changes, and dom0 changes GO only after DONE
            // caught up.
            unsafe {
                control(PAGES).write_volatile(pages);
                control(CHAIN).write_volatile(chain);
            }
            for &(kind, other, name) in &CASES {
                let (mut round_trip, mut quiet, mut flushed) = (Times::new(), Times::new(), Times::new());
                // A kernel refuses the first flush of a case it cannot make on this core; one refused
                // later is a failure.
                if flush(kind, other).is_none() {
                    let _ = writeln!(
                        ConsoleWriter::new(),
                        "flush cost: CPU 1 in user mode, {} pages, {}, {}: not available",
                        pages, loads, name,
                    );
                    continue;
                }
                for _ in 0..WARM_PASSES {
                    pass(next)?;
                    next += 1;
                }
                for _ in 0..ROUNDS {
                    quiet.add(pass(next)?);
                    round_trip.add(flush(kind, other)?);
                    flushed.add(pass(next + 1)?);
                    next += 2;
                }
                let _ = writeln!(
                    ConsoleWriter::new(),
                    "flush cost: CPU 1 in user mode, {} pages, {}, {}: round trip fastest {} mean {}, pass fastest {} mean {}, \
                     after the flush fastest {} mean {} cycles over {} rounds",
                    pages, loads, name, round_trip.fastest, round_trip.total / ROUNDS, quiet.fastest, quiet.total / ROUNDS,
                    flushed.fastest, flushed.total / ROUNDS, ROUNDS,
                );
            }
        }
    }
    Some(next)
}

/// Whether the measurement held: nothing to measure on a kernel that answers OPERATION unknown;
/// otherwise the walk is mapped into the child's space, through the empty slot `slot` for its frame, the
/// thread runs on core 1, every case is timed and printed, and the thread suspends itself, after which
/// dom0 unmaps the walked pages so the child is as the checks after this one expect it.
pub(crate) fn held(caller: &mut Tracked<Caller>, empty: u64, process: u64, slot: u64) -> bool {
    // A kind past every flush asks for nothing: a kernel with the operation refuses it.
    let probe = unsafe { operation::invoke(OPERATION, 0, [UNKNOWN_KIND, 0, 0, 0, 0]) };
    match operation::status(probe) {
        operation::STATUS_UNKNOWN => return true,
        operation::STATUS_REFUSED => {}
        _ => return false,
    }
    if !walk_mapped(caller, empty, process, slot) || !walker_started(caller, process) || measured(1).is_none() {
        return false;
    }
    // The thread reads GO until it changes and suspends itself at STOP.
    unsafe { control(GO).write_volatile(STOP) };
    (0..=WALK_PAGES).all(|k| unmap(caller, process, WALK_ADDRESS + k * 4096, 1).status == operation::STATUS_OK)
}
