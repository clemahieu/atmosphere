// SPDX-License-Identifier: MIT

//! The loader's AArch64 instructions: the device accesses, the system registers and the branches.

use core::arch::asm;
use core::ffi::c_void;

use astd::boot::BootInfo;

use super::{coherence, flush_argument, lines, system_control, translation_control, MEMORY_ATTRIBUTES};

/// Reads the 32-bit register at `address` in one load of a register without writeback, the form
/// whose stage 2 data abort reports the access in its syndrome (Arm ARM D24.2.45, ISV), which a
/// hypervisor emulating the device needs.
pub(super) unsafe fn read_register(address: usize) -> u32 {
    let value: u32;
    asm!(
        "ldr {value:w}, [{address}]",
        address = in(reg) address,
        value = out(reg) value,
        options(nostack, readonly, preserves_flags),
    );
    value
}

/// Writes the 32-bit register at `address` in one store of that form.
pub(super) unsafe fn write_register(address: usize, value: u32) {
    asm!(
        "str {value:w}, [{address}]",
        address = in(reg) address,
        value = in(reg) value,
        options(nostack, preserves_flags),
    );
}

/// Masks this CPU's interrupts: PSTATE.{D, A, I, F}, all four.
pub unsafe fn disable_interrupts() {
    asm!("msr daifset, #0xf", options(nomem, nostack, preserves_flags));
}

/// Runs `crate::load` on the stack that ends at `stack_top`.
pub unsafe fn load_on_stack(stack_top: u64, rsdp: u64, wait_for_debugger: bool) -> ! {
    asm!(
        "mov sp, {stack_top}",
        "bl {load}",
        stack_top = in(reg) stack_top,
        load = sym load,
        in("x0") rsdp,
        in("x1") wait_for_debugger as u64,
        options(noreturn),
    );
}

/// Called on the loader's stack with the RSDP in x0 and whether to wait for a debugger in x1.
extern "C" fn load(rsdp: u64, wait_for_debugger: bool) -> ! {
    crate::load(rsdp, wait_for_debugger)
}

/// The register a debugger clears to let the loader go, for the line `debugger::wait` logs.
pub const DEBUGGER_REGISTER: &str = "x0";

/// What x0 holds while the loader waits.
const WAITING: u64 = 0x6764_6277_6169_7421;

/// Spins until a debugger sets x0 to anything but `WAITING`.
pub fn wait_for_debugger() {
    unsafe {
        asm!(
            "2:",
            "yield",
            "cmp x0, {waiting}",
            "b.eq 2b",
            waiting = in(reg) WAITING,
            inout("x0") WAITING => _,
            options(nomem, nostack),
        );
    }
}

/// The exception level, CurrentEL bits 3:2.
fn exception_level() -> u64 {
    let current: u64;
    unsafe {
        asm!("mrs {current}, CurrentEL", current = out(reg) current, options(nomem, nostack, preserves_flags));
    }
    current >> 2 & 0b11
}

/// Makes `root` the table this CPU translates through at EL1, with the translation control and the
/// memory attributes the loader's descriptors are written for. Returns whether the TLB is tagged,
/// for `BootInfo::pcide`: an ASID always tags it.
///
/// The firmware's tables need not have the loader's shape, and the translation control and the
/// root table cannot change in one step, so the switch turns translation off, which leaves every
/// address its own, and on again over the loader's tables. While it is off a data access is a
/// device access that the caches do not serve, so the switch is one block that touches no memory;
/// its own instructions are cleaned to memory first, where the fetch finds them whatever serves
/// it.
pub unsafe fn activate(root: *const c_void) -> bool {
    let level = exception_level();
    log::info!("Running at EL{}", level);
    assert!(level == 1, "the loader's tables are EL1's, and the firmware left it at EL{}", level);

    let (id_aa64mmfr0, id_aa64mmfr1, firmware): (u64, u64, u64);
    asm!(
        "mrs {id_aa64mmfr0}, ID_AA64MMFR0_EL1",
        "mrs {id_aa64mmfr1}, ID_AA64MMFR1_EL1",
        "mrs {firmware}, SCTLR_EL1",
        id_aa64mmfr0 = out(reg) id_aa64mmfr0,
        id_aa64mmfr1 = out(reg) id_aa64mmfr1,
        firmware = out(reg) firmware,
        options(nomem, nostack, preserves_flags),
    );
    let translation = translation_control(id_aa64mmfr0, id_aa64mmfr1);
    let control = system_control(firmware);

    log::info!("Switching to the root table @ {:x?}", root);
    asm!(
        // Clean the lines that hold 2: up to 3:, by the smallest line any data cache has:
        // 4 << CTR_EL0.DminLine bytes, DminLine being bits 19:16.
        "adr {start}, 2f",
        "adr {end}, 3f",
        "mrs {line}, CTR_EL0",
        "ubfx {line}, {line}, #16, #4",
        "mov {mask}, #4",
        "lsl {line}, {mask}, {line}",
        "sub {mask}, {line}, #1",
        "bic {start}, {start}, {mask}",
        "4:",
        "dc cvac, {start}",
        "add {start}, {start}, {line}",
        "cmp {start}, {end}",
        "b.lo 4b",
        "dsb sy",
        "isb",
        "2:",
        // Translation off: SCTLR_EL1.M, bit 0, clear.
        "bic {off}, {control}, #1",
        "msr SCTLR_EL1, {off}",
        "isb",
        "msr TCR_EL1, {translation}",
        "msr MAIR_EL1, {attributes}",
        // The root table, under ASID 0.
        "msr TTBR0_EL1, {root}",
        "isb",
        // Nothing the firmware's tables left stays cached.
        "tlbi vmalle1",
        "dsb nsh",
        "isb",
        "msr SCTLR_EL1, {control}",
        "isb",
        "3:",
        start = out(reg) _,
        end = out(reg) _,
        line = out(reg) _,
        mask = out(reg) _,
        off = out(reg) _,
        control = in(reg) control,
        translation = in(reg) translation,
        attributes = in(reg) MEMORY_ATTRIBUTES,
        root = in(reg) root,
        options(nostack),
    );

    let (ttbr0, tcr, mair, sctlr): (u64, u64, u64, u64);
    asm!(
        "mrs {ttbr0}, TTBR0_EL1",
        "mrs {tcr}, TCR_EL1",
        "mrs {mair}, MAIR_EL1",
        "mrs {sctlr}, SCTLR_EL1",
        ttbr0 = out(reg) ttbr0,
        tcr = out(reg) tcr,
        mair = out(reg) mair,
        sctlr = out(reg) sctlr,
        options(nomem, nostack, preserves_flags),
    );
    log::info!(
        "Translating through the loader's tables: TTBR0_EL1 {:#x}, TCR_EL1 {:#x}, MAIR_EL1 {:#x}, SCTLR_EL1 {:#x}",
        ttbr0,
        tcr,
        mair,
        sctlr
    );

    true
}

/// Drops the TLB's entry for the page at `vaddr`, whatever the page's size.
pub unsafe fn flush_page(vaddr: u64) {
    asm!(
        "tlbi vae1, {page}",
        "dsb nsh",
        "isb",
        page = in(reg) flush_argument(vaddr),
        options(nostack, preserves_flags),
    );
}

/// Makes this CPU's instruction fetch see what the loader wrote to `start..end`, addresses mapped in
/// the live table, before anything there is executed.
///
/// A fetch need not see a write made through the data cache until the lines written are cleaned to
/// where the two caches meet and the instruction cache's copies of them are invalidated, each
/// complete at a DSB, with an ISB before the first fetch (Arm ARM B2.2.5); CTR_EL0 says which of
/// the two this core needs. The firmware does it for the image it loads, the loader's own; what the
/// loader places is the loader's to do. An instruction cache indexed by virtual address drops the
/// lines of the address it is given, not of every address the frame is mapped at (D7.5.9.13), so
/// the range is the one the code executes at.
pub unsafe fn synchronize_instructions(start: u64, end: u64) {
    let cache_type: u64;
    asm!("mrs {cache_type}, CTR_EL0", cache_type = out(reg) cache_type, options(nomem, nostack, preserves_flags));
    let coherence = coherence(cache_type);

    if let Some(line) = coherence.clean {
        for address in lines(start, end, line) {
            asm!("dc cvau, {address}", address = in(reg) address, options(nostack, preserves_flags));
        }
    }
    // The writes, and the cleans, are complete.
    asm!("dsb ish", options(nostack, preserves_flags));
    if let Some(line) = coherence.invalidate {
        for address in lines(start, end, line) {
            asm!("ic ivau, {address}", address = in(reg) address, options(nostack, preserves_flags));
        }
        asm!("dsb ish", options(nostack, preserves_flags));
    }
    asm!("isb", options(nostack, preserves_flags));

    log::info!("Instruction fetch sees {:x}-{:x}: CTR_EL0 {:#x}, {:?}", start, end, cache_type, coherence);
}

/// PSTATE.{D, A, I, F} as DAIF reads them, bits 9:6.
const INTERRUPTS_MASKED: u64 = 0b1111 << 6;

/// Calls the kernel's entry on the stack that ends at `stack_top`, with the boot information's
/// address in x0, where the entry's C signature takes it, and returns what the entry returns.
///
/// The kernel's stack is SP_EL1, the one an exception taken to EL1 runs on, whichever the firmware
/// left selected. The kernel finds every interrupt masked, as `disable_interrupts` left them, and
/// translates through the table `activate` installed.
pub unsafe fn enter_kernel(entry: *const c_void, boot_info: *const BootInfo, stack_top: u64) -> usize {
    let masks: u64;
    asm!("mrs {masks}, DAIF", masks = out(reg) masks, options(nomem, nostack, preserves_flags));
    assert!(masks == INTERRUPTS_MASKED, "the kernel's entry takes every interrupt masked: DAIF {:#x}", masks);

    let ret: usize;
    asm!(
        // The loader's stack and its selection, in registers the entry preserves.
        "mov x20, sp",
        "mrs x21, SPSel",
        "msr SPSel, #1",
        "mov sp, {stack_top}",
        "blr {entry}",
        "msr SPSel, x21",
        "mov sp, x20",
        entry = in(reg) entry,
        stack_top = in(reg) stack_top,
        inout("x0") boot_info => ret,
        out("x20") _,
        out("x21") _,
        clobber_abi("C"),
    );
    ret
}
