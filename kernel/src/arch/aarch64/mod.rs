//! The AArch64 instructions and system registers the kernel uses at EL1.
//!
//! Written from the Arm Architecture Reference Manual for A-profile architecture (DDI 0487 M.d),
//! cited as Arm ARM with the section beside each item. The loader enters the kernel at EL1 with
//! interrupts masked, translating through its table in TTBR0_EL1 with TCR_EL1 and MAIR_EL1 as
//! design/arch-module/ item 1 names them, the kernel's stack in sp and the `BootInfo` address in x0.

use core::arch::asm;
use core::ffi::c_void;

use astd::boot::BootInfo;
use verified::define::PCID_MAX;

use crate::cpu::Cpu;

pub mod write_protect;

/// The AArch64 share of a core's [`Cpu`]: nothing, since what the instruction set keeps per core is
/// in the core's own system registers.
#[repr(C)]
pub struct CoreState {}

impl CoreState {
    pub const fn new() -> Self {
        Self {}
    }
}

/// Makes `cpu` the block this core finds through [`core_pointer`]: it becomes TPIDR_EL1, the
/// register the architecture leaves to EL1 software and makes no use of itself. Arm ARM D24.2.204.
pub unsafe fn set_core_pointer(cpu: *const Cpu) {
    asm!("msr TPIDR_EL1, {cpu}", cpu = in(reg) cpu, options(nomem, nostack, preserves_flags));
}

/// This core's block, read from TPIDR_EL1.
pub fn core_pointer() -> *mut Cpu {
    let cpu: *mut Cpu;
    unsafe { asm!("mrs {cpu}, TPIDR_EL1", cpu = out(reg) cpu, options(nomem, nostack, preserves_flags)) };
    cpu
}

/// Keeps nothing from `boot`: each core reads what the instruction set needs from its own ID
/// registers. Once on the boot core, after the kernel copies `BootInfo`.
pub unsafe fn init(boot: &BootInfo) {
    let _ = boot;
}

/// The value a core that is starting loads as its translation base: the kernel's root table as the
/// loader built it, as TTBR0_EL1 holds it under address-space id 0.
pub fn translation_root(boot: &BootInfo) -> u64 {
    translation_base(boot.pml4 as usize, 0)
}

/// Brings up the boot core, whose [`Cpu`] is in place: its translation control. It has no exception
/// vectors to install, so it stops there, naming itself.
pub unsafe fn init_boot_core() {
    init_translation_control();
    unimplemented!("init_boot_core");
}

/// Brings up a core started after the boot core, whose [`Cpu`] is in place, as far as
/// [`init_boot_core`] brings up the boot core.
pub unsafe fn init_core() {
    init_translation_control();
    unimplemented!("init_core");
}

/// ID_AA64MMFR0_EL1.ASIDBits, bits 7:4: 0b0010 where an address-space id has 16 bits and 0b0000
/// where it has 8. Arm ARM D24.2.87.
const ASID_BITS_SHIFT: u32 = 4;
const ASID_BITS_MASK: u64 = 0b1111;
const ASID_BITS_16: u64 = 0b0010;

/// TCR_EL1.A1, bit 22. Clear, the current address-space id is TTBR0_EL1's ASID field, so one write
/// of that register changes the table and the id together. Arm ARM D24.2.193.
const TCR_A1: u64 = 1 << 22;

/// TCR_EL1.AS, bit 36. Set, all 16 bits of the ASID field tag a TLB entry; clear, the upper 8 are
/// ignored. Arm ARM D24.2.193.
const TCR_AS: u64 = 1 << 36;

/// An address-space id the kernel hands out fits the 16 bits, and not the 8.
const _: () = assert!(PCID_MAX > 1 << 8 && PCID_MAX <= 1 << 16);

/// TCR_EL1 as the kernel switches address spaces by it, from the value the core entered with.
const fn translation_control(entered: u64) -> u64 {
    entered & !TCR_A1 | TCR_AS
}

const _: () = assert!(translation_control(0) == 1 << 36);
const _: () = assert!(translation_control(u64::MAX) == !(1 << 22));

/// Sets the translation control [`switch_address_space`] relies on: a 16-bit address-space id, taken
/// from TTBR0_EL1. Every core sets this itself, so none depends on what the loader or the start of
/// a second core left. The id in use is 0 before and after, so no TLB entry changes meaning.
unsafe fn init_translation_control() {
    let features: u64;
    asm!("mrs {features}, ID_AA64MMFR0_EL1", features = out(reg) features, options(nomem, nostack, preserves_flags));
    assert!(
        features >> ASID_BITS_SHIFT & ASID_BITS_MASK == ASID_BITS_16,
        "this core's address-space ids have 8 bits, and the kernel hands out ids below {}",
        PCID_MAX
    );
    let entered: u64;
    asm!("mrs {entered}, TCR_EL1", entered = out(reg) entered, options(nomem, nostack, preserves_flags));
    let control = translation_control(entered);
    // A change to a system register binds the instructions after the next ISB. Arm ARM B2.6.1.
    asm!("msr TCR_EL1, {control}", "isb", control = in(reg) control, options(nomem, nostack, preserves_flags));
    log::info!("CPU {}: TCR_EL1 {:#x}", crate::cpu::get_cpu_id(), control);
}

/// Stops this core: every interrupt masked (MSR DAIFSet, Arm ARM C6.2.288, whose operand's bits are
/// D, A, I and F), then WFI for good.
pub unsafe fn spin_forever() -> ! {
    asm!("msr DAIFSet, #0b1111", options(nomem, nostack, preserves_flags));
    loop {
        asm!("wfi", options(nomem, nostack, preserves_flags));
    }
}

/// The cycle counter: the generic timer's virtual count, which EL1 reads on every core. Arm ARM
/// D24.10.26.
pub fn cycles() -> u64 {
    let count: u64;
    unsafe { asm!("mrs {count}, CNTVCT_EL0", count = out(reg) count, options(nomem, nostack, preserves_flags)) };
    count
}

/// Seconds a boot check waits for another core, where a core that answers takes microseconds.
const STALL_SECONDS: u64 = 5;

/// CNTFRQ_EL0.ClockFreq, bits 31:0: the counter's frequency in Hz, which the firmware wrote. The
/// upper bits are reserved. Arm ARM D24.10.1.
const COUNTER_FREQUENCY_MASK: u64 = 0xffff_ffff;

/// How many cycles of [`cycles`] a boot check waits for another core before it reports that the core
/// did not answer.
pub fn stall_cycles() -> u64 {
    let frequency: u64;
    unsafe {
        asm!("mrs {frequency}, CNTFRQ_EL0", frequency = out(reg) frequency, options(nomem, nostack, preserves_flags))
    };
    STALL_SECONDS * (frequency & COUNTER_FREQUENCY_MASK)
}

/// Waits for the next interrupt: IRQs unmasked (MSR DAIFClr with the I bit, Arm ARM C6.2.288), then
/// WFI (Arm ARM C6.2.504).
pub fn wait() {
    unsafe { asm!("msr DAIFClr, #0b0010", "wfi", options(nomem, nostack, preserves_flags)) };
}

/// Enters user code at `pc` with stack `sp` and two entry arguments. The return to EL0 comes with
/// the exception vectors that take EL0's calls, so this stops, naming itself.
pub unsafe fn enter_userspace(pc: *const c_void, sp: *mut c_void, first: u64, second: u64) -> ! {
    let _ = (pc, sp, first, second);
    unimplemented!("enter_userspace");
}

/// TTBR0_EL1's ASID field, bits 63:48. Arm ARM D24.2.208.
const TTBR_ASID_SHIFT: u32 = 48;

/// TTBR0_EL1's table address with a 4K granule and 48-bit addresses: bits 47:12. Bits 11:1 are the
/// low bits of the address field, zero for a table aligned to its size, and bit 0 is CnP, clear: a
/// core's entries under an id are its own. Arm ARM D24.2.208.
const TTBR_ADDRESS: u64 = 0x0000_ffff_ffff_f000;

/// TTBR0_EL1 for the table whose top level is at physical address `root`, as address space `asid`.
const fn translation_base(root: usize, asid: usize) -> u64 {
    assert!(root as u64 & !TTBR_ADDRESS == 0, "a page table root is 4K-aligned and below 2^48");
    assert!(asid < PCID_MAX, "an address-space id fits an ASID");
    (asid as u64) << TTBR_ASID_SHIFT | root as u64
}

const _: () = assert!(translation_base(0x4000_0000, 0) == 0x4000_0000);
const _: () = assert!(translation_base(0xffff_ffff_f000, PCID_MAX - 1) == 0x0fff_ffff_ffff_f000);
const _: () = assert!(translation_base(0x1000, 1) == 1 << 48 | 1 << 12);

/// Switches this core to the page table whose top level is at physical address `root`, as address
/// space `asid`, keeping the entries the TLB holds under `asid`: one write of TTBR0_EL1 changes the
/// table and the id together, and flushes nothing. The kernel tracks when an address space's entries
/// go stale and flushes them itself, design/flush-without-waiting/.
pub fn switch_address_space(root: usize, asid: usize) {
    let base = translation_base(root, asid);
    // The instructions after the ISB translate through the new table. Arm ARM B2.6.1.
    unsafe { asm!("msr TTBR0_EL1, {base}", "isb", base = in(reg) base, options(nostack, preserves_flags)) };
}
