//! This core's x86_64 state: what the instruction set adds to its [`Cpu`], the GS base that finds
//! the block, and the order a core is brought up in.

use core::arch::asm;

use astd::boot::BootInfo;
use memoffset::offset_of;

use super::gdt::{GlobalDescriptorTable, TaskStateSegment};
use super::{gdt, interrupt, msr, syscalls};
use crate::cpu::{Cpu, KernelStack};

/// The x86_64 share of a core's [`Cpu`].
#[repr(C)]
pub struct CoreState {
    /// The Global Descriptor Table.
    ///
    /// See [crate::arch::gdt] for a list of indices and their associated usages.
    pub gdt: GlobalDescriptorTable,

    /// The Task State Segment.
    pub tss: TaskStateSegment,

    /// The Interrupt Stacks.
    pub ist: [KernelStack; 7],

    /// The user's stack pointer, held here by the syscall entry while it switches to the syscall stack,
    /// so that no argument register has to hold it.
    pub user_rsp: u64,
}

impl CoreState {
    pub const fn new() -> Self {
        Self {
            gdt: GlobalDescriptorTable::empty(),
            tss: TaskStateSegment::new(),
            ist: [
                KernelStack::new(),
                KernelStack::new(),
                KernelStack::new(),
                KernelStack::new(),
                KernelStack::new(),
                KernelStack::new(),
                KernelStack::new(),
            ],
            user_rsp: 0,
        }
    }
}

/// Makes `cpu` the block this core finds through [`core_pointer`]: it becomes the GS base.
pub unsafe fn set_core_pointer(cpu: *const Cpu) {
    msr::wrmsr(msr::GS_BASE, cpu as u64);
}

/// This core's block, read from its own first field through GS.
pub fn core_pointer() -> *mut Cpu {
    let address: u64;
    unsafe {
        asm!(
            "mov {address}, gs:[{self_ptr}]",
            address = out(reg) address,
            self_ptr = const offset_of!(Cpu, self_ptr),
            options(pure, readonly, nostack, preserves_flags),
        );
    }
    address as *mut Cpu
}

/// Keeps what the instruction set needs from `boot`: whether PCID is on. Once on the boot core,
/// after the kernel copies `BootInfo`.
pub unsafe fn init(boot: &BootInfo) {
    super::PCIDE = if boot.pcide { 1 } else { 0 };
}

/// The value a core that is starting loads as its translation base: the kernel's PML4 as the loader
/// built it, with the no-flush bit where PCID is on, which asks the trampoline to turn PCIDE on.
pub fn translation_root(boot: &BootInfo) -> u64 {
    let mut root = boot.pml4 as u64;
    if boot.pcide {
        root |= super::CR3_NO_FLUSH;
    }
    root
}

/// Brings up the boot core, whose [`Cpu`] is in place: the control bits, its GDT and TSS, the IDT
/// every core shares, its local APIC with the IOAPIC routed to it, and the syscall entry.
pub unsafe fn init_boot_core() {
    init_control_registers();
    gdt::init_cpu();

    interrupt::init();
    interrupt::init_cpu();

    syscalls::init_cpu();
}

/// Brings up a core started after the boot core, whose [`Cpu`] is in place.
pub unsafe fn init_core() {
    init_control_registers();
    gdt::init_cpu();
    interrupt::init_ap();
    syscalls::init_cpu();
}

/// CR0.MP, CR0.EM, CR0.NE, CR0.WP, CR0.NW and CR0.CD.
const CR0_MONITOR_COPROCESSOR: u64 = 1 << 1;
const CR0_EMULATE_COPROCESSOR: u64 = 1 << 2;
const CR0_NUMERIC_ERROR: u64 = 1 << 5;
const CR0_WRITE_PROTECT: u64 = 1 << 16;
const CR0_NOT_WRITE_THROUGH: u64 = 1 << 29;
const CR0_CACHE_DISABLE: u64 = 1 << 30;
/// CR4.OSFXSR and CR4.OSXMMEXCPT.
const CR4_OSFXSR: u64 = 1 << 9;
const CR4_OSXMMEXCPT: u64 = 1 << 10;

/// Sets the control bits the kernel relies on. Ring 0 cannot write through a read-only mapping,
/// caching is on, and threads can use x87 and SSE: no x87 emulation, WAIT checks CR0.TS, x87
/// errors raise #MF, the SSE instructions and FXSAVE are on, and an unmasked SIMD exception raises
/// #XM. Every core sets this itself, so none depends on what firmware or the trampoline left.
unsafe fn init_control_registers() {
    let mut cr0 = super::read_cr0();
    let mut cr4 = super::read_cr4();
    cr0 &= !(CR0_EMULATE_COPROCESSOR | CR0_NOT_WRITE_THROUGH | CR0_CACHE_DISABLE);
    cr0 |= CR0_MONITOR_COPROCESSOR | CR0_NUMERIC_ERROR | CR0_WRITE_PROTECT;
    cr4 |= CR4_OSFXSR | CR4_OSXMMEXCPT;
    super::write_cr0(cr0);
    super::write_cr4(cr4);
    log::info!("CPU {}: CR0 {:#x}, CR4 {:#x}", crate::cpu::get_cpu_id(), cr0, cr4);
}
