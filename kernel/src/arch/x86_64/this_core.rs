// SPDX-License-Identifier: MIT

//! This core's x86_64 state: what the instruction set adds to its [`Cpu`], the GS base that finds
//! the block, and the order a core is brought up in.

use core::arch::asm;

use astd::boot::BootInfo;
use core::mem::offset_of;

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
    /// The stacks this share holds: the interrupt stacks.
    pub fn stacks(&self) -> &[KernelStack] {
        &self.ist
    }

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
/// every core shares, its local APIC, and the syscall entry.
pub unsafe fn init_boot_core() {
    init_control_registers();
    init_performance_counters();
    gdt::init_cpu();

    interrupt::init();
    interrupt::init_cpu();

    syscalls::init_cpu();
}

/// Brings up a core started after the boot core, whose [`Cpu`] is in place.
pub unsafe fn init_core() {
    init_control_registers();
    init_performance_counters();
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

/// CR4.PCE, which lets RDPMC run outside ring 0. APM 2 §3.1.3, Figure 3-7.
const CR4_PCE: u64 = 1 << 8;
/// CPUID Fn8000_0001 ECX bit 23, PerfCtrExtCore: the six core counters at PERF_CTL0. APM 2 §13.2.2.
const PERF_CTR_EXT_CORE: u32 = 1 << 23;
/// PerfEvtSel0 and PerfCtr0; counter n is at twice n past each. APM 2 Appendix A.6.
const PERF_CTL0: u32 = 0xC001_0200;
const PERF_CTR0: u32 = 0xC001_0201;
/// The events counters 0 to 3 count, in PerfEvtSel's format (APM 2 §13.2.1, Figure 13-11): 0x43 in
/// bits 23:16 is EN, OS and USR, the unit mask is bits 15:8 and the event bits 7:0. The events are AMD
/// doc 58550 Rev 0.02's: cycles not in halt, PMCx076 (p. 20); retired instructions, PMCx0C0 (p. 26);
/// data cache fills from any source, PMCx044 with every defined unit mask bit but 7, extension memory
/// (p. 18); and those fills that came from another CCX's cache in the same NUMA node, PMCx044 bit 2.
const PERF_EVENTS: [u64; 4] = [0x43_0076, 0x43_00C0, 0x43_5F44, 0x43_0444];
/// CPUID Fn8000_0022 EAX bit 0, PerfMonV2: PerfCntrGlobalCtl exists. APM 2 §13.2.2.
const PERF_MON_V2: u32 = 1 << 0;
/// PerfCntrGlobalCtl: counter n counts only while its bit n here and its PerfEvtSel's EN are both
/// set. APM 2 §13.2.1, Figure 13-12, and Appendix A.6. Its documented reset value enables all six,
/// but firmware or a hypervisor may leave them clear, as KVM's PerfMonV2 guest starts.
const PERF_CNTR_GLOBAL_CTL: u32 = 0xC000_0301;
/// The bits of PerfCntrGlobalCtl that enable counters 0 to 3.
const PERF_GLOBAL_ENABLE: u64 = (1 << PERF_EVENTS.len()) - 1;

/// Counts PERF_EVENTS on counters 0 to 3 from boot on, in the kernel and in every process, and lets
/// every process read them with RDPMC, where CPUID offers the extended core counters. That is a boot
/// setting, not a capability: no process can change what is counted, and the counts are readable by
/// all as the TSC is, the same timing channel. A core without the counters, under TCG or under KVM
/// with QEMU's pmu off, keeps CR4.PCE clear, so RDPMC outside ring 0 faults there.
unsafe fn init_performance_counters() {
    if core::arch::x86_64::__cpuid(0x8000_0001).ecx & PERF_CTR_EXT_CORE == 0 {
        log::info!("CPU {}: no extended core performance counters", crate::cpu::get_cpu_id());
        return;
    }
    for (n, &event) in PERF_EVENTS.iter().enumerate() {
        msr::wrmsr(PERF_CTR0 + 2 * n as u32, 0);
        msr::wrmsr(PERF_CTL0 + 2 * n as u32, event);
    }
    if core::arch::x86_64::__cpuid(0x8000_0000).eax >= 0x8000_0022
        && core::arch::x86_64::__cpuid(0x8000_0022).eax & PERF_MON_V2 != 0
    {
        msr::wrmsr(PERF_CNTR_GLOBAL_CTL, msr::rdmsr(PERF_CNTR_GLOBAL_CTL) | PERF_GLOBAL_ENABLE);
    }
    super::write_cr4(super::read_cr4() | CR4_PCE);
    log::info!("CPU {}: performance counters 0 to 3 count {:x?}", crate::cpu::get_cpu_id(), PERF_EVENTS);
}

/// How far counters 0 to 3 have counted PERF_EVENTS on this core, or None where the core has no
/// extended core counters and init_performance_counters left them alone. RDPMC reads a counter in
/// ring 0 whatever CR4.PCE says (APM 3, RDPMC).
pub fn counters() -> Option<[u64; 4]> {
    if core::arch::x86_64::__cpuid(0x8000_0001).ecx & PERF_CTR_EXT_CORE == 0 {
        return None;
    }
    Some(core::array::from_fn(|n| {
        let (lo, hi): (u32, u32);
        unsafe {
            asm!("rdpmc", in("ecx") n as u32, out("eax") lo, out("edx") hi, options(nomem, nostack, preserves_flags))
        };
        (hi as u64) << 32 | lo as u64
    }))
}
