//! The per-CPU data structure.
//!
//! The [`Cpu`] data structure is set as the `GS` base on the CPU.
//! It currently consists of the following:
//!
//! - GDT
//! - TSS
//! - IST stack spaces

use core::ptr;

use crate::arch::msr;

use crate::arch::gdt::{GlobalDescriptorTable, TaskStateSegment};
use crate::thread::SwitchDecision;
use verified::arch::Registers;

const NEW_CPU: Cpu = Cpu::new();

/// Per-processor data.
static mut CPUS: [Cpu; 16] = [NEW_CPU; 16];

/// Size of an IST stack.
const IST_STACK_SIZE: usize = 1 * 1024 * 1024; // 1 MiB

/// Per-processor data for a CPU.
#[repr(C, align(4096))]
pub struct Cpu {
    /// A pointer to ourselves.
    ///
    /// We do a `mov rax, gs:[GS_SELF_PTR_OFFSET]` to get our own address.
    /// We also want to be able to easily access other fields directly.
    pub self_ptr: *const Cpu,

    /// The CPU ID.
    ///
    /// Currently it's the logical APIC ID.
    pub id: usize,

    /// The state of the parked thread.
    pub parked: Registers,

    /// The context switch decision upon exiting the kernel.
    pub switch_decision: SwitchDecision,

    /// The Global Descriptor Table.
    ///
    /// See [crate::arch::gdt] for a list of indices and their associated usages.
    pub gdt: GlobalDescriptorTable,

    /// The Task State Segment.
    pub tss: TaskStateSegment,

    /// The Interrupt Stacks.
    pub ist: [IstStack; 7],

    pub syscall_stack: IstStack,

    /// The stack pointer for syscalls.
    ///
    /// We do not support nested syscalls.
    pub syscall_sp: u64,

    /// The user's stack pointer, held here by the syscall entry while it switches to the syscall stack,
    /// so that no argument register has to hold it.
    pub user_rsp: u64,
}

/// A stack. Its top must be 16-byte aligned: a byte array alone could leave the syscall stack
/// pointer misaligned.
#[repr(C, align(16))]
pub struct Stack<const SZ: usize>([u8; SZ]);

/// An IST stack.
pub type IstStack = Stack<IST_STACK_SIZE>;

impl<const SZ: usize> Stack<SZ> {
    pub const fn new() -> Self {
        Self([0u8; SZ])
    }

    pub fn bottom(&self) -> *const u8 {
        unsafe {
            (self.0.as_ptr() as *const u8).add(SZ)
        }
    }
}

unsafe impl Send for Cpu {}
unsafe impl Sync for Cpu {}

impl Cpu {
    pub const fn new() -> Self {
        Self {
            self_ptr: ptr::null(),
            id: 0,
            parked: Registers::zeroed(),
            switch_decision: SwitchDecision::NoSwitching,
            gdt: GlobalDescriptorTable::empty(),
            tss: TaskStateSegment::new(),
            ist: [
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
                IstStack::new(),
            ],
            syscall_stack: IstStack::new(),
            syscall_sp: 0,
            user_rsp: 0,
        }
    }
}

/// Returns a handle to the current CPU's data structure.
pub fn get_current() -> &'static mut Cpu {
    let address = crate::read_current_cpu_field!(self_ptr) as *mut Cpu;
    unsafe { &mut *address }
}

/// Returns the current CPU ID.
pub fn get_cpu_id() -> usize {
    crate::read_current_cpu_field!(id) as usize
}

/// Initialize the CPU-local data structure.
///
/// This should only be called once.
pub unsafe fn init_cpu(cpu_id: usize) {
    let cpu = &mut CPUS[cpu_id];
    let address = cpu as *const Cpu;

    log::debug!("CPU{} @ {:?}", cpu_id, address);

    cpu.self_ptr = address;
    cpu.id = cpu_id;
    cpu.syscall_sp = cpu.syscall_stack.bottom() as u64;

    msr::wrmsr(msr::GS_BASE, address as u64);
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
pub unsafe fn init_control_registers() {
    let mut cr0 = crate::arch::read_cr0();
    let mut cr4 = crate::arch::read_cr4();
    cr0 &= !(CR0_EMULATE_COPROCESSOR | CR0_NOT_WRITE_THROUGH | CR0_CACHE_DISABLE);
    cr0 |= CR0_MONITOR_COPROCESSOR | CR0_NUMERIC_ERROR | CR0_WRITE_PROTECT;
    cr4 |= CR4_OSFXSR | CR4_OSXMMEXCPT;
    crate::arch::write_cr0(cr0);
    crate::arch::write_cr4(cr4);
    log::info!("CPU {}: CR0 {:#x}, CR4 {:#x}", get_cpu_id(), cr0, cr4);
}

/// Spins until `done`. Whether it spins at all depends on how far another core has got, so the loop
/// is left out of coverage, which would otherwise differ between two boots of one build.
#[coverage(off)]
pub fn spin_until(done: impl Fn() -> bool) {
    while !done() {
        core::hint::spin_loop();
    }
}
