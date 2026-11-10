//! The per-core block.
//!
//! Each core has a [`Cpu`]. The arch module keeps the pointer through which a core finds its own
//! (`arch::set_core_pointer`, `arch::core_pointer`) and adds the state its instruction set needs
//! (`arch::CoreState`). design/one-lock-bounded-steps/ says what may live here, outside the lock.

use core::ptr;

use crate::arch;
use crate::thread::SwitchDecision;
use verified::arch::Registers;

const NEW_CPU: Cpu = Cpu::new();

/// Slots for the CPUs the test machine boots. The benchmark starts 4 and the gate starts 2.
/// design/test-guest-memory/.
const CPU_SLOTS: usize = 4;

/// Per-processor data.
static mut CPUS: [Cpu; CPU_SLOTS] = [NEW_CPU; CPU_SLOTS];

/// Interrupt and syscall stacks. Boot's copy of BootInfo is on the boot stack, not on these.
/// design/test-guest-memory/.
const KERNEL_STACK_SIZE: usize = 64 * 1024;

/// Per-processor data for a CPU.
#[repr(C, align(4096))]
pub struct Cpu {
    /// A pointer to ourselves, the first field, so that a core can load its block's address from
    /// the block.
    pub self_ptr: *const Cpu,

    /// The CPU's index.
    pub id: usize,

    /// The state of the parked thread.
    pub parked: Registers,

    /// The context switch decision upon exiting the kernel.
    pub switch_decision: SwitchDecision,

    /// What this core's instruction set keeps per core.
    pub arch: arch::CoreState,

    pub syscall_stack: KernelStack,

    /// The stack pointer for syscalls.
    ///
    /// We do not support nested syscalls.
    pub syscall_sp: u64,
}

/// A stack. Its top must be 16-byte aligned: a byte array alone could leave the syscall stack
/// pointer misaligned.
#[repr(C, align(16))]
pub struct Stack<const SZ: usize>([u8; SZ]);

/// A stack the kernel runs on after it has left its boot stack.
pub type KernelStack = Stack<KERNEL_STACK_SIZE>;

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
            arch: arch::CoreState::new(),
            syscall_stack: KernelStack::new(),
            syscall_sp: 0,
        }
    }
}

/// Returns a handle to the current CPU's data structure.
pub fn get_current() -> &'static mut Cpu {
    unsafe { &mut *arch::core_pointer() }
}

/// Returns the current CPU ID.
pub fn get_cpu_id() -> usize {
    unsafe { (*arch::core_pointer()).id }
}

/// Initialize the CPU-local data structure.
///
/// This should only be called once.
pub unsafe fn init_cpu(cpu_id: usize) {
    assert!(cpu_id < CPU_SLOTS);
    let cpu = &mut CPUS[cpu_id];
    let address = cpu as *const Cpu;

    log::debug!("CPU{} @ {:?}", cpu_id, address);

    cpu.self_ptr = address;
    cpu.id = cpu_id;
    cpu.syscall_sp = cpu.syscall_stack.bottom() as u64;

    arch::set_core_pointer(address);
}

/// Spins until `done`. Whether it spins at all depends on how far another core has got, so the loop
/// is left out of coverage, which would otherwise differ between two boots of one build.
#[coverage(off)]
pub fn spin_until(done: impl Fn() -> bool) {
    while !done() {
        core::hint::spin_loop();
    }
}
