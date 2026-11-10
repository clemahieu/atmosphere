//! The per-core block.
//!
//! Each core has a [`Cpu`]. The arch module keeps the pointer through which a core finds its own
//! (`arch::set_core_pointer`, `arch::core_pointer`) and adds the state its instruction set needs
//! (`arch::CoreState`). design/one-lock-bounded-steps/ says what may live here, outside the lock.

use core::ptr;

use crate::arch;
use verified::arch::Registers;

const NEW_CPU: Cpu = Cpu::new();

/// Slots for the CPUs the kernel runs: CPU 0 and the second core `start_second_core` starts.
/// design/test-guest-memory/.
const CPU_SLOTS: usize = 2;

/// Per-processor data.
static mut CPUS: [Cpu; CPU_SLOTS] = [NEW_CPU; CPU_SLOTS];

/// Interrupt and syscall stacks. Boot's copy of BootInfo is on the boot stack, not on these.
/// design/test-guest-memory/.
const KERNEL_STACK_SIZE: usize = 64 * 1024;

/// The syscall stack. small_syscall_stack makes it shallower than a syscall, so that
/// tools/check-boot-stack.py can force an overflow into its guard.
#[cfg(not(feature = "small_syscall_stack"))]
const SYSCALL_STACK_SIZE: usize = KERNEL_STACK_SIZE;
#[cfg(feature = "small_syscall_stack")]
const SYSCALL_STACK_SIZE: usize = 1024;

/// The guard under a stack: one page, which a frame cannot jump, since the kernel probes every page
/// of a frame larger than one.
const GUARD_SIZE: usize = 4096;

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

    /// What this core's instruction set keeps per core.
    pub arch: arch::CoreState,

    pub syscall_stack: Stack<SYSCALL_STACK_SIZE>,

    /// The stack pointer for syscalls.
    ///
    /// We do not support nested syscalls.
    pub syscall_sp: u64,
}

/// A stack with its guard page under it. The guard is a page of its own, which [`guard_stacks`]
/// unmaps so that a stack that runs off its end faults there instead of writing over what lies
/// below. Its top is 16-byte aligned, as the stack pointer must be, since the stack starts on a
/// page and its size is a multiple of 16.
#[repr(C, align(4096))]
pub struct Stack<const SZ: usize> {
    guard: [u8; GUARD_SIZE],
    bytes: [u8; SZ],
}

/// A stack the kernel runs on after it has left its boot stack.
pub type KernelStack = Stack<KERNEL_STACK_SIZE>;

impl<const SZ: usize> Stack<SZ> {
    const ALIGNED: () = assert!(SZ % 16 == 0);

    pub const fn new() -> Self {
        let () = Self::ALIGNED;
        Self { guard: [0u8; GUARD_SIZE], bytes: [0u8; SZ] }
    }

    /// The stack's top, where a push starts.
    pub fn bottom(&self) -> *const u8 {
        unsafe { self.bytes.as_ptr().add(SZ) }
    }

    /// The stack's lowest address, the end of its guard.
    pub fn lowest(&self) -> *const u8 {
        self.bytes.as_ptr()
    }

    /// The guard page's address.
    pub fn guard(&self) -> *const u8 {
        self.guard.as_ptr()
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
            arch: arch::CoreState::new(),
            syscall_stack: Stack::new(),
            syscall_sp: 0,
        }
    }
}

/// Unmaps the guard under every stack in every slot's block: the syscall stack and the stacks the
/// instruction set's share holds. Once, on the boot core, before another core starts.
pub unsafe fn guard_stacks() {
    for cpu in &*(&raw const CPUS) {
        arch::guard(cpu.syscall_stack.guard());
        for stack in cpu.arch.stacks() {
            arch::guard(stack.guard());
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
