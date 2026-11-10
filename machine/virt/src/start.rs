//! Starts a second core: PSCI CPU_ON, and the entry the core runs from there to the kernel.
//! design/machine-glue-below-the-kernel/.
//!
//! Written from the Arm Power State Coordination Interface (DEN 0022F.b), cited as PSCI, and the Arm
//! ARM (DDI 0487 M.d). A core CPU_ON starts is at EL1 on SP_EL1 with every interrupt masked,
//! translation and the caches off, and the caller's context word in x0 (PSCI 6.4). With translation
//! off every address is its own, a data access is a device access the caches do not serve, and an
//! instruction is fetched uncached while SCTLR_EL1.I is clear (Arm ARM D8.2.12.1). So the entry is
//! code that runs wherever it lies and reads one block of memory, the kernel is mapped at its own
//! addresses in the table it starts a core through, and the core that calls CPU_ON cleans the
//! entry and the block to memory first.

#[cfg(target_arch = "aarch64")]
use core::arch::global_asm;
#[cfg(target_arch = "aarch64")]
use core::mem::offset_of;
use core::mem::size_of;

use crate::instruction::{clean, hvc, read, System};
use crate::interrupt::affinity;

/// CPU_ON's function id, in the form whose arguments are 64 bits. PSCI 5.1.4.
const CPU_ON: u32 = 0xc400_0003;

/// What a PSCI function returns when it did what it was asked. PSCI 5.2.2, Table 5.
const SUCCESS: i64 = 0;

/// What the entry reads, at the address CPU_ON hands it as its context: the top of the core's
/// stack, less this block. The stack grows over it once the entry has read it.
#[repr(C)]
struct Start {
    /// TCR_EL1, MAIR_EL1 and SCTLR_EL1 as the core that called CPU_ON has them.
    translation_control: u64,
    memory_attributes: u64,
    system_control: u64,
    /// TTBR0_EL1.
    root: u64,
    /// The stack's top.
    stack: u64,
    /// The kernel's entry and its argument.
    entry: u64,
    cpu: u64,
}

// The entry, with the block's address in x0. It loads the translation control, the memory
// attributes and the root table, drops what the TLB holds, which a reset may leave as anything
// (Arm ARM D8.16.1), and reads the rest of the block while a data access still goes to memory.
// Then it turns translation on with the calling core's system control, and the instructions after
// the ISB are fetched through the table, at the addresses they were fetched from without it. It
// calls the kernel on the core's stack with no frame and no return address above it. A change to a
// system register binds the instructions after the next ISB (Arm ARM B2.6.1).
#[cfg(target_arch = "aarch64")]
global_asm!(
    r#"
    .pushsection .text.virt_core_entry, "ax"
    .balign 4
    .global virt_core_entry
    .global virt_core_entry_end
    .hidden virt_core_entry
    .hidden virt_core_entry_end
    virt_core_entry:
    ldr x1, [x0, #{translation_control}]
    msr TCR_EL1, x1
    ldr x1, [x0, #{memory_attributes}]
    msr MAIR_EL1, x1
    ldr x1, [x0, #{root}]
    msr TTBR0_EL1, x1
    isb
    tlbi vmalle1
    dsb nsh
    isb
    ldr x1, [x0, #{system_control}]
    ldr x2, [x0, #{stack}]
    ldr x3, [x0, #{entry}]
    ldr x0, [x0, #{cpu}]
    msr SCTLR_EL1, x1
    isb
    mov sp, x2
    mov x29, #0
    mov x30, #0
    br x3
    virt_core_entry_end:
    .popsection
    "#,
    translation_control = const offset_of!(Start, translation_control),
    memory_attributes = const offset_of!(Start, memory_attributes),
    system_control = const offset_of!(Start, system_control),
    root = const offset_of!(Start, root),
    stack = const offset_of!(Start, stack),
    entry = const offset_of!(Start, entry),
    cpu = const offset_of!(Start, cpu),
);

/// SP is 16-byte aligned whenever it is the base of an access, which SCTLR_EL1.SA checks. Arm ARM
/// D1.4.10.
const STACK_ALIGNMENT: u64 = 16;

/// CPU_ON's target_cpu for core `cpu`: the affinity fields of its MPIDR_EL1, Aff0 in bits 7:0 and
/// Aff1 in bits 15:8, with Aff2, Aff3 and every other bit zero. PSCI 5.1.4.
const fn target(cpu: usize) -> u64 {
    let (cluster, place) = affinity(cpu);
    cluster << 8 | place
}

/// Where the entry lies, and its size in bytes.
#[cfg(target_arch = "aarch64")]
fn entry_code() -> (usize, usize) {
    unsafe extern "C" {
        fn virt_core_entry();
        fn virt_core_entry_end();
    }
    let start = virt_core_entry as *const () as usize;
    (start, virt_core_entry_end as *const () as usize - start)
}

/// A word that stands for the entry where it cannot run.
#[cfg(not(target_arch = "aarch64"))]
fn entry_code() -> (usize, usize) {
    static ENTRY: u32 = 0;
    (&raw const ENTRY as usize, size_of::<u32>())
}

/// Starts `cpu` on the stack that ends at `stack`, translating through `root`, at `entry` with `cpu`
/// as its argument. Returns once the firmware has taken the call; the core runs when the firmware
/// gets to it. A refusal is logged and the core does not start.
///
/// # Safety
///
/// The stack is the new core's alone, and `root` maps the kernel, the stack and this crate's
/// devices at the addresses the calling core has them.
pub unsafe fn start(cpu: usize, stack: u64, entry: extern "C" fn(u64) -> !, root: u64) {
    let target = target(cpu);
    assert!(stack % STACK_ALIGNMENT == 0, "a stack's top is 16-byte aligned");
    let block = (stack as usize - size_of::<Start>()) as *mut Start;
    block.write(Start {
        translation_control: read(System::Tcr),
        memory_attributes: read(System::Mair),
        system_control: read(System::Sctlr),
        root,
        stack,
        entry: entry as usize as u64,
        cpu: cpu as u64,
    });
    let (code, bytes) = entry_code();
    clean(code, bytes);
    clean(block as usize, size_of::<Start>());
    let status = hvc(CPU_ON, [target, code as u64, block as u64]);
    if status != SUCCESS {
        log::error!("CPU_ON did not start CPU {}: the firmware returned {}", cpu, status);
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::{entry_code, start, Start};
    use crate::instruction::{answer, events, set, Event, System};

    extern "C" fn kernel_entry(_: u64) -> ! {
        unreachable!()
    }

    /// A stack of `words`, 16-byte aligned, and the address past its last word.
    fn stack(words: usize) -> (std::vec::Vec<u128>, u64) {
        let stack = vec![0u128; words / 2];
        let top = stack.as_ptr_range().end as u64;
        (stack, top)
    }

    /// The word of `stack` that lies `below` bytes under its top.
    fn word(stack: &[u128], top: u64, below: u64) -> u64 {
        assert_eq!(stack.as_ptr_range().end as u64, top);
        unsafe { ((top - below) as *const u64).read() }
    }

    #[test]
    fn cpu_on_gets_the_core_the_entry_and_the_block_in_that_order() {
        let (_stack, top) = stack(64);
        let (code, bytes) = entry_code();

        unsafe { start(1, top, kernel_entry, 0x4000_0000) };

        let block = top - 56;
        let events = events();
        // PSCI 5.1.4: CPU_ON is 0xC400 0003 in the form with 64-bit arguments, which are target_cpu,
        // entry_point_address and context_id; 5.2.1: in X1 to X3. 5.6.2: the entry's address is
        // physical as the caller sees it, and the context is the caller's own.
        assert_eq!(
            events.last(),
            Some(&Event::Hvc { function: 0xc400_0003, arguments: [1, code as u64, block] })
        );
        // The entry and the block are in memory before the firmware can start the core: it runs with
        // the caches off (PSCI 6.4.3.4).
        assert_eq!(
            events[events.len() - 3..events.len() - 1],
            [Event::Clean { start: code, bytes }, Event::Clean { start: block as usize, bytes: 56 }]
        );
        assert_eq!(events.iter().filter(|event| matches!(event, Event::Hvc { .. })).count(), 1);
    }

    #[test]
    fn the_block_under_the_stack_s_top_holds_what_the_calling_core_translates_by() {
        let (stack, top) = stack(64);
        set(System::Tcr, 0x0000_01b5_0080_3510);
        set(System::Mair, 0xff);
        set(System::Sctlr, 0x30d0_1805);

        unsafe { start(1, top, kernel_entry, 0x4123_4000) };

        assert_eq!(core::mem::size_of::<Start>(), 56);
        assert_eq!(word(&stack, top, 56), 0x0000_01b5_0080_3510);
        assert_eq!(word(&stack, top, 48), 0xff);
        assert_eq!(word(&stack, top, 40), 0x30d0_1805);
        assert_eq!(word(&stack, top, 32), 0x4123_4000);
        assert_eq!(word(&stack, top, 24), top);
        assert_eq!(word(&stack, top, 16), kernel_entry as *const () as u64);
        assert_eq!(word(&stack, top, 8), 1);
        // The registers are read, never written: the calling core keeps what it runs with.
        assert!(events().iter().all(|event| !matches!(event, Event::Write { .. })));
    }

    #[test]
    fn the_target_is_the_core_s_affinity_as_mpidr_holds_it() {
        // PSCI 5.1.4: target_cpu has Aff0 in bits 7:0 and Aff1 in bits 15:8. QEMU virt's device tree
        // names core n `reg = <n / 16 << 8 | n % 16>`.
        for (cpu, target) in [(0, 0x000), (1, 0x001), (15, 0x00f), (16, 0x100), (17, 0x101), (31, 0x10f)] {
            let (stack, top) = stack(64);
            unsafe { start(cpu, top, kernel_entry, 0) };
            let Some(Event::Hvc { arguments, .. }) = events().pop() else { panic!("no call for core {}", cpu) };
            assert_eq!(arguments[0], target);
            assert_eq!(word(&stack, top, 8), cpu as u64);
        }
    }

    #[test]
    fn a_refusal_leaves_the_core_off_and_returns() {
        let (_stack, top) = stack(64);
        // PSCI 5.2.2, Table 5: INVALID_PARAMETERS, which CPU_ON returns for a core the machine does
        // not have (5.6.2).
        answer(-2);

        unsafe { start(1, top, kernel_entry, 0) };

        assert_eq!(events().iter().filter(|event| matches!(event, Event::Hvc { .. })).count(), 1);
    }

    #[test]
    #[should_panic(expected = "cpu < MAX_CPUS")]
    fn a_core_past_the_last_this_crate_names_is_a_bug() {
        let (_stack, top) = stack(64);
        unsafe { start(32, top, kernel_entry, 0) };
    }

    #[test]
    #[should_panic(expected = "a stack's top is 16-byte aligned")]
    fn a_stack_whose_top_is_not_aligned_is_a_bug() {
        let (_stack, top) = stack(64);
        unsafe { start(1, top - 8, kernel_entry, 0) };
    }
}
