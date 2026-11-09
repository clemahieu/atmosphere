//! Syscalls.

use core::arch::{asm, global_asm, naked_asm};

#[cfg(not(feature = "capability"))]
use asys::MAX_SYSCALLS;
use memoffset::offset_of;
use crate::arch::{msr, Ring, SegmentSelector};

use crate::cpu::Cpu;
use crate::gdt::GlobalDescriptorTable;
#[cfg(not(feature = "capability"))]
use crate::kernel;
use crate::thread::SwitchDecision;
use verified::capability::{boot, operation};
use verified::trap::Registers;

/// Flags cleared on syscall entry. The kernel is not preemptible, so IF. Compiled code assumes DF is
/// clear. TF would trap on the first kernel instruction, on the user's stack. AC and NT must not reach
/// kernel code or an iretq. The return path restores the process's own flags.
const ENTRY_FLAG_MASK: u32 = (1 << 8) | (1 << 9) | (1 << 10) | (1 << 14) | (1 << 18);

const SYSCALL32_ENTRY: u64 = 0; // nein
const SYSCALL32_ENTRY_EIP: u32 = 0; // nein

// Every name a process passes through these calls resolves within the caller's kernel instance, so
// the ABI has no machine-wide names. Why, and what to do about a call that needs one: design/one-kernel-instance/.
#[cfg(not(feature = "capability"))]
static mut SYSCALLS: [u64; MAX_SYSCALLS] = [0; MAX_SYSCALLS];

// sys_entry calls handlers with the C convention, so the six argument entry must declare it.
#[cfg(not(feature = "capability"))]
const _: extern "C" fn(usize, usize, usize, &mut Registers, usize, usize) = kernel::sys_new_proc;

// User space invokes operations by asys's numbers, reads asys's statuses and finds its first capabilities
// at asys's slots; they must be the ones the verified dispatch decodes and returns and boot writes.
const _: () = {
    use asys::operation as user;
    assert!(user::STATUS_OK == operation::STATUS_OK);
    assert!(user::STATUS_REFUSED == operation::STATUS_REFUSED);
    assert!(user::STATUS_UNKNOWN == operation::STATUS_UNKNOWN);
    assert!(user::RETYPE == operation::OPERATION_RETYPE);
    assert!(user::DERIVE == operation::OPERATION_DERIVE);
    assert!(user::MOVE == operation::OPERATION_MOVE);
    assert!(user::CLAIM == operation::OPERATION_CLAIM);
    assert!(user::DELETE == operation::OPERATION_DELETE);
    assert!(user::REVOKE == operation::OPERATION_REVOKE);
    assert!(user::MAP == operation::OPERATION_MAP);
    assert!(user::UNMAP == operation::OPERATION_UNMAP);
    assert!(user::DESTROY == operation::OPERATION_DESTROY);
    assert!(user::SEND == operation::OPERATION_SEND);
    assert!(user::RECEIVE == operation::OPERATION_RECEIVE);
    assert!(user::CALL == operation::OPERATION_CALL);
    assert!(user::REPLY_RECV == operation::OPERATION_REPLY_RECV);
    assert!(user::PRINT == operation::OPERATION_PRINT);
    assert!(user::ROOT_PROCESS_SLOT == boot::ROOT_PROCESS_SLOT as u64);
    assert!(user::ROOT_THREAD_SLOT == boot::ROOT_THREAD_SLOT as u64);
    assert!(user::ROOT_CONSOLE_SLOT == boot::ROOT_CONSOLE_SLOT as u64);
};

/// Initializes syscalls.
///
/// This must be called only once for each CPU reset.
pub unsafe fn init_cpu() {
    use GlobalDescriptorTable as GDT;

    // syscall loads CS from this selector and SS from the next entry.
    let syscall_seg = SegmentSelector::new(GDT::KERNEL_CODE_INDEX, Ring::Ring0);
    // sysret loads SS from the next entry and CS from the one after, with no look at the GDT, so
    // these must be the selectors an iretq back to a process finds there.
    let sysret_seg = SegmentSelector::new(GDT::USER_DATA_INDEX - 1, Ring::Ring3);
    const _: () = assert!(GDT::USER_DATA_INDEX + 1 == GDT::USER_CODE_INDEX);

    // Set STAR
    let star = ((sysret_seg.bits() as u64) << 48)
        | ((syscall_seg.bits() as u64) << 32)
        | (SYSCALL32_ENTRY_EIP as u64);
    msr::wrmsr(msr::STAR, star);

    // Set LSTAR - 64-bit syscall entry
    msr::wrmsr(msr::LSTAR, sys_entry as *const () as u64);

    // Set LSTAR - 32-bit syscall entry
    msr::wrmsr(msr::CSTAR, SYSCALL32_ENTRY);

    msr::wrmsr(msr::SF_MASK, ENTRY_FLAG_MASK as u64);

    msr::wrmsr(msr::EFER, msr::rdmsr(msr::EFER) | msr::EFER_SCE);

    #[cfg(not(feature = "capability"))]
    register_handlers();
}

/// Fills the old kernel's table of handlers, which its entry indexes by the number in rax.
#[cfg(not(feature = "capability"))]
unsafe fn register_handlers() {
    SYSCALLS[asys::__NR_PRINT] = kernel::sys_print as *const () as u64;
    SYSCALLS[asys::__NR_MMAP] = kernel::sys_mmap as *const () as u64;
    SYSCALLS[asys::__NR_MRESOLVE] = kernel::sys_resolve as *const () as u64;
    SYSCALLS[asys::__NR_MRESOLVE_IO] = kernel::sys_resolve_io as *const () as u64;
    SYSCALLS[asys::__NR_NEW_END] = kernel::sys_new_endpoint as *const () as u64;
    SYSCALLS[asys::__NR_NEW_PROC] = kernel::sys_new_proc as *const () as u64;
    SYSCALLS[asys::__NR_NEW_THREAD] = kernel::sys_new_thread as *const () as u64;
    SYSCALLS[asys::__NR_LOG] = kernel::sys_log as *const () as u64;
    SYSCALLS[asys::__NR_RECEIVE_EMPTY] = kernel::sys_receive_empty as *const () as u64;
    SYSCALLS[asys::__NR_IO_MMAP] = kernel::sys_iommu_mmap as *const () as u64;
    SYSCALLS[asys::__NR_SET_DEVICE_IOMMU] = kernel::sys_set_device_iommu as *const () as u64;
    SYSCALLS[asys::__NR_INVALIDATE_IOTLB] = sys_invalidate_iotlb as *const () as u64;
    SYSCALLS[asys::__NR_SEND_EMPTY_TRY_SCH] = kernel::sys_send_empty_try_schedule as *const () as u64;
}

/// Enters the thread whose frame is `regs` from an idle core, as a syscall return to it would. It
/// clears the caller-saved registers for the same reason: a process must not see them.
pub unsafe fn enter_thread(regs: &Registers) -> ! {
    asm!(
        "mov rsp, {regs}",
        "mov r15, [rsp + 8*0]",
        "mov r14, [rsp + 8*1]",
        "mov r13, [rsp + 8*2]",
        "mov r12, [rsp + 8*3]",
        "mov rbp, [rsp + 8*4]",
        "mov rbx, [rsp + 8*5]",
        "mov rax, [rsp + 8*14]",
        "mov rcx, [rsp + 8*16]", // rip
        "mov r11, [rsp + 8*18]", // rflags
        "mov rsp, [rsp + 8*19]", // rsp
        "xor edi, edi",
        "xor esi, esi",
        "xor edx, edx",
        "xor r8d, r8d",
        "xor r9d, r9d",
        "xor r10d, r10d",
        "sysretq",
        regs = in(reg) regs as *const Registers,
        options(noreturn),
    )
}

#[cfg(all(not(feature = "capability"), debug_assertions))]
global_asm!(
    ".macro push_caller_saved",
    "push 0",         // rax
    "push 0",         // rdi
    "push 0",         // rsi
    "push 0",         // rdx
    "push 0",         // rcx (taken by original rip)
    "push 0",         // r8
    "push 0",         // r9
    "push 0",         // r10
    "push 0",         // r11 (taken by original rflags across syscall)
    ".endm",
);

#[cfg(all(not(feature = "capability"), not(debug_assertions)))]
global_asm!(
    ".macro push_caller_saved",
    "push 0",         // rax: the one slot a return path reads
    "sub rsp, 8*8",
    ".endm",
);

// The capability kernel's frame holds the operation and its arguments, which the dispatch reads from it.
#[cfg(feature = "capability")]
global_asm!(
    ".macro push_caller_saved",
    "push rax",       // rax: the operation
    "push rdi",       // rdi: the capability's slot
    "push rsi",
    "push rdx",
    "push 0",         // rcx (taken by original rip)
    "push r8",
    "push r9",
    "push r10",
    "push 0",         // r11 (taken by original rflags across syscall)
    ".endm",
);

// The old kernel's dispatch: the handler the table holds for the number in rax, called with the
// arguments in place and the frame in rcx, or -1 in the frame's rax when there is none.
#[cfg(not(feature = "capability"))]
global_asm!(
    ".macro dispatch",
    "cmp rax, {max_syscalls}",
    "jae 2f",
    "shl rax, 3",
    "lea r11, [rip + {syscalls}]",
    "add r11, rax",
    "mov r11, [r11]",
    "cmp r11, 0",
    "jz 2f",
    // handler(arg1, arg2, arg3, registers, arg4, arg5)
    // rdi, rsi, rdx, (rcx), r8, r9
    "check_entry_flags",
    "call r11",
    "jmp 3f",
    "2:",
    "mov qword ptr [rsp + 8*14], -1", // rax: the return paths reload it from the frame
    "3:",
    ".endm",
    max_syscalls = const MAX_SYSCALLS,
    syscalls = sym SYSCALLS,
);

// The capability kernel's dispatch: one handler, given the frame in rcx.
#[cfg(feature = "capability")]
global_asm!(
    ".macro dispatch",
    "mov rdi, rcx",
    "check_entry_flags",
    "call {capability_entry}",
    ".endm",
    capability_entry = sym capability_entry,
);

// In a debug build, stop if a syscall reaches its handler with a flag from ENTRY_FLAG_MASK set. r10 is
// free here: no handler takes an argument in it, and the capability kernel's frame already holds it.
#[cfg(debug_assertions)]
global_asm!(
    ".macro check_entry_flags",
    "pushfq",
    "pop r10",
    "test r10d, {mask}",
    "jz 77f",
    "call {entered_with_flags_set}",
    "77:",
    ".endm",
    mask = const ENTRY_FLAG_MASK,
    entered_with_flags_set = sym entered_with_flags_set,
);

#[cfg(not(debug_assertions))]
global_asm!(
    ".macro check_entry_flags",
    ".endm",
);

#[cfg(debug_assertions)]
extern "C" fn entered_with_flags_set() -> ! {
    panic!("a syscall reached its handler with a masked flag set");
}

// Syscall ABI
//
// Register | User           | Kernel Handler
// ------------------------------------------
// rax      | Syscall Number | Return Value
// rdi      | Arg #1         | Arg #1
// rsi      | Arg #2         | Arg #2
// rdx      | Arg #3         | Arg #3
// rcx      | N/A            | Registers (Arg #4)
// r8       | Arg #4         | Arg #5
// r9       | Arg #5         | Arg #6
//
// That table is the old kernel's. The capability kernel's handler takes only the frame, which holds
// the operation from rax, the capability's slot from rdi and the arguments from rsi, rdx, r8, r9 and
// r10, design/syscall-abi-in-registers/.
//
// All caller-saved registers are considered clobbered once invoked
//
// rax on return is the syscall's result. A syscall that blocked and was woken returns 0, whichever
// thread woke it, and a new thread starts with 0. The frame's rax slot starts at 0 on every entry, so
// a saved frame never carries a value from an earlier syscall on this core's stack. The capability
// kernel's entry saves the operation and its arguments there instead, and its handler always writes
// the status over the operation.
#[unsafe(naked)]
unsafe extern "C" fn sys_entry() -> ! {
    naked_asm!(
        // We may not have a valid rsp. Every register but rcx and r11 still holds the user's value,
        // so the user's rsp waits in the Cpu while the stack switches.

        "mov gs:{user_rsp_offset}, rsp",
        "mov rsp, gs:{syscall_sp_offset}",

        // Here we construct the Registers struct and only save
        // a subset of registers
        "push {user_ss}", // ss
        "push qword ptr gs:{user_rsp_offset}", // rsp
        "push r11",       // rflags
        "push {user_cs}", // cs
        "push rcx",       // rip
        "push 0",         // error_code

        "push_caller_saved",

        "push rbx",       // rbx
        "push rbp",       // rbp
        "push r12",       // r12
        "push r13",       // r13
        "push r14",       // r14
        "push r15",       // r15

        "mov rcx, rsp",

        "dispatch",

        // Cleanup

        // Three cases:
        // 1. Switch to another thread that was suspended due to a syscall
        //    ("clean" thread)
        // 2. Return to the same thread
        // 3. Switch to a different preempted thread
        //
        // For 1, we can directly skip over restoring most registers since
        // we trust the handler to have already restored callee-saved registers
        //
        // Paths 1 and 2 restore only part of the frame, so they clear the
        // caller-saved registers the handler used: a process must not see them.

        "mov r10, gs:{switch_decision_offset}",
        "cmp r10, {decision_no_switching}",
        "je 22f",
        "cmp r10, {decision_switch_to_preempted}",
        "je 23f",

        // 1. Switch to another clean thread
        // Fast return that clobbers rcx, r11
        "21:",

        "mov r15, [rsp + 8*0]",
        "mov r14, [rsp + 8*1]",
        "mov r13, [rsp + 8*2]",
        "mov r12, [rsp + 8*3]",
        "mov rbp, [rsp + 8*4]",
        "mov rbx, [rsp + 8*5]",
        // skip r11~rdi (8 registers)
        "mov rax, [rsp + 8*14]",
        // skip error_code
        "mov rcx, [rsp + 8*16]", // rip
        // skip cs
        "mov r11, [rsp + 8*18]", // rflags
        "mov rsp, [rsp + 8*19]", // rsp

        "xor edi, edi",
        "xor esi, esi",
        "xor edx, edx",
        "xor r8d, r8d",
        "xor r9d, r9d",
        "xor r10d, r10d",

        "sti",
        "sysretq",

        // 2. Return to the same thread
        "22:",

        // skip r15~rdi (14 registers)
        "mov rax, [rsp + 8*14]", // rax
        // skip error_code
        "mov rcx, [rsp + 8*16]", // rip
        // skip cs
        "mov r11, [rsp + 8*18]", // rflags
        "mov rsp, [rsp + 8*19]", // rsp

        "xor edi, edi",
        "xor esi, esi",
        "xor edx, edx",
        "xor r8d, r8d",
        "xor r9d, r9d",
        "xor r10d, r10d",

        "sti",
        "sysretq",

        // 3. Switch to a preempted thread (slow)
        "23:",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbp",
        "pop rbx",
        "pop r11",
        "pop r10",
        "pop r9",
        "pop r8",
        "pop rcx",
        "pop rdx",
        "pop rsi",
        "pop rdi",
        "pop rax",
        "add rsp, 8",
        "iretq",

        user_ss = const GlobalDescriptorTable::USER_SS,
        user_cs = const GlobalDescriptorTable::USER_CS,
        syscall_sp_offset = const offset_of!(Cpu, syscall_sp),
        user_rsp_offset = const offset_of!(Cpu, user_rsp),

        switch_decision_offset = const offset_of!(Cpu, switch_decision),
        decision_no_switching = const SwitchDecision::NoSwitching as u64,
        decision_switch_to_preempted = const SwitchDecision::SwitchToPreempted as u64,
    );
}

#[cfg(not(feature = "capability"))]
extern "C" fn sys_invalidate_iotlb(bus: usize, device: usize, function: usize, regs: &mut Registers, page: u64) {
    if let Ok(()) = unsafe { crate::iommu::invalidate_iotlb(bus, device, function, page) } {
        regs.rax = 0;
    } else {
        regs.rax = 1;
    }
}

/// The capability kernel's handler. The verified dispatch decides the status rax returns, and the
/// kernel logs each invocation, since no operation is wired yet to report anything itself.
#[cfg(feature = "capability")]
extern "C" fn capability_entry(regs: &mut Registers) {
    use crate::bridge::Bridge;
    use verified::bridge::TrustedBridge;

    let number = regs.rax;
    let status = operation::dispatch(number);
    let outcome = match status {
        operation::STATUS_REFUSED => "refused",
        _ => "unknown",
    };
    let arguments = [regs.rsi, regs.rdx, regs.r8, regs.r9, regs.r10];
    log::info!("capability entry: operation {} on slot {} with {:?}: {}", number, regs.rdi, arguments, outcome);
    regs.rax = status;
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}
