//! Syscalls.

use core::arch::{asm, global_asm, naked_asm};

use memoffset::offset_of;
use crate::arch::{msr, CoreState, Ring, SegmentSelector};

use crate::cpu::Cpu;
use crate::arch::gdt::GlobalDescriptorTable;
use crate::thread::SwitchDecision;
use verified::capability::{boot, inspect, operation, table};
use verified::arch::Registers;

/// Flags cleared on syscall entry. The kernel is not preemptible, so IF. Compiled code assumes DF is
/// clear. TF would trap on the first kernel instruction, on the user's stack. AC and NT must not reach
/// kernel code or an iretq. The return path restores the process's own flags.
const ENTRY_FLAG_MASK: u32 = (1 << 8) | (1 << 9) | (1 << 10) | (1 << 14) | (1 << 18);

const SYSCALL32_ENTRY: u64 = 0; // nein
const SYSCALL32_ENTRY_EIP: u32 = 0; // nein

// User space invokes operations by asys's numbers, reads asys's statuses and kind numbers, names a slot below asys's
// table size, encodes a table position as asys does and finds its first capabilities at asys's slots; they must be the
// ones the verified dispatch decodes and returns and boot writes.
const _: () = {
    use asys::operation as user;
    assert!(user::STATUS_OK == operation::STATUS_OK);
    assert!(user::STATUS_REFUSED == operation::STATUS_REFUSED);
    assert!(user::STATUS_UNKNOWN == operation::STATUS_UNKNOWN);
    assert!(user::STATUS_AGAIN == operation::STATUS_AGAIN);
    assert!(user::RETYPE == operation::OPERATION_RETYPE);
    assert!(user::DERIVE == operation::OPERATION_DERIVE);
    assert!(user::MOVE == operation::OPERATION_MOVE);
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
    assert!(user::INSPECT == operation::OPERATION_INSPECT);
    assert!(user::LINK == operation::OPERATION_LINK);
    assert!(user::PROBE == operation::OPERATION_PROBE);
    assert!(user::POWER_OFF == operation::OPERATION_POWER_OFF);
    assert!(user::PROBE_MAX == verified::capability::probe::PROBE_MAX);
    assert!(user::RETYPE_FRAME == operation::RETYPE_FRAME);
    assert!(user::RETYPE_LARGE_FRAME == operation::RETYPE_LARGE_FRAME);
    assert!(user::RETYPE_TABLE_PAGE == operation::RETYPE_TABLE_PAGE);
    assert!(user::RETYPE_LEAF == operation::RETYPE_LEAF);
    assert!(user::POSITION_THROUGH_SHIFT == verified::capability::position::POSITION_THROUGH_SHIFT);
    assert!(user::POSITION_WIDTH == verified::capability::position::POSITION_WIDTH);
    assert!(user::TABLE_INDICES - 1 == verified::capability::position::POSITION_INDEX_MASK);
    assert!(user::TABLE_INDICES == table::TABLE_INDICES as u64);
    assert!(user::KIND_UNTYPED == inspect::CAP_KIND_UNTYPED);
    assert!(user::KIND_FRAME == inspect::CAP_KIND_FRAME);
    assert!(user::KIND_PROCESS == inspect::CAP_KIND_PROCESS);
    assert!(user::KIND_THREAD == inspect::CAP_KIND_THREAD);
    assert!(user::KIND_ENDPOINT == inspect::CAP_KIND_ENDPOINT);
    assert!(user::KIND_REPLY == inspect::CAP_KIND_REPLY);
    assert!(user::KIND_NOTIFICATION == inspect::CAP_KIND_NOTIFICATION);
    assert!(user::KIND_SPACE == inspect::CAP_KIND_SPACE);
    assert!(user::KIND_DEVICE == inspect::CAP_KIND_DEVICE);
    assert!(user::KIND_CONSOLE == inspect::CAP_KIND_CONSOLE);
    assert!(user::KIND_POWER == inspect::CAP_KIND_POWER);
    assert!(user::ROOT_PROCESS_SLOT == boot::ROOT_PROCESS_SLOT as u64);
    assert!(user::ROOT_THREAD_SLOT == boot::ROOT_THREAD_SLOT as u64);
    assert!(user::ROOT_CONSOLE_SLOT == boot::ROOT_CONSOLE_SLOT as u64);
    assert!(user::ROOT_POWER_SLOT == boot::ROOT_POWER_SLOT as u64);
    assert!(user::ROOT_UNTYPED_SLOT == boot::ROOT_UNTYPED_SLOT as u64);
    assert!(user::ROOT_FRAME_SLOT == boot::ROOT_FRAME_SLOT as u64);
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

// The frame holds the operation and its arguments, which the dispatch reads from it.
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

// In a debug build, stop if a syscall reaches its handler with a flag from ENTRY_FLAG_MASK set.
#[cfg(debug_assertions)]
global_asm!(
    ".macro check_entry_flags",
    "pushfq",
    "pop r10",        // free here: the frame already holds it
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
// The handler takes only the frame, which holds the operation number, the capability's slot and the
// arguments at the positions the arch module's syscall register table names,
// design/syscall-abi-in-registers/. Every name a process passes resolves within the caller's kernel
// instance, so the ABI has no machine-wide names. Why, and what to do about an operation that needs
// one: design/one-kernel-instance/.
//
// All caller-saved registers are considered clobbered once invoked
//
// The handler always writes the status word over the operation number in the frame, and the result
// words over the slot and the arguments, each at its position.
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

        // The dispatch: one handler, given the frame as its argument.
        "mov rdi, rsp",
        "check_entry_flags",
        "call {capability_entry}",

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
        // Path 2 returns the frame's rdi, rsi, rdx and r8, where the handler
        // wrote the invocation's result words.

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

        // skip r15~r10 (8 registers)
        "mov r8, [rsp + 8*9]",   // r8
        // skip rcx
        "mov rdx, [rsp + 8*11]", // rdx
        "mov rsi, [rsp + 8*12]", // rsi
        "mov rdi, [rsp + 8*13]", // rdi
        "mov rax, [rsp + 8*14]", // rax
        // skip error_code
        "mov rcx, [rsp + 8*16]", // rip
        // skip cs
        "mov r11, [rsp + 8*18]", // rflags
        "mov rsp, [rsp + 8*19]", // rsp

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
        user_rsp_offset = const offset_of!(Cpu, arch) + offset_of!(CoreState, user_rsp),

        switch_decision_offset = const offset_of!(Cpu, switch_decision),
        decision_no_switching = const SwitchDecision::NoSwitching as u64,
        decision_switch_to_preempted = const SwitchDecision::SwitchToPreempted as u64,
        capability_entry = sym capability_entry,
    );
}

/// The handler. The verified dispatch runs the invocation for the core's current thread and decides
/// the status and result words that return. A power-off it accepted ends the run here and returns to
/// no thread.
extern "C" fn capability_entry(regs: &mut Registers) {
    use crate::bridge::Bridge;
    use crate::capability::{power_off_accepted, CAP_KERNEL};
    use verified::bridge::TrustedBridge;

    let returned = CAP_KERNEL
        .lock()
        .as_deref_mut()
        .expect("a syscall before the capability kernel was built")
        .dispatch(crate::cpu::get_cpu_id(), *regs)
        .expect("no operation is wired that moves the calling thread off its core");
    match returned.status {
        operation::STATUS_OK
        | operation::STATUS_REFUSED
        | operation::STATUS_UNKNOWN
        | operation::STATUS_AGAIN => {}
        status => unreachable!("dispatch returned status {status}, which no operation returns"),
    }
    // The statement that ran the dispatch released the kernel's lock when it ended.
    if let Some(success) = power_off_accepted(regs, &returned) {
        unsafe { crate::machine::shutdown(success) }
    }
    regs.write_outcome(returned);
    Bridge::set_switch_decision(SwitchDecision::NoSwitching);
}
