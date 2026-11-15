// SPDX-License-Identifier: MIT

//! Boot checks that every register the syscall ABI preserves keeps a distinct value across a
//! cheap invocation and across a timer preemption, on both targets (`design/syscall-abi-in-registers/`).
//!
//! Each pass loads a distinct sentinel into every preserved register (and user status/direction
//! flags) in assembly, runs either an `inspect` on `ROOT_CONSOLE_SLOT` or a wait loop until a peer
//! thread at priority 0 on core 0 increments its shared counter (proving a timer preemption occurred),
//! captures the returned registers and flags before any comparison alters them, and checks every
//! preserved value in Rust.

use core::arch::global_asm;
use core::ptr;

use asys::operation;

use crate::{print_parts, print_slot};

/// What dom0 prints once every register the syscall ABI preserves kept a distinct value across a
/// cheap invocation, which `tools/check-boot-log.py` looks for on both targets.
const SYSCALL_REGISTERS_HELD: [u64; 5] = operation::print_words(b"dom0 syscall registers held\n");

/// What dom0 prints once every register the syscall ABI preserves kept a distinct value across a
/// timer preemption, which `tools/check-boot-log.py` looks for on both targets.
const PREEMPTION_REGISTERS_HELD: [u64; 5] = operation::print_words(b"dom0 preemption registers held\n");

/// Writes a diagnostic message when a pass fails, keeping under `print`'s 39-byte limit.
fn report_failure(pass: &[u8], reg: &[u8], timed_out: bool) {
    if timed_out {
        print_parts(&[b"dom0 ", pass, b" regs timed out\n"]);
    } else {
        print_parts(&[b"dom0 ", pass, b" reg fail: ", reg, b"\n"]);
    }
}

#[cfg(target_arch = "x86_64")]
mod target {
    use super::*;

    /// Number of `loop` instructions per preemption poll batch (`~200 us` under KVM).
    const PREEMPT_BATCH_LOOPS: u32 = 100_000;

    /// Maximum poll batches before reporting preemption wait timeout.
    const PREEMPT_MAX_BATCHES: u32 = 50_000;

    /// Mask of RFLAGS bits that our assembly sets or clears: CF(0), PF(2), AF(4), ZF(6), SF(7),
    /// TF(8), DF(10), OF(11).
    const RFLAGS_TEST_BITS: u64 = 0xdd5;

    /// Arithmetic/status RFLAGS bits (`OF|SF|ZF|AF|PF|CF`), captured by `lahf` + `seto` before `cmp`.
    const RFLAGS_STATUS_MASK: u64 = 0x8d5;

    /// First test flag set: CF=1, bit1=1, PF=0, AF=1, ZF=0, SF=1, TF=0, IF=1, DF=1, OF=1 (`0xe93`).
    const RFLAGS_PATTERN_A: u64 = 0xe93;

    /// Complement test flag set: CF=0, bit1=1, PF=1, AF=0, ZF=1, SF=0, TF=0, IF=1, DF=0, OF=0 (`0x246`).
    const RFLAGS_PATTERN_B: u64 = 0x246;

    const NAMES: [&[u8]; 7] = [b"rbx", b"rbp", b"r12", b"r13", b"r14", b"r15", b"rsp"];

    #[repr(C)]
    struct Expected {
        gprs: [u64; 7],
        flags_set_bits: u64,
    }

    #[repr(C)]
    struct Report {
        actual_gprs: [u64; 7],
        expected_flags: u64,
        actual_flags: u64,
        timed_out: u64,
    }

    const PATTERNS: [Expected; 2] = [
        Expected {
            gprs: [
                0x1122_3344_5566_7781,
                0x2233_4455_6677_8892,
                0x3344_5566_7788_99a3,
                0x4455_6677_8899_aab4,
                0x5566_7788_99aa_bbc5,
                0x6677_8899_aabb_ccd6,
                0x0000_6789_abcd_ef70,
            ],
            flags_set_bits: RFLAGS_PATTERN_A,
        },
        Expected {
            gprs: [
                !0x1122_3344_5566_7781,
                !0x2233_4455_6677_8892,
                !0x3344_5566_7788_99a3,
                !0x4455_6677_8899_aab4,
                !0x5566_7788_99aa_bbc5,
                !0x6677_8899_aabb_ccd6,
                0x0000_1876_5432_1088,
            ],
            flags_set_bits: RFLAGS_PATTERN_B,
        },
    ];

    global_asm!(
        ".global dom0_regs_run",
        "dom0_regs_run:",
        "push rbx",
        "push rbp",
        "push r12",
        "push r13",
        "push r14",
        "push r15",
        "mov [rip + .Lx86_saved_sp], rsp",
        "mov [rip + .Lx86_report], rdi",
        "mov [rip + .Lx86_counter], rdx",

        // Compute expected RFLAGS keeping IF, IOPL, AC, ID, etc., while forcing our status/DF bits.
        "pushfq",
        "pop rax",
        "movabs rcx, {clear_mask}",
        "and rax, rcx",
        "or rax, [rsi + 56]",
        "mov [rip + .Lx86_expected_flags], rax",

        // Load expected RFLAGS before switching away from Rust's stack.
        "push rax",
        "popfq",

        // Load every preserved GPR (mov / movabs never modify RFLAGS).
        "mov rbx, [rsi + 0]",
        "mov rbp, [rsi + 8]",
        "mov r12, [rsi + 16]",
        "mov r13, [rsi + 24]",
        "mov r14, [rsi + 32]",
        "mov r15, [rsi + 40]",
        "mov rcx, [rip + .Lx86_counter]",
        "mov rsp, [rsi + 48]",

        // jrcxz and jmp neither read nor write RFLAGS; place .Lx86_do_syscall right after for rel8.
        "jrcxz .Lx86_do_syscall",
        "jmp .Lx86_do_preempt",

        ".Lx86_do_syscall:",
        "mov eax, {inspect_op}",
        "mov edi, {console_slot}",
        "mov esi, 0",
        "mov edx, 0",
        "mov r10d, 0",
        "mov r8d, 0",
        "mov r9d, 0",
        "syscall",
        "mov r9, rsp",
        "mov rsp, [rip + .Lx86_saved_sp]",
        "pushfq",
        "cld",
        "pop r11",
        "mov r10d, 0",
        "jmp .Lx86_save_report",

        // Preemption path: rcx holds counter_ptr; RFLAGS stays equal to RFLAGS_PATTERN_A throughout
        // the `loop` window where `[r10]` is sampled and checked.
        ".Lx86_do_preempt:",
        "mov r10, rcx",
        "mov eax, {max_batches}",
        "mov [rip + .Lx86_wait_batches], rax",
        ".Lx86_preempt_batch:",
        "mov al, 0x7f",
        "add al, 1", // OF=1, SF=1, ZF=0, AF=1, PF=0, CF=0
        "stc",       // CF=1
        "std",       // DF=1
        "mov rdx, [r10]",
        "mov ecx, {batch_loops}",
        "1:",
        "loop 1b",
        "lahf",      // Capture SF, ZF, AF, PF, CF before cmp.
        "seto al",   // Capture OF before cmp.
        "cmp [r10], rdx",
        "jne .Lx86_preempt_done",
        "dec qword ptr [rip + .Lx86_wait_batches]",
        "jnz .Lx86_preempt_batch",
        // Timed out:
        "mov r9, rsp",
        "mov rsp, [rip + .Lx86_saved_sp]",
        "pushfq",
        "cld",
        "pop r11",
        "mov r10d, 1",
        "jmp .Lx86_save_report",

        ".Lx86_preempt_done:",
        "mov r9, rsp",
        "mov rsp, [rip + .Lx86_saved_sp]",
        "mov r8d, eax",
        "pushfq",
        "cld",
        "pop r11",
        "movabs rax, {not_status_mask}",
        "and r11, rax",
        "mov eax, r8d",
        "and eax, 1",
        "shl eax, 11",
        "or r11, rax",
        "shr r8d, 8",
        "and r8d, 0xd5",
        "or r11, r8",
        "mov r10d, 0",
        "jmp .Lx86_save_report",

        ".Lx86_save_report:",
        "mov rax, [rip + .Lx86_report]",
        "mov [rax + 0], rbx",
        "mov [rax + 8], rbp",
        "mov [rax + 16], r12",
        "mov [rax + 24], r13",
        "mov [rax + 32], r14",
        "mov [rax + 40], r15",
        "mov [rax + 48], r9",
        "mov rcx, [rip + .Lx86_expected_flags]",
        "mov [rax + 56], rcx",
        "mov [rax + 64], r11",
        "mov [rax + 72], r10",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbp",
        "pop rbx",
        "ret",

        ".pushsection .bss.dom0_reg_scratch, \"aw\", @nobits",
        ".balign 8",
        ".Lx86_saved_sp: .quad 0",
        ".Lx86_report: .quad 0",
        ".Lx86_counter: .quad 0",
        ".Lx86_expected_flags: .quad 0",
        ".Lx86_wait_batches: .quad 0",
        ".popsection",

        clear_mask = const !RFLAGS_TEST_BITS,
        not_status_mask = const !RFLAGS_STATUS_MASK,
        max_batches = const PREEMPT_MAX_BATCHES,
        batch_loops = const PREEMPT_BATCH_LOOPS,
        inspect_op = const operation::INSPECT,
        console_slot = const operation::ROOT_CONSOLE_SLOT,
    );

    unsafe extern "C" {
        fn dom0_regs_run(report: *mut Report, expected: *const Expected, counter: *const u64);
    }

    fn run_pass(pass: &[u8], expected: &Expected, counter: *const u64) -> bool {
        let mut report = Report {
            actual_gprs: [0; 7],
            expected_flags: 0,
            actual_flags: 0,
            timed_out: 0,
        };
        unsafe { dom0_regs_run(&raw mut report, expected, counter) };
        if report.timed_out != 0 {
            report_failure(pass, b"", true);
            return false;
        }
        for (i, &name) in NAMES.iter().enumerate() {
            if report.actual_gprs[i] != expected.gprs[i] {
                report_failure(pass, name, false);
                return false;
            }
        }
        if report.actual_flags != report.expected_flags {
            report_failure(pass, b"rflags", false);
            return false;
        }
        true
    }

    pub fn syscall() -> bool {
        PATTERNS.iter().all(|expected| run_pass(b"syscall", expected, ptr::null()))
    }

    pub fn preemption(counter: *const u64) -> bool {
        run_pass(b"preemption", &PATTERNS[0], counter)
    }
}

#[cfg(target_arch = "aarch64")]
mod target {
    use super::*;

    /// Maximum poll iterations before reporting preemption wait timeout (`~0x4000_0000` spins).
    const PREEMPT_MAX_SPINS_HI: u64 = 0x4000;

    const NAMES: [&[u8]; 14] = [
        b"x18", b"x19", b"x20", b"x21", b"x22", b"x23", b"x24", b"x25", b"x26", b"x27", b"x28",
        b"x29", b"SP_EL0", b"NZCV",
    ];

    #[repr(C)]
    struct Report {
        actual: [u64; 14], // x18..x29, SP_EL0, NZCV
        timed_out: u64,
    }

    const PATTERNS: [[u64; 14]; 2] = [
        [
            0x1122_3344_5566_7781,
            0x2233_4455_6677_8892,
            0x3344_5566_7788_99a3,
            0x4455_6677_8899_aab4,
            0x5566_7788_99aa_bbc5,
            0x6677_8899_aabb_ccd6,
            0x7788_99aa_bbcc_dde7,
            0x8899_aabb_ccdd_eef8,
            0x99aa_bbcc_ddee_ff09,
            0xaabb_ccdd_eeff_001a,
            0xbbcc_ddee_ff00_112b,
            0xccdd_eeff_0011_223c,
            0x0000_6789_abcd_ef70,
            0xa000_0000, // N=1, Z=0, C=1, V=0
        ],
        [
            !0x1122_3344_5566_7781,
            !0x2233_4455_6677_8892,
            !0x3344_5566_7788_99a3,
            !0x4455_6677_8899_aab4,
            !0x5566_7788_99aa_bbc5,
            !0x6677_8899_aabb_ccd6,
            !0x7788_99aa_bbcc_dde7,
            !0x8899_aabb_ccdd_eef8,
            !0x99aa_bbcc_ddee_ff09,
            !0xaabb_ccdd_eeff_001a,
            !0xbbcc_ddee_ff00_112b,
            !0xccdd_eeff_0011_223c,
            0x0000_1876_5432_1080,
            0x5000_0000, // N=0, Z=1, C=0, V=1
        ],
    ];

    global_asm!(
        ".balign 4",
        ".global dom0_regs_run",
        "dom0_regs_run:",
        "sub sp, sp, #112",
        "stp x18, x19, [sp, #0]",
        "stp x20, x21, [sp, #16]",
        "stp x22, x23, [sp, #32]",
        "stp x24, x25, [sp, #48]",
        "stp x26, x27, [sp, #64]",
        "stp x28, x29, [sp, #80]",
        "str x30, [sp, #96]",

        "adrp x9, .Laarch64_scratch",
        "add x9, x9, :lo12:.Laarch64_scratch",
        "mov x10, sp",
        "stp x10, x0, [x9, #0]",

        // Load distinct values into x18..x29, SP_EL0 and NZCV.
        "ldp x18, x19, [x1, #0]",
        "ldp x20, x21, [x1, #16]",
        "ldp x22, x23, [x1, #32]",
        "ldp x24, x25, [x1, #48]",
        "ldp x26, x27, [x1, #64]",
        "ldp x28, x29, [x1, #80]",
        "ldp x10, x11, [x1, #96]",
        "mov sp, x10",
        "msr NZCV, x11",

        // cbnz reads x2 without reading or modifying NZCV.
        "cbnz x2, .Laarch64_do_preempt",

        // Syscall pass: inspect ROOT_CONSOLE_SLOT with zeroed args.
        "mov x8, #{inspect_op}",
        "mov x0, #{console_slot}",
        "mov x1, #0",
        "mov x2, #0",
        "mov x3, #0",
        "mov x4, #0",
        "mov x5, #0",
        "svc #0",
        "mov x13, #0",
        "b .Laarch64_capture",

        // Preemption pass: ldr, eor, sub (without 's') and cbnz never touch NZCV.
        ".Laarch64_do_preempt:",
        "ldr x10, [x2]",
        "movz x12, #{max_spins_hi}, lsl #16",
        "1:",
        "ldr x9, [x2]",
        "eor x9, x9, x10",
        "cbnz x9, .Laarch64_preempt_ok",
        "sub x12, x12, #1",
        "cbnz x12, 1b",
        "mov x13, #1",
        "b .Laarch64_capture",

        ".Laarch64_preempt_ok:",
        "mov x13, #0",

        ".Laarch64_capture:",
        "mrs x9, NZCV",
        "mov x10, sp",
        "adrp x11, .Laarch64_scratch",
        "add x11, x11, :lo12:.Laarch64_scratch",
        "ldp x12, x14, [x11, #0]",
        "mov sp, x12",

        "stp x18, x19, [x14, #0]",
        "stp x20, x21, [x14, #16]",
        "stp x22, x23, [x14, #32]",
        "stp x24, x25, [x14, #48]",
        "stp x26, x27, [x14, #64]",
        "stp x28, x29, [x14, #80]",
        "stp x10, x9, [x14, #96]",
        "str x13, [x14, #112]",

        "ldp x18, x19, [sp, #0]",
        "ldp x20, x21, [sp, #16]",
        "ldp x22, x23, [sp, #32]",
        "ldp x24, x25, [sp, #48]",
        "ldp x26, x27, [sp, #64]",
        "ldp x28, x29, [sp, #80]",
        "ldr x30, [sp, #96]",
        "add sp, sp, #112",
        "ret",

        ".pushsection .bss.dom0_reg_scratch, \"aw\", %nobits",
        ".balign 8",
        ".Laarch64_scratch: .space 16",
        ".popsection",

        inspect_op = const operation::INSPECT,
        console_slot = const operation::ROOT_CONSOLE_SLOT,
        max_spins_hi = const PREEMPT_MAX_SPINS_HI,
    );

    unsafe extern "C" {
        fn dom0_regs_run(report: *mut Report, expected: *const [u64; 14], counter: *const u64);
    }

    fn run_pass(pass: &[u8], expected: &[u64; 14], counter: *const u64) -> bool {
        let mut report = Report {
            actual: [0; 14],
            timed_out: 0,
        };
        unsafe { dom0_regs_run(&raw mut report, expected, counter) };
        if report.timed_out != 0 {
            report_failure(pass, b"", true);
            return false;
        }
        for (i, &name) in NAMES.iter().enumerate() {
            if report.actual[i] != expected[i] {
                report_failure(pass, name, false);
                return false;
            }
        }
        true
    }

    pub fn syscall() -> bool {
        PATTERNS.iter().all(|expected| run_pass(b"syscall", expected, ptr::null()))
    }

    pub fn preemption(counter: *const u64) -> bool {
        PATTERNS.iter().all(|expected| run_pass(b"preemption", expected, counter))
    }
}

/// Whether every preserved register of the syscall ABI kept a distinct value across an invocation,
/// printing `SYSCALL_REGISTERS_HELD` when it did.
pub fn syscall_registers_held() -> bool {
    target::syscall()
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, SYSCALL_REGISTERS_HELD) }
            == operation::STATUS_OK
}

/// Whether every preserved register of the syscall ABI kept a distinct value across a timer
/// preemption (observed via the peer thread counting at `counter` on core 0), printing
/// `PREEMPTION_REGISTERS_HELD` when it did.
pub fn preemption_registers_held(counter: *const u64) -> bool {
    target::preemption(counter)
        && unsafe { print_slot(operation::ROOT_CONSOLE_SLOT, PREEMPTION_REGISTERS_HELD) }
            == operation::STATUS_OK
}
