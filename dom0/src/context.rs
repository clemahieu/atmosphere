// SPDX-License-Identifier: MIT

//! Boot-time check that `acontext` starts a second context on a 16-byte-aligned stack and
//! preserves every saved integer callee-saved register and stack pointer across switches on both
//! targets (`design/register-convention-of-an-assembly-leaf/`).

use acontext::Context;
use asys::operation;

const STACK_BYTES: usize = 16384;

#[repr(C, align(16))]
struct AlignedStack([u8; STACK_BYTES]);

static mut SECONDARY_STACK: AlignedStack = AlignedStack([0; STACK_BYTES]);

const PATTERN_A: [u64; 12] = [
    0x1111_2222_3333_4401,
    0x1111_2222_3333_4402,
    0x1111_2222_3333_4403,
    0x1111_2222_3333_4404,
    0x1111_2222_3333_4405,
    0x1111_2222_3333_4406,
    0x1111_2222_3333_4407,
    0x1111_2222_3333_4408,
    0x1111_2222_3333_4409,
    0x1111_2222_3333_440a,
    0x1111_2222_3333_440b,
    0x1111_2222_3333_440c,
];

const PATTERN_A2: [u64; 12] = [
    0x5555_6666_7777_8821,
    0x5555_6666_7777_8822,
    0x5555_6666_7777_8823,
    0x5555_6666_7777_8824,
    0x5555_6666_7777_8825,
    0x5555_6666_7777_8826,
    0x5555_6666_7777_8827,
    0x5555_6666_7777_8828,
    0x5555_6666_7777_8829,
    0x5555_6666_7777_882a,
    0x5555_6666_7777_882b,
    0x5555_6666_7777_882c,
];

const PATTERN_B: [u64; 12] = [
    0xaaaa_bbbb_cccc_dd11,
    0xaaaa_bbbb_cccc_dd12,
    0xaaaa_bbbb_cccc_dd13,
    0xaaaa_bbbb_cccc_dd14,
    0xaaaa_bbbb_cccc_dd15,
    0xaaaa_bbbb_cccc_dd16,
    0xaaaa_bbbb_cccc_dd17,
    0xaaaa_bbbb_cccc_dd18,
    0xaaaa_bbbb_cccc_dd19,
    0xaaaa_bbbb_cccc_dd1a,
    0xaaaa_bbbb_cccc_dd1b,
    0xaaaa_bbbb_cccc_dd1c,
];

const PATTERN_C: [u64; 12] = [
    0x9999_8888_7777_6631,
    0x9999_8888_7777_6632,
    0x9999_8888_7777_6633,
    0x9999_8888_7777_6634,
    0x9999_8888_7777_6635,
    0x9999_8888_7777_6636,
    0x9999_8888_7777_6637,
    0x9999_8888_7777_6638,
    0x9999_8888_7777_6639,
    0x9999_8888_7777_663a,
    0x9999_8888_7777_663b,
    0x9999_8888_7777_663c,
];

#[repr(C)]
struct SwitchCheckState {
    primary: Context,
    secondary: Context,
    primary_expected_sp: u64,
    secondary_expected_sp: u64,
    secondary_aligned_top: u64,
    secondary_entry_sp_ok: u64,
    secondary_roundtrip_ok: u64,
    pattern_a: [u64; 12],
    pattern_a2: [u64; 12],
    pattern_b: [u64; 12],
    pattern_c: [u64; 12],
}

static mut STATE: SwitchCheckState = SwitchCheckState {
    primary: Context::empty(),
    secondary: Context::empty(),
    primary_expected_sp: 0,
    secondary_expected_sp: 0,
    secondary_aligned_top: 0,
    secondary_entry_sp_ok: 0,
    secondary_roundtrip_ok: 0,
    pattern_a: PATTERN_A,
    pattern_a2: PATTERN_A2,
    pattern_b: PATTERN_B,
    pattern_c: PATTERN_C,
};

#[cfg(target_arch = "x86_64")]
mod target {
    use super::*;
    use core::arch::naked_asm;
    use core::mem::offset_of;

    #[unsafe(naked)]
    pub(super) unsafe extern "C" fn secondary_entry() {
        naked_asm!(
            "mov rdi, rsp",
            "jmp {body}",
            body = sym secondary_body,
        );
    }

    extern "C" fn secondary_body(entry_sp: u64) {
        let state = &raw mut STATE;
        unsafe {
            let aligned_top = (*state).secondary_aligned_top;
            if entry_sp + 8 == aligned_top && ((entry_sp + 8) & 0xf) == 0 {
                (*state).secondary_entry_sp_ok = 1;
            }
            secondary_check_asm(state, acontext::switch as *const ());
        }
    }

    #[unsafe(naked)]
    pub(super) unsafe extern "C" fn primary_check_asm(
        state: *mut SwitchCheckState,
        switch_fn: *const (),
    ) -> u64 {
        naked_asm!(
            "push rbx",
            "push rbp",
            "push r12",
            "push r13",
            "push r14",
            "push r15",
            "sub rsp, 24",
            "mov [rsp + 0], rdi",
            "mov [rsp + 8], rsi",
            "mov [rdi + {prim_sp}], rsp",

            // Pattern A in every callee-saved register (x86-64 psABI Fig. 3.4).
            "mov rbx, [rdi + {pa} + 0]",
            "mov rbp, [rdi + {pa} + 8]",
            "mov r12, [rdi + {pa} + 16]",
            "mov r13, [rdi + {pa} + 24]",
            "mov r14, [rdi + {pa} + 32]",
            "mov r15, [rdi + {pa} + 40]",

            "mov rdx, rsi",
            "lea rsi, [rdi + {secondary}]",
            "lea rdi, [rdi + {primary}]",
            "call rdx",

            "mov rcx, [rsp + 0]",
            "cmp rsp, [rcx + {prim_sp}]",
            "jne 2f",
            "cmp rbx, [rcx + {pa} + 0]",
            "jne 2f",
            "cmp rbp, [rcx + {pa} + 8]",
            "jne 2f",
            "cmp r12, [rcx + {pa} + 16]",
            "jne 2f",
            "cmp r13, [rcx + {pa} + 24]",
            "jne 2f",
            "cmp r14, [rcx + {pa} + 32]",
            "jne 2f",
            "cmp r15, [rcx + {pa} + 40]",
            "jne 2f",

            // Roundtrip 2 with Pattern A2 to check secondary's restore and clobber recovery.
            "mov rbx, [rcx + {pa2} + 0]",
            "mov rbp, [rcx + {pa2} + 8]",
            "mov r12, [rcx + {pa2} + 16]",
            "mov r13, [rcx + {pa2} + 24]",
            "mov r14, [rcx + {pa2} + 32]",
            "mov r15, [rcx + {pa2} + 40]",

            "mov rax, [rsp + 8]",
            "lea rdi, [rcx + {primary}]",
            "lea rsi, [rcx + {secondary}]",
            "call rax",

            "mov rcx, [rsp + 0]",
            "cmp rsp, [rcx + {prim_sp}]",
            "jne 2f",
            "cmp rbx, [rcx + {pa2} + 0]",
            "jne 2f",
            "cmp rbp, [rcx + {pa2} + 8]",
            "jne 2f",
            "cmp r12, [rcx + {pa2} + 16]",
            "jne 2f",
            "cmp r13, [rcx + {pa2} + 24]",
            "jne 2f",
            "cmp r14, [rcx + {pa2} + 32]",
            "jne 2f",
            "cmp r15, [rcx + {pa2} + 40]",
            "jne 2f",

            "mov eax, 1",
            "jmp 3f",
            "2:",
            "xor eax, eax",
            "3:",
            "add rsp, 24",
            "pop r15",
            "pop r14",
            "pop r13",
            "pop r12",
            "pop rbp",
            "pop rbx",
            "ret",
            primary = const offset_of!(SwitchCheckState, primary),
            secondary = const offset_of!(SwitchCheckState, secondary),
            prim_sp = const offset_of!(SwitchCheckState, primary_expected_sp),
            pa = const offset_of!(SwitchCheckState, pattern_a),
            pa2 = const offset_of!(SwitchCheckState, pattern_a2),
        );
    }

    #[unsafe(naked)]
    unsafe extern "C" fn secondary_check_asm(
        state: *mut SwitchCheckState,
        switch_fn: *const (),
    ) -> ! {
        naked_asm!(
            "sub rsp, 24",
            "mov [rsp + 0], rdi",
            "mov [rsp + 8], rsi",
            "mov [rdi + {sec_sp}], rsp",

            "mov rbx, [rdi + {pb} + 0]",
            "mov rbp, [rdi + {pb} + 8]",
            "mov r12, [rdi + {pb} + 16]",
            "mov r13, [rdi + {pb} + 24]",
            "mov r14, [rdi + {pb} + 32]",
            "mov r15, [rdi + {pb} + 40]",

            "mov rdx, rsi",
            "mov rax, rdi",
            "lea rdi, [rax + {secondary}]",
            "lea rsi, [rax + {primary}]",
            "call rdx",

            "mov rcx, [rsp + 0]",
            "cmp rsp, [rcx + {sec_sp}]",
            "jne 2f",
            "cmp rbx, [rcx + {pb} + 0]",
            "jne 2f",
            "cmp rbp, [rcx + {pb} + 8]",
            "jne 2f",
            "cmp r12, [rcx + {pb} + 16]",
            "jne 2f",
            "cmp r13, [rcx + {pb} + 24]",
            "jne 2f",
            "cmp r14, [rcx + {pb} + 32]",
            "jne 2f",
            "cmp r15, [rcx + {pb} + 40]",
            "jne 2f",
            "mov qword ptr [rcx + {sec_ok}], 1",

            "2:",
            "mov rbx, [rcx + {pc} + 0]",
            "mov rbp, [rcx + {pc} + 8]",
            "mov r12, [rcx + {pc} + 16]",
            "mov r13, [rcx + {pc} + 24]",
            "mov r14, [rcx + {pc} + 32]",
            "mov r15, [rcx + {pc} + 40]",

            "mov rax, [rsp + 8]",
            "lea rdi, [rcx + {secondary}]",
            "lea rsi, [rcx + {primary}]",
            "call rax",
            "ud2",
            primary = const offset_of!(SwitchCheckState, primary),
            secondary = const offset_of!(SwitchCheckState, secondary),
            sec_sp = const offset_of!(SwitchCheckState, secondary_expected_sp),
            sec_ok = const offset_of!(SwitchCheckState, secondary_roundtrip_ok),
            pb = const offset_of!(SwitchCheckState, pattern_b),
            pc = const offset_of!(SwitchCheckState, pattern_c),
        );
    }
}

#[cfg(target_arch = "aarch64")]
mod target {
    use super::*;
    use core::arch::naked_asm;
    use core::mem::offset_of;

    #[unsafe(naked)]
    pub(super) unsafe extern "C" fn secondary_entry() {
        naked_asm!(
            "mov x0, sp",
            "b {body}",
            body = sym secondary_body,
        );
    }

    extern "C" fn secondary_body(entry_sp: u64) {
        let state = &raw mut STATE;
        unsafe {
            let aligned_top = (*state).secondary_aligned_top;
            if entry_sp == aligned_top && (entry_sp & 0xf) == 0 {
                (*state).secondary_entry_sp_ok = 1;
            }
            secondary_check_asm(state, acontext::switch as *const ());
        }
    }

    #[unsafe(naked)]
    pub(super) unsafe extern "C" fn primary_check_asm(
        state: *mut SwitchCheckState,
        switch_fn: *const (),
    ) -> u64 {
        naked_asm!(
            "sub sp, sp, #128",
            "stp x18, x19, [sp, #16]",
            "stp x20, x21, [sp, #32]",
            "stp x22, x23, [sp, #48]",
            "stp x24, x25, [sp, #64]",
            "stp x26, x27, [sp, #80]",
            "stp x28, x29, [sp, #96]",
            "str x30, [sp, #112]",
            "stp x0, x1, [sp, #0]",
            "mov x9, sp",
            "str x9, [x0, #{prim_sp}]",

            // Pattern A in x18-x29 (AAPCS64 Table 2 + syscall-abi x18).
            "add x9, x0, #{pa}",
            "ldp x18, x19, [x9, #0]",
            "ldp x20, x21, [x9, #16]",
            "ldp x22, x23, [x9, #32]",
            "ldp x24, x25, [x9, #48]",
            "ldp x26, x27, [x9, #64]",
            "ldp x28, x29, [x9, #80]",

            "mov x9, x1",
            "add x1, x0, #{secondary}",
            "add x0, x0, #{primary}",
            "blr x9",

            "ldr x9, [sp, #0]",
            "mov x10, sp",
            "ldr x11, [x9, #{prim_sp}]",
            "cmp x10, x11",
            "b.ne 2f",
            "add x10, x9, #{pa}",
            "ldr x11, [x10, #0]",  "cmp x18, x11", "b.ne 2f",
            "ldr x11, [x10, #8]",  "cmp x19, x11", "b.ne 2f",
            "ldr x11, [x10, #16]", "cmp x20, x11", "b.ne 2f",
            "ldr x11, [x10, #24]", "cmp x21, x11", "b.ne 2f",
            "ldr x11, [x10, #32]", "cmp x22, x11", "b.ne 2f",
            "ldr x11, [x10, #40]", "cmp x23, x11", "b.ne 2f",
            "ldr x11, [x10, #48]", "cmp x24, x11", "b.ne 2f",
            "ldr x11, [x10, #56]", "cmp x25, x11", "b.ne 2f",
            "ldr x11, [x10, #64]", "cmp x26, x11", "b.ne 2f",
            "ldr x11, [x10, #72]", "cmp x27, x11", "b.ne 2f",
            "ldr x11, [x10, #80]", "cmp x28, x11", "b.ne 2f",
            "ldr x11, [x10, #88]", "cmp x29, x11", "b.ne 2f",

            // Roundtrip 2 with Pattern A2.
            "add x10, x9, #{pa2}",
            "ldp x18, x19, [x10, #0]",
            "ldp x20, x21, [x10, #16]",
            "ldp x22, x23, [x10, #32]",
            "ldp x24, x25, [x10, #48]",
            "ldp x26, x27, [x10, #64]",
            "ldp x28, x29, [x10, #80]",

            "ldr x10, [sp, #8]",
            "add x0, x9, #{primary}",
            "add x1, x9, #{secondary}",
            "blr x10",

            "ldr x9, [sp, #0]",
            "mov x10, sp",
            "ldr x11, [x9, #{prim_sp}]",
            "cmp x10, x11",
            "b.ne 2f",
            "add x10, x9, #{pa2}",
            "ldr x11, [x10, #0]",  "cmp x18, x11", "b.ne 2f",
            "ldr x11, [x10, #8]",  "cmp x19, x11", "b.ne 2f",
            "ldr x11, [x10, #16]", "cmp x20, x11", "b.ne 2f",
            "ldr x11, [x10, #24]", "cmp x21, x11", "b.ne 2f",
            "ldr x11, [x10, #32]", "cmp x22, x11", "b.ne 2f",
            "ldr x11, [x10, #40]", "cmp x23, x11", "b.ne 2f",
            "ldr x11, [x10, #48]", "cmp x24, x11", "b.ne 2f",
            "ldr x11, [x10, #56]", "cmp x25, x11", "b.ne 2f",
            "ldr x11, [x10, #64]", "cmp x26, x11", "b.ne 2f",
            "ldr x11, [x10, #72]", "cmp x27, x11", "b.ne 2f",
            "ldr x11, [x10, #80]", "cmp x28, x11", "b.ne 2f",
            "ldr x11, [x10, #88]", "cmp x29, x11", "b.ne 2f",

            "mov x0, #1",
            "b 3f",
            "2:",
            "mov x0, #0",
            "3:",
            "ldp x18, x19, [sp, #16]",
            "ldp x20, x21, [sp, #32]",
            "ldp x22, x23, [sp, #48]",
            "ldp x24, x25, [sp, #64]",
            "ldp x26, x27, [sp, #80]",
            "ldp x28, x29, [sp, #96]",
            "ldr x30, [sp, #112]",
            "add sp, sp, #128",
            "ret",
            primary = const offset_of!(SwitchCheckState, primary),
            secondary = const offset_of!(SwitchCheckState, secondary),
            prim_sp = const offset_of!(SwitchCheckState, primary_expected_sp),
            pa = const offset_of!(SwitchCheckState, pattern_a),
            pa2 = const offset_of!(SwitchCheckState, pattern_a2),
        );
    }

    #[unsafe(naked)]
    unsafe extern "C" fn secondary_check_asm(
        state: *mut SwitchCheckState,
        switch_fn: *const (),
    ) -> ! {
        naked_asm!(
            "sub sp, sp, #16",
            "stp x0, x1, [sp, #0]",
            "mov x9, sp",
            "str x9, [x0, #{sec_sp}]",

            "add x9, x0, #{pb}",
            "ldp x18, x19, [x9, #0]",
            "ldp x20, x21, [x9, #16]",
            "ldp x22, x23, [x9, #32]",
            "ldp x24, x25, [x9, #48]",
            "ldp x26, x27, [x9, #64]",
            "ldp x28, x29, [x9, #80]",

            "mov x9, x1",
            "add x1, x0, #{primary}",
            "add x0, x0, #{secondary}",
            "blr x9",

            "ldr x9, [sp, #0]",
            "mov x10, sp",
            "ldr x11, [x9, #{sec_sp}]",
            "cmp x10, x11",
            "b.ne 2f",
            "add x10, x9, #{pb}",
            "ldr x11, [x10, #0]",  "cmp x18, x11", "b.ne 2f",
            "ldr x11, [x10, #8]",  "cmp x19, x11", "b.ne 2f",
            "ldr x11, [x10, #16]", "cmp x20, x11", "b.ne 2f",
            "ldr x11, [x10, #24]", "cmp x21, x11", "b.ne 2f",
            "ldr x11, [x10, #32]", "cmp x22, x11", "b.ne 2f",
            "ldr x11, [x10, #40]", "cmp x23, x11", "b.ne 2f",
            "ldr x11, [x10, #48]", "cmp x24, x11", "b.ne 2f",
            "ldr x11, [x10, #56]", "cmp x25, x11", "b.ne 2f",
            "ldr x11, [x10, #64]", "cmp x26, x11", "b.ne 2f",
            "ldr x11, [x10, #72]", "cmp x27, x11", "b.ne 2f",
            "ldr x11, [x10, #80]", "cmp x28, x11", "b.ne 2f",
            "ldr x11, [x10, #88]", "cmp x29, x11", "b.ne 2f",
            "mov x10, #1",
            "str x10, [x9, #{sec_ok}]",

            "2:",
            "add x10, x9, #{pc}",
            "ldp x18, x19, [x10, #0]",
            "ldp x20, x21, [x10, #16]",
            "ldp x22, x23, [x10, #32]",
            "ldp x24, x25, [x10, #48]",
            "ldp x26, x27, [x10, #64]",
            "ldp x28, x29, [x10, #80]",

            "ldr x10, [sp, #8]",
            "add x0, x9, #{secondary}",
            "add x1, x9, #{primary}",
            "blr x10",
            "udf #0",
            primary = const offset_of!(SwitchCheckState, primary),
            secondary = const offset_of!(SwitchCheckState, secondary),
            sec_sp = const offset_of!(SwitchCheckState, secondary_expected_sp),
            sec_ok = const offset_of!(SwitchCheckState, secondary_roundtrip_ok),
            pb = const offset_of!(SwitchCheckState, pattern_b),
            pc = const offset_of!(SwitchCheckState, pattern_c),
        );
    }
}

/// Switches from dom0's carrier stack to a fresh context on `SECONDARY_STACK` and back twice,
/// verifying 16-byte stack alignment at entry and distinct sentinels in every saved register
/// (`design/register-convention-of-an-assembly-leaf/`).
pub(crate) fn context_switch_held() -> bool {
    let stack_bottom = (&raw mut SECONDARY_STACK).cast::<u8>();
    let aligned_top = ((stack_bottom as usize + STACK_BYTES) & !0xf) as u64;
    let entry: extern "C" fn() = unsafe { core::mem::transmute(target::secondary_entry as unsafe extern "C" fn()) };
    let state = &raw mut STATE;
    let ok = unsafe {
        (*state).primary = Context::empty();
        (*state).secondary = Context::new(entry, stack_bottom, STACK_BYTES);
        (*state).primary_expected_sp = 0;
        (*state).secondary_expected_sp = 0;
        (*state).secondary_aligned_top = aligned_top;
        (*state).secondary_entry_sp_ok = 0;
        (*state).secondary_roundtrip_ok = 0;

        let primary_ok = target::primary_check_asm(state, acontext::switch as *const ());
        primary_ok == 1
            && (*state).secondary_entry_sp_ok == 1
            && (*state).secondary_roundtrip_ok == 1
    };
    if ok {
        unsafe {
            crate::print_slot(
                operation::ROOT_CONSOLE_SLOT,
                operation::print_words(b"dom0 context switch registers held\n"),
            );
        }
        true
    } else {
        unsafe {
            crate::print_slot(
                operation::ROOT_CONSOLE_SLOT,
                operation::print_words(b"dom0 context switch registers FAIL\n"),
            );
        }
        false
    }
}
