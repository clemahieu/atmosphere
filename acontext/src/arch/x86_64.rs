// SPDX-License-Identifier: MIT

//! x86_64 user-context switch (`reference/elf/x86-64-psABI-1.0.pdf`).
//!
//! Atmosphere builds for `x86_64-unknown-aloader` with `-mmx,-sse,+soft-float`, so no x87 CW or
//! MXCSR control bits exist to preserve and the saved set consists solely of the System V AMD64
//! callee-saved integer registers (`%rbx`, `%rbp`, `%r12`-`%r15`), `%rsp`, and the resume `%rip`
//! (`x86-64-psABI-1.0.pdf` §3.2.1 and Figure 3.4, pp. 21-22, 27).

use core::arch::naked_asm;
use core::mem::offset_of;

/// Saved callee-saved integer registers, stack pointer, and resume instruction pointer for one
/// x86_64 user execution context.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Context {
    rbx: u64,
    rbp: u64,
    r12: u64,
    r13: u64,
    r14: u64,
    r15: u64,
    rsp: u64,
    rip: u64,
}

impl Context {
    /// Returns an empty zeroed context for a currently running carrier thread prior to its first
    /// call to [`switch`].
    pub const fn empty() -> Self {
        Self {
            rbx: 0,
            rbp: 0,
            r12: 0,
            r13: 0,
            r14: 0,
            r15: 0,
            rsp: 0,
            rip: 0,
        }
    }

    /// Creates a fresh context that starts `entry` on the stack `[stack_bottom, stack_bottom + stack_size)`
    /// aligned to 16 bytes at entry, and aborts if `entry` ever returns.
    ///
    /// Per `reference/elf/x86-64-psABI-1.0.pdf` §3.2.2 (pp. 22-23), `%rsp` is 16-byte aligned
    /// immediately before `call`, so on entry after `call` pushes the 8-byte return address
    /// `(%rsp + 8)` is a multiple of 16.
    pub fn new(entry: extern "C" fn(), stack_bottom: *mut u8, stack_size: usize) -> Self {
        let base = stack_bottom as usize;
        let top = base.checked_add(stack_size).expect("stack address overflow");
        let aligned_top = top & !0xf;
        assert!(
            aligned_top >= base && aligned_top - base >= 16,
            "stack must hold at least 16 aligned bytes",
        );
        Self {
            rbx: 0,
            rbp: 0,
            r12: entry as *const () as usize as u64,
            r13: 0,
            r14: 0,
            r15: 0,
            rsp: aligned_top as u64,
            rip: entry_trampoline as *const () as usize as u64,
        }
    }
}

#[unsafe(naked)]
unsafe extern "C" fn entry_trampoline() -> ! {
    naked_asm!(
        // `Context::new` places `entry` in `%r12` and sets `%rsp` 16-byte aligned.
        // `call` pushes the 8-byte return address so `(%rsp + 8) % 16 == 0` on entry per
        // x86-64 psABI §3.2.2; returning falls through to `ud2` and aborts.
        "call r12",
        "ud2",
    );
}

/// Saves the caller's callee-saved integer registers (`%rbx`, `%rbp`, `%r12`-`%r15`), `%rsp`,
/// and return address (`%rip`) into `*from`, and resumes execution from `*to`.
///
/// Register convention: `reference/elf/x86-64-psABI-1.0.pdf` §3.2.1 (pp. 21-22) and Figure 3.4
/// (p. 27), omitting x87/MXCSR state under `+soft-float`. Calling this obeys the ABI invariant that
/// `DF = 0` in `%rFLAGS` on entry and return.
///
/// # Safety
///
/// - `from` must point to writable storage for a `Context`.
/// - `to` must point to an initialized `Context` whose stack memory remains valid, exclusively
///   owned while suspended, and disjoint from the caller's active stack.
/// - `DF` in `%rFLAGS` must be clear (`0`) per psABI §3.2.1, and panics must abort rather than
///   unwind across `switch`.
#[unsafe(naked)]
pub unsafe extern "C" fn switch(from: *mut Context, to: *const Context) {
    naked_asm!(
        // Save callee-saved integer registers (x86-64 psABI 1.0 §3.2.1, Fig. 3.4), return RIP,
        // and caller's RSP prior to `call` into `from` (rdi).
        "mov [rdi + {rbx}], rbx",
        "mov [rdi + {rbp}], rbp",
        "mov [rdi + {r12}], r12",
        "mov [rdi + {r13}], r13",
        "mov [rdi + {r14}], r14",
        "mov [rdi + {r15}], r15",
        "mov rax, [rsp]",
        "mov [rdi + {rip}], rax",
        "lea rax, [rsp + 8]",
        "mov [rdi + {rsp}], rax",

        // Restore callee-saved integer registers, stack pointer, and resume RIP from `to` (rsi).
        "mov rbx, [rsi + {rbx}]",
        "mov rbp, [rsi + {rbp}]",
        "mov r12, [rsi + {r12}]",
        "mov r13, [rsi + {r13}]",
        "mov r14, [rsi + {r14}]",
        "mov r15, [rsi + {r15}]",
        "mov rax, [rsi + {rip}]",
        "mov rsp, [rsi + {rsp}]",
        "jmp rax",
        rbx = const offset_of!(Context, rbx),
        rbp = const offset_of!(Context, rbp),
        r12 = const offset_of!(Context, r12),
        r13 = const offset_of!(Context, r13),
        r14 = const offset_of!(Context, r14),
        r15 = const offset_of!(Context, r15),
        rsp = const offset_of!(Context, rsp),
        rip = const offset_of!(Context, rip),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicPtr, AtomicU64, AtomicUsize, Ordering};

    static ALIGN_FROM: AtomicPtr<Context> = AtomicPtr::new(core::ptr::null_mut());
    static ALIGN_TO: AtomicPtr<Context> = AtomicPtr::new(core::ptr::null_mut());
    static ALIGN_OBSERVED_SP: AtomicU64 = AtomicU64::new(0);

    #[unsafe(naked)]
    unsafe extern "C" fn capture_entry_rsp() {
        naked_asm!(
            "mov rdi, rsp",
            "jmp {finish}",
            finish = sym capture_entry_rsp_body,
        );
    }

    extern "C" fn capture_entry_rsp_body(entry_rsp: u64) {
        ALIGN_OBSERVED_SP.store(entry_rsp, Ordering::Relaxed);
        let to = ALIGN_TO.load(Ordering::Relaxed);
        let from = ALIGN_FROM.load(Ordering::Relaxed);
        unsafe { switch(to, from) };
    }

    #[test]
    fn new_aligns_unaligned_stack_to_16_bytes() {
        let mut raw = [0u8; 4096 + 32];
        for offset in 1usize..16usize {
            let bottom = unsafe { raw.as_mut_ptr().add(offset) };
            let size = 4096 + offset;
            let expected_top = ((bottom as usize + size) & !0xf) as u64;
            let mut from = Context::empty();
            let entry: extern "C" fn() = unsafe { core::mem::transmute(capture_entry_rsp as unsafe extern "C" fn()) };
            let mut to = Context::new(entry, bottom, size);
            ALIGN_FROM.store(&raw mut from, Ordering::Relaxed);
            ALIGN_TO.store(&raw mut to, Ordering::Relaxed);
            ALIGN_OBSERVED_SP.store(0, Ordering::Relaxed);

            unsafe { switch(&raw mut from, &raw const to) };

            let observed = ALIGN_OBSERVED_SP.load(Ordering::Relaxed);
            assert_eq!(observed, expected_top - 8);
            assert_eq!((observed + 8) & 0xf, 0);
            assert!(observed >= bottom as u64 && observed < expected_top);
        }
    }

    #[test]
    #[should_panic]
    fn new_rejects_too_small_stack() {
        let mut raw = [0u8; 16];
        let entry: extern "C" fn() = unsafe { core::mem::transmute(capture_entry_rsp as unsafe extern "C" fn()) };
        let _ = Context::new(entry, unsafe { raw.as_mut_ptr().add(1) }, 15);
    }

    static RT_FROM: AtomicPtr<Context> = AtomicPtr::new(core::ptr::null_mut());
    static RT_TO: AtomicPtr<Context> = AtomicPtr::new(core::ptr::null_mut());
    static RT_EXPECTED_PRIMARY_SP: AtomicU64 = AtomicU64::new(0);
    static RT_EXPECTED_SECONDARY_SP: AtomicU64 = AtomicU64::new(0);
    static RT_SECONDARY_OK: AtomicUsize = AtomicUsize::new(0);

    unsafe extern "C" {
        fn rt_primary_run(
            from: *mut Context,
            to: *const Context,
            switch_fn: *const (),
            expected_sp_out: *mut AtomicU64,
        ) -> u64;
        fn rt_secondary_entry();
    }

    core::arch::global_asm!(
        r#"
        .global rt_primary_run
        rt_primary_run:
            push rbx
            push rbp
            push r12
            push r13
            push r14
            push r15
            sub rsp, 24
            mov [rsp + 0], rdi
            mov [rsp + 8], rsi
            mov [rsp + 16], rdx
            mov [rcx], rsp

            // Pattern A in every callee-saved register.
            movabs rbx, 0x1111222233334401
            movabs rbp, 0x1111222233334402
            movabs r12, 0x1111222233334403
            movabs r13, 0x1111222233334404
            movabs r14, 0x1111222233334405
            movabs r15, 0x1111222233334406
            call rdx

            mov rcx, [rip + {expected_sp}]
            cmp rsp, rcx
            jne 2f
            movabs rax, 0x1111222233334401
            cmp rbx, rax
            jne 2f
            movabs rax, 0x1111222233334402
            cmp rbp, rax
            jne 2f
            movabs rax, 0x1111222233334403
            cmp r12, rax
            jne 2f
            movabs rax, 0x1111222233334404
            cmp r13, rax
            jne 2f
            movabs rax, 0x1111222233334405
            cmp r14, rax
            jne 2f
            movabs rax, 0x1111222233334406
            cmp r15, rax
            jne 2f

            // Roundtrip 2 with distinct sentinels (Pattern A2).
            movabs rbx, 0x5555666677778821
            movabs rbp, 0x5555666677778822
            movabs r12, 0x5555666677778823
            movabs r13, 0x5555666677778824
            movabs r14, 0x5555666677778825
            movabs r15, 0x5555666677778826
            mov rdi, [rsp + 0]
            mov rsi, [rsp + 8]
            mov rax, [rsp + 16]
            call rax

            mov rcx, [rip + {expected_sp}]
            cmp rsp, rcx
            jne 2f
            movabs rax, 0x5555666677778821
            cmp rbx, rax
            jne 2f
            movabs rax, 0x5555666677778822
            cmp rbp, rax
            jne 2f
            movabs rax, 0x5555666677778823
            cmp r12, rax
            jne 2f
            movabs rax, 0x5555666677778824
            cmp r13, rax
            jne 2f
            movabs rax, 0x5555666677778825
            cmp r14, rax
            jne 2f
            movabs rax, 0x5555666677778826
            cmp r15, rax
            jne 2f
            mov eax, 1
            jmp 3f
        2:
            xor eax, eax
        3:
            add rsp, 24
            pop r15
            pop r14
            pop r13
            pop r12
            pop rbp
            pop rbx
            ret

        .global rt_secondary_entry
        rt_secondary_entry:
            sub rsp, 8
            mov [rip + {sec_sp}], rsp
            movabs rbx, 0xaaaabbbbccccdd11
            movabs rbp, 0xaaaabbbbccccdd12
            movabs r12, 0xaaaabbbbccccdd13
            movabs r13, 0xaaaabbbbccccdd14
            movabs r14, 0xaaaabbbbccccdd15
            movabs r15, 0xaaaabbbbccccdd16
            mov rdi, [rip + {rt_to}]
            mov rsi, [rip + {rt_from}]
            call {switch_sym}

            mov rcx, [rip + {sec_sp}]
            cmp rsp, rcx
            jne 3f
            movabs rax, 0xaaaabbbbccccdd11
            cmp rbx, rax
            jne 3f
            movabs rax, 0xaaaabbbbccccdd12
            cmp rbp, rax
            jne 3f
            movabs rax, 0xaaaabbbbccccdd13
            cmp r12, rax
            jne 3f
            movabs rax, 0xaaaabbbbccccdd14
            cmp r13, rax
            jne 3f
            movabs rax, 0xaaaabbbbccccdd15
            cmp r14, rax
            jne 3f
            movabs rax, 0xaaaabbbbccccdd16
            cmp r15, rax
            jne 3f
            mov qword ptr [rip + {sec_ok}], 1
        3:
            movabs rbx, 0x9999888877776631
            movabs rbp, 0x9999888877776632
            movabs r12, 0x9999888877776633
            movabs r13, 0x9999888877776634
            movabs r14, 0x9999888877776635
            movabs r15, 0x9999888877776636
            mov rdi, [rip + {rt_to}]
            mov rsi, [rip + {rt_from}]
            call {switch_sym}
            ud2
        "#,
        expected_sp = sym RT_EXPECTED_PRIMARY_SP,
        sec_sp = sym RT_EXPECTED_SECONDARY_SP,
        rt_to = sym RT_TO,
        rt_from = sym RT_FROM,
        sec_ok = sym RT_SECONDARY_OK,
        switch_sym = sym switch,
    );

    #[test]
    fn switch_roundtrip_preserves_all_callee_saved_registers() {
        let mut stack = [0u8; 8192];
        let mut from = Context::empty();
        let entry: extern "C" fn() = unsafe { core::mem::transmute(rt_secondary_entry as unsafe extern "C" fn()) };
        let mut to = Context::new(entry, stack.as_mut_ptr(), stack.len());
        RT_FROM.store(&raw mut from, Ordering::Relaxed);
        RT_TO.store(&raw mut to, Ordering::Relaxed);
        RT_SECONDARY_OK.store(0, Ordering::Relaxed);

        let primary_ok = unsafe {
            rt_primary_run(
                &raw mut from,
                &raw const to,
                switch as *const (),
                &raw const RT_EXPECTED_PRIMARY_SP as *mut AtomicU64,
            )
        };
        assert_eq!(primary_ok, 1);
        assert_eq!(RT_SECONDARY_OK.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn self_switch_preserves_registers() {
        let mut ctx = Context::empty();
        let ok = unsafe {
            let from = &raw mut ctx;
            let to = &raw const ctx;
            let mut out: u64;
            core::arch::asm!(
                "push rbx",
                "push r12",
                "movabs rbx, 0x0102030405060708",
                "movabs r12, 0x1112131415161718",
                "call {sw}",
                "movabs rdx, 0x0102030405060708",
                "cmp rbx, rdx",
                "jne 2f",
                "movabs rdx, 0x1112131415161718",
                "cmp r12, rdx",
                "jne 2f",
                "mov eax, 1",
                "jmp 3f",
                "2:",
                "xor eax, eax",
                "3:",
                "pop r12",
                "pop rbx",
                sw = sym switch,
                in("rdi") from,
                in("rsi") to,
                lateout("rax") out,
                lateout("rdx") _,
                lateout("rcx") _,
                lateout("r8") _,
                lateout("r9") _,
                lateout("r10") _,
                lateout("r11") _,
            );
            out
        };
        assert_eq!(ok, 1);
    }

    extern "C" fn returning_entry() {}

    #[test]
    fn returning_from_entry_aborts() {
        if std::env::var_os("ACONTEXT_TEST_RETURN_ABORT").is_some() {
            let mut stack = [0u8; 4096];
            let mut from = Context::empty();
            let to = Context::new(returning_entry, stack.as_mut_ptr(), stack.len());
            unsafe { switch(&raw mut from, &raw const to) };
            std::process::exit(42);
        }

        let exe = std::env::current_exe().expect("current_exe");
        let output = std::process::Command::new(exe)
            .arg("returning_from_entry_aborts")
            .env("ACONTEXT_TEST_RETURN_ABORT", "1")
            .output()
            .expect("spawn child test");
        assert!(!output.status.success(), "returning from entry unexpectedly exited cleanly: {:?}", output.status);
        assert_ne!(output.status.code(), Some(42), "switch returned after entry function returned");
    }
}
