// SPDX-License-Identifier: MIT

//! AArch64 user-context switch (`reference/arm/aapcs64.pdf`).
//!
//! Atmosphere builds for `aarch64-unknown-aloader` with `+v8a,+strict-align,-neon` and
//! `"abi": "softfloat"`, so no SIMD or floating-point registers (`v8`-`v15`) exist to preserve and
//! the saved set consists of the AAPCS64 callee-saved general-purpose registers (`x19`-`x29`) and
//! `SP` (`reference/arm/aapcs64.pdf` §6.1.1 and Table 2, pp. 21-22), plus `x18` because Atmosphere's
//! syscall ABI preserves it (`design/syscall-abi-in-registers/`), and the resume link register `x30`.

use core::arch::naked_asm;
use core::mem::offset_of;

/// Saved callee-saved integer registers (`x19`-`x29`), platform register `x18`, stack pointer,
/// and resume link register (`x30`) for one AArch64 user execution context.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Context {
    x18: u64,
    x19: u64,
    x20: u64,
    x21: u64,
    x22: u64,
    x23: u64,
    x24: u64,
    x25: u64,
    x26: u64,
    x27: u64,
    x28: u64,
    x29: u64,
    sp: u64,
    lr: u64,
}

impl Context {
    /// Returns an empty zeroed context for a currently running carrier thread prior to its first
    /// call to [`switch`].
    pub const fn empty() -> Self {
        Self {
            x18: 0,
            x19: 0,
            x20: 0,
            x21: 0,
            x22: 0,
            x23: 0,
            x24: 0,
            x25: 0,
            x26: 0,
            x27: 0,
            x28: 0,
            x29: 0,
            sp: 0,
            lr: 0,
        }
    }

    /// Creates a fresh context that starts `entry` on the stack `[stack_bottom, stack_bottom + stack_size)`
    /// aligned to 16 bytes at entry, and aborts if `entry` ever returns.
    ///
    /// Per `reference/arm/aapcs64.pdf` §6.4.5.1 and §6.4.5.2 (pp. 26-27), the stack is
    /// full-descending and `SP mod 16 = 0` at every public interface and memory access via `SP`.
    pub fn new(entry: extern "C" fn(), stack_bottom: *mut u8, stack_size: usize) -> Self {
        let base = stack_bottom as usize;
        let top = base.checked_add(stack_size).expect("stack address overflow");
        let aligned_top = top & !0xf;
        assert!(
            aligned_top >= base && aligned_top - base >= 16,
            "stack must hold at least 16 aligned bytes",
        );
        Self {
            x18: 0,
            x19: entry as *const () as usize as u64,
            x20: 0,
            x21: 0,
            x22: 0,
            x23: 0,
            x24: 0,
            x25: 0,
            x26: 0,
            x27: 0,
            x28: 0,
            x29: 0,
            sp: aligned_top as u64,
            lr: entry_trampoline as *const () as usize as u64,
        }
    }
}

#[unsafe(naked)]
unsafe extern "C" fn entry_trampoline() -> ! {
    naked_asm!(
        // `Context::new` places `entry` in `x19` and sets `sp` 16-byte aligned (`SP mod 16 = 0`
        // per AAPCS64 §6.4.5.2). `blr x19` sets `x30` to `udf #0` so returning aborts.
        "blr x19",
        "udf #0",
    );
}

/// Saves the caller's callee-saved registers (`x19`-`x29`), platform register `x18`, `SP`, and
/// link register `x30` into `*from`, and resumes execution from `*to`.
///
/// Register convention: `reference/arm/aapcs64.pdf` §6.1.1 and Table 2 (pp. 21-22), omitting SIMD
/// registers (`v8`-`v15`) under `-neon` / `softfloat`, and preserving `x18` per
/// `design/syscall-abi-in-registers/`.
///
/// # Safety
///
/// - `from` must point to writable storage for a `Context`.
/// - `to` must point to an initialized `Context` whose stack memory remains valid, exclusively
///   owned while suspended, and disjoint from the caller's active stack.
/// - Panics must abort rather than unwind across `switch`.
#[unsafe(naked)]
pub unsafe extern "C" fn switch(from: *mut Context, to: *const Context) {
    naked_asm!(
        "stp x18, x19, [x0, #{x18}]",
        "stp x20, x21, [x0, #{x20}]",
        "stp x22, x23, [x0, #{x22}]",
        "stp x24, x25, [x0, #{x24}]",
        "stp x26, x27, [x0, #{x26}]",
        "stp x28, x29, [x0, #{x28}]",
        "mov x9, sp",
        "stp x9, x30, [x0, #{sp}]",

        "ldp x18, x19, [x1, #{x18}]",
        "ldp x20, x21, [x1, #{x20}]",
        "ldp x22, x23, [x1, #{x22}]",
        "ldp x24, x25, [x1, #{x24}]",
        "ldp x26, x27, [x1, #{x26}]",
        "ldp x28, x29, [x1, #{x28}]",
        "ldp x9, x30, [x1, #{sp}]",
        "mov sp, x9",
        "ret",
        x18 = const offset_of!(Context, x18),
        x20 = const offset_of!(Context, x20),
        x22 = const offset_of!(Context, x22),
        x24 = const offset_of!(Context, x24),
        x26 = const offset_of!(Context, x26),
        x28 = const offset_of!(Context, x28),
        sp = const offset_of!(Context, sp),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicPtr, AtomicU64, Ordering};

    static ALIGN_FROM: AtomicPtr<Context> = AtomicPtr::new(core::ptr::null_mut());
    static ALIGN_TO: AtomicPtr<Context> = AtomicPtr::new(core::ptr::null_mut());
    static ALIGN_OBSERVED_SP: AtomicU64 = AtomicU64::new(0);

    #[unsafe(naked)]
    unsafe extern "C" fn capture_entry_sp() {
        naked_asm!(
            "mov x0, sp",
            "b {finish}",
            finish = sym capture_entry_sp_body,
        );
    }

    extern "C" fn capture_entry_sp_body(entry_sp: u64) {
        ALIGN_OBSERVED_SP.store(entry_sp, Ordering::Relaxed);
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
            let entry: extern "C" fn() = unsafe { core::mem::transmute(capture_entry_sp as unsafe extern "C" fn()) };
            let mut to = Context::new(entry, bottom, size);
            ALIGN_FROM.store(&raw mut from, Ordering::Relaxed);
            ALIGN_TO.store(&raw mut to, Ordering::Relaxed);
            ALIGN_OBSERVED_SP.store(0, Ordering::Relaxed);

            unsafe { switch(&raw mut from, &raw const to) };

            let observed = ALIGN_OBSERVED_SP.load(Ordering::Relaxed);
            assert_eq!(observed, expected_top);
            assert_eq!(observed & 0xf, 0);
            assert!(observed >= bottom as u64 && observed <= expected_top);
        }
    }

    #[test]
    #[should_panic]
    fn new_rejects_too_small_stack() {
        let mut raw = [0u8; 16];
        let entry: extern "C" fn() = unsafe { core::mem::transmute(capture_entry_sp as unsafe extern "C" fn()) };
        let _ = Context::new(entry, unsafe { raw.as_mut_ptr().add(1) }, 15);
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
