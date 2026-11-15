// SPDX-License-Identifier: MIT

//! User-space cooperative context switch for a placed carrier thread.
//!
//! Each target module under [`arch`] is selected by `cfg(target_arch)` with identical item names
//! and signatures (`design/arch-module/`). It holds only the saved execution context type,
//! [`switch`], and initial context setup on a caller-provided stack; schedulers live outside this
//! crate.
//!
//! # Target conventions and assumptions
//!
//! - **Floating-point and vector registers**: Both Atmosphere targets compile without floating-point
//!   or SIMD registers (`-mmx,-sse,+soft-float` on `x86_64`, `+v8a,+strict-align,-neon` with
//!   `softfloat` on `aarch64`), so `Context` saves only the target's integer callee-saved registers
//!   and stack pointer. On `aarch64`, `x18` is also saved because Atmosphere's syscall ABI preserves
//!   it (`design/syscall-abi-in-registers/`).
//! - **Thread pointer**: The thread pointer register belongs to the carrier's kernel thread and is
//!   shared by all cooperative tasks running on that carrier (`design/thread-pointer-cleared-on-switch/`).
//! - **Panics**: Atmosphere targets configure panic-strategy abort, so no unwinding crosses `switch`.
//! - **Stack overflow**: Task stacks have no guard page yet; overflowing a stack corrupts memory
//!   below the stack range until region-map guard pages exist.
//! - **Return-address signing**: If hardware pointer authentication for return addresses is ever
//!   enabled, switching stack pointers invalidates signed links and `switch` must be updated to
//!   resign or rebind them.
//!
//! Register conventions are cited to `reference/elf/x86-64-psABI-1.0.pdf` and
//! `reference/arm/aapcs64.pdf` and are held by `dom0`'s boot check on both targets
//! (`design/register-convention-of-an-assembly-leaf/`).

#![cfg_attr(not(test), no_std)]

pub mod arch;

pub use arch::{switch, Context};
