// SPDX-License-Identifier: MIT

//! The sizes the target's translation fixes, one implementation per target, selected by target_arch.
//! Each defines the same items with the same meaning, so the heap above this module counts in
//! pages and blocks without knowing the ISA. See design/arch-module/.

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;
#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;
