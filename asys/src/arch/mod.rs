// SPDX-License-Identifier: MIT

//! The instruction that invokes a capability and the registers it carries each position in, one
//! implementation per target, selected by target_arch. Each defines `syscall` with the same signature,
//! so the operations above this module name positions, not registers, and the frame's length and the
//! words of its program counter and stack pointer, which read registers and write registers index. This is asys's copy of the tables
//! under Registers in design/syscall-abi-in-registers/; asys does not link the kernel's arch module, so
//! that record is the one source both follow. See design/arch-module/, item 4.

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::{syscall, FRAME_WORDS, PC_WORD, SP_WORD};
#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::{syscall, FRAME_WORDS, PC_WORD, SP_WORD};
