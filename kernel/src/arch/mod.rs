// SPDX-License-Identifier: MIT

//! The instruction set this kernel is built for. design/arch-module/.

#[cfg(target_arch = "x86_64")]
mod x86_64;

#[cfg(target_arch = "x86_64")]
pub use x86_64::*;

#[cfg(target_arch = "aarch64")]
mod aarch64;

#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

/// Whether a core whose state is `state` has loaded a space since boot: loading one hands out a tag, a
/// PCID here or an ASID on aarch64, which moves the core's next tag or, once they run out, its
/// generation from boot's. A core that has not holds no tag and so no translation of any space.
pub fn loaded_a_space(state: &verified::capability::kernel::CoreState) -> bool {
    state.generation != 1 || state.next_pcid != 1
}
