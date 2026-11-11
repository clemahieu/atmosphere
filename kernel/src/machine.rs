// SPDX-License-Identifier: MIT

//! The machine this kernel is built for, re-exported under one name. design/machine-glue-below-the-kernel/.

#[cfg(target_arch = "x86_64")]
pub use machine_pc::*;

#[cfg(target_arch = "aarch64")]
pub use machine_virt::*;

const _: () = assert!(MAX_CPUS >= verified::define::NUM_CPUS);
