//! The machine this kernel is built for, re-exported under one name. design/machine-glue-below-the-kernel/.

#[cfg(target_arch = "x86_64")]
pub use machine_pc::*;

const _: () = assert!(MAX_CPUS >= verified::define::NUM_CPUS);
