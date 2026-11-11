// SPDX-License-Identifier: MIT

//! Debugger integration.
//!
//! The loader is a PE whose debug information is a PDB, which gdb cannot read, and the firmware
//! relocates it; so a debugger finds nothing of the loader's by symbol. It learns where the kernel
//! and dom0 were loaded from the serial log instead: the loader logs each binary's load bias, and,
//! when asked to, waits before it enters the kernel until the debugger clears the register the arch
//! module names. tools/run.py --gdb reads these lines, and tools/gdb-helper.py, which tools/gdb.py
//! sources, lets the loader go.

use crate::arch;

/// Logs where the binary `name` was loaded, as `debugger: <name> at bias <bias>`.
pub fn loaded(name: &str, bias: usize) {
    log::info!("debugger: {} at bias {:#x}", name, bias);
}

/// Logs `debugger: waiting`, then spins until a debugger clears that register.
pub fn wait() {
    log::info!("debugger: waiting; clear {} to enter the kernel", arch::DEBUGGER_REGISTER);
    arch::wait_for_debugger();
}
