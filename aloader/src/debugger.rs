//! Debugger integration.
//!
//! The loader is a PE whose debug information is a PDB, which gdb cannot read, and the firmware
//! relocates it; so a debugger finds nothing of the loader's by symbol. It learns where the kernel
//! and dom0 were loaded from the serial log instead: the loader logs each binary's load bias, and,
//! when asked to, waits before it enters the kernel until the debugger clears rax. tools/run.py --gdb
//! reads these lines, and build-tool/src/emulator/gdb-helper.py lets the loader go.

use core::arch::asm;

/// What rax holds while the loader waits; gdb-helper.py checks for it before clearing rax.
const WAITING: u64 = 0x6764_6277_6169_7421;

/// Logs where the binary `name` was loaded, as `debugger: <name> at bias <bias>`.
pub fn loaded(name: &str, bias: usize) {
    log::info!("debugger: {} at bias {:#x}", name, bias);
}

/// Logs `debugger: waiting`, then spins until a debugger sets rax to anything but `WAITING`.
pub fn wait() {
    log::info!("debugger: waiting; clear rax to enter the kernel");
    unsafe {
        asm!(
            "2:",
            "pause",
            "cmp rax, {waiting}",
            "je 2b",
            waiting = in(reg) WAITING,
            inout("rax") WAITING => _,
            options(nomem, nostack),
        );
    }
}
