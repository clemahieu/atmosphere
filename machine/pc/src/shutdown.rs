//! Ends a run. design/machine-glue-below-the-kernel/.

use core::arch::asm;

use astd::sync::Mutex;

use crate::port;

static QEMU_DEBUG_EXIT: Mutex<Option<u16>> = Mutex::new(None);
static BOCHS_APM: Mutex<Option<u16>> = Mutex::new(None);

#[cfg(test)]
pub(crate) fn qemu_debug_exit_port() -> Option<u16> {
    *QEMU_DEBUG_EXIT.lock()
}

#[cfg(test)]
pub(crate) fn bochs_apm_port() -> Option<u16> {
    *BOCHS_APM.lock()
}

/// Takes `qemu_debug_exit_io_base` and `bochs_apm_io_base`. A value that is not a `u16` is refused.
pub fn set_option(key: &str, value: &str) -> bool {
    let Ok(port) = value.parse::<u16>() else {
        return false;
    };
    match key {
        "qemu_debug_exit_io_base" => *QEMU_DEBUG_EXIT.lock() = Some(port),
        "bochs_apm_io_base" => *BOCHS_APM.lock() = Some(port),
        _ => return false,
    }
    true
}

/// Ends the run, then halts.
///
/// # Safety
///
/// The caller is not returning to the kernel.
pub unsafe fn shutdown(success: bool) -> ! {
    log::info!("The system is shutting down...");

    // isa-debug-exit: a write of 0 makes QEMU exit with status 1, `(value << 1) | 1`.
    if let Some(io_base) = *QEMU_DEBUG_EXIT.lock() {
        if !success {
            log::debug!(
                "Trying QEMU isa-debug-exit shutdown (IO Port {:#x})",
                io_base
            );
            port::outw(io_base, 0x0);
        }
    }

    if let Some(io_base) = *BOCHS_APM.lock() {
        let success_marker = if success {
            "BOCHS_SUCCESS"
        } else {
            "BOCHS_FAILURE"
        };
        log::debug!(
            "Trying Bochs APM shutdown (IO Port {:#x}) - {}",
            io_base,
            success_marker
        );

        let shutdown = "Shutdown";

        for ch in shutdown.chars() {
            port::outb(io_base, ch as u8);
        }
    }

    // QEMU ACPI poweroff.
    port::outw(0x604, 0x2000);

    log::info!("It is now safe to turn off your computer");

    loop {
        asm!("hlt");
    }
}
