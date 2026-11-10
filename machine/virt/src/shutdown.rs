//! Ends a run. design/machine-glue-below-the-kernel/.

use crate::instruction::{hvc, wait};

/// SYSTEM_OFF's function id. The function takes no argument and does not return (PSCI, ARM DEN 0022,
/// 5.1.9).
const SYSTEM_OFF: u32 = 0x8400_0008;

/// Refuses every key: this machine has no option.
pub fn set_option(key: &str, value: &str) -> bool {
    let _ = (key, value);
    false
}

/// Powers the machine off after a run that succeeded. QEMU exits with status 0 when its guest powers
/// off, which the runner reads as success, so a run that failed stays on until the runner's timeout.
unsafe fn power_off(success: bool) {
    if success {
        hvc(SYSTEM_OFF, [0; 3]);
    }
}

/// Ends the run, then waits.
///
/// # Safety
///
/// The caller is not returning to the kernel.
pub unsafe fn shutdown(success: bool) -> ! {
    log::info!("The system is shutting down...");
    power_off(success);
    loop {
        wait();
    }
}

#[cfg(test)]
mod tests {
    use crate::instruction::{events, Event};

    #[test]
    fn a_run_that_succeeded_asks_the_firmware_for_system_off() {
        unsafe { super::power_off(true) };
        // PSCI, ARM DEN 0022F.b, 5.1.9: SYSTEM_OFF's function id.
        assert_eq!(events(), [Event::Hvc { function: 0x8400_0008, arguments: [0; 3] }]);
    }

    #[test]
    fn a_run_that_failed_asks_the_firmware_for_nothing() {
        unsafe { super::power_off(false) };
        assert_eq!(events(), []);
    }
}
