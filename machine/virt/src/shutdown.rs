//! Ends a run. design/machine-glue-below-the-kernel/.

use crate::instruction::{dsb, hvc, load, store, wait};

/// SYSTEM_OFF's function id. The function takes no argument and does not return (PSCI, ARM DEN 0022,
/// 5.1.9).
const SYSTEM_OFF: u32 = 0x8400_0008;

/// Bus 0's configuration space, where QEMU virt puts it under `highmem-ecam=off`, as
/// tools/orangepi-kvm.py launches it: ECAM, a function's 4 KiB at bus << 20 | device << 15 |
/// function << 12 (PCI Express Base 7.2.2), inside the device memory of the loader's identity map.
const CONFIG: usize = 0x3f00_0000;

/// The bytes between one device's configuration space and the next's on a bus: eight functions.
const DEVICE_BYTES: usize = 1 << 15;

/// The devices on a bus.
const DEVICES: usize = 32;

/// A function's vendor id, bits 15:0, and device id, bits 31:16 (PCI Local Bus 3.0, 6.2.1).
const ID: usize = 0x00;

/// A function's command register, bits 15:0; the status register above it takes a write of zero
/// as no change (PCI Local Bus 3.0, 6.2.2 and 6.2.3).
const COMMAND: usize = 0x04;

/// Memory Space: the function decodes its memory BARs.
const MEMORY_SPACE: u32 = 1 << 1;

/// Base Address Register 0 (PCI Local Bus 3.0, 6.2.5.1).
const BAR0: usize = 0x10;

/// QEMU's pvpanic PCI device: vendor 1b36, device 0011, as the firmware's shell lists it on the
/// board. Its BAR 0 is one register; a write of [`PANICKED`] to it is a guest panic, which ends
/// QEMU with status 1 under `-action panic=exit-failure`.
const PVPANIC: u32 = 0x0011_1b36;

/// The guest panicked.
const PANICKED: u32 = 1;

/// Where this crate places the pvpanic register, which the firmware leaves unplaced: the last page
/// of virt's 32-bit PCI memory window, which ends at 0x3eff_0000 and which the firmware fills from
/// 0x1000_0000 up.
const PANIC_REGISTER: u32 = 0x3efe_f000;

/// Reports a failed run to QEMU through the pvpanic device on bus 0 of the configuration space at
/// `config`, placing its register at physical address `physical`, which this core reaches at
/// `register`. Does nothing on a machine without one.
///
/// # Safety
///
/// `config` is bus 0's configuration space and `register` maps `physical`.
unsafe fn report_failure(config: usize, physical: u32, register: usize) {
    for device in 0..DEVICES {
        let function = config + device * DEVICE_BYTES;
        if load(function + ID) == PVPANIC {
            store(function + BAR0, physical);
            store(function + COMMAND, MEMORY_SPACE);
            // The register decodes only once both configuration writes have reached the device.
            dsb();
            store(register, PANICKED);
            return;
        }
    }
}

/// Ends the machine's run: a power-off after a run that succeeded, which QEMU exits with status 0,
/// and a guest panic after one that failed, which QEMU exits with status 1.
unsafe fn end(success: bool, config: usize, physical: u32, register: usize) {
    if success {
        hvc(SYSTEM_OFF, [0; 3]);
    } else {
        report_failure(config, physical, register);
    }
}

/// Refuses every key: this machine has no option.
pub fn set_option(key: &str, value: &str) -> bool {
    let _ = (key, value);
    false
}

/// Ends the run, then waits.
///
/// # Safety
///
/// The caller is not returning to the kernel.
pub unsafe fn shutdown(success: bool) -> ! {
    log::info!("The system is shutting down...");
    end(success, CONFIG, PANIC_REGISTER, PANIC_REGISTER as usize);
    loop {
        wait();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction::{events, Block, Event};

    /// Bus 0 as tools/orangepi-kvm.py launches virt with an ESP: the host bridge, the virtio drive
    /// and, when asked for, the pvpanic device in its first three slots, and no device in the others.
    fn bus(pvpanic: bool) -> Block {
        let bus = Block::of(DEVICES * DEVICE_BYTES);
        for device in 0..DEVICES {
            bus.set(device * DEVICE_BYTES + ID, u32::MAX);
        }
        bus.set(ID, 0x0008_1b36);
        bus.set(DEVICE_BYTES + ID, 0x1001_1af4);
        if pvpanic {
            bus.set(2 * DEVICE_BYTES + ID, 0x0011_1b36);
        }
        bus
    }

    #[test]
    fn a_run_that_succeeded_asks_the_firmware_for_system_off() {
        let bus = bus(true);
        let register = Block::new();
        unsafe { end(true, bus.base(), PANIC_REGISTER, register.base()) };
        // PSCI, ARM DEN 0022F.b, 5.1.9: SYSTEM_OFF's function id.
        assert_eq!(events(), [Event::Hvc { function: 0x8400_0008, arguments: [0; 3] }]);
    }

    #[test]
    fn a_run_that_failed_places_the_pvpanic_register_and_writes_the_panic() {
        let bus = bus(true);
        let register = Block::new();
        unsafe { end(false, bus.base(), PANIC_REGISTER, register.base()) };
        // PCI Local Bus 3.0, 6.2.2 and 6.2.5.1: the command register at 0x04, Memory Space its bit 1,
        // BAR 0 at 0x10; ECAM puts device 2 of bus 0 at 2 << 15.
        let pvpanic = bus.base() + (2 << 15);
        assert_eq!(
            events(),
            [
                Event::Store { register: pvpanic + 0x10, value: 0x3efe_f000 },
                Event::Store { register: pvpanic + 0x04, value: 0b10 },
                Event::Dsb,
                Event::Store { register: register.base(), value: 1 },
            ]
        );
    }

    #[test]
    fn a_run_that_failed_on_a_machine_without_pvpanic_writes_nothing() {
        let bus = bus(false);
        let register = Block::new();
        unsafe { end(false, bus.base(), PANIC_REGISTER, register.base()) };
        assert_eq!(events(), []);
    }

    #[test]
    fn the_register_lies_in_the_32_bit_window_and_the_identity_map_s_device_memory() {
        // QEMU virt's 32-bit PCI memory window ends at 0x3eff_0000, below its ECAM under
        // highmem-ecam=off, and the loader's identity map is device memory below RAM at 1 GiB.
        assert_eq!(PANIC_REGISTER % 0x1000, 0);
        assert!(PANIC_REGISTER >= 0x1000_0000 && PANIC_REGISTER + 0x1000 <= 0x3eff_0000);
        assert!(CONFIG + DEVICES * DEVICE_BYTES <= 0x4000_0000);
    }
}
