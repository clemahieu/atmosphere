// SPDX-License-Identifier: MIT

//! QEMU virt on aarch64: the PL011 console, the GICv3, the generic timer, the PSCI power-off and
//! start of a second core, and the SMMUv3 when the machine has one, with every stream refused.
//! design/machine-glue-below-the-kernel/.

#![no_std]

#[cfg(test)]
extern crate std;

mod console;
mod instruction;
mod interrupt;
mod iommu;
mod shutdown;
mod start;
mod timer;

use interrupt::Gic;

/// The timer's interrupt: the EL1 physical timer's, which QEMU virt's device tree gives as PPI 14 (node
/// `timer`, its second interrupt), interrupt 30 to the GIC.
pub const TIMER_VECTOR: u8 = 30;

/// The IOMMU fault's interrupt: the SMMUv3's event queue, which QEMU virt's device tree gives as SPI 74
/// when the machine has one (`iommu=smmuv3`, node `smmuv3@9050000`, `eventq`), interrupt 106 to the GIC.
pub const IOMMU_FAULT_VECTOR: u8 = 106;

/// The flush IPI's interrupt, the first SGI.
pub const FLUSH_VECTOR: u8 = 0;

/// The reschedule IPI's interrupt, the second SGI.
pub const RESCHEDULE_VECTOR: u8 = 1;

/// Cores a machine crate can name. The kernel asserts this is at least `verified::define::NUM_CPUS`.
pub const MAX_CPUS: usize = 32;

pub use console::{console, console_init, Console};
pub use iommu::{iommu_fault_dump, iommu_init, iommu_invalidate, iommu_map};
pub use shutdown::{set_option, shutdown};

/// Keeps the SMMUv3's base, when `boot` names one; the rest of what this crate drives is where QEMU
/// virt's device tree puts it. Once on the boot core, after the kernel copies `BootInfo`.
pub unsafe fn init(boot: &astd::boot::BootInfo) {
    iommu::keep(boot.iommu_base);
}

static GIC: Gic = unsafe { Gic::new(interrupt::DISTRIBUTOR, interrupt::REDISTRIBUTORS) };

/// Sets up the interrupt controller: the GIC's Distributor, with affinity routing and Group 1
/// forwarded. Once on the boot core, before any `interrupt_init_core`.
pub unsafe fn interrupt_init() {
    GIC.init();
}

/// Sets up `cpu`'s share of the interrupt controller, its Redistributor and its CPU interface, with
/// the flush SGI and the timer's PPI enabled, and leaves its one-shot timer unarmed. Once on each
/// core, which is `cpu`.
pub unsafe fn interrupt_init_core(cpu: usize) {
    GIC.init_core(cpu);
}

/// Arms this core's one-shot timer to fire `ticks` of the physical count from now.
pub fn set_timer(ticks: u64) {
    timer::arm(ticks);
}

/// Acknowledges the interrupt this core took and returns its id, one of the vector constants, or
/// nothing when none was pending. The interrupt's handler ends with [`end_of_interrupt`]. The
/// timer's shot is spent here: its line is a level, which would raise the interrupt again at the
/// end of this one.
pub fn acknowledge_interrupt() -> Option<u32> {
    acknowledge(&GIC)
}

fn acknowledge(gic: &Gic) -> Option<u32> {
    let id = gic.acknowledge()?;
    if id == u32::from(TIMER_VECTOR) {
        timer::disarm();
    }
    Some(id)
}

/// Ends the interrupt this core acknowledged last.
pub fn end_of_interrupt() {
    GIC.end();
}

/// Sends `vector`, an SGI, to `cpu`, returning once this core's interrupt controller has taken it.
pub fn send_ipi(cpu: usize, vector: u8) {
    interrupt::send(cpu, vector);
}

/// Starts `cpu` on `stack`, translating through `root`, at `entry` with `cpu` as its argument.
pub unsafe fn start_core(cpu: usize, stack: u64, entry: extern "C" fn(u64) -> !, root: u64) {
    start::start(cpu, stack, entry, root);
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use astd::boot::BootInfo;

    use crate::instruction::{events, set, Block, Event, System};
    use crate::interrupt::Gic;

    #[test]
    fn every_item_of_the_record_is_here_with_its_signature() {
        let _: unsafe fn(&BootInfo) = crate::init;
        let _: fn(&str, &str) -> bool = crate::set_option;
        let _: unsafe fn() = crate::console_init;
        let _: fn() -> crate::Console = crate::console;
        fn writer<T: core::fmt::Write>() {}
        writer::<crate::Console>();
        let _: unsafe fn() = crate::interrupt_init;
        let _: unsafe fn(usize) = crate::interrupt_init_core;
        let _: fn(u64) = crate::set_timer;
        let _: fn() -> Option<u32> = crate::acknowledge_interrupt;
        let _: fn() = crate::end_of_interrupt;
        let _: fn(usize, u8) = crate::send_ipi;
        let _: unsafe fn(usize, u64, extern "C" fn(u64) -> !, u64) = crate::start_core;
        let _: unsafe fn(bool) -> ! = crate::shutdown;
        let _: unsafe fn() = crate::iommu_init;
        let _: unsafe fn(usize, usize, usize, u64) -> Result<(), &'static str> = crate::iommu_map;
        let _: unsafe fn(usize, usize, usize, u64) -> Result<(), &'static str> = crate::iommu_invalidate;
        let _: fn() -> Result<(), &'static str> = crate::iommu_fault_dump;
        let _: u8 = crate::TIMER_VECTOR;
        let _: u8 = crate::IOMMU_FAULT_VECTOR;
        let _: u8 = crate::FLUSH_VECTOR;
        let _: u8 = crate::RESCHEDULE_VECTOR;
        let _: usize = crate::MAX_CPUS;
    }

    #[test]
    fn the_ipis_are_sgis_and_no_two_interrupts_share_an_id() {
        assert!(crate::FLUSH_VECTOR < 16);
        assert!(crate::RESCHEDULE_VECTOR < 16);
        let ids = [crate::TIMER_VECTOR, crate::IOMMU_FAULT_VECTOR, crate::FLUSH_VECTOR, crate::RESCHEDULE_VECTOR];
        for (i, a) in ids.iter().enumerate() {
            assert!(ids[i + 1..].iter().all(|b| a != b));
        }
    }

    #[test]
    fn the_timer_s_acknowledgement_spends_its_shot_before_the_interrupt_ends() {
        let block = Block::new();
        let gic = unsafe { Gic::new(block.base(), block.base()) };
        set(System::IccIar1, u64::from(crate::TIMER_VECTOR));
        set(System::CntpCtl, 0b001);

        assert_eq!(crate::acknowledge(&gic), Some(30));
        gic.end();

        let writes: Vec<Event> = events().into_iter().filter(|event| matches!(event, Event::Write { .. })).collect();
        assert_eq!(
            writes,
            [
                Event::Write { register: System::CntpCtl, value: 0 },
                Event::Write { register: System::IccEoir1, value: 30 },
            ]
        );
    }

    #[test]
    fn another_interrupt_s_acknowledgement_leaves_the_timer_armed() {
        let block = Block::new();
        let gic = unsafe { Gic::new(block.base(), block.base()) };
        set(System::IccIar1, u64::from(crate::FLUSH_VECTOR));

        assert_eq!(crate::acknowledge(&gic), Some(0));

        assert!(events().iter().all(|event| !matches!(event, Event::Write { .. })));
    }

    #[test]
    fn a_spurious_acknowledgement_leaves_the_timer_armed() {
        let block = Block::new();
        let gic = unsafe { Gic::new(block.base(), block.base()) };
        set(System::IccIar1, 1023);

        assert_eq!(crate::acknowledge(&gic), None);

        assert_eq!(events(), [Event::Read { register: System::IccIar1 }]);
    }

    #[test]
    fn the_timer_s_and_the_ipis_interrupts_are_private_to_a_core() {
        // IHI 0069 2.2: INTIDs 0 to 15 are SGIs and 16 to 31 PPIs, the two kinds a Redistributor's
        // SGI_base configures.
        assert!((16..32).contains(&crate::TIMER_VECTOR));
        assert!(crate::FLUSH_VECTOR < 16);
        assert!(crate::RESCHEDULE_VECTOR < 16);
    }

    #[test]
    fn init_takes_a_boot_info_without_an_iommu() {
        unsafe { crate::init(&BootInfo::empty()) };
    }

    #[test]
    fn set_option_refuses_every_key() {
        assert!(!crate::set_option("qemu_debug_exit_io_base", "244"));
        assert!(!crate::set_option("bochs_apm_io_base", "8900"));
        assert!(!crate::set_option("nologo", "1"));
        assert!(!crate::set_option("", ""));
    }

    #[test]
    fn iommu_init_without_hardware_returns() {
        unsafe { crate::iommu_init() };
    }

    #[test]
    fn iommu_map_without_hardware_refuses() {
        assert_eq!(unsafe { crate::iommu_map(0, 0, 0, 0) }, Err("No IOMMU available"));
        assert_eq!(unsafe { crate::iommu_map(255, 31, 7, 0) }, Err("No IOMMU available"));
    }

    #[test]
    fn iommu_invalidate_without_hardware_refuses() {
        assert_eq!(unsafe { crate::iommu_invalidate(0, 0, 0, 0) }, Err("No IOMMU hardware"));
    }

    #[test]
    fn iommu_fault_dump_without_hardware_refuses() {
        assert_eq!(crate::iommu_fault_dump(), Err("No IOMMU hardware"));
    }

    #[test]
    #[should_panic(expected = "Device id out of range")]
    fn iommu_map_rejects_a_bus_past_255() {
        unsafe {
            let _ = crate::iommu_map(256, 0, 0, 0);
        }
    }

    #[test]
    #[should_panic(expected = "Device id out of range")]
    fn iommu_invalidate_rejects_a_device_past_31() {
        unsafe {
            let _ = crate::iommu_invalidate(0, 32, 0, 0);
        }
    }
}
