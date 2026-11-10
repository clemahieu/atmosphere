//! QEMU virt on aarch64: the PL011 console and the PSCI power-off, on a machine without an IOMMU. The
//! items of the interrupt controller, the timer and the start of a second core are declared and panic
//! with their names. design/machine-glue-below-the-kernel/.

#![no_std]

#[cfg(test)]
extern crate std;

mod console;
mod instruction;
mod iommu;
mod shutdown;

/// The timer's interrupt: the EL1 physical timer's, which QEMU virt's device tree gives as PPI 14 (node
/// `timer`, its second interrupt), interrupt 30 to the GIC.
pub const TIMER_VECTOR: u8 = 30;

/// The IOMMU fault's interrupt: the SMMUv3's event queue, which QEMU virt's device tree gives as SPI 74
/// when the machine has one (`iommu=smmuv3`, node `smmuv3@9050000`, `eventq`), interrupt 106 to the GIC.
pub const IOMMU_FAULT_VECTOR: u8 = 106;

/// The flush IPI's interrupt, the first SGI.
pub const FLUSH_VECTOR: u8 = 0;

/// Cores a machine crate can name. The kernel asserts this is at least `verified::define::NUM_CPUS`.
pub const MAX_CPUS: usize = 32;

pub use console::{console, console_init, Console};
pub use iommu::{iommu_fault_dump, iommu_init, iommu_invalidate, iommu_map};
pub use shutdown::{set_option, shutdown};

/// Keeps nothing: what this crate drives is where QEMU virt's device tree puts it, and `boot` names no
/// IOMMU. Once on the boot core, after the kernel copies `BootInfo`.
pub unsafe fn init(boot: &astd::boot::BootInfo) {
    assert!(boot.iommu_base.is_none(), "machine-virt drives no IOMMU");
}

/// Sets up the interrupt controller. Once on the boot core, before any `interrupt_init_core`.
pub unsafe fn interrupt_init() {
    unimplemented!("interrupt_init");
}

/// Sets up `cpu`'s share of the interrupt controller and points its one-shot timer at
/// [`TIMER_VECTOR`], unarmed. Once on each core.
pub unsafe fn interrupt_init_core(cpu: usize) {
    let _ = cpu;
    unimplemented!("interrupt_init_core");
}

/// Routes the external interrupts to `cpu`.
pub unsafe fn route_external(cpu: usize) {
    let _ = cpu;
    unimplemented!("route_external");
}

/// Arms this core's one-shot timer.
pub fn set_timer(ticks: u64) {
    let _ = ticks;
    unimplemented!("set_timer");
}

/// Acknowledges an interrupt on this core.
pub fn end_of_interrupt() {
    unimplemented!("end_of_interrupt");
}

/// Sends `vector` to `cpu`, returning once this core's interrupt controller has taken it.
pub fn send_ipi(cpu: usize, vector: u8) {
    let _ = (cpu, vector);
    unimplemented!("send_ipi");
}

/// Starts `cpu` on `stack`, translating through `root`, at `entry` with `cpu` as its argument.
pub unsafe fn start_core(cpu: usize, stack: u64, entry: extern "C" fn(u64) -> !, root: u64) {
    let _ = (cpu, stack, entry, root);
    unimplemented!("start_core");
}

#[cfg(test)]
mod tests {
    use std::boxed::Box;
    use std::string::String;

    use astd::boot::BootInfo;

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
        let _: unsafe fn(usize) = crate::route_external;
        let _: fn(u64) = crate::set_timer;
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
        let _: usize = crate::MAX_CPUS;
    }

    #[test]
    fn the_flush_ipi_is_an_sgi_and_no_two_interrupts_share_an_id() {
        assert!(crate::FLUSH_VECTOR < 16);
        assert_ne!(crate::TIMER_VECTOR, crate::FLUSH_VECTOR);
        assert_ne!(crate::TIMER_VECTOR, crate::IOMMU_FAULT_VECTOR);
        assert_ne!(crate::IOMMU_FAULT_VECTOR, crate::FLUSH_VECTOR);
    }

    extern "C" fn entry(_: u64) -> ! {
        unreachable!()
    }

    #[test]
    fn an_item_that_is_not_written_panics_with_its_name() {
        let items: [(&str, Box<dyn Fn() + std::panic::UnwindSafe>); 7] = [
            ("interrupt_init", Box::new(|| unsafe { crate::interrupt_init() })),
            ("interrupt_init_core", Box::new(|| unsafe { crate::interrupt_init_core(0) })),
            ("route_external", Box::new(|| unsafe { crate::route_external(0) })),
            ("set_timer", Box::new(|| crate::set_timer(1))),
            ("end_of_interrupt", Box::new(crate::end_of_interrupt)),
            ("send_ipi", Box::new(|| crate::send_ipi(1, crate::FLUSH_VECTOR))),
            ("start_core", Box::new(|| unsafe { crate::start_core(1, 0, entry, 0) })),
        ];
        for (name, item) in items {
            let panic = std::panic::catch_unwind(item).expect_err(name);
            // The message is a literal once the compiler has folded the name into it.
            let message = panic.downcast_ref::<&str>().copied().or(panic.downcast_ref::<String>().map(String::as_str));
            assert_eq!(message, Some(std::format!("not implemented: {}", name).as_str()));
        }
    }

    #[test]
    fn init_takes_a_boot_info_without_an_iommu() {
        unsafe { crate::init(&BootInfo::empty()) };
    }

    #[test]
    #[should_panic(expected = "machine-virt drives no IOMMU")]
    fn init_refuses_a_boot_info_with_an_iommu() {
        let mut boot = BootInfo::empty();
        boot.iommu_base = Some(0x0905_0000);
        unsafe { crate::init(&boot) };
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
