//! IOAPIC.

use core::mem::MaybeUninit;

use x86::apic::{ioapic::IoApic, ApicControl};

/// Reached only by `init` and then `init_cpu`, both on CPU 0 during its boot; an application
/// processor leaves the IOAPIC routed to CPU 0 and never touches it.
static mut IOAPIC: MaybeUninit<IoApic> = MaybeUninit::zeroed();

pub unsafe fn init(ioapic_base: usize) {
    log::debug!("IOAPIC base: {:#x}", ioapic_base);
    let mut ioapic = IoApic::new(ioapic_base);
    // Exclusive: see IOAPIC.
    (*&raw mut IOAPIC).write(ioapic);
}

pub unsafe fn init_cpu() {
    let mut cpu = crate::cpu::get_current();

    // Exclusive: see IOAPIC. init wrote it first.
    let ioapic = (*&raw mut IOAPIC).assume_init_mut();
    ioapic.enable(0, crate::cpu::get_cpu_id() as u8);
    ioapic.enable(1, crate::cpu::get_cpu_id() as u8);

    let xapic = cpu.xapic.assume_init_mut();

    log::debug!("Init CPU {} {} {}", cpu.id, xapic.id(), xapic.logical_id());
}
