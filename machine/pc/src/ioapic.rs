//! IOAPIC, written from the Intel 82093AA I/O APIC datasheet (order number 290566-001).

use core::mem::MaybeUninit;

use super::TIMER_VECTOR;

/// An I/O APIC, reached through its register select IOREGSEL at the base and its data window
/// IOWIN at base + 10h. Datasheet Table 1.
struct IoApic {
    base: usize,
}

/// The register index of IOREDTBL0; entry n is the pair at 10h + 2n (bits 31:0) and 11h + 2n
/// (bits 63:32). Datasheet Table 2 and §3.2.4.
const IOREDTBL: u8 = 0x10;

/// The redirection entry that routes input `irq` to vector TIMER_VECTOR + irq at the local APIC
/// `apic_id`: fixed delivery, physical destination mode, active high, edge triggered and unmasked,
/// which is bits 16:8 clear, and the APIC ID in bits 63:56. Datasheet §3.2.4.
const fn redirection_entry(irq: u8, apic_id: u8) -> u64 {
    (apic_id as u64) << 56 | (TIMER_VECTOR as u64 + irq as u64)
}

impl IoApic {
    unsafe fn write(&mut self, register: u8, value: u32) {
        (self.base as *mut u32).write_volatile(register as u32);
        ((self.base + 0x10) as *mut u32).write_volatile(value);
    }

    /// Routes input `irq` to the local APIC `apic_id`.
    unsafe fn enable(&mut self, irq: u8, apic_id: u8) {
        let entry = redirection_entry(irq, apic_id);
        self.write(IOREDTBL + 2 * irq, entry as u32);
        self.write(IOREDTBL + 2 * irq + 1, (entry >> 32) as u32);
    }
}

/// Reached only by `init` and then `route`, both on CPU 0 during its boot; an application
/// processor leaves the IOAPIC routed to CPU 0 and never touches it.
static mut IOAPIC: MaybeUninit<IoApic> = MaybeUninit::zeroed();

pub unsafe fn init(ioapic_base: usize) {
    log::debug!("IOAPIC base: {:#x}", ioapic_base);
    // Exclusive: see IOAPIC.
    (*&raw mut IOAPIC).write(IoApic { base: ioapic_base });
}

/// Routes inputs 0 and 1 to the local APIC `apic_id`.
pub unsafe fn route(apic_id: u8) {
    // Exclusive: see IOAPIC. init wrote it first, and only the boot core routes.
    let ioapic = (*&raw mut IOAPIC).assume_init_mut();
    ioapic.enable(0, apic_id);
    ioapic.enable(1, apic_id);
}

// The entries the x86 crate's IoApic::enable wrote.
const _: () = assert!(redirection_entry(0, 2) == 0x0200_0000_0000_0020);
const _: () = assert!(redirection_entry(1, 0) == 0x0000_0000_0000_0021);
