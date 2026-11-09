//! The local APIC, one register page shared by every core.

use super::msr::{rdmsr, APIC_BASE};
use super::x86_xapic::{Icr, XAPIC};

/// Written once by `probe` on the boot core, before another core runs; only read after that.
static mut MMIO: *mut u32 = core::ptr::null_mut();

/// The register page `IA32_APIC_BASE` names on this core. The address is the same on every core.
pub unsafe fn probe() {
    let base = rdmsr(APIC_BASE) as usize;
    let mmio = (base & 0xffff_0000) as *mut u32;
    MMIO = mmio;
    log::debug!("APIC base: {:?}", mmio);
}

fn lapic() -> XAPIC {
    XAPIC::from_mmio(unsafe { MMIO })
}

/// Enables this core's local APIC and points its one-shot timer at `vector`, unarmed.
pub unsafe fn init_core(vector: u8) {
    let mut xapic = lapic();
    xapic.attach();
    xapic.tsc_enable(vector);
}

/// Arms this core's one-shot timer. The count register holds 32 bits, as the kernel's timer did.
pub fn set_timer(ticks: u64) {
    lapic().tsc_set_oneshot(ticks as u32);
}

pub fn end_of_interrupt() {
    lapic().eoi();
}

pub fn send_ipi(cpu: usize, vector: u8) {
    unsafe { lapic().send_ipi(Icr::fixed(cpu as u8, vector)) };
}

pub fn ids() -> (u32, u32) {
    let xapic = lapic();
    (xapic.id(), xapic.logical_id())
}

/// Waits between start-up IPIs. The architecture asks for 10 ms and 200 us. No timer is calibrated this
/// early, so this is a fixed spin, which only QEMU has exercised.
fn start_delay() {
    for _ in 0..100_000 {
        core::hint::spin_loop();
    }
}

/// INIT, then two STARTUPs at `start_page`. A core takes the first STARTUP it sees and ignores a later
/// one; the second is for the first being lost, as the universal start-up algorithm allows.
pub unsafe fn send_init_sipi(cpu: usize, start_page: u8) {
    let mut xapic = lapic();
    let apic_id = cpu as u8;
    xapic.ipi_init(apic_id);
    start_delay();
    xapic.ipi_startup(apic_id, start_page);
    start_delay();
    xapic.ipi_startup(apic_id, start_page);
}
