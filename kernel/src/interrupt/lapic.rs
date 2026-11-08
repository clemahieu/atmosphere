//! LAPIC, driven in xAPIC mode by `x86_xapic`.

use core::arch::asm;
use core::mem::MaybeUninit;
use core::slice;

use super::x86_xapic::{Icr, XAPIC};
use verified::define::PCID_ENABLE_MASK;
use crate::arch::msr;

use super::Cycles;
use crate::boot::ap_start::StartTrampoline;
use crate::{boot, cpu};

/// Returns the 4KiB LAPIC region.
unsafe fn probe_apic() -> &'static mut [u32] {
    let msr27: u32 = msr::rdmsr(msr::APIC_BASE) as u32;
    let lapic = (msr27 & 0xffff_0000) as usize as *mut u32;

    slice::from_raw_parts_mut(lapic, 4096 / 4)
}

/// Initializes LAPIC in xAPIC mode.
pub unsafe fn init() {
    let cpu = cpu::get_current();

    let apic_region = probe_apic();
    log::debug!("APIC base: {:?}", apic_region as *mut _ as *mut u8);

    let mut xapic = XAPIC::new(apic_region);
    xapic.attach();
    xapic.tsc_enable(32);

    cpu.xapic.write(xapic);
}

/// Arms the timer interrupt.
pub fn set_timer(cycles: Cycles) {
    let xapic = unsafe {
        (&mut *crate::cpu::get_current_cpu_field_ptr!(xapic, MaybeUninit<XAPIC>)).assume_init_mut()
    };

    // FIXME: Truncated
    xapic.tsc_set_oneshot(cycles.0 as u32);
}

/// Acknowledges an interrupt.
pub fn end_of_interrupt() {
    let xapic = unsafe {
        (&mut *crate::cpu::get_current_cpu_field_ptr!(xapic, MaybeUninit<XAPIC>)).assume_init_mut()
    };

    xapic.eoi();
}

/// Sends an interrupt to a CPU, returning once the local APIC has taken it.
pub fn send_ipi(cpu_id: usize, vector: u8) {
    let xapic = unsafe {
        (&mut *crate::cpu::get_current_cpu_field_ptr!(xapic, MaybeUninit<XAPIC>)).assume_init_mut()
    };
    // FIXME: X2APIC APIC ID
    unsafe { xapic.send_ipi(Icr::fixed(cpu_id as u8, vector)) };
}

/// Waits between start-up IPIs. The architecture asks for 10 ms and 200 us. No timer is calibrated this
/// early, so this is a fixed spin, which only QEMU has exercised.
fn start_delay() {
    for _ in 0..100_000 {
        core::hint::spin_loop();
    }
}

/// Boots an application processor.
pub unsafe fn boot_ap(cpu_id: u32, stack: u64, code: u64) {
    let xapic = unsafe {
        (&mut *crate::cpu::get_current_cpu_field_ptr!(xapic, MaybeUninit<XAPIC>)).assume_init_mut()
    };

    let boot_info = boot::get_boot_info();

    let mut cr3 = boot_info.pml4 as u64;
    if boot_info.pcide {
        cr3 |= PCID_ENABLE_MASK as u64;
    }

    let start_page = StartTrampoline::new()
        .with_code(code)
        .with_cr3(cr3)
        .with_stack(stack)
        .with_arg(cpu_id as u64)
        .start_page();

    log::info!("page = {:#x}", start_page);

    // FIXME: X2APIC APIC ID
    let apic_id = cpu_id as u8;
    xapic.ipi_init(apic_id);
    start_delay();
    // A core takes the first STARTUP it sees and ignores a later one; the second is for the first
    // being lost, as the universal start-up algorithm allows.
    xapic.ipi_startup(apic_id, start_page);
    start_delay();
    xapic.ipi_startup(apic_id, start_page);
}
