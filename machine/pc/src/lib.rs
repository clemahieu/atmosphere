//! The x86_64 PC machine: COM1, the xAPIC, the IOAPIC and the 8259s. design/machine-glue-below-the-kernel/.

#![no_std]

mod console;
mod ioapic;
mod lapic;
mod mps;
mod msr;
mod port;
mod x86_xapic;

/// The timer's vector.
pub const TIMER_VECTOR: u8 = 32;

/// The IOMMU fault's vector.
pub const IOMMU_FAULT_VECTOR: u8 = 33;

/// The flush IPI's vector.
pub const FLUSH_VECTOR: u8 = 34;

/// Cores a machine crate can name. The kernel asserts this is at least `verified::define::NUM_CPUS`.
pub const MAX_CPUS: usize = 32;

pub use console::{console, console_init, Console};

const PIC1_DATA: u16 = 0x21;
const PIC2_DATA: u16 = 0xa1;

/// Masks the 8259s and finds the IOAPIC. Once on the boot core, before any `interrupt_init_core`.
pub unsafe fn interrupt_init() {
    let pic1 = port::inb(PIC1_DATA);
    let pic2 = port::inb(PIC2_DATA);
    log::debug!("PIC masks: PIC1={:#x?}, PIC2={:#x?}", pic1, pic2);
    port::outb(PIC1_DATA, 0xff);
    port::outb(PIC2_DATA, 0xff);

    lapic::probe();
    let ioapic_base = mps::probe_ioapic();
    ioapic::init(ioapic_base);
}

/// Enables `cpu`'s local APIC and points its one-shot timer at [`TIMER_VECTOR`], unarmed. Once on each core.
pub unsafe fn interrupt_init_core(cpu: usize) {
    let _ = cpu;
    lapic::init_core(TIMER_VECTOR);
}

/// Routes the IOAPIC's inputs to `cpu`.
pub unsafe fn route_external(cpu: usize) {
    ioapic::route(cpu as u8);
    let (id, logical) = lapic::ids();
    log::debug!("Init CPU {} {} {}", cpu, id, logical);
}

/// Arms this core's one-shot timer.
pub fn set_timer(ticks: u64) {
    lapic::set_timer(ticks);
}

/// Acknowledges an interrupt on this core.
pub fn end_of_interrupt() {
    lapic::end_of_interrupt();
}

/// Sends `vector` to `cpu`, returning once this core's local APIC has taken it.
pub fn send_ipi(cpu: usize, vector: u8) {
    lapic::send_ipi(cpu, vector);
}

/// INIT, then two STARTUPs at `start_page`, for the kernel's `boot_ap`. `start_core` replaces that.
pub unsafe fn send_init_sipi(cpu: usize, start_page: u8) {
    lapic::send_init_sipi(cpu, start_page);
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_console_is_a_writer() {
        fn assert_writer<T: core::fmt::Write>(_: &mut T) {}
        let mut console = crate::console();
        assert_writer(&mut console);
    }
}
