//! The x86_64 PC machine: COM1, the xAPIC, the IOAPIC, the 8259s and the IOMMU. design/machine-glue-below-the-kernel/.

#![no_std]

mod ap_start;
mod console;
mod ioapic;
mod iommu;
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

/// Starts `cpu` on `stack`, translating through `root`, at `entry` with `cpu` as its argument.
///
/// `root` is the value the new core loads as its translation base. On this machine that is CR3,
/// and bit 63 asks the trampoline to turn PCID on.
pub unsafe fn start_core(cpu: usize, stack: u64, entry: extern "C" fn(u64) -> !, root: u64) {
    let start_page = ap_start::StartTrampoline::new()
        .with_code(entry as usize as u64)
        .with_cr3(root)
        .with_stack(stack)
        .with_arg(cpu as u64)
        .start_page();
    log::info!("page = {:#x}", start_page);
    lapic::send_init_sipi(cpu, start_page);
}

/// Keeps the IOMMU base from `boot`. Once on the boot core, after the kernel copies `BootInfo`.
pub unsafe fn init(boot: &astd::boot::BootInfo) {
    iommu::store_base(boot.iommu_base);
}

pub use iommu::{iommu_fault_dump, iommu_init, iommu_invalidate, iommu_map};

#[cfg(test)]
mod tests {
    #[test]
    fn the_console_is_a_writer() {
        fn assert_writer<T: core::fmt::Write>(_: &mut T) {}
        let mut console = crate::console();
        assert_writer(&mut console);
    }

    #[test]
    fn iommu_map_without_hardware_refuses() {
        let err = unsafe { crate::iommu_map(0, 0, 0, 0) };
        assert_eq!(err, Err("No IOMMU available"));
    }

    #[test]
    fn iommu_invalidate_without_hardware_refuses() {
        let err = unsafe { crate::iommu_invalidate(0, 0, 0, 0) };
        assert_eq!(err, Err("No IOMMU hardware"));
    }

    #[test]
    #[should_panic(expected = "Device id out of range")]
    fn iommu_map_rejects_a_bus_past_255() {
        unsafe {
            let _ = crate::iommu_map(256, 0, 0, 0);
        }
    }
}
