//! Starting an application processor. The local APIC itself is `machine`'s; this builds the trampoline
//! and asks the machine to send INIT and STARTUP. design/machine-glue-below-the-kernel/.

use crate::boot::ap_start::StartTrampoline;
use crate::{boot, machine};

/// Boots an application processor.
pub unsafe fn boot_ap(cpu_id: u32, stack: u64, code: u64) {
    let boot_info = boot::get_boot_info();

    let mut cr3 = boot_info.pml4 as u64;
    if boot_info.pcide {
        cr3 |= crate::arch::CR3_NO_FLUSH;
    }

    let start_page = StartTrampoline::new()
        .with_code(code)
        .with_cr3(cr3)
        .with_stack(stack)
        .with_arg(cpu_id as u64)
        .start_page();

    log::info!("page = {:#x}", start_page);

    machine::send_init_sipi(cpu_id as usize, start_page);
}
