//! Each core checks at start-up that ring 0 cannot write through a read-only mapping, which holds
//! only while CR0.WP is set.
//!
//! The check maps one kernel page read-only for one write. The page fault handler recognises the
//! fault by its instruction and resumes after it, so the write faults without stopping the machine.

use core::arch::{asm, global_asm};

use verified::arch::Registers;

/// The page the check writes to.
#[repr(C, align(4096))]
struct Page([u8; 4096]);

static mut PROBE_PAGE: Page = Page([0; 4096]);

/// A page table entry's present, writable and page size bits, and its address.
const PRESENT: u64 = 1 << 0;
const WRITABLE: u64 = 1 << 1;
const PAGE_SIZE: u64 = 1 << 7;
const ADDRESS: u64 = 0x000f_ffff_ffff_f000;

// write_protect_probe(address) writes a byte there and returns 0, or the page fault's error code
// when the write faulted: fixup resumes at write_protect_probe_done with the code in rax.
global_asm!(
    ".global write_protect_probe",
    ".global write_protect_probe_write",
    ".global write_protect_probe_done",
    "write_protect_probe:",
    "xor eax, eax",
    "write_protect_probe_write:",
    "mov byte ptr [rdi], 1",
    "write_protect_probe_done:",
    "ret",
);

unsafe extern "C" {
    fn write_protect_probe(address: *mut u8) -> u64;
    fn write_protect_probe_write();
    fn write_protect_probe_done();
}

/// The leaf page table entry that maps address under the current CR3. Page tables lie in the
/// identity map the loader built, so their physical addresses are usable as pointers.
unsafe fn leaf_entry(address: u64) -> *mut u64 {
    let cr3: u64;
    asm!("mov {}, cr3", out(reg) cr3);
    let mut table = (cr3 & ADDRESS) as *mut u64;
    for level in (1..4).rev() {
        let entry = *table.add((address >> (12 + 9 * level)) as usize & 0x1ff);
        assert!(entry & PRESENT != 0 && entry & PAGE_SIZE == 0, "the probe page is not mapped by a 4 KiB entry");
        table = (entry & ADDRESS) as *mut u64;
    }
    table.add((address >> 12) as usize & 0x1ff)
}

/// Writes to a read-only page on this core and stops the machine unless the write faults.
///
/// Runs while no other core uses the probe page; another core's stale writable translation of it
/// is harmless, since only this function writes there and the page is writable again on return.
pub unsafe fn check() {
    let page = (&raw mut PROBE_PAGE).cast::<u8>();
    let entry = leaf_entry(page as u64);
    let writable = *entry;
    assert!(writable & WRITABLE != 0);
    *entry = writable & !WRITABLE;
    asm!("invlpg [{}]", in(reg) page);
    let error_code = write_protect_probe(page);
    *entry = writable;
    asm!("invlpg [{}]", in(reg) page);
    assert!(
        error_code != 0,
        "CPU {}: a ring-0 write to a read-only page did not fault",
        crate::cpu::get_cpu_id(),
    );
    log::info!(
        "CPU {}: a ring-0 write to a read-only page faulted with error code {:#x}",
        crate::cpu::get_cpu_id(),
        error_code,
    );
}

/// Resumes the probe after its faulting write, with the error code as its result. Whether the
/// kernel fault at regs was the probe's.
pub fn fixup(regs: &mut Registers) -> bool {
    if regs.rip != write_protect_probe_write as *const () as u64 {
        return false;
    }
    regs.rax = regs.error_code;
    regs.rip = write_protect_probe_done as *const () as u64;
    true
}
