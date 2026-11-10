//! Each core checks at start-up that EL1 cannot write through a read-only mapping, and with it
//! that a fault the core takes arrives at its exception vectors and returns.
//!
//! The check maps one kernel page read-only for one write. The exception handler recognises the
//! fault by its instruction and resumes after it, so the write faults without stopping the machine.

use core::arch::global_asm;

use verified::arch::{Registers, DESC_AP_RO, DESC_DBM};

use super::{forget, leaf_entry, TABLE_OR_PAGE};

/// The page the check writes to.
#[repr(C, align(4096))]
struct Page([u8; 4096]);

static mut PROBE_PAGE: Page = Page([0; 4096]);

/// What the probe's write raised: ESR_EL1 and FAR_EL1 as the handler read them, both zero when the
/// write did not fault. Two words, which a call returns in x0 and x1.
#[repr(C)]
struct Fault {
    syndrome: u64,
    address: u64,
}

// write_protect_probe(address) writes a byte there and returns a zero Fault, or the fault's when the
// write faulted: fixup resumes at write_protect_probe_done with it in x0 and x1.
global_asm!(
    ".global write_protect_probe",
    ".global write_protect_probe_write",
    ".global write_protect_probe_done",
    "write_protect_probe:",
    "mov x2, x0",
    "mov x0, #0",
    "mov x1, #0",
    "mov w3, #1",
    "write_protect_probe_write:",
    "strb w3, [x2]",
    "write_protect_probe_done:",
    "ret",
);

unsafe extern "C" {
    fn write_protect_probe(address: *mut u8) -> Fault;
    fn write_protect_probe_write();
    fn write_protect_probe_done();
}

/// Whether a write through the page descriptor `leaf` is allowed: AP[2] is clear, or the
/// descriptor is marked with the dirty-bit modifier, under which the walker clears AP[2] on the
/// first write where TCR_EL1.HD is set. Arm ARM D8.5.2.1.
const fn writable(leaf: u64) -> bool {
    leaf & DESC_AP_RO == 0 || leaf & DESC_DBM != 0
}

/// `leaf` as a read-only mapping of the same page: AP[2] set and the modifier clear, so the walker
/// does not make it writable again.
const fn read_only(leaf: u64) -> u64 {
    leaf & !DESC_DBM | DESC_AP_RO
}

const _: () = assert!(writable(DESC_DBM | DESC_AP_RO | TABLE_OR_PAGE) && writable(TABLE_OR_PAGE));
const _: () = assert!(!writable(DESC_AP_RO | TABLE_OR_PAGE));
const _: () = assert!(!writable(read_only(DESC_DBM | TABLE_OR_PAGE)) && !writable(read_only(TABLE_OR_PAGE)));
const _: () = assert!(read_only(DESC_DBM | 0x4000_0703) == 0x4000_0783);

/// ESR_EL1.EC, bits 31:26: 0b100101 is a Data Abort taken without a change of exception level. Arm
/// ARM D24.2.44.
const SYNDROME_CLASS_SHIFT: u32 = 26;
const SYNDROME_CLASS_MASK: u64 = 0b11_1111;
const CLASS_DATA_ABORT_SAME_LEVEL: u64 = 0b10_0101;

/// A Data Abort's WnR, bit 6 of the syndrome: set, the access was a write. Its DFSC, bits 5:0:
/// 0b001111 is a permission fault at lookup level 3, the level of a page descriptor. Arm ARM
/// D24.2.44, the ISS encoding for an exception from a Data Abort.
const ABORT_WRITE: u64 = 1 << 6;
const ABORT_STATUS_MASK: u64 = 0b11_1111;
const STATUS_PERMISSION_LEVEL_3: u64 = 0b00_1111;

/// Whether `syndrome` says that EL1's write was refused by a page descriptor's permissions.
const fn refused_write(syndrome: u64) -> bool {
    syndrome >> SYNDROME_CLASS_SHIFT & SYNDROME_CLASS_MASK == CLASS_DATA_ABORT_SAME_LEVEL
        && syndrome & ABORT_WRITE != 0
        && syndrome & ABORT_STATUS_MASK == STATUS_PERMISSION_LEVEL_3
}

// With IL, bit 25, set for a 32-bit instruction: a write's permission fault at level 3 from EL1;
// then the same from EL0 (class 0b100100), as a read, and as a translation fault (0b000111).
const _: () = assert!(refused_write(0x9600_004f));
const _: () = assert!(!refused_write(0x9200_004f) && !refused_write(0x9600_000f) && !refused_write(0x9600_0047));
const _: () = assert!(!refused_write(0));

/// Writes to a read-only page on this core and stops the machine unless the write takes a
/// permission fault and leaves the page as it was.
///
/// The page's descriptor changes in permission only, between two valid values, which asks for no
/// break-before-make (Arm ARM D8.17.1); the loader wrote it with the access flag set and as dirty,
/// so the walker has nothing to write there meanwhile. Runs while no other core uses the probe page;
/// another core's stale writable translation of it is harmless, since only this function writes
/// there and the page is writable again on return.
pub unsafe fn check() {
    let page = (&raw mut PROBE_PAGE).cast::<u8>();
    let entry = leaf_entry(page as u64);
    let leaf = entry.read_volatile();
    assert!(leaf & TABLE_OR_PAGE == TABLE_OR_PAGE && writable(leaf));
    entry.write_volatile(read_only(leaf));
    forget(page);
    let fault = write_protect_probe(page);
    entry.write_volatile(leaf);
    forget(page);
    assert!(
        refused_write(fault.syndrome) && fault.address == page as u64,
        "CPU {}: an EL1 write to a read-only page at {:p} did not take its permission fault: ESR_EL1 {:#x}, FAR_EL1 {:#x}",
        crate::cpu::get_cpu_id(),
        page,
        fault.syndrome,
        fault.address,
    );
    assert!(page.read_volatile() == 0, "CPU {}: a write that faulted reached its page", crate::cpu::get_cpu_id());
    log::info!(
        "CPU {}: an EL1 write to a read-only page faulted with syndrome {:#x} and was refused",
        crate::cpu::get_cpu_id(),
        fault.syndrome,
    );
}

/// Resumes the probe after its faulting write, with the fault as its result. Whether the kernel's
/// exception at `frame` was the probe's: a synchronous exception's return address is the
/// instruction that raised it (Arm ARM D1.4.1.5).
pub fn fixup(frame: &mut Registers, syndrome: u64, address: u64) -> bool {
    if frame.elr_el1 != write_protect_probe_write as *const () as u64 {
        return false;
    }
    frame.x0 = syndrome;
    frame.x1 = address;
    frame.elr_el1 = write_protect_probe_done as *const () as u64;
    true
}
