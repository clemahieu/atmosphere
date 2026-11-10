//! The exception vectors of EL1: the table VBAR_EL1 names, the stub that saves the trap frame around
//! the handler and restores it on return, and the handler.
//!
//! An exception taken to EL1 starts at one of sixteen vectors, 0x80 bytes apart: four kinds, the
//! synchronous exception, IRQ, FIQ and SError in that order, from each of four sources, EL1 on
//! SP_EL0, EL1 on SP_EL1, a lower level in AArch64 and a lower level in AArch32 (Arm ARM D1.4.1.6).
//! Entry writes the interrupted PSTATE to SPSR_EL1 and the return address to ELR_EL1, masks every
//! interrupt, selects SP_EL1 whatever the source and changes no general register (D1.4.2), so
//! every vector runs on this core's EL1 stack and the frame lies on it.

use core::arch::{asm, global_asm};
use core::mem::{offset_of, size_of};

use verified::arch::Registers;

use super::{spin_forever, write_protect};

// The stub stores the frame as pairs at fixed offsets: x0 to x30 in order, then SP_EL0, ELR_EL1 and
// SPSR_EL1. The stack pointer stays 16-byte aligned under the frame, which SCTLR_EL1.SA checks on
// every access through it (D1.4.10).
const FRAME_BYTES: usize = size_of::<Registers>();
const _: () = assert!(FRAME_BYTES == 34 * 8 && FRAME_BYTES % 16 == 0);
const _: () = assert!(offset_of!(Registers, x0) == 0 && offset_of!(Registers, x30) == 30 * 8);
const _: () = assert!(offset_of!(Registers, sp_el0) == 31 * 8);
const _: () = assert!(offset_of!(Registers, elr_el1) == 32 * 8 && offset_of!(Registers, spsr_el1) == 33 * 8);

// Each vector makes room for the frame, saves x0 and x1, and branches to the shared stub with its
// index in x0. The stub saves the rest and calls the handler with the index and the frame; when
// the handler returns, the stub restores the frame, which the handler may have changed, and returns
// from the exception (ERET, C6.2.157; D1.4.4). VBAR_EL1 holds bits 63:11 of the table's address, so
// the table is aligned to 0x800 (D24.2.213).
global_asm!(
    r#"
    .pushsection .text.exception_vectors, "ax"
    .balign 0x800
    .global exception_vectors
    exception_vectors:
    .irp index, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
    .balign 0x80
    sub sp, sp, #{frame}
    stp x0, x1, [sp, #0]
    mov x0, #\index
    b exception_entry
    .endr
    .balign 0x80

    exception_entry:
    stp x2, x3, [sp, #16]
    stp x4, x5, [sp, #32]
    stp x6, x7, [sp, #48]
    stp x8, x9, [sp, #64]
    stp x10, x11, [sp, #80]
    stp x12, x13, [sp, #96]
    stp x14, x15, [sp, #112]
    stp x16, x17, [sp, #128]
    stp x18, x19, [sp, #144]
    stp x20, x21, [sp, #160]
    stp x22, x23, [sp, #176]
    stp x24, x25, [sp, #192]
    stp x26, x27, [sp, #208]
    stp x28, x29, [sp, #224]
    mrs x1, SP_EL0
    stp x30, x1, [sp, #240]
    mrs x1, ELR_EL1
    mrs x2, SPSR_EL1
    stp x1, x2, [sp, #256]
    mov x1, sp
    bl {handler}
    ldp x1, x2, [sp, #256]
    msr ELR_EL1, x1
    msr SPSR_EL1, x2
    ldp x30, x1, [sp, #240]
    msr SP_EL0, x1
    ldp x28, x29, [sp, #224]
    ldp x26, x27, [sp, #208]
    ldp x24, x25, [sp, #192]
    ldp x22, x23, [sp, #176]
    ldp x20, x21, [sp, #160]
    ldp x18, x19, [sp, #144]
    ldp x16, x17, [sp, #128]
    ldp x14, x15, [sp, #112]
    ldp x12, x13, [sp, #96]
    ldp x10, x11, [sp, #80]
    ldp x8, x9, [sp, #64]
    ldp x6, x7, [sp, #48]
    ldp x4, x5, [sp, #32]
    ldp x2, x3, [sp, #16]
    ldp x0, x1, [sp, #0]
    add sp, sp, #{frame}
    eret
    .popsection
    "#,
    frame = const FRAME_BYTES,
    handler = sym exception,
);

unsafe extern "C" {
    /// The table's first vector.
    fn exception_vectors();
}

/// VBAR_EL1's RES0 bits, 10:0. Arm ARM D24.2.213.
const VECTOR_BASE_RESERVED: u64 = 0x7ff;

/// Makes the table this core's exception vectors.
pub unsafe fn install() {
    let base = exception_vectors as *const () as u64;
    assert!(base & VECTOR_BASE_RESERVED == 0, "the exception vectors are aligned to 0x800");
    // A change to a system register binds the instructions after the next ISB. Arm ARM B2.6.1.
    asm!("msr VBAR_EL1, {base}", "isb", base = in(reg) base, options(nomem, nostack, preserves_flags));
}

/// What a vector's index says: the kind is the index modulo four and the source the index over
/// four, in the table's order.
const KINDS: [&str; 4] = ["Synchronous exception", "IRQ", "FIQ", "SError"];
const SOURCES: [&str; 4] = ["EL1 on SP_EL0", "EL1", "EL0", "AArch32 EL0"];

/// The vector for a synchronous exception from EL1 on SP_EL1, which is where the kernel runs.
const SYNCHRONOUS_FROM_EL1: u64 = 4;

const _: () = assert!(KINDS.len() * SOURCES.len() == 16);

/// Every vector's handler. The write-protect check's fault resumes past its write; anything else is
/// logged with the syndrome, the fault address and the frame, and stops the core. ESR_EL1 is what
/// the latest synchronous exception or SError wrote (Arm ARM D24.2.44), and FAR_EL1 the address of
/// the latest abort or alignment fault (D24.2.47), so under an IRQ or FIQ both are older than it.
extern "C" fn exception(vector: u64, frame: &mut Registers) {
    let syndrome: u64;
    let address: u64;
    unsafe {
        asm!("mrs {syndrome}, ESR_EL1", syndrome = out(reg) syndrome, options(nomem, nostack, preserves_flags));
        asm!("mrs {address}, FAR_EL1", address = out(reg) address, options(nomem, nostack, preserves_flags));
    }
    if vector == SYNCHRONOUS_FROM_EL1 && write_protect::fixup(frame, syndrome, address) {
        return;
    }
    log::error!(
        "CPU {}: {} from {}: ESR_EL1 {:#x}, FAR_EL1 {:#x}: {:#x?}",
        crate::cpu::get_cpu_id(),
        KINDS[vector as usize % KINDS.len()],
        SOURCES[vector as usize / KINDS.len()],
        syndrome,
        address,
        frame,
    );
    unsafe {
        spin_forever();
    }
}
