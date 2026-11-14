// SPDX-License-Identifier: MIT

//! The exception vectors of EL1: the table VBAR_EL1 names, the stub that saves the trap frame around
//! the handler and restores it on return, and the handler.
//!
//! An exception taken to EL1 starts at one of sixteen vectors, 0x80 bytes apart: four kinds, the
//! synchronous exception, IRQ, FIQ and SError in that order, from each of four sources, EL1 on
//! SP_EL0, EL1 on SP_EL1, a lower level in AArch64 and a lower level in AArch32 (Arm ARM D1.4.1.6).
//! Entry writes the interrupted PSTATE to SPSR_EL1 and the return address to ELR_EL1, masks every
//! interrupt, selects SP_EL1 whatever the source and changes no general register (D1.4.2), so
//! every vector runs on this core's EL1 stack and the frame lies on it.
//!
//! A stack that cannot take the frame, one that ran into its guard or a stack pointer that is not
//! a stack's, faults under the vector's own stores, and that fault is a synchronous exception from
//! EL1 on the same stack pointer. Its vector tells it by where it was taken, in the vectors or the
//! stub, and saves that frame on the core's emergency stack; the handler then reports and stops the
//! core. design/arch-module/ item 5.

use core::arch::{asm, global_asm};
use core::mem::{offset_of, size_of};

use verified::arch::Registers;

use super::{access_dirty, interrupt, spin_forever, syscall, write_protect, CoreState};
use crate::cpu::{Cpu, KernelStack};

// The stub stores the frame as pairs at fixed offsets: x0 to x30 in order, then SP_EL0, ELR_EL1 and
// SPSR_EL1. The stack pointer stays 16-byte aligned under the frame, which SCTLR_EL1.SA checks on
// every access through it (D1.4.10).
const FRAME_BYTES: usize = size_of::<Registers>();
const _: () = assert!(FRAME_BYTES == 34 * 8 && FRAME_BYTES % 16 == 0);
const _: () = assert!(offset_of!(Registers, x0) == 0 && offset_of!(Registers, x30) == 30 * 8);
const _: () = assert!(offset_of!(Registers, sp_el0) == 31 * 8);
const _: () = assert!(offset_of!(Registers, elr_el1) == 32 * 8 && offset_of!(Registers, spsr_el1) == 33 * 8);

// The code a fault under a frame's save or restore is taken in: the table and the stub after it,
// which the assembly below pads to this size and fits nothing else into.
const CODE_BYTES: usize = 0x1000;

// Where the vector that decides finds the slot it spills x1 to and the top of the emergency stack,
// from this core's `Cpu`. The slot is within a load's scaled offset and the top within two adds, of
// the low twelve bits and of the twelve above them (ADD immediate, Arm ARM C6.2.5).
const SPILL: usize = offset_of!(Cpu, arch) + offset_of!(CoreState, spill);
const EMERGENCY_TOP: usize =
    offset_of!(Cpu, arch) + offset_of!(CoreState, emergency_stack) + size_of::<KernelStack>();
const _: () = assert!(SPILL % 8 == 0 && SPILL < 4096 * 8);
const _: () = assert!(EMERGENCY_TOP % 16 == 0 && EMERGENCY_TOP < 1 << 24);

/// The index the stub hands the handler for a synchronous exception from EL1 that was taken in the
/// vectors or the stub: the frame is on the emergency stack, and it is the last one.
const FRAME_SAVE_FAULTED: u64 = 16;

// Each vector makes room for the frame, saves x0 and x1, and branches to the shared stub with its
// index in x0. The stub saves the rest and calls the handler with the index and the frame; when
// the handler returns, the stub restores the frame, which the handler may have changed, and returns
// from the exception (ERET, C6.2.157; D1.4.4). That restore is `exception_return`, which [`enter`]
// branches to with a frame no vector saved. VBAR_EL1 holds bits 63:11 of the table's address, so
// the table is aligned to 0x800 (D24.2.213).
//
// The vector for a synchronous exception from EL1 on SP_EL1, index 4, first decides which stack
// takes the frame. A fault under another vector's stores, or under the stub's, arrives here with
// ELR_EL1 in that code, and so does a fault under this vector's own. The kernel stack took no frame
// then and will not take this one, so sp becomes the top of this core's emergency stack and the
// handler gets FRAME_SAVE_FAULTED. Entry leaves no general register free, so x0 waits in
// TPIDRRO_EL0, which EL1 writes and the core makes no use of (D24.2.207), and x1 in the core's
// spill slot, found through TPIDR_EL1. EL0 reads TPIDRRO_EL0, so it is cleared again before the
// frame is saved. The flags are free: entry saved them in SPSR_EL1.
global_asm!(
    r#"
    .pushsection .text.exception_vectors, "ax"
    .balign 0x800
    .global exception_vectors
    exception_vectors:
    .irp index, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
    .balign 0x80
    .if \index == 4
    msr TPIDRRO_EL0, x0
    mrs x0, TPIDR_EL1
    str x1, [x0, #{spill}]
    mrs x0, ELR_EL1
    adr x1, exception_vectors
    sub x0, x0, x1
    cmp x0, #{code}
    mrs x0, TPIDR_EL1
    ldr x1, [x0, #{spill}]
    b.hs 1f
    add x0, x0, #{emergency_top_low}
    add x0, x0, #{emergency_top_high}, lsl #12
    mov sp, x0
    mrs x0, TPIDRRO_EL0
    msr TPIDRRO_EL0, xzr
    sub sp, sp, #{frame}
    stp x0, x1, [sp, #0]
    mov x0, #{frame_save_faulted}
    b exception_entry
    1:
    mrs x0, TPIDRRO_EL0
    msr TPIDRRO_EL0, xzr
    .endif
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
    .global exception_return
    exception_return:
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
    .org exception_vectors + {code}
    .popsection
    "#,
    frame = const FRAME_BYTES,
    code = const CODE_BYTES,
    spill = const SPILL,
    emergency_top_low = const EMERGENCY_TOP & 0xfff,
    emergency_top_high = const EMERGENCY_TOP >> 12,
    frame_save_faulted = const FRAME_SAVE_FAULTED,
    handler = sym exception,
);

unsafe extern "C" {
    /// The table's first vector.
    fn exception_vectors();
}

/// VBAR_EL1's RES0 bits, 10:0. Arm ARM D24.2.213.
const VECTOR_BASE_RESERVED: u64 = 0x7ff;

/// Makes the table this core's exception vectors. TPIDRRO_EL0, which the vector that decides the
/// frame's stack borrows and clears, is cleared here first: its reset value is not known, and EL0
/// reads it.
pub unsafe fn install() {
    let base = exception_vectors as *const () as u64;
    assert!(base & VECTOR_BASE_RESERVED == 0, "the exception vectors are aligned to 0x800");
    asm!("msr TPIDRRO_EL0, xzr", options(nomem, nostack, preserves_flags));
    // A change to a system register binds the instructions after the next ISB. Arm ARM B2.6.1.
    asm!("msr VBAR_EL1, {base}", "isb", base = in(reg) base, options(nomem, nostack, preserves_flags));
}

/// Leaves EL1 for the thread whose frame is `frame`, as the return from an exception taken from the
/// thread would: the frame goes under `stack`'s top, where a vector would have saved it, and the
/// stub restores it and returns. SP_EL1 is `stack`'s top again once the frame is restored, so the
/// thread's next exception saves its frame there.
pub unsafe fn enter(frame: &Registers, stack: u64) -> ! {
    assert!(stack % 16 == 0, "a stack's top is 16-byte aligned");
    let saved = (stack as *mut Registers).sub(1);
    saved.write(*frame);
    asm!("mov sp, {saved}", "b exception_return", saved = in(reg) saved, options(noreturn));
}

/// What a vector's index says: the kind is the index modulo four and the source the index over
/// four, in the table's order.
const KINDS: [&str; 4] = ["Synchronous exception", "IRQ", "FIQ", "SError"];
const SOURCES: [&str; 4] = ["EL1 on SP_EL0", "EL1", "EL0", "AArch32 EL0"];

/// The vector for a synchronous exception from EL1 on SP_EL1, which is where the kernel runs.
const SYNCHRONOUS_FROM_EL1: u64 = 4;

/// The vector for a synchronous exception from EL0, a thread's call among them.
const SYNCHRONOUS_FROM_EL0: u64 = 8;

/// The vectors for an IRQ, from the kernel and from EL0.
const IRQ_FROM_EL1: u64 = 5;
pub(super) const IRQ_FROM_EL0: u64 = 9;

/// Checks that the timer's interrupt reaches this core through the kernel's IRQ vector.
pub unsafe fn check_interrupt() {
    interrupt::check(IRQ_FROM_EL1);
}

const _: () = assert!(KINDS.len() * SOURCES.len() == 16);

/// Every vector's handler. An IRQ goes to the interrupt it names and resumes; the write-protect
/// check's fault resumes past its write; an `svc` from EL0 is the thread's invocation, whose
/// outcome is written over the frame the thread resumes with; an abort from EL0 that the walker
/// would have spared, where it does not keep the access flag or the dirty state, is served and the
/// instruction runs again; anything else, another exception from EL0 among them, is reported and
/// stops the core. ESR_EL1 is what the latest synchronous
/// exception or SError wrote (Arm ARM D24.2.44), and FAR_EL1 the address of the latest abort or
/// alignment fault (D24.2.47), so under an FIQ both are older than it.
///
/// The report runs on this core's emergency stack whatever the exception, since the stack that
/// took the frame may have no room for more: from its top, or from under the frame when the frame
/// is there.
extern "C" fn exception(vector: u64, frame: &mut Registers) {
    if vector == IRQ_FROM_EL1 || vector == IRQ_FROM_EL0 {
        interrupt::irq(vector, frame);
        return;
    }
    let syndrome: u64;
    let address: u64;
    unsafe {
        asm!("mrs {syndrome}, ESR_EL1", syndrome = out(reg) syndrome, options(nomem, nostack, preserves_flags));
        asm!("mrs {address}, FAR_EL1", address = out(reg) address, options(nomem, nostack, preserves_flags));
    }
    if vector == SYNCHRONOUS_FROM_EL1 && write_protect::fixup(frame, syndrome, address) {
        return;
    }
    if vector == SYNCHRONOUS_FROM_EL0 {
        if let Some(immediate) = syscall::svc_immediate(syndrome) {
            syscall::invoke(frame, immediate);
            return;
        }
        if access_dirty::serve(syndrome, address) {
            return;
        }
    }
    let frame = frame as *const Registers;
    let stack = if vector == FRAME_SAVE_FAULTED { frame as u64 } else { emergency_stack().1 };
    unsafe {
        asm!(
            "mov sp, {stack}",
            "b {report}",
            stack = in(reg) stack,
            report = sym report,
            in("x0") vector,
            in("x1") frame,
            in("x2") syndrome,
            in("x3") address,
            options(noreturn),
        );
    }
}

/// This core's emergency stack, from its lowest address to its top.
fn emergency_stack() -> (u64, u64) {
    let stack = &crate::cpu::get_current().arch.emergency_stack;
    (stack.lowest() as u64, stack.bottom() as u64)
}

/// Logs an exception nothing serves, with the syndrome, the fault address and the frame, and stops
/// the core. Under [`FRAME_SAVE_FAULTED`] the syndrome and the address are those of the fault under
/// the save, so the address is where the stack pointer was, and the frame is what that save was
/// saving: the general registers as the exception before it left them, with ELR_EL1 in the vectors.
extern "C" fn report(vector: u64, frame: &Registers, syndrome: u64, address: u64) -> ! {
    let (kind, source) = if vector == FRAME_SAVE_FAULTED {
        (KINDS[SYNCHRONOUS_FROM_EL1 as usize % KINDS.len()], "EL1, taken where a vector saves its frame")
    } else {
        (KINDS[vector as usize % KINDS.len()], SOURCES[vector as usize / KINDS.len()])
    };
    let cpu = crate::cpu::get_cpu_id();
    log::error!("CPU {}: {} from {}: ESR_EL1 {:#x}, FAR_EL1 {:#x}: {:#x?}", cpu, kind, source, syndrome, address, frame);
    let (lowest, top) = emergency_stack();
    log::error!(
        "CPU {}: stopped. The report ran on the emergency stack {:#x}-{:#x}, and the frame is at {:p}",
        cpu,
        lowest,
        top,
        frame
    );
    unsafe {
        spin_forever();
    }
}
