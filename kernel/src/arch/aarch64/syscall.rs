// SPDX-License-Identifier: MIT

//! The call from EL0: `svc #0`, by the aarch64 table of design/syscall-abi-in-registers/.
//!
//! `svc` takes a synchronous exception to EL1 whose syndrome names its class and carries the
//! instruction's immediate, with ELR_EL1 at the instruction after it (Arm ARM C6.2.466, D1.4.1.5).
//! The vector saved the caller's whole frame, so the dispatch reads the operation number, the slot
//! and the arguments from it, the outcome is written over it, and the stub's return restores every
//! register the outcome did not take with the caller's own value.

use verified::arch::Registers;
use verified::capability::operation::{self, Outcome};

use crate::capability::{dispatch, power_off_accepted};

/// ESR_EL1.EC, bits 31:26, the exception's class. Arm ARM D24.2.44.
const CLASS_SHIFT: u32 = 26;
const CLASS_MASK: u64 = 0b11_1111;

/// The class of an SVC instruction executed in AArch64 state.
const CLASS_SVC: u64 = 0b01_0101;

/// imm16, bits 15:0 of that class's syndrome: the instruction's immediate. Arm ARM D24.2.44, the
/// ISS encoding for an exception from HVC or SVC instruction execution.
const IMMEDIATE_MASK: u64 = 0xffff;

/// The immediate of the `svc` that `syndrome` reports, and nothing when it reports anything else.
pub const fn svc_immediate(syndrome: u64) -> Option<u64> {
    if syndrome >> CLASS_SHIFT & CLASS_MASK == CLASS_SVC {
        Some(syndrome & IMMEDIATE_MASK)
    } else {
        None
    }
}

// `svc #0` and `svc #1` as a core reports them, with IL, bit 25, set for a 32-bit instruction; a
// data abort and an instruction abort from EL0, which are no call; and the zero syndrome.
const _: () = assert!(matches!(svc_immediate(0x5600_0000), Some(0)));
const _: () = assert!(matches!(svc_immediate(0x5600_0001), Some(1)));
const _: () = assert!(matches!(svc_immediate(0x5600_ffff), Some(0xffff)));
const _: () = assert!(svc_immediate(0x9200_0045).is_none() && svc_immediate(0x8200_0005).is_none());
const _: () = assert!(svc_immediate(0).is_none());

/// Serves the `svc` with `immediate` that the thread whose frame is `frame` executed. The verified
/// dispatch runs the invocation for the core's current thread and decides the status and result
/// words that return; an immediate other than 0 names no invocation and returns unknown. A
/// power-off the dispatch accepted ends the run here and returns to no thread. A thread that left the
/// core returns to nothing: the core waits on its syscall stack, whose frames here it gives up, until
/// the reschedule IPI enters the thread selected.
pub fn invoke(frame: &mut Registers, immediate: u64) {
    if immediate != 0 {
        frame.write_outcome(operation::status_only_outcome(operation::STATUS_UNKNOWN));
        return;
    }
    let Some(returned): Option<Outcome> = dispatch(*frame) else {
        unsafe { super::idle_on(crate::cpu::get_current().syscall_sp) }
    };
    match returned.status {
        operation::STATUS_OK
        | operation::STATUS_REFUSED
        | operation::STATUS_UNKNOWN
        | operation::STATUS_AGAIN => {}
        status => unreachable!("dispatch returned status {status}, which no operation returns"),
    }
    // The dispatch released the kernel's lock before it returned.
    if let Some(success) = power_off_accepted(frame, &returned) {
        super::access_dirty::report();
        unsafe { crate::machine::shutdown(success) }
    }
    frame.write_outcome(returned);
}
