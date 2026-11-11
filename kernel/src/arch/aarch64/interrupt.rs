// SPDX-License-Identifier: MIT

//! The IRQ entry: which interrupt arrived, its handler and its end, and the boot check that an
//! interrupt arrives at all.
//!
//! An IRQ comes through one vector whatever raised it, where the x86_64 IDT has a vector for each.
//! The machine names the interrupt when it is acknowledged, and every interrupt it delivers is one
//! of its vector constants. design/machine-glue-below-the-kernel/.

use core::arch::asm;
use core::sync::atomic::{AtomicU64, Ordering};

use verified::arch::Registers;

use super::{cycles, spin_forever, stall_cycles};
use crate::machine;

/// The check's state: [`IDLE`], [`ARMED`] while [`check`] waits, and otherwise the vector the
/// timer's interrupt arrived through, in the upper half, with the id the machine acknowledged.
static CHECK: AtomicU64 = AtomicU64::new(IDLE);
const IDLE: u64 = u64::MAX;
const ARMED: u64 = u64::MAX - 1;
const VECTOR_SHIFT: u32 = 32;

/// Ticks of the machine's timer the check arms it for: long enough to return from arming it,
/// short beside the stall a boot check waits.
const CHECK_TICKS: u64 = 10_000;

/// An IRQ taken through `vector`.
pub fn irq(vector: u64, frame: &mut Registers) {
    // Nothing pending by the time the core asked: nothing was activated, so nothing ends.
    let Some(id) = machine::acknowledge_interrupt() else {
        return;
    };
    if id == u32::from(machine::TIMER_VECTOR) {
        timer(vector, id, frame);
    } else if id == u32::from(machine::FLUSH_VECTOR) {
        crate::flush::handle_ipi();
    } else if id == u32::from(machine::IOMMU_FAULT_VECTOR) {
        log::error!("CPU {}: IOMMU fault: {:#x?}", crate::cpu::get_cpu_id(), frame);
        machine::iommu_fault_dump().unwrap();
        unsafe { spin_forever() };
    } else {
        log::error!("CPU {}: interrupt {} has no handler: {:#x?}", crate::cpu::get_cpu_id(), id, frame);
        unsafe { spin_forever() };
    }
    machine::end_of_interrupt();
}

/// The timer's interrupt: the check's, when it is waiting for one. Nothing else arms the timer, so
/// any other is reported, and the core stops.
fn timer(vector: u64, id: u32, frame: &Registers) {
    let taken = vector << VECTOR_SHIFT | u64::from(id);
    if CHECK.compare_exchange(ARMED, taken, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
        return;
    }
    log::error!("CPU {}: stray timer interrupt, outside the boot check: {:#x?}", crate::cpu::get_cpu_id(), frame);
    unsafe { spin_forever() };
}

/// Shots of the timer the check takes. The second arrives only when the first was ended and the
/// timer armed again after its shot was spent.
const CHECK_SHOTS: usize = 2;

/// Arms this core's timer and waits, IRQs open, for its interrupt to arrive through `vector`, the
/// IRQ vector for where the kernel runs, [`CHECK_SHOTS`] times over. Stops the machine when one
/// does not arrive.
pub unsafe fn check(vector: u64) {
    let cpu = crate::cpu::get_cpu_id();
    let mut acknowledged = 0;
    for _ in 0..CHECK_SHOTS {
        CHECK.store(ARMED, Ordering::SeqCst);
        machine::set_timer(CHECK_TICKS);
        let deadline = cycles() + stall_cycles();
        // MSR DAIFClr and DAIFSet with the I bit, Arm ARM C6.2.288.
        asm!("msr DAIFClr, #0b0010", options(nomem, nostack, preserves_flags));
        // `|`, not `||`: a branch here would be taken or not by how soon the interrupt arrives.
        crate::cpu::spin_until(|| (CHECK.load(Ordering::SeqCst) != ARMED) | (cycles() > deadline));
        asm!("msr DAIFSet, #0b0010", options(nomem, nostack, preserves_flags));
        let taken = CHECK.swap(IDLE, Ordering::SeqCst);
        assert!(taken != ARMED, "CPU {}: the timer's interrupt did not arrive", cpu);
        let (through, id) = (taken >> VECTOR_SHIFT, taken as u32);
        assert!(
            through == vector && id == u32::from(machine::TIMER_VECTOR),
            "CPU {}: the timer's interrupt arrived through vector {} as interrupt {}",
            cpu,
            through,
            id
        );
        acknowledged = id;
    }
    log::info!(
        "CPU {}: the timer's interrupt arrived at EL1 through the IRQ vector as interrupt {}, {} times",
        cpu,
        acknowledged,
        CHECK_SHOTS
    );
}
