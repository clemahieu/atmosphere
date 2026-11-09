//! Threading.

use crate::interrupt::Cycles;
use verified::arch::Registers;
use crate::cpu;
pub use verified::bridge::SwitchDecision;

/// Schedules the next thread, returning its time slice.
pub fn schedule(_regs: &mut Registers) -> Option<Cycles> {
    log::debug!("hello from cpu {:?} scheduler",cpu::get_cpu_id());
    loop{
    }
}
