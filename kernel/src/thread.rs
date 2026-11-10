//! Threading.

use verified::arch::Registers;
use crate::cpu;

/// A time slice, in ticks of the machine's timer.
#[derive(Debug)]
#[repr(transparent)]
pub struct Cycles(pub usize);

/// Schedules the next thread, returning its time slice.
pub fn schedule(_regs: &mut Registers) -> Option<Cycles> {
    log::debug!("hello from cpu {:?} scheduler",cpu::get_cpu_id());
    loop{
    }
}
