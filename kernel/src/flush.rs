//! Flushing another core's TLB. The kernel never waits for another core while holding a lock: that
//! core may be spinning for the lock with interrupts off, and so could not take the IPI. A flush bumps
//! the epoch, sends the IPI and lets go. The target's handler flushes every context and records its
//! acknowledgement under the lock. See design/flush-without-waiting/.
//!
//! CapKernel holds the proven form of this state, and acknowledge takes the token flush_every_context
//! returns. No operation that unmaps is wired to it, so this holds the state the boot test flushes by.

use verified::arch::flush_every_context;
use verified::define::NUM_CPUS;

use crate::cpu;
use crate::interrupt::{self, IRQ_FLUSH, IRQ_OFFSET};
use crate::lock::Locked;

struct FlushState {
    epoch: usize,
    acked: [usize; NUM_CPUS],
}

static FLUSH: Locked<FlushState> = Locked::new("flush", FlushState { epoch: 0, acked: [0; NUM_CPUS] });

/// How long the boot test waits, in TSC cycles.
const ACK_CYCLES: u64 = 20_000_000_000;

/// Starts a flush on `target`, returning the epoch its acknowledgement must reach.
pub fn start(target: usize) -> usize {
    let epoch = {
        let mut state = FLUSH.lock();
        state.epoch += 1;
        state.epoch
    };
    interrupt::send_ipi(target, (IRQ_OFFSET + IRQ_FLUSH) as u8);
    epoch
}

/// Whether `target` has acknowledged `epoch`.
pub fn acknowledged(target: usize, epoch: usize) -> bool {
    FLUSH.lock().acked[target] >= epoch
}

/// The flush IPI's handler. An epoch read before the flush covers every unmap up to it.
pub fn handle_ipi() {
    let core = cpu::get_cpu_id();
    let mut state = FLUSH.lock();
    let epoch = state.epoch;
    let _flushed = flush_every_context(core, epoch);
    state.acked[core] = epoch;
}

/// Rounds of the boot test, so that one slow first round does not stand for the cost.
const CHECK_ROUNDS: u64 = 1000;

/// Boot test: CPU 0 flushes CPU 1 and waits for it, holding no lock while it waits.
pub fn check_second_core() {
    let (mut fastest, mut total) = (u64::MAX, 0);
    let mut epoch = 0;
    for _ in 0..CHECK_ROUNDS {
        let start_tsc = unsafe { core::arch::x86_64::_rdtsc() };
        epoch = start(1);
        while !acknowledged(1, epoch) {
            if unsafe { core::arch::x86_64::_rdtsc() } - start_tsc > ACK_CYCLES {
                log::error!("CPU 1 did not acknowledge a flush IPI");
                return;
            }
            core::hint::spin_loop();
        }
        let cycles = unsafe { core::arch::x86_64::_rdtsc() } - start_tsc;
        fastest = fastest.min(cycles);
        total += cycles;
    }
    log::info!(
        "flush IPI acknowledged by CPU 1 at epoch {}: fastest {} mean {} TSC cycles over {} rounds",
        epoch, fastest, total / CHECK_ROUNDS, CHECK_ROUNDS,
    );
}
