// SPDX-License-Identifier: MIT

//! Flushing another core's TLB. The kernel never waits for another core while holding a lock: that
//! core may be spinning for the lock with interrupts off, and so could not take the IPI. A flush bumps
//! the epoch, sends the IPI and lets go. The target's handler flushes every context and records its
//! acknowledgement under the lock. See design/flush-without-waiting/.
//!
//! CapKernel holds the proven form of this state, and its acknowledge makes the flush itself. An
//! operation's unmaps bump its epoch and record their IPIs in ghost state; `owed` and `send` make them
//! on the running kernel, and the IPI's handler acknowledges in CapKernel, as CapKernel's entry does for
//! the core that made the call. FlushState is the boot test's
//! own, which runs before CapKernel is built.

use verified::arch::flush_every_context;
use verified::capability::kernel::CapKernel;
use verified::define::NUM_CPUS;
use vstd::prelude::Tracked;

use crate::arch;
use crate::capability::CAP_KERNEL;
use crate::cpu;
use crate::machine::{self, FLUSH_VECTOR};
use crate::lock::Locked;

struct FlushState {
    epoch: usize,
    acked: [usize; NUM_CPUS],
}

static FLUSH: Locked<FlushState> = Locked::new("flush", FlushState { epoch: 0, acked: [0; NUM_CPUS] });

/// Starts a flush on `target`, returning the epoch its acknowledgement must reach.
pub fn start(target: usize) -> usize {
    let epoch = {
        let mut state = FLUSH.lock();
        state.epoch += 1;
        state.epoch
    };
    machine::send_ipi(target, FLUSH_VECTOR);
    epoch
}

/// Whether `target` has acknowledged `epoch`.
pub fn acknowledged(target: usize, epoch: usize) -> bool {
    FLUSH.lock().acked[target] >= epoch
}

/// The flush IPI's handler. An epoch read before the flush covers every unmap up to it. It serves the
/// boot test's state, then CapKernel's: a core behind CapKernel's epoch acknowledges it, which flushes
/// every context. The handler runs with interrupts closed, and no core holds the kernel's lock with them
/// open, so it never waits on a lock its own core holds.
pub fn handle_ipi() {
    let core = cpu::get_cpu_id();
    {
        let mut state = FLUSH.lock();
        let epoch = state.epoch;
        // This state is not CapKernel's, so no TLB model is kept for it and the one made here is dropped.
        flush_every_context(Tracked::assume_new(), core);
        state.acked[core] = epoch;
    }
    if let Some(kernel) = CAP_KERNEL.lock().as_deref_mut() {
        if kernel.cores.get(core).acked_epoch < kernel.flush_epoch {
            // The handler runs on `core`, which acknowledge requires of its caller.
            kernel.acknowledge(core, Tracked::assume_new());
        }
    }
}

/// The flush an operation owes, given CapKernel's epoch before it ran, as the mask of cores to send the
/// flush IPI. Called under the kernel's lock by the core that ran the operation, after the verified
/// entry, which has that core acknowledge whenever it is behind the epoch. An unmap bumps the epoch and
/// records an IPI to each core that loaded the space, in ghost state only; when the epoch moved, every
/// other core that has loaded a space and has not reached it is owed the IPI, a superset of the cores
/// the unmaps listed.
pub fn owed(kernel: &CapKernel, epoch: usize) -> u64 {
    if kernel.flush_epoch == epoch {
        return 0;
    }
    let mut targets = 0;
    for d in 0..NUM_CPUS {
        let state = kernel.cores.get(d);
        if arch::loaded_a_space(state) && state.acked_epoch < kernel.flush_epoch {
            targets |= 1 << d;
        }
    }
    targets
}

// `owed`'s mask has a bit for each core.
const _: () = assert!(NUM_CPUS <= u64::BITS as usize);

/// Sends the flush IPI to each core in `targets`, the mask `owed` returned, once the kernel's lock is
/// released.
pub fn send(targets: u64) {
    for d in 0..NUM_CPUS {
        if targets >> d & 1 == 1 {
            machine::send_ipi(d, FLUSH_VECTOR);
        }
    }
}

/// Rounds of the boot test, so that one slow first round does not stand for the cost.
const CHECK_ROUNDS: u64 = 1000;

/// Boot test: CPU 0 flushes CPU 1 and waits for it, holding no lock while it waits.
pub fn check_second_core() {
    let (mut fastest, mut total) = (u64::MAX, 0);
    let mut epoch = 0;
    for _ in 0..CHECK_ROUNDS {
        let started = arch::cycles();
        epoch = start(1);
        while !acknowledged(1, epoch) {
            if arch::cycles() - started > arch::stall_cycles() {
                log::error!("CPU 1 did not acknowledge a flush IPI");
                return;
            }
            core::hint::spin_loop();
        }
        let cycles = arch::cycles() - started;
        fastest = fastest.min(cycles);
        total += cycles;
    }
    log::info!(
        "flush IPI acknowledged by CPU 1 at epoch {}: fastest {} mean {} cycles over {} rounds",
        epoch, fastest, total / CHECK_ROUNDS, CHECK_ROUNDS,
    );
}
