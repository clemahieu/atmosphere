// SPDX-License-Identifier: MIT

//! The reschedule IPI and the core that runs nothing. CapKernel decides which thread a core runs and
//! which space it translates through: a start that makes a thread Runnable above what its core runs
//! records a reschedule IPI for that core in ghost state, `selection_due` reads the same condition,
//! and `tick` selects, switching the thread, its frame and its space in one operation. The glue here
//! sends the IPIs `selection_due` names once the kernel's lock is released, runs `tick` in the IPI's
//! handler and returns with the frame `current_frame` gives. A core whose thread left it waits for
//! the next interrupt. design/cpu-time-as-capability/.

use verified::arch::Registers;
use verified::capability::kernel::CapKernel;
use verified::capability::switch::TickStep;
use verified::define::NUM_CPUS;
use vstd::prelude::Tracked;

use crate::boot;
use crate::capability::CAP_KERNEL;
use crate::cpu;
use crate::machine::{self, RESCHEDULE_VECTOR};

/// Where the reschedule IPI's handler returns to.
pub enum Resume {
    /// What the interrupt interrupted: the thread that still runs, or the wait of a core that still
    /// runs nothing.
    Interrupted,
    /// User mode with this frame, the core's current thread's.
    Thread(Registers),
    /// The wait for the next interrupt: the core runs nothing.
    Idle,
}

/// The online cores whose selection is due, as the mask of cores to send the reschedule IPI. Called
/// under the kernel's lock after an entry.
pub fn due(kernel: &CapKernel) -> u64 {
    let online = cpu::online();
    let mut targets = 0;
    for d in 0..NUM_CPUS {
        if online >> d & 1 == 1 && kernel.selection_due(d) {
            targets |= 1 << d;
        }
    }
    targets
}

// `due`'s mask has a bit for each core.
const _: () = assert!(NUM_CPUS <= u64::BITS as usize);

/// Sends the reschedule IPI to each core in `targets`, the mask `due` returned, once the kernel's
/// lock is released.
pub fn send(targets: u64) {
    for d in 0..NUM_CPUS {
        if targets >> d & 1 == 1 {
            machine::send_ipi(d, RESCHEDULE_VECTOR);
        }
    }
}

/// Runs the selection on this core, `core`, whose interrupted frame is `frame`: ticks until the tick
/// does not drop a thread that may not run, and returns whether it switched. The kernel's root is the
/// loader's table, the one boot gave CapKernel.
fn select(kernel: &mut CapKernel, core: usize, frame: Registers) -> bool {
    let kernel_root = boot::get_boot_info().pml4 as usize;
    loop {
        match kernel.tick(core, frame, kernel_root, Tracked::assume_new()) {
            TickStep::Switched => return true,
            TickStep::Kept => return false,
            TickStep::Dropped => {},
        }
    }
}

/// The reschedule IPI's handler, on the core that took it, after the interrupt ended: the selection,
/// with the interrupted `frame`, which `from_user` says was a thread's. A thread the tick switched to
/// resumes with its frame, and so does a thread current when the interrupt came from the core's wait;
/// a core whose thread left it waits.
pub fn handle_ipi(frame: &Registers, from_user: bool) -> Resume {
    let core = cpu::get_cpu_id();
    let (switched, current, flushes) = {
        let mut guard = CAP_KERNEL.lock();
        let kernel = guard.as_deref_mut().expect("a reschedule IPI before the capability kernel was built");
        let epoch = kernel.flush_epoch;
        let switched = select(kernel, core, *frame);
        (switched, kernel.current_frame(core), crate::flush::owed(kernel, epoch))
    };
    crate::flush::send(flushes);
    match current {
        Some(resumed) if switched || !from_user => Resume::Thread(resumed),
        Some(_) => Resume::Interrupted,
        None if from_user => Resume::Idle,
        None => Resume::Interrupted,
    }
}
