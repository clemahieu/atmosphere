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
/// every context. When the core was running a thread, it logs the epoch it acknowledged while it still
/// holds the kernel's lock, so the line comes before anything a free that waited for it prints. The
/// handler runs with interrupts closed, and no core holds the kernel's lock with them open, so it never
/// waits on a lock its own core holds.
pub fn handle_ipi() {
    let core = cpu::get_cpu_id();
    {
        let mut state = FLUSH.lock();
        let epoch = state.epoch;
        flush_this_core(core);
        state.acked[core] = epoch;
    }
    if let Some(kernel) = CAP_KERNEL.lock().as_deref_mut() {
        // The handler runs on `core`, which the charge and the entry require of their caller. The thread
        // the IPI interrupted is charged the cycles since this core's last entry, as at an invocation:
        // design/cpu-time-as-capability/. The entry makes its own step counter in the one passed here.
        kernel.charge(core, arch::cycles());
        let state = kernel.cores.get(core);
        let logged = state.acked_epoch < kernel.flush_epoch && state.current_thread.is_some();
        kernel.enter_flush(core, Tracked::assume_new());
        if logged {
            log::info!("CPU {} acknowledged flush epoch {}", core, kernel.flush_epoch);
        }
    }
}

/// Flushes every context on `core`, the core this runs on, for the boot test's state. That state is
/// not CapKernel's, so no TLB model is kept for it and the one made here is dropped. In a flush_cost
/// build the user-mode round may have chosen a narrower flush for this one.
fn flush_this_core(core: usize) {
    #[cfg(feature = "flush_cost")]
    if cost::flushed_as_chosen() {
        return;
    }
    flush_every_context(Tracked::assume_new(), core);
}

/// The flush an operation owes, given CapKernel's epoch before it ran, as the mask of cores to send the
/// flush IPI. Called under the kernel's lock by the core that ran the operation, after the verified
/// entry, which has that core acknowledge whenever it is behind the epoch. An unmap bumps the epoch and
/// records an IPI to each core that loaded the space, in ghost state only; when the epoch moved, every
/// other core that has loaded a space and has not reached it is owed the IPI, a superset of the cores
/// the unmaps listed and of the cores a free waits for, CapKernel::all_acknowledged: those that loaded a
/// space and owe a flush, each behind the epoch.
pub fn owed(kernel: &CapKernel, epoch: usize) -> u64 {
    if kernel.flush_epoch == epoch {
        return 0;
    }
    let mut targets = 0;
    for d in 0..NUM_CPUS {
        let state = kernel.cores.get(d);
        if state.loaded_a_space() && state.acked_epoch < kernel.flush_epoch {
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

/// What a flush request costs by where the target is, for the flush design's numbers: CPU 0 times
/// [`CHECK_ROUNDS`] requests to CPU 1 until CPU 1 acknowledges, with CPU 1 running a loop with
/// interrupts open, so the IPI finds it running rather than halted as [`check_second_core`] does, and
/// then spinning with interrupts closed, as a core waiting for the queue lock does, polling a request
/// word in its loop, which takes no IPI. The second models a lock whose wait loop serves flush
/// requests; the queue lock itself is unchanged. Two more split the cost: the polled word answered
/// without a flush, the cache lines' round trip alone, and the flush alone on CPU 0. Once dom0 runs, it
/// times the round trip to CPU 1 in user mode through [`cost::USER_OPERATION`], choosing the flush CPU 1
/// makes, and the TLB refill that flush costs the thread there. A test build: tools/run.py
/// --kernel-feature flush_cost.
#[cfg(feature = "flush_cost")]
pub mod cost {
    use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    use verified::arch::Registers;
    use verified::capability::operation::{Outcome, STATUS_OK, STATUS_REFUSED};

    use super::{acknowledged, flush_this_core, start, CHECK_ROUNDS};
    use crate::{arch, cpu};

    /// The operation number of the user-mode round, past every operation's and below the number dom0
    /// checks no operation has. Argument 1 is the flush CPU 1 makes for it, one of the kinds below;
    /// argument 2 not zero has it name another context than the one CPU 1 runs; argument 3 is the page
    /// the one-page flush names. It returns ok and the round trip in cycles as result 1, or refused for a
    /// kind it does not know, for a flush CPU 1 cannot make, or when CPU 1 did not acknowledge.
    pub const USER_OPERATION: u64 = 0xfff0;

    /// The flushes the user-mode round chooses from: every context, as every flush IPI makes today; one
    /// context's entries, the id a space's entries are tagged with ([`arch::flush_context`]); one page of
    /// one context ([`arch::flush_page`]); or none, the IPI alone.
    const EVERY: u64 = 0;
    const CONTEXT: u64 = 1;
    const PAGE: u64 = 2;
    const NONE: u64 = 3;

    /// The flush CPU 1 makes for the next flush IPI, with whether it names another context and the page
    /// it names. Every flush IPI but the user-mode round's flushes every context.
    static KIND: AtomicU64 = AtomicU64::new(EVERY);
    static OTHER: AtomicU64 = AtomicU64::new(0);
    static PAGE_ADDRESS: AtomicU64 = AtomicU64::new(0);

    /// Makes the flush the user-mode round chose, if it chose one, on the core this runs on, and says
    /// whether it did. The context is the one the core runs, or with OTHER another: the id with its
    /// lowest bit flipped, which no space the core runs has.
    pub(super) fn flushed_as_chosen() -> bool {
        let kind = KIND.load(Ordering::SeqCst);
        let context = arch::current_context() ^ OTHER.load(Ordering::SeqCst) as usize;
        match kind {
            CONTEXT => arch::flush_context(context),
            PAGE => arch::flush_page(context, PAGE_ADDRESS.load(Ordering::SeqCst)),
            NONE => {}
            _ => return false,
        }
        true
    }

    /// The user-mode round, for the invocation in `frame` from dom0 on CPU 0: one flush IPI to CPU 1,
    /// which runs a thread in user mode, making the flush the invocation chose, timed from the send
    /// until CPU 1 acknowledges. It holds no lock while it waits.
    pub fn user_round(frame: &Registers) -> Outcome {
        let kind = frame.argument(1);
        let refused = Outcome { status: STATUS_REFUSED, result_1: 0, result_2: 0, result_3: 0, result_4: 0, result_5: 0 };
        let other = frame.argument(2) != 0;
        if kind > NONE || (matches!(kind, CONTEXT | PAGE) && !arch::context_flush_available(other)) {
            return refused;
        }
        KIND.store(kind, Ordering::SeqCst);
        OTHER.store(other as u64, Ordering::SeqCst);
        PAGE_ADDRESS.store(frame.argument(3), Ordering::SeqCst);
        let started = arch::cycles();
        let epoch = start(1);
        cpu::spin_until(|| acknowledged(1, epoch) | (arch::cycles() - started > arch::stall_cycles()));
        let cycles = arch::cycles() - started;
        // CPU 1 read the kind before it acknowledged.
        KIND.store(EVERY, Ordering::SeqCst);
        if !acknowledged(1, epoch) {
            log::error!("flush cost: CPU 1 in user mode did not acknowledge");
            return refused;
        }
        Outcome { status: STATUS_OK, result_1: cycles, ..refused }
    }

    /// Where CPU 1 waits: halted for an interrupt, as when idle; running with interrupts open; spinning
    /// with them closed and polling REQUEST, flushing before it answers or not; or done, back to its
    /// idle loop.
    const HALTED: usize = 0;
    const RUNNING: usize = 1;
    const SPINNING: usize = 2;
    const SPINNING_BARE: usize = 3;
    const DONE: usize = 4;

    /// The mode CPU 0 asks for, and the one CPU 1 is in.
    static MODE: AtomicUsize = AtomicUsize::new(HALTED);
    static SEEN: AtomicUsize = AtomicUsize::new(HALTED);

    /// The last request CPU 0 posted while CPU 1 spins, and the last CPU 1 served.
    static REQUEST: AtomicUsize = AtomicUsize::new(0);
    static SERVED: AtomicUsize = AtomicUsize::new(0);

    /// CPU 1's loop, after it comes online and before it idles, until CPU 0 is done with it.
    pub fn serve() {
        let core = cpu::get_cpu_id();
        loop {
            let mode = MODE.load(Ordering::SeqCst);
            SEEN.store(mode, Ordering::SeqCst);
            match mode {
                HALTED => arch::wait(),
                RUNNING => {
                    arch::open_interrupts();
                    core::hint::spin_loop();
                }
                SPINNING | SPINNING_BARE => {
                    arch::close_interrupts();
                    let request = REQUEST.load(Ordering::SeqCst);
                    if request != SERVED.load(Ordering::Relaxed) {
                        if mode == SPINNING {
                            flush_this_core(core);
                        }
                        SERVED.store(request, Ordering::SeqCst);
                    }
                }
                _ => return,
            }
        }
    }

    /// Puts CPU 1 in `mode` and waits until it is there. A halted CPU 1 reads the mode only after an
    /// interrupt, so it is sent a flush IPI, which also leaves nothing it owes.
    fn enter(mode: usize) -> bool {
        MODE.store(mode, Ordering::SeqCst);
        let started = arch::cycles();
        let epoch = start(1);
        cpu::spin_until(|| {
            (acknowledged(1, epoch) & (SEEN.load(Ordering::SeqCst) == mode))
                | (arch::cycles() - started > arch::stall_cycles())
        });
        SEEN.load(Ordering::SeqCst) == mode
    }

    /// Times CHECK_ROUNDS of `request`, each until `answered` holds for what it returned, and logs the
    /// fastest and the mean as `case`.
    fn time(case: &str, request: impl Fn() -> usize, answered: impl Fn(usize) -> bool) {
        let (mut fastest, mut total) = (u64::MAX, 0);
        for _ in 0..CHECK_ROUNDS {
            let started = arch::cycles();
            let token = request();
            while !answered(token) {
                if arch::cycles() - started > arch::stall_cycles() {
                    log::error!("flush cost: CPU 1 {} did not acknowledge", case);
                    return;
                }
                core::hint::spin_loop();
            }
            let cycles = arch::cycles() - started;
            fastest = fastest.min(cycles);
            total += cycles;
        }
        log::info!(
            "flush cost: CPU 1 {}: fastest {} mean {} cycles over {} rounds",
            case, fastest, total / CHECK_ROUNDS, CHECK_ROUNDS,
        );
    }

    /// The polled word's request and answer.
    fn poll(case: &str) {
        time(case, || REQUEST.fetch_add(1, Ordering::SeqCst) + 1, |request| SERVED.load(Ordering::SeqCst) == request);
    }

    /// A flush CPU 0 makes and times itself: every context, one context's entries, or one page of one
    /// context.
    #[derive(Clone, Copy)]
    pub enum Flush {
        Every,
        Context(usize),
        Page(usize, u64),
    }

    /// The page CPU 0's one-page flushes name: one nothing maps, so a flush leaves nothing to refill.
    const UNMAPPED_PAGE: u64 = 0;

    /// The flushes CPU 0 times, each with its name, naming the context it runs.
    fn flushes() -> [(&'static str, Flush); 3] {
        let context = arch::current_context();
        [("every context", Flush::Every), ("its context", Flush::Context(context)), ("one page", Flush::Page(context, UNMAPPED_PAGE))]
    }

    /// Makes `flush` on this core alone, and says whether this core can, given whether it can flush one
    /// context of its own ([`arch::context_flush_available`], which is not timed: CPUID exits under
    /// KVM).
    fn flush_here(flush: Flush, context_flush: bool) -> bool {
        match flush {
            Flush::Every => flush_this_core(cpu::get_cpu_id()),
            _ if !context_flush => return false,
            Flush::Context(context) => arch::flush_context(context),
            Flush::Page(context, address) => arch::flush_page(context, address),
        }
        true
    }

    /// Times CHECK_ROUNDS of `flush`, which says whether this core can make it, and logs the fastest and
    /// the mean to a hundredth of a cycle as `case`, or that this core cannot.
    fn time_flush(case: &str, name: &str, flush: impl Fn() -> bool) {
        if !flush() {
            log::info!("flush cost: CPU 0 {} {}: not available", case, name);
            return;
        }
        let (mut fastest, mut total) = (u64::MAX, 0);
        for _ in 0..CHECK_ROUNDS {
            let started = arch::cycles();
            flush();
            let cycles = arch::cycles() - started;
            fastest = fastest.min(cycles);
            total += cycles;
        }
        log::info!(
            "flush cost: CPU 0 {} {}: fastest {} mean {}.{:02} cycles over {} rounds",
            case, name, fastest, total / CHECK_ROUNDS, total * 100 / CHECK_ROUNDS % 100, CHECK_ROUNDS,
        );
    }

    /// CPU 0 broadcasting each flush to every core, with CPU 1 as `cpu_1` says.
    fn time_broadcasts(cpu_1: &str) {
        for (name, flush) in flushes() {
            time_flush(cpu_1, name, || arch::broadcast_flush(flush));
        }
    }

    /// CPU 0's side: every case, after check_second_core timed the halted one, then CPU 1 back to idle.
    /// CPU 0 times each flush made on itself alone, and broadcast with CPU 1 halted and with it running.
    pub fn measure() {
        let context_flush = arch::context_flush_available(false);
        for (name, flush) in flushes() {
            time_flush("flushing itself", name, || flush_here(flush, context_flush));
        }
        time_broadcasts("broadcasting, CPU 1 halted,");
        if !enter(RUNNING) {
            log::error!("flush cost: CPU 1 did not start running");
            return;
        }
        time("running, interrupts open, IPI", || start(1), |epoch| acknowledged(1, epoch));
        time_broadcasts("broadcasting, CPU 1 running,");
        if !enter(SPINNING) {
            log::error!("flush cost: CPU 1 did not start spinning");
            return;
        }
        poll("spinning, interrupts closed, polled word");
        if !enter(SPINNING_BARE) {
            log::error!("flush cost: CPU 1 did not start spinning without a flush");
            return;
        }
        poll("spinning, interrupts closed, polled word, no flush");
        MODE.store(DONE, Ordering::SeqCst);
    }
}
