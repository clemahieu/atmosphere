// SPDX-License-Identifier: MIT

//! The benchmarks that need threads on cores: shared-memory CAS contention across 2 to every core, and
//! the round trip of placing, starting and suspending a thread on another core and on dom0's own,
//! design/synthetic-benchmark-suite/ (Barrelfish's shared_mem_clock and scheduling). Their threads are
//! dom0's own, bound to its process, so they run dom0's code in its space and share its statics; no map
//! is needed. [`threads_held`] makes them through acall while dom0 still holds its caller token, before
//! the heap takes it; [`register`] adds the cases to the runner, which invoke place, start and suspend
//! raw, as Syscall/Null invokes, the token being the heap's by then.
//!
//! Place takes a thread that was never placed, so the place cases draw a fresh thread from a pool each
//! iteration: [`POOL`] of them for each case, as many as the runner's iterations.

use core::sync::atomic::{AtomicU64, Ordering};

use acall::capability::{place, start};
use acall::memory::retype;
use acall::step::Caller;
use asys::operation;
use vstd::prelude::Tracked;

use crate::{
    dom0_child_count, dom0_child_entry, first_slot, inspect, set_frame_word, untyped_of_pages, ARGUMENT_WORDS,
    HEAP_ENTRY, HEAP_LEAVES, LEAF_BYTES, LEAF_INDICES, THREAD_BYTES,
};

/// The most cores boot gives the root a capability for: one slot each from ROOT_CORE_SLOT to the first
/// untyped's.
const MAX_CORES: u64 = operation::ROOT_UNTYPED_SLOT - operation::ROOT_CORE_SLOT;

/// The iterations the runner makes of a case, warm-up included, which is how many threads a place case
/// uses: abench's PerfConfig::default() in a bench build, its unit-test counts otherwise.
#[cfg(feature = "bench")]
pub(crate) const POOL: u64 = 4 + 20 * 16;
#[cfg(not(feature = "bench"))]
pub(crate) const POOL: u64 = (abench::runner::UNIT_TEST_WARMUP + abench::runner::UNIT_TEST_BATCHES) as u64;

/// The threads, by index: a CAS helper for each core from 1, then the remote place case's pool, then the
/// local one's.
const HELPER_FIRST: u64 = 0;
const REMOTE_FIRST: u64 = HELPER_FIRST + MAX_CORES - 1;
const LOCAL_FIRST: u64 = REMOTE_FIRST + POOL;
const THREADS: u64 = LOCAL_FIRST + POOL;

/// The slots a table leaf gives, past its hidden node.
const LEAF_SLOTS: u64 = LEAF_INDICES - 1;

/// The root entries of dom0's table whose leaves take the threads' capabilities: those after the heap's.
const BENCH_ENTRY: u64 = HEAP_ENTRY + HEAP_LEAVES;
const BENCH_LEAVES: u64 = THREADS.div_ceil(LEAF_SLOTS);

/// How far below the top of the gigabyte untyped the leaves and then the threads' blocks are: a quarter
/// of it, between the blocks the other checks take from that top, the heap's lowest at 8M, and the flush
/// cost's at half.
const BENCH_BELOW_TOP: u64 = 1 << 28;
const _: () = assert!((BENCH_LEAVES + THREADS) * THREAD_BYTES < BENCH_BELOW_TOP / 2);
const _: () = assert!(LEAF_BYTES == THREAD_BYTES);

/// The slot of thread `index`.
const fn slot(index: u64) -> u64 {
    first_slot(BENCH_ENTRY + index / LEAF_SLOTS) + index % LEAF_SLOTS
}

/// A word on a cache line of its own, on both targets, so no two of them share one.
#[repr(C, align(128))]
struct Line(AtomicU64);

impl Line {
    const fn new() -> Self {
        Self(AtomicU64::new(0))
    }

    fn address(&self) -> u64 {
        self.0.as_ptr() as u64
    }
}

/// The counter the CAS case's helpers and dom0 increment.
static COUNTER: Line = Line::new();

/// Each core's helper's count of its increments, which only it writes.
static COUNTS: [Line; MAX_CORES as usize] = [const { Line::new() }; MAX_CORES as usize];

/// The word a place case's thread writes once it runs, which dom0 clears before each.
static WAKE: Line = Line::new();

/// What the local place case's thread writes to WAKE.
const WAKE_WORD: u64 = 0x7761_6b65_5f6c_6f63;

/// How many reads of a word dom0 makes before it gives up on a thread on another core changing it:
/// tens of milliseconds.
const WAKE_READS: u64 = 1 << 24;

/// How many again returns a suspend of a thread running on another core may take before dom0 gives up on
/// that core taking the reschedule IPI, as core_1_restarted_held allows.
const STOP_AGAIN_MAX: u64 = 1 << 20;

// The code a CAS helper runs, in dom0's image: from dom0_bench_cas it increments the word at its first
// argument by compare-and-swap, for good, and after each increment adds one to the word at its second,
// which only it writes. It keeps no stack and enters the kernel only when the timer takes its core.
#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".balign 64",
    ".global dom0_bench_cas",
    "dom0_bench_cas:",
    "2: mov rax, [rdi]",
    "3: lea rcx, [rax + 1]",
    "lock cmpxchg [rdi], rcx",
    "jne 3b",
    "inc qword ptr [rsi]",
    "jmp 2b",
);
#[cfg(target_arch = "aarch64")]
core::arch::global_asm!(
    ".balign 64",
    ".global dom0_bench_cas",
    "dom0_bench_cas:",
    "2: ldaxr x9, [x0]",
    "add x9, x9, #1",
    "stlxr w10, x9, [x0]",
    "cbnz w10, 2b",
    "ldr x9, [x1]",
    "add x9, x9, #1",
    "str x9, [x1]",
    "b 2b",
);

unsafe extern "C" {
    /// The first instruction of the CAS helper's code above.
    fn dom0_bench_cas();
}

/// How many cores run threads, from core 0 up, which threads_held finds; 0 until it has.
static CORES: AtomicU64 = AtomicU64::new(0);

/// Whether thread `index` is retyped from its block of the untyped at `untyped` above `low`, bound to
/// dom0's process, and its frame gets `entry` and `arguments`.
fn thread_made(caller: &mut Tracked<Caller>, untyped: u64, low: u64, index: u64, entry: unsafe extern "C" fn(), arguments: [u64; 3]) -> bool {
    let base = low + (BENCH_LEAVES + index) * THREAD_BYTES;
    let thread = slot(index);
    retype(caller, untyped, operation::RETYPE_THREAD, base, thread, operation::ROOT_PROCESS_SLOT).status == operation::STATUS_OK
        && set_frame_word(caller, thread, operation::PC_WORD, entry as u64) == operation::STATUS_OK
        && (0..3).all(|k| set_frame_word(caller, thread, ARGUMENT_WORDS[k], arguments[k]) == operation::STATUS_OK)
}

/// Whether dom0 makes the benchmarks' threads, from the gigabyte untyped, the last from `empty` down,
/// BENCH_BELOW_TOP below its top: table leaves into the BENCH_LEAVES root entries from BENCH_ENTRY; a CAS
/// helper on COUNTER and a core's COUNTS for each core from 1, placed on that core at priority 0; POOL
/// threads that count at WAKE, for the remote place case; and POOL threads that write WAKE_WORD to WAKE
/// and suspend themselves, for the local one. A place case's threads are not placed. Boot gives the root
/// a capability for every core the kernel can run on, booted or not, so dom0 finds the cores that run
/// threads by their helpers: each is started, seen counting or not within WAKE_READS reads and
/// suspended, and the first that did not count ends the cores in CORES.
pub(crate) fn threads_held(caller: &mut Tracked<Caller>, empty: u64) -> bool {
    let Some((untyped, block)) = untyped_of_pages(caller, empty, 1 << 18) else {
        return false;
    };
    let low = block.base + (4096 << block.order) - BENCH_BELOW_TOP;
    let leaves = (0..BENCH_LEAVES).all(|l| {
        retype(caller, untyped, operation::RETYPE_LEAF, low + l * LEAF_BYTES, BENCH_ENTRY + l, 0).status == operation::STATUS_OK
    });
    if !leaves || !matches!(inspect(caller, operation::ROOT_CORE_SLOT), Ok(core) if core.kind == operation::KIND_CORE) {
        return false;
    }
    let mut cores = 1;
    while cores < MAX_CORES {
        let index = HELPER_FIRST + cores - 1;
        let count = &COUNTS[cores as usize];
        let arguments = [COUNTER.address(), count.address(), 0];
        if !thread_made(caller, untyped, low, index, dom0_bench_cas, arguments)
            || !matches!(inspect(caller, operation::ROOT_CORE_SLOT + cores), Ok(core) if core.kind == operation::KIND_CORE)
            || place(caller, slot(index), operation::ROOT_CORE_SLOT + cores, 0).status != operation::STATUS_OK
            || start(caller, slot(index)).status != operation::STATUS_OK
        {
            return false;
        }
        let ran = moved(count, 0);
        if !stopped(slot(index)) {
            return false;
        }
        if !ran {
            break;
        }
        cores += 1;
    }
    CORES.store(cores, Ordering::Relaxed);
    (0..POOL).all(|k| thread_made(caller, untyped, low, REMOTE_FIRST + k, dom0_child_count, [WAKE.address(), 0, 0]))
        && (0..POOL).all(|k| {
            let index = LOCAL_FIRST + k;
            thread_made(caller, untyped, low, index, dom0_child_entry, [WAKE.address(), WAKE_WORD, slot(index)])
        })
}

/// The status of `operation` on the thread at `thread` with `arguments`, invoked raw.
fn invoked(operation: u64, thread: u64, arguments: [u64; 5]) -> u64 {
    // Place, start and suspend change no address space.
    operation::status(unsafe { operation::invoke(operation, thread, arguments) })
}

/// Whether the thread at `thread` is suspended: a suspend returns ok, after again while it runs on
/// another core, within STOP_AGAIN_MAX.
fn stopped(thread: u64) -> bool {
    let mut again = 0;
    loop {
        match invoked(operation::SUSPEND, thread, [0; 5]) {
            operation::STATUS_AGAIN if again < STOP_AGAIN_MAX => again += 1,
            status => return status == operation::STATUS_OK,
        }
    }
}

/// Whether `word` comes to hold something other than `from` within WAKE_READS reads.
fn moved(word: &Line, from: u64) -> bool {
    (0..WAKE_READS).any(|_| word.0.load(Ordering::Acquire) != from)
}

/// One increment of COUNTER by compare-and-swap, retried until it lands.
fn cas_increment() {
    let mut seen = COUNTER.0.load(Ordering::Relaxed);
    while let Err(now) = COUNTER.0.compare_exchange(seen, seen + 1, Ordering::AcqRel, Ordering::Relaxed) {
        seen = now;
    }
}

/// Registers, for each count of cores from 2 to CORES, Atomic/ContendedCasScaling/<n>Cores: dom0
/// on core 0 increments COUNTER by CAS, one increment an iteration, while the helpers of cores 1 to n - 1
/// do the same for good, each started and seen counting before the first iteration and suspended after
/// the last. With two cores or more it registers Core/PlaceStartSuspend/RemoteCore: each iteration
/// places a fresh thread on core 1 (step Place), starts it (Start), reads WAKE until the thread's count
/// there moves (Wake) and suspends it, again until core 1 has stopped it (Suspend). It always registers
/// Core/PlaceStartSuspend/LocalCore: a fresh thread placed on core 0 at priority 1, above dom0's 0
/// (Place), started, which runs it there at once, writing WAKE_WORD and suspending itself before dom0
/// runs again (Start), and WAKE read for that word (Wake).
pub(crate) fn register(registry: &mut abench::runner::Registry) -> Result<(), &'static str> {
    let cores = CORES.load(Ordering::Relaxed);
    assert!(cores >= 1, "threads_held found the cores");
    for n in 2..=cores {
        registry.register(alloc::format!("Atomic/ContendedCasScaling/{n}Cores"), move |state| {
            let helpers = 1..n;
            let started = helpers.clone().all(|c| {
                let seen = COUNTS[c as usize].0.load(Ordering::Acquire);
                invoked(operation::START, slot(HELPER_FIRST + c - 1), [0; 5]) == operation::STATUS_OK
                    && moved(&COUNTS[c as usize], seen)
            });
            if started {
                while state.keep_running() {
                    cas_increment();
                }
            }
            let suspended = helpers.into_iter().all(|c| stopped(slot(HELPER_FIRST + c - 1)));
            started && suspended
        })?;
    }
    if cores >= 2 {
        let mut next = 0;
        registry.register("Core/PlaceStartSuspend/RemoteCore", move |state| {
            for step in ["Place", "Start", "Wake", "Suspend"] {
                state.declare_step(step);
            }
            while state.keep_running() {
                if next == POOL {
                    return false;
                }
                let thread = slot(REMOTE_FIRST + next);
                next += 1;
                WAKE.0.store(0, Ordering::Release);
                if invoked(operation::PLACE, thread, [operation::ROOT_CORE_SLOT + 1, 0, 0, 0, 0]) != operation::STATUS_OK {
                    return false;
                }
                state.next_step();
                if invoked(operation::START, thread, [0; 5]) != operation::STATUS_OK {
                    return false;
                }
                state.next_step();
                if !moved(&WAKE, 0) {
                    return false;
                }
                state.next_step();
                if !stopped(thread) {
                    return false;
                }
            }
            true
        })?;
    }
    let mut next = 0;
    registry.register("Core/PlaceStartSuspend/LocalCore", move |state| {
        for step in ["Place", "Start", "Wake"] {
            state.declare_step(step);
        }
        while state.keep_running() {
            if next == POOL {
                return false;
            }
            let thread = slot(LOCAL_FIRST + next);
            next += 1;
            WAKE.0.store(0, Ordering::Release);
            if invoked(operation::PLACE, thread, [operation::ROOT_CORE_SLOT, 1, 0, 0, 0]) != operation::STATUS_OK {
                return false;
            }
            state.next_step();
            if invoked(operation::START, thread, [0; 5]) != operation::STATUS_OK {
                return false;
            }
            state.next_step();
            if !(0..WAKE_READS).any(|_| WAKE.0.load(Ordering::Acquire) == WAKE_WORD) {
                return false;
            }
        }
        true
    })
}
