use core::arch::x86_64::{_mm_lfence, _rdtsc};
use crate::*;

pub fn test_mmap(){
    let iter = 5000000;
    unsafe {
        let start = _rdtsc();
        for i in 0..iter{
            let error_code = asys::sys_mmap(0xA000000000 + 4096 * i, 0x0000_0000_0000_0002u64 as usize, 1);
            if error_code != 0 {
                log::info!("sys_mmap failed {:?}", error_code);
                return;
            }
        }
        let end = _rdtsc();
        log::info!("mmap cycle per syscall {:?}",(end-start) as usize /iter);
    }
}

pub fn test_pingpong(){
    log::info!("thread_1_main at {:p}", thread_1_main as *const ());
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
        if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let error_code = asys::sys_new_endpoint(1);
        if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let new_stack = 0xA000000000;
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }

        let rsp: usize = (new_stack + size) & !(4096 - 1);

        let error_code = asys::sys_new_thread(0,thread_1_main as *const () as usize, rsp);
        if error_code != 0 {
            log::info!("sys_new_thread failed {:?}", error_code);
            return;
        }
        let iter = 1000000;
        {
            let start = _rdtsc();
            for _i in 0..iter{
                let error_code = asys::sys_receive_empty(0);
                if error_code != 0 {
                    log::info!("sys_new_thread failed {:?}", error_code);
                    return;
                }
            }
            let end: u64 = _rdtsc();
            log::info!("pingpong between threads using send/receive syscall {:x?}",((end-start) as usize /iter));
        }

    }
}

pub fn test_proc_pingpong(){
    unsafe {
        let error_code = asys::sys_new_endpoint(0);
            if error_code != 0 {
                log::info!("sys_new_endpoint failed {:?}", error_code);
                return;
            }
        let mut range = 0;
        loop{
            let (pa,perm) = asys::sys_mresolve(0x8000000000usize + range * 4096);
            log::info!("va:{:x?}, pa:{:x?}, perm:{:?}", 0x8000000000usize + range * 4096, pa, perm);
            if perm == 1{
                break;
            }
            range = range + 1;
        }

        let new_stack = 0x8000000000usize + range * 4096;
        let size = 16 * 1024 * 1024;
        let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
        if error_code != 0 {
            log::info!("sys_mmap failed {:?}", error_code);
            return;
        }
        let rsp: usize = (new_stack + size) & !(4096 - 1);
        let error_code = asys::sys_new_proc(0,dom_1_main as *const () as usize, rsp, 0x8000000000usize, range + size / 4096);
            if error_code != 0 {
                log::info!("sys_new_proc failed {:?}", error_code);
                return;
            }

        log::info!("sys_new_proc success");
        let iter = 10000000;
        {
            let start = _rdtsc();
            for _i in 0..iter{
                let error_code = asys::sys_receive_empty(0);
                if error_code != 0 {
                    log::info!("sys_receive_empty failed {:?}", error_code);
                    return;
                }
            }
            let end = _rdtsc();
            log::info!("pingpong between process using send/receive syscall {:?}",(end-start) as usize /iter);
        }
    }
}

// ---- Timers matching VeriFlat's dom0 timers (same rounds, same log lines) ----

use core::sync::atomic::{AtomicUsize, Ordering};

/// Interleaved rounds of the null syscall timing, and calls per path in each round.
const RETURN_ROUNDS: usize = 5;
const RETURN_CALLS: u64 = 100_000;
/// A syscall number without a handler: the entry stub returns at once.
const NR_UNASSIGNED: usize = asys::MAX_SYSCALLS - 1;
/// Pages per mmap call of the batched mmap timing.
const MMAP_PAGES: usize = 64;
/// Fresh 4K pages mapped and touched by each variant of the mmap timing, and the region of each
/// variant: a separate GiB of dom0's user half that nothing mapped before.
const MMAP_ONLY_PAGES: usize = 16384;
const MMAP_ONLY_VA: [usize; 2] = [0xc0_0000_0000, 0xc0_4000_0000];
const PAGE_MAGIC: u64 = 0x5afe_9a9e;
/// Where dom0's image starts, the page only dom0 maps, and the child's stack size.
const DOM0_IMAGE_VA: usize = 0x80_0000_0000;
const CHILD_UNSHARED_VA: usize = 0xb0_0000_0000;
const CHILD_STACK_PAGES: usize = 16;
const CHILD_ENDPOINT: usize = 3;
/// Stack pages for one faulting child and for its witness, and how many children there are.
const FAULT_STACK_PAGES: usize = 4;
const FAULT_KINDS: [&str; 8] = [
    "a load from an unmapped address",
    "hlt in ring 3",
    "int 33, the IOMMU fault vector",
    "ud2",
    "a division by zero",
    "single-stepping across a syscall with the trap flag",
    "an unmasked SIMD division by zero",
    "int3, which returns, then a load from an unmapped address",
];
const FAULT_ENDPOINT: usize = 4;
/// Mapped by no one.
const UNMAPPED_VA: usize = 0xe0_0000_0000;
static mut WAKE_ONCE_STACK: [u8; 16384] = [0; 16384];
static mut RAX_PROBE_STACK: [u8; 16384] = [0; 16384];
const RAX_PROBE_ENDPOINT: usize = 9;
static SHARED_PAGES: AtomicUsize = AtomicUsize::new(0);
static FAULT_KIND: AtomicUsize = AtomicUsize::new(0);
static FAULT_WITNESS_SP: AtomicUsize = AtomicUsize::new(0);
static FAULTS_REACHED: AtomicUsize = AtomicUsize::new(0);
static FAULTS_SURVIVED: AtomicUsize = AtomicUsize::new(0);
static INT3_RETURNED: AtomicUsize = AtomicUsize::new(0);
static CHILD_RESOLVED: [AtomicUsize; 2] = [AtomicUsize::new(0), AtomicUsize::new(0)];
static CHILD_BOUND: AtomicUsize = AtomicUsize::new(0);
/// Ping-pong round trips to time IPC.
const IPC_ROUNDS: u64 = 1000;
/// Threads created to time `new_thread`.
const TIMED_THREADS: usize = 32;
/// Threads created between two drains of the container scheduler, which holds at most 10 runnable
/// threads (`MAX_CONTAINER_SCHEDULER_LEN`); the waker takes one more slot.
const THREAD_BATCH: usize = 8;

/// Endpoint descriptors of dom0's main thread.
const IPC_ENDPOINT: usize = 0;
const PARK_ENDPOINT: usize = 1;
const WAKE_ENDPOINT: usize = 2;

static mut PONG_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
static mut WAKER_STACK: [u8; 64 * 1024] = [0; 64 * 1024];
/// Shared by every timed thread, which never touches its stack.
static mut PARKED_STACK: [u8; 4096] = [0; 4096];
/// A page of dom0's image that `mresolve` resolves.
#[repr(C, align(4096))]
struct PageBuffer([u64; 512]);
static mut RESOLVED_PAGE: PageBuffer = PageBuffer([1; 512]);
static PONGS: AtomicUsize = AtomicUsize::new(0);

/// The code dom0 exits with when every timer finished. The kernel's failure shutdown writes 0 to the
/// same port, so zero cannot mean success here.
pub const EXIT_SUCCESS: u32 = 0x10;

/// Ends the QEMU run through the isa-debug-exit device at port 0xf4 (dom0 runs with IOPL 3), which
/// exits with status `code << 1 | 1`.
pub fn exit_qemu(code: u32) -> ! {
    unsafe { core::arch::asm!("out dx, eax", in("dx") 0xf4u16, in("eax") code) };
    loop {}
}

fn bench_fail(what: &str, ret: usize) -> ! {
    log::error!("{} failed: {}", what, ret);
    log::error!("dom0 benchmark FAILED");
    exit_qemu(1)
}

fn stack_top<const N: usize>(stack: *const [u8; N]) -> usize {
    stack as usize + N - 8
}

/// A syscall with an unassigned number. Only callee-saved registers survive the syscall.
unsafe fn sys_unassigned() {
    core::arch::asm!(
        "syscall",
        inout("rax") NR_UNASSIGNED => _,
        out("rdi") _, out("rsi") _, out("rdx") _, out("rcx") _,
        out("r8") _, out("r9") _, out("r10") _, out("r11") _,
    );
}

/// Times a syscall with an unassigned number, which returns from the entry stub, and `mresolve` of a
/// mapped page, interleaved, and logs the best round of each in TSC cycles per call.
pub fn time_syscall_returns() {
    let va = (&raw const RESOLVED_PAGE) as usize;
    // Also leaves the per-CPU switch decision at NoSwitching, which the unassigned number returns through.
    let pa = unsafe { asys::sys_mresolve(va) }.0;
    if pa == 1 {
        bench_fail("mresolve of dom0's image", pa);
    }
    let mut best = [u64::MAX; 2];
    for _ in 0..RETURN_ROUNDS {
        let start = unsafe { _rdtsc() };
        for _ in 0..RETURN_CALLS {
            unsafe { sys_unassigned() };
        }
        best[0] = best[0].min((unsafe { _rdtsc() } - start) / RETURN_CALLS);
        let start = unsafe { _rdtsc() };
        for _ in 0..RETURN_CALLS {
            unsafe { asys::sys_mresolve(va) };
        }
        best[1] = best[1].min((unsafe { _rdtsc() } - start) / RETURN_CALLS);
    }
    log::info!("null syscall: {} TSC cycles for an unassigned syscall number, {} for mresolve of a mapped page", best[0], best[1]);
}

/// Times mapping and touching `MMAP_ONLY_PAGES` fresh 4K pages, once with `MMAP_PAGES` pages per
/// mmap and once with one page per call, and logs the mean TSC cycles per page of each.
pub fn time_mmap_only() {
    for (va, per_call) in [(MMAP_ONLY_VA[0], MMAP_PAGES), (MMAP_ONLY_VA[1], 1)] {
        let start = unsafe { _rdtsc() };
        for call in 0..MMAP_ONLY_PAGES / per_call {
            let base = va + call * per_call * 4096;
            let ret = unsafe { asys::sys_mmap(base, 0x2, per_call) };
            if ret != 0 {
                bench_fail("mmap (timed)", ret);
            }
            for i in 0..per_call {
                let p = (base + i * 4096) as *mut u64;
                unsafe { p.write_volatile(PAGE_MAGIC ^ i as u64) };
                if unsafe { p.read_volatile() } != PAGE_MAGIC ^ i as u64 {
                    bench_fail("mmap: reading back a mapped page", base);
                }
            }
        }
        let cycles = (unsafe { _rdtsc() } - start) / MMAP_ONLY_PAGES as u64;
        log::info!("mmap 4K: {} TSC cycles per page, {} pages per call, over {} pages", cycles, per_call, MMAP_ONLY_PAGES);
    }
}

/// Allocates on dom0's heap and checks that its page is not in dom0's IOMMU space: a heap page
/// mapped for DMA is a grant to every device bound to dom0's table that nobody asked for.
pub fn check_heap_not_io_mapped() {
    let v: alloc::vec::Vec<u64> = alloc::vec![0; 64];
    let resolved = unsafe { asys::sys_mresolve_io(v.as_ptr() as usize) }.0;
    log::info!("sys_mresolve_io of a heap page: {:#x}", resolved);
    if resolved != 1 {
        bench_fail("a heap page is IO-mapped", resolved);
    }
}

/// Maps fresh pages and counts those that do not read as zero: what a new page holds is old data.
pub fn check_new_pages_are_zero() {
    const PAGES: usize = 120_000;
    const VA: usize = 0xd0_0000_0000;
    let (mut dirty, mut first) = (0usize, None);
    for call in 0..PAGES / MMAP_PAGES {
        let base = VA + call * MMAP_PAGES * 4096;
        let ret = unsafe { asys::sys_mmap(base, 0x2, MMAP_PAGES) };
        if ret != 0 {
            bench_fail("mmap (zero check)", ret);
        }
        for i in 0..MMAP_PAGES {
            let page = base + i * 4096;
            let mut word = 0;
            while word < 512 {
                let v = unsafe { ((page + word * 8) as *const u64).read_volatile() };
                if v != 0 {
                    dirty += 1;
                    if first.is_none() {
                        first = Some((call * MMAP_PAGES + i, word, v));
                    }
                    break;
                }
                word += 1;
            }
        }
    }
    log::info!("new pages not zero: {} of {}, first {:x?}", dirty, PAGES, first);
    if dirty != 0 {
        bench_fail("a new page holds old data", dirty);
    }
}

/// Sends `IPC_ROUNDS` empty messages on its endpoint, each running the receiving main thread, then
/// parks on that endpoint, which nobody sends on any more.
extern "C" fn pong_thread() -> ! {
    for _ in 0..IPC_ROUNDS {
        PONGS.fetch_add(1, Ordering::SeqCst);
        // The kernel does not set a return value when it switches threads.
        unsafe { asys::sys_send_empty_try_schedule(0) };
    }
    loop {
        unsafe { asys::sys_receive_empty(0) };
    }
}

/// Times one IPC round trip (receive_empty, which blocks and switches to `pong_thread`, then its
/// send_empty_try_schedule, which switches back) while only the two threads are runnable.
pub fn time_ipc_round_trip() {
    let ret = unsafe { asys::sys_new_endpoint(IPC_ENDPOINT) };
    if ret != 0 {
        bench_fail("new_endpoint (IPC)", ret);
    }
    let ret = unsafe { asys::sys_new_thread(IPC_ENDPOINT, pong_thread as *const () as usize, stack_top(&raw const PONG_STACK)) };
    if ret != 0 {
        bench_fail("new_thread (pong)", ret);
    }
    let start = unsafe { _rdtsc() };
    for _ in 0..IPC_ROUNDS {
        unsafe { asys::sys_receive_empty(IPC_ENDPOINT) };
    }
    let cycles = (unsafe { _rdtsc() } - start) / IPC_ROUNDS;
    if PONGS.load(Ordering::SeqCst) != IPC_ROUNDS as usize {
        bench_fail("IPC: pongs sent", PONGS.load(Ordering::SeqCst));
    }
    log::info!("IPC round trip: {} TSC cycles (2 syscalls, 2 thread switches) over {} rounds", cycles, IPC_ROUNDS);
}

/// Makes one syscall with zeroed arguments but `arg`, and returns rax and the six registers the
/// kernel must not leave its own values in, as they stand straight after it.
unsafe fn registers_after_syscall(nr: usize, arg: usize) -> (usize, [usize; 6]) {
    let (rax, rdi, rsi, rdx, r8, r9, r10): (usize, usize, usize, usize, usize, usize, usize);
    unsafe {
        core::arch::asm!(
            "syscall",
            inlateout("rax") nr => rax,
            inlateout("rdi") arg => rdi,
            inlateout("rsi") 0usize => rsi,
            inlateout("rdx") 0usize => rdx,
            lateout("rcx") _,
            inlateout("r8") 0usize => r8,
            inlateout("r9") 0usize => r9,
            lateout("r10") r10,
            lateout("r11") _,
        );
    }
    (rax, [rdi, rsi, rdx, r8, r9, r10])
}

/// Fails the run unless a syscall returns with rdi, rsi, rdx, r8, r9 and r10 zero, both when it
/// returns to the same thread and when another thread's syscall switches back to this one, and
/// unless a syscall that blocked and was woken returns 0 in rax, whatever the last syscall on this
/// core returned. The waker is `waker_thread`, so this runs after `time_new_thread` has started it.
pub fn check_syscall_return_registers() {
    let va = (&raw const RESOLVED_PAGE) as usize;
    let (resolved, same_thread) = unsafe { registers_after_syscall(asys::__NR_MRESOLVE, va & !0xfff) };
    let (woken, switched) = unsafe { registers_after_syscall(asys::__NR_RECEIVE_EMPTY, WAKE_ENDPOINT) };
    log::info!("registers after syscall: same thread {:x?}, switched {:x?}", same_thread, switched);
    log::info!("rax after mresolve {:#x}, after a woken receive {:#x}", resolved, woken);
    if same_thread != [0; 6] || switched != [0; 6] {
        bench_fail("registers left by the kernel", 0);
    }
    if resolved == 0 || resolved == 1 || woken != 0 {
        bench_fail("rax after a woken receive", woken);
    }
}

/// What rax held when `rax_probe` started.
static NEW_THREAD_RAX: AtomicUsize = AtomicUsize::new(usize::MAX);

#[unsafe(naked)]
extern "C" fn rax_probe() -> ! {
    core::arch::naked_asm!(
        "mov [rip + {rax}], rax",
        "jmp {next}",
        rax = sym NEW_THREAD_RAX,
        next = sym wake_once,
    )
}

/// Fails the run unless a new thread starts with rax 0, not whatever its creator's last syscall left.
pub fn check_new_thread_rax() {
    let va = (&raw const RESOLVED_PAGE) as usize;
    let ret = unsafe { asys::sys_new_endpoint(RAX_PROBE_ENDPOINT) };
    if ret != 0 {
        bench_fail("new_endpoint (rax)", ret);
    }
    let (resolved, _) = unsafe { registers_after_syscall(asys::__NR_MRESOLVE, va & !0xfff) };
    let ret = unsafe {
        asys::sys_new_thread(RAX_PROBE_ENDPOINT, rax_probe as *const () as usize, stack_top(&raw const RAX_PROBE_STACK))
    };
    if ret != 0 {
        bench_fail("new_thread (rax)", ret);
    }
    unsafe { asys::sys_receive_empty(RAX_PROBE_ENDPOINT) };
    let rax = NEW_THREAD_RAX.load(Ordering::SeqCst);
    log::info!("rax after mresolve {:#x}, in a new thread {:#x}", resolved, rax);
    if rax != 0 {
        bench_fail("rax in a new thread", rax);
    }
}

const SECOND_CORE_ENDPOINT: usize = 10;
const SECOND_CORE_SYSCALLS: usize = 1000;
/// How long to wait for the other core, in TSC cycles. With no timer, a thread only runs on another
/// core, so one that never starts means CPU 1 is not scheduling.
const SECOND_CORE_CYCLES: u64 = 60_000_000_000;
static mut SECOND_CORE_STACK: [u8; 16384] = [0; 16384];
static SECOND_CORE_MADE: AtomicUsize = AtomicUsize::new(0);
static SECOND_CORE_STOP: AtomicUsize = AtomicUsize::new(0);
static SECOND_CORE_REPORTED: AtomicUsize = AtomicUsize::new(0);
static SECOND_CORE_WOKEN: AtomicUsize = AtomicUsize::new(0);
/// A value on a cache line of its own.
#[repr(align(64))]
struct OwnLine(AtomicUsize);
/// The thread on CPU 1 reads this while it waits. `#[used]` keeps the static whole: without it, LLVM
/// splits it into its one field and drops the padding, and the statics after it share the line.
#[used]
static SECOND_CORE_CONTEND: OwnLine = OwnLine(AtomicUsize::new(0));
const CONTEND_NOW: usize = 1;
const CONTEND_DONE: usize = 2;
static SECOND_CORE_PLACED: AtomicUsize = AtomicUsize::new(0);
/// How many times the thread blocks with nothing else runnable: once on each core, since a wake swaps
/// sender and receiver onto each other's core.
const SECOND_CORE_BLOCKS: usize = 2;

/// Makes syscalls until told to stop, blocks with nothing to run on its core, then holds CPU 1 for the
/// rest of the boot.
extern "C" fn second_core_thread() -> ! {
    let va = (&raw const RESOLVED_PAGE) as usize & !0xfff;
    while SECOND_CORE_STOP.load(Ordering::SeqCst) == 0 {
        unsafe { asys::sys_mresolve(va) };
        SECOND_CORE_MADE.fetch_add(1, Ordering::SeqCst);
    }
    log::info!("thread on CPU 1 made {} syscalls", SECOND_CORE_MADE.load(Ordering::SeqCst));
    SECOND_CORE_REPORTED.store(1, Ordering::SeqCst);
    while SECOND_CORE_CONTEND.0.load(Ordering::SeqCst) != CONTEND_DONE {
        if SECOND_CORE_CONTEND.0.load(Ordering::SeqCst) == CONTEND_NOW {
            unsafe { asys::sys_mresolve(va) };
            SECOND_CORE_MADE.fetch_add(1, Ordering::SeqCst);
        } else {
            core::hint::spin_loop();
        }
    }
    for block in 1..=SECOND_CORE_BLOCKS {
        // Wait until the other thread is running on the other core. If it were still in the scheduler,
        // blocking here would run it on this core, and this core would not be left with nothing to run.
        while SECOND_CORE_PLACED.load(Ordering::SeqCst) < block - 1 {
            core::hint::spin_loop();
        }
        // A new thread holds the endpoint it was created with at descriptor 0.
        unsafe { asys::sys_receive_empty(0) };
        SECOND_CORE_WOKEN.store(block, Ordering::SeqCst);
    }
    // Touching no memory from here on, so no line this core reads moves when CPU 0's benchmarks write
    // it: a read of a line the IPC benchmark writes costs it a line transfer each round trip, about
    // 40 TSC cycles with this core in the same CCD and 370 across CCDs.
    loop {
        core::hint::spin_loop();
    }
}

/// Fails the run unless a thread on CPU 1 and this one on CPU 0 both make syscalls at the same time.
/// Nothing preempts this thread, so the other can only run on the other core.
pub fn check_second_core() {
    let va = (&raw const RESOLVED_PAGE) as usize & !0xfff;
    let ret = unsafe { asys::sys_new_endpoint(SECOND_CORE_ENDPOINT) };
    if ret != 0 {
        bench_fail("new_endpoint (second core)", ret);
    }
    let ret = unsafe {
        asys::sys_new_thread(
            SECOND_CORE_ENDPOINT,
            second_core_thread as *const () as usize,
            stack_top(&raw const SECOND_CORE_STACK),
        )
    };
    if ret != 0 {
        bench_fail("new_thread (second core)", ret);
    }
    let deadline = unsafe { _rdtsc() } + SECOND_CORE_CYCLES;
    let mut mine = 0;
    while mine < SECOND_CORE_SYSCALLS || SECOND_CORE_MADE.load(Ordering::SeqCst) < SECOND_CORE_SYSCALLS {
        unsafe { asys::sys_mresolve(va) };
        // Count only while the other thread is also running.
        if SECOND_CORE_MADE.load(Ordering::SeqCst) > 0 {
            mine += 1;
        }
        if unsafe { _rdtsc() } > deadline {
            bench_fail("a thread on the second core", SECOND_CORE_MADE.load(Ordering::SeqCst));
        }
    }
    SECOND_CORE_STOP.store(1, Ordering::SeqCst);
    while SECOND_CORE_REPORTED.load(Ordering::SeqCst) == 0 {
        if unsafe { _rdtsc() } > deadline {
            bench_fail("the second core's report", 0);
        }
        core::hint::spin_loop();
    }
    log::info!("thread on CPU 0 made {} syscalls beside it", mine);
    time_contended_syscalls();
    // The thread blocks on CPU 1 with nothing to run there. A wake puts it on this core and this thread
    // in the scheduler, which CPU 1 takes from. The second wake swaps them back, so this thread ends on
    // CPU 0 with the other on CPU 1. A send with no receiver yet does nothing, so each is retried.
    for block in 1..=SECOND_CORE_BLOCKS {
        while SECOND_CORE_WOKEN.load(Ordering::SeqCst) < block {
            unsafe { asys::sys_send_empty_try_schedule(SECOND_CORE_ENDPOINT) };
            if unsafe { _rdtsc() } > deadline {
                bench_fail("waking a thread blocked with nothing to run", block);
            }
        }
        SECOND_CORE_PLACED.store(block, Ordering::SeqCst);
    }
    log::info!("a thread blocked with nothing else to run on each core, and was woken from the other");
}

/// Calls per timed batch, and batches per measurement. A host interrupt or preemption lands in one
/// batch, so it moves the mean but not the minimum or the median.
const BATCH_CALLS: u64 = 1000;
const BATCHES: usize = 100;
const CONTENTION_CALLS: u64 = BATCH_CALLS * BATCHES as u64;

/// The TSC, read after every earlier instruction has finished and before any later one starts.
fn fenced_tsc() -> u64 {
    unsafe {
        _mm_lfence();
        let tsc = _rdtsc();
        _mm_lfence();
        tsc
    }
}

/// TSC cycles per call: the least and the median over the batches, and the mean over every call.
struct Batched {
    min: u64,
    median: u64,
    mean: u64,
}

/// How long a syscall takes, timed in BATCHES batches of BATCH_CALLS calls.
fn time_mresolve(va: usize) -> Batched {
    let mut per_call = [0u64; BATCHES];
    let mut total = 0;
    for batch in per_call.iter_mut() {
        let start = fenced_tsc();
        for _ in 0..BATCH_CALLS {
            unsafe { asys::sys_mresolve(va) };
        }
        let cycles = fenced_tsc() - start;
        total += cycles;
        *batch = cycles / BATCH_CALLS;
    }
    per_call.sort_unstable();
    Batched { min: per_call[0], median: per_call[BATCHES / 2], mean: total / CONTENTION_CALLS }
}

/// How much the other core slows this one through the kernel's lock: the same syscall with that core
/// idle in user mode, then with it making the same call in a loop.
fn time_contended_syscalls() {
    let va = (&raw const RESOLVED_PAGE) as usize & !0xfff;
    let alone = time_mresolve(va);
    let made = SECOND_CORE_MADE.load(Ordering::SeqCst);
    SECOND_CORE_CONTEND.0.store(CONTEND_NOW, Ordering::SeqCst);
    while SECOND_CORE_MADE.load(Ordering::SeqCst) == made {
        core::hint::spin_loop();
    }
    let contended = time_mresolve(va);
    SECOND_CORE_CONTEND.0.store(CONTEND_DONE, Ordering::SeqCst);
    let other = SECOND_CORE_MADE.load(Ordering::SeqCst) - made;
    log::info!(
        "sys_mresolve alone: min {}, median {}, mean {} TSC cycles per call over {} batches of {} calls",
        alone.min, alone.median, alone.mean, BATCHES, BATCH_CALLS,
    );
    log::info!(
        "sys_mresolve contended: min {}, median {}, mean {} TSC cycles per call over {} batches of {} calls, with the other core contending ({} calls there)",
        contended.min, contended.median, contended.mean, BATCHES, BATCH_CALLS, other,
    );
    if other < CONTENTION_CALLS as usize / 100 {
        bench_fail("the other core contending", other);
    }
}

/// Fails the run unless the logging syscalls refuse a buffer the caller does not own, and accept
/// one it does.
pub fn check_log_buffers() {
    let mine = b"a buffer dom0 owns";
    let cases: [(&str, *const u8, usize, isize); 4] = [
        ("a kernel address", 0x1_0000_0000 as *const u8, 64, 1),
        ("an unmapped address", 0xa0_0000_0000u64 as *const u8, 64, 1),
        ("a range that overflows", usize::MAX as *const u8, 64, 1),
        ("dom0's own buffer", mine.as_ptr(), mine.len(), 0),
    ];
    for (what, data, len, expected) in cases {
        let ret = unsafe { asys::sys_print(data, len) };
        log::info!("sys_print of {}: {}", what, ret);
        if ret != expected {
            bench_fail(what, ret as usize);
        }
    }
    let level = unsafe { syscall_log_raw(mine.as_ptr(), mine.len(), 99) };
    log::info!("sys_log with level 99: {}", level);
    if level != 1 {
        bench_fail("a log level past the end", level as usize);
    }
}

/// Every syscall that takes an endpoint index, with an index past the descriptor array.
pub fn check_endpoint_indexes() {
    let calls: [(&str, unsafe fn(usize) -> usize); 5] = [
        ("sys_new_endpoint", |i| unsafe { asys::sys_new_endpoint(i) }),
        ("sys_new_thread", |i| unsafe { asys::sys_new_thread(i, 0, 0) }),
        ("sys_new_proc", |i| unsafe { asys::sys_new_proc(i, 0, 0, 0xa0_0000_0000, 1) }),
        ("sys_send_empty_try_schedule", |i| unsafe { asys::sys_send_empty_try_schedule(i) }),
        ("sys_receive_empty", |i| unsafe { asys::sys_receive_empty(i) }),
    ];
    for (what, call) in calls {
        for index in [128, usize::MAX] {
            let ret = unsafe { call(index) };
            log::info!("{} with endpoint index {:#x}: {}", what, index, ret);
            if ret != 1 {
                bench_fail(what, ret);
            }
        }
    }
}

/// A number with no handler and a number past the table, each right after a call that returned
/// something else, so a stale return value cannot pass for the error.
pub fn check_unassigned_syscalls() {
    let va = (&raw const RESOLVED_PAGE) as usize;
    for number in [NR_UNASSIGNED, asys::MAX_SYSCALLS] {
        let pa = unsafe { asys::sys_mresolve(va) }.0;
        let ret = unsafe { sys_raw(number) };
        log::info!("syscall {} after a call returning {:#x}: {}", number, pa, ret);
        if ret != -1 {
            bench_fail("a syscall with no handler", ret as usize);
        }
    }
}

/// A syscall by number, which the asys wrappers cannot express for a number with no handler.
unsafe fn sys_raw(number: usize) -> isize {
    let ret: isize;
    unsafe {
        core::arch::asm!(
            "syscall",
            inlateout("rax") number => ret,
            lateout("rdi") _, lateout("rsi") _, lateout("rdx") _, lateout("rcx") _,
            lateout("r8") _, lateout("r9") _, lateout("r10") _, lateout("r11") _,
        );
    }
    ret
}

/// Binds a device function no process uses, naming an address that is not dom0's IO table in the
/// register the argument used to arrive in, then flushes it. Both return 1 with no IOMMU; the gate's
/// IOMMU boot looks for these lines with 0, and for the kernel's log of the table it bound.
pub fn check_device_iommu() {
    let (bus, device, function) = (0, 0x1f, 7);
    let bound: isize;
    unsafe {
        core::arch::asm!(
            "syscall",
            inlateout("rax") asys::__NR_SET_DEVICE_IOMMU => bound,
            inlateout("rdi") bus => _,
            inlateout("rsi") device => _,
            inlateout("rdx") function => _,
            inlateout("r8") 0x1000usize => _,
            lateout("rcx") _, lateout("r9") _, lateout("r10") _, lateout("r11") _,
        );
    }
    log::info!("sys_set_device_iommu of dom0's own table: {}", bound);
    let flushed = unsafe { asys::sys_invalidate_iotlb(bus, device, function, 0) };
    log::info!("sys_invalidate_iotlb of that device: {}", flushed);
    // Every bus would share one context table, so a bind on another bus must not reach this one.
    let other_bus = unsafe { asys::sys_set_device_iommu(1, device, function) };
    log::info!("sys_set_device_iommu on bus 1: {}", other_bus);
    if other_bus != 1 {
        bench_fail("sys_set_device_iommu on bus 1", other_bus as usize);
    }
}

/// Starts a child process that shares dom0's image and a stack, has it resolve two addresses, and
/// checks its results. The endpoint carries only the signal; the results come back through a
/// static in the shared image. The child parks at dom0's next blocking syscall.
pub fn check_child_process() {
    let shared = (&raw const RESOLVED_PAGE) as usize;
    let ret = unsafe { asys::sys_new_endpoint(CHILD_ENDPOINT) };
    if ret != 0 {
        bench_fail("new_endpoint (child)", ret);
    }
    let ret = unsafe { asys::sys_mmap(CHILD_UNSHARED_VA, 0x2, 1) };
    if ret != 0 {
        bench_fail("mmap (unshared with the child)", ret);
    }
    let mut image_pages = 0;
    while unsafe { asys::sys_mresolve(DOM0_IMAGE_VA + image_pages * 4096) }.0 != 1 {
        image_pages += 1;
    }
    let stack = DOM0_IMAGE_VA + image_pages * 4096;
    let fault_stacks = FAULT_KINDS.len() * 2 * FAULT_STACK_PAGES;
    let ret = unsafe { asys::sys_mmap(stack, 0x2, CHILD_STACK_PAGES + fault_stacks) };
    if ret != 0 {
        bench_fail("mmap (child stack)", ret);
    }
    let sp = stack + CHILD_STACK_PAGES * 4096 - 8;
    let shared_pages = image_pages + CHILD_STACK_PAGES + fault_stacks;
    SHARED_PAGES.store(shared_pages, Ordering::SeqCst);
    let ret = unsafe {
        asys::sys_new_proc(CHILD_ENDPOINT, child_process as *const () as usize, sp, DOM0_IMAGE_VA, shared_pages)
    };
    if ret != 0 {
        bench_fail("new_proc", ret);
    }
    unsafe { asys::sys_receive_empty(CHILD_ENDPOINT) };

    let parent = unsafe { (asys::sys_mresolve(shared).0, asys::sys_mresolve(CHILD_UNSHARED_VA).0) };
    let child = (CHILD_RESOLVED[0].load(Ordering::SeqCst), CHILD_RESOLVED[1].load(Ordering::SeqCst));
    log::info!("mresolve of a shared page: dom0 {:#x}, child {:#x}", parent.0, child.0);
    log::info!("mresolve of a page only dom0 maps: dom0 {:#x}, child {:#x}", parent.1, child.1);
    if parent.0 == 1 || child.0 != parent.0 {
        bench_fail("the child's view of a shared page", child.0);
    }
    if parent.1 == 1 || child.1 != 1 {
        bench_fail("the child's view of a page only dom0 maps", child.1);
    }
    // The child has no IO table to bind a device to.
    let bound = CHILD_BOUND.load(Ordering::SeqCst);
    log::info!("sys_set_device_iommu from a process with no IO table: {}", bound);
    if bound != 1 {
        bench_fail("a device bind with no IO table", bound);
    }
}

extern "C" fn child_process() -> ! {
    let shared = (&raw const RESOLVED_PAGE) as usize;
    CHILD_RESOLVED[0].store(unsafe { asys::sys_mresolve(shared) }.0, Ordering::SeqCst);
    CHILD_RESOLVED[1].store(unsafe { asys::sys_mresolve(CHILD_UNSHARED_VA) }.0, Ordering::SeqCst);
    CHILD_BOUND.store(unsafe { asys::sys_set_device_iommu(0, 0x1f, 7) } as usize, Ordering::SeqCst);
    // sys_new_proc puts the endpoint in the child's descriptor 0.
    unsafe { asys::sys_send_empty_try_schedule(0) };
    loop {
        unsafe { asys::sys_receive_empty(0) };
    }
}

/// Device ids no PCI function can have. The gate's IOMMU boot is what makes this reach the checks:
/// with no IOMMU both syscalls return 1 first.
pub fn check_device_arguments() {
    let calls: [(&str, unsafe fn(usize, usize, usize) -> isize); 2] = [
        ("sys_set_device_iommu", |b, d, f| unsafe { asys::sys_set_device_iommu(b, d, f) }),
        ("sys_invalidate_iotlb", |b, d, f| unsafe { asys::sys_invalidate_iotlb(b, d, f, 0) }),
    ];
    let ids = [(256, 0, 0), (0, 32, 0), (0, 0, 8), (usize::MAX, 0, 0), (0, usize::MAX, 0), (0, 0, usize::MAX)];
    for (what, call) in calls {
        for (bus, device, function) in ids {
            let ret = unsafe { call(bus, device, function) };
            log::info!("{} of {:#x}:{:#x}.{:#x}: {}", what, bus, device, function, ret);
            if ret != 1 {
                bench_fail(what, ret as usize);
            }
        }
    }
}

/// Has a child process fault in each way the kernel must survive, and checks that only the child
/// stops. A witness thread in the child wakes dom0, since dom0 is blocked when the child dies.
pub fn check_process_faults() {
    let ret = unsafe { asys::sys_new_endpoint(FAULT_ENDPOINT) };
    if ret != 0 {
        bench_fail("new_endpoint (faults)", ret);
    }
    let shared_pages = SHARED_PAGES.load(Ordering::SeqCst);
    let first_stack = DOM0_IMAGE_VA + (shared_pages - FAULT_KINDS.len() * 2 * FAULT_STACK_PAGES) * 4096;
    for (kind, what) in FAULT_KINDS.iter().enumerate() {
        let child_stack = first_stack + kind * 2 * FAULT_STACK_PAGES * 4096;
        let sp = child_stack + FAULT_STACK_PAGES * 4096 - 8;
        FAULT_WITNESS_SP.store(sp + FAULT_STACK_PAGES * 4096, Ordering::SeqCst);
        FAULT_KIND.store(kind, Ordering::SeqCst);
        let ret = unsafe {
            asys::sys_new_proc(FAULT_ENDPOINT, faulting_child as *const () as usize, sp, DOM0_IMAGE_VA, shared_pages)
        };
        if ret != 0 {
            bench_fail("new_proc (fault)", ret);
        }
        unsafe { asys::sys_receive_empty(FAULT_ENDPOINT) };
        let reached = FAULTS_REACHED.load(Ordering::SeqCst);
        let survived = FAULTS_SURVIVED.load(Ordering::SeqCst);
        log::info!("a child faulting by {}: {} reached a fault, {} ran past one", what, reached, survived);
        if reached != kind + 1 || survived != 0 {
            bench_fail(what, survived);
        }
    }
    log::info!("int3 from a child returned {} time", INT3_RETURNED.load(Ordering::SeqCst));
    if INT3_RETURNED.load(Ordering::SeqCst) != 1 {
        bench_fail("int3 from a child", INT3_RETURNED.load(Ordering::SeqCst));
    }
    // The last witness dies at dom0's next block. Have it die here, not inside a benchmark.
    let ret = unsafe {
        asys::sys_new_thread(FAULT_ENDPOINT, wake_once as *const () as usize, stack_top(&raw const WAKE_ONCE_STACK))
    };
    if ret != 0 {
        bench_fail("new_thread (wake once)", ret);
    }
    unsafe { asys::sys_receive_empty(FAULT_ENDPOINT) };
}

extern "C" fn wake_once() -> ! {
    unsafe { asys::sys_send_empty_try_schedule(0) };
    loop {
        unsafe { asys::sys_receive_empty(0) };
    }
}

extern "C" fn faulting_child() -> ! {
    let witness = fault_witness as *const () as usize;
    unsafe { asys::sys_new_thread(0, witness, FAULT_WITNESS_SP.load(Ordering::SeqCst)) };
    FAULTS_REACHED.fetch_add(1, Ordering::SeqCst);
    match FAULT_KIND.load(Ordering::SeqCst) {
        0 => unsafe {
            core::ptr::read_volatile(UNMAPPED_VA as *const u64);
        },
        1 => unsafe { core::arch::asm!("hlt") },
        2 => unsafe { core::arch::asm!("int 33") },
        3 => unsafe { core::arch::asm!("ud2") },
        4 => unsafe {
            core::arch::asm!(
                "xor edx, edx",
                "xor ecx, ecx",
                "mov eax, 1",
                "div ecx",
                out("eax") _, out("ecx") _, out("edx") _,
            )
        },
        5 => unsafe {
            // TF set across a syscall: the kernel must not take the trap on its first instruction. It
            // comes back on return, in this child.
            core::arch::asm!(
                "pushfq",
                "or qword ptr [rsp], 0x100",
                "popfq",
                "syscall",
                "nop",
                inlateout("rax") usize::MAX => _,
                lateout("rcx") _, lateout("r11") _,
            )
        },
        6 => unsafe {
            // Clear every mask bit, then divide with both registers holding zero.
            let mxcsr = 0u32;
            core::arch::asm!(
                "ldmxcsr [{mxcsr}]",
                "xorps xmm0, xmm0",
                "xorps xmm1, xmm1",
                "divss xmm0, xmm1",
                mxcsr = in(reg) &mxcsr,
            )
        },
        _ => unsafe {
            core::arch::asm!("int3");
            INT3_RETURNED.fetch_add(1, Ordering::SeqCst);
            core::ptr::read_volatile(UNMAPPED_VA as *const u64);
        },
    }
    FAULTS_SURVIVED.fetch_add(1, Ordering::SeqCst);
    loop {
        unsafe { asys::sys_receive_empty(0) };
    }
}

extern "C" fn fault_witness() -> ! {
    unsafe {
        asys::sys_send_empty_try_schedule(0);
        core::ptr::read_volatile(UNMAPPED_VA as *const u64);
    }
    FAULTS_SURVIVED.fetch_add(1, Ordering::SeqCst);
    loop {
        unsafe { asys::sys_receive_empty(0) };
    }
}

/// Every syscall that takes an address range, with ranges no process may name. The first two are
/// in the kernel's own L4 slot.
pub fn check_address_ranges() {
    let calls: [(&str, unsafe fn(usize, usize) -> usize); 5] = [
        ("sys_mmap", |va, len| unsafe { asys::sys_mmap(va, 0x2, len) }),
        ("sys_mresolve", |va, _| unsafe { sys_raw_arg(asys::__NR_MRESOLVE, va) }),
        ("sys_mresolve_io", |va, _| unsafe { sys_raw_arg(asys::__NR_MRESOLVE_IO, va) }),
        ("sys_io_mmap", |va, len| unsafe { asys::sys_io_mmap(va, 0x2, len) }),
        ("sys_new_proc", |va, len| unsafe { asys::sys_new_proc(CHILD_ENDPOINT, 0, 0, va, len) }),
    ];
    let free = 0xd0_0000_0000usize;
    let ranges = [
        ("L4 index 0", 0x1000, 1),
        ("the kernel's image", 0x1_0000_0000, 1),
        ("an unaligned address", free + 1, 1),
        ("a non-canonical address", 1 << 48, 1),
        ("a range past the user half", (1 << 48) - 4096, 2),
        ("a range that wraps", free, 1 << 52),
        ("the longest length", free, usize::MAX),
    ];
    for (what, call) in calls {
        for (range, va, len) in ranges {
            let ret = unsafe { call(va, len) };
            log::info!("{} of {} ({:#x}, {:#x}): {}", what, range, va, len, ret);
            if ret != 1 {
                bench_fail(what, ret);
            }
        }
    }
}

/// A syscall with one argument, unmasked, which the asys resolve wrappers do not send.
unsafe fn sys_raw_arg(number: usize, arg: usize) -> usize {
    let ret: usize;
    unsafe {
        core::arch::asm!(
            "syscall",
            inlateout("rax") number => ret,
            inlateout("rdi") arg => _,
            lateout("rsi") _, lateout("rdx") _, lateout("rcx") _,
            lateout("r8") _, lateout("r9") _, lateout("r10") _, lateout("r11") _,
        );
    }
    ret
}

/// Flags a process may set that the kernel must not run with. Each comes back on return.
pub fn check_entry_flags() {
    const TEXT: &str = "text copied with the process's flags set";
    for (what, bits) in [("DF", 0x400usize), ("AC", 0x4_0000), ("NT", 0x4000), ("all", 0x4_4400)] {
        let ret: isize;
        let flags: usize;
        unsafe {
            core::arch::asm!(
                "pushfq",
                "or [rsp], {bits}",
                "popfq",
                "syscall",
                "pushfq",
                "pop {flags}",
                "push 0x202",
                "popfq",
                bits = in(reg) bits,
                flags = lateout(reg) flags,
                inlateout("rax") asys::__NR_LOG => ret,
                inlateout("rdi") TEXT.as_ptr() => _,
                inlateout("rsi") TEXT.len() => _,
                inlateout("rdx") 3usize => _,
                lateout("rcx") _, lateout("r8") _, lateout("r9") _, lateout("r10") _, lateout("r11") _,
            );
        }
        log::info!("a syscall with {} set returned {}, flags {:#x}", what, ret, flags);
        if ret != 0 || flags & bits != bits {
            bench_fail(what, flags);
        }
    }
}

/// sys_log with a level no log::Level can hold, which asys::sys_log cannot express.
unsafe fn syscall_log_raw(data: *const u8, len: usize, level: usize) -> isize {
    let ret: isize;
    unsafe {
        core::arch::asm!(
            "syscall",
            inlateout("rax") asys::__NR_LOG => ret,
            inlateout("rdi") data => _,
            inlateout("rsi") len => _,
            inlateout("rdx") level => _,
            lateout("rcx") _,
            lateout("r8") _,
            lateout("r9") _,
            lateout("r10") _,
            lateout("r11") _,
        );
    }
    ret
}

/// Entry of every timed thread: parks on its endpoint without touching its stack.
#[unsafe(naked)]
extern "C" fn parked_thread() -> ! {
    core::arch::naked_asm!("2:", "mov eax, {nr}", "xor edi, edi", "syscall", "jmp 2b", nr = const asys::__NR_RECEIVE_EMPTY);
}

/// Wakes the main thread, blocked on the wake endpoint, every time it runs.
extern "C" fn waker_thread() -> ! {
    loop {
        unsafe { asys::sys_send_empty_try_schedule(0) };
    }
}

/// Empties the container scheduler but for the waker: the first receive runs the queue up to the
/// waker, which wakes this thread and queues itself behind the threads created since; the second runs
/// those threads, which park, and then the waker again.
fn drain_scheduler() {
    for _ in 0..2 {
        unsafe { asys::sys_receive_empty(WAKE_ENDPOINT) };
    }
}

/// Times `new_thread` over `TIMED_THREADS` creations and logs the best and the mean in TSC cycles.
pub fn time_new_thread() {
    for (index, what) in [(PARK_ENDPOINT, "new_endpoint (park)"), (WAKE_ENDPOINT, "new_endpoint (wake)")] {
        let ret = unsafe { asys::sys_new_endpoint(index) };
        if ret != 0 {
            bench_fail(what, ret);
        }
    }
    let ret = unsafe { asys::sys_new_thread(WAKE_ENDPOINT, waker_thread as *const () as usize, stack_top(&raw const WAKER_STACK)) };
    if ret != 0 {
        bench_fail("new_thread (waker)", ret);
    }
    drain_scheduler();
    let sp = stack_top(&raw const PARKED_STACK);
    let (mut best, mut total) = (u64::MAX, 0);
    for _ in 0..TIMED_THREADS / THREAD_BATCH {
        for _ in 0..THREAD_BATCH {
            let start = unsafe { _rdtsc() };
            let ret = unsafe { asys::sys_new_thread(PARK_ENDPOINT, parked_thread as *const () as usize, sp) };
            let cycles = unsafe { _rdtsc() } - start;
            if ret != 0 {
                bench_fail("new_thread (timed)", ret);
            }
            best = best.min(cycles);
            total += cycles;
        }
        drain_scheduler();
    }
    log::info!("new_thread: best {} TSC cycles, mean {} over {} threads", best, total / TIMED_THREADS as u64, TIMED_THREADS);
}
