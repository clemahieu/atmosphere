use core::arch::x86_64::_rdtsc;
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

// pub fn try_new_thread_ap(){
//     log::info!("thread_1_hello_ap at {:p}", thread_1_hello_ap as *const ());
//     unsafe {
//         let error_code = asys::sys_new_endpoint(0);
//             if error_code != 0 {
//                 log::info!("sys_new_endpoint failed {:?}", error_code);
//                 return;
//             }
//         let new_stack = 0xA000000000;
//         let size = 16 * 1024 * 1024;
//         let error_code = asys::sys_mmap(new_stack, 0x0000_0000_0000_0002u64 as usize, size / 4096);
//         if error_code != 0 {
//             log::info!("sys_mmap failed {:?}", error_code);
//             return;
//         }

//         let rsp: usize = (new_stack + size) & !(4096 - 1);

//         let error_code = asys::sys_new_thread(0,thread_1_hello_ap as *const () as usize, rsp);
//         if error_code != 0 {
//             log::info!("sys_new_thread failed {:?}", error_code);
//             return;
//         }
//     }
// }

// pub fn test_null_syscall(){
//     unsafe {
//         let error_code = asys::sys_new_endpoint(0);
//             if error_code != 0 {
//                 log::info!("sys_new_endpoint failed {:?}", error_code);
//                 return;
//             }
//         let iter = 50000000;
//             let start = _rdtsc();
//             for i in 0..iter{
//                 let error_code = asys::sys_send_empty_no_wait(0);
//                 if error_code != 5 {
//                     log::info!("sys_send_empty_no_wait failed {:?}", error_code);
//                     return;
//                 }
//             }
//             let end = _rdtsc();
//             log::info!("send no wait cycle per syscall {:?}",(end-start) as usize /iter);
//         }
// }

// pub fn test_new_thread(){
//     unsafe {
//     let error_code = asys::sys_new_endpoint(0);
//         if error_code != 0 {
//             log::info!("sys_new_endpoint failed {:?}", error_code);
//             return;
//         }
//     let iter = 249;
//         let start = _rdtsc();
//         for i in 0..iter{
//             let error_code = asys::sys_new_thread(0,0,0);
//             if error_code != 0 {
//                 log::info!("sys_new_thread failed {:?}", error_code);
//                 return;
//             }
//         }
//         let end = _rdtsc();
//         log::info!("new thread cycle per syscall {:?}",(end-start) as usize /iter);
//     }
// }

// pub fn test_new_proc(){
//     unsafe {
//     let error_code = asys::sys_new_endpoint(0);
//         if error_code != 0 {
//             log::info!("sys_new_endpoint failed {:?}", error_code);
//             return;
//         }
//     let iter = 4095;
//         let start = _rdtsc();
//         for i in 0..iter{
//             let error_code = asys::sys_new_proc(0,0);
//             if error_code != 0 {
//                 log::info!("sys_new_proc failed {:?}", error_code);
//                 return;
//             }
//         }
//         let end = _rdtsc();
//         log::info!("new proc cycle per syscall {:?}",(end-start) as usize /iter);
//     }
// }

// pub fn test_new_endpoint(){
//     let iter = 128;
//     unsafe {
//         let start = _rdtsc();
//         for i in 0..iter{
//             let error_code = asys::sys_new_endpoint(i);
//             if error_code != 0 {
//                 log::info!("sys_new_endpoint failed {:?}", error_code);
//                 return;
//             }
//         }
//         let end = _rdtsc();
//         log::info!("new endpoint cycle per syscall {:?}",(end-start) as usize /iter);
//     }
// }




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

/// Makes one syscall with zeroed arguments but `arg`, and returns the six registers the kernel
/// must not leave its own values in, as they stand straight after it.
unsafe fn registers_after_syscall(nr: usize, arg: usize) -> [usize; 6] {
    let (rdi, rsi, rdx, r8, r9, r10): (usize, usize, usize, usize, usize, usize);
    unsafe {
        core::arch::asm!(
            "syscall",
            inlateout("rax") nr => _,
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
    [rdi, rsi, rdx, r8, r9, r10]
}

/// Fails the run unless a syscall returns with rdi, rsi, rdx, r8, r9 and r10 zero, both when it
/// returns to the same thread and when another thread's syscall switches back to this one, which
/// is `waker_thread`, so this runs after `time_new_thread` has started it.
pub fn check_syscall_return_registers() {
    let va = (&raw const RESOLVED_PAGE) as usize;
    let same_thread = unsafe { registers_after_syscall(asys::__NR_MRESOLVE, va & !0xfff) };
    let switched = unsafe { registers_after_syscall(asys::__NR_RECEIVE_EMPTY, WAKE_ENDPOINT) };
    log::info!("registers after syscall: same thread {:x?}, switched {:x?}", same_thread, switched);
    if same_thread != [0; 6] || switched != [0; 6] {
        bench_fail("registers left by the kernel", 0);
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

/// Binds a device function no process uses to dom0's own IO table, then flushes it. Both return 1
/// with no IOMMU; the gate's IOMMU boot looks for these lines with 0.
pub fn check_device_iommu() {
    let (bus, device, function) = (0, 0x1f, 7);
    let table = unsafe { asys::sys_rd_io_cr3() } as u64;
    let bound = unsafe { asys::sys_set_device_iommu(bus, device, function, table) };
    log::info!("sys_set_device_iommu of dom0's own table: {}", bound);
    let flushed = unsafe { asys::sys_invalidate_iotlb(bus, device, function, 0) };
    log::info!("sys_invalidate_iotlb of that device: {}", flushed);
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
