//! The Atmosphere microkernel.
//!
//! See [`KernelCommandLine`](boot::command_line::KernelCommandLine) for a list of accepted kernel command-line options.

#![no_std]
#![feature(
    abi_x86_interrupt,
    alloc_error_handler,
    arbitrary_self_types,
    custom_test_frameworks,
    pattern
)]
#![deny(
    asm_sub_register,
    deprecated,
    missing_abi,
    unused_macros,
    unused_must_use,
    unused_unsafe
)]
#![deny(clippy::from_over_into, clippy::needless_question_mark)]
#![deny(rustdoc::bare_urls, rustdoc::broken_intra_doc_links)]
// #![cfg_attr(
//     not(debug_assertions),
//     deny(dead_code, unused_imports, unused_mut, unused_variables,)
// )]
#![reexport_test_harness_main = "test_main"]
#![test_runner(crate::test_runner)]
#![no_main]

mod boot;
mod bridge;
mod console;
mod cpu;
mod debugger;
mod error;
mod gdt;
mod interrupt;
mod iommu;
mod kernel;
mod logging;
mod syscalls;
mod thread;
mod utils;
mod ring_buffer;
mod lock;

use core::arch::asm;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use core::{ffi::c_void, panic::PanicInfo};

use astd::boot::{BootInfo, PhysicalMemoryType};
use x86::Ring;

static mut SHUTDOWN_ON_PANIC: bool = false;

/// CPU 1's stack while it is idle.
static mut AP_STACK: cpu::IstStack = cpu::IstStack::new();
/// CPU 1 sets this when it has come up, so CPU 0 can start contending for the lock with it.
static AP_UP: AtomicBool = AtomicBool::new(false);
/// How long CPU 0 waits for it, in TSC cycles. A core that does not start is reported, not fatal.
const AP_START_CYCLES: u64 = 20_000_000_000;
static mut THREAD_STACK: [u8; 64 * 1024 * 1024] = [0; 64 * 1024 * 1024];
static THREAD_COUNTER: AtomicUsize = AtomicUsize::new(0);

use verified::array_vec::ArrayVec as vArrayVec;

/// CPU 0 entry point.
#[no_mangle]
extern "C" fn main(boot_info: *const BootInfo) -> isize {
    unsafe {
        console::early_init();
        logging::early_init();

        cpu::init_cpu(0); // Now get_current() can be used
        gdt::init_cpu();

        interrupt::init();
        interrupt::init_cpu();

        syscalls::init_cpu();
    }

    boot_cpu0(boot_info)
}

/// The rest of CPU 0's boot. Never inlined: main's prologue runs before the IDT exists, so a large
/// frame probed there would overflow without a report.
#[inline(never)]
fn boot_cpu0(boot_info: *const BootInfo) -> isize {
    unsafe {
        boot::init(boot_info);
        iommu::init_iommu();

        // XXX: disable reinitializing console as it hangs on real hw. disabling it on qemu doesn't
        // cause any harm
        //console::init();
        logging::init();
    }

    let cmdline = boot::get_command_line();

    if !cmdline.nologo {
        print_logo();
    }

    // Thread test
    // unsafe {
    //     thread::start_thread(
    //         thread_main as u64,
    //         &THREAD_STACK as *const _ as u64 + THREAD_STACK.len() as u64,
    //         Ring::Ring0,
    //     );
    // }
    // loop {
    //     let counter = THREAD_COUNTER.load(Ordering::SeqCst);
    //     log::debug!("Counter: {}", counter);
    // }


    kernel::kernel_new();

    log::info!("Command line: {}", boot::get_raw_command_line());
    #[cfg(debug_assertions)]
    {
        log::info!("Atmosphere was built in debug mode.");
    }

    #[cfg(test)]
    {
        log::info!("Atmosphere was built with the test harness");
        test_main();
    }

    let boot_info = boot::get_boot_info();
    let dom0 = boot_info.dom0.as_ref().unwrap();
    let pml4 = boot_info.pml4;
    let mut kernel_pml4: usize = 0;
    unsafe {
        kernel_pml4 = *(pml4 as *const usize);
    }
    // log::info!("dom0: {:?}", dom0);
    // log::info!("pml4: {:?}", pml4);
    // log::info!("kernel_pml4: {:x}", kernel_pml4);
    // log::info!("page_array_len: {:x}", boot_info.pages.len());

    kernel::kernel_init(&boot_info.pages, pml4 as usize, kernel_pml4 as usize);

    log::info!("CPU 0 syscall stack {:#x}", cpu::get_current().syscall_sp);
    unsafe {
        start_second_core();
    }

    let initial_sp = unsafe { dom0.virt_start.add(dom0.reserved_size - 0x1000) };
    log::info!("initial_sp: {:?}", initial_sp);
    unsafe {
        let (rdi, rsi) = if let Some(payload) = &boot_info.payload {
            (payload.base as u64, payload.size as u64)
        } else {
            (0, 0)
        };

        enter_userspace(dom0.entry_point, initial_sp as *mut _, rdi, rsi);
    }
}

/// Starts CPU 1, and both contend for the lock until the test is done, so that dom0's log and CPU 1's
/// start-up log do not interleave.
unsafe fn start_second_core() {
    let stack = (&raw const AP_STACK).cast::<u8>().add(core::mem::size_of::<cpu::IstStack>()) as u64;
    interrupt::boot_ap(1, stack, ap_main as *const () as u64);

    let deadline = core::arch::x86_64::_rdtsc() + AP_START_CYCLES;
    while !AP_UP.load(Ordering::SeqCst) {
        if core::arch::x86_64::_rdtsc() > deadline {
            log::error!("CPU 1 did not start");
            return;
        }
        core::hint::spin_loop();
    }
    lock::contend();
    lock::report_contention();
}

/// AP entry point, called by the trampoline in boot/ap_start.asm.
extern "C" fn ap_main(cpu_id: u64) -> ! {
    unsafe {
        cpu::init_cpu(cpu_id as usize);
        gdt::init_cpu();
        interrupt::init_ap();
        syscalls::init_cpu();
    }

    log::info!("CPU {} idle, syscall stack {:#x}", cpu::get_cpu_id(), cpu::get_current().syscall_sp);
    AP_UP.store(true, Ordering::SeqCst);
    lock::contend();

    // Two cores now enter the kernel under its lock. Interrupts are off while this core could hold
    // the lock, as on every kernel entry, and open only between tries.
    let mut regs = verified::trap::Registers::zeroed();
    loop {
        unsafe { asm!("cli") };
        if kernel::take_next_thread(&mut regs) {
            log::info!("CPU {} entering a thread", cpu::get_cpu_id());
            unsafe { syscalls::enter_thread(&regs) };
        }
        unsafe { asm!("sti") };
        for _ in 0..1000 {
            core::hint::spin_loop();
        }
    }
}

/// Thread entry point.
fn thread_main(cpu_id: u64) {
    //debugger::breakpoint(1);
    loop {
        THREAD_COUNTER.fetch_add(1, Ordering::SeqCst);
    }
}

/// Runs all tests.
#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) -> ! {
    unsafe {
        SHUTDOWN_ON_PANIC = true;
    }

    log::info!("Running {} tests", tests.len());

    for test in tests {
        test();
    }

    log::info!("All good!");

    unsafe {
        boot::shutdown(true);
    }
}

/// Prints the Atmosphere logo.
fn print_logo() {
    let logo = include_str!("logo.txt");
    for line in logo.split('\n') {
        log::info!("{}", line);
    }
}

/// The kernel panic handler.
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("panic! {:x?}", info);

    debugger::breakpoint(1);

    unsafe {
        if SHUTDOWN_ON_PANIC {
            boot::shutdown(false);
        }
    }

    // FIXME: Signal all other CPUs to halt

    unsafe {
        boot::spin_forever();
    }
}

unsafe fn enter_userspace(pc: *const c_void, sp: *mut c_void, rdi: u64, rsi: u64) -> ! {
    log::info!("Going to sysret into {:x?}", pc);
    asm!(
        "pushfq",
        "pop r11",
        "mov rsp, {sp}",
        // HACK: Set IOPL to 3 unconditionally for accessing io ports from dom0
        "or r11, (3 << 12)",
        // dom0 gets its entry arguments in rdi and rsi and no kernel values.
        "xor eax, eax",
        "xor edx, edx",
        "xor ebx, ebx",
        "xor ebp, ebp",
        "xor r8d, r8d",
        "xor r9d, r9d",
        "xor r10d, r10d",
        "xor r12d, r12d",
        "xor r13d, r13d",
        "xor r14d, r14d",
        "xor r15d, r15d",
        "sysretq",

        in("rcx") pc,
        sp = in(reg) sp,
        in("rdi") rdi,
        in("rsi") rsi,
        out("r15") _,
    );

    loop {}
}
