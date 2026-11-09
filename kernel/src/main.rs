//! The Atmosphere microkernel.
//!
//! See [`KernelCommandLine`](boot::command_line::KernelCommandLine) for a list of accepted kernel command-line options.

#![no_std]
#![feature(
    abi_x86_interrupt,
    arbitrary_self_types,
    coverage_attribute,
    custom_test_frameworks
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
#![reexport_test_harness_main = "test_main"]
#![test_runner(crate::test_runner)]
#![no_main]

mod arch;
mod boot;
mod bridge;
mod capability;
mod cpu;
mod debugger;
mod error;
mod gdt;
mod interrupt;
mod logging;
mod machine;
mod syscalls;
mod thread;
mod utils;
mod lock;
mod flush;
mod write_protect;

use core::arch::asm;
use core::sync::atomic::{AtomicBool, Ordering};
use core::{ffi::c_void, panic::PanicInfo};

use astd::boot::BootInfo;

static mut SHUTDOWN_ON_PANIC: bool = false;

/// CPU 1's stack while it is idle.
static mut AP_STACK: cpu::IstStack = cpu::IstStack::new();
/// CPU 1 sets this when it has come up, so CPU 0 can start contending for the lock with it.
static AP_UP: AtomicBool = AtomicBool::new(false);
/// How long CPU 0 waits for it, in TSC cycles. A core that does not start is reported, not fatal.
const AP_START_CYCLES: u64 = 20_000_000_000;

/// CPU 0 entry point.
#[no_mangle]
extern "C" fn main(boot_info: *const BootInfo) -> isize {
    unsafe {
        machine::console_init();
        logging::early_init();

        cpu::init_cpu(0); // Now get_current() can be used
        cpu::init_control_registers();
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
        write_protect::check();
        boot::init(boot_info);
        machine::init(boot::get_boot_info());
        machine::iommu_init();

        logging::init();
    }

    let cmdline = boot::get_command_line();

    if !cmdline.nologo {
        print_logo();
    }

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

    log::info!("CPU 0 syscall stack {:#x}", cpu::get_current().syscall_sp);
    unsafe {
        start_second_core();
    }
    let entry = capability::boot(boot_info);
    let (entry_point, initial_sp) = (entry.pc, entry.sp.cast::<u8>());

    log::info!("initial_sp: {:?}", initial_sp);
    unsafe {
        let (rdi, rsi) = if let Some(payload) = &boot_info.payload {
            (payload.base as u64, payload.size as u64)
        } else {
            (0, 0)
        };

        enter_userspace(entry_point, initial_sp as *mut _, rdi, rsi);
    }
}

/// Starts CPU 1, and both contend for the lock until the test is done, so that dom0's log and CPU 1's
/// start-up log do not interleave.
unsafe fn start_second_core() {
    let stack = (&raw const AP_STACK).cast::<u8>().add(core::mem::size_of::<cpu::IstStack>()) as u64;
    interrupt::boot_ap(1, stack, ap_main as *const () as u64);

    let deadline = core::arch::x86_64::_rdtsc() + AP_START_CYCLES;
    // `|`, not `||`: a branch here would be taken or not by how fast CPU 1 starts.
    cpu::spin_until(|| AP_UP.load(Ordering::SeqCst) | (core::arch::x86_64::_rdtsc() > deadline));
    if !AP_UP.load(Ordering::SeqCst) {
        log::error!("CPU 1 did not start");
        return;
    }
    lock::contend();
    lock::report_contention();
    flush::check_second_core();
}

/// AP entry point, called by the trampoline in boot/ap_start.rs.
extern "C" fn ap_main(cpu_id: u64) -> ! {
    unsafe {
        cpu::init_cpu(cpu_id as usize);
        cpu::init_control_registers();
        gdt::init_cpu();
        interrupt::init_ap();
        syscalls::init_cpu();
        write_protect::check();
    }

    log::info!("CPU {} idle, syscall stack {:#x}", cpu::get_cpu_id(), cpu::get_current().syscall_sp);
    AP_UP.store(true, Ordering::SeqCst);
    lock::contend();

    idle()
}

/// Waits with interrupts open, so this core takes flush IPIs. Nothing schedules a thread on it: no
/// operation that places a thread on a core is wired.
fn idle() -> ! {
    loop {
        unsafe { asm!("sti", "hlt") };
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
