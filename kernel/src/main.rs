//! The Atmosphere microkernel.
//!
//! See [`KernelCommandLine`](boot::command_line::KernelCommandLine) for a list of accepted kernel command-line options.

#![no_std]
#![feature(coverage_attribute)]
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
#![no_main]

mod arch;
mod boot;
mod capability;
mod cpu;
mod debugger;
mod error;
mod logging;
mod machine;
mod utils;
mod lock;
mod flush;

use core::sync::atomic::{AtomicBool, Ordering};
use core::panic::PanicInfo;

use astd::boot::BootInfo;

/// CPU 1's stack while it is idle.
static mut AP_STACK: cpu::KernelStack = cpu::KernelStack::new();
/// CPU 1 sets this when it has come up, so CPU 0 can start contending for the lock with it. CPU 0
/// waits `arch::stall_cycles` for it: a core that does not start is reported, not fatal.
static AP_UP: AtomicBool = AtomicBool::new(false);

/// CPU 0 entry point.
#[no_mangle]
extern "C" fn main(boot_info: *const BootInfo) -> isize {
    unsafe {
        machine::console_init();
        logging::early_init();

        cpu::init_cpu(0); // Now get_current() can be used
        arch::init_boot_core();
    }

    boot_cpu0(boot_info)
}

/// The rest of CPU 0's boot. Never inlined: main's prologue runs before the core can report a fault,
/// so a large frame probed there would overflow without a report.
#[inline(never)]
fn boot_cpu0(boot_info: *const BootInfo) -> isize {
    unsafe {
        arch::write_protect::check();
        cpu::guard_stacks();
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

    let boot_info = boot::get_boot_info();

    let syscall_stack = &cpu::get_current().syscall_stack;
    log::info!(
        "CPU 0 syscall stack {:p}-{:p}, guard {:p}-{:p}",
        syscall_stack.lowest(),
        syscall_stack.bottom(),
        syscall_stack.guard(),
        syscall_stack.lowest(),
    );
    unsafe {
        start_second_core();
    }
    let entry = capability::boot(boot_info);
    let (entry_point, initial_sp) = (entry.pc, entry.sp.cast::<u8>());

    log::info!("initial_sp: {:?}", initial_sp);
    unsafe {
        let (base, size) = if let Some(payload) = &boot_info.payload {
            (payload.base as u64, payload.size as u64)
        } else {
            (0, 0)
        };

        arch::enter_userspace(entry_point, initial_sp as *mut _, base, size);
    }
}

/// Ticks of the machine's timer the stray_timer build arms it for as CPU 0 enters dom0, in
/// `arch::enter_userspace` before its last line: short beside dom0's run, so the interrupt arrives
/// before dom0 finishes, and before that line, so the report shows that the kernel takes no
/// interrupt while a line in progress holds the console's lock.
#[cfg(feature = "stray_timer")]
const STRAY_TIMER_TICKS: u64 = 10_000;

/// Times the lock test's loop on CPU 0 alone, then starts CPU 1, and both contend for the lock until
/// the test is done, so that dom0's log and CPU 1's start-up log do not interleave.
unsafe fn start_second_core() {
    lock::time_alone();
    let idle_stack = &*(&raw const AP_STACK);
    arch::guard(idle_stack.guard());
    let stack = idle_stack.bottom() as u64;
    machine::start_core(1, stack, ap_main, arch::translation_root(boot::get_boot_info()));

    let deadline = arch::cycles() + arch::stall_cycles();
    // `|`, not `||`: a branch here would be taken or not by how fast CPU 1 starts.
    cpu::spin_until(|| AP_UP.load(Ordering::SeqCst) | (arch::cycles() > deadline));
    if !AP_UP.load(Ordering::SeqCst) {
        log::error!("CPU 1 did not start");
        return;
    }
    lock::contend();
    lock::report_contention();
    flush::check_second_core();
}

/// AP entry point. The machine trampoline calls this with the cpu index.
extern "C" fn ap_main(cpu_id: u64) -> ! {
    unsafe {
        cpu::init_cpu(cpu_id as usize);
        arch::init_core();
        arch::write_protect::check();
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
        arch::wait();
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

    // FIXME: Signal all other CPUs to halt

    unsafe {
        arch::spin_forever();
    }
}

