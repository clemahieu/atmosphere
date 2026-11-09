//! The root process of its kernel instance. It treats what boot gave it as all there is and does
//! not assume it owns the machine, so several instances each with a root stay possible. Why, and
//! what to do about a change that breaks this: design/one-kernel-instance/.

#![no_std]
#![no_main]
#![feature(coverage_attribute)]

extern crate alloc;

mod payload;
mod slab_alloc;

use core::panic::PanicInfo;
mod syscall_benchmark;
pub use log::info as println;

#[no_mangle]
extern "C" fn main(payload_base: *mut u8, payload_size: usize) -> isize {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::trace!("hello {}", "world");
    log::info!("payload {:?}, size {}", payload_base, payload_size);

    // First, while CPU 1 has nothing else to run.
    syscall_benchmark::check_second_core_simd_fault();
    // Its thread holds CPU 1 for the rest of the boot, so everything below stays on CPU 0.
    syscall_benchmark::check_second_core();
    // The syscall timers, matching VeriFlat's dom0 timers, on CPU 0 with no other runnable thread.
    syscall_benchmark::check_unassigned_syscalls();
    syscall_benchmark::check_device_iommu();
    syscall_benchmark::check_device_arguments();
    syscall_benchmark::check_log_buffers();
    syscall_benchmark::check_endpoint_indexes();
    syscall_benchmark::check_child_process();
    payload::start(payload_base, payload_size);
    syscall_benchmark::check_process_faults();
    syscall_benchmark::check_address_ranges();
    syscall_benchmark::check_entry_flags();
    syscall_benchmark::check_new_thread_rax();
    syscall_benchmark::time_syscall_returns();
    syscall_benchmark::time_mmap_only();
    syscall_benchmark::time_ipc_round_trip();
    syscall_benchmark::time_new_thread();
    syscall_benchmark::check_syscall_return_registers();
    syscall_benchmark::check_new_pages_are_zero();
    syscall_benchmark::check_heap_not_io_mapped();
    log::info!("dom0 benchmark done");
    syscall_benchmark::exit_qemu(syscall_benchmark::EXIT_SUCCESS)
}

/// The kernel panic handler.
#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    log::info!("panic {:#?}", _info);
    loop {}
}
