//! The root process of its kernel instance. It treats what boot gave it as all there is and does
//! not assume it owns the machine, so several instances each with a root stay possible. Why, and
//! what to do about a change that breaks this: atmo-6x9.17.1.

#![no_std]
#![no_main]

extern crate alloc;
// extern crate ixgbe_driver;
extern crate nvme_driver;
extern crate pcid;
extern crate ring_buffer;

mod e810_client;
mod ixgbe_client;
mod nvme_client;
mod pci;
mod slab_alloc;
// mod elf;
// mod dom1;
// mod maglev;
// mod smoltcp_device;

use core::panic::PanicInfo;
// mod benchmark_null_driver;
mod syscall_benchmark;
use alloc::vec::Vec;
use constants::*;
use e810_client::test_e810_driver;
use ixgbe_client::*;
use libtime::sys_ns_loopsleep;
pub use log::info as println;
use nvme_client::test_nvme_driver;
use pci::scan_pci_devs;

fn test_sleep() {
    log::trace!("Sleeping for 100 ns");
    sys_ns_loopsleep(100);
    log::trace!("Waking up from sleep");
}

fn test_alloc() {
    log::info!("testing alloc");
    let mut v: Vec<u64> = Vec::with_capacity(32);
    for i in 0..64 {
        v.push(i);
    }
    log::info!("Allocator works");
}

#[no_mangle]
extern "C" fn main(payload_base: *mut u8, payload_size: usize) -> isize {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::trace!("hello {}", "world");
    log::info!("payload {:?}, size {}", payload_base, payload_size);

    // The syscall timers, matching VeriFlat's dom0 timers, on CPU 0 with no other runnable thread.
    syscall_benchmark::check_unassigned_syscalls();
    syscall_benchmark::check_device_iommu();
    syscall_benchmark::check_device_arguments();
    syscall_benchmark::check_log_buffers();
    syscall_benchmark::check_endpoint_indexes();
    syscall_benchmark::check_child_process();
    syscall_benchmark::check_process_faults();
    syscall_benchmark::time_syscall_returns();
    syscall_benchmark::time_mmap_only();
    syscall_benchmark::time_ipc_round_trip();
    syscall_benchmark::time_new_thread();
    syscall_benchmark::check_syscall_return_registers();
    syscall_benchmark::check_new_pages_are_zero();
    log::info!("dom0 benchmark done");
    syscall_benchmark::exit_qemu(syscall_benchmark::EXIT_SUCCESS)
}
fn thread_1_main() {
    log::info!("hello from thread_1_main");
    loop {
        unsafe {
            // log::info!("ping");
            let error_code = asys::sys_send_empty_try_schedule(0);
            if error_code != 0 {
                log::info!("sys_new_thread failed {:?}", error_code);
                return;
            }
        }
    }
}

// fn thread_1_hello_ap() {
//     log::info!("hello from thread_1_main");
// }

fn dom_1_main() {
    log::info!("hello from dom_1_main");
    loop {
        unsafe {
            // log::info!("ping");
            let error_code = asys::sys_send_empty_try_schedule(0);
            if error_code != 0 {
                log::info!("sys_send_empty_try_schedule failed {:?}", error_code);
                return;
            }
        }
    }
}

/// The kernel panic handler.
#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    log::info!("panic {:#?}", _info);
    loop {}
}
