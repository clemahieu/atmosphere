//! The payload the loader hands dom0. dom0 does not start it: no operation that starts a process is
//! wired. Started, it prints a greeting through a console capability at the slot the root holds its
//! own console at.

#![no_std]
#![no_main]

use core::panic::PanicInfo;

use asys::operation;

const GREETING: [u64; 5] = operation::print_words(b"Hello, world!\n");

#[no_mangle]
extern "C" fn main() -> ! {
    unsafe { operation::invoke(operation::PRINT, operation::ROOT_CONSOLE_SLOT, GREETING) };
    loop {
        core::hint::spin_loop();
    }
}

#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
