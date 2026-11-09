#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[no_mangle]
extern "C" fn main() -> ! {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::info!("Hello, world!");
    // The parent waits on the endpoint sys_new_proc puts in descriptor 0.
    unsafe { asys::sys_send_empty_try_schedule(0) };
    loop {
        unsafe { asys::sys_receive_empty(0) };
    }
}

#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    log::info!("panic {:#?}", _info);
    loop {}
}
