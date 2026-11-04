#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[no_mangle]
extern "C" fn main() {
    asys::logger::init_logging_with_level(log::Level::Info);
    log::info!("Hello, world!");
}

#[panic_handler]
pub fn panic(_info: &PanicInfo) -> ! {
    log::info!("panic {:#?}", _info);
    loop {}
}
