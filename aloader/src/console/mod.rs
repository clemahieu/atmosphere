// SPDX-License-Identifier: MIT

//! Serial console.

use core::fmt::Write;

use astd::sync::{Mutex, MutexGuard};

use crate::arch::{self, Serial};

/// The serial device.
static SERIAL: Mutex<Serial> = Mutex::new(arch::serial());

pub type WriterType = MutexGuard<'static, Serial>;

/// Returns a writer that implements `core::fmt::Write`.
pub fn get_writer() -> WriterType {
    SERIAL.lock()
}

/// Initializes early logging.
pub unsafe fn early_init() {
    let serial = SERIAL.lock();
    serial.init();
}

/// Initializes the serial console.
pub unsafe fn init() {
    let mut serial = SERIAL.lock();
    let _invalid_serial = false;

    *serial = arch::serial();

    serial.init();

    // Clear the screen and move the cursor to (0,0).
    //
    // In some terminals, [2J alone does not reset the cursor position.
    write!(serial, "   ALOADER\x1B[2J\x1B[0;0H").unwrap();
}
