// SPDX-License-Identifier: MIT

//! COM1, the kernel's serial console. design/machine-glue-below-the-kernel/.

use core::fmt::{self, Write};

use astd::sync::{Mutex, MutexGuard};
use ns16550a::PioSerial;

const COM1: usize = 0x3f8;

static SERIAL: Mutex<PioSerial> = Mutex::new(unsafe { PioSerial::new(COM1) });

/// COM1's writer. It holds the port's lock until it is dropped.
pub struct Console(MutexGuard<'static, PioSerial>);

impl Write for Console {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.0.write_str(text)
    }
}

/// COM1, holding its lock for as long as the value lives.
pub fn console() -> Console {
    Console(SERIAL.lock())
}

/// Programs COM1. Once, before any [`console`] write.
pub unsafe fn console_init() {
    SERIAL.lock().init();
}
