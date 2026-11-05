//! Serial console.
//!
//! Outputs from the kernel and applications are typically
//! done through [`log`] macros so verbosity can be controlled
//! as needed. `print!` and `println!` are intentionally
//! omitted from the kernel.
//!
//! The serial port defaults to COM1 (0x3F8), and can be
//! configured through the kernel command line:
//!
//! `serial=[com1|com2|com3|com4]`

use crate::boot;
use astd::sync::{Mutex, MutexGuard};
use ns16550a::PioSerial;

#[allow(dead_code)]
const COM1: usize = 0x3f8;
#[allow(dead_code)]
const COM2: usize = 0x2f8;

/// The serial device.
static SERIAL: Mutex<PioSerial> = Mutex::new(unsafe { PioSerial::new(COM1) });

pub type WriterType = MutexGuard<'static, PioSerial>;

/// Returns a writer that implements `core::fmt::Write`.
pub fn get_writer() -> WriterType {
    SERIAL.lock()
}

/// Initializes early logging.
pub unsafe fn early_init() {
    let serial = SERIAL.lock();
    serial.init();
}

