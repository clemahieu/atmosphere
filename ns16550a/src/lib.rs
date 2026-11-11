// SPDX-License-Identifier: MIT

//! A simple poll-only NS16550A driver over x86 port I/O.
//!
//! Initializes the serial to 115200 baud, 8N1. Does not do funny stuff with
//! the bytes you send (*cough* uart_16550 *cough*). The Port IO base of COM1
//! is 0x3F8.
//!
//! # Example
//! ```no_run
//! use core::fmt::Write;
//! use ns16550a::PioSerial;
//!
//! let mut serial = unsafe { PioSerial::new(0x3F8) };
//! serial.init();
//! writeln!(serial, "meow").unwrap();
//! serial.putc(b'?');
//! ```
//!
//! References:
//! - <https://osblog.stephenmarz.com/ch2.html>
//! - <https://github.com/mit-pdos/xv6-riscv/blob/riscv/kernel/uart.c>
//! - <http://byterunner.com/16550.html>

#![no_std]
#![cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#![deny(
    asm_sub_register,
    dead_code,
    deprecated,
    missing_abi,
    rustdoc::bare_urls,
    unused_imports,
    unused_must_use,
    unused_mut,
    unused_unsafe,
    unused_variables
)]

use core::arch::asm;
use core::fmt::{Result as FmtResult, Write};

/// Transmit Holding Register
const THR: usize = 0;

/// Interrupt Enable Register
const IER: usize = 1;

/// FIFO Control Register
const FCR: usize = 2;

/// Line Control Register
const LCR: usize = 3;

/// Line Status Register
const LSR: usize = 5;

pub struct PioSerial {
    base: usize,
}

impl PioSerial {
    pub const unsafe fn new(base: usize) -> Self {
        Self { base }
    }

    /// Initializes the serial port.
    ///
    /// Currently hardcoded to do 115200 8N1
    pub fn init(&self) {
        unsafe {
            // Disable interrupts
            pio_write(self.base, IER, 0x00);

            // Enable DLAB to set baud rate
            pio_write(self.base, LCR, 0x80);

            // Set 115200 baud
            pio_write(self.base, 0, 0x01);
            pio_write(self.base, 1, 0x00);

            // Disable DLAB, and 8N1
            pio_write(self.base, LCR, 0x03);

            // Reset and enable FIFOs
            pio_write(self.base, FCR, 0xc7);
        }
    }

    /// Puts a byte to the serial port.
    pub fn putc(&mut self, c: u8) {
        unsafe {
            while pio_read(self.base, LSR) & (1 << 5) == 0 {}

            if c == '\n' as u8 {
                pio_write(self.base, THR, '\r' as u8);
                pio_write(self.base, THR, '\n' as u8);
            } else {
                pio_write(self.base, THR, c);
            }
        }
    }
}

impl Write for PioSerial {
    fn write_str(&mut self, s: &str) -> FmtResult {
        for byte in s.as_bytes() {
            self.putc(*byte);
        }
        Ok(())
    }
}

#[inline(always)]
unsafe fn pio_write(base: usize, reg: usize, value: u8) {
    asm!("out dx, al", in("dx") base + reg, in("al") value, options(nomem, nostack));
}

#[inline(always)]
unsafe fn pio_read(base: usize, reg: usize) -> u8 {
    let mut result: u8;
    asm!("in al, dx", in("dx") base + reg, out("al") result, options(nomem, nostack));
    result
}
