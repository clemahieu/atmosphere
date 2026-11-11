// SPDX-License-Identifier: MIT

//! The PL011, the kernel's serial console. design/machine-glue-below-the-kernel/.

use core::fmt::{self, Write};

use astd::sync::{Mutex, MutexGuard};

use crate::instruction::{load, store};

/// The PL011's registers, where QEMU virt's device tree puts them: node `pl011@9000000`, one page, the
/// machine's `stdout-path`.
const BASE: usize = 0x0900_0000;

/// UARTDR, the data register: a write pushes the byte onto the transmit FIFO, or into the transmit
/// holding register while the FIFO is disabled (DDI 0183 3.3.1).
const DATA: usize = 0x000;

/// UARTFR, the flag register (DDI 0183 3.3.3).
const FLAG: usize = 0x018;

/// TXFF: the transmit FIFO or holding register is full.
const TRANSMIT_FULL: u32 = 1 << 5;

struct Pl011 {
    base: usize,
}

impl Pl011 {
    /// # Safety
    ///
    /// A PL011's registers are at `base`, and nothing else writes them while this value is used.
    const unsafe fn new(base: usize) -> Self {
        Self { base }
    }
}

impl Write for Pl011 {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        for byte in text.bytes() {
            unsafe {
                while load(self.base + FLAG) & TRANSMIT_FULL != 0 {
                    core::hint::spin_loop();
                }
                store(self.base + DATA, byte as u32);
            }
        }
        Ok(())
    }
}

static SERIAL: Mutex<Pl011> = Mutex::new(unsafe { Pl011::new(BASE) });

/// The PL011's writer. It holds the port's lock until it is dropped.
pub struct Console(MutexGuard<'static, Pl011>);

impl Write for Console {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.0.write_str(text)
    }
}

/// The PL011, holding its lock for as long as the value lives.
pub fn console() -> Console {
    Console(SERIAL.lock())
}

/// Does nothing: the firmware leaves the PL011 enabled and its line set. Once, before any [`console`]
/// write.
pub unsafe fn console_init() {}

#[cfg(test)]
mod tests {
    use core::fmt::Write;
    use std::thread;
    use std::time::Duration;
    use std::vec::Vec;

    use super::{Pl011, DATA, FLAG, TRANSMIT_FULL};
    use crate::instruction::{events, Block, Event};

    #[test]
    fn each_byte_goes_to_the_data_register_in_order() {
        let block = Block::new();
        // Every flag but the transmitter's: none of them holds a byte back.
        block.set(FLAG, !TRANSMIT_FULL);
        let mut uart = unsafe { Pl011::new(block.base()) };
        let text = "dom0 capability done\n";

        uart.write_str(text).unwrap();

        let stores: Vec<Event> =
            text.bytes().map(|byte| Event::Store { register: block.base() + DATA, value: byte as u32 }).collect();
        assert_eq!(events(), stores);
    }

    #[test]
    fn a_byte_waits_while_the_transmitter_is_full() {
        let block = Block::new();
        block.set(FLAG, TRANSMIT_FULL);
        thread::scope(|scope| {
            let writer = scope.spawn(|| {
                let mut uart = unsafe { Pl011::new(block.base()) };
                uart.write_str("A").unwrap();
            });
            thread::sleep(Duration::from_millis(50));
            assert_eq!(block.get(DATA), 0);
            assert!(!writer.is_finished());
            block.set(FLAG, 0);
        });
        assert_eq!(block.get(DATA), b'A' as u32);
    }

    #[test]
    fn the_registers_are_the_manuals() {
        // DDI 0183G Table 3-1: UARTDR at 0x000, UARTFR at 0x018; 3.3.3: TXFF is bit 5.
        assert_eq!((DATA, FLAG, TRANSMIT_FULL), (0x000, 0x018, 0x20));
    }
}
