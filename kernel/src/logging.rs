//! Logging facilities.
//!
//! The logger is available very early in boot, before allocators
//! are initialized. After the allocator is available, it's possible
//! to configure the logger to log to multiple targets, such as a
//! file in the Filesystem.

use core::ops::{Deref, DerefMut};

use kernel_logger::Logger;

use crate::boot;
use crate::machine::{console, Console};

/// One log line's console. The logger writes through a deref to [`Console`].
struct Line(Console);

impl Deref for Line {
    type Target = Console;

    fn deref(&self) -> &Console {
        &self.0
    }
}

impl DerefMut for Line {
    fn deref_mut(&mut self) -> &mut Console {
        &mut self.0
    }
}

fn line() -> Line {
    Line(console())
}

/// The global logger.
static LOGGER: Logger<Line> = Logger::new(line, true);

/// Initializes the early-boot logger, crashing the kernel on failure.
///
/// This should only be called once.
pub unsafe fn early_init() {
    log::set_logger(&LOGGER)
        .map(|_| log::set_max_level(log::LevelFilter::Info))
        .unwrap();
}

pub unsafe fn init() {
    let cmdline = boot::get_command_line();
    LOGGER.set_colors(!cmdline.nocolor);
}
