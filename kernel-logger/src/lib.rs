// SPDX-License-Identifier: MIT

//! The kernel logger.
//!
//! Shared logger implementation for the microkernel and the
//! loader.

#![no_std]

use core::fmt::Write;
use core::sync::atomic::{AtomicBool, Ordering};

use log::{Level, Metadata, Record};

/// The default logger.
pub struct Logger<WR> {
    /// Function to call to acquire a writer.
    acquire_writer: fn() -> WR,

    /// The maximum log level to emit.
    log_level: Level,

    /// Whether to enable colors or not.
    ///
    /// This can be disabled via the kernel command-line with `nocolors`. Atomic so that the
    /// logger can be a plain static that `log` holds by shared reference while this changes.
    use_colors: AtomicBool,
}

impl<WR, W> Logger<WR>
where
    WR: core::ops::DerefMut<Target = W>,
    W: Write,
{
    /// Creates a logger that writes to what `acquire_writer` returns.
    pub const fn new(acquire_writer: fn() -> WR, use_colors: bool) -> Self {
        Self {
            acquire_writer,
            log_level: Level::Trace,
            use_colors: AtomicBool::new(use_colors),
        }
    }

    /// Sets whether to use colors.
    pub fn set_colors(&self, use_colors: bool) {
        self.use_colors.store(use_colors, Ordering::Relaxed);
    }

    /// Returns the color prefix for a log level.
    fn get_color(level: Level) -> &'static str {
        match level {
            Level::Error => "\x1b[31m",
            Level::Warn => "\x1b[33m",
            Level::Info => "\x1b[34m",
            Level::Debug => "\x1b[36m",
            Level::Trace => "\x1b[35m",
        }
    }
}

impl<WR, W> log::Log for Logger<WR>
where
    WR: core::ops::DerefMut<Target = W>,
    W: Write,
{
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= self.log_level
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let mut writer = (self.acquire_writer)();
            if self.use_colors.load(Ordering::Relaxed) {
                let color = Self::get_color(record.level());
                writeln!(
                    writer,
                    "{}{:>5} {}\x1b[0m",
                    color,
                    record.level(),
                    record.args()
                )
                .unwrap();
            } else {
                writeln!(writer, "{:>5} {}", record.level(), record.args()).unwrap();
            }
        }
    }

    fn flush(&self) {}
}
