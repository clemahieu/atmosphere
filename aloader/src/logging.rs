//! Logging facilities.

use crate::console::{get_writer, WriterType};
use kernel_logger::Logger;

/// The global logger.
static LOGGER: Logger<WriterType> = Logger::new(get_writer, false);

/// Initializes the logger.
///
/// This should only be called once.
pub unsafe fn init() {
    log::set_logger(&LOGGER)
        .map(|_| log::set_max_level(log::LevelFilter::Trace))
        .unwrap();
}
