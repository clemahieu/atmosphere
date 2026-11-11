// SPDX-License-Identifier: MIT

//! Error handling.

pub type Result<T> = core::result::Result<T, Error>;

use crate::boot::command_line::Component as CommandLineComponent;

/// An error.
#[non_exhaustive]
#[derive(Clone, Debug)]
pub enum Error {
    /// An invalid kernel command-line component.
    InvalidCommandLineOption(CommandLineComponent<'static>),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidCommandLineOption(component) => write!(f, "Invalid kernel command-line component: {component:?}"),
        }
    }
}
