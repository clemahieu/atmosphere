//! The kernel's command line.
//!
//! The firmware starts the loader from removable media, a path with no boot entry and so no load
//! options; the line is a file beside the initrd instead. With no such file the line is empty, as
//! on a machine nobody prepared one for.

use core::fmt;

use astd::string::ArrayString;

/// The bytes `BootInfo::command_line` holds.
pub const CAPACITY: usize = 4096;

/// Why a command-line file was not taken.
#[derive(Debug, PartialEq, Eq)]
pub enum Refused {
    /// It is longer than `CAPACITY` bytes.
    TooLong,
    /// It is not UTF-8.
    NotUtf8,
}

impl fmt::Display for Refused {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::TooLong => write!(f, "it is longer than {} bytes", CAPACITY),
            Self::NotUtf8 => write!(f, "it is not UTF-8"),
        }
    }
}

/// The line for the kernel from the command-line file's bytes, `None` when the partition has no
/// such file: the file's text without the line ends that close it. A reader that stops one byte
/// past `CAPACITY` has read enough for a longer file to be refused.
pub fn from_file(file: Option<&[u8]>) -> Result<ArrayString<CAPACITY>, Refused> {
    let Some(file) = file else {
        return Ok(ArrayString::empty());
    };
    if file.len() > CAPACITY {
        return Err(Refused::TooLong);
    }
    let text = core::str::from_utf8(file).map_err(|_| Refused::NotUtf8)?;
    Ok(ArrayString::new(text.trim_end_matches(['\r', '\n'])).expect("the text is within the capacity"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line(file: &[u8]) -> Result<String, Refused> {
        from_file(Some(file)).map(|line| line.as_str().to_string())
    }

    #[test]
    fn no_file_gives_the_empty_line() {
        assert_eq!(from_file(None).unwrap().as_str(), "");
    }

    #[test]
    fn a_file_gives_its_text_without_the_line_end() {
        assert_eq!(line(b"qemu_debug_exit_io_base=244\n").unwrap(), "qemu_debug_exit_io_base=244");
        assert_eq!(line(b"qemu_debug_exit_io_base=244\r\n").unwrap(), "qemu_debug_exit_io_base=244");
        assert_eq!(line(b"nologo nocolor").unwrap(), "nologo nocolor");
        assert_eq!(line(b"").unwrap(), "");
    }

    #[test]
    fn a_file_of_the_capacity_is_taken_whole() {
        let file = [b'a'; CAPACITY];
        assert_eq!(line(&file).unwrap().len(), CAPACITY);
    }

    #[test]
    fn a_longer_file_is_refused_not_cut() {
        let file = [b'a'; CAPACITY + 1];
        assert_eq!(line(&file), Err(Refused::TooLong));
        // The line end counts: the file is what is measured.
        let mut file = [b'a'; CAPACITY + 1];
        file[CAPACITY] = b'\n';
        assert_eq!(line(&file), Err(Refused::TooLong));
    }

    #[test]
    fn a_file_that_is_not_utf8_is_refused() {
        assert_eq!(line(b"nologo \xff"), Err(Refused::NotUtf8));
        // A sequence the file's end cuts short.
        assert_eq!(line(b"nologo \xe2\x82"), Err(Refused::NotUtf8));
    }
}
