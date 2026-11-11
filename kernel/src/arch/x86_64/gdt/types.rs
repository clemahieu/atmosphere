// SPDX-License-Identifier: MIT

//! The access bytes of GDT descriptors.

/// The Present bit, set in every descriptor in use.
const PRESENT: u8 = 1 << 7;

/// The descriptor privilege level, bits 6 and 5.
const PRIVILEGE_SHIFT: u8 = 5;

/// The descriptor type bit: 1 for code and data, 0 for system descriptors.
const CODE_DATA: u8 = 1 << 4;

/// The Executable bit of a code or data descriptor.
const EXECUTABLE: u8 = 1 << 3;

/// The Readable (code) or Writable (data) bit.
const READ_WRITE: u8 = 1 << 1;

/// The access byte of a code or data descriptor, Intel SDM Volume 3A section 3.4.5.
#[derive(Copy, Clone)]
pub struct AccessByte(pub(super) u8);

impl AccessByte {
    /// A present data segment at the privilege level, neither writable nor executable.
    pub const fn code_data(privilege: u8) -> Self {
        assert!(privilege <= 3);
        Self(PRESENT | privilege << PRIVILEGE_SHIFT | CODE_DATA)
    }

    /// The same segment, executable: a code segment.
    pub const fn executable(self) -> Self {
        Self(self.0 | EXECUTABLE)
    }

    /// The same segment, readable if code and writable if data.
    pub const fn read_write(self) -> Self {
        Self(self.0 | READ_WRITE)
    }

    pub const fn not_present() -> Self {
        Self(0)
    }
}

/// The access byte of a system descriptor, Intel SDM Volume 3A section 3.4.5.
#[derive(Copy, Clone)]
pub struct SystemAccessByte(pub(super) u8);

impl SystemAccessByte {
    /// A present system descriptor of the type at the privilege level.
    pub const fn new(descriptor_type: SystemDescriptorType, privilege: u8) -> Self {
        assert!(privilege <= 3);
        Self(PRESENT | privilege << PRIVILEGE_SHIFT | descriptor_type as u8)
    }

    pub const fn not_present() -> Self {
        Self(0)
    }
}

/// The type of a System descriptor, Intel SDM Volume 3A table 3-2.
#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub enum SystemDescriptorType {
    /// An available TSS.
    AvailableTss = 0b1001,
}
