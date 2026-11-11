// SPDX-License-Identifier: MIT

//! The ELF64 records and values the loader reads, from the System V gABI (file header and
//! program header layouts, `Elf64_Dyn`, `Elf64_Rel`, `Elf64_Rela`), the AMD64 psABI
//! (relocation types, table 4.9) and the AArch64 ELF ABI (dynamic relocations).

/// `e_type` of a shared object, which a position-independent executable is.
pub const ET_DYN: u16 = 3;
/// `e_machine` of this target: `EM_X86_64` or `EM_AARCH64`.
#[cfg(target_arch = "x86_64")]
pub const EM_SELF: u16 = 62;
#[cfg(target_arch = "aarch64")]
pub const EM_SELF: u16 = 183;

pub const PT_LOAD: u32 = 1;
pub const PT_DYNAMIC: u32 = 2;
pub const PF_X: u32 = 1;
pub const PF_W: u32 = 2;
pub const PF_R: u32 = 4;

pub const DT_NULL: i64 = 0;
pub const DT_RELA: i64 = 7;
pub const DT_RELASZ: i64 = 8;
pub const DT_RELAENT: i64 = 9;
pub const DT_REL: i64 = 17;
pub const DT_RELSZ: i64 = 18;
pub const DT_RELENT: i64 = 19;

/// This target's relative relocation: `R_X86_64_RELATIVE` or `R_AARCH64_RELATIVE`.
#[cfg(target_arch = "x86_64")]
pub const R_RELATIVE: u32 = 8;
#[cfg(target_arch = "aarch64")]
pub const R_RELATIVE: u32 = 1027;

pub const HEADER_SIZE: usize = 64;
pub const PROGRAM_HEADER_SIZE: usize = 56;

/// The fields of an ELF64 file header the loader reads.
#[derive(Clone, Debug)]
pub struct Header {
    pub e_ident: [u8; 16],
    pub e_type: u16,
    pub e_machine: u16,
    pub e_entry: u64,
    pub e_shoff: u64,
    pub e_phentsize: u16,
    pub e_phnum: u16,
    pub e_shentsize: u16,
    pub e_shnum: u16,
}

/// The fields of an ELF64 program header the loader reads.
#[derive(Clone, Copy, Debug)]
pub struct ProgramHeader {
    pub p_type: u32,
    pub p_flags: u32,
    pub p_offset: u64,
    pub p_vaddr: u64,
    pub p_filesz: u64,
    pub p_memsz: u64,
}

/// An entry of the dynamic section, read in place: `d_un` as `d_val`.
#[repr(C)]
pub struct Dyn {
    pub d_tag: i64,
    pub d_val: u64,
}

/// A relocation with an explicit addend, read in place.
#[repr(C)]
pub struct Rela {
    pub r_offset: u64,
    pub r_info: u64,
    pub r_addend: i64,
}

/// A relocation whose addend is at the place it relocates, read in place.
#[repr(C)]
pub struct Rel {
    pub r_offset: u64,
    pub r_info: u64,
}

/// `ELF64_R_TYPE`: the relocation type, the low word of `r_info`.
pub fn r_type(r_info: u64) -> u32 {
    r_info as u32
}

fn half(bytes: &[u8], at: usize) -> u16 {
    u16::from_ne_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn word(bytes: &[u8], at: usize) -> u32 {
    u32::from_ne_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn xword(bytes: &[u8], at: usize) -> u64 {
    u64::from_ne_bytes(bytes[at..at + 8].try_into().unwrap())
}

/// Reads an ELF64 file header in the target's byte order, each field from its offset.
pub fn read_header(bytes: &[u8; HEADER_SIZE]) -> Header {
    Header {
        e_ident: bytes[0..16].try_into().unwrap(),
        e_type: half(bytes, 16),
        e_machine: half(bytes, 18),
        e_entry: xword(bytes, 24),
        e_shoff: xword(bytes, 40),
        e_phentsize: half(bytes, 54),
        e_phnum: half(bytes, 56),
        e_shentsize: half(bytes, 58),
        e_shnum: half(bytes, 60),
    }
}

/// Reads an ELF64 program header in the target's byte order, each field from its offset.
pub fn read_program_header(bytes: &[u8; PROGRAM_HEADER_SIZE]) -> ProgramHeader {
    ProgramHeader {
        p_type: word(bytes, 0),
        p_flags: word(bytes, 4),
        p_offset: xword(bytes, 8),
        p_vaddr: xword(bytes, 16),
        p_filesz: xword(bytes, 32),
        p_memsz: xword(bytes, 40),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem;

    #[test]
    fn constants_match_the_gabi_and_psabis() {
        assert_eq!(ET_DYN, 3);
        assert_eq!((PT_LOAD, PT_DYNAMIC), (1, 2));
        assert_eq!((PF_X, PF_W, PF_R), (1, 2, 4));
        assert_eq!((DT_NULL, DT_RELA, DT_RELASZ, DT_RELAENT), (0, 7, 8, 9));
        assert_eq!((DT_REL, DT_RELSZ, DT_RELENT), (17, 18, 19));
    }

    #[cfg(target_arch = "x86_64")]
    const EXPECTED: (u16, u32) = (62, 8);
    #[cfg(target_arch = "aarch64")]
    const EXPECTED: (u16, u32) = (183, 1027);

    #[test]
    fn target_selects_its_machine_and_relative_relocation() {
        assert_eq!((EM_SELF, R_RELATIVE), EXPECTED);
    }

    #[test]
    fn records_have_the_gabi_sizes() {
        assert_eq!((HEADER_SIZE, PROGRAM_HEADER_SIZE), (64, 56));
        assert_eq!(mem::size_of::<Dyn>(), 16);
        assert_eq!(mem::size_of::<Rela>(), 24);
        assert_eq!(mem::size_of::<Rel>(), 16);
    }

    #[test]
    fn r_type_is_the_low_word_of_r_info() {
        assert_eq!(r_type(0x1234_5678_0000_0403), 0x403);
        assert_eq!(r_type(0xffff_ffff_0000_0000), 0);
    }

    #[test]
    fn header_reads_each_field_from_its_offset() {
        let mut bytes = [0u8; HEADER_SIZE];
        for (at, byte) in bytes.iter_mut().enumerate() {
            *byte = at as u8;
        }
        let half = |at: usize| u16::from_ne_bytes([at as u8, at as u8 + 1]);
        let xword = |at: usize| u64::from_ne_bytes(core::array::from_fn(|i| (at + i) as u8));
        let header = read_header(&bytes);
        assert_eq!(header.e_ident, core::array::from_fn(|i| i as u8));
        assert_eq!(header.e_type, half(16));
        assert_eq!(header.e_machine, half(18));
        assert_eq!(header.e_entry, xword(24));
        assert_eq!(header.e_shoff, xword(40));
        assert_eq!(header.e_phentsize, half(54));
        assert_eq!(header.e_phnum, half(56));
        assert_eq!(header.e_shentsize, half(58));
        assert_eq!(header.e_shnum, half(60));
    }

    #[test]
    fn program_header_reads_each_field_from_its_offset() {
        let mut bytes = [0u8; PROGRAM_HEADER_SIZE];
        for (at, byte) in bytes.iter_mut().enumerate() {
            *byte = at as u8;
        }
        let word = |at: usize| u32::from_ne_bytes(core::array::from_fn(|i| (at + i) as u8));
        let xword = |at: usize| u64::from_ne_bytes(core::array::from_fn(|i| (at + i) as u8));
        let ph = read_program_header(&bytes);
        assert_eq!(ph.p_type, word(0));
        assert_eq!(ph.p_flags, word(4));
        assert_eq!(ph.p_offset, xword(8));
        assert_eq!(ph.p_vaddr, xword(16));
        assert_eq!(ph.p_filesz, xword(32));
        assert_eq!(ph.p_memsz, xword(40));
    }
}
