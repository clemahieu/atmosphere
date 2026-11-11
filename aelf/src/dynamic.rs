// SPDX-License-Identifier: MIT

//! Relocation fixups.

use core::mem;
use core::ptr;
use core::slice;

use super::elf::{
    r_type, Dyn, ProgramHeader, Rel, Rela, DT_NULL, DT_REL, DT_RELA, DT_RELAENT, DT_RELASZ,
    DT_RELENT, DT_RELSZ, PT_DYNAMIC, R_RELATIVE,
};

pub struct Dynamic {
    ptr: *const Dyn,
    load_bias: usize,
    load_bias_loader: usize,
}

impl Dynamic {
    pub fn from_program_headers<'a>(
        mut phs: impl Iterator<Item = &'a ProgramHeader>,
        load_bias: usize,
        load_bias_loader: usize,
    ) -> Option<Self> {
        phs.find(|ph| ph.p_type == PT_DYNAMIC).map(|ph| {
            let ptr = load_bias_loader.wrapping_add(ph.p_vaddr as usize) as *const Dyn;
            Self {
                ptr,
                load_bias,
                load_bias_loader,
            }
        })
    }

    pub fn fixup(self) {
        let mut cur = self.ptr;

        let mut rela_data = None;
        let mut rela_len = None;

        let mut rel_data = None;
        let mut rel_len = None;

        loop {
            let entry = unsafe { &*cur };

            match entry.d_tag {
                DT_NULL => break,

                // DT_RELA
                DT_RELA => {
                    rela_data =
                        Some(entry.d_val.wrapping_add(self.load_bias_loader as _) as *const Rela);
                }
                DT_RELASZ => {
                    rela_len = Some(entry.d_val as usize / mem::size_of::<Rela>());
                }
                DT_RELAENT => {
                    let actual_size = entry.d_val as usize;
                    if actual_size != mem::size_of::<Rela>() {
                        panic!("DT_RELAENT has unsupported size");
                    }
                }

                // DT_REL
                DT_REL => {
                    rel_data =
                        Some(entry.d_val.wrapping_add(self.load_bias_loader as _) as *const Rel);
                }
                DT_RELSZ => {
                    rel_len = Some(entry.d_val as usize / mem::size_of::<Rel>());
                }
                DT_RELENT => {
                    let actual_size = entry.d_val as usize;
                    if actual_size != mem::size_of::<Rel>() {
                        panic!("DT_RELENT has unsupported size");
                    }
                }

                _ => {}
            }

            cur = unsafe { cur.add(1) };
        }

        if let (Some(rela_data), Some(rela_len)) = (rela_data, rela_len) {
            let rela = unsafe { slice::from_raw_parts(rela_data, rela_len) };
            for reloc in rela {
                let r_type = r_type(reloc.r_info);
                if r_type != R_RELATIVE {
                    panic!("Unsupported relocation type");
                }

                let relocated = self.load_bias.wrapping_add(reloc.r_addend as usize);
                let ptr = self.load_bias_loader.wrapping_add(reloc.r_offset as usize) as *mut usize;

                unsafe {
                    ptr::write_unaligned(ptr, relocated);
                }
            }
        }

        if let (Some(rel_data), Some(rel_len)) = (rel_data, rel_len) {
            let rel = unsafe { slice::from_raw_parts(rel_data, rel_len) };
            for reloc in rel {
                let r_type = r_type(reloc.r_info);
                if r_type != R_RELATIVE {
                    panic!("Unsupported relocation type");
                }

                let ptr = self.load_bias_loader.wrapping_add(reloc.r_offset as usize) as *mut usize;
                unsafe {
                    let addend = *ptr;
                    let relocated = self.load_bias.wrapping_add(addend);
                    *ptr = relocated;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // An image in the loader's memory, in 8-byte words: a dynamic section at word 0, a RELA
    // table of one entry at word 16, a REL table of one entry at word 20, the RELA target at
    // word 24 and the REL target, holding its addend, at word 25.
    #[test]
    fn fixup_applies_rela_and_rel_relative_relocations() {
        let mut image = [0u64; 26];
        let dynamic = [
            (DT_RELA, 16 * 8),
            (DT_RELASZ, mem::size_of::<Rela>() as u64),
            (DT_RELAENT, mem::size_of::<Rela>() as u64),
            (DT_REL, 20 * 8),
            (DT_RELSZ, mem::size_of::<Rel>() as u64),
            (DT_RELENT, mem::size_of::<Rel>() as u64),
            (DT_NULL, 0),
        ];
        for (i, (tag, val)) in dynamic.iter().enumerate() {
            image[2 * i] = *tag as u64;
            image[2 * i + 1] = *val;
        }
        // A symbol index in the high word, which a relative relocation ignores.
        let r_info = 0x5_0000_0000 | R_RELATIVE as u64;
        image[16..19].copy_from_slice(&[24 * 8, r_info, 0x1234]);
        image[20..22].copy_from_slice(&[25 * 8, r_info]);
        image[25] = 0x5678;

        let load_bias = 0x4000_0000;
        let ph = ProgramHeader {
            p_type: PT_DYNAMIC,
            p_flags: 0,
            p_offset: 0,
            p_vaddr: 0,
            p_filesz: 7 * 16,
            p_memsz: 7 * 16,
        };
        let dynamic =
            Dynamic::from_program_headers([ph].iter(), load_bias, image.as_mut_ptr() as usize)
                .unwrap();
        dynamic.fixup();

        assert_eq!(image[24], 0x4000_1234);
        assert_eq!(image[25], 0x4000_5678);
    }
}
