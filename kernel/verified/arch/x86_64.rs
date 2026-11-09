//! The x86_64 arch items. Written from the AMD64 Architecture Programmer's Manual, Volume 2: System
//! Programming (24593).
use vstd::prelude::*;

verus! {

use crate::capability::kernel::{FlushTarget, Flushed};

// The page-entry encoding: the long-mode page-translation entry's bits, chapter 5. The decoders and
// encoders in pagetable/entry.rs, the address checks in util/page_ptr_util_u.rs and the address lemmas
// in capability/map.rs and capability/link.rs read them.

pub const PAGE_ENTRY_PRESENT_MASK: u64 = 0x1;

pub const PAGE_ENTRY_WRITE_MASK: u64 = 0x1u64 << 1;

pub const PAGE_ENTRY_USER_MASK: u64 = 0x1u64 << 2;

/// PS: a large page at the 2M and 1G levels.
pub const PAGE_ENTRY_PS_MASK: u64 = 0x1u64 << 7;

/// NX: no instruction fetch, under EFER.NXE.
pub const PAGE_ENTRY_EXECUTE_MASK: u64 = 0x1u64 << 63;

/// The physical address of a 4K page or of the next table, bits 47:12.
pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

/// A 2M page's address, bits 47:21.
pub const MEM_2m_MASK: u64 = 0x0000_ffff_ffe0_0000;

/// Bits 47:34.
pub const MEM_1g_MASK: u64 = 0x0000_fffc_0000_0000;

/// Flushes every context on this core, all PCIDs and paging-structure caches: changing CR4.PGE does
/// that where a flush of the current PCID would leave entries under the others.
#[verifier(external_body)]
// external_body(glue): only the hardware can attest a flush, so only this makes the token
pub fn flush_every_context(core: usize, epoch: usize) -> (ret: Tracked<Flushed>)
    ensures
        ret@.target == FlushTarget::Core(core as int),
        ret@.epoch == epoch as int,
{
    unsafe {
        core::arch::asm!(
            "mov {cr4}, cr4",
            "xor {cr4}, {pge}",
            "mov cr4, {cr4}",
            "xor {cr4}, {pge}",
            "mov cr4, {cr4}",
            cr4 = out(reg) _,
            pge = const 1 << 7,
        );
    }
    Tracked::assume_new()
}

} // verus!
