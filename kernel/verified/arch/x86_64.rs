// SPDX-License-Identifier: MIT

//! The x86_64 arch items. Written from the AMD64 Architecture Programmer's Manual, Volume 2: System
//! Programming (24593).
use vstd::prelude::*;

verus! {

use crate::capability::kernel::CommandBuffers;
#[cfg(verus_keep_ghost)]
use crate::capability::kernel::TlbEntry;
use crate::arch::{BaseRegister, IotlbModel, TlbModel};
use crate::capability::operation::Outcome;
use crate::capability::steps::Steps;
use crate::define::PAddr;
#[cfg(verus_keep_ghost)]
use crate::define::{NUM_IOMMUS, PAGE_SZ, PCID_MAX};
use crate::pagetable::entry::{PageEntry, PageEntryPerm, PageEntryStatus};
#[cfg(verus_keep_ghost)]
use crate::util::page_ptr_util_u::*;

// The page-entry encoding: the long-mode page-translation entry's bits, chapter 5. The decoders and
// the encoder below read them, and mem_valid in util/page_ptr_util_u.rs and the address lemmas in
// capability/map.rs and capability/link.rs read MEM_MASK. The accessed and dirty bits are the
// processor's, set on any core at any time; see design/arch-module/.

pub const PAGE_ENTRY_PRESENT_MASK: u64 = 0x1;

pub const PAGE_ENTRY_WRITE_MASK: u64 = 0x1u64 << 1;

pub const PAGE_ENTRY_USER_MASK: u64 = 0x1u64 << 2;

/// A: the processor sets it in every entry a walk uses, at every level.
pub const PAGE_ENTRY_ACCESSED_MASK: u64 = 0x1u64 << 5;

/// D: the processor sets it in the leaf entry a write goes through. Above a leaf the bit is ignored.
pub const PAGE_ENTRY_DIRTY_MASK: u64 = 0x1u64 << 6;

/// PS: a large page at the 2M and 1G levels.
pub const PAGE_ENTRY_PS_MASK: u64 = 0x1u64 << 7;

/// Whether this target's walker maintains the accessed bit: always on x86_64.
pub open spec fn spec_maintains_accessed() -> bool {
    true
}

#[verifier(when_used_as_spec(spec_maintains_accessed))]
pub fn maintains_accessed() -> (ret: bool)
    ensures
        ret == spec_maintains_accessed(),
{
    true
}

/// Whether this target's walker maintains the dirty bit: always on x86_64.
pub open spec fn spec_maintains_dirty() -> bool {
    true
}

#[verifier(when_used_as_spec(spec_maintains_dirty))]
pub fn maintains_dirty() -> (ret: bool)
    ensures
        ret == spec_maintains_dirty(),
{
    true
}

/// NX: no instruction fetch, under EFER.NXE.
pub const PAGE_ENTRY_EXECUTE_MASK: u64 = 0x1u64 << 63;

/// The physical address of a 4K page or of the next table, bits 47:12.
pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

/// The bits of an entry's word that are not the processor's accessed and dirty bits: a word ANDed with
/// it has its status clear.
pub const STATUS_KEPT_MASK: usize = !((PAGE_ENTRY_ACCESSED_MASK | PAGE_ENTRY_DIRTY_MASK) as usize);

// The decoders and the encoder: a word of a table at a level, in the kernel's numbering (4 for a root,
// 1 for a table of 4K leaves), against the abstract PageEntry, PageEntryPerm and PageEntryStatus.
// x86_64 reads every bit the same way at every level, so it ignores the level; PS is defined at levels
// 2 and 3 only, and the kernel writes it clear elsewhere. Shared code reaches the bits only through
// these specs and lemmas. See design/arch-module/.

pub open spec fn usize2present(v: usize, level: usize) -> bool {
    (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0
}

pub open spec fn usize2ps(v: usize, level: usize) -> bool {
    (v & PAGE_ENTRY_PS_MASK as usize) != 0
}

pub open spec fn usize2write(v: usize, level: usize) -> bool {
    (v & PAGE_ENTRY_WRITE_MASK as usize) != 0
}

pub open spec fn usize2execute_disable(v: usize, level: usize) -> bool {
    (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0
}

pub open spec fn usize2user(v: usize, level: usize) -> bool {
    (v & PAGE_ENTRY_USER_MASK as usize) != 0
}

pub open spec fn usize2accessed(v: usize, level: usize) -> bool {
    (v & PAGE_ENTRY_ACCESSED_MASK as usize) != 0
}

pub open spec fn usize2dirty(v: usize, level: usize) -> bool {
    (v & PAGE_ENTRY_DIRTY_MASK as usize) != 0
}

/// The processor's accessed and dirty bits of a word, apart from the entry it decodes to.
pub open spec fn spec_usize2page_entry_status(v: usize, level: usize) -> PageEntryStatus {
    PageEntryStatus { accessed: usize2accessed(v, level), dirty: usize2dirty(v, level) }
}

#[verifier(when_used_as_spec(spec_usize2page_entry_status))]
pub fn usize2page_entry_status(v: usize, level: usize) -> (ret: PageEntryStatus)
    ensures
        ret == spec_usize2page_entry_status(v, level),
{
    PageEntryStatus {
        accessed: (v & PAGE_ENTRY_ACCESSED_MASK as usize) != 0,
        dirty: (v & PAGE_ENTRY_DIRTY_MASK as usize) != 0,
    }
}

/// The word with its accessed and dirty bits clear.
pub open spec fn spec_without_status(v: usize) -> usize {
    v & STATUS_KEPT_MASK
}

/// What a clear of the status bits writes in place of the word it read.
#[verifier(when_used_as_spec(spec_without_status))]
pub fn without_status(v: usize) -> (ret: usize)
    ensures
        ret == spec_without_status(v),
{
    v & STATUS_KEPT_MASK
}

/// Two words that differ only in the accessed and dirty bits decode to the same entry, so whatever the
/// processor sets there leaves every table's view as it was.
pub proof fn lemma_status_outside_entry(v: usize, w: usize, level: usize)
    requires
        spec_without_status(v) == spec_without_status(w),
    ensures
        spec_usize2page_entry(v, level) == spec_usize2page_entry(w, level),
{
    assert(v & 0x0000_ffff_ffff_f000u64 as usize == w & 0x0000_ffff_ffff_f000u64 as usize
        && (v & 0x1u64 as usize != 0) == (w & 0x1u64 as usize != 0)
        && (v & (0x1u64 << 7u64) as usize != 0) == (w & (0x1u64 << 7u64) as usize != 0)
        && (v & (0x1u64 << 1u64) as usize != 0) == (w & (0x1u64 << 1u64) as usize != 0)
        && (v & (0x1u64 << 63u64) as usize != 0) == (w & (0x1u64 << 63u64) as usize != 0)
        && (v & (0x1u64 << 2u64) as usize != 0) == (w & (0x1u64 << 2u64) as usize != 0))
        by (bit_vector)
        requires
            v & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize == w & (!((0x1u64 << 5u64) | (
            0x1u64 << 6u64))) as usize,
    ;
}

/// Clearing the status bits clears them and keeps the rest: clearing again changes nothing.
pub proof fn lemma_without_status(v: usize, level: usize)
    ensures
        spec_without_status(spec_without_status(v)) == spec_without_status(v),
        spec_usize2page_entry_status(spec_without_status(v), level).is_clear(),
{
    assert((v & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) & (!((0x1u64 << 5u64) | (0x1u64
        << 6u64))) as usize == v & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) by (bit_vector);
    assert((v & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) & (0x1u64 << 5u64) as usize == 0
        && (v & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) & (0x1u64 << 6u64) as usize == 0)
        by (bit_vector);
}

/// The zero word is the empty entry with its status clear, at every level.
pub proof fn zero_leads_is_empty_page_entry(level: usize)
    ensures
        spec_usize2page_entry(0, level).is_empty(),
        spec_usize2page_entry_status(0, level).is_clear(),
        spec_without_status(0) == 0,
{
    assert(0usize & 0x0000_ffff_ffff_f000u64 as usize == 0) by (bit_vector);
    assert(0usize & 0x1 as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x7u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x1u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 63u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x2u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 5u64) as usize == 0 && 0usize & (0x1u64 << 6u64) as usize == 0)
        by (bit_vector);
    assert(0usize & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize == 0) by (bit_vector);
}

pub open spec fn spec_usize2page_entry_perm(v: usize, level: usize) -> PageEntryPerm {
    PageEntryPerm {
        present: usize2present(v, level),
        ps: usize2ps(v, level),
        write: usize2write(v, level),
        execute_disable: usize2execute_disable(v, level),
        user: usize2user(v, level),
    }
}

#[verifier(when_used_as_spec(spec_usize2page_entry_perm))]
pub fn usize2page_entry_perm(v: usize, level: usize) -> (ret: PageEntryPerm)
    ensures
        ret =~= spec_usize2page_entry_perm(v, level),
{
    PageEntryPerm {
        present: (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0,
        ps: (v & PAGE_ENTRY_PS_MASK as usize) != 0,
        write: (v & PAGE_ENTRY_WRITE_MASK as usize) != 0,
        execute_disable: (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0,
        user: (v & PAGE_ENTRY_USER_MASK as usize) != 0,
    }
}

/// The entry a word of a table at `level` holds.
pub open spec fn spec_usize2page_entry(v: usize, level: usize) -> PageEntry {
    PageEntry { addr: usize2pa(v, level), perm: usize2page_entry_perm(v, level) }
}

#[verifier(when_used_as_spec(spec_usize2page_entry))]
pub fn usize2page_entry(v: usize, level: usize) -> (ret: PageEntry)
    ensures
        ret =~= spec_usize2page_entry(v, level),
        mem_valid(ret.addr),
{
    PageEntry { addr: usize2pa(v, level), perm: usize2page_entry_perm(v, level) }
}

pub open spec fn spec_usize2pa(v: usize, level: usize) -> PAddr {
    v & MEM_MASK as usize
}

#[verifier(when_used_as_spec(spec_usize2pa))]
pub fn usize2pa(v: usize, level: usize) -> (ret: PAddr)
    ensures
        ret =~= spec_usize2pa(v, level),
        mem_valid(ret),
{
    let ret = v & MEM_MASK as usize;
    assert(v & 0x0000_ffff_ffff_f000u64 as usize & (!0x0000_ffff_ffff_f000u64) as usize == 0)
        by (bit_vector);
    return ret;
}

/// The word that holds an entry in a table at `level`, with its status clear.
pub fn page_entry2usize(page_entry: &PageEntry, level: usize) -> (ret: usize)
    requires
        mem_valid(page_entry.addr),
    ensures
        spec_usize2page_entry(ret, level) == *page_entry,
        spec_usize2page_entry_status(ret, level).is_clear(),
        page_entry.perm.present ==> ret != 0,
{
    let mut ret: usize = page_entry.addr;

    let ghost_addr = Ghost(page_entry.addr);
    let mut ghost_ret = Ghost(page_entry.addr);
    let ghost_present = Ghost(page_entry.perm.present);
    let ghost_ps = Ghost(page_entry.perm.ps);
    let ghost_write = Ghost(page_entry.perm.write);
    let ghost_execute_disable = Ghost(page_entry.perm.execute_disable);
    assert(ret == ghost_addr@);

    if page_entry.perm.present == true {
        assert(((ret | 0x1u64 as usize) & 0x1u64 as usize) != 0) by (bit_vector);
        assert(((ret | 0x1u64 as usize) & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@)
            by (bit_vector)
            requires
                ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0 && ghost_addr@ == ret,
        ;

        ret = ret | 0x1u64 as usize;

        assert((ret & 0x1u64 as usize) != 0);
        assert(usize2present(ret, level) == page_entry.perm.present);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == page_entry.addr);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert((ghost_ret@ | 0x1u64 as usize) & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize
            == 0) by (bit_vector)
            requires
                ghost_ret@ & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & 0x1u64 as usize) == 0) by (bit_vector)
            requires
                ret & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(usize2present(ret, level) == page_entry.perm.present);

        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ret) by (bit_vector)
            requires
                ret & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(usize2pa(ret, level) == page_entry.addr);

        assert(ghost_addr@ & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret, level) == page_entry.perm.present);
    assert(usize2pa(ret, level) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.ps == true {
        assert(((ret | (0x1u64 << 0x7u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 0x7u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 0x7u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 0x7u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret, level) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 0x7u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64
            | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 0x7u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret, level) == page_entry.perm.present);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0)
            by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret, level) == page_entry.perm.present);
    assert(usize2ps(ret, level) == page_entry.perm.ps);
    assert(usize2pa(ret, level) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.write == true {
        assert(((ret | (0x1u64 << 0x1u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 0x1u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 0x1u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0
            == ghost_ps@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@,
        ;
        assert(((ret | (0x1u64 << 0x1u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 0x1u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret, level) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0);
        assert(usize2write(ret, level) == page_entry.perm.write);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 0x1u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64
            << 0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize
                    == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 0x1u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret, level) == page_entry.perm.present);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert(usize2write(ret, level) == page_entry.perm.write);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
            | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret, level) == page_entry.perm.present);
    assert(usize2ps(ret, level) == page_entry.perm.ps);
    assert(usize2write(ret, level) == page_entry.perm.write);
    assert(usize2pa(ret, level) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
        | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.execute_disable == true {
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 63u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 63u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@,
        ;
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0
            == ghost_write@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@,
        ;
        assert(((ret | (0x1u64 << 63u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 63u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret, level) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@);
        assert(usize2write(ret, level) == page_entry.perm.write);
        assert((ret & (0x1u64 << 63u64) as usize) != 0);
        assert(usize2execute_disable(ret, level) == page_entry.perm.execute_disable);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 63u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64
            << 0x1u64 | 0x1u64 << 63u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 63u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret, level) == page_entry.perm.present);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert(usize2write(ret, level) == page_entry.perm.write);
        assert(usize2execute_disable(ret, level) == page_entry.perm.execute_disable);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
            | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret, level) == page_entry.perm.present);
    assert(usize2ps(ret, level) == page_entry.perm.ps);
    assert(usize2write(ret, level) == page_entry.perm.write);
    assert(usize2execute_disable(ret, level) == page_entry.perm.execute_disable);
    assert(usize2pa(ret, level) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
        | PAGE_ENTRY_EXECUTE_MASK | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.user == true {
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 2u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 2u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0
            == ghost_write@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 63u64) as usize) != 0
            == ghost_execute_disable@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 63u64) as usize) != 0
                    == ghost_execute_disable@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 2u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret, level) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@);
        assert(usize2write(ret, level) == page_entry.perm.write);
        assert((ret & (0x1u64 << 63u64) as usize) != 0 == ghost_execute_disable@);
        assert(usize2execute_disable(ret, level) == page_entry.perm.execute_disable);
        assert((ret & (0x1u64 << 2u64) as usize) != 0);
        assert(usize2user(ret, level) == page_entry.perm.user);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 2u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64
            << 0x1u64 | 0x1u64 << 63u64 | 0x1u64 << 2u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0)
            by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | PAGE_ENTRY_USER_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 2u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret, level) == page_entry.perm.present);
        assert(usize2ps(ret, level) == page_entry.perm.ps);
        assert(usize2write(ret, level) == page_entry.perm.write);
        assert(usize2execute_disable(ret, level) == page_entry.perm.execute_disable);
        assert(usize2user(ret, level) == page_entry.perm.user);
        assert(usize2pa(ret, level) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 | 0x1u64
            << 2u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | PAGE_ENTRY_USER_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret, level) == page_entry.perm.present);
    assert(usize2ps(ret, level) == page_entry.perm.ps);
    assert(usize2write(ret, level) == page_entry.perm.write);
    assert(usize2execute_disable(ret, level) == page_entry.perm.execute_disable);
    assert(usize2user(ret, level) == page_entry.perm.user);
    assert(usize2pa(ret, level) == page_entry.addr);

    assert(ret & (0x1u64 << 5u64) as usize == 0 && ret & (0x1u64 << 6u64) as usize == 0)
        by (bit_vector)
        requires
            ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 | 0x1u64 << 2u64
                | 0x0000_ffff_ffff_f000u64)) as usize == 0,
    ;
    assert(spec_usize2page_entry_status(ret, level).is_clear());
    assert(usize2page_entry_perm(ret, level) =~= page_entry.perm);
    assert(spec_usize2page_entry(ret, level) =~= *page_entry);
    if page_entry.perm.present {
        assert(ret != 0) by (bit_vector)
            requires
                (ret & 0x1u64 as usize) != 0,
        ;
    }

    return ret;
}

/// Flushes every context on this core, all PCIDs and paging-structure caches: changing CR4.PGE does
/// that where a flush of the current PCID would leave entries under the others. `core` is the core this
/// runs on, whose set in `model` it empties.
#[verifier(external_body)]
// external_body(glue): only the hardware can attest a flush, so only this empties a core's TLB model
pub fn flush_every_context(Tracked(model): Tracked<&mut TlbModel>, core: usize)
    ensures
        final(model).len() == old(model).len(),
        final(model)[core as int] == Set::<TlbEntry>::empty(),
        forall|d: int| d != core ==> #[trigger] final(model)[d] == old(model)[d],
        final(model).tags(core as int) == Set::<usize>::empty(),
        forall|d: int| d != core ==> #[trigger] final(model).tags(d) == old(model).tags(d),
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
}

/// Points this core's CR3 at the table whose top level is at physical address `root`. Where CR4.PCIDE,
/// bit 17, is set, the write tags it with PCID `id` and sets bit 63, which keeps the entries the TLB
/// holds under every PCID; where it is clear, CR3 holds the root alone and the write flushes the
/// non-global entries. APM 2, the CR3 register in its PCID format.
/// From then on the core may hold entries under `id`, so the tag joins the core's tags in `model`.
#[verifier(external_body)]
// external_body(glue): only the hardware can attest which root a core translates through, so only this changes a BaseRegister
pub fn load_translation_root(
    Tracked(register): Tracked<&mut BaseRegister>,
    Tracked(model): Tracked<&mut TlbModel>,
    root: usize,
    id: usize,
)
    requires
        root % PAGE_SZ == 0,
        id < PCID_MAX,
    ensures
        final(register).core() == old(register).core(),
        final(register).root() == root,
        final(register).tag() == id,
        final(model).len() == old(model).len(),
        forall|d: int| #[trigger] final(model)[d] == old(model)[d],
        final(model).tags(old(register).core()) == old(model).tags(old(register).core()).insert(id),
        forall|d: int| d != old(register).core() ==> #[trigger] final(model).tags(d) == old(model).tags(d),
{
    let cr4: u64;
    unsafe {
        core::arch::asm!("mov {cr4}, cr4", cr4 = out(reg) cr4, options(nomem, nostack, preserves_flags));
    }
    let cr3 = if cr4 & (1 << 17) != 0 { (root | id) as u64 | 1 << 63 } else { root as u64 };
    unsafe {
        core::arch::asm!("mov cr3, {cr3}", cr3 = in(reg) cr3, options(nostack, preserves_flags));
    }
}

// The IOMMU's command ring: AMD-Vi's, the IOMMU of the PC this target runs on. capability/kernel.rs's
// CommandBuffers holds one ring per IOMMU, and this module says which rings the IOMMU accepts, how a
// command is encoded and how an invalidate is sent. AMD IOMMU specification 48882.

/// Bytes in one IOMMU command: a 4-bit opcode and two operands. 48882 §2.4.
pub const IOMMU_COMMAND_SIZE: usize = 16;

/// An IOMMU's MMIO registers start on a 16 KiB boundary at least. 48882 §3.2, IOMMU Base Address Low
/// Register.
pub const IOMMU_MMIO_ALIGN: usize = 16384;

/// A ring the base register can name: a length its ComLen field can say, a power of two from 256 to
/// 32768 entries. Its address need only be 4 KiB aligned, as CommandBuffers asks of every ring. 48882
/// §3.4.1, Command Buffer Base Address Register.
pub open spec fn command_ring_ok(ring: usize, len: usize) -> bool {
    len == 256 || len == 512 || len == 1024 || len == 2048 || len == 4096 || len == 8192 || len == 16384 || len == 32768
}

/// How many commands invalidate_iommu_all writes.
pub const IOMMU_INVALIDATE_COMMANDS: usize = 2;

/// Opcode of INVALIDATE_IOMMU_ALL, which empties every cache of the IOMMU. 48882 §2.4.8; the IOMMU must
/// report IASup, MMIO 0030h, for it to be legal.
pub const IOMMU_INVALIDATE_ALL: u64 = 0x08;

/// Opcode of COMPLETION_WAIT, which finishes once every older command has, and with its s bit stores its
/// 64-bit data at its address. 48882 §2.4.1.
pub const IOMMU_COMPLETION_WAIT: u64 = 0x01;

/// The command buffer tail register's offset in an IOMMU's MMIO registers. 48882 §3.4.15.
pub const IOMMU_COMMAND_TAIL: usize = 0x2008;

/// A command as the ring holds it: the first quadword, with the opcode in bits 63:60, then the second.
/// 48882 Rev 3.11, Figure 43.
pub type IommuCommand = (u64, u64);

/// INVALIDATE_IOMMU_ALL: the opcode in bits 63:60 of the first quadword and every other bit reserved,
/// so zero. 48882 Rev 3.11, Figure 51 and Table 41.
pub open spec fn invalidate_all_command_spec() -> IommuCommand {
    (IOMMU_INVALIDATE_ALL << 60u64, 0)
}

fn invalidate_all_command() -> (ret: IommuCommand)
    ensures
        ret == invalidate_all_command_spec(),
{
    (IOMMU_INVALIDATE_ALL << 60u64, 0)
}

/// COMPLETION_WAIT with s set and f and i clear: the opcode in bits 63:60 of the first quadword, the
/// store address's bits 51:3 in place, s at bit 0, and the store data as the second quadword. 48882
/// Rev 3.11, Figure 44 and Table 34.
pub open spec fn completion_wait_command_spec(address: u64, data: u64) -> IommuCommand {
    ((address & 0x000f_ffff_ffff_fff8u64) | 1u64 | (IOMMU_COMPLETION_WAIT << 60u64), data)
}

fn completion_wait_command(address: u64, data: u64) -> (ret: IommuCommand)
    ensures
        ret == completion_wait_command_spec(address, data),
{
    ((address & 0x000f_ffff_ffff_fff8u64) | 1u64 | (IOMMU_COMPLETION_WAIT << 60u64), data)
}

/// What one invalidate stored into an IOMMU's command ring: each slot it wrote, by its index from the
/// ring's start, and the command it wrote there. It begins empty and only store_command adds to it,
/// so a slot it names holds that command until the IOMMU reads it.
tracked struct QueuedCommands {
    #[cfg(verus_keep_ghost)]
    ghost ring: usize,
    #[cfg(verus_keep_ghost)]
    ghost slots: Map<int, IommuCommand>,
}

/// Stores `command` into slot `slot` of the ring at `queued.ring`, whose address is `address`.
#[verifier(external_body)]
// external_body(glue): the IOMMU reads the ring, so only this can say what one of its slots holds
fn store_command(address: usize, command: IommuCommand, Tracked(queued): Tracked<&mut QueuedCommands>, Ghost(slot): Ghost<int>)
    requires
        address == old(queued).ring + slot * IOMMU_COMMAND_SIZE,
    ensures
        final(queued).ring == old(queued).ring,
        final(queued).slots == old(queued).slots.insert(slot, command),
{
    unsafe {
        core::ptr::write_volatile(address as *mut u64, command.0);
        core::ptr::write_volatile((address as *mut u64).add(1), command.1);
    }
}

/// Hands IOMMU i the INVALIDATE_IOMMU_ALL and the COMPLETION_WAIT queued at its tail and returns once
/// the IOMMU has finished them, emptying i's set in `model`. It clears the completion word, orders
/// that and the commands before the store of `tail` into the tail register at `tail_register`, which
/// moves the tail past both, and spins until the IOMMU stores the wait's nonzero data to the word.
/// COMPLETION_WAIT finishes only once every older command has, 48882 Rev 3.11 §2.4.1, and
/// INVALIDATE_IOMMU_ALL invalidates every IOMMU TLB, §2.4.8.
#[verifier(external_body)]
// external_body(glue): only the IOMMU can attest an invalidate, so only this empties its IOTLB model
fn submit_invalidate(
    commands: &CommandBuffers,
    i: usize,
    tail_register: usize,
    tail: u64,
    completion: usize,
    Tracked(queued): Tracked<&QueuedCommands>,
    Tracked(model): Tracked<&mut IotlbModel>,
)
    requires
        i < NUM_IOMMUS,
        commands.buffers.wf(),
        commands.buffer_wf(i as int),
        tail_register == commands.buffers@[i as int].mmio + IOMMU_COMMAND_TAIL,
        tail == (commands.buffers@[i as int].tail + IOMMU_INVALIDATE_COMMANDS) % commands.buffers@[i as int].len as int * IOMMU_COMMAND_SIZE,
        completion == commands.buffers@[i as int].completion,
        queued.ring == commands.buffers@[i as int].ring,
        queued.slots.contains_key(commands.buffers@[i as int].tail as int),
        queued.slots[commands.buffers@[i as int].tail as int] == invalidate_all_command_spec(),
        queued.slots.contains_key((commands.buffers@[i as int].tail + 1) % commands.buffers@[i as int].len as int),
        queued.slots[(commands.buffers@[i as int].tail + 1) % commands.buffers@[i as int].len as int]
            == completion_wait_command_spec(completion as u64, 1),
    ensures
        final(model).len() == old(model).len(),
        final(model)[i as int] == Set::<TlbEntry>::empty(),
        forall|j: int| j != i ==> #[trigger] final(model)[j] == old(model)[j],
{
    unsafe {
        core::ptr::write_volatile(completion as *mut u64, 0);
        core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
        core::ptr::write_volatile(tail_register as *mut u64, tail);
        while core::ptr::read_volatile(completion as *const u64) == 0 {
            core::hint::spin_loop();
        }
    }
}

/// Invalidates all of IOMMU i's caches and returns once it has finished, with the tail after the
/// commands it wrote, and empties i's set in `model`: the caller holds the lock, so no table changes
/// while this runs, and once the invalidate finishes i holds nothing the tables no longer say. It
/// stores INVALIDATE_IOMMU_ALL then COMPLETION_WAIT at i's tail and submits them. Only this writes i's
/// ring, and each call waits for the IOMMU to read all it wrote, so the ring is empty on entry and two
/// commands fit in it. The kernel maps memory at its physical address, as the entries it writes
/// assume, so the completion word's address is the one the IOMMU stores to. Waiting here is not
/// waiting for a core: design/flush-without-waiting/. The wait is on the IOMMU, which finishes two
/// commands in a time the state does not set, so it is one unit: design/one-lock-bounded-steps/.
pub fn invalidate_iommu_all(commands: &CommandBuffers, i: usize, Tracked(model): Tracked<&mut IotlbModel>, Tracked(steps): Tracked<&mut Steps>) -> (ret: usize)
    requires
        i < NUM_IOMMUS,
        commands.buffers.wf(),
        commands.buffer_wf(i as int),
    ensures
        final(steps).count == old(steps).count + 1,
        ret == (commands.buffers@[i as int].tail + IOMMU_INVALIDATE_COMMANDS) % commands.buffers@[i as int].len as int,
        final(model).len() == old(model).len(),
        final(model)[i as int] == Set::<TlbEntry>::empty(),
        forall|j: int| j != i ==> #[trigger] final(model)[j] == old(model)[j],
{
    let b = *commands.buffers.get(i);
    let first = b.tail;
    let second = (b.tail + 1) % b.len;
    let next = (b.tail + IOMMU_INVALIDATE_COMMANDS) % b.len;
    let tracked mut queued = QueuedCommands { ring: b.ring, slots: Map::empty() };
    store_command(b.ring + first * IOMMU_COMMAND_SIZE, invalidate_all_command(), Tracked(&mut queued), Ghost(first as int));
    store_command(b.ring + second * IOMMU_COMMAND_SIZE, completion_wait_command(b.completion as u64, 1), Tracked(&mut queued), Ghost(second as int));
    proof {
        assert(second != first) by (nonlinear_arith)
            requires
                second == (first + 1) % b.len as int,
                first < b.len,
                b.len >= 2,
        ;
        assert(b.mmio + IOMMU_COMMAND_TAIL <= usize::MAX) by (nonlinear_arith)
            requires
                b.mmio % IOMMU_MMIO_ALIGN == 0,
                b.mmio <= usize::MAX,
        ;
    }
    submit_invalidate(commands, i, b.mmio + IOMMU_COMMAND_TAIL, (next * IOMMU_COMMAND_SIZE) as u64, b.completion, Tracked(&queued), Tracked(model));
    proof {
        steps.step();
    }
    next
}

// The trap frame and the user-return checks: what a thread record holds, what a return to user mode
// writes, and which program counters are user addresses. capability/thread.rs reads them.

/// The frame a thread record holds: the general registers the entry stubs in
/// kernel/src/arch/x86_64/interrupt/ and kernel/src/arch/x86_64/syscalls/ push, then the interrupt
/// stack frame, chapter 8.
#[repr(C, align(8))]
#[derive(Clone, Copy, Debug)]
pub struct Registers {
    pub r15: u64,
    pub r14: u64,
    pub r13: u64,
    pub r12: u64,
    pub rbp: u64,
    pub rbx: u64,
    pub r11: u64,
    pub r10: u64,
    pub r9: u64,
    pub r8: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub rax: u64,
    // Original interrupt stack frame
    pub error_code: u64,
    pub rip: u64,
    pub cs: u64,
    pub flags: u64,
    pub rsp: u64,
    pub ss: u64,
}

impl Registers {
    pub const fn zeroed() -> (ret: Self)
        ensures
            ret == zero_registers(),
    {
        Self {
            r15: 0,
            r14: 0,
            r13: 0,
            r12: 0,
            rbp: 0,
            rbx: 0,
            r11: 0,
            r10: 0,
            r9: 0,
            r8: 0,
            rcx: 0,
            rdx: 0,
            rsi: 0,
            rdi: 0,
            rax: 0,
            error_code: 0,
            rip: 0,
            cs: 0,
            flags: 0,
            rsp: 0,
            ss: 0,
        }
    }

    /// The program counter the thread returns to, rip.
    pub open spec fn spec_pc(&self) -> u64 {
        self.rip
    }

    #[verifier(when_used_as_spec(spec_pc))]
    pub fn pc(&self) -> (ret: u64)
        ensures
            ret == self.spec_pc(),
    {
        self.rip
    }

    // The syscall register table: which register of the frame carries each position of an
    // invocation, design/syscall-abi-in-registers/ under Registers. The dispatch reads and writes the
    // frame only through these.

    /// The operation number, in rax.
    pub open spec fn spec_operation_number(&self) -> u64 {
        self.rax
    }

    #[verifier(when_used_as_spec(spec_operation_number))]
    pub fn operation_number(&self) -> (ret: u64)
        ensures
            ret == self.spec_operation_number(),
    {
        self.rax
    }

    /// The slot of the invoked capability, in rdi.
    pub open spec fn spec_slot(&self) -> u64 {
        self.rdi
    }

    #[verifier(when_used_as_spec(spec_slot))]
    pub fn slot(&self) -> (ret: u64)
        ensures
            ret == self.spec_slot(),
    {
        self.rdi
    }

    /// Argument k of 1 to 5, in rsi, rdx, r8, r9 and r10.
    pub open spec fn spec_argument(&self, k: usize) -> u64 {
        if k == 1 {
            self.rsi
        } else if k == 2 {
            self.rdx
        } else if k == 3 {
            self.r8
        } else if k == 4 {
            self.r9
        } else {
            self.r10
        }
    }

    #[verifier(when_used_as_spec(spec_argument))]
    pub fn argument(&self, k: usize) -> (ret: u64)
        requires
            1 <= k <= 5,
        ensures
            ret == self.spec_argument(k),
    {
        if k == 1 {
            self.rsi
        } else if k == 2 {
            self.rdx
        } else if k == 3 {
            self.r8
        } else if k == 4 {
            self.r9
        } else {
            self.r10
        }
    }

    /// The status word, which returns in the operation number's register.
    pub open spec fn spec_status_word(&self) -> u64 {
        self.spec_operation_number()
    }

    /// Result k of 1 to 5, which returns in the register of the input at its position: result 1 in
    /// the slot's, result k in argument k - 1's.
    pub open spec fn spec_result(&self, k: usize) -> u64 {
        if k == 1 {
            self.spec_slot()
        } else {
            self.spec_argument((k - 1) as usize)
        }
    }

    /// Writes what an invocation returns over the frame it entered with: the status word and results
    /// 1 to 4, each at its position. Argument 5 returns no result, so its register keeps what the
    /// frame held.
    pub fn write_outcome(&mut self, out: Outcome)
        ensures
            final(self).spec_status_word() == out.status,
            final(self).spec_result(1) == out.result_1,
            final(self).spec_result(2) == out.result_2,
            final(self).spec_result(3) == out.result_3,
            final(self).spec_result(4) == out.result_4,
            final(self).spec_argument(5) == old(self).spec_argument(5),
    {
        self.rax = out.status;
        self.rdi = out.result_1;
        self.rsi = out.result_2;
        self.rdx = out.result_3;
        self.r8 = out.result_4;
    }
}

/// Registers that are all zero.
pub open spec fn zero_registers() -> Registers {
    Registers {
        r15: 0,
        r14: 0,
        r13: 0,
        r12: 0,
        rbp: 0,
        rbx: 0,
        r11: 0,
        r10: 0,
        r9: 0,
        r8: 0,
        rcx: 0,
        rdx: 0,
        rsi: 0,
        rdi: 0,
        rax: 0,
        error_code: 0,
        rip: 0,
        cs: 0,
        flags: 0,
        rsp: 0,
        ss: 0,
    }
}

pub fn zero_frame() -> (ret: Registers)
    ensures
        ret == zero_registers(),
{
    Registers::zeroed()
}

/// The selectors a thread returns to user mode with: the GDT's user code and data entries, 4 and 3,
/// at privilege 3. See kernel/src/arch/x86_64/gdt/.
pub const USER_CS: u64 = 0x23;
pub const USER_SS: u64 = 0x1b;

/// The flags a written frame keeps: those user mode can set itself with popf (carry, parity, adjust,
/// zero, sign, trap, direction, overflow, alignment check, ID), without nested task.
pub const USER_FLAGS: u64 = 0x24_0fd5;

/// The flags a written frame always has: interrupts enabled and the reserved bit 1.
pub const FORCED_FLAGS: u64 = 0x202;

/// The first address past user space. A frame returning to a non-canonical rip would fault in the
/// kernel's iretq, so a write refuses any rip at or past it.
pub const USER_RIP_END: u64 = 0x8000_0000_0000;

pub open spec fn user_rip(rip: u64) -> bool {
    rip < USER_RIP_END
}

pub fn is_user_rip(rip: u64) -> (ret: bool)
    ensures
        ret == user_rip(rip),
{
    rip < USER_RIP_END
}

pub fn user_frame_of(f: Registers) -> (ret: Registers)
    ensures
        ret == user_frame(f),
{
    Registers {
        r15: f.r15,
        r14: f.r14,
        r13: f.r13,
        r12: f.r12,
        rbp: f.rbp,
        rbx: f.rbx,
        r11: f.r11,
        r10: f.r10,
        r9: f.r9,
        r8: f.r8,
        rcx: f.rcx,
        rdx: f.rdx,
        rsi: f.rsi,
        rdi: f.rdi,
        rax: f.rax,
        error_code: f.error_code,
        rip: f.rip,
        cs: USER_CS,
        flags: (f.flags & USER_FLAGS) | FORCED_FLAGS,
        rsp: f.rsp,
        ss: USER_SS,
    }
}

/// A frame a controller wrote, as the thread will return to user mode with it: the selectors are
/// user mode's and the flags only those user mode could set, so the write grants no privilege. See
/// design/process-holds-capabilities/.
pub open spec fn user_frame(f: Registers) -> Registers {
    Registers {
        r15: f.r15,
        r14: f.r14,
        r13: f.r13,
        r12: f.r12,
        rbp: f.rbp,
        rbx: f.rbx,
        r11: f.r11,
        r10: f.r10,
        r9: f.r9,
        r8: f.r8,
        rcx: f.rcx,
        rdx: f.rdx,
        rsi: f.rsi,
        rdi: f.rdi,
        rax: f.rax,
        error_code: f.error_code,
        rip: f.rip,
        cs: USER_CS,
        flags: (f.flags & USER_FLAGS) | FORCED_FLAGS,
        rsp: f.rsp,
        ss: USER_SS,
    }
}

/// COM1's base port, the serial port the kernel crate's console writes. The PC's COM1 is a 16550 at this
/// port, a fact of the machine.
pub const COM1: u16 = 0x3f8;

/// The line status register, five ports above the base; bit 5, THRE, says the transmit holding
/// register is empty, or with the FIFOs on the transmit FIFO (PC16550D datasheet, National
/// Semiconductor, June 1995: the register table under A0, A1, A2, p. 11, and section 8.4).
pub const SERIAL_LINE_STATUS: u16 = 5;

pub const SERIAL_TRANSMIT_EMPTY: u8 = 1 << 5;

/// Writes one byte to COM1: waits until the line status says the transmit holding register is empty,
/// then stores the byte in it at the base port (PC16550D datasheet, p. 11 and section 8.4). The store
/// reaches the holding register while Line Control bit 7, DLAB, is clear, as machine/pc's console_init
/// leaves it. The wait is on the device, which the kernel's state does not set, so the byte is one
/// unit: design/one-lock-bounded-steps/. IN and OUT reach the I/O address space and no memory, so
/// nothing the proof models changes.
#[verifier(external_body)]
// external_body(glue): waits on COM1's line status and stores one byte in its transmit holding register through port I/O, which has no state a proof could see
pub fn serial_write_byte(byte: u8, Tracked(steps): Tracked<&mut Steps>)
    ensures
        final(steps).count == old(steps).count + 1,
{
    unsafe {
        loop {
            let status: u8;
            core::arch::asm!(
                "in al, dx",
                in("dx") COM1 + SERIAL_LINE_STATUS,
                out("al") status,
                options(nomem, nostack),
            );
            if status & SERIAL_TRANSMIT_EMPTY != 0 {
                break;
            }
        }
        core::arch::asm!("out dx, al", in("dx") COM1, in("al") byte, options(nomem, nostack));
    }
}

} // verus!
