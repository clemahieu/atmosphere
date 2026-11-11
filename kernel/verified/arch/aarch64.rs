// SPDX-License-Identifier: MIT

//! The aarch64 arch items, with the names, signatures and specs of the x86_64 module's. Each item's
//! values come from the Arm Architecture Reference Manual, and the console's from the PL011's
//! Technical Reference Manual, ARM DDI 0183, and the IOMMU's from the SMMU architecture specification
//! v3, IHI 0070. The flushes and the console write are external_body glue, counted in
//! tools/external-body-list. See design/arch-module/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::{CommandBuffers, Flushed, Translating};
#[cfg(verus_keep_ghost)]
use crate::capability::kernel::FlushTarget;
use crate::capability::operation::Outcome;
#[cfg(verus_keep_ghost)]
use crate::capability::console::PRINT_BYTES;
use crate::capability::steps::Steps;
use crate::define::PAddr;
#[cfg(verus_keep_ghost)]
use crate::define::{NUM_IOMMUS, PAGE_SZ, PCID_MAX};
use crate::pagetable::entry::{PageEntry, PageEntryPerm, PageEntryStatus};
#[cfg(verus_keep_ghost)]
use crate::util::page_ptr_util_u::*;

// The page-entry encoding: the VMSAv8-64 stage-1 descriptor for the 4K granule with TCR_EL1.T0SZ = 16,
// Arm ARM D8.3.1. The kernel's level 4 is the Arm lookup level 0 and its level 1 the lookup level 3.
// A valid word is one of two formats. A table descriptor, at levels 4 to 2 with bit 1 set, holds the
// next table's address and the hierarchical permissions every lookup below it obeys (D8.3.1.1,
// D8.4.1.2.2, D8.4.1.2.5). A block or page descriptor, a block at levels 3 and 2 with bit 1 clear and
// a page at level 1 with bit 1 set, holds the output address, its permissions and its memory
// attributes (D8.3.1.2). An invalid word, bit 0 clear, is ignored by the walker in every other bit
// (D8.3.1.3), so the encoder keeps the abstract entry there in the same bits as a valid word's.
// Several of the hardware's bits mean what the abstract entry means when clear (bit 1, AP[2],
// APTable): the decoders read them against bit 0, so a valid word reads them inverted and the zero
// word is the empty entry. A writable leaf is marked DBM, and AP[2] in a word so marked is the dirty
// state, clear once the leaf was written (D8.5.2). The user bits, AP[1] and APTable[0], govern EL0's
// reads and writes only, so the abstract entry's user bit is also written in the execute-never bits:
// an entry that is not user removes execution at EL0, as x86_64's U/S does, and its execute_disable
// is the EL1 bit, PXN or PXNTable; a user leaf's is the EL0 bit, UXN, and it always carries PXN
// (D8.4.1.2.3, D8.4.1.2.5, Table D8-65). Its output address sits where x86_64's does, so the address
// masks are the same.

/// Valid descriptor, bit 0.
pub const DESC_VALID: u64 = 0x1;

/// Bit 1: a table descriptor at levels 4 to 2, a page descriptor at level 1, and a block descriptor at
/// levels 3 and 2 when clear (D8.3.1.1, D8.3.1.2). At level 1 a valid word with it clear is reserved
/// and translates as invalid.
pub const DESC_TYPE: u64 = 0x2;

/// AP[1], bit 6 of a block or page descriptor: EL0 may read, and write if AP[2] allows (D8.3.1.2,
/// D8.4.1.2.1).
pub const DESC_AP_EL0: u64 = 0x40;

/// AP[2], bit 7 of a block or page descriptor: read-only at every exception level. In a descriptor
/// whose DBM is set it is the dirty state instead: set while the leaf is clean (D8.5.2.1).
pub const DESC_AP_RO: u64 = 0x80;

/// AF, bit 10 of a block or page descriptor: the access flag (D8.5.1). In a table descriptor the bit
/// is IGNORED unless hardware management of the table descriptor's access flag is enabled, which the
/// kernel does not enable, so the walker sets it only in a leaf.
pub const DESC_AF: u64 = 0x400;

/// DBM, bit 51 of a block or page descriptor: the dirty bit modifier (D8.3.1.2). With AP[2] set the
/// descriptor is writable-clean, and a write through it clears AP[2], which makes it writable-dirty
/// (D8.5.2.1). In a table descriptor the bit is IGNORED (D8.3.1.1).
pub const DESC_DBM: u64 = 0x0008_0000_0000_0000;

/// The memory attributes the encoder writes in every valid leaf and the decoders ignore: AttrIndx[2:0]
/// = 0, bits 4:2, which MAIR_EL1 attribute 0 makes Normal write-back memory (D8.6.1); SH[1:0] = 0b11,
/// bits 9:8, Inner Shareable (D8.6.2); and nG, bit 11, so the translation is cached under the current
/// ASID only (D8.3.1.2), as x86_64's leaves are never global.
pub const DESC_LEAF_ATTRS: u64 = 0xb00;

/// UXN, bit 54 of a block or page descriptor: no execution at EL0 (D8.4.1.2.3).
pub const DESC_UXN: u64 = 0x0040_0000_0000_0000;

/// PXN, bit 53 of a block or page descriptor: no execution at EL1 (D8.4.1.2.3).
pub const DESC_PXN: u64 = 0x0020_0000_0000_0000;

/// UXNTable, bit 60 of a table descriptor: every leaf below it is UXN (D8.3.1.1, D8.4.1.2.5).
pub const TABLE_UXN: u64 = 0x1000_0000_0000_0000;

/// PXNTable, bit 59 of a table descriptor: every leaf below it is PXN (D8.3.1.1, D8.4.1.2.5).
pub const TABLE_PXN: u64 = 0x0800_0000_0000_0000;

/// APTable[0], bit 61 of a table descriptor: no EL0 access below it (D8.4.1.2.2, Table D8-64).
pub const TABLE_AP_NO_EL0: u64 = 0x2000_0000_0000_0000;

/// APTable[1], bit 62 of a table descriptor: no write below it.
pub const TABLE_AP_RO: u64 = 0x4000_0000_0000_0000;

/// The physical address of a 4K page or of the next table, bits 47:12.
pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

/// Whether this target maintains the accessed bit: always. The walker sets AF where TCR_EL1.HA is set
/// (D8.5.1.2); a leaf whose AF is clear faults on its first access otherwise (D8.5.1.1), so where
/// ID_AA64MMFR1_EL1.HAFDBS says the walker cannot, the kernel's access-flag fault sets it. Either way
/// AF says the leaf was used since the kernel wrote it.
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

/// Whether this target maintains the dirty bit: always. The encoder writes a writable leaf as DBM with
/// AP[2] set, and the walker clears AP[2] on the first write through it where TCR_EL1.HD is set
/// (D8.5.2.1). Where ID_AA64MMFR1_EL1.HAFDBS says the walker cannot, the dirty state is software's to
/// keep (D8.5.2): the write takes a permission fault on AP[2] (D8.4.1.2.1) and the kernel's handler
/// clears AP[2] in a leaf whose DBM is set. Either way DBM with AP[2] clear says the leaf was written
/// since the kernel wrote it or last cleared its status. See design/arch-module/.
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

// The decoders and the encoder: a word of a table at a level, in the kernel's numbering (4 for a root,
// 1 for a table of 4K leaves), against the abstract PageEntry, PageEntryPerm and PageEntryStatus.
// Shared code reaches the bits only through these specs and lemmas. See design/arch-module/.

pub open spec fn usize2present(v: usize, level: usize) -> bool {
    (v & DESC_VALID as usize) != 0
}

/// A block, or at level 4 and level 1 a word the walker refuses: bit 1 clear in a valid word. An
/// invalid word keeps it set.
pub open spec fn usize2ps(v: usize, level: usize) -> bool {
    ((v & DESC_TYPE as usize) != 0) != usize2present(v, level)
}

/// Whether the word is in the table descriptor's format, which places the permissions in the
/// hierarchical attributes: a table at levels 4 to 2.
pub open spec fn usize2table(v: usize, level: usize) -> bool {
    level != 1 && !usize2ps(v, level)
}

/// Writable: in a table descriptor, APTable[1] clear in a valid word and set in an invalid one. In a
/// block or page descriptor, DBM set, whose AP[2] is the dirty state, or else AP[2] clear in a valid
/// word and set in an invalid one.
pub open spec fn usize2write(v: usize, level: usize) -> bool {
    if usize2table(v, level) {
        ((v & TABLE_AP_RO as usize) != 0) != usize2present(v, level)
    } else {
        (v & DESC_DBM as usize) != 0 || ((v & DESC_AP_RO as usize) != 0) != usize2present(v, level)
    }
}

/// Not executable by whoever the entry is for. A table descriptor binds both exception levels below
/// it, as x86_64's NX in a table entry does, so it is PXNTable, beside which the encoder writes
/// UXNTable. In a block or page descriptor it is UXN where the entry is user, and PXN where it is
/// not: the other bit of the two is always set there, so it says nothing.
pub open spec fn usize2execute_disable(v: usize, level: usize) -> bool {
    if usize2table(v, level) {
        (v & TABLE_PXN as usize) != 0
    } else if usize2user(v, level) {
        (v & DESC_UXN as usize) != 0
    } else {
        (v & DESC_PXN as usize) != 0
    }
}

/// User-accessible: APTable[0] clear in a valid word and set in an invalid one, or AP[1] set.
pub open spec fn usize2user(v: usize, level: usize) -> bool {
    if usize2table(v, level) {
        ((v & TABLE_AP_NO_EL0 as usize) != 0) != usize2present(v, level)
    } else {
        (v & DESC_AP_EL0 as usize) != 0
    }
}

/// Whether the word removes execution at EL0 from what it maps: UXN in a block or page descriptor,
/// and UXNTable in a table descriptor, which every leaf below it obeys (D8.4.1.2.3, D8.4.1.2.5). The
/// user bits do not: with AP[1] clear and UXN clear EL0 still executes the page, and APTable[0]
/// removes only EL0's reads and writes (Tables D8-64 and D8-65).
pub open spec fn usize2el0_execute_never(v: usize, level: usize) -> bool {
    if usize2table(v, level) {
        (v & TABLE_UXN as usize) != 0
    } else {
        (v & DESC_UXN as usize) != 0
    }
}

/// Whether the word removes execution at EL1 from what it maps: PXN in a block or page descriptor,
/// and PXNTable in a table descriptor.
pub open spec fn usize2el1_execute_never(v: usize, level: usize) -> bool {
    if usize2table(v, level) {
        (v & TABLE_PXN as usize) != 0
    } else {
        (v & DESC_PXN as usize) != 0
    }
}

pub open spec fn usize2accessed(v: usize, level: usize) -> bool {
    (v & DESC_AF as usize) != 0
}

/// Dirty: DBM with AP[2] clear, the writable-dirty state. The encoder sets DBM in no table descriptor,
/// so one is never dirty.
pub open spec fn usize2dirty(v: usize, level: usize) -> bool {
    (v & DESC_DBM as usize) != 0 && (v & DESC_AP_RO as usize) == 0
}

/// The walker's accessed and dirty state of a word, apart from the entry it decodes to.
pub open spec fn spec_usize2page_entry_status(v: usize, level: usize) -> PageEntryStatus {
    PageEntryStatus { accessed: usize2accessed(v, level), dirty: usize2dirty(v, level) }
}

#[verifier(when_used_as_spec(spec_usize2page_entry_status))]
pub fn usize2page_entry_status(v: usize, level: usize) -> (ret: PageEntryStatus)
    ensures
        ret == spec_usize2page_entry_status(v, level),
{
    PageEntryStatus {
        accessed: (v & DESC_AF as usize) != 0,
        dirty: (v & DESC_DBM as usize) != 0 && (v & DESC_AP_RO as usize) == 0,
    }
}

/// The word with its access flag clear and, where DBM is set, AP[2] set: accessed and dirty clear.
pub open spec fn spec_without_status(v: usize) -> usize {
    if (v & DESC_DBM as usize) != 0 {
        (v & !(DESC_AF as usize)) | DESC_AP_RO as usize
    } else {
        v & !(DESC_AF as usize)
    }
}

/// What a clear of the status bits writes in place of the word it read.
#[verifier(when_used_as_spec(spec_without_status))]
pub fn without_status(v: usize) -> (ret: usize)
    ensures
        ret == spec_without_status(v),
{
    let cleared = v & !(DESC_AF as usize);
    if (v & DESC_DBM as usize) != 0 {
        cleared | DESC_AP_RO as usize
    } else {
        cleared
    }
}

/// Two words that differ only in the access flag, and in AP[2] where DBM is set, decode to the same
/// entry, so whatever the walker sets or clears there leaves every table's view as it was: a word
/// with DBM set is writable whatever its AP[2].
pub proof fn lemma_status_outside_entry(v: usize, w: usize, level: usize)
    requires
        spec_without_status(v) == spec_without_status(w),
    ensures
        spec_usize2page_entry(v, level) == spec_usize2page_entry(w, level),
{
    assert(v & 0x0000_ffff_ffff_f000usize == w & 0x0000_ffff_ffff_f000usize
        && (v & 0x1usize != 0) == (w & 0x1usize != 0)
        && (v & 0x2usize != 0) == (w & 0x2usize != 0)
        && (v & 0x40usize != 0) == (w & 0x40usize != 0)
        && (v & 0x0008_0000_0000_0000usize != 0) == (w & 0x0008_0000_0000_0000usize != 0)
        && (v & 0x0008_0000_0000_0000usize == 0 ==> (v & 0x80usize != 0) == (w & 0x80usize != 0))
        && (v & 0x0020_0000_0000_0000usize != 0) == (w & 0x0020_0000_0000_0000usize != 0)
        && (v & 0x0040_0000_0000_0000usize != 0) == (w & 0x0040_0000_0000_0000usize != 0)
        && (v & 0x0800_0000_0000_0000usize != 0) == (w & 0x0800_0000_0000_0000usize != 0)
        && (v & 0x2000_0000_0000_0000usize != 0) == (w & 0x2000_0000_0000_0000usize != 0)
        && (v & 0x4000_0000_0000_0000usize != 0) == (w & 0x4000_0000_0000_0000usize != 0))
        by (bit_vector)
        requires
            (if v & 0x0008_0000_0000_0000usize != 0 {
                (v & !0x400usize) | 0x80usize
            } else {
                v & !0x400usize
            }) == (if w & 0x0008_0000_0000_0000usize != 0 {
                (w & !0x400usize) | 0x80usize
            } else {
                w & !0x400usize
            }),
    ;
}

/// Clearing the status bits clears them and keeps the rest: clearing again changes nothing.
pub proof fn lemma_without_status(v: usize, level: usize)
    ensures
        spec_without_status(spec_without_status(v)) == spec_without_status(v),
        spec_usize2page_entry_status(spec_without_status(v), level).is_clear(),
{
    let c = spec_without_status(v);
    assert(c == (if c & 0x0008_0000_0000_0000usize != 0 {
        (c & !0x400usize) | 0x80usize
    } else {
        c & !0x400usize
    })) by (bit_vector)
        requires
            c == (if v & 0x0008_0000_0000_0000usize != 0 {
                (v & !0x400usize) | 0x80usize
            } else {
                v & !0x400usize
            }),
    ;
    assert(c & 0x400usize == 0 && (c & 0x0008_0000_0000_0000usize != 0 ==> c & 0x80usize != 0))
        by (bit_vector)
        requires
            c == (if v & 0x0008_0000_0000_0000usize != 0 {
                (v & !0x400usize) | 0x80usize
            } else {
                v & !0x400usize
            }),
    ;
}

/// The zero word is the empty entry with its status clear, at every level.
pub proof fn zero_leads_is_empty_page_entry(level: usize)
    ensures
        spec_usize2page_entry(0, level).is_empty(),
        spec_usize2page_entry_status(0, level).is_clear(),
        spec_without_status(0) == 0,
{
    assert(0usize & 0x0000_ffff_ffff_f000usize == 0
        && 0usize & 0x1usize == 0
        && 0usize & 0x2usize == 0
        && 0usize & 0x40usize == 0
        && 0usize & 0x80usize == 0
        && 0usize & 0x400usize == 0
        && 0usize & 0x0020_0000_0000_0000usize == 0
        && 0usize & 0x0040_0000_0000_0000usize == 0
        && 0usize & 0x0800_0000_0000_0000usize == 0
        && 0usize & 0x2000_0000_0000_0000usize == 0
        && 0usize & 0x4000_0000_0000_0000usize == 0
        && 0usize & 0x0008_0000_0000_0000usize == 0
        && 0usize & !0x400usize == 0) by (bit_vector);
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
    let present = (v & DESC_VALID as usize) != 0;
    let ps = ((v & DESC_TYPE as usize) != 0) != present;
    if level != 1 && !ps {
        PageEntryPerm {
            present,
            ps,
            write: ((v & TABLE_AP_RO as usize) != 0) != present,
            execute_disable: (v & TABLE_PXN as usize) != 0,
            user: ((v & TABLE_AP_NO_EL0 as usize) != 0) != present,
        }
    } else {
        let user = (v & DESC_AP_EL0 as usize) != 0;
        PageEntryPerm {
            present,
            ps,
            write: (v & DESC_DBM as usize) != 0 || ((v & DESC_AP_RO as usize) != 0) != present,
            execute_disable: if user {
                (v & DESC_UXN as usize) != 0
            } else {
                (v & DESC_PXN as usize) != 0
            },
            user,
        }
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

/// The word that holds an entry in a table at `level`, with its status clear. A valid leaf is written
/// read-only in AP[2], and DBM beside it where the entry is writable: the writable-clean state. An
/// invalid leaf keeps write in AP[2] alone. A valid leaf also gets DESC_LEAF_ATTRS, which the decoders
/// ignore. The last two ensures are what the hardware does with the word, which the round trip
/// cannot say: EL0 executes nothing that an entry without user maps, and EL1 executes no user leaf.
pub fn page_entry2usize(page_entry: &PageEntry, level: usize) -> (ret: usize)
    requires
        mem_valid(page_entry.addr),
    ensures
        spec_usize2page_entry(ret, level) == *page_entry,
        spec_usize2page_entry_status(ret, level).is_clear(),
        page_entry.perm.present ==> ret != 0,
        usize2el0_execute_never(ret, level) == (page_entry.perm.execute_disable
            || !page_entry.perm.user),
        usize2el1_execute_never(ret, level) == (page_entry.perm.execute_disable
            || (page_entry.perm.user && (level == 1 || page_entry.perm.ps))),
{
    let addr = page_entry.addr;
    let present = page_entry.perm.present;
    let ps = page_entry.perm.ps;
    let leaf = level == 1 || ps;
    let write = page_entry.perm.write;
    let p: usize = if present { DESC_VALID as usize } else { 0 };
    let t: usize = if ps != present { DESC_TYPE as usize } else { 0 };
    let lw: usize = if leaf && (present || write) { DESC_AP_RO as usize } else { 0 };
    let ld: usize = if leaf && present && write { DESC_DBM as usize } else { 0 };
    let tw: usize = if !leaf && write != present { TABLE_AP_RO as usize } else { 0 };
    let user = page_entry.perm.user;
    let xd = page_entry.perm.execute_disable;
    let lu: usize = if leaf && user { DESC_AP_EL0 as usize } else { 0 };
    let tu: usize = if !leaf && user != present { TABLE_AP_NO_EL0 as usize } else { 0 };
    let lux: usize = if leaf && (xd || !user) { DESC_UXN as usize } else { 0 };
    let lpx: usize = if leaf && (xd || user) { DESC_PXN as usize } else { 0 };
    let tux: usize = if !leaf && (xd || !user) { TABLE_UXN as usize } else { 0 };
    let tpx: usize = if !leaf && xd { TABLE_PXN as usize } else { 0 };
    let la: usize = if leaf && present { DESC_LEAF_ATTRS as usize } else { 0 };
    let ret = addr | p | t | lw | ld | tw | lu | tu | lux | lpx | tux | tpx | la;
    assert(ret & 0x1usize == p
        && ret & 0x2usize == t
        && ret & 0x40usize == lu
        && ret & 0x80usize == lw
        && ret & 0x0008_0000_0000_0000usize == ld
        && ret & 0x400usize == 0
        && ret & 0x0040_0000_0000_0000usize == lux
        && ret & 0x0020_0000_0000_0000usize == lpx
        && ret & 0x1000_0000_0000_0000usize == tux
        && ret & 0x0800_0000_0000_0000usize == tpx
        && ret & 0x2000_0000_0000_0000usize == tu
        && ret & 0x4000_0000_0000_0000usize == tw
        && ret & 0x0000_ffff_ffff_f000usize == addr
        && (p == 1 ==> ret != 0)) by (bit_vector)
        requires
            ret == addr | p | t | lw | ld | tw | lu | tu | lux | lpx | tux | tpx | la,
            addr & (!0x0000_ffff_ffff_f000u64) as usize == 0,
            p == 0 || p == 1,
            t == 0 || t == 2,
            lw == 0 || lw == 0x80,
            ld == 0 || ld == 0x0008_0000_0000_0000usize,
            tw == 0 || tw == 0x4000_0000_0000_0000usize,
            lu == 0 || lu == 0x40,
            tu == 0 || tu == 0x2000_0000_0000_0000usize,
            lux == 0 || lux == 0x0040_0000_0000_0000usize,
            lpx == 0 || lpx == 0x0020_0000_0000_0000usize,
            tux == 0 || tux == 0x1000_0000_0000_0000usize,
            tpx == 0 || tpx == 0x0800_0000_0000_0000usize,
            la == 0 || la == 0xb00,
    ;
    assert(spec_usize2page_entry_perm(ret, level) =~= page_entry.perm);
    assert(spec_usize2page_entry(ret, level) =~= *page_entry);
    ret
}

/// Flushes every context on this core: TLBI VMALLE1 drops the stage-1 entries of the EL1&0 regime
/// with any ASID, global ones too, from every level of the walk, and only on this core, which is the
/// per-core flush of design/flush-without-waiting/ (Arm ARM C5.5.77). The DSB before it orders this
/// core's table writes ahead of it, and the DSB and ISB after it complete it for this core's own
/// translations (D8.17.8).
#[verifier(external_body)]
// external_body(glue): only the hardware can attest a flush, so only this makes the token
pub fn flush_every_context(core: usize, epoch: usize) -> (ret: Tracked<Flushed>)
    ensures
        ret@.target == FlushTarget::Core(core as int),
        ret@.epoch == epoch as int,
{
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1", "dsb ish", "isb", options(nostack, preserves_flags));
    }
    Tracked::assume_new()
}

/// Points this core's TTBR0_EL1 at the table whose top level is at physical address `root`, as ASID
/// `id` in bits 63:48: one write changes the table and the id together and flushes nothing, and the
/// instructions after the ISB translate through the new table. Arm ARM D24.2.208, B2.6.1.
#[verifier(external_body)]
// external_body(glue): only the hardware can attest which root a core translates through, so only this makes the token
pub fn load_translation_root(core: usize, root: usize, id: usize) -> (ret: Tracked<Translating>)
    requires
        root % PAGE_SZ == 0,
        id < PCID_MAX,
    ensures
        ret@.core == core as int,
        ret@.root == root,
        ret@.tag == id,
{
    let base = (id as u64) << 48 | root as u64;
    unsafe {
        core::arch::asm!("msr TTBR0_EL1, {base}", "isb", base = in(reg) base, options(nostack, preserves_flags));
    }
    Tracked::assume_new()
}

// The IOMMU's command ring: the command queue of an SMMUv3, the IOMMU QEMU virt offers. capability/
// kernel.rs's CommandBuffers holds one ring per IOMMU, and this module says which rings the SMMU accepts,
// how a command is encoded and how an invalidate is sent. Arm IHI 0070 H.a, cited as SMMU; the machine
// glue's driver, machine/virt/src/iommu.rs, gives the SMMU its queue at boot with the same encodings.

/// Bytes in one SMMU command: two 64-bit words, the opcode in bits 7:0 of the first. SMMU 4.1.
pub const IOMMU_COMMAND_SIZE: usize = 16;

/// An SMMU's registers are two 64 KiB pages, starting on a 64 KiB boundary. SMMU 6.1.
pub const IOMMU_MMIO_ALIGN: usize = 65536;

/// A queue SMMU_CMDQ_BASE can name: a power of two from 256 to 32768 entries, which its LOG2SIZE
/// field says, at an address aligned to its size in bytes (SMMU 6.3.26). The SMMU takes up to
/// 2^IDR1.CMDQS entries, which the boot that gives it the queue checks.
pub open spec fn command_ring_ok(ring: usize, len: usize) -> bool {
    &&& len == 256 || len == 512 || len == 1024 || len == 2048 || len == 4096 || len == 8192 || len == 16384 || len == 32768
    &&& ring % (len * IOMMU_COMMAND_SIZE) as usize == 0
}

/// How many commands invalidate_iommu_all writes.
pub const IOMMU_INVALIDATE_COMMANDS: usize = 3;

/// CMD_CFGI_ALL: opcode 0x04 with Range, bits 68:64, 31, which drops every STE and CD the SMMU
/// caches. SMMU 4.3.9.
pub const SMMU_CFGI_ALL: [u64; 2] = [0x04, 31];

/// CMD_TLBI_NSNH_ALL, opcode 0x30, which drops every non-secure TLB entry outside the EL2 regime, of
/// either stage and with any ASID or VMID, from every level of the walk. SMMU 4.4.4.1.
pub const SMMU_TLBI_NSNH_ALL: [u64; 2] = [0x30, 0];

/// CMD_SYNC, opcode 0x46, with CS, bits 13:12, 0b00: it completes once every command before it has,
/// and the queue's consumer index passing it shows that. SMMU 4.7.3.
pub const SMMU_SYNC: [u64; 2] = [0x46, 0];

/// SMMU_CMDQ_PROD and SMMU_CMDQ_CONS, by their offset from the SMMU's base. SMMU 6.2, Table 6-1. In
/// each, the queue's index is bits LOG2SIZE-1:0 and its wrap bit is bit LOG2SIZE (SMMU 3.5.1); CONS
/// also holds an error code above them.
pub const SMMU_CMDQ_PROD: usize = 0x98;
pub const SMMU_CMDQ_CONS: usize = 0x9c;

/// Invalidates all of SMMU i's caches and returns once it has finished, with the tail after the
/// commands it wrote. It writes CMD_CFGI_ALL, CMD_TLBI_NSNH_ALL and CMD_SYNC at i's tail, moves the
/// producer index past all three and spins until the consumer index reaches it, which it does only once
/// CMD_SYNC has completed. The SMMU is never handed the EL2 regime, so the TLB invalidation leaves it.
/// The completion word is not used: CMD_SYNC signals through the consumer index. Only this writes i's
/// queue, and each call waits for the SMMU to consume all it wrote, so the queue is empty on entry and
/// three commands fit in it. The producer register keeps the wrap bit the ring's tail leaves out, so
/// this reads it back. The SMMU reads the queue coherently, as boot asks of it (machine/virt's CR1), so
/// a DSB orders the commands, and every table write before them, ahead of the producer's store. Each
/// register access is one load or store with no writeback, which a hypervisor emulating the SMMU can
/// decode (Arm ARM D24.2.45, ISV). Waiting here is not waiting for a core: design/flush-without-waiting/.
/// The wait is on the SMMU, which finishes three commands in a time the state does not set, so it is one
/// unit: design/one-lock-bounded-steps/.
#[verifier(external_body)]
// external_body(glue): only the SMMU can attest an invalidate, so only this makes its token
pub fn invalidate_iommu_all(commands: &CommandBuffers, i: usize, epoch: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: (usize, Tracked<Flushed>))
    requires
        i < NUM_IOMMUS,
        commands.buffers.wf(),
        commands.buffer_wf(i as int),
    ensures
        final(steps).count == old(steps).count + 1,
        ret.0 == (commands.buffers@[i as int].tail + IOMMU_INVALIDATE_COMMANDS) % commands.buffers@[i as int].len as int,
        ret.1@.target == FlushTarget::Iommu(i as int),
        ret.1@.epoch == epoch as int,
{
    let b = *commands.buffers.get(i);
    // The index and the wrap bit of a place in the queue.
    let place_mask = (2 * b.len - 1) as u32;
    let load = |register: usize| -> u32 {
        let value: u32;
        unsafe {
            core::arch::asm!(
                "ldr {value:w}, [{register}]",
                register = in(reg) b.mmio + register,
                value = out(reg) value,
                options(nostack, readonly, preserves_flags),
            );
        }
        value
    };
    let mut place = load(SMMU_CMDQ_PROD) & place_mask;
    assert!(place as usize & (b.len - 1) == b.tail, "the SMMU's producer index is the ring's tail");
    for command in [SMMU_CFGI_ALL, SMMU_TLBI_NSNH_ALL, SMMU_SYNC] {
        let slot = (b.ring + (place as usize & (b.len - 1)) * IOMMU_COMMAND_SIZE) as *mut u64;
        unsafe {
            core::ptr::write_volatile(slot, command[0]);
            core::ptr::write_volatile(slot.add(1), command[1]);
        }
        place = (place + 1) & place_mask;
    }
    unsafe {
        core::arch::asm!(
            "dsb st",
            "str {place:w}, [{register}]",
            register = in(reg) b.mmio + SMMU_CMDQ_PROD,
            place = in(reg) place,
            options(nostack, preserves_flags),
        );
    }
    while load(SMMU_CMDQ_CONS) & place_mask != place {
        core::hint::spin_loop();
    }
    ((b.tail + IOMMU_INVALIDATE_COMMANDS) % b.len, Tracked::assume_new())
}

// The trap frame and the user-return checks: what a thread record holds, what a return to user mode
// writes, and which program counters are user addresses. capability/thread.rs reads them.

/// The frame a thread record holds: the general registers x0 to x30, then the EL0 stack pointer and
/// the exception return state, ELR_EL1 and SPSR_EL1.
#[repr(C, align(8))]
#[derive(Clone, Copy, Debug)]
pub struct Registers {
    pub x0: u64,
    pub x1: u64,
    pub x2: u64,
    pub x3: u64,
    pub x4: u64,
    pub x5: u64,
    pub x6: u64,
    pub x7: u64,
    pub x8: u64,
    pub x9: u64,
    pub x10: u64,
    pub x11: u64,
    pub x12: u64,
    pub x13: u64,
    pub x14: u64,
    pub x15: u64,
    pub x16: u64,
    pub x17: u64,
    pub x18: u64,
    pub x19: u64,
    pub x20: u64,
    pub x21: u64,
    pub x22: u64,
    pub x23: u64,
    pub x24: u64,
    pub x25: u64,
    pub x26: u64,
    pub x27: u64,
    pub x28: u64,
    pub x29: u64,
    pub x30: u64,
    pub sp_el0: u64,
    pub elr_el1: u64,
    pub spsr_el1: u64,
}

impl Registers {
    pub const fn zeroed() -> (ret: Self)
        ensures
            ret == zero_registers(),
    {
        Self {
            x0: 0,
            x1: 0,
            x2: 0,
            x3: 0,
            x4: 0,
            x5: 0,
            x6: 0,
            x7: 0,
            x8: 0,
            x9: 0,
            x10: 0,
            x11: 0,
            x12: 0,
            x13: 0,
            x14: 0,
            x15: 0,
            x16: 0,
            x17: 0,
            x18: 0,
            x19: 0,
            x20: 0,
            x21: 0,
            x22: 0,
            x23: 0,
            x24: 0,
            x25: 0,
            x26: 0,
            x27: 0,
            x28: 0,
            x29: 0,
            x30: 0,
            sp_el0: 0,
            elr_el1: 0,
            spsr_el1: 0,
        }
    }

    pub fn new(input: &Registers) -> (ret: Self)
        ensures
            ret =~= *input,
    {
        *input
    }

    pub fn set_self(&mut self, src: &Registers)
        ensures
            *final(self) == *src,
    {
        *self = *src;
    }

    /// The program counter the thread returns to, ELR_EL1.
    pub open spec fn spec_pc(&self) -> u64 {
        self.elr_el1
    }

    #[verifier(when_used_as_spec(spec_pc))]
    pub fn pc(&self) -> (ret: u64)
        ensures
            ret == self.spec_pc(),
    {
        self.elr_el1
    }

    // The syscall register table: which register of the frame carries each position of an
    // invocation, design/syscall-abi-in-registers/ under Registers. The dispatch reads and writes the
    // frame only through these.

    /// The operation number, in x8.
    pub open spec fn spec_operation_number(&self) -> u64 {
        self.x8
    }

    #[verifier(when_used_as_spec(spec_operation_number))]
    pub fn operation_number(&self) -> (ret: u64)
        ensures
            ret == self.spec_operation_number(),
    {
        self.x8
    }

    /// The slot of the invoked capability, in x0.
    pub open spec fn spec_slot(&self) -> u64 {
        self.x0
    }

    #[verifier(when_used_as_spec(spec_slot))]
    pub fn slot(&self) -> (ret: u64)
        ensures
            ret == self.spec_slot(),
    {
        self.x0
    }

    /// Argument k of 1 to 5, in x1 to x5.
    pub open spec fn spec_argument(&self, k: usize) -> u64 {
        if k == 1 {
            self.x1
        } else if k == 2 {
            self.x2
        } else if k == 3 {
            self.x3
        } else if k == 4 {
            self.x4
        } else {
            self.x5
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
            self.x1
        } else if k == 2 {
            self.x2
        } else if k == 3 {
            self.x3
        } else if k == 4 {
            self.x4
        } else {
            self.x5
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
        self.x8 = out.status;
        self.x0 = out.result_1;
        self.x1 = out.result_2;
        self.x2 = out.result_3;
        self.x3 = out.result_4;
    }
}

/// Registers that are all zero.
pub open spec fn zero_registers() -> Registers {
    Registers {
        x0: 0,
        x1: 0,
        x2: 0,
        x3: 0,
        x4: 0,
        x5: 0,
        x6: 0,
        x7: 0,
        x8: 0,
        x9: 0,
        x10: 0,
        x11: 0,
        x12: 0,
        x13: 0,
        x14: 0,
        x15: 0,
        x16: 0,
        x17: 0,
        x18: 0,
        x19: 0,
        x20: 0,
        x21: 0,
        x22: 0,
        x23: 0,
        x24: 0,
        x25: 0,
        x26: 0,
        x27: 0,
        x28: 0,
        x29: 0,
        x30: 0,
        sp_el0: 0,
        elr_el1: 0,
        spsr_el1: 0,
    }
}

pub fn zero_frame() -> (ret: Registers)
    ensures
        ret == zero_registers(),
{
    Registers::zeroed()
}

/// What a written frame keeps of SPSR_EL1: the condition flags N, Z, C and V, bits 31 to 28, which
/// user mode sets itself with MSR NZCV. Arm ARM C5.2.21, the layout for M[4] = 0.
pub const USER_SPSR_KEPT: u64 = 0xf000_0000;

/// The mode a written frame always returns to: M[4] = 0, AArch64 state, and M[3:0] = 0b0000, EL0.
/// Every other bit is clear: D, A, I and F (bits 9 to 6) leave debug, SError, IRQ and FIQ unmasked,
/// and with IL and SS (bits 20 and 21) clear the exception return is legal and not single-stepped.
/// Arm ARM C5.2.21 and D1.4.4.
pub const USER_SPSR_MODE: u64 = 0b0_0000;

/// The first address past user space: 2^48, the top of TTBR0_EL1's range with T0SZ = 16. A write
/// refuses any program counter at or past it.
pub const USER_RIP_END: u64 = 0x1_0000_0000_0000;

/// Whether a program counter is a user address.
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
    Registers { spsr_el1: (f.spsr_el1 & USER_SPSR_KEPT) | USER_SPSR_MODE, ..f }
}

/// A frame a controller wrote, as the thread will return to user mode with it: SPSR_EL1 returns to
/// EL0 with only the condition flags user mode could set, so the write grants no privilege. See
/// design/process-holds-capabilities/.
pub open spec fn user_frame(f: Registers) -> Registers {
    Registers { spsr_el1: (f.spsr_el1 & USER_SPSR_KEPT) | USER_SPSR_MODE, ..f }
}

/// A written frame returns to EL0 in AArch64 state with debug, SError, IRQ and FIQ unmasked, and
/// carries no saved process state but the condition flags; the rest of it is the frame as written.
pub proof fn lemma_user_frame_at_el0(f: Registers)
    ensures
        user_frame(f).spsr_el1 & 0x1f == 0,
        user_frame(f).spsr_el1 & 0x3c0 == 0,
        user_frame(f).spsr_el1 & !0xf000_0000u64 == 0,
        user_frame(f).spsr_el1 & 0xf000_0000u64 == f.spsr_el1 & 0xf000_0000u64,
        user_frame(f).elr_el1 == f.elr_el1,
        user_frame(f).sp_el0 == f.sp_el0,
        user_frame(f).x0 == f.x0,
        user_frame(f).x30 == f.x30,
{
    let s = f.spsr_el1;
    assert(((s & 0xf000_0000u64) | 0u64) & 0x1f == 0) by (bit_vector);
    assert(((s & 0xf000_0000u64) | 0u64) & 0x3c0 == 0) by (bit_vector);
    assert(((s & 0xf000_0000u64) | 0u64) & !0xf000_0000u64 == 0) by (bit_vector);
    assert(((s & 0xf000_0000u64) | 0u64) & 0xf000_0000u64 == s & 0xf000_0000u64) by (bit_vector);
}

/// The last byte below 2^48 is a user address and 2^48 is not.
pub proof fn lemma_user_rip_bound()
    ensures
        user_rip(0xffff_ffff_ffff),
        !user_rip(0x1_0000_0000_0000),
{
}

/// The PL011 the console writes, at the address QEMU virt's device tree gives it: node pl011@9000000,
/// one page, the machine's stdout-path. The kernel reads and writes the device at this address, so the
/// address space it runs in maps the page there.
pub const PL011: usize = 0x0900_0000;

/// UARTDR, the data register: a write pushes the byte onto the transmit FIFO, or into the transmit
/// holding register while the FIFO is disabled (DDI 0183 3.3.1).
pub const PL011_DATA: usize = 0x000;

/// UARTFR, the flag register; bit 5, TXFF, says the transmit FIFO or holding register is full (DDI 0183
/// 3.3.3).
pub const PL011_FLAG: usize = 0x018;

pub const PL011_TRANSMIT_FULL: u32 = 1 << 5;

/// Writes to the PL011 the bytes words a to e carry: each word's eight bytes from its lowest, a's
/// first, up to the first zero byte. Each byte waits while the transmitter is full, which the device
/// sets and the kernel's state does not, so each byte is one unit: design/one-lock-bounded-steps/.
/// Each access is one load or store of a single register without writeback, the form whose stage 2
/// data abort reports the access in its syndrome (Arm ARM D24.2.45, ISV), which a hypervisor
/// emulating the device needs.
#[verifier(external_body)]
// external_body(glue): writes the PL011 through its memory-mapped registers, which have no state a proof could see
pub fn serial_write(a: u64, b: u64, c: u64, d: u64, e: u64, Tracked(steps): Tracked<&mut Steps>)
    ensures
        final(steps).count <= old(steps).count + PRINT_BYTES,
{
    let words = [a, b, c, d, e];
    let mut w = 0;
    while w < 5 {
        let mut k = 0;
        while k < 8 {
            let byte = (words[w] >> (8 * k)) as u8;
            if byte == 0 {
                return;
            }
            unsafe {
                loop {
                    let flags: u32;
                    core::arch::asm!(
                        "ldr {flags:w}, [{register}]",
                        register = in(reg) PL011 + PL011_FLAG,
                        flags = out(reg) flags,
                        options(nostack, readonly, preserves_flags),
                    );
                    if flags & PL011_TRANSMIT_FULL == 0 {
                        break;
                    }
                }
                core::arch::asm!(
                    "str {byte:w}, [{register}]",
                    register = in(reg) PL011 + PL011_DATA,
                    byte = in(reg) byte as u32,
                    options(nostack, preserves_flags),
                );
            }
            k += 1;
        }
        w += 1;
    }
}

} // verus!
