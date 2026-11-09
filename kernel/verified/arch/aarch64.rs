//! The aarch64 arch items, with the names, signatures and specs of the x86_64 module's. Each item's
//! values come from the Arm Architecture Reference Manual. An item that has not been written from it
//! yet is declared here and nothing more: its spec functions are uninterpreted and its executable and
//! proof functions are external_body, counted as unproven in tools/external-body-list. See
//! design/arch-module/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::{FlushTarget, Flushed};
use crate::capability::operation::Outcome;
use crate::define::PAddr;
use crate::pagetable::entry::{PageEntry, PageEntryPerm, PageEntryStatus};
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
// word is the empty entry. Its output address sits where x86_64's does, so the address masks are
// the same.

/// Valid descriptor, bit 0.
pub const DESC_VALID: u64 = 0x1;

/// Bit 1: a table descriptor at levels 4 to 2, a page descriptor at level 1, and a block descriptor at
/// levels 3 and 2 when clear (D8.3.1.1, D8.3.1.2). At level 1 a valid word with it clear is reserved
/// and translates as invalid.
pub const DESC_TYPE: u64 = 0x2;

/// AP[1], bit 6 of a block or page descriptor: EL0 may read, and write if AP[2] allows (D8.3.1.2,
/// D8.4.1.2.1).
pub const DESC_AP_EL0: u64 = 0x40;

/// AP[2], bit 7 of a block or page descriptor: read-only at every exception level.
pub const DESC_AP_RO: u64 = 0x80;

/// AF, bit 10 of a block or page descriptor: the access flag (D8.5.1). In a table descriptor the bit
/// is IGNORED unless hardware management of the table descriptor's access flag is enabled, which the
/// kernel does not enable, so the walker sets it only in a leaf.
pub const DESC_AF: u64 = 0x400;

/// The memory attributes the encoder writes in every valid leaf and the decoders ignore: AttrIndx[2:0]
/// = 0, bits 4:2, which MAIR_EL1 attribute 0 makes Normal write-back memory (D8.6.1); SH[1:0] = 0b11,
/// bits 9:8, Inner Shareable (D8.6.2); and nG, bit 11, so the translation is cached under the current
/// ASID only (D8.3.1.2), as x86_64's leaves are never global.
pub const DESC_LEAF_ATTRS: u64 = 0xb00;

/// UXN, bit 54 of a block or page descriptor: no execution at EL0 (D8.4.1.2.3).
pub const DESC_UXN: u64 = 0x0040_0000_0000_0000;

/// UXN and PXN, bits 54 and 53 of a block or page descriptor: no execution at EL0 or at EL1.
pub const DESC_XN: u64 = 0x0060_0000_0000_0000;

/// UXNTable, bit 60 of a table descriptor: every leaf below it is UXN (D8.3.1.1, D8.4.1.2.5).
pub const TABLE_UXN: u64 = 0x1000_0000_0000_0000;

/// UXNTable and PXNTable, bits 60 and 59 of a table descriptor: every leaf below it is UXN and PXN.
pub const TABLE_XN: u64 = 0x1800_0000_0000_0000;

/// APTable[0], bit 61 of a table descriptor: no EL0 access below it (D8.4.1.2.2, Table D8-64).
pub const TABLE_AP_NO_EL0: u64 = 0x2000_0000_0000_0000;

/// APTable[1], bit 62 of a table descriptor: no write below it.
pub const TABLE_AP_RO: u64 = 0x4000_0000_0000_0000;

/// The physical address of a 4K page or of the next table, bits 47:12.
pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

/// A 2M block's address, bits 47:21.
pub const MEM_2m_MASK: u64 = 0x0000_ffff_ffe0_0000;

/// A 1G block's address, bits 47:30.
pub const MEM_1g_MASK: u64 = 0x0000_ffff_c000_0000;

/// The bits of an entry's word that are not the walker's access flag: a word ANDed with it has its
/// status clear, which is what a clear of the status bits writes.
pub const STATUS_KEPT_MASK: usize = 0xffff_ffff_ffff_fbff;

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

/// Whether this target maintains the dirty bit: never. The hardware's dirty state is DBM with AP[2]
/// clear, and a clean entry is AP[2] set (D8.5.2.1), so clearing it sets a bit, which the AND of
/// STATUS_KEPT_MASK cannot. The kernel leaves TCR_EL1.HD clear and writes DBM clear, so AP[2] is the
/// kernel's own and the status's dirty bit is always clear. See design/arch-module/.
pub open spec fn spec_maintains_dirty() -> bool {
    false
}

#[verifier(when_used_as_spec(spec_maintains_dirty))]
pub fn maintains_dirty() -> (ret: bool)
    ensures
        ret == spec_maintains_dirty(),
{
    false
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

/// Writable: APTable[1] or AP[2] clear in a valid word, set in an invalid one.
pub open spec fn usize2write(v: usize, level: usize) -> bool {
    if usize2table(v, level) {
        ((v & TABLE_AP_RO as usize) != 0) != usize2present(v, level)
    } else {
        ((v & DESC_AP_RO as usize) != 0) != usize2present(v, level)
    }
}

/// Not executable at EL0: UXNTable or UXN. The encoder writes the PXN bit beside it.
pub open spec fn usize2execute_disable(v: usize, level: usize) -> bool {
    if usize2table(v, level) {
        (v & TABLE_UXN as usize) != 0
    } else {
        (v & DESC_UXN as usize) != 0
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

pub open spec fn usize2accessed(v: usize, level: usize) -> bool {
    (v & DESC_AF as usize) != 0
}

/// The walker's accessed and dirty bits of a word, apart from the entry it decodes to.
pub open spec fn spec_usize2page_entry_status(v: usize, level: usize) -> PageEntryStatus {
    PageEntryStatus { accessed: usize2accessed(v, level), dirty: false }
}

#[verifier(when_used_as_spec(spec_usize2page_entry_status))]
pub fn usize2page_entry_status(v: usize, level: usize) -> (ret: PageEntryStatus)
    ensures
        ret == spec_usize2page_entry_status(v, level),
{
    PageEntryStatus { accessed: (v & DESC_AF as usize) != 0, dirty: false }
}

/// The word with its access flag clear.
pub open spec fn spec_without_status(v: usize) -> usize {
    v & STATUS_KEPT_MASK
}

/// Two words that differ only in the access flag decode to the same entry, so whatever the walker
/// sets there leaves every table's view as it was.
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
        && (v & 0x80usize != 0) == (w & 0x80usize != 0)
        && (v & 0x0040_0000_0000_0000usize != 0) == (w & 0x0040_0000_0000_0000usize != 0)
        && (v & 0x1000_0000_0000_0000usize != 0) == (w & 0x1000_0000_0000_0000usize != 0)
        && (v & 0x2000_0000_0000_0000usize != 0) == (w & 0x2000_0000_0000_0000usize != 0)
        && (v & 0x4000_0000_0000_0000usize != 0) == (w & 0x4000_0000_0000_0000usize != 0))
        by (bit_vector)
        requires
            v & 0xffff_ffff_ffff_fbffusize == w & 0xffff_ffff_ffff_fbffusize,
    ;
}

/// Clearing the status bits clears them and keeps the rest: clearing again changes nothing.
pub proof fn lemma_without_status(v: usize, level: usize)
    ensures
        spec_without_status(spec_without_status(v)) == spec_without_status(v),
        spec_usize2page_entry_status(spec_without_status(v), level).is_clear(),
{
    assert((v & 0xffff_ffff_ffff_fbffusize) & 0xffff_ffff_ffff_fbffusize == v
        & 0xffff_ffff_ffff_fbffusize) by (bit_vector);
    assert((v & 0xffff_ffff_ffff_fbffusize) & 0x400usize == 0) by (bit_vector);
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
        && 0usize & 0x0040_0000_0000_0000usize == 0
        && 0usize & 0x1000_0000_0000_0000usize == 0
        && 0usize & 0x2000_0000_0000_0000usize == 0
        && 0usize & 0x4000_0000_0000_0000usize == 0
        && 0usize & 0xffff_ffff_ffff_fbffusize == 0) by (bit_vector);
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
            execute_disable: (v & TABLE_UXN as usize) != 0,
            user: ((v & TABLE_AP_NO_EL0 as usize) != 0) != present,
        }
    } else {
        PageEntryPerm {
            present,
            ps,
            write: ((v & DESC_AP_RO as usize) != 0) != present,
            execute_disable: (v & DESC_UXN as usize) != 0,
            user: (v & DESC_AP_EL0 as usize) != 0,
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
        MEM_valid(ret.addr),
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
        MEM_valid(ret),
{
    let ret = v & MEM_MASK as usize;
    assert(v & 0x0000_ffff_ffff_f000u64 as usize & (!0x0000_ffff_ffff_f000u64) as usize == 0)
        by (bit_vector);
    return ret;
}

/// The word that holds an entry in a table at `level`, with its status clear. A valid leaf also gets
/// DESC_LEAF_ATTRS, which the decoders ignore.
pub fn page_entry2usize(page_entry: &PageEntry, level: usize) -> (ret: usize)
    requires
        MEM_valid(page_entry.addr),
    ensures
        spec_usize2page_entry(ret, level) == *page_entry,
        spec_usize2page_entry_status(ret, level).is_clear(),
        page_entry.perm.present ==> ret != 0,
{
    let addr = page_entry.addr;
    let present = page_entry.perm.present;
    let ps = page_entry.perm.ps;
    let leaf = level == 1 || ps;
    let write_bit = page_entry.perm.write != present;
    let p: usize = if present { DESC_VALID as usize } else { 0 };
    let t: usize = if ps != present { DESC_TYPE as usize } else { 0 };
    let lw: usize = if leaf && write_bit { DESC_AP_RO as usize } else { 0 };
    let tw: usize = if !leaf && write_bit { TABLE_AP_RO as usize } else { 0 };
    let lu: usize = if leaf && page_entry.perm.user { DESC_AP_EL0 as usize } else { 0 };
    let tu: usize = if !leaf && page_entry.perm.user != present { TABLE_AP_NO_EL0 as usize } else { 0 };
    let lx: usize = if leaf && page_entry.perm.execute_disable { DESC_XN as usize } else { 0 };
    let tx: usize = if !leaf && page_entry.perm.execute_disable { TABLE_XN as usize } else { 0 };
    let la: usize = if leaf && present { DESC_LEAF_ATTRS as usize } else { 0 };
    let ret = addr | p | t | lw | tw | lu | tu | lx | tx | la;
    assert(ret & 0x1usize == p
        && ret & 0x2usize == t
        && ret & 0x40usize == lu
        && ret & 0x80usize == lw
        && ret & 0x400usize == 0
        && (ret & 0x0040_0000_0000_0000usize != 0) == (lx != 0)
        && (ret & 0x1000_0000_0000_0000usize != 0) == (tx != 0)
        && ret & 0x2000_0000_0000_0000usize == tu
        && ret & 0x4000_0000_0000_0000usize == tw
        && ret & 0x0000_ffff_ffff_f000usize == addr
        && (p == 1 ==> ret != 0)) by (bit_vector)
        requires
            ret == addr | p | t | lw | tw | lu | tu | lx | tx | la,
            addr & (!0x0000_ffff_ffff_f000u64) as usize == 0,
            p == 0 || p == 1,
            t == 0 || t == 2,
            lw == 0 || lw == 0x80,
            tw == 0 || tw == 0x4000_0000_0000_0000usize,
            lu == 0 || lu == 0x40,
            tu == 0 || tu == 0x2000_0000_0000_0000usize,
            lx == 0 || lx == 0x0060_0000_0000_0000usize,
            tx == 0 || tx == 0x1800_0000_0000_0000usize,
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

/// Writes the bytes words a to e carry: each word's eight bytes from its lowest, a's first, up to the
/// first zero byte.
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for serial_write
pub fn serial_write(a: u64, b: u64, c: u64, d: u64, e: u64) {
    unimplemented!()
}

} // verus!
