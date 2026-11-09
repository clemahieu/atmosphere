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

// The page-entry encoding: the VMSAv8-64 stage-1 descriptor for the 4K granule with TCR_EL1.T0SZ = 16.
// Its output address sits where x86_64's does, so the address masks are the same.

/// The physical address of a 4K page or of the next table, bits 47:12.
pub const MEM_MASK: u64 = 0x0000_ffff_ffff_f000;

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

/// A 2M block's address, bits 47:21.
pub const MEM_2m_MASK: u64 = 0x0000_ffff_ffe0_0000;

/// A 1G block's address, bits 47:30.
pub const MEM_1g_MASK: u64 = 0x0000_ffff_c000_0000;

/// The bits of an entry's word that are not the walker's status bits. Not yet placed: it keeps every
/// bit.
pub const STATUS_KEPT_MASK: usize = !0usize;

/// Whether this target's walker maintains the accessed bit.
pub uninterp spec fn spec_maintains_accessed() -> bool;

#[verifier(when_used_as_spec(spec_maintains_accessed))]
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for maintains_accessed
pub fn maintains_accessed() -> (ret: bool)
    ensures
        ret == spec_maintains_accessed(),
{
    unimplemented!()
}

/// Whether this target's walker maintains the dirty bit.
pub uninterp spec fn spec_maintains_dirty() -> bool;

#[verifier(when_used_as_spec(spec_maintains_dirty))]
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for maintains_dirty
pub fn maintains_dirty() -> (ret: bool)
    ensures
        ret == spec_maintains_dirty(),
{
    unimplemented!()
}

/// The walker's accessed and dirty bits of a word, apart from the entry it decodes to.
pub uninterp spec fn spec_usize2page_entry_status(v: usize, level: usize) -> PageEntryStatus;

#[verifier(when_used_as_spec(spec_usize2page_entry_status))]
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for usize2page_entry_status
pub fn usize2page_entry_status(v: usize, level: usize) -> (ret: PageEntryStatus)
    ensures
        ret == spec_usize2page_entry_status(v, level),
{
    unimplemented!()
}

/// The word with its status bits clear.
pub uninterp spec fn spec_without_status(v: usize) -> usize;

/// Two words that differ only in the status bits decode to the same entry.
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for lemma_status_outside_entry
pub proof fn lemma_status_outside_entry(v: usize, w: usize, level: usize)
    requires
        spec_without_status(v) == spec_without_status(w),
    ensures
        spec_usize2page_entry(v, level) == spec_usize2page_entry(w, level),
{
}

/// Clearing the status bits clears them and keeps the rest: clearing again changes nothing.
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for lemma_without_status
pub proof fn lemma_without_status(v: usize, level: usize)
    ensures
        spec_without_status(spec_without_status(v)) == spec_without_status(v),
        spec_usize2page_entry_status(spec_without_status(v), level).is_clear(),
{
}

/// The zero word is the empty entry with its status clear, at every level.
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for zero_leads_is_empty_page_entry
pub proof fn zero_leads_is_empty_page_entry(level: usize)
    ensures
        spec_usize2page_entry(0, level).is_empty(),
        spec_usize2page_entry_status(0, level).is_clear(),
        spec_without_status(0) == 0,
{
}

pub uninterp spec fn spec_usize2page_entry_perm(v: usize, level: usize) -> PageEntryPerm;

#[verifier(when_used_as_spec(spec_usize2page_entry_perm))]
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for usize2page_entry_perm
pub fn usize2page_entry_perm(v: usize, level: usize) -> (ret: PageEntryPerm)
    ensures
        ret =~= spec_usize2page_entry_perm(v, level),
{
    unimplemented!()
}

/// The entry a word of a table at `level` holds.
pub open spec fn spec_usize2page_entry(v: usize, level: usize) -> PageEntry {
    PageEntry { addr: spec_usize2pa(v, level), perm: spec_usize2page_entry_perm(v, level) }
}

#[verifier(when_used_as_spec(spec_usize2page_entry))]
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for usize2page_entry
pub fn usize2page_entry(v: usize, level: usize) -> (ret: PageEntry)
    ensures
        ret =~= spec_usize2page_entry(v, level),
        MEM_valid(ret.addr),
{
    unimplemented!()
}

pub uninterp spec fn spec_usize2pa(v: usize, level: usize) -> PAddr;

#[verifier(when_used_as_spec(spec_usize2pa))]
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for usize2pa
pub fn usize2pa(v: usize, level: usize) -> (ret: PAddr)
    ensures
        ret =~= spec_usize2pa(v, level),
        MEM_valid(ret),
{
    unimplemented!()
}

/// The word that holds an entry in a table at `level`, with its status clear.
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for page_entry2usize
pub fn page_entry2usize(page_entry: &PageEntry, level: usize) -> (ret: usize)
    requires
        MEM_valid(page_entry.addr),
    ensures
        spec_usize2page_entry(ret, level) == *page_entry,
        spec_usize2page_entry_status(ret, level).is_clear(),
        page_entry.perm.present ==> ret != 0,
{
    unimplemented!()
}

/// Flushes every context on this core.
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for flush_every_context
pub fn flush_every_context(core: usize, epoch: usize) -> (ret: Tracked<Flushed>)
    ensures
        ret@.target == FlushTarget::Core(core as int),
        ret@.epoch == epoch as int,
{
    unimplemented!()
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

    /// The operation number.
    pub uninterp spec fn spec_operation_number(&self) -> u64;

    #[verifier(when_used_as_spec(spec_operation_number))]
    #[verifier(external_body)]
    // external_body(unproven): the aarch64 placeholder for operation_number
    pub fn operation_number(&self) -> (ret: u64)
        ensures
            ret == self.spec_operation_number(),
    {
        unimplemented!()
    }

    /// The slot of the invoked capability.
    pub uninterp spec fn spec_slot(&self) -> u64;

    #[verifier(when_used_as_spec(spec_slot))]
    #[verifier(external_body)]
    // external_body(unproven): the aarch64 placeholder for slot
    pub fn slot(&self) -> (ret: u64)
        ensures
            ret == self.spec_slot(),
    {
        unimplemented!()
    }

    /// Argument k of 1 to 5.
    pub uninterp spec fn spec_argument(&self, k: usize) -> u64;

    #[verifier(when_used_as_spec(spec_argument))]
    #[verifier(external_body)]
    // external_body(unproven): the aarch64 placeholder for argument
    pub fn argument(&self, k: usize) -> (ret: u64)
        requires
            1 <= k <= 5,
        ensures
            ret == self.spec_argument(k),
    {
        unimplemented!()
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
    #[verifier(external_body)]
    // external_body(unproven): the aarch64 placeholder for write_outcome
    pub fn write_outcome(&mut self, out: Outcome)
        ensures
            final(self).spec_status_word() == out.status,
            final(self).spec_result(1) == out.result_1,
            final(self).spec_result(2) == out.result_2,
            final(self).spec_result(3) == out.result_3,
            final(self).spec_result(4) == out.result_4,
            final(self).spec_argument(5) == old(self).spec_argument(5),
    {
        unimplemented!()
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

/// Whether a program counter is a user address.
pub uninterp spec fn user_rip(rip: u64) -> bool;

#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for is_user_rip
pub fn is_user_rip(rip: u64) -> (ret: bool)
    ensures
        ret == user_rip(rip),
{
    unimplemented!()
}

#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for user_frame_of
pub fn user_frame_of(f: Registers) -> (ret: Registers)
    ensures
        ret == user_frame(f),
{
    unimplemented!()
}

/// A frame a controller wrote, as the thread will return to user mode with it, granting no
/// privilege. See design/process-holds-capabilities/.
pub uninterp spec fn user_frame(f: Registers) -> Registers;

/// Writes the bytes words a to e carry: each word's eight bytes from its lowest, a's first, up to the
/// first zero byte.
#[verifier(external_body)]
// external_body(unproven): the aarch64 placeholder for serial_write
pub fn serial_write(a: u64, b: u64, c: u64, d: u64, e: u64) {
    unimplemented!()
}

} // verus!
