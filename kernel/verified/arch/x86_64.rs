//! The x86_64 arch items. Written from the AMD64 Architecture Programmer's Manual, Volume 2: System
//! Programming (24593).
use core::mem::MaybeUninit;
use vstd::prelude::*;

verus! {

use crate::capability::kernel::{FlushTarget, Flushed};
use crate::capability::operation::Outcome;

// The page-entry encoding: the long-mode page-translation entry's bits, chapter 5. The decoders and
// encoders in pagetable/entry.rs, the address checks in util/page_ptr_util_u.rs and the address lemmas
// in capability/map.rs and capability/link.rs read them. The accessed and dirty bits are the
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

pub const MEM_4k_MASK: u64 = 0x0000_ffff_ffff_f000;

/// A 2M page's address, bits 47:21.
pub const MEM_2m_MASK: u64 = 0x0000_ffff_ffe0_0000;

/// A 1G page's address, bits 47:30.
pub const MEM_1g_MASK: u64 = 0x0000_ffff_c000_0000;

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

// The trap frame and the user-return checks: what a thread record holds, what a return to user mode
// writes, and which program counters are user addresses. capability/thread.rs reads them.

/// The frame a thread record holds: the general registers the entry stubs in kernel/src/interrupt/
/// and kernel/src/syscalls/ push, then the interrupt stack frame, chapter 8.
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
    #[verifier(external_body)]
    // external_body(gap): builds a value from zeroed memory, which Verus cannot check
    pub const fn zeroed() -> Self {
        unsafe { MaybeUninit::zeroed().assume_init() }
    }

    pub fn new(input: &Registers) -> (ret: Self)
        ensures
            ret =~= *input,
    {
        let ret = Self {
            r15: input.r15,
            r14: input.r14,
            r13: input.r13,
            r12: input.r12,
            rbp: input.rbp,
            rbx: input.rbx,
            r11: input.r11,
            r10: input.r10,
            r9: input.r9,
            r8: input.r8,
            rcx: input.rcx,
            rdx: input.rdx,
            rsi: input.rsi,
            rdi: input.rdi,
            rax: input.rax,
            error_code: input.error_code,
            rip: input.rip,
            cs: input.cs,
            flags: input.flags,
            rsp: input.rsp,
            ss: input.ss,
        };
        ret
    }

    pub fn set_self(&mut self, src: &Registers)
        ensures
            *final(self) == *src,
    {
        *self = *src;
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

/// The selectors a thread returns to user mode with: the GDT's user code and data entries, 4 and 3,
/// at privilege 3. See kernel/src/gdt/.
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

/// COM1's base port, the serial port the kernel crate's console writes.
pub const COM1: u16 = 0x3f8;

/// The line status register, five ports above the base; bit 5 says the transmit register is empty.
pub const SERIAL_LINE_STATUS: u16 = 5;

pub const SERIAL_TRANSMIT_EMPTY: u8 = 1 << 5;

/// Writes to COM1 the bytes words a to e carry: each word's eight bytes from its lowest, a's first, up
/// to the first zero byte. Each byte waits for the transmit register to empty.
#[verifier(external_body)]
// external_body(glue): writes the serial port through port I/O, which has no state a proof could see
pub fn serial_write(a: u64, b: u64, c: u64, d: u64, e: u64) {
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
            k += 1;
        }
        w += 1;
    }
}

} // verus!
