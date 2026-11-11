// SPDX-License-Identifier: MIT

//! The x86_64 instructions, registers and tables the kernel uses outside the APIC.
//!
//! Written from the AMD64 Architecture Programmer's Manual, Volume 2: System Programming (24593),
//! cited as APM 2 with the section beside each table; the instructions themselves are in APM
//! Volume 3. The APIC's own registers are in `interrupt/`.

use core::arch::asm;
use core::ffi::c_void;
use core::mem::size_of;

pub mod gdt;
pub mod interrupt;
pub mod syscalls;
mod this_core;
pub mod write_protect;

pub use this_core::{
    core_pointer, counters, init, init_boot_core, init_core, set_core_pointer, translation_root, CoreState,
};

/// A privilege level: a selector's RPL and a descriptor's DPL. APM 2 §4.9.1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Ring {
    Ring0 = 0,
    Ring3 = 3,
}

/// A segment selector: the index into the GDT in bits 15:3, the table indicator in bit 2 (0, the
/// GDT) and the RPL in bits 1:0. APM 2 §4.5.1, Figure 4-3.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct SegmentSelector(u16);

impl SegmentSelector {
    pub const fn new(index: u16, rpl: Ring) -> Self {
        Self(index << 3 | rpl as u16)
    }

    pub const fn bits(self) -> u16 {
        self.0
    }
}

/// The current code segment selector. APM 2 §6.3.1.
pub fn cs() -> SegmentSelector {
    let selector: u16;
    unsafe { asm!("mov {0:x}, cs", out(reg) selector, options(nomem, nostack, preserves_flags)) };
    SegmentSelector(selector)
}

/// Loads CS with a far return to the next instruction, since 64-bit mode has no far jump to an
/// immediate selector. APM 2 §6.3.1.
pub unsafe fn load_cs(selector: SegmentSelector) {
    asm!(
        "push {selector}",
        "lea {tmp}, [rip + 2f]",
        "push {tmp}",
        "retfq",
        "2:",
        selector = in(reg) selector.0 as u64,
        tmp = lateout(reg) _,
    );
}

pub unsafe fn load_ds(selector: SegmentSelector) {
    asm!("mov ds, {0:x}", in(reg) selector.0, options(nostack, preserves_flags));
}

pub unsafe fn load_es(selector: SegmentSelector) {
    asm!("mov es, {0:x}", in(reg) selector.0, options(nostack, preserves_flags));
}

pub unsafe fn load_ss(selector: SegmentSelector) {
    asm!("mov ss, {0:x}", in(reg) selector.0, options(nostack, preserves_flags));
}

/// Loads the task register with the selector of a TSS descriptor. APM 2 §6.3.3.
pub unsafe fn load_tr(selector: SegmentSelector) {
    asm!("ltr {0:x}", in(reg) selector.0, options(nostack, preserves_flags));
}

/// The operand of LGDT and LIDT in 64-bit mode: a 16-bit limit and a 64-bit base. APM 2 §4.6.2,
/// Figure 4-8, and §4.6.6.
#[repr(C, packed)]
pub struct DescriptorTablePointer<T> {
    pub limit: u16,
    pub base: *const T,
}

const _: () = assert!(size_of::<DescriptorTablePointer<u8>>() == 10);

pub unsafe fn lgdt<T>(pointer: &DescriptorTablePointer<T>) {
    asm!("lgdt [{0}]", in(reg) pointer, options(readonly, nostack, preserves_flags));
}

pub unsafe fn lidt<T>(pointer: &DescriptorTablePointer<T>) {
    asm!("lidt [{0}]", in(reg) pointer, options(readonly, nostack, preserves_flags));
}

/// The 64-bit task state segment: RSP0 to RSP2 at bytes 04h to 1Bh, IST1 to IST7 at 24h to 5Bh, the
/// I/O map base at 66h. APM 2 §12.2.5, Figure 12-8.
#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct TaskStateSegment {
    _reserved0: u32,
    rsp: [u64; 3],
    _reserved1: u64,
    ist: [u64; 7],
    _reserved2: u64,
    _reserved3: u16,
    iomap_base: u16,
}

const _: () = assert!(size_of::<TaskStateSegment>() == 0x68);

impl TaskStateSegment {
    pub const fn new() -> Self {
        Self {
            _reserved0: 0,
            rsp: [0; 3],
            _reserved1: 0,
            ist: [0; 7],
            _reserved2: 0,
            _reserved3: 0,
            iomap_base: 0,
        }
    }

    /// Sets the stack an interrupt from ring 3 switches to.
    pub fn set_rsp0(&mut self, stack: u64) {
        self.rsp[0] = stack;
    }

    /// Sets IST`index + 1`, the stack a gate whose IST field is `index + 1` switches to.
    pub fn set_ist(&mut self, index: usize, stack: u64) {
        assert!(index < 7);
        self.ist[index] = stack;
    }
}

/// CR3 bit 63. With CR4.PCIDE set, a load of CR3 that sets it keeps the TLB entries tagged with the
/// loaded PCID; with PCIDE clear the bit is reserved. APM 2, the CR3 register in its PCID format.
pub const CR3_NO_FLUSH: u64 = 1 << 63;

/// Set by boot when the processor's PCID feature is on. `switch_address_space` reads it.
pub static mut PCIDE: u64 = 0;

/// A page table entry's present and page size bits, and the address it holds. APM 2 §5.4.
const ENTRY_PRESENT: u64 = 1 << 0;
const ENTRY_PAGE_SIZE: u64 = 1 << 7;
const ENTRY_ADDRESS: u64 = 0x000f_ffff_ffff_f000;

/// The leaf page table entry that maps `address` under the current CR3, which must be a 4 KiB
/// entry, as the loader writes for the kernel's image. Page tables lie in the identity map the
/// loader built, so their physical addresses are usable as pointers.
unsafe fn leaf_entry(address: u64) -> *mut u64 {
    let cr3: u64;
    asm!("mov {}, cr3", out(reg) cr3);
    let mut table = (cr3 & ENTRY_ADDRESS) as *mut u64;
    for level in (1..4).rev() {
        let entry = *table.add((address >> (12 + 9 * level)) as usize & 0x1ff);
        assert!(
            entry & ENTRY_PRESENT != 0 && entry & ENTRY_PAGE_SIZE == 0,
            "{:#x} is not mapped by a 4 KiB entry",
            address,
        );
        table = (entry & ENTRY_ADDRESS) as *mut u64;
    }
    table.add((address >> 12) as usize & 0x1ff)
}

/// Unmaps `page`, a page of the kernel's image, so that any access to it faults. Every address
/// space shares the kernel's tables, so the page is gone from all of them. This core forgets its
/// translation; the caller runs before another core starts, so no other core holds one.
pub unsafe fn guard(page: *const u8) {
    assert!(page as u64 & 0xfff == 0, "a guard is a page");
    let entry = leaf_entry(page as u64);
    assert!(*entry & ENTRY_PRESENT != 0, "{:p} is guarded twice", page);
    *entry &= !ENTRY_PRESENT;
    asm!("invlpg [{}]", in(reg) page);
}

/// Enters a busy loop.
pub unsafe fn spin_forever() -> ! {
    loop {
        asm!("hlt");
    }
}

/// Refuses every key: the x86_64 arch module has no command-line option, and the machine's
/// `set_option` answers for its own.
pub fn set_option(key: &str, value: &str) -> bool {
    let _ = (key, value);
    false
}

/// The cycle counter: the TSC.
pub fn cycles() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

/// How many cycles of [`cycles`] a boot check waits for another core before it reports that the core
/// did not answer: seconds on any machine this runs on, where a core that answers takes microseconds.
pub fn stall_cycles() -> u64 {
    20_000_000_000
}

/// Waits for the next interrupt.
pub fn wait() {
    unsafe { asm!("sti", "hlt") };
}

pub unsafe fn read_cr0() -> u64 {
    let cr0: u64;
    asm!("mov {}, cr0", out(reg) cr0);
    cr0
}

pub unsafe fn read_cr4() -> u64 {
    let cr4: u64;
    asm!("mov {}, cr4", out(reg) cr4);
    cr4
}

pub unsafe fn write_cr0(cr0: u64) {
    asm!("mov cr0, {}", in(reg) cr0);
}

pub unsafe fn write_cr4(cr4: u64) {
    asm!("mov cr4, {}", in(reg) cr4);
}

/// RFLAGS.IF, which lets the core take maskable interrupts, and bit 1, which is reserved and reads as
/// one. APM 2 §3.1.6, Figure 3-7.
const RFLAGS_IF: u64 = 1 << 9;
const RFLAGS_RESERVED_ONE: u64 = 1 << 1;

/// Enters user code at `pc` with stack `sp` and two entry arguments, which it finds in `rdi` and `rsi`,
/// and with interrupts unmasked, which the kernel kept masked: SYSRET loads RFLAGS from r11 (APM 3,
/// SYSRET), so the process starts with IF set and no other flag.
pub unsafe fn enter_userspace(pc: *const c_void, sp: *mut c_void, rdi: u64, rsi: u64) -> ! {
    #[cfg(feature = "stray_timer")]
    crate::machine::set_timer(crate::STRAY_TIMER_TICKS);
    log::info!("Going to sysret into {:x?}", pc);
    asm!(
        "mov rsp, {sp}",
        // dom0 gets its entry arguments in rdi and rsi and no kernel values.
        "xor eax, eax",
        "xor edx, edx",
        "xor ebx, ebx",
        "xor ebp, ebp",
        "xor r8d, r8d",
        "xor r9d, r9d",
        "xor r10d, r10d",
        "xor r12d, r12d",
        "xor r13d, r13d",
        "xor r14d, r14d",
        "xor r15d, r15d",
        "sysretq",

        in("rcx") pc,
        in("r11") RFLAGS_IF | RFLAGS_RESERVED_ONE,
        sp = in(reg) sp,
        in("rdi") rdi,
        in("rsi") rsi,
        out("r15") _,
    );

    loop {}
}

/// Switches this core to the page table whose top level is at physical address `root`, as address
/// space `asid`, keeping the entries the TLB holds under `asid`: CR3 takes the root in bits 51:12 and
/// the PCID in bits 11:0. The kernel tracks when an address space's entries go stale and flushes them
/// itself, design/flush-without-waiting/. Without PCIDE, which boot records, the no-flush bit is
/// cleared before the load.
pub fn switch_address_space(root: usize, asid: usize) {
    assert!(root & 0xfff == 0, "a page table root is 4K-aligned");
    assert!(asid < verified::define::PCID_MAX, "an address-space id fits a PCID");
    let cr3 = (root | asid) as u64 | CR3_NO_FLUSH;
    unsafe {
        asm!(
            "mov {tmp}, [rip + {pcide}]",
            "test {tmp}, {tmp}",
            "jnz 2f",
            "btr {cr3}, 63",
            "2:",
            "mov cr3, {cr3}",
            tmp = out(reg) _,
            cr3 = inout(reg) cr3 => _,
            pcide = sym PCIDE,
            options(readonly, nostack),
        );
    }
}

/// Model-specific registers. The numbers are APM 2 Appendix A, Table A-2, except where noted.
pub mod msr {
    use core::arch::asm;

    /// APM 2 §3.1.7, Figure 3-9.
    pub const EFER: u32 = 0xC000_0080;
    /// SYSCALL and SYSRET selectors, and the 64-bit, compatibility-mode and flag-mask targets. APM 2
    /// §6.1.1, Figure 6-1.
    pub const STAR: u32 = 0xC000_0081;
    pub const LSTAR: u32 = 0xC000_0082;
    pub const CSTAR: u32 = 0xC000_0083;
    pub const SF_MASK: u32 = 0xC000_0084;
    /// APM 2 §4.5.3.
    pub const GS_BASE: u32 = 0xC000_0101;

    /// EFER.SCE, which enables SYSCALL and SYSRET. APM 2 §3.1.7, Figure 3-9.
    pub const EFER_SCE: u64 = 1 << 0;

    /// APM 2 §6.2.5.
    pub unsafe fn rdmsr(msr: u32) -> u64 {
        let (low, high): (u32, u32);
        asm!("rdmsr", in("ecx") msr, out("eax") low, out("edx") high, options(nomem, nostack, preserves_flags));
        (high as u64) << 32 | low as u64
    }

    pub unsafe fn wrmsr(msr: u32, value: u64) {
        asm!(
            "wrmsr",
            in("ecx") msr,
            in("eax") value as u32,
            in("edx") (value >> 32) as u32,
            options(nostack, preserves_flags),
        );
    }
}
