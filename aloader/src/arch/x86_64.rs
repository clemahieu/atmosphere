//! The x86_64 PC as UEFI leaves it: long mode with four-level paging, and COM1.

use core::arch::asm;
use core::arch::x86_64::__cpuid;
use core::ffi::c_void;

use astd::boot::{BootInfo, PAGE_BYTES};
use bit_field::BitField;
use constants::SPORT_ADDR;
use ns16550a::PioSerial;

use crate::memory::Leaf;

/// The serial device the loader logs to.
pub type Serial = PioSerial;

/// COM1, not yet initialized.
pub const fn serial() -> Serial {
    unsafe { PioSerial::new(SPORT_ADDR) }
}

/// Masks this CPU's interrupts.
pub unsafe fn disable_interrupts() {
    asm!("cli");
}

/// Runs `crate::load` on the stack that ends at `stack_top`.
pub unsafe fn load_on_stack(stack_top: u64, rsdp: u64, wait_for_debugger: bool) -> ! {
    asm!(
        "mov rsp, {stack_top}",
        "call {load}",
        stack_top = in(reg) stack_top,
        load = sym load,
        in("rdi") rsdp,
        in("rsi") wait_for_debugger as u64,
        options(noreturn),
    );
}

/// Called on the loader's stack with the RSDP in rdi and whether to wait for a debugger in rsi. The
/// target's C convention is Microsoft's, which passes them in rcx and rdx.
extern "sysv64" fn load(rsdp: u64, wait_for_debugger: bool) -> ! {
    crate::load(rsdp, wait_for_debugger)
}

/// The register a debugger clears to let the loader go, for the line `debugger::wait` logs.
pub const DEBUGGER_REGISTER: &str = "rax";

/// What rax holds while the loader waits; tools/gdb-helper.py checks for it before clearing rax.
const WAITING: u64 = 0x6764_6277_6169_7421;

/// Spins until a debugger sets rax to anything but `WAITING`.
pub fn wait_for_debugger() {
    unsafe {
        asm!(
            "2:",
            "pause",
            "cmp rax, {waiting}",
            "je 2b",
            waiting = in(reg) WAITING,
            inout("rax") WAITING => _,
            options(nomem, nostack),
        );
    }
}

/// Makes `root` the table this CPU translates through, with tagged TLB enabled where the CPU has
/// it. Returns whether it has, for `BootInfo::pcide`.
pub unsafe fn activate(root: *const c_void) -> bool {
    let pcide = cpu_has_pcid();

    if pcide {
        log::info!("Enabling Tagged TLB");
        asm!(
            "mov {cr4}, cr4",
            "or {cr4}, {cr4_pcide}",
            "mov cr4, {cr4}",
            cr4 = out(reg) _,
            cr4_pcide = const (1 << 17),
        );
    } else {
        log::warn!("CPU does not support Tagged TLB");
    }

    log::info!("Switching to PML4 @ {:x?}", root);
    asm!(
        "mov cr3, {pml4}",
        pml4 = inout(reg) root => _,
    );

    pcide
}

fn cpu_has_pcid() -> bool {
    let cpuid_1 = __cpuid(0x1);
    (cpuid_1.ecx & (1 << 17)) != 0
}

/// Drops the TLB's entry for the page at `vaddr`, whatever the page's size, and a global one the
/// firmware's tables left.
pub unsafe fn flush_page(vaddr: u64) {
    asm!("invlpg [{}]", in(reg) vaddr);
}

/// Calls the kernel's `entry` on the stack that ends at `stack_top`, with `boot_info` as its
/// argument and the data segment registers cleared. Returns what the kernel returns.
pub unsafe fn enter_kernel(entry: *const c_void, boot_info: *const BootInfo, stack_top: u64) -> usize {
    let ret: usize;
    asm!(
        // save state
        "mov r15w, ds; push r15w",
        "mov r15w, fs; push r15w",
        "mov r15w, gs; push r15w",
        "mov r15w, ss; push r15w",

        // clear state
        // rdi = &boot_info
        "xor r15, r15",
        "mov ds, r15w",
        "mov fs, r15w",
        "mov gs, r15w",
        "mov ss, r15w",

        "push rsp",
        "mov rsp, rsi",
        "xor rsi, rsi",

        // call entry
        "call rax",

        // restore state
        "pop rsp",
        "pop r15w; mov ss, r15w",
        "pop r15w; mov gs, r15w",
        "pop r15w; mov fs, r15w",
        "pop r15w; mov ds, r15w",

        inout("rax") entry => ret,
        inout("rdi") boot_info => _,
        inout("rsi") stack_top => _,
        out("r15") _,
    );
    ret
}

/// The number of bits in a physical address.
///
/// This is also called M in the Intel manual.
const MAXPHYADDR: u64 = 56;

/// Bitmask to get the page in a linear address.
const PAGE_MASK: u64 = !(PAGE_BYTES - 1);

/// Bitmask to get the physical address.
const PHYSICAL_MASK: u64 = (1u64 << MAXPHYADDR) - 1u64;

/// Bitmask to get the physical page address.
const PHYSICAL_PAGE_MASK: u64 = PAGE_MASK & PHYSICAL_MASK;

/// A page-table entry, at any of the four levels.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Entry(u64);

impl Entry {
    /// The entry that maps nothing.
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Names the table at `address`. `user` lets user mode through to what the table maps.
    pub fn table(address: u64, user: bool) -> Self {
        Self::empty()
            .with_present(true)
            .with_read_write(true)
            .with_address(address)
            .with_user(user)
    }

    /// Maps the writable frame at `paddr`, of `leaf`'s size.
    pub fn leaf(paddr: u64, leaf: Leaf, user: bool, cache_disable: bool) -> Self {
        Self::empty()
            .with_present(true)
            .with_read_write(true)
            .with_address(paddr)
            .with_page_size_bit(leaf == Leaf::Large)
            .with_cache_disable(cache_disable)
            .with_user(user)
    }

    pub fn present(&self) -> bool {
        (self.0 & 0b1) == 1
    }

    /// Whether a present entry above the last level maps a frame itself, where it would otherwise
    /// name the next table.
    pub fn large(&self) -> bool {
        self.0.get_bit(7)
    }

    /// The table a table entry names, or the frame a leaf maps.
    pub fn address(&self) -> u64 {
        PHYSICAL_PAGE_MASK & self.0
    }

    pub fn user(&self) -> bool {
        self.0.get_bit(2)
    }

    pub fn cache_disable(&self) -> bool {
        self.0.get_bit(4)
    }

    fn with_present(mut self, present: bool) -> Self {
        self.0 = (self.0 & !(0b1)) | (if present { 1 } else { 0 });
        self
    }

    fn with_read_write(mut self, read_write: bool) -> Self {
        self.0.set_bit(1, read_write);
        self
    }

    fn with_user(mut self, user: bool) -> Self {
        self.0.set_bit(2, user);
        self
    }

    fn with_cache_disable(mut self, cache_disable: bool) -> Self {
        self.0.set_bit(4, cache_disable);
        self
    }

    fn with_address(mut self, address: u64) -> Self {
        let masked = PHYSICAL_PAGE_MASK & address;
        self.0 = self.0 & !(PHYSICAL_PAGE_MASK) | masked;
        self
    }

    fn with_page_size_bit(mut self, page_size: bool) -> Self {
        self.0.set_bit(7, page_size);
        self
    }
}
