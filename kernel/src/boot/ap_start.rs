//! AP boot trampoline.
//!
//! ## AP Boot ABI
//!
//! -32 @ 0x6fe0: Argument
//! -24 @ 0x6fe8: Code Pointer
//! -16 @ 0x6ff0: Stack Pointer
//!  -8 @ 0x6ff8: CR3
//!   0 @ 0x7000: Trampoline Code
//!
//! The trampoline is assembled into the kernel image between `ap_trampoline_start` and
//! `ap_trampoline_end` and runs where `StartTrampoline` copies it, at `BASE`, not where the kernel
//! is linked. So every absolute address in it is `BASE` plus the symbol's offset from
//! `ap_trampoline_start`, which the assembler resolves without a relocation.

use core::arch::global_asm;
use core::ptr;

/// Where the trampoline runs: the page a STARTUP IPI names.
const BASE: u16 = 0x7000;

global_asm!(
    ".pushsection .rodata.ap_trampoline, \"a\"",
    ".balign 16",
    ".global ap_trampoline_start",
    ".global ap_trampoline_end",
    ".hidden ap_trampoline_start",
    ".hidden ap_trampoline_end",
    "ap_trampoline_start:",
    ".code16",
    "cli",
    // Zero the segment registers.
    "xor %ax, %ax",
    "mov %ax, %ds",
    "mov %ax, %es",
    "mov %ax, %ss",
    "mov %ax, %gs",
    "mov %ax, %fs",
    "cld",
    "lgdt {base} + (ap_trampoline_gdt32_pointer - ap_trampoline_start)",
    // Set the protected-mode bit.
    "mov %cr0, %eax",
    "or $1, %eax",
    "mov %eax, %cr0",
    "ljmp $(ap_trampoline_gdt32_code - ap_trampoline_gdt32), $({base} + (ap_trampoline_start32 - ap_trampoline_start))",
    ".code32",
    "ap_trampoline_start32:",
    "mov $(ap_trampoline_gdt32_data - ap_trampoline_gdt32), %eax",
    "mov %eax, %ds",
    "mov %eax, %es",
    "mov %eax, %ss",
    "xor %eax, %eax",
    "mov %eax, %fs",
    "mov %eax, %gs",
    // Load CR3's low half; long mode is not on yet, so bit 63 waits for the 64-bit code.
    "mov {base} - 8, %eax",
    "mov %eax, %cr3",
    // Enable PAE.
    "mov %cr4, %eax",
    "or $(1 << 5), %eax",
    "mov %eax, %cr4",
    // Enable long mode in EFER.
    "mov $0xc0000080, %ecx",
    "rdmsr",
    "or $(1 << 8), %eax",
    "wrmsr",
    // Enable paging.
    "mov %cr0, %eax",
    "or $(1 << 31), %eax",
    "mov %eax, %cr0",
    "lgdt {base} + (ap_trampoline_gdt64_pointer - ap_trampoline_start)",
    "ljmp $(ap_trampoline_gdt64_code - ap_trampoline_gdt64), $({base} + (ap_trampoline_start64 - ap_trampoline_start))",
    ".code64",
    "ap_trampoline_start64:",
    "xor %eax, %eax",
    "mov %ax, %ss",
    "mov %ax, %ds",
    "mov %ax, %es",
    "mov %ax, %fs",
    "mov %ax, %gs",
    // Enable PCID when the kernel's CR3 value asks for it. The 32-bit load above could not carry
    // bit 63, so read the slot, not CR3.
    "mov $({base} - 8), %ebx",
    "mov (%rbx), %rax",
    "bt $63, %rax",
    "jnc 2f",
    "mov %cr4, %rax",
    "or $(1 << 17), %rax",
    "mov %rax, %cr4",
    "2:",
    "mov $({base} - 16), %ebx",
    "mov (%rbx), %rsp",
    "mov -16(%rbx), %rdi",
    "call *-8(%rbx)",
    "3:",
    "hlt",
    "jmp 3b",
    ".balign 16",
    "ap_trampoline_gdt32:",
    ".quad 0",
    "ap_trampoline_gdt32_code:",
    ".quad 0x00cf9a000000ffff",
    "ap_trampoline_gdt32_data:",
    ".quad 0x00cf92000000ffff",
    "ap_trampoline_gdt32_end:",
    "ap_trampoline_gdt32_pointer:",
    ".word ap_trampoline_gdt32_end - ap_trampoline_gdt32 - 1",
    ".long {base} + (ap_trampoline_gdt32 - ap_trampoline_start)",
    ".balign 16",
    "ap_trampoline_gdt64:",
    ".quad 0",
    "ap_trampoline_gdt64_code:",
    ".quad (1 << 43) | (1 << 44) | (1 << 47) | (1 << 53)",
    "ap_trampoline_gdt64_pointer:",
    ".word ap_trampoline_gdt64_pointer - ap_trampoline_gdt64 - 1",
    ".quad {base} + (ap_trampoline_gdt64 - ap_trampoline_start)",
    "ap_trampoline_end:",
    ".popsection",
    base = const BASE,
    options(att_syntax),
);

unsafe extern "C" {
    static ap_trampoline_start: u8;
    static ap_trampoline_end: u8;
}

pub struct StartTrampoline;

impl StartTrampoline {
    const CR3_OFFSET: isize = -8;
    const STACK_PTR_OFFSET: isize = -16;
    const CODE_POINTER_OFFSET: isize = -24;
    const ARG_OFFSET: isize = -32;

    pub unsafe fn new() -> Self {
        let mut handle = Self;

        handle.copy_binary();

        handle
    }

    pub fn with_stack(&mut self, stack: u64) -> &mut Self {
        unsafe {
            let stack_dst = self.base_ptr().offset(Self::STACK_PTR_OFFSET) as *mut u64;
            ptr::write_volatile(stack_dst, stack);
        }

        self
    }

    pub fn with_cr3(&mut self, cr3: u64) -> &mut Self {
        unsafe {
            let cr3_dst = self.base_ptr().offset(Self::CR3_OFFSET) as *mut u64;
            ptr::write_volatile(cr3_dst, cr3);
        }

        self
    }

    pub fn with_code(&mut self, code: u64) -> &mut Self {
        unsafe {
            let code_dst = self.base_ptr().offset(Self::CODE_POINTER_OFFSET) as *mut u64;
            ptr::write_volatile(code_dst, code);
        }

        self
    }

    pub fn with_arg(&mut self, arg: u64) -> &mut Self {
        unsafe {
            let arg_dst = self.base_ptr().offset(Self::ARG_OFFSET) as *mut u64;
            ptr::write_volatile(arg_dst, arg);
        }

        self
    }

    pub fn start_page(&self) -> u8 {
        (BASE >> 12) as u8
    }

    fn base_ptr(&self) -> *mut u8 {
        BASE as *mut u8
    }

    fn copy_binary(&mut self) {
        unsafe {
            let start = &raw const ap_trampoline_start;
            let end = &raw const ap_trampoline_end;
            ptr::copy(start, self.base_ptr(), end as usize - start as usize);
        }
    }
}
