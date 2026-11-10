//! Interrupt handling.

// Copyright 2021 Zhaofeng Li
// Copyright 2017 Philipp Oppermann
//
// Licensed under the MIT license <http://opensource.org/licenses/MIT>.
// See top-level LICENSE.

mod exception;
mod idt;

use core::arch::{asm, naked_asm};
use core::convert::{Into, TryFrom};

use crate::arch::Ring;

use crate::arch::spin_forever;
pub use exception::Exception;
use exception::EXCEPTION_MAX;
use idt::Idt;
use crate::machine;
use verified::arch::Registers;

/// The first vector after the exceptions. The IDT's interrupt array starts here.
pub const IRQ_OFFSET: usize = 32;

pub const IST_EXCEPTION: usize = 1;
pub const IST_IRQ: usize = 2;

/// The global IDT. Written only by `init` on CPU 0, before any core loads it; only read after that.
static mut GLOBAL_IDT: Idt = Idt::new();

#[repr(C)]
pub(crate) struct TrampolineMarker(());

macro_rules! wrap_interrupt_with_error_code {
    ($handler:path) => {{
        let _: unsafe extern "C" fn(&mut Registers) = $handler;

        /// Interrupt trampoline
        #[unsafe(naked)]
        unsafe extern "C" fn trampoline(_: TrampolineMarker) {
            // Figure 6-7. Stack Usage on Transfers to Interrupt and Exception Handling Routines

            // Here rsp is at the frame the CPU pushed: [rip][cs][rflags][rsp][ss]
            naked_asm!(
                "cli",
                "cld",
                "push rax",
                "push rdi",
                "push rsi",
                "push rdx",
                "push rcx",
                "push r8",
                "push r9",
                "push r10",
                "push r11",
                "push rbx",
                "push rbp",
                "push r12",
                "push r13",
                "push r14",
                "push r15",

                // fn handler(registers: &mut Registers)
                "mov rdi, rsp",
                "call {handler}",

                "pop r15",
                "pop r14",
                "pop r13",
                "pop r12",
                "pop rbp",
                "pop rbx",
                "pop r11",
                "pop r10",
                "pop r9",
                "pop r8",
                "pop rcx",
                "pop rdx",
                "pop rsi",
                "pop rdi",
                "pop rax",

                "add rsp, 8", // error_code

                "sti",
                "iretq",

                handler = sym $handler,
            );
        }

        trampoline
    }}
}

macro_rules! wrap_interrupt {
    ($handler:path) => {{
        let _: unsafe extern "C" fn(&mut Registers) = $handler;

        /// Interrupt trampoline
        #[unsafe(naked)]
        unsafe extern "C" fn trampoline(_: TrampolineMarker) {
            // Figure 6-7. Stack Usage on Transfers to Interrupt and Exception Handling Routines

            // Here rsp is at the frame the CPU pushed: [rip][cs][rflags][rsp][ss]
            naked_asm!(
                "cli",
                "cld",

                "push 0", // error_code

                "push rax",
                "push rdi",
                "push rsi",
                "push rdx",
                "push rcx",
                "push r8",
                "push r9",
                "push r10",
                "push r11",
                "push rbx",
                "push rbp",
                "push r12",
                "push r13",
                "push r14",
                "push r15",

                // fn handler(registers: &mut Registers)
                "mov rdi, rsp",
                "call {handler}",

                "pop r15",
                "pop r14",
                "pop r13",
                "pop r12",
                "pop rbp",
                "pop rbx",
                "pop r11",
                "pop r10",
                "pop r9",
                "pop r8",
                "pop rcx",
                "pop rdx",
                "pop rsi",
                "pop rdi",
                "pop rax",

                "add rsp, 8", // error_code

                "sti",
                "iretq",

                handler = sym $handler,
            );
        }

        trampoline
    }}
}

/// A handler function for an interrupt or an exception without error code.
pub type HandlerFunc = unsafe extern "C" fn(&mut PtRegs);

/// A handler function wrapped by the interrupt trampoline.
pub type TrampolineHandlerFunc = unsafe extern "C" fn(TrampolineMarker);

/// Whether the CPU was in ring 3 when the exception that saved these registers happened.
fn from_process(regs: &Registers) -> bool {
    regs.cs & 3 == 3
}

/// Stops the machine when a process raised the exception. No operation that delivers a fault to a
/// process is wired, so its thread can neither be told nor be removed.
unsafe fn stop_on_process_fault(what: &str, regs: &Registers) {
    if from_process(regs) {
        log::error!("CPU {}: {} in a process at {:#x}: stopping", crate::cpu::get_cpu_id(), what, regs.rip);
        crate::debugger::breakpoint(2);
        spin_forever();
    }
}

/// Stops the machine on an exception, which neither a process nor the kernel recovers from.
unsafe fn fatal(what: &str, regs: &Registers) -> ! {
    stop_on_process_fault(what, regs);
    log::error!("CPU {}: {}: {:#x?}", crate::cpu::get_cpu_id(), what, regs);
    crate::debugger::breakpoint(2);
    spin_forever();
}

macro_rules! process_exception {
    ($handler:ident, $what:literal) => {
        unsafe extern "C" fn $handler(regs: &mut Registers) {
            fatal($what, regs);
        }
    };
}

process_exception!(divide_by_zero, "Divide Error");
process_exception!(debug, "Debug Exception");
process_exception!(overflow, "Overflow");
process_exception!(bound_range_exceeded, "Bound Range Exceeded");
process_exception!(invalid_opcode, "Invalid Opcode");
process_exception!(device_not_available, "Device Not Available");
process_exception!(invalid_tss, "Invalid TSS");
process_exception!(segment_not_present, "Segment Not Present");
process_exception!(stack_segment_fault, "Stack Segment Fault");
process_exception!(x87_floating_point, "x87 Floating Point Exception");
process_exception!(alignment_check, "Alignment Check");
process_exception!(simd_floating_point, "SIMD Floating Point Exception");

/// Double Fault handler.
unsafe extern "C" fn double_fault(regs: &mut PtRegs) {
    log::error!("CPU {}: Double Fault: {:#x?}", crate::cpu::get_cpu_id(), regs);
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// Breakpoint handler.
unsafe extern "C" fn breakpoint(regs: &mut Registers) {
    log::warn!("CPU {}: Breakpoint: {:#x?}", crate::cpu::get_cpu_id(), regs);
    crate::debugger::breakpoint(2);
}

/// General Protection Fault handler.
unsafe extern "C" fn general_protection_fault(regs: &mut Registers) {
    stop_on_process_fault("General Protection Fault", regs);
    log::error!(
        "CPU {}: General Protection Fault (error code {:#b}): {:#x?}",
        crate::cpu::get_cpu_id(),
        regs.error_code,
        regs,
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// Page Fault handler.
unsafe extern "C" fn page_fault(regs: &mut Registers) {
    let address: u64;
    asm!("mov {}, cr2", out(reg) address);
    if from_process(regs) {
        log::error!("CPU {}: Page Fault in a process, address {:#x}", crate::cpu::get_cpu_id(), address);
    }
    stop_on_process_fault("Page Fault", regs);
    if crate::arch::write_protect::fixup(regs) {
        return;
    }
    log::info!("CPU {}: Page Fault (address {:#x}, error code {:?}): {:#x?}",
        crate::cpu::get_cpu_id(),
        address,
        regs.error_code,
        regs,
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// The timer's interrupt, which nothing arms the timer for: reported, and the core stops.
unsafe extern "C" fn timer(regs: &mut Registers) {
    log::error!(
        "CPU {}: stray timer interrupt, which nothing armed the timer for: {:#x?}",
        crate::cpu::get_cpu_id(),
        regs,
    );
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// Flush request from another CPU.
unsafe extern "C" fn flush_ipi(_regs: &mut Registers) {
    crate::flush::handle_ipi();
    machine::end_of_interrupt();
}

/// IOMMU fault handler.
unsafe extern "C" fn iommu_fault(regs: &mut Registers) {
    log::error!("CPU {}: IOMMU fault: {:#x?}",
        crate::cpu::get_cpu_id(),
        regs,
    );
    crate::machine::iommu_fault_dump().unwrap();
    crate::debugger::breakpoint(2);
    spin_forever();
}

/// An interrupt.
#[derive(Copy, Clone, Debug)]
pub enum Interrupt {
    /// An exception.
    Exception(Exception),

    /// An IRQ.
    Irq(usize),
}

impl From<Interrupt> for usize {
    fn from(interrupt: Interrupt) -> usize {
        match interrupt {
            Interrupt::Exception(ex) => ex.into(),
            Interrupt::Irq(num) => IRQ_OFFSET + num,
        }
    }
}

impl TryFrom<usize> for Interrupt {
    type Error = &'static str;

    fn try_from(num: usize) -> Result<Self, Self::Error> {
        match num {
            0..=EXCEPTION_MAX => TryFrom::try_from(num).map(Self::Exception),
            IRQ_OFFSET..=255 => Ok(Self::Irq(num)),
            _ => Err("Invalid interrupt line"),
        }
    }
}

/// Registers passed to the ISR.
#[repr(C)]
#[derive(Debug)]
pub struct PtRegs {
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
}

/// Initializes global interrupt controllers.
///
/// This should be called only once.
pub unsafe fn init() {
    machine::interrupt_init();

    // Exclusive: this is the only writer, and no core has loaded the IDT yet.
    let idt = &mut *&raw mut GLOBAL_IDT;
    idt.divide_by_zero.set_handler_fn(wrap_interrupt!(divide_by_zero));
    idt.debug.set_handler_fn(wrap_interrupt!(debug));
    idt.overflow.set_handler_fn(wrap_interrupt!(overflow));
    idt.bound_range_exceeded.set_handler_fn(wrap_interrupt!(bound_range_exceeded));
    idt.invalid_opcode.set_handler_fn(wrap_interrupt!(invalid_opcode));
    idt.device_not_available.set_handler_fn(wrap_interrupt!(device_not_available));
    idt.x87_floating_point.set_handler_fn(wrap_interrupt!(x87_floating_point));
    idt.simd_floating_point.set_handler_fn(wrap_interrupt!(simd_floating_point));
    idt.invalid_tss.set_handler_fn(wrap_interrupt_with_error_code!(invalid_tss));
    idt.segment_not_present.set_handler_fn(wrap_interrupt_with_error_code!(segment_not_present));
    idt.alignment_check.set_handler_fn(wrap_interrupt_with_error_code!(alignment_check));
    idt.breakpoint.set_handler_fn(wrap_interrupt!(breakpoint));
    idt.breakpoint.attributes.set_privilege_level(Ring::Ring3);
    idt.double_fault.set_handler_fn(double_fault);
    idt.stack_segment_fault.set_handler_fn(wrap_interrupt_with_error_code!(stack_segment_fault));
    idt.general_protection_fault
        .set_handler_fn(wrap_interrupt_with_error_code!(general_protection_fault));
    idt.page_fault.set_handler_fn(wrap_interrupt_with_error_code!(page_fault));

    idt.interrupts[machine::TIMER_VECTOR as usize - IRQ_OFFSET].set_handler_fn(wrap_interrupt!(timer));

    idt.interrupts[machine::IOMMU_FAULT_VECTOR as usize - IRQ_OFFSET].set_handler_fn(wrap_interrupt!(iommu_fault));

    idt.interrupts[machine::FLUSH_VECTOR as usize - IRQ_OFFSET].set_handler_fn(wrap_interrupt!(flush_ipi));
}

/// Initializes per-CPU interrupt controllers.
///
/// This should be called only once per CPU. Interrupts stay masked: a core takes them only where it
/// waits (`arch::wait`) or runs a process (`arch::enter_userspace`), so no handler that logs runs
/// while the core holds the console's lock.
pub unsafe fn init_cpu() {
    let cpu = crate::cpu::get_cpu_id();
    machine::interrupt_init_core(cpu);

    // Shared: init is done, so the IDT is only read from here on.
    (*&raw const GLOBAL_IDT).load();
}

/// Initializes an application processor's interrupts.
///
/// This should be called only once per CPU. Interrupts stay masked, as in [`init_cpu`].
pub unsafe fn init_ap() {
    machine::interrupt_init_core(crate::cpu::get_cpu_id());

    // Shared: init is done, so the IDT is only read from here on.
    (*&raw const GLOBAL_IDT).load();
}
