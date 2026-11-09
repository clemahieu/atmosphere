//! The local APIC in xAPIC mode.
//!
//! The register map and the driver are vendored from `XAPIC` in the x86 crate (MIT); search for
//! `LOCAL MOD` for local modifications. The Interrupt Command Register is written from the AMD64
//! Architecture Programmer's Manual, Volume 2 (24593), §16.5, Figure 16-18.
//!
//! Table 10-1 Local APIC Register Address Map
//! the MMIO base values are found in this file.

use bit_field::BitField;
use core::fmt;

use crate::arch::msr::{rdmsr, wrmsr, APIC_BASE};

/// Local APIC ID register. Read-only. See Section 10.12.5.1 for initial values.
pub const XAPIC_ID: u32 = 0x020;

/// Local APIC Version register. Read-only. Same version used in xAPIC mode and x2APIC mode.
pub const XAPIC_VERSION: u32 = 0x030;

/// Task Priority Register (TPR). Read/write. Bits 31:8 are reserved.
pub const XAPIC_TPR: u32 = 0x080;

/// Processor Priority Register (PPR). Read-only.
pub const XAPIC_PPR: u32 = 0x0A0;

/// EOI register. Write-only.
pub const XAPIC_EOI: u32 = 0x0B0;

/// Logical Destination Register (LDR). Read/write in xAPIC mode.
pub const XAPIC_LDR: u32 = 0x0D0;

/// Spurious Interrupt Vector Register (SVR). Read/write. See Section 10.9 for reserved bits.
pub const XAPIC_SVR: u32 = 0x0F0;

/// In-Service Register (ISR); bits 31:0. Read-only.
pub const XAPIC_ISR0: u32 = 0x100;

/// ISR bits 63:32. Read-only.
pub const XAPIC_ISR1: u32 = 0x110;

/// ISR bits 95:64. Read-only.
pub const XAPIC_ISR2: u32 = 0x120;

/// ISR bits 127:96. Read-only.
pub const XAPIC_ISR3: u32 = 0x130;

/// ISR bits 159:128. Read-only.
pub const XAPIC_ISR4: u32 = 0x140;

/// ISR bits 191:160. Read-only.
pub const XAPIC_ISR5: u32 = 0x150;

/// ISR bits 223:192. Read-only.
pub const XAPIC_ISR6: u32 = 0x160;

/// ISR bits 255:224. Read-only.
pub const XAPIC_ISR7: u32 = 0x170;

/// Trigger Mode Register (TMR); bits 31:0. Read-only.
pub const XAPIC_TMR0: u32 = 0x180;

/// TMR bits 63:32. Read-only.
pub const XAPIC_TMR1: u32 = 0x190;

/// TMR bits 95:64. Read-only.
pub const XAPIC_TMR2: u32 = 0x1A0;

/// TMR bits 127:96. Read-only.
pub const XAPIC_TMR3: u32 = 0x1B0;

/// TMR bits 159:128. Read-only.
pub const XAPIC_TMR4: u32 = 0x1C0;

/// TMR bits 191:160. Read-only.
pub const XAPIC_TMR5: u32 = 0x1D0;

/// TMR bits 223:192. Read-only.
pub const XAPIC_TMR6: u32 = 0x1E0;

/// TMR bits 255:224. Read-only.
pub const XAPIC_TMR7: u32 = 0x1F0;

/// Interrupt Request Register (IRR); bits 31:0. Read-only.
pub const XAPIC_IRR0: u32 = 0x200;

/// IRR bits 63:32. Read-only.
pub const XAPIC_IRR1: u32 = 0x210;

/// IRR bits 95:64. Read-only.
pub const XAPIC_IRR2: u32 = 0x220;

/// IRR bits 127:96. Read-only.
pub const XAPIC_IRR3: u32 = 0x230;

/// IRR bits 159:128. Read-only.
pub const XAPIC_IRR4: u32 = 0x240;

/// IRR bits 191:160. Read-only.
pub const XAPIC_IRR5: u32 = 0x250;

/// IRR bits 223:192. Read-only.
pub const XAPIC_IRR6: u32 = 0x260;

/// IRR bits 255:224. Read-only.
pub const XAPIC_IRR7: u32 = 0x270;

/// Error Status Register (ESR). Read/write. See Section 10.5.3.
pub const XAPIC_ESR: u32 = 0x280;

/// LVT CMCI register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_CMCI: u32 = 0x2F0;

/// Interrupt Command Register (ICR). Read/write. See Figure 10-28 for reserved bits
pub const XAPIC_ICR0: u32 = 0x300;

/// Interrupt Command Register (ICR). Read/write. See Figure 10-28 for reserved bits
pub const XAPIC_ICR1: u32 = 0x310;

/// LVT Timer register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_TIMER: u32 = 0x320;

/// LVT Thermal Sensor register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_THERMAL: u32 = 0x330;

/// LVT Performance Monitoring register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_PMI: u32 = 0x340;

/// LVT LINT0 register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_LINT0: u32 = 0x350;

/// LVT LINT1 register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_LINT1: u32 = 0x360;

/// LVT Error register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_ERROR: u32 = 0x370;

/// Initial Count register (for Timer). Read/write.
pub const XAPIC_TIMER_INIT_COUNT: u32 = 0x380;

/// Current Count register (for Timer). Read-only.
pub const XAPIC_TIMER_CURRENT_COUNT: u32 = 0x390;

/// Divide Configuration Register (DCR; for Timer). Read/write. See Figure 10-10 for reserved bits.
pub const XAPIC_TIMER_DIV_CONF: u32 = 0x3E0;

#[derive(Copy, Clone)]
#[allow(dead_code, non_camel_case_types)]
enum ApicRegister {
    XAPIC_ID = XAPIC_ID as isize,
    XAPIC_VERSION = XAPIC_VERSION as isize,
    XAPIC_TPR = XAPIC_TPR as isize,
    XAPIC_PPR = XAPIC_PPR as isize,
    XAPIC_EOI = XAPIC_EOI as isize,
    XAPIC_LDR = XAPIC_LDR as isize,
    XAPIC_SVR = XAPIC_SVR as isize,
    XAPIC_ISR0 = XAPIC_ISR0 as isize,
    XAPIC_ISR1 = XAPIC_ISR1 as isize,
    XAPIC_ISR2 = XAPIC_ISR2 as isize,
    XAPIC_ISR3 = XAPIC_ISR3 as isize,
    XAPIC_ISR4 = XAPIC_ISR4 as isize,
    XAPIC_ISR5 = XAPIC_ISR5 as isize,
    XAPIC_ISR6 = XAPIC_ISR6 as isize,
    XAPIC_ISR7 = XAPIC_ISR7 as isize,
    XAPIC_TMR0 = XAPIC_TMR0 as isize,
    XAPIC_TMR1 = XAPIC_TMR1 as isize,
    XAPIC_TMR2 = XAPIC_TMR2 as isize,
    XAPIC_TMR3 = XAPIC_TMR3 as isize,
    XAPIC_TMR4 = XAPIC_TMR4 as isize,
    XAPIC_TMR5 = XAPIC_TMR5 as isize,
    XAPIC_TMR6 = XAPIC_TMR6 as isize,
    XAPIC_TMR7 = XAPIC_TMR7 as isize,
    XAPIC_IRR0 = XAPIC_IRR0 as isize,
    XAPIC_IRR1 = XAPIC_IRR1 as isize,
    XAPIC_IRR2 = XAPIC_IRR2 as isize,
    XAPIC_IRR3 = XAPIC_IRR3 as isize,
    XAPIC_IRR4 = XAPIC_IRR4 as isize,
    XAPIC_IRR5 = XAPIC_IRR5 as isize,
    XAPIC_IRR6 = XAPIC_IRR6 as isize,
    XAPIC_IRR7 = XAPIC_IRR7 as isize,
    XAPIC_ESR = XAPIC_ESR as isize,
    XAPIC_LVT_CMCI = XAPIC_LVT_CMCI as isize,
    XAPIC_ICR0 = XAPIC_ICR0 as isize,
    XAPIC_ICR1 = XAPIC_ICR1 as isize,
    XAPIC_LVT_TIMER = XAPIC_LVT_TIMER as isize,
    XAPIC_LVT_THERMAL = XAPIC_LVT_THERMAL as isize,
    XAPIC_LVT_PMI = XAPIC_LVT_PMI as isize,
    XAPIC_LVT_LINT0 = XAPIC_LVT_LINT0 as isize,
    XAPIC_LVT_LINT1 = XAPIC_LVT_LINT1 as isize,
    XAPIC_LVT_ERROR = XAPIC_LVT_ERROR as isize,
    XAPIC_TIMER_INIT_COUNT = XAPIC_TIMER_INIT_COUNT as isize,
    XAPIC_TIMER_CURRENT_COUNT = XAPIC_TIMER_CURRENT_COUNT as isize,
    XAPIC_TIMER_DIV_CONF = XAPIC_TIMER_DIV_CONF as isize,
}

/// State for the XAPIC driver.
#[allow(clippy::clippy::upper_case_acronyms)]
pub struct XAPIC {
    /// Reference to the xAPCI region
    mmio_region: &'static mut [u32],
    /// Initial APIC Base register value.
    base: u64,
}

impl fmt::Debug for XAPIC {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("XAPIC")
            .field("XAPIC_ID", &self.read(ApicRegister::XAPIC_ID))
            .field("XAPIC_VERSION", &self.read(ApicRegister::XAPIC_VERSION))
            .field("XAPIC_TPR", &self.read(ApicRegister::XAPIC_TPR))
            .field("XAPIC_PPR", &self.read(ApicRegister::XAPIC_PPR))
            .field("XAPIC_EOI", &self.read(ApicRegister::XAPIC_EOI))
            .field("XAPIC_LDR", &self.read(ApicRegister::XAPIC_LDR))
            .field("XAPIC_SVR", &self.read(ApicRegister::XAPIC_SVR))
            .field("XAPIC_ISR0", &self.read(ApicRegister::XAPIC_ISR0))
            .field("XAPIC_ISR1", &self.read(ApicRegister::XAPIC_ISR1))
            .field("XAPIC_ISR2", &self.read(ApicRegister::XAPIC_ISR2))
            .field("XAPIC_ISR3", &self.read(ApicRegister::XAPIC_ISR3))
            .field("XAPIC_ISR4", &self.read(ApicRegister::XAPIC_ISR4))
            .field("XAPIC_ISR5", &self.read(ApicRegister::XAPIC_ISR5))
            .field("XAPIC_ISR6", &self.read(ApicRegister::XAPIC_ISR6))
            .field("XAPIC_ISR7", &self.read(ApicRegister::XAPIC_ISR7))
            .field("XAPIC_TMR0", &self.read(ApicRegister::XAPIC_TMR0))
            .field("XAPIC_TMR1", &self.read(ApicRegister::XAPIC_TMR1))
            .field("XAPIC_TMR2", &self.read(ApicRegister::XAPIC_TMR2))
            .field("XAPIC_TMR3", &self.read(ApicRegister::XAPIC_TMR3))
            .field("XAPIC_TMR4", &self.read(ApicRegister::XAPIC_TMR4))
            .field("XAPIC_TMR5", &self.read(ApicRegister::XAPIC_TMR5))
            .field("XAPIC_TMR6", &self.read(ApicRegister::XAPIC_TMR6))
            .field("XAPIC_TMR7", &self.read(ApicRegister::XAPIC_TMR7))
            .field("XAPIC_IRR0", &self.read(ApicRegister::XAPIC_IRR0))
            .field("XAPIC_IRR1", &self.read(ApicRegister::XAPIC_IRR1))
            .field("XAPIC_IRR2", &self.read(ApicRegister::XAPIC_IRR2))
            .field("XAPIC_IRR3", &self.read(ApicRegister::XAPIC_IRR3))
            .field("XAPIC_IRR4", &self.read(ApicRegister::XAPIC_IRR4))
            .field("XAPIC_IRR5", &self.read(ApicRegister::XAPIC_IRR5))
            .field("XAPIC_IRR6", &self.read(ApicRegister::XAPIC_IRR6))
            .field("XAPIC_IRR7", &self.read(ApicRegister::XAPIC_IRR7))
            .field("XAPIC_ESR", &self.read(ApicRegister::XAPIC_ESR))
            .field("XAPIC_LVT_CMCI", &self.read(ApicRegister::XAPIC_LVT_CMCI))
            .field("XAPIC_ICR0", &self.read(ApicRegister::XAPIC_ICR0))
            .field("XAPIC_ICR1", &self.read(ApicRegister::XAPIC_ICR1))
            .field("XAPIC_LVT_TIMER", &self.read(ApicRegister::XAPIC_LVT_TIMER))
            .field(
                "XAPIC_LVT_THERMAL",
                &self.read(ApicRegister::XAPIC_LVT_THERMAL),
            )
            .field("XAPIC_LVT_PMI", &self.read(ApicRegister::XAPIC_LVT_PMI))
            .field("XAPIC_LVT_LINT0", &self.read(ApicRegister::XAPIC_LVT_LINT0))
            .field("XAPIC_LVT_LINT1", &self.read(ApicRegister::XAPIC_LVT_LINT1))
            .field("XAPIC_LVT_ERROR", &self.read(ApicRegister::XAPIC_LVT_ERROR))
            .field(
                "XAPIC_TIMER_INIT_COUNT",
                &self.read(ApicRegister::XAPIC_TIMER_INIT_COUNT),
            )
            .field(
                "XAPIC_TIMER_CURRENT_COUNT",
                &self.read(ApicRegister::XAPIC_TIMER_CURRENT_COUNT),
            )
            .field(
                "XAPIC_TIMER_DIV_CONF",
                &self.read(ApicRegister::XAPIC_TIMER_DIV_CONF),
            )
            .finish()
    }
}

impl XAPIC {
    /// Create a new xAPIC object for the local CPU.
    ///
    /// Pass the xAPCI region which is at XXX unless you have
    /// relocated the region.
    pub fn new(apic_region: &'static mut [u32]) -> XAPIC {
        unsafe {
            XAPIC {
                mmio_region: apic_region,
                base: rdmsr(APIC_BASE),
            }
        }
    }

    /// Attach driver to the xAPIC (enables device).
    pub fn attach(&mut self) {
        // Enable
        unsafe {
            // Enable xAPIC globally
            self.base = rdmsr(APIC_BASE);
            self.base.set_bit(11, true);
            wrmsr(APIC_BASE, self.base);

            // Enable this XAPIC (set bit 8, spurious IRQ vector 15)
            let svr: u32 = 1 << 8 | 15;
            self.write(ApicRegister::XAPIC_SVR, svr);
        }
    }

    /// Read a register from the MMIO region.
    fn read(&self, offset: ApicRegister) -> u32 {
        assert!(offset as usize % 4 == 0);
        let index = offset as usize / 4;
        unsafe { core::ptr::read_volatile(&self.mmio_region[index]) }
    }

    /// write a register in the MMIO region.
    fn write(&mut self, offset: ApicRegister, val: u32) {
        assert!(offset as usize % 4 == 0);
        let index = offset as usize / 4;
        unsafe { core::ptr::write_volatile(&mut self.mmio_region[index], val) }
    }

    /// Set TSC one-shot value.
    ///
    /// LOCAL MOD
    pub fn tsc_set_oneshot(&mut self, value: u32) {
        self.write(ApicRegister::XAPIC_TIMER_INIT_COUNT, value);
    }
}

/// The message type of an interprocessor interrupt, ICR bits 10:8. APM 2 §16.5.
#[derive(Clone, Copy)]
#[repr(u64)]
enum MessageType {
    Fixed = 0b000,
    Init = 0b101,
    Startup = 0b110,
}

/// The level of an interprocessor interrupt, ICR bit 14. APM 2 §16.5.
#[derive(Clone, Copy)]
#[repr(u64)]
enum Level {
    Assert = 1,
}

/// The trigger mode of an interprocessor interrupt, ICR bit 15. APM 2 §16.5.
#[derive(Clone, Copy)]
#[repr(u64)]
enum TriggerMode {
    Edge = 0,
    Level = 1,
}

/// An Interrupt Command Register value that names its destination: the destination APIC ID in
/// bits 63:56, destination shorthand 00b in bits 19:18, physical destination mode (bit 11 clear),
/// and the read-only delivery status and remote read status written as 0. APM 2 §16.5, Figure
/// 16-18; Table 16-4 lists the valid combinations of message type, trigger mode and level.
#[derive(Clone, Copy)]
pub struct Icr(u64);

impl Icr {
    const fn new(
        destination: u8,
        message_type: MessageType,
        level: Level,
        trigger_mode: TriggerMode,
        vector: u8,
    ) -> Icr {
        Icr((destination as u64) << 56
            | (trigger_mode as u64) << 15
            | (level as u64) << 14
            | (message_type as u64) << 8
            | vector as u64)
    }

    /// Interrupts the local APIC `destination` at `vector`.
    pub const fn fixed(destination: u8, vector: u8) -> Icr {
        Icr::new(destination, MessageType::Fixed, Level::Assert, TriggerMode::Edge, vector)
    }

    /// Puts the core of the local APIC `destination` in the INIT state, to await a STARTUP.
    pub const fn init(destination: u8) -> Icr {
        Icr::new(destination, MessageType::Init, Level::Assert, TriggerMode::Level, 0)
    }

    /// Starts the core of the local APIC `destination` in real mode at physical page `start_page`.
    pub const fn startup(destination: u8, start_page: u8) -> Icr {
        Icr::new(destination, MessageType::Startup, Level::Assert, TriggerMode::Edge, start_page)
    }

    /// Bits 31:0, the write to which sends the interrupt.
    const fn lower(self) -> u32 {
        self.0 as u32
    }

    /// Bits 63:32.
    const fn upper(self) -> u32 {
        (self.0 >> 32) as u32
    }
}

impl XAPIC {
    /// Read local APIC ID.
    pub fn id(&self) -> u32 {
        self.read(ApicRegister::XAPIC_ID)
    }

    pub fn logical_id(&self) -> u32 {
        self.read(ApicRegister::XAPIC_LDR)
    }

    /// End Of Interrupt -- Acknowledge interrupt delivery.
    pub fn eoi(&mut self) {
        self.write(ApicRegister::XAPIC_EOI, 0);
    }

    /// Enable TSC timer.
    pub fn tsc_enable(&mut self, vector: u8) {
        let mut lvt: u32 = self.read(ApicRegister::XAPIC_LVT_TIMER);
        lvt &= !0xff;
        lvt |= vector as u32;

        lvt.set_bit(16, false);
        lvt.set_bit(17, false);

        // LOCAL MOD
        // > Bits 18:17 selects the timer mode (see Section 11.5.4)
        // > (00b) one-shot mode using a count-down value
        // > (01b) periodic mode reloading a count-down value
        // > (10b) TSC-Deadline mode using absolute target value in TSC_DEADLINE MSR
        lvt.set_bits(17..18, 0b00); // One-shot

        // Firmware may leave the timer counting: OVMF does after ExitBootServices. A zero initial
        // count stops it, so the unmasked timer fires only once set_timer arms it.
        self.write(ApicRegister::XAPIC_TIMER_INIT_COUNT, 0);
        self.write(ApicRegister::XAPIC_LVT_TIMER, lvt);
    }

    /// Send a INIT IPI to a core.
    pub unsafe fn ipi_init(&mut self, core: u8) {
        self.send_ipi(Icr::init(core));
    }

    /// Send a STARTUP IPI to a core.
    pub unsafe fn ipi_startup(&mut self, core: u8, start_page: u8) {
        self.send_ipi(Icr::startup(core, start_page));
    }

    /// Send a generic IPI.
    pub unsafe fn send_ipi(&mut self, icr: Icr) {
        self.write(ApicRegister::XAPIC_ESR, 0);
        self.write(ApicRegister::XAPIC_ESR, 0);

        // 10.6 ISSUING INTERPROCESSOR INTERRUPTS
        self.write(ApicRegister::XAPIC_ICR1, icr.upper());
        self.write(ApicRegister::XAPIC_ICR0, icr.lower());

        loop {
            let icr = self.read(ApicRegister::XAPIC_ICR0);
            if (icr >> 12 & 0x1) == 0 {
                break;
            }
            if self.read(ApicRegister::XAPIC_ESR) > 0 {
                break;
            }
        }
    }
}

// The encodings the x86 crate's Icr::for_xapic produced for each IPI the kernel sends.
const _: () = assert!(Icr::init(3).0 == 0x0300_0000_0000_c500);
const _: () = assert!(Icr::startup(1, 0x08).0 == 0x0100_0000_0000_4608);
const _: () = assert!(Icr::fixed(1, 34).0 == 0x0100_0000_0000_4022);
