// SPDX-License-Identifier: MIT

//! The local APIC in xAPIC mode.
//!
//! The register map and the driver are vendored from `XAPIC` in the x86 crate (MIT); search for
//! `LOCAL MOD` for local modifications. The Interrupt Command Register is written from the AMD64
//! Architecture Programmer's Manual, Volume 2 (24593), §16.5, Figure 16-18.
//!
//! Table 10-1 Local APIC Register Address Map
//! the MMIO base values are found in this file.

use bit_field::BitField;

use super::msr::{rdmsr, wrmsr, APIC_BASE};

/// EOI register. Write-only.
pub const XAPIC_EOI: u32 = 0x0B0;

/// Spurious Interrupt Vector Register (SVR). Read/write. See Section 10.9 for reserved bits.
pub const XAPIC_SVR: u32 = 0x0F0;

/// Error Status Register (ESR). Read/write. See Section 10.5.3.
pub const XAPIC_ESR: u32 = 0x280;

/// Interrupt Command Register (ICR). Read/write. See Figure 10-28 for reserved bits
pub const XAPIC_ICR0: u32 = 0x300;

/// Interrupt Command Register (ICR). Read/write. See Figure 10-28 for reserved bits
pub const XAPIC_ICR1: u32 = 0x310;

/// LVT Timer register. Read/write. See Figure 10-8 for reserved bits.
pub const XAPIC_LVT_TIMER: u32 = 0x320;

/// Initial Count register (for Timer). Read/write.
pub const XAPIC_TIMER_INIT_COUNT: u32 = 0x380;

#[derive(Copy, Clone)]
#[allow(non_camel_case_types)]
enum ApicRegister {
    XAPIC_EOI = XAPIC_EOI as isize,
    XAPIC_SVR = XAPIC_SVR as isize,
    XAPIC_ESR = XAPIC_ESR as isize,
    XAPIC_ICR0 = XAPIC_ICR0 as isize,
    XAPIC_ICR1 = XAPIC_ICR1 as isize,
    XAPIC_LVT_TIMER = XAPIC_LVT_TIMER as isize,
    XAPIC_TIMER_INIT_COUNT = XAPIC_TIMER_INIT_COUNT as isize,
}

/// State for the XAPIC driver.
#[allow(clippy::upper_case_acronyms)]
pub struct XAPIC {
    /// The xAPIC register page. The same physical address on every core; each core's access reaches its own.
    mmio_region: *mut u32,
    /// Initial APIC Base register value.
    base: u64,
}

impl XAPIC {
    /// The local APIC at `mmio`, the register page `IA32_APIC_BASE` names.
    pub(crate) fn from_mmio(mmio: *mut u32) -> XAPIC {
        XAPIC { mmio_region: mmio, base: 0 }
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
        unsafe { core::ptr::read_volatile(self.mmio_region.add(index)) }
    }

    /// write a register in the MMIO region.
    fn write(&mut self, offset: ApicRegister, val: u32) {
        assert!(offset as usize % 4 == 0);
        let index = offset as usize / 4;
        unsafe { core::ptr::write_volatile(self.mmio_region.add(index), val) }
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

// LOCAL MOD
/// The LVT timer value that delivers `vector`, unmasked, in one-shot mode, from the value `lvt`
/// the register held. Bit 16 is the mask; bits 18:17 select the timer mode (Intel SDM Vol. 3A
/// §11.5.1, the local vector table): 00b one-shot, 01b periodic, 10b TSC-deadline.
fn one_shot_timer_lvt(mut lvt: u32, vector: u8) -> u32 {
    lvt &= !0xff;
    lvt |= vector as u32;
    lvt.set_bit(16, false);
    lvt.set_bits(17..19, 0b00);
    lvt
}

impl XAPIC {
    /// End Of Interrupt -- Acknowledge interrupt delivery.
    pub fn eoi(&mut self) {
        self.write(ApicRegister::XAPIC_EOI, 0);
    }

    /// Enable TSC timer.
    pub fn tsc_enable(&mut self, vector: u8) {
        let lvt = one_shot_timer_lvt(self.read(ApicRegister::XAPIC_LVT_TIMER), vector);

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

#[cfg(test)]
mod tests {
    use super::one_shot_timer_lvt;

    #[test]
    fn the_timer_is_one_shot_whatever_mode_firmware_left() {
        // Masked, TSC-deadline mode, vector 0x30.
        let lvt = one_shot_timer_lvt(0x0005_0030, 0xec);
        assert_eq!(lvt, 0x0000_00ec);
        let lvt = one_shot_timer_lvt(0xffff_ffff, 0x20);
        assert_eq!(lvt & (0b111 << 16), 0, "mask and timer mode clear");
        assert_eq!(lvt & 0xff, 0x20);
    }
}
