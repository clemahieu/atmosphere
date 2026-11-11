// SPDX-License-Identifier: MIT

//! AArch64 as UEFI leaves it on QEMU virt: EL1 with the VMSAv8-64 stage-1 tables of the 4K granule,
//! and the PL011.
//!
//! What is arithmetic is here, where the host's tests build it; what is an instruction is in
//! `instructions`, which only the target builds.

use core::fmt::{Result as FmtResult, Write};

use crate::memory::Leaf;

#[cfg(target_arch = "aarch64")]
mod instructions;
#[cfg(target_arch = "aarch64")]
pub use instructions::*;

/// The serial device the loader logs to.
pub type Serial = Pl011;

/// The PL011 the firmware's console is on, at the address QEMU virt's device tree gives it: node
/// pl011@9000000, the machine's stdout-path.
const PL011: usize = 0x0900_0000;

/// UARTDR, the data register: a write pushes the byte onto the transmit FIFO (DDI 0183G 3.3.1).
const PL011_DATA: usize = 0x000;

/// UARTFR, the flag register; bit 5, TXFF, says the transmit FIFO is full (DDI 0183G 3.3.3).
const PL011_FLAG: usize = 0x018;
const PL011_TRANSMIT_FULL: u32 = 1 << 5;

/// The machine's PL011.
pub const fn serial() -> Serial {
    Pl011 { base: PL011 }
}

/// A PL011 UART, by the address of its registers.
pub struct Pl011 {
    base: usize,
}

impl Pl011 {
    /// The firmware leaves the UART enabled at its line settings, and the loader keeps them.
    pub fn init(&self) {}

    /// Sends a byte, and a carriage return ahead of a line feed.
    pub fn putc(&mut self, c: u8) {
        if c == b'\n' {
            self.send(b'\r');
        }
        self.send(c);
    }

    fn send(&mut self, byte: u8) {
        // The registers of the device `serial` names, or of the block a test built.
        unsafe {
            while read_register(self.base + PL011_FLAG) & PL011_TRANSMIT_FULL != 0 {}
            write_register(self.base + PL011_DATA, byte as u32);
        }
    }
}

impl Write for Pl011 {
    fn write_str(&mut self, s: &str) -> FmtResult {
        for byte in s.as_bytes() {
            self.putc(*byte);
        }
        Ok(())
    }
}

/// Reads the 32-bit register at `address`; in the host's tests, memory another thread may write.
#[cfg(not(target_arch = "aarch64"))]
unsafe fn read_register(address: usize) -> u32 {
    use core::sync::atomic::{AtomicU32, Ordering};
    AtomicU32::from_ptr(address as *mut u32).load(Ordering::Relaxed)
}

/// Writes the 32-bit register at `address`.
#[cfg(not(target_arch = "aarch64"))]
unsafe fn write_register(address: usize, value: u32) {
    use core::sync::atomic::{AtomicU32, Ordering};
    AtomicU32::from_ptr(address as *mut u32).store(value, Ordering::Relaxed)
}

// The system-register values `activate` writes, Arm ARM DDI 0487 M.d D24.2: the state
// design/arch-module/ item 1 relies on, which the kernel finds in place.

/// ID_AA64MMFR0_EL1.PARange, bits 3:0: the physical address size, in TCR_EL1.IPS's encoding. 0b0101
/// is 48 bits, the most a descriptor of this format holds.
const PA_RANGE: u64 = 0b1111;
const PA_RANGE_48_BITS: u64 = 0b0101;

/// ID_AA64MMFR0_EL1.TGran4, bits 31:28: 0b1111 where the core has no 4K granule.
const TGRAN4_SHIFT: u32 = 28;
const TGRAN4_NONE: u64 = 0b1111;

/// ID_AA64MMFR1_EL1.HAFDBS, bits 3:0: from 0b0001 the walker sets the access flag, and from 0b0010
/// it keeps the dirty state as well.
const HAFDBS: u64 = 0b1111;

/// TCR_EL1.T0SZ, bits 5:0, and T1SZ, bits 21:16: 64 less the bits of a virtual address, 48.
const TCR_T0SZ_48_BITS: u64 = 16;
const TCR_T1SZ_48_BITS: u64 = 16 << 16;

/// TCR_EL1.IRGN0, bits 9:8, and ORGN0, bits 11:10: the walker reads the tables under TTBR0_EL1 as
/// write-back cacheable memory, 0b01 in each.
const TCR_IRGN0_WRITE_BACK: u64 = 0b01 << 8;
const TCR_ORGN0_WRITE_BACK: u64 = 0b01 << 10;

/// TCR_EL1.SH0, bits 13:12: and as Inner Shareable memory, 0b11. TG0, bits 15:14, stays 0b00, the
/// 4K granule.
const TCR_SH0_INNER: u64 = 0b11 << 12;

/// TCR_EL1.EPD1, bit 23: no walk through TTBR1_EL1, so an address in the upper half faults. TG1,
/// bits 31:30, has no encoding of zero; it holds the 4K granule, 0b10.
const TCR_EPD1: u64 = 1 << 23;
const TCR_TG1_4K: u64 = 0b10 << 30;

/// TCR_EL1.IPS, bits 34:32: the size of the physical addresses the tables give.
const TCR_IPS_SHIFT: u32 = 32;

/// TCR_EL1.HA, bit 39, and HD, bit 40: the walker sets the access flag, and keeps the dirty state.
const TCR_HA: u64 = 1 << 39;
const TCR_HD: u64 = 1 << 40;

/// TCR_EL1 for a core with these ID registers: one four-level walk of the 4K granule through
/// TTBR0_EL1 over 48-bit addresses, physical addresses of the core's size up to 48 bits, and the
/// walker keeping the access flag and the dirty state where the core can. HPD0, bit 41, stays
/// clear, so a table descriptor's permission bits bind what is below it; so do TBI0, EPD0, A1 and
/// AS.
pub fn translation_control(id_aa64mmfr0: u64, id_aa64mmfr1: u64) -> u64 {
    assert!(
        id_aa64mmfr0 >> TGRAN4_SHIFT & 0b1111 != TGRAN4_NONE,
        "this core has no 4K granule: ID_AA64MMFR0_EL1 {:#x}",
        id_aa64mmfr0
    );
    let physical = core::cmp::min(id_aa64mmfr0 & PA_RANGE, PA_RANGE_48_BITS);
    let status = match id_aa64mmfr1 & HAFDBS {
        0 => 0,
        1 => TCR_HA,
        _ => TCR_HA | TCR_HD,
    };
    TCR_T0SZ_48_BITS
        | TCR_IRGN0_WRITE_BACK
        | TCR_ORGN0_WRITE_BACK
        | TCR_SH0_INNER
        | TCR_T1SZ_48_BITS
        | TCR_EPD1
        | TCR_TG1_4K
        | physical << TCR_IPS_SHIFT
        | status
}

/// MAIR_EL1, what a leaf's attribute index names (D8.6.1): Attr0 is Normal memory, write-back
/// non-transient in the inner and the outer cache, 0xff; Attr1 is Device-nGnRnE, 0x00.
pub const MEMORY_ATTRIBUTES: u64 = 0xff << (8 * ATTR_NORMAL) | 0x00 << (8 * ATTR_DEVICE);

/// SCTLR_EL1.M, bit 0: stage 1 translation on.
const SCTLR_M: u64 = 1 << 0;

/// SCTLR_EL1.C, bit 2, and I, bit 12: data and instruction accesses may be cached.
const SCTLR_C: u64 = 1 << 2;
const SCTLR_I: u64 = 1 << 12;

/// SCTLR_EL1.WXN, bit 19: a writable page is never executed. Every leaf the loader writes is
/// writable, its own code's among them.
const SCTLR_WXN: u64 = 1 << 19;

/// SCTLR_EL1 for the loader's tables, from the value the firmware left: translation and the caches
/// on, and WXN off.
pub fn system_control(firmware: u64) -> u64 {
    (firmware | SCTLR_M | SCTLR_C | SCTLR_I) & !SCTLR_WXN
}

/// TLBI VAE1's argument for the page at `vaddr` (C5.5.59): VA[55:12] in bits 43:0. The ASID, bits
/// 63:48, is 0, which the loader's root table is live under, and TTL, bits 47:44, is 0, a leaf of
/// any level.
pub fn flush_argument(vaddr: u64) -> u64 {
    vaddr >> 12 & ((1 << 44) - 1)
}

// What the fetch of an instruction sees of a write, Arm ARM DDI 0487 M.d B2.7.4.2, by the cache
// type register, CTR_EL0 (D24.2.41).

/// CTR_EL0.IminLine, bits 3:0, and DminLine, bits 19:16: log2 of the 4-byte words in the smallest
/// line of the instruction caches, and of the data caches, that maintenance by address reaches.
const CTR_LINE: u64 = 0b1111;
const CTR_DMINLINE_SHIFT: u32 = 16;

/// CTR_EL0.IDC, bit 28: the fetch needs no clean of the data cache to see a write.
const CTR_IDC: u64 = 1 << 28;

/// CTR_EL0.DIC, bit 29: nor an invalidation of the instruction cache.
const CTR_DIC: u64 = 1 << 29;

/// What a core asks for before its fetch sees a write: the bytes of the line to clean the data
/// cache by, and of the line to invalidate the instruction cache by, each absent where the core
/// needs no such step.
#[derive(Debug, PartialEq, Eq)]
pub struct Coherence {
    pub clean: Option<u64>,
    pub invalidate: Option<u64>,
}

/// What the core whose CTR_EL0 is `cache_type` asks for.
pub fn coherence(cache_type: u64) -> Coherence {
    let line = |shift: u32| 4 << (cache_type >> shift & CTR_LINE);
    Coherence {
        clean: (cache_type & CTR_IDC == 0).then(|| line(CTR_DMINLINE_SHIFT)),
        invalidate: (cache_type & CTR_DIC == 0).then(|| line(0)),
    }
}

/// The address of every `line`-byte cache line that holds a byte of `start..end`, which holds one
/// at least: an operation by address reaches the naturally aligned line its address is in
/// (D7.5.9.4).
pub fn lines(start: u64, end: u64, line: u64) -> impl Iterator<Item = u64> {
    assert!(line.is_power_of_two(), "a cache line of {} bytes", line);
    assert!(start < end, "no byte in {:#x}-{:#x}", start, end);
    (start & !(line - 1)..end).step_by(line as usize)
}

/// Where QEMU virt's RAM starts: the lowest address in the memory map its firmware reports. What is
/// below is the machine's devices.
const RAM_START: u64 = 0x4000_0000;

/// Whether the 2M frame at `paddr` is device memory in the identity map: every frame below the RAM.
pub fn device(paddr: u64) -> bool {
    paddr < RAM_START
}

// The descriptor the walk writes, Arm ARM DDI 0487 M.d D8.3.1, in the bits the kernel's decoders in
// kernel/verified/arch/aarch64.rs read. design/arch-module/.

/// Valid descriptor, bit 0.
const VALID: u64 = 1 << 0;

/// Bit 1: a table descriptor above the last level and a page descriptor at it; a valid descriptor
/// above the last level with it clear is a block (Tables D8-50 and D8-52).
const TYPE: u64 = 1 << 1;

/// The next table's address or a page's frame, bits 47:12. A 2M block's frame is bits 47:21, and
/// the bits under it are reserved, zero.
const ADDRESS: u64 = 0x0000_ffff_ffff_f000;

/// AttrIndx[2:0], bits 4:2 of a block or page descriptor: the field of MAIR_EL1 that says what
/// memory the frame is (D8.6.1). Index 0 is Normal write-back memory, as the kernel's leaves have
/// it, and index 1 is Device memory.
const ATTR_INDEX_SHIFT: u32 = 2;
const ATTR_INDEX: u64 = 0b111 << ATTR_INDEX_SHIFT;
const ATTR_NORMAL: u64 = 0;
const ATTR_DEVICE: u64 = 1;

/// AP[1], bit 6 of a block or page descriptor: EL0 may read and write (D8.4.1.2.1).
const AP_EL0: u64 = 1 << 6;

/// SH[1:0], bits 9:8 of a block or page descriptor (D8.6.2). Normal memory is Inner Shareable,
/// 0b11. Device memory is Outer Shareable whatever the field holds, and holds that, 0b10.
const SH_INNER: u64 = 0b11 << 8;
const SH_OUTER: u64 = 0b10 << 8;

/// AF, bit 10 of a block or page descriptor: the access flag (D8.5.1). Set, so no first access
/// faults where the walker does not set it.
const AF: u64 = 1 << 10;

/// nG, bit 11 of a block or page descriptor: cached under the current ASID only, as every leaf the
/// kernel writes is.
const NG: u64 = 1 << 11;

/// DBM, bit 51 of a block or page descriptor: the kernel's mark of a writable leaf, whose AP[2],
/// bit 7, is then its dirty state (D8.5.2). The loader leaves AP[2] clear, the writable-dirty
/// state: no first write faults where the walker does not clear it, and the kernel reads the frame
/// as written to, which the loader's own writes make it.
const DBM: u64 = 1 << 51;

/// PXN, bit 53 of a block or page descriptor: no execution at EL1 (D8.4.1.2.3).
const PXN: u64 = 1 << 53;

/// UXN, bit 54 of a block or page descriptor: no execution at EL0 (D8.4.1.2.3).
const UXN: u64 = 1 << 54;

/// UXNTable, bit 60 of a table descriptor: every leaf below it is UXN (D8.4.1.2.5).
const TABLE_UXN: u64 = 1 << 60;

/// APTable[0], bit 61 of a table descriptor: no EL0 access below it (Table D8-64).
const TABLE_AP_NO_EL0: u64 = 1 << 61;

/// A translation-table descriptor, at any of the four levels.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Entry(u64);

impl Entry {
    /// The entry that maps nothing.
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Names the table at `address`. `user` lets user mode through to what the table maps; without
    /// it EL0 neither reads nor executes anything below, as the kernel's encoder writes an entry
    /// that is not user.
    pub fn table(address: u64, user: bool) -> Self {
        assert!(address & !ADDRESS == 0, "{:#x} is outside the descriptor's address field", address);
        let el0 = if user { 0 } else { TABLE_AP_NO_EL0 | TABLE_UXN };
        Self(VALID | TYPE | address | el0)
    }

    /// Maps the writable frame at `paddr`, of `leaf`'s size. A user frame is EL0's to execute and
    /// any other EL1's, never both. `cache_disable` makes the frame device memory, which neither
    /// executes: where Device memory is not execute-never the core may fetch from it speculatively,
    /// and a read changes a device's state (D8.4.4).
    pub fn leaf(paddr: u64, leaf: Leaf, user: bool, cache_disable: bool) -> Self {
        assert!(
            paddr & !(ADDRESS & !(leaf.size() - 1)) == 0,
            "{:#x} is outside the descriptor's address field",
            paddr
        );
        let kind = match leaf {
            Leaf::Small => TYPE,
            Leaf::Large => 0,
        };
        let memory = if cache_disable {
            ATTR_DEVICE << ATTR_INDEX_SHIFT | SH_OUTER
        } else {
            ATTR_NORMAL << ATTR_INDEX_SHIFT | SH_INNER
        };
        let access = if user { AP_EL0 } else { 0 };
        let execute_never = match (cache_disable, user) {
            (true, _) => PXN | UXN,
            (false, true) => PXN,
            (false, false) => UXN,
        };
        Self(VALID | kind | paddr | memory | AF | NG | DBM | access | execute_never)
    }

    pub fn present(&self) -> bool {
        self.0 & VALID != 0
    }

    /// Whether a present entry above the last level maps a frame itself, where it would otherwise
    /// name the next table.
    pub fn large(&self) -> bool {
        self.0 & TYPE == 0
    }

    /// The table a table entry names, or the frame a leaf maps.
    pub fn address(&self) -> u64 {
        self.0 & ADDRESS
    }

    /// Whether a leaf lets user mode reach its frame.
    pub fn user(&self) -> bool {
        self.0 & AP_EL0 != 0
    }

    /// Whether a leaf maps its frame as device memory.
    pub fn cache_disable(&self) -> bool {
        (self.0 & ATTR_INDEX) >> ATTR_INDEX_SHIFT == ATTR_DEVICE
    }
}

#[cfg(test)]
mod tests {
    use core::sync::atomic::{AtomicU32, Ordering};

    use super::*;

    /// Bit `n` of a descriptor, by its number in the manual's tables D8-50 and D8-52.
    const fn bit(n: u32) -> u64 {
        1 << n
    }

    const FRAME: u64 = 0x0000_8765_4320_0000;

    #[test]
    fn the_empty_entry_is_the_invalid_descriptor() {
        assert_eq!(Entry::empty().0, 0);
        assert!(!Entry::empty().present());
    }

    #[test]
    fn a_table_descriptor_holds_table_d8_50_s_fields() {
        // [0] valid, [1] table, [47:12] the next table. [59] PXNTable and [62] APTable[1] stay
        // clear: what the table maps may be executed at EL1 and written.
        let user = Entry::table(0x0000_ffff_ffff_f000, true);
        assert_eq!(user.0, bit(0) | bit(1) | 0x0000_ffff_ffff_f000);
        // [60] UXNTable and [61] APTable[0]: EL0 neither executes nor reads below it.
        let kernel = Entry::table(FRAME, false);
        assert_eq!(kernel.0, bit(0) | bit(1) | FRAME | bit(60) | bit(61));
        for entry in [user, kernel] {
            assert!(entry.present());
            assert!(!entry.large());
        }
        assert_eq!(user.address(), 0x0000_ffff_ffff_f000);
        assert_eq!(kernel.address(), FRAME);
    }

    /// What every leaf holds: [0] valid, [10] the access flag, [11] nG and [51] DBM, with [7] AP[2]
    /// clear beside it, the writable-dirty state.
    const LEAF: u64 = bit(0) | bit(10) | bit(11) | bit(51);
    /// [9:8] SH: Inner Shareable is 0b11 and Outer Shareable 0b10.
    const INNER_SHAREABLE: u64 = bit(9) | bit(8);
    const OUTER_SHAREABLE: u64 = bit(9);

    #[test]
    fn a_page_descriptor_holds_table_d8_52_s_fields() {
        // [1] page, [47:12] the frame, [4:2] AttrIndx 0, [54] UXN and [6] AP[1] clear: EL1 alone
        // reads, writes and executes it.
        let kernel = Entry::leaf(FRAME, Leaf::Small, false, false);
        assert_eq!(kernel.0, LEAF | bit(1) | FRAME | INNER_SHAREABLE | bit(54));
        // [6] AP[1]: EL0 reads and writes it. [53] PXN, and UXN clear: EL0 alone executes it.
        let user = Entry::leaf(FRAME, Leaf::Small, true, false);
        assert_eq!(user.0, LEAF | bit(1) | FRAME | INNER_SHAREABLE | bit(6) | bit(53));
        // [4:2] AttrIndx 1, device memory, which no exception level executes: [53] PXN and [54] UXN
        // both, whether or not [6] AP[1] lets EL0 read and write it.
        let device = Entry::leaf(FRAME, Leaf::Small, false, true);
        assert_eq!(device.0, LEAF | bit(1) | FRAME | OUTER_SHAREABLE | bit(2) | bit(53) | bit(54));
        let user_device = Entry::leaf(FRAME, Leaf::Small, true, true);
        assert_eq!(user_device.0, device.0 | bit(6));

        for (entry, is_user, is_device) in
            [(kernel, false, false), (user, true, false), (device, false, true), (user_device, true, true)]
        {
            assert!(entry.present());
            assert_eq!(entry.address(), FRAME);
            assert_eq!(entry.user(), is_user);
            assert_eq!(entry.cache_disable(), is_device);
        }
    }

    #[test]
    fn a_device_leaf_is_execute_never_at_both_exception_levels() {
        // [53] PXN and [54] UXN. Device memory takes both, or the core may fetch from it
        // speculatively (D8.4.4); Normal memory keeps the one that is not its own level's.
        const EXECUTE_NEVER: u64 = bit(53) | bit(54);
        for leaf in [Leaf::Small, Leaf::Large] {
            for user in [false, true] {
                let device = Entry::leaf(FRAME, leaf, user, true);
                assert_eq!(device.0 & EXECUTE_NEVER, EXECUTE_NEVER, "user {user}");
                let normal = Entry::leaf(FRAME, leaf, user, false);
                assert_eq!(normal.0 & EXECUTE_NEVER, if user { bit(53) } else { bit(54) }, "user {user}");
            }
        }
    }

    #[test]
    fn a_block_descriptor_differs_from_a_page_s_in_bit_1() {
        for (user, device) in [(false, false), (true, false), (false, true), (true, true)] {
            let block = Entry::leaf(FRAME, Leaf::Large, user, device);
            let page = Entry::leaf(FRAME, Leaf::Small, user, device);
            assert_eq!(block.0, page.0 & !bit(1));
            assert!(block.present());
            assert!(block.large());
            assert_eq!(block.address(), FRAME);
            assert_eq!(block.user(), user);
            assert_eq!(block.cache_disable(), device);
        }
    }

    /// A PL011's register block in host memory, every register holding `fill`.
    fn registers(fill: u32) -> [AtomicU32; 8] {
        core::array::from_fn(|_| AtomicU32::new(fill))
    }

    fn pl011(registers: &[AtomicU32; 8]) -> Pl011 {
        Pl011 { base: registers.as_ptr() as usize }
    }

    /// The registers by their offsets in the manual's Table 3-1: UARTDR at 0x000, UARTFR at 0x018.
    const DATA: usize = 0x000 / 4;
    const FLAG: usize = 0x018 / 4;

    #[test]
    fn the_pl011_writes_a_byte_to_its_data_register_alone() {
        // Every flag set but [5] TXFF: the transmitter has room.
        let registers = registers(!(1 << 5));
        pl011(&registers).putc(b'a');
        for (index, register) in registers.iter().enumerate() {
            let expected = if index == DATA { b'a' as u32 } else { !(1 << 5) };
            assert_eq!(register.load(Ordering::Relaxed), expected, "register {index}");
        }
    }

    #[test]
    fn the_pl011_writes_a_string_s_bytes_in_order() {
        let registers = registers(0);
        let mut serial = pl011(&registers);
        serial.write_str("ab").unwrap();
        assert_eq!(registers[DATA].load(Ordering::Relaxed), b'b' as u32);
        // A line feed goes out after the carriage return it gets.
        serial.write_str("c\n").unwrap();
        assert_eq!(registers[DATA].load(Ordering::Relaxed), b'\n' as u32);
        serial.init();
        assert_eq!(registers[DATA].load(Ordering::Relaxed), b'\n' as u32);
    }

    #[test]
    fn the_pl011_waits_while_its_transmitter_is_full() {
        let registers = registers(0);
        registers[FLAG].store(1 << 5, Ordering::Relaxed);
        std::thread::scope(|scope| {
            let writer = scope.spawn(|| pl011(&registers).putc(b'z'));
            std::thread::sleep(std::time::Duration::from_millis(50));
            assert!(!writer.is_finished());
            assert_eq!(registers[DATA].load(Ordering::Relaxed), 0);
            registers[FLAG].store(0, Ordering::Relaxed);
            writer.join().unwrap();
        });
        assert_eq!(registers[DATA].load(Ordering::Relaxed), b'z' as u32);
    }

    /// TCR_EL1 for a core whose ID registers are all zero: [5:0] T0SZ 16, [9:8] IRGN0 and [11:10]
    /// ORGN0 0b01, write-back, [13:12] SH0 0b11, Inner Shareable, [21:16] T1SZ 16, [23] EPD1 and
    /// [31:30] TG1 0b10, the 4K granule. Clear: [7] EPD0, [15:14] TG0, the 4K granule, [22] A1,
    /// [34:32] IPS, 32 bits, [36] AS, [37] TBI0, [39] HA, [40] HD and [41] HPD0.
    const TCR: u64 = 16 | bit(8) | bit(10) | bit(12) | bit(13) | 16 << 16 | bit(23) | bit(31);

    #[test]
    fn the_translation_control_holds_tcr_el1_s_fields() {
        assert_eq!(translation_control(0, 0), TCR);
    }

    #[test]
    fn the_physical_size_is_the_core_s_up_to_48_bits() {
        // ID_AA64MMFR0_EL1 [3:0] PARange goes to [34:32] IPS: 0b0010 is 40 bits and 0b0101 is 48.
        assert_eq!(translation_control(0b0010, 0), TCR | 0b010 << 32);
        assert_eq!(translation_control(0b0101, 0), TCR | 0b101 << 32);
        // 0b0110 is 52 bits, which a descriptor of this format does not hold.
        assert_eq!(translation_control(0b0110, 0), TCR | 0b101 << 32);
        // [7:4] ASIDBits, [27:24] TGran64 and [31:28] TGran4 0b0001, 4K with 52-bit addresses,
        // change nothing.
        assert_eq!(translation_control(0b0001 << 28 | 0xf << 24 | 0b0010 << 4 | 0b0101, 0), TCR | 0b101 << 32);
    }

    #[test]
    fn the_walker_keeps_the_access_flag_and_dirty_state_where_the_core_can() {
        // ID_AA64MMFR1_EL1 [3:0] HAFDBS: 0b0001 is the access flag, [39] HA; 0b0010 adds dirty
        // state, [40] HD; 0b0011 adds the access flag in table descriptors.
        assert_eq!(translation_control(0, 0b0001), TCR | bit(39));
        assert_eq!(translation_control(0, 0b0010), TCR | bit(39) | bit(40));
        assert_eq!(translation_control(0, 0b0011), TCR | bit(39) | bit(40));
        // [7:4] VMIDBits beside it changes nothing.
        assert_eq!(translation_control(0, 0b0010 << 4), TCR);
    }

    #[test]
    #[should_panic(expected = "no 4K granule")]
    fn a_core_without_the_4k_granule_is_refused() {
        // ID_AA64MMFR0_EL1 [31:28] TGran4 0b1111.
        translation_control(0xf << 28, 0);
    }

    #[test]
    fn the_memory_attributes_are_what_the_descriptor_s_indices_name() {
        // Attr<n> is bits [8n+7:8n]. 0b1111_1111 is Normal memory, write-back non-transient, inner
        // and outer; 0b0000_0000 is Device-nGnRnE.
        assert_eq!(MEMORY_ATTRIBUTES >> (8 * ATTR_NORMAL) & 0xff, 0xff);
        assert_eq!(MEMORY_ATTRIBUTES >> (8 * ATTR_DEVICE) & 0xff, 0x00);
    }

    #[test]
    fn the_system_control_turns_translation_and_the_caches_on_and_wxn_off() {
        // SCTLR_EL1: [0] M, [2] C, [12] I, and [19] WXN, which would take execution from the
        // loader's leaves, all of them writable.
        assert_eq!(system_control(0), bit(0) | bit(2) | bit(12));
        assert_eq!(system_control(bit(19)), bit(0) | bit(2) | bit(12));
        // What else the firmware set stays: [3] SA, [4] SA0, [11] EOS, [22] EIS, [23] SPAN.
        let firmware = bit(0) | bit(2) | bit(3) | bit(4) | bit(11) | bit(12) | bit(22) | bit(23);
        assert_eq!(system_control(firmware), firmware);
    }

    #[test]
    fn a_page_s_flush_names_bits_55_to_12_of_its_address() {
        // TLBI VAE1's argument: [43:0] VA[55:12]; [47:44] TTL 0, a leaf of any level; [63:48] ASID
        // 0, the one the loader's root table is live under.
        assert_eq!(flush_argument(0x0000_8765_4321_0fff), 0x8_7654_3210);
        assert_eq!(flush_argument(0x0000_8765_4321_1000), 0x8_7654_3211);
        assert_eq!(flush_argument(u64::MAX), (1 << 44) - 1);
    }

    /// CTR_EL0 with [31] RES1 alone: [19:16] DminLine and [3:0] IminLine 0, one word a line, and
    /// [28] IDC and [29] DIC clear, a core that asks for the clean and for the invalidation.
    const CTR: u64 = bit(31);

    #[test]
    fn the_cache_type_gives_each_line_as_four_bytes_shifted_by_its_field() {
        assert_eq!(coherence(CTR), Coherence { clean: Some(4), invalidate: Some(4) });
        // DminLine 4 and IminLine 4: 16 words, 64 bytes, in each.
        assert_eq!(coherence(CTR | 4 << 16 | 4), Coherence { clean: Some(64), invalidate: Some(64) });
        // Each field is its own: DminLine 5 beside IminLine 3, and the other way round.
        assert_eq!(coherence(CTR | 5 << 16 | 3), Coherence { clean: Some(128), invalidate: Some(32) });
        assert_eq!(coherence(CTR | 3 << 16 | 5), Coherence { clean: Some(32), invalidate: Some(128) });
        // The largest a field holds: 2^15 words.
        assert_eq!(coherence(CTR | 0xf << 16 | 0xf), Coherence { clean: Some(1 << 17), invalidate: Some(1 << 17) });
        // [15:14] L1Ip, [23:20] ERG, [27:24] CWG and [37:32] TminLine beside them change nothing.
        let others = 0b11 << 14 | 0xf << 20 | 0xf << 24 | 0x3f << 32;
        assert_eq!(coherence(CTR | others | 4 << 16 | 4), Coherence { clean: Some(64), invalidate: Some(64) });
    }

    #[test]
    fn a_core_whose_fetch_reads_through_the_data_cache_is_not_cleaned() {
        // [28] IDC: no clean to the point of unification; the invalidation stays.
        assert_eq!(coherence(CTR | bit(28) | 4 << 16 | 4), Coherence { clean: None, invalidate: Some(64) });
    }

    #[test]
    fn a_core_whose_fetch_sees_every_write_is_not_invalidated() {
        // [29] DIC, which a core reports with [28] IDC: neither step.
        assert_eq!(coherence(CTR | bit(29) | bit(28) | 4 << 16 | 4), Coherence { clean: None, invalidate: None });
        // Each bit takes its own step away, so DIC without IDC still cleans.
        assert_eq!(coherence(CTR | bit(29) | 4 << 16 | 4), Coherence { clean: Some(64), invalidate: None });
    }

    #[test]
    fn a_range_s_lines_are_every_line_that_holds_one_of_its_bytes() {
        fn all(start: u64, end: u64, line: u64) -> Vec<u64> {
            lines(start, end, line).collect()
        }
        // A range that starts and ends inside one line is that line.
        assert_eq!(all(0x1010, 0x1030, 64), [0x1000]);
        assert_eq!(all(0x103f, 0x1040, 64), [0x1000]);
        // One that starts inside a line and ends inside a later one takes both and what is between.
        assert_eq!(all(0x103f, 0x1041, 64), [0x1000, 0x1040]);
        assert_eq!(all(0x1010, 0x10c1, 64), [0x1000, 0x1040, 0x1080, 0x10c0]);
        // The end is exclusive: a range that ends where a line starts leaves that line out.
        assert_eq!(all(0x1000, 0x1080, 64), [0x1000, 0x1040]);
        assert_eq!(all(0x1000, 0x1081, 64), [0x1000, 0x1040, 0x1080]);
        // Another line size, and a page of 64-byte lines.
        assert_eq!(all(0x1004, 0x100c, 4), [0x1004, 0x1008]);
        assert_eq!(all(0x8000013000, 0x8000014000, 64).len(), 64);
    }

    #[test]
    #[should_panic(expected = "no byte in 0x1010-0x1010")]
    fn a_range_without_a_byte_has_no_lines_to_ask_for() {
        // Its start rounded down is below its end, which would name a line it has no byte in.
        let _ = lines(0x1010, 0x1010, 64);
    }

    #[test]
    #[should_panic(expected = "a cache line of 48 bytes")]
    fn a_line_is_a_power_of_two() {
        let _ = lines(0x1000, 0x2000, 48);
    }

    #[test]
    fn the_frames_below_virt_s_ram_are_devices() {
        // The PL011, and the last frame below 1 GiB.
        for paddr in [0, 0x0900_0000, 0x3fe0_0000] {
            assert!(device(paddr), "{paddr:#x}");
        }
        for paddr in [0x4000_0000, 0xffe0_0000] {
            assert!(!device(paddr), "{paddr:#x}");
        }
    }

    #[test]
    #[should_panic(expected = "outside the descriptor's address field")]
    fn a_block_takes_no_address_bit_under_bit_21() {
        Entry::leaf(FRAME + 0x1000, Leaf::Large, false, false);
    }

    #[test]
    #[should_panic(expected = "outside the descriptor's address field")]
    fn a_table_takes_no_address_bit_over_bit_47() {
        Entry::table(1 << 48, false);
    }
}
