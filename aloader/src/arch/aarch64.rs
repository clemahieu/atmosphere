//! AArch64 as UEFI leaves it: EL1 with the VMSAv8-64 stage-1 tables of the 4K granule.

use crate::memory::Leaf;

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
    /// any other EL1's, never both. `cache_disable` makes the frame device memory.
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
        let el0 = if user { AP_EL0 | PXN } else { UXN };
        Self(VALID | kind | paddr | memory | AF | NG | DBM | el0)
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
        // [4:2] AttrIndx 1, device memory.
        let device = Entry::leaf(FRAME, Leaf::Small, true, true);
        assert_eq!(device.0, LEAF | bit(1) | FRAME | OUTER_SHAREABLE | bit(2) | bit(6) | bit(53));

        for (entry, is_user, is_device) in [(kernel, false, false), (user, true, false), (device, true, true)] {
            assert!(entry.present());
            assert_eq!(entry.address(), FRAME);
            assert_eq!(entry.user(), is_user);
            assert_eq!(entry.cache_disable(), is_device);
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
