//! The access flag and the dirty state of a process's leaves where the walker does not keep them.
//!
//! The verified encoder writes a leaf with its access flag clear, and a writable leaf marked with the
//! dirty-bit modifier and AP[2] set, its clean state; `maintains_accessed` and `maintains_dirty` say
//! this target keeps both (design/arch-module/ item 1). Where TCR_EL1.HA is set the walker sets the
//! flag on the first access through a leaf, and where HD is set as well it clears AP[2] on the first
//! write (Arm ARM D8.5.1.2, D8.5.2.1). Where they are clear, because the core has no FEAT_HAFDBS or
//! the command line asked for it, that access takes an access-flag fault (D8.5.1.1) and that write a
//! permission fault (D8.5.2), and this handler makes the change the walker would have made, then
//! returns to the instruction, which runs again. The leaves the kernel runs on are the loader's,
//! written with the flag set and AP[2] clear, so only EL0 takes either fault. design/arch-module/
//! item 5.

use core::arch::asm;
use core::sync::atomic::{AtomicU64, Ordering};

use verified::arch::{
    DESC_AF, DESC_AP_EL0, DESC_AP_RO, DESC_DBM, DESC_TYPE, DESC_VALID, MEM_MASK, TABLE_AP_NO_EL0, TABLE_AP_RO,
};

use super::TTBR_ADDRESS;
use crate::capability::CAP_KERNEL;

/// The faults served since boot, on every core.
static ACCESS_FAULTS: AtomicU64 = AtomicU64::new(0);
static DIRTY_FAULTS: AtomicU64 = AtomicU64::new(0);

/// ESR_EL1.EC, bits 31:26: 0b100000 is an Instruction Abort and 0b100100 a Data Abort, each taken
/// from a lower exception level. Arm ARM D24.2.44.
const CLASS_SHIFT: u32 = 26;
const CLASS_MASK: u64 = 0b11_1111;
const CLASS_INSTRUCTION_ABORT_LOWER: u64 = 0b10_0000;
const CLASS_DATA_ABORT_LOWER: u64 = 0b10_0100;

/// The abort's ISS: FnV, bit 10, set when FAR_EL1 does not hold the faulting address; WnR, bit 6, of
/// a Data Abort, set when the access was a write; and DFSC or IFSC, bits 5:0, whose upper four bits
/// name the fault and whose lower two the lookup level it was found at: 0b0010 an access-flag fault
/// and 0b0011 a permission fault. Arm ARM D24.2.44, the ISS encodings for a Data Abort and an
/// Instruction Abort.
const FAR_NOT_VALID: u64 = 1 << 10;
const ABORT_WRITE: u64 = 1 << 6;
const STATUS_KIND_MASK: u64 = 0b11_1100;
const STATUS_ACCESS_FLAG: u64 = 0b00_1000;
const STATUS_PERMISSION: u64 = 0b00_1100;

/// What an abort from EL0 asks of the leaf that translated it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fault {
    /// The access flag was clear: set it.
    Access,
    /// A write was refused: clear AP[2] where the leaf is writable-clean.
    Dirty,
}

/// The fault `syndrome` reports, when it is one the walker would have spared.
const fn fault(syndrome: u64) -> Option<Fault> {
    let class = syndrome >> CLASS_SHIFT & CLASS_MASK;
    if class != CLASS_DATA_ABORT_LOWER && class != CLASS_INSTRUCTION_ABORT_LOWER || syndrome & FAR_NOT_VALID != 0 {
        return None;
    }
    let kind = syndrome & STATUS_KIND_MASK;
    if kind == STATUS_ACCESS_FLAG {
        Some(Fault::Access)
    } else if kind == STATUS_PERMISSION && class == CLASS_DATA_ABORT_LOWER && syndrome & ABORT_WRITE != 0 {
        Some(Fault::Dirty)
    } else {
        None
    }
}

// With IL, bit 25, set: a read's and a write's access-flag fault at level 3, an instruction fetch's
// at level 2, a write's permission fault at level 3; then a read's permission fault, a fetch's, a
// translation fault, the same write with FnV set, the kernel's own write and an svc.
const _: () = assert!(matches!(fault(0x9200_000b), Some(Fault::Access)));
const _: () = assert!(matches!(fault(0x9200_004b), Some(Fault::Access)));
const _: () = assert!(matches!(fault(0x8200_000a), Some(Fault::Access)));
const _: () = assert!(matches!(fault(0x9200_004f), Some(Fault::Dirty)));
const _: () = assert!(fault(0x9200_000f).is_none() && fault(0x8200_000f).is_none() && fault(0x9200_0047).is_none());
const _: () = assert!(fault(0x9200_044f).is_none() && fault(0x9600_004f).is_none() && fault(0x5600_0000).is_none());

/// What the tables above a leaf leave EL0: whether any of them removes EL0's access, APTable[0], or
/// the write, APTable[1] (Arm ARM D8.4.1.2.2).
#[derive(Clone, Copy)]
struct Above {
    el0: bool,
    write: bool,
}

/// The leaf `fault` asks for in place of `leaf`, a valid leaf under tables that leave `above`, or
/// nothing when the walker would not have spared the fault: the leaf is EL0's, and for a write it is
/// writable-clean, AP[2] set in a leaf marked with the modifier and nothing else refusing the write.
const fn served(fault: Fault, leaf: u64, above: Above) -> Option<u64> {
    if leaf & DESC_VALID == 0 || leaf & DESC_AP_EL0 == 0 || !above.el0 {
        return None;
    }
    match fault {
        Fault::Access => Some(leaf | DESC_AF),
        Fault::Dirty if leaf & DESC_DBM != 0 && above.write => Some(leaf & !DESC_AP_RO),
        Fault::Dirty => None,
    }
}

const OPEN: Above = Above { el0: true, write: true };
// A user page writable-clean with its flag clear, 0x...0x4c3 with DBM: the flag set, then AP[2]
// cleared; a leaf the modifier does not mark, one that is not EL0's, one under a table that removes
// EL0 or the write, and an invalid word, refused.
const _: () = assert!(matches!(served(Fault::Access, DESC_DBM | 0x4000_00c3, OPEN), Some(0x0008_0000_4000_04c3)));
const _: () = assert!(matches!(served(Fault::Dirty, DESC_DBM | 0x4000_04c3, OPEN), Some(0x0008_0000_4000_0443)));
const _: () = assert!(served(Fault::Dirty, 0x4000_04c3, OPEN).is_none());
const _: () = assert!(served(Fault::Access, DESC_DBM | 0x4000_0083, OPEN).is_none());
const _: () = assert!(served(Fault::Access, DESC_DBM | 0x4000_00c3, Above { el0: false, write: true }).is_none());
const _: () = assert!(served(Fault::Dirty, DESC_DBM | 0x4000_04c3, Above { el0: true, write: false }).is_none());
const _: () = assert!(served(Fault::Access, DESC_DBM | 0x4000_00c2, OPEN).is_none());

/// The lookup levels of a walk of the 4K granule over 48-bit addresses, 0 to 3, and the address bit
/// each level's index starts at. Arm ARM D8.2.
const LEVELS: u64 = 4;
const fn index_shift(level: u64) -> u64 {
    39 - 9 * level
}

/// The leaf that maps `address` under this core's TTBR0_EL1 and what the tables above it leave EL0,
/// or nothing when no valid leaf does. A block at lookup levels 1 and 2 is a leaf, as a page at level
/// 3 is (D8.3.1). Page tables lie in the identity map the loader built, so their physical addresses
/// are usable as pointers.
unsafe fn leaf(address: u64) -> Option<(*mut u64, Above)> {
    if address >> 48 != 0 {
        return None;
    }
    let base: u64;
    asm!("mrs {base}, TTBR0_EL1", base = out(reg) base, options(nomem, nostack, preserves_flags));
    let mut table = (base & TTBR_ADDRESS) as *mut u64;
    let mut above = OPEN;
    for level in 0..LEVELS {
        let entry = table.add((address >> index_shift(level)) as usize & 0x1ff);
        let word = entry.read_volatile();
        if word & DESC_VALID == 0 {
            return None;
        }
        let next_table = word & DESC_TYPE != 0 && level < LEVELS - 1;
        if !next_table {
            // Bit 1 clear at level 0 is no block with the 4K granule, and at level 3 is reserved.
            let leaf = level > 0 && (level < LEVELS - 1) == (word & DESC_TYPE == 0);
            return leaf.then_some((entry, above));
        }
        above.el0 &= word & TABLE_AP_NO_EL0 == 0;
        above.write &= word & TABLE_AP_RO == 0;
        table = (word & MEM_MASK) as *mut u64;
    }
    None
}

/// A TLBI operand's VA[55:12], bits 43:0. Arm ARM C5.5.53.
const TLBI_ADDRESS_MASK: u64 = (1 << 44) - 1;

/// Drops this core's TLB entries for the page at `address` under every address-space id (TLBI
/// VAAE1, Arm ARM C5.5.53): the leaf was read-only and may be cached so. The DSB before it orders the
/// write of the leaf ahead of it, and the DSB after it completes it for this core (D8.17.8); the
/// exception's return is the context synchronization after.
unsafe fn forget(address: u64) {
    asm!(
        "dsb ishst",
        "tlbi vaae1, {page}",
        "dsb nsh",
        page = in(reg) address >> 12 & TLBI_ADDRESS_MASK,
        options(nostack, preserves_flags),
    );
}

/// Serves an abort from EL0 with `syndrome` at `address` that the walker would have spared: sets the
/// access flag, or clears AP[2] of a writable-clean leaf, and returns true, so the instruction runs
/// again. Returns false for any other abort, and for one whose leaf another core changed meanwhile so
/// that the abort no longer applies; then the instruction's next try faults as it would.
///
/// The kernel's lock is held over the walk, so the tables do not change or go free under it. The
/// update is a compare-exchange, since a walker that keeps the access flag, on a core whose
/// TCR_EL1.HA is set, may write the leaf at any time (D8.5.1.2). A leaf whose flag was clear is held
/// in no TLB (D8.5.1), and one that was read-only is dropped from this core's; another core's stale
/// read-only entry faults there and is dropped by the same path.
pub fn serve(syndrome: u64, address: u64) -> bool {
    let Some(fault) = fault(syndrome) else {
        return false;
    };
    let _tables = CAP_KERNEL.lock();
    let Some((entry, above)) = (unsafe { leaf(address) }) else {
        return false;
    };
    let updated = unsafe { AtomicU64::from_ptr(entry) }.try_update(Ordering::SeqCst, Ordering::SeqCst, |leaf| {
        served(fault, leaf, above)
    });
    if updated.is_err() {
        return false;
    }
    match fault {
        Fault::Access => ACCESS_FAULTS.fetch_add(1, Ordering::Relaxed),
        Fault::Dirty => {
            unsafe { forget(address) };
            DIRTY_FAULTS.fetch_add(1, Ordering::Relaxed)
        }
    };
    true
}

/// Logs how many faults of each kind the kernel served since boot.
pub fn report() {
    log::info!(
        "Served from EL0: {} access-flag faults, {} dirty-state faults",
        ACCESS_FAULTS.load(Ordering::Relaxed),
        DIRTY_FAULTS.load(Ordering::Relaxed)
    );
}
