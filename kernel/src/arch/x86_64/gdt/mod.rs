//! The Global Descriptor Table and related stuff.
//!
//! During boot, we do the following:
//!
//! 1. The bootstrap assembly code loads a temporary GDT.
//! 2. On CPU 0, we initialize and load the GDT in Rust using preallocated space.
//! 3. On other CPUs, we initialize and load the GDT using space provided by
//!    Cpu capabilities.
//!
//! ## GDT Entries
//!
//! * 0 - Null
//! * 1 - Kernel Data
//! * 2 - Kernel Code
//! * 3 - User Data
//! * 4 - User Code
//! * 5,6 - TSS

mod types;

use core::cmp::min;
use core::mem;

pub use crate::arch::TaskStateSegment;
use crate::arch::{lgdt, load_cs, load_ds, load_es, load_ss, load_tr, DescriptorTablePointer, Ring, SegmentSelector};

use types::{AccessByte, SystemAccessByte, SystemDescriptorType};

const GDT_F_LONG_MODE: u8 = 1 << 5;

/// The access bytes of the four flat segments and the TSS.
const KERNEL_CODE: AccessByte = AccessByte::code_data(0).executable().read_write();
const KERNEL_DATA: AccessByte = AccessByte::code_data(0).read_write();
const USER_CODE: AccessByte = AccessByte::code_data(3).executable().read_write();
const USER_DATA: AccessByte = AccessByte::code_data(3).read_write();
const TSS: SystemAccessByte = SystemAccessByte::new(SystemDescriptorType::AvailableTss, 3);

// The encodings Intel SDM Volume 3A section 3.4.5 gives for a present, readable
// code segment, a present, writable data segment and an available 64-bit TSS.
const _: () = assert!(KERNEL_CODE.0 == 0x9a && KERNEL_DATA.0 == 0x92);
const _: () = assert!(USER_CODE.0 == 0xfa && USER_DATA.0 == 0xf2);
const _: () = assert!(TSS.0 == 0xe9);

/// Initializes and loads the GDT.
///
/// This must be called only once for each CPU reset.
pub unsafe fn init_cpu() {
    let cpu = &mut crate::cpu::get_current().arch;

    // Initialize TSS
    let tss_addr = {
        for i in 0..min(cpu.ist.len(), 7) {
            let ist_addr = cpu.ist[i].bottom();
            cpu.tss.set_ist(i, ist_addr as u64);
        }

        let rsp0_addr = cpu.ist[0].bottom();
        cpu.tss.set_rsp0(rsp0_addr as u64);

        &cpu.tss as *const TaskStateSegment
    };

    // Initialize GDT
    let gdt = &mut cpu.gdt;

    gdt.kernel_code = GdtEntry::new(0, 0, KERNEL_CODE, GDT_F_LONG_MODE);
    gdt.kernel_data = GdtEntry::new(0, 0, KERNEL_DATA, GDT_F_LONG_MODE);
    gdt.user_code = GdtEntry::new(0, 0, USER_CODE, GDT_F_LONG_MODE);
    gdt.user_data = GdtEntry::new(0, 0, USER_DATA, GDT_F_LONG_MODE);
    gdt.tss = BigGdtEntry::new(tss_addr as u64, mem::size_of::<TaskStateSegment>() as u32, TSS, 0);

    // Load GDT
    lgdt(&gdt.get_pointer());

    // We don't load FS and GS
    // GS is used for the CPU-local structure (crate::cpu).
    use GlobalDescriptorTable as GDT;
    load_cs(SegmentSelector::new(GDT::KERNEL_CODE_INDEX, Ring::Ring0));
    load_ds(SegmentSelector::new(GDT::KERNEL_DATA_INDEX, Ring::Ring0));
    load_es(SegmentSelector::new(GDT::KERNEL_DATA_INDEX, Ring::Ring0));
    load_ss(SegmentSelector::new(GDT::KERNEL_DATA_INDEX, Ring::Ring0));
    load_tr(SegmentSelector::new(GDT::TSS_INDEX, Ring::Ring0));
}

/// A Global Descriptor Table.
#[derive(Debug)]
#[repr(packed)]
pub struct GlobalDescriptorTable {
    /// Null entry.
    _null: GdtEntry,

    /// Kernel code. syscall loads SS from the entry after this one.
    pub kernel_code: GdtEntry,

    /// Kernel data.
    pub kernel_data: GdtEntry,

    /// User data. sysret loads CS from the entry after this one.
    pub user_data: GdtEntry,

    /// User code.
    pub user_code: GdtEntry,

    /// TSS.
    ///
    /// This is 16 bytes in Long Mode.
    pub tss: BigGdtEntry,
}

impl GlobalDescriptorTable {
    pub const KERNEL_CODE_INDEX: u16 = 1;
    pub const KERNEL_DATA_INDEX: u16 = 2;
    pub const USER_DATA_INDEX: u16 = 3;
    pub const USER_CODE_INDEX: u16 = 4;
    pub const TSS_INDEX: u16 = 5;

    pub const USER_CS: u16 = SegmentSelector::new(Self::USER_CODE_INDEX, Ring::Ring3).bits();
    pub const USER_SS: u16 = SegmentSelector::new(Self::USER_DATA_INDEX, Ring::Ring3).bits();

    /// Zero-initializes the GDT.
    ///
    /// It must be correctly initialized before being loaded.
    pub const fn empty() -> Self {
        Self {
            _null: GdtEntry::empty(),
            kernel_code: GdtEntry::empty(),
            kernel_data: GdtEntry::empty(),
            user_code: GdtEntry::empty(),
            user_data: GdtEntry::empty(),
            tss: BigGdtEntry::empty(),
        }
    }

    /// Returns a pointer to this GDT.
    fn get_pointer(&self) -> DescriptorTablePointer<Self> {
        let limit = mem::size_of::<Self>().try_into().expect("GDT too big");

        DescriptorTablePointer {
            limit,
            base: self as *const GlobalDescriptorTable,
        }
    }
}

/// A 8-byte GDT Code/Data entry, in the segment descriptor layout of Intel SDM Volume 3A
/// section 3.4.5. The CPU reads the fields, so `repr(C)` keeps their order and marks them used.
#[derive(Copy, Clone, Debug)]
#[repr(C, packed)]
pub struct GdtEntry {
    limitl: u16,
    offsetl: u16,
    offsetm: u8,
    access: u8,
    flags_limith: u8,
    offseth: u8,
}

impl GdtEntry {
    /// Creates an empty (not present) entry.
    pub const fn empty() -> Self {
        Self::new(0, 0, AccessByte::not_present(), 0)
    }

    /// Creates a GDT entry.
    const fn new(offset: u32, limit: u32, access: AccessByte, flags: u8) -> Self {
        Self {
            limitl: limit as u16,
            offsetl: offset as u16,
            offsetm: (offset >> 16) as u8,
            access: access.0,
            flags_limith: flags & 0xF0 | ((limit >> 16) as u8) & 0x0F,
            offseth: (offset >> 24) as u8,
        }
    }
}

/// A 16-byte GDT System entry, in the layout of Figure 4-22 in AMD Vol. 2. The CPU reads the
/// fields, so `repr(C)` keeps their order and marks them used.
#[derive(Copy, Clone, Debug)]
#[repr(C, packed)]
pub struct BigGdtEntry {
    limitl: u16,
    offsetl: u16,
    offsetm: u8,
    access_type: u8,
    flags_limith: u8,
    offseth: u8,
    offsetx: u32,
    _reserved: u32,
}

impl BigGdtEntry {
    /// Creates an empty (not present) entry.
    pub const fn empty() -> Self {
        Self::new(0, 0, SystemAccessByte::not_present(), 0)
    }

    /// Creates a 16-byte GDT entry.
    const fn new(offset: u64, limit: u32, access_type: SystemAccessByte, flags: u8) -> Self {
        Self {
            limitl: limit as u16,
            offsetl: offset as u16,
            offsetm: (offset >> 16) as u8,
            access_type: access_type.0,
            flags_limith: flags & 0xF0 | ((limit >> 16) as u8) & 0x0F,
            offsetx: (offset >> 32) as u32,
            offseth: (offset >> 24) as u8,
            _reserved: 0,
        }
    }
}
