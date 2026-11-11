// SPDX-License-Identifier: MIT

//! The IOMMU items: QEMU virt's SMMUv3, when the machine has one (`iommu=smmuv3`), with a stream
//! table whose every entry refuses its stream. design/machine-glue-below-the-kernel/.
//!
//! Written from the Arm SMMU architecture specification v3 (IHI 0070 H.a), cited as SMMU. The
//! tables and queues are statics of the kernel's image, which runs where the loader put it in the
//! identity map, so their addresses are the physical ones the SMMU reads. The event queue's
//! interrupt is not routed: no stream reaches a translation, so only a StreamID past the table
//! records an event, and `iommu_fault_dump` reads what the queue holds.

use core::ptr::{addr_of_mut, read_volatile, write_volatile};
use core::sync::atomic::{compiler_fence, AtomicUsize, Ordering};

use crate::instruction::{dsb, load, store};

fn assert_device(bus: usize, device: usize, function: usize) {
    assert!(bus < 256 && device < 32 && function < 8, "Device id out of range");
}

// The registers, by their offset from the SMMU's base. SMMU 6.2, Table 6-1; the event queue's
// pointers are on the second 64 KiB page.
const IDR0: usize = 0x0;
const IDR1: usize = 0x4;
const CR0: usize = 0x20;
const CR0ACK: usize = 0x24;
const CR1: usize = 0x28;
const CR2: usize = 0x2c;
const IRQ_CTRL: usize = 0x50;
const IRQ_CTRLACK: usize = 0x54;
const GERROR: usize = 0x60;
const GERRORN: usize = 0x64;
const STRTAB_BASE: usize = 0x80;
const STRTAB_BASE_CFG: usize = 0x88;
const CMDQ_BASE: usize = 0x90;
const CMDQ_PROD: usize = 0x98;
const CMDQ_CONS: usize = 0x9c;
const EVENTQ_BASE: usize = 0xa0;
const EVENTQ_PROD: usize = 0x1_00a8;
const EVENTQ_CONS: usize = 0x1_00ac;

/// The bytes of registers the SMMU has: two 64 KiB pages.
#[cfg(test)]
const REGISTER_BYTES: usize = 0x2_0000;

/// SMMU 6.3.1: IDR0.COHACC, bit 4, the SMMU's accesses to its tables and queues are coherent with
/// the cores' caches; HYP, bit 9, it has the EL2 translation regime, which CMD_TLBI_EL2_ALL names.
const IDR0_COHACC: u32 = 1 << 4;
const IDR0_HYP: u32 = 1 << 9;

/// SMMU 6.3.2: IDR1.CMDQS, bits 25:21, and EVENTQS, bits 20:16, log2 of the most entries each queue
/// may have.
const IDR1_CMDQS_SHIFT: u32 = 21;
const IDR1_EVENTQS_SHIFT: u32 = 16;
const IDR1_QS_MASK: u32 = 0b1_1111;

/// SMMU 6.3.9: CR0.SMMUEN, bit 0, EVENTQEN, bit 2, CMDQEN, bit 3; each change shows in CR0ACK once
/// it took effect.
const CR0_SMMUEN: u32 = 1 << 0;
const CR0_EVENTQEN: u32 = 1 << 2;
const CR0_CMDQEN: u32 = 1 << 3;

/// SMMU 6.3.11: CR1, the stream table's and the queues' accesses Inner Shareable (0b11 in TABLE_SH,
/// bits 11:10, and QUEUE_SH, 5:4) and Write-Back cacheable inner and outer (0b01 in TABLE_OC, 9:8,
/// TABLE_IC, 7:6, QUEUE_OC, 3:2, and QUEUE_IC, 1:0), as the kernel's own memory is.
const CR1_COHERENT: u32 = 0b11 << 10 | 0b01 << 8 | 0b01 << 6 | 0b11 << 4 | 0b01 << 2 | 0b01;

/// SMMU 6.3.12: CR2.RECINVSID, bit 1, a StreamID past the table records C_BAD_STREAMID; PTM, bit 2,
/// the SMMU's TLBs take no broadcast maintenance from the cores, since this crate invalidates them.
const CR2_RECINVSID_PTM: u32 = 1 << 1 | 1 << 2;

/// log2 of the stream table's entries: a linear table of 256, the StreamIDs of PCI bus 0.
const STREAM_BITS: u32 = 8;
const STREAMS: usize = 1 << STREAM_BITS;

/// log2 of the command queue's entries, and of the event queue's.
const COMMAND_BITS: u32 = 4;
const COMMANDS: usize = 1 << COMMAND_BITS;
const EVENT_BITS: u32 = 4;
const EVENTS: usize = 1 << EVENT_BITS;

/// SMMU 5.2: an STE with V, bit 0, set and Config, bits 3:1, 0b000 reports an abort to its stream's
/// device and records no event.
const STE_REFUSE: u64 = 1;

/// SMMU 4.3.9: CMD_CFGI_ALL, opcode 0x04 with Range, bits 68:64, 31: every STE and CD the SMMU caches.
const CMD_CFGI_ALL: [u64; 2] = [0x04, 31];
/// SMMU 4.4.4.1: CMD_TLBI_NSNH_ALL, opcode 0x30: every non-secure non-hypervisor TLB entry.
const CMD_TLBI_NSNH_ALL: [u64; 2] = [0x30, 0];
/// SMMU 4.4.2.7: CMD_TLBI_EL2_ALL, opcode 0x20: every EL2 TLB entry.
const CMD_TLBI_EL2_ALL: [u64; 2] = [0x20, 0];
/// SMMU 4.7.3: CMD_SYNC, opcode 0x46 with CS, bits 13:12, 0b00: completes once every command before
/// it has, which the command queue's consumer index passing it shows.
const CMD_SYNC: [u64; 2] = [0x46, 0];

/// SMMU 6.3.24 and 6.3.26: the address fields of STRTAB_BASE, bits 55:6, and of a queue base, 55:5.
const STRTAB_ADDRESS_MASK: u64 = ((1 << 56) - 1) & !((1 << 6) - 1);
const QUEUE_ADDRESS_MASK: u64 = ((1 << 56) - 1) & !((1 << 5) - 1);

/// The stream table, linear: aligned to its size, which SMMU 6.3.24 has the SMMU assume.
#[repr(C, align(16384))]
struct StreamTable([[u64; 8]; STREAMS]);

/// The command queue: aligned to its size, SMMU 6.3.26.
#[repr(C, align(256))]
struct CommandQueue([[u64; 2]; COMMANDS]);

/// The event queue, aligned as the command queue is: SMMU 6.3.29.
#[repr(C, align(512))]
struct EventQueue([[u64; 4]; EVENTS]);

/// What the SMMU reads and writes in memory.
pub(crate) struct Tables {
    streams: StreamTable,
    commands: CommandQueue,
    events: EventQueue,
}

impl Tables {
    pub(crate) const fn new() -> Self {
        Self {
            streams: StreamTable([[0; 8]; STREAMS]),
            commands: CommandQueue([[0; 2]; COMMANDS]),
            events: EventQueue([[0; 4]; EVENTS]),
        }
    }
}

/// The SMMU's register base, or 0 on a machine without one. `init` sets it once on the boot core.
static BASE: AtomicUsize = AtomicUsize::new(0);

static mut TABLES: Tables = Tables::new();

/// Keeps the SMMU's register base from `BootInfo`.
pub(crate) fn keep(base: Option<u64>) {
    BASE.store(base.map_or(0, |base| base as usize), Ordering::Relaxed);
}

/// The SMMU, when the machine has one.
fn smmu() -> Option<Smmu> {
    match BASE.load(Ordering::Relaxed) {
        0 => None,
        base => Some(Smmu { base, tables: addr_of_mut!(TABLES) }),
    }
}

/// An SMMUv3's registers, and the tables and queues it is given.
pub(crate) struct Smmu {
    base: usize,
    tables: *mut Tables,
}

/// The index and the wrap bit of a queue of `2^bits` entries, SMMU 3.5.1: the bits of a PROD or CONS
/// register that name its place.
const fn place_mask(bits: u32) -> u32 {
    (1 << (bits + 1)) - 1
}

impl Smmu {
    unsafe fn load(&self, offset: usize) -> u32 {
        load(self.base + offset)
    }

    unsafe fn store(&self, offset: usize, value: u32) {
        store(self.base + offset, value);
    }

    /// Stores a 64-bit register as its two halves, the lower first, which SMMU 6.2 permits.
    unsafe fn store_wide(&self, offset: usize, value: u64) {
        self.store(offset, value as u32);
        self.store(offset + 4, (value >> 32) as u32);
    }

    /// Stores `value` to CR0, or IRQ_CTRL, and waits until its acknowledgement shows it.
    unsafe fn store_acknowledged(&self, offset: usize, acknowledgement: usize, value: u32) {
        self.store(offset, value);
        while self.load(acknowledgement) != value {
            core::hint::spin_loop();
        }
    }

    /// Turns translation on with every stream refused, as SMMU 3.11 orders it: translation off, the
    /// stream table and the queues given while it is, the queues on, the SMMU's cached
    /// configuration and TLBs invalidated, then SMMUEN.
    pub(crate) unsafe fn enable(&self) {
        let idr0 = self.load(IDR0);
        let idr1 = self.load(IDR1);
        log::info!("SMMUv3 at {:#x}: IDR0 {:#x}, IDR1 {:#x}", self.base, idr0, idr1);
        assert!(idr0 & IDR0_COHACC != 0, "SMMUv3 without coherent access to its tables");
        assert!(idr1 >> IDR1_CMDQS_SHIFT & IDR1_QS_MASK >= COMMAND_BITS, "SMMUv3 command queue too small");
        assert!(idr1 >> IDR1_EVENTQS_SHIFT & IDR1_QS_MASK >= EVENT_BITS, "SMMUv3 event queue too small");

        self.store_acknowledged(CR0, CR0ACK, 0);
        self.store_acknowledged(IRQ_CTRL, IRQ_CTRLACK, 0);

        let tables = &mut *self.tables;
        for entry in tables.streams.0.iter_mut() {
            write_volatile(entry, [STE_REFUSE, 0, 0, 0, 0, 0, 0, 0]);
        }
        for entry in tables.commands.0.iter_mut() {
            write_volatile(entry, [0; 2]);
        }
        for entry in tables.events.0.iter_mut() {
            write_volatile(entry, [0; 4]);
        }
        let streams = addr_of_mut!(tables.streams) as u64;
        let commands = addr_of_mut!(tables.commands) as u64;
        let events = addr_of_mut!(tables.events) as u64;
        compiler_fence(Ordering::SeqCst);
        dsb();

        self.store(CR1, CR1_COHERENT);
        self.store(CR2, CR2_RECINVSID_PTM);
        self.store_wide(STRTAB_BASE, streams & STRTAB_ADDRESS_MASK);
        // SMMU 6.3.25: FMT, bits 17:16, 0b00 is a linear table, of 2^LOG2SIZE (bits 5:0) entries.
        self.store(STRTAB_BASE_CFG, STREAM_BITS);
        self.store_wide(CMDQ_BASE, commands & QUEUE_ADDRESS_MASK | u64::from(COMMAND_BITS));
        self.store(CMDQ_PROD, 0);
        self.store(CMDQ_CONS, 0);
        self.store_wide(EVENTQ_BASE, events & QUEUE_ADDRESS_MASK | u64::from(EVENT_BITS));
        self.store(EVENTQ_PROD, 0);
        self.store(EVENTQ_CONS, 0);
        self.store_acknowledged(CR0, CR0ACK, CR0_CMDQEN | CR0_EVENTQEN);

        let mut prod = 0;
        self.command(&mut prod, CMD_CFGI_ALL);
        self.command(&mut prod, CMD_TLBI_NSNH_ALL);
        if idr0 & IDR0_HYP != 0 {
            self.command(&mut prod, CMD_TLBI_EL2_ALL);
        }
        self.command(&mut prod, CMD_SYNC);
        compiler_fence(Ordering::SeqCst);
        dsb();
        self.store(CMDQ_PROD, prod);
        while self.load(CMDQ_CONS) & place_mask(COMMAND_BITS) != prod {
            core::hint::spin_loop();
        }
        assert_eq!(self.load(GERROR), self.load(GERRORN), "SMMUv3 global error");

        log::info!("Enabling translation");
        self.store_acknowledged(CR0, CR0ACK, CR0_CMDQEN | CR0_EVENTQEN | CR0_SMMUEN);
    }

    /// Writes `command` at the command queue's place `prod`, and moves `prod` past it.
    unsafe fn command(&self, prod: &mut u32, command: [u64; 2]) {
        let index = *prod as usize & (COMMANDS - 1);
        write_volatile(addr_of_mut!((*self.tables).commands.0[index]), command);
        *prod = (*prod + 1) & place_mask(COMMAND_BITS);
    }

    /// Logs each event record the event queue holds, SMMU 7.3, consuming it, and returns how many.
    pub(crate) unsafe fn dump(&self) -> usize {
        let prod = self.load(EVENTQ_PROD) & place_mask(EVENT_BITS);
        let mut cons = self.load(EVENTQ_CONS) & place_mask(EVENT_BITS);
        let mut records = 0;
        while cons != prod {
            let record = read_volatile(addr_of_mut!((*self.tables).events.0[cons as usize & (EVENTS - 1)]));
            log::error!(
                "SMMUv3 event {:#x}: {:#018x} {:#018x} {:#018x} {:#018x}",
                record[0] & 0xff,
                record[0],
                record[1],
                record[2],
                record[3]
            );
            cons = (cons + 1) & place_mask(EVENT_BITS);
            self.store(EVENTQ_CONS, cons);
            records += 1;
        }
        records
    }
}

/// What `iommu_map` and `iommu_invalidate` answer: there is no IOMMU, or it refuses every stream.
fn refusal(present: bool, absent: &'static str) -> Result<(), &'static str> {
    if present {
        Err("The SMMUv3 refuses every stream")
    } else {
        Err(absent)
    }
}

/// With no SMMU in `BootInfo`, does nothing; otherwise turns its translation on with every stream
/// refused, and logs `Enabling translation`. Once on the boot core, after `init`.
pub unsafe fn iommu_init() {
    if let Some(smmu) = smmu() {
        smmu.enable();
    }
}

/// Refuses: no stream is mapped.
pub unsafe fn iommu_map(bus: usize, device: usize, function: usize, root: u64) -> Result<(), &'static str> {
    assert_device(bus, device, function);
    let _ = root;
    refusal(smmu().is_some(), "No IOMMU available")
}

/// Refuses: no stream is mapped.
pub unsafe fn iommu_invalidate(bus: usize, device: usize, function: usize, page: u64) -> Result<(), &'static str> {
    assert_device(bus, device, function);
    let _ = page;
    refusal(smmu().is_some(), "No IOMMU hardware")
}

/// Logs and consumes the SMMU's pending event records; refuses on a machine without an SMMU.
pub fn iommu_fault_dump() -> Result<(), &'static str> {
    let smmu = smmu().ok_or("No IOMMU hardware")?;
    unsafe { smmu.dump() };
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::boxed::Box;
    use std::sync::atomic::AtomicBool;
    use std::vec::Vec;

    use super::*;
    use crate::instruction::{events, Block, Event};

    /// IDR0 as given, and IDR1 as an SMMU with queues of up to 2^19 entries and 16-bit StreamIDs has it.
    fn identify(block: &Block, idr0: u32) {
        block.set(IDR0, idr0);
        block.set(IDR1, 19 << IDR1_CMDQS_SHIFT | 19 << IDR1_EVENTQS_SHIFT | 16);
    }

    /// Runs `enable` against `block` while another thread plays the SMMU: it acknowledges CR0 and
    /// IRQ_CTRL and consumes every command produced.
    fn enable(block: &Block, tables: &mut Tables) {
        let stop = AtomicBool::new(false);
        std::thread::scope(|scope| {
            scope.spawn(|| {
                while !stop.load(Ordering::SeqCst) {
                    block.set(CR0ACK, block.get(CR0));
                    block.set(IRQ_CTRLACK, block.get(IRQ_CTRL));
                    block.set(CMDQ_CONS, block.get(CMDQ_PROD));
                    std::thread::yield_now();
                }
            });
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                Smmu { base: block.base(), tables }.enable()
            }));
            stop.store(true, Ordering::SeqCst);
            if let Err(panic) = result {
                std::panic::resume_unwind(panic);
            }
        });
    }

    fn wide(block: &Block, offset: usize) -> u64 {
        u64::from(block.get(offset)) | u64::from(block.get(offset + 4)) << 32
    }

    /// What this thread stored, by offset from `block`, with each DSB as `(usize::MAX, 0)`.
    fn stores(block: &Block) -> Vec<(usize, u32)> {
        events()
            .into_iter()
            .filter_map(|event| match event {
                Event::Store { register, value } => Some((register - block.base(), value)),
                Event::Dsb => Some((usize::MAX, 0)),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn the_tables_and_queues_are_aligned_to_their_sizes() {
        let tables = Box::new(Tables::new());
        assert_eq!(core::mem::size_of::<StreamTable>(), 64 << STREAM_BITS);
        assert_eq!(core::mem::size_of::<CommandQueue>(), 16 << COMMAND_BITS);
        assert_eq!(core::mem::size_of::<EventQueue>(), 32 << EVENT_BITS);
        assert_eq!(&tables.streams as *const _ as usize % (64 << STREAM_BITS), 0);
        assert_eq!(&tables.commands as *const _ as usize % (16 << COMMAND_BITS), 0);
        assert_eq!(&tables.events as *const _ as usize % (32 << EVENT_BITS), 0);
    }

    #[test]
    fn enable_refuses_every_stream_and_turns_translation_on_last() {
        let block = Block::of(REGISTER_BYTES);
        identify(&block, IDR0_COHACC);
        let mut tables = Box::new(Tables::new());
        tables.streams.0[7][2] = 0xdead;
        let streams = &tables.streams as *const _ as u64;
        let commands = &tables.commands as *const _ as u64;
        let events = &tables.events as *const _ as u64;

        enable(&block, &mut tables);

        assert!(tables.streams.0.iter().all(|entry| *entry == [1, 0, 0, 0, 0, 0, 0, 0]));
        assert_eq!(wide(&block, STRTAB_BASE), streams);
        assert_eq!(block.get(STRTAB_BASE_CFG), 8);
        assert_eq!(wide(&block, CMDQ_BASE), commands | 4);
        assert_eq!(wide(&block, EVENTQ_BASE), events | 4);
        assert_eq!(block.get(CR1), 0xd75);
        assert_eq!(block.get(CR2), 0b110);
        assert_eq!(block.get(IRQ_CTRL), 0);
        assert_eq!(block.get(CR0), 0b1101);
        assert_eq!(block.get(CMDQ_PROD), 3);
        assert_eq!(tables.commands.0[..4], [[0x04, 31], [0x30, 0], [0x46, 0], [0, 0]]);
        let dsb = (usize::MAX, 0);
        assert_eq!(
            stores(&block),
            [
                (CR0, 0),
                (IRQ_CTRL, 0),
                dsb,
                (CR1, 0xd75),
                (CR2, 0b110),
                (STRTAB_BASE, streams as u32),
                (STRTAB_BASE + 4, (streams >> 32) as u32),
                (STRTAB_BASE_CFG, 8),
                (CMDQ_BASE, commands as u32 | 4),
                (CMDQ_BASE + 4, (commands >> 32) as u32),
                (CMDQ_PROD, 0),
                (CMDQ_CONS, 0),
                (EVENTQ_BASE, events as u32 | 4),
                (EVENTQ_BASE + 4, (events >> 32) as u32),
                (EVENTQ_PROD, 0),
                (EVENTQ_CONS, 0),
                (CR0, 0b1100),
                dsb,
                (CMDQ_PROD, 3),
                (CR0, 0b1101),
            ]
        );
    }

    #[test]
    fn enable_invalidates_the_el2_tlb_of_an_smmu_with_one() {
        let block = Block::of(REGISTER_BYTES);
        identify(&block, IDR0_COHACC | IDR0_HYP);
        let mut tables = Box::new(Tables::new());

        enable(&block, &mut tables);

        assert_eq!(tables.commands.0[..4], [[0x04, 31], [0x30, 0], [0x20, 0], [0x46, 0]]);
        assert_eq!(block.get(CMDQ_PROD), 4);
        assert_eq!(block.get(CR0), 0b1101);
    }

    #[test]
    #[should_panic(expected = "SMMUv3 without coherent access to its tables")]
    fn enable_refuses_an_smmu_without_coherent_access() {
        let block = Block::of(REGISTER_BYTES);
        identify(&block, 0);
        let mut tables = Box::new(Tables::new());
        enable(&block, &mut tables);
    }

    #[test]
    #[should_panic(expected = "SMMUv3 global error")]
    fn enable_stops_at_a_global_error() {
        let block = Block::of(REGISTER_BYTES);
        identify(&block, IDR0_COHACC);
        block.set(GERROR, 1);
        let mut tables = Box::new(Tables::new());
        enable(&block, &mut tables);
    }

    #[test]
    fn dump_consumes_each_record_the_event_queue_holds() {
        let block = Block::of(REGISTER_BYTES);
        let mut tables = Box::new(Tables::new());
        block.set(EVENTQ_CONS, 3);
        block.set(EVENTQ_PROD, 5);

        assert_eq!(unsafe { Smmu { base: block.base(), tables: &mut *tables }.dump() }, 2);

        assert_eq!(block.get(EVENTQ_CONS), 5);
        assert_eq!(stores(&block), [(EVENTQ_CONS, 4), (EVENTQ_CONS, 5)]);
    }

    #[test]
    fn dump_follows_the_queue_across_its_wrap_and_ignores_the_overflow_flag() {
        let block = Block::of(REGISTER_BYTES);
        let mut tables = Box::new(Tables::new());
        block.set(EVENTQ_CONS, 15);
        block.set(EVENTQ_PROD, 1 << 31 | 1 << 4 | 1);

        assert_eq!(unsafe { Smmu { base: block.base(), tables: &mut *tables }.dump() }, 2);

        assert_eq!(block.get(EVENTQ_CONS), 1 << 4 | 1);
    }

    #[test]
    fn dump_of_an_empty_queue_stores_nothing() {
        let block = Block::of(REGISTER_BYTES);
        let mut tables = Box::new(Tables::new());
        block.set(EVENTQ_CONS, 1 << 4 | 2);
        block.set(EVENTQ_PROD, 1 << 4 | 2);

        assert_eq!(unsafe { Smmu { base: block.base(), tables: &mut *tables }.dump() }, 0);

        assert_eq!(stores(&block), []);
    }

    #[test]
    fn an_smmu_refuses_every_stream_and_no_iommu_says_so() {
        assert_eq!(refusal(true, "No IOMMU available"), Err("The SMMUv3 refuses every stream"));
        assert_eq!(refusal(false, "No IOMMU available"), Err("No IOMMU available"));
    }
}
