// SPDX-License-Identifier: MIT

//! The GICv3: the Distributor, each core's Redistributor and each core's CPU interface through the
//! ICC system registers. design/machine-glue-below-the-kernel/.
//!
//! Written from the Arm Generic Interrupt Controller Architecture Specification, GIC architecture
//! version 3 and version 4 (IHI 0069H.b), cited as IHI 0069 with the section beside each item. The
//! kernel takes every interrupt as Group 1, which a core at EL1 receives as an IRQ; nothing here is
//! Group 0, which would arrive as an FIQ (IHI 0069 4.6).

use core::sync::atomic::{AtomicU32, Ordering};

use crate::instruction::{dsb, isb, load, load_wide, read, store, write, System};
use crate::{timer, FLUSH_VECTOR, MAX_CPUS, RESCHEDULE_VECTOR, TIMER_VECTOR};

/// The Distributor's frame, where QEMU virt's device tree puts it: node `intc@8000000`, compatible
/// `arm,gic-v3`, the first pair of `reg`.
pub const DISTRIBUTOR: usize = 0x0800_0000;

/// The Redistributors' one region, the second pair of the same `reg`, and its size.
pub const REDISTRIBUTORS: usize = 0x080a_0000;
const REDISTRIBUTORS_BYTES: usize = 0x00f6_0000;

/// A frame of the GIC's register map is 64 KiB, and a GICv3 Redistributor is two of them in order,
/// RD_base and then SGI_base; the frames of one region are contiguous. IHI 0069 12.10.
const FRAME_BYTES: usize = 0x1_0000;
pub const REDISTRIBUTOR_BYTES: usize = 2 * FRAME_BYTES;

/// The region holds a Redistributor for every core this crate can name.
const _: () = assert!(MAX_CPUS * REDISTRIBUTOR_BYTES <= REDISTRIBUTORS_BYTES);

/// GICD_CTLR, at offset 0 of the Distributor. ARE, bit 4, turns affinity routing on, and may change
/// only while every group is disabled; EnableGrp1, bit 1, forwards Group 1 interrupts; RWP, bit 31,
/// reads 1 while a write of ARE or a group's disabling is still spreading. A write that changes ARE
/// is read in the format from before it, so the group's enable is a write of its own. To a
/// Non-secure access on a GIC with two Security states the same bits are ARE_NS and EnableGrp1A.
/// IHI 0069 12.9.4.
const GICD_CTLR: usize = 0x0000;
const GICD_CTLR_ENABLE_GROUP_1: u32 = 1 << 1;
const GICD_CTLR_AFFINITY_ROUTING: u32 = 1 << 4;
const GICD_CTLR_WRITE_PENDING: u32 = 1 << 31;

/// GICR_CTLR, at offset 0 of RD_base. RWP, bit 3, reads 1 while a write of GICR_ICENABLER0 is
/// still spreading. IHI 0069 12.11.2.
const GICR_CTLR: usize = 0x0000;
const GICR_CTLR_WRITE_PENDING: u32 = 1 << 3;

/// GICR_TYPER, 64 bits at offset 8 of RD_base, read-only. Affinity_Value, bits 63:32, is the core
/// this Redistributor serves, as Aff3, Aff2, Aff1 and Aff0 from the top byte down; VLPIS, bit 1,
/// is clear on a GICv3, whose Redistributor is the two frames. IHI 0069 12.11.37.
const GICR_TYPER: usize = 0x0008;
const GICR_TYPER_VIRTUAL_LPIS: u64 = 1 << 1;
const GICR_TYPER_AFFINITY_SHIFT: u32 = 32;

/// GICR_WAKER, at offset 0x14 of RD_base. ProcessorSleep, bit 1, resets to 1 and holds every
/// interrupt back from the CPU interface; software clears it and waits until ChildrenAsleep, bit 2,
/// reads 0. Until then a write to an ICC register other than ICC_SRE_EL1 is unpredictable.
/// IHI 0069 12.11.42 and 11.1.
const GICR_WAKER: usize = 0x0014;
const GICR_WAKER_PROCESSOR_SLEEP: u32 = 1 << 1;
const GICR_WAKER_CHILDREN_ASLEEP: u32 = 1 << 2;

/// The registers of SGI_base, each with one bit per interrupt 0 to 31, the SGIs in bits 15:0 and the
/// PPIs in bits 31:16: GICR_IGROUPR0, where a 1 puts the interrupt in Group 1 (IHI 0069 12.11.12);
/// GICR_ISENABLER0, where a written 1 enables it (12.11.25); and GICR_ICENABLER0, where a written
/// 1 disables it (12.11.5). IHI 0069 12.10, Table 12-29.
const GICR_IGROUPR0: usize = 0x0080;
const GICR_ISENABLER0: usize = 0x0100;
const GICR_ICENABLER0: usize = 0x0180;

/// GICR_IPRIORITYR<n>, n from 0 to 7, at offset 0x400 + 4n of SGI_base: a byte per interrupt, the
/// lower value the higher priority. IHI 0069 12.11.21.
const GICR_IPRIORITYR: usize = 0x0400;
const GICR_IPRIORITYR_COUNT: usize = 8;

/// The one priority every interrupt has, in every byte of a priority register: the middle of the
/// range, which every implementation has bits for (IHI 0069 4.8).
const PRIORITY: u32 = 0x8080_8080;

/// ICC_PMR_EL1 as the kernel runs: an interrupt is signaled when its priority is higher than this
/// mask, the lowest there is. IHI 0069 12.2.19.
const PRIORITY_MASK: u64 = 0xff;

/// ICC_SRE_EL1.SRE, bit 0: the ICC system registers are the CPU interface. IHI 0069 12.2.23.
const ICC_SRE_SYSTEM_REGISTERS: u64 = 1 << 0;

/// ICC_CTLR_EL1.EOImode, bit 1. Clear, a write of ICC_EOIR1_EL1 drops the running priority and
/// deactivates the interrupt in one step. IHI 0069 12.2.6 and 12.2.10.
const ICC_CTLR_SEPARATE_DEACTIVATION: u64 = 1 << 1;

/// ICC_IGRPEN1_EL1.Enable, bit 0. IHI 0069 12.2.16.
const ICC_IGRPEN1_ENABLE: u64 = 1 << 0;

/// The INTID field of ICC_IAR1_EL1 and ICC_EOIR1_EL1, bits 23:0. IHI 0069 12.2.14.
const INTID: u64 = 0x00ff_ffff;

/// The INTID an acknowledgement reads when no interrupt is pending with the priority to be
/// signaled. It was not activated and takes no end of interrupt. IHI 0069 2.2.1.
const SPURIOUS: u32 = 1023;

/// The SGIs are interrupts 0 to 15. IHI 0069 2.2.
const SGIS: u8 = 16;

/// ICC_SGI1R_EL1: the SGI's INTID in bits 27:24, Aff1 of the target in bits 23:16, and TargetList in
/// bits 15:0, one bit per Aff0. With RS, bits 47:44, zero, the list names Aff0 0 to 15; Aff2, Aff3
/// and IRM are zero. IHI 0069 12.2.22.
const ICC_SGI1R_INTID_SHIFT: u32 = 24;
const ICC_SGI1R_AFF1_SHIFT: u32 = 16;

/// Cores under one Aff1 value on QEMU virt, whose device tree names core n `reg = <n / 16 << 8 |
/// n % 16>` (nodes `cpu@0` to `cpu@31` at 32 cores): MPIDR_EL1's Aff1 and Aff0.
const CORES_PER_CLUSTER: usize = 16;

/// MPIDR_EL1's affinity fields: Aff0 in bits 7:0, Aff1 in bits 15:8, Aff2 in bits 23:16 and Aff3 in
/// bits 39:32. Arm ARM D24.2.137.
const MPIDR_AFFINITY: u64 = 0x00ff_00ff_ffff;

/// The affinity of core `cpu`, as Aff1 and Aff0. Aff2 and Aff3 are zero.
pub const fn affinity(cpu: usize) -> (u64, u64) {
    assert!(cpu < MAX_CPUS);
    ((cpu / CORES_PER_CLUSTER) as u64, (cpu % CORES_PER_CLUSTER) as u64)
}

/// The kernel's index of the calling core, from its MPIDR_EL1.
fn this_core() -> usize {
    let affinity = unsafe { read(System::Mpidr) } & MPIDR_AFFINITY;
    let (cluster, place) = ((affinity >> 8) as usize, (affinity & 0xff) as usize);
    assert!(
        place < CORES_PER_CLUSTER && cluster < MAX_CPUS / CORES_PER_CLUSTER,
        "a core with affinity {:#x} is outside QEMU virt's numbering",
        affinity
    );
    cluster * CORES_PER_CLUSTER + place
}

/// No interrupt is acknowledged and not ended.
const NOTHING: u32 = u32::MAX;

/// A GICv3, by the addresses of its Distributor and of its Redistributors, the latter an array of
/// [`REDISTRIBUTOR_BYTES`] each, indexed by the kernel's cpu index.
pub struct Gic {
    distributor: usize,
    redistributors: usize,
    /// The interrupt each core acknowledged and has not ended.
    acknowledged: [AtomicU32; MAX_CPUS],
}

impl Gic {
    /// # Safety
    ///
    /// A GICv3 Distributor's registers are at `distributor`, and at `redistributors` the
    /// Redistributor of each core that will call [`Gic::init_core`], in the order of the cpu index.
    pub const unsafe fn new(distributor: usize, redistributors: usize) -> Self {
        Self { distributor, redistributors, acknowledged: [const { AtomicU32::new(NOTHING) }; MAX_CPUS] }
    }

    /// Turns the Distributor on with affinity routing and Group 1 forwarded.
    pub unsafe fn init(&self) {
        let control = self.distributor + GICD_CTLR;
        let settled = || {
            while load(control) & GICD_CTLR_WRITE_PENDING != 0 {
                core::hint::spin_loop();
            }
        };
        store(control, 0);
        settled();
        store(control, GICD_CTLR_AFFINITY_ROUTING);
        settled();
        store(control, GICD_CTLR_AFFINITY_ROUTING | GICD_CTLR_ENABLE_GROUP_1);
    }

    /// Brings up the calling core's Redistributor and CPU interface, the flush SGI and the timer's
    /// PPI enabled. `cpu` is the calling core.
    pub unsafe fn init_core(&self, cpu: usize) {
        let core = this_core();
        assert!(core == cpu, "interrupt_init_core({}) on core {}", cpu, core);
        let rd = self.redistributors + cpu * REDISTRIBUTOR_BYTES;
        let sgi = rd + FRAME_BYTES;
        let kind = load_wide(rd + GICR_TYPER);
        assert!(
            kind & GICR_TYPER_VIRTUAL_LPIS == 0,
            "Redistributor {} is a GICv4's, four frames where this crate steps by two",
            cpu
        );
        let (cluster, place) = affinity(cpu);
        assert!(
            kind >> GICR_TYPER_AFFINITY_SHIFT == cluster << 8 | place,
            "Redistributor {} serves affinity {:#x}",
            cpu,
            kind >> GICR_TYPER_AFFINITY_SHIFT
        );

        // The timer is quiet before its interrupt can be delivered.
        timer::disarm();

        store(rd + GICR_WAKER, load(rd + GICR_WAKER) & !GICR_WAKER_PROCESSOR_SLEEP);
        while load(rd + GICR_WAKER) & GICR_WAKER_CHILDREN_ASLEEP != 0 {
            core::hint::spin_loop();
        }

        // Every SGI and PPI disabled, in Group 1 and at the one priority; then the three enabled.
        store(sgi + GICR_ICENABLER0, u32::MAX);
        while load(rd + GICR_CTLR) & GICR_CTLR_WRITE_PENDING != 0 {
            core::hint::spin_loop();
        }
        store(sgi + GICR_IGROUPR0, u32::MAX);
        for n in 0..GICR_IPRIORITYR_COUNT {
            store(sgi + GICR_IPRIORITYR + 4 * n, PRIORITY);
        }
        store(sgi + GICR_ISENABLER0, 1 << TIMER_VECTOR | 1 << FLUSH_VECTOR | 1 << RESCHEDULE_VECTOR);

        write(System::IccSre, read(System::IccSre) | ICC_SRE_SYSTEM_REGISTERS);
        isb();
        assert!(
            read(System::IccSre) & ICC_SRE_SYSTEM_REGISTERS != 0,
            "core {} cannot use the ICC system registers",
            cpu
        );
        write(System::IccPmr, PRIORITY_MASK);
        write(System::IccCtlr, read(System::IccCtlr) & !ICC_CTLR_SEPARATE_DEACTIVATION);
        write(System::IccIgrpen1, ICC_IGRPEN1_ENABLE);
        isb();
    }

    /// Acknowledges the interrupt signaled to this core and returns its INTID, or nothing when
    /// none was pending.
    pub fn acknowledge(&self) -> Option<u32> {
        let id = (unsafe { read(System::IccIar1) } & INTID) as u32;
        if id == SPURIOUS {
            return None;
        }
        self.acknowledged[this_core()].store(id, Ordering::Relaxed);
        Some(id)
    }

    /// Ends the interrupt this core acknowledged last.
    pub fn end(&self) {
        let core = this_core();
        let id = self.acknowledged[core].swap(NOTHING, Ordering::Relaxed);
        assert!(id != NOTHING, "end_of_interrupt on core {}, which acknowledged nothing", core);
        unsafe {
            write(System::IccEoir1, u64::from(id));
        }
    }
}

/// Raises SGI `id` on core `cpu`.
pub fn send(cpu: usize, id: u8) {
    assert!(id < SGIS, "interrupt {} is not an SGI", id);
    let (cluster, place) = affinity(cpu);
    unsafe {
        write(System::IccSgi1r, u64::from(id) << ICC_SGI1R_INTID_SHIFT | cluster << ICC_SGI1R_AFF1_SHIFT | 1 << place);
    }
    isb();
    dsb();
}

#[cfg(test)]
mod tests {
    use std::thread;
    use std::time::Duration;
    use std::vec::Vec;

    use super::Gic;
    use crate::instruction::{events, ignore_writes, set, Block, Event, System};

    /// A Distributor frame and two Redistributors, each two frames, in the test's memory.
    struct Fake {
        distributor: Block,
        redistributors: Block,
    }

    impl Fake {
        fn new() -> Self {
            Self { distributor: Block::of(0x1_0000), redistributors: Block::of(2 * 0x2_0000) }
        }

        fn gic(&self) -> Gic {
            unsafe { Gic::new(self.distributor.base(), self.redistributors.base()) }
        }

        /// Core `cpu`'s RD_base, as an offset into the Redistributors.
        fn rd(cpu: usize) -> usize {
            cpu * 0x2_0000
        }

        /// Core `cpu`'s SGI_base, the frame after its RD_base.
        fn sgi(cpu: usize) -> usize {
            cpu * 0x2_0000 + 0x1_0000
        }

        /// Makes core `cpu`'s Redistributor read as one that is awake and belongs to that core, and
        /// makes this thread that core.
        fn become_core(&self, cpu: usize) {
            // IHI 0069 12.11.37: GICR_TYPER at 0x0008, Affinity_Value in bits 63:32, which is the
            // word at 0x000c. Arm ARM D24.2.137: MPIDR_EL1's Aff0 in bits 7:0; bit 31 is RES1.
            self.redistributors.set(Self::rd(cpu) + 0x000c, cpu as u32);
            set(System::Mpidr, 1 << 31 | cpu as u64);
        }

        fn store(&self, offset: usize, value: u32) -> Event {
            Event::Store { register: self.redistributors.base() + offset, value }
        }
    }

    #[test]
    fn the_distributor_gets_affinity_routing_while_disabled_and_then_group_1() {
        let fake = Fake::new();
        // A Distributor some earlier software left forwarding both groups without affinity routing.
        fake.distributor.set(0x0000, 0b11);

        unsafe { fake.gic().init() };

        // IHI 0069 12.9.4: GICD_CTLR at 0x0000; ARE, bit 4, changes only with every group disabled;
        // EnableGrp1 is bit 1, and Group 0, bit 0, stays disabled.
        let control = fake.distributor.base();
        assert_eq!(
            events(),
            [
                Event::Store { register: control, value: 0 },
                Event::Store { register: control, value: 1 << 4 },
                Event::Store { register: control, value: 1 << 4 | 1 << 1 },
            ]
        );
    }

    #[test]
    fn the_distributor_s_next_write_waits_while_a_write_is_pending() {
        let fake = Fake::new();
        // IHI 0069 12.9.4: RWP is bit 31 of GICD_CTLR, read-only. This fake reads it as 1 until
        // the test lets go.
        fake.distributor.set(0x0000, 1 << 31 | 0b11);
        fake.distributor.hold(0x0000, 1 << 31);
        let stores = thread::scope(|scope| {
            let init = scope.spawn(|| {
                unsafe { fake.gic().init() };
                events()
            });
            thread::sleep(Duration::from_millis(50));
            // The groups are disabled, and affinity routing is not written while that spreads.
            assert_eq!(fake.distributor.get(0x0000), 1 << 31);
            assert!(!init.is_finished());
            fake.distributor.release(0x0000);
            fake.distributor.set(0x0000, 0);
            init.join().unwrap()
        });
        assert_eq!(stores.len(), 3);
        assert_eq!(fake.distributor.get(0x0000), 1 << 4 | 1 << 1);
    }

    #[test]
    fn a_core_wakes_its_redistributor_then_sets_its_interrupts_then_its_cpu_interface() {
        let fake = Fake::new();
        fake.become_core(1);
        // IHI 0069 12.11.42: GICR_WAKER at 0x0014, ProcessorSleep bit 1; bit 31 is the
        // implementation's and is written back as read.
        fake.redistributors.set(Fake::rd(1) + 0x0014, 1 << 31 | 1 << 1);
        // ICC_SRE_EL1 with DFB and DIB, bits 1 and 2, which a core without bypass reads as 1;
        // ICC_CTLR_EL1 with EOImode, bit 1, and PMHE, bit 6, set by earlier software.
        set(System::IccSre, 0b110);
        set(System::IccCtlr, 1 << 6 | 1 << 1);
        // The timer as earlier software left it, enabled.
        set(System::CntpCtl, 0b001);

        unsafe { fake.gic().init_core(1) };

        let mut expected = Vec::from([
            Event::Read { register: System::Mpidr },
            // The timer is quiet before anything can deliver its interrupt.
            Event::Write { register: System::CntpCtl, value: 0 },
            Event::Isb,
            // IHI 0069 11.1: ProcessorSleep cleared before any ICC register but ICC_SRE_EL1.
            fake.store(Fake::rd(1) + 0x0014, 1 << 31),
            // IHI 0069 12.10 Table 12-29: GICR_ICENABLER0 at 0x0180 of SGI_base, GICR_IGROUPR0 at
            // 0x0080, GICR_IPRIORITYR0 to 7 from 0x0400, GICR_ISENABLER0 at 0x0100.
            fake.store(Fake::sgi(1) + 0x0180, 0xffff_ffff),
            fake.store(Fake::sgi(1) + 0x0080, 0xffff_ffff),
        ]);
        expected.extend((0..8).map(|n| fake.store(Fake::sgi(1) + 0x0400 + 4 * n, 0x8080_8080)));
        expected.extend([
            // SGI 0, the flush IPI, SGI 1, the reschedule IPI, and PPI 30, the EL1 physical timer.
            fake.store(Fake::sgi(1) + 0x0100, 1 << 30 | 1 << 0 | 1 << 1),
            // IHI 0069 12.2.23: SRE is bit 0, set before any other ICC register is used.
            Event::Read { register: System::IccSre },
            Event::Write { register: System::IccSre, value: 0b111 },
            Event::Isb,
            Event::Read { register: System::IccSre },
            // IHI 0069 12.2.19: the mask that lets every priority above the lowest through.
            Event::Write { register: System::IccPmr, value: 0xff },
            // IHI 0069 12.2.6: EOImode, bit 1, cleared and the rest kept.
            Event::Read { register: System::IccCtlr },
            Event::Write { register: System::IccCtlr, value: 1 << 6 },
            // IHI 0069 12.2.16: Enable is bit 0.
            Event::Write { register: System::IccIgrpen1, value: 1 },
            Event::Isb,
        ]);
        assert_eq!(events(), expected);
        // Core 0's Redistributor was not touched.
        assert_eq!(fake.redistributors.get(Fake::sgi(0) + 0x0100), 0);
    }

    #[test]
    fn a_core_waits_until_its_redistributor_reports_it_awake() {
        let fake = Fake::new();
        // The reset value: ProcessorSleep and ChildrenAsleep, bits 1 and 2.
        fake.redistributors.set(Fake::rd(0) + 0x0014, 0b110);
        thread::scope(|scope| {
            let init = scope.spawn(|| {
                fake.become_core(0);
                unsafe { fake.gic().init_core(0) };
            });
            thread::sleep(Duration::from_millis(50));
            // ProcessorSleep is cleared, and nothing of SGI_base is written while the fake still
            // reports ChildrenAsleep.
            assert_eq!(fake.redistributors.get(Fake::rd(0) + 0x0014), 0b100);
            assert_eq!(fake.redistributors.get(Fake::sgi(0) + 0x0080), 0);
            assert!(!init.is_finished());
            fake.redistributors.set(Fake::rd(0) + 0x0014, 0);
        });
        assert_eq!(fake.redistributors.get(Fake::sgi(0) + 0x0100), 1 << 30 | 1 << 0 | 1 << 1);
    }

    #[test]
    #[should_panic(expected = "interrupt_init_core(1) on core 0")]
    fn a_core_does_not_bring_up_another_core_s_share() {
        let fake = Fake::new();
        fake.become_core(0);
        unsafe { fake.gic().init_core(1) };
    }

    #[test]
    #[should_panic(expected = "Redistributor 1 serves affinity 0x100")]
    fn a_redistributor_that_serves_another_core_is_refused() {
        let fake = Fake::new();
        fake.become_core(1);
        fake.redistributors.set(Fake::rd(1) + 0x000c, 0x100);
        unsafe { fake.gic().init_core(1) };
    }

    #[test]
    #[should_panic(expected = "four frames")]
    fn a_gicv4_redistributor_whose_frames_this_crate_would_miscount_is_refused() {
        let fake = Fake::new();
        fake.become_core(0);
        // IHI 0069 12.11.37: VLPIS is bit 1 of GICR_TYPER.
        fake.redistributors.set(Fake::rd(0) + 0x0008, 1 << 1);
        unsafe { fake.gic().init_core(0) };
    }

    #[test]
    #[should_panic(expected = "the ICC system registers")]
    fn a_core_whose_system_register_interface_stays_off_is_refused() {
        // ICC_SRE_EL1.SRE as a core reads it where a higher exception level keeps the system
        // registers from EL1: zero, whatever is written (IHI 0069 12.2.23).
        ignore_writes(System::IccSre);
        let fake = Fake::new();
        fake.become_core(0);
        unsafe { fake.gic().init_core(0) };
    }

    #[test]
    fn the_index_of_a_core_is_its_cluster_times_sixteen_plus_its_place() {
        // QEMU virt's device tree at 32 cores: cpu@17 has reg 0x101.
        set(System::Mpidr, 1 << 31 | 0x101);
        assert_eq!(super::this_core(), 17);
        assert_eq!(super::affinity(17), (1, 1));
        assert_eq!(super::affinity(15), (0, 15));
        assert_eq!(super::affinity(31), (1, 15));
    }

    #[test]
    #[should_panic(expected = "affinity")]
    fn a_core_outside_the_machine_s_numbering_has_no_index() {
        // Aff2 is bits 23:16, and QEMU virt's device tree names no core with one.
        set(System::Mpidr, 1 << 16);
        super::this_core();
    }

    #[test]
    fn an_acknowledgement_returns_the_interrupt_and_its_end_names_it() {
        let fake = Fake::new();
        let gic = fake.gic();
        fake.become_core(1);
        // IHI 0069 12.2.14: INTID is bits 23:0 of ICC_IAR1_EL1; the rest is RES0.
        set(System::IccIar1, 30);

        assert_eq!(gic.acknowledge(), Some(30));
        gic.end();

        assert_eq!(
            events(),
            [
                Event::Read { register: System::IccIar1 },
                Event::Read { register: System::Mpidr },
                Event::Read { register: System::Mpidr },
                Event::Write { register: System::IccEoir1, value: 30 },
            ]
        );
    }

    #[test]
    fn each_core_ends_what_it_acknowledged() {
        let fake = Fake::new();
        let gic = fake.gic();
        fake.become_core(0);
        set(System::IccIar1, 30);
        assert_eq!(gic.acknowledge(), Some(30));
        fake.become_core(1);
        set(System::IccIar1, 0);
        assert_eq!(gic.acknowledge(), Some(0));
        events();

        gic.end();
        fake.become_core(0);
        gic.end();

        let ends: Vec<Event> = events().into_iter().filter(|event| matches!(event, Event::Write { .. })).collect();
        assert_eq!(
            ends,
            [
                Event::Write { register: System::IccEoir1, value: 0 },
                Event::Write { register: System::IccEoir1, value: 30 },
            ]
        );
    }

    #[test]
    fn a_spurious_acknowledgement_is_nothing() {
        let fake = Fake::new();
        // IHI 0069 2.2.1: INTID 1023 when nothing is pending.
        set(System::IccIar1, 1023);

        assert_eq!(fake.gic().acknowledge(), None);

        assert_eq!(events(), [Event::Read { register: System::IccIar1 }]);
    }

    #[test]
    #[should_panic(expected = "end_of_interrupt on core 0, which acknowledged nothing")]
    fn an_end_without_an_acknowledgement_is_a_bug() {
        let fake = Fake::new();
        fake.become_core(0);
        fake.gic().end();
    }

    #[test]
    #[should_panic(expected = "end_of_interrupt on core 0, which acknowledged nothing")]
    fn an_interrupt_is_ended_once() {
        let fake = Fake::new();
        let gic = fake.gic();
        fake.become_core(0);
        set(System::IccIar1, 30);
        gic.acknowledge();
        gic.end();
        gic.end();
    }

    #[test]
    fn an_ipi_names_the_sgi_the_cluster_and_the_core_in_it_and_is_observed_before_the_return() {
        super::send(1, 0);
        super::send(17, 5);

        // IHI 0069 12.2.22: INTID in bits 27:24, Aff1 in bits 23:16, TargetList one bit per Aff0.
        // 12.1.6: after an ISB, a DSB has the Redistributor observe the write.
        assert_eq!(
            events(),
            [
                Event::Write { register: System::IccSgi1r, value: 1 << 1 },
                Event::Isb,
                Event::Dsb,
                Event::Write { register: System::IccSgi1r, value: 5 << 24 | 1 << 16 | 1 << 1 },
                Event::Isb,
                Event::Dsb,
            ]
        );
    }

    #[test]
    #[should_panic(expected = "interrupt 30 is not an SGI")]
    fn an_ipi_is_an_sgi() {
        super::send(1, 30);
    }
}
