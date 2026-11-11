// SPDX-License-Identifier: MIT

//! The instructions this crate issues itself: the load and the store of a device register, the read
//! and the write of a system register, the two barriers, the clean of the data cache, the hypervisor
//! call and the wait for an interrupt. On another architecture the crate is built for its tests,
//! where a device register is a word of the test's own memory, a system register is a value the
//! test's thread keeps, and each store, system register access, barrier, clean and call is recorded.

#[cfg(target_arch = "aarch64")]
pub use aarch64::{clean, dsb, hvc, isb, load, load_wide, read, store, wait, write};
#[cfg(test)]
pub use host::{answer, events, ignore_writes, set, Block, Event};
#[cfg(not(target_arch = "aarch64"))]
pub use host::{clean, dsb, hvc, isb, load, load_wide, read, store, wait, write};

/// A system register this crate reads or writes, by its name in the Arm ARM (DDI 0487) and, for the
/// ICC registers, in the GIC architecture specification (IHI 0069).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum System {
    /// MPIDR_EL1, read-only: this core's affinity. Arm ARM D24.2.137.
    Mpidr,
    /// SCTLR_EL1: the system control, with the enables of translation and of the caches. A core
    /// that is starting writes it in its entry, and nothing else here does. Arm ARM D24.2.174.
    Sctlr,
    /// TCR_EL1: the translation control, written as SCTLR_EL1 is. Arm ARM D24.2.193.
    Tcr,
    /// MAIR_EL1: what a descriptor's attribute index names, written as SCTLR_EL1 is. Arm ARM
    /// D24.2.126.
    Mair,
    /// ICC_SRE_EL1: whether the ICC system registers are in use. IHI 0069 12.2.23.
    IccSre,
    /// ICC_PMR_EL1: the priority mask. IHI 0069 12.2.19.
    IccPmr,
    /// ICC_CTLR_EL1: the CPU interface's control. IHI 0069 12.2.6.
    IccCtlr,
    /// ICC_IGRPEN1_EL1: Group 1's enable. IHI 0069 12.2.16.
    IccIgrpen1,
    /// ICC_IAR1_EL1, read-only: a read acknowledges the Group 1 interrupt signaled. IHI 0069 12.2.14.
    IccIar1,
    /// ICC_EOIR1_EL1, write-only: the end of a Group 1 interrupt. IHI 0069 12.2.10.
    IccEoir1,
    /// ICC_SGI1R_EL1, write-only: a write generates a Group 1 SGI. IHI 0069 12.2.22.
    IccSgi1r,
    /// CNTPCT_EL0, read-only: the physical count. Arm ARM D24.10.17.
    Cntpct,
    /// CNTP_CVAL_EL0: the EL1 physical timer's compare value. Arm ARM D24.10.23.
    CntpCval,
    /// CNTP_CTL_EL0: the EL1 physical timer's control. Arm ARM D24.10.22.
    CntpCtl,
}

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use core::arch::asm;

    use super::System;

    /// Loads the 32-bit device register at `register`.
    ///
    /// The access is one load of a single register without writeback, the form whose stage 2 data
    /// abort reports the access in its syndrome (Arm ARM D24.2.45, ISV), which a hypervisor emulating
    /// the device needs.
    ///
    /// # Safety
    ///
    /// `register` is a device register this core can read.
    pub unsafe fn load(register: usize) -> u32 {
        let value: u32;
        asm!(
            "ldr {value:w}, [{register}]",
            register = in(reg) register,
            value = out(reg) value,
            options(nostack, readonly, preserves_flags),
        );
        value
    }

    /// Stores `value` to the 32-bit device register at `register`, in the form [`load`] names.
    ///
    /// # Safety
    ///
    /// `register` is a device register this core can write.
    pub unsafe fn store(register: usize, value: u32) {
        asm!(
            "str {value:w}, [{register}]",
            register = in(reg) register,
            value = in(reg) value,
            options(nostack, preserves_flags),
        );
    }

    /// Loads the 64-bit device register at `register`, in the form [`load`] names.
    ///
    /// # Safety
    ///
    /// `register` is a 64-bit device register this core can read.
    pub unsafe fn load_wide(register: usize) -> u64 {
        let value: u64;
        asm!(
            "ldr {value}, [{register}]",
            register = in(reg) register,
            value = out(reg) value,
            options(nostack, readonly, preserves_flags),
        );
        value
    }

    /// Reads `register`.
    ///
    /// # Safety
    ///
    /// The caller accepts what the read does: a read of ICC_IAR1_EL1 acknowledges an interrupt.
    pub unsafe fn read(register: System) -> u64 {
        let value: u64;
        macro_rules! mrs {
            ($name:literal) => {
                asm!(concat!("mrs {value}, ", $name), value = out(reg) value, options(nomem, nostack, preserves_flags))
            };
        }
        match register {
            System::Mpidr => mrs!("MPIDR_EL1"),
            System::Sctlr => mrs!("SCTLR_EL1"),
            System::Tcr => mrs!("TCR_EL1"),
            System::Mair => mrs!("MAIR_EL1"),
            System::IccSre => mrs!("ICC_SRE_EL1"),
            System::IccPmr => mrs!("ICC_PMR_EL1"),
            System::IccCtlr => mrs!("ICC_CTLR_EL1"),
            System::IccIgrpen1 => mrs!("ICC_IGRPEN1_EL1"),
            System::IccIar1 => mrs!("ICC_IAR1_EL1"),
            System::Cntpct => mrs!("CNTPCT_EL0"),
            System::CntpCval => mrs!("CNTP_CVAL_EL0"),
            System::CntpCtl => mrs!("CNTP_CTL_EL0"),
            System::IccEoir1 | System::IccSgi1r => panic!("{:?} is write-only", register),
        }
        value
    }

    /// Writes `value` to `register`.
    ///
    /// # Safety
    ///
    /// The caller accepts what the write does to this core's interrupts and timer.
    pub unsafe fn write(register: System, value: u64) {
        macro_rules! msr {
            ($name:literal) => {
                asm!(concat!("msr ", $name, ", {value}"), value = in(reg) value, options(nomem, nostack, preserves_flags))
            };
        }
        match register {
            System::IccSre => msr!("ICC_SRE_EL1"),
            System::IccPmr => msr!("ICC_PMR_EL1"),
            System::IccCtlr => msr!("ICC_CTLR_EL1"),
            System::IccIgrpen1 => msr!("ICC_IGRPEN1_EL1"),
            System::IccEoir1 => msr!("ICC_EOIR1_EL1"),
            System::IccSgi1r => msr!("ICC_SGI1R_EL1"),
            System::CntpCval => msr!("CNTP_CVAL_EL0"),
            System::CntpCtl => msr!("CNTP_CTL_EL0"),
            System::Mpidr | System::IccIar1 | System::Cntpct => panic!("{:?} is read-only", register),
            System::Sctlr | System::Tcr | System::Mair => panic!("{:?} is written by a core's entry alone", register),
        }
    }

    /// ISB: the instructions after it see every system register write before it. Arm ARM B2.6.1.
    pub fn isb() {
        unsafe {
            asm!("isb", options(nomem, nostack, preserves_flags));
        }
    }

    /// DSB SY: after an ISB, the Redistributor has observed the last write to an ICC register that
    /// IHI 0069 12.1.6 lists.
    pub fn dsb() {
        unsafe {
            asm!("dsb sy", options(nomem, nostack, preserves_flags));
        }
    }

    /// CTR_EL0.DminLine, bits 19:16: log2 of the 4-byte words in the smallest line of any data
    /// cache this core has. Arm ARM D24.2.41.
    const DATA_LINE_SHIFT: u32 = 16;
    const DATA_LINE_MASK: u64 = 0b1111;

    /// Cleans the data cache's lines that hold `start..start + bytes` to memory, where an access the
    /// caches do not serve finds what was written: DC CVAC on each line (Arm ARM C5.3.25), complete
    /// at the DSB.
    ///
    /// # Safety
    ///
    /// The range is mapped for this core to read.
    pub unsafe fn clean(start: usize, bytes: usize) {
        let cache_type: u64;
        asm!("mrs {cache_type}, CTR_EL0", cache_type = out(reg) cache_type, options(nomem, nostack, preserves_flags));
        let line = 4usize << (cache_type >> DATA_LINE_SHIFT & DATA_LINE_MASK);
        let mut address = start & !(line - 1);
        while address < start + bytes {
            asm!("dc cvac, {address}", address = in(reg) address, options(nostack, preserves_flags));
            address += line;
        }
        dsb();
    }

    /// Calls the PSCI function `function` with `arguments`, and returns its result.
    ///
    /// The conduit is `hvc`, as QEMU virt's device tree says (node `psci`, `method = "hvc"`). The
    /// function id goes in W0, the arguments in X1 to X3, the result comes back in X0 and the
    /// instruction's immediate is 0 (PSCI, ARM DEN 0022, 5.2.1). A function that takes fewer
    /// arguments ignores the rest.
    ///
    /// # Safety
    ///
    /// The caller accepts what `function` does to the machine.
    pub unsafe fn hvc(function: u32, arguments: [u64; 3]) -> i64 {
        let result: i64;
        asm!(
            "hvc #0",
            inout("x0") u64::from(function) => result,
            inout("x1") arguments[0] => _,
            inout("x2") arguments[1] => _,
            inout("x3") arguments[2] => _,
            clobber_abi("C"),
            options(nostack),
        );
        result
    }

    /// Waits for an interrupt.
    pub fn wait() {
        unsafe {
            asm!("wfi", options(nomem, nostack, preserves_flags));
        }
    }
}

#[cfg(not(target_arch = "aarch64"))]
mod host {
    use core::sync::atomic::{AtomicU32, Ordering};
    #[cfg(test)]
    use {core::cell::RefCell, std::boxed::Box, std::vec::Vec};

    use super::System;

    /// What a test's thread did to the machine.
    #[cfg(test)]
    #[derive(Debug, PartialEq)]
    pub enum Event {
        Store { register: usize, value: u32 },
        Read { register: System },
        Write { register: System, value: u64 },
        Isb,
        Dsb,
        Clean { start: usize, bytes: usize },
        Hvc { function: u32, arguments: [u64; 3] },
    }

    /// The system registers [`System`] names.
    #[cfg(test)]
    const SYSTEM_REGISTERS: usize = System::CntpCtl as usize + 1;

    #[cfg(test)]
    std::thread_local! {
        static EVENTS: RefCell<Vec<Event>> = const { RefCell::new(Vec::new()) };
        static SYSTEM: RefCell<[u64; SYSTEM_REGISTERS]> = const { RefCell::new([0; SYSTEM_REGISTERS]) };
        static IGNORED: RefCell<[bool; SYSTEM_REGISTERS]> = const { RefCell::new([false; SYSTEM_REGISTERS]) };
        static ANSWER: RefCell<i64> = const { RefCell::new(0) };
    }

    /// Makes every [`hvc`] this thread issues from here on return `result`. It returns 0 until then.
    #[cfg(test)]
    pub fn answer(result: i64) {
        ANSWER.set(result);
    }

    /// Makes `register` keep its value across the writes this thread makes from here on, as a
    /// register that ignores writes does. The writes are still recorded.
    #[cfg(test)]
    pub fn ignore_writes(register: System) {
        IGNORED.with_borrow_mut(|ignored| ignored[register as usize] = true);
    }

    /// The bits a [`Block::hold`] keeps, by the word's address.
    #[cfg(test)]
    static HELD: std::sync::Mutex<Vec<(usize, u32)>> = std::sync::Mutex::new(Vec::new());

    /// Makes `register` hold `value` on this thread, recording nothing.
    #[cfg(test)]
    pub fn set(register: System, value: u64) {
        SYSTEM.with_borrow_mut(|system| system[register as usize] = value);
    }

    /// Takes what this thread did since the last call, in order.
    #[cfg(test)]
    pub fn events() -> Vec<Event> {
        EVENTS.take()
    }

    /// Device registers in the test's memory, all zero.
    #[cfg(test)]
    pub struct Block(Box<[AtomicU32]>);

    #[cfg(test)]
    impl Block {
        /// A page of registers.
        pub fn new() -> Self {
            Self::of(0x1000)
        }

        /// `bytes` of registers.
        pub fn of(bytes: usize) -> Self {
            Self((0..bytes / 4).map(|_| AtomicU32::new(0)).collect())
        }

        pub fn base(&self) -> usize {
            self.0.as_ptr() as usize
        }

        pub fn get(&self, offset: usize) -> u32 {
            self.0[offset / 4].load(Ordering::SeqCst)
        }

        pub fn set(&self, offset: usize, value: u32) {
            self.0[offset / 4].store(value, Ordering::SeqCst);
        }

        /// Makes the bits of `mask` in the word at `offset` keep their value across every
        /// [`store`], as read-only bits do, until [`Block::release`].
        pub fn hold(&self, offset: usize, mask: u32) {
            HELD.lock().unwrap().push((self.base() + offset, mask));
        }

        /// Ends every [`Block::hold`] on the word at `offset`.
        pub fn release(&self, offset: usize) {
            HELD.lock().unwrap().retain(|(register, _)| *register != self.base() + offset);
        }
    }

    /// Loads the word at `register`.
    ///
    /// # Safety
    ///
    /// `register` is a word of a [`Block`].
    pub unsafe fn load(register: usize) -> u32 {
        (*(register as *const AtomicU32)).load(Ordering::SeqCst)
    }

    /// Stores `value` to the word at `register`.
    ///
    /// # Safety
    ///
    /// `register` is a word of a [`Block`].
    pub unsafe fn store(register: usize, value: u32) {
        #[cfg(test)]
        let value = {
            EVENTS.with_borrow_mut(|events| events.push(Event::Store { register, value }));
            let held = HELD.lock().unwrap().iter().filter(|(word, _)| *word == register).fold(0, |all, (_, mask)| all | mask);
            value & !held | load(register) & held
        };
        (*(register as *const AtomicU32)).store(value, Ordering::SeqCst);
    }

    /// Loads the two words at `register`, the lower first.
    ///
    /// # Safety
    ///
    /// `register` is a pair of words of a [`Block`].
    pub unsafe fn load_wide(register: usize) -> u64 {
        u64::from(load(register)) | u64::from(load(register + 4)) << 32
    }

    /// Reads the value this thread keeps for `register`, and records the read.
    ///
    /// # Safety
    ///
    /// None is needed here; the signature is the aarch64 one.
    pub unsafe fn read(register: System) -> u64 {
        assert!(!matches!(register, System::IccEoir1 | System::IccSgi1r), "{:?} is write-only", register);
        #[cfg(test)]
        {
            EVENTS.with_borrow_mut(|events| events.push(Event::Read { register }));
            SYSTEM.with_borrow(|system| system[register as usize])
        }
        #[cfg(not(test))]
        0
    }

    /// Keeps `value` as `register` on this thread, and records the write.
    ///
    /// # Safety
    ///
    /// None is needed here; the signature is the aarch64 one.
    pub unsafe fn write(register: System, value: u64) {
        assert!(!matches!(register, System::Mpidr | System::IccIar1 | System::Cntpct), "{:?} is read-only", register);
        assert!(
            !matches!(register, System::Sctlr | System::Tcr | System::Mair),
            "{:?} is written by a core's entry alone",
            register
        );
        #[cfg(test)]
        {
            EVENTS.with_borrow_mut(|events| events.push(Event::Write { register, value }));
            if !IGNORED.with_borrow(|ignored| ignored[register as usize]) {
                set(register, value);
            }
        }
        #[cfg(not(test))]
        let _ = value;
    }

    /// Records the barrier.
    pub fn isb() {
        #[cfg(test)]
        EVENTS.with_borrow_mut(|events| events.push(Event::Isb));
    }

    /// Records the barrier.
    pub fn dsb() {
        #[cfg(test)]
        EVENTS.with_borrow_mut(|events| events.push(Event::Dsb));
    }

    /// Records the clean.
    ///
    /// # Safety
    ///
    /// None is needed here; the signature is the aarch64 one.
    pub unsafe fn clean(start: usize, bytes: usize) {
        #[cfg(test)]
        EVENTS.with_borrow_mut(|events| events.push(Event::Clean { start, bytes }));
        #[cfg(not(test))]
        let _ = (start, bytes);
    }

    /// Records the call and returns what the test's thread answers, 0 unless it said otherwise. It
    /// returns, as no PSCI function that changes the machine's power does.
    ///
    /// # Safety
    ///
    /// None is needed here; the signature is the aarch64 one.
    pub unsafe fn hvc(function: u32, arguments: [u64; 3]) -> i64 {
        #[cfg(test)]
        {
            EVENTS.with_borrow_mut(|events| events.push(Event::Hvc { function, arguments }));
            ANSWER.with_borrow(|answer| *answer)
        }
        #[cfg(not(test))]
        {
            let _ = (function, arguments);
            0
        }
    }

    /// Yields to the other threads.
    pub fn wait() {
        core::hint::spin_loop();
    }
}
