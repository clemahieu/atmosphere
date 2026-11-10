//! The instructions this crate issues itself: the load and the store of a device register, the
//! hypervisor call and the wait for an interrupt. On another architecture the crate is built for its
//! tests, where a register is a word of the test's own memory and each store and call is recorded.

#[cfg(target_arch = "aarch64")]
pub use aarch64::{hvc, load, store, wait};
#[cfg(test)]
pub use host::{events, Block, Event};
#[cfg(not(target_arch = "aarch64"))]
pub use host::{hvc, load, store, wait};

#[cfg(target_arch = "aarch64")]
mod aarch64 {
    use core::arch::asm;

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

    /// Calls the PSCI function `function`, which takes no argument.
    ///
    /// The conduit is `hvc`, as QEMU virt's device tree says (node `psci`, `method = "hvc"`). The
    /// function id goes in W0 and the instruction's immediate is 0 (PSCI, ARM DEN 0022, 5.2.1).
    ///
    /// # Safety
    ///
    /// The caller accepts what `function` does to the machine.
    pub unsafe fn hvc(function: u32) {
        asm!(
            "hvc #0",
            inout("x0") u64::from(function) => _,
            clobber_abi("C"),
            options(nostack),
        );
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

    /// What a test's thread did to the machine.
    #[cfg(test)]
    #[derive(Debug, PartialEq)]
    pub enum Event {
        Store { register: usize, value: u32 },
        Hvc { function: u32 },
    }

    #[cfg(test)]
    std::thread_local! {
        static EVENTS: RefCell<Vec<Event>> = const { RefCell::new(Vec::new()) };
    }

    /// Takes what this thread did since the last call, in order.
    #[cfg(test)]
    pub fn events() -> Vec<Event> {
        EVENTS.take()
    }

    /// A page of device registers in the test's memory, all zero.
    #[cfg(test)]
    pub struct Block(Box<[AtomicU32; 1024]>);

    #[cfg(test)]
    impl Block {
        pub fn new() -> Self {
            Self(Box::new([const { AtomicU32::new(0) }; 1024]))
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
        EVENTS.with_borrow_mut(|events| events.push(Event::Store { register, value }));
        (*(register as *const AtomicU32)).store(value, Ordering::SeqCst);
    }

    /// Records the call. It returns, as no PSCI function that changes the machine's power does.
    ///
    /// # Safety
    ///
    /// None is needed here; the signature is the aarch64 one.
    pub unsafe fn hvc(function: u32) {
        #[cfg(test)]
        EVENTS.with_borrow_mut(|events| events.push(Event::Hvc { function }));
        #[cfg(not(test))]
        let _ = function;
    }

    /// Yields to the other threads.
    pub fn wait() {
        core::hint::spin_loop();
    }
}
