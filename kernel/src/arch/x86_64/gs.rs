//! GS-relative reads of this core's [`crate::cpu::Cpu`].

#[macro_export]
macro_rules! read_current_cpu_offset {
    ($offset:expr) => {{
        let value: u64;
        unsafe {
            core::arch::asm!(
                "mov {result}, gs:[{offset}]",
                offset = const $offset,
                result = out(reg) value,
            );
        }
        value
    }};
}

#[macro_export]
macro_rules! read_current_cpu_field {
    ($field:ident) => {
        $crate::read_current_cpu_offset!(memoffset::offset_of!($crate::cpu::Cpu, $field))
    };
}

#[macro_export]
macro_rules! get_current_cpu_field_ptr {
    ($field:ident, $type:ty) => {{
        let mut address: u64 = memoffset::offset_of!($crate::cpu::Cpu, $field) as u64;
        #[allow(unused_unsafe)] // nested unsafe
        unsafe {
            core::arch::asm!(
                "add {result}, gs:{self_offset}",
                self_offset = const memoffset::offset_of!($crate::cpu::Cpu, self_ptr),
                result = inout(reg) address => address,
                options(pure, readonly),
            );
        }
        address as *mut $type
    }};
}
