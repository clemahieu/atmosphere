// SPDX-License-Identifier: MIT

//! `rdmsr` and `wrmsr` of `IA32_APIC_BASE`. The kernel keeps the MSRs it writes itself.

use core::arch::asm;

/// The local APIC's base address and enables. APM 2 §16.3.1, Figure 16-2.
pub const APIC_BASE: u32 = 0x0000_001B;

/// APM 2 §6.2.5.
pub unsafe fn rdmsr(msr: u32) -> u64 {
    let (low, high): (u32, u32);
    asm!("rdmsr", in("ecx") msr, out("eax") low, out("edx") high, options(nomem, nostack, preserves_flags));
    (high as u64) << 32 | low as u64
}

pub unsafe fn wrmsr(msr: u32, value: u64) {
    asm!(
        "wrmsr",
        in("ecx") msr,
        in("eax") value as u32,
        in("edx") (value >> 32) as u32,
        options(nostack, preserves_flags),
    );
}
