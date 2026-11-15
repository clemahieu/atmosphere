// SPDX-License-Identifier: MIT

//! Hardware counter and serialized timestamp sources.

use core::arch::asm;

/// Number of extended core performance counters exposed via `RDPMC` when available.
pub const PMU_COUNT: usize = 4;

/// Dotted label suffixes for the four hardware PMU counters read from counters `0..3`.
pub const PMU_SUFFIXES: [&str; PMU_COUNT] = ["cycles", "instructions", "fills", "ccx_fills"];

/// Units matching each PMU counter suffix in `fuchsiaperf.json`.
pub const PMU_UNITS: [&str; PMU_COUNT] = ["cycles", "instructions", "count", "count"];

/// One sample point taken before or after a batch or step.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Snapshot {
    /// Serialized hardware timestamp (`TSC` on `x86_64`, `CNTVCT_EL0` on `aarch64`).
    pub tsc: u64,
    /// Performance counters `[cycles, instructions, fills, ccx_fills]` when enabled and supported.
    pub pmu: Option<[u64; PMU_COUNT]>,
}

/// Source of timestamps, optional PMU counts, and optional tick frequency.
pub trait CounterSource {
    /// Reads a serialized snapshot of the hardware counter(s).
    fn snapshot(&mut self) -> Snapshot;

    /// Returns the counter tick rate in Hz if calibrated in the current environment.
    fn ticks_per_second(&self) -> Option<u64>;
}

/// Computes `after.wrapping_sub(before)` without overflowing on counter wraparound.
#[inline]
pub const fn counter_delta(before: u64, after: u64) -> u64 {
    after.wrapping_sub(before)
}

/// Default hardware counter source reading serialized TSC (`CNTVCT_EL0` on aarch64) and `RDPMC`.
#[derive(Clone, Copy, Debug)]
pub struct HardwareCounters {
    enable_pmu: bool,
    pmu_available: bool,
    tsc_hz: Option<u64>,
}

impl HardwareCounters {
    /// Creates a hardware counter source, checking CPUID once for extended core PMU support.
    pub fn new(enable_pmu: bool) -> Self {
        Self {
            enable_pmu,
            pmu_available: has_perf_ctr_ext_core(),
            tsc_hz: default_ticks_per_second(),
        }
    }

    /// Overrides the tick frequency used to convert raw ticks into `"nanoseconds"`.
    pub const fn with_ticks_per_second(mut self, tsc_hz: Option<u64>) -> Self {
        self.tsc_hz = tsc_hz;
        self
    }

    /// Returns whether PMU readings will be collected.
    pub const fn pmu_active(&self) -> bool {
        self.enable_pmu && self.pmu_available
    }
}

impl CounterSource for HardwareCounters {
    #[inline]
    fn snapshot(&mut self) -> Snapshot {
        let tsc = read_tsc_fenced();
        let pmu = if self.pmu_active() {
            read_pmu_unchecked()
        } else {
            None
        };
        Snapshot { tsc, pmu }
    }

    fn ticks_per_second(&self) -> Option<u64> {
        self.tsc_hz
    }
}

/// Reads a serialized timestamp counter (`lfence; rdtsc; lfence` on x86_64, `isb; mrs cntvct_el0` on aarch64).
#[inline]
pub fn read_tsc_fenced() -> u64 {
    #[cfg(target_arch = "x86_64")]
    {
        let lo: u32;
        let hi: u32;
        unsafe {
            asm!(
                "lfence",
                "rdtsc",
                "lfence",
                out("eax") lo,
                out("edx") hi,
                options(nomem, nostack, preserves_flags)
            );
        }
        ((hi as u64) << 32) | (lo as u64)
    }
    #[cfg(target_arch = "aarch64")]
    {
        let ticks: u64;
        unsafe {
            asm!(
                "isb",
                "mrs {ticks}, cntvct_el0",
                ticks = out(reg) ticks,
                options(nomem, nostack, preserves_flags)
            );
        }
        ticks
    }
}

/// Returns whether the core advertises extended core performance counters usable with `RDPMC`.
pub fn has_perf_ctr_ext_core() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        /// CPUID Fn8000_0001 ECX bit 23, PerfCtrExtCore. AMD APM 2 §13.2.2.
        const PERF_CTR_EXT_CORE: u32 = 1 << 23;
        core::arch::x86_64::__cpuid(0x8000_0000).eax >= 0x8000_0001
            && (core::arch::x86_64::__cpuid(0x8000_0001).ecx & PERF_CTR_EXT_CORE) != 0
    }
    #[cfg(target_arch = "aarch64")]
    {
        false
    }
}

#[inline]
fn read_pmu_unchecked() -> Option<[u64; PMU_COUNT]> {
    #[cfg(target_arch = "x86_64")]
    {
        let mut counts = [0u64; PMU_COUNT];
        for (n, count) in counts.iter_mut().enumerate() {
            let lo: u32;
            let hi: u32;
            unsafe {
                asm!(
                    "rdpmc",
                    in("ecx") n as u32,
                    out("eax") lo,
                    out("edx") hi,
                    options(nomem, nostack, preserves_flags)
                );
            }
            *count = ((hi as u64) << 32) | (lo as u64);
        }
        Some(counts)
    }
    #[cfg(target_arch = "aarch64")]
    {
        None
    }
}

/// Reads extended core PMU counters `0..3` via `RDPMC`, or `None` when unavailable.
pub fn read_pmu_counters() -> Option<[u64; PMU_COUNT]> {
    if !has_perf_ctr_ext_core() {
        return None;
    }
    read_pmu_unchecked()
}

/// Returns the hardware counter frequency in Hz when readable directly by user space.
pub fn default_ticks_per_second() -> Option<u64> {
    #[cfg(target_arch = "x86_64")]
    {
        None
    }
    #[cfg(target_arch = "aarch64")]
    {
        /// CNTFRQ_EL0 holds the counter frequency in bits 31:0. Arm ARM D24.10.15.
        const FREQUENCY_MASK: u64 = 0xffff_ffff;
        let frequency: u64;
        unsafe {
            asm!(
                "mrs {frequency}, cntfrq_el0",
                frequency = out(reg) frequency,
                options(nomem, nostack, preserves_flags)
            );
        }
        let hz = frequency & FREQUENCY_MASK;
        (hz != 0).then_some(hz)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counter_delta_handles_wraparound() {
        assert_eq!(counter_delta(100, 150), 50);
        assert_eq!(counter_delta(u64::MAX - 9, 10), 20);
    }

    #[test]
    fn read_tsc_fenced_is_monotonic_on_host() {
        let t0 = read_tsc_fenced();
        let t1 = read_tsc_fenced();
        assert!(t1 >= t0, "t1={t1} < t0={t0}");
    }
}
