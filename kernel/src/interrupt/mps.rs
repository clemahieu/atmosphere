//! Finding the IOAPIC.

const FALLBACK_IOAPIC_BASE: usize = 0xfec0_0000;

/// The IOAPIC's base address, which is the architectural default on the machines this runs on.
pub unsafe fn probe_ioapic() -> usize {
    FALLBACK_IOAPIC_BASE
}
