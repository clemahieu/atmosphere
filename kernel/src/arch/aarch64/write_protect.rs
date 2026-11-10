//! The check that EL1 cannot write through a read-only mapping.

/// Writes through a read-only leaf on the calling core and stops the machine unless the write
/// faults. The fault arrives through the exception vectors, which this core does not have, so the
/// check stops, naming itself.
pub unsafe fn check() {
    unimplemented!("write_protect::check");
}
