#![allow(dead_code)]
// SPDX-License-Identifier: MIT

//! Checks the runs the loader recorded for dom0.
//!
//! The list crosses the trust boundary. A run that is empty, not 4 KiB aligned, sits outside
//! dom0's reservation, falls in the low entries a process space keeps for the kernel, leaves the
//! user half, or overlaps another run's physical or virtual pages is a boot panic. Why the
//! boundary is tier 3: design/trust-boundary/. The root's space is built from the runs that pass:
//! design/address-spaces-as-objects/.

use astd::boot::{MappedRun, PAGE_BYTES};
use astd::memory::USERSPACE_BASE;

/// First address of the upper canonical half. A user mapping stays below it.
const USER_HALF_END: u64 = 1 << 47;

struct Reject {
    address: u64,
    reason: &'static str,
}

/// Checks `runs` against dom0's physical reservation `[reservation_phys, reservation_phys +
/// reservation_len)`.
///
/// Returns how many runs passed. A run the loader was not allowed to record panics with that
/// run's address and the reason.
pub fn mapped_runs(runs: &[MappedRun], reservation_phys: u64, reservation_len: u64) -> usize {
    match check(runs, reservation_phys, reservation_len) {
        Ok(()) => runs.len(),
        Err(reject) => panic!("boot mapped runs: {:#x}: {}", reject.address, reject.reason),
    }
}

fn check(runs: &[MappedRun], reservation_phys: u64, reservation_len: u64) -> Result<(), Reject> {
    for run in runs {
        run_bytes(run, reservation_phys, reservation_len)?;
    }
    for later in 0..runs.len() {
        for earlier in 0..later {
            if overlaps(
                runs[later].phys,
                runs[later].pages * PAGE_BYTES,
                runs[earlier].phys,
                runs[earlier].pages * PAGE_BYTES,
            ) {
                return Err(Reject {
                    address: runs[later].phys,
                    reason: "overlaps another run's physical pages",
                });
            }
        }
    }
    for later in 0..runs.len() {
        for earlier in 0..later {
            if overlaps(
                runs[later].virt,
                runs[later].pages * PAGE_BYTES,
                runs[earlier].virt,
                runs[earlier].pages * PAGE_BYTES,
            ) {
                return Err(Reject {
                    address: runs[later].virt,
                    reason: "overlaps another run's virtual pages",
                });
            }
        }
    }
    Ok(())
}

fn run_bytes(run: &MappedRun, reservation_phys: u64, reservation_len: u64) -> Result<u64, Reject> {
    if run.pages == 0 {
        return Err(Reject {
            address: run.virt,
            reason: "empty",
        });
    }
    if run.virt % PAGE_BYTES != 0 {
        return Err(Reject {
            address: run.virt,
            reason: "not 4 KiB aligned",
        });
    }
    if run.phys % PAGE_BYTES != 0 {
        return Err(Reject {
            address: run.phys,
            reason: "not 4 KiB aligned",
        });
    }
    let bytes = run.pages.checked_mul(PAGE_BYTES).ok_or(Reject {
        address: run.phys,
        reason: "outside dom0's reservation",
    })?;
    let phys_end = run.phys.checked_add(bytes).ok_or(Reject {
        address: run.phys,
        reason: "outside dom0's reservation",
    })?;
    let reservation_end = reservation_phys
        .checked_add(reservation_len)
        .ok_or(Reject {
            address: run.phys,
            reason: "outside dom0's reservation",
        })?;
    if run.phys < reservation_phys || phys_end > reservation_end {
        return Err(Reject {
            address: run.phys,
            reason: "outside dom0's reservation",
        });
    }
    if run.virt < USERSPACE_BASE {
        return Err(Reject {
            address: run.virt,
            reason: "in the kernel's entries",
        });
    }
    let virt_end = run.virt.checked_add(bytes).ok_or(Reject {
        address: run.virt,
        reason: "not in the user half",
    })?;
    if virt_end > USER_HALF_END {
        return Err(Reject {
            address: run.virt,
            reason: "not in the user half",
        });
    }
    Ok(bytes)
}

fn overlaps(later: u64, later_bytes: u64, earlier: u64, earlier_bytes: u64) -> bool {
    later < earlier.saturating_add(earlier_bytes) && earlier < later.saturating_add(later_bytes)
}
