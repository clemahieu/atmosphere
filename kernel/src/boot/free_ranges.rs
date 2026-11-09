#![allow(dead_code)]
//! Folds the loader's memory map into the free runs boot can hand the root.
//!
//! The map crosses the trust boundary, so a range that is empty, is not 4 KiB aligned, runs past
//! the node space, shares a page with another range, or is available inside the kernel image or
//! dom0's reserved range is a boot panic. Memory past the pages the kernel tracks is left unused.
//! Pages set aside for the kernel, the root's own boot objects and the 2M regions of dom0's image
//! are taken out of the runs. Why the boundary is tier 3: design/trust-boundary/. What boot sets
//! aside: design/root-process-at-boot/.

use astd::boot::{PhysicalMemoryType, PhysicalRange, PAGE_BYTES};

/// Pages the kernel tracks. `boot/mod.rs` checks this against `verified::define::NUM_PAGES`.
pub const PAGE_SLOTS: usize = 512 * 1024;

/// First address that is not a tracked page.
pub const MAX_PAGE_ADDRESS: u64 = (PAGE_SLOTS as u64) * PAGE_BYTES;

/// First address that is not a node id. `boot/mod.rs` checks this against the list's `NODE_SPACE`.
pub const NODE_SPACE: u64 = 0x1_0000_0000_0000;

// A free run is made of tracked pages, so every page of one is a node id.
const _: () = assert!(MAX_PAGE_ADDRESS <= NODE_SPACE);

const TAKEN: u8 = 0;
const FREE: u8 = 1;

/// A half-open physical range `[base, base + size)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteRange {
    pub base: u64,
    pub size: u64,
}

impl ByteRange {
    fn end(self) -> u64 {
        self.base.saturating_add(self.size)
    }

    /// The address of the first page of `[base, end)`, which starts and ends on pages, that holds a
    /// byte of this range.
    fn first_page_in(self, base: u64, end: u64) -> Option<u64> {
        if self.size == 0 || self.base >= end || self.end() <= base {
            return None;
        }
        Some(base.max(self.base / PAGE_BYTES * PAGE_BYTES))
    }
}

/// A maximal run of free pages. `first` is the physical address of the first page.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PageRun {
    pub first: u64,
    pub count: u64,
}

struct Reject {
    address: u64,
    reason: &'static str,
}

/// Folds `ranges` into maximal free runs written at `out`, in address order.
///
/// `seen` is one byte per tracked page; it must be `PAGE_SLOTS` long and is cleared here. `aside`
/// is the pages boot keeps for the kernel, the root's process, thread and table leaves, the list's
/// synthetic root and the 2M regions of dom0's image. Returns how many runs were written. A range
/// the loader was not allowed to hand over panics with the address at fault and the reason.
pub fn free_page_ranges(
    ranges: &[PhysicalRange],
    seen: &mut [u8],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
    out: &mut [PageRun],
) -> usize {
    match fold(ranges, seen, aside, kernel_image, dom0_reserved, out) {
        Ok(count) => count,
        Err(reject) => panic!("boot memory map: {:#x}: {}", reject.address, reject.reason),
    }
}

/// The page numbers of `[base, end)` that the kernel tracks, with the range's edges moved out to
/// pages.
fn tracked(base: u64, end: u64) -> core::ops::Range<usize> {
    let first = base.min(MAX_PAGE_ADDRESS) / PAGE_BYTES;
    let last = end.min(MAX_PAGE_ADDRESS).div_ceil(PAGE_BYTES);
    first as usize..last as usize
}

fn fold(
    ranges: &[PhysicalRange],
    seen: &mut [u8],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
    out: &mut [PageRun],
) -> Result<usize, Reject> {
    assert!(seen.len() == PAGE_SLOTS);
    seen.fill(TAKEN);

    for range in ranges {
        let address = range.base;
        if range.bytes == 0 {
            return Err(Reject {
                address,
                reason: "empty range",
            });
        }
        if range.base % PAGE_BYTES != 0 || range.bytes % PAGE_BYTES != 0 {
            return Err(Reject {
                address,
                reason: "not 4 KiB aligned",
            });
        }
        match range.base.checked_add(range.bytes) {
            Some(end) if end <= NODE_SPACE => {}
            _ => {
                return Err(Reject {
                    address,
                    reason: "runs past NODE_SPACE",
                })
            }
        }
    }

    for (index, range) in ranges.iter().enumerate() {
        for earlier in &ranges[..index] {
            if range.base < earlier.base + earlier.bytes && earlier.base < range.base + range.bytes
            {
                return Err(Reject {
                    address: range.base.max(earlier.base),
                    reason: "listed twice or overlaps another range",
                });
            }
        }
    }

    for range in ranges {
        if range.kind != PhysicalMemoryType::Available {
            continue;
        }
        let end = range.base + range.bytes;
        if let Some(address) = kernel_image.first_page_in(range.base, end) {
            return Err(Reject {
                address,
                reason: "available page inside the kernel image",
            });
        }
        if let Some(address) =
            dom0_reserved.and_then(|reserved| reserved.first_page_in(range.base, end))
        {
            return Err(Reject {
                address,
                reason: "available page inside dom0's reserved range",
            });
        }
        seen[tracked(range.base, end)].fill(FREE);
    }
    for reserved in aside {
        if reserved.size != 0 {
            seen[tracked(reserved.base, reserved.end())].fill(TAKEN);
        }
    }

    let mut written = 0;
    let mut index = 0;
    while index < seen.len() {
        if seen[index] != FREE {
            index += 1;
            continue;
        }
        let start = index;
        while index < seen.len() && seen[index] == FREE {
            index += 1;
        }
        let first = (start as u64) * PAGE_BYTES;
        if written >= out.len() {
            return Err(Reject {
                address: first,
                reason: "free ranges do not fit",
            });
        }
        out[written] = PageRun {
            first,
            count: (index - start) as u64,
        };
        written += 1;
    }
    Ok(written)
}
