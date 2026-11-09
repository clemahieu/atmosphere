#![allow(dead_code)]
//! Folds the loader's page list into the free runs boot can hand the root.
//!
//! The list crosses the trust boundary, so a page that is not 4 KiB aligned, is listed twice, sits
//! at or past the page limit or the node space, or is available inside the kernel image or dom0's
//! reserved range is a boot panic. Pages set aside for the root's own boot objects are taken out of
//! the runs. Why the boundary is tier 3: design/trust-boundary/. What boot sets aside:
//! design/root-process-at-boot/.

use astd::boot::PhysicalMemoryType;

/// Bytes in a page. The loader's list is one entry per page.
pub const PAGE_BYTES: u64 = 4096;

/// Pages the kernel tracks. `boot/mod.rs` checks this against `verified::define::NUM_PAGES`.
pub const PAGE_SLOTS: usize = 2 * 1024 * 1024;

/// First address that is not a tracked page.
pub const MAX_PAGE_ADDRESS: u64 = (PAGE_SLOTS as u64) * PAGE_BYTES;

/// First address that is not a node id. `boot/mod.rs` checks this against the list's `NODE_SPACE`.
pub const NODE_SPACE: u64 = 0x1_0000_0000_0000;

const EMPTY: u8 = 0;
const LISTED: u8 = 1;
const FREE: u8 = 2;

/// A half-open physical range `[base, base + size)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ByteRange {
    pub base: u64,
    pub size: u64,
}

impl ByteRange {
    fn overlaps_page(self, address: u64) -> bool {
        self.size != 0
            && address < self.base.saturating_add(self.size)
            && address.saturating_add(PAGE_BYTES) > self.base
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

/// Folds `pages` into maximal free runs written at `out`.
///
/// `seen` is one byte per tracked page; it must be `PAGE_SLOTS` long and is cleared here. `aside`
/// is the pages boot keeps for the root's process, thread, table leaf and the list's synthetic
/// root. Returns how many runs were written. A page the loader was not allowed to hand over panics
/// with that page's address and the reason.
pub fn free_page_ranges(
    pages: &[(u64, PhysicalMemoryType)],
    seen: &mut [u8],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
    out: &mut [PageRun],
) -> usize {
    match fold(pages, seen, aside, kernel_image, dom0_reserved, out) {
        Ok(count) => count,
        Err(reject) => panic!("boot memory map: {:#x}: {}", reject.address, reject.reason),
    }
}

fn fold(
    pages: &[(u64, PhysicalMemoryType)],
    seen: &mut [u8],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
    out: &mut [PageRun],
) -> Result<usize, Reject> {
    assert!(seen.len() == PAGE_SLOTS);
    seen.fill(EMPTY);

    for &(address, _) in pages {
        if address % PAGE_BYTES != 0 {
            return Err(Reject {
                address,
                reason: "not 4 KiB aligned",
            });
        }
        if address >= NODE_SPACE || address >= MAX_PAGE_ADDRESS {
            return Err(Reject {
                address,
                reason: "at or past NUM_PAGES * 4096 or NODE_SPACE",
            });
        }
    }

    for &(address, kind) in pages {
        let index = (address / PAGE_BYTES) as usize;
        if seen[index] != EMPTY {
            return Err(Reject {
                address,
                reason: "listed twice or overlaps another page",
            });
        }
        if kind == PhysicalMemoryType::Available && kernel_image.overlaps_page(address) {
            return Err(Reject {
                address,
                reason: "available page inside the kernel image",
            });
        }
        if kind == PhysicalMemoryType::Available
            && dom0_reserved.is_some_and(|reserved| reserved.overlaps_page(address))
        {
            return Err(Reject {
                address,
                reason: "available page inside dom0's reserved range",
            });
        }
        let set_aside = aside.iter().any(|reserved| reserved.overlaps_page(address));
        seen[index] = if kind == PhysicalMemoryType::Available && !set_aside {
            FREE
        } else {
            LISTED
        };
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
