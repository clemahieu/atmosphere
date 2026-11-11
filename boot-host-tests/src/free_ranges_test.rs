// SPDX-License-Identifier: MIT

//! Host runs of the loader map check. The kernel builds the same file.

#[path = "../../kernel/src/boot/free_ranges.rs"]
mod free_ranges;

use std::panic::{catch_unwind, AssertUnwindSafe};

use astd::boot::{PhysicalMemoryType, PhysicalRange};
use free_ranges::{free_page_ranges, ByteRange, PageRun, MAX_PAGE_ADDRESS, NODE_SPACE, PAGE_SLOTS};

use PhysicalMemoryType::{Available, Domain, Kernel, Reserved};

fn range(base: u64, size: u64) -> ByteRange {
    ByteRange { base, size }
}

fn memory(base: u64, bytes: u64, kind: PhysicalMemoryType) -> PhysicalRange {
    PhysicalRange { base, bytes, kind }
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else {
        "non-string panic".to_string()
    }
}

fn runs(
    ranges: &[PhysicalRange],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
    out_len: usize,
) -> Result<Vec<PageRun>, String> {
    let mut seen = vec![0u8; PAGE_SLOTS];
    let mut out = vec![PageRun { first: 0, count: 0 }; out_len];
    match catch_unwind(AssertUnwindSafe(|| {
        free_page_ranges(
            ranges,
            &mut seen,
            aside,
            kernel_image,
            dom0_reserved,
            &mut out,
        )
    })) {
        Ok(count) => Ok(out[..count].to_vec()),
        Err(payload) => Err(panic_message(payload)),
    }
}

fn rejected(
    ranges: &[PhysicalRange],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
) -> String {
    let message = runs(ranges, aside, kernel_image, dom0_reserved, 8)
        .expect_err("the map is not free ranges");
    println!("free page ranges: rejected {message}");
    message
}

fn line(runs: &[PageRun]) -> String {
    runs.iter()
        .map(|run| format!("{:#x}+{}", run.first, run.count))
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn free_page_unaligned_is_rejected() {
    // A base inside a page, then a length that ends inside one.
    for (base, bytes, at) in [(0x100, 0x1000, "0x100"), (0x2000, 0x1800, "0x2000")] {
        let message = rejected(&[memory(base, bytes, Available)], &[], range(0, 0), None);
        assert!(message.contains(at), "{message}");
        assert!(message.contains("not 4 KiB aligned"), "{message}");
    }
}

#[test]
fn free_page_empty_range_is_rejected() {
    let message = rejected(&[memory(0x3000, 0, Reserved)], &[], range(0, 0), None);
    assert!(message.contains("0x3000"), "{message}");
    assert!(message.contains("empty range"), "{message}");
}

#[test]
fn free_page_repeated_or_overlapping_is_rejected() {
    // The same page listed twice, whatever the types say.
    let repeated = [
        memory(0x2000, 0x1000, Reserved),
        memory(0x1000, 0x1000, Available),
        memory(0x1000, 0x1000, Kernel),
    ];
    // Two ranges that share their middle: the first shared page is the later base.
    let overlapping = [
        memory(0x4000, 0x4000, Available),
        memory(0x6000, 0x4000, Available),
    ];
    // One range inside another, past the pages the kernel tracks.
    let nested = [
        memory(MAX_PAGE_ADDRESS, 0x10_0000, Reserved),
        memory(MAX_PAGE_ADDRESS + 0x8000, 0x1000, Available),
    ];
    for (ranges, at) in [
        (&repeated[..], 0x1000),
        (&overlapping[..], 0x6000),
        (&nested[..], MAX_PAGE_ADDRESS + 0x8000),
    ] {
        let message = rejected(ranges, &[], range(0, 0), None);
        assert!(message.contains(&format!("{at:#x}")), "{message}");
        assert!(
            message.contains("listed twice or overlaps another range"),
            "{message}"
        );
    }
}

#[test]
fn free_page_out_of_range_is_rejected() {
    // Starting at the node space's end, running across it, and wrapping the address space.
    for (base, bytes) in [
        (NODE_SPACE, 0x1000),
        (NODE_SPACE - 0x1000, 0x2000),
        (0x1000, u64::MAX - 0xfff),
    ] {
        let message = rejected(&[memory(base, bytes, Available)], &[], range(0, 0), None);
        assert!(message.contains(&format!("{base:#x}")), "{message}");
        assert!(message.contains("runs past NODE_SPACE"), "{message}");
    }
}

#[test]
fn free_page_available_inside_kernel_or_dom0_is_rejected() {
    // The image starts inside the range's second page.
    let kernel = rejected(
        &[memory(0x2000, 0x4000, Available)],
        &[],
        range(0x3800, 0x1000),
        None,
    );
    assert!(kernel.contains("0x3000"), "{kernel}");
    assert!(
        kernel.contains("available page inside the kernel image"),
        "{kernel}"
    );

    // The reservation starts below the range.
    let dom0 = rejected(
        &[memory(0x4000, 0x2000, Available)],
        &[],
        range(0, 0),
        Some(range(0x3000, 0x2000)),
    );
    assert!(dom0.contains("0x4000"), "{dom0}");
    assert!(
        dom0.contains("available page inside dom0's reserved range"),
        "{dom0}"
    );
}

#[test]
fn free_page_ranges_take_set_aside_pages_out() {
    // Shuffled, with a hole and ranges that are not available, so a run is maximal only over
    // free pages, and two available ranges that touch make one run.
    let ranges = [
        memory(0xa000, 0x1000, Available),
        memory(0x0000, 0x1000, Available),
        memory(0x5000, 0x4000, Available),
        memory(0x3000, 0x1000, Kernel),
        memory(0x1000, 0x2000, Available),
        memory(0x4000, 0x1000, Reserved),
        memory(0x9000, 0x1000, Domain),
    ];
    let aside = [range(0x2000, 0x1000), range(0x5000, 0x3000)];
    let got = runs(
        &ranges,
        &aside,
        range(0x3000, 0x1000),
        Some(range(0x4000, 0x1000)),
        8,
    )
    .expect("well-formed map");
    println!("free page ranges: {}", line(&got));
    assert_eq!(
        got,
        vec![
            PageRun {
                first: 0x0000,
                count: 2
            },
            PageRun {
                first: 0x8000,
                count: 1
            },
            PageRun {
                first: 0xa000,
                count: 1
            },
        ]
    );
}

#[test]
fn free_page_ranges_stop_at_the_tracked_pages() {
    // Memory the kernel does not track is left unused, not refused: an available range that
    // crosses the limit gives its tracked pages, and ranges past the limit give none.
    let ranges = [
        memory(MAX_PAGE_ADDRESS - 0x3000, 0x10_0000, Available),
        memory(MAX_PAGE_ADDRESS + 0x1000_0000, 0x1000_0000, Available),
        memory(0xe000_0000, 0x1000_0000, Reserved),
    ];
    let aside = [range(MAX_PAGE_ADDRESS - 0x1000, 0x8000)];
    let got = runs(&ranges, &aside, range(0, 0), None, 8).expect("well-formed map");
    println!("free page ranges: past the tracked pages: {}", line(&got));
    assert_eq!(
        got,
        vec![PageRun {
            first: MAX_PAGE_ADDRESS - 0x3000,
            count: 2
        }]
    );
}

#[test]
fn free_page_runs_that_do_not_fit_are_rejected() {
    let ranges = [
        memory(0x0000, 0x1000, Available),
        memory(0x2000, 0x1000, Available),
    ];
    let message = runs(&ranges, &[], range(0, 0), None, 1).expect_err("two runs, room for one");
    println!("free page ranges: rejected {message}");
    assert!(message.contains("0x2000"), "{message}");
    assert!(message.contains("free ranges do not fit"), "{message}");
}
