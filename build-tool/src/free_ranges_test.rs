//! Host runs of the loader map check. The kernel builds the same file.

#[path = "../../kernel/src/boot/free_ranges.rs"]
mod free_ranges;

use std::panic::{catch_unwind, AssertUnwindSafe};

use astd::boot::PhysicalMemoryType;
use free_ranges::{free_page_ranges, ByteRange, PageRun, MAX_PAGE_ADDRESS, NODE_SPACE, PAGE_SLOTS};

use PhysicalMemoryType::{Available, Domain, Kernel, Reserved};

fn range(base: u64, size: u64) -> ByteRange {
    ByteRange { base, size }
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
    pages: &[(u64, PhysicalMemoryType)],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
    out_len: usize,
) -> Result<Vec<PageRun>, String> {
    let mut seen = vec![0u8; PAGE_SLOTS];
    let mut out = vec![PageRun { first: 0, count: 0 }; out_len];
    match catch_unwind(AssertUnwindSafe(|| {
        free_page_ranges(
            pages,
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
    pages: &[(u64, PhysicalMemoryType)],
    aside: &[ByteRange],
    kernel_image: ByteRange,
    dom0_reserved: Option<ByteRange>,
) -> String {
    let message =
        runs(pages, aside, kernel_image, dom0_reserved, 8).expect_err("the map is not free ranges");
    println!("free page ranges: rejected {message}");
    message
}

#[test]
fn free_page_unaligned_is_rejected() {
    let message = rejected(&[(0x100, Available)], &[], range(0, 0), None);
    assert!(message.contains("0x100"), "{message}");
    assert!(message.contains("not 4 KiB aligned"), "{message}");
}

#[test]
fn free_page_repeated_or_overlapping_is_rejected() {
    let pages = [(0x2000, Reserved), (0x1000, Available), (0x1000, Kernel)];
    let message = rejected(&pages, &[], range(0, 0), None);
    assert!(message.contains("0x1000"), "{message}");
    assert!(
        message.contains("listed twice or overlaps another page"),
        "{message}"
    );
}

#[test]
fn free_page_out_of_range_is_rejected() {
    for address in [MAX_PAGE_ADDRESS, NODE_SPACE] {
        let message = rejected(&[(address, Available)], &[], range(0, 0), None);
        assert!(message.contains(&format!("{address:#x}")), "{message}");
        assert!(
            message.contains("at or past NUM_PAGES * 4096 or NODE_SPACE"),
            "{message}"
        );
    }
}

#[test]
fn free_page_available_inside_kernel_or_dom0_is_rejected() {
    let kernel = rejected(&[(0x3000, Available)], &[], range(0x2800, 0x1000), None);
    assert!(kernel.contains("0x3000"), "{kernel}");
    assert!(
        kernel.contains("available page inside the kernel image"),
        "{kernel}"
    );

    let dom0 = rejected(
        &[(0x4000, Available)],
        &[],
        range(0, 0),
        Some(range(0x4000, 0x1000)),
    );
    assert!(dom0.contains("0x4000"), "{dom0}");
    assert!(
        dom0.contains("available page inside dom0's reserved range"),
        "{dom0}"
    );
}

#[test]
fn free_page_ranges_take_set_aside_pages_out() {
    // Shuffled, with a hole and a non-available page, so a run is maximal only over free pages.
    let pages = [
        (0xa000, Available),
        (0x0000, Available),
        (0x7000, Available),
        (0x3000, Kernel),
        (0x1000, Available),
        (0x5000, Available),
        (0x8000, Available),
        (0x4000, Reserved),
        (0x6000, Available),
        (0x2000, Available),
        (0x9000, Domain),
    ];
    let aside = [
        range(0x2000, 0x1000),
        range(0x5000, 0x1000),
        range(0x6000, 0x1000),
        range(0x7000, 0x1000),
    ];
    let got = runs(
        &pages,
        &aside,
        range(0x3000, 0x1000),
        Some(range(0x4000, 0x1000)),
        8,
    )
    .expect("well-formed map");
    let line = got
        .iter()
        .map(|run| format!("{:#x}+{}", run.first, run.count))
        .collect::<Vec<_>>()
        .join(" ");
    println!("free page ranges: {line}");
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
