//! Host runs of the dom0 mapping check. The kernel builds the same file.

#[path = "../../kernel/src/boot/mapped_runs.rs"]
mod mapped_runs;

use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;

use astd::boot::{
    disjoint_page_runs, page_end, page_start, MappedRun, SegmentSpan, DOM0_RESERVATION, DOM0_STACK,
    PAGE_BYTES,
};
use astd::memory::{USERSPACE_BASE, USERSPACE_PAYLOAD_BASE};
use mapped_runs::mapped_runs;

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(message) = payload.downcast_ref::<String>() {
        message.clone()
    } else if let Some(message) = payload.downcast_ref::<&str>() {
        (*message).to_string()
    } else {
        "non-string panic".to_string()
    }
}

fn run(virt: u64, phys: u64, pages: u64, writable: bool, executable: bool) -> MappedRun {
    MappedRun {
        virt,
        phys,
        pages,
        writable,
        executable,
    }
}

fn check(runs: &[MappedRun], reservation_phys: u64, reservation_len: u64) -> Result<usize, String> {
    match catch_unwind(AssertUnwindSafe(|| {
        mapped_runs(runs, reservation_phys, reservation_len)
    })) {
        Ok(count) => Ok(count),
        Err(payload) => Err(panic_message(payload)),
    }
}

fn rejected(runs: &[MappedRun]) -> String {
    let (phys, len) = (0x1_0000_0000, DOM0_RESERVATION);
    let message = check(runs, phys, len).expect_err("the runs are not a dom0 map");
    println!("mapped runs: rejected {message}");
    message
}

fn artifact(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join(format!("../target/x86_64-unknown-aloader/debug/{name}"))
}

fn read_u16(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn read_u32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn read_u64(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

/// The runs `load_domain` records for the built dom0 and hello, against a synthetic reservation.
fn real_dom0_runs() -> (Vec<MappedRun>, u64) {
    let dom0 = fs::read(artifact("dom0")).expect("dom0 is built before this check");
    let hello_len = fs::metadata(artifact("hello"))
        .expect("hello is built before this check")
        .len();
    assert_eq!(&dom0[..4], b"\x7fELF", "dom0 is an ELF");
    assert_eq!(dom0[4], 2, "dom0 is ELFCLASS64");
    let phoff = read_u64(&dom0, 32) as usize;
    let phentsize = read_u16(&dom0, 54) as usize;
    let phnum = read_u16(&dom0, 56) as usize;
    assert!(phentsize >= 48 && phoff + phentsize * phnum <= dom0.len());

    let mut first_vaddr = None;
    let mut addr_min = u64::MAX;
    let mut addr_max = 0u64;
    let mut raw = Vec::new();
    for index in 0..phnum {
        let at = phoff + index * phentsize;
        if read_u32(&dom0, at) != 1 {
            continue;
        }
        let vaddr = read_u64(&dom0, at + 16);
        let memsz = read_u64(&dom0, at + 40);
        if memsz == 0 {
            continue;
        }
        if first_vaddr.is_none() {
            first_vaddr = Some(vaddr);
        }
        addr_min = addr_min.min(vaddr);
        addr_max = addr_max.max(vaddr + memsz);
        let flags = read_u32(&dom0, at + 4);
        raw.push((vaddr, memsz, flags & 2 != 0, flags & 1 != 0));
    }
    let first_vaddr = first_vaddr.expect("dom0 has a loadable segment");
    let load_addr = USERSPACE_BASE;
    let load_size = page_end(addr_max - addr_min);
    let load_bias = load_addr - page_start(first_vaddr);
    let phys_base = 0x1_0000_0000u64;

    let mut spans = Vec::new();
    for (vaddr, memsz, writable, executable) in raw {
        let start = page_start(load_bias + vaddr);
        let end = page_end(load_bias + vaddr + memsz);
        assert!(end > start);
        spans.push(SegmentSpan {
            virt: start,
            pages: (end - start) / PAGE_BYTES,
            writable,
            executable,
        });
    }
    let mut folded = [run(0, 0, 0, false, false); 64];
    let count = disjoint_page_runs(&spans, |virt| phys_base + (virt - load_addr), &mut folded)
        .expect("dom0 segments fit");
    let mut runs = folded[..count].to_vec();
    runs.push(run(
        USERSPACE_BASE + DOM0_RESERVATION - DOM0_STACK,
        phys_base + load_size,
        DOM0_STACK / PAGE_BYTES,
        true,
        false,
    ));
    let payload_pages = page_end(hello_len) / PAGE_BYTES;
    if payload_pages != 0 {
        runs.push(run(
            USERSPACE_PAYLOAD_BASE,
            phys_base + load_size + DOM0_STACK,
            payload_pages,
            true,
            false,
        ));
    }
    (runs, phys_base)
}

#[test]
fn mapped_run_unaligned_is_rejected() {
    let virt = rejected(&[run(USERSPACE_BASE + 0x100, 0x1_0000_0000, 1, true, false)]);
    assert!(virt.contains("0x8000000100"), "{virt}");
    assert!(virt.contains("not 4 KiB aligned"), "{virt}");

    let phys = rejected(&[run(USERSPACE_BASE, 0x1_0000_0100, 1, true, false)]);
    assert!(phys.contains("0x100000100"), "{phys}");
    assert!(phys.contains("not 4 KiB aligned"), "{phys}");
}

#[test]
fn mapped_run_empty_is_rejected() {
    let message = rejected(&[run(USERSPACE_BASE, 0x1_0000_0000, 0, true, false)]);
    assert!(message.contains("0x8000000000"), "{message}");
    assert!(message.contains("empty"), "{message}");
}

#[test]
fn mapped_run_outside_reservation_is_rejected() {
    let past = rejected(&[run(
        USERSPACE_BASE,
        0x1_0000_0000 + DOM0_RESERVATION,
        1,
        true,
        false,
    )]);
    assert!(past.contains("outside dom0's reservation"), "{past}");

    let huge = rejected(&[run(
        USERSPACE_BASE,
        0x1_0000_0000,
        DOM0_RESERVATION / PAGE_BYTES + 1,
        true,
        false,
    )]);
    assert!(huge.contains("outside dom0's reservation"), "{huge}");
}

#[test]
fn mapped_run_in_kernel_entries_is_rejected() {
    let message = rejected(&[run(
        USERSPACE_BASE - PAGE_BYTES,
        0x1_0000_0000,
        1,
        true,
        false,
    )]);
    assert!(message.contains("0x7ffffff000"), "{message}");
    assert!(message.contains("in the kernel's entries"), "{message}");
}

#[test]
fn mapped_run_above_user_half_is_rejected() {
    let message = rejected(&[run(1 << 47, 0x1_0000_0000, 1, true, false)]);
    assert!(message.contains("0x800000000000"), "{message}");
    assert!(message.contains("not in the user half"), "{message}");
}

#[test]
fn mapped_run_physical_overlap_is_rejected() {
    let runs = [
        run(USERSPACE_BASE, 0x1_0000_0000, 2, true, false),
        run(USERSPACE_BASE + 0x3000, 0x1_0000_1000, 1, true, false),
    ];
    let message = rejected(&runs);
    assert!(message.contains("0x100001000"), "{message}");
    assert!(
        message.contains("overlaps another run's physical pages"),
        "{message}"
    );
}

#[test]
fn mapped_run_virtual_overlap_is_rejected() {
    let later = USERSPACE_BASE + PAGE_BYTES;
    let runs = [
        run(USERSPACE_BASE, 0x1_0000_0000, 2, true, false),
        run(later, 0x1_0000_3000, 1, false, true),
    ];
    let message = rejected(&runs);
    assert!(message.contains(&format!("{later:#x}")), "{message}");
    assert!(
        message.contains("overlaps another run's virtual pages"),
        "{message}"
    );
}

#[test]
fn mapped_run_shared_page_is_one_run() {
    let segments = [
        SegmentSpan {
            virt: USERSPACE_BASE,
            pages: 1,
            writable: false,
            executable: true,
        },
        SegmentSpan {
            virt: USERSPACE_BASE,
            pages: 1,
            writable: true,
            executable: false,
        },
    ];
    let mut out = [run(0, 0, 0, false, false); 4];
    let count = disjoint_page_runs(
        &segments,
        |virt| 0x1_0000_0000 + (virt - USERSPACE_BASE),
        &mut out,
    )
    .expect("one page fits");
    assert_eq!(count, 1);
    assert_eq!(out[0].pages, 1);
    assert!(out[0].writable && out[0].executable);
    println!("mapped runs: shared page is one run with both rights");
}

#[test]
fn mapped_run_real_dom0_load_shape_is_accepted() {
    let (runs, phys_base) = real_dom0_runs();
    let count = check(&runs, phys_base, DOM0_RESERVATION).expect("a real dom0 load is a valid map");
    assert_eq!(count, runs.len());
    assert!(
        runs.iter().any(|run| run.executable),
        "dom0 has an executable run"
    );
    let stack_virt = USERSPACE_BASE + DOM0_RESERVATION - DOM0_STACK;
    assert!(runs.iter().any(|run| {
        run.virt == stack_virt
            && run.pages == DOM0_STACK / PAGE_BYTES
            && run.writable
            && !run.executable
    }));
    assert!(runs
        .iter()
        .any(|run| run.virt == USERSPACE_PAYLOAD_BASE && run.writable && !run.executable));
    println!(
        "mapped runs: accepted {count} runs, an executable segment, stack {stack_virt:#x}, payload {USERSPACE_PAYLOAD_BASE:#x}"
    );
}
