---
title: "The test guest has 512 MiB, and the loader's pools and the kernel's tracked pages are sized to that guest"
date: 2026-11-09
status: active
tags: [boot, memory, test]
one_line: "The gate, the boot-stack check, the pinned measurement and the syscall benchmark boot a 512 MiB guest. The loader's pools, the kernel and loader stacks, dom0's window and the per-CPU stacks are sized to that guest, not to a board. The loader hands over its memory map as typed ranges, and the kernel tracks the first 1 GiB of it."
revisit_if: "A functional or performance test needs more RAM than 512 MiB, or a machine the kernel must run on has RAM above 1 GiB, which the kernel does not track."
confidence: "Judgement from the reservation arithmetic below. The gate boot is what checks that a 512 MiB guest actually reaches dom0."
---

## Decision

`tools/run.py`, `tools/check-boot-stack.py`, `tools/measure-pinned.py` and `bench/run-bench.sh` boot a 512 MiB guest. The loader identity-maps the first 4 GiB, which is this guest's RAM and the 32-bit MMIO window just below 4 GiB, with 2M leaves; the kernel's image and its stack guard have 4K entries. Its page-table pool is 512 KiB, its bump allocator is 128 MiB, the kernel window inside that is 64 MiB and dom0's window is 16 MiB with a 1 MiB stack. The loader hands the kernel its memory map as ranges of base, bytes and type, at most 256 of them, and the kernel tracks the pages of the first 1 GiB: `NUM_PAGES` is 262,144, tiled by 512 2M regions and one 1G region. Memory a range names past that is left unused. The loader's stack and the kernel's boot stack are 1 MiB each. The kernel keeps four CPU slots, each with 64 KiB interrupt and syscall stacks. The benchmark starts four CPUs; the gate starts two.

## Context

The guest had been 32 GiB, then 6 GiB. Both were chosen from outside the kernel: 32 GiB was more than `NUM_PAGES` can track, and 6 GiB was what still fitted an Orange Pi after leaving the board's OS about a gigabyte. The loader meanwhile required one conventional region larger than a 2 GiB allocator, whether or not the guest used that allocator.

## Reasoning

The sizes are the bytes each pool has to hold, with slack where a check demands it.

- The memory map crosses to the kernel as typed ranges, which is the shape firmware gives it in, on x86_64 and on aarch64. OVMF lists 30 regions for the test guest once the loader has labelled its own; with their edges moved to pages and neighbours of one type merged they are 21 ranges of 24 bytes, in a list that holds 256. The list's length does not depend on how much memory there is, so the loader does not know how many pages the kernel tracks: the kernel checks the ranges at the trust boundary, takes the free pages below its own limit, and leaves the rest unused.
- The stacks are sized from what is written on them, measured by zeroing each, booting to dom0's exit and dumping it with `pmemsave`. The kernel's boot writes 48 KiB of its stack in a debug build and 16 KiB in release; the stack is 1 MiB, and `tools/check-boot-stack.py` requires 512 KiB of it unused. The overflow build's stack is 8 KiB, under that depth in either profile and over what `main` uses before the IDT exists. The loader's `load` writes 108 KiB of its stack in a debug build and 48 KiB in release, with the handoff and its own copies of the memory map on it; that stack is 1 MiB.
- Sixteen CPU slots with eight 1 MiB stacks each were 128 MiB of kernel image. Four slots with 64 KiB stacks are 2 MiB. Boot's copy of the handoff is on the boot stack, not on these.
- The test guest's RAM is below 512 MiB. The local APIC, the I/O APIC and the IOMMU sit just below 4 GiB, and the loader only allocates below 4 GiB, so the identity map ends at 4 GiB. With 2M leaves that map is six tables: a PML4, a PDPT and four page directories. With 4K entries it is a page table for every 2 MiB besides, 2,054 tables and about 8 MiB. `tools/run.py`'s CPU model, Haswell-IBRS, has no 1G pages.
- A 2M stretch has a page table only where something inside it needs a protection of its own. The kernel write-protects one page of its image at a time (`kernel/src/arch/x86_64/write_protect.rs`), and its 1 MiB stack guard is less than a stretch, so the loader gives the stretches from the start of the kernel's image to the end of the guard 4K entries. The rest of the kernel window, the stack included, and all other memory stay on 2M leaves.
- The page-table pool is 128 pages, 512 KiB. The loader logs how many hold tables as it enters the kernel, the line `Page-table pool:` in `serial.log` after `tools/run.py`: 19, in the debug build and in release (`tools/check-boot-stack.py release`, `target/boot-stack-check-release/serial.log`). Those are 6 for the identity map, 3 page tables for the kernel's image and guard, 4 for the address space the loader builds for the IOMMU, and 6 for dom0: a PDPT, a page directory and two page tables for its image and stack, and a page directory and a page table for the payload. The most the loader can write is 55: 6, then 32 if every stretch of the 64 MiB kernel window had a page table, 4, and 13 for a 16 MiB dom0 window, which is a PDPT, two page directories and ten page tables. That fits the lower 64 pages, so the upper half, which the boot-stack check requires to stay unwritten, stays clear.
- The kernel window holds the image, under 3 MiB with the CPU slots and about 2 MiB of boot scratch, and the 1 MiB stack plus a 1 MiB guard. 64 MiB covers that. dom0's release image is under 1 MiB, so its window is 16 MiB with a 1 MiB stack. The bump allocator is 128 MiB, which is those two windows with room left over, and the guest's one conventional region is larger than that without the 2 GiB floor.

- The capability kernel keeps about 48 bytes per tracked page (a 32-byte page entry, an 8-byte stale epoch, an 8-byte zeroing cursor), and boot zeroes that stretch. Tracking 8 GiB was about 96 MiB, nearly all of it entries for pages the guest does not have. Tracking 1 GiB is about 12 MiB, and a 512 MiB guest's RAM and the gaps below it sit inside that. A smaller cap would leave no whole 1G region, and a 1G block is one of the sizes the block table types.

A 512 MiB guest has that region below 4 GiB.

## Alternatives rejected

- **Keep 6 GiB so the guest matches the Orange Pi.** The board is not the test. A guest that leaves the board's OS a gigabyte was a host constraint, and it hid the loader pools.
- **Stay at 32 GiB.** Pages at or past 8 GiB are not tracked. The guest was RAM the kernel cannot use.
- **Track 512 MiB, the guest's RAM.** That leaves `NUM_1G` at zero, so no 1G region and no 1G block.
- **Hand the kernel one entry per page.** At 16 bytes an entry that is 4 MiB for each GiB the list covers, copied by value onto the loader's stack and the kernel's, and a slot count the loader and the kernel must share at compile time.

## What this does not settle

RAM at or above 1 GiB is not tracked; a machine with more RAM needs a larger `NUM_PAGES`, and nothing in the loader changes with it. A guest with RAM above 4 GiB needs an identity map past the 32-bit MMIO window; this machine has no such RAM. The 64 MiB kernel window is larger than the image and the stack it holds, and a later measurement can tighten it. The kernel's image is on 4K entries for the write-protect check alone; a check that split the leaf it tests would let the image share 2M leaves with the rest.
