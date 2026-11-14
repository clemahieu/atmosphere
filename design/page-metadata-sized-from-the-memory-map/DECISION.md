---
title: "Page metadata is one boot-carved region, indexed by physical address and bounded by the identity-mapped span"
date: 2026-11-14
status: active
tags: [memory, boot, verified]
one_line: "The block table owns one length, the tracked page count: boot takes the highest RAM the map names, rounds it up to 1 GiB, refuses it past the identity-mapped span, and carves one region holding a page entry, region entries, counts, a stale epoch and a zeroing cursor for every page from address 0, holes included."
revisit_if: "A machine's address holes cost more metadata than its RAM, so a dense table of only the RAM pages pays for an address-to-index translation; or the identity-mapped span has to exceed 2^48, which the page-table address mask and the device names both stop; or a boot must track RAM the loader has not identity-mapped."
confidence: "The tiling and the overflow bound are arithmetic on the span and the 4K granule. That a closed per-element points-to map verifies at the cost of the fixed arrays is a judgement; the storage change measures it."
---

# Page metadata is carved at boot

## Decision

The block table holds two integers and nothing else that says how much memory it tracks: the physical address of one carved region, and `pages`, the number of tracked pages. Every other count is that number. A 2M region count is `pages / PAGES_PER_2M` and a 1G region count is `pages / PAGES_PER_1G`. Stale epochs and zeroing cursors store neither a count nor a pointer. `kernel/verified` has no static for any of it, `design/one-kernel-instance/`.

`pages` is a multiple of `PAGES_PER_1G`, so `pages == count_1g * PAGES_PER_1G` and `pages == count_2m * PAGES_PER_2M`. The tracked bytes `pages * PAGE_SZ` are at most the identity-mapped span, `KERNEL_MEM_END_L4INDEX * SIZE_512G`, which is the same boundary as `USERSPACE_BASE`. That span is at most 2^48 bytes, because the kernel uses at most `ENTRIES` top-level entries and `ENTRIES * SIZE_512G == 1 << 48`. A proof that used to take those products from the literals `NUM_PAGES`, `NUM_2M` and `NUM_1G` takes them from two lemmas on `pages`: one that a tracked index times `PAGE_SZ` does not overflow, from the span, and one that the two region products equal `pages`, from the multiple. No proof bounds `pages` by anything smaller than the span. The granule stays 4K, `design/arch-module/`.

The tables cover every page from physical address 0 up to `pages`, holes included. Page `i` is the page at address `i * PAGE_SZ`. A hole, a firmware reservation or a device window inside that range is tracked and stays reserved: no range calls it available, so it is never handed out. The index of a page stays its address over 4K.

Boot computes the range from the memory map, which is at most 256 ranges. The RAM end is the maximum `base + bytes` over ranges of kind Available, Kernel, Domain or PageTable. Reserved does not move it: the loader folds firmware bookkeeping, ACPI, NVS, BIOS and PCI into Reserved, and a device window above the last RAM must not become tracked pages. Boot rounds that end up to a multiple of 1 GiB. It panics, naming the address, with reason `no RAM` when there is no such range and with reason `past the identity-mapped span` when a RAM range's end overflows or a RAM range or the rounded end lies past the span. The rounded tail, the partial last gigabyte that is not RAM, is tracked and stays reserved, so it is never the free 1G block a boot check looks for.

The carve is whole pages, taken from the first Available range inside the tracked end that holds it clear of the kernel image and of dom0's reservation. Its base is that physical address. The loader's identity map leaves it equal to the virtual address, and the columns are read through that map. Finding that range is a scan of the map, before any per-page bitmap exists. The region then holds these columns, in this order, each aligned to its element and none of them interleaved:

1. page entries, one per tracked page
2. 2M region entries, then 1G region entries
3. 2M counts, then 1G counts
4. stale epochs, one per tracked page, then one per 2M region, then one per 1G region
5. zeroing cursors, one per tracked page
6. active flags, one per 2M region, then one per 1G region
7. boot scratch, one byte per tracked page

Offsets and the byte count are one function of `pages`, `size_of` and `align_of`, called from boot and specified beside the block table. There is no second copy of the layout. Boot zeroes the carve, folds the map with the scratch bytes, then logs `page metadata: N pages, M bytes`, where M is the column bytes and not the scratch. The scratch is that byte column, not a static array, and the verified permission does not cover it. The rest of boot's scratch, the run and block lists, stays fixed-bound. The carve is set aside as the kernel stretch is, `design/root-process-at-boot/`, so its pages stay reserved and the root's untyped does not cover them.

The permission is a points-to per element, held in a map on the struct that already owns that column: the block table for page entries, region entries and counts, the stale-epoch struct for its three columns, the zeroing struct for the cursor and the two active flags. The map is closed, as `Array`'s match of sequence to elements is closed, and the open view stays the sequence those proofs already read. `get` and `set` are the only items that open the map. The addresses in the map are the layout function's. Unverified boot passes the carve's raw permission in with `Tracked::assume_new()`, as it passes the free-page permissions, and `kernel_init`'s specification says that permission covers the columns. The verified init splits it into the element permissions and writes each initial value. It does not add an `external_body`. Zeroed memory is not what the proof trusts; the write loop is. A free page's content permission stays the free-page map, and it is never a permission of the carve.

The block table's well-formedness says `pages` is a non-zero multiple of `PAGES_PER_1G`, `pages * PAGE_SZ` is at most the span, and each column's sequence and permission domain have the length the layout gives them. Every operation ensures `pages` is unchanged. The helpers that already name a tracked page, `spec_page_count` and `tracks` and the rest on `BlockTable`, keep their call sites; their bodies read `pages`. `NUM_PAGES`, `NUM_2M` and `NUM_1G` do not size kernel state.

## Context

The page entries, region entries, counts, stale epochs and zeroing cursors are arrays inside the `Kernel` value, sized by `NUM_PAGES` of 1,048,576 and by the 2,048 and 4 that tile it. The image therefore carries metadata for exactly 4 GiB. RAM above that is unusable and a smaller machine pays for entries it does not have. A page entry, a stale word and a cursor are about 48 bytes, measured as 32 plus 8 plus 8, `design/test-guest-memory/`, so the tables are about 1.2 percent of the memory they track: about 6 MiB at 512 MiB, about 48 MiB at 4 GiB, about 6 GiB at 512 GiB. The region columns are one entry, one count, one epoch and one flag per 2M and per 1G, and they do not change the proportion. One byte per page of boot scratch is a further static of the same length.

The literal is also what makes the arithmetic proofs close. `NUM_PAGES * PAGE_SZ` is 4 GiB, so an index times 4096 cannot overflow, and `NUM_2M * PAGES_PER_2M` and `NUM_1G * PAGES_PER_1G` equal `NUM_PAGES` by computation. A length that is only known at boot has to say the same facts without a literal the solver can fold.

## Reasoning

Indexing by address is the arithmetic the block table, the capabilities and the page tables already share: a base, a region and a table entry are all an address divided by the page size. A table packed to the RAM pages would need a translation in front of every one of those, and a block that is contiguous in address would no longer be a contiguous run of entries. The holes this buys are the firmware's gaps and the rounded tail, each well under a gigabyte on the two test guests. At about 48 bytes a page, a gibibyte of hole is 12 MiB of entries. On virt the addresses below 1 GiB hold no RAM, `design/test-guest-memory/`, and they stay in the table for the same reason.

Rounding up to 1 GiB, rather than to a page or to 2 MiB, is what keeps the two products equal to `pages`. A partial last region would turn each of them into a ceiling and put a clamp on every large-block range. The tail is reserved, so the free 1G block the boot check names is still a region the map calls available all the way across: 1 to 2 GiB on the PC, where RAM ends at 2.5 GiB and the tracked end is 3 GiB, and 2 to 3 GiB on virt, where RAM ends at 3.5 GiB and the tracked end is 4 GiB. Both ends sit inside the 4 GiB the loader identity-maps.

The span, rather than a tighter constant, is the bound because raising it is adding top-level entries, up to `ENTRIES`, and the block-table proofs quantify over `pages` under the span lemma. They do not mention 4 GiB or 512 GiB. A memory capability's block ends at or below 2^48, `design/capability-names-a-block/`, and a tracked page is below the span, so the same lemma is what keeps a tracked page from being a device name.

One stored length is what keeps a second integer from having to be proved equal to the first on every operation. The sequence length and the permission domain equalling `pages` is the well-formedness `Array` already has, with the constant replaced by the field. The closed map is what stops a million points-to values from entering a query that only reads an entry: the open facts stay a sequence update, which is what `Array::set` already ensures.

The carve is placed by a scan of the map because the per-page bitmap is part of what is being placed. The map has at most 256 ranges, so the scan is bounded without it.

## Alternatives rejected

- **A compile-time `NUM_PAGES`.** The image carries one machine's metadata. Bare metal has more RAM than the test guest's 4 GiB, and a smaller guest still pays the 4 GiB tables.
- **A dense table of only the RAM pages.** It drops the holes and loses `index = address / PAGE_SZ`. The holes on the machines this boots are the cheap part.
- **Size to the highest range of any kind, Reserved included.** The loader's Reserved includes device windows. The APIC just below 4 GiB, or a PCI window above RAM, would pull the tracked end up to itself.
- **Round only to a page or to 2 MiB.** The 1G product stops being `pages`, and every large-block proof gains a partial last region.
- **Three stored counts, kept equal by well-formedness.** Any operation that touches one has to say the others are unchanged. Two of the three are divisions of the first.
- **A fat pointer whose length is the count.** The length would sit in the metadata of an unsized pointee, and this vstd's `PointsTo` and `into_typed` are for a sized type. A `usize` on the block table is the count; the column pointers are computed.
- **One `PointsTo` of the whole region as the view proofs read.** A raw permission does not remember values, and an unsized slice is not a sized `PointsTo`. Per-element permissions, closed behind the sequence, remember one entry and leave the quantifiers on the sequence.
- **A static, or a global in `kernel/verified`.** The tables would be outside the `Kernel` value, `design/one-kernel-instance/`.
- **Track from a non-zero physical base the target names.** Rejected in `design/test-guest-memory/`: the page arithmetic assumes the index is the address over 4K.
- **Leave RAM past the span unused.** A machine with RAM the kernel will not track would boot a silent subset of its map. Boot refuses instead.

## What this does not settle

The loader identity-maps the first 4 GiB, `design/test-guest-memory/`, and the span constant is one top-level entry, 512 GiB. Both test guests' tracked ends fall inside the mapped 4 GiB. A tracked end above those 4 GiB needs the loader's identity map extended before the kernel can zero a page there; the span check does not walk the loader's tables, and this record does not change either. The byte size of a page entry stays `size_of`, not a number frozen here. The 1G frame the page-table module does not yet map, and the device, console and power names above 2^48, stay `design/capability-names-a-block/`.
