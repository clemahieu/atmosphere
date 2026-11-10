---
title: "An untyped or frame capability names an aligned power-of-two block, retyped in constant time"
date: 2026-11-10
status: active
tags: [capability, memory]
one_line: "A memory capability names a block: a base aligned to its size and 2^order pages. Frames retype at 4K or 2M in constant time, a 2M frame derives 4K pieces, and a map names a capability, a page offset and an address, so a pager needs few slots."
revisit_if: "A workload needs frames that are not power-of-two aligned, or the 1G frame that pagetable does not yet map becomes necessary rather than convenient."
confidence: "Arithmetic on the page table's block sizes; the payload well-formedness is proven in kernel/verified/capability/table.rs."
---

# A capability names a block

## Decision

An untyped or frame capability names a block: base aligned to its size, 2^order pages, inside the address space. Frames retype at 4K or 2M in constant time, with 1G when the page table module gains a 1G map. A capability to a 2M frame can derive 4K pieces, so a pager needs few slots. A map names a capability, a page offset and an address. Every retyped object is a block too, with a fixed order per kind, `design/untyped-memory/`.

A device is boot-sized and is no block of memory, so its capability names its device as an object above the 48-bit address space: device d is the page at 2^48 + d pages. Every memory capability's block ends at or below 2^48, so none covers a device, and a device is reached only through its own capability. The console is no block either: its capability names the page at 2^49, past the 2^36 pages left for devices, so no memory capability and no device's covers it. Power, the authority to end the machine's run, is no block either: its capability names the page after the console's.

## Reasoning

Alignment to size is what makes retype a constant-time check: the page metadata holds, at 4K, a type, block order, stale epoch and zeroing cursor with a reference count at the block's base, and at 2M and 1G a count of typed units, so freedom of a block is one read, `design/teardown-driven-by-retype/`. A frame that could straddle blocks would need a walk.

Deriving pieces rather than retyping each page keeps the pager's slot count proportional to what it has handed out, not to memory size, and keeps every piece revocable through the parent, `design/sharing-by-derive/`.

## Alternatives rejected

- **Arbitrary ranges.** Freedom and overlap checks stop being constant time.
- **Naming a device inside the address space.** An untyped large enough to cover its name would reach it.
- **Retype per 4K page only.** A slot per page; a pager handing out a 2M region would hold 512 capabilities for it.
