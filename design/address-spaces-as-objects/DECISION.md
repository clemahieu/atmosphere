---
title: "An address space is a retyped object of a kind, whose table pages whoever maps pays for"
date: 2026-11-06
status: active
tags: [capability, memory, address-space]
one_line: "A space is a retyped object of kind process, IO or nested; its table pages come from an untyped named in the map call; a frame entry's mapping node sits at a fixed index in the table page's block so it is found in constant time; a child table's hidden node is its entry's node; PCIDs and ASIDs recycle per core by generation, an IOid is fixed per device."
revisit_if: "A space kind appears whose entries cannot carry a node at a fixed index, or a device must change IOid while bound."
confidence: "Structural; the table-page layout and the entry-record agreement are proven in kernel/verified/capability/space.rs, link.rs and mapping.rs."
---

# Address spaces are retyped objects

## Decision

A space is a retyped object of a kind: process, IO, and nested for a guest, `design/vmm-over-svm/`. Table pages come from an untyped named in the call, so a table costs one order-3 block, paid by whoever maps. A table page's block holds its node pages, whose node 0 is the block's hidden node, then the table, then its parent record. An entry that maps a frame has a list node at a fixed index in the block, so its mapping is found from the entry in constant time. An entry that points to a child table has no node of its own: the child's hidden node is that entry's node, holds the one reference to the child, and carries its parent record. A table entry names a child table exactly when that child's record names the entry, and a link writes both in one step so a detach can always clear both, `design/teardown-driven-by-retype/`.

Mapping nodes are keyed by space kind, so nested tables fit, and revocation's reverse map is over a kind, not two concrete tables. The existing page table module and its map and unmap proofs are kept and adapted. Kernel slots exist only in process spaces; a device space has no kernel slots, so a device's address may use the low entries a process's root keeps for the kernel.

PCIDs and SVM ASIDs are per core, recycled by generation with a flush on wrap, which needs no authority and no free list, and removes one shared resource a process could exhaust; generations cost one word per core per space, in the space's object. An IOid is fixed, the device's number on its IOMMU, since a bound device has no load event to pick up a new id after a wrap; the IOTLB invalidate a wrap would have needed comes between an unbind and a rebind.

## Reasoning

Making the mapper pay for tables is what `design/untyped-memory/` demands: the kernel has nothing to pay with. Putting the mapping node at a fixed index in the table's own block, rather than in a separate structure, is what makes unmap and revoke constant time per entry, `design/revoke-by-depth-first-list/`.

A child table represented twice, by a mapping node and its hidden node, left its count at 1 after retype unlinked the hidden node and no retype case applied; one node per entry is the fix.

## Alternatives rejected

- **A global PCID or ASID allocator.** A shared resource a process could exhaust, and a free list the kernel would own.
- **Per-core IOids.** A device is bound to one IOMMU and does not reload, so per core is the wrong axis.
