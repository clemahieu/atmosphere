---
title: "The page buddy keeps each span's records in the span, so it holds as many spans as the source gives"
date: 2026-11-11
status: active
tags: [memory, heap, verified]
one_line: "aheap's page buddy reserves spans of two blocks, gives each block a block buddy of its own, and keeps both buddies' records and the link to the next held span in the span's metadata page, the first page of its second block, allocated there as a run of order 0; held spans form one list, so the only refusal is the source's and every page of a held span is a free block, a run or that page."
revisit_if: "A reservation from the source becomes costly enough that the second block of each span is a measured waste, a caller needs runs larger than one block, or the node outgrows one page."
confidence: "Proven in the tree, aheap/src/page.rs: lemma_view states the partition of both blocks and where each metadata page lies, alloc_run refuses only when the source did, and aheap/src/witness.rs holds PAGE_BYTES / BLOCK_PAGES + 1 whole blocks at once. The two-block span is a judgement about the cost of address space against the cost of a metadata page that lives apart from what it describes."
---

# The page buddy keeps each span's records in the span

## Decision

A run span, the unit the page buddy reserves from its span source, is two blocks. Each block is cut by a block buddy of its own. The span's metadata page is page 0 of the second block, allocated in that block's buddy as a run of order 0, backed when the span is reserved and given back with it. It holds the span's node: the base of the next held span and the two block buddies' records, 1032 bytes (`aheap/src/arch/`, `lemma_node_layout`). The nodes link every held span into one list from the page buddy's head.

The first block holds no record, so a run span can give a whole block, a run of order BLOCK_ORDER. The second block gives every page but its first.

## Context

The page buddy's contract is that it refuses a run only when no held span has room and the source refused to reserve a span or to back its metadata page, and that every page of a held span is a free block, an allocated run or a metadata page. The records of a block buddy are BLOCK_PAGES bytes, and they must live somewhere the page buddy owns.

## Alternatives rejected

- One metadata page in a span of its own, holding a table of records: it holds PAGE_BYTES / BLOCK_PAGES records, 8 with 4 KiB pages and 512-page blocks, so the page buddy would refuse at 16 MiB whatever the source would give, and the other pages of the metadata span would be reserved yet in no free block, run or metadata page.
- Further table pages, each in a span of its own, when the table is full: every such span keeps the same unpartitioned pages, and the bound moves rather than goes.
- The metadata page inside a one-block span: the block loses its page 0, so no run of a whole block could be cut, while `alloc_run` offers every order up to BLOCK_ORDER.
- Two-block spans with one block buddy over the first block and the second block kept only for the metadata page: the second block's other pages are reserved and in no free block, run or metadata page, which breaks the partition the contract states.

## Reasoning

Keeping the node in the span it describes makes the count of held spans unbounded by anything but the source, and the node's lifetime the span's: it is backed with the span and released with it, so freeing the last run of a span gives back everything it took. Making the metadata page a run of the second block's own buddy puts it in the partition, so `lemma_view` can state of every page of a held span which of the three it is. The cost is address space: a span reserves two blocks where a whole-block run needs one, and the second block serves smaller runs.

## What this does not settle

How many idle spans the page buddy keeps as spares is its caller's choice at construction. Whether a span's second block should be given back separately when only it is idle is not decided; today a span is given back whole.
