---
title: "Boot hands the root process every capability there is, at fixed slots, and nothing else is reachable"
date: 2026-11-09
status: active
tags: [boot, capability]
one_line: "Boot writes page metadata and creates the root process, thread and table. The root holds at fixed slots untyped capabilities covering free memory as aligned blocks, frame capabilities for dom0's image and stack with the rights they were loaded with, its own process and thread, a capability per core at top priority, interrupts, devices, ports, a console, SVM and timers; the list's root is a synthetic node boot sets aside, and the root's boot objects are never retyped."
revisit_if: "Several kernel instances each need a root, in which case what boot hands each root is the open question recorded with that work; or a second boot-created process is wanted."
confidence: "Follows from the kernel allocating nothing after boot: something must hold everything at the start, and only one thing does."
---

# The root process at boot

## Decision

Boot writes page metadata and creates the root process, thread and table. The root holds at fixed slots: untyped covering free memory as aligned blocks, frames covering dom0's image and stack, its own process and thread, a capability per core at top priority, interrupts, device and port capabilities, a console, an SVM capability, and timers. Nothing is reachable without one. The root treats these as all there is, `design/one-kernel-instance/`.

The list's root is a synthetic node at depth 0 in a page boot sets aside, and the root's capabilities are its children at depth 1. The root's process, thread and table come from boot, not from an untyped: boot types their blocks from pages it sets aside, and no untyped covers those pages, so a retype never names them. A table leaf boot makes keeps its hidden node, at node 0 of its first page as every live leaf's is, also a child of the synthetic root; with no untyped above it, no revoke reaches it.

The frames dom0's image and stack are loaded in are frame capabilities at consecutive slots of the root's second boot leaf, from `ROOT_FRAME_SLOT`: each run of pages the loader mapped for dom0 decomposes into maximal aligned blocks of at most 512 pages, in address order and run by run, one capability per block, with the run's rights (read, and write and execute as the loader mapped the run) and without control. Boot refuses when the blocks do not fit in the leaf. dom0's pages are reserved, so no untyped covers them either: boot types each 2M region holding them as a large frame, its pages free under the region as every large block's are, and each capability names an aligned block of at most 512 pages inside its region, a narrowed piece of the region as a derived frame is, `design/capability-names-a-block/`. A small frame is one page, so frames of 4K alone would take one slot per page, more than a leaf holds.

## Reasoning

Under `design/untyped-memory/` the kernel has no authority of its own to hand out later, so everything must be in some process's hands from the first instruction of user mode, and in one lineage so that revocation reaches it, `design/revoke-by-depth-first-list/`. Fixed slots are what the root's own code and its tests can rely on without an enumerate operation the ABI does not have.

The leaf's hidden node stays because a leaf whose hidden node is gone is dead, refused by lookup, `design/teardown-driven-by-retype/`, and every live leaf having one is what lets revoking an untyped reach the leaves typed from it; a boot leaf without one would be the only leaf that rule does not cover, and every proof over leaves would carry the exception. Under the synthetic root it costs one node and changes nothing a retype or revoke can reach.

## What this does not settle

- Whether the retype into a vCPU being gated by an SVM capability is the only hardware surface so gated; others follow the same pattern as they are exposed.
