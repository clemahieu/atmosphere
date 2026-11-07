---
title: "Boot hands the root process every capability there is, at fixed slots, and nothing else is reachable"
date: 2026-11-06
status: active
tags: [boot, capability]
one_line: "Boot writes page metadata and creates the root process, thread and table. The root holds at fixed slots untyped capabilities covering free memory as aligned blocks, its own process and thread, a capability per core at top priority, interrupts, devices, ports, a console, SVM and timers; the list's root is a synthetic node boot sets aside, and the root's boot objects are never retyped."
revisit_if: "Several kernel instances each need a root, in which case what boot hands each root is the open question recorded with that work; or a second boot-created process is wanted."
confidence: "Follows from the kernel allocating nothing after boot: something must hold everything at the start, and only one thing does."
---

# The root process at boot

## Decision

Boot writes page metadata and creates the root process, thread and table. The root holds at fixed slots: untyped covering free memory as aligned blocks, its own process and thread, a capability per core at top priority, interrupts, device and port capabilities, a console, an SVM capability, and timers. Nothing is reachable without one. The root treats these as all there is, `design/one-kernel-instance/`.

The list's root is a synthetic node at depth 0 in a page boot sets aside, and the root's capabilities are its children at depth 1. The root's process, thread and table come from boot, not from an untyped, so they have no hidden node and are never retyped.

## Reasoning

Under `design/untyped-memory/` the kernel has no authority of its own to hand out later, so everything must be in some process's hands from the first instruction of user mode, and in one lineage so that revocation reaches it, `design/revoke-by-depth-first-list/`. Fixed slots are what the root's own code and its tests can rely on without an enumerate operation the ABI does not have.

## What this does not settle

- Whether the retype into a vCPU being gated by an SVM capability is the only hardware surface so gated; others follow the same pattern as they are exposed.
