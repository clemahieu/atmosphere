---
title: "One lock covers the kernel, the kernel is not preemptible, and every operation is a bounded step"
date: 2026-11-06
status: active
tags: [multicore, lock, kernel-state, verified]
one_line: "All of the Kernel value is under one lock with IF clear from entry to exit; every operation does a bounded amount of work and long work returns again with progress in an object, so the invariant holds at every step boundary and other cores interleave only there; per-CPU state outside the lock is only stacks, GDT and TSS, and only core c writes its own current thread."
revisit_if: "The bounded-step budget measured on this kernel gives a lock hold time a workload cannot tolerate, which is the case for a smaller node rather than for preemption."
confidence: "The non-preemptible rule is in the tree since the interrupt change that made it true; the per-CPU split is stated in kernel/verified/capability/kernel.rs; the step counter bounds the capability list's walks, the flush's IPI loop, the acknowledgement check, the stale-epoch record, a table page's cut, a mapping's and a device binding's stale note, the IOMMU invalidate, probe, print, a zeroing step, a small block's typing and freeing, revoke, destroy, the device table, each arm of a reclaim, each retype, and each operation dispatch runs, not yet a whole entry; the budget's value is unmeasured."
---

# One lock, no preemption, bounded steps

## Decision

The kernel is not preemptible: IF stays clear from kernel entry to exit. NMIs bypass IF, so the kernel generates none, and one that arrives stops the machine with a report. Every operation does a bounded amount of work: a small constant number of list steps, one page table walk, or 64 KiB of zeroing. Long work returns `again` with progress in an object, so the invariant holds at every step boundary, and other cores interleave only there.

The bound is proven with a ghost step counter, `Steps` in `kernel/verified/capability/steps.rs`. Its unit is one iteration of an exec loop under the lock, whose body, apart from what its callees count, runs a number of instructions the code alone bounds: a list node read or written, a table or page-table entry read or written, a 4K page zeroed, a dead waiter skipped, an IPI sent. Straight-line code between loops is bounded by the code's size and is not counted, and the verified code that calls a cited hardware leaf counts what the leaf does in the same units. A wait on a device, whose length the device sets and the kernel's state does not, is one unit: the IOMMU's completion wait after an invalidate, and the serial port's wait for room before each byte of a print. A function that loops takes the counter as `Tracked<&mut Steps>`, adds one per iteration, and ensures the count rose by at most its bound, a constant in its specification; a callee's units add to its caller's. The counter is passed rather than held in the `Kernel` value, so a refusal that reads entries still leaves the kernel equal to what it was. Each path that holds the lock makes one counter per entry, dispatch for an invocation, and boot and the witnesses, which hold no lock, make their own.

Each operation dispatch runs states its bound, a constant named for it in `kernel/verified/capability/operation.rs` or beside the operation:

- retype, `INVOKE_RETYPE_STEPS`: a table page's retype, the largest of the four kinds, 1168.
- revoke, `INVOKE_REVOKE_STEPS`: `REVOKE_BUDGET` steps, each its own unit, the walk to its leaf, a table page's stale note and the leaf's arm, 49216.
- unmap, `INVOKE_UNMAP_STEPS`: a 2M mapping's stale note and the flush's IPIs, 544.
- probe, `INVOKE_PROBE_STEPS`: an entry each, `PROBE_MAX`, 64.
- print, `PRINT_BYTES`: a byte each, 40.
- derive, move, delete, link, map, power-off (`POWER_OFF_STEPS`), inspect (`INSPECT_STEPS`) and the entry's check of its current thread (`CHECK_CURRENT_STEPS`): 0, since each runs no loop and calls nothing counted; a loop added to one raises a bound already in its specification. A core's acknowledgement of a flush, `ACKNOWLEDGE_STEPS`, is 0 the same way.
- an IOMMU's invalidate and acknowledgement, `FLUSH_IOMMU_STEPS`: the wait for the invalidate, 1.

Shared and under the lock: all of the `Kernel` value, including the per-CPU list and every thread's state. Per CPU and outside the lock: stacks, GDT and TSS, in `kernel/src`'s `Cpu`. A core's user-mode execution depends on its current thread and the tables it has loaded, which is what the retype rule in `design/teardown-driven-by-retype/` protects.

The invariant splits at one rule: only core c writes its own current thread and the frame of the thread it runs. A blocked thread's frame is written under the lock by whoever delivers to it. The invariant states that a core's current thread is t exactly when t is Running on that core. Stopping a thread on another core sets a pending stop on it and sends an IPI, then returns `again`; that core, on kernel entry, moves it off. Destroying a thread Running on a core sets the same pending stop, marked so that the core makes it Dead rather than Inactive; when that core is the destroyer's own, no IPI is sent and the core acts on the stop itself. Destroying any other thread makes it Dead at once. Thread states: Inactive, Runnable on a core, Running on a core, Blocked on an endpoint, reply or notification, Dead.

## Reasoning

A non-preemptible kernel with bounded steps is what makes the proofs sequential: the invariant is about one `Kernel` value between steps, and concurrency is only the interleaving of whole steps, `design/multicore-kernel-shape/`. Hold time is then the longest step, which the budget sets.

The old kernel's cross-core kill nulled another CPU's current thread and freed the page while that CPU still ran the thread, the deletion problem von Tessin's thesis describes; the pending-stop state designs it out from the first leaf rather than retrofitting it.

## Alternatives rejected

- **The counter as a field of the `Kernel` value.** Every refusal that reads before refusing would change the kernel, and each specification that says a refusal leaves it unchanged would have to say so of every field but one.
- **Bounding each loop by its own invariant, with no counter.** Each loop would be bounded, but the bound of an entry would be a sum taken by hand over the call graph, which nothing checks.

- **A preemptible kernel.** The invariant would have to hold at every instruction a preemption could land on.
- **Waiting under the lock** for another core to act. See `design/flush-without-waiting/`.

## What this does not settle

- The budget's value, to be set from lock measurements on this kernel.
