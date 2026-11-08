---
title: "One lock covers the kernel, the kernel is not preemptible, and every operation is a bounded step"
date: 2026-11-06
status: active
tags: [multicore, lock, kernel-state, verified]
one_line: "All of the Kernel value is under one lock with IF clear from entry to exit; every operation does a bounded amount of work and long work returns again with progress in an object, so the invariant holds at every step boundary and other cores interleave only there; per-CPU state outside the lock is only stacks, GDT, TSS and the switch decision, and only core c writes its own current thread."
revisit_if: "The bounded-step budget measured on this kernel gives a lock hold time a workload cannot tolerate, which is the case for a smaller node rather than for preemption."
confidence: "The non-preemptible rule is in the tree since the interrupt change that made it true; the per-CPU split is stated in kernel/verified/capability/kernel.rs; the budget's value is unmeasured."
---

# One lock, no preemption, bounded steps

## Decision

The kernel is not preemptible: IF stays clear from kernel entry to exit. NMIs bypass IF, so the kernel generates none, and one that arrives stops the machine with a report. Every operation does a bounded amount of work: a small constant number of list steps, one page table walk, or 64 KiB of zeroing. Long work returns `again` with progress in an object, so the invariant holds at every step boundary, and other cores interleave only there.

Shared and under the lock: all of the `Kernel` value, including the per-CPU list and every thread's state. Per CPU and outside the lock: stacks, GDT and TSS and the switch decision, in `kernel/src`'s `Cpu`. A core's user-mode execution depends on its current thread and the tables it has loaded, which is what the retype rule in `design/teardown-driven-by-retype/` protects.

The invariant splits at one rule: only core c writes its own current thread and the frame of the thread it runs. A blocked thread's frame is written under the lock by whoever delivers to it. The invariant states that a core's current thread is t exactly when t is Running on that core. Stopping a thread on another core sets a pending stop on it and sends an IPI, then returns `again`; that core, on kernel entry, moves it off. Destroying a thread Running on a core sets the same pending stop, marked so that the core makes it Dead rather than Inactive; when that core is the destroyer's own, no IPI is sent and the core acts on the stop itself. Destroying any other thread makes it Dead at once. Thread states: Inactive, Runnable on a core, Running on a core, Blocked on an endpoint, reply or notification, Dead.

## Reasoning

A non-preemptible kernel with bounded steps is what makes the proofs sequential: the invariant is about one `Kernel` value between steps, and concurrency is only the interleaving of whole steps, `design/multicore-kernel-shape/`. Hold time is then the longest step, which the budget sets.

The old kernel's cross-core kill nulled another CPU's current thread and freed the page while that CPU still ran the thread, the deletion problem von Tessin's thesis describes; the pending-stop state designs it out from the first leaf rather than retrofitting it.

## Alternatives rejected

- **A preemptible kernel.** The invariant would have to hold at every instruction a preemption could land on.
- **Waiting under the lock** for another core to act. See `design/flush-without-waiting/`.

## What this does not settle

- The budget's value, to be set from lock measurements on this kernel.
