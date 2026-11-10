---
title: "One kernel instance holds every core, and a process lives inside it"
date: 2026-11-05
status: active
tags: [multicore, kernel-state, abi]
one_line: "One kernel instance holds every core of the machine and a process lives inside it; the kernel provides no spanning. Four rules keep a later move to several instances cheap, and breaking one is the human's decision."
revisit_if: "Lock contention measured on this kernel is one a real workload would hit, a workload needs distrusting programs separated from the shared lock's timing, or a change would break one of the four rules."
confidence: "A staging judgement on top of the multicore shape. That one instance pays almost nothing for the node concept is reasoned from the code, not measured: finding the instance is one per-CPU load and no syscall path gains a check."
---

# One kernel instance holds every core

## Decision

Today one kernel instance holds every core of the machine. A process lives inside one instance, and the kernel provides no way for a process to span instances. Several instances per machine, with the layout a boot setting, is the direction set by `design/multicore-kernel-shape/`, parked as deferred work that nothing depends on. Starting it is the human's decision.

Four rules keep that move cheap, and the code that each governs points here:

1. Kernel state stays inside the `Kernel` value, and `kernel/verified` has no statics.
2. A capability, and any name a process passes to the kernel, resolves within the caller's instance. The ABI has no machine-wide names.
3. The root process treats what boot gave it as all there is, and does not assume it owns the machine.
4. The pager library draws from the pool it was given, not from all memory.

A change that breaks a rule, or adds kernel spanning, is a decision only the human can make. File it as a question with what it costs the multi-instance path, the alternative that keeps the rule, and why the change is wanted.

## Context

`design/multicore-kernel-shape/` allows several nodes, each a set of cores with one kernel instance and one lock. That raised the question of what happens when one program wants more threads than its node has cores, or wants cores on two nodes. Three answers were worked through:

- A, stays on its node. A process lives on one node; extra threads timeslice there. A program wanting several nodes is written as one process per node over shared frames. The kernel stays sequential per node, and a program that does nothing special never reaches another node, which may surprise its user.
- B, spans in the kernel. One process has threads on several nodes; the kernel provides one address space across them and takes on cross-node page tables, shootdown and kill. The concurrency the design exists to avoid enters the kernel and its proofs.
- C, spans in the runtime. The kernel is as in A; a runtime library starts a thread on another node inside a sibling process sharing frames and coordinates address space, capabilities and threads in user space, as Barrelfish does.

A system with one node behaves the same under all three, which is what made deferral possible.

## Reasoning

The human put least surprise for threads across a whole chip first: on a general-purpose machine, a program that starts more threads than it has cores should see them spread across the chip without doing anything special. One instance per machine gives that with no spanning mechanism at all. It is A's kernel with the multi-node work parked, and neither a spanning library nor B is ruled out later.

It is safe to defer because a one-node system pays almost nothing for the node concept at run time, and because `kernel/verified` has no statics and its invariant is a property of one `Kernel` value, so the sequential proofs should carry to several instances. The new work for several instances, disjoint kernel memory, untyped handoff, cross-node signalling and the rule that a frame never becomes a kernel object while another node maps it, costs about the same later as now.

The rules are the only cost paid today, and each is a property the single-instance kernel wants anyway.

An admin who later wants nodes for contention or isolation gets them only after the deferred work is built. Until then a multi-socket machine is one instance.

## Alternatives rejected

**One node per cache domain by default.** An independent evaluation of this question proposed it. Rejected because it puts the surprise above on every machine with more than one cache domain, which on the development host means every program.

**Design spanning now.** The weak points of C (non-atomic kill of a spanned program, capabilities usable only on their node, replicated address-space state with no owner, thread identity across nodes, no gang scheduling, an SMP guest across nodes) and the unestimated proof cost of B are real, and none of them has to be solved for a system that is one instance.

## What this does not settle

- When several instances start, which node owns the IOMMU root table, a single hardware structure that one `Kernel` value holds today, and the IOAPIC once device interrupts are routed through it, and how device init, which hands every device to one root, and the machine-wide PCI names a process passes fit a per-node root. Recorded with the deferred work.
- Whether a spanning library is ever written, and if so whether it is C's sibling-process shape.
