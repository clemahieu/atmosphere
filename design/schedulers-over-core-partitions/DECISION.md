---
title: "User-level schedulers own whole cores; a real-time library and a general scheduler never share one"
date: 2026-11-09
status: active
tags: [scheduling, capability, real-time]
one_line: "Schedulers are swappable user programs over whole-core partitions handed out as derived core capabilities. A real-time library is the only placer on the cores it holds and runs a cooperative class above a preemptive one; a general scheduler holds the rest, places every runnable thread it owns and lets the kernel preempt. The kernel's fixed-priority selection is unchanged."
revisit_if: "Budgets and periods land, which contain a runaway thread on a shared core; or the kernel gains a block-and-wake event on a placement and per-thread consumed time, which make a scheduler that places one thread per core and owns the quantum (fair share) possible."
confidence: "A judgement by the human between three ways of hosting two policies, informed by published partitioned and core-granting systems. Nothing here is measured on this kernel; the latency bound of an isolated core is the lock's, and its step is not yet measured."
---

# Schedulers over whole-core partitions

## Decision

Schedulers are user programs, swappable like any other, and each owns whole cores. The machine is partitioned by core, not by priority on a shared core. The root derives core capabilities from the ones boot gave it, `design/root-process-at-boot/`, and hands them out; a holder may derive again with a lower maximum priority and hand those on, so partitions nest. The root keeps the originals and does not place on a core it has given away.

The kernel is unchanged: fixed priorities, turns at equal priority, one selection function, placement as a binding under a core capability, `design/cpu-time-as-capability/`.

Two schedulers come first.

- **A real-time library** holds the core capabilities for the cores it keeps and is the only placer on them. Its cooperative class never shares a core with a thread it does not place. In one process it runs a cooperative class, a thread that runs until it yields or blocks, above a preemptive class sliced by the library's own timer, the two classes Zephyr mixes in one image. The kernel takes turns between placed threads of equal priority, so the library places only the chosen thread of each class; a scheduler thread above both waits on the core's timer notification, rotates the preemptive class, and never stops a cooperative thread. A blocking call unplaces the caller and places the next ready thread. The slice is the library's tick count, not consumed time and not a budget. That is the kernel-thread form, the first one built, because it exercises stop, start and the timer path. The carrier form, one placed thread per core switching user contexts by a function call, is the same cooperative class without a kernel switch per yield.
- **A general scheduler** is a process holding derived core capabilities for the remaining cores. It places every runnable thread it owns and lets the kernel preempt: the highest priority runs, equal priorities take turns on the kernel's slice, and a block deschedules only the thread that blocked. Its policy is the priority it gives each thread. There is no second slice fighting the kernel's.

## Isolated cores, two grades

**Same kernel instance.** A core is isolated when it has one placer and no foreign placement, takes no kernel tick while it has at most one runnable thread, receives no interrupt it did not bind, and receives no flush IPI for a space it never loaded. One placer and no foreign placement follow from who holds the core capability. Flush IPIs already go only to the cores that loaded the space, `design/flush-without-waiting/`. The kernel lock remains shared: a kernel entry on an isolated core can wait behind one step of every other core, so its latency bound is the number of cores times the longest step, `design/one-lock-bounded-steps/`.

**Own kernel node.** A core in a node of its own, `design/multicore-kernel-shape/`, has its own lock as well, so no other core's step lies on its path. This grade waits on several kernel instances, which are deferred, `design/one-kernel-instance/`.

## Consequences

- A runaway cooperative task hangs its core, not the system. Without budgets, this is the only temporal containment the design offers.
- Time spent in a server is charged to the server, `design/cpu-time-as-capability/`. A real-time partition therefore hosts its own servers, or talks outward by notification, which does not block it on another partition's placement.
- Real-time cores sit on one CCD. A cache-line round trip across CCDs costs about twice one within a CCD on this host, `design/multicore-kernel-shape/`; keeping a partition inside a CCD is a convention, not a measured requirement.

## Context

`design/cpu-time-as-capability/` gives CPU time as core capabilities over fixed priorities and accepts that a high-priority thread can starve lower ones on its core. Two kinds of scheduling are wanted on top of it: a real-time library with cooperative and preemptive threads, and the familiar preemptive policy applications assume. The question was how the two share the machine.

## Reasoning

On a shared core, a cooperative class placed above general threads runs until it blocks and the general threads wait; placed below, the general threads preempt it and it is no longer cooperative. The published ways to put two policies on one CPU need what this kernel lacks: CPU Inheritance Scheduling (Ford and Susarla, OSDI 1996) a policy-free dispatcher that runs threads only by donation, and A Hierarchical CPU Scheduler for Multimedia Operating Systems (Goyal, Guo and Vin, OSDI 1996) a bandwidth share, which is a budget. Partitioning by whole cores needs neither, because no two policies meet on a core.

Partitioning is also what published real-time and core-granting systems do. Quest-V assigns cores statically to its sandboxes (Quest-V: A Virtualized Multikernel for Safety-Critical Real-Time Systems). RTEMS clustered scheduling runs one scheduler instance per cluster of processors. An Empirical Comparison of Global, Partitioned, and Clustered Multiprocessor EDF Schedulers (Bastoni, Brandenburg and Anderson, RTSS 2010) and On the Scalability of Real-Time Scheduling Algorithms on Multicore Platforms: A Case Study (Brandenburg, Calandrino and Anderson, RTSS 2008) found partitioned scheduling the strongest choice for hard real-time on the multicore machines they measured. Arachne: Core-Aware Thread Management (Qin et al., OSDI 2018) grants applications whole cores through a core arbiter, and Akaros dedicates cores to a many-core process (Rhoden, Operating System Support for Parallel Processes, UC Berkeley 2014).

A general scheduler that places every runnable thread needs no kernel fact beyond those it has. One that places only its chosen thread and switches it from its own timer would have to know when that thread blocks in IPC, and a separate process does not see its threads' IPC.

## Alternatives rejected

- **Both classes on shared cores, cooperative above.** Zephyr's model in one image. No core is given away, but a hung cooperative thread stops every general thread on its core, and with the class on every core, the system.
- **One placed thread per core, the general scheduler owning the quantum, now.** It gives a weight or a virtual time a real quantum, as fair-share policies want, but it needs a block-and-wake event on a placement that the kernel does not give, and fair share needs per-thread consumed time, which the kernel does not keep.
- **Budgets now.** Scheduling contexts would contain a runaway thread inside a shared core; they are deferred by `design/cpu-time-as-capability/`.

## What this does not settle

- The kernel facts the first grade needs and does not have: no tick on a core with at most one runnable thread, and interrupt delivery bound to a core through its core capability.
- The latency bound in cycles. It waits on the step budget `design/one-lock-bounded-steps/` leaves unset.
- Which priorities the general scheduler computes, and how the root decides which cores are real-time.
