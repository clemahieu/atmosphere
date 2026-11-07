---
title: "The multicore kernel is a clustered multikernel: one instance and one lock per node"
date: 2026-11-05
status: active
tags: [multicore, lock, kernel-state]
one_line: "A node is a set of cores with one kernel instance and one queue lock; a system may have any number of nodes, laid out at boot; nothing in kernel state is shared between nodes, memory crosses only as a quiescent untyped handoff, and stealing is pager policy."
revisit_if: "Lock hold times measured on this kernel make a one-node system's contention a real workload's problem and a smaller node is not the answer, or a workload needs kernel state shared between nodes that a handoff cannot express."
confidence: "The shape is a judgement against published multicore kernels; the lock numbers below are measured on the host with user-space threads, not this kernel, and its own lock has not been measured."
---

# The multicore kernel is a clustered multikernel

## Decision

A node is a set of cores with one kernel instance and one lock. A system has any number of nodes; node layout is a boot setting, so an architecture or a load can choose it. Nothing in kernel state is shared between nodes. Memory crosses nodes only as a quiescent untyped handoff, the one cross-node operation the kernel supplies. Stealing memory between nodes is user-space pager policy over per-node pools of untyped, since under `design/untyped-memory/` the kernel has no free lists to steal from.

The lock inside a node is a queue lock, `kernel/verified/queue_lock.rs`: each waiter spins on its own cache line, so the line holding the lock's word does not bounce between waiters on each handover.

The first stage is one node holding every core, `design/one-kernel-instance/`.

## Context

The kernel had one big lock, and the second core had never run. The question was how the kernel should use several cores, weighing a big lock, static per-core kernels, clustered kernels, fine-grained locks and replication against verification cost, scaling and purity.

## Reasoning

A per-core kernel with resource stealing was the first proposal. A node of any size generalises it: one core per node is that setting, and one node holding every core is the big lock. Choosing the size at boot keeps both available without two kernels.

Measured on the host, a 9950X3D, on 2026-11-05, in TSC ticks, with user-space Linux threads pinned to cores, not this kernel. Cache-line round trip: 227 between SMT siblings, about 300 to 370 within a CCD, 680 across CCDs. A simulated big lock with an assumed 400-tick hold plus writes to 8 shared words, then a spin outside the lock, in millions of operations per second across all cores:

| ticks outside the lock | 1 core | 4 cores | 8 cores | 16 cores across CCDs | ticket lock, 16 cores |
|---|---|---|---|---|---|
| 2000 | 1.67 | 6.42 | 6.69 | 4.65 | 2.81 |
| 8000 | 0.50 | 1.96 | 3.92 | 4.75 | 3.16 |
| 32000 | 0.13 | 0.53 | 1.05 | 2.05 | 2.06 |

So a lock every waiter spins on fell well below a queue lock across two CCDs, and throughput under one lock stops scaling near a shared-cache cluster. That is why the lock is a queue lock and why the node size is not fixed at the whole machine.

CPUID on this host reports no INVLPGB, so TLB shootdown needs IPIs, and no RTM, so transactional memory is not an option.

## Alternatives rejected

- **Big lock alone.** Every process shares a lock no capability governs, which leaks timing, and scaling stops near a shared-cache cluster. It remains available as the one-node setting.
- **Static per-core kernels**, the shape seL4 is verifying. No runtime rebalancing. It is a setting of this design minus handoff.
- **Fine-grained locks.** Published seL4 experiments report 4 locks per IPC and about 30 percent overhead, and breaking up the kernel's invariant into per-lock pieces means redoing every proof.
- **Node replication** of kernel state. IPC is nearly all writes.
- **Transactional memory.** The CPU reports no RTM.

## What this does not settle

- Whether Verus ghost permissions can move through a small verified channel between instances, which the handoff needs. Untested.
- The IPC cost between nodes, an IPI where a shared kernel would cost a cache-line transfer. Not measured here.
- The hardest rule, that a frame must never become a kernel object while another node maps it, is stated, not proven, until the multi-node work starts.
