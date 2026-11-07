---
title: "CPU time is granted by a core capability with fixed priorities; scheduling contexts are deferred"
date: 2026-11-05
status: active
tags: [scheduling, capability]
one_line: "Per-core run queues, fixed priorities, turns at equal priority, one selection function and one scheduling record per thread. A core capability allows placing a thread on that core at or below its maximum priority, a derived copy may lower it, and a placement is a binding so CPU time is revocable. Budgets and periods are deferred, with three constraints kept so they stay addable."
revisit_if: "A workload needs a bound on how much time a thread can take, which fixed priorities cannot give, or temporal isolation inside a core is wanted by design/isolation-claim/."
confidence: "The human's choice to defer scheduling contexts; the estimate that they cost about 600 to 900 lines of code and 2,500 to 4,000 of proof plus a one-time rework of the scheduler and IPC proofs is reasoned from structure, not measured."
---

# CPU time as a capability, priorities now

## Decision

Per-core queues over the intrusive list, fixed priorities, turns at equal priority, one selection function and one scheduling record in a thread. A core capability allows placing a thread on that core at or below its maximum priority, and a derived copy may lower it. A thread with no placement cannot run, so CPU time is granted. A placement is a binding under the core capability, so revoking that capability makes its threads Inactive: CPU time is revocable. Timer: a per-core capability arms a deadline that signals a notification, multiplexed with the kernel's slice, so a user-level scheduler can be built. Thread placement across cores is the default thread library's policy, and rebalancing, if wanted, is a service holding thread capabilities.

Scheduling contexts, a budget and period per thread, are deferred. Three constraints are kept so they stay addable: a reply is an explicit kernel object, `design/ipc-with-reply-object/`; programs create threads and do IPC through the runtime library; a thread's scheduling state stays in one record behind one selection function. The marker telling a preempted thread's full saved frame from a blocked thread's partial copy is a field on the thread set at each save point. Extended register state lives in the thread object. Running a guest adds no third saved-frame kind, `design/vmm-over-svm/`.

Accepted limit: CPU time is only partly governed by capabilities. A high-priority thread can starve lower ones on its core until something stops it, and time spent in a server is charged to the server. Whole-core grants or a trusted top-priority manager contain this as policy.

## Context

Containers owned the CPUs and the run queues, so removing them under `design/untyped-memory/` removed the kernel's scheduling authority, and timer preemption did not exist. Round-robin alone was dropped at once, because a user-level scheduler cannot be guaranteed to run without priorities. The question was priorities now, or priorities plus scheduling contexts now.

## Reasoning

The context object, accounting at every kernel entry and exit, donation and timeouts are new work whenever they are done, and budget configuration is paid per component as budgets are used. A context with equal budget and period behaves as round-robin, so priorities-only is a special case and existing threads need not change behaviour. Deferring adds a one-time rework of the scheduler and IPC proofs, bounded because the kernel's size does not grow with applications; the only cost that grows with time is programs calling kernel IPC directly, which the library constraint limits. seL4's MCS took years to verify, but it was added to an existing verified kernel with a different prover, so that evidence does not separate retrofit cost from inherent cost.

## Alternatives rejected

- **Round-robin only.** No guarantee a user-level scheduler runs.
- **Scheduling contexts now.** New work either way; deferring costs the rework above and nothing that grows.
