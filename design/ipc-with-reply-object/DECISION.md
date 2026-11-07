---
title: "Endpoints rendezvous over an intrusive queue, and a reply is an explicit kernel object"
date: 2026-11-06
status: active
tags: [ipc, capability]
one_line: "Endpoints rendezvous with queues over the intrusive list, so there is no fixed thread bound; a reply is a retyped object named at receive and used once; a blocked receiver's reply and destination slot are stored as indices and resolved through the root pointer at the match; a match skips dead waiters a fixed number per entry."
revisit_if: "Scheduling contexts are added, which is what the explicit reply object keeps possible; or a workload needs asynchronous messages with payload, which notifications do not carry."
confidence: "Rendezvous and the explicit reply follow from the CPU-time decision's constraints; resolving at the match is the answer to a memory-safety finding and is a stated invariant."
---

# IPC: rendezvous, and a reply is an object

## Decision

Endpoints rendezvous, with queues over the intrusive list, so the old 128-thread bound goes. A reply is an explicit retyped object: receive names a reply capability, the kernel binds the caller to it, and reply uses it once. The bound caller is held both ways and cleared by either side's death; if the holder dies the caller gets an error when the holder's teardown is driven.

A blocked receiver's reply capability and destination slot are stored as indices and resolved through the root pointer at the match. If the reply is gone, the call fails with an error to the sender. If the destination is gone or occupied, the message is delivered without the capability and a status flag says so. A match skips and removes dead waiters, a fixed number per entry, then returns `again`. Notifications are a word and a queue.

Faults: a thread names a fault endpoint at configuration, the message is kind, address and code, and the reply resumes it. With no handler the thread stops, `design/teardown-driven-by-retype/`. A thread suspended while blocked and then started returns an interrupted status, so the runtime can retry or unwind.

## Reasoning

An explicit reply object is the first of three constraints kept so that scheduling contexts stay addable, `design/cpu-time-as-capability/`: seL4's MCS needed explicit reply objects for budget donation over call and reply, and this kernel had no reply concept to retrofit.

Resolving the reply and the destination slot at receive time was found unsafe: a revoke, retype and regrant between receive and match would leave the match writing through a stale pointer into another process's frame, and a destroyed thread still queued could receive a capability that was then lost. Storing indices and re-resolving at delivery, with dead waiters skipped, is the fix, and the occupied-slot case is stated so that no delivery is silently dropped.

## Alternatives rejected

- **A reply implicit in the thread**, as in classic L4. Cannot carry a donated budget later and has no object for revocation to act on.
- **Resolve pointers at receive time.** Unsafe, see above.
