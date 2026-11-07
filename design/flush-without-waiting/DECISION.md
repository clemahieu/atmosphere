---
title: "The kernel never waits for another core under the lock; flushes are epochs, IPIs and return again"
date: 2026-11-06
status: active
tags: [multicore, lock, memory, verified]
one_line: "A ghost per-core TLB model holds possibly stale translations keyed by space and core; unmap bumps a flush epoch, sends IPIs and returns again; each core's handler flushes every context and records its acknowledgement on its own kernel entry; retype requires every core's acknowledgement to have reached the epoch, a token only flush glue can produce."
revisit_if: "The hardware gains a broadcast invalidation the kernel can rely on (this host reports no INVLPGB), or a flush that returns again is measured as the cost that dominates unmap."
confidence: "The no-wait rule is forced by the lock, see reasoning; the epoch comparison and model are in kernel/verified/capability/kernel.rs and kernel/src/flush.rs, with the flush itself counted glue."
---

# Flushing without waiting under the lock

## Decision

A ghost per-core TLB model holds possibly stale translations, keyed by space and core, including the paging-structure caches for table pages. A space's translations enter it when a core loads that space. Unmap marks them stale. Only the flush glue removes them, and that is the token retype requires; the glue is listed on `tools/external-body-list`.

Storage is bounded: one flush epoch, one acknowledged epoch per core in the per-CPU list, and one stale epoch per block, the word at the block's level, so an unmap writes the 4K, 2M and 1G words for its page and a free reads its block's one. The comparison is strict: unmap bumps the epoch first and records the new value, and retype requires every core's acknowledgement to have reached it. The handler's flush covers all PCIDs, since a flush of the current one would leave stale entries under others and its acknowledgement would then mean nothing.

The kernel never waits for another core while holding the lock. A flush bumps the epoch, sends IPIs and returns `again`. The target's handler flushes and, entering the kernel as any entry does, records its acknowledgement under the lock, so all of this stays inside the `Kernel` value. Each kind of address space has its own flush with the same token: IPI for a process table, IOTLB invalidate for an IO table, kick plus TLB_CONTROL for a nested table, `design/vmm-over-svm/`.

## Reasoning

A core may be spinning for the lock with IF clear, `design/one-lock-bounded-steps/`, and so cannot take an IPI; a holder that waited for it would deadlock. Returning `again` and letting the acknowledgement arrive on the target's own entry is the only shape that keeps the no-wait rule and keeps the state inside the kernel value, `design/one-kernel-instance/`.

Keying the model by loaded space, and covering table pages, is what makes the token mean something for a retype of a table page as well as a frame. An acknowledge counter outside the kernel value was an earlier shape and was rejected because the proof could not see it.

## Alternatives rejected

- **Wait under the lock for the IPI.** Deadlocks against a waiter with interrupts off.
- **Flush only the current PCID.** Stale entries survive under other PCIDs and the acknowledgement proves nothing.
- **An acknowledge counter outside the kernel value.** Invisible to the invariant.
