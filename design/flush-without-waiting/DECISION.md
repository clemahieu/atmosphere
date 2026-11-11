---
title: "The kernel never waits for another core under the lock; flushes are epochs, IPIs and return again"
date: 2026-11-10
status: active
tags: [multicore, lock, memory, verified]
one_line: "A ghost per-core TLB model holds possibly stale translations keyed by space and core; unmap bumps a flush epoch, sends IPIs to exactly the cores that loaded the space and returns again; each core's handler flushes every context and records its acknowledgement on its own kernel entry; an IOMMU's invalidate waits for its completion inside the glue, since an IOMMU is not a core; retype requires every core's and present IOMMU's acknowledgement to have reached the epoch, a token only flush glue can produce."
revisit_if: "The hardware gains a broadcast invalidation the kernel can rely on (this host reports no INVLPGB), a flush that returns again is measured as the cost that dominates unmap, or an IOMMU's completion wait is measured as the longest step under the lock."
confidence: "The no-wait rule is forced by the lock, see reasoning; the epoch comparison and model are in kernel/verified/capability/kernel.rs and kernel/src/flush.rs, with the flush itself counted glue."
---

# Flushing without waiting under the lock

## Decision

A ghost per-core TLB model holds possibly stale translations, keyed by space and core, including the paging-structure caches for table pages. A space's translations enter it when a core loads that space. Unmap marks them stale. Only the flush glue removes them, and that is the token retype requires; the glue is listed on `tools/external-body-list`. Each core's state also records the space its page-table base register names, written only with the token of the glue that wrote the register, `load_translation_root`, which records the root and the tag written, and only for a space the core has loaded that is not retired and under the tag that space holds on the core, a tag the space keeps while the register names it, so a core's acknowledgement of a space's retire is not undone by the core walking that space again. A register naming no space is written under `KERNEL_TAG`, which no space holds, at a root no space can have; that the root is the kernel's own, outside every untyped and mapping nothing of a space, is owed by the glue, not kept by the model; `design/teardown-driven-by-retype/`.

Storage is bounded: one flush epoch, one acknowledged epoch per core in the per-CPU list, and one stale epoch per block, the word at the block's level, so an unmap writes the 4K, 2M and 1G words for its page and a free reads its block's one. The comparison is strict: unmap bumps the epoch first and records the new value, and retype requires every core's acknowledgement to have reached it. The handler's flush covers all PCIDs, since a flush of the current one would leave stale entries under others and its acknowledgement would then mean nothing.

The kernel never waits for another core while holding the lock. A flush bumps the epoch, sends IPIs and returns `again`. The IPIs go to the unmapped space's list of cores, exactly the cores that have loaded it. Only those may hold an entry of the space in the model, so a core that never loaded it, such as an isolated core of another partition, is never sent one; `flush_sent` in `kernel/verified/capability/unmap.rs` states it. A core stays on the list once on it, and of the cores on it only those that depend on the space may hold an entry: a core on the list of a dead process's space that a retype retired since the core last loaded it no longer depends on it once its acknowledgement reaches the retire epoch, since the retire ran while no core's base register named the space and none can name it again until a load clears the retire, `design/teardown-driven-by-retype/`. The target's handler flushes and, entering the kernel as any entry does, records its acknowledgement under the lock, so all of this stays inside the `Kernel` value. Each kind of address space has its own flush with the same token: IPI for a process table, IOTLB invalidate for a device space, kick plus TLB_CONTROL for a nested table, `design/vmm-over-svm/`.

An IOMMU is acknowledged inside the step that invalidates it. The arch module's glue writes an invalidate of all the IOMMU's caches and a command that completes after it to the IOMMU's command ring (INVALIDATE_IOMMU_ALL and COMPLETION_WAIT on AMD-Vi, CMD_CFGI_ALL, CMD_TLBI_NSNH_ALL and CMD_SYNC on SMMUv3), moves the tail and spins until the IOMMU shows the last one done, then returns the token for the epoch it started at; `flush_iommu` hands that token to `acknowledge_iommu` under the same lock hold.

## Reasoning

A core may be spinning for the lock with IF clear, `design/one-lock-bounded-steps/`, and so cannot take an IPI; a holder that waited for it would deadlock. Returning `again` and letting the acknowledgement arrive on the target's own entry is the only shape that keeps the no-wait rule and keeps the state inside the kernel value, `design/one-kernel-instance/`.

The no-wait rule is about cores. An IOMMU takes no lock and no interrupt: it reads its command buffer whatever any core's IF says, so a core waiting on its completion word cannot deadlock against a core spinning for the lock. The wait is bounded by the IOMMU's command latency, not by another core's progress. Acknowledging on a later entry would need a second glue item to read the completion word and a ghost record of the epochs submitted to each IOMMU, so that a token could not claim an epoch the invalidate did not start at; waiting in the glue needs neither, and the token states the epoch the caller passed, as a core's does.

Keying the model by loaded space, and covering table pages, is what makes the token mean something for a retype of a table page as well as a frame. An acknowledge counter outside the kernel value was an earlier shape and was rejected because the proof could not see it.

## Alternatives rejected

- **Wait under the lock for the IPI.** Deadlocks against a waiter with interrupts off.
- **Flush only the current PCID.** Stale entries survive under other PCIDs and the acknowledgement proves nothing.
- **An acknowledge counter outside the kernel value.** Invisible to the invariant.
- **Acknowledge an IOMMU on a later entry.** Submit the invalidate, return, and read the completion word when retype next needs the epoch. It keeps the lock hold shorter by one command latency, at the cost of a second glue item and ghost state tying the stored word to a submitted epoch.

## What this does not settle

- How long an IOMMU's completion wait holds the lock, which is unmeasured, and what a step does about an IOMMU that halts command processing and never stores. The glue relies on boot listing an IOMMU as present only once its command buffer runs and it reports INVALIDATE_IOMMU_ALL (IASup); an IOMMU that rejects the command halts its command processing and the glue spins.
- A device's own IOTLB. INVALIDATE_IOMMU_ALL empties the IOMMU's caches and not a device's address translation cache, so the token covers a device only while its device table entry leaves ATS off.
