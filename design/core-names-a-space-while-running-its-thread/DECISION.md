---
title: "A core names a space only while it runs one of the space's threads, and one verified operation moves it from root to root"
date: 2026-11-12
status: active
tags: [capability, address-space, scheduling, verified]
one_line: "Past boot a core's page-table base register always names a root: the space of the thread it runs, or the kernel's own root under KERNEL_TAG when it runs none. A thread switch is one verified operation that goes from the leaving thread's root straight to the arriving thread's, passing through the kernel's root only when the arriving space needs a fresh id and the core's ids have run out; a kernel entry is no transition."
revisit_if: "The cost of the idle write is measured on a core that does not tag its TLB, or measured as mattering on one that does, so that keeping an idle core on its last space would pay for a register that outlives its thread."
confidence: "The human's choice of policy, eager over lazy, on the cost argument below; the cost of a register write is something to measure, not cite, and no measurement has been taken."
---

# A core names a space only while it runs one of its threads

## Decision

Past boot a core's page-table base register always names some root, and every transition goes from one root to another. The root is the space of the process whose thread the core runs, or the kernel's own root under `KERNEL_TAG` when the core runs no thread: in the model `cores[c].space` is `Some(s)` for the first and `None` for the second, and `None` means the kernel's root, a real table every core boots on and no space can have, `design/teardown-driven-by-retype/`. A core that goes idle writes the kernel's root. A kernel entry is not a transition: every process space carries the kernel's entries (`Spaces::kernel_entries`), so a system call or an interrupt from a thread of A runs on A's root.

A thread switch is one verified operation of `CapKernel`: it takes core c from the thread leaving to the thread arriving, or to no thread, and does the load of the arriving thread's space, the register write and making the thread current inside its own proof. The glue chooses no order among them. The switch goes from A's root straight to B's with one register write, when B holds a valid id on the core or the core has ids left in its generation to hand B a fresh one: `load_space` starts no new generation then, so the id A holds stays valid and A's tag stays A's while the register names it. In one case alone it passes through the kernel's root: B holds no valid id on the core and the core's ids have run out (`next_pcid == PCID_MAX`, known before the load), so the load flushes every context and starts a new generation, which hands the ids out again from the start. A register still naming A under A's old tag across that flush could let the core cache entries under a tag the new generation hands to another space. So the operation writes the kernel's root under `KERNEL_TAG`, loads B, which flushes and hands B its id, and writes B's root. That happens once per `PCID_MAX - 2` fresh ids on a core and comes with a full flush, so its second write costs nothing that matters.

What the eager rule buys the teardown: a dead process's space is named by no register once no core runs one of its threads. Destroy's IPI already makes each core that runs one of its threads take a kernel entry and stop it, `design/teardown-driven-by-retype/`, and the stop is a switch, so it leaves the space; the retire that reclaim needs, which refuses while a register names the space, needs no step of its own.

## Context

The teardown work wrote the mechanism of a core's register: the record of the space it names, `BaseRegister`, the kernel's root, `tag_written`, and `switch_space` as the one writer, `design/teardown-driven-by-retype/` and `design/flush-without-waiting/`. It did not decide when a core leaves a space. With only that mechanism, nothing on the running system makes a core leave one: the boot is the only caller of `switch_space` outside the witnesses, and a destroyed process whose space an idle core still names would never be reclaimed once threads are wired, since reclaim refuses while a register names a dead process's space. The scheduler's round would otherwise have decided it in passing.

## Reasoning

On a core that tags its TLB the eager write drops nothing: `load_translation_root` sets CR3 bit 63 where CR4.PCIDE is set, and a write with that bit set may keep using the mappings stored under the written PCID (AMD64 APM volume 2, section 5.5.1); aarch64 tags by ASID. Both gate targets tag. So eager costs two register writes around an idle period, and a refill of the TLB only on an x86_64 core without PCID, which the gate boots none of. No AMD document gives the cost of a CR3 write in cycles; that is for a measurement.

Lazy, against that, is new proof and design work, not a switch to flip: the model would keep a register that outlives the thread that put it there, each kernel entry would need a second check beside the current-thread one (no current thread and a register naming a dead space), and an idle core would have to be woken to leave a dead space. Eager empties the register through destroy's existing IPI and the thread stop.

One operation rather than a sequence of glue calls: the ordering of leave, load, write and make-current is what keeps a register naming only a loaded, unretired space with a valid id (`registers_wf`, `names_wf`), and a core on its thread's space (`current_wf` in `kernel/verified/capability/thread.rs`). Proving it once inside the operation leaves the glue nothing to get wrong.

Going straight from A to B, rather than always through the kernel's root, saves a register write on every cross-process switch; the rollover case that needs the kernel's root is rare and pays a full flush anyway.

## Alternatives rejected

- **Lazy: an idle core keeps its last space.** Saves the write when the same process runs next. It needs a register that outlives its thread, a second check on entry and an idle core woken to leave a dead space, above. A performance optimisation to weigh later, on a measurement.
- **Always through the kernel's root on a cross-process switch.** Keeps `load_space`'s requirement that the register name no space, at a second register write on every switch between processes.
- **The glue composes the switch.** It would own an ordering whose mistakes the proof cannot see, and the eager rule would hold only as far as the glue keeps it.

## What this does not settle

- Which thread a core runs next, and when: `design/cpu-time-as-capability/`.
- The cost of a register write on either target, which no measurement has taken.
