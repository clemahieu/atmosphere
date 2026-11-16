---
title: "A core flushes its predictors and its L1D before it runs a thread of a core share other than the last it ran"
date: 2026-11-15
status: active
tags: [scheduling, capability, side-channel, verified]
one_line: "A share of a core is a core capability, named by a 64-bit number boot or a derive gives it once, which a move keeps and a placement copies into the thread. Each core holds a flush token naming the share of the last thread it ran in user mode; switch_thread and boot's entry, making current a thread of another share, first run the arch module's flush, which returns the new token. On x86_64 the flush is IBPB through PRED_CMD and an L1D write-back and invalidate through FLUSH_CMD, each where CPUID reports it; on aarch64 it is CFP, DVP and CPP RCTX over every EL0 context where FEAT_SPECRES is reported, and no L1D command."
revisit_if: "The flush is measured as a cost that matters on a workload whose shares within one tenant take turns on a core, which is when the share is widened to the holder of the parent capability the divider handed out; or a target gains an architectural command that clears what this flush leaves, such as a whole-core buffer clear, which is when the command is added here."
confidence: "The trigger is a judgement: it follows the hypervisor practice of flushing at a change of tenant, with the capability as the tenant's mark, and its cost is unmeasured. What each command clears is the manuals' word, cited below; whether a core honours it is the hardware's."
---

# A core flushes on a change of core share

## Decision

A share of a core is a core capability, `design/cpu-time-as-capability/`. Each core capability carries a number naming its share, 64 bits, given once: boot gives the root's capability for core c the number c + 1, and a derive of a core capability gives the child the kernel's next number and advances it. A move keeps the number, since the node keeps its children and its payload, `design/sharing-by-derive/`. A placement copies the number of the capability it hangs under into the thread's placement. So two live core capabilities carry different numbers, and a thread placed under one carries that one's. 0 names no share and no capability carries it.

Each core holds a flush token, a tracked value of the arch module's with fields private to it, `design/arch-module/`, naming the core and a share. Boot makes one per core, naming 0, as it makes each core's `BaseRegister`, so a core's first thread is always of another share than its token's. The arch module's flush is the only maker of a token past boot: given the core's token and a share, it runs the core's flush commands and returns a token naming that share. Two operations make a thread current on a core: `switch_thread` in `kernel/verified/capability/switch.rs`, and `enter_boot_thread` in `kernel/verified/capability/thread.rs`, boot's entry into the root's thread, which boot placed through the root's capability for the core, `design/root-process-at-boot/`. Each compares the arriving thread's share with the share the core's token names, and when they differ runs the flush before the thread is made current; boot's entry always does. The kernel's invariant: the thread current on a core is of the share that core's token names. A core that goes idle keeps its token, so a core that runs the same share before and after an idle period does not flush.

The commands, run on the core the token names:

- x86_64: WRMSR to PRED_CMD (MSR 049h) with IBPB, bit 0, where CPUID Fn8000_0008_EBX[IBPB] (bit 12) is 1, which stops older indirect branch predictions influencing later indirect branches (amd-apm2 3.2.9, Figure 3-14); then WRMSR to FLUSH_CMD (MSR 10Bh) with L1D_FLUSH, bit 0, where CPUID Fn0000_0007_EDX[L1D_FLUSH] (bit 28) is 1, which writes back and invalidates the L1 data cache (amd-apm2 6.6.1, Figure 6-3). Each write is dispatch serializing, so no younger instruction runs before it completes.
- aarch64: where ID_AA64ISAR1_EL1.SPECRES reports FEAT_SPECRES, CFP RCTX, DVP RCTX and CPP RCTX with an argument naming EL0 of every ASID in the current VMID and Security state, then DSB and ISB, after which no control flow, data value or cache prefetch prediction for those contexts is influenced by execution before them (arm-arm A2.2 FEAT_SPECRES, B2.5.7, C5.6.1, C5.6.3, C5.6.4). There is no L1D command.

Both targets take those reports from the core's processor report, read once at that core's boot, `design/processor-report-read-once/`. The flush does not execute CPUID or read an ID register.

The flush reports which commands the core ran, so the glue can say it on the serial line; the proof's claim is that the flush ran, not what the hardware cleared.

The numbers have a limit: a derive of a core capability is refused once the next number is the largest 64 bits hold, as an unmap is refused once the flush epoch is at its own, `design/flush-without-waiting/`. At one derive a nanosecond the limit is 584 years away.

## Context

Hypervisors clear a core's predictor state, and on cores that need it its L1D, when the core passes from one tenant to another, so that one tenant cannot train predictions another's execution follows or read the other's lines from the cache by timing. Here a tenant's share of a core is a core capability the divider derives for it, `design/schedulers-over-core-partitions/`, and moving a core between tenants is a revoke of one tenant's share and a derive of another's, `design/divider-proven-by-invariant/`. The kernel needed to know, at a switch, whether the arriving thread is of another share than the last, from state it can read in constant time.

A core capability's node index cannot be that state. A move renames the node, `kernel/verified/capability/moving.rs`. A freed slot takes the next capability put there, which can be another tenant's share: a divider holding both tenants' shares in its own table can delete one and derive the other into the same slot, so the core's record would match a share it never flushed for. And the switch cannot read the parent of a thread's placement node: the tree's parent map is ghost, the list holds it only as depth order, and a copy kept in the thread would be renamed by every move of the capability above it. A number given once and copied at placement has none of these faults: a move keeps it, a slot reused gets a new one, and the thread holds its own.

## Reasoning

The share is the narrowest mark that always separates tenants: two tenants never hold the same core capability, and each share the divider hands a tenant is derived and so numbered afresh. Two shares within one tenant, two capabilities its threads are placed under, flush between them too, which costs time and not isolation. A share handed on by a move keeps its number and the threads placed under it, so a tenant that moves its share to another hands over a flush domain with threads already in it; the divider moves a core between tenants by revoke and derive, which numbers the new share.

The check sits in the operations that make a thread current, because a core runs another share's code only after one of them, `design/core-names-a-space-while-running-its-thread/`; a kernel entry that returns to the thread it came from changes no share. Boot's entry flushes once on a core nothing has run on, which costs one flush and keeps the flush the only maker of a token past boot. Between the flush and the return to user mode the core runs only kernel code, which reads the kernel's state and the arriving thread's frame, not the leaving tenant's memory.

A token that only the arch module makes, held per core with the invariant above, is what makes the claim a proof and not a convention: verified code cannot make a thread of another share current without calling the flush, as it cannot write the base register without the core's `BaseRegister`, `design/flush-without-waiting/`. Each command is a hardware guarantee in the arch module, counted on `tools/external-body-list` with its cite, `design/who-vouches-for-an-unproven-claim/`.

On aarch64, FEAT_CSV2 already keeps one hardware-defined context from controlling another's prediction, and the context at EL0 is told apart by ASID (arm-arm B2.5.4). That is not enough on its own: ASIDs are handed out again at each generation of a core's ids, `design/address-spaces-as-objects/`, so the space that gets an ASID after a rollover shares the context of the space that held it before. The RCTX instructions name every ASID and so cover that case. A core that does not report FEAT_SPECRES runs no command, and its separation rests on FEAT_CSV2 where that is reported; the Orange Pi's own kernel reports its cores' Spectre v2 mitigation as CSV2.

## Alternatives rejected

- **Flush on every switch between processes.** Simple to state and needs no number: the space's change already marks it. A tenant is usually many processes, so it flushes at every switch inside a tenant, which buys nothing hypervisors give; and a process's identity is the address of its block, which a retype reuses, so it has the same reuse fault as a node index unless retype clears every core's record.
- **The core capability's node index.** Renamed by a move, reused by a later capability in the same slot, and unreadable from the thread at a switch; above.
- **Flush at every switch.** Covers threads of one tenant that do not trust each other, which the tenant can already separate by placing them under different shares.
- **Flush when the divider moves a core.** The move runs on whatever core the divider runs on, so flushing the moved core would need an IPI and an acknowledgement before the new share may run there, and it would still miss a share that reaches a core by any other step. The switch is where the new share's code is about to run, on the core that runs it.

## What this does not settle

- SMT siblings: a core's sibling thread shares its predictors and L1D while both run, and no flush on one covers the other. Keeping tenants off sibling pairs is the divider's partition.
- Caches shared between cores, L2 and L3, and every buffer the core's commands do not clear: on x86_64 the store, fill and load buffers, and the return address predictor on a core that does not report IBPB_RET (CPUID Fn8000_0008_EBX bit 30, amd-apm2 3.2.9). On aarch64, the L1D, for which there is no command.
- An Intel core reports IBPB in CPUID leaf 7, in a document `tools/hardware-documents` does not list; until it is listed the flush reads AMD's bit, and an Intel core reports no IBPB.
- The firmware calls Arm cores without FEAT_SPECRES offer for predictor invalidation, whose specification is not among the listed documents.
- The kernel's own exposure to predictions trained in user mode, which is a matter for the kernel's entry and not for the switch between tenants.
- Timing channels, which `design/isolation-claim/` leaves out.
