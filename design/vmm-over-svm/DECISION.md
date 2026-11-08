---
title: "A guest is a principal with no capabilities; the VMM is an ordinary process and the kernel owns the VMCB"
date: 2026-11-05
status: active
tags: [virtualization, capability, address-space]
one_line: "A guest touches only what its nested table maps and what its intercept maps let through. The VMM is an ordinary process; VMRUN needs CPL 0, so the kernel runs it on the VMM's thread, owns the VMCB, and rewrites every control field from the validated request on each run. A nested table is an address space kind for revocation."
revisit_if: "The VMM must run on a core the kernel cannot kick, a guest needs AVIC or SEV before those kernel-owned structures are designed, or a guest must span kernel instances."
confidence: "A design note against AMD APM volume 2 chapter 15 and the host's reported SVM features; no code yet. The run path's register facts (what VMRUN does and does not save) are from the manual."
---

# A user-space VMM over AMD SVM

## Decision

A guest is a principal with no capabilities. It can touch only what its nested table maps and what its intercept maps let through. The VMM is an ordinary process with no special authority. VMRUN needs CPL 0, so the kernel runs it for the VMM, on the VMM's own thread. A process could reach the host by choosing VMCB contents, so the kernel owns the VMCB and no process ever maps it.

Objects, all retyped from untyped, `design/untyped-memory/`: a vCPU, holding the VMCB, the guest registers VMRUN does not save and the guest's extended register state, runnable on one core at a time; a nested table, a root and table pages retyped like a process table's; intercept maps, a 12 KB I/O map and an 8 KB MSR map written only by the kernel. Retyping into a vCPU requires a capability to SVM itself, handed to the root at boot, so the root decides who gets this hardware surface. A vCPU capability has rights run and kick; a nested table capability has map and unmap; frame capabilities are the ordinary ones, so a frame can sit in a process table, a device space and a nested table at once. Pass-through of an I/O port needs a port capability covering it; an MSR is passed through only from a fixed kernel allowlist.

A nested table is an address space of the same kind as a process table for revocation, `design/address-spaces-as-objects/`. Revoking a frame removes every entry in all three kinds, then flushes per kind: IPI for a process table, IOTLB invalidate for a device space, a kick of every core running that ASID plus flush-by-ASID on its next VMRUN for a nested table, all producing the token retype requires, `design/flush-without-waiting/`. The guest sees a nested page fault, delivered to the VMM, which is how a pager overcommits guest memory. Hardware writes accessed and dirty bits in nested tables, so an entry's spec allows those bits to change.

Per core, boot reserves the host save area and a host VMCB with the rest of per-CPU state, never retyped. A VMCB and its maps stay resident because kernel objects are not paged; a pager that wants that memory back revokes and destroys the vCPU. A vCPU or its table follows the same rule as a thread on another core: no retype until the core has been kicked out and has acknowledged.

The run path: with the lock held, validate and write the VMCB; release the lock; CLGI; VMSAVE host; VMLOAD guest; set IF; VMRUN; on exit VMSAVE guest, VMLOAD host, clear IF, STGI. The lock is not held in the guest, so a guest cannot stall the kernel. A host interrupt, including the timer, exits the guest; the kernel handles it and returns from run to the VMM thread with reason interrupted, scheduling first if the timer says so. There is no in-guest scheduled state: a thread in a guest is simply running, so no third saved-frame kind exists, `design/cpu-time-as-capability/`, at the cost of one user crossing per host interrupt. A vCPU is a thread under fixed priorities; a spinning guest is timesliced by the forced timer exit.

What the kernel forces on every VMRUN, the property tier 1 proves: nested paging enabled, the nested root being the bound table, a nonzero kernel-chosen ASID, the kernel's intercept maps, the intercepts that keep the host in control (VMRUN, VMLOAD, VMSAVE, STGI, CLGI, SKINIT, INTR, NMI, SMI, INIT, shutdown, MSR and I/O protection), and every AVIC, SEV, VMSA, PML and LBR pointer and enable clear. Control fields are rewritten from the validated request on each run, so nothing the guest or VMM leaves in the VMCB is trusted; guest state the VMM sets needs no further validation, since VMRUN checks consistency and reports an invalid state as an ordinary exit.

An SMP guest's vCPUs all live in the one kernel instance, `design/one-kernel-instance/`.

## Reasoning

This is the purity principle's escape hatch made concrete: the native API stays capability-shaped, and compatibility comes from a guest. Keeping the VMM an ordinary process means the kernel exposes hardware virtualization as capabilities and nothing more, and the theorem's reach for a guest is exactly what its nested table maps, `design/theorem-over-reach/`.

The kernel owning the VMCB, and rewriting control fields on each run, is what keeps a VMM from reaching the host; without the forced intercepts a triple fault would shut down the host and a guest could hold off the host's interrupts.

## Alternatives rejected

- **The VMM maps and fills the VMCB itself.** A process would choose host-reaching control fields.
- **An in-kernel scheduled guest state** with fast re-entry. A third saved-frame kind; available as a later optimisation if the crossing per interrupt is measured to matter.

## What this does not settle

- AVIC backing pages and tables, kernel-owned since the VMCB names them by physical pointer: later.
- A guest spanning kernel instances, one VMM per node with replicated nested tables: plausible, not designed.
