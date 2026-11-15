---
title: "An assembly leaf's register convention is cited to the document that fixes it and held by a dom0 boot check on each target, not vouched for"
date: 2026-11-15
status: active
tags: [abi, arch, trusted-base]
one_line: "An assembly leaf's register convention, which registers carry each value and which survive it, comes from a published ABI or a design record's table, is cited in the leaf's comments, and is held by a dom0 boot check on each target that puts a distinct value in every register the convention keeps, runs the leaf and compares. It takes no voucher and no list entry. A leaf no verified code calls lands with no assumed specification."
revisit_if: "Verus or another tool the project runs comes to check inline assembly against a register convention, which would make the convention a proof rather than a test; or a leaf's convention depends on state a dom0 check cannot set and observe, such as a register only a higher privilege level reads."
confidence: "A judgement: a check that sets and compares every kept register observes the whole of what the convention says survives, but only on the paths it drives, only on the two targets the gate boots, and not that a clobbered register leaks nothing."
---

# The register convention of an assembly leaf

## Decision

An assembly leaf is a function whose body is inline or global assembly that moves values between registers by a convention: the system-call stub in `asys/src/arch/`, the kernel's trap entry and exit stubs under `kernel/src/arch/<target>/`, a user-space context switch. Its convention says which registers carry each value in and out, which the leaf keeps and which it destroys.

**The document.** A published document fixes the convention: the target's C calling convention (the System V x86-64 psABI, Arm's AAPCS64) or a table in a design record, as `design/syscall-abi-in-registers/` is for the system call. The leaf's comments cite the document and the section or table that names the registers.

**The check.** What holds the code to the document is a dom0 boot check on each target: it puts a distinct value in every register the convention keeps, runs the leaf, compares each register afterwards and prints a line `tools/check-boot-log.py` requires on that target. A leaf entered by more than one path is checked on each. The change that lands a check records, once, that leaving one register out of the leaf makes it fail; that is not a gate step. On aarch64 the boot is the board's, so when the gate's aarch64 step passes on the board being unreachable, the check has not run. The thread pointer and the segment registers user mode writes are held this way already, by the checks `design/thread-pointer-cleared-on-switch/` and `design/gs-base-swapped-at-ring-3/` describe. The system call's kept set is held only in part; Context says which registers no check holds.

**No voucher.** The convention takes no voucher and no `tools/external-body-list` entry, and the leaf is no `tools/boundary-list` site of its own. Specifications above a leaf speak of a frame's named fields and the positions the table maps to them, as acall's `system_call` specification does through `carries`; that the leaf moved each field to or from the hardware register the convention names is what the check holds. Where unverified code hands such a frame to the proof, that site is counted as any site is, `design/boundary-into-verified-code-counted/`.

What a call to the leaf means to verified code is written as `design/who-vouches-for-an-unproven-claim/` says, in the verified crate that calls it. A leaf no verified code calls lands with no assumed specification. The compiler and assembler are trusted as that record says.

## Context

`design/who-vouches-for-an-unproven-claim/` covers what a verified crate takes on trust, and said of the system call that the boot checks held its register convention. They hold part of it. The result words reaching dom0 show the outputs' registers, and `dom0_child_invoke` keeps its arguments in r12 to r14 on x86_64 and x19 to x21 on aarch64 across invocations, so a kernel that lost one of those would fault, be refused or count wrongly, and dom0 would not print its line. Across a system call no check holds rbx, rbp, r15 or rflags on x86_64, or x18, x22 to x29 or the condition flags on aarch64. A stub that clobbered one of the general registers would fail only where compiled code held a live value there, intermittently and far from the stub. The flags would fail nowhere: the asys stubs do not declare `preserves_flags`, so compiled code keeps no live flag across a call, and the table's promise about them is observed by nothing.

A user-space context switch, for tasks that share one kernel thread, raised the same question with nothing to point at. Its convention is the C calling convention's callee-saved set: an ABI, not a hardware manual, a kernel proof or a passage of rust-src, so none of the voucher classes fits it.

## Reasoning

A register convention is mechanical and observable at the instruction level. A check that sets every kept register, runs the leaf and compares observes what the convention says survives, on the paths it drives. A citation can only say what the document requires, not that the code does it, which is why a hardware guarantee's body is held to the instruction or register access its manual describes.

The check is a dom0 boot check, not a host test, because the host is x86_64: only the gate's boots reach aarch64, and the kernel's stubs run only in a boot. Recording that the check fails without one register keeps a comparison that compares nothing from passing.

Leaving a leaf no verified code calls without a specification keeps every assumed specification one that some proof reads.

## Alternatives rejected

- **A voucher class for an ABI, listed in `tools/hardware-documents` beside the manuals.** It would vouch for the document and not for the code, and it would apply only inside a crate marked verified, which a leaf usually is not.
- **An `external_body` in a verified crate, counted as debt.** It would count as unproven something a test can observe completely.
- **A host test.** It reaches neither aarch64 nor the kernel's stubs.
- **Relying on compiled code to show a clobber.** It shows one only where the compiler happened to keep a live value in that register at that moment, and never for the flags.

## What this does not settle

- The interrupt path's convention, that an interrupted thread resumes with every register it held. No record states it as a table and the kernel's interrupt stubs cite no document; `dom0_child_count`'s counter surviving ticks observes one register of it.
- That the registers a leaf clobbers carry no kernel value when it returns to user mode, which `design/arch-module/` item 5 requires of the kernel's stubs. A comparison of the kept registers does not observe it.
- How a verified caller would specify a context switch: other tasks run between the switch out and the switch back, so its specification needs a relation over what they may do, as a system call's relies on `CapKernel::rely`.
- Floating-point and vector registers. Both targets build without floating-point code today (`+soft-float` on x86_64, `-neon` on aarch64, in the target files), so no leaf saves one; turning it on adds the ones the conventions keep, such as d8 to d15 under AAPCS64, to each leaf and its check.
- Registers below user mode, such as what the kernel's stubs leave in the system registers, which a dom0 check cannot set and observe.
