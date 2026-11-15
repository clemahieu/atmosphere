---
title: "On aarch64 a process's TPIDR_EL0 lasts only while its thread holds the core"
date: 2026-11-15
status: active
tags: [abi, portability, multicore]
one_line: "TPIDR_EL0, the thread pointer EL0 reads and writes, is not saved with a thread. A core that enters a thread through a selection, after a tick, a reschedule IPI or its wait, and the first entry into dom0, write it 0 first, so a value one thread writes reaches no other; a thread that returns from its own system call, or from an interrupt that left it current, keeps what it wrote."
revisit_if: "A process needs a thread pointer that survives a switch (a runtime that keeps thread-local storage in TPIDR_EL0, as the AArch64 ELF TLS convention does), or a core the project runs implements FEAT_SME, whose TPIDR2_EL0 EL0 can also write."
confidence: "dom0's thread pointer check in the gate's aarch64 boot writes TPIDR_EL0 and finds 0 in another process's thread resumed on the same core. Clearing rather than saving is a judgement that no native process needs a thread pointer of its own yet."
---

# The thread pointer, cleared on a switch

## Decision

`TPIDR_EL0` is the register EL0 may read and write for its own thread pointer; the processor makes no use of it (Arm ARM D24.2.203). It is not part of a thread's saved state, and no operation reads or writes it. Every entry into a thread that the kernel makes itself, rather than returning from an exception the thread took, writes it 0 first: `exception::enter` in `kernel/src/arch/aarch64/exception.rs`, through which a core enters the thread a selection left current, after a tick, a reschedule IPI or its wait, and the first entry into dom0. A thread that returns from its own system call, or from an interrupt that left it current, returns through the vector's own exit and keeps what it wrote.

`TPIDRRO_EL0`, which EL0 can read and not write, carries nothing between threads either: the vector that borrows it clears it before any exit, in the same file.

## Context

A register a thread can write and the next thread on the core can read is a channel between processes, which the capability model does not grant. A kernel that neither saves `TPIDR_EL0` nor writes it hands what one thread wrote to the next thread the core resumes, whatever its process. x86_64 has the same question for its data segments and the FS and GS bases; for GS, `design/gs-base-swapped-at-ring-3/` answers it the same way.

## Reasoning

Cleared, because nothing native uses it: no native runtime keeps thread-local storage, dom0 and its children are single images with no TLS, and the ABI names no operation on a thread pointer (`design/syscall-abi-in-registers/`). Saving it would add a word to every thread's record, to the frame the vector saves and restores, and to the verified frame the read and write of a saved frame carry, for a register no process reads back. Writing it at the kernel's own entries and not at every exit costs one instruction at a switch and nothing on a system call's return.

## Alternatives rejected

- **Saving it with the thread.** The AArch64 convention for thread-local storage keeps the thread pointer here, so a ported runtime would want it saved; that is the revisit condition, and until then it is a word in every frame for no reader.
- **Leaving it as it was.** A channel between processes.
- **Writing it at every return to EL0.** It would also take a thread's own value from it across its own system calls, which no channel needs, at an instruction on every return.

## What this does not settle

- A thread pointer as saved state, for a runtime that wants thread-local storage: under `design/syscall-abi-in-registers/`, for both targets at once.
- `TPIDR2_EL0`, which exists only with FEAT_SME; no core the project runs implements it, and one that does revisits this record.
