---
title: "On x86_64 the kernel swaps the GS base at every crossing of ring 3, and a process's GS lasts only while its thread holds the core"
date: 2026-11-15
status: active
tags: [abi, portability, multicore]
one_line: "The core's block is the GS base only while the core runs the kernel: SWAPGS exchanges it with KERNEL_GS_BASE on every entry from ring 3 (syscall, and an interrupt or exception whose saved CS has RPL 3) and on every return there. A process may load GS; its selector and base are not saved with its thread, and a core clears both when it resumes a thread through a selection, so one thread's GS reaches no other."
revisit_if: "A process needs a GS of its own that survives a switch (a runtime that keeps its thread pointer in GS), CR4.FSGSBASE is turned on so ring 3 can write the base with WRGSBASE, or a target's entry can find the core's block without a register ring 3 can set."
confidence: "Arithmetic for the swap: ring 3 can set the GS base by loading a selector (APM 2 §4.5.3), so a base read before SWAPGS is the process's; dom0's GS check in the gate's boot loads GS across a system call and a tick. The clear on switch is a judgement that no native process needs GS."
---

# The GS base, swapped at ring 3

## Decision

On x86_64 the kernel finds the core's block, `Cpu`, through the GS base. That base is the block's address only while the core runs the kernel. While a process runs, the block's address waits in `KERNEL_GS_BASE`, and every entry from ring 3 starts with `SWAPGS`, before any `gs:` access: the syscall entry, and each interrupt and exception trampoline when the CS the processor saved has RPL 3. Every return to ring 3 ends with `SWAPGS`: the syscall's `sysretq`, a trampoline's `iretq` when the frame it returns with names ring 3, whichever ring it was entered from, and the first entry into dom0. The code is `kernel/src/arch/x86_64/this_core.rs` and the entries it names.

A process may load GS. Its selector and base are not part of its thread's saved state, and no operation reads or writes them. A core that resumes a thread through a selection, after a tick, a reschedule IPI or its wait, gives it a null selector and a base of 0 first. A thread that returns from its own system call, or from an interrupt that left it current, keeps what it loaded.

## Context

`syscall` loads no stack and no segment, so the entry finds its stack through a register the kernel set beforehand, and on x86_64 that is the GS base. Ring 3 can change that base without privilege: loading GS with any ring 3 data selector, or with a null one on a processor that clears the base on a null load, sets it (APM 2 §4.5.3). Before this record the kernel wrote the base once at boot and read `gs:` at every entry, so a process that loaded GS chose the kernel's stack and the core number every interrupt read. aarch64 finds the block through `TPIDR_EL1`, which EL0 cannot access, and needs no swap; its thread pointer `TPIDR_EL0`, which EL0 may write, is cleared on a switch the same way, `design/thread-pointer-cleared-on-switch/`.

## Reasoning

`SWAPGS` is the instruction the architecture provides for this: one instruction at each crossing, no memory access before the base is right, and no register a process can reach that holds the kernel's value while the process runs. Testing the saved CS on interrupt entry, rather than swapping always, is required because interrupts also arrive in ring 0, in the core's wait; testing the outgoing frame's CS on exit, rather than remembering the entry's, is required because a selection may return to a thread from an interrupt that came from the wait.

The process's GS is cleared on a switch rather than saved because nothing native uses it: the kernel's ABI names no GS operation, `CR4.FSGSBASE` is clear, and saving it would add the selector and base to every thread's record and to the read and write of a saved frame, `design/syscall-abi-in-registers/`. Leaving it as it was would hand one thread's GS to the next on the same core, a channel between processes the capability model does not grant.

## Alternatives rejected

- **Finding the block from the stack pointer.** Interrupts arrive on per-core stacks the block could be found from, but `syscall` arrives on the process's stack, so the syscall entry would still need a register.
- **Writing the GS base with `wrmsr` at every entry.** The entry must know the core's block to write it, which is the problem.
- **Saving GS with the thread.** Two words more in every thread's record and in its frame's read and write, for a register no native process uses.

## What this does not settle

- FS, which the kernel does not use: a process's FS selector and base also pass from one thread to the next on a core today. Whether a thread pointer is saved state is under `design/syscall-abi-in-registers/`.
- `WRGSBASE` and `WRFSBASE` in ring 3, which `CR4.FSGSBASE` would allow; turning it on revisits this record.
