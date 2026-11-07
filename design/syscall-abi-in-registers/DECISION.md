---
title: "One syscall entry, and IPC carries its message in registers"
date: 2026-11-06
status: active
tags: [abi, ipc]
one_line: "One entry: rax the operation, rdi the capability index, rsi, rdx, r8, r9 and r10 the arguments; rax returns status in its low 16 bits and a badge in the upper 48. A send carries five words, four with a grant; the kernel copies nothing from user memory for IPC, and larger data goes through shared frames."
revisit_if: "A message that does not fit five words is on a hot path and the shared-frame ring is measured as its cost, or a second entry is needed for a different privilege transition."
confidence: "A packing judgement; the preserved-register set is the one the existing syscall convention keeps."
---

# The syscall ABI, and IPC in registers

## Decision

One entry. `rax` holds the operation, `rdi` the capability index, and `rsi`, `rdx`, `r8`, `r9` and `r10` arguments. On return `rax` holds status in its low 16 bits, including `again` and `busy`, and on a receive the badge in its upper 48; those five and `rdi` hold results. `rbx`, `rbp`, `r12` to `r15`, `rsp`, `rip` and flags are preserved and `rcx` and `r11` clobbered, the convention the kernel already keeps. Every name a process passes resolves within the caller's kernel instance, `design/one-kernel-instance/`.

A send carries five message words in `rsi`, `rdx`, `r8`, `r9` and `r10`; with a grant, `r10` names the capability, leaving four. A receive names the reply capability in `rsi` and a destination slot in `rdx`, and returns the words in `rdi`, `rsi`, `rdx`, `r8` and `r9`, with a status flag if a capability arrived. A call also receives a reply, so it names a destination slot in `rsi` and carries four words, or three with a grant. `reply_recv` is one operation, since it is a server's hot path: `rdi` names the endpoint, `rsi` the reply capability and `rdx` the destination slot, with three reply words in `r8`, `r9` and `r10`.

The kernel copies nothing from user memory for IPC. Larger data goes through shared frames. The thread's saved set is the preserved registers plus these six plus `rax`, so a blocked thread's partial frame copy is well defined. Debug print is an operation on a console capability that takes words.

## Reasoning

Copying nothing from user memory keeps every IPC operation a bounded step with no page walk on the message, `design/one-lock-bounded-steps/`, and keeps the reach theorem's IPC relation to a fixed delivery into the receiver's frame, `design/theorem-over-reach/`. A first packing did not add up for a grant or a receive, which is why the slot and reply positions are fixed here rather than left to a leaf.

## Alternatives rejected

- **A message buffer in user memory.** A copy the kernel must walk and bound, and a relation the theorem must widen.
- **Separate reply and receive operations.** Two entries on every server round trip.
