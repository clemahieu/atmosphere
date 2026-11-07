---
title: "The kernel's security claim is spatial isolation; noninterference and timing are later refinements"
date: 2026-11-05
status: active
tags: [security, proof]
one_line: "The kernel proves spatial isolation: a process affects only what its capabilities reach and gains authority only by grant or retype. It does not claim noninterference or freedom from timing channels, and the claim says so."
revisit_if: "A workload needs distrusting programs that cannot observe each other through status codes or timing, which is when noninterference or multiple kernel instances become required rather than later."
confidence: "A scoping choice by the human. Noninterference is the claim the Atmosphere paper proved with unwinding conditions, so it is known to be reachable; timing needs hardware modelling the project does not have."
---

# The security claim is spatial isolation

## Decision

The kernel's theorem is spatial isolation, stated over capabilities: a process affects only what its capabilities reach, and reach grows only by a grant from a holder or a retype from untyped memory it holds. The form of that statement is `design/theorem-over-reach/`.

The claim is spatial. A process can observe other processes' activity through status codes such as `again`, through timing, and through a refused retype. That is allowed, and the claim says so. Noninterference and timing channels are refinements for later; a design choice that would needlessly rule them out is a question for the human.

## Context

The plan required no security theorem. An isolation proof existed, stated over containers and commented out, so nothing checked it, and the capability work's acceptance did not mention isolation. The options each added to the one before: A, authority only; B, spatial isolation; C, noninterference, one subsystem's syscalls cannot change what another observes; D, timing channels as well.

## Reasoning

B restates the memory and endpoint isolation the kernel already claimed, over capabilities rather than containers, which is what the move to `design/untyped-memory/` needs and no more.

C is the claim in the Atmosphere paper, proven there by unwinding conditions. The kernel allocating nothing after boot helps, since there is no shared allocator, but revocation and shared run queues need care, and revocation is why the statement must let a parent act on its child. Deferred rather than rejected.

D is out of scope: it includes the shared lock and the caches, and reaching it needs several kernel instances, `design/multicore-kernel-shape/`, and hardware modelling the project does not have. Temporal isolation inside a core would need scheduling contexts, deferred by `design/cpu-time-as-capability/`.

## What this does not settle

- The theorem's form and what reach means: `design/theorem-over-reach/`.
- Whether the component that divides memory between subsystems is itself proven: `design/trust-boundary/`.
