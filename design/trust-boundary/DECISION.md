---
title: "The kernel theorem assumes nothing about user code; the component that divides memory is tier 3 and the claim says so"
date: 2026-11-05
status: active
tags: [security, proof, tiers]
one_line: "The kernel's theorem holds whatever a pager does, so a swapped per-application pager needs no assurance for anyone else's safety. Isolation between two subsystems also depends on the component that divided memory between them, which is tier 3 today, and the security claim states that dependence."
revisit_if: "End-to-end isolation between real subsystems is required as a proven property, which means raising the divider's tier: full coverage, or a small proven divider specified under its own parent's revocation."
confidence: "The human's choice of the cheapest option with the gap explicit. The tier can rise later; raising it is new work."
---

# The trust boundary

## Decision

The kernel theorem assumes nothing about user code. A swapped pager needs no assurance for anyone else's safety, since it only holds what it was given, `design/theorem-over-reach/`. Isolation between two subsystems also depends on the component that divided memory between them, the root process and any shared pager; that component is tier 3 today, and the security claim states the dependence. Hardware and counted glue are trusted.

## Context

The kernel can prove that a process reaches only what it was granted, but who was granted what is decided in user space. The root process is tier 3 and the pager library is tier 3 until a higher tier is chosen, so end-to-end isolation between real subsystems is only as strong as tier 3 code. The options were tier 3 now with the dependence stated, tier 2 with full line and branch coverage for the divider, or a small proven divider from the start.

## Reasoning

A proven divider from the start would put verified user-space work before the capability kernel could be called done, and would require specifying that code under its own parent's revocation, which the new theorem allows at any time. Stating the dependence costs nothing and keeps the claim honest.

## Alternatives rejected

- **Tier 2 or tier 1 divider now.** New work before the kernel is done; available later.
