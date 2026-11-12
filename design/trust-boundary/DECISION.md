---
title: "The kernel theorem assumes nothing about user code; the component that divides the machine is tier 1, and the claim depends on it until its first statement verifies"
date: 2026-11-10
status: active
tags: [security, proof, tiers]
one_line: "The kernel's theorem holds whatever a pager does, so a swapped per-application pager needs no assurance for anyone else's safety. Isolation between two subsystems also depends on the component that divided the machine between them; that component is tier 1 by design/divider-proven-by-invariant/, and until its stage-one statement verifies the security claim states the dependence on unproven code."
revisit_if: "The divider's stage-one statement verifies, when the claim's dependence becomes the proven statement and this record says so; or the divider's tier is lowered, which is the human's decision."
confidence: "The divider's tier is the human's choice. That the kernel theorem needs nothing of user code is the form of design/theorem-over-reach/."
---

# The trust boundary

## Decision

The kernel theorem assumes nothing about user code. A swapped pager needs no assurance for anyone else's safety, since it only holds what it was given, `design/theorem-over-reach/`.

Isolation between two subsystems also depends on the component that divided the machine between them. That component, the divider, is tier 1: `design/divider-proven-by-invariant/` says what it proves and in what order. A server shared by several subsystems, such as a pager, is not part of the divider; it is a tenant bounded by its rows, and whether it leaks between its clients is its own correctness at its own tier.

Until the divider's stage-one statement verifies, the root process that divides the machine is unproven code, and the security claim states that isolation between subsystems depends on it. Once it verifies, the claim is the composed statement: each tenant reaches only its rows and the declared overlap in every state after the divider's last step, over the trusted base that record names. The claims `tools/external-body-list` counts are trusted: hardware, kernel and language claims, and the `gap` and `unproven` debt, `design/who-vouches-for-an-unproven-claim/`.

## Context

The kernel can prove that a process reaches only what it was granted, but who was granted what is decided in user space. A native subsystem is meant to stand in for a virtual machine as an isolation boundary, which makes isolation between real subsystems a property to prove, not a dependence to state. The options were tier 3 with the dependence stated, tier 2 with full line and branch coverage for the divider, or a proven divider.

## Reasoning

Proving the divider does not mean specifying it under its own parent's revocation, the cost that would make it large: the root's capabilities hang from a node nobody holds, so nothing revokes them, `design/root-process-at-boot/`, and the root is the divider stage one proves. Stating the dependence while the proof is built keeps the claim honest in the meantime.

## Alternatives rejected

- **The divider at tier 3, with the dependence stated for good.** The claim would stop at the kernel, and a subsystem boundary would be only as strong as the root process's tests.
- **The divider at tier 2.** Full coverage of the divider says its tests reached every branch, not that every layout it accepts isolates; the claim a subsystem boundary needs is the second.
- **A pager or shared server inside the divider's proof.** It would put its whole service logic under the divider's statement; as a tenant it is bounded by the kernel theorem and its rows without it.
