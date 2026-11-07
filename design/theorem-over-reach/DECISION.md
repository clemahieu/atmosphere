---
title: "The security theorem is stated per object over a capability's reach, not as a partition"
date: 2026-11-06
status: active
tags: [security, proof, capability, verified]
one_line: "A process can read or write an object only if a capability to it is reachable from its own capabilities; every operation changes objects only by a relation of its kind over that reach; reach grows only by grant or retype. Isolation of disjoint subsystems is a corollary."
revisit_if: "A kernel operation is wanted whose effect cannot be written as a relation over the caller's reach, or a shared object must be reachable without any capability naming it."
confidence: "The statement is the human's choice; the definition and the per-operation shape are in the tree, kernel/verified/capability/reach.rs, and each operation's leaf discharges it as it lands. The composed theorem is not yet proven."
---

# The theorem is per object over reach

## Decision

Direct reach of a process P: the objects its capabilities name, the capabilities descended from them, and the frames its address spaces map, a mapping being a hardware copy. `reach(P)` is the least set containing P and closed under direct reach. A process holding a control capability to a process contributes what that process directly reaches, live or dead, until its slots are revoked. The closure makes control transitive: if S controls P and P controls Q, S reaches what Q directly reaches, since S can claim P's control over Q and repeat.

An operation changes objects only by a relation of its kind, not by general write. A frame in reach is read and written as its rights allow. An endpoint with send delivers at most five words and one derived capability to the matched receiver's frame and wakes it. A reply delivers once to its bound caller's frame. A notification sets bits and wakes a waiter. A revoke unlinks nodes only in the capability's lineage, which may lie in other processes' tables and spaces, and marks dead any object whose last reference it removed. Teardown of a dead object unlinks that object's own slots, mappings and bindings and their runs, which can be in other lineages, and wakes or stops what waited on it. Destroy, through a control capability, marks a thread or process dead. Claim, through a control capability to a process, moves one node from that process's slot to the caller's table, leaving its place in its lineage unchanged. Retype, on a block under a held untyped, types it if free, unlinks its hidden node, or does a slice of its teardown. These change run queues and kernel lists, which no process can read directly.

The theorem: every step by a thread of P changes objects only by these relations over `reach(P)`; any user-mode access reads or writes only frames P's spaces map; and reach grows only by a grant from a holder or a retype from an untyped held. A retype creates something new rather than reaching something existing. Control over a process lets its controller take what the process holds, which reach already counts, so a claim does not grow reach. Two subsystems sharing an object still cannot reach each other's private objects unless one grants; isolation of fully disjoint subsystems follows.

Revocation only shrinks reach, so a parent's revocation needs no exemption. The old isolation proof's assumption, that memory is never revoked under verified user code, is gone with containers: verified user code must be specified knowing an ancestor can revoke mid-operation.

The spec is `kernel/verified/capability/reach.rs`; the view it is stated over is `kernel/verified/capability/view.rs`. Each capability operation's spec ensures `discharges` of its step, written to it rather than retrofitted.

## Context

`design/isolation-claim/` chose spatial isolation, first worded as two subsystems with disjoint capabilities cannot touch each other's memory or endpoints. Under `design/untyped-memory/` nearly every application shares frames with a pager or a driver, so two real subsystems are rarely disjoint and that wording says nothing about them. The commented-out proof in the old tree was that partition form, with a verified third party exempt.

## Reasoning

Reach constrains every syscall's spec from the start and covers the system the plan builds, where sharing is normal. Partition is closer to the old proof and smaller, but holds only for subsystems sharing nothing or with named exemptions.

A first wording of the theorem was found false for IPC, which writes the receiver's frame, and for bookkeeping a process can observe. The per-kind relations are what fixed it: the theorem is not "only reachable objects change" but "objects change only by the relation their kind allows, over reach".

## Alternatives rejected

- **Partition between subsystems** with exemptions for a verified third party. Does not cover shared pagers, drivers or rings.
- **Counting a controlled process's reach only when dead.** Wider in wording than needed and no narrower in fact, since a controller can destroy and then claim at any time; and it would stop a controller that is not the pager from reading a live child's memory for a crash dump.

## What this does not settle

- The proof that composes the per-operation lemmas into the theorem, which lands with the last operation.
- A guest's reach is what its nested table maps, `design/vmm-over-svm/`.
