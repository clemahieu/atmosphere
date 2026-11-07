---
title: "Revoke walks one depth-first list, so a lineage is a run and needs no scan, mark or cursor"
date: 2026-11-06
status: active
tags: [capability, revoke, verified]
one_line: "All capabilities, mappings and bindings derived from the boot root are one doubly linked list in depth-first order, a child straight after its parent; a node's descendants are the run after it with greater depth, and revoke unlinks leaves of that run a bounded number per kernel entry."
revisit_if: "A node needs more than one parent, or a lineage must be reparented, neither of which the list can express; or the 255-link walk to a leaf is measured as the bound that sets the lock hold time."
confidence: "Proven in the tree, kernel/verified/capability/list.rs and revoke.rs: derive and unlink in constant time, depth-first order kept, a node is in a run exactly when the run's head is its ancestor, a revoke step removes one such node and nothing outside the run, with a falling measure."
---

# Revoke walks a depth-first list

## Decision

All capabilities, mappings and bindings derived from one root are one doubly linked list in depth-first order: a child goes straight after its parent. A node's descendants are exactly the run after it with greater depth, so revoke needs no scan, mark or cursor. This is seL4's published structure, as Nevill's thesis describes it; no seL4 code was read.

A mapping is a node too, a leaf child of the capability used to make it, so revoking a capability reaches the mappings made through it in anyone's address space. A binding, anything that holds a reference to an object without being a capability or a mapping, is likewise a leaf child of the capability used to make it, stored in the object doing the holding: a thread's process, fault endpoint and placement on a core; a vector's or timer's notification; a device's IO space; a vCPU's nested table.

`Revoke(c)` repeatedly walks down from the node after c while the next node is deeper, at most 255 links since depth is a byte and each link adds one, and unlinks that leaf. It does a fixed number of these per kernel entry, returns `again`, and returns done when the node after c is not deeper. Only leaves are unlinked, so no node loses its place. Delete is the same unlink with no children required. An unlink has an effect by node kind: a mapping clears its entry and records staleness, a hidden node detaches its block, a binding is undone by a hook per binding kind. Each arm drops one reference, changes no other node's liveness and preserves the kernel invariant, which is what lets a revoke's exact lineage be proven before every arm exists.

Semantics: revoke removes exactly c's lineage. Two children of one parent do not touch each other. A child can derive while its parent revokes, but only inside the run being removed; a fair queue lock and a per-entry budget above the core count make the revoker outrun any number of deriving threads, since each core gets one entry per turn. That is reasoned, not proven, since the theorem is about safety rather than liveness.

## Context

The first design hypothesised that per-page metadata and flat permissions could replace a derivation tree with a scan plus linked copies, which looked cheaper than seL4's tree. A page-list prototype with depth and containment was built and reviewed.

## Reasoning

The page-list prototype's invariant was broken by derive from a shallow peer, and by copy, move or map of a deep capability on the cursor page, so authority escaped revoke; it also deleted capabilities outside the revoker's lineage. Marks could stall a parent's revoke and leak. The hypothesis failed.

The depth-first list gives exact lineage with constant-time derive and unlink and no global state. Its prototype verified at 21 items with 0 errors and no assume, admit or external_body in about 2 seconds, and the landed list proves the same claims with nodes in pages and adds move. Spelled out, the invariants exhausted Verus's rlimit, so membership, distinctness, the link structure and the parent-child order are kept opaque and reached through one-position lemmas; later leaves follow that.

## Alternatives rejected

- **Scan of per-page metadata plus linked copies.** Authority escaped it, see above.
- **An explicit tree with parent links.** Not needed by the semantics in `design/sharing-by-derive/`, which never reparent.

## What this does not settle

- The per-entry budget's value, which the lock hold-time measurement sets, `design/one-lock-bounded-steps/`.
