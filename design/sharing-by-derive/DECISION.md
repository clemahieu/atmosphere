---
title: "A capability is shared only by derive; move and claim keep a node's place; there is no copy"
date: 2026-11-05
status: active
tags: [capability, revoke, lifetime]
one_line: "The only way to share a capability is derive, a child one depth deeper with rights and range within its parent's; nodes never change ancestor; move and claim relocate a node without changing its place; delete is refused while a node has children, mappings or bindings."
revisit_if: "A service must survive the death of the holder that granted to its clients without a longer-lived parent doing the granting, and claim by a supervisor is not enough."
confidence: "The human's choice among three lifetime packages, with a precedent survey of seL4, NOVA, L4Re, Genode, EROS, Zircon and Barrelfish from their documents. The structure it rests on is proven, design/revoke-by-depth-first-list/."
---

# Sharing is derive only

## Decision

Derive is the only way to share: the child's rights and range lie within the parent's and its depth is one greater. Depth is a byte; overflow is an error. There is no copy, because a copy would be a peer the grantor could not revoke. Every holder may revoke what it derived, so revoke needs no right.

Nodes never change ancestor. Move keeps a node's place and depth, for things with one holder such as a device, whose capability derive refuses so that it has exactly one, and for cooperative upgrade: an old service moves its untyped and receive capabilities to its replacement, and every derived child comes along. Claim is that move out of another process's table: a process holding a control capability to a process, live or dead, names one of that process's slots and one of its own, and the node moves in one bounded step. Death is not a precondition; destroy before claim is a supervisor's discipline, not the kernel's rule. The claimer then holds that process's own node, the parent of everything derived from it, revocation included. Nothing enumerates the table.

A grant over an endpoint places a derived child in the receiver's slot. Delete is refused while a capability has children, mappings or bindings, which are all child nodes, so a holder revokes first.

Consequences accepted with the package: when a holder dies or is revoked, everything it granted goes too, so a pager or server that restarts takes its clients' memory with it unless a longer-lived parent granted to those clients directly; a pager that holds the untyped a live process's table pages or capability leaves came from can reclaim them, which faults or strips that process, while the roots of its address space and table go only with the process; retype from a held untyped counts beside grant as a way reach grows, `design/theorem-over-reach/`.

Rights: read, write and execute for frames; retype for untyped; send, receive and grant for endpoints; control for threads and processes; none for a device, whose capability is the authority; plus a maximum priority on a core capability and a badge on an endpoint.

The service contract this implies for the runtime: cooperative upgrade by move, crash recovery by claim, and the holder of a dead process's untyped not retyping its leaves before the controller has claimed, a convention when both are one party and a contract when they are not.

## Context

These semantics follow from the depth-first list that makes revoke exact. The question put to the human was whether to accept them as a package, let children survive a holder's death by moving to the holder's parent, or amend named items.

## Reasoning

Live upgrade is wanted. Cooperative upgrade is already move. Claim covers the crash: the supervisor that controls the dead service moves its slots into the replacement, which then has exactly the dead service's authority over its clients. Reparenting orphans to the grandparent does not give that: a replacement holding a fresh derived capability would be the orphans' sibling, unable to revoke them, and the only way to regain control would strip the clients anyway. Reparenting gives survival as an orphan, for grants that never need taking back, and it would hide descendants from the party responsible for them; with claim, survivors exist only when a controller claimed them, slot by slot.

Recorded for honesty: reparenting's structural cost was overstated when first put. An explicit tree with first-child, sibling and back links splices a dead node's children to the grandparent in constant time, with stored depth as an upper bound. The list is kept because the semantics do not need reparenting, not because reparenting is expensive. Proof size is not the criterion; bounded steps per entry and a clean reach statement are.

Why claim does not require death: the kernel decides no kill policy, so a fault with no handler stops only the faulting thread, `design/teardown-driven-by-retype/`, and crash recovery is a supervisor protocol over suspend, readable registers, claim, fault messages and revoke. Requiring death before claim would add only a kernel-enforced order that protects a supervisor from itself, which the theorem does not need, and it would stop a controller that is not the pager from reading a live child's memory for a crash dump.

## Alternatives rejected

- **Copy.** A peer the grantor cannot revoke; a pager that copies cannot revoke.
- **Children survive by moving to the holder's parent.** See above.
- **Claim only from a dead process.** See above.

## What this does not settle

- A reversible process-wide suspend, and a death notification to a controller. Filed as later questions.
