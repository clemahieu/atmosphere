---
title: "A capability is shared only by derive; a move keeps a node's place, between tables too; there is no copy"
date: 2026-11-10
status: active
tags: [capability, revoke, lifetime]
one_line: "The only way to share a capability is derive, a child one depth deeper with rights and range within its parent's; nodes never change ancestor; a move relocates a node without changing its place, within the caller's table, out of a controlled process's table, which is a claim, or into one, which is a placement; delete is refused while a node has children, mappings or bindings."
revisit_if: "A service must survive the death of the holder that granted to its clients without a longer-lived parent doing the granting, and claim by a supervisor is not enough."
confidence: "The human's choice among three lifetime packages, with a precedent survey of seL4, NOVA, L4Re, Genode, EROS, Zircon and Barrelfish from their documents. The structure it rests on is proven, design/revoke-by-depth-first-list/."
---

# Sharing is derive only

## Decision

Derive is the only way to share: the child's rights and range lie within the parent's and its depth is one greater. Depth is a byte; overflow is an error. There is no copy, because a copy would be a peer the grantor could not revoke. Every holder may revoke what it derived, so revoke needs no right.

Nodes never change ancestor. Move keeps a node's place and depth, for things with one holder such as a device, whose capability derive refuses so that it has exactly one, and for cooperative upgrade: an old service moves its untyped and receive capabilities to its replacement, and every derived child comes along. A move names its source and its destination as table positions, `design/process-holds-capabilities/`: each is a slot of the caller's own table or, through a process capability with the control right, of that process's table, and the node moves in one bounded step. Nothing enumerates a table.

Claim is the move whose source is in a controlled table; it is not an operation of its own. The process may be live or dead, and the capability moved may name a dead process or thread, which a move out of the caller's own table refuses. Death is not a precondition; destroy before claim is a supervisor's discipline, not the kernel's rule. The claimer then holds that process's own node, the parent of everything derived from it, revocation included.

A move whose destination is in a controlled table is a placement of the node itself, as a derive there is a placement of a child, and a dead process's table is refused. It is how a device's one capability reaches a process its holder builds. With both positions in controlled tables, one move takes a slot of a dead service into its replacement.

A derived child goes in a slot of the deriver's own table, or enters another process's table in one of two ways. A grant over an endpoint places it in the receiver's slot. A placement through control places it in a slot of a process the deriver holds a process capability to with the control right: the derive names its destination as a table position, `design/process-holds-capabilities/`, and a dead process's table is refused, since nothing is given to a process that cannot use it. Either way the child is its parent's child wherever it lies, so the deriver can revoke it. Delete is refused while a capability has children, mappings or bindings, which are all child nodes, so a holder revokes first.

Consequences accepted with the package: when a holder dies or is revoked, everything it granted goes too, so a pager or server that restarts takes its clients' memory with it unless a longer-lived parent granted to those clients directly; a pager that holds the untyped a live process's table pages or capability leaves came from can reclaim them, which faults or strips that process, while the roots of its address space and table go only with the process; retype from a held untyped counts beside grant as a way reach grows, `design/theorem-over-reach/`.

Rights: read, write and execute for frames; retype for untyped; send, receive and grant for endpoints; control for threads and processes; none for a device, whose capability is the authority; plus a maximum priority on a core capability and a badge on an endpoint.

A console or power capability names one page past memory, `design/capability-names-a-block/`, so there is no range to narrow: its child names the same object with rights no wider, both carrying none today, and goes with its parent on revoke. The root passes the console to whatever should be heard, or the authority to end the run to a supervisor, and keeps its own and the means to take it back. A device's capability is the exception: it is bound to one space at a time, so derive refuses it and it moves.

The service contract this implies for the runtime: cooperative upgrade by move, crash recovery by claim, and the holder of a dead process's untyped not retyping its leaves before the controller has claimed, a convention when both are one party and a contract when they are not.

## Context

These semantics follow from the depth-first list that makes revoke exact. The question put to the human was whether to accept them as a package, let children survive a holder's death by moving to the holder's parent, or amend named items.

## Reasoning

Live upgrade is wanted. Cooperative upgrade is already move. Claim covers the crash: the supervisor that controls the dead service moves its slots into the replacement, one move per slot, which then has exactly the dead service's authority over its clients. Reparenting orphans to the grandparent does not give that: a replacement holding a fresh derived capability would be the orphans' sibling, unable to revoke them, and the only way to regain control would strip the clients anyway. Reparenting gives survival as an orphan, for grants that never need taking back, and it would hide descendants from the party responsible for them; with claim, survivors exist only when a controller claimed them, slot by slot.

Recorded for honesty: reparenting's structural cost was overstated when first put. An explicit tree with first-child, sibling and back links splices a dead node's children to the grandparent in constant time, with stored depth as an upper bound. The list is kept because the semantics do not need reparenting, not because reparenting is expensive. Proof size is not the criterion; bounded steps per entry and a clean reach statement are.

Why claim does not require death: the kernel decides no kill policy, so a fault with no handler stops only the faulting thread, `design/teardown-driven-by-retype/`, and crash recovery is a supervisor protocol over suspend, readable registers, claim, fault messages and revoke. Requiring death before claim would add only a kernel-enforced order that protects a supervisor from itself, which the theorem does not need, and it would stop a controller that is not the pager from reading a live child's memory for a crash dump.

Why a controller may place: a creator has to give a process it builds its first capabilities, and no rendezvous can, because a receive names an endpoint in the receiver's own table and a new process's table is empty. Control already lets its holder take from the process's table, write its threads' registers and destroy it, so giving to the process grants the controller nothing. What it grants the process, and whoever else controls it, is counted as a grant, `design/theorem-over-reach/`.

Why claim is a move and not an operation: a claim and a move do the same step to the list, and differ only in which table the source slot is in. Once an operation names a slot as a table position, the move already says that, for its destination as well as its source, so a claim operation would be a second number and a second path for one step, and it could not put what it took anywhere but the claimer's own table.

## Alternatives rejected

- **A new process's first capabilities by a grant over an endpoint alone.** A receive names an endpoint the receiver holds, and a new process holds nothing, so only its creator's own table could ever hold capabilities.
- **Copy.** A peer the grantor cannot revoke; a pager that copies cannot revoke.
- **Children survive by moving to the holder's parent.** See above.
- **Claim only from a dead process.** See above.
- **Claim as an operation beside move.** See above.

## What this does not settle

- A reversible process-wide suspend, and a death notification to a controller. Filed as later questions.
