---
title: "The divider is proven: it establishes an invariant over a checked table of grants, static first, then dynamic on the same invariant"
date: 2026-11-10
status: active
tags: [security, proof, tiers, capability]
one_line: "The rules that divide the machine between tenants are a table of grants with declared overlap, checked by a decidable layout_ok. A Verus-verified user crate establishes an invariant over the kernel's state and that table, with a state per block; with the kernel theorem it bounds each tenant from above by its rows over reach and from below by a capability for each row, and a witness shows it finishes for every layout that fits. Stage one divides at boot and ends dead while still holding; stage two serves create and destroy, then grow and shrink, then forced reclaim and core moves, each handler keeping the invariant."
revisit_if: "The caller's-view contracts cannot be proven from the kernel's operation specifications at a cost the project will pay, or a handler stage two needs cannot be written to keep one invariant, which is when the dynamic stage is reconsidered and the statement stays the static one."
confidence: "The human's choice among static only, static then dynamic, and dynamic from the start, after a survey of published initialiser and policy proofs (capDL, Boyton's verified initialisation, seL4's integrity and information-flow proofs, take-grant, EROS confinement) and of hypervisors' allocation. The sizes the choice weighed are reasoned from structure, not measured; that the static case can be carried to running code is the published result, and the dynamic case is new ground."
---

# The divider is proven

## Decision

The component that divides the machine between tenants is tier 1. Its rules are a table of grants: rows of (tenant, kind, base, order, rights). Two rows of different tenants whose blocks intersect are declared overlap, each with its rights: a frame one tenant writes and another reads, an endpoint one sends on and another receives on, a server that appears in several tenants' rows. `layout_ok` is a decidable check on the table, a spec function with an executable check proven to return exactly it: every block aligned to its order and inside what the divider holds; rows of different tenants intersecting only where both are marked shared; an endpoint two tenants hold with the grant right declared, which counts the two as one for what they may come to reach; a device in at most one row.

The divider is a Verus-verified user crate that establishes an invariant I over the kernel's abstract state and its own table: the layout, plus a state per block, free, granted to a tenant, or being revoked from a tenant. A grant is made only from free, and the middle state is real because revoke can return again.

The statement bounds each tenant from both sides, as `CLAUDE.md`'s tiers ask of every tier-1 component. From above: in every state after the divider establishes I, each tenant reaches only its rows and the declared overlap, which follows from I and the kernel theorem, `design/theorem-over-reach/`. From below: when I is established, each tenant holds a capability for each of its rows. A witness verifies that for every layout `layout_ok` accepts and that fits what boot gave, the divider reaches its last step, beside a throwaway claim of more that does not verify. The statement is a bound, not an exact description of every object the divider made.

It comes in two stages on the one invariant.

- Stage one: the root process divides what boot gave it, `design/root-process-at-boot/`, by a layout built into its image, establishes I, and destroys itself. It ends dead while still holding: sharing is derive only and the divider holds the parent of every tenant capability, `design/sharing-by-derive/`, so it cannot let go without taking the tenants' capabilities with it. A dead process performs no operation, `design/teardown-driven-by-retype/`.
- Stage two turns the divider into a server whose every handler keeps I, in this order: create and destroy tenants from layouts checked in advance; cooperative grow and shrink by quota; forced reclaim of memory and moving a core between tenants. A block or a core reaches a new tenant only after its revoke finished and, for a core, its flush.

Policy stays out of the proof. An unproven placement process decides which tenant to create, what quota to give and what to take back, and asks; the proven divider enforces I and refuses what would break it.

The proof lives in user space. Each operation the divider uses has a caller's-view contract, requires and ensures over the caller's own slots, proven in `kernel/verified` from the operation's specification and carried into the divider's crate by `tools/verify.py`'s import of marked crates. A syscall wrapper is the one `external_body` the divider's crates hold, counted as glue, and it lands only with its contract's proof. For the root the contracts need no assumption about other processes: its capabilities hang from the synthetic root that nobody holds, so no other step changes its slots unless it gave control of itself away.

## Context

The kernel theorem bounds each process by its reach. That two tenants are isolated also needs the component that divided the machine between them to have handed out sets that overlap only where its rules say, and not to be a path between them afterwards. `design/trust-boundary/` left that component at tier 3 and stated the dependence; this record raises it.

## Reasoning

A table of grants, not a partition, because the theorem is over reach and real tenants share: a pager or driver serving several tenants is a tenant like any other, bounded by its rows, and whether it leaks between its clients is its own correctness. This follows capDL's description of a system as which objects exist and which capabilities each holds, more than a separation kernel's partitions joined by wires. The grant rule on shared endpoints is needed because a delivery with a granted capability is how reach grows; seL4's integrity proof imposes the same rule by putting both ends of a grant edge in one label.

An upper bound, not an exact description, because a bound is all isolation needs, it is what a divider under a parent could keep since revocation only shrinks reach, and it leaves out what an exact description must track and isolation does not use. The lower bound and the witness keep the bound from being empty: a divider that granted nothing would satisfy the upper bound alone.

Static first because the static case is the only one the literature has carried from a model to running code, and it builds and tests the bridge from the kernel's specifications to a user crate on the simplest client: one thread, no ancestor, no requests. Stating it as "the divider establishes I" costs almost nothing over a bare static statement, since stage one leaves the block state constant, and lets stage two extend the proof rather than restate it. The dynamic case is published only as a model or resting on trusted code, so it follows a working static proof.

Stage two's order puts the handlers that only add and remove whole tenants before those that move part of one, and the one that takes from an unwilling tenant last, since it is the one whose intermediate states I must cover most.

The kernel already makes reclaim clean, so the divider does not scrub: revoke unlinks exactly a capability's lineage wherever its nodes sit, `design/revoke-by-depth-first-list/`; memory is zeroed before a capability names it, `design/teardown-driven-by-retype/`; a retype or regrant waits for every core's and IOMMU's flush acknowledgement, `design/flush-without-waiting/`.

## Alternatives rejected

- **Static only.** Proves the same first statement, and then nothing about change after boot: the machine's division is fixed until reboot, since the dead divider holds every parent. Hypervisors' users create, destroy, resize and move tenants, and stage two is what lets the native boundary stand in for that.
- **Dynamic from the start.** Proves at the end what the two stages prove, with no earlier statement, and needs both blocking contracts and the revoke path before anything is claimed, with no smaller system to test the bridge on first.
- **An unverified divider audited by a proven checker.** The check would be of what the checker can read, and the ABI does not show reach. Inspect returns a slot's kind, base, order and rights, of the caller's table or of a process it controls, `design/process-holds-capabilities/`; nothing returns a node's place in its lineage, which frame a space entry maps, or which thread waits on what. Reach is defined over exactly those, `design/theorem-over-reach/`: a capability whose descendant sits in another tenant's table, a frame mapped into a second tenant's space and a thread listed on another tenant's endpoint are all invisible to an audit of slots. Adding operations that read them would widen the ABI to show kernel structure to user space. And an audit is of one state: a divider that keeps running holds control over every tenant and the parent of everything they hold, so its next step is unbounded by any earlier audit, and a checker that gated every step would be the proven divider.
- **An exact description of every object as the statement.** Boyton's verified initialisation proves each object is exactly as described. Isolation does not use that, a divider under a parent could not keep it, and it would make every handler track objects the bound ignores.

## What this does not settle

- Timing and the kernel's shared lock, `design/isolation-claim/`.
- Transient execution, caches and predictor state, beyond the flush a core move requires.
- A device's own registers and buffers when it moves between tenants; the kernel undoes its IO space binding and waits for the IOMMU's invalidation, and nothing proven resets the device.
- What tenants do once they run, including whether a shared server leaks between its clients.
- Termination of requests: the stage-two statement is that a handler given what it requires completes, not that every request is served.
- That a layout says what the operator meant: a layout that declares the wrong overlap is enforced faithfully.
- The trusted base: counted glue, the loader, firmware, hardware and the IOMMU, Verus, Z3 and rustc.
