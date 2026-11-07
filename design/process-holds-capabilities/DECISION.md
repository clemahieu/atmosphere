---
title: "A process holds capabilities, in a two-level table that no capability names"
date: 2026-11-06
status: active
tags: [capability, process]
one_line: "Capabilities belong to a process, not a thread; its table is a root of 512 pointers in the process object and leaves of 127 slots retyped on demand; no capability names a table and no table holds a table, so the capability graph has no cycles and lookup is constant time."
revisit_if: "Threads in one process need distinct authority, or a process needs more slots than the two levels give, or a table must be passed as a capability."
confidence: "A structural choice; the no-cycles property it buys is what rules out the delete-cascade problem Nevill's thesis describes, and the table invariant is proven in kernel/verified/capability/table.rs."
---

# A process holds capabilities

## Decision

A process holds capabilities, not a thread: threads in a process share authority, as they share memory. The table is two levels of fixed size: a root of 512 pointers inside the process object, and leaves retyped on demand from untyped memory. A leaf is an order-1 block, a node page holding the slots' list nodes and a payload page holding what each capability says at the same index. Node 0 of a leaf is its hidden node, `design/teardown-driven-by-retype/`, so a leaf has 127 slots and a table up to 65,024, with constant-time lookup. An index from user space is checked.

No capability names a table and no table holds a table. A slot is the list node, with kind, depth and links, plus a 32-byte payload with rights, order, base and badge.

## Context

Before this, endpoints sat in per-thread slots and pages and devices in per-process tables, so authority was split between thread and process. The new table had to be found by every syscall in constant time and had to fit the depth-first list, `design/revoke-by-depth-first-list/`.

## Reasoning

Per-process authority matches the memory model: a thread that can map a frame can already hand it to any sibling, so per-thread slots would be a distinction without isolation.

Because no capability names a table, the capability graph has no cycles and the delete-cascade problem of a table reachable from itself cannot arise. Two fixed levels give constant-time lookup and a bounded cost per entry without a tree walk.

## Alternatives rejected

- **Per-thread capabilities.** No isolation gained, see above.
- **Tables as capabilities**, as in seL4's CNodes. Allows cycles and a delete cascade; more flexible addressing was not needed.

## What this does not settle

- The process object's own layout and the thread's, which the thread leaf sets.
