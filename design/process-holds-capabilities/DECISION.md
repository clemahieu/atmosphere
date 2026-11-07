---
title: "A process holds capabilities, in a two-level table that no capability names"
date: 2026-11-07
status: active
tags: [capability, process, thread]
one_line: "Capabilities belong to a process, not a thread; its table is a root of 512 pointers in the process object and leaves of 127 slots retyped on demand; no capability names a table and no table holds a table, so the capability graph has no cycles and lookup is constant time. A process is an order-3 block of its table's root, its record and its address space; a thread holds no slots: it is an order-1 block of a node page for its bindings and a page for its record and XSAVE area."
revisit_if: "Threads in one process need distinct authority, or a process needs more slots than the two levels give, or a table must be passed as a capability, or a supported core's XSAVE area outgrows the 3072 bytes a thread's record page leaves it."
confidence: "A structural choice; the no-cycles property it buys is what rules out the delete-cascade problem Nevill's thesis describes, and the table invariant is proven in kernel/verified/capability/table.rs."
---

# A process holds capabilities

## Decision

A process holds capabilities, not a thread: threads in a process share authority, as they share memory. The table is two levels of fixed size: a root of 512 pointers inside the process object, and leaves retyped on demand from untyped memory. A leaf is an order-1 block, a node page holding the slots' list nodes and a payload page holding what each capability says at the same index. Node 0 of a leaf is its hidden node, `design/teardown-driven-by-retype/`, so a leaf has 127 slots and a table up to 65,024, with constant-time lookup. An index from user space is checked.

No capability names a table and no table holds a table. A slot is the list node, with kind, depth and links, plus a 32-byte payload with rights, order, base and badge.

A thread holds no slots. It is an order-1 block retyped from an untyped held: page 0 is a node page whose nodes are its bindings, to its process, its fault endpoint and its placement, each a counted node under the capability it binds; page 1 holds the thread's record (state, saved frame, pending stop, process) at offset 0 and its XSAVE area at offset 1024, 64-byte aligned, with 3072 bytes to the end of the page. A capability names a thread by its block's base, with the control right, and the capabilities naming it hold its block's references.

Through that control right a holder reads and writes an Inactive thread's saved frame whole; a thread in any other state is refused, since only its core writes a Running thread's frame. A written frame is the one the thread returns to user mode with, so the kernel keeps its selectors user mode's and its flags to those user mode can set itself with popf, and refuses a rip past the lower half, which would fault in the kernel's iretq. A write grants nothing the thread could not do to itself.

A holder of a thread's control capability and a process's binds the thread to the process; both need the control right. The binding is node 0 of the thread's node page, a child of the process capability, holding one of the process block's references, and the thread's record names the process. A thread bound already is refused, so a thread has one process. The binding is a child, so the process capability cannot be deleted while it stands; revoking the capability unlinks the binding, which drops the reference, clears the record's process and leaves the thread Inactive, unless it is Running, which only its core changes, or Dead. Binding moves no capability, and the reach model does not read bindings, so there it is a local step.

A process is an order-3 block retyped from an untyped held. Page 0 is its table's root, so a table is named by its process's base. Page 1 holds the process's record, a dead flag. Pages 2 to 4 are kept for later per-process state. Pages 5 to 7 are its address space's root, record and list of cores, at the offsets an IO space has them, so the space's invariants and the TLB model apply to it unchanged. A process's space has no node pages: a level-4 entry maps no frame, so nothing in the space needs a list node. A capability names a process by its block's base, with the control right, and the capabilities naming it hold its block's references. No space capability names a process's space.

## Context

Before this, endpoints sat in per-thread slots and pages and devices in per-process tables, so authority was split between thread and process. The new table had to be found by every syscall in constant time and had to fit the depth-first list, `design/revoke-by-depth-first-list/`.

## Reasoning

Per-process authority matches the memory model: a thread that can map a frame can already hand it to any sibling, so per-thread slots would be a distinction without isolation.

Because no capability names a table, the capability graph has no cycles and the delete-cascade problem of a table reachable from itself cannot arise. Two fixed levels give constant-time lookup and a bounded cost per entry without a tree walk.

The thread's order comes from its parts. Its record is 208 bytes. Its XSAVE area is what CPUID leaf 0xD, sub-leaf 0, reports in ECX for every state component the core supports: 2440 bytes on the reference host, a Ryzen 9 9950X3D with AVX-512 and PKU, read with `__cpuid_count(0xd, 0, ...)`. Both fit one page with the area at 1024, and the bindings take a node page of their own, so two pages; the block table's small orders are 0, 1 and 3, and order 1 is the smallest that holds them. The node page comes first so that a thread's base is a page the node list holds, as a leaf's and a space's are.

## Alternatives rejected

- **Per-thread capabilities.** No isolation gained, see above.
- **Tables as capabilities**, as in seL4's CNodes. Allows cycles and a delete cascade; more flexible addressing was not needed.

## What this does not settle

- How a holder maps into a process's space through its process capability.
- How a process is destroyed and its block reclaimed.
