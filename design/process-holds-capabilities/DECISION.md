---
title: "A process holds capabilities, in a two-level table that no capability names"
date: 2026-11-10
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

A thread holds no slots. It is an order-1 block retyped from an untyped held: page 0 is a node page whose nodes are its bindings, to its process, its fault endpoint and its placement, each a counted node under the capability it binds; page 1 holds the thread's record (state, saved frame, pending stop, process, placement) at offset 0 and its XSAVE area at offset 1024, 64-byte aligned, with 3072 bytes to the end of the page. A capability names a thread by its block's base, with the control right, and the capabilities naming it hold its block's references.

Through that control right a holder reads and writes an Inactive thread's saved frame whole; a thread in any other state is refused, since only its core writes a Running thread's frame. A written frame is the one the thread returns to user mode with, so the kernel keeps its selectors user mode's and its flags to those user mode can set itself with popf, and refuses a rip past the lower half, which would fault in the kernel's iretq. A write grants nothing the thread could not do to itself.

A thread is bound to its process when it is retyped: the retype names, with the untyped and the destination slot, a process capability the caller holds with the control right, and the binding is node 0 of the thread's node page, a child of that capability, holding one of the process block's references, with the thread's record naming the process. Nothing binds a thread afterwards, so a thread has one process for its life. The binding is a child, so the process capability cannot be deleted while it stands; revoking the capability unlinks the binding, which drops the reference, clears the record's process and leaves the thread inert: Inactive, unless it is Dead, or Running, which its core stops at its next kernel entry. Reach reads this binding, a control capability over a thread reaching the thread's process, and the retype grows nobody's reach because the caller is the new capability's only holder and controls the process already. Why the binding is made at retype and never set is `design/thread-bound-at-retype/`.

A process is an order-3 block retyped from an untyped held. Page 0 is its table's root, so a table is named by its process's base. Page 1 holds the process's record, a dead flag. Pages 2 to 4 are kept for later per-process state. Pages 5 to 7 are its address space's root, record and list of cores, at the offsets a device space has them, so the space's invariants and the TLB model apply to it unchanged. A process's space has no node pages: a level-4 entry maps no frame, so nothing in the space needs a list node. A capability names a process by its block's base, with the control right, and the capabilities naming it hold its block's references. No space capability names a process's space: a holder links tables into it and maps frames into it through a process capability with the control right, which names the space by the same base, whether the process is the holder's own or another's. A device space is changed through its space capability with the write right. Control already lets a holder claim from the process's table and destroy it, so changing its space grants nothing a separate right would withhold.

Through that control right a holder destroys the process: one bounded step sets its record dead and sends an IPI to each core on its space's list of cores, so each such core, at its next kernel entry, finds its current thread's process dead and moves the thread off; only a thread's own core moves it out of Running, `design/one-lock-bounded-steps/`. Its threads, table, space, references and capabilities stay as they were, so a holder can still claim from the dead process's table, and destroy changes nothing reach reads.

Through that control right a holder deletes, revokes and inspects a slot of the process's table, moves a capability out of a slot of it or into one, and retypes a leaf into a root entry of it: the process capability names its process's table as it names its space. An operation names the slot or the root entry it acts on as a table position: an index into the caller's own table, or, through a process capability with the control right held in the caller's own table, into that process's table. It is one hop, since the capability a position goes through is always in the caller's own table, so lookup stays constant time and still no capability names a table. A thread's capability names no table, and neither does a process capability without control. An operation that reads or empties a slot does not read whether the process is dead, so a supervisor reads a dead service's slots and clears them without spending slots of its own. A derive names its destination as a position too, and a move its source and its destination, which is how a creator gives a process it builds its capabilities, `design/sharing-by-derive/`. An operation that adds to a table, a derive, a move into it or a leaf's retype, reads whether the process is dead and refuses one that is. The lookup is `kernel/verified/capability/position.rs`, and the word a position travels in is `design/syscall-abi-in-registers/`.

A process's table starts with no leaf, so the leaf its creator retypes into it is what gives it slots. The untyped the leaf is retyped under is in the creator's own table, as the capability any operation exercises is, and the leaf's hidden node is that untyped's child, so revoking the untyped takes the leaf back whichever table it went into. A leaf is no capability, so it adds to nobody's reach.

That a creator can build such a process is proven. `kernel/verified/capability/witness.rs` starts from the state boot leaves and, as the root, retypes a leaf into its own table, a process and a thread bound to it into that leaf, a leaf into the new process's table through the process capability, and derives an untyped into that leaf the same way; each step is proven to succeed, and at the end the new process holds the root's untyped's child and has the thread bound to it. Only Verus compiles that module, so no image contains it.

## Context

Before this, endpoints sat in per-thread slots and pages and devices in per-process tables, so authority was split between thread and process. The new table had to be found by every syscall in constant time and had to fit the depth-first list, `design/revoke-by-depth-first-list/`.

## Reasoning

Per-process authority matches the memory model: a thread that can map a frame can already hand it to any sibling, so per-thread slots would be a distinction without isolation.

Because no capability names a table, the capability graph has no cycles and the delete-cascade problem of a table reachable from itself cannot arise. Two fixed levels give constant-time lookup and a bounded cost per entry without a tree walk.

The thread's order comes from its parts. Its record is 224 bytes. Its XSAVE area is what CPUID leaf 0xD, sub-leaf 0, reports in ECX for every state component the core supports: 2440 bytes on the reference host, a Ryzen 9 9950X3D with AVX-512 and PKU, read with `__cpuid_count(0xd, 0, ...)`. Both fit one page with the area at 1024, and the bindings take a node page of their own, so two pages; the block table's small orders are 0, 1 and 3, and order 1 is the smallest that holds them. The node page comes first so that a thread's base is a page the node list holds, as a leaf's and a space's are.

## Alternatives rejected

- **Per-thread capabilities.** No isolation gained, see above.
- **Tables as capabilities**, as in seL4's CNodes. Allows cycles and a delete cascade; more flexible addressing was not needed.

## What this does not settle

- How a dead process's block is torn down and reclaimed.
