---
title: "An object is dead at once; the holder of its untyped tears it down by retype, in slices"
date: 2026-11-08
status: active
tags: [capability, memory, lifetime, revoke]
one_line: "An object is dead when its references reach zero or, for a process or thread, when destroyed through a control capability; every operation then refuses it. There is no kernel list of dead objects: a retype of the block by the holder of its untyped detaches, then dismantles, a bounded slice per entry, until the block is free. The kernel never kills on its own."
revisit_if: "Memory held by dead objects nobody retypes becomes a real shortage that pager policy cannot collect, or a workload needs the kernel to kill a whole process on a fault."
confidence: "The human's choice of who pays, and of the kernel deciding no kill policy, after a precedent survey. The block state machine, references, zeroing, reclaim and two-way detach are in the tree; the dismantle arms land with each object kind."
---

# Teardown is driven by retype

## Decision

Each capability, hidden node and mapping holds a reference on its object's block. Page metadata holds at 4K a type, block order, stale epoch and zeroing cursor, with a reference count at the block's base, and at 2M and 1G a count of typed units, so a retype checks freedom in constant time. Zeroing happens before a capability names memory: at once for 4K, in 64 KiB chunks for larger, with the cursor in the metadata, so a later retype of an abandoned block resumes it.

A binding holds a reference too. What holds a reference is a list node, a capability, a mapping, a hidden node or a binding, and only revoke or teardown removes it. What holds none is a record that points back along such a node: a leaf's parent record, a thread record's process, a reply's bound caller. A back-pointer is cleared in the same step as the node that justified it, so it names a live object or nothing and keeps nothing alive. The count's job is the free check at retype, not the definition of death: a thread's binding holds its process while the process's table holds the thread's capability, so references alone would never reach zero there. Destroy through a control capability is the second way to die, and the holder of the untyped above both clears the counts by revoking its lineage before it retypes.

An object is dead when its block's references reach zero, and a process or thread also when destroy is invoked through a control capability, since a control capability holds a reference and claim needs one to survive the death. Either is one bounded step. Every operation refuses a dead target, except claim, and revoke or delete of a capability naming it. A dead process's threads stop at the next kernel entry: each core checks its current thread's process on entry and on exit, one load each, and an IPI to the process's loaded cores forces that entry.

The kernel never kills on its own. A fault stops only the faulting thread, Inactive with its fault recorded, and sends the fault message if a fault endpoint is named; a stopped thread's registers are readable through its control capability. So destroy is the only way to be dead while references remain.

There is no kernel list of dead objects, and no revoke or delete drains another's teardown. A retype naming a block, by a holder of an untyped covering it, does the work: on a free block it types it; on a block with a hidden node it unlinks that node, so a pager can reclaim a live process's interior leaves and tables; on a dead object with zero references it does a bounded slice of teardown and returns `again` until the block is free; on anything still named by a capability it is refused, and that holder revokes those first.

Every block no capability names has a hidden node, node 0 of its first node page, a child of the untyped it came from: table leaves and table pages. So revoking the untyped reaches them, and a retype can name one alone. A process's address space root and table root are inside the process object, so they go only with the process, after its threads are off every core and flushed. An IO or nested space has its own root, which goes after the bindings under it are undone.

Nothing can be added behind a dismantle's cursor. What the hardware walks is detached first: every table page records its parent, the root pointer or table entry that points at it, and detach is two-way in one bounded step: clearing a parent's pointer also clears the child's record, and a child with no record skips the parent write. So a parent record names a live block or nothing. The capability table is walked by software only, through `Tables::lookup` (`kernel/verified/capability/table.rs`), which refuses a slot in a leaf whose hidden node is dead, one load of node 0 of the leaf's page. So a table leaf is not detached: it stays in its root entry, inert, until its own retype frees it, and that free clears the root entry its parent record names, the same two-way clear in one step. A root entry names a live leaf or nothing, a leaf's owner always names a root the tables hold, and a dead process's block frees only when its table root is empty, waiting for its leaves' retypes as it waits for its threads' bindings. Unlinking a hidden node, by revoke or by retype, detaches a table page and drops the reference, and for a leaf only drops the reference; the rest is dismantle, on a dead block, in slices of the retype that drives it, so a revoke stays exactly its lineage. A leaf or table page a process leaves behind is unreachable and inert, keeping its hidden node until its own untyped's holder retypes it. So is a thread whose process binding was revoked: it cannot run or be bound again, its registers stay readable through its control capability, and its block goes when its untyped's holder retypes it after the capabilities naming it are gone, `design/thread-bound-at-retype/`. A thread Running when its binding goes gets a pending stop and its core's IPI, and leaves the core at that core's next kernel entry, as a dead process's threads do. An endpoint wakes its queue with an error. A dead object nobody retypes keeps its memory, its nodes stay linked in other lineages, inert, and a thread blocked on it stays blocked until the holder drives teardown. Collecting while idle is the holder's policy, charged to the holder.

Rules: a retype or regrant requires zero remaining mappings and no stale translation on any core, `design/flush-without-waiting/`, and a thread object or loaded address space cannot be retyped while a core depends on it.

## Context

Marking dead is one bounded step, but clearing a process's contents takes many, and something must drive them. Two drivers were put to the human: the block's next user, or a kernel list that any revoke or delete advances. Separately, a process with a controller could never reach zero references, so there had to be a second way to die, and whether a fault with no handler should kill the whole process.

## Reasoning

Charging teardown to the party who wants the memory keeps reach exact: no process touches objects outside what it holds, and the theorem needs no housekeeping attributed to no one, `design/theorem-over-reach/`. A kernel list would make one process do another's teardown, and a process killing a large one would slow everyone's revoke until it drained. The cost, memory held by dead objects nobody retypes, is accepted; a pager that wants it back retypes.

Two reviews found what the order of operations had to be: dismantling before detaching left a zombie writable (a grant into a torn-down process, a map through a table page being cleared), bindings that the count did not hold could be freed and retyped under the kernel, and a parent record that outlived its parent could write into a block another process now owned. Two-way detach, bindings as counted nodes, and the hidden-node arm doing no more than detach and its reference are the answers, each now a stated invariant.

On kill policy: seL4, NOVA, L4Re, Genode, KeyKOS, EROS and Barrelfish stop or report the faulting thread and leave the decision to user level; Unix, Windows NT and Zircon kill the process. The kernel here decides no kill policy, so the thread stops and a supervisor destroys and claims, `design/sharing-by-derive/`. Crash dumps, graceful unwinding, migration and paging to disk were each checked as a supervisor, runtime or pager protocol over suspend, readable registers, claim, fault messages and revoke.

## Alternatives rejected

- **A kernel zombie list advanced by any revoke or delete.** See above.
- **A fault with no handler kills the whole process.** One thread's fault would end its siblings, which a process with its own recovery could avoid only by naming a fault endpoint.
- **Detaching a table leaf from its root entry at unlink, as a table page is.** The view attributes a leaf's capabilities to the process its owner names, so a detached leaf keeps an owner whose root entry no longer names it, and the process block could free and its base be retyped while those capabilities are still attributed there. Keeping the owner sound then needs a count of owned leaves, which the root entries already hold, or a sentinel owner, which grows the sentinel's reach and the theorem's statement. A refusing lookup needs neither: the entry itself says the leaf is still the process's.
- **Teardown at zero references with no driver.** Dangled: a table's node pages could be freed while nodes on them were in another lineage, and a revoked thread could keep running with nothing left to stop it.
