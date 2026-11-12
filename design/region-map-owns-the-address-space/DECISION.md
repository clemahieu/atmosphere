---
title: "A process's own address space changes only through its region map, which holds a token for every page it may hand out"
date: 2026-11-12
status: active
tags: [user, memory, address-space, proof, trusted-base]
one_line: "Between the kernel, which decides what can be mapped, and the heap, which carves pages it was given, a region map says which part of a program owns which addresses: built once at entry from what the kernel reports empty, it holds a tracked token per page saying which frame is mapped there or none, acall maps and unmaps in the caller's own space only against such a token, and the proof holds for a process whose code and controller keep four rules."
revisit_if: "The kernel comes to keep a revoked entry claimed until its owner unmaps it, which would let the kernel's table be the only record and the tokens go; or several threads of one process must map at once, which one authority per process does not serve; or a program that keeps the four rules is found whose memory proof still fails."
confidence: "The hole is measured: a throwaway against the tree verifies false, below. That page tokens close it was checked on a model outside the tree whose kernel is a bare map, not on the tree. Of what the tokens need of the kernel, that a call returns with nothing stale on its core is proven, from the kernel's entry through acall's step; that other callers only remove a sealed process's entries is not. Where the proof stops, the four rules, is the human's choice."
---

# The region map

## Decision

Three layers stand between a frame and a Rust value. The kernel decides what can be mapped, and is proven. The heap carves the pages it was given, and is proven. Between them the region map says which part of a program owns which addresses of the process's own space, and it is the only route by which verified code maps or unmaps there.

- **A page token.** For every page of its own space that a process may hand out there is one tracked token, which says which frame is mapped at the page or that none is. It cannot be built or copied by verified code. What it means is an invariant over the kernel's state the caller token carries (`acall/src/step.rs`): the entry at the page maps the frame the token names, or is absent. Absent is allowed under a token that names a frame because an ancestor's revoke removes entries. The access then faults and shows no wrong value, and the token still holds the address, so nothing else is mapped there in its place.
- **The own-space calls.** acall's map of a page in the caller's own space takes a page token that says none and returns it naming the frame, together with the permission to the page's bytes. Its unmap takes the token and the permission and returns the token saying none. acall's raw step is private to acall, and its general map and unmap require that the slot names another process's space, which is how a process building a child is told from one changing itself.
- **A frame's token.** A frame's capability slot has a token of the same shape, saying whether the frame is mapped. The own-space map takes it saying unmapped, so a frame backs one page at a time and the permission to that page is to bytes nothing else reaches.
- **The region map.** One per process, built once, from the entry token, which exists once. It asks the kernel which regions of the space are empty and takes the page tokens of those regions and no others. The image, the stack and whatever else was mapped at entry are so outside it, with no claim about how the loader laid the process out. It hands out disjoint ranges with their tokens and takes them back. A source such as aeager is its client and holds the tokens of its window.
- **The residual claim.** One statement is left that no proof reaches, and it sits in acall's own-space map: a page whose entry the kernel wrote present and writable, in the space the calling core has loaded, with nothing stale on that core, of a frame that is memory and that no other entry maps, at an address whose token the caller holds, may be held as a `PointsToRaw`. Rust's library documentation states the rule this restates, in the `core::ptr` module's account of exposed provenance: memory outside the abstract machine is exposed so long as it is disjoint from the memory the abstract machine uses, such as the stack, the heap and statics. The page token is that disjointness.

The proof covers verified code. It holds for a process only while everything that can reach the process's memory keeps four rules:

1. Map and unmap in your own address space only through the region map.
2. Write only to memory the region map or the heap handed you.
3. A frame mapped at two addresses, or in two processes, is shared memory: what you read there is not known to be what you wrote. Ask for it as shared, and do not use it as ordinary memory.
4. Whoever controls the process, its creator or a debugger, keeps rules 1 to 3 when it acts on the process.

Unverified code in the process, dom0 or a C++ program, and a controller cannot be held to these by a proof. Nothing outside the process depends on them: the kernel's theorem assumes nothing of user code, `design/trust-boundary/`, so a process that breaks a rule harms itself.

One thread of a process maps and unmaps.

## Context

`aeager` maps frames into a window of its process's space and hands the heap the permission to each page's bytes. One trusted item made that permission, on premises its reason listed and nothing proved. Three of them were about the address and not about the frame or the hardware: that no other Rust memory lies at the page, that no other entry maps the frame, and that the entry stays as it is while the permission is held. Each was a promise by whoever created the source.

They are not a worry about what a committer could add, which `design/committer-is-not-the-adversary/` sets aside. A throwaway that uses the tree's items as they stand shows it, added to `aeager/src/glue.rs` at a4b96f6: it calls `map_page`, then `acall::memory::unmap` at the same address without giving up the permission, then `map_page` with another frame, splits one byte from each of the two permissions and calls vstd's `PointsTo::is_disjoint`. `assert(false)` after it verifies: `tools/verify.py` reports aeager at 86 verified, 0 errors with the throwaway in place. With the `is_disjoint` line removed it reports 85 verified, 1 errors, the assertion, so the false comes from the two permissions and not from a branch nothing reaches.

The tree showed the missing layer in other ways. `Eager::new` took the process's only caller token by value, so no other verified code could make a system call, and dom0 minted a second and a third token to go on. dom0 chose each source's window as a constant. `map_page` took the set of live pages as a ghost value its caller picked.

## Reasoning

**Two things must change together**, the entry at an address and the permission to its bytes, so one module has to be the only one that changes either. The permission was already private to one module. The entry is not a field anyone can make private, since it lives in the kernel, so a token stands for it and the calls that change the entry demand the token. That is a capability at the level of the proof, and it costs nothing at run time: a token is erased.

**The token remembers what the kernel's table forgets.** The kernel refuses a map onto an occupied entry (`map_fits`, `kernel/verified/capability/caller.rs`), and while every address a program uses is mapped that alone tells a free address from a used one. Two cases part them. An ancestor's revoke empties an entry while the program still holds the permission to the page, and the kernel would then accept a second map there. A source that backs pages on first use hands out addresses whose entries are empty. In both the address is claimed and the table does not say so; the token does.

**The base case asks the kernel.** Before any code of the process has run, nothing outside what is mapped is claimed, so the regions the kernel reports empty are exactly the ones whose tokens may be issued. Asking at entry serves any loader, with or without a chosen layout, and it leaves Rust's own memory out by construction, since the stack and the statics are mapped or the program would not be running. The region map is built once because it consumes the entry token.

**What others do is the kernel's to prove.** The invariant under a token survives the process's own calls because each of them takes and returns the token. It survives every other caller's step if those steps only remove entries from the process's space, which is a clause the rely of `kernel/verified/capability/rely.rs` does not have yet: it speaks of table slots, for a sealed process. A controller is the case the kernel cannot prove, because changing the process's space is what the control right is for, `design/process-holds-capabilities/`; rule 4 is that case.

**The rules are few because the tokens carry the rest.** Disjointness between clients, a frame backing one page, an address not reused under a held permission: verified code cannot break these, so nothing asks a program to keep them. The four rules are what is left for code no proof reads.

**The calling core holds nothing stale.** The kernel's verified entry acknowledges the flush epoch on the calling core whenever that core is behind, whichever core's unmap or revoke moved it, `design/flush-without-waiting/`, and acall's step restates that the core returns to its thread caught up, holding no translation of the caller's space to a page no space maps. The residual claim takes that from the map's own step.

**On a model.** A standalone file over vstd's ghost map, with the kernel as a bare map from page to frame and the step specifications restated by hand, verified the own-space calls keeping the invariant under removal by others, and refused four throwaways: a second map at a page whose permission is held, one frame at two pages, an unmap through the raw step, and a forged token. It is not in the tree and shows only that the shape is consistent.

## Alternatives rejected

- **Keep the premises on the creator's promise.** It is the gap as it stood, and verified code can break the promise without knowing, as the throwaway does.
- **Each source keeps the caller token.** The entry then changes only by the source's own calls and its record can prove the rest, but the process can make no other system call. dom0's minted tokens were this alternative's cost showing.
- **The kernel's table as the only record, asked at every map.** It needs no tokens and no entry step, and it is what the tree did. Revocation and backing on first use are where it fails, above.
- **The kernel keeps a revoked entry claimed until its owner unmaps it.** It would make the table the only record after all. It changes what an entry can hold and what revoke leaves, in the proven kernel, for a fact the user side can hold for nothing; it is the first thing to look at again if the tokens prove heavy.
- **A range of address space as a kernel object with a capability**, as Zircon's address regions are by its documentation. The same authority, enforced where every program meets it, C++ included. It puts the choice of addresses and a new object kind in the kernel, and the proof would still need the user side to say what it holds.
- **No tokens, each client proving at every call that it agrees with the kernel's state.** Each client would then reason about every other client's calls, which is what a shared caller token was meant to spare them.

## What this does not settle

- Several threads of one process, or one process on several cores: who holds the authority, and how an address is reused when an unmap returns before other cores have flushed, `design/flush-without-waiting/`.
- What a process another process built may assume in its proof. It is not sealed while its creator keeps the capability, so the rely does not serve it as proven; whether the creator gives the capability up, or is held to a stated guarantee, is open.
- How the residual claim is written: an assumed specification under a new kind of citation, to Rust's documentation, or an exempted body with its reason.
- Whether the values unverified code conjures for verified code, the entry token among them, are counted as the exemptions inside verified crates are.
- Where Rust's allocator interface meets the heap. `astd/src/heap.rs` conjures the permission in `dealloc` because that interface carries none, and the region map does not change it.
- Shared memory's own interface, the one rule 3 points a program to.
