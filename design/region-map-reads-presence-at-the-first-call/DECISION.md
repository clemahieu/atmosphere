---
title: "The region map learns what is empty from a kernel read of which entries are present, judged at the entry of the process's first call"
date: 2026-11-17
status: active
tags: [user, memory, address-space, proof, trusted-base]
one_line: "A read-only kernel operation reports which of up to 64 entries at one level of a space are present and which are leaves; the region map walks the user part of its own space with it at entry, 8 calls for the root and 8 per table page beneath a present entry; the first step through the caller token fixes the state the page tokens are claimed against at that step's entry, so what no proof reaches is that the process's Rust memory is mapped when its first call enters; the entry value is the caller token with no step taken and no page claimed, which the build requires, so the map is built once."
revisit_if: "A process's space holds so many table pages that the walk at entry costs more than the program's start-up can pay; or a loader must hand a process a layout it cannot map before the first call; or the kernel comes to record, per space, what was mapped when the process was handed it."
confidence: "The call bound is arithmetic over the entry counts. That the read's contract proves a region empty was not yet verified: it rests on the walk the probe already proves, and the leaf that adds the operation verifies it. Moving the unproven claim from the handed state to the first call's entry is a judgement that the two are exposed to the same thing, a revoke the process cannot see, and the record says why."
---

# How the region map learns what is empty

## Decision

**The kernel answer.** One operation of `kernel/verified/capability`, read-only: in the space of the capability at a slot, which must name a live process's space and allow writing it, read `count` entries, 1 to 64, at level 1 to 4, from the one an address names, all in one table. It is refused, with nothing changed, exactly when the address names no entry at that level, the count is out of range or leaves the table, the slot fails as probe's does, or the walk reaches no table at that level. On success the kernel is as it was, and it returns two masks: bit i of the first is set exactly when entry i is present, bit i of the second exactly when entry i is present and a leaf, a 4K page at level 1 or a 2M frame at level 2. Its contract carries the fact the region map needs: an entry absent at level L means no path under it is in the space's mapping.

**The walk.** The region map reads the root's user entries, `KERNEL_MEM_END_L4INDEX` to 511, in 64-entry calls, and descends under each present entry that is not a leaf, reading the table below in the same way. Every page under an absent entry, at any level, is free. A present leaf, and every page of a 2M leaf, is not. A call reads 64 entries and a table holds 512, so the walk makes at most 8 calls for the root and 8 for each table page beneath a present entry. A process whose image and stack sit under one root entry, in one level 3 table, one level 2 table and a few level 1 tables, is walked in about 40 calls.

**The state the base case is judged at.** A run-time answer says what was empty when the call that asked entered. The rely relates that state to the one the process was handed only by removal, `space_kept`: an entry present when the process was handed it may have been removed since, by an ancestor's revoke, and a page found empty then may still hold the process's Rust memory. So the first step through the caller token fixes `Caller::start` at that step's entry state, and `claim` keeps its two premises, empty at `start` and empty now, with `start` that state. No page token rests on a state before the first step. What no proof reaches moves with it: the process's Rust memory, its image, stack and statics, is mapped when its first call through acall enters.

**The entry value.** It is the caller token itself, as the program's start-up code conjures it, once, with no step in its history and no page token claimed; its conjuring is a line of `tools/boundary-list`. `RegionMap::build` takes it by exclusive reference and requires both, and its own reads are the first steps. A second build from the same token fails its requires, since the first took steps. No separate entry type is added: the token's history already says whether it is fresh.

**The crate.** `aregion`, marked verified, with no static, so that a lock can hold the map later without changing its specification. Its operations:

- `build`: the walk and the claim, above. It holds the free pages as runs in a fixed array, since the heap is one of its clients and there is no allocator beneath it, and their page tokens as one set token. When the walk finds more free runs than the array holds, the map keeps the lowest runs that fit and claims nothing of the rest. It refuses exactly when a read is refused, which for the caller's own space with the write right does not happen; that is its postcondition's to say.
- `reserve(pages, alignment)`: splits a run of that many pages at that alignment from the lowest free run that holds it and returns it as a range with its set token. It refuses exactly when no free run holds it.
- `give_back(range)`: takes a range the map handed out whose every page token says no frame, and returns it to the free runs, merging with its neighbours. It refuses exactly when the range adjoins no free run and the array is full; the client then keeps the range and its tokens.
- `split` and `merge`: a range splits at a page into two, each with its tokens, and two adjoining ranges of the same map merge into one. Neither refuses at run time; what each needs is in its requires.

A range's tokens are one set token over the caller's page authority, from which a client splits the `PageToken` of one page to map it through `map_own` and to which it joins it back. One empty root entry is 2^27 pages, so the map cannot claim them one at a time; acall claims a set at once.

## Context

`design/region-map-owns-the-address-space/` decided that the region map is built once at entry from what the kernel reports empty, and that `claim` issues a page's token only for a page empty both in the state the process was handed and now. It left open which kernel answer shows a region empty at a cost entry can pay, and what the entry value is. The human preferred, on 2026-11-12, asking the kernel at run time to deriving the layout in proof.

No operation answered it. `probe` reads the accessed and dirty bits of level 1 entries, sets a bit only for a present entry and so says nothing of an absent one, and is refused when the walk reaches no level 1 table, which happens both above an absent entry and above a 2M frame at level 2. `inspect` reads capabilities, not entries.

## Reasoning

**One read per table, not per entry.** A level 4 entry covers 512 GiB, so most of a process's space is found free by reading one root, and only the tables the loader linked are descended into. 64 entries a call matches probe's bound, `PROBE_MAX`, which keeps the operation's step count within the bound a probe already has, `INVOKE_PROBE_STEPS`.

**Present and leaf, and nothing else.** The region map needs to know where the walk stops and whether it stopped at a mapping. Returning the entries' addresses or permissions would tell a process nothing it may act on and would make the contract wider than its one use.

**The write right, as probe asks.** The read reveals the shape of a space, which is part of what the right to change it covers. A process reads only its own space at entry; a reader of another process's space with less authority is a use nothing has asked for.

**Why the first call's entry and not the handed state.** The kernel keeps no record of what a space held when a process was handed it, and adding one for this would put a history of the space into the proven kernel for a fact only the process needs once. The handed state was already a vouched premise: `step.rs` says that the token was the kernel's state when the process was handed it is unproven. Both versions of the claim are exposed to the same event, a revoke of a page of the process's image that the process cannot see. A revoke just before the process was handed it makes the handed state lack the page too, and nothing proves the image was mapped then either. Moving the premise to the first call's entry, which the start-up code makes the region map's own read, narrows nothing a proof covered and lets a run-time answer serve.

**The token is the entry value.** A separate tracked entry type would add a second conjured value to say what an empty history and an empty authority already say. Requiring both of `build` gives the build-once property as a precondition Verus checks, which a throwaway that builds twice shows.

## Alternatives rejected

- **Probe with a present mask in its fifth result.** It covers level 1 only, and its refusal cannot tell a missing table from a 2M frame, so a region above level 1 is never shown empty. It also clears accessed and dirty bits as it reads.
- **One call per entry, a walk to the level where an address stops.** Simplest to state, but a level 1 table that the loader linked costs 512 calls in place of 8.
- **Deriving the layout in proof from boot's theorem.** It serves the root process alone, whose handed state boot's theorem states, and no process another process builds. The human preferred a run-time answer.
- **A layout the loader passes in.** The loader then vouches for every address it names; a run-time answer from the kernel needs no such promise.
- **A separate entry type that build consumes.** Above: it restates what the caller token's history already says.
- **The kernel records, per space, what was mapped when the process was handed it.** It makes the handed state provable at the cost of a history in the proven kernel; it is the first thing to look at again if the moved premise proves too weak.

## What this does not settle

- Where each program's start-up code conjures the caller token and builds the map, dom0's and astd's.
- How the region map is shared by several threads of one process, which `design/region-map-owns-the-address-space/` leaves open.
- How large the run array is, which is the crate's to set from what dom0's space needs.
