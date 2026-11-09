---
title: "Producers that do not trust each other each own a ring, and the consumer scans the rings; there is no shared cursor"
date: 2026-11-09
status: active
tags: [ipc, shared-memory, verified, security]
one_line: "Several untrusted producers feeding one consumer get one aring each, and afanin's scan finds the first ring with a slot available from a start the caller rotates. No word is written by two producers, so a wild index is rejected by its own ring alone and a producer that stops stalls only its own ring. A queue with one shared enqueue cursor is for producers inside one trust domain and is not built until a caller needs its total order."
revisit_if: "A caller inside one trust domain needs one total order across producers, which the scan does not give; or the number of producers grows until a scan over every ring costs more than the shared cursor's contended line, which a measurement would show."
confidence: "The isolation is proven in afanin/src/lib.rs over aring's proven observe. That the shared cursor cannot reject a peer's store is an argument from the published algorithms' structure, not a proof; the cost comparison is not measured."
---

# Fan-in over private rings

## Decision

Several producers that do not trust each other, and one consumer, share `afanin`: one `aring` per producer, each with its own slots and its own two indices. A producer writes only its own head and its own slots, exactly as on a single ring. The consumer holds one `aring::Consumer` per producer and polls with `afanin::scan`, which starts at a ring the caller supplies, wraps, and examines each ring once: a ring that already has a slot available is returned without a load; otherwise the producer's head is loaded and passed through that ring's `observe`, and the ring is returned if a slot is now available. The caller consumes on the returned ring through `aring` and starts the next scan past it, so every ring is reached within one scan per ring.

What is proven, in `afanin/src/lib.rs`: each ring ends the scan as `examined` of its own state and the one head loaded for it, whatever was loaded for any other ring; a head a ring rejects leaves that ring as it was; the rings after the returned one are untouched; and a scan that loaded an honest producer's head with slots in flight does not report every ring idle, so a producer that stopped, or published garbage, stalls only its own ring.

## Context

A single-producer ring is the bulk path across a trust boundary (`aring`, with `design/trust-boundary/` for why the peer's index is untrusted). When several clients feed one service, the obvious extension is one ring that every producer enqueues into, claiming slots through one shared index. That queue is attractive: one total order, one place to look, and the published algorithms for it are well known and fast. It does not survive producers that do not trust each other.

## Reasoning

The bounded multi-producer ring (Vyukov's bounded MPMC queue, whose published code is BSD-2-Clause or Apache-2.0) claims a slot by a compare-and-swap of one shared enqueue index and publishes it by storing that slot's sequence. The consumer cannot pass a claimed slot whose sequence was never stored. Three consequences follow from that structure:

- A producer that claims and stops stalls every later slot, including slots other producers have already published. Finishing its claim for it means writing its slot, which is trusting it again.
- Every producer can store the shared index, so one producer can skip or tear another's slot. Once several parties write one word there is no single-writer advance for the consumer to reject; `aring`'s `observe` rejects a wild index only because exactly one party publishes it.
- Every producer writes the same cache line on every enqueue.

The intrusive multi-producer list (Vyukov's, same terms) and Michael and Scott's queues (PODC 1996) share the shape: a head or tail every producer exchanges, and either a missing link that hides every later node or helping that reads and writes a peer's state.

Fan-in has none of the three. No word is written by two producers. A producer's wild index reaches only its own ring's `observe`, which rejects it and leaves the ring unchanged, and no other ring's state depends on it. A stopped producer leaves its own ring empty and every other ring returnable. Each producer's path is the single-producer path: a store of its own head, on its own line.

The cost is the scan: the consumer loads up to one head per producer when it has nothing cached, and there is no order across producers. A service that serves untrusted clients does not need one, and the rotating start gives each ring its turn.

## Alternatives rejected

- **One ring with a shared enqueue cursor.** Fails all three bars above for untrusted producers. It belongs to producers inside one trust domain that need one total order and can assume every claim finishes; it is not built until such a caller exists.
- **A shared cursor with helping.** Lets a later producer finish a stopped one's claim, which means writing a peer's slot or link: agreement again, and the same contended line.
- **Loading every head before the scan.** A slice of heads gives a simpler signature, but it loads every producer's line on every poll, even when the first ring already has slots. `Heads::load` is called only for a ring that has nothing available.
- **A scan that always starts at ring 0.** A busy low ring would starve the rest. The start is the caller's so that it can rotate it.

## What this does not settle

- Waking the consumer. The scan polls; whether an empty scan blocks on an endpoint or a notification, and how producers signal it, is the caller's.
- Placing the rings and the heads in shared frames, and the acquire load in `Heads::load` before the consumer reads a slot, as with `aring`.
- A total order across producers, which this object does not give.
