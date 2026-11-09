---
title: "The latest value goes through three slots and one swapped word, not a seqlock or a one-slot ring"
date: 2026-11-09
status: active
tags: [ipc, shared-memory, verified]
one_line: "amailbox gives one producer and one consumer the latest value through three slots and one atomic word holding the shared slot's index and a fresh bit: publish is one swap, observe is one load and at most one swap, nobody copies the payload or retries, and intermediate values are dropped. It is for two ends that both follow it; across a distrust boundary the path is aring."
revisit_if: "Two ends that do not trust each other need the latest value, which a swapped word cannot protect; a caller measures the word sharing a cache line with the slots as its cost; or a target lacks an atomic swap of 32 bits."
confidence: "The permutation, the fresh bit's meaning and the atomic counts are proven in amailbox/src/lib.rs. That three slots are cheaper to prove than Simpson's four is a judgement from the size of each protocol, not a measurement."
---

# The latest value by a three-slot exchange

## Decision

A producer that publishes at its own pace and a consumer that wants only the most recent value share `amailbox`: three slots and one `u32` word. Each end holds one slot privately. The word's low two bits name the third slot and the next bit says whether that slot is a publish the consumer has not taken.

- Publish writes the producer's slot in place, then swaps the word to the producer's index with the fresh bit set and takes the slot that comes back. One atomic, whatever the consumer is doing.
- Observe loads the word. Stale, it keeps its slot. Fresh, it swaps in its own index with the fresh bit clear and takes the fresh slot. One or two atomics, never a loop.

The proof's invariant, `Exchange` in `amailbox/src/lib.rs`, is that the three indices are always a permutation of 0, 1 and 2, so the producer never writes the slot the consumer holds; that the word is fresh exactly when the producer has published past what the consumer took; and that the latest publish is in the shared slot when the word is fresh and with the consumer when it is stale.

## Context

`aring` keeps every slot until the consumer takes it, so a consumer that falls behind fills the ring and stalls the producer. Telemetry, a clock, a pointer to the current configuration: for these the consumer wants the newest value and the producer must not wait. Three objects present themselves for that, and only one gives both ends a bounded number of steps without copying the payload.

## Reasoning

Swapping one word that names a slot moves ownership of a whole slot in one atomic step, so the payload is written and read in place and never copied. A swap cannot duplicate an index, so the permutation holds whatever the interleaving, provided both ends store only through the swap.

The consumer swaps only after a load finds the fresh bit. Only the consumer clears that bit, so a fresh load is still fresh at its swap, and the swap takes the latest publish. A poll that swapped unconditionally could hand the latest slot back to the producer and take an older one.

Published accounts agree on the shape: Simpson's four-slot mechanism (IEE Proceedings E 137(1), 1990) needs no read-modify-write but four slots and four control bits; Rushby's model checking report (SRI, 2002) notes that Simpson's own three-slot mechanism fails without timing constraints and that three slots work when the control is a compare-and-swap; the swap of one word here is that kind of read-modify-write. The three-slot exchange is the smaller proof.

## Alternatives rejected

- **A seqlock.** The reader copies the payload and retries when a write overlaps the copy, so a fast producer starves a slow consumer, and the copy is the cost the slots avoid.
- **A one-slot ring.** Full after one publish, so the producer stalls until the consumer takes it, the case this object exists to avoid.
- **A compare-exchange loop on observe.** Lock-free, not wait-free: a producer that keeps publishing can make every attempt fail.
- **Simpson's four slots.** Meets the same bar with plain atomic bits and no swap; the larger proof, with no property the three-slot exchange lacks for two ends that follow the protocol.
- **One atomic store of the value.** Right when the value fits in one word, and then no crate is needed.

## What this does not settle

The trust model is the exchange's own: a peer that stores an arbitrary word can hand back the slot the other end holds, and the honest end has no local test for it. Across a distrust boundary the path stays `aring`, whose each index has one writer. Where the word and the slots live in shared frames, and whether the word gets its own cache line, is the caller's, after a measurement.
