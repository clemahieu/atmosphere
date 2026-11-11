---
title: "The heap's size classes step by a quarter of each doubling up to the page, and a class's slabs come from the smallest run that wastes at most an eighth"
date: 2026-11-11
status: active
tags: [memory, heap, verified]
one_line: "aheap has CLASSES size classes: the first eight multiples of 16 bytes, then four classes an even step apart in each doubling up to the page (28 with a 4 KiB page); a class's slab is a run of the smallest order whose tail after the last slot is at most an eighth of it, as long as the run holds no more slots than a slab's bitmap has bits for."
revisit_if: "A measured workload's internal fragmentation or slab count points at another spacing, a target's page is not 4 KiB (CLASSES and the slab bitmap follow the page, and lemma_class stops verifying until CLASSES is set for it), or the heap's front needs an alignment above 16 bytes from a class that is not a power of two."
confidence: "The facts a slab needs are proven per class in aheap/src/class.rs (lemma_class, by computation over every class); the spacing and the eighth are a judgement, taken in the correctness phase without a workload to measure."
---

# The heap's size classes

## Decision

A small object is rounded up to a size class, and each class's slabs are cut into slots of that one size (`aheap/src/class.rs`).

- The first eight classes are the multiples of SLOT_MIN, 16 bytes: 16 to 128.
- Past 128 bytes each doubling of the slot size is cut into four classes an even step apart, a quarter of the doubling's base: 160, 192, 224, 256, then 320 to 512 by 64, and so on, up to the page, which is the last class. With a 4 KiB page that is 28 classes, every one a multiple of 16.
- A class's slabs are cut from a page run of the smallest order whose tail, the bytes after the last whole slot, is at most an eighth of the run, as long as the run holds no more slots than the slab's bitmap has bits for (MAP_SLOTS, a page of 16-byte slots). With a 4 KiB page that is one page for every class but 1536 (two pages), 2560 (two) and 3072 (four).
- `class_of(n)` is the smallest class whose slots hold n bytes, for n up to the page; an object over a page is not a slab's.

## Context

StarMalloc, whose specification the heap is modelled on (arXiv 2403.09435, section 2.2), has 27 classes of multiples of 16 bytes up to the page, and a slab of exactly one page. The paper does not list its classes, and its repository is not read for this work, so the classes are chosen here.

## Reasoning

Four classes per doubling bound the bytes a rounded-up object wastes to a quarter of its size past 128 bytes, and to 15 bytes below it, with few enough classes that each holds slabs that fill. The classes are a formula in SLOT_MIN and the doubling, not a table of literals, so nothing in it is page-shaped; the count is the one number that follows from the page, and the proof that the last class is the page fails if the page changes and the count does not.

A one-page slab, StarMalloc's, wastes more than a third of the page for a 2560-byte class and a quarter for 1536 and 3072. The page buddy cuts runs of any order, so a class takes the smallest run that wastes at most an eighth. Every class up to 1024 bytes already does in one page, and the bitmap bound keeps a run from holding more slots than a slab can track.

## Alternatives rejected

- StarMalloc's one-page slab for every class: simpler, and the waste above for the largest classes is avoidable at no cost to the proofs, which hold for a run of any order.
- A table of class sizes: it writes the page's fractions as literals and has to be rewritten for another page.
- Classes of every multiple of 16 up to the page: 256 classes, most with slabs that never fill.

## What this does not settle

Alignment above 16 bytes. A slot of a power-of-two class is aligned to its size when the run is; whether the heap's front serves a larger alignment from those classes or from a page run is the front's decision.
