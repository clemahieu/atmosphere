---
title: "A change is gated on the main it rebased onto and lands on the main of that moment"
date: 2026-11-10
status: active
tags: [process, gate, landing]
one_line: "No lock is held across the gate: a change is gated on the main it rebased onto, then rebased again and landed by a fast-forward git refuses when main moved; a clean rebase lands without a second gate, so main's tip may be a composition no gate has run on until the next change is gated on it, and tools/land.py tells that case from a failing change."
revisit_if: "The project enters a release phase, where main's tip must be a gated tree; or compositions that fail become frequent enough that gating bases and finding the pair costs more than the lock's waits did, counted as `fail` lines in logs/gate-ledger against landings."
confidence: "A bet by the human on a measured cost and an inferred frequency: the lock's waits are measured over one day, the rate of failing compositions is inferred from gate durations over the same day and was zero in 19."
---

## Decision

A round lands with `tools/land.py`. It rebases the branch onto main, runs the gate, and when the gate passes rebases again, merges into main as a fast-forward and pushes. Nothing is locked. Gates of several loops run side by side.

When main moved while the gate ran and the second rebase is clean, the change lands without a second gate. Main's tip is then a composition of changes that each passed a gate and that no gate has run on together. It is gated when the next change is gated on top of it. A rebase that conflicts is new content and is gated again after it is resolved.

When a gate fails, the tool says whose failure it is. It keeps a ledger, `logs/gate-ledger` at the project root, of every tree a gate has judged. A failure on a base whose tree passed is the change's. A base no gate has judged is gated by itself, once across all loops, and the verdict is recorded. A base that fails by itself is a bug in main: the tool names the commits since the last gated tree, a round files the bug, and the changes that failed on that base wait on it.

Origin's main follows local main, ungated compositions included.

## Context

Landing used to hold one lock across rebase, gate, merge and push, so the commit a gate passed was the commit that landed, and main's tip was always a gated tree. The gate takes about 280 s, so the lock allowed about 13 landings an hour whatever the number of loops.

## Reasoning

Measured on 2026-11-10 on the host (Ryzen 9 9950X3D, 32 threads) from the creation and last-write times of the 43 gate logs of that day, a log being created when its round reaches the lock: 19 landings waited at the lock, 46 minutes in all, and with three loops running the lock was held without a gap from 13:50 to 15:00, twelve landings in the last 55 minutes. Three loops already landed at the lock's ceiling; a fourth could add nothing.

The lock was not protecting the machine. A one-second sample of a gate under the lock showed the x86_64 verify at 26% of the 32 threads on average, the aarch64 verify at 29% and every boot step under 8%. Each step writes inside its own worktree. The one resource gates share is the board, which runs one guest at a time and queues the others (`tools/orangepi-kvm.py`).

What the lock bought was the absence of ungated compositions. Of the 19 gates that ran after main had moved under their branch, none ran long enough to hold a failure at verify or later and a retry, so no composition failed that day, as far as durations can show. A composition that does fail costs one gate of the base to attribute, a search among the commits since the last gated tree, and a fix, while the other loops' changes wait on the bug. That is paid per failure. The lock's wait was paid on every landing once the loops outnumbered what it could carry.

The project is not releasing. A main whose tip is ungated for the length of one gate harms nothing outside the loops, and the loops find it at their next gate.

git needs no help to keep landings apart: `merge --ff-only` refuses when main is not an ancestor of the branch and fails when main's index is taken, and both are answered by rebasing and trying again.

## Alternatives rejected

- **The lock across the gate.** Keeps every tip gated and caps landings at one gate's length each. Its cost is above.
- **A second gate whenever main moved.** Keeps every tip gated without a lock, but under load main moves during nearly every gate, so nearly every landing gates twice and may never catch up.
- **A lock across rebase, merge and push only.** Correct and seconds long, but it adds a mechanism for what git's fast-forward check already does.
- **One gate for a batch of waiting branches.** Gates the tip and not each commit, and a failing batch needs the same search for the culprit, with every branch of the batch held up meanwhile.
- **Pushing only gated tips to origin.** Keeps origin's main gated at the price of a second moving ref and a process to advance it. Nothing consumes origin's main today that needs it.

## What this does not settle

Running the gate's steps side by side, which would shorten each gate and is independent of this. Finding the first failing commit among the suspects, which the tool leaves to the round that takes the bug.
