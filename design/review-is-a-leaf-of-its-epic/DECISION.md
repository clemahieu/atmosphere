---
title: "A skeptic pass is a review, a leaf under the epic it judges"
date: 2026-11-11
status: active
tags: [process, skeptic, tracker]
one_line: "The skeptic pass that an epic closes on is its own issue: a task labelled review under the epic, waiting on the epic's other children; one review is one pass, a refuting review files a repeat, and the epic closes when its newest review passed after everything else below it closed. An epic is never claimed for a pass."
revisit_if: "The tracker lets a task wait on an epic, so a review could be written ahead for every epic and not only at a split; or reviews written at a split mostly run early or are withdrawn, counted as close reasons starting `withdrawn` against reviews closed."
confidence: "A judgement about structure. Coverage is the same by construction: the rule for which epic needs a pass is unchanged, and tools/reviews.py refuses an epic whose review missed a later closing. Cost per pass is not expected to change."
---

## Decision

The skeptic pass is a review: a task with the label `review`, a child of the epic whose acceptance criteria it judges. A round claims it from the ready list like any leaf, writes where the evidence is and hands it to the driver, which runs the skeptic and appends the report. The round that claims it next closes it: `skeptic pass:` when every criterion stands, or `refuted:` after filing a leaf per refuted criterion and a repeat review that waits on those leaves. One review is one pass.

Which epic needs one is unchanged: more than three children, depth 1, or the label `skeptic`. A review is written with the leaves at a split, waiting on each of them, and otherwise when the epic finishes. An issue filed under an epic later is added to what the open review waits on.

An epic closes on its children's evidence when it needs no review, and otherwise when its newest review passed and every other issue below the epic closed before that review's pass began. `tools/reviews.py` decides that from the tracker, and a round acts on its lines. An epic is claimed only for the moment a round writes its review, so that two loops do not write two.

## Context

The pass used to be a state of the epic. A round claimed a finished epic, the driver ran the skeptic on it, the report went into the epic's notes and a later round read it there. Three things followed.

An epic was handed out like a task, but it is not one: its size is whatever its subtree turned out to be, and the pass had no issue of its own. It was not in the ready list, so the passes still owed were invisible, and its tokens were counted under an epic alongside nothing that said how many passes they were.

The tracker (bd 1.1.0-rc.1) refuses a dependency between an epic and a task in either direction: `epics can only block other epics, not tasks` and `tasks can only block other tasks, not epics`. So nothing could wait on a pass, and a pass could wait on nothing; "finished" was a rule a round evaluated in prose over the whole list of epics. The refusal is checked only when the edge is added: an edge survives a retype, and on 2026-11-11 the tree held 99 edges where an epic waited on a task and 34 the other way, all left by a leaf that was split and became an epic.

The unit of review was whatever container the splits happened to produce. A split sizes pieces for implementation, one change each; it says nothing about what a reviewer can judge in one pass.

## Reasoning

Measured on 2026-11-11 from the token ledger (`tools/token-ledger.py`, the calls of kind `skeptic` grouped by transcript, each transcript one pass) and one `bd list --all --json`:

- 78 passes on 50 epics. A pass took 38k output tokens at the median and 117k at most, with 3.5M tokens read from cache at the median and 24.7M at most. The 576 leaves with calls of kind `round` or `prover` took 20k output at the median. A pass is a unit of work the size of one or two leaves, and 28 of the 78 were repeats.
- Nothing about the epic predicted a first pass's output: over the 49 epics with a pass when it was taken, the correlation was 0.39 with its number of children, 0.38 with the commits its children's close reasons name, and -0.09 with the lines those commits changed.
- 120 of the 168 epics below the star needed a pass by the rule. 89 of them were open, 76 with no pass in the ledger, and 32 were finished and waiting for one. None of that was in the ready list.
- The passes find things. Of those 49 epics, 20 had at least one child whose description cites a refutation, 69 such leaves in all.

A review as a leaf answers each point with what the tracker already does. It is claimed atomically, so the claim that keeps two loops off one pass needs no rule of its own. It waits on tasks, which the tracker allows, so the ready list holds a review exactly when its pass is due, and an edge to a child survives that child's split. It has an id, so the ledger counts one pass under one issue and the status page shows who holds it. A repeat is a new review whose description names what it repeats and which waits on the leaves that answer the refutations, so its scope is written down.

Coverage does not rest on those edges. An issue can be filed under an epic without being added to its review, and the tracker refuses the edge when the issue is an epic. So the close is decided by time: every other issue below the epic must have closed before the time the passing review's `Skeptic input` note carries. An edge that is missing costs a pass that ran early; it cannot let an epic close over work no pass saw.

Existing epics are not migrated. One whose children are all closed gets its review when an epic round reaches it, which is when its pass would have run.

## Alternatives rejected

- **The pass as a claim on the epic.** What was done before; its costs are the context above.
- **One review per epic, reopened for each repeat.** Fewer issues, and the notes read as they did on the epic. But a pass again has no issue of its own: the ready list cannot tell a first pass from a repeat, the ledger cannot tell their costs apart, and what a repeat is to re-judge is recovered from notes instead of read from a description.
- **Every issue a task, a container being a task with a label.** Removes the refused edges altogether. A task with an open child stays in `bd ready` (checked on a scratch tree), so every query of the procedure, the driver and the status page would need a label filter, and 168 epics a retype. A review that is a task already gets the edges a pass needs.
- **No review for an epic that a leaf split made.** The same commits are judged at each level, and removing the inner levels would remove passes. Of the 20 epics refuted, 14 sat under another epic that needed a pass, and they account for 38 of the 69 leaves; those findings would come later, at an ancestor's pass over more work, or not at all.
- **Coverage by dependency edges alone.** The tracker refuses the edge from a review to a child that is already an epic, and an issue filed while a pass runs is not seen by it whatever the review waits on.

## What this does not settle

- What bounds a pass. Nothing measured predicts its cost, so a bound would be imposed: a budget, or a review that judges less than the whole epic. Neither is decided, and either could lower coverage.
- A review for an epic split before this decision is written when the epic finishes, so its pass is not in the ready list ahead of time.
- How much work a subtree will be once split. A review makes the review part of it countable and no more.
