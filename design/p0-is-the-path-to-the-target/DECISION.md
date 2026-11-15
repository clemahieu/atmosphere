---
title: "P0 is the path to the one epic labelled target"
date: 2026-11-15
status: active
tags: [process, tools, tracker]
one_line: "P0 means on the path to the one epic labelled target: the loop recomputes that path before each dispatch, sets it and every epic that holds one to P0 up to but not including the root, demotes every other P0, and files one issue when nothing on the path can be taken."
revisit_if: "More than one epic is labelled target at once, or a priority has to mean something other than the path to that epic."
confidence: "Judgement from a dependency cycle through a parent edge that hid the trunk while hand-set P0 sat elsewhere; the loop's tests check the closure, the edits, the one stall and the dispatch order."
---

## Decision

The human marks one epic with the label `target`. P0 means on the path to that epic, and `tools/loop.py` recomputes it before each dispatch.

The path is every open issue the target transitively waits on. Waits-on follows three edges: a blocks-dependency, a child (a closed child is walked so an open descendant is reached), and the blockers of any ancestor, because a blocked ancestor hides its children from ready. An epic that holds a path issue stays at P0 as well, walked up to but not including the root. The root's priority is left alone: it is never a split or a close round, unless it is itself the target.

Every open, in-progress or blocked issue on that set whose priority is not 0 is set to 0. Every other open, in-progress or blocked P0 is set to 1. Closed and deferred issues are not rewritten. An issue whose title or a label marks main failing the gate by itself stays P0 wherever it sits, and is not raised to P0 when it sits off the path: it blocks every landing, which is a different reason.

When the path is non-empty and has no ready leaf, nothing in progress on it or on an epic that holds it, and no epic there that a split or close round would take, the loop files one task under the target, once while one is open. Its title starts `No progress possible toward `, and it names the cycle over blocks and parent edges, or the blocking issues when there is no cycle. It does not carry the target label. It is on the path, so a round takes it next. Only a stall a round cannot resolve becomes a question to the human.

A P0 leaf is still taken before a P0 epic. A P0 epic round, split or close, is taken before any non-P0 leaf, and a finished epic is still closed before a split. Stage hand-offs stay first. `--check` prints the target, the path size, the priority changes and the stall state, and changes nothing. No target, or more than one, changes nothing.

## Context

Priorities were set by hand. P0 then sat on work off the trunk, while the work the target waits on was hidden by a cycle that runs through a parent edge: an epic waits on an issue that waits on one of that epic's descendants. Ready lists nothing behind a blocked ancestor, so every worker took other leaves and the trunk did not move.

## Reasoning

The ordering the loop already had, P0 before everything else, is worth keeping. What was missing is a rule for which issues are P0. The path is that rule, because an issue the target does not wait on cannot be the next step toward it, and an issue the target does wait on is that step whatever priority a hand edit left it at.

The epics that hold a path issue are on the same ordering. A close or a split of one of them is how the path gets shorter, and a P0 epic round is what runs that ahead of unrelated leaves. The root is the exception: no round splits or closes it, so changing its priority would only move a number nothing reads.

The stall is one issue rather than a stop, because a cycle or a blocker is something a round can still break. Filing it under the target puts it on the path, which is what makes the next round take it. Filing a second while one is open would hand every worker the same stuckness.

## Alternatives rejected

- **Priorities set by hand.** They drift. P0 collected on work the target does not wait on, and the trunk's priority was left wherever the last edit put it.
- **P0 only on the issues the closure names, not on the epics that hold them.** An epic that is not itself a blocker then stays off P0, and the close and split rounds of the epic that holds the path lose the ordering that would have taken them ahead of unrelated leaves.
- **Demoting the root with everything else off the path.** The root is never a split or a close round, so its priority orders nothing. It is left as it stands.
- **Filing the stall as a blocked question at once.** A round can still name the cycle and break it. A question is what remains when that round cannot.
- **Making the stall issue inherit the target's labels.** It would be a second epic labelled target, and the pre-check, which changes nothing when more than one target is marked, would stop setting P0.

## What this does not settle

- Which epic carries the label. Marking it, or moving it, is the human's decision, as a new top-level epic is.
- Whether the target's blocks-dependencies and children cover what its acceptance criteria ask. That is checked when the epic is reviewed.
- What a round does with a stall it cannot resolve. That becomes a question to the human, filed from the round, not by this pre-check.
