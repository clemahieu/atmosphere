# design/

One directory per decision. `INDEX.md` is generated and is the entry point for a reader who wants to know what was decided without opening anything.

```
design/<slug>/DECISION.md   one per decision: frontmatter, then the reasoning
design/INDEX.md             generated from the frontmatter of every DECISION.md
design/README.md            this file
```

Regenerate the index with `tools/build-design-index.py`; `tools/build-design-index.py --check` says whether it is current. Never hand-edit `INDEX.md`.

## What a record is

`CLAUDE.md` holds the principles: what the project is for and the rules every issue must be derivable from. A record here holds a choice made under those principles: what we do, why, what we rejected, and what would make the choice wrong. The code and its comments say what the tree does; a record says why it does it that way rather than the way someone arriving fresh would propose.

A record is not evidence. It is an account of a choice made on the information available at the time, under constraints that may not outlive it. Where its reasoning rests on a measurement, the measurement is in the record with its numbers and how it was taken, and that part can be rechecked. The choice built on it is a judgement, and the record says so.

The test for whether something belongs here: would someone arriving fresh be likely to propose the alternative, and would explaining why not take more than a line? If yes, write the record. A decision whose rationale is obvious from the code does not need one.

## One question per record

Each record settles one question and is named for that question, not for the component it lives in and not for the outcome: `revoke-by-depth-first-list`, not `capability-list`. Two records do not decide the same thing from two angles. When a choice follows from another record, the body links it rather than restating it, so that revising the one does not leave the other quietly contradicting it. If a new record would overlap an existing one, revise the existing one instead.

## Revising a record

Revise in place. A record always describes what we do today. Git history is the archive: `git log -p design/<slug>/` recovers every earlier version with the commit message that says why it changed. Do not leave the superseded reasoning in the file struck through or labelled "formerly".

The exception is the reversal that is itself load-bearing: the abandoned approach is attractive enough that someone would otherwise re-propose it. Then the fact that we tried it and why we stopped is the current decision, and it belongs in the body, stated positively. Set `status: superseded` only when we have stopped doing something and put nothing in its place, and the record exists to stop it coming back. Otherwise `status: active`.

## The shape of a DECISION.md

```yaml
---
title: "Revoke walks a depth-first list, so a lineage is a run"
date: 2026-11-06
status: active
tags: [capability, revoke, verified]
one_line: "Every capability, mapping and binding is a node of one doubly linked list in depth-first order; a node's descendants are the run after it with greater depth, so revoke needs no scan, mark or cursor."
revisit_if: "A capability needs more than one parent, or a lineage must survive its grantor, which the list cannot express."
confidence: "Proven in the tree: the list's invariants and revoke's exact lineage verify."
---
```

- `title` states the decision as a sentence.
- `date` is when the decision was made or last revised.
- `status` is `active` or `superseded`.
- `tags` are lowercase words; the index groups by them.
- `one_line` is what the index shows. State the decision, not the topic, so a reader scanning the index can tell whether this is the record they want.
- `revisit_if` names the condition that would make the choice wrong, concretely enough to be checked. "If requirements change" is not an answer. A decision that follows from something fixed says so rather than leaving the field empty.
- `confidence` is optional: one line on how well founded the choice is, not how firmly we mean to keep it. Some decisions are arithmetic; others are bets a project places because it has to pick something. Say which, and for a bet say what would settle it.

Body sections, in this order, none mandatory:

- **Decision**: what we do, stated flatly enough to act on without reading the rest.
- **Context**: what made this a decision rather than a default.
- **Reasoning**: why, with the measurements that support it and their numbers.
- **Alternatives rejected**: each with the reason. This is the part neither the code nor the commit history preserves.
- **What this does not settle**: the open edges, so nobody reads the record as deciding more than it did.

A number in a record says what was measured, on what, and how, in enough detail to re-run. Where a script produced it, name the script. Say plainly when something is judgement; it usually is.

## What does not go here

Tracker issues are private and close; a record never cites one. The tree's own files are cited by path, and a comment in the tree that explains a design choice points at the record by path, `design/<slug>/`, not at an issue. Facts about the hardware or the tools, as opposed to choices, belong in the code or in `CLAUDE.md`.
