---
title: "A change to only what no gate step reads lands without a gate"
date: 2026-11-11
status: active
tags: [process, gate, landing]
one_line: "tools/land.py lists the paths no gate step reads (.claude/agents/, .claude/skills/, CLAUDE.md, and the loop and status tools); a change that touches nothing else, with no file over the size limit and no source that fails to state an allowed license, is rebased, merged and pushed without running the gate, and its tree takes the base's verdict in the ledger."
revisit_if: "A gate step starts reading a listed path, which removes the path from the list in the same commit; or a main that fails by itself is traced to a commit that landed this way."
confidence: "An argument, not a measurement: the gate's result is a function of the files its steps read. That no step reads the listed paths was checked by search on the day, and nothing in the gate keeps it true."
---

## Decision

`tools/land.py` holds a list, `UNREAD`, of the paths no gate step reads: `.claude/agents/`, `.claude/skills/`, `CLAUDE.md`, and the tools people and loops run around the gate: `tools/loop.py`, `tools/bead-status.py` with its page `tools/bead-status.html`, `tools/round-status.py`, `tools/token-ledger.py`, `tools/leaf-cost.py`, `tools/reviews.py` and `tools/review-evidence.py`. When every path a branch changes since the main it was rebased onto is on the list, no file it leaves is over the gate's size limit, and every source it leaves states a license the allowlist passes, the tool does not run the gate. It rebases, merges into main as a fast-forward and pushes as for any change, and its last line says the commit landed without a gate.

The ledger gets the new tree with the verdict of the base, when the base has one. The gate would say of that tree what it said of the base, so a later change that fails on it is blamed as it would be on the base, and the commit is not listed among a broken main's suspects.

A change that touches anything else is gated whole.

## Context

A commit landed by running the whole gate whatever it changed. A change to the round procedure, `.claude/agents/round.md`, waited 271 s on 2026-11-10 for a build, two verifies and six boots, none of which opens that file.

## Reasoning

The gate's result depends only on the files its steps read. A change to no such file cannot turn a pass into a fail or a fail into a pass, so the gate adds no evidence about it and its base's verdict stands for it.

Two gate steps read every file. The size check refuses a file over 1 MiB. The source license check holds every source file, by its name or its `#!` line, to stating its license (`design/license-stated-in-every-source-file/`). The tool asks both questions itself of the files the change leaves, the second through `tools/check-spdx.py`'s own scan against `tools/license-allowlist`, and gates the change when a file is over the limit or a source does not state an allowed license, so the gate reports it as it would have.

The list was checked by searching what the gate runs (`tools/`, `.claude/hooks/`) for each path. For the first three the matches are comments that cite `CLAUDE.md`, and one hook test that passes the string `CLAUDE.md` to the license guard as a path to judge, which the guard does not open. The tools on the list are named only by one another and by comments in the actor hook; no step runs or imports them.

What tests a change to these files is a session or a round running under it, and for a tool its own `--test`, which the round runs before it commits. The gate never did either.

## Alternatives rejected

- **Gate everything.** One rule and no list to keep true, at the cost of a gate's length for a result known beforehand.
- **A reduced gate per kind of path**, such as only the design index check for a change under `design/`. It needs a map from paths to the steps that read them, kept true as steps change. The list here is the case where that map is empty.
- **Deciding per landing**, by a flag the round passes. The round would be judging its own change exempt; the list is decided once, in a commit that is itself gated.

## What this does not settle

`design/`, which the index check reads, and the documentation outside the list. Each joins the list only by a commit that shows no step reads it.
