---
name: round
description: Run one round of the Atmosphere Beads discipline. Takes the next ready issue and discards, redefines, splits or implements it; with no ready leaf, runs a skeptic pass or a split round on an epic. Use only when the user invokes /round, or /loop /round to run rounds until everything open is blocked on the human.
---

# One round

The rules are in `CLAUDE.md`; this is the procedure. A round moves exactly one issue by exactly one action. Beads is at `~/atmosphere.src/.beads`; `bd` finds it from any worktree. If the context is fresh, run `bd prime` first.

## 1. Orient

```
bd ready --exclude-type=epic     # ready leaves, highest priority first
bd list -s blocked               # questions waiting on the human
bd list -s in_progress           # a round that did not finish
```

`bd ready` without the filter also lists open epics. A round never takes an epic from that list.

Rounds run one at a time, so an issue in progress at orient was left by a round that did not finish, unless a round handed it to a background agent that is still running (the prover, `ListAgents` or the harness shows it): leave that one alone. For each of the others: `bd update <id> --append-notes "Recovered at orient: worktree ~/atmosphere.src/<id> <absent | exists, N commits past main, M files changed>"` (from `git -C ~/atmosphere.src/<id> log --oneline main..HEAD | wc -l` and `git -C ~/atmosphere.src/<id> status --short | wc -l`), then `bd update <id> -s open`. The round that takes it re-reads it and starts from that worktree (section 5). Then pick.

## 2. Pick

- A ready leaf: take the first line. `bd show <id>` and `bd show <parent>`. Read the description, the acceptance criteria, the design notes and the parent epic's tier, even if you remember them: an issue that was blocked and is ready again may have a changed premise. Claim it: `bd update <id> --claim`.
- No ready leaf: section 6.
- No epic qualifies there either: section 8.

## 3. Decide one action

- Discard. The issue is no longer part of the work: not derivable from the star, superseded, or already true. `bd close <id> --reason "<why>"`.
- Redefine. The outcome or the acceptance criteria do not decide success. Rewrite them: `bd update <id> --description "..." --acceptance "..." --design "..."`, then `bd update <id> -s open`. The code starts on a later round.
- Split. The issue is more than one independent change. One child per piece: `bd create "<title>" -t task --parent <id> -d "<what and why>" --acceptance "<what a skeptic checks, and from which evidence>"`, each stating the tier it inherits. `bd dep add <blocked> <blocker>` only where one piece blocks another. Then `bd update <id> -t epic -s open` so the parent leaves the leaf list.
- Implement. The issue is one discrete change: section 4.

Discard, redefine and split do not commit.

## 4. Implement

1. Worktree: `git -C ~/atmosphere.src/main worktree add ../<id> -b <id> main`; work in `~/atmosphere.src/<id>`, where `<id>` is the issue id. Verus is built once, under main; link it so the gate runs here: `ln -s ../../main/tools/verus ~/atmosphere.src/<id>/tools/verus`.
2. Sources: before reading an external source for the first time, check its license and record the source and the license on the issue with `bd update <id> --append-notes "..."`. Never open a forbidden source (CLAUDE.md, License).
3. Test first, at the epic's tier: a Verus specification and proof for tier 1; a test that reaches the branch, with fault injection where nothing else reaches it, for tier 2; the best test reasonable for tier 3. Run it and see it fail, make the change, see it pass. For tier 1, when the first verify after the change fails, delegate the proof search to the prover agent (`.claude/agents/prover.md`) with the issue id, the worktree path, the failing `atmo verify` output, the target line and the change so far; it works in that worktree and reports the verify line it reached. One prover run ends the attempt (the bound below): continue to the gate if the target is reached, otherwise record its report as the attempt.
4. Anything the issue did not name (a dependency, a bug, more complexity, a decision only the human can make) goes through section 5. Do not widen the change.
5. Gate: `source tools/env.sh`, then `atmo test`. Record the command and its result on the issue.
6. Commit: one logical change per commit; the message says why; the trailer the harness asks for. If the message needs "and", make two commits, each building on its own.
7. Land: `git -C ~/atmosphere.src/main merge --ff-only <id>`. If main moved, `git rebase main` in the worktree, run the gate again, merge again. Then `git -C ~/atmosphere.src/main push origin main`, `git -C ~/atmosphere.src/main worktree remove ../<id>`, `git -C ~/atmosphere.src/main branch -d <id>`.
8. Close: `bd close <id> --reason "<sha>: <evidence>"`. The reason names every commit SHA and the evidence a skeptic will want: verify counts, the serial log line with dom0's exit, where the test output is.

An attempt is bounded. When ten runs of the tier's check (`atmo verify` for tier 1, the test for tiers 2 and 3) have not reached the gate, stop: `bd update <id> --append-notes "Attempt <n>: <what was tried>; closest result: <the verify line or the test output>; next: <what a further attempt would try, as lemma statements for tier 1>"`, keep the worktree, `bd update <id> -s open`, and end the round with the report. The round that takes it next starts from that worktree (section 5). A leaf whose notes hold two attempts is a decision only the human can make (section 5); the question names both attempts and the options: a third attempt (budget), a split into the lemmas the notes name (more rounds, smaller proofs), a deferral (the error stays in the allowance), or a tier change (unverified code; the human's by principle 3).

## 5. The stack

- A discovered issue: `bd create "<title>" -t task --parent <epic of the current issue> -d "Discovered from <current>: ..." --acceptance "..."` (type `bug` for a bug), then `bd dep add <current> <new>`: the current issue depends on the new one. Set the current issue back with `bd update <current> -s open`; it leaves `bd ready` because it is blocked. Keep its worktree if the change so far is still wanted. End the round with the report. The next round takes the new issue; when that closes, the current issue is ready again, and the round that takes it re-reads it before resuming, rebasing its worktree on main or removing it.
- A bug's commit includes the test that exercises the bug.
- A decision only the human can make: `bd update <id> --append-notes "Question for the human: <the question, the options, what each implies>"`, then `bd update <id> -s blocked`. Its dependents stay blocked through it. Where the harness has a PushNotification tool, send one line, `<id> needs a decision: <the question's first clause>`; where it has none, skip this. Nothing else changes; end the round with the report.

## 6. Epic rounds (no ready leaf)

Consider the open epics other than the star, shallowest first. Depth is the number of dots in the id: `atmo-1ab` is the star, `atmo-1ab.5` depth 1, `atmo-1ab.5.3` depth 2. `bd list -t epic`, then `bd show <id>`.

- Skeptic pass: an epic with at least one child and no open child. Spawn a reviewer with no prior context (a fresh subagent given only the epic's acceptance criteria, its tier, and where the evidence is: `bd show` of each closed child, the commit SHAs, `atmo test` and `atmo verify` output, serial logs). It tries to refute each criterion from that evidence. If every criterion survives, `bd close <epic> --reason "skeptic pass: <summary>"`. A refuted criterion keeps the epic open and becomes a leaf under it, the refutation as its description.
- Split round: the shallowest open epic with no ready children that is not blocked on the human. Write its leaves, each with a description, acceptance criteria a skeptic can check from evidence, and the tier; `bd dep add` only where one blocks another. If a leaf cannot be written without a decision only the human can make, record the question on the epic and mark it blocked, with the notification of section 5.
- The star never closes and never gets a split round. Its children are the human's decision.

## 7. Report

End every round with: the issue (id and title), the action taken, the commit SHAs if any, the first lines of `bd ready --exclude-type=epic`, and the open questions from `bd list -s blocked`.

## 8. Under /loop

- Stop condition: no leaf is ready, no epic qualifies for a skeptic pass or a split round, and every open issue other than the star is blocked on the human (status blocked, with a recorded question) or blocked only by such issues. Then print every question in full (`bd show` each blocked issue), send one PushNotification, `round loop stopped: <n> questions in bd list -s blocked`, and end the loop (ScheduleWakeup with stop). There is no other stop; the human monitors budget.
- Otherwise schedule the next round at the shortest delay the runtime allows, with the same `/round` prompt.
