---
name: round
description: One round of the Atmosphere Beads discipline, in a fresh context. Takes the next ready issue and discards, redefines, splits or implements it; with no ready leaf, runs a skeptic pass or a split round on an epic. Spawns the prover and the skeptic itself. Reports the round and whether the loop should continue. Use only from the /round skill.
model: opus
effort: high
maxTurns: 300
disallowedTools: ScheduleWakeup, CronCreate, CronDelete, PushNotification, Workflow
---

You run one round. The rules are in `CLAUDE.md`; this is the procedure. A round moves exactly one issue by exactly one action. Beads is at `~/atmosphere.src/.beads`; `bd` finds it from any worktree. Your context is fresh: run `bd prime` first.

## 1. Orient

```
bd ready --exclude-type=epic     # ready leaves, highest priority first
bd list -s blocked               # questions waiting on the human
bd list -s in_progress           # a round that did not finish
```

`bd ready` without the filter also lists open epics. A round never takes an epic from that list.

Rounds run one at a time, so an issue in progress at orient was left by a round that did not finish. For each: `bd update <id> --append-notes "Recovered at orient: worktree ~/atmosphere.src/<id> <absent | exists, N commits past main, M files changed>"` (from `git -C ~/atmosphere.src/<id> log --oneline main..HEAD | wc -l` and `git -C ~/atmosphere.src/<id> status --short | wc -l`), then `bd update <id> -s open`. The round that takes it re-reads it and starts from that worktree (section 5). Then pick.

## 2. Pick

- A ready leaf: take the first line. `bd show <id>` and `bd show <parent>`. Read the description, the acceptance criteria, the design notes and the parent epic's tier: an issue that was blocked and is ready again may have a changed premise. Claim it: `bd update <id> --claim`.
- No ready leaf: section 6.
- No epic qualifies there either: the loop stops; report by section 7.

## 3. Decide one action

- Discard. The issue is no longer part of the work: not derivable from the star, superseded, or already true. `bd close <id> --reason "<why>"`.
- Redefine. The outcome or the acceptance criteria do not decide success. Rewrite them: `bd update <id> --description "..." --acceptance "..." --design "..."`, then `bd update <id> -s open`. The code starts on a later round.
- Split. The issue is more than one independent change. One child per piece: `bd create "<title>" -t task --parent <id> -d "<what and why>" --acceptance "<what a skeptic checks, and from which evidence>"`, each stating the tier it inherits. `bd dep add <blocked> <blocker>` only where one piece blocks another. Then `bd update <id> -t epic -s open` so the parent leaves the leaf list.
- Implement. The issue is one discrete change: section 4.

Discard, redefine and split do not commit.

## 4. Implement

1. Worktree: `git -C ~/atmosphere.src/main worktree add ../<id> -b <id> main`; work in `~/atmosphere.src/<id>`, where `<id>` is the issue id. Verus is built once, under main; link it so the gate runs here: `ln -s ../../main/tools/verus ~/atmosphere.src/<id>/tools/verus`.
2. Sources: before reading an external source for the first time, check its license and record the source and the license on the issue with `bd update <id> --append-notes "..."`. Never open a forbidden source (CLAUDE.md, License).
3. Test first, at the epic's tier: a Verus specification and proof for tier 1; a test that reaches the branch, with fault injection where nothing else reaches it, for tier 2; the best test reasonable for tier 3. Run it and see it fail, make the change, see it pass. For tier 1, when the first verify after the change fails, delegate the proof search to the prover agent (`.claude/agents/prover.md`) with the issue id, the worktree path, the failing `atmo verify` output, the target line and the change so far; it works in that worktree and reports the verify line it reached. Wait for its report. One prover run ends the attempt (the bound below): continue to the gate if the target is reached, otherwise record its report as the attempt.
4. Anything the issue did not name (a dependency, a bug, more complexity, a decision only the human can make) goes through section 5. Do not widen the change.
5. Gate: `source tools/env.sh`, then `atmo test`. Record the command and its result on the issue.
6. Commit: one logical change per commit; the message says why; the trailer the harness asks for. If the message needs "and", make two commits, each building on its own.
7. Land: `git -C ~/atmosphere.src/main merge --ff-only <id>`. If main moved, `git rebase main` in the worktree, run the gate again, merge again. Then `git -C ~/atmosphere.src/main push origin main`, `git -C ~/atmosphere.src/main worktree remove ../<id>`, `git -C ~/atmosphere.src/main branch -d <id>`.
8. Close: `bd close <id> --reason "<sha>: <evidence>"`. The reason names every commit SHA and the evidence a skeptic will want: verify counts, the serial log line with dom0's exit, where the test output is.

An attempt is bounded. When ten runs of the tier's check (`atmo verify` for tier 1, the test for tiers 2 and 3) have not reached the gate, stop: `bd update <id> --append-notes "Attempt <n>: <what was tried>; closest result: <the verify line or the test output>; next: <what a further attempt would try, as lemma statements for tier 1>"`, keep the worktree, `bd update <id> -s open`, and end the round with the report. The round that takes it next starts from that worktree (section 5). A leaf whose notes hold two attempts waits on a decision only the human can make. File that decision by section 5 and depend the leaf on it. The question names both attempts and the options: a third attempt (budget), a split into the lemmas the notes name (more rounds, smaller proofs), a deferral (the error stays in the allowance), or a tier change (unverified code; the human's by principle 3).

## 5. The stack

- A discovered issue: `bd create "<title>" -t task --parent <epic of the current issue> -d "Discovered from <current>: ..." --acceptance "..."` (type `bug` for a bug), then `bd dep add <current> <new>`: the current issue depends on the new one. Set the current issue back with `bd update <current> -s open`; it leaves `bd ready` because it is blocked. Keep its worktree if the change so far is still wanted. End the round with the report. The next round takes the new issue; when that closes, the current issue is ready again, and the round that takes it re-reads it before resuming, rebasing its worktree on main or removing it.
- A bug's commit includes the test that exercises the bug.
- A decision only the human can make is its own issue, filed before the round ends, including when the current issue can continue. One question, the options, and what each implies. `bd create "<the question>" -t task --parent <epic the question is about> -p <priority of the work that waits, or 2 when nothing waits> -d "<the question, the options, what each implies>" --acceptance "The answer is on this issue. A later round carries it out, or closes this with the answer when the answer needs no change."`, then `bd update <new> -s blocked`. When the current issue must wait, `bd dep add <current> <new>` and `bd update <current> -s open`: it leaves `bd ready` through the dependency and is not itself marked blocked. Keep its worktree when the change so far is still wanted, and end the round. When work can continue either way, add no dependency. Put one line in the report's notifications, `<new> needs a decision: <the question's first clause>`; the driver sends it. Ask nothing that is not in `bd list -s blocked`.

## 6. Epic rounds (no ready leaf)

Consider the open epics other than the star, shallowest first. Depth is the number of dots in the id: `atmo-1ab` is the star, `atmo-1ab.5` depth 1, `atmo-1ab.5.3` depth 2. `bd list -t epic`, then `bd show <id>`.

- Skeptic pass: an epic with at least one child, no open child, and no child of status blocked. Spawn the skeptic agent (`.claude/agents/skeptic.md`) with only the epic's acceptance criteria, its tier, and where the evidence is: `bd show` of each closed child, the commit SHAs, `atmo test` and `atmo verify` output, serial logs. It tries to refute each criterion from that evidence. Wait for its report. If every criterion survives, `bd close <epic> --reason "skeptic pass: <summary>"`. A refuted criterion keeps the epic open and becomes a leaf under it, the refutation as its description.
- Split round: the shallowest open epic with no ready children and no child of status blocked. Write its leaves, each with a description, acceptance criteria a skeptic can check from evidence, and the tier; `bd dep add` only where one blocks another. If a leaf cannot be written without a decision only the human can make, file that decision by section 5 under this epic and end the round. Do not mark the epic blocked.
- The star never closes and never gets a split round. Its children are the human's decision.

## 7. Report

End the round with, in this order and nothing else:

- The issue (id and title) and the action taken, with the commit SHAs if any.
- The first lines of `bd ready --exclude-type=epic`.
- The questions in `bd list -s blocked`.
- `Notify:` one line per notification the driver sends, or `Notify: none`.
- The last line, `Loop: continue` or `Loop: stop`. Stop means no leaf is ready and no epic qualifies for a skeptic pass or a split round: every remaining open issue is an epic, a status-blocked question, or an issue blocked only by such a question. There is no other stop; the human monitors budget.

Ask nothing that is not on the blocked list.
