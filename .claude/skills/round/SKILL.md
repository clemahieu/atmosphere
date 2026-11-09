---
name: round
description: Run one round of the Atmosphere Beads discipline in a fresh subagent, and under /loop /round start the next round when one finishes. Use only when the user invokes /round, or /loop /round to run rounds until everything open is blocked on the human.
---

# The driver

The procedure is `.claude/agents/round.md`. This skill spawns that agent so every round starts with a fresh context, relays its report, and keeps the loop going. It also runs the prover and the skeptic a round hands it, because a round cannot wait for a background agent; recording their reports on the issue is the only issue it writes, and it touches no file.

## On `/round`, and on each wakeup under `/loop /round`

1. `ListAgents`. If a round, prover or skeptic agent is still running, spawn nothing: under `/loop`, `ScheduleWakeup` with a long delay (3600 s), `noop: true`, the same `/round` prompt, reason `round agent still running; fallback`. End the turn.
2. Otherwise spawn the agent: `Agent` with `subagent_type: "round"` and the prompt `Run one round.` It runs in the background. Under `/loop`, schedule the same fallback wakeup. End the turn; the hand-back re-invokes this session.

## On the hand-back

1. Print the agent's report as it came.
2. For each line under `Notify:`, send it with `PushNotification` where the harness has that tool.
3. If the report's last line is `Loop: stop`, or if not under `/loop`: `bd show` each issue in `bd list -s blocked` when stopping, send one PushNotification, `round loop stopped: <n> questions in bd list -s blocked`, and under `/loop` end the loop (`ScheduleWakeup` with `stop`).
4. If the report's last line is `Loop: wait`, another loop holds the issues in progress and nothing is ready: `ScheduleWakeup` with 900 s, `noop: true`, the same `/round` prompt, reason `nothing ready; another loop holds the issues in progress`. End the turn; that wakeup spawns the next round by the rule above.
5. If the report has a `Prover: <id>` line, spawn `Agent` with `subagent_type: "prover"` and the prompt `Issue <id>, worktree ~/atmosphere.src/<id>. Your input is the issue's last Prover input note.` If it has a `Skeptic: <epic>` line, spawn `Agent` with `subagent_type: "skeptic"` and the prompt `Epic <epic>. Your input is the epic's last Skeptic input note.` Schedule the fallback wakeup and end the turn. On that agent's hand-back, `bd update <id> --append-notes "Prover report: <the report>"` and `bd update <id> -s open --assignee ""` (or `Skeptic report:` on the epic, which stays as it is), then spawn the next round.
6. Otherwise spawn the next round at once, as above, and schedule the fallback wakeup.

A wakeup that finds no agent running and no hand-back received means the round died; the next round's orient recovers what it left. Ask nothing that is not in `bd list -s blocked`.

## On any other message

The harness also sends a task-notification when a round ends, after its hand-back, and an interim one when a round parks on its own background gate. Neither needs anything: end the turn without text, spawning nothing. The hand-back is the one signal that moves the loop; the fallback wakeup covers a round that dies.

## Several loops

Loops run one per terminal, each a session of its own and so its own Beads actor: `.claude/hooks/beads-actor.sh` names the session's process in `BEADS_ACTOR` at session start, and nothing is set by hand. The actor is how a round tells an issue a finished session abandoned from one that another loop is working on; the landing lock in `round.md` keeps their gates and merges from colliding. This driver sees only its own agents, so it needs to know nothing else about the other loops.

The Grok loop is the other driver: a Grok session in `~/atmosphere.src/main` runs `/loop 60s <prompt>`. Every fire is a fresh background subagent of that session, which cannot see the conversation, so the prompt stands alone and names the actor, `grok-<pid>` with the pid of the session's `grok` process (`echo $PPID` from its shell is not it; Grok reports its own pid):

```
/loop 60s Run one round of ~/atmosphere.src/main/.claude/agents/round.md as the Grok round whose actor is grok-<pid>. Put BEADS_ACTOR=grok-<pid> in front of every bd call. Claim with --label grok. Spawn no subagent. End with the round report.
```

A fire still running when the next tick comes is skipped, so rounds run one at a time; the schedule expires after seven days and is started again. The loop has no prover and no skeptic, takes only leaves labeled `grok`, and reports wait rather than stop. While the session lives, `/proc/<pid>/comm` is `grok` and the Claude loops leave its leaves alone; when it ends, a Claude round recovers what it held. The rounds this driver spawns pass a leaf to it by label (`round.md`, section 5).
