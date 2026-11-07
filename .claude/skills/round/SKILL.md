---
name: round
description: Run one round of the Atmosphere Beads discipline in a fresh subagent, and under /loop /round start the next round when one finishes. Use only when the user invokes /round, or /loop /round to run rounds until everything open is blocked on the human.
---

# The driver

The procedure is `.claude/agents/round.md`. This skill spawns that agent so every round starts with a fresh context, relays its report, and keeps the loop going. It reads no issue and touches no file itself.

## On `/round`, and on each wakeup under `/loop /round`

1. `ListAgents`. If a round agent is still running, spawn nothing: under `/loop`, `ScheduleWakeup` with a long delay (3600 s), `noop: true`, the same `/round` prompt, reason `round agent still running; fallback`. End the turn.
2. Otherwise spawn the agent: `Agent` with `subagent_type: "round"` and the prompt `Run one round.` It runs in the background. Under `/loop`, schedule the same fallback wakeup. End the turn; the hand-back re-invokes this session.

## On the hand-back

1. Print the agent's report as it came.
2. For each line under `Notify:`, send it with `PushNotification` where the harness has that tool.
3. If the report's last line is `Loop: stop`, or if not under `/loop`: `bd show` each issue in `bd list -s blocked` when stopping, send one PushNotification, `round loop stopped: <n> questions in bd list -s blocked`, and under `/loop` end the loop (`ScheduleWakeup` with `stop`).
4. Otherwise spawn the next round at once, as above, and schedule the fallback wakeup.

A wakeup that finds no agent running and no hand-back received means the round died; the next round's orient recovers what it left. Ask nothing that is not in `bd list -s blocked`.
