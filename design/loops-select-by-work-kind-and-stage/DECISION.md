---
title: "Loops select ready work and model difficulty in Python by work kind and stage, configured in loop.toml"
date: 2026-11-13
status: active
tags: [process, tools, tracker]
one_line: "One driver, tools/loop.py, runs a pool of worker loops sized live by [pool] jobs; each worker inspects Beads in Python at zero token cost and either auto-routes each work kind, epic round and specialist stage to its configured harness and model difficulty under [routes.<key>] in loop.toml (with per-provider quota cooldowns so a rate-limited provider yields to the non-limited provider without stopping the loop) or runs a single slice with --profile <name>."
revisit_if: "One provider and one model become cheap enough to carry every round, proof search and skeptic pass within a single subscription window, so routing across harnesses and models buys nothing; or the heuristic that classifies unlabeled leaves misroutes enough leaves that requiring an explicit kind:* label on every task becomes cheaper."
confidence: "Measured over five days of token-ledger history (774M weighted tokens across 631 leaves and 77 reviews) and meter readings: Fable 5.2 costs 0.57 weekly points per million weighted tokens against Opus 5.5 at 0.12, while round sessions account for 77% of weighted tokens and 62% of leaves touch no Verus specification. How much of that base load a second provider's subscription carries before its own window saturates is settled by running the routed loop under live load."
---

## Decision

One driver script, `tools/loop.py`, inspects Beads in Python at zero token cost and dispatches sessions across harnesses (`claude` and `agy`) and model difficulties from `loop.toml` at the project root.

One invocation is a pool. The pool process runs no session; it keeps `[pool] jobs` worker loops running, each a `tools/loop.py --worker <pool pid>` process, and re-reads the number every few seconds, so concurrency is changed by editing `loop.toml` rather than by opening or closing terminals. Each worker is a whole loop as before: its own Beads actor `loop-<pid>`, its own pid file under `logs/loop/` naming its pool, and the same claim, recovery and wait rules toward its siblings as toward any other loop. The pool passes stop, stop-now and reload on to its workers, stops them all when one finds nothing left but questions, and does not replace a worker that failed until the number changes. Each worker chooses as follows:

- **Automatic routing (`[routes.<key>]`, plain `tools/loop.py` with no `--profile` or `--model` flag).** `[routes]` maps each of the twelve work and stage keys — leaf kinds (`tool`, `sys`, `proof`, `spec`, `arch`, `review`), epic rounds (`epic-close`, `epic-split`), post-prover landing (`needs-land`), and specialist or escalation passes (`prover`, `skeptic`, `retry`), with `[routes.default]` as fallback and `disabled = true` to turn off a route — to its own `harness`, `model`, and `effort`. One `tools/loop.py` invocation determines both what is ready next and which harness and difficulty tier runs it.
- **Named single-slice profiles (`[profiles.<name>]`, `tools/loop.py --profile <name>`).** Each profile names its harness, per-agent flags (`round`, `retry`, `prover`, `skeptic`), the work kinds and stage hand-offs it takes, whether it takes epic close or split rounds (`epics = "none" | "close" | "split" | "all"`), and which specialist hand-offs it delegates (`prover`, `skeptic`, `retry`).

Tasks are classified by what the work is and what stage it has reached, never by a model's name:

- **Work kinds** (`kind:<name>` on new leaves, with `--no-inherit-labels`, or inferred deterministically for unlabeled leaves): `tool` (tier-3 scripts, hooks, UI and docs), `sys` (unverified Rust, platform and boot glue), `proof` (proving an existing tier-1 specification, lemma, witness or `external_body` removal), `spec` (a new tier-1 specification or operation), `arch` (`design/` records and spikes), and `review` (epic skeptic-review leaves, `design/review-is-a-leaf-of-its-epic/`).
- **Stage hand-offs** (`stage:<name>`): `stage:needs-prover` (a round wrote `Prover input:` and delegated or deferred `prover`), `stage:needs-skeptic` (a round matched a review's evidence, wrote `Skeptic input`, and delegated or deferred `skeptic`), `stage:escalated` (a leaf's first attempt reached its ten-run bound and delegated or deferred `retry`), and `stage:needs-land` (a specialist prover finished in the leaf's worktree, leaving triage, the gate and closing).

Before spawning `claude -p` or `agy -p`, a routed or profiled loop inspects Beads in Python at zero token cost: it recovers abandoned `in_progress` issues from dead loops, claims a queued `stage:needs-prover` or `stage:needs-skeptic` issue and invokes that specialist agent directly without a wrapper round, claims a matching `stage:escalated`, `stage:needs-land` or `kind:*` leaf and pins the round prompt to that issue (`Issue <id> is yours`), or starts an epic-only round when `tools/reviews.py` lists finished epics. When nothing in Beads matches, no LLM session is started: the loop waits while another loop or actor is active, and exits cleanly otherwise.

Rate and usage limits are tracked per harness (`claude`, `agy`) in one state file, `logs/loop/state.json`, that the pool and every worker share, written under a lock and replaced atomically: when one worker hits a limit, the cooldown it writes makes every worker skip that harness until its reset timestamp without spending a session on finding the limit again; any pre-claimed issue is released keeping its stage label, in-flight specialist hand-offs targeting the cooled-down harness park on `stage:needs-prover`, `stage:needs-skeptic`, or `stage:escalated`, and ready work routed to the non-limited harness continues immediately. The same file keeps each provider's meters: the pool samples Claude's from `~/.claude.json` and Gemini's from `agy -p /usage`, workers add the readings Claude sessions stream, and each meter keeps its readings history and a rate in percent per hour fitted over the recent readings, split at resets, so pacing sessions to a meter's reset has its rate to work from and the history outlives a restart of the pool.

For `harness = "agy"`, `tools/loop.py` strips the YAML frontmatter from `.claude/agents/<kind>.md` and passes the procedure body with the prompt to `agy -p`, keeping `.claude/agents/` the single source of truth across harnesses.

## Context

Running every round, retry, proof search and skeptic pass on one Anthropic subscription saturated the weekly meter before the week ended, leaving ready leaves unworked while a Google AI Ultra subscription (`agy` with Gemini 4 Carbon) sat idle. Meanwhile, inside the Anthropic allowance itself, Fable 5.2 cost 4.75 times as much per weighted token as Opus 5.5, so spending Fable on mechanical rounds, gating, or routine tool leaves starved the hard proof searches and escalations where Fable pays for itself.

An earlier experiment routed tier-3 issues to a separate model by adding a dedicated driver script, a duplicate procedure file, and a model-named tracker label (`grok`). It was removed a day later when that model proved unreliable on unsupervised rounds: the duplicate script and procedure had already drifted from `tools/loop.py` and `.claude/agents/round.md`, and the model-named label coupled tracker state to one vendor's product name.

## Reasoning

Measured on 2026-11-13 from `logs/token-ledger.sqlite` (`tools/token-ledger.py` and `tools/leaf-cost.py`) and one `bd list --all --json`:

- Across 774.2M weighted tokens recorded in the ledger, `round` accounted for 596.9M (77.1%), `skeptic` for 116.5M (15.0%), `prover` for 17.8M (2.3%), and interactive sessions for the remainder.
- Meter fittings in `tools/leaf-cost.py` put Opus 5.5 at 0.12 weekly points per million weighted tokens and Fable 5.2 at 0.57. A single Fable round of 2.5M weighted tokens costs 1.4 weekly points; reserving Fable for `stage:needs-prover`, `stage:escalated`, and open-oracle `spec` work preserves that budget for proof search while moving mechanical rounds off it.
- Across 631 closed leaves with ledger rows, 62% were tier-3 tooling, unverified platform glue, or closed-oracle tier-1 proofs that never invoked `prover`. Even within a tier-1 leaf that does invoke `prover`, reading, editing, running `tools/land.py` across the gate, and closing are distinct stages from the 25-run Verus search itself, which `stage:needs-prover` and `stage:needs-land` separate cleanly across loops.
- Checking Beads in Python before spawning a headless CLI session costs zero tokens when a specialist profile (`fable` or `opus`) has no matching stage or leaf ready, instead of paying ~90K cached input tokens per idle `Loop: wait` check.

Concurrency is the lever that keeps the subscriptions under their limits: one number moves every provider's spend together, and later pacing changes the number rather than each loop's choice of work. Workers stay separate processes, not threads of the pool, because the Beads actor is per process (the hook reads the pid), a session's process group is ended by its own loop's signal, and a worker that crashes takes no sibling with it.

Keeping one `tools/loop.py` binary preserves `loop_alive(pid)` (`/proc/<pid>/cmdline` ending in `tools/loop.py`), which `--stop`, `--reload`, peer-loop detection, and `.claude/agents/round.md` orient recovery all rely on.

## Alternatives rejected

- **One script per loop flavor (`tools/loop-carbon.py`, `tools/loop-fable.py`).** Duplicates signal handling, PID tracking, stream parsing, backoff and tests across files, and breaks `loop_alive(pid)` unless every recovery check learns every script name.
- **Model-named labels on issues (`carbon`, `fable`, `opus`).** Couples the issue tracker to today's model names and subscription tiers; every model release or quota shift requires relabeling open issues instead of editing `loop.toml`.
- **A second copy of `round.md` for `agy`.** Tried for the earlier Grok loop and drifted within a day. Passing the body of `.claude/agents/<kind>.md` directly to `agy -p` keeps one procedure.
- **Several loops started by hand, one per terminal.** Concurrency then changes only by starting or stopping terminals, so nothing in the script can adjust it to the meters, and stopping or reloading them all is a per-terminal chore.
- **Threads inside one loop process.** Every thread would share one pid and so one Beads actor, which breaks orient's rule that an issue in progress under your own actor was left by this loop.
- **Letting the LLM check whether matching work exists.** Each idle wake-up loads rules and procedures into context only to emit `Loop: wait`. Querying `bd` in Python before starting a session makes idle specialist loops free.

## What this does not settle

- Whether Gemini 4 Carbon writes open-oracle tier-1 specifications (`kind:spec`) that survive the Opus skeptic at the same rate as Opus 5.5; `loop.toml` can keep `spec` on `fable` or `opus` until replayed leaves measure that rate.
- Harvesting `agy` transcripts into `logs/token-ledger.sqlite`: `tools/loop.py` logs each `agy` session's turns and weighted tokens from `stream-json`, while `tools/token-ledger.py` currently harvests `~/.claude/projects` alone.
