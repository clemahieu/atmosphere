#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The round loop, driven from the command line.

Each round runs in the main worktree as a fresh headless agent session (`claude -p --agent round` by
default, or `agy -p` or `grok -p` with the body of `.claude/agents/<kind>.md` when the offering chosen has
`harness = "agy"` or `harness = "grok"`).
Print mode waits for a background command the round started, such as its landing, and wakes the round
when it exits, so the last result the session streams is the round's report. The report's lines say what
comes next, as the round skill reads them (.claude/skills/round/SKILL.md):

- `Notify: <text>` (or bullets under a bare `Notify:`), each sent with notify-send and printed;
- `Prover: <id>` runs the prover agent on the first of its candidates not cooled down (or stamps
  `stage:needs-prover` when the route is disabled or every candidate is cooled down), then appends its report to the issue as `Prover report:` and sets the issue open; `Skeptic: <review>`
  does the same with the skeptic (`stage:needs-skeptic` when disabled or cooled down);
- `Retry: <id>`, from a round whose attempt on a leaf ended at its bound, makes the next session a
  retry (or stamps `stage:escalated` when `retry` is disabled, or when a routed loop finds every retry
  candidate cooled down): a round whose prompt
  names that issue, so it takes that issue and no other, with the flags of the retry table or on the
  first retry candidate not cooled down;
- `Loop: continue` starts the next round, `Loop: wait` waits (another loop holds the issues in
  progress), `Loop: stop` prints the questions waiting on the human and ends the loop.

One invocation is a pool of loops. The pool runs no session itself: it keeps `jobs` worker loops
running, each a `tools/loop.py --worker <pool pid>` process in its own session, and re-reads `[pool] jobs`
in <project root>/loop.toml every 5 s (1 when the table is absent). A larger number starts workers; a
smaller one stops the newest after their run in flight. Each worker is one Beads actor, loop-<pid>, for
every session it runs (.claude/hooks/beads-actor.sh), so an issue a round hands to the prover, or leaves
for a retry, stays held between the two sessions, and workers of one pool claim, recover and wait on
one another as separate loops do. A worker that stops by itself because nothing is left (`Loop: stop`, or
no matching work with no other loop active) exits with status 3, and the pool then stops the others and
ends with status 0. A worker that ends with status 1 (four failures in a row, or a configuration error)
is not replaced until `jobs` changes; the pool ends with status 1 when no worker is left. Workers' lines
carry their pid after the time.

Each session's temporary directory is <project root>/scratch, on disk: the loop sets TMPDIR, which the
session's commands read, and CLAUDE_CODE_TMPDIR, under which Claude Code keeps the session's scratchpad
and the output of its background commands.

Automatic routing and zero-token pre-filtering (`design/loops-select-by-work-kind-and-stage/`).
`[offerings.<name>]` in <project root>/loop.toml names one way to run a session: `harness`, `model`,
`effort`, `autocompact`, and `meters`, the usage meters the offering draws on (`claude-week` and
`claude-fable` for Fable; `gemini-week` and `gemini-5h` for a Gemini model; a `grok-<name>` of the
file's own choosing for Grok). When `[routes]` is defined,
`tools/loop.py` inspects Beads in Python at zero token cost and dispatches
each ready stage, leaf, or epic round by its route `[routes.<key>]` (`default`, `tool`, `sys`, `proof`,
`spec`, `arch`, `review`, `epic-close`, `epic-split`, `needs-land`, `prover`, `skeptic`, `retry`), which
holds `candidates`, the offerings capable of that work, cheapest first, or `disabled = true`. At claim,
and for each hand-off, the work goes to the first candidate free to take it: none of its meters, nor its
harness as a whole, is cooled down, and each of its meters that `[meters.<name>]` paces admits one more
session than the loops have in flight on it, counted from the pid files. When no candidate is free, the
work waits, for the earliest reset when only cooldowns keep it and at most PACE_WAIT s when a pace does,
and `--check` names each cooldown or pace it waits on. A key left out takes `default`'s candidates, or none when `default` is
left out too. A candidate that is not under `[offerings]` is an error. When nothing matches, no LLM
session is started: the loop waits if another loop or actor is active, and stops otherwise. Without
`[routes]`, the loop runs plain rounds on Claude with the top-level tables' flags.

Pacing (`[meters.<name>]`, with `target` and `max`). A meter at p percent, its reset h hours away, with
r its fitted rate a session in flight, admits floor((target - p) / (h * r)) sessions at once, clamped to
[0, max]: the use those sessions project to the reset stays under the target. A meter at or past its
target admits none; one with no readings, no rate yet, or a window that has reset since the last
reading admits max; a meter no table names is not paced. r is the meter's fitted rate over the mean
number of the loops' sessions in flight on it at the readings it was fitted over, a mean under one
counting as one, so use from outside the loops is charged to the sessions. The pool recomputes every
paced meter's admission each tick and logs each change with p, h and r; each worker recomputes it
before it chooses. Two workers choosing at the same instant may both take a meter's last place.

Shared meter and cooldown state. The pool and its workers share `<project root>/logs/loop/state.json`,
updated under `<project root>/logs/loop/.state.lock` and replaced atomically so readers never see half a
file and the readings history survives a supervisor restart. The pool samples Claude's meters from
`~/.claude.json` (`cachedUsageUtilization`: `claude-week`, `claude-5h` when the plan has a five-hour
window, and each scoped model limit `claude-<model>` such as `claude-fable`) and Gemini's buckets from
`agy -p /usage --output-format json` (`Gemini Models`: `gemini-week` and `gemini-5h`, keeping the last
readings when `/usage` fails); workers also record `rate_limit_event` readings streamed by Claude
sessions and write a usage-limit cooldown immediately. A limit cools the meter its stream names, or,
when it names none, every meter the offering draws on; when the meter that refused is not one the
offering declares, the harness as a whole is cooled too, since the declaration missed it. The unrouted
loop's tables declare no meters, so their limit cools the whole harness. Every worker reads
this file before claiming or starting a session: when one worker hits a usage limit, every worker passes
over the offerings that draw on the cooled meter until its reset without spending a session, parks
specialist hand-offs with no free candidate on `stage:needs-prover`, `stage:needs-skeptic` or
`stage:escalated`, and
continues ready work on the candidates still free. Schema of `logs/loop/state.json`:

  {
    "meters": {
      "<meter>": {
        "harness": "claude" | "agy" | "grok",
        "percent": <float 0..100>,
        "resets_at": <float epoch seconds | null>,
        "read": <float epoch seconds>,
        "rate": <float percent per hour fitted reset-aware over recent readings | null>,
        "session_rate": <float percent per hour a session in flight adds | null>,
        "history": [{"read": <float>, "percent": <float>, "resets_at": <float | null>,
                     "sessions": <int loops' sessions in flight on the meter when read | null>}, ...]
      }
    },
    "cooldown": {
      "<meter, or harness when the whole harness is cooled>": {
        "harness": "claude" | "agy" | "grok",
        "until": <float epoch seconds>
      }
    }
  }

A Grok session. `grok -p` takes the agent's body and the prompt, as agy does, and these flags:
`--output-format streaming-messages-json`, Claude's stream-json shape, so one reader follows both;
`--always-approve`; `--trust`, without which Grok loads none of the worktree's hooks, the license guard
among them; `--background-wait-timeout`, since a headless Grok stops a background command 600 s after its
last turn and a landing's gate runs longer; `--rules` with <project root>/CLAUDE.md when it is there,
which Grok does not look for above the repository; and the offering's `model` and `effort`. Grok's plan
meter cannot be read from outside its own interface, so a grok meter has no readings: `[meters]` holds it
to its `max`, and a session whose result names a limit cools the offering's meters for an hour.

The session record. Each session a loop runs, round, prover or skeptic on any harness, appends one row
to the table `sessions` of <project root>/logs/loop/sessions.sqlite when it ends, written under
`logs/loop/.sessions.lock` so the workers of a pool write in turn; the file outlives every loop. Columns:
`actor` (loop-<pid>), `session` (round, prover or skeptic), `issue` (the issue the prompt names, or null
for a round that claims its own), `work_kind` (the issue's kind when the loop classified it at claim),
`route` (the route key the offering was chosen by, or null for the unrouted loop's round), `offering`
(null for the unrouted loop's table), `harness`, `model` and `effort` (null for the
harness's default), `started` (epoch seconds), `minutes`, `turns`, `weighted` (plan-weighted tokens),
`exit`, `error` and `limited` (0 or 1), and a round's report words `loop`, `prover`, `retry` and
`skeptic` (null when the report has none, and for a prover or skeptic session).

Stopping. SIGINT (Ctrl-C) or SIGTERM to the pool, or `tools/loop.py --stop`, is passed to every worker
as SIGTERM, which lets the agent run in flight finish and ends that loop; a prover or skeptic pass a finished round handed over is not started, and its
issue is released with a note so the next round picks it up. A second signal, or `--stop --now`
(SIGUSR1, passed to every worker), ends the run in flight too: the session's process group gets SIGTERM, then SIGKILL after
30 s, and the next round's orient recovers what it left. The pool and each worker keep the file
<project root>/logs/loop/<pid> while they run; `--stop` with no pid signals each such pid that is still a
loop and not a worker of a live pool, and with pids signals those. The file is JSON: `pool` is a
worker's pool pid, `workers` and `leaving` are a pool's workers and those it is stopping, and `session`
is the session a worker runs, as its kind, the offering it runs on (null for the unrouted loop's
tables), harness, model and effort
(each model and effort the flags name, or null for the harness's own default) and the meters it draws
on, or null between sessions, so another process such as tools/bead-status.py can say what an issue is
worked at and every worker can count the sessions in flight on each meter.

Tuning. Before each session the loop reads <project root>/loop.toml: `[offerings.<name>]`,
`[routes.<key>]` and `[meters.<name>]` configure automatic per-task routing and pacing, and top-level
tables (`round`, `prover`, `skeptic`, `retry`) configure the unrouted default Claude loop. An edit takes
effect at the next session, and `[pool] jobs` within 5 s. A file that does not parse or names invalid
keys, or a route naming an offering that is not there, is reported, and the loop keeps the last
values it read. SIGHUP to the pool, or `tools/loop.py
--reload`, passes SIGHUP to every worker, which re-executes after the run in flight and its hand-off,
with the same pid and so the same actor, and re-executes the pool at once, which takes its workers back
from its pid file; either way a change to this script is taken up.

A usage limit on an unrouted single-provider loop waits until the limit's reset and goes on. A round
that fails otherwise (no report, or an error result) is followed after 1, 2 and 4 minutes by another;
the fourth failure in a row ends the loop. When the failed round left exactly one issue in progress
under the loop's actor, the round that follows is a retry on that issue; with none or several it is a
plain round, whose orient recovers them. A retry is a round in every other way: its report is read the
same, and its failure counts the same.

usage: tools/loop.py [--wait SECONDS]                             run a pool of loops until it stops
       tools/loop.py --once                                       run one round in this process
       tools/loop.py --check                                      show matching ready work (0 tokens)
       tools/loop.py --list-profiles                              list the offerings and routes in loop.toml
       tools/loop.py --stop [--now] [PID...]                      stop running loops, after their run in flight
       tools/loop.py --reload [PID...]                            re-execute running loops, after their run in flight
       tools/loop.py --test                                       this script's own tests
"""
import argparse
import fcntl
import importlib.util
import io
import json
import multiprocessing
import os
import re
import shutil
import signal
import sqlite3
import subprocess
import sys
import tempfile
import textwrap
import time
import tomllib
import unittest
from contextlib import closing
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[2]
MAIN = ROOT / "main"
PIDS = ROOT / "logs" / "loop"
STATE_FILE = "state.json"
STATE_LOCK = ".state.lock"
SESSIONS_FILE = "sessions.sqlite"
SESSIONS_LOCK = ".sessions.lock"
SESSION_COLUMNS = (("actor", "TEXT"), ("session", "TEXT"), ("issue", "TEXT"), ("work_kind", "TEXT"), ("route", "TEXT"),
                   ("offering", "TEXT"), ("harness", "TEXT"), ("model", "TEXT"), ("effort", "TEXT"),
                   ("started", "REAL"), ("minutes", "REAL"), ("turns", "INTEGER"), ("weighted", "REAL"),
                   ("exit", "INTEGER"), ("error", "INTEGER"), ("limited", "INTEGER"),
                   ("loop", "TEXT"), ("prover", "TEXT"), ("retry", "TEXT"), ("skeptic", "TEXT"))
AGY_GROUP = "Gemini Models"
AGY_USAGE_INTERVAL = 300
AGY_USAGE_TIMEOUT = 30
RATE_WINDOW = 12 * 3600
HISTORY_MAX_AGE = 24 * 3600
MAX_HISTORY = 500
MIN_RATE_SPAN = 60
RESET_JITTER = 300
PACE_WAIT = 60
CONFIG = ROOT / "loop.toml"
SCRATCH = ROOT / "scratch"
RULES = ROOT / "CLAUDE.md"
GROK_BACKGROUND_WAIT = 4 * 3600
KINDS = ("round", "prover", "skeptic")
RETRY = "retry"
TABLES = (*KINDS, RETRY)
HARNESSES = ("claude", "agy", "grok")
AGY_MODES = ("skip-permissions", "auto", "accept-edits", "plan")
EFFORTS = ("low", "medium", "high", "xhigh", "max")
WORK_KINDS = ("tool", "sys", "proof", "spec", "arch", "review")
STAGE_NAMES = ("needs-prover", "needs-skeptic", "escalated", "needs-land")
HAND_OFFS = ("prover", "skeptic", "retry")
ROUTE_KEYS = (*WORK_KINDS, "epic-close", "epic-split", "needs-land", *HAND_OFFS)
STAGE_FOR_HAND_OFF = {"prover": "needs-prover", "skeptic": "needs-skeptic", "retry": "escalated"}
STAGE_ROUTE = {
    "needs-prover": "prover",
    "needs-skeptic": "skeptic",
    "escalated": "retry",
    "needs-land": "needs-land",
}
ISSUE = r"[a-z][a-z0-9]*-[a-z0-9]+(?:\.[0-9]+)*"
KEY = re.compile(rf"^(Loop|Prover|Skeptic|Retry|Notify):\s*(.*)$")
LIMIT_RE = re.compile(r"usage limit|limit reached|rate limit|quota|resource[ _]exhausted", re.I)
DECORATION = "-*`> \t"
WAIT = 900
FAILURES = 4
KILL_AFTER = 30
SHOWN = 160
TICK = 5
DONE = 3

_reviews_spec = importlib.util.spec_from_file_location("reviews", Path(__file__).with_name("reviews.py"))
reviews_mod = importlib.util.module_from_spec(_reviews_spec)
_reviews_spec.loader.exec_module(reviews_mod)


@dataclass
class Report:
    """What a round's report asks of the driver."""
    loop: str = None
    prover: str = None
    skeptic: str = None
    retry: str = None
    notify: list = field(default_factory=list)


@dataclass
class AgentSpec:
    """The harness and CLI flags for one agent table. An offering of [offerings] also has its name and the
    meters it draws on; a top-level table has neither and stands for its whole harness."""
    harness: str = "claude"
    flags: list = field(default_factory=list)
    name: str = None
    meters: tuple = ()


@dataclass
class Dispatch:
    """What loop.toml gives the loop: its top-level tables, and with [routes] each route's candidates."""
    agents: dict = field(default_factory=dict)
    routes: dict = field(default_factory=dict)
    routed: bool = False
    paces: dict = field(default_factory=dict)


def plain(line):
    """A report line without the markdown a model may wrap it in."""
    return line.strip().strip(DECORATION).replace("**", "").replace("`", "").strip(DECORATION)


def parse(text):
    """The report's directives; a key's last line wins, as the skill reads the last line."""
    report = Report()
    bullets = False
    for raw in text.splitlines():
        line = plain(raw)
        match = KEY.match(line)
        if match:
            key, value = match.group(1), match.group(2).strip()
            bullets = False
            if key == "Loop":
                word = re.match(r"(continue|wait|stop)\b", value)
                report.loop = word.group(1) if word else report.loop
            elif key in ("Prover", "Skeptic", "Retry"):
                issue = re.match(ISSUE, value)
                if issue:
                    setattr(report, key.lower(), issue.group(0))
            elif value.lower() in ("", "none"):
                bullets = value == ""
            else:
                report.notify.append(value)
        elif bullets and raw.strip().startswith(("-", "*")) and line:
            report.notify.append(line)
        elif line:
            bullets = False
    return report


@dataclass
class Run:
    """One agent session as its stream told it."""
    report: str = ""
    error: bool = False
    exit: int = None
    limited: bool = False
    reset: float = None
    turns: int = 0
    weighted: float = 0.0
    utilization: float = None
    readings: dict = field(default_factory=dict)
    limit_meters: set = field(default_factory=set)


def weighted(usage):
    """Plan-weighted tokens: uncached input at 1, cache writes at 1.25, cache reads at 0.1, output and thinking at 5."""
    if "cache_read_tokens" in usage or "thinking_tokens" in usage:
        cached = usage.get("cache_read_tokens", 0)
        uncached = max(usage.get("input_tokens", 0) - cached, 0)
        out = usage.get("output_tokens", 0) + usage.get("thinking_tokens", 0)
        return uncached + 0.1 * cached + 5 * out
    return (usage.get("input_tokens", 0) + 1.25 * usage.get("cache_creation_input_tokens", 0)
            + 0.1 * usage.get("cache_read_input_tokens", 0) + 5 * usage.get("output_tokens", 0))


def glimpse(tool):
    """One line for a Claude or Grok tool call: its description, or what it acts on."""
    given = tool.get("input", {})
    what = (given.get("description") or given.get("command") or given.get("file_path") or given.get("target_file")
            or given.get("target_directory") or given.get("pattern") or "")
    return f"{tool.get('name')}: {what.splitlines()[0] if what else ''}"


def agy_glimpse(step):
    """One line for an agy tool step: its summary, command, path or query."""
    info = step.get("tool_info") or {}
    given = info.get("parameters") or {}
    what = (given.get("toolSummary") or given.get("CommandLine") or given.get("Path")
            or given.get("AbsolutePath") or given.get("Query") or given.get("Pattern") or given.get("Prompt") or "")
    name = info.get("name") or step.get("tool_name") or "tool"
    return f"{name}: {str(what).splitlines()[0] if what else ''}"


def follow(lines, show):
    """Read a session's stream-json lines, showing its progress; the last result is the report. Grok's
    streaming-messages-json is Claude's shape, with an error result's reasons under `errors`."""
    run = Run()
    agy_buffers = {}
    agy_steps = 0
    for line in lines:
        try:
            event = json.loads(line)
        except ValueError:
            if line.strip():
                show(line.rstrip()[:SHOWN])
                if LIMIT_RE.search(line):
                    run.limited = True
            continue
        if not isinstance(event, dict):
            continue
        if "event" in event:
            ev = event.get("event")
            if ev == "step_update":
                step = event.get("step_update") or {}
                stype, state = step.get("step_type"), step.get("state")
                if stype == "tool" and state == "ACTIVE":
                    show(agy_glimpse(step)[:SHOWN])
                elif stype == "agent_response":
                    idx = step.get("step_index", 0)
                    agy_buffers[idx] = agy_buffers.get(idx, "") + (step.get("text_delta") or "")
                    if state == "DONE":
                        agy_steps += 1
                        text = agy_buffers.pop(idx, "").strip()
                        if text:
                            show("says: " + text.splitlines()[0][:SHOWN])
            elif ev == "result":
                res = event.get("result") or {}
                run.report = res.get("response") or ""
                run.error = res.get("status") != "SUCCESS" or bool(res.get("finished_reason"))
                run.turns += agy_steps if agy_steps else (res.get("num_turns") or 0)
                agy_steps = 0
                run.weighted += weighted(res.get("usage") or {})
                detail = f"{run.report} {res.get('error') or ''} {res.get('finished_reason') or ''}"
                if run.error and LIMIT_RE.search(detail):
                    run.limited = True
            continue

        kind = event.get("type")
        if kind == "assistant":
            for block in event.get("message", {}).get("content", []):
                if block.get("type") == "tool_use":
                    show(glimpse(block)[:SHOWN])
                elif block.get("type") == "text" and block.get("text", "").strip():
                    show("says: " + block["text"].strip().splitlines()[0][:SHOWN])
        elif kind == "rate_limit_event":
            info = event.get("rate_limit_info", {})
            if info.get("utilization") is not None and info.get("rateLimitType") == "seven_day":
                if run.utilization is None or int(100 * info["utilization"]) != int(100 * run.utilization):
                    show(f"weekly usage {100 * info['utilization']:.0f}%")
                run.utilization = info["utilization"]
            meter = stream_meter(info.get("rateLimitType"))
            if info.get("utilization") is not None and meter:
                run.readings[meter] = (100 * info["utilization"], info.get("resetsAt"))
            if not str(info.get("status", "allowed")).startswith("allowed"):
                run.limited = True
                run.reset = info.get("resetsAt") or run.reset
                if meter:
                    run.limit_meters.add(meter)
        elif kind == "result":
            run.report = event.get("result") or ""
            run.error = bool(event.get("is_error")) or event.get("subtype") != "success"
            run.turns += event.get("num_turns") or 0
            run.weighted += weighted(event.get("usage") or {})
            if run.error and LIMIT_RE.search(" ".join([run.report, *map(str, event.get("errors") or [])])):
                run.limited = True
    return run


def validate_str(value, where):
    if not isinstance(value, str) or not value or value.startswith("-"):
        raise ValueError(f"{where}: not a value")


def build_agent_spec(table, where):
    """Validate an agent table and build an AgentSpec."""
    merged = dict(table)
    harness = merged.pop("harness", "claude")
    validate_str(harness, f"{where}.harness")
    if harness not in HARNESSES:
        raise ValueError(f"{where}.harness: {harness} is not one of {', '.join(HARNESSES)}")

    flags = []
    if harness == "agy":
        mode = merged.pop("mode", "skip-permissions")
        validate_str(mode, f"{where}.mode")
        if mode not in AGY_MODES:
            raise ValueError(f"{where}.mode: {mode} is not one of {', '.join(AGY_MODES)}")
        flags += ["--dangerously-skip-permissions"] if mode == "skip-permissions" else ["--mode", mode]

    for key, value in merged.items():
        validate_str(value, f"{where}.{key}")
        if key == "effort":
            if value not in EFFORTS:
                raise ValueError(f"{where}.{key}: {value} is not one of {', '.join(EFFORTS)}")
        elif key == "model":
            pass
        elif harness == "claude" and key == "autocompact":
            size = re.fullmatch(r"([0-9]+)k|(1)m", value.lower())
            if value != "auto" and not (size and (size.group(2) or 100 <= int(size.group(1)) <= 1000)):
                raise ValueError(f"{where}.autocompact: {value} is not auto or 100k to 1M")
        elif harness == "claude" and key == "fallback-model":
            pass
        else:
            allowed = {"claude": "model, autocompact, effort or fallback-model", "agy": "harness, mode, model or effort",
                       "grok": "harness, model or effort"}[harness]
            raise ValueError(f"{where}.{key}: not {allowed}")
        flags += [f"--{key}", value]
    return AgentSpec(harness=harness, flags=flags)


def check_pool(table):
    """The number of worker loops a [pool] table asks for."""
    if not isinstance(table, dict):
        raise ValueError("pool: not a table")
    for key in table:
        if key != "jobs":
            raise ValueError(f"pool.{key}: not jobs")
    jobs = table.get("jobs", 1)
    if not isinstance(jobs, int) or isinstance(jobs, bool) or jobs < 1:
        raise ValueError(f"pool.jobs: {jobs!r} is not a whole number of at least 1")
    return jobs


def pool_jobs(text):
    """How many worker loops loop.toml asks the pool for; the whole file is validated, as a session's tune does."""
    parse_all(text)
    return check_pool(load_toml(text).get("pool", {}))


def load_toml(text):
    try:
        return tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        raise ValueError(f"not TOML: {error}")


METER_PREFIX = {"claude": "claude-", "agy": "gemini-", "grok": "grok-"}


def parse_offerings(raw):
    """[offerings.<name>]: each a harness with its flags and the meters it draws on, by name."""
    if not isinstance(raw, dict):
        raise ValueError("offerings: not a table")
    offerings = {}
    for name, table in raw.items():
        where = f"offerings.{name}"
        if not isinstance(table, dict):
            raise ValueError(f"{where}: not a table")
        table = dict(table)
        meters = table.pop("meters", None)
        spec = build_agent_spec(table, where)
        prefix = METER_PREFIX[spec.harness]
        if (not isinstance(meters, list) or not meters
                or not all(isinstance(m, str) and re.fullmatch(rf"{prefix}[a-z0-9]+(-[a-z0-9]+)*", m) for m in meters)):
            raise ValueError(f"{where}.meters: must be a list of the {spec.harness} meters it draws on, each {prefix}<name>")
        spec.name, spec.meters = name, tuple(dict.fromkeys(meters))
        offerings[name] = spec
    return offerings


def parse_paces(raw):
    """[meters.<name>]: each meter's target, the percent its projected use at reset stays under, and max,
    the most sessions it admits at once."""
    if not isinstance(raw, dict):
        raise ValueError("meters: not a table")
    paces = {}
    for name, table in raw.items():
        where = f"meters.{name}"
        if not re.fullmatch(r"[a-z0-9]+(-[a-z0-9]+)*", name) or not isinstance(table, dict):
            raise ValueError(f"{where}: not a table of a meter's target and max")
        for key in table:
            if key not in ("target", "max"):
                raise ValueError(f"{where}.{key}: a meter takes target and max")
        target, most = table.get("target"), table.get("max")
        if not isinstance(target, (int, float)) or isinstance(target, bool) or not 0 < target <= 100:
            raise ValueError(f"{where}.target: {target!r} is not a percent above 0 and at most 100")
        if not isinstance(most, int) or isinstance(most, bool) or most < 0:
            raise ValueError(f"{where}.max: {most!r} is not a whole number of sessions")
        paces[name] = {"target": float(target), "max": most}
    return paces


def parse_route(table, where, offerings):
    """One [routes.<key>]: its candidate offerings in order, or None when disabled."""
    for key in table:
        if key not in ("candidates", "disabled"):
            raise ValueError(f"{where}.{key}: a route takes candidates and disabled")
    disabled = table.get("disabled", False)
    if not isinstance(disabled, bool):
        raise ValueError(f"{where}.disabled: must be true or false")
    if disabled:
        return None
    names = table.get("candidates")
    if not isinstance(names, list) or not names or not all(isinstance(name, str) for name in names):
        raise ValueError(f"{where}.candidates: must be a list of offering names, cheapest capable first")
    for name in names:
        if name not in offerings:
            raise ValueError(f"{where}.candidates: {name} is not under [offerings]")
    return tuple(offerings[name] for name in dict.fromkeys(names))


def parse_all(text):
    """Validate the whole loop.toml and return (top_flags_dict, offerings_dict, routes_dict, paces_dict). A
    route maps to its tuple of candidate offerings, or None when disabled or left out with no
    [routes.default]; a paced meter to its target and max."""
    raw = load_toml(text)
    top_flags = {}
    raw_routes = None
    offerings = {}
    paces = {}
    for key, table in raw.items():
        if key == "routes":
            if not isinstance(table, dict):
                raise ValueError("routes: not a table")
            raw_routes = table
            continue
        if key == "offerings":
            offerings = parse_offerings(table)
            continue
        if key == "pool":
            check_pool(table)
            continue
        if key == "meters":
            paces = parse_paces(table)
            continue
        if key not in TABLES or not isinstance(table, dict):
            raise ValueError(f"{key}: not a table of {', '.join((*TABLES, 'pool', 'offerings', 'routes', 'meters'))}")
        if "harness" in table or "mode" in table:
            raise ValueError(f"{key}: top-level tables take model, autocompact, effort or fallback-model")
        top_flags[key] = build_agent_spec(table, key).flags

    routes = {}
    if raw_routes is not None:
        allowed_routes = ("default", *ROUTE_KEYS)
        for rkey, rtable in raw_routes.items():
            if rkey not in allowed_routes or not isinstance(rtable, dict):
                raise ValueError(f"routes.{rkey}: not a route table of {', '.join(allowed_routes)}")
        parsed = {rkey: parse_route(rtable, f"routes.{rkey}", offerings) for rkey, rtable in raw_routes.items()}
        for rkey in ROUTE_KEYS:
            routes[rkey] = parsed[rkey] if rkey in parsed else parsed.get("default")
    return top_flags, offerings, routes, paces


def options(text):
    """The claude -p flags loop.toml gives each top-level table."""
    top_flags, _, _, _ = parse_all(text)
    return top_flags


def parse_dispatch(text):
    """The loop's dispatch from loop.toml: routed when [routes] is there, else the top-level tables alone."""
    top_flags, _, routes, paces = parse_all(text)
    agents = {kind: AgentSpec(harness="claude", flags=list(flags)) for kind, flags in top_flags.items()}
    return Dispatch(agents=agents, routes=routes, routed=bool(routes), paces=paces)


def nearest_tier(issue, by_id):
    """The tier (1, 2 or 3) named on the issue or its nearest non-star ancestor epic, or None."""
    cur = issue
    seen = set()
    while cur and cur.get("parent") and cur.get("id") not in seen:
        seen.add(cur.get("id"))
        txt = f"{cur.get('title', '')} {cur.get('description', '')} {cur.get('acceptance_criteria', '')}".lower()
        for tier in (1, 2, 3):
            if re.search(rf"\btier[- ]{tier}\b", txt):
                return tier
        cur = (by_id or {}).get(cur.get("parent"))
    return None


def classify_issue(issue, by_id=None):
    """Classify a leaf into one of WORK_KINDS ('tool', 'sys', 'proof', 'spec', 'arch', 'review').

    An explicit `kind:<name>` label wins; otherwise `review` wins, and unlabeled legacy leaves are
    classified deterministically from their text and nearest ancestor epic's tier.
    """
    labels = set(issue.get("labels") or [])
    for label in sorted(labels):
        if label.startswith("kind:") and label[5:] in WORK_KINDS:
            return label[5:]
    if "review" in labels:
        return "review"
    own = f"{issue.get('title', '')} {issue.get('description', '')} {issue.get('acceptance_criteria', '')}".lower()
    tier = nearest_tier(issue, by_id)
    if "decision.md" in own or (re.search(r"\bdesign/[a-z0-9-]+", own)
                                and any(w in own for w in ("write the record", "design record", "revise its record"))):
        return "arch"
    if tier == 3:
        if (any(p in own for p in ("machine/", "aloader", "kernel/src", "dom0", "orangepi", "qemu", "aarch64", "x86_64"))
                and not any(p in own for p in ("tools/", ".claude/", ".agents/", "bead-status", "token-ledger", "leaf-cost", "loop.py"))):
            return "sys"
        return "tool"
    if any(p in own for p in ("tools/", ".claude/", ".agents/", "claude.md", "agents.md")) and tier != 1 and "kernel/verified" not in own:
        return "tool"
    if (any(w in own for w in ("machine/pc", "machine/virt", "aloader/", "wire "))
            and not any(w in own for w in ("verus", "spec fn", "witness", "lemma", "ensures", "kernel/verified"))):
        return "sys"
    if (("refuted" in labels or any(k in own for k in ("external_body", "verify-allowance", "witness", "check-throwaways", "lemma", "prove ")))
            and not any(s in own for s in ("new operation", "define spec"))):
        return "proof"
    if tier in (1, 2) or any(k in own for k in ("kernel/verified", "verus", "spec", "ensures", "requires", "invariant", "aheap", "aring", "amailbox", "afanin")):
        return "spec"
    return "tool"


def issue_stages(issue):
    """The stage:<name> suffixes carried by an issue."""
    return [lbl[6:] for lbl in (issue.get("labels") or []) if lbl.startswith("stage:") and lbl[6:] in STAGE_NAMES]


def agent_body(cwd, kind):
    """The instructions in .claude/agents/<kind>.md without its YAML frontmatter."""
    path = Path(cwd) / ".claude" / "agents" / f"{kind}.md"
    if not path.exists():
        return ""
    text = path.read_text()
    if text.startswith("---\n"):
        end = text.find("\n---\n", 4)
        if end != -1:
            return text[end + 5:].strip()
    return text.strip()


def loop_alive(pid):
    """Whether the process with this pid is a loop: an argument of its argv ends in tools/loop.py."""
    try:
        argv = Path(f"/proc/{pid}/cmdline").read_bytes().split(b"\0")
    except (FileNotFoundError, ProcessLookupError):
        return False
    return any(arg.endswith(b"tools/loop.py") for arg in argv)


def claude_alive(pid):
    """Whether the process with this pid is a live claude session."""
    try:
        return Path(f"/proc/{pid}/comm").read_text().strip() == "claude"
    except (FileNotFoundError, ProcessLookupError):
        return False


def write_pid_file(folder, held):
    """Replace <folder>/<pid> with `held` as JSON, so a reader never sees half a file."""
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / str(held["pid"])
    scratch = path.with_name(f".{path.name}.new")
    scratch.write_text(json.dumps(held) + "\n")
    os.replace(scratch, path)


def read_pid_file(folder, pid):
    """The JSON a loop's pid file holds, or {} when there is none or it is not a JSON object."""
    try:
        held = json.loads((Path(folder) / str(pid)).read_text())
    except (OSError, ValueError):
        return {}
    return held if isinstance(held, dict) else {}


# The session record (the opening comment gives its columns).

def record_session(folder, row):
    """Append one session's row to <folder>/sessions.sqlite, under <folder>/.sessions.lock so the loops of a
    pool write in turn, the first of them creating the table. In WAL mode a reader such as a report holds
    no writer up."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    names = [name for name, _ in SESSION_COLUMNS]
    assert sorted(row) == sorted(names), sorted(row)
    with open(folder / SESSIONS_LOCK, "a") as lock, closing(sqlite3.connect(folder / SESSIONS_FILE, timeout=60)) as db:
        fcntl.flock(lock, fcntl.LOCK_EX)
        db.execute("PRAGMA journal_mode=WAL")
        with db:
            db.execute("CREATE TABLE IF NOT EXISTS sessions (id INTEGER PRIMARY KEY, "
                       + ", ".join(f"{name} {kind}" for name, kind in SESSION_COLUMNS) + ")")
            db.execute(f"INSERT INTO sessions ({', '.join(names)}) VALUES ({', '.join('?' * len(names))})",
                       [row[name] for name in names])


def read_sessions(folder):
    """Every row of <folder>/sessions.sqlite in the order written, as dicts without the row id."""
    path = Path(folder) / SESSIONS_FILE
    if not path.exists():
        return []
    names = [name for name, _ in SESSION_COLUMNS]
    with closing(sqlite3.connect(path, timeout=60)) as db:
        return [dict(zip(names, values)) for values in db.execute(f"SELECT {', '.join(names)} FROM sessions ORDER BY id")]


# The shared meter and cooldown state (the opening comment gives its schema).

def empty_state():
    return {"meters": {}, "cooldown": {}}


def read_state(folder):
    """The state file in `folder`, or an empty state when there is none or it is not the schema's shape."""
    try:
        state = json.loads((Path(folder) / STATE_FILE).read_text())
    except (OSError, ValueError):
        return empty_state()
    if not isinstance(state, dict) or not isinstance(state.get("meters"), dict) or not isinstance(state.get("cooldown"), dict):
        return empty_state()
    state["cooldown"] = {key: held for key, held in state["cooldown"].items()
                         if isinstance(held, dict) and held.get("harness") in HARNESSES
                         and isinstance(held.get("until"), (int, float))}
    return state


def update_state(folder, change):
    """Apply change(state) to the state file under its lock and replace the file atomically, so the pool
    and every worker write in turn and a reader never sees half a file."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    with open(folder / STATE_LOCK, "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        state = read_state(folder)
        change(state)
        scratch = folder / f".{STATE_FILE}.{os.getpid()}.new"
        scratch.write_text(json.dumps(state, indent=1, sort_keys=True) + "\n")
        os.replace(scratch, folder / STATE_FILE)
    return state


def epoch(stamp):
    """Epoch seconds from an ISO 8601 time, or None for none."""
    return None if stamp is None else datetime.fromisoformat(stamp.replace("Z", "+00:00")).timestamp()


def reset_between(earlier, later):
    """Whether the meter reset between two readings: it went down, or its window moved on."""
    if later["percent"] < earlier["percent"] - 1.0:
        return True
    return (earlier["resets_at"] is not None and later["resets_at"] is not None
            and later["resets_at"] - earlier["resets_at"] > RESET_JITTER)


def fit_rate(history):
    """Percent per hour, fitted over the readings of the last RATE_WINDOW. A reset splits the readings into
    windows, and the rate is one least-squares slope shared by every window of two readings or more, each
    about its own mean. With none such, a window whose first reading follows a scheduled reset is taken
    as starting from 0% at that reset. None when nothing spans MIN_RATE_SPAN."""
    points = sorted(history, key=lambda reading: reading["read"])
    if not points:
        return None
    points = [reading for reading in points if reading["read"] >= points[-1]["read"] - RATE_WINDOW]
    windows, previous = [], None
    for reading in points:
        if previous is None or reset_between(previous, reading):
            windows.append({"after": previous, "readings": []})
        windows[-1]["readings"].append(reading)
        previous = reading
    sxx = sxy = span = 0.0
    for window in windows:
        readings = window["readings"]
        if len(readings) < 2:
            continue
        mean_t = sum(r["read"] for r in readings) / len(readings)
        mean_p = sum(r["percent"] for r in readings) / len(readings)
        sxx += sum((r["read"] - mean_t) ** 2 for r in readings)
        sxy += sum((r["read"] - mean_t) * (r["percent"] - mean_p) for r in readings)
        span += readings[-1]["read"] - readings[0]["read"]
    if span >= MIN_RATE_SPAN and sxx > 0:
        return 3600 * sxy / sxx
    for window in reversed(windows):
        after, first = window["after"], window["readings"][0]
        reset = after["resets_at"] if after else None
        if reset is not None and after["read"] < reset <= first["read"] - MIN_RATE_SPAN:
            return 3600 * first["percent"] / (first["read"] - reset)
    return None


def session_rate(history, rate):
    """Percent per hour a session in flight adds: the fitted rate over the mean number of the loops'
    sessions in flight on the meter at the readings it was fitted over. A mean below one, or none counted,
    is reckoned as one, so use from outside the loops is charged to the sessions rather than taken as
    room."""
    if rate is None:
        return None
    newest = max(r["read"] for r in history)
    counted = [r["sessions"] for r in history if r["read"] >= newest - RATE_WINDOW and r.get("sessions") is not None]
    return rate / max(sum(counted) / len(counted) if counted else 1.0, 1.0)


def add_reading(state, meter, harness, percent, resets_at, read, sessions=None):
    """Keep one reading of a meter, with the number of the loops' sessions in flight on it when read when
    that is known: its history, pruned by age and count, and the meter's latest reading, fitted rate and
    rate a session. A reading at a time already kept is the same reading and is not kept twice."""
    held = state["meters"].setdefault(meter, {"harness": harness, "history": []})
    history = [r for r in held.get("history", []) if r["read"] != read]
    history.append({"read": float(read), "percent": float(percent),
                    "resets_at": None if resets_at is None else float(resets_at), "sessions": sessions})
    history.sort(key=lambda r: r["read"])
    newest = history[-1]["read"]
    history = [r for r in history if r["read"] >= newest - HISTORY_MAX_AGE][-MAX_HISTORY:]
    rate = fit_rate(history)
    held.update(harness=harness, history=history, percent=history[-1]["percent"],
                resets_at=history[-1]["resets_at"], read=history[-1]["read"], rate=rate,
                session_rate=session_rate(history, rate))


def admission(held, pace, now):
    """(sessions the meter admits at once, percent, hours to reset, rate a session) for a meter's state
    `held` (None when it has no readings) under its pace from [meters]: floor((target - percent) / (hours
    * rate)), so the use the admitted sessions project to the reset stays under the target, clamped to
    [0, max]. At or past the target none; with no readings, no window running, a window that has reset
    since the reading, or no rate a session, the max."""
    if held is None:
        return pace["max"], None, None, None
    percent, resets_at, rate = held["percent"], held.get("resets_at"), held.get("session_rate")
    hours = None if resets_at is None else (resets_at - now) / 3600
    if hours is not None and hours <= 0:
        return pace["max"], percent, hours, rate
    if percent >= pace["target"]:
        return 0, percent, hours, rate
    if hours is None or rate is None or rate <= 0:
        return pace["max"], percent, hours, rate
    return min(int((pace["target"] - percent) / (hours * rate)), pace["max"]), percent, hours, rate


def in_flight(folder, alive=loop_alive):
    """The loops' sessions in flight on each meter, from the pid files in `folder` of the loops still alive."""
    counts = {}
    for path in Path(folder).glob("*"):
        if not path.name.isdigit() or not alive(int(path.name)):
            continue
        session = read_pid_file(folder, path.name).get("session") or {}
        for meter in session.get("meters") or ():
            counts[meter] = counts.get(meter, 0) + 1
    return counts


def fmt_admission(meter, admits, percent, hours, rate, pace):
    """One meter's admission with what it was computed from, for the pool's log."""
    if percent is None:
        why = "no readings"
    else:
        why = f"{percent:.1f}% used, " + ("no reset known" if hours is None else f"{hours:.1f} h to reset") + ", " + (
            "no rate yet" if rate is None else f"{rate:.2f}%/h a session")
    return f"{meter}: {why}: admits {admits} (target {pace['target']:g}, max {pace['max']})"


def stream_meter(limit_type):
    """The meter a Claude rate_limit_event's rateLimitType reads: seven_day is the week, five_hour the
    five-hour window, seven_day_<model> that model's week."""
    if limit_type == "seven_day":
        return "claude-week"
    if limit_type == "five_hour":
        return "claude-5h"
    if limit_type and limit_type.startswith("seven_day_"):
        return "claude-" + limit_type.removeprefix("seven_day_")
    return None


def claude_readings(account):
    """(meter, percent, resets_at, read) for each Claude meter in ~/.claude.json's cachedUsageUtilization:
    the week, the five-hour window when the plan has one, and each scoped limit that names a model."""
    cached = json.loads(Path(account).read_text())["cachedUsageUtilization"]
    meter, read = cached["utilization"], cached["fetchedAtMs"] / 1000
    readings = [("claude-week", meter["seven_day"]["utilization"], epoch(meter["seven_day"]["resets_at"]), read)]
    if meter.get("five_hour"):
        readings.append(("claude-5h", meter["five_hour"]["utilization"], epoch(meter["five_hour"]["resets_at"]), read))
    for limit in meter.get("limits") or []:
        model = (limit.get("scope") or {}).get("model") if limit["kind"] == "weekly_scoped" else None
        if model and model.get("display_name"):
            readings.append((f"claude-{model['display_name'].lower()}", limit["percent"], epoch(limit["resets_at"]), read))
    return readings


def agy_readings(text, read):
    """(meter, percent, resets_at, read) for each bucket of agy's Gemini group, out of what
    `agy -p /usage --output-format json` printed."""
    names = {"weekly": "gemini-week", "5h": "gemini-5h"}
    groups = json.loads(text)["command"]["data"]["groups"]
    return [(names[bucket["window"]], 100 * (1 - bucket["remaining_fraction"]), epoch(bucket["reset_time"]), read)
            for group in groups if group["name"] == AGY_GROUP
            for bucket in group["buckets"] if bucket["window"] in names]


def flag(flags, name):
    """The value given to --name among the flags, or None."""
    for at, given in enumerate(flags[:-1]):
        if given == f"--{name}":
            return flags[at + 1]
    return None


def fmt_spec(spec):
    """Short human-readable summary of an AgentSpec for --list-profiles and --check: an offering by its name."""
    if spec is None:
        return "disabled"
    if spec.name:
        return spec.name
    shown = [f for f in spec.flags if f != "--dangerously-skip-permissions"]
    return f"{spec.harness}({' '.join(shown)})" if shown else spec.harness


def fmt_candidates(candidates):
    """A route's candidates, in order, for --list-profiles and the loop's log."""
    return "disabled" if candidates is None else " > ".join(fmt_spec(spec) for spec in candidates)


def fmt_offering(spec):
    """An offering with its harness, flags and meters, for --list-profiles."""
    shown = [f for f in spec.flags if f != "--dangerously-skip-permissions"]
    return f"{spec.name}: {spec.harness}({' '.join(shown)}) on {', '.join(spec.meters)}"


def fmt_waits(waits):
    """Why a route waits: each candidate with the cooldowns that keep it, and when they end, or the meters
    whose pace has no room for it."""
    return "; ".join(f"{fmt_spec(spec)} cooled on " + ", ".join(
        f"{key} until {time.strftime('%a %H:%M', time.localtime(until))}" for key, until in cooled)
        if cooled else f"{fmt_spec(spec)} paced on " + ", ".join(
        f"{meter} (admits {admits}, {flying} in flight)" for meter, admits, flying in paced)
        for spec, cooled, paced in waits)


def limit_keys(run, spec):
    """What a session's usage limit cools: the meters its stream named, or with none named every meter the
    offering draws on; and its whole harness when none of those is a meter the offering declares, so an
    offering whose list misses the meter that refused still waits. A table that names no meters cools the
    meters named, or its harness."""
    if not spec.meters:
        return sorted(run.limit_meters) or [spec.harness]
    keys = set(run.limit_meters) or set(spec.meters)
    if not keys & set(spec.meters):
        keys.add(spec.harness)
    return sorted(keys)


class Loop:
    """The driver. The commands and the clock are parameters so the tests can replace them."""

    def __init__(self, claude="claude", agy="agy", grok="grok", bd="bd", notifier="notify-send", cwd=MAIN, pids=PIDS,
                 config=CONFIG, scratch=SCRATCH, rules=RULES, wait=WAIT, sleep=time.sleep, now=time.time, out=sys.stdout,
                 pool=None):
        self.claude, self.agy, self.grok, self.bd, self.notifier = claude, agy, grok, bd, notifier
        self.rules = Path(rules)
        self.pool = pool
        self.tag = f"{os.getpid()} " if pool is not None else ""
        self.cwd, self.pids, self.config, self.wait = Path(cwd), Path(pids), Path(config), wait
        self.scratch = Path(scratch)
        self.dispatch = Dispatch()
        self.read = None
        self.sleep, self.now, self.out = sleep, now, out
        self.actor = f"loop-{os.getpid()}"
        self.env = {key: value for key, value in os.environ.items() if key != "CLAUDECODE"}
        self.env["BEADS_ACTOR"] = self.actor
        self.env["TMPDIR"] = self.env["CLAUDE_CODE_TMPDIR"] = str(self.scratch)
        self.stopping = False
        self.halting = False
        self.reloading = False
        self.child = None
        self.retry = None
        self.kinds = {}
        self.paced = False
        self.alive = loop_alive

    def record(self, kind=None, spec=None):
        """Rewrite the loop's pid file to name the session it runs, or none."""
        session = spec and {"kind": kind, "offering": spec.name, "harness": spec.harness,
                            "model": flag(spec.flags, "model"), "effort": flag(spec.flags, "effort"),
                            "meters": list(spec.meters)}
        held = {"pid": os.getpid(), "session": session}
        if self.pool is not None:
            held["pool"] = self.pool
        write_pid_file(self.pids, held)

    def say(self, who, text):
        print(f"{time.strftime('%H:%M:%S')} {self.tag}{who:<8} {text}", file=self.out, flush=True)

    # Signals.

    def on_stop(self, signum, frame):
        if self.stopping or signum == signal.SIGUSR1:
            self.halt()
        else:
            self.stopping = True
            self.say("loop", "stopping after the run in flight (again, or --stop --now, ends it now)")

    def on_reload(self, signum, frame):
        self.reloading = True
        self.say("loop", "re-executing after the run in flight and its hand-off")

    def halt(self):
        self.stopping = self.halting = True
        self.say("loop", "ending the run in flight")
        if self.child and self.child.poll() is None:
            os.killpg(self.child.pid, signal.SIGTERM)

    def pause(self, seconds, why):
        """Wait, unless a stop comes first. True when the wait ran out."""
        self.say("loop", f"{why}: waiting {seconds:.0f} s")
        deadline = self.now() + seconds
        while not self.stopping and not self.reloading and self.now() < deadline:
            self.sleep(min(1.0, deadline - self.now()))
        return not self.stopping and not self.reloading

    def cooled(self, spec):
        """The cooldowns any loop of the pool wrote that still keep `spec` from a session, as (meter or
        harness, until): one on a meter the offering draws on or on its whole harness, or for a table that
        names no meters, any on its harness."""
        found = []
        for key, held in read_state(self.pids)["cooldown"].items():
            if held["until"] <= self.now():
                continue
            if (key in spec.meters or key == spec.harness) if spec.meters else held["harness"] == spec.harness:
                found.append((key, held["until"]))
        return sorted(found)

    def cooldowns(self):
        """The ends of the cooldowns still running, of every meter and harness."""
        return [held["until"] for held in read_state(self.pids)["cooldown"].values() if held["until"] > self.now()]

    def mark_cooldown(self, keys, harness, reset):
        """Cool the meters (or the whole harness) in `keys` down for every loop until the reported reset, or
        for an hour when none was given."""
        until = float(reset) if reset is not None else self.now() + 3600

        def cool(state):
            for key in keys:
                held = state["cooldown"].get(key) or {"until": 0.0}
                state["cooldown"][key] = {"harness": harness, "until": max(held["until"], until)}
        state = update_state(self.pids, cool)
        wait_s = max(max(state["cooldown"][key]["until"] for key in keys) - self.now(), 0.0)
        self.say("loop", f"{harness} usage limit on {', '.join(keys)}: cooling down what draws on it "
                         f"for every loop for {wait_s:.0f} s")

    def paced_out(self, spec):
        """The meters `spec` draws on whose pace in [meters] has no room for one more session, as (meter,
        sessions it admits, sessions in flight on it)."""
        paces = self.dispatch.paces
        if not any(meter in paces for meter in spec.meters):
            return []
        meters, flying = read_state(self.pids)["meters"], in_flight(self.pids, self.alive)
        found = []
        for meter in spec.meters:
            if meter in paces:
                admits = admission(meters.get(meter), paces[meter], self.now())[0]
                if admits <= flying.get(meter, 0):
                    found.append((meter, admits, flying.get(meter, 0)))
        return found

    def keep_readings(self, run, spec):
        """Write what the session told of its meters, and any usage limit it hit, to the state file. The
        session itself counts as in flight on the meters it drew on."""
        if run.readings:
            read = self.now()
            flying = in_flight(self.pids, self.alive)

            def keep(state):
                for meter, (percent, resets_at) in run.readings.items():
                    add_reading(state, meter, spec.harness, percent, resets_at, read,
                                sessions=flying.get(meter, 0) + (meter in spec.meters))
            update_state(self.pids, keep)
        if run.limited:
            self.mark_cooldown(limit_keys(run, spec), spec.harness, run.reset)

    # Sessions.

    def tune(self):
        """Take up loop.toml when it changed since the last session; keep the last values when it is wrong."""
        text = self.config.read_text() if self.config.exists() else ""
        if text == self.read:
            return
        self.read = text
        try:
            self.dispatch = parse_dispatch(text)
        except ValueError as error:
            self.say("loop", f"{self.config.name}: {error}; keeping the last values")
            return
        if self.dispatch.routed:
            parts = [f"{k}={fmt_candidates(c)}" for k, c in self.dispatch.routes.items()]
            self.say("loop", f"{self.config.name} [routes]: {'; '.join(parts)}")
        else:
            shown = "; ".join(f"{kind} {' '.join(spec.flags)}" for kind, spec in self.dispatch.agents.items() if spec.flags)
            self.say("loop", f"{self.config.name}: {shown or 'no flags'}")

    def candidates(self, route_key):
        """The offerings `route_key` may run on, cheapest capable first, or None when it is disabled: a
        route's candidates under [routes], or for the unrouted loop the one table of its kind."""
        if self.dispatch.routed:
            return self.dispatch.routes.get(route_key)
        if route_key in ("prover", "skeptic"):
            return (self.spec_for(route_key),)
        return (self.spec_for("round", RETRY if route_key == RETRY else None),)

    def choose(self, route_key):
        """(the first candidate free to take a session, None): no cooldown keeps it and every meter it draws
        on admits one more session than it has in flight. (None, [(candidate, its cooldowns, its meters
        with no room)]) when no candidate is free, so the work waits; (None, None) when the route is
        disabled."""
        self.tune()
        candidates = self.candidates(route_key)
        if candidates is None:
            return None, None
        waits = []
        for spec in candidates:
            cooled = self.cooled(spec)
            paced = [] if cooled else self.paced_out(spec)
            if not cooled and not paced:
                return spec, None
            waits.append((spec, cooled, paced))
        self.paced = self.paced or any(paced for _, _, paced in waits)
        return None, waits

    def spec_for(self, kind, table=None):
        """The AgentSpec of the unrouted loop's table for `kind`, or of the table named when loop.toml has it."""
        agents = self.dispatch.agents
        return agents.get(table or kind) or agents.get(kind) or AgentSpec()

    def agent(self, kind, prompt, table=None, spec=None, issue=None, route=None):
        """Run one agent session in the main worktree on the offering chosen for it, or with the flags of its
        kind's table or of the one named; its stream is shown as it comes. The session's row goes to the
        session record, with the issue it was given and the route it was chosen by when the loop knows them."""
        self.tune()
        spec = spec or self.spec_for(kind, table)
        if spec.harness in ("agy", "grok"):
            body = agent_body(self.cwd, kind)
            full_prompt = f"{body}\n\n{prompt}" if body else prompt
        if spec.harness == "agy":
            command = [self.agy, "--output-format", "stream-json", *spec.flags, "-p", full_prompt]
        elif spec.harness == "grok":
            rules = ["--rules", self.rules.read_text()] if self.rules.exists() else []
            command = [self.grok, "-p", full_prompt, "--output-format", "streaming-messages-json", "--always-approve",
                       "--trust", "--background-wait-timeout", str(GROK_BACKGROUND_WAIT), *rules, *spec.flags]
        else:
            command = [self.claude, "-p", "--agent", kind, "--permission-mode", "auto",
                       "--output-format", "stream-json", "--verbose", *spec.flags, prompt]
        started = self.now()
        self.say(kind, f"start ({fmt_spec(spec) if spec.name else spec.harness}): {prompt}")
        self.scratch.mkdir(exist_ok=True)
        self.record(kind, spec)
        self.child = subprocess.Popen(command, cwd=self.cwd, env=self.env, stdin=subprocess.DEVNULL,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                      start_new_session=True)
        try:
            run = follow(self.child.stdout, lambda text: self.say(kind, text))
            try:
                run.exit = self.child.wait(timeout=KILL_AFTER if self.halting else None)
            except subprocess.TimeoutExpired:
                os.killpg(self.child.pid, signal.SIGKILL)
                run.exit = self.child.wait()
        finally:
            if self.child and self.child.stdout:
                self.child.stdout.close()
            self.child = None
            self.record()
        self.keep_readings(run, spec)
        minutes = (self.now() - started) / 60
        words = parse(run.report) if kind == "round" and not run.error else Report()
        record_session(self.pids, {
            "actor": self.actor, "session": kind, "issue": issue, "work_kind": self.kinds.get(issue), "route": route,
            "offering": spec.name, "harness": spec.harness, "model": flag(spec.flags, "model"),
            "effort": flag(spec.flags, "effort"), "started": started, "minutes": minutes, "turns": run.turns,
            "weighted": run.weighted, "exit": run.exit, "error": int(run.error), "limited": int(run.limited),
            "loop": words.loop, "prover": words.prover, "retry": words.retry, "skeptic": words.skeptic})
        usage = f", weekly {100 * run.utilization:.0f}%" if run.utilization is not None else ""
        self.say(kind, f"end: exit {run.exit}, {minutes:.1f} min, {run.turns} turns, "
                       f"{run.weighted / 1e6:.2f}M weighted tokens{usage}")
        return run

    def beads_run(self, *args):
        done = subprocess.run([self.bd, *args], cwd=self.cwd, env=self.env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True)
        if done.returncode != 0:
            self.say("bd", f"bd {' '.join(args[:2])} failed: {(done.stderr or done.stdout).strip()[:SHOWN]}")
        return done.returncode == 0, done.stdout

    def beads(self, *args):
        _, stdout = self.beads_run(*args)
        return stdout

    def beads_json(self, *args):
        raw = self.beads(*args).strip()
        if not raw:
            return []
        try:
            return json.loads(raw)
        except ValueError:
            return []

    def notify(self, text):
        self.say("notify", text)
        if shutil.which(self.notifier):
            subprocess.run([self.notifier, "atmosphere loop", text], stdin=subprocess.DEVNULL,
                           capture_output=True)

    # Zero-token pre-check and stage recovery for routed loops.

    def worktree_note(self, issue_id):
        wt = self.cwd.parent / issue_id
        if not wt.exists():
            return f"worktree {wt} absent"
        commits = subprocess.run(["git", "-C", str(wt), "log", "--oneline", "main..HEAD"],
                                 capture_output=True, text=True).stdout.splitlines()
        changed = subprocess.run(["git", "-C", str(wt), "status", "--short"],
                                 capture_output=True, text=True).stdout.splitlines()
        return f"worktree {wt} exists, {len(commits)} commits past main, {len(changed)} files changed"

    def recover_abandoned(self, dry_run=False):
        """Recover abandoned in-progress issues from dead loops/sessions; return (recovered_ids, other_live)."""
        in_prog = self.beads_json("list", "-s", "in_progress", "--json", "--limit", "0")
        recovered = []
        other_live = False
        for issue in in_prog:
            assignee = issue.get("assignee") or ""
            issue_id = issue["id"]
            if assignee == self.actor:
                if issue_id == self.retry:
                    continue
                abandoned = True
            elif m := re.fullmatch(r"loop-([0-9]+)", assignee):
                abandoned = not loop_alive(int(m.group(1)))
            elif m := re.fullmatch(r"claude-([0-9]+)", assignee):
                abandoned = not claude_alive(int(m.group(1)))
            else:
                abandoned = False
            if abandoned:
                recovered.append(issue_id)
                if not dry_run:
                    self.beads("update", issue_id, "--append-notes",
                               f"Recovered at orient: {self.worktree_note(issue_id)}")
                    self.beads("update", issue_id, "-s", "open", "--assignee", "")
            elif assignee != self.actor:
                other_live = True
        return recovered, other_live

    def release_if_held(self, issue_id):
        held = {item["id"] for item in self.beads_json("list", "-s", "in_progress", "--assignee", self.actor, "--json")}
        if issue_id in held:
            self.beads("update", issue_id, "-s", "open", "--assignee", "")

    def other_loop_alive(self):
        if not self.pids.exists():
            return False
        mine = (os.getpid(), self.pool)
        for path in self.pids.glob("*"):
            if path.name.isdigit() and int(path.name) not in mine and loop_alive(int(path.name)):
                return True
        return False

    def inspect_work(self, claim=False):
        """Inspect Beads at zero token cost for the routes of loop.toml.

        When claim=True, atomically claims the first matching non-cooled-down stage or leaf so no peer loop races it.
        Returns (action, payload, summary_dict).
        """
        self.tune()
        recovered, other_live = self.recover_abandoned(dry_run=not claim)
        ready = self.beads_json("ready", "--exclude-type=epic", "--json", "--limit", "0")
        all_issues = None
        by_id = None

        def ensure_all():
            nonlocal all_issues, by_id
            if all_issues is None:
                all_issues = self.beads_json("list", "--all", "--json", "--limit", "0")
                by_id = {item["id"]: item for item in all_issues}
            return all_issues, by_id

        matched_stages = []
        matched_leaves = []
        cooled = []

        # 1. Queued stage hand-offs in priority order.
        for leaf in ready:
            stages = issue_stages(leaf)
            for sname in stages:
                rkey = STAGE_ROUTE[sname]
                spec, waits = self.choose(rkey)
                if spec is None:
                    if waits:
                        cooled.append((rkey, leaf["id"], waits))
                    continue
                matched_stages.append((sname, leaf["id"], leaf.get("title", ""), spec))
                if claim:
                    ok, _ = self.beads_run("update", leaf["id"], "--claim")
                    if ok:
                        self.kinds[leaf["id"]] = classify_issue(leaf, by_id)
                        return f"stage:{sname}", (leaf["id"], rkey, spec), {}
                break

        # 2. Plain ready leaves whose kind has a route (skipping leaves waiting on another stage).
        for leaf in ready:
            if issue_stages(leaf):
                continue
            labels = set(leaf.get("labels") or [])
            has_explicit = any(lbl.startswith("kind:") or lbl == "review" for lbl in labels)
            if not has_explicit:
                ensure_all()
            kind = classify_issue(leaf, by_id)
            spec, waits = self.choose(kind)
            if spec is None:
                if waits:
                    cooled.append((kind, leaf["id"], waits))
                continue
            matched_leaves.append((kind, leaf["id"], leaf.get("title", ""), spec))
            if claim:
                ok, _ = self.beads_run("update", leaf["id"], "--claim")
                if ok:
                    self.kinds[leaf["id"]] = kind
                    return "leaf", (leaf["id"], kind, spec), {}

        # 3. Epic rounds (finished epics first via tools/reviews.py, then childless ready epics).
        all_list, _ = ensure_all()
        finished_lines = reviews_mod.finished(all_list) if all_list else []
        split_epics = []
        if not finished_lines and not ready:
            ready_epics = self.beads_json("ready", "-t", "epic", "--json", "--limit", "0")
            has_child = {item.get("parent") for item in all_list if item.get("parent")}
            split_epics = [ep["id"] for ep in ready_epics if ep.get("parent") and ep["id"] not in has_child]

        close_route = self.candidates("epic-close")
        split_route = self.candidates("epic-split")
        close_spec = split_spec = None
        if finished_lines and close_route is not None:
            close_spec, waits = self.choose("epic-close")
            if close_spec is None:
                cooled.append(("epic-close", "epics", waits))
        if split_epics and not ready and split_route is not None:
            split_spec, waits = self.choose("epic-split")
            if split_spec is None:
                cooled.append(("epic-split", split_epics[0], waits))

        summary = {
            "recovered": recovered,
            "other_live": other_live,
            "stages": matched_stages,
            "leaves": matched_leaves,
            "finished_epics": finished_lines if close_route is not None else [],
            "split_epics": split_epics if split_route is not None else [],
            "close_route": close_route,
            "split_route": split_route,
            "cooled": cooled,
        }
        if claim:
            if close_spec is not None:
                return "epic_finished", ("epic-close", close_spec), summary
            if split_spec is not None:
                return "epic_split", ("epic-split", split_spec), summary
            if cooled:
                return "cooldown_wait", None, summary
            globally_done = not ready and not finished_lines and not split_epics and not other_live
            if globally_done:
                return "stop", None, summary
            if other_live or self.other_loop_alive():
                return "wait", None, summary
            return "idle_stop", None, summary
        return "check", None, summary

    # The hand-offs.

    def hand_off(self, kind, issue, prompt):
        """Run the prover or the skeptic a round handed over on the first of its route's candidates no
        cooldown keeps, and record its report; or, when the route is disabled or every candidate is cooled
        down, stamp the issue's stage for a later loop. Then release the issue."""
        label = kind.capitalize()
        spec, waits = self.choose(kind)
        if spec is None:
            stage = STAGE_FOR_HAND_OFF[kind]
            why = f"no candidate is free ({fmt_waits(waits)})" if waits else "route disabled"
            self.say(kind, f"{why}: queueing {issue} on stage:{stage}")
            self.beads("update", issue, "--add-label", f"stage:{stage}", "-s", "open", "--assignee", "")
            return
        if self.stopping:
            self.beads("update", issue, "--append-notes",
                       f"{label} not run: the loop stopped before it started; the next round hands it over again.")
        else:
            run = self.agent(kind, prompt, spec=spec, issue=issue, route=kind)
            if run.limited and self.dispatch.routed:
                stage = STAGE_FOR_HAND_OFF[kind]
                self.say(kind, f"{fmt_spec(spec)} hit a usage limit; parking {issue} on stage:{stage}")
                self.beads("update", issue, "--add-label", f"stage:{stage}", "-s", "open", "--assignee", "")
                return
            report = run.report.strip() if run.report.strip() and not run.error else (
                f"none; the {kind}'s session ended without one (exit {run.exit}"
                f"{', usage limit' if run.limited else ''}).")
            self.beads("update", issue, "--append-notes", f"{label} report: {report}")
            if self.dispatch.routed and kind == "prover" and self.candidates("needs-land") is not None:
                self.beads("update", issue, "--add-label", "stage:needs-land", "-s", "open", "--assignee", "")
                return
        self.beads("update", issue, "-s", "open", "--assignee", "")

    def run_specialist_stage(self, sname, issue, spec):
        """Run a queued stage:needs-prover or stage:needs-skeptic directly, on the offering chosen at its claim."""
        kind = "prover" if sname == "needs-prover" else "skeptic"
        label = kind.capitalize()
        if self.stopping:
            self.beads("update", issue, "-s", "open", "--assignee", "")
            return "continue", Run()
        prompt = (f"Issue {issue}, worktree {self.cwd.parent / issue}. Your input is the issue's last Prover input note."
                  if kind == "prover" else
                  f"Review {issue}. Your input is the review's last Skeptic input note.")
        run = self.agent(kind, prompt, spec=spec, issue=issue, route=kind)
        if run.limited:
            self.beads("update", issue, "-s", "open", "--assignee", "")
            return "cooldown", run
        report = run.report.strip() if run.report.strip() and not run.error else (
            f"none; the {kind}'s session ended without one (exit {run.exit}).")
        self.beads("update", issue, "--append-notes", f"{label} report: {report}")
        extra = ("--add-label", "stage:needs-land") if kind == "prover" else ()
        self.beads("update", issue, "--remove-label", f"stage:{sname}", *extra, "-s", "open", "--assignee", "")
        return "continue", run

    def escalate(self, issue, why):
        """Leave `issue` for a loop that can run its retry: stamp stage:escalated and release it."""
        self.say("retry", f"{why}: queueing {issue} on stage:escalated")
        self.beads("update", issue, "--add-label", "stage:escalated", "-s", "open", "--assignee", "")

    def finish_round_report(self, run, clear_stage=None):
        """Parse a round's report, clear any consumed stage label, run or queue hand-offs, and return Loop word."""
        if run.report.strip():
            print(textwrap.indent(run.report.strip(), f"{self.tag}    "), file=self.out, flush=True)
        report = parse(run.report) if not run.error else Report()
        if report.loop is not None and clear_stage:
            issue_id, stage_label = clear_stage
            self.beads("update", issue_id, "--remove-label", stage_label)
        for text in report.notify:
            self.notify(text)
        if report.prover:
            self.hand_off("prover", report.prover,
                          f"Issue {report.prover}, worktree {self.cwd.parent / report.prover}. "
                          "Your input is the issue's last Prover input note.")
        if report.skeptic:
            self.hand_off("skeptic", report.skeptic,
                          f"Review {report.skeptic}. Your input is the review's last Skeptic input note.")
        self.retry = None
        if report.retry:
            spec, waits = self.choose(RETRY)
            if spec is None and waits is None:
                self.escalate(report.retry, "route disabled")
            elif spec is None and self.dispatch.routed:
                self.escalate(report.retry, f"no candidate is free ({fmt_waits(waits)})")
            else:
                self.retry = report.retry
        return report.loop, run

    def round(self):
        """One round (or specialist stage pass) and its hand-off. The report's Loop word, or None when it failed."""
        self.tune()
        self.paced = False
        issue, self.retry = self.retry, None
        if issue:
            spec, waits = self.choose(RETRY)
            if spec is None and waits is None:
                self.escalate(issue, "route disabled")
                return "continue", Run()
            if spec is None:
                self.retry = issue
                return "cooldown_wait", Run()
            run = self.agent("round", f"Run one round. Issue {issue} is yours: a round of this loop left it unfinished.",
                             spec=spec, issue=issue, route=RETRY)
            if run.limited and self.dispatch.routed:
                self.beads("update", issue, "--add-label", "stage:escalated", "-s", "open", "--assignee", "")
                return "cooldown", run
            return self.finish_round_report(run)

        if not self.dispatch.routed:
            if self.cooled(self.spec_for("round")):
                return "cooldown_wait", Run()
            run = self.agent("round", "Run one round.")
            return self.finish_round_report(run)

        action, payload, _ = self.inspect_work(claim=True)
        if action in ("stage:needs-prover", "stage:needs-skeptic"):
            target, _, spec = payload
            return self.run_specialist_stage(action.split(":", 1)[1], target, spec)
        if action == "stage:escalated":
            target, rkey, spec = payload
            run = self.agent("round",
                             f"Run one round. Issue {target} is yours: a round left it unfinished; take no other issue.",
                             spec=spec, issue=target, route=rkey)
            if run.limited:
                self.release_if_held(target)
                return "cooldown", run
            return self.finish_round_report(run, clear_stage=(target, "stage:escalated"))
        if action in ("stage:needs-land", "leaf"):
            target, rkey, spec = payload
            run = self.agent("round", f"Run one round. Issue {target} is yours (claimed for route {rkey}; take no other issue).",
                             spec=spec, issue=target, route=rkey)
            if run.limited:
                self.release_if_held(target)
                return "cooldown", run
            clear = (target, "stage:needs-land") if action == "stage:needs-land" else None
            return self.finish_round_report(run, clear_stage=clear)
        if action == "epic_finished":
            _, spec = payload
            run = self.agent("round", "Run one round. Epic round only: act on finished epics from tools/reviews.py; "
                                      "do not claim from bd ready and do not run an epic split round.", spec=spec,
                             route="epic-close")
            if run.limited:
                return "cooldown", run
            return self.finish_round_report(run)
        if action == "epic_split":
            _, spec = payload
            run = self.agent("round", "Run one round.", spec=spec, route="epic-split")
            if run.limited:
                return "cooldown", run
            return self.finish_round_report(run)
        return action, Run()

    def held(self):
        """The one issue in progress under the loop's actor, or None when there is none or more than one."""
        issues = self.beads_json("list", "-s", "in_progress", "--assignee", self.actor, "--json")
        return issues[0]["id"] if len(issues) == 1 else None

    def drive(self, once=False):
        """Rounds until the loop stops. The exit status: 0 for a stop, 1 for repeated failures."""
        failures = 0
        while not self.stopping and not self.reloading:
            loop, run = self.round()
            if loop is not None:
                failures = 0
            if loop == "cooldown":
                continue
            if loop == "stop":
                blocked = self.beads("list", "-s", "blocked")
                print(blocked, file=self.out, flush=True)
                questions = sum(1 for line in blocked.splitlines() if re.search(ISSUE, line) and line.lstrip()[:1] in "●○◐")
                self.notify(f"round loop stopped: {questions} questions in bd list -s blocked")
                return 0
            if loop == "idle_stop":
                self.say("loop", "no work matching the configured routes and no peer loop running; stopping")
                return 0
            if loop == "cooldown_wait":
                if once:
                    self.say("loop", "remaining ready work waits on a cooled-down harness; stopping (--once)")
                    return 0
                active = self.cooldowns()
                until = max(min(min(active) - self.now(), self.wait), 1.0) if active else self.wait
                if self.paced:
                    self.pause(min(until, PACE_WAIT), "every candidate cooled down or paced out")
                else:
                    self.pause(until, "cooldown on rate-limited harness")
                continue
            if once or self.stopping or self.reloading:
                break
            if loop == "wait":
                why = ("no work matching the configured routes; another loop is active"
                       if self.dispatch.routed else "nothing ready; another loop holds the issues in progress")
                self.pause(self.wait, why)
            elif loop is None and run.limited:
                reset = max((run.reset or self.now() + 3600) - self.now(), 0) + 60
                self.pause(reset, "usage limit")
            elif loop is None:
                failures += 1
                if failures >= FAILURES:
                    self.notify(f"round loop stopped: {failures} failed rounds in a row")
                    return 1
                self.retry = self.held()
                self.pause(60 * 2 ** (failures - 1), f"the round ended without a report (failure {failures})")
        self.say("loop", "reloading" if self.reloading and not self.stopping else "stopped")
        return 0


class Pool:
    """The supervisor: keeps loop.toml's [pool] jobs worker loops running, each a process of this script.

    A worker is spawned as `worker + ["--worker", <the pool's pid>]` in a session of its own, so a Ctrl-C
    at the terminal reaches the pool alone, which passes a stop on. The workers are tracked by pid, and
    the pool's pid file names them, so a pool that re-executes itself adopts the workers it had. The
    sleep is a parameter so the tests can drive the pool a tick at a time with step().
    """

    def __init__(self, worker, pids=PIDS, config=CONFIG, tick=TICK, sleep=time.sleep, out=sys.stdout,
                 execute=os.execv, argv=None, claude_account=Path.home() / ".claude.json", agy="agy", now=time.time):
        self.worker = list(worker)
        self.claude_account, self.agy, self.now = Path(claude_account), agy, now
        self.asked_agy = self.claude_failure = None
        self.pids, self.config, self.tick = Path(pids), Path(config), tick
        self.sleep, self.out, self.execute = sleep, out, execute
        self.argv = argv or [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]]
        self.pid = os.getpid()
        self.workers = []
        self.leaving = set()
        self.failed = 0
        self.jobs = 1
        self.paces = {}
        self.admitted = {}
        self.read = None
        self.stopping = self.halting = self.reloading = False
        self.status = 0

    def say(self, text):
        print(f"{time.strftime('%H:%M:%S')} pool     {text}", file=self.out, flush=True)

    def record(self):
        write_pid_file(self.pids, {"pid": self.pid, "session": None, "workers": self.workers,
                                   "leaving": sorted(self.leaving)})

    def signal_workers(self, signum, pids):
        for pid in pids:
            try:
                os.kill(pid, signum)
            except ProcessLookupError:
                pass

    # Signals, passed on to the workers.

    def on_stop(self, signum, frame):
        if self.stopping or signum == signal.SIGUSR1:
            self.stopping = self.halting = True
            self.say("ending every worker's run in flight")
            self.signal_workers(signal.SIGUSR1, self.workers)
        else:
            self.stop("stopping every worker after its run in flight (again, or --stop --now, ends them now)")

    def on_reload(self, signum, frame):
        self.reloading = True

    def stop(self, why):
        self.stopping = True
        self.say(why)
        self.signal_workers(signal.SIGTERM, [pid for pid in self.workers if pid not in self.leaving])

    # The meters.

    def keep(self, readings, harness):
        flying = in_flight(self.pids)

        def change(state):
            for meter, percent, resets_at, read in readings:
                add_reading(state, meter, harness, percent, resets_at, read, sessions=flying.get(meter, 0))
        update_state(self.pids, change)

    def pace(self):
        """Recompute how many sessions each meter of [meters] admits, as every worker does before it
        chooses an offering, and log each change with what it was computed from."""
        meters = read_state(self.pids)["meters"]
        admitted = {}
        for meter, pace in self.paces.items():
            admits, percent, hours, rate = admission(meters.get(meter), pace, self.now())
            admitted[meter] = admits
            if self.admitted.get(meter) != admits:
                self.say(fmt_admission(meter, admits, percent, hours, rate, pace))
        self.admitted = admitted

    def sample(self):
        """Keep Claude's meters as Claude Code last fetched them, when it fetched them since, and every
        AGY_USAGE_INTERVAL ask agy for Gemini's; a reading that fails keeps the last ones."""
        try:
            readings = claude_readings(self.claude_account)
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as failure:
            # ~/.claude.json is Claude Code's own file: one it has not written, or of a shape this does not know, keeps the last readings.
            readings = []
            if self.claude_account.exists() and repr(failure) != self.claude_failure:
                self.say(f"claude usage: {failure!r}; keeping the last readings")
            self.claude_failure = repr(failure)
        held = read_state(self.pids)["meters"]
        if any(held.get(meter, {}).get("read") != read for meter, _, _, read in readings):
            self.keep(readings, "claude")
        if self.asked_agy is not None and self.now() - self.asked_agy < AGY_USAGE_INTERVAL:
            return
        self.asked_agy = self.now()
        try:
            done = subprocess.run([self.agy, "-p", "/usage", "--output-format", "json"], stdin=subprocess.DEVNULL,
                                  capture_output=True, text=True, timeout=AGY_USAGE_TIMEOUT, check=True)
            self.keep(agy_readings(done.stdout, self.asked_agy), "agy")
        except (OSError, subprocess.SubprocessError, ValueError, KeyError, TypeError) as failure:
            # agy is another program: one it lacks, or a reply of a shape this does not know, keeps the last readings.
            self.say(f"agy usage: {failure!r}; keeping the last readings")

    # The tick.

    def tune(self):
        """Take up [pool] jobs when loop.toml changed; keep the last value when it is wrong. A new value
        forgives the workers lost to failures, since the human has looked at the pool."""
        text = self.config.read_text() if self.config.exists() else ""
        if text == self.read:
            return
        self.read = text
        try:
            jobs = pool_jobs(text)
            self.paces = parse_all(text)[3]
        except ValueError as error:
            self.say(f"{self.config.name}: {error}; keeping {self.jobs} jobs")
            return
        if jobs != self.jobs or not self.workers:
            self.say(f"{self.config.name}: {jobs} jobs")
        if jobs != self.jobs:
            self.failed = 0
        self.jobs = jobs

    def exit_status(self, pid):
        """A worker's exit status once it has ended, else None."""
        try:
            done, status = os.waitpid(pid, os.WNOHANG)
        except ChildProcessError:
            return None if loop_alive(pid) else 0
        return os.waitstatus_to_exitcode(status) if done else None

    def reap(self):
        for pid in list(self.workers):
            status = self.exit_status(pid)
            if status is None:
                continue
            self.workers.remove(pid)
            shrunk = pid in self.leaving
            self.leaving.discard(pid)
            if status == DONE and not self.stopping:
                self.stop(f"worker {pid} found only questions for the human left; stopping the pool")
            elif status == 1 and not shrunk and not self.stopping:
                self.failed += 1
                self.say(f"worker {pid} ended after {FAILURES} failed rounds in a row; not replaced until jobs changes")
            else:
                self.say(f"worker {pid} ended (status {status})")

    def spawn(self):
        argv = [*self.worker, "--worker", str(self.pid)]
        pid = os.posix_spawn(argv[0], argv, os.environ, setsid=True,
                             file_actions=[(os.POSIX_SPAWN_OPEN, 0, os.devnull, os.O_RDONLY, 0)])
        self.workers.append(pid)
        self.say(f"worker {pid} started")

    def resize(self):
        active = [pid for pid in self.workers if pid not in self.leaving]
        target = max(self.jobs - self.failed, 0)
        for pid in active[target:][::-1]:
            self.say(f"worker {pid} stopping after its run in flight: the pool shrank to {self.jobs}")
            self.leaving.add(pid)
            os.kill(pid, signal.SIGTERM)
        for _ in range(target - len(active)):
            self.spawn()

    def adopt(self):
        """Take back the workers the pid file names, after this pool re-executed itself."""
        held = read_pid_file(self.pids, self.pid)
        self.workers = [pid for pid in held.get("workers", []) if loop_alive(pid)]
        self.leaving = {pid for pid in held.get("leaving", []) if pid in self.workers}
        if self.workers:
            self.say(f"adopted workers {', '.join(map(str, self.workers))}")

    def step(self):
        """One tick. False once the pool is over."""
        self.tune()
        self.sample()
        self.pace()
        self.reap()
        if self.reloading and not self.stopping:
            self.say("re-executing; each worker re-executes after its run in flight")
            self.signal_workers(signal.SIGHUP, self.workers)
            self.record()
            self.execute(self.argv[0], self.argv)
            return False
        if self.stopping:
            return bool(self.workers)
        self.resize()
        if not self.workers:
            self.say("every worker ended after repeated failures; stopping")
            self.status = 1
            return False
        return True

    def run(self):
        """Ticks until the pool is over; the exit status: 0 for a stop, 1 when every worker failed."""
        self.adopt()
        try:
            while self.step():
                self.record()
                self.sleep(self.tick)
        finally:
            if not self.reloading or self.stopping:
                (self.pids / str(self.pid)).unlink(missing_ok=True)
        self.say("stopped")
        return self.status


def list_offerings(config=CONFIG, out=sys.stdout):
    """The offerings and the routes loop.toml defines, each route with its candidates in order."""
    text = Path(config).read_text() if Path(config).exists() else ""
    _, offerings, routes, paces = parse_all(text)
    for spec in offerings.values():
        print(f"offering {fmt_offering(spec)}", file=out)
    for key, candidates in routes.items():
        print(f"route {key}: {fmt_candidates(candidates)}", file=out)
    for meter, pace in paces.items():
        print(f"meter {meter}: target {pace['target']:g}, max {pace['max']}", file=out)
    if not routes:
        print(f"no [routes] in {Path(config).name}: the loop runs plain rounds on its top-level tables", file=out)
    return 0


def check(config=CONFIG, out=sys.stdout, loop=None):
    loop = loop or Loop(config=config, out=out)
    _, _, summary = loop.inspect_work(claim=False)
    tag = "auto-routed [routes]" if loop.dispatch.routed else "unrouted"
    print(f"=== {tag} ===", file=out)
    print(f"abandoned recoverable: {summary['recovered'] or 'none'} (other live actors: {summary['other_live']})", file=out)
    print(f"matching stages ({len(summary['stages'])}): "
          + (", ".join(f"{i} [{s} -> {fmt_spec(sp)}]" for s, i, _, sp in summary["stages"]) or "none"), file=out)
    print(f"matching leaves ({len(summary['leaves'])}): "
          + (", ".join(f"{i} [{k} -> {fmt_spec(sp)}]" for k, i, _, sp in summary["leaves"]) or "none"), file=out)
    close_tag = f" -> {fmt_candidates(summary['close_route'])}" if summary["close_route"] else ""
    split_tag = f" -> {fmt_candidates(summary['split_route'])}" if summary["split_route"] else ""
    print(f"finished epics ({len(summary['finished_epics'])}{close_tag}): "
          + ("; ".join(summary["finished_epics"]) or "none"), file=out)
    print(f"splittable epics ({len(summary['split_epics'])}{split_tag}): "
          + (", ".join(summary["split_epics"]) or "none"), file=out)
    meters, flying = read_state(loop.pids)["meters"], in_flight(loop.pids, loop.alive)
    for meter, pace in loop.dispatch.paces.items():
        admits, percent, hours, rate = admission(meters.get(meter), pace, loop.now())
        print(f"meter {fmt_admission(meter, admits, percent, hours, rate, pace)}, {flying.get(meter, 0)} in flight", file=out)
    print(f"waiting on cooldowns or pace ({len(summary['cooled'])})" + ("".join(
        f"\n  {what} [{key}]: {fmt_waits(waits)}" for key, what, waits in summary["cooled"]) or ": none"), file=out)
    return 0


def main_loop(args):
    """One loop in this process: a worker of a pool, or a loop run --once."""
    loop = Loop(wait=args.wait, pool=args.worker)
    loop.record()
    pidfile = PIDS / str(os.getpid())
    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGUSR1):
        signal.signal(signum, loop.on_stop)
    signal.signal(signal.SIGHUP, loop.on_reload)
    loop.say("loop", f"actor {loop.actor}; stop with Ctrl-C or tools/loop.py --stop {os.getpid()}")
    try:
        status = loop.drive(once=args.once)
    finally:
        pidfile.unlink(missing_ok=True)
    if loop.reloading and not loop.stopping and not args.once:
        os.execv(sys.executable, [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]])
    if args.worker is not None and status == 0 and not loop.stopping:
        return DONE
    return status


def main_pool(args):
    """The pool of worker loops, in this process; each worker is this script with --worker."""
    text = CONFIG.read_text() if CONFIG.exists() else ""
    parse_all(text)
    worker = [sys.executable, str(Path(__file__).resolve()), "--wait", str(args.wait)]
    pool = Pool(worker)
    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGUSR1):
        signal.signal(signum, pool.on_stop)
    signal.signal(signal.SIGHUP, pool.on_reload)
    pool.say(f"pool {pool.pid}; resize with [pool] jobs in {CONFIG.name}, stop with Ctrl-C or tools/loop.py --stop")
    return pool.run()


SIGNALS = {signal.SIGTERM: "stopping after its run in flight", signal.SIGUSR1: "ending now",
           signal.SIGHUP: "re-executing after its run in flight"}


def pooled(folder, pid):
    """Whether the loop with this pid is a worker of a pool that still runs, which passes signals on."""
    pool = read_pid_file(folder, pid).get("pool")
    return isinstance(pool, int) and loop_alive(pool)


def send(pids, signum, folder=PIDS):
    """Signal each named loop, or every loop with a pid file except a live pool's workers, which their
    pool signals; a pid file whose process is no loop is removed."""
    named = [int(pid) for pid in pids] or sorted(int(path.name) for path in folder.glob("*")
                                                 if path.name.isdigit() and not pooled(folder, path.name))
    signalled = 0
    for pid in named:
        if loop_alive(pid):
            os.kill(pid, signum)
            print(f"loop {pid}: {SIGNALS[signum]}")
            signalled += 1
        else:
            (folder / str(pid)).unlink(missing_ok=True)
            print(f"loop {pid}: not running")
    if not named:
        print("no loop is running")
    return 0 if signalled or not named else 1


class Tests(unittest.TestCase):
    REPORT = textwrap.dedent("""\
        - atmo-1.2 Implemented: abc1234.

        Blocked questions:
        - atmo-1.9 P2: Should the loop ask?

        Notify: none
        Prover: atmo-1.2.3
        Loop: continue
        """)

    def test_a_report_gives_its_hand_off_and_its_loop_word(self):
        report = parse(self.REPORT)
        self.assertEqual((report.loop, report.prover, report.skeptic, report.notify), ("continue", "atmo-1.2.3", None, []))

    def test_markdown_around_a_key_is_read_through(self):
        report = parse("**Notify:** atmo-1.9 needs a decision: ask?\n- **Skeptic:** `atmo-1.4`\n**Loop: stop**\n")
        self.assertEqual((report.loop, report.skeptic, report.notify), ("stop", "atmo-1.4", ["atmo-1.9 needs a decision: ask?"]))

    def test_bullets_under_a_bare_notify_are_each_a_notification(self):
        report = parse("Notify:\n- atmo-1.9 needs a decision: a?\n- atmo-1.8 needs a decision: b?\nLoop: wait\n")
        self.assertEqual((report.loop, report.notify), ("wait", ["atmo-1.9 needs a decision: a?", "atmo-1.8 needs a decision: b?"]))

    def test_a_retry_line_names_the_issue_the_next_round_is_pinned_to(self):
        report = parse("- atmo-1.2 Attempt 1 ended at its bound.\nNotify: none\n**Retry:** `atmo-1.2`\nLoop: continue\n")
        self.assertEqual((report.loop, report.retry, report.prover), ("continue", "atmo-1.2", None))
        self.assertIsNone(parse(self.REPORT).retry)

    def test_a_report_without_a_loop_line_has_no_loop_word(self):
        self.assertIsNone(parse("The round ran out of turns.\nLoop: maybe\n").loop)

    def test_the_last_result_of_a_stream_is_the_report_and_turns_add_up(self):
        lines = [
            "not json",
            json.dumps({"type": "assistant", "message": {"content": [
                {"type": "tool_use", "name": "Bash", "input": {"command": "tools/land.py", "description": "Land"}}]}}),
            json.dumps({"type": "rate_limit_event", "rate_limit_info": {"status": "allowed_warning", "rateLimitType": "seven_day", "utilization": 0.82}}),
            json.dumps({"type": "result", "subtype": "success", "result": "parked on the gate", "num_turns": 3,
                        "usage": {"input_tokens": 10, "output_tokens": 2}}),
            json.dumps({"type": "result", "subtype": "success", "result": "the report", "num_turns": 4,
                        "usage": {"cache_read_input_tokens": 1000}}),
        ]
        shown = []
        run = follow(lines, shown.append)
        self.assertEqual((run.report, run.error, run.turns, run.weighted, run.limited), ("the report", False, 7, 120.0, False))
        self.assertEqual(shown, ["not json", "Bash: Land", "weekly usage 82%"])

    def test_a_rejected_rate_limit_is_a_usage_limit_with_its_reset(self):
        lines = [json.dumps({"type": "rate_limit_event", "rate_limit_info": {"status": "rejected", "resetsAt": 5000}}),
                 json.dumps({"type": "result", "subtype": "success", "is_error": True, "result": "You've hit your limit"})]
        run = follow(lines, lambda text: None)
        self.assertEqual((run.error, run.limited, run.reset), (True, True, 5000))

    def test_a_process_is_a_loop_when_an_argument_ends_in_tools_loop_py(self):
        self.assertFalse(loop_alive(4194305))
        sleep = [sys.executable, "-c", "import time; print('up', flush=True); time.sleep(60)"]
        plain_proc = subprocess.Popen(sleep, stdout=subprocess.PIPE, text=True)
        other = subprocess.Popen(sleep + ["/x/tools/loop.py"], stdout=subprocess.PIPE, text=True)
        try:
            for process in (plain_proc, other):
                process.stdout.readline()
                process.stdout.close()
            self.assertEqual((loop_alive(plain_proc.pid), loop_alive(other.pid)), (False, True))
        finally:
            for process in (plain_proc, other):
                process.kill()
                process.wait()

    def test_stop_signals_a_live_loop_and_drops_a_stale_pid_file(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            catcher = "import signal, sys, time\nsignal.signal(signal.SIGTERM, lambda *a: sys.exit(7))\nprint('up', flush=True)\ntime.sleep(60)\n"
            other = subprocess.Popen([sys.executable, "-c", catcher, "/x/tools/loop.py"], stdout=subprocess.PIPE, text=True)
            other.stdout.readline()
            other.stdout.close()
            (folder / str(other.pid)).write_text("")
            (folder / "4194305").write_text("")
            try:
                with open(os.devnull, "w") as quiet:
                    sys.stdout, saved = quiet, sys.stdout
                    try:
                        self.assertEqual(send([], signal.SIGTERM, folder), 0)
                    finally:
                        sys.stdout = saved
                self.assertEqual(other.wait(timeout=10), 7)
            finally:
                other.kill()
                other.wait()
            self.assertFalse((folder / "4194305").exists())

    def test_loop_toml_gives_each_kind_its_flags(self):
        text = '[round]\nmodel = "opus"\nautocompact = "200k"\n[prover]\neffort = "xhigh"\nfallback-model = "opus"\n[skeptic]\nautocompact = "1M"\n'
        self.assertEqual(options(text), {"round": ["--model", "opus", "--autocompact", "200k"],
                                         "prover": ["--effort", "xhigh", "--fallback-model", "opus"],
                                         "skeptic": ["--autocompact", "1M"]})
        self.assertEqual(options(""), {})
        self.assertEqual(options('[retry]\nmodel = "fable"\neffort = "high"\nautocompact = "200k"\nfallback-model = "opus"\n'),
                         {"retry": ["--model", "fable", "--effort", "high", "--autocompact", "200k", "--fallback-model", "opus"]})

    def test_loop_toml_refuses_what_claude_does_not_take(self):
        for text in ("[round\n", "[driver]\nmodel = \"opus\"\n", "model = \"opus\"\n", "[round]\nturns = \"9\"\n",
                     "[round]\neffort = \"huge\"\n", "[round]\nautocompact = \"50k\"\n", "[round]\nautocompact = \"2m\"\n",
                     "[round]\nautocompact = 200000\n", "[round]\nmodel = \"--dangerously\"\n", "[retry]\nturns = \"9\"\n",
                     "[retry]\neffort = \"huge\"\n"):
            with self.assertRaises(ValueError, msg=text):
                options(text)

    # The driver against a fake claude and a fake bd, which log their arguments.

    FAKE_CLAUDE = textwrap.dedent("""\
        import json, os, sys, time
        folder = os.environ["FAKE"]
        open(os.path.join(folder, "claude.log"), "a").write(json.dumps(sys.argv[1:] + [os.environ["BEADS_ACTOR"]]) + "\\n")
        temporary = [os.environ.get("TMPDIR"), os.environ.get("CLAUDE_CODE_TMPDIR")]
        open(os.path.join(folder, "temporary.log"), "a").write(json.dumps(temporary + [os.path.isdir(temporary[0] or "")]) + "\\n")
        open(os.path.join(folder, "pidfile.log"), "a").write(open(os.path.join(folder, str(os.getppid()))).read())
        queue = sorted(name for name in os.listdir(folder) if name.startswith("reply-"))
        reply = open(os.path.join(folder, queue[0])).read()
        os.remove(os.path.join(folder, queue[0]))
        if reply.startswith("SLEEP"):
            time.sleep(60)
        error = reply.startswith("ERROR")
        print(json.dumps({"type": "result", "subtype": "success", "is_error": error, "result": reply, "num_turns": 1, "usage": {}}))
        """)
    FAKE_BD = textwrap.dedent("""\
        import json, os, sys
        folder = os.environ["FAKE"]
        args = sys.argv[1:]
        open(os.path.join(folder, "bd.log"), "a").write(json.dumps(args) + "\\n")
        def emit(filename, fallback="[]"):
            p = os.path.join(folder, filename)
            print(open(p).read() if os.path.exists(p) else fallback)
        if args[:3] == ["list", "-s", "blocked"]:
            print("● atmo-1.9 ● P2 Should the loop ask?")
        elif args[:3] == ["list", "-s", "in_progress"]:
            if "--assignee" in args:
                emit("held")
            else:
                emit("in_progress.json")
        elif args[:2] == ["ready", "--exclude-type=epic"]:
            emit("ready.json")
        elif args[:2] == ["ready", "-t"]:
            emit("ready_epics.json")
        elif args[:2] == ["list", "--all"]:
            emit("all.json")
        """)

    def driver(self, folder, *replies, **given):
        for name, text in (("claude", self.FAKE_CLAUDE), ("bd", self.FAKE_BD)):
            path = folder / name
            path.write_text(f"#!{sys.executable}\n{text}")
            path.chmod(0o755)
        for existing in folder.glob("reply-*"):
            existing.unlink()
        for number, reply in enumerate(replies):
            (folder / f"reply-{number:03}").write_text(reply)
        os.environ["FAKE"] = str(folder)
        clock = [0.0]
        sink = open(os.devnull, "w")
        self.addCleanup(sink.close)
        loop = Loop(claude=str(folder / "claude"), bd=str(folder / "bd"), notifier="no-such-notifier",
                    cwd=folder, pids=folder, config=folder / "loop.toml", scratch=folder / "scratch",
                    sleep=lambda seconds: clock.__setitem__(0, clock[0] + seconds),
                    now=lambda: clock[0], out=sink, **given)
        return loop, clock

    def log(self, folder, name):
        path = folder / f"{name}.log"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def test_a_prover_hand_off_runs_the_prover_records_its_report_then_the_loop_goes_on_to_a_stop(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Notify: none\nProver: atmo-1.2\nLoop: continue\n", "Reached 3 verified, 0 errors.",
                                  "Notify: atmo-1.9 needs a decision: ask?\nLoop: stop\n")
            self.assertEqual(loop.drive(), 0)
            agents = [(call[2], call[-2], call[-1]) for call in self.log(folder, "claude")]
            self.assertEqual(agents, [
                ("round", "Run one round.", loop.actor),
                ("prover", f"Issue atmo-1.2, worktree {folder.parent / 'atmo-1.2'}. Your input is the issue's last Prover input note.", loop.actor),
                ("round", "Run one round.", loop.actor)])
            self.assertEqual(self.log(folder, "bd"), [
                ["update", "atmo-1.2", "--append-notes", "Prover report: Reached 3 verified, 0 errors."],
                ["update", "atmo-1.2", "-s", "open", "--assignee", ""],
                ["list", "-s", "blocked"]])

    def test_each_session_keeps_its_temporary_files_in_the_scratch_directory(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Notify: none\nProver: atmo-1.2\nLoop: continue\n", "Reached 3 verified, 0 errors.",
                                  "Notify: none\nLoop: stop\n")
            self.assertEqual(loop.drive(), 0)
            scratch = str(folder / "scratch")
            self.assertEqual(self.log(folder, "temporary"), [[scratch, scratch, True]] * 3)

    def test_the_pid_file_names_the_session_in_flight_and_none_between_sessions(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            (folder / "loop.toml").write_text('[round]\nmodel = "fable"\neffort = "high"\nautocompact = "200k"\n')
            loop, _ = self.driver(folder, "Notify: none\nProver: atmo-1.2\nLoop: continue\n", "Reached 3 verified, 0 errors.",
                                  "Notify: none\nLoop: stop\n")
            self.assertEqual(loop.drive(), 0)
            round_, prover = ({"kind": kind, "offering": None, "harness": "claude", "model": model, "effort": effort,
                               "meters": []}
                              for kind, model, effort in (("round", "fable", "high"), ("prover", None, None)))
            self.assertEqual(self.log(folder, "pidfile"), [{"pid": os.getpid(), "session": session} for session in (round_, prover, round_)])
            self.assertEqual(json.loads((folder / str(os.getpid())).read_text()), {"pid": os.getpid(), "session": None})

    def test_a_stop_before_a_hand_off_releases_the_issue_without_running_the_skeptic(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Skeptic: atmo-1.4\nLoop: continue\n")
            real = loop.agent

            def agent_then_stop(kind, prompt, **given):
                run = real(kind, prompt, **given)
                loop.on_stop(signal.SIGTERM, None)
                return run
            loop.agent = agent_then_stop
            self.assertEqual(loop.drive(), 0)
            self.assertEqual([call[2] for call in self.log(folder, "claude")], ["round"])
            self.assertEqual(self.log(folder, "bd"), [
                ["update", "atmo-1.4", "--append-notes",
                 "Skeptic not run: the loop stopped before it started; the next round hands it over again."],
                ["update", "atmo-1.4", "-s", "open", "--assignee", ""]])

    def test_each_session_takes_up_loop_toml_as_it_stands_and_a_wrong_edit_keeps_the_last_values(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Prover: atmo-1.2\nLoop: continue\n", "proved", "Loop: continue\n", "Loop: stop\n")
            (folder / "loop.toml").write_text('[round]\nautocompact = "200k"\n[prover]\nmodel = "opus"\n')
            real = loop.agent
            edits = iter(['[round]\nautocompact = "300k"\n', '[round]\neffort = "huge"\n', None])

            def agent_then_edit(kind, prompt, **given):
                run = real(kind, prompt, **given)
                edit = next(edits, None)
                if edit:
                    (folder / "loop.toml").write_text(edit)
                return run
            loop.agent = agent_then_edit
            self.assertEqual(loop.drive(), 0)
            flags = [(call[2], call[8:-2]) for call in self.log(folder, "claude")]
            self.assertEqual(flags, [("round", ["--autocompact", "200k"]),
                                     ("prover", []),
                                     ("round", ["--autocompact", "300k"]),
                                     ("round", ["--autocompact", "300k"])])

    def test_a_reload_lets_the_round_and_its_hand_off_finish_then_ends_the_drive(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Prover: atmo-1.2\nLoop: continue\n", "proved", "Loop: stop\n")
            real = loop.agent

            def agent_then_reload(kind, prompt, **given):
                run = real(kind, prompt, **given)
                if kind == "round":
                    loop.on_reload(signal.SIGHUP, None)
                return run
            loop.agent = agent_then_reload
            self.assertEqual(loop.drive(), 0)
            self.assertTrue(loop.reloading)
            self.assertEqual([call[2] for call in self.log(folder, "claude")], ["round", "prover"])
            self.assertEqual(self.log(folder, "bd"), [["update", "atmo-1.2", "--append-notes", "Prover report: proved"],
                                                      ["update", "atmo-1.2", "-s", "open", "--assignee", ""]])

    def test_wait_pauses_and_failures_back_off_until_the_fourth_ends_the_loop(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, "Loop: wait\n", "ERROR", "no loop line", "ERROR", "ERROR", wait=900)
            self.assertEqual(loop.drive(), 1)
            self.assertEqual(clock[0], 900 + 60 + 120 + 240)
            self.assertEqual(self.log(folder, "bd"), [["list", "-s", "in_progress", "--assignee", loop.actor, "--json"]] * 3)
            self.assertEqual([call[-2] for call in self.log(folder, "claude")], ["Run one round."] * 5)

    RETRY = "Run one round. Issue {} is yours: a round of this loop left it unfinished."
    TABLES = '[round]\nmodel = "fable"\neffort = "medium"\n[retry]\nmodel = "fable"\neffort = "high"\nautocompact = "200k"\n'

    def sessions(self, folder):
        return [(call[2], call[8:-2], call[-2]) for call in self.log(folder, "claude")]

    def test_a_retry_line_pins_the_next_round_to_the_issue_at_the_retry_tables_flags_and_its_hand_off_runs(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Notify: none\nRetry: atmo-1.2\nLoop: continue\n", "Prover: atmo-1.2\nLoop: continue\n",
                                  "proved", "Loop: stop\n")
            (folder / "loop.toml").write_text(self.TABLES)
            self.assertEqual(loop.drive(), 0)
            plain_flags, strong = ["--model", "fable", "--effort", "medium"], ["--model", "fable", "--effort", "high", "--autocompact", "200k"]
            self.assertEqual(self.sessions(folder), [
                ("round", plain_flags, "Run one round."),
                ("round", strong, self.RETRY.format("atmo-1.2")),
                ("prover", [], f"Issue atmo-1.2, worktree {folder.parent / 'atmo-1.2'}. Your input is the issue's last Prover input note."),
                ("round", plain_flags, "Run one round.")])
            self.assertEqual(self.log(folder, "bd"), [
                ["update", "atmo-1.2", "--append-notes", "Prover report: proved"],
                ["update", "atmo-1.2", "-s", "open", "--assignee", ""],
                ["list", "-s", "blocked"]])

    def test_a_round_without_a_report_that_left_one_issue_held_is_followed_by_a_retry_on_it(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, "ERROR", "Loop: stop\n")
            (folder / "loop.toml").write_text(self.TABLES)
            (folder / "held").write_text('[{"id": "atmo-1.3", "status": "in_progress"}]')
            self.assertEqual(loop.drive(), 0)
            self.assertEqual([(flags[3], prompt) for _, flags, prompt in self.sessions(folder)],
                             [("medium", "Run one round."), ("high", self.RETRY.format("atmo-1.3"))])
            self.assertEqual(clock[0], 60)
            self.assertEqual(self.log(folder, "bd")[0], ["list", "-s", "in_progress", "--assignee", loop.actor, "--json"])

    def test_a_round_without_a_report_that_left_two_issues_held_is_followed_by_a_plain_round(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "no loop line", "Loop: stop\n")
            (folder / "held").write_text('[{"id": "atmo-1.3"}, {"id": "atmo-1.4"}]')
            self.assertEqual(loop.drive(), 0)
            self.assertEqual([call[-2] for call in self.log(folder, "claude")], ["Run one round."] * 2)

    def test_a_failed_retry_counts_as_a_failed_round_and_the_fourth_failure_ends_the_loop(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, "ERROR", "ERROR", "no loop line", "ERROR")
            (folder / "held").write_text('[{"id": "atmo-1.3"}]')
            self.assertEqual(loop.drive(), 1)
            self.assertEqual([call[-2] for call in self.log(folder, "claude")], ["Run one round."] + [self.RETRY.format("atmo-1.3")] * 3)
            self.assertEqual(clock[0], 60 + 120 + 240)

    def test_a_second_signal_ends_the_session_in_flight(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "SLEEP")
            started = time.monotonic()
            timer = __import__("threading").Timer(1.0, lambda: (loop.on_stop(signal.SIGTERM, None), loop.on_stop(signal.SIGTERM, None)))
            timer.start()
            self.assertEqual(loop.drive(), 0)
            self.assertLess(time.monotonic() - started, 20)

    def test_list_shows_offerings_and_routes_and_loop_toml_takes_no_profiles(self):
        with tempfile.TemporaryDirectory() as folder:
            config = Path(folder) / "loop.toml"
            config.write_text('[round]\nmodel = "fable"\n\n[offerings.carbon]\nharness = "agy"\nmodel = "gemini-4-carbon-high"\n'
                              'meters = ["gemini-week"]\n\n[offerings.opus]\nmodel = "opus"\nmeters = ["claude-week"]\n\n'
                              '[routes.default]\ncandidates = ["opus"]\n\n[routes.tool]\ncandidates = ["carbon", "opus"]\n\n'
                              '[routes.skeptic]\ndisabled = true\n\n[meters.claude-week]\ntarget = 95\nmax = 4\n')
            shown = io.StringIO()
            self.assertEqual(list_offerings(config, shown), 0)
            lines = shown.getvalue().splitlines()
            self.assertEqual(lines[:2], ["offering carbon: agy(--model gemini-4-carbon-high) on gemini-week",
                                         "offering opus: claude(--model opus) on claude-week"])
            self.assertIn("route tool: carbon > opus", lines)
            self.assertIn("route spec: opus", lines)
            self.assertIn("route skeptic: disabled", lines)
            self.assertEqual(lines[-1], "meter claude-week: target 95, max 4")
            self.assertEqual(len(lines), 3 + len(ROUTE_KEYS))
            config.write_text('[round]\nmodel = "fable"\n')
            shown = io.StringIO()
            list_offerings(config, shown)
            self.assertEqual(shown.getvalue(), "no [routes] in loop.toml: the loop runs plain rounds on its top-level tables\n")
        self.assertEqual(options('[round]\nmodel = "fable"\nautocompact = "200k"\n'),
                         {"round": ["--model", "fable", "--autocompact", "200k"]})
        for bad in ('[profiles.carbon]\nharness = "agy"\n',
                    '[offerings.x]\nharness = "agy"\nautocompact = "200k"\nmeters = ["gemini-week"]\n',
                    '[offerings.x]\nharness = "agy"\nfallback-model = "opus"\nmeters = ["gemini-week"]\n',
                    '[offerings.x]\nmode = "auto"\nmeters = ["claude-week"]\n',
                    '[offerings.x]\nharness = "grok"\nmeters = ["claude-week"]\n'):
            with self.assertRaises(ValueError, msg=bad):
                parse_dispatch(bad)

    def test_agy_stream_events_report_tools_text_steps_usage_and_limits(self):
        lines = [
            json.dumps({"event": "init", "conversation_id": "c1", "init": {"model": "gemini-4-carbon-high"}}),
            json.dumps({"event": "step_update", "step_update": {
                "step_index": 1, "state": "ACTIVE", "step_type": "tool", "tool_name": "run_command",
                "tool_info": {"name": "run_command", "parameters": {"CommandLine": "tools/land.py", "toolSummary": "Land branch"}}}}),
            json.dumps({"event": "step_update", "step_update": {"step_index": 1, "state": "DONE", "step_type": "tool"}}),
            json.dumps({"event": "step_update", "step_update": {
                "step_index": 2, "state": "ACTIVE", "step_type": "agent_response", "text_delta": "Landed "}}),
            json.dumps({"event": "step_update", "step_update": {
                "step_index": 2, "state": "DONE", "step_type": "agent_response", "text_delta": "cleanly.\nLoop: continue\n"}}),
            json.dumps({"event": "result", "result": {
                "status": "SUCCESS", "response": "Landed cleanly.\nLoop: continue\n", "num_turns": 1,
                "usage": {"input_tokens": 5000, "cache_read_tokens": 4000, "output_tokens": 100, "thinking_tokens": 50}}}),
        ]
        shown = []
        run = follow(lines, shown.append)
        self.assertEqual((run.report, run.error, run.turns, run.weighted, run.limited),
                         ("Landed cleanly.\nLoop: continue\n", False, 1, 1000 + 400 + 5 * 150, False))
        self.assertEqual(shown, ["run_command: Land branch", "says: Landed cleanly."])

        timeout_lines = [json.dumps({"event": "result", "result": {
            "status": "ERROR", "finished_reason": "print_timeout", "response": "partial", "usage": {}}})]
        self.assertTrue(follow(timeout_lines, lambda _: None).error)

        quota_lines = [json.dumps({"event": "result", "result": {
            "status": "ERROR", "finished_reason": "error", "response": "Quota exceeded: resource exhausted", "usage": {}}})]
        quota_run = follow(quota_lines, lambda _: None)
        self.assertEqual((quota_run.error, quota_run.limited), (True, True))

    def test_agy_agent_invokes_agy_with_procedure_body_and_prompt_at_p_flag(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            agents_dir = folder / ".claude" / "agents"
            agents_dir.mkdir(parents=True)
            (agents_dir / "round.md").write_text("---\nname: round\nmodel: opus\n---\n\nYou run one round.\n")
            fake_agy = folder / "agy"
            fake_agy.write_text(
                f"#!{sys.executable}\nimport json, os, sys\n"
                f"open({str(folder / 'agy.log')!r}, 'a').write(json.dumps(sys.argv[1:] + [os.environ['BEADS_ACTOR']]) + '\\n')\n"
                "print(json.dumps({'event': 'result', 'result': {'status': 'SUCCESS', 'response': 'Loop: stop\\n', 'num_turns': 1, 'usage': {}}}))\n"
            )
            fake_agy.chmod(0o755)
            loop, _ = self.driver(folder, agy=str(fake_agy))
            (folder / "loop.toml").write_text('[offerings.carbon]\nharness = "agy"\nmodel = "gemini-4-carbon-high"\neffort = "high"\n'
                                              'meters = ["gemini-week"]\n[routes.tool]\ncandidates = ["carbon"]\n')
            (folder / "ready.json").write_text('[{"id": "atmo-1.2", "title": "Fix tool", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]')
            self.assertEqual(loop.drive(once=True), 0)
            [call] = self.log(folder, "agy")
            self.assertEqual(call[:8], ["--output-format", "stream-json", "--dangerously-skip-permissions",
                                        "--model", "gemini-4-carbon-high", "--effort", "high", "-p"])
            self.assertTrue(call[8].startswith("You run one round.\n\nRun one round. Issue atmo-1.2 is yours"))
            self.assertNotIn("model: opus", call[8])
            self.assertEqual(call[9], loop.actor)

    GROK = ('[offerings.grok-high]\nharness = "grok"\nmodel = "grok-4.7"\neffort = "high"\nmeters = ["grok-week"]\n\n'
            '[offerings.opus]\nmodel = "opus"\nmeters = ["claude-week"]\n\n[routes.tool]\ncandidates = ["grok-high", "opus"]\n')

    def stub_grok(self, folder, *lines):
        """A fake grok that logs its arguments and its actor and prints `lines`, each a stream event."""
        fake = folder / "grok"
        fake.write_text(
            f"#!{sys.executable}\nimport json, os, sys\n"
            f"open({str(folder / 'grok.log')!r}, 'a').write(json.dumps(sys.argv[1:] + [os.environ['BEADS_ACTOR']]) + '\\n')\n"
            f"print({chr(10).join(json.dumps(line) for line in lines)!r})\n")
        fake.chmod(0o755)
        return str(fake)

    def test_a_grok_offering_takes_a_model_an_effort_and_grok_meters(self):
        [grok, opus] = parse_dispatch(self.GROK).routes["tool"]
        self.assertEqual((grok.harness, grok.name, grok.flags, grok.meters),
                         ("grok", "grok-high", ["--model", "grok-4.7", "--effort", "high"], ("grok-week",)))
        for bad in ('[offerings.x]\nharness = "grok"\nmeters = ["gemini-week"]\n',
                    '[offerings.x]\nharness = "grok"\nautocompact = "200k"\nmeters = ["grok-week"]\n',
                    '[offerings.x]\nharness = "grok"\nmode = "auto"\nmeters = ["grok-week"]\n',
                    '[offerings.x]\nharness = "grok"\neffort = "huge"\nmeters = ["grok-week"]\n'):
            with self.assertRaises(ValueError, msg=bad):
                parse_dispatch(bad)

    def test_a_grok_session_is_grok_p_with_the_procedure_body_the_prompt_and_the_project_roots_rules(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            agents_dir = folder / ".claude" / "agents"
            agents_dir.mkdir(parents=True)
            (agents_dir / "round.md").write_text("---\nname: round\nmodel: opus\n---\n\nYou run one round.\n")
            rules = folder / "root-rules.md"
            rules.write_text("# Local rules\n")
            grok = self.stub_grok(
                folder,
                {"type": "system", "subtype": "init", "model": "grok-4.7"},
                {"type": "assistant", "message": {"content": [
                    {"type": "text", "text": "Landing it.\nMore."},
                    {"type": "tool_use", "name": "run_terminal_command", "input": {"command": "tools/land.py", "description": "Land the branch"}},
                    {"type": "tool_use", "name": "read_file", "input": {"target_file": "tools/land.py"}}]}},
                {"type": "result", "subtype": "success", "is_error": False, "num_turns": 3, "result": "Landed.\nLoop: stop\n",
                 "usage": {"input_tokens": 1000, "cache_read_input_tokens": 400, "cache_creation_input_tokens": 0, "output_tokens": 10}})
            said = io.StringIO()
            loop, _ = self.driver(folder, grok=grok, rules=rules)
            loop.out = said
            (folder / "loop.toml").write_text(self.GROK)
            (folder / "ready.json").write_text('[{"id": "atmo-1.2", "title": "Fix tool", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]')
            self.assertEqual(loop.drive(once=True), 0)
            [call] = self.log(folder, "grok")
            self.assertEqual(call[0], "-p")
            self.assertTrue(call[1].startswith("You run one round.\n\nRun one round. Issue atmo-1.2 is yours"))
            self.assertNotIn("model: opus", call[1])
            self.assertEqual(call[2:], ["--output-format", "streaming-messages-json", "--always-approve", "--trust",
                                        "--background-wait-timeout", str(GROK_BACKGROUND_WAIT), "--rules", "# Local rules\n",
                                        "--model", "grok-4.7", "--effort", "high", loop.actor])
            for line in ("says: Landing it.", "run_terminal_command: Land the branch", "read_file: tools/land.py"):
                self.assertIn(line, said.getvalue())
            self.assertEqual(read_sessions(folder), [
                self.row(loop, issue="atmo-1.2", work_kind="tool", route="tool", offering="grok-high", harness="grok",
                         model="grok-4.7", effort="high", turns=3, weighted=1090.0, loop="stop")])
            self.assertEqual(self.log(folder, "claude"), [])

            # A checkout with no rules file beside its worktrees, as a clone is, passes none.
            rules.unlink()
            self.assertEqual(loop.drive(once=True), 0)
            self.assertNotIn("--rules", self.log(folder, "grok")[-1])

    def test_a_grok_result_that_names_a_limit_cools_its_meters_and_the_leaf_goes_to_the_next_candidate(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            grok = self.stub_grok(folder, {"type": "result", "subtype": "error_during_execution", "is_error": True,
                                           "num_turns": 0, "errors": ["You have reached your usage limit."], "usage": {}})
            loop, clock = self.driver(folder, "Loop: stop\n", grok=grok)
            clock[0] = 100.0
            (folder / "loop.toml").write_text(self.GROK)
            (folder / "ready.json").write_text('[{"id": "atmo-1.2", "title": "Fix tool", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]')
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(read_state(folder)["cooldown"], {"grok-week": {"harness": "grok", "until": 3700.0}})
            self.assertEqual(len(self.log(folder, "grok")), 1)
            [call] = self.log(folder, "claude")
            self.assertEqual(call[call.index("--model") + 1], "opus")
            self.assertEqual([(row["harness"], row["error"], row["limited"]) for row in read_sessions(folder)],
                             [("grok", 1, 1), ("claude", 0, 0)])

    def test_zero_token_precheck_skips_llm_when_no_work_matches_and_recovers_abandoned_leaves(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, "Loop: stop\n", wait=300)
            (folder / "loop.toml").write_text(self.OFFERINGS + '[routes.tool]\ncandidates = ["sonnet"]\n')
            (folder / "ready.json").write_text('[{"id": "atmo-1.9", "title": "Prove kernel spec", "issue_type": "task", "priority": 1, "labels": ["kind:spec"]}]')
            self.assertEqual(loop.drive(), 0)
            self.assertEqual(self.log(folder, "claude"), [])
            self.assertEqual(clock[0], 0.0)

            # While a peer loop is alive, the idle loop waits instead of exiting, then stops once signalled.
            peer = subprocess.Popen([sys.executable, "-c", "import time; print('up', flush=True); time.sleep(60)", "/x/tools/loop.py"],
                                    stdout=subprocess.PIPE, text=True)
            try:
                peer.stdout.readline()
                peer.stdout.close()
                (folder / str(peer.pid)).write_text(f"{peer.pid}\n")
                waits = [0]

                def sleep_then_stop(seconds):
                    clock[0] += seconds
                    waits[0] += 1
                    if waits[0] >= 300:
                        loop.stopping = True
                loop.sleep = sleep_then_stop
                self.assertEqual(loop.drive(), 0)
                self.assertEqual(self.log(folder, "claude"), [])
                self.assertGreaterEqual(clock[0], 300.0)
            finally:
                peer.kill()
                peer.wait()
                (folder / str(peer.pid)).unlink(missing_ok=True)

            (folder / "in_progress.json").write_text('[{"id": "atmo-1.5", "status": "in_progress", "assignee": "loop-4194305", "labels": ["kind:tool"]}]')
            loop.recover_abandoned()
            bd_calls = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.5", "-s", "open", "--assignee", ""], bd_calls)

    def test_routes_claim_matching_leaf_by_inference_and_run_epic_close_without_stealing_other_leaves(self):
        by_id = {
            "atmo-1": {"id": "atmo-1", "issue_type": "epic", "title": "Star", "description": "Tier 1, Tier 2, Tier 3"},
            "atmo-1.1": {"id": "atmo-1.1", "parent": "atmo-1", "issue_type": "epic", "title": "Kernel", "description": "Tier 1."},
            "atmo-1.2": {"id": "atmo-1.2", "parent": "atmo-1", "issue_type": "epic", "title": "Tools", "description": "Tier 3."},
        }
        self.assertEqual(classify_issue({"id": "atmo-1.1.1", "parent": "atmo-1.1", "title": "Remove external_body in list.rs"}, by_id), "proof")
        self.assertEqual(classify_issue({"id": "atmo-1.1.2", "parent": "atmo-1.1", "title": "Endpoint send and receive spec"}, by_id), "spec")
        self.assertEqual(classify_issue({"id": "atmo-1.2.1", "parent": "atmo-1.2", "title": "Update status page"}, by_id), "tool")
        self.assertEqual(classify_issue({"id": "atmo-1.1.3", "parent": "atmo-1.1", "title": "Review: Kernel", "labels": ["review"]}, by_id), "review")

        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Loop: continue\n", "Loop: continue\n")
            (folder / "loop.toml").write_text(self.OFFERINGS + '[routes.tool]\ncandidates = ["sonnet"]\n'
                                              '[routes.epic-close]\ncandidates = ["sonnet"]\n')
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1.2", "parent": "atmo-1.1", "title": "Endpoint spec", "issue_type": "task", "priority": 0, "labels": ["kind:spec"]},
                {"id": "atmo-1.2.1", "parent": "atmo-1.2", "title": "Status script", "issue_type": "task", "priority": 2, "labels": ["kind:tool"]},
            ]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertIn(["update", "atmo-1.2.1", "--claim"], self.log(folder, "bd"))
            self.assertTrue(self.log(folder, "claude")[0][-2].startswith("Run one round. Issue atmo-1.2.1 is yours"))

            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1.2", "parent": "atmo-1.1", "title": "Endpoint spec", "issue_type": "task", "priority": 0, "labels": ["kind:spec"]},
            ]))
            (folder / "all.json").write_text(json.dumps([
                {"id": "atmo-1", "issue_type": "epic", "status": "open", "priority": 0},
                {"id": "atmo-1.1", "parent": "atmo-1", "issue_type": "epic", "status": "open", "priority": 1},
                {"id": "atmo-1.1.2", "parent": "atmo-1.1", "issue_type": "task", "status": "open", "priority": 0, "labels": ["kind:spec"]},
                {"id": "atmo-1.3", "parent": "atmo-1", "issue_type": "epic", "status": "open", "priority": 2},
                {"id": "atmo-1.3.1", "parent": "atmo-1.3", "issue_type": "task", "status": "closed", "priority": 2,
                 "closed_at": "2026-11-11T12:00:00Z", "close_reason": "abc: gate"},
            ]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertIn("Epic round only", self.log(folder, "claude")[1][-2])

    def test_disabled_hand_off_routes_stamp_stage_labels_and_a_loop_routing_them_runs_them(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            (folder / "loop.toml").write_text(self.OFFERINGS + textwrap.dedent("""\
                [routes.proof]
                candidates = ["sonnet"]
                [routes.review]
                candidates = ["sonnet"]
                [routes.needs-land]
                candidates = ["sonnet"]
                [routes.prover]
                disabled = true
                [routes.skeptic]
                disabled = true
                [routes.retry]
                disabled = true
                """))
            carbon, _ = self.driver(folder, "Prover: atmo-1.1\nLoop: continue\n", "Skeptic: atmo-1.2\nLoop: continue\n",
                                    "Retry: atmo-1.3\nLoop: continue\n")
            for issue_id, lbl in (("atmo-1.1", "kind:proof"), ("atmo-1.2", "review"), ("atmo-1.3", "kind:proof")):
                (folder / "ready.json").write_text(json.dumps([{"id": issue_id, "title": "x", "issue_type": "task", "priority": 1, "labels": [lbl]}]))
                self.assertEqual(carbon.drive(once=True), 0)
            bd_calls = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.1", "--add-label", "stage:needs-prover", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.2", "--add-label", "stage:needs-skeptic", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.3", "--add-label", "stage:escalated", "-s", "open", "--assignee", ""], bd_calls)

            (folder / "loop.toml").write_text(self.OFFERINGS + textwrap.dedent("""\
                [offerings.fable-xhigh]
                model = "fable"
                effort = "xhigh"
                meters = ["claude-week", "claude-fable"]
                [routes.prover]
                candidates = ["fable-xhigh"]
                [routes.retry]
                candidates = ["fable-xhigh"]
                """))
            fable, _ = self.driver(folder, "Verified 10, 0 errors.", "Loop: continue\n")
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "x", "issue_type": "task", "priority": 1, "labels": ["kind:proof", "stage:needs-prover"]}
            ]))
            self.assertEqual(fable.drive(once=True), 0)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.3", "title": "y", "issue_type": "task", "priority": 1, "labels": ["kind:proof", "stage:escalated"]}
            ]))
            self.assertEqual(fable.drive(once=True), 0)
            fable_sessions = [(call[2], call[8:-2], call[-2]) for call in self.log(folder, "claude")[-2:]]
            self.assertEqual(fable_sessions[0][0], "prover")
            self.assertEqual(fable_sessions[0][1], ["--model", "fable", "--effort", "xhigh"])
            self.assertEqual(fable_sessions[1][0], "round")
            self.assertEqual(fable_sessions[1][1], ["--model", "fable", "--effort", "xhigh"])
            self.assertTrue(fable_sessions[1][2].startswith("Run one round. Issue atmo-1.3 is yours"))
            bd_after = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.1", "--remove-label", "stage:needs-prover", "--add-label", "stage:needs-land", "-s", "open", "--assignee", ""], bd_after)
            self.assertIn(["update", "atmo-1.3", "--remove-label", "stage:escalated"], bd_after)

    OFFERINGS = textwrap.dedent("""\
        [offerings.carbon]
        harness = "agy"
        model = "gemini-4-carbon-high"
        meters = ["gemini-week", "gemini-5h"]

        [offerings.carbon-low]
        harness = "agy"
        model = "gemini-4-carbon-low"
        meters = ["gemini-week", "gemini-5h"]

        [offerings.sonnet]
        model = "sonnet"
        effort = "high"
        meters = ["claude-week"]

        [offerings.opus]
        model = "opus"
        effort = "high"
        meters = ["claude-week"]

        [offerings.opus-xhigh]
        model = "opus"
        effort = "xhigh"
        meters = ["claude-week"]

        [offerings.fable]
        model = "fable"
        effort = "xhigh"
        autocompact = "400k"
        meters = ["claude-week", "claude-fable"]
        """)
    ROUTES = OFFERINGS + textwrap.dedent("""\
        [routes.default]
        candidates = ["carbon", "sonnet", "opus"]

        [routes.spec]
        candidates = ["fable", "opus"]

        [routes.epic-close]
        candidates = ["carbon-low", "sonnet"]

        [routes.needs-land]
        candidates = ["carbon-low", "sonnet"]

        [routes.prover]
        candidates = ["fable", "opus-xhigh"]

        [routes.skeptic]
        candidates = ["opus-xhigh"]

        [routes.retry]
        candidates = ["fable", "opus-xhigh"]
        """)

    def stub_agy(self, folder, *replies):
        """A fake agy that logs its arguments and answers each session with the next reply ('Loop: continue' when none is left)."""
        for idx, reply in enumerate(replies):
            (folder / f"agy-reply-{idx:03}").write_text(reply)
        fake = folder / "agy"
        fake.write_text(
            f"#!{sys.executable}\nimport json, os, sys\n"
            f"folder = {str(folder)!r}\n"
            "open(os.path.join(folder, 'agy.log'), 'a').write(json.dumps(sys.argv[1:]) + '\\n')\n"
            "q = sorted(n for n in os.listdir(folder) if n.startswith('agy-reply-'))\n"
            "r = 'Loop: continue\\n'\n"
            "if q:\n"
            "    r = open(os.path.join(folder, q[0])).read(); os.remove(os.path.join(folder, q[0]))\n"
            "print(json.dumps({'event': 'result', 'result': {'status': 'SUCCESS', 'response': r, 'num_turns': 1, 'usage': {}}}))\n")
        fake.chmod(0o755)
        return str(fake)

    def cool(self, folder, until, *keys):
        def change(state):
            for key in keys:
                state["cooldown"][key] = {"harness": "agy" if key.startswith("gemini") or key == "agy" else "claude",
                                          "until": until}
        update_state(folder, change)

    def test_routes_list_candidate_offerings_in_order_and_refuse_an_unknown_name_or_a_single_spec(self):
        cfg = parse_dispatch(self.ROUTES)
        self.assertTrue(cfg.routed)
        self.assertEqual([spec.name for spec in cfg.routes["tool"]], ["carbon", "sonnet", "opus"])
        self.assertEqual([spec.name for spec in cfg.routes["spec"]], ["fable", "opus"])
        carbon, sonnet, _ = cfg.routes["tool"]
        self.assertEqual((carbon.harness, carbon.flags, carbon.meters),
                         ("agy", ["--dangerously-skip-permissions", "--model", "gemini-4-carbon-high"], ("gemini-week", "gemini-5h")))
        self.assertEqual((sonnet.harness, sonnet.flags, sonnet.meters), ("claude", ["--model", "sonnet", "--effort", "high"], ("claude-week",)))
        self.assertEqual(cfg.routes["prover"][0].flags, ["--model", "fable", "--effort", "xhigh", "--autocompact", "400k"])
        self.assertEqual(cfg.routes["prover"][0].meters, ("claude-week", "claude-fable"))
        self.assertTrue(all(cfg.routes[key] for key in ROUTE_KEYS))

        disabled = parse_dispatch(self.ROUTES + "[routes.epic-split]\ndisabled = true\n[routes.arch]\ndisabled = true\n")
        self.assertIsNone(disabled.routes["epic-split"])
        self.assertIsNone(disabled.routes["arch"])
        self.assertIsNone(parse_dispatch(self.OFFERINGS + '[routes.tool]\ncandidates = ["sonnet"]\n').routes["sys"])
        self.assertFalse(parse_dispatch(self.OFFERINGS).routed)

        for bad in (self.OFFERINGS + '[routes.tool]\ncandidates = ["sonnet", "haiku"]\n',
                    '[routes.tool]\ncandidates = ["sonnet"]\n',
                    self.OFFERINGS + '[routes.tool]\nharness = "claude"\nmodel = "opus"\n',
                    self.OFFERINGS + '[routes.tool]\ncandidates = ["sonnet"]\nmodel = "opus"\n',
                    self.OFFERINGS + '[routes.tool]\ncandidates = []\n',
                    self.OFFERINGS + '[routes.tool]\ncandidates = "sonnet"\n',
                    self.OFFERINGS + '[routes.magic]\ncandidates = ["sonnet"]\n',
                    self.OFFERINGS + '[routes.tool]\ndisabled = "yes"\n',
                    '[offerings.opus]\nmodel = "opus"\n',
                    '[offerings.opus]\nmodel = "opus"\nmeters = []\n',
                    '[offerings.opus]\nmodel = "opus"\nmeters = ["gemini-week"]\n',
                    '[offerings.carbon]\nharness = "agy"\nmeters = ["claude-week"]\n',
                    '[offerings.opus]\nmodel = "opus"\nturns = "9"\nmeters = ["claude-week"]\n'):
            with self.assertRaises(ValueError, msg=bad):
                parse_dispatch(bad)

        # A loop that reads a route naming an unknown offering reports it and keeps routing on the last good file.
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder)
            (folder / "loop.toml").write_text(self.ROUTES)
            loop.tune()
            (folder / "loop.toml").write_text(self.ROUTES.replace('["fable", "opus"]', '["fable", "opsu"]'))
            loop.tune()
            self.assertEqual([spec.name for spec in loop.candidates("spec")], ["fable", "opus"])

    def test_a_leaf_falls_through_to_the_next_candidate_whose_meters_are_not_cooled_down(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, "Loop: continue\n", "Loop: continue\n", agy=self.stub_agy(folder))
            clock[0] = 100.0
            (folder / "loop.toml").write_text(self.ROUTES)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Tool fix", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]))

            # Carbon's week is cooled down: the tool leaf runs on sonnet, the next candidate, and the pid file names it.
            self.cool(folder, 5000.0, "gemini-week")
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(self.log(folder, "agy"), [])
            [call] = self.log(folder, "claude")
            self.assertEqual((call[2], call[8:-2]), ("round", ["--model", "sonnet", "--effort", "high"]))
            self.assertEqual(self.log(folder, "pidfile")[-1]["session"],
                             {"kind": "round", "offering": "sonnet", "harness": "claude", "model": "sonnet", "effort": "high",
                              "meters": ["claude-week"]})

            # Fable's own limit leaves the Claude week free: a spec leaf goes from fable to opus.
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.2", "title": "Endpoint spec", "issue_type": "task", "priority": 1, "labels": ["kind:spec"]}]))
            self.cool(folder, 5000.0, "claude-fable")
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(self.log(folder, "claude")[-1][8:-2], ["--model", "opus", "--effort", "high"])

            # Past the reset, the cheapest candidate takes the work again.
            clock[0] = 5000.0
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.3", "title": "Tool fix", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual([call[call.index("--model") + 1] for call in self.log(folder, "agy")], ["gemini-4-carbon-high"])

    def test_a_route_whose_every_candidate_is_cooled_down_waits_and_check_says_why(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, agy=self.stub_agy(folder))
            clock[0] = 100.0
            (folder / "loop.toml").write_text(self.ROUTES)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Tool fix", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]))
            self.cool(folder, 5000.0, "gemini-5h", "claude-week")
            action, _, summary = loop.inspect_work(claim=True)
            self.assertEqual(action, "cooldown_wait")
            self.assertNotIn(["update", "atmo-1.1", "--claim"], self.log(folder, "bd"))
            [(key, issue, waits)] = summary["cooled"]
            self.assertEqual((key, issue, [(spec.name, cooled) for spec, cooled, _ in waits]),
                             ("tool", "atmo-1.1", [("carbon", [("gemini-5h", 5000.0)]), ("sonnet", [("claude-week", 5000.0)]),
                                                   ("opus", [("claude-week", 5000.0)])]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual((self.log(folder, "claude"), self.log(folder, "agy")), ([], []))

            shown = []

            class Lines:
                def write(self, text):
                    shown.append(text)

                def flush(self):
                    pass
            check(config=folder / "loop.toml", out=Lines(), loop=loop)
            text = "".join(shown)
            self.assertIn("waiting on cooldowns or pace (1)", text)
            self.assertIn("atmo-1.1 [tool]: carbon cooled on gemini-5h until", text)
            self.assertIn("; sonnet cooled on claude-week until", text)

            # The wait lasts until the earliest cooldown ends.
            loop.sleep = lambda seconds: (clock.__setitem__(0, clock[0] + seconds), setattr(loop, "stopping", clock[0] >= 5000.0))
            self.assertEqual(loop.drive(), 0)
            self.assertEqual(clock[0], 5000.0)

    def test_a_claude_only_route_never_goes_to_agy_and_hand_offs_choose_their_candidates_the_same_way(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            agy = self.stub_agy(folder, "Prover: atmo-1.1\nLoop: continue\n", "Prover: atmo-1.4\nLoop: continue\n")
            loop, clock = self.driver(folder, "Verified 12, 0 errors.", agy=agy)
            clock[0] = 100.0
            (folder / "loop.toml").write_text(self.ROUTES)

            # Every Claude offering is cooled down: a spec leaf waits though carbon is free.
            self.cool(folder, 5000.0, "claude-week")
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.2", "title": "Endpoint spec", "issue_type": "task", "priority": 1, "labels": ["kind:spec"]}]))
            self.assertEqual(loop.inspect_work(claim=True)[0], "cooldown_wait")
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual((self.log(folder, "claude"), self.log(folder, "agy")), ([], []))

            # A proof leaf runs on carbon and hands over a proof search; fable and opus-xhigh are cooled down,
            # so the search is queued on stage:needs-prover and never runs on agy.
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Prove invariant", "issue_type": "task", "priority": 1, "labels": ["kind:proof"]}]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(len(self.log(folder, "agy")), 1)
            self.assertEqual(self.log(folder, "claude"), [])
            self.assertIn(["update", "atmo-1.1", "--add-label", "stage:needs-prover", "-s", "open", "--assignee", ""],
                          self.log(folder, "bd"))

            # With only fable's own meter cooled, the next hand-off falls through to opus-xhigh.
            clock[0] = 5000.0
            self.cool(folder, 9000.0, "claude-fable")
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.4", "title": "Prove invariant", "issue_type": "task", "priority": 1, "labels": ["kind:proof"]}]))
            self.assertEqual(loop.drive(once=True), 0)
            [call] = self.log(folder, "claude")
            self.assertEqual((call[2], call[8:-2]), ("prover", ["--model", "opus", "--effort", "xhigh"]))
            self.assertIn(["update", "atmo-1.4", "--append-notes", "Prover report: Verified 12, 0 errors."], self.log(folder, "bd"))
            self.assertIn(["update", "atmo-1.4", "--add-label", "stage:needs-land", "-s", "open", "--assignee", ""], self.log(folder, "bd"))

    def test_a_usage_limit_cools_the_meter_it_names_or_the_offerings_meters(self):
        fable = AgentSpec(harness="claude", name="fable", meters=("claude-week", "claude-fable"))
        sonnet = AgentSpec(harness="claude", name="sonnet", meters=("claude-week",))
        table = AgentSpec(harness="claude")
        self.assertEqual(limit_keys(Run(limited=True, limit_meters={"claude-fable"}), fable), ["claude-fable"])
        self.assertEqual(limit_keys(Run(limited=True), fable), ["claude-fable", "claude-week"])
        self.assertEqual(limit_keys(Run(limited=True, limit_meters={"claude-5h"}), sonnet), ["claude", "claude-5h"])
        self.assertEqual(limit_keys(Run(limited=True), table), ["claude"])
        lines = [json.dumps({"type": "rate_limit_event", "rate_limit_info": {
            "status": "rejected", "rateLimitType": "seven_day_fable", "utilization": 1.0, "resetsAt": 5000}})]
        self.assertEqual(follow(lines, lambda text: None).limit_meters, {"claude-fable"})

    def test_auto_routed_loop_dispatches_each_stage_to_its_route_and_parks_hand_offs_on_a_limit(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            agy = self.stub_agy(folder, "Prover: atmo-1.1\nLoop: continue\n", "Loop: continue\n", "Loop: continue\n")
            loop, _ = self.driver(folder, "Verified 12, 0 errors.", agy=agy)
            (folder / "loop.toml").write_text(self.ROUTES)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Prove invariant", "issue_type": "task", "priority": 1, "labels": ["kind:proof"]},
            ]))
            self.assertEqual(loop.drive(once=True), 0)

            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Prove invariant", "issue_type": "task", "priority": 1, "labels": ["kind:proof", "stage:needs-land"]},
            ]))
            self.assertEqual(loop.drive(once=True), 0)

            (folder / "ready.json").write_text("[]")
            (folder / "all.json").write_text(json.dumps([
                {"id": "atmo-1", "issue_type": "epic", "status": "open", "priority": 0},
                {"id": "atmo-1.3", "parent": "atmo-1", "issue_type": "epic", "status": "open", "priority": 2},
                {"id": "atmo-1.3.1", "parent": "atmo-1.3", "issue_type": "task", "status": "closed", "priority": 2,
                 "closed_at": "2026-11-11T12:00:00Z", "close_reason": "abc: gate"},
            ]))
            self.assertEqual(loop.drive(once=True), 0)

            agy_models = [call[call.index("--model") + 1] for call in self.log(folder, "agy")]
            self.assertEqual(agy_models, ["gemini-4-carbon-high", "gemini-4-carbon-low", "gemini-4-carbon-low"])
            [claude_call] = self.log(folder, "claude")
            self.assertEqual((claude_call[2], claude_call[8:-2]),
                             ("prover", ["--model", "fable", "--effort", "xhigh", "--autocompact", "400k"]))
            bd_calls = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.1", "--add-label", "stage:needs-land", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.1", "--remove-label", "stage:needs-land"], bd_calls)

        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            fake_claude = folder / "claude_limit"
            fake_claude.write_text(
                f"#!{sys.executable}\nimport json, sys\n"
                f"open({str(folder / 'claude.log')!r}, 'a').write(json.dumps(sys.argv[1:]) + '\\n')\n"
                "print(json.dumps({'type': 'rate_limit_event', 'rate_limit_info': {'status': 'rejected', 'resetsAt': 5000}}))\n"
                "print(json.dumps({'type': 'result', 'subtype': 'success', 'is_error': True, 'result': 'You hit your usage limit'}))\n"
            )
            fake_claude.chmod(0o755)
            loop, clock = self.driver(folder, agy=self.stub_agy(folder, "Prover: atmo-1.2\nLoop: continue\n"))
            loop.claude = str(fake_claude)
            (folder / "loop.toml").write_text(self.ROUTES)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Review epic", "issue_type": "task", "priority": 0, "labels": ["review", "stage:needs-skeptic"]},
                {"id": "atmo-1.2", "title": "Tool fix", "issue_type": "task", "priority": 2, "labels": ["kind:tool"]},
            ]))
            # The skeptic's session on opus-xhigh hits a limit that names no meter, which cools every meter
            # opus-xhigh draws on; the tool leaf then runs on carbon and its prover hand-off is queued.
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(clock[0], 0.0)
            self.assertEqual(read_state(folder)["cooldown"], {"claude-week": {"harness": "claude", "until": 5000.0}})
            self.assertEqual((len(self.log(folder, "claude")), len(self.log(folder, "agy"))), (1, 1))
            bd_calls = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.1", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.2", "--add-label", "stage:needs-prover", "-s", "open", "--assignee", ""], bd_calls)

            # With only claude-routed work left, --once exits 0 at zero tokens without invoking claude again.
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Review epic", "issue_type": "task", "priority": 0, "labels": ["review", "stage:needs-skeptic"]},
            ]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual((len(self.log(folder, "claude")), len(self.log(folder, "agy"))), (1, 1))

    # The session record.

    def row(self, driver, **given):
        """A session row with the fake sessions' outcome and nothing else known, then what `given` says."""
        row = {"actor": driver.actor, "session": "round", "issue": None, "work_kind": None, "route": None, "offering": None,
               "harness": "claude", "model": None, "effort": None, "started": 0.0, "minutes": 0.0, "turns": 1,
               "weighted": 0.0, "exit": 0, "error": 0, "limited": 0, "loop": None, "prover": None, "retry": None,
               "skeptic": None}
        row.update(given)
        return row

    def test_each_session_on_either_harness_appends_its_row_with_issue_route_offering_tokens_and_report_words(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            agy = folder / "agy"
            agy.write_text(
                f"#!{sys.executable}\nimport json\n"
                "print(json.dumps({'event': 'result', 'result': {'status': 'SUCCESS', 'num_turns': 7, "
                "'response': 'Prover: atmo-1.1\\nLoop: continue\\n', "
                "'usage': {'input_tokens': 1000, 'cache_read_tokens': 400, 'output_tokens': 10}}}))\n")
            agy.chmod(0o755)
            loop, clock = self.driver(folder, "Verified 12, 0 errors.", agy=str(agy))
            clock[0] = 100.0
            (folder / "loop.toml").write_text(self.ROUTES)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Tool fix", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(read_sessions(folder), [
                self.row(loop, issue="atmo-1.1", work_kind="tool", route="tool", offering="carbon", harness="agy",
                         model="gemini-4-carbon-high", started=100.0, turns=7, weighted=690.0, loop="continue",
                         prover="atmo-1.1"),
                self.row(loop, session="prover", issue="atmo-1.1", work_kind="tool", route="prover", offering="fable",
                         model="fable", effort="xhigh", started=100.0)])

            # The unrouted loop records its round with no issue or route, since the round claims its own.
            (folder / "loop.toml").write_text('[round]\nmodel = "opus"\n')
            loop, _ = self.driver(folder, "Notify: none\nLoop: stop\n")
            self.assertEqual(loop.drive(), 0)
            self.assertEqual(read_sessions(folder)[2:], [self.row(loop, model="opus", loop="stop")])

    def test_a_session_that_hits_a_usage_limit_is_recorded_as_limited(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            fake_claude = folder / "claude_limit"
            fake_claude.write_text(
                f"#!{sys.executable}\nimport json\n"
                "print(json.dumps({'type': 'rate_limit_event', 'rate_limit_info': {'status': 'rejected', 'resetsAt': 5000}}))\n"
                "print(json.dumps({'type': 'result', 'subtype': 'success', 'is_error': True, 'num_turns': 2, "
                "'result': 'You hit your usage limit'}))\n")
            fake_claude.chmod(0o755)
            loop, _ = self.driver(folder, agy=self.stub_agy(folder, "Loop: continue\n"))
            loop.claude = str(fake_claude)
            (folder / "loop.toml").write_text(self.ROUTES)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Review epic", "issue_type": "task", "priority": 0, "labels": ["review", "stage:needs-skeptic"]},
                {"id": "atmo-1.2", "title": "Tool fix", "issue_type": "task", "priority": 2, "labels": ["kind:tool"]}]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(read_sessions(folder), [
                self.row(loop, session="skeptic", issue="atmo-1.1", work_kind="review", route="skeptic", offering="opus-xhigh",
                         model="opus", effort="xhigh", turns=2, error=1, limited=1),
                self.row(loop, issue="atmo-1.2", work_kind="tool", route="tool", offering="carbon", harness="agy",
                         model="gemini-4-carbon-high", loop="continue")])

    def test_two_workers_writing_sessions_at_once_lose_no_row(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            context = multiprocessing.get_context("fork")
            start = context.Barrier(2)

            def write(actor):
                start.wait()
                for number in range(40):
                    record_session(folder, {name: None for name, _ in SESSION_COLUMNS} | {"actor": actor, "turns": number})

            workers = [context.Process(target=write, args=(f"loop-{n}",)) for n in (1, 2)]
            for worker in workers:
                worker.start()
            for worker in workers:
                worker.join(60)
            self.assertEqual([worker.exitcode for worker in workers], [0, 0])
            rows = read_sessions(folder)
            for actor in ("loop-1", "loop-2"):
                self.assertEqual([row["turns"] for row in rows if row["actor"] == actor], list(range(40)))

    # The pool against fake workers: each logs what it is sent, ends on SIGTERM unless the file
    # `linger` exists, ends on SIGUSR1, stays on SIGHUP (as a worker re-executing in place would), and
    # ends with the status written to quit-<pid>.

    FAKE_WORKER = textwrap.dedent("""\
        import os, signal, sys, time
        folder = os.environ["FAKE"]
        def log(word):
            open(os.path.join(folder, "workers.log"), "a").write(f"{os.getpid()} {word}\\n")
        def term(signum, frame):
            log("TERM")
            if not os.path.exists(os.path.join(folder, "linger")):
                sys.exit(0)
        def now(signum, frame):
            log("USR1")
            sys.exit(0)
        signal.signal(signal.SIGTERM, term)
        signal.signal(signal.SIGUSR1, now)
        signal.signal(signal.SIGHUP, lambda signum, frame: log("HUP"))
        log("start " + " ".join(sys.argv[1:]))
        quit = os.path.join(folder, f"quit-{os.getpid()}")
        while not os.path.exists(quit):
            time.sleep(0.02)
        sys.exit(int(open(quit).read()))
        """)

    def pool(self, folder, jobs, **given):
        given.setdefault("claude_account", folder / "no-claude.json")
        given.setdefault("agy", str(folder / "no-agy"))
        (folder / "tools").mkdir(exist_ok=True)
        (folder / "tools" / "loop.py").write_text(self.FAKE_WORKER)
        (folder / "loop.toml").write_text(f"[pool]\njobs = {jobs}\n")
        os.environ["FAKE"] = str(folder)
        sink = open(os.devnull, "w")
        self.addCleanup(sink.close)
        executed = []
        pool = Pool([sys.executable, str(folder / "tools" / "loop.py")], pids=folder / "pids", config=folder / "loop.toml",
                    tick=0, sleep=lambda seconds: None, out=sink, argv=["python", "loop.py"],
                    execute=lambda path, argv: executed.append(argv), **given)
        self.addCleanup(self.end_workers, pool)
        return pool, executed

    def end_workers(self, pool):
        for pid in pool.workers:
            try:
                os.kill(pid, signal.SIGKILL)
                os.waitpid(pid, 0)
            except (ProcessLookupError, ChildProcessError):
                pass

    def workers_log(self, folder):
        path = folder / "workers.log"
        lines = path.read_text().splitlines() if path.exists() else []
        return [(int(pid), word) for pid, _, word in (line.partition(" ") for line in lines)]

    def started(self, folder):
        return [pid for pid, word in self.workers_log(folder) if word.startswith("start")]

    def settle(self, pool, done):
        """Tick the pool until done() holds; the last tick's answer."""
        deadline = time.time() + 20
        while True:
            going = pool.step()
            if going:
                pool.record()
            if done():
                return going
            self.assertLess(time.time(), deadline, "the pool did not settle")
            time.sleep(0.02)

    def test_a_pool_keeps_as_many_workers_as_jobs_says_and_follows_an_edit_both_ways(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            pool, _ = self.pool(folder, 2)
            self.settle(pool, lambda: len(self.started(folder)) == 2)
            self.assertEqual(sorted(pool.workers), sorted(self.started(folder)))
            self.assertEqual({word for _, word in self.workers_log(folder)}, {f"start --worker {os.getpid()}"})
            self.assertEqual(read_pid_file(folder / "pids", os.getpid()),
                             {"pid": os.getpid(), "session": None, "workers": pool.workers, "leaving": []})
            (folder / "loop.toml").write_text("[pool]\njobs = 3\n")
            self.settle(pool, lambda: len(self.started(folder)) == 3)
            first, second, third = pool.workers
            (folder / "loop.toml").write_text("[pool]\njobs = 1\n")
            self.assertTrue(self.settle(pool, lambda: pool.workers == [first]))
            self.assertEqual(sorted(pid for pid, word in self.workers_log(folder) if word == "TERM"), sorted([second, third]))
            for _ in range(3):
                self.assertTrue(pool.step())
            self.assertEqual(len(self.started(folder)), 3)

    def test_a_worker_that_fails_is_not_replaced_and_one_that_finds_only_questions_stops_the_pool(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            (folder / "linger").write_text("")
            pool, _ = self.pool(folder, 3)
            self.settle(pool, lambda: len(self.started(folder)) == 3)
            failing, done, other = pool.workers
            (folder / f"quit-{failing}").write_text("1")
            self.settle(pool, lambda: failing not in pool.workers)
            for _ in range(3):
                self.assertTrue(pool.step())
            self.assertEqual((len(self.started(folder)), pool.failed), (3, 1))
            (folder / f"quit-{done}").write_text(str(DONE))
            self.settle(pool, lambda: (other, "TERM") in self.workers_log(folder))
            self.assertTrue(pool.stopping)
            (folder / f"quit-{other}").write_text("0")
            self.assertFalse(self.settle(pool, lambda: not pool.workers))
            self.assertEqual(pool.status, 0)

    def test_a_pool_whose_every_worker_failed_ends_with_status_1(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            pool, _ = self.pool(folder, 1)
            self.settle(pool, lambda: len(self.started(folder)) == 1)
            (folder / f"quit-{self.started(folder)[0]}").write_text("1")
            self.assertFalse(self.settle(pool, lambda: not pool.workers))
            self.assertEqual(pool.status, 1)

    def test_a_stop_reaches_every_worker_and_a_second_ends_their_runs_in_flight(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            (folder / "linger").write_text("")
            pool, _ = self.pool(folder, 2)
            self.settle(pool, lambda: len(self.started(folder)) == 2)
            pool.on_stop(signal.SIGTERM, None)
            self.assertTrue(self.settle(pool, lambda: sum(word == "TERM" for _, word in self.workers_log(folder)) == 2))
            pool.on_stop(signal.SIGTERM, None)
            self.assertFalse(self.settle(pool, lambda: not pool.workers))
            self.assertEqual(sorted(pid for pid, word in self.workers_log(folder) if word == "USR1"), sorted(self.started(folder)))
            self.assertEqual(pool.run(), 0)
            self.assertFalse((folder / "pids" / str(os.getpid())).exists())

    def test_a_reload_passes_on_to_the_workers_and_the_re_executed_pool_adopts_them(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            pool, executed = self.pool(folder, 2)
            self.settle(pool, lambda: len(self.started(folder)) == 2)
            workers = pool.workers
            pool.on_reload(signal.SIGHUP, None)
            self.assertFalse(pool.step())
            self.assertEqual(executed, [["python", "loop.py"]])
            again, _ = self.pool(folder, 2)
            again.adopt()
            self.assertEqual(again.workers, workers)
            self.settle(again, lambda: sum(word == "HUP" for _, word in self.workers_log(folder)) == 2)
            self.assertEqual(len(self.started(folder)), 2)
            again.on_stop(signal.SIGTERM, None)
            self.assertFalse(self.settle(again, lambda: not again.workers))

    def test_a_stop_for_every_loop_leaves_a_live_pools_workers_to_their_pool(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            catcher = "import signal, sys, time\nsignal.signal(signal.SIGTERM, lambda *a: sys.exit(7))\nprint('up', flush=True)\ntime.sleep(60)\n"
            pool, worker = (subprocess.Popen([sys.executable, "-c", catcher, "/x/tools/loop.py"], stdout=subprocess.PIPE, text=True)
                            for _ in range(2))
            try:
                for process in (pool, worker):
                    process.stdout.readline()
                    process.stdout.close()
                write_pid_file(folder, {"pid": pool.pid, "session": None, "workers": [worker.pid], "leaving": []})
                write_pid_file(folder, {"pid": worker.pid, "session": None, "pool": pool.pid})
                with open(os.devnull, "w") as quiet:
                    sys.stdout, saved = quiet, sys.stdout
                    try:
                        self.assertEqual(send([], signal.SIGTERM, folder), 0)
                        self.assertEqual(pool.wait(timeout=10), 7)
                        self.assertIsNone(worker.poll())
                        self.assertEqual(send([str(worker.pid)], signal.SIGTERM, folder), 0)
                        self.assertEqual(worker.wait(timeout=10), 7)
                    finally:
                        sys.stdout = saved
            finally:
                for process in (pool, worker):
                    process.kill()
                    process.wait()

    def test_a_worker_names_its_pool_and_does_not_count_it_as_a_peer(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            sleep = [sys.executable, "-c", "import time; print('up', flush=True); time.sleep(60)", "/x/tools/loop.py"]
            pool, sibling = (subprocess.Popen(sleep, stdout=subprocess.PIPE, text=True) for _ in range(2))
            try:
                for process in (pool, sibling):
                    process.stdout.readline()
                    process.stdout.close()
                loop, _ = self.driver(folder, pool=pool.pid)
                loop.record()
                self.assertEqual(read_pid_file(folder, os.getpid()), {"pid": os.getpid(), "session": None, "pool": pool.pid})
                write_pid_file(folder, {"pid": pool.pid, "session": None, "workers": [os.getpid()], "leaving": []})
                self.assertFalse(loop.other_loop_alive())
                write_pid_file(folder, {"pid": sibling.pid, "session": None, "pool": pool.pid})
                self.assertTrue(loop.other_loop_alive())
            finally:
                for process in (pool, sibling):
                    process.kill()
                    process.wait()

    def test_pool_jobs_is_a_whole_number_of_at_least_one_and_defaults_to_one(self):
        self.assertEqual(pool_jobs(""), 1)
        self.assertEqual(pool_jobs("[pool]\njobs = 6\n[round]\nmodel = \"opus\"\n"), 6)
        for text in ("[pool]\njobs = 0\n", "[pool]\njobs = \"2\"\n", "[pool]\njobs = true\n", "[pool]\nsize = 2\n",
                     "pool = 2\n", "[pool]\njobs = 2\n[round]\neffort = \"huge\"\n"):
            with self.assertRaises(ValueError, msg=text):
                pool_jobs(text)

    def test_fit_rate_computes_hourly_slope_and_handles_scheduled_and_manual_resets(self):
        self.assertIsNone(fit_rate([]))
        self.assertIsNone(fit_rate([{"read": 1000.0, "percent": 25.0, "resets_at": 10000.0}]))
        # Steady spend: 10% -> 15% -> 20% across one hour = 10%/h.
        steady = [
            {"read": 0.0, "percent": 10.0, "resets_at": 50000.0},
            {"read": 1800.0, "percent": 15.0, "resets_at": 50000.0},
            {"read": 3600.0, "percent": 20.0, "resets_at": 50000.0},
        ]
        self.assertAlmostEqual(fit_rate(steady), 10.0)

        # Scheduled window rollover between two readings: 80% -> 90% in 1h, reset, 5% -> 15% in 1h = 10%/h.
        rollover = [
            {"read": 0.0, "percent": 80.0, "resets_at": 5000.0},
            {"read": 3600.0, "percent": 90.0, "resets_at": 5000.0},
            {"read": 7200.0, "percent": 5.0, "resets_at": 23000.0},
            {"read": 10800.0, "percent": 15.0, "resets_at": 23000.0},
        ]
        self.assertAlmostEqual(fit_rate(rollover), 10.0)

        # Manual reset within the same window (resets_at unchanged, percent drops): still 12%/h.
        manual_reset = [
            {"read": 0.0, "percent": 70.0, "resets_at": 50000.0},
            {"read": 3600.0, "percent": 82.0, "resets_at": 50000.0},
            {"read": 7200.0, "percent": 4.0, "resets_at": 50000.0},
            {"read": 10800.0, "percent": 16.0, "resets_at": 50000.0},
        ]
        self.assertAlmostEqual(fit_rate(manual_reset), 12.0)

        # Reset right before the latest reading (only one point after reset): keeps pre-reset slope.
        just_reset = [
            {"read": 0.0, "percent": 80.0, "resets_at": 5000.0},
            {"read": 3600.0, "percent": 90.0, "resets_at": 5000.0},
            {"read": 7200.0, "percent": 2.0, "resets_at": 23000.0},
        ]
        self.assertAlmostEqual(fit_rate(just_reset), 10.0)

        # Only two readings total, straddling a scheduled reset at t=1800: 15% spent in 1h after reset = 15%/h.
        two_across_reset = [
            {"read": 1000.0, "percent": 92.0, "resets_at": 1800.0},
            {"read": 5400.0, "percent": 15.0, "resets_at": 19800.0},
        ]
        self.assertAlmostEqual(fit_rate(two_across_reset), 15.0)

    def test_a_limit_in_one_workers_stream_cools_the_harness_for_a_second_worker_until_reset(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            fake_claude = folder / "claude_stream"
            fake_claude.write_text(
                f"#!{sys.executable}\nimport json, os, sys\n"
                f"log = {str(folder / 'claude.log')!r}\n"
                "calls = sum(1 for _ in open(log)) if os.path.exists(log) else 0\n"
                "open(log, 'a').write(json.dumps(sys.argv[1:]) + '\\n')\n"
                "if calls == 0:\n"
                "    print(json.dumps({'type': 'rate_limit_event', 'rate_limit_info': "
                "{'status': 'rejected', 'rateLimitType': 'seven_day', 'utilization': 1.0, 'resetsAt': 5000}}))\n"
                "    print(json.dumps({'type': 'result', 'subtype': 'success', 'is_error': True, 'result': 'You hit your usage limit'}))\n"
                "else:\n"
                "    print(json.dumps({'type': 'result', 'subtype': 'success', 'is_error': False, 'result': 'Loop: continue\\n', 'num_turns': 1, 'usage': {}}))\n"
            )
            fake_claude.chmod(0o755)
            fake_agy = folder / "agy"
            fake_agy.write_text(
                f"#!{sys.executable}\nimport json, sys\n"
                f"open({str(folder / 'agy.log')!r}, 'a').write(json.dumps(sys.argv[1:]) + '\\n')\n"
                "print(json.dumps({'event': 'result', 'result': {'status': 'SUCCESS', 'response': 'Loop: continue\\n', 'num_turns': 1, 'usage': {}}}))\n"
            )
            fake_agy.chmod(0o755)
            (folder / "loop.toml").write_text(textwrap.dedent("""\
                [offerings.carbon]
                harness = "agy"
                model = "gemini-4-carbon-medium"
                meters = ["gemini-week", "gemini-5h"]
                [offerings.opus]
                model = "opus"
                effort = "high"
                meters = ["claude-week"]
                [routes.default]
                candidates = ["carbon"]
                [routes.arch]
                candidates = ["opus"]
                """))
            worker1, clock1 = self.driver(folder, agy=str(fake_agy))
            worker1.claude = str(fake_claude)
            worker2, clock2 = self.driver(folder, agy=str(fake_agy))
            worker2.claude = str(fake_claude)
            clock1[0] = clock2[0] = 100.0

            # Worker 1 hits a claude usage limit on atmo-1.1, then falls over to agy on atmo-1.2.
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Design doc", "issue_type": "task", "priority": 0, "labels": ["kind:arch"]},
                {"id": "atmo-1.2", "title": "Tool fix", "issue_type": "task", "priority": 2, "labels": ["kind:tool"]},
            ]))
            self.assertEqual(worker1.drive(once=True), 0)
            self.assertEqual(len(self.log(folder, "claude")), 1)
            self.assertEqual(len(self.log(folder, "agy")), 1)

            state = read_state(folder)
            self.assertEqual(state["cooldown"], {"claude-week": {"harness": "claude", "until": 5000.0}})
            self.assertEqual(state["meters"]["claude-week"]["percent"], 100.0)
            self.assertEqual(state["meters"]["claude-week"]["resets_at"], 5000.0)

            # Worker 2 (separate Loop instance) sees the cooldown in state.json and skips claude without spending a session.
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Design doc", "issue_type": "task", "priority": 0, "labels": ["kind:arch"]},
                {"id": "atmo-1.3", "title": "Another tool", "issue_type": "task", "priority": 2, "labels": ["kind:tool"]},
            ]))
            clock2[0] = 4999.0
            self.assertEqual(worker2.choose("arch")[1][0][1], [("claude-week", 5000.0)])
            self.assertEqual(worker2.drive(once=True), 0)
            self.assertEqual(len(self.log(folder, "claude")), 1)
            self.assertEqual(len(self.log(folder, "agy")), 2)

            # With only claude work left before reset, worker 2 spends no session at all.
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Design doc", "issue_type": "task", "priority": 0, "labels": ["kind:arch"]},
            ]))
            self.assertEqual(worker2.drive(once=True), 0)
            self.assertEqual(len(self.log(folder, "claude")), 1)

            # Once the reset time arrives, worker 2 runs the claude session.
            clock2[0] = 5000.0
            self.assertEqual(worker2.choose("arch")[0].name, "opus")
            self.assertEqual(worker2.drive(once=True), 0)
            self.assertEqual(len(self.log(folder, "claude")), 2)

    def test_pool_samples_meters_survives_restart_and_keeps_last_readings_on_failed_agy_usage(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            pids = folder / "pids"
            account = folder / "claude.json"
            usage_file = folder / "usage.json"
            fail_flag = folder / "fail-agy"
            fake_agy = folder / "agy"
            fake_agy.write_text(
                f"#!/bin/sh\n[ -e {fail_flag} ] && exit 1\ncat {usage_file}\n"
            )
            fake_agy.chmod(0o755)

            def write_sources(fetched_ms, c_week, c_5h, fable, g_rem_week, g_rem_5h):
                account.write_text(json.dumps({"cachedUsageUtilization": {
                    "fetchedAtMs": fetched_ms,
                    "utilization": {
                        "five_hour": {"utilization": c_5h, "resets_at": "2026-11-13T18:00:00+00:00"},
                        "seven_day": {"utilization": c_week, "resets_at": "2026-11-15T05:00:00+00:00"},
                        "limits": [
                            {"kind": "weekly_all", "group": "weekly", "percent": c_week,
                             "resets_at": "2026-11-15T05:00:00+00:00", "scope": None},
                            {"kind": "weekly_scoped", "group": "weekly", "percent": fable,
                             "resets_at": "2026-11-15T05:00:00+00:00",
                             "scope": {"model": {"id": None, "display_name": "Fable"}, "surface": None}},
                            {"kind": "weekly_scoped", "group": "weekly", "percent": 3,
                             "resets_at": "2026-11-15T05:00:00+00:00",
                             "scope": {"model": None, "surface": "desk"}},
                        ],
                    },
                }}))
                usage_file.write_text(json.dumps({"status": "SUCCESS", "command": {"name": "usage", "data": {"groups": [
                    {"name": "Gemini Models", "buckets": [
                        {"id": "gemini-weekly", "window": "weekly", "remaining_fraction": g_rem_week,
                         "reset_time": "2026-11-19T13:00:00Z"},
                        {"id": "gemini-5h", "window": "5h", "remaining_fraction": g_rem_5h,
                         "reset_time": "2026-11-13T19:00:00Z"},
                    ]},
                    {"name": "Claude and GPT models", "buckets": [
                        {"id": "3p-weekly", "window": "weekly", "remaining_fraction": 1.0,
                         "reset_time": "2026-11-20T12:00:00Z"},
                    ]},
                ]}}}))

            clock = [1000.0]
            write_sources(1000_000, 20, 10, 30, 0.80, 0.90)
            pool1, _ = self.pool(folder, 1, claude_account=account, agy=str(fake_agy), now=lambda: clock[0])
            self.settle(pool1, lambda: len(self.started(folder)) == 1)
            state1 = read_state(pids)
            self.assertEqual(set(state1["meters"]), {"claude-week", "claude-5h", "claude-fable", "gemini-week", "gemini-5h"})
            self.assertEqual(state1["meters"]["claude-week"]["percent"], 20.0)
            self.assertEqual(state1["meters"]["claude-5h"]["percent"], 10.0)
            self.assertEqual(state1["meters"]["claude-fable"]["percent"], 30.0)
            self.assertAlmostEqual(state1["meters"]["gemini-week"]["percent"], 20.0)
            self.assertAlmostEqual(state1["meters"]["gemini-5h"]["percent"], 10.0)
            self.assertIsNone(state1["meters"]["claude-week"]["rate"])
            self.assertEqual(list(pids.glob(".*.new")), [])

            # Stop supervisor 1 and start a fresh supervisor 2 an hour later: history survives the restart.
            pool1.on_stop(signal.SIGTERM, None)
            self.assertFalse(self.settle(pool1, lambda: not pool1.workers))

            clock[0] = 4600.0
            write_sources(4600_000, 26, 25, 38, 0.75, 0.70)
            pool2, _ = self.pool(folder, 1, claude_account=account, agy=str(fake_agy), now=lambda: clock[0])
            self.settle(pool2, lambda: len(self.started(folder)) == 2)
            state2 = read_state(pids)
            self.assertAlmostEqual(state2["meters"]["claude-week"]["rate"], 6.0)
            self.assertAlmostEqual(state2["meters"]["claude-5h"]["rate"], 15.0)
            self.assertAlmostEqual(state2["meters"]["claude-fable"]["rate"], 8.0)
            self.assertAlmostEqual(state2["meters"]["gemini-week"]["rate"], 5.0)
            self.assertAlmostEqual(state2["meters"]["gemini-5h"]["rate"], 20.0)

            # A failed agy /usage on a later sample keeps Gemini's last readings and fitted rates.
            fail_flag.touch()
            clock[0] = 8200.0
            write_sources(8200_000, 32, 40, 46, 0.0, 0.0)
            pool2.step()
            state3 = read_state(pids)
            self.assertEqual(state3["meters"]["claude-week"]["percent"], 32.0)
            self.assertAlmostEqual(state3["meters"]["claude-week"]["rate"], 6.0)
            self.assertAlmostEqual(state3["meters"]["gemini-week"]["percent"], 25.0)
            self.assertEqual(state3["meters"]["gemini-week"]["read"], 4600.0)
            self.assertAlmostEqual(state3["meters"]["gemini-week"]["rate"], 5.0)
            self.assertAlmostEqual(state3["meters"]["gemini-5h"]["percent"], 30.0)
            pool2.on_stop(signal.SIGTERM, None)
            self.assertFalse(self.settle(pool2, lambda: not pool2.workers))

    PACED = textwrap.dedent("""\
        [offerings.carbon]
        harness = "agy"
        model = "gemini-4-carbon-high"
        meters = ["gemini-week", "gemini-5h"]

        [offerings.opus]
        model = "opus"
        effort = "high"
        meters = ["claude-week", "claude-5h"]

        [offerings.sonnet]
        model = "sonnet"
        effort = "high"
        meters = ["claude-week"]

        [routes.default]
        candidates = ["opus", "carbon"]

        [meters.claude-week]
        target = 95
        max = 4

        [meters.claude-5h]
        target = 95
        max = 3

        [meters.gemini-week]
        target = 90
        max = 2
        """)

    def meter(self, percent, resets_at, read=0.0, rate=None, session_rate=None):
        return {"harness": "claude", "percent": percent, "resets_at": resets_at, "read": read, "rate": rate,
                "session_rate": session_rate, "history": []}

    def test_a_meter_admits_what_its_headroom_over_its_projected_use_at_reset_allows_up_to_its_max(self):
        pace = {"target": 95.0, "max": 4}
        hour = 3600.0
        # Behind pace: 10% used, 50 h to reset, 0.5%/h a session: (95 - 10) / (50 * 0.5) = 3.4, so 3.
        self.assertEqual(admission(self.meter(10.0, 50 * hour, session_rate=0.5), pace, 0.0)[0], 3)
        # Further behind, the max clamps it.
        self.assertEqual(admission(self.meter(10.0, 50 * hour, session_rate=0.1), pace, 0.0)[0], 4)
        # Ahead of pace: 80% used, 50 h to go at 0.5%/h a session projects past the target with one more.
        self.assertEqual(admission(self.meter(80.0, 50 * hour, session_rate=0.5), pace, 0.0)[0], 0)
        # The same meter near its reset has headroom for more: (95 - 80) / (2 * 0.5) = 15, clamped to 4.
        self.assertEqual(admission(self.meter(80.0, 2 * hour, session_rate=0.5), pace, 0.0)[0], 4)
        self.assertEqual(admission(self.meter(80.0, 10 * hour, session_rate=0.5), pace, 0.0)[0], 3)
        # At or past the target nothing is admitted, whatever the rate.
        self.assertEqual(admission(self.meter(95.0, 2 * hour), pace, 0.0)[0], 0)
        # No fitted rate yet, or a meter that is not moving: up to the max.
        self.assertEqual(admission(self.meter(50.0, 50 * hour), pace, 0.0)[0], 4)
        self.assertEqual(admission(self.meter(50.0, 50 * hour, session_rate=0.0), pace, 0.0)[0], 4)
        # A reading whose window has since reset says nothing of the new window: up to the max.
        self.assertEqual(admission(self.meter(94.0, 100.0, session_rate=5.0), pace, 200.0)[0], 4)
        # A meter with no readings: up to the max; the reasons are given for the log.
        self.assertEqual(admission(None, pace, 0.0), (4, None, None, None))
        self.assertEqual(admission(self.meter(10.0, 50 * hour, session_rate=0.5), pace, 0.0), (3, 10.0, 50.0, 0.5))

    def test_the_rate_a_session_is_the_meters_rate_over_the_sessions_in_flight_when_read(self):
        state = empty_state()
        for read, percent, sessions in ((0.0, 10.0, 2), (1800.0, 15.0, 2), (3600.0, 20.0, 2)):
            add_reading(state, "claude-week", "claude", percent, 50000.0, read, sessions=sessions)
        held = state["meters"]["claude-week"]
        self.assertAlmostEqual(held["rate"], 10.0)
        self.assertAlmostEqual(held["session_rate"], 5.0)
        # Readings taken with no session in flight, or with none counted, are reckoned as one session's,
        # so a meter moved by use outside the pool is not taken as free.
        state = empty_state()
        for read, percent in ((0.0, 10.0), (3600.0, 20.0)):
            add_reading(state, "claude-week", "claude", percent, 50000.0, read)
        self.assertAlmostEqual(state["meters"]["claude-week"]["session_rate"], 10.0)
        state = empty_state()
        for read, percent in ((0.0, 10.0), (3600.0, 20.0)):
            add_reading(state, "claude-week", "claude", percent, 50000.0, read, sessions=0)
        self.assertAlmostEqual(state["meters"]["claude-week"]["session_rate"], 10.0)
        add_reading(state, "claude-week", "claude", 20.0, 50000.0, 3600.0, sessions=0)
        self.assertEqual(state["meters"]["claude-week"]["history"][-1]["sessions"], 0)

    def test_meters_tables_take_a_target_and_a_max(self):
        self.assertEqual(parse_dispatch(self.PACED).paces["claude-5h"], {"target": 95.0, "max": 3})
        for bad in ('[meters.claude-week]\nmax = 4\n', '[meters.claude-week]\ntarget = 95\n',
                    '[meters.claude-week]\ntarget = 0\nmax = 4\n', '[meters.claude-week]\ntarget = 101\nmax = 4\n',
                    '[meters.claude-week]\ntarget = 95\nmax = -1\n', '[meters.claude-week]\ntarget = 95\nmax = 1.5\n',
                    '[meters.claude-week]\ntarget = 95\nmax = 4\nfloor = 1\n', '[meters.Claude]\ntarget = 95\nmax = 4\n',
                    '[meters]\nclaude-week = 95\n'):
            with self.assertRaises(ValueError, msg=bad):
                parse_dispatch(bad)

    def test_a_worker_takes_an_offering_only_while_every_meter_it_draws_on_has_room(self):
        hour = 3600.0
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, "Loop: continue\n", agy=self.stub_agy(folder))
            loop.alive = lambda pid: True
            (folder / "loop.toml").write_text(self.PACED)
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Tool fix", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]))

            def readings(week, five_hour, sessions=1):
                state = empty_state()
                for meter, (percent, rate, resets_at) in (("claude-week", week), ("claude-5h", five_hour)):
                    add_reading(state, meter, "claude", percent - rate, resets_at, 0.0, sessions=sessions)
                    add_reading(state, meter, "claude", percent, resets_at, hour, sessions=sessions)
                update_state(folder, lambda held: held.update(meters=state["meters"]))
                clock[0] = hour

            def in_flight(*offerings):
                for path in folder.glob("[0-9]*"):
                    path.unlink()
                for pid, name in enumerate(offerings, start=900001):
                    meters = {"opus": ["claude-week", "claude-5h"], "sonnet": ["claude-week"]}[name]
                    write_pid_file(folder, {"pid": pid, "pool": 1, "session": {
                        "kind": "round", "offering": name, "meters": meters}})

            def choice():
                spec, waits = loop.choose("tool")
                return spec.name if spec else [(s.name, paced) for s, _, paced in waits]

            # Week behind pace (10% at 1%/h a session, 50 h out: 1 admitted), five-hour fine: opus takes the leaf.
            readings((10.0, 1.0, 51 * hour), (10.0, 1.0, 5 * hour))
            in_flight()
            self.assertEqual(choice(), "opus")
            # One session already draws on the week, which admits one: the leaf goes to the next candidate.
            in_flight("sonnet")
            self.assertEqual(choice(), "carbon")
            # The week has room, the five-hour window is ahead of pace: the five-hour window binds.
            readings((10.0, 0.5, 51 * hour), (90.0, 2.0, 5 * hour))
            in_flight("sonnet")
            self.assertEqual(choice(), "carbon")
            # The week admits two and the five-hour window three: opus again, with one in flight on each.
            readings((10.0, 0.8, 51 * hour), (10.0, 2.0, 5 * hour))
            in_flight("opus")
            self.assertEqual(choice(), "opus")
            # Every candidate held: Gemini's week at its target admits none; the leaf waits and is not claimed.
            update_state(folder, lambda held: add_reading(held, "gemini-week", "agy", 90.0, 100 * hour, hour))
            in_flight("opus", "opus")
            self.assertEqual(choice(), [("opus", [("claude-week", 2, 2)]), ("carbon", [("gemini-week", 0, 0)])])
            action, _, summary = loop.inspect_work(claim=True)
            self.assertEqual(action, "cooldown_wait")
            self.assertNotIn(["update", "atmo-1.1", "--claim"], self.log(folder, "bd"))
            shown = []

            class Lines:
                def write(self, text):
                    shown.append(text)

                def flush(self):
                    pass
            check(config=folder / "loop.toml", out=Lines(), loop=loop)
            self.assertIn("meter claude-week: 10.0% used, 50.0 h to reset, 0.80%/h a session: admits 2 (target 95, max 4), "
                          "2 in flight", "".join(shown))
            self.assertIn("opus paced on claude-week (admits 2, 2 in flight); carbon paced on gemini-week (admits 0, 0 in flight)", "".join(shown))

            # A held route rechecks after PACE_WAIT, not after the full wait: a session ending frees a place.
            pauses = []
            loop.sleep = lambda seconds: (pauses.append(seconds), clock.__setitem__(0, clock[0] + seconds),
                                          in_flight("opus"))
            self.assertEqual(loop.drive(once=True), 0)
            loop.wait = 900
            loop.stopping = False
            # drive() without once: the first pause is the pacing recheck, after which the session runs.
            original = loop.round
            rounds = []

            def round_then_stop():
                rounds.append(1)
                result = original()
                if len(rounds) >= 2:
                    loop.stopping = True
                return result
            loop.round = round_then_stop
            in_flight("opus", "opus")
            self.assertEqual(loop.drive(), 0)
            self.assertEqual(sum(pauses), PACE_WAIT)
            self.assertEqual([call[call.index("--model") + 1] for call in self.log(folder, "claude")], ["opus"])
            # The session's pid file names the meters it draws on, for the other workers to count.
            self.assertEqual(self.log(folder, "pidfile")[-1]["session"]["meters"], ["claude-week", "claude-5h"])

    def test_the_pool_recomputes_admission_every_tick_and_logs_each_change(self):
        hour = 3600.0
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            clock = [hour]
            shown = []

            class Lines:
                def write(self, text):
                    shown.append(text)

                def flush(self):
                    pass
            pool, _ = self.pool(folder, 1, now=lambda: clock[0])
            pool.out = Lines()
            (folder / "loop.toml").write_text("[pool]\njobs = 1\n" + self.PACED)
            pids = folder / "pids"

            def set_meter(percent, rate, resets_at):
                def change(state):
                    state["meters"] = {}
                    add_reading(state, "claude-week", "claude", percent - rate, resets_at, 0.0, sessions=1)
                    add_reading(state, "claude-week", "claude", percent, resets_at, hour, sessions=1)
                update_state(pids, change)

            def lines():
                return [text for text in "".join(shown).splitlines() if "admits" in text]

            set_meter(10.0, 1.0, 51 * hour)
            pool.tune()
            pool.pace()
            self.assertEqual(len(lines()), 3)
            self.assertIn("claude-week: 10.0% used, 50.0 h to reset, 1.00%/h a session: admits 1 (target 95, max 4)", lines()[0])
            self.assertIn("claude-5h: no readings: admits 3 (target 95, max 3)", "\n".join(lines()))
            # Unchanged admission is not logged again, though the hours to reset moved.
            clock[0] = 1.5 * hour
            pool.pace()
            self.assertEqual(len(lines()), 3)
            # The meter falls behind its target's pace: the change is logged with what it came from.
            set_meter(94.5, 1.0, 51 * hour)
            pool.pace()
            self.assertEqual(len(lines()), 4)
            self.assertIn("claude-week: 94.5% used, 49.5 h to reset, 1.00%/h a session: admits 0 (target 95, max 4)", lines()[-1])
            # step() is a tick, and recomputes it.
            set_meter(10.0, 1.0, 51 * hour)
            pool.step()
            self.assertIn("admits 1", lines()[-1])

def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--list-profiles", action="store_true", help="list the offerings and routes in loop.toml and exit")
    parser.add_argument("--check", action="store_true", help="show matching ready work at zero token cost and exit")
    parser.add_argument("--once", action="store_true", help="run one round and its hand-off, then stop")
    parser.add_argument("--wait", type=float, default=WAIT, help="seconds to wait on 'Loop: wait'")
    parser.add_argument("--stop", action="store_true", help="stop running loops after their run in flight")
    parser.add_argument("--now", action="store_true", help="with --stop, end the run in flight too")
    parser.add_argument("--reload", action="store_true", help="re-execute running loops after their run in flight")
    parser.add_argument("--test", action="store_true", help="run this script's own tests")
    parser.add_argument("--worker", type=int, metavar="POOL", help="run as a worker loop of the pool with this pid")
    parser.add_argument("pids", nargs="*", help="with --stop or --reload, the loops to signal; all by default")
    args = parser.parse_args()
    if args.test:
        unittest.main(argv=[sys.argv[0]], verbosity=1)
    if args.list_profiles:
        return list_offerings()
    if args.check:
        return check()
    if args.stop and args.reload:
        parser.error("--stop and --reload are each their own command")
    if args.stop:
        return send(args.pids, signal.SIGUSR1 if args.now else signal.SIGTERM)
    if args.reload:
        return send(args.pids, signal.SIGHUP)
    if args.pids or args.now:
        parser.error("PID goes with --stop or --reload, --now with --stop")
    if args.worker is not None or args.once:
        return main_loop(args)
    return main_pool(args)


if __name__ == "__main__":
    sys.exit(main())
