#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The round loop, driven from the command line.

Each round runs in the main worktree as a fresh headless agent session (`claude -p --agent round` by
default, or `agy -p` with `.claude/agents/<kind>.md` when a route or profile selects `harness = "agy"`).
Print mode waits for a background command the round started, such as its landing, and wakes the round
when it exits, so the last result the session streams is the round's report. The report's lines say what
comes next, as the round skill reads them (.claude/skills/round/SKILL.md):

- `Notify: <text>` (or bullets under a bare `Notify:`), each sent with notify-send and printed;
- `Prover: <id>` runs the prover agent (or stamps `stage:needs-prover` when delegated or cooled down),
  then appends its report to the issue as `Prover report:` and sets the issue open; `Skeptic: <review>`
  does the same with the skeptic (`stage:needs-skeptic` when delegated or cooled down);
- `Retry: <id>`, from a round whose attempt on a leaf ended at its bound, makes the next session a
  retry (or stamps `stage:escalated` when `retry` is delegated or cooled down): a round whose prompt
  names that issue, so it takes that issue and no other, with the flags of the retry table or route;
- `Loop: continue` starts the next round, `Loop: wait` waits (another loop holds the issues in
  progress), `Loop: stop` prints the questions waiting on the human and ends the loop.

The loop is one Beads actor, loop-<pid>, for every session it runs (.claude/hooks/beads-actor.sh),
so an issue a round hands to the prover, or leaves for a retry, stays held between the two sessions.

Each session's temporary directory is <project root>/scratch, on disk: the loop sets TMPDIR, which the
session's commands read, and CLAUDE_CODE_TMPDIR, under which Claude Code keeps the session's scratchpad
and the output of its background commands.

Automatic routing, profiles, and zero-token pre-filtering (`design/loops-select-by-work-kind-and-stage/`).
When `[routes]` is defined in <project root>/loop.toml, plain `tools/loop.py` (with no `--profile` or
`--model` flag) inspects Beads in Python at zero token cost and dispatches each ready stage, leaf, or
epic round to the harness and model difficulty configured under `[routes.<key>]` (`default`, `tool`,
`sys`, `proof`, `spec`, `arch`, `review`, `epic-close`, `epic-split`, `needs-land`, `prover`, `skeptic`,
`retry`, with optional `disabled = true`). With `--profile <name>`, the loop instead runs the named
`[profiles.<name>]` slice (`kinds`, `stages`, `epics`, `delegate`). When nothing matches, no LLM session
is started: the loop waits if another loop or actor is active, and stops otherwise.

Per-harness quota cooldowns. When one harness (`claude` or `agy`) hits a rate or usage limit in routed
or profiled mode, only that harness's routes enter cooldown until its reset timestamp: any pre-claimed
issue is released back to open keeping its stage label, specialist hand-offs targeting the cooled-down
harness park on `stage:needs-prover`, `stage:needs-skeptic`, or `stage:escalated`, and ready work routed
to non-limited harnesses continues immediately.

Stopping. SIGINT (Ctrl-C) or SIGTERM, or `tools/loop.py --stop`, lets the agent run in flight finish
and ends the loop; a prover or skeptic pass a finished round handed over is not started, and its
issue is released with a note so the next round picks it up. A second signal, or `--stop --now`
(SIGUSR1), ends the run in flight too: the session's process group gets SIGTERM, then SIGKILL after
30 s, and the next round's orient recovers what it left. Each loop keeps the file
<project root>/logs/loop/<pid> while it runs; `--stop` signals each such pid that is still a loop.
The file is JSON: `session` is the session the loop runs, as its kind, harness, model and effort
(each model and effort the flags name, or null for the harness's own default), or null between
sessions, so another process such as tools/bead-status.py can say what an issue is worked at.

Tuning. Before each session the loop reads <project root>/loop.toml: `[routes.<key>]` configures
automatic per-task routing, `[profiles.<name>]` configures named single-slice profiles, and top-level
tables (`round`, `prover`, `skeptic`, `retry`) configure the unrouted default Claude loop. An edit takes
effect at the next session. A file that does not parse or names invalid keys is reported, and the loop
keeps the last values it read. SIGHUP, or `tools/loop.py --reload`, re-executes the loop after the run
in flight and its hand-off, with the same pid and so the same actor, to take up a change to this script.

A usage limit on an unrouted single-provider loop waits until the limit's reset and goes on. A round
that fails otherwise (no report, or an error result) is followed after 1, 2 and 4 minutes by another;
the fourth failure in a row ends the loop. When the failed round left exactly one issue in progress
under the loop's actor, the round that follows is a retry on that issue; with none or several it is a
plain round, whose orient recovers them. A retry is a round in every other way: its report is read the
same, and its failure counts the same.

usage: tools/loop.py [--profile NAME] [--once] [--wait SECONDS]   run rounds until the loop stops
       tools/loop.py [--profile NAME] --check                     show matching ready work (0 tokens)
       tools/loop.py --list-profiles                              list routes and profiles in loop.toml
       tools/loop.py --stop [--now] [PID...]                      stop running loops, after their run in flight
       tools/loop.py --reload [PID...]                            re-execute running loops, after their run in flight
       tools/loop.py --test                                       this script's own tests
"""
import argparse
import importlib.util
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import tomllib
import unittest
from dataclasses import dataclass, field
from pathlib import Path

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[2]
MAIN = ROOT / "main"
PIDS = ROOT / "logs" / "loop"
CONFIG = ROOT / "loop.toml"
SCRATCH = ROOT / "scratch"
KINDS = ("round", "prover", "skeptic")
RETRY = "retry"
TABLES = (*KINDS, RETRY)
HARNESSES = ("claude", "agy")
AGY_MODES = ("skip-permissions", "auto", "accept-edits", "plan")
EFFORTS = ("low", "medium", "high", "xhigh", "max")
WORK_KINDS = ("tool", "sys", "proof", "spec", "arch", "review")
STAGE_NAMES = ("needs-prover", "needs-skeptic", "escalated", "needs-land")
EPIC_MODES = ("none", "close", "split", "all")
DELEGATABLE = ("prover", "skeptic", "retry")
ROUTE_KEYS = (*WORK_KINDS, "epic-close", "epic-split", "needs-land", *DELEGATABLE)
STAGE_FOR_DELEGATE = {"prover": "needs-prover", "skeptic": "needs-skeptic", "retry": "escalated"}
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
    """The harness and CLI flags for one agent table."""
    harness: str = "claude"
    flags: list = field(default_factory=list)


@dataclass
class ProfileConfig:
    """Resolved settings and work/stage selectors for one loop profile, [routes], or unprofiled default."""
    name: str = None
    agents: dict = field(default_factory=dict)
    routes: dict = field(default_factory=dict)
    kinds: tuple = WORK_KINDS
    stages: tuple = STAGE_NAMES
    epics: str = "all"
    delegate: frozenset = field(default_factory=frozenset)
    filtered: bool = False
    routed: bool = False


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
    """One line for a Claude tool call: its description, or what it acts on."""
    given = tool.get("input", {})
    what = given.get("description") or given.get("command") or given.get("file_path") or given.get("pattern") or ""
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
    """Read a session's stream-json lines (claude or agy), showing its progress; the last result is the report."""
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
            if not str(info.get("status", "allowed")).startswith("allowed"):
                run.limited = True
                run.reset = info.get("resetsAt") or run.reset
        elif kind == "result":
            run.report = event.get("result") or ""
            run.error = bool(event.get("is_error")) or event.get("subtype") != "success"
            run.turns += event.get("num_turns") or 0
            run.weighted += weighted(event.get("usage") or {})
            if run.error and LIMIT_RE.search(run.report):
                run.limited = True
    return run


def validate_str(value, where):
    if not isinstance(value, str) or not value or value.startswith("-"):
        raise ValueError(f"{where}: not a value")


def build_agent_spec(table, where, default_harness="claude", base=None):
    """Validate an agent table (or profile-level agent keys) and build an AgentSpec."""
    merged = dict(base or {})
    merged.update(table)
    harness = merged.pop("harness", default_harness)
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
            allowed = "model, autocompact, effort or fallback-model" if harness == "claude" else "harness, mode, model or effort"
            raise ValueError(f"{where}.{key}: not {allowed}")
        flags += [f"--{key}", value]
    return AgentSpec(harness=harness, flags=flags)


def check_list(value, allowed, where):
    if not isinstance(value, list) or not all(isinstance(item, str) and item in allowed for item in value):
        raise ValueError(f"{where}: must be a list from {', '.join(allowed)}")
    return tuple(dict.fromkeys(value))


def load_toml(text):
    try:
        return tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        raise ValueError(f"not TOML: {error}")


def parse_all(text):
    """Validate the whole loop.toml and return (top_flags_dict, profiles_dict, routes_dict)."""
    raw = load_toml(text)
    top_raw = {}
    top_flags = {}
    raw_profiles = {}
    raw_routes = None
    for key, table in raw.items():
        if key == "profiles":
            if not isinstance(table, dict):
                raise ValueError("profiles: not a table")
            raw_profiles = table
            continue
        if key == "routes":
            if not isinstance(table, dict):
                raise ValueError("routes: not a table")
            raw_routes = table
            continue
        if key not in TABLES or not isinstance(table, dict):
            raise ValueError(f"{key}: not a table of {', '.join((*TABLES, 'routes', 'profiles'))}")
        if "harness" in table or "mode" in table:
            raise ValueError(f"{key}: top-level tables take model, autocompact, effort or fallback-model")
        spec = build_agent_spec(table, key, default_harness="claude")
        top_raw[key] = dict(table)
        top_flags[key] = spec.flags

    routes = {}
    if raw_routes is not None:
        allowed_routes = ("default", *ROUTE_KEYS)
        for rkey, rtable in raw_routes.items():
            if rkey not in allowed_routes or not isinstance(rtable, dict):
                raise ValueError(f"routes.{rkey}: not a route table of {', '.join(allowed_routes)}")
        has_default = "default" in raw_routes
        rdefault_disabled = False
        rdefault_harness = "claude"
        rdefault_base = {}
        rdefault_spec = None
        if has_default:
            dcopy = dict(raw_routes["default"])
            rdefault_disabled = dcopy.pop("disabled", False)
            if not isinstance(rdefault_disabled, bool):
                raise ValueError("routes.default.disabled: must be true or false")
            rdefault_harness = dcopy.get("harness", "claude")
            rdefault_spec = build_agent_spec(dcopy, "routes.default", default_harness=rdefault_harness)
            rdefault_base = {k: v for k, v in dcopy.items() if k != "harness"}

        for rkey in ROUTE_KEYS:
            if rkey in raw_routes:
                rcopy = dict(raw_routes[rkey])
                disabled = rcopy.pop("disabled", False)
                if not isinstance(disabled, bool):
                    raise ValueError(f"routes.{rkey}.disabled: must be true or false")
                base_h = rdefault_harness if (has_default and not rdefault_disabled) else "claude"
                sub_h = rcopy.get("harness", base_h)
                inherited = dict(rdefault_base) if (has_default and not rdefault_disabled and sub_h == rdefault_harness) else {}
                spec = build_agent_spec(rcopy, f"routes.{rkey}", default_harness=sub_h, base=inherited)
                routes[rkey] = None if disabled else spec
            elif has_default:
                routes[rkey] = (None if rdefault_disabled
                                else AgentSpec(harness=rdefault_spec.harness, flags=list(rdefault_spec.flags)))
            else:
                tkey = rkey if rkey in DELEGATABLE else "round"
                routes[rkey] = (build_agent_spec(top_raw[tkey], tkey, default_harness="claude")
                                if tkey in top_raw else AgentSpec(harness="claude", flags=[]))

    profiles = {}
    agent_keys = ("harness", "mode", "model", "effort", "autocompact", "fallback-model")
    selector_keys = ("kinds", "stages", "epics", "delegate")
    for name, ptable in raw_profiles.items():
        if not isinstance(ptable, dict):
            raise ValueError(f"profiles.{name}: not a table")
        where = f"profiles.{name}"
        unknown = set(ptable) - set(agent_keys) - set(selector_keys) - set(TABLES)
        if unknown:
            raise ValueError(f"{where}.{sorted(unknown)[0]}: unknown profile key")
        default_harness = ptable.get("harness", "claude")
        validate_str(default_harness, f"{where}.harness")
        if default_harness not in HARNESSES:
            raise ValueError(f"{where}.harness: {default_harness} is not one of {', '.join(HARNESSES)}")

        p_base = {k: ptable[k] for k in ptable if k in agent_keys}
        # Validate profile-level agent defaults immediately so invalid keys fail even with no subtables.
        default_spec = build_agent_spec({}, where, default_harness=default_harness, base=p_base)

        delegate = frozenset()
        if "delegate" in ptable:
            delegate = frozenset(check_list(ptable["delegate"], DELEGATABLE, f"{where}.delegate"))
        kinds = check_list(ptable["kinds"], WORK_KINDS, f"{where}.kinds") if "kinds" in ptable else WORK_KINDS
        if "stages" in ptable:
            stages = check_list(ptable["stages"], STAGE_NAMES, f"{where}.stages")
        else:
            skipped = {STAGE_FOR_DELEGATE[d] for d in delegate}
            stages = tuple(s for s in STAGE_NAMES if s not in skipped)
        epics = ptable.get("epics", "all")
        if not isinstance(epics, str) or epics not in EPIC_MODES:
            raise ValueError(f"{where}.epics: {epics!r} is not one of {', '.join(EPIC_MODES)}")

        agents = {}
        for tname in TABLES:
            sub = ptable.get(tname)
            if sub is not None:
                if not isinstance(sub, dict):
                    raise ValueError(f"{where}.{tname}: not a table")
                sub_harness = sub.get("harness", default_harness)
                inherited = {k: v for k, v in p_base.items() if k != "harness"} if sub_harness == default_harness else {}
                agents[tname] = build_agent_spec(sub, f"{where}.{tname}", default_harness=sub_harness, base=inherited)
            elif p_base:
                agents[tname] = AgentSpec(harness=default_spec.harness, flags=list(default_spec.flags))
            elif default_harness == "claude" and tname in top_raw:
                agents[tname] = build_agent_spec(top_raw[tname], tname, default_harness="claude")
            elif default_harness == "agy":
                agents[tname] = build_agent_spec({}, f"{where}.{tname}", default_harness="agy")

        profiles[name] = ProfileConfig(
            name=name, agents=agents, kinds=kinds, stages=stages,
            epics=epics, delegate=delegate, filtered=True,
        )
    return top_flags, profiles, routes


def options(text):
    """The claude -p flags loop.toml gives each top-level table. Kept compatible for callers and tests."""
    top_flags, _, _ = parse_all(text)
    return top_flags


def parse_profile(text, profile=None):
    """Resolve [routes] (when present and profile is None), the unprofiled default, or [profiles.<name>]."""
    top_flags, profiles, routes = parse_all(text)
    if profile is None:
        agents = {kind: AgentSpec(harness="claude", flags=list(flags)) for kind, flags in top_flags.items()}
        if routes:
            kinds = tuple(k for k in WORK_KINDS if routes.get(k) is not None)
            stages = tuple(s for s in STAGE_NAMES if routes.get(STAGE_ROUTE[s]) is not None)
            delegate = frozenset(d for d in DELEGATABLE if routes.get(d) is None)
            has_close = routes.get("epic-close") is not None
            has_split = routes.get("epic-split") is not None
            epics = "all" if (has_close and has_split) else ("close" if has_close else ("split" if has_split else "none"))
            return ProfileConfig(
                name=None, agents=agents, routes=routes, kinds=kinds, stages=stages,
                epics=epics, delegate=delegate, filtered=True, routed=True,
            )
        return ProfileConfig(name=None, agents=agents, filtered=False, routed=False)
    if profile not in profiles:
        known = ", ".join(sorted(profiles)) or "none defined"
        raise ValueError(f"profile {profile!r} not in [profiles] ({known})")
    return profiles[profile]


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


def flag(flags, name):
    """The value given to --name among the flags, or None."""
    for at, given in enumerate(flags[:-1]):
        if given == f"--{name}":
            return flags[at + 1]
    return None


def fmt_spec(spec):
    """Short human-readable summary of an AgentSpec for --list-profiles and --check."""
    if spec is None:
        return "disabled"
    shown = [f for f in spec.flags if f != "--dangerously-skip-permissions"]
    return f"{spec.harness}({' '.join(shown)})" if shown else spec.harness


class Loop:
    """The driver. The commands and the clock are parameters so the tests can replace them."""

    def __init__(self, claude="claude", agy="agy", bd="bd", notifier="notify-send", cwd=MAIN, pids=PIDS, config=CONFIG,
                 scratch=SCRATCH, wait=WAIT, profile=None, sleep=time.sleep, now=time.time, out=sys.stdout):
        self.claude, self.agy, self.bd, self.notifier = claude, agy, bd, notifier
        self.cwd, self.pids, self.config, self.wait = Path(cwd), Path(pids), Path(config), wait
        self.scratch = Path(scratch)
        self.profile_name = profile
        self.flags = {}
        self.profile_cfg = ProfileConfig(name=profile, filtered=profile is not None)
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
        self.active_route = None
        self.cooldown = {}

    def record(self, kind=None, spec=None):
        """Rewrite the loop's pid file to name the session it runs, or none."""
        session = spec and {"kind": kind, "harness": spec.harness,
                            "model": flag(spec.flags, "model"), "effort": flag(spec.flags, "effort")}
        self.pids.mkdir(parents=True, exist_ok=True)
        path = self.pids / str(os.getpid())
        scratch = path.with_name(f".{path.name}.new")
        scratch.write_text(json.dumps({"pid": os.getpid(), "session": session}) + "\n")
        os.replace(scratch, path)

    def say(self, who, text):
        print(f"{time.strftime('%H:%M:%S')} {who:<8} {text}", file=self.out, flush=True)

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

    def cooled_down(self, harness):
        """Whether `harness` is currently in a rate/usage-limit cooldown window."""
        exp = self.cooldown.get(harness)
        if exp is None:
            return False
        if self.now() >= exp:
            self.cooldown.pop(harness, None)
            return False
        return True

    def mark_cooldown(self, harness, reset):
        """Put `harness` into cooldown until its reported reset timestamp (or 1 hour + 60 s)."""
        until = (reset if reset is not None else self.now() + 3600) + 60
        self.cooldown[harness] = max(self.cooldown.get(harness, 0.0), until)
        wait_s = max(self.cooldown[harness] - self.now(), 0.0)
        self.say("loop", f"{harness} usage limit: cooling down {harness} routes for {wait_s:.0f} s")

    # Sessions.

    def tune(self):
        """Take up loop.toml when it changed since the last session; keep the last values when it is wrong."""
        text = self.config.read_text() if self.config.exists() else ""
        if text == self.read:
            return
        self.read = text
        try:
            if self.profile_name is None:
                self.flags = options(text)
                self.profile_cfg = parse_profile(text, None)
            else:
                self.profile_cfg = parse_profile(text, self.profile_name)
                self.flags = {k: list(spec.flags) for k, spec in self.profile_cfg.agents.items()}
        except ValueError as error:
            self.say("loop", f"{self.config.name}: {error}; keeping the last values")
            return
        if self.profile_name is None and self.profile_cfg.routed:
            parts = [f"{k}={fmt_spec(s)}" for k, s in self.profile_cfg.routes.items()]
            self.say("loop", f"{self.config.name} [routes]: {'; '.join(parts)}")
        elif self.profile_name is None:
            shown = "; ".join(f"{kind} {' '.join(flags)}" for kind, flags in self.flags.items() if flags)
            self.say("loop", f"{self.config.name}: {shown or 'no flags'}")
        else:
            parts = [f"{kind}[{spec.harness}] {' '.join(spec.flags)}".strip()
                     for kind, spec in self.profile_cfg.agents.items()]
            self.say("loop", f"{self.config.name} [{self.profile_name}]: {'; '.join(parts) or 'defaults'}")

    def route_spec(self, route_key):
        """The AgentSpec for `route_key`, or None when disabled or excluded by the active configuration."""
        cfg = self.profile_cfg
        if cfg.routed:
            return cfg.routes.get(route_key)
        if route_key in DELEGATABLE:
            if route_key in cfg.delegate:
                return None
            return self.spec_for("round" if route_key == RETRY else route_key, RETRY if route_key == RETRY else None)
        if route_key == "needs-land":
            return self.spec_for("round") if "needs-land" in cfg.stages else None
        if route_key in WORK_KINDS:
            return self.spec_for("round") if route_key in cfg.kinds else None
        if route_key == "epic-close":
            return self.spec_for("round") if cfg.epics in ("close", "all") else None
        if route_key == "epic-split":
            return self.spec_for("round") if cfg.epics in ("split", "all") else None
        return None

    def spec_for(self, kind, table=None):
        if self.profile_cfg.routed:
            rkey = table or self.active_route or (kind if kind in DELEGATABLE else None)
            if rkey and self.profile_cfg.routes.get(rkey) is not None:
                return self.profile_cfg.routes[rkey]
        chosen = table or kind
        if chosen in self.profile_cfg.agents:
            return self.profile_cfg.agents[chosen]
        if kind in self.profile_cfg.agents:
            return self.profile_cfg.agents[kind]
        return AgentSpec(harness="claude", flags=list(self.flags.get(chosen, [])))

    def run_routed(self, route_key, kind, prompt, table=None):
        prev = self.active_route
        self.active_route = route_key
        try:
            return self.agent(kind, prompt) if table is None else self.agent(kind, prompt, table)
        finally:
            self.active_route = prev

    def agent(self, kind, prompt, table=None):
        """Run one agent session in the main worktree, with the flags of its kind's table or of the one named; its stream is shown as it comes."""
        self.tune()
        spec = self.spec_for(kind, table)
        if spec.harness == "agy":
            body = agent_body(self.cwd, kind)
            full_prompt = f"{body}\n\n{prompt}" if body else prompt
            command = [self.agy, "--output-format", "stream-json", *spec.flags, "-p", full_prompt]
        else:
            command = [self.claude, "-p", "--agent", kind, "--permission-mode", "auto",
                       "--output-format", "stream-json", "--verbose", *spec.flags, prompt]
        started = self.now()
        self.say(kind, f"start ({spec.harness}): {prompt}")
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
        minutes = (self.now() - started) / 60
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

    # Zero-token pre-check and stage recovery for routed and profiled loops.

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
        me = os.getpid()
        for path in self.pids.glob("*"):
            if path.name.isdigit() and int(path.name) != me and loop_alive(int(path.name)):
                return True
        return False

    def inspect_work(self, claim=False):
        """Inspect Beads at zero token cost for self.profile_cfg.

        When claim=True, atomically claims the first matching non-cooled-down stage or leaf so no peer loop races it.
        Returns (action, payload, summary_dict).
        """
        self.tune()
        cfg = self.profile_cfg
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
                if sname not in cfg.stages:
                    continue
                rkey = STAGE_ROUTE[sname]
                spec = self.route_spec(rkey)
                if spec is None:
                    continue
                if self.cooled_down(spec.harness):
                    cooled.append((rkey, leaf["id"], spec.harness))
                    continue
                matched_stages.append((sname, leaf["id"], leaf.get("title", ""), spec))
                if claim:
                    ok, _ = self.beads_run("update", leaf["id"], "--claim")
                    if ok:
                        return f"stage:{sname}", (leaf["id"], rkey), {}
                break

        # 2. Plain ready leaves matching cfg.kinds (skipping leaves waiting on another stage).
        for leaf in ready:
            if issue_stages(leaf):
                continue
            labels = set(leaf.get("labels") or [])
            has_explicit = any(lbl.startswith("kind:") or lbl == "review" for lbl in labels)
            if not has_explicit:
                ensure_all()
            kind = classify_issue(leaf, by_id)
            if kind not in cfg.kinds:
                continue
            spec = self.route_spec(kind)
            if spec is None:
                continue
            if self.cooled_down(spec.harness):
                cooled.append((kind, leaf["id"], spec.harness))
                continue
            matched_leaves.append((kind, leaf["id"], leaf.get("title", ""), spec))
            if claim:
                ok, _ = self.beads_run("update", leaf["id"], "--claim")
                if ok:
                    return "leaf", (leaf["id"], kind), {}

        # 3. Epic rounds (finished epics first via tools/reviews.py, then childless ready epics).
        all_list, _ = ensure_all()
        finished_lines = reviews_mod.finished(all_list) if all_list else []
        split_epics = []
        if not finished_lines and not ready:
            ready_epics = self.beads_json("ready", "-t", "epic", "--json", "--limit", "0")
            has_child = {item.get("parent") for item in all_list if item.get("parent")}
            split_epics = [ep["id"] for ep in ready_epics if ep.get("parent") and ep["id"] not in has_child]

        close_spec = self.route_spec("epic-close")
        split_spec = self.route_spec("epic-split")
        close_ready = bool(finished_lines and close_spec is not None)
        split_ready = bool(split_epics and not ready and split_spec is not None)
        if close_ready and self.cooled_down(close_spec.harness):
            cooled.append(("epic-close", "epics", close_spec.harness))
            close_ready = False
        if split_ready and self.cooled_down(split_spec.harness):
            cooled.append(("epic-split", split_epics[0], split_spec.harness))
            split_ready = False

        summary = {
            "recovered": recovered,
            "other_live": other_live,
            "stages": matched_stages,
            "leaves": matched_leaves,
            "finished_epics": finished_lines if close_spec is not None else [],
            "split_epics": split_epics if split_spec is not None else [],
            "close_spec": close_spec,
            "split_spec": split_spec,
            "cooled": cooled,
        }
        if claim:
            if close_ready:
                return "epic_finished", "epic-close", summary
            if split_ready:
                return "epic_split", "epic-split", summary
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
        """Run or delegate the prover or the skeptic a round handed over, record or stamp, and release."""
        label = kind.capitalize()
        spec = self.route_spec(kind)
        if kind in self.profile_cfg.delegate or spec is None or self.cooled_down(spec.harness):
            stage = STAGE_FOR_DELEGATE[kind]
            self.say(kind, f"delegating {issue} via stage:{stage}")
            self.beads("update", issue, "--add-label", f"stage:{stage}", "-s", "open", "--assignee", "")
            return
        if self.stopping:
            self.beads("update", issue, "--append-notes",
                       f"{label} not run: the loop stopped before it started; the next round hands it over again.")
        else:
            run = self.agent(kind, prompt)
            if run.limited and self.profile_cfg.filtered:
                self.mark_cooldown(spec.harness, run.reset)
                stage = STAGE_FOR_DELEGATE[kind]
                self.say(kind, f"{spec.harness} hit usage limit; parking {issue} on stage:{stage}")
                self.beads("update", issue, "--add-label", f"stage:{stage}", "-s", "open", "--assignee", "")
                return
            report = run.report.strip() if run.report.strip() and not run.error else (
                f"none; the {kind}'s session ended without one (exit {run.exit}"
                f"{', usage limit' if run.limited else ''}).")
            self.beads("update", issue, "--append-notes", f"{label} report: {report}")
            if self.profile_cfg.routed and kind == "prover" and self.route_spec("needs-land") is not None:
                self.beads("update", issue, "--add-label", "stage:needs-land", "-s", "open", "--assignee", "")
                return
        self.beads("update", issue, "-s", "open", "--assignee", "")

    def run_specialist_stage(self, sname, issue):
        """Run a queued stage:needs-prover or stage:needs-skeptic directly without a wrapper round."""
        kind = "prover" if sname == "needs-prover" else "skeptic"
        label = kind.capitalize()
        if self.stopping:
            self.beads("update", issue, "-s", "open", "--assignee", "")
            return "continue", Run()
        prompt = (f"Issue {issue}, worktree {self.cwd.parent / issue}. Your input is the issue's last Prover input note."
                  if kind == "prover" else
                  f"Review {issue}. Your input is the review's last Skeptic input note.")
        spec = self.route_spec(kind)
        run = self.agent(kind, prompt)
        if run.limited:
            if spec is not None:
                self.mark_cooldown(spec.harness, run.reset)
            self.beads("update", issue, "-s", "open", "--assignee", "")
            return "cooldown", run
        report = run.report.strip() if run.report.strip() and not run.error else (
            f"none; the {kind}'s session ended without one (exit {run.exit}).")
        self.beads("update", issue, "--append-notes", f"{label} report: {report}")
        extra = ("--add-label", "stage:needs-land") if kind == "prover" else ()
        self.beads("update", issue, "--remove-label", f"stage:{sname}", *extra, "-s", "open", "--assignee", "")
        return "continue", run

    def finish_round_report(self, run, clear_stage=None):
        """Parse a round's report, clear any consumed stage label, run or delegate hand-offs, and return Loop word."""
        if run.report.strip():
            print(textwrap.indent(run.report.strip(), "    "), file=self.out, flush=True)
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
        retry_spec = self.route_spec(RETRY)
        if report.retry and ("retry" in self.profile_cfg.delegate or retry_spec is None
                             or (self.profile_cfg.filtered and self.cooled_down(retry_spec.harness))):
            self.say("retry", f"delegating {report.retry} via stage:escalated")
            self.beads("update", report.retry, "--add-label", "stage:escalated", "-s", "open", "--assignee", "")
            self.retry = None
        else:
            self.retry = report.retry
        return report.loop, run

    def round(self):
        """One round (or specialist stage pass) and its hand-off. The report's Loop word, or None when it failed."""
        self.tune()
        issue, self.retry = self.retry, None
        if issue:
            run = self.agent("round", f"Run one round. Issue {issue} is yours: a round of this loop left it unfinished.", RETRY)
            if run.limited and self.profile_cfg.filtered:
                rspec = self.route_spec(RETRY)
                if rspec is not None:
                    self.mark_cooldown(rspec.harness, run.reset)
                self.beads("update", issue, "--add-label", "stage:escalated", "-s", "open", "--assignee", "")
                return "cooldown", run
            return self.finish_round_report(run)

        if not self.profile_cfg.filtered:
            run = self.agent("round", "Run one round.")
            return self.finish_round_report(run)

        action, payload, _ = self.inspect_work(claim=True)
        if action in ("stage:needs-prover", "stage:needs-skeptic"):
            target, _ = payload
            return self.run_specialist_stage(action.split(":", 1)[1], target)
        if action == "stage:escalated":
            target, rkey = payload
            spec = self.route_spec(rkey)
            run = self.agent("round",
                             f"Run one round. Issue {target} is yours: a round left it unfinished; take no other issue.",
                             RETRY)
            if run.limited:
                if spec is not None:
                    self.mark_cooldown(spec.harness, run.reset)
                self.release_if_held(target)
                return "cooldown", run
            return self.finish_round_report(run, clear_stage=(target, "stage:escalated"))
        if action == "stage:needs-land":
            target, rkey = payload
            owner = f"profile {self.profile_name}" if self.profile_name else f"route {rkey}"
            spec = self.route_spec(rkey)
            run = self.run_routed(rkey, "round",
                                  f"Run one round. Issue {target} is yours (claimed for {owner}; take no other issue).")
            if run.limited:
                if spec is not None:
                    self.mark_cooldown(spec.harness, run.reset)
                self.release_if_held(target)
                return "cooldown", run
            return self.finish_round_report(run, clear_stage=(target, "stage:needs-land"))
        if action == "leaf":
            target, rkey = payload
            owner = f"profile {self.profile_name}" if self.profile_name else f"route {rkey}"
            spec = self.route_spec(rkey)
            run = self.run_routed(rkey, "round",
                                  f"Run one round. Issue {target} is yours (claimed for {owner}; take no other issue).")
            if run.limited:
                if spec is not None:
                    self.mark_cooldown(spec.harness, run.reset)
                self.release_if_held(target)
                return "cooldown", run
            return self.finish_round_report(run)
        if action == "epic_finished":
            spec = self.route_spec("epic-close")
            run = self.run_routed("epic-close", "round",
                                  "Run one round. Epic round only: act on finished epics from tools/reviews.py; "
                                  "do not claim from bd ready and do not run an epic split round.")
            if run.limited:
                if spec is not None:
                    self.mark_cooldown(spec.harness, run.reset)
                return "cooldown", run
            return self.finish_round_report(run)
        if action == "epic_split":
            spec = self.route_spec("epic-split")
            run = self.run_routed("epic-split", "round", "Run one round.")
            if run.limited:
                if spec is not None:
                    self.mark_cooldown(spec.harness, run.reset)
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
                label = f"profile {self.profile_name}" if self.profile_name else "configured routes"
                self.say("loop", f"no work matching {label} and no peer loop running; stopping")
                return 0
            if loop == "cooldown_wait":
                if once:
                    self.say("loop", "remaining ready work waits on a cooled-down harness; stopping (--once)")
                    return 0
                active = [exp for h, exp in list(self.cooldown.items()) if self.cooled_down(h)]
                until = max(min(min(active) - self.now(), self.wait), 1.0) if active else self.wait
                self.pause(until, "cooldown on rate-limited harness")
                continue
            if once or self.stopping or self.reloading:
                break
            if loop == "wait":
                label = f"profile {self.profile_name}" if self.profile_name else "configured routes"
                why = (f"no work matching {label}; another loop is active"
                       if self.profile_cfg.filtered else "nothing ready; another loop holds the issues in progress")
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


def list_profiles(config=CONFIG, out=sys.stdout):
    text = Path(config).read_text() if Path(config).exists() else ""
    top_flags, profiles, routes = parse_all(text)
    if top_flags:
        shown = "; ".join(f"{k}: {' '.join(v)}" for k, v in top_flags.items() if v)
        print(f"default (claude): {shown or 'agent defaults'}", file=out)
    if routes:
        shown_routes = ", ".join(f"{k}={fmt_spec(s)}" for k, s in routes.items())
        print(f"routes (auto): {shown_routes}", file=out)
    if not profiles and not routes:
        print("no [routes] or [profiles.<name>] defined in loop.toml", file=out)
        return 0
    for name, cfg in sorted(profiles.items()):
        agents = ", ".join(f"{k}={fmt_spec(s)}" for k, s in cfg.agents.items())
        print(f"{name}: kinds={list(cfg.kinds)} stages={list(cfg.stages)} epics={cfg.epics} "
              f"delegate={sorted(cfg.delegate)} | {agents}", file=out)
    return 0


def check_profile(profile, config=CONFIG, out=sys.stdout):
    loop = Loop(config=config, profile=profile, out=out)
    _, _, summary = loop.inspect_work(claim=False)
    tag = (f"profile {profile}" if profile else
           ("auto-routed [routes]" if loop.profile_cfg.routed else "unfiltered"))
    print(f"=== {tag} ===", file=out)
    print(f"abandoned recoverable: {summary['recovered'] or 'none'} (other live actors: {summary['other_live']})", file=out)
    print(f"matching stages ({len(summary['stages'])}): "
          + (", ".join(f"{i} [{s} -> {fmt_spec(sp)}]" for s, i, _, sp in summary["stages"]) or "none"), file=out)
    print(f"matching leaves ({len(summary['leaves'])}): "
          + (", ".join(f"{i} [{k} -> {fmt_spec(sp)}]" for k, i, _, sp in summary["leaves"]) or "none"), file=out)
    close_tag = f" -> {fmt_spec(summary['close_spec'])}" if summary["close_spec"] else ""
    split_tag = f" -> {fmt_spec(summary['split_spec'])}" if summary["split_spec"] else ""
    print(f"finished epics ({len(summary['finished_epics'])}{close_tag}): "
          + ("; ".join(summary["finished_epics"]) or "none"), file=out)
    print(f"splittable epics ({len(summary['split_epics'])}{split_tag}): "
          + (", ".join(summary["split_epics"]) or "none"), file=out)
    return 0


def main_loop(args):
    loop = Loop(wait=args.wait, profile=args.profile)
    if args.profile is not None:
        text = loop.config.read_text() if loop.config.exists() else ""
        parse_profile(text, args.profile)
    loop.record()
    pidfile = PIDS / str(os.getpid())
    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGUSR1):
        signal.signal(signum, loop.on_stop)
    signal.signal(signal.SIGHUP, loop.on_reload)
    prof = f" (profile {args.profile})" if args.profile else ""
    loop.say("loop", f"actor {loop.actor}{prof}; stop with Ctrl-C or tools/loop.py --stop {os.getpid()}")
    try:
        status = loop.drive(once=args.once)
    finally:
        pidfile.unlink(missing_ok=True)
    if loop.reloading and not loop.stopping and not args.once:
        os.execv(sys.executable, [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]])
    return status


SIGNALS = {signal.SIGTERM: "stopping after its run in flight", signal.SIGUSR1: "ending now",
           signal.SIGHUP: "re-executing after its run in flight"}


def send(pids, signum, folder=PIDS):
    """Signal each named loop, or every loop with a pid file; a pid file whose process is no loop is removed."""
    named = [int(pid) for pid in pids] or sorted(int(path.name) for path in folder.glob("*") if path.name.isdigit())
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
            round_, prover = ({"kind": kind, "harness": "claude", "model": model, "effort": effort}
                              for kind, model, effort in (("round", "fable", "high"), ("prover", None, None)))
            self.assertEqual(self.log(folder, "pidfile"), [{"pid": os.getpid(), "session": session} for session in (round_, prover, round_)])
            self.assertEqual(json.loads((folder / str(os.getpid())).read_text()), {"pid": os.getpid(), "session": None})

    def test_a_stop_before_a_hand_off_releases_the_issue_without_running_the_skeptic(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "Skeptic: atmo-1.4\nLoop: continue\n")
            real = loop.agent

            def agent_then_stop(kind, prompt):
                run = real(kind, prompt)
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

            def agent_then_edit(kind, prompt):
                run = real(kind, prompt)
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

            def agent_then_reload(kind, prompt):
                run = real(kind, prompt)
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

    def test_profiles_parse_claude_and_agy_flags_and_selectors(self):
        text = textwrap.dedent("""\
            [round]
            model = "fable"
            autocompact = "200k"

            [profiles.carbon]
            harness = "agy"
            model = "gemini-4-carbon-high"
            kinds = ["tool", "sys", "proof", "review"]
            stages = ["needs-land"]
            epics = "close"
            delegate = ["prover", "skeptic", "retry"]

            [profiles.fable]
            harness = "claude"
            kinds = ["spec"]
            stages = ["needs-prover", "escalated"]
            epics = "none"
            [profiles.fable.round]
            model = "fable"
            effort = "high"
            autocompact = "200k"
            [profiles.fable.retry]
            model = "fable"
            effort = "xhigh"
            [profiles.fable.prover]
            model = "fable"
            effort = "xhigh"
            autocompact = "400k"
            """)
        self.assertEqual(options(text), {"round": ["--model", "fable", "--autocompact", "200k"]})
        carbon = parse_profile(text, "carbon")
        self.assertEqual((carbon.name, carbon.filtered, carbon.kinds, carbon.stages, carbon.epics, carbon.delegate),
                         ("carbon", True, ("tool", "sys", "proof", "review"), ("needs-land",), "close",
                          frozenset({"prover", "skeptic", "retry"})))
        self.assertEqual((carbon.agents["round"].harness, carbon.agents["round"].flags),
                         ("agy", ["--dangerously-skip-permissions", "--model", "gemini-4-carbon-high"]))
        fable = parse_profile(text, "fable")
        self.assertEqual((fable.agents["round"].harness, fable.agents["round"].flags),
                         ("claude", ["--model", "fable", "--effort", "high", "--autocompact", "200k"]))
        self.assertEqual(fable.agents["prover"].flags, ["--model", "fable", "--effort", "xhigh", "--autocompact", "400k"])
        for bad in (
            '[profiles.x]\nharness = "agy"\nautocompact = "200k"\n',
            '[profiles.x]\nharness = "agy"\nfallback-model = "opus"\n',
            '[profiles.x]\nharness = "claude"\nmode = "auto"\n',
            '[profiles.x]\nharness = "grok"\n',
            '[profiles.x]\nkinds = ["magic"]\n',
            '[profiles.x]\nstages = ["needs-magic"]\n',
            '[profiles.x]\nepics = "some"\n',
            '[profiles.x]\ndelegate = ["round"]\n',
        ):
            with self.assertRaises(ValueError, msg=bad):
                parse_profile(bad, "x")
        with self.assertRaises(ValueError):
            parse_profile(text, "missing")

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
            loop, _ = self.driver(folder, agy=str(fake_agy), profile="carbon")
            (folder / "loop.toml").write_text('[profiles.carbon]\nharness = "agy"\nmodel = "gemini-4-carbon-high"\neffort = "high"\n')
            (folder / "ready.json").write_text('[{"id": "atmo-1.2", "title": "Fix tool", "issue_type": "task", "priority": 1, "labels": ["kind:tool"]}]')
            self.assertEqual(loop.drive(once=True), 0)
            [call] = self.log(folder, "agy")
            self.assertEqual(call[:8], ["--output-format", "stream-json", "--dangerously-skip-permissions",
                                        "--model", "gemini-4-carbon-high", "--effort", "high", "-p"])
            self.assertTrue(call[8].startswith("You run one round.\n\nRun one round. Issue atmo-1.2 is yours"))
            self.assertNotIn("model: opus", call[8])
            self.assertEqual(call[9], loop.actor)

    def test_zero_token_precheck_skips_llm_when_no_work_matches_and_recovers_abandoned_leaves(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, clock = self.driver(folder, "Loop: stop\n", profile="carbon", wait=300)
            (folder / "loop.toml").write_text('[profiles.carbon]\nkinds = ["tool"]\nepics = "none"\n')
            (folder / "ready.json").write_text('[{"id": "atmo-1.9", "title": "Prove kernel spec", "issue_type": "task", "priority": 1, "labels": ["kind:spec"]}]')
            self.assertEqual(loop.drive(), 0)
            self.assertEqual(self.log(folder, "claude"), [])
            self.assertEqual(clock[0], 0.0)

            # While a peer loop is alive, the idle profile waits instead of exiting, then stops once signalled.
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

    def test_profile_claims_matching_leaf_by_inference_and_runs_epic_close_without_stealing_other_leaves(self):
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
            loop, _ = self.driver(folder, "Loop: continue\n", "Loop: continue\n", profile="carbon")
            (folder / "loop.toml").write_text('[profiles.carbon]\nkinds = ["tool"]\nepics = "close"\n')
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

    def test_delegated_hand_offs_stamp_stage_labels_and_specialist_profile_runs_them(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            toml = textwrap.dedent("""\
                [profiles.carbon]
                kinds = ["proof", "review"]
                stages = ["needs-land"]
                epics = "none"
                delegate = ["prover", "skeptic", "retry"]

                [profiles.fable]
                kinds = []
                stages = ["needs-prover", "escalated"]
                epics = "none"
                [profiles.fable.retry]
                model = "fable"
                effort = "xhigh"
                [profiles.fable.prover]
                model = "fable"
                effort = "xhigh"
                """)
            (folder / "loop.toml").write_text(toml)
            carbon, _ = self.driver(folder, "Prover: atmo-1.1\nLoop: continue\n", "Skeptic: atmo-1.2\nLoop: continue\n",
                                    "Retry: atmo-1.3\nLoop: continue\n", profile="carbon")
            for issue_id, lbl in (("atmo-1.1", "kind:proof"), ("atmo-1.2", "review"), ("atmo-1.3", "kind:proof")):
                (folder / "ready.json").write_text(json.dumps([{"id": issue_id, "title": "x", "issue_type": "task", "priority": 1, "labels": [lbl]}]))
                self.assertEqual(carbon.drive(once=True), 0)
            bd_calls = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.1", "--add-label", "stage:needs-prover", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.2", "--add-label", "stage:needs-skeptic", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.3", "--add-label", "stage:escalated", "-s", "open", "--assignee", ""], bd_calls)

            fable, _ = self.driver(folder, "Verified 10, 0 errors.", "Loop: continue\n", profile="fable")
            (folder / "loop.toml").write_text(toml)
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

    def test_routes_table_parses_per_kind_and_stage_models_default_and_disabled(self):
        text = textwrap.dedent("""\
            [routes.default]
            harness = "agy"
            model = "gemini-4-carbon-medium"

            [routes.epic-close]
            model = "gemini-4-carbon-low"

            [routes.needs-land]
            model = "gemini-4-carbon-low"

            [routes.proof]
            model = "gemini-4-carbon-high"

            [routes.arch]
            harness = "claude"
            model = "opus"
            effort = "high"

            [routes.prover]
            harness = "claude"
            model = "fable"
            effort = "xhigh"
            autocompact = "400k"

            [routes.skeptic]
            harness = "claude"
            model = "opus"
            effort = "xhigh"

            [routes.retry]
            harness = "claude"
            model = "fable"
            effort = "xhigh"
            """)
        cfg = parse_profile(text, None)
        self.assertTrue(cfg.routed)
        self.assertTrue(cfg.filtered)
        self.assertEqual((cfg.routes["tool"].harness, cfg.routes["tool"].flags),
                         ("agy", ["--dangerously-skip-permissions", "--model", "gemini-4-carbon-medium"]))
        self.assertEqual((cfg.routes["proof"].harness, cfg.routes["proof"].flags),
                         ("agy", ["--dangerously-skip-permissions", "--model", "gemini-4-carbon-high"]))
        self.assertEqual(cfg.routes["epic-close"].flags,
                         ["--dangerously-skip-permissions", "--model", "gemini-4-carbon-low"])
        self.assertEqual(cfg.routes["needs-land"].flags,
                         ["--dangerously-skip-permissions", "--model", "gemini-4-carbon-low"])
        self.assertEqual((cfg.routes["arch"].harness, cfg.routes["arch"].flags),
                         ("claude", ["--model", "opus", "--effort", "high"]))
        self.assertEqual((cfg.routes["prover"].harness, cfg.routes["prover"].flags),
                         ("claude", ["--model", "fable", "--effort", "xhigh", "--autocompact", "400k"]))

        disabled_toml = text + "\n[routes.epic-split]\ndisabled = true\n"
        cfg2 = parse_profile(disabled_toml, None)
        self.assertIsNone(cfg2.routes["epic-split"])
        for bad in ('[routes.magic]\nmodel = "opus"\n', '[routes.tool]\ndisabled = "yes"\n'):
            with self.assertRaises(ValueError, msg=bad):
                parse_profile(bad, None)

    def test_auto_routed_loop_dispatches_difficulty_and_harness_per_task_without_profile_flag(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            fake_agy = folder / "agy"
            fake_agy.write_text(
                f"#!{sys.executable}\nimport json, os, sys\n"
                f"open({str(folder / 'agy.log')!r}, 'a').write(json.dumps(sys.argv[1:]) + '\\n')\n"
                f"q = sorted(n for n in os.listdir({str(folder)!r}) if n.startswith('agy-reply-'))\n"
                f"r = open(os.path.join({str(folder)!r}, q[0])).read(); os.remove(os.path.join({str(folder)!r}, q[0]))\n"
                "print(json.dumps({'event': 'result', 'result': {'status': 'SUCCESS', 'response': r, 'num_turns': 1, 'usage': {}}}))\n"
            )
            fake_agy.chmod(0o755)
            for idx, reply in enumerate(("Prover: atmo-1.1\nLoop: continue\n", "Loop: continue\n", "Loop: continue\n")):
                (folder / f"agy-reply-{idx:03}").write_text(reply)

            loop, _ = self.driver(folder, "Verified 12, 0 errors.", agy=str(fake_agy))
            (folder / "loop.toml").write_text(textwrap.dedent("""\
                [routes.default]
                harness = "agy"
                model = "gemini-4-carbon-medium"
                [routes.epic-close]
                model = "gemini-4-carbon-low"
                [routes.needs-land]
                model = "gemini-4-carbon-low"
                [routes.proof]
                model = "gemini-4-carbon-high"
                [routes.prover]
                harness = "claude"
                model = "fable"
                effort = "xhigh"
                """))
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
            self.assertEqual((claude_call[2], claude_call[8:-2]), ("prover", ["--model", "fable", "--effort", "xhigh"]))
            bd_calls = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.1", "--add-label", "stage:needs-land", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.1", "--remove-label", "stage:needs-land"], bd_calls)

    def test_per_harness_quota_cooldown_parks_limited_provider_and_continues_other_harness(self):
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
            fake_agy = folder / "agy"
            fake_agy.write_text(
                f"#!{sys.executable}\nimport json, sys\n"
                f"open({str(folder / 'agy.log')!r}, 'a').write(json.dumps(sys.argv[1:]) + '\\n')\n"
                "print(json.dumps({'event': 'result', 'result': {'status': 'SUCCESS', 'response': 'Prover: atmo-1.2\\nLoop: continue\\n', 'num_turns': 1, 'usage': {}}}))\n"
            )
            fake_agy.chmod(0o755)
            loop, clock = self.driver(folder, agy=str(fake_agy))
            loop.claude = str(fake_claude)
            (folder / "loop.toml").write_text(textwrap.dedent("""\
                [routes.default]
                harness = "agy"
                model = "gemini-4-carbon-medium"
                [routes.prover]
                harness = "claude"
                model = "fable"
                effort = "xhigh"
                [routes.skeptic]
                harness = "claude"
                model = "opus"
                effort = "xhigh"
                """))
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Review epic", "issue_type": "task", "priority": 0, "labels": ["review", "stage:needs-skeptic"]},
                {"id": "atmo-1.2", "title": "Tool fix", "issue_type": "task", "priority": 2, "labels": ["kind:tool"]},
            ]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(clock[0], 0.0)
            self.assertTrue(loop.cooled_down("claude"))
            self.assertFalse(loop.cooled_down("agy"))
            self.assertEqual(len(self.log(folder, "claude")), 1)
            self.assertEqual(len(self.log(folder, "agy")), 1)
            bd_calls = self.log(folder, "bd")
            self.assertIn(["update", "atmo-1.1", "-s", "open", "--assignee", ""], bd_calls)
            self.assertIn(["update", "atmo-1.2", "--add-label", "stage:needs-prover", "-s", "open", "--assignee", ""], bd_calls)

            # With only claude-routed work left, --once exits 0 at zero tokens without invoking claude again.
            (folder / "ready.json").write_text(json.dumps([
                {"id": "atmo-1.1", "title": "Review epic", "issue_type": "task", "priority": 0, "labels": ["review", "stage:needs-skeptic"]},
            ]))
            self.assertEqual(loop.drive(once=True), 0)
            self.assertEqual(len(self.log(folder, "claude")), 1)
            self.assertEqual(len(self.log(folder, "agy")), 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--profile", help="run the named [profiles.<name>] configuration from loop.toml")
    parser.add_argument("--list-profiles", action="store_true", help="list profiles in loop.toml and exit")
    parser.add_argument("--check", action="store_true", help="show matching ready work at zero token cost and exit")
    parser.add_argument("--once", action="store_true", help="run one round and its hand-off, then stop")
    parser.add_argument("--wait", type=float, default=WAIT, help="seconds to wait on 'Loop: wait'")
    parser.add_argument("--stop", action="store_true", help="stop running loops after their run in flight")
    parser.add_argument("--now", action="store_true", help="with --stop, end the run in flight too")
    parser.add_argument("--reload", action="store_true", help="re-execute running loops after their run in flight")
    parser.add_argument("--test", action="store_true", help="run this script's own tests")
    parser.add_argument("pids", nargs="*", help="with --stop or --reload, the loops to signal; all by default")
    args = parser.parse_args()
    if args.test:
        unittest.main(argv=[sys.argv[0]], verbosity=1)
    if args.list_profiles:
        return list_profiles()
    if args.check:
        return check_profile(args.profile)
    if args.stop and args.reload:
        parser.error("--stop and --reload are each their own command")
    if args.stop:
        return send(args.pids, signal.SIGUSR1 if args.now else signal.SIGTERM)
    if args.reload:
        return send(args.pids, signal.SIGHUP)
    if args.pids or args.now:
        parser.error("PID goes with --stop or --reload, --now with --stop")
    return main_loop(args)


if __name__ == "__main__":
    sys.exit(main())
