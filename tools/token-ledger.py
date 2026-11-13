#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The tokens each Beads issue cost, out of the transcripts Claude Code and Grok keep for this project.

Claude Code writes one transcript per session under ~/.claude/projects/<the session's directory,
every character not a letter or digit made '-'>, and one per agent the session spawned under
<session>/subagents/, with the agent's type beside it in agent-<id>.meta.json. A session started as
an agent (`claude -p --agent round`, as tools/loop.py runs each round, prover and skeptic) counts as
that agent: its transcript's first line names it (`"type":"agent-setting"`). Every API call is an
assistant line carrying its request id and its usage. A harvest reads each transcript from where
the last one stopped, whole lines only, into a SQLite ledger: one row per request id, so a call
written on several lines counts once, and a total per issue, agent kind, model and hour, kept as
calls arrive, so what the page asks for stays small however long the history grows.

A call goes to the issue its transcript was working:
- a round agent's or a session's, from the moment it claims one (`bd ready --claim`, whose reply
  names it, or `bd update <id> ... --claim`) until it claims another or closes that one; a round
  that claims nothing, as one closing an epic does, works the first issue it updates or closes; a
  round's calls before its first claim go to that claim; a round tools/loop.py pins to the issue an
  earlier round left unfinished works the issue its first prompt names, as if it had claimed it;
- a prover's or a skeptic's, the issue or review its first prompt names;
- any other, none, which the page counts at the root.

Grok writes one directory per session under ~/.grok/sessions/<the session's cwd, percent-encoded>,
and the transcript is that directory's updates.jsonl. A turn_completed line stamps the turn's token
buckets (inputTokens, cachedReadTokens, cacheCreationTokens, outputTokens) and costUsdTicks, 10^10
ticks a dollar. The ledger stores the buckets in the same columns as a Claude call and does not store
the dollar stamp: list price is not the unit. inputTokens counts the cache buckets inside it when
totalTokens is inputTokens plus outputTokens, and those buckets then go in their own columns. The
prompt id is the request id, so a turn a resumed session repeats counts once. The kind is round,
prover or skeptic when the first user message is the loop's prompt for that agent, and a session's
otherwise; the issue is read by the same rules as a Claude transcript. A session whose cwd is not
this project root or somewhere below it is not this project's.

The ledger keeps what it harvested after Claude Code or Grok removes a transcript, so the history outlives
the transcripts' retention.

A harvest also keeps the plan's meter as Claude Code last fetched it (`cachedUsageUtilization` in
~/.claude.json, which holds the newest fetch alone), one row of the table `readings` per fetch:
`fetched_ms`, the fetch's time in milliseconds since the epoch; `percent`, how much of the week's
limit every model together has used; `resets_at`, when that week ends; and `scoped`, a JSON object
holding each scoped limit under the name of the model it is for, as `percent` of its own allowance,
`share`, that allowance in percent of the week's limit, and its own `resets_at`. So
`json_extract(scoped, '$.Fable.percent')` is the Fable meter. A rate is fitted between two readings
(tools/leaf-cost.py), and a reading lower than the one before it with `resets_at` unchanged shows a
reset the human spent between them. A fetch no harvest saw is not in the table: the readings are as
close together as the harvests were.

usage: tools/token-ledger.py [--ledger PATH]   (harvest this project's transcripts and print each kind's total)
       tools/token-ledger.py --test             (this script's own tests)
"""
import argparse
import json
import re
import sqlite3
import sys
import tempfile
import unittest
import urllib.parse
from datetime import datetime, timezone
from pathlib import Path

KINDS = ("input", "cache_write", "cache_read", "output")
USAGE = ("input_tokens", "cache_creation_input_tokens", "cache_read_input_tokens", "output_tokens")
ISSUE = r"[a-z][a-z0-9]*-[a-z0-9]+(?:\.[0-9]+)*"
CLAIM = re.compile(rf"\bbd\s+update\s+({ISSUE})\b[^;&|\n]*--claim\b")
READY_CLAIM = re.compile(r"\bbd\s+ready\b[^;&|\n]*--claim\b")
CLOSE = re.compile(rf"\bbd\s+close\s+({ISSUE})\b")
WRITE = re.compile(rf"\bbd\s+(?:update|close)\s+({ISSUE})\b")
PROMPTED = re.compile(rf"\b(?:Issue|Review|Epic):?\s+({ISSUE})\b")
FIRST_ID = re.compile(rf'"id":\s*"({ISSUE})"')
PINNED = re.compile(rf"^Run one round\. Issue ({ISSUE}) is yours\b")
ROUND_PIN = re.compile(rf"Run one round\. Issue ({ISSUE}) is yours\b")
PROVER_PIN = re.compile(rf"Issue ({ISSUE}), worktree\b")
SKEPTIC_PIN = re.compile(rf"Review ({ISSUE})\. Your input is the review's last Skeptic input note")
NAMED_BY_PROMPT = ("prover", "skeptic")
SESSION = "session"

SCHEMA = """
create table if not exists files (path text primary key, id integer unique, offset integer, state text);
create table if not exists calls (request text primary key, file integer, issue text, kind text, model text, hour integer,
    input integer, cache_write integer, cache_read integer, output integer);
create index if not exists calls_file on calls (file, issue);
create table if not exists totals (issue text, kind text, model text, hour integer,
    input integer, cache_write integer, cache_read integer, output integer, calls integer,
    primary key (issue, kind, model, hour));
create table if not exists readings (fetched_ms integer primary key, percent real, resets_at text, scoped text);
"""


def directories(projects, root):
    """The transcript directories of sessions run at this project root or anywhere below it."""
    name = re.sub(r"[^A-Za-z0-9]", "-", str(root))
    return sorted(path for path in projects.glob(name + "*") if path.is_dir() and path.name[len(name):][:1] in ("", "-"))


def transcripts(directory):
    """Each transcript in that directory with its kind: a session's, or its agent's type."""
    for path in sorted(directory.glob("*.jsonl")):
        yield path, started_as(path)
    for path in sorted(directory.glob("*/subagents/agent-*.jsonl")):
        try:
            kind = json.loads(path.with_suffix(".meta.json").read_text()).get("agentType") or "agent"
        except (OSError, ValueError):
            kind = "agent"
        yield path, kind


def started_as(path):
    """The agent a session was started as, from its transcript's first line; a session's kind when it was started as none."""
    try:
        with path.open("rb") as stream:
            line = json.loads(stream.readline())
    except (OSError, ValueError):
        return SESSION  # removed since the listing, empty, or its first line still being written
    if isinstance(line, dict) and line.get("type") == "agent-setting" and isinstance(line.get("agentSetting"), str):
        return line["agentSetting"]
    return SESSION


def connect(ledger):
    ledger.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(ledger, timeout=60, isolation_level=None)
    db.execute("pragma journal_mode = wal")
    db.executescript(SCHEMA)
    return db


def hour_of(stamp):
    """The hour a UTC timestamp is in, as the seconds from the epoch to its start."""
    return int(datetime.fromisoformat(stamp[:13] + ":00:00+00:00").timestamp())


def add(db, issue, kind, model, hour, counts, calls):
    db.execute(
        "insert into totals values (?, ?, ?, ?, ?, ?, ?, ?, ?) on conflict do update set "
        "input = input + excluded.input, cache_write = cache_write + excluded.cache_write, "
        "cache_read = cache_read + excluded.cache_read, output = output + excluded.output, calls = calls + excluded.calls",
        (issue, kind, model, hour, *counts, calls),
    )
    if calls < 0:
        db.execute("delete from totals where issue = ? and kind = ? and model = ? and hour = ? and calls = 0", (issue, kind, model, hour))


def record(db, file, state, kind, line):
    """Count the call an assistant line carries, under the issue the transcript is working now."""
    request = line.get("requestId")
    usage = line["message"].get("usage")
    if not request or not usage:
        return
    counts = [usage.get(field) or 0 for field in USAGE]
    model = line["message"].get("model") or ""
    old = db.execute("select input, cache_write, cache_read, output, issue, kind, model, hour from calls where request = ?", (request,)).fetchone()
    if old is None:
        when = hour_of(line["timestamp"])
        db.execute("insert into calls values (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)", (request, file, state["issue"], kind, model, when, *counts))
        add(db, state["issue"], kind, model, when, counts, 1)
        return
    # The same call on a later line: its usage only grows as the reply streams.
    grown = [max(new, was) - was for new, was in zip(counts, old[:4])]
    if any(grown):
        db.execute(
            "update calls set input = input + ?, cache_write = cache_write + ?, cache_read = cache_read + ?, output = output + ? where request = ?",
            (*grown, request),
        )
        add(db, *old[4:], grown, 0)


def claim(db, file, state, kind, issue):
    """The transcript works that issue from now; a round's calls so far, made before any claim, go to it too."""
    if kind == "round" and not state["claimed"]:
        for row in db.execute("select kind, model, hour, sum(input), sum(cache_write), sum(cache_read), sum(output), count(*) from calls "
                              "where file = ? and issue = '' group by kind, model, hour", (file,)).fetchall():
            add(db, "", *row[:3], [-count for count in row[3:7]], -row[7])
            add(db, issue, *row[:3], row[3:7], row[7])
        db.execute("update calls set issue = ? where file = ? and issue = ''", (issue, file))
    state["issue"] = issue
    state["claimed"] = True


def blocks(line):
    content = line.get("message", {}).get("content")
    return content if isinstance(content, list) else []


def text(content):
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "\n".join(part.get("text", "") for part in content if isinstance(part, dict))
    return ""


def follow(db, file, state, kind, raw):
    """One whole line of a transcript: count its call, then see whether it moves the transcript to another issue."""
    if b'"requestId"' in raw and b'"usage"' in raw:
        line = json.loads(raw)
        if line.get("type") == "assistant":
            record(db, file, state, kind, line)
    if kind in NAMED_BY_PROMPT and not state["prompted"] and b'"type":"user"' in raw:
        line = json.loads(raw)
        state["prompted"] = True
        found = PROMPTED.search(text(line.get("message", {}).get("content")))
        if found:
            state["issue"] = found.group(1)
        return
    if kind in NAMED_BY_PROMPT:
        return
    if kind == "round" and not state["prompted"] and b'"type":"user"' in raw:
        state["prompted"] = True
        found = PINNED.match(text(json.loads(raw).get("message", {}).get("content")))
        if found:
            claim(db, file, state, kind, found.group(1))
    if b"bd " in raw and b'"tool_use"' in raw:
        for block in blocks(json.loads(raw)):
            command = block.get("input", {}).get("command", "") if block.get("type") == "tool_use" else ""
            written = WRITE.search(command)
            if kind == "round" and not state["claimed"] and written and not CLAIM.search(command):
                claim(db, file, state, kind, written.group(1))
            for found in CLAIM.finditer(command):
                claim(db, file, state, kind, found.group(1))
            if READY_CLAIM.search(command):
                state["waiting"].append(block["id"])
            for found in CLOSE.finditer(command):
                if found.group(1) == state["issue"]:
                    state["issue"] = ""
    if state["waiting"] and b'"tool_result"' in raw:
        for block in blocks(json.loads(raw)):
            if block.get("type") == "tool_result" and block.get("tool_use_id") in state["waiting"]:
                state["waiting"].remove(block["tool_use_id"])
                found = FIRST_ID.search(text(block.get("content")))
                if found:
                    claim(db, file, state, kind, found.group(1))


def grok_text(update):
    """The text of a Grok user message."""
    content = update.get("content")
    return content.get("text") or "" if isinstance(content, dict) else ""


def grok_result_text(update):
    """The text of a Grok tool result."""
    content = update.get("content")
    if not isinstance(content, list):
        return ""
    parts = []
    for item in content:
        inner = item.get("content") if isinstance(item, dict) else None
        if isinstance(inner, dict) and isinstance(inner.get("text"), str):
            parts.append(inner["text"])
        elif isinstance(inner, str):
            parts.append(inner)
    return "\n".join(parts)


def grok_prompt(text):
    """The loop's prompt inside a Grok user message, in the shape a Claude transcript's first user line has."""
    found = ROUND_PIN.search(text)
    if found:
        return found.group(0)
    if "Run one round." in text:
        return "Run one round."
    found = PROVER_PIN.search(text) if "Prover input note" in text else None
    if found:
        return f"Issue {found.group(1)}, worktree x. Your input is the issue's last Prover input note."
    found = SKEPTIC_PIN.search(text)
    if found:
        return found.group(0)
    return ""


def grok_buckets(usage):
    """The ledger's four columns from the usage object a Grok turn stamps."""
    cached = int(usage.get("cachedReadTokens") or 0)
    created = int(usage.get("cacheCreationTokens") or 0)
    incoming = int(usage.get("inputTokens") or 0)
    output = int(usage.get("outputTokens") or 0)
    # totalTokens is inputTokens + outputTokens, so a cache bucket that fits in inputTokens was counted
    # there. It is stored in its own column, as a Claude call's cache buckets are.
    if usage.get("totalTokens") == incoming + output and incoming >= cached + created:
        incoming -= cached + created
    return {"input_tokens": incoming, "cache_creation_input_tokens": created,
            "cache_read_input_tokens": cached, "output_tokens": output}


def grok_lines(raw, model):
    """The Claude-shaped lines one Grok updates.jsonl line counts as, or none."""
    try:
        obj = json.loads(raw)
    except ValueError:
        return ()
    update = (obj.get("params") or {}).get("update")
    if not isinstance(update, dict):
        return ()
    event = update.get("sessionUpdate")
    if event == "user_message_chunk":
        content = grok_prompt(grok_text(update))
        if not content:
            return ()
        return (json.dumps({"type": "user", "message": {"content": content}}, separators=(",", ":")).encode(),)
    if event == "tool_call":
        command = (update.get("rawInput") or {}).get("command") if isinstance(update.get("rawInput"), dict) else None
        if not isinstance(command, str) or not update.get("toolCallId"):
            return ()
        line = {"type": "assistant", "message": {"content": [
            {"type": "tool_use", "id": update["toolCallId"], "name": "Bash", "input": {"command": command}}]}}
        return (json.dumps(line, separators=(",", ":")).encode(),)
    if event == "tool_call_update":
        text = grok_result_text(update)
        if not text or not update.get("toolCallId"):
            return ()
        line = {"type": "user", "message": {"content": [
            {"type": "tool_result", "tool_use_id": update["toolCallId"], "content": text}]}}
        return (json.dumps(line, separators=(",", ":")).encode(),)
    if event != "turn_completed":
        return ()
    usage = update.get("usage")
    prompt = update.get("prompt_id")
    stamp = obj.get("timestamp")
    if not isinstance(usage, dict) or not isinstance(prompt, str) or not isinstance(stamp, str):
        return ()
    names = [name for name in (usage.get("modelUsage") or {}) if isinstance(name, str)]
    line = {"type": "assistant", "requestId": prompt, "timestamp": stamp, "message": {
        "model": names[0] if len(names) == 1 else model, "usage": grok_buckets(usage)}}
    return (json.dumps(line, separators=(",", ":")).encode(),)


def grok_directories(sessions, root):
    """The Grok session directories of runs whose cwd is this project root or anywhere below it."""
    if not sessions.is_dir():
        return []
    root = Path(root).resolve()
    found = []
    for path in sessions.iterdir():
        if not path.is_dir():
            continue
        cwd = Path(urllib.parse.unquote(path.name))
        if cwd == root or root in cwd.parents:
            found.append(path)
    return sorted(found)


def grok_kind(session_dir):
    """The agent a Grok session was, from the loop's prompt in its first user message, and its model."""
    model, agent = "", None
    try:
        summary = json.loads((session_dir / "summary.json").read_text())
        model = summary.get("current_model_id") or ""
        if summary.get("agent_name") in ("round", "prover", "skeptic"):
            agent = summary["agent_name"]
    except (OSError, ValueError):
        pass
    text = ""
    try:
        with (session_dir / "updates.jsonl").open() as stream:
            for raw in stream:
                if "user_message_chunk" not in raw:
                    continue
                try:
                    update = json.loads(raw)["params"]["update"]
                except (ValueError, KeyError, TypeError):
                    continue
                if isinstance(update, dict) and update.get("sessionUpdate") == "user_message_chunk":
                    text = grok_text(update)
                    break
    except OSError:
        pass
    if "Run one round." in text:
        return "round", model
    if "Prover input note" in text:
        return "prover", model
    if "Skeptic input note" in text:
        return "skeptic", model
    return agent or SESSION, model


def grok_sessions(directory):
    """Each Grok session's transcript in that directory, with its kind and model, oldest first."""
    found = []
    for path in directory.iterdir():
        if path.is_dir() and (path / "updates.jsonl").is_file():
            found.append(path)

    def created(path):
        try:
            return json.loads((path / "summary.json").read_text()).get("created_at") or ""
        except (OSError, ValueError):
            return ""

    for path in sorted(found, key=lambda path: (created(path), path.name)):
        kind, model = grok_kind(path)
        yield path / "updates.jsonl", kind, model


def read(db, path, kind, adapt=None):
    """Take in what was appended to that transcript since the last harvest; the number of lines taken.
    adapt turns one source line into the Claude-shaped lines follow counts, when the transcript is not Claude's."""
    size = path.stat().st_size
    db.execute("begin immediate")
    try:
        row = db.execute("select id, offset, state from files where path = ?", (str(path),)).fetchone()
        if row is None:
            file = (db.execute("select coalesce(max(id), 0) + 1 from files").fetchone()[0])
            offset, state = 0, {"issue": "", "claimed": False, "prompted": False, "waiting": []}
        else:
            file, offset, state = row[0], row[1], json.loads(row[2])
            if size < offset:
                # Rewritten from the start: read it again; the calls already counted are known by their request ids.
                offset, state = 0, {"issue": "", "claimed": False, "prompted": False, "waiting": []}
        taken = 0
        if size > offset:
            with path.open("rb") as stream:
                stream.seek(offset)
                data = stream.read(size - offset)
            whole = data.rfind(b"\n") + 1
            for raw in data[:whole].split(b"\n")[:-1]:
                if raw.strip():
                    for line in (adapt(raw) if adapt else (raw,)):
                        try:
                            follow(db, file, state, kind, line)
                        except (ValueError, KeyError, TypeError, AttributeError):
                            pass  # a line of a shape this does not know carries nothing it counts
                    taken += 1
            offset += whole
        db.execute("insert or replace into files values (?, ?, ?, ?)", (str(path), file, offset, json.dumps(state)))
        db.execute("commit")
        return taken
    except BaseException:
        db.execute("rollback")
        raise


def reading(account):
    """The meter as Claude Code's account file holds it, as a row of `readings`; None when the file
    holds no reading of the shape this knows."""
    try:
        cached = json.loads(account.read_text())["cachedUsageUtilization"]
        meter = cached["utilization"]
        shares = {share["limit_index"]: share["allowance_percent_of_weekly"] for share in meter.get("weekly_scoped_shares") or []}
        scoped = {}
        for index, limit in enumerate(meter.get("limits") or []):
            if limit["kind"] == "weekly_scoped":
                name = (limit["scope"].get("model") or {}).get("display_name") or json.dumps(limit["scope"], sort_keys=True)
                scoped[name] = {"percent": limit["percent"], "share": shares.get(index), "resets_at": limit["resets_at"]}
        return int(cached["fetchedAtMs"]), meter["seven_day"]["utilization"], meter["seven_day"]["resets_at"], json.dumps(scoped, sort_keys=True)
    except (OSError, ValueError, KeyError, TypeError, AttributeError):
        return None  # no file, no fetch yet, an account with no weekly limit, or read while Claude Code was writing it


def harvest(ledger, home, root):
    """Bring the ledger up to date with every transcript of this project and with the meter, out of
    what Claude Code and Grok keep under that home directory; the number of new lines read."""
    db = connect(ledger)
    try:
        found = reading(home / ".claude.json")
        if found is not None:
            db.execute("insert or ignore into readings values (?, ?, ?, ?)", found)
        known = dict(db.execute("select path, offset from files").fetchall())
        taken = 0
        for directory in directories(home / ".claude" / "projects", root):
            for path, kind in transcripts(directory):
                try:
                    if path.stat().st_size != known.get(str(path)):
                        taken += read(db, path, kind)
                except FileNotFoundError:
                    pass  # removed by Claude Code's retention between the listing and the read
        for directory in grok_directories(home / ".grok" / "sessions", root):
            for path, kind, model in grok_sessions(directory):
                try:
                    if path.stat().st_size != known.get(str(path)):
                        taken += read(db, path, kind, lambda raw, model=model: grok_lines(raw, model))
                except FileNotFoundError:
                    pass  # removed between the listing and the read
        return taken
    finally:
        db.close()


def spent(ledger, since=0):
    """What the ledger holds, as the page draws it: each issue's tokens by kind ('' for none), and each
    hour's tokens by agent kind, as the hour's start, the kind and the counts. The hours that start
    before `since` are summed into their local days, each standing at its day's start, so the
    reply grows by a row a day and kind for what is older, not by twenty-four."""
    if not ledger.exists():
        return {}, []
    db = connect(ledger)
    try:
        issues = {row[0]: list(row[1:]) for row in db.execute(
            "select issue, sum(input), sum(cache_write), sum(cache_read), sum(output), sum(calls) from totals group by issue")}
        hours = [[row[0], row[1], list(row[2:])] for row in db.execute(
            "select case when hour < ? then cast(strftime('%s', hour, 'unixepoch', 'localtime', 'start of day', 'utc') as integer) else hour end as start, "
            "kind, sum(input), sum(cache_write), sum(cache_read), sum(output), sum(calls) from totals group by start, kind order by start, kind", (since,))]
        return issues, hours
    finally:
        db.close()


def newest(ledger):
    """The meter's newest reading as a row of `readings`, or None when the ledger holds none."""
    if not ledger.exists():
        return None
    db = connect(ledger)
    try:
        return db.execute("select fetched_ms, percent, resets_at, scoped from readings order by fetched_ms desc limit 1").fetchone()
    finally:
        db.close()


def main(arguments):
    parser = argparse.ArgumentParser(description="Harvest this project's transcripts into the token ledger.")
    root = Path(__file__).resolve().parents[2]
    parser.add_argument("--ledger", type=Path, default=root / "logs" / "token-ledger.sqlite")
    options = parser.parse_args(arguments)
    taken = harvest(options.ledger, Path.home(), root)
    issues, hours = spent(options.ledger)
    print(f"read {taken} new lines; {len(issues)} issues")
    totals = {}
    for _, kind, counts in hours:
        totals[kind] = [a + b for a, b in zip(totals.get(kind, [0] * 5), counts)]
    for kind, counts in sorted(totals.items()):
        print(kind, " ".join(f"{name} {count}" for name, count in zip(KINDS + ("calls",), counts)))
    return 0


class Tests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.home = Path(self.directory.name)
        self.root = Path("/work/atmo.src")
        self.projects = self.home / ".claude" / "projects"
        self.sessions = self.projects / "-work-atmo-src-main"
        self.sessions.mkdir(parents=True)
        self.ledger = self.home / "logs" / "ledger.sqlite"
        self.request = 0

    def call(self, usage=(1, 10, 100, 5), request=None, stamp="2026-11-10T12:00:00Z", model="claude-opus-5-5", content=()):
        if request is None:
            self.request += 1
            request = f"req_{self.request}"
        return {"type": "assistant", "requestId": request, "timestamp": stamp, "message": {
            "model": model, "content": list(content), "usage": dict(zip(USAGE, usage))}}

    def bash(self, command, use="toolu_1"):
        return self.call(content=[{"type": "tool_use", "id": use, "name": "Bash", "input": {"command": command}}])

    def result(self, use, output):
        return {"type": "user", "message": {"content": [{"type": "tool_result", "tool_use_id": use, "content": output}]}}

    def prompt(self, words):
        return {"type": "user", "message": {"role": "user", "content": words}}

    def write(self, path, lines, mode="w"):
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open(mode) as stream:
            for line in lines:
                stream.write(json.dumps(line, separators=(",", ":")) + "\n")

    def agent(self, kind, lines, name="a1"):
        path = self.sessions / "s1" / "subagents" / f"agent-{name}.jsonl"
        self.write(path, lines)
        path.with_suffix(".meta.json").write_text(json.dumps({"agentType": kind}))
        return path

    def issues(self):
        harvest(self.ledger, self.home, self.root)
        return {issue: counts for issue, counts in spent(self.ledger)[0].items()}

    def test_the_directories_are_this_roots_and_those_below_it_only(self):
        for name in ("-work-atmo-src", "-work-atmo-src--bare", "-work-atmo-srcx", "-other"):
            (self.projects / name).mkdir()
        self.assertEqual([path.name for path in directories(self.projects, self.root)], ["-work-atmo-src", "-work-atmo-src--bare", "-work-atmo-src-main"])

    def test_a_round_works_what_it_claims_from_before_its_first_claim(self):
        self.agent("round", [
            self.prompt("Run one round."),
            self.bash("bd ready --claim --exclude-type=epic --json", "toolu_r"),
            self.result("toolu_r", '[\n  {\n    "id": "atmo-1.2",\n    "title": "x", "parent": "atmo-1"}]'),
            self.call(),
            self.bash("cd main; bd update atmo-1.3 --claim"),
            self.call(),
        ])
        self.assertEqual(self.issues(), {"atmo-1.2": [3, 30, 300, 15, 3], "atmo-1.3": [1, 10, 100, 5, 1]})

    def test_a_round_pinned_to_an_issue_works_it_from_its_first_call(self):
        self.agent("round", [self.call(), self.prompt("Run one round. Issue atmo-1.7 is yours: a round of this loop left it unfinished."),
                             self.call(), self.bash('bd update atmo-1.8 --append-notes "Recovered at orient"'), self.call(),
                             self.bash("bd close atmo-1.7 --reason done"), self.call()])
        self.assertEqual(self.issues(), {"atmo-1.7": [5, 50, 500, 25, 5], "": [1, 10, 100, 5, 1]})

    def test_a_round_that_claims_nothing_works_the_first_issue_it_writes(self):
        self.agent("round", [self.call(), self.bash('bd update atmo-1 --append-notes "Skeptic input: tier 3"'), self.call(),
                             self.bash('bd update atmo-2 --append-notes "x"'), self.call()])
        self.assertEqual(self.issues(), {"atmo-1": [5, 50, 500, 25, 5]})
        self.agent("round", [self.call(), self.bash("bd close atmo-3 --reason done"), self.call()], "a2")
        self.assertEqual(self.issues()["atmo-3"], [2, 20, 200, 10, 2])

    def test_a_session_works_what_it_claims_until_it_closes_it(self):
        self.write(self.sessions / "s1.jsonl", [
            self.call(),
            self.bash('bd update atmo-1.2 -s in_progress --claim && echo "--claim"'),
            self.call(),
            self.bash("bd close atmo-1.2 --reason done"),
            self.call(),
        ])
        self.assertEqual(self.issues(), {"": [3, 30, 300, 15, 3], "atmo-1.2": [2, 20, 200, 10, 2]})

    def test_a_prover_and_a_skeptic_work_what_their_first_prompt_names(self):
        self.agent("prover", [self.prompt("Issue atmo-1.2.3, worktree /x/atmo-1.2.3. Your input is ..."), self.call(),
                              self.bash("bd update atmo-9 --claim")], "p")
        self.agent("skeptic", [self.prompt("Run the pass. Epic: atmo-1.2. Your input is the epic's last Skeptic input note."), self.call()], "s")
        self.agent("general-purpose", [self.prompt("Issue atmo-1.4, look"), self.call()], "g")
        self.assertEqual(self.issues(), {"atmo-1.2.3": [2, 20, 200, 10, 2], "atmo-1.2": [1, 10, 100, 5, 1], "": [1, 10, 100, 5, 1]})

    def test_a_command_line_agent_session_counts_as_that_agent(self):
        self.write(self.sessions / "r.jsonl", [{"type": "agent-setting", "agentSetting": "round", "sessionId": "r"},
                                               self.call(), self.bash("bd update atmo-1.2 --claim"), self.call()])
        self.write(self.sessions / "s.jsonl", [{"type": "agent-setting", "agentSetting": "skeptic", "sessionId": "s"},
                                               self.prompt("Review atmo-1.9. Your input is the review's last Skeptic input note."), self.call()])
        self.write(self.sessions / "i.jsonl", [self.call()])
        self.assertEqual(self.issues(), {"atmo-1.2": [3, 30, 300, 15, 3], "atmo-1.9": [1, 10, 100, 5, 1], "": [1, 10, 100, 5, 1]})
        self.assertEqual([kind for _, kind, _ in spent(self.ledger)[1]], ["round", "session", "skeptic"])

    def test_a_call_written_on_several_lines_counts_once_at_its_largest(self):
        self.write(self.sessions / "s1.jsonl", [self.call((1, 10, 100, 5), "req_a"), self.call((1, 10, 100, 70), "req_a")])
        self.assertEqual(self.issues(), {"": [1, 10, 100, 70, 1]})

    def test_a_line_still_being_written_is_read_once_it_is_whole(self):
        path = self.sessions / "s1.jsonl"
        self.write(path, [self.call()])
        whole = json.dumps(self.call(), separators=(",", ":")) + "\n"
        with path.open("a") as stream:
            stream.write(whole[:40])
        self.assertEqual(self.issues(), {"": [1, 10, 100, 5, 1]})
        with path.open("a") as stream:
            stream.write(whole[40:])
        self.assertEqual(self.issues(), {"": [2, 20, 200, 10, 2]})
        self.assertEqual(harvest(self.ledger, self.home, self.root), 0)

    def test_a_claim_answered_by_a_later_harvest_still_moves_the_round(self):
        path = self.agent("round", [self.call(), self.bash("bd ready --claim --json", "toolu_r")])
        self.assertEqual(self.issues(), {"": [2, 20, 200, 10, 2]})
        self.write(path, [self.result("toolu_r", '[{"id": "atmo-7"}]'), self.call()], "a")
        self.assertEqual(self.issues(), {"atmo-7": [3, 30, 300, 15, 3]})

    def test_the_ledger_keeps_what_a_removed_transcript_held(self):
        path = self.sessions / "s1.jsonl"
        self.write(path, [self.call()])
        self.issues()
        path.unlink()
        self.assertEqual(self.issues(), {"": [1, 10, 100, 5, 1]})

    def test_an_hour_is_the_hour_of_its_calls_by_agent_kind(self):
        self.write(self.sessions / "s1.jsonl", [self.call(stamp="2026-11-10T12:05:00Z"), self.call(stamp="2026-11-10T12:55:00.123Z"),
                                               self.call(stamp="2026-11-10T13:00:00Z")])
        self.agent("round", [self.call(stamp="2026-11-10T12:30:00Z")])
        harvest(self.ledger, self.home, self.root)
        noon = int(datetime(2026, 11, 10, 12, tzinfo=timezone.utc).timestamp())
        self.assertEqual(spent(self.ledger)[1], [
            [noon, "round", [1, 10, 100, 5, 1]], [noon, "session", [2, 20, 200, 10, 2]], [noon + 3600, "session", [1, 10, 100, 5, 1]]])

    def test_the_hours_before_a_time_are_summed_into_their_local_days(self):
        stamps = ["2026-11-09T03:10:00Z", "2026-11-09T04:10:00Z", "2026-11-10T20:00:00Z", "2026-11-11T12:00:00Z"]
        self.write(self.sessions / "s1.jsonl", [self.call(stamp=stamp) for stamp in stamps])
        harvest(self.ledger, self.home, self.root)
        hours = [int(datetime.fromisoformat(stamp[:13] + ":00:00+00:00").timestamp()) for stamp in stamps]
        midnight = lambda hour: int(datetime.fromtimestamp(hour).replace(hour=0, minute=0).timestamp())
        folded = {}
        for hour in hours[:3]:
            folded[midnight(hour)] = folded.get(midnight(hour), 0) + 1
        self.assertEqual(spent(self.ledger, hours[3])[1],
                         [[day, "session", [calls, 10 * calls, 100 * calls, 5 * calls, calls]] for day, calls in sorted(folded.items())]
                         + [[hours[3], "session", [1, 10, 100, 5, 1]]])

    def test_a_round_claim_moves_each_hours_calls_made_before_it(self):
        self.agent("round", [self.call(stamp="2026-11-10T12:59:00Z"), self.call(stamp="2026-11-10T13:01:00Z"),
                             self.bash("bd update atmo-1.2 --claim")])
        self.assertEqual(self.issues(), {"atmo-1.2": [3, 30, 300, 15, 3]})
        self.assertEqual([counts for _, _, counts in spent(self.ledger)[1]], [[2, 20, 200, 10, 2], [1, 10, 100, 5, 1]])

    def test_a_ledger_not_yet_harvested_holds_nothing(self):
        self.assertEqual(spent(self.ledger), ({}, []))

    def meter(self, fetched, percent, fable, week="2026-11-15T04:59:59+00:00"):
        """The account file as Claude Code leaves it after fetching the meter, with what else it holds left out."""
        (self.home / ".claude.json").write_text(json.dumps({"numStartups": 7, "cachedUsageUtilization": {"fetchedAtMs": fetched, "utilization": {
            "five_hour": None,
            "seven_day": {"utilization": percent, "resets_at": week},
            "limits": [
                {"kind": "weekly_all", "group": "weekly", "percent": percent, "resets_at": week, "scope": None},
                {"kind": "weekly_scoped", "group": "weekly", "percent": fable, "resets_at": "2026-11-15T05:00:00+00:00",
                 "scope": {"model": {"id": None, "display_name": "Fable"}, "surface": None}},
                {"kind": "weekly_scoped", "group": "weekly", "percent": 3, "resets_at": "2026-11-15T05:00:00+00:00",
                 "scope": {"model": None, "surface": "desk"}},
            ],
            "weekly_scoped_shares": [{"limit_index": 1, "used_percent_of_weekly": 16, "allowance_percent_of_weekly": 50}],
        }}}))

    def kept(self):
        harvest(self.ledger, self.home, self.root)
        db = connect(self.ledger)
        self.addCleanup(db.close)
        return db.execute("select fetched_ms, percent, resets_at, scoped from readings order by fetched_ms").fetchall()

    def test_a_harvest_keeps_the_reading_the_meter_last_gave(self):
        self.meter(1794520654306, 97, 31)
        [(fetched, percent, resets_at, scoped)] = self.kept()
        self.assertEqual((fetched, percent, resets_at), (1794520654306, 97, "2026-11-15T04:59:59+00:00"))
        self.assertEqual(json.loads(scoped), {
            "Fable": {"percent": 31, "share": 50, "resets_at": "2026-11-15T05:00:00+00:00"},
            # A scoped limit that names no model goes by its scope as it came, and one the shares leave out has none.
            '{"model": null, "surface": "desk"}': {"percent": 3, "share": None, "resets_at": "2026-11-15T05:00:00+00:00"}})
        # The Fable meter is read out of the row as SQLite reads JSON.
        db = connect(self.ledger)
        self.addCleanup(db.close)
        self.assertEqual(db.execute("select json_extract(scoped, '$.Fable.percent'), json_extract(scoped, '$.Fable.share') from readings").fetchall(), [(31, 50)])

    def test_a_reading_is_kept_once_and_a_reset_shows_as_a_fall(self):
        self.meter(1000, 60, 20)
        self.kept()
        self.assertEqual([row[:2] for row in self.kept()], [(1000, 60)])
        # The human spends a reset: the next fetch is lower and the week ends when it did.
        self.meter(2000, 4, 1)
        self.assertEqual([row[:3] for row in self.kept()], [(1000, 60, "2026-11-15T04:59:59+00:00"), (2000, 4, "2026-11-15T04:59:59+00:00")])

    def test_the_newest_reading_is_the_one_fetched_last(self):
        self.assertIsNone(newest(self.ledger))
        self.meter(2000, 4, 1)
        self.kept()
        self.meter(1000, 60, 20)  # an older fetch harvested later is not the newest
        self.kept()
        self.assertEqual(newest(self.ledger)[:2], (2000, 4))

    def grok_session(self, cwd, name, lines, model="grok-4.7", created="2026-11-13T12:00:00Z"):
        """One Grok session directory under the percent-encoded cwd, as ~/.grok/sessions keeps it."""
        session = self.home / ".grok" / "sessions" / urllib.parse.quote(cwd, safe="") / name
        session.mkdir(parents=True)
        (session / "summary.json").write_text(json.dumps({"current_model_id": model, "created_at": created}))
        self.write(session / "updates.jsonl", lines)
        return session

    def test_a_grok_session_counts_under_the_issue_its_prompt_names(self):
        usage = {"inputTokens": 1000, "cachedReadTokens": 400, "cacheCreationTokens": 0, "outputTokens": 10,
                 "reasoningTokens": 4, "totalTokens": 1010, "costUsdTicks": 50_000_000_000, "modelUsage": {"grok-4.7": {}}}
        turn = {"timestamp": "2026-11-13T12:10:00.152Z", "method": "session/update", "params": {"update": {
            "sessionUpdate": "turn_completed", "prompt_id": "prompt-1", "usage": usage}}}
        self.grok_session("/work/atmo.src", "sess-round", [
            {"timestamp": "2026-11-13T12:00:00Z", "method": "session/update", "params": {"update": {
                "sessionUpdate": "user_message_chunk", "content": {"type": "text", "text":
                    "You run one round.\n\nRun one round. Issue atmo-1.6 is yours (claimed for route tool; take no other issue)."}}}},
            turn])
        # A resumed session repeats the turn. The prompt id is the request id, so the turn counts once.
        self.grok_session("/work/atmo.src", "sess-again", [turn], created="2026-11-13T13:00:00Z")
        self.grok_session("/work/atmo.src/main", "sess-prover", [
            {"timestamp": "2026-11-13T12:20:00Z", "method": "session/update", "params": {"update": {
                "sessionUpdate": "user_message_chunk", "content": {"type": "text", "text":
                    "Prove it.\n\nIssue atmo-2.2, worktree /work/atmo-2.2. Your input is the issue's last Prover input note."}}}},
            {"timestamp": "2026-11-13T12:21:00Z", "method": "session/update", "params": {"update": {
                "sessionUpdate": "tool_call", "toolCallId": "c1", "rawInput": {"command": "bd update atmo-9 --claim"}}}},
            {"timestamp": "2026-11-13T12:30:00Z", "method": "session/update", "params": {"update": {
                "sessionUpdate": "turn_completed", "prompt_id": "prompt-2", "usage": {
                    "inputTokens": 50, "cachedReadTokens": 0, "cacheCreationTokens": 0, "outputTokens": 5,
                    "totalTokens": 55, "modelUsage": {"grok-4.7": {}}}}}}])
        self.grok_session("/other", "sess-out", [
            {"timestamp": "2026-11-13T12:00:00Z", "method": "session/update", "params": {"update": {
                "sessionUpdate": "turn_completed", "prompt_id": "prompt-out", "usage": {
                    "inputTokens": 9_000_000, "outputTokens": 1, "totalTokens": 9_000_001, "modelUsage": {"grok-4.7": {}}}}}}])
        self.assertEqual(self.issues(), {"atmo-1.6": [600, 0, 400, 10, 1], "atmo-2.2": [50, 0, 0, 5, 1]})
        self.assertEqual([kind for _, kind, _ in spent(self.ledger)[1]], ["prover", "round"])

    def test_an_account_file_with_no_reading_adds_none_and_fails_nothing(self):
        self.write(self.sessions / "s1.jsonl", [self.call()])
        self.assertEqual(self.kept(), [])  # no account file
        account = self.home / ".claude.json"
        account.write_text(json.dumps({"numStartups": 7}))
        self.assertEqual(self.kept(), [])  # Claude Code has not fetched the meter
        account.write_text(json.dumps({"cachedUsageUtilization": {"fetchedAtMs": 1000, "utilization": {"seven_day": None}}}))
        self.assertEqual(self.kept(), [])  # an account with no weekly limit
        account.write_text('{"cachedUsageUtilization": {"fetchedAtMs": 10')
        self.assertEqual(self.kept(), [])  # read while it was being written
        self.assertEqual(spent(self.ledger)[0], {"": [1, 10, 100, 5, 1]})


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        sys.argv[1:] = []
        unittest.main()
    sys.exit(main(sys.argv[1:]))
