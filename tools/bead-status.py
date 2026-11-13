#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The state of the Beads tree as a page for a browser: how many issues are not closed over time,
what each session holds and the stage its round is at, the questions waiting on the human, the
graph of what waits on what, the ready leaves, each top epic's progress and what closed last. An
issue of the graph opens its details: its texts and the issues around it.

The server reads Beads only while a page asks. A request for /data runs bd when what the server
holds is older than AGE seconds, and the page (tools/bead-status.html) asks only while its tab is
visible. The history is each issue's creation and close time out of one `bd list --all`, so nothing
is recorded between runs; an issue reopened counts as open from its creation. A session's stage and
clock are the ones its status line wrote (tools/round-status.py), read from the same files.

The tokens are the token ledger's (tools/token-ledger.py), which the server harvests every
HARVEST seconds in a thread of its own, so a page never waits on a harvest. An issue's tokens are
its own and those of every issue below it; the root epic's are every call's, since calls that name
no issue the tree has are its own. The page has each of the last HOURLY seconds' hours by who spent
its tokens, and each day before them.

The page has a gauge for each plan meter the loop draws on, as percent used with the time it
resets. Claude's are the token ledger's newest reading: every model's week and each scoped model's,
such as Fable's. Gemini's, which agy's carbon models spend, are what `agy -p /usage` prints, asked
for every USAGE seconds in a thread of its own; agy's group of Claude and GPT models is left out,
since the loop reaches Claude through Claude Code. A failed ask keeps the gauges of the last one.

The server follows the tree. The page is read from disk at each request, and the server's own code
is what the process loaded, so a change landing under a running server would put a new page over
old data. Every RENEW seconds the server looks at its script and the two it loads, and once a
change to them has settled it executes itself again, so the page and its data are of one commit.

Beads is private, so the server listens on this machine alone unless --bind says otherwise.

usage: tools/bead-status.py [--bind ADDRESS] [--port PORT]   (serve the page)
       tools/bead-status.py --test                            (this script's own tests)
"""
import argparse
import contextlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
import threading
import time
import unittest
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

sys.dont_write_bytecode = True  # round-status.py is imported from the tree: leave no __pycache__ in it

AGE = 5
PORT = 8377
PAGE = Path(__file__).with_suffix(".html")
CLOSED_SHOWN = 10
TEXT_SHOWN = 240
HARVEST = 60
RENEW = 2
# How far back the page has the tokens by the hour. It draws at most 30 periods over any stretch of
# time, so whatever it draws from further back than 31 days is in periods of a day or more.
HOURLY = 31 * 86400
LEDGER = Path("logs") / "token-ledger.sqlite"
USAGE = 300
AGY_GROUP = "Gemini Models"
WINDOWS = {"weekly": "week", "5h": "five hours"}


def tool(name):
    """A script beside this one as a module."""
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), Path(__file__).with_name(f"{name}.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def round_status():
    """tools/round-status.py as a module: it says where the status lines keep their clocks."""
    return tool("round-status")


def token_ledger():
    return tool("token-ledger")


# The code a running server holds: this script and the two it loads. The page is not among them,
# since each request reads it.
WATCHED = (Path(__file__).resolve(), Path(__file__).resolve().with_name("round-status.py"), Path(__file__).resolve().with_name("token-ledger.py"))


def stamp(path):
    """What says a file changed: its time of change and its size, or None while it is not there."""
    try:
        found = path.stat()
    except FileNotFoundError:
        return None
    return found.st_mtime_ns, found.st_size


def stamps(paths):
    return [stamp(path) for path in paths]


def renewing(paths, renew, pause=RENEW):
    """Call renew once the files differ from what they were at the start. A checkout takes a file
    away and writes it again, so a change counts only when every file is there and two looks, pause
    seconds apart, agree."""
    started = seen = stamps(paths)
    while True:
        time.sleep(pause)
        now = stamps(paths)
        if now != started and now == seen and None not in now:
            return renew()
        seen = now


def owned(issues, own):
    """Each issue's own tokens and calls, out of the ledger's per issue: a call naming no issue of the
    tree is the root epic's, the one made first; with no root epic it is in no issue's."""
    names = {issue["id"] for issue in issues}
    roots = sorted((issue for issue in issues if not issue.get("parent") and issue["issue_type"] == "epic"), key=lambda issue: issue["created_at"])
    found = {}
    for name, counts in own.items():
        name = name if name in names else roots[0]["id"] if roots else None
        if name:
            found[name] = [a + b for a, b in zip(found.get(name, [0] * len(counts)), counts)]
    return found


def tokens(issues, own):
    """Each issue's tokens and calls: its own with those of every issue below it."""
    by_id = {issue["id"]: issue for issue in issues}
    found = {}
    for name, counts in owned(issues, own).items():
        while name:
            found[name] = [a + b for a, b in zip(found.get(name, [0] * len(counts)), counts)]
            name = by_id[name].get("parent")
    return found


def seconds(stamp):
    return int(datetime.fromisoformat(stamp).timestamp())


def events(issues):
    """Every creation (+1) and every close (-1) as [time, change, 1 for an epic], oldest first."""
    found = []
    for issue in issues:
        epic = int(issue["issue_type"] == "epic")
        found.append([seconds(issue["created_at"]), 1, epic])
        if issue["status"] == "closed":
            found.append([seconds(issue["closed_at"]), -1, epic])
    return sorted(found)


def brief(issue, by_id):
    """What a row of the page says of an issue, with the epics above it below the root, the top one first."""
    above = []
    parent = issue.get("parent")
    while parent:
        above.append(by_id[parent])
        parent = by_id[parent].get("parent")
    return {
        "id": issue["id"],
        "title": issue["title"],
        "priority": issue["priority"],
        "type": issue["issue_type"],
        "trail": [epic["title"] for epic in reversed(above[:-1])],
    }


def order(name):
    """What sorts issue ids by their numbers, a.2 ahead of a.10."""
    return [(int(part), "") if part.isdigit() else (0, part) for part in name.split(".")]


def blockers(issue):
    """The ids a `blocks` dependency of the issue names, closed or not, in their order."""
    return sorted({link["depends_on_id"] for link in issue.get("dependencies", []) if link["type"] == "blocks"}, key=order)


def loops(issues):
    """Each set of issues not closed that wait on one another, as its ids in order, the sets in
    order of their first id. An issue waits on its blockers not closed and on its parent: a loop
    holds a `blocks` dependency, so the parent on it waits, and bd counts its child as blocked by it.
    `bd dep cycles` reads `blocks` edges alone and does not see a loop through a parent. Tarjan's
    strongly connected components, kept on a stack of its own so a deep tree does not recurse."""
    live = {issue["id"]: issue for issue in issues if issue["status"] != "closed"}
    edges = {name: [other for other in blockers(issue) + [issue.get("parent")] if other in live] for name, issue in live.items()}
    index, low, stack, held, found = {}, {}, [], set(), []
    for start in live:
        if start in index:
            continue
        index[start] = low[start] = len(index)
        stack.append(start)
        held.add(start)
        walk = [(start, iter(edges[start]))]
        while walk:
            name, rest = walk[-1]
            other = next(rest, None)
            if other is None:
                walk.pop()
                if walk:
                    low[walk[-1][0]] = min(low[walk[-1][0]], low[name])
                if low[name] == index[name]:
                    group = []
                    while not group or group[-1] != name:
                        group.append(stack.pop())
                        held.discard(group[-1])
                    if len(group) > 1 or name in edges[name]:
                        found.append(sorted(group, key=order))
            elif other not in index:
                index[other] = low[other] = len(index)
                stack.append(other)
                held.add(other)
                walk.append((other, iter(edges[other])))
            elif other in held:
                low[name] = min(low[name], index[other])
    return sorted(found, key=lambda group: order(group[0]))


def graph(issues, ready):
    """Every issue not closed as a node under what it waits on: its blockers, the issues not closed
    that a `blocks` dependency of it names, and its parent when the parent waits, since bd counts
    the child of a blocked epic as blocked by it. The rank is the longest chain of waits above the
    issue, so rank 0 waits on nothing. A wait between two issues of one loop (loops()) is left out,
    so every rank is finite; the page names the loops beside the graph. Ready is bd's word, given
    as the issues `bd ready` lists."""
    live = {issue["id"]: issue for issue in issues if issue["status"] != "closed"}
    ready = {issue["id"] for issue in ready}
    loop = {name: number for number, group in enumerate(loops(issues)) for name in group}
    apart = lambda name, other: other in live and (name not in loop or loop.get(other) != loop[name])
    nodes = {}

    def node(name):
        if name not in nodes:
            issue = live[name]
            waits = [other for other in blockers(issue) if apart(name, other)]
            parent = issue.get("parent")
            under = parent if apart(name, parent) and node(parent)["rank"] else None
            above = waits + [under] if under else waits
            nodes[name] = {
                "id": name,
                "title": issue["title"],
                "type": issue["issue_type"],
                "status": issue["status"],
                "priority": issue["priority"],
                "ready": name in ready,
                "blockers": waits,
                "under": under,
                "rank": 1 + max(node(other)["rank"] for other in above) if above else 0,
            }
        return nodes[name]

    return [node(name) for name in live]


def detail(issues, name, own={}):
    """What the page shows of one issue, closed or not: its texts whole and the issues around it. None when the tree has no such issue."""
    by_id = {issue["id"]: issue for issue in issues}
    if name not in by_id:
        return None
    issue = by_id[name]
    near = lambda found: [{"id": other["id"], "title": other["title"], "type": other["issue_type"], "status": other["status"]} for other in sorted(found, key=lambda other: order(other["id"]))]
    return {
        **brief(issue, by_id),
        "status": issue["status"],
        "assignee": issue.get("assignee"),
        "labels": issue.get("labels", []),
        "created": seconds(issue["created_at"]),
        "closed": seconds(issue["closed_at"]) if issue["status"] == "closed" else None,
        "parent": near([by_id[issue["parent"]]])[0] if "parent" in issue else None,
        "children": near(other for other in issues if other.get("parent") == name),
        "blockers": near(by_id[other] for other in blockers(issue)),
        "dependents": near(other for other in issues if name in blockers(other)),
        "text": {key: issue.get(key, "") for key in ("description", "acceptance_criteria", "design", "notes", "close_reason")},
        "tokens": tokens(issues, own).get(name),
        "own_tokens": owned(issues, own).get(name),
    }


def clocks(state):
    """What each session's status line last wrote: the issue it holds, the stage and when the stage began."""
    found = {}
    for file in state.glob("claude-*.json"):
        seen = json.loads(file.read_text())
        issue, _, stage = seen["key"].partition(" ")
        found[file.stem] = {"issue": issue, "stage": stage, "since": seen["since"]}
    return found


def alive(actor):
    """Whether the session claude-<pid> or the loop loop-<pid> still runs, as a round tells it; None for an assignee that is neither."""
    kind, _, pid = (actor or "").partition("-")
    if kind not in ("claude", "loop") or not pid.isdigit():
        return None
    try:
        if kind == "claude":
            return Path(f"/proc/{pid}/comm").read_text().strip() == "claude"
        return any(arg.endswith("tools/loop.py") for arg in Path(f"/proc/{pid}/cmdline").read_text().split("\0"))
    except FileNotFoundError:
        return False


def gate_line(log):
    """The last line the landing or the gate wrote of a step, or None when the log has none."""
    if not log.exists():
        return None
    with open(log, "rb") as file:
        file.seek(max(log.stat().st_size - 8192, 0))
        lines = file.read().decode(errors="replace").splitlines()
    steps = [line for line in lines if line.startswith(("gate ", "land: "))]
    return steps[-1][:TEXT_SHOWN] if steps else None


def flights(issues, by_id, seen, running, root, spent={}):
    """The issues in progress, the one held longest first, each with its holder and the stage its holder's status line names for it."""
    rows = []
    for issue in sorted((issue for issue in issues if issue["status"] == "in_progress"), key=lambda issue: issue["started_at"]):
        actor = issue.get("assignee")
        clock = seen.get(actor, {})
        mine = clock.get("issue") == issue["id"]
        rows.append({
            **brief(issue, by_id),
            "actor": actor,
            "alive": running(actor),
            "stage": clock["stage"] if mine else None,
            "since": clock["since"] if mine else None,
            "started": seconds(issue["started_at"]),
            "gate": gate_line(root / "logs" / f"{issue['id']}-gate.log"),
            "tokens": spent.get(issue["id"]),
        })
    return rows


def progress(issues, spent={}):
    """Each epic directly under a root that has issues below it: how many, and how many of them are closed."""
    children = {}
    for issue in issues:
        children.setdefault(issue.get("parent"), []).append(issue)

    def below(issue):
        found = []
        for child in children.get(issue["id"], []):
            found += [child] + below(child)
        return found

    rows = []
    for root in children[None]:
        for epic in children.get(root["id"], []):
            under = below(epic)
            if under:
                rows.append({
                    "id": epic["id"],
                    "title": epic["title"],
                    "status": epic["status"],
                    "total": len(under),
                    "closed": sum(issue["status"] == "closed" for issue in under),
                    "flying": sum(issue["status"] == "in_progress" for issue in under),
                    "tokens": spent.get(epic["id"]),
                })
    return sorted(rows, key=lambda row: order(row["id"]))


def claude_meters(reading):
    """The gauges of Claude's plan out of a row of the ledger's `readings`: every model's week, then
    each scoped limit that names a model; none without a reading."""
    if reading is None:
        return []
    fetched, percent, resets_at, scoped = reading
    gauge = lambda name, percent, resets_at: {"name": name, "window": "week", "percent": percent, "resets": seconds(resets_at), "read": fetched // 1000}
    return [gauge("Claude", percent, resets_at)] + [
        gauge(name, limit["percent"], limit["resets_at"]) for name, limit in sorted(json.loads(scoped).items()) if not name.startswith("{")]


def agy_meters(reply, read):
    """The gauges of agy's Gemini group out of what `agy -p /usage --output-format json` printed, read
    at that time: each window's bucket as percent used."""
    return [
        {"name": "Gemini", "window": WINDOWS.get(bucket["window"], bucket["window"]), "percent": round(100 * (1 - bucket["remaining_fraction"]), 1),
         "resets": seconds(bucket["reset_time"]), "read": int(read)}
        for group in json.loads(reply)["command"]["data"]["groups"] if group["name"] == AGY_GROUP for bucket in group["buckets"]]


def summary(issues, ready, seen, running, root, now, own={}, hours=(), meters=()):
    """What the page draws, from every issue, the ready ones in bd's order, the sessions' clocks, the
    token ledger (each issue's own tokens and each hour's by agent kind) and the plan meters."""
    by_id = {issue["id"]: issue for issue in issues}
    spent = tokens(issues, own)
    roots = [issue["id"] for issue in issues if not issue.get("parent") and issue["id"] in spent]
    count = lambda status: sum(issue["status"] == status for issue in issues)
    held = {issue.get("assignee") for issue in issues if issue["status"] == "in_progress"}
    closed = sorted((issue for issue in issues if issue["status"] == "closed"), key=lambda issue: issue["closed_at"])
    questions = sorted((issue for issue in issues if issue["status"] == "blocked"), key=lambda issue: issue["created_at"])
    return {
        "now": now,
        "counts": {
            "total": len(issues),
            "open": len(issues) - len(closed),
            "deferred": count("deferred"),
            "ready_epics": sum(issue["issue_type"] == "epic" for issue in ready),
        },
        "events": events(issues),
        "flights": flights(issues, by_id, seen, running, root, spent),
        "idle": sorted(actor for actor in seen if running(actor) and actor not in held),
        "questions": [{**brief(issue, by_id), "created": seconds(issue["created_at"])} for issue in questions],
        "ready": [brief(issue, by_id) for issue in ready if issue["issue_type"] != "epic"],
        "graph": graph(issues, ready),
        "loops": loops(issues),
        "meters": list(meters),
        "epics": progress(issues, spent),
        "tokens": {"roots": [{**brief(by_id[name], by_id), "tokens": spent[name]} for name in sorted(roots, key=order)], "hours": list(hours)},
        "closed": [
            {
                **brief(issue, by_id),
                "at": seconds(issue["closed_at"]),
                "actor": issue.get("assignee"),
                "reason": issue["close_reason"][:TEXT_SHOWN],
                "tokens": spent.get(issue["id"]),
            }
            for issue in reversed(closed[-CLOSED_SHOWN:])
        ],
    }


def read(root, now, agy=()):
    """Every issue of the tree at this project root, each issue's own tokens, and their summary as it
    is now, with agy's gauges as last asked for."""
    bd = lambda *arguments: json.loads(subprocess.run(["bd", *arguments, "--json", "--limit", "0"], cwd=root, check=True, capture_output=True, text=True).stdout)
    issues = bd("list", "--all")
    ledger = token_ledger()
    own, hours = ledger.spent(root / LEDGER, now - HOURLY)
    meters = claude_meters(ledger.newest(root / LEDGER)) + list(agy)
    return issues, own, summary(issues, bd("ready"), clocks(round_status().state_dir(root)), alive, root, now, own, hours, meters)


class Beads:
    """The tree as the bodies of replies, read again once it is older than AGE however many pages ask."""

    def __init__(self, root):
        self.root = root
        self.lock = threading.Lock()
        self.read_at = 0
        self.issues = []
        self.own = {}
        self.held = b""
        self.agy = []

    def fresh(self):
        """Read the tree again when what is held is too old; the caller holds the lock."""
        now = time.time()
        if now - self.read_at > AGE:
            self.issues, self.own, found = read(self.root, now, self.agy)
            self.held = json.dumps(found).encode()
            self.read_at = now

    def body(self):
        with self.lock:
            self.fresh()
            return self.held

    def issue(self, name):
        """The details of that issue as a body, or None when the tree has no such issue."""
        with self.lock:
            self.fresh()
            found = detail(self.issues, name, self.own)
            return found and json.dumps(found).encode()


class Page(BaseHTTPRequestHandler):
    ISSUE = "/issue/"

    def do_GET(self):
        try:
            if self.path == "/":
                self.reply(200, "text/html; charset=utf-8", PAGE.read_bytes())
            elif self.path == "/data":
                self.reply(200, "application/json", self.server.beads.body())
            elif self.path.startswith(self.ISSUE):
                # The id is the browser's word: one the tree does not have is refused, and none reaches bd.
                body = self.server.beads.issue(urllib.parse.unquote(self.path[len(self.ISSUE):]))
                if body:
                    self.reply(200, "application/json", body)
                else:
                    self.reply(404, "text/plain; charset=utf-8", b"no such issue\n")
            else:
                self.reply(404, "text/plain; charset=utf-8", b"not found\n")
        except subprocess.CalledProcessError as failure:
            # bd is another process, and it gives up when the tree's lock stays held.
            self.reply(503, "text/plain; charset=utf-8", f"bd {failure.cmd[1]} exited {failure.returncode}: {failure.stderr.strip()}".encode())

    def reply(self, status, kind, body):
        self.send_response(status)
        self.send_header("Content-Type", kind)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, format, *arguments):
        pass


def server(root, bind, port):
    made = ThreadingHTTPServer((bind, port), Page)
    made.daemon_threads = True
    made.beads = Beads(root)
    return made


def harvesting(root, home):
    """Bring the token ledger up to date every HARVEST seconds, for as long as the server runs."""
    ledger = token_ledger()
    while True:
        try:
            ledger.harvest(root / LEDGER, home, root)
        except Exception as failure:  # a transcript of a shape the ledger does not know stops one harvest, not the page
            print(f"token ledger: {failure!r}", file=sys.stderr, flush=True)
        time.sleep(HARVEST)


def ask_agy(beads, root, agy="agy"):
    """Ask agy for its quota once, and give the server its gauges."""
    try:
        done = subprocess.run([agy, "-p", "/usage", "--output-format", "json"], cwd=root, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=120, check=True)
        beads.agy = agy_meters(done.stdout, time.time())
    except (OSError, subprocess.SubprocessError, ValueError, KeyError, TypeError) as failure:
        # agy is another program: one it lacks, or a reply of a shape this does not know, keeps the last gauges.
        print(f"agy usage: {failure!r}", file=sys.stderr, flush=True)


def asking_agy(beads, root):
    """Ask agy for its quota every USAGE seconds, for as long as the server runs."""
    while True:
        ask_agy(beads, root)
        time.sleep(USAGE)


def main(arguments):
    parser = argparse.ArgumentParser(description="Serve the state of the Beads tree as a page.")
    parser.add_argument("--bind", default="127.0.0.1", help="the address to listen on (default: this machine alone)")
    parser.add_argument("--port", type=int, default=PORT)
    options = parser.parse_args(arguments)
    root = Path(__file__).resolve().parents[2]
    serving = server(root, options.bind, options.port)
    threading.Thread(target=harvesting, args=(root, Path.home()), daemon=True).start()
    threading.Thread(target=asking_agy, args=(serving.beads, root), daemon=True).start()
    # The same command again, in this process: the listening socket closes with the old image.
    threading.Thread(target=renewing, args=(WATCHED, lambda: os.execv(sys.executable, [sys.executable, *sys.argv])), daemon=True).start()
    print(f"bead status: http://{options.bind}:{serving.server_address[1]}/", flush=True)
    try:
        serving.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


class Tests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        (self.root / "logs").mkdir()

    def issue(self, name, status="open", kind="task", created="2026-11-10T10:00:00Z", needs=(), **fields):
        parent = name.rpartition(".")[0]
        issue = {"id": name, "title": f"Title of {name}", "status": status, "priority": 1, "issue_type": kind, "created_at": created, **fields}
        # As bd lists them: the issues a `blocks` dependency names, then the parent, and no list at all for a root.
        links = [{"depends_on_id": other, "type": "blocks"} for other in needs]
        if parent:
            issue["parent"] = parent
            links.append({"depends_on_id": parent, "type": "parent-child"})
        if links:
            issue["dependencies"] = links
        if status == "closed":
            issue.setdefault("closed_at", "2026-11-10T11:00:00Z")
            issue.setdefault("close_reason", "done")
        if status == "in_progress":
            issue.setdefault("started_at", "2026-11-10T10:30:00Z")
        return issue

    def tree(self):
        return [
            self.issue("a", kind="epic", created="2026-11-10T09:00:00Z"),
            self.issue("a.1", kind="epic"),
            self.issue("a.1.1", "closed"),
            self.issue("a.1.2", "in_progress", assignee="claude-11"),
            self.issue("a.1.3", "closed", closed_at="2026-11-10T12:00:00Z", assignee="claude-12", close_reason="x" * 500),
            self.issue("a.2", kind="epic"),
            self.issue("a.2.1", "blocked"),
            self.issue("a.2.2", "deferred"),
            self.issue("a.10", kind="epic"),
            self.issue("a.10.1"),
            self.issue("a.3", kind="epic"),
            self.issue("a.4", "blocked", created="2026-11-10T09:30:00Z"),
        ]

    def test_a_time_is_read_in_utc(self):
        self.assertEqual(seconds("1970-01-02T00:00:01Z"), 86401)

    def test_an_issue_is_an_event_at_its_creation_and_another_at_its_close(self):
        issues = [
            self.issue("a", kind="epic", created="1970-01-01T00:00:10Z"),
            self.issue("a.1", "closed", created="1970-01-01T00:00:20Z", closed_at="1970-01-01T00:00:40Z"),
            # A reopened issue keeps the time of a close that no longer holds.
            self.issue("a.2", created="1970-01-01T00:00:30Z", closed_at="1970-01-01T00:00:35Z"),
        ]
        self.assertEqual(events(issues), [[10, 1, 1], [20, 1, 0], [30, 1, 0], [40, -1, 0]])

    def test_a_row_names_the_epics_above_its_issue_below_the_root(self):
        by_id = {issue["id"]: issue for issue in self.tree()}
        self.assertEqual(brief(by_id["a.1.2"], by_id), {"id": "a.1.2", "title": "Title of a.1.2", "priority": 1, "type": "task", "trail": ["Title of a.1"]})
        self.assertEqual(brief(by_id["a.1"], by_id)["trail"], [])
        self.assertEqual(brief(by_id["a"], by_id)["trail"], [])

    def test_a_clock_is_the_issue_and_the_stage_a_status_line_wrote(self):
        state = self.root / "state"
        self.assertEqual(clocks(state), {})
        state.mkdir()
        (state / "claude-11.json").write_text(json.dumps({"key": "a.1.2 gate", "since": 100.5}))
        (state / "claude-12.json").write_text(json.dumps({"key": "", "since": 50}))
        # The list the status lines share and a clock one of them is still writing are not clocks.
        (state / "in-progress.json").write_text("[]")
        (state / "claude-13.json.4242").write_text("{")
        self.assertEqual(clocks(state), {
            "claude-11": {"issue": "a.1.2", "stage": "gate", "since": 100.5},
            "claude-12": {"issue": "", "stage": "", "since": 50},
        })

    def test_a_session_is_alive_while_a_process_named_claude_has_its_pid(self):
        self.assertIsNone(alive(None))
        self.assertIsNone(alive("Colin LeMahieu"))
        self.assertIsNone(alive("claude-code"))
        # This process is not named claude, and no process has a pid over the kernel's limit.
        self.assertFalse(alive(f"claude-{os.getpid()}"))
        self.assertFalse(alive("claude-4194305"))

    def test_a_loop_is_alive_while_a_process_with_its_pid_runs_tools_loop_py(self):
        self.assertIsNone(alive("loop-x"))
        self.assertFalse(alive(f"loop-{os.getpid()}"))
        self.assertFalse(alive("loop-4194305"))
        loop = subprocess.Popen([sys.executable, "-c", "import time; print(flush=True); time.sleep(60)", "/somewhere/tools/loop.py"], stdout=subprocess.PIPE)
        try:
            loop.stdout.readline()  # the child runs its command, so its cmdline is no longer the test's
            self.assertTrue(alive(f"loop-{loop.pid}"))
        finally:
            loop.kill()
            loop.wait()
            loop.stdout.close()
        self.assertFalse(alive(f"loop-{loop.pid}"))

    def test_the_last_step_of_a_landing_log_is_its_gate_line(self):
        log = self.root / "logs" / "a.1.2-gate.log"
        self.assertIsNone(gate_line(log))
        log.write_bytes(b"   Compiling \xff\xfe scroll v0.11.0\n")
        self.assertIsNone(gate_line(log))
        log.write_text("land: gating abc on main at def\ngate build: ok in 38.0 s: 19 workspace members\n   Compiling semver\n")
        self.assertEqual(gate_line(log), "gate build: ok in 38.0 s: 19 workspace members")
        log.write_text("gate total: 287.5 s\nland: abc landed as gated\nexit 0\n")
        self.assertEqual(gate_line(log), "land: abc landed as gated")
        log.write_text("gate boot: FAIL in 120.1 s: " + "x" * 500 + "\n")
        self.assertEqual(len(gate_line(log)), TEXT_SHOWN)

    def test_a_flight_takes_its_stage_from_its_holders_clock_for_that_issue_only(self):
        issues = self.tree() + [self.issue("a.3.1", "in_progress", assignee="claude-12", started_at="2026-11-10T10:10:00Z"), self.issue("a.3.2", "in_progress")]
        by_id = {issue["id"]: issue for issue in issues}
        seen = {"claude-11": {"issue": "a.1.2", "stage": "gate", "since": 100.5}, "claude-12": {"issue": "a.9", "stage": "work", "since": 50}}
        (self.root / "logs" / "a.1.2-gate.log").write_text("gate verify: ok in 58.7 s: 0 errors, allowance 0\n")
        rows = flights(issues, by_id, seen, lambda actor: actor == "claude-11", self.root)
        self.assertEqual([row["id"] for row in rows], ["a.3.1", "a.1.2", "a.3.2"])
        self.assertEqual(rows[1], {
            "id": "a.1.2", "title": "Title of a.1.2", "priority": 1, "type": "task", "trail": ["Title of a.1"],
            "actor": "claude-11", "alive": True, "stage": "gate", "since": 100.5, "started": seconds("2026-11-10T10:30:00Z"),
            "gate": "gate verify: ok in 58.7 s: 0 errors, allowance 0", "tokens": None,
        })
        # A clock that names another issue says nothing of this one.
        self.assertEqual((rows[0]["actor"], rows[0]["alive"], rows[0]["stage"], rows[0]["since"], rows[0]["gate"]), ("claude-12", False, None, None, None))
        self.assertEqual((rows[2]["actor"], rows[2]["stage"]), (None, None))

    def test_an_epic_under_the_root_counts_every_issue_below_it(self):
        issues = self.tree() + [self.issue("a.1.2.1", "closed"), self.issue("b", kind="epic"), self.issue("b.1", kind="epic"), self.issue("b.1.1")]
        rows = progress(issues)
        # In the order of their numbers, and without the ones that have nothing below.
        self.assertEqual([row["id"] for row in rows], ["a.1", "a.2", "a.10", "b.1"])
        self.assertEqual(rows[0], {"id": "a.1", "title": "Title of a.1", "status": "open", "total": 4, "closed": 3, "flying": 1, "tokens": None})
        self.assertEqual(progress(issues, {"a.1": [1, 2, 3, 4, 5]})[0]["tokens"], [1, 2, 3, 4, 5])
        self.assertEqual((rows[1]["total"], rows[1]["closed"], rows[1]["flying"]), (2, 0, 0))

    def test_an_issues_tokens_are_its_own_and_those_below_it(self):
        issues = self.tree() + [self.issue("x", kind="task", created="2026-11-09T00:00:00Z"), self.issue("b", kind="epic", created="2026-11-11T00:00:00Z")]
        own = {"a.1.2": [1, 10, 100, 5, 1], "a.1": [2, 0, 0, 0, 1], "a.10.1": [4, 0, 0, 0, 1], "": [8, 0, 0, 0, 1], "gone-1": [16, 0, 0, 0, 1], "b": [32, 0, 0, 0, 1]}
        found = tokens(issues, own)
        self.assertEqual(found["a.1.2"], [1, 10, 100, 5, 1])
        self.assertEqual(found["a.1"], [3, 10, 100, 5, 2])
        self.assertEqual(found["a.10"], [4, 0, 0, 0, 1])
        # The root epic, the one made first and not a task, holds every call that names no issue of the tree.
        self.assertEqual(found["a"], [31, 10, 100, 5, 5])
        self.assertEqual((found["b"], "x" in found, "a.2" in found), ([32, 0, 0, 0, 1], False, False))
        self.assertEqual(tokens([self.issue("x")], {"": [1]}), {})
        self.assertEqual(owned(issues, own)["a"], [24, 0, 0, 0, 2])

    def test_the_details_of_an_issue_say_its_tokens_and_its_own(self):
        own = {"a.1.2": [1, 10, 100, 5, 1], "a.1": [2, 0, 0, 0, 1]}
        found = detail(self.tree(), "a.1", own)
        self.assertEqual((found["tokens"], found["own_tokens"]), ([3, 10, 100, 5, 2], [2, 0, 0, 0, 1]))
        found = detail(self.tree(), "a.2", own)
        self.assertEqual((found["tokens"], found["own_tokens"]), (None, None))

    def waits(self):
        """The tree with waits in it: a.3 on a.10.1 and on a closed issue, a.2.1 on a.3 and on a.1.2, and a.4 on a.2.1."""
        issues = {issue["id"]: issue for issue in self.tree()}
        issues["a.3"] = self.issue("a.3", kind="epic", needs=["a.10.1", "a.1.1"])
        issues["a.3.1"] = self.issue("a.3.1")
        issues["a.3.1.1"] = self.issue("a.3.1.1")
        issues["a.2.1"] = self.issue("a.2.1", "blocked", needs=["a.3", "a.1.2"])
        issues["a.4"] = self.issue("a.4", "blocked", needs=["a.2.1"])
        return list(issues.values())

    def test_the_graph_is_every_issue_not_closed_under_what_it_waits_on(self):
        issues = self.waits()
        by_id = {issue["id"]: issue for issue in issues}
        found = {node["id"]: node for node in graph(issues, [by_id["a.10.1"], by_id["a.1"]])}
        self.assertEqual(sorted(found), sorted(issue["id"] for issue in issues if issue["status"] != "closed"))
        self.assertEqual(found["a.10.1"], {"id": "a.10.1", "title": "Title of a.10.1", "type": "task", "status": "open", "priority": 1, "ready": True, "blockers": [], "under": None, "rank": 0})
        # An epic is a node as a leaf is, and a wait on a closed issue is no wait.
        self.assertEqual((found["a.3"]["type"], found["a.3"]["blockers"], found["a.3"]["rank"], found["a.3"]["ready"]), ("epic", ["a.10.1"], 1, False))
        # The rank is the longest chain of waits above the issue.
        self.assertEqual((found["a.2.1"]["blockers"], found["a.2.1"]["rank"]), (["a.1.2", "a.3"], 2))
        self.assertEqual((found["a.4"]["blockers"], found["a.4"]["rank"]), (["a.2.1"], 3))
        # What an epic waits on its children wait on through it, and theirs through them.
        self.assertEqual((found["a.3.1"]["blockers"], found["a.3.1"]["under"], found["a.3.1"]["rank"]), ([], "a.3", 2))
        self.assertEqual((found["a.3.1.1"]["under"], found["a.3.1.1"]["rank"]), ("a.3.1", 3))
        # An epic that waits on nothing passes nothing down, whatever waits below it.
        self.assertEqual((found["a.2"]["rank"], found["a.2.2"]["under"], found["a.2.1"]["under"], found["a"]["rank"]), (0, None, None, 0))
        self.assertEqual((found["a.1"]["ready"], found["a.1.2"]["ready"], found["a.1.2"]["status"]), (True, False, "in_progress"))

    def test_a_loop_of_waits_ends_the_graph_and_is_named(self):
        """An epic that waits on an issue waiting on the epic's own child: the child waits through
        the epic, so the three wait on one another, though no `blocks` dependency closes a loop."""
        issues = self.waits()
        issues += [self.issue("b", kind="epic"), self.issue("b.1", "blocked"), self.issue("b.1.1"), self.issue("c", needs=["b.1"])]
        issues[-4] = self.issue("b", kind="epic", needs=["c"])
        by_id = {issue["id"]: issue for issue in issues}
        found = {node["id"]: node for node in graph(issues, [])}
        self.assertEqual(sorted(found), sorted(issue["id"] for issue in issues if issue["status"] != "closed"))
        # The waits inside the loop are not drawn, so every rank is finite; a wait out of the loop is.
        self.assertEqual((found["b"]["blockers"], found["c"]["blockers"], found["b.1"]["under"]), ([], [], None))
        self.assertEqual((found["b.1.1"]["under"], found["b.1.1"]["rank"]), (None, 0))
        self.assertEqual(found["a.4"]["rank"], 3)
        self.assertEqual(loops(issues), [["b", "b.1", "c"]])
        self.assertEqual(loops(self.waits()), [])
        self.assertEqual(summary(issues, [], {}, alive, self.root, 0)["loops"], [["b", "b.1", "c"]])

    def test_the_details_of_an_issue_are_its_texts_and_the_issues_around_it(self):
        issues = self.waits()
        by_id = {issue["id"]: issue for issue in issues}
        by_id["a.3"].update(description="What it is.", acceptance_criteria="When it is done.", notes="n" * 5000, labels=["skeptic"], assignee="claude-11")
        found = detail(issues, "a.3")
        self.assertEqual({key: found[key] for key in ("id", "title", "priority", "type", "trail", "status", "assignee", "labels")}, {
            "id": "a.3", "title": "Title of a.3", "priority": 1, "type": "epic", "trail": [], "status": "open", "assignee": "claude-11", "labels": ["skeptic"],
        })
        self.assertEqual((found["created"], found["closed"]), (seconds("2026-11-10T10:00:00Z"), None))
        self.assertEqual(found["parent"], {"id": "a", "title": "Title of a", "type": "epic", "status": "open"})
        self.assertEqual([row["id"] for row in found["children"]], ["a.3.1"])
        # A wait on a closed issue is shown as one, closed.
        self.assertEqual([(row["id"], row["status"]) for row in found["blockers"]], [("a.1.1", "closed"), ("a.10.1", "open")])
        self.assertEqual([(row["id"], row["status"]) for row in found["dependents"]], [("a.2.1", "blocked")])
        # Every text whole, and an empty one for what the issue does not have.
        self.assertEqual(found["text"], {"description": "What it is.", "acceptance_criteria": "When it is done.", "design": "", "notes": "n" * 5000, "close_reason": ""})
        json.dumps(found)
        closed = detail(issues, "a.1.3")
        self.assertEqual((closed["closed"], closed["trail"], closed["text"]["close_reason"]), (seconds("2026-11-10T12:00:00Z"), ["Title of a.1"], "x" * 500))
        self.assertEqual((detail(issues, "a")["parent"], detail(issues, "a")["blockers"]), (None, []))
        # The children in the order of their numbers.
        self.assertEqual([row["id"] for row in detail(issues, "a")["children"]], ["a.1", "a.2", "a.3", "a.4", "a.10"])
        self.assertIsNone(detail(issues, "a.99"))

    def test_the_summary_is_what_the_page_draws(self):
        issues = self.tree()
        by_id = {issue["id"]: issue for issue in issues}
        seen = {"claude-11": {"issue": "a.1.2", "stage": "work", "since": 7}, "claude-12": {"issue": "", "stage": "", "since": 8}, "claude-13": {"issue": "", "stage": "", "since": 9}}
        found = summary(issues, [by_id["a.3"], by_id["a.10.1"], by_id["a"]], seen, lambda actor: actor != "claude-13", self.root, 1234.5)
        self.assertEqual(found["now"], 1234.5)
        self.assertEqual(found["counts"], {"total": 12, "open": 10, "deferred": 1, "ready_epics": 2})
        self.assertEqual(len(found["events"]), 14)
        self.assertEqual([row["id"] for row in found["flights"]], ["a.1.2"])
        # A live session that holds nothing is idle; one that ended is not shown.
        self.assertEqual(found["idle"], ["claude-12"])
        # The questions, the one asked first at the top.
        self.assertEqual([(row["id"], row["created"]) for row in found["questions"]], [("a.4", seconds("2026-11-10T09:30:00Z")), ("a.2.1", seconds("2026-11-10T10:00:00Z"))])
        self.assertEqual([row["id"] for row in found["ready"]], ["a.10.1"])
        self.assertEqual([row["id"] for row in found["epics"]], ["a.1", "a.2", "a.10"])
        self.assertEqual(found["graph"], graph(issues, [by_id["a.3"], by_id["a.10.1"], by_id["a"]]))
        self.assertEqual(found["tokens"], {"roots": [], "hours": []})
        self.assertEqual(found["meters"], [])
        self.assertEqual(summary(issues, [], seen, alive, self.root, 0, meters=agy_meters(self.AGY, 0))["meters"], agy_meters(self.AGY, 0))
        hours = [[seconds("2026-11-10T12:00:00Z"), "round", [1, 10, 100, 5, 1]]]
        spent = summary(issues, [], seen, alive, self.root, 0, {"a.1.2": [1, 10, 100, 5, 1], "a.1.3": [2, 0, 0, 0, 1]}, hours)
        self.assertEqual(spent["tokens"], {"roots": [{**brief(by_id["a"], by_id), "tokens": [3, 10, 100, 5, 2]}], "hours": hours})
        self.assertEqual(([row["tokens"] for row in spent["flights"]], spent["epics"][0]["tokens"], spent["closed"][0]["tokens"]),
                         ([[1, 10, 100, 5, 1]], [3, 10, 100, 5, 2], [2, 0, 0, 0, 1]))
        # What closed last comes first, with the start of its reason.
        self.assertEqual([(row["id"], row["actor"], len(row["reason"])) for row in found["closed"]], [("a.1.3", "claude-12", TEXT_SHOWN), ("a.1.1", None, 4)])
        json.dumps(found)

    AGY = json.dumps({"status": "SUCCESS", "command": {"name": "usage", "data": {"groups": [
        {"name": "Gemini Models", "buckets": [
            {"id": "gemini-weekly", "window": "weekly", "remaining_fraction": 0.7372794151306152, "reset_time": "2026-11-19T13:08:11Z"},
            {"id": "gemini-5h", "window": "5h", "remaining_fraction": 0.767340898513794, "reset_time": "2026-11-13T14:55:29Z"}]},
        {"name": "Claude and GPT models", "buckets": [
            {"id": "3p-weekly", "window": "weekly", "remaining_fraction": 1, "reset_time": "2026-11-20T11:56:41Z"}]}]}}})

    def test_agys_gauges_are_its_gemini_buckets_as_percent_used(self):
        self.assertEqual(agy_meters(self.AGY, 99.5), [
            {"name": "Gemini", "window": "week", "percent": 26.3, "resets": seconds("2026-11-19T13:08:11Z"), "read": 99},
            {"name": "Gemini", "window": "five hours", "percent": 23.3, "resets": seconds("2026-11-13T14:55:29Z"), "read": 99}])
        with self.assertRaises(KeyError):
            agy_meters('{"status": "SUCCESS"}', 0)

    def test_claudes_gauges_are_the_week_and_each_scoped_model(self):
        self.assertEqual(claude_meters(None), [])
        scoped = {"Fable": {"percent": 38, "share": 50, "resets_at": "2026-11-15T05:00:00+00:00"},
                  '{"model": null, "surface": "desk"}': {"percent": 3, "share": None, "resets_at": "2026-11-15T05:00:00+00:00"}}
        self.assertEqual(claude_meters((1794562367836, 100, "2026-11-15T04:59:59+00:00", json.dumps(scoped))), [
            {"name": "Claude", "window": "week", "percent": 100, "resets": seconds("2026-11-15T04:59:59+00:00"), "read": 1794562367},
            {"name": "Fable", "window": "week", "percent": 38, "resets": seconds("2026-11-15T05:00:00+00:00"), "read": 1794562367}])

    def test_a_server_asks_agy_for_its_gauges_and_keeps_the_last_through_a_failure(self):
        fake = self.root / "agy"
        fake.write_text(f"#!/bin/sh\n[ -e {self.root}/fail ] && exit 1\ncat {self.root}/usage.json\n")
        fake.chmod(0o755)
        (self.root / "usage.json").write_text(self.AGY)
        beads = Beads(self.root)
        (self.root / "fail").touch()
        with contextlib.redirect_stderr(io.StringIO()) as said:
            ask_agy(beads, self.root, str(fake))
            self.assertEqual(beads.agy, [])
            (self.root / "fail").unlink()
            ask_agy(beads, self.root, str(fake))
            self.assertEqual([(gauge["window"], gauge["percent"]) for gauge in beads.agy], [("week", 26.3), ("five hours", 23.3)])
            (self.root / "fail").touch()
            ask_agy(beads, self.root, str(fake))
            self.assertEqual(len(beads.agy), 2)
        self.assertEqual(said.getvalue().count("agy usage: CalledProcessError"), 2)

    def test_only_the_closes_shown_are_sent(self):
        issues = [self.issue("a", kind="epic")] + [self.issue(f"a.{number}", "closed", closed_at=f"2026-11-10T11:{number:02}:00Z") for number in range(1, 30)]
        found = summary(issues, [], {}, alive, self.root, 0)
        self.assertEqual([row["id"] for row in found["closed"]], [f"a.{number}" for number in range(29, 29 - CLOSED_SHOWN, -1)])

    def serve(self, bd):
        """A server over this root on a free port, with that script as bd; its address."""
        tools = self.root / "bin"
        tools.mkdir()
        (tools / "bd").write_text(f"#!/bin/sh\necho \"$@\" >> {self.root}/calls\n{bd}\n")
        (tools / "bd").chmod(0o755)
        environment = dict(os.environ)
        self.addCleanup(lambda: (os.environ.clear(), os.environ.update(environment)))
        os.environ["PATH"] = f"{tools}:{os.environ['PATH']}"
        os.environ["XDG_RUNTIME_DIR"] = str(self.root / "run")
        serving = server(self.root, "127.0.0.1", 0)
        thread = threading.Thread(target=serving.serve_forever)
        thread.start()
        self.addCleanup(thread.join)
        self.addCleanup(serving.server_close)
        self.addCleanup(serving.shutdown)
        return f"http://127.0.0.1:{serving.server_address[1]}"

    def refused(self, url):
        """The status and the body of the reply to a request the server refuses."""
        with self.assertRaises(urllib.error.HTTPError) as caught:
            urllib.request.urlopen(url)
        with caught.exception as reply:
            return reply.code, reply.read().decode()

    def test_the_server_reads_beads_once_for_pages_that_ask_together(self):
        (self.root / "list.json").write_text(json.dumps(self.tree()))
        (self.root / "ready.json").write_text(json.dumps([issue for issue in self.tree() if issue["id"] == "a.10.1"]))
        address = self.serve(f'case "$1" in list) cat {self.root}/list.json;; ready) cat {self.root}/ready.json;; esac')
        state = round_status().state_dir(self.root)
        state.mkdir(parents=True)
        (state / "claude-11.json").write_text(json.dumps({"key": "a.1.2 verify", "since": 42}))
        with urllib.request.urlopen(f"{address}/data") as reply:
            self.assertEqual(reply.headers["Content-Type"], "application/json")
            found = json.load(reply)
        self.assertEqual(found["counts"]["open"], 10)
        self.assertEqual([(row["id"], row["stage"], row["since"], row["alive"]) for row in found["flights"]], [("a.1.2", "verify", 42, False)])
        self.assertEqual([row["id"] for row in found["ready"]], ["a.10.1"])
        with urllib.request.urlopen(f"{address}/data") as reply:
            self.assertEqual(json.load(reply), found)
        # An issue's details come out of the same read.
        with urllib.request.urlopen(f"{address}/issue/a.1.2") as reply:
            self.assertEqual(reply.headers["Content-Type"], "application/json")
            self.assertEqual(json.load(reply), detail(self.tree(), "a.1.2"))
        self.assertEqual(self.refused(f"{address}/issue/a.99"), (404, "no such issue\n"))
        self.assertEqual(self.refused(f"{address}/issue/"), (404, "no such issue\n"))
        self.assertEqual(found["tokens"], {"roots": [], "hours": []})
        self.assertEqual((self.root / "calls").read_text(), "list --all --json --limit 0\nready --json --limit 0\n")

    def test_the_server_reads_the_tokens_out_of_the_ledger(self):
        (self.root / "list.json").write_text(json.dumps(self.tree()))
        sessions = self.root / ".claude" / "projects" / (str(self.root).replace("/", "-").replace(".", "-").replace("_", "-") + "-main")
        sessions.mkdir(parents=True)
        # One call long ago and one this hour.
        hour = int(time.time()) // 3600 * 3600
        call = {"type": "assistant", "requestId": "req_1", "timestamp": "2020-01-05T12:30:00Z", "message": {"model": "m", "content": [
            {"type": "tool_use", "id": "t", "name": "Bash", "input": {"command": "bd update gone-1 --claim"}}],
            "usage": {"input_tokens": 1, "cache_creation_input_tokens": 10, "cache_read_input_tokens": 100, "output_tokens": 5}}}
        later = {**call, "requestId": "req_2", "timestamp": datetime.fromtimestamp(hour, timezone.utc).isoformat(), "message": {**call["message"], "content": []}}
        (sessions / "s.jsonl").write_text(json.dumps(call) + "\n" + json.dumps(later) + "\n")
        (self.root / ".claude.json").write_text(json.dumps({"cachedUsageUtilization": {"fetchedAtMs": 5000, "utilization": {
            "seven_day": {"utilization": 97, "resets_at": "2026-11-15T04:59:59+00:00"}, "limits": []}}}))
        token_ledger().harvest(self.root / LEDGER, self.root, self.root)
        address = self.serve(f'case "$1" in list) cat {self.root}/list.json;; ready) echo [];; esac')
        with urllib.request.urlopen(f"{address}/data") as reply:
            found = json.load(reply)
        self.assertEqual([(row["id"], row["tokens"]) for row in found["tokens"]["roots"]], [("a", [2, 20, 200, 10, 2])])
        self.assertEqual(found["meters"], [{"name": "Claude", "window": "week", "percent": 97, "resets": seconds("2026-11-15T04:59:59+00:00"), "read": 5}])
        # An hour older than the page draws by the hour comes as its local day.
        day = int(datetime.fromtimestamp(seconds("2020-01-05T12:00:00Z")).replace(hour=0, minute=0).timestamp())
        self.assertEqual(found["tokens"]["hours"], [[day, "session", [1, 10, 100, 5, 1]], [hour, "session", [1, 10, 100, 5, 1]]])
        # The issue the session claimed is not in the tree, so its call is the root's own, as the one before the claim is.
        with urllib.request.urlopen(f"{address}/issue/a") as reply:
            self.assertEqual(json.load(reply)["own_tokens"], [2, 20, 200, 10, 2])

    def test_the_server_gives_the_page_and_nothing_else(self):
        address = self.serve("exit 0")
        with urllib.request.urlopen(f"{address}/") as reply:
            self.assertEqual(reply.headers["Content-Type"], "text/html; charset=utf-8")
            self.assertEqual(reply.read(), PAGE.read_bytes())
        self.assertEqual(self.refused(f"{address}/logs/a-gate.log"), (404, "not found\n"))
        self.assertFalse((self.root / "calls").exists())

    def test_a_bd_that_fails_is_reported_and_asked_again(self):
        address = self.serve("echo 'database is locked' >&2\nexit 3")
        for path in ("/data", "/issue/a.1"):
            self.assertEqual(self.refused(f"{address}{path}"), (503, "bd list exited 3: database is locked"))
        self.assertEqual((self.root / "calls").read_text(), "list --all --json --limit 0\n" * 2)

    def test_a_change_to_the_server_s_code_renews_it_once_the_file_has_settled(self):
        script = self.root / "script.py"
        script.write_text("one\n")
        renewed = threading.Event()
        watch = threading.Thread(target=renewing, args=([script], renewed.set, 0.05), daemon=True)
        watch.start()
        self.assertFalse(renewed.wait(0.4))
        # A file a checkout has taken away and not yet written is not a change to act on.
        script.unlink()
        self.assertFalse(renewed.wait(0.4))
        script.write_text("two, and longer\n")
        self.assertTrue(renewed.wait(5))
        watch.join(5)
        self.assertFalse(watch.is_alive())

    def test_a_running_server_whose_script_changes_executes_the_new_one(self):
        tools = self.root / "main" / "tools"
        tools.mkdir(parents=True)
        for path in (*WATCHED, PAGE):
            (tools / path.name).write_bytes(path.read_bytes())
        script = tools / Path(__file__).name
        running = subprocess.Popen([sys.executable, str(script), "--port", "0"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                   text=True, env={**os.environ, "HOME": str(self.root)})
        self.addCleanup(running.wait)
        self.addCleanup(running.kill)
        limit = threading.Timer(30, running.kill)  # a server that does not renew ends the read below, not the test run
        limit.start()
        self.addCleanup(limit.cancel)
        self.assertTrue(running.stdout.readline().startswith("bead status: http://127.0.0.1:"))
        script.write_text(script.read_text().replace('print(f"bead status: ', 'print(f"bead status renewed: '))
        self.assertTrue(running.stdout.readline().startswith("bead status renewed: http://127.0.0.1:"))


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    sys.exit(main(sys.argv[1:]))
