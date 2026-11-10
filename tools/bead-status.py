#!/usr/bin/env python3
"""The state of the Beads tree as a page for a browser: how many issues are not closed over time,
what each session holds and the stage its round is at, the questions waiting on the human, the
ready leaves, each top epic's progress and what closed last.

The server reads Beads only while a page asks. A request for /data runs bd when what the server
holds is older than AGE seconds, and the page (tools/bead-status.html) asks only while its tab is
visible. The history is each issue's creation and close time out of one `bd list --all`, so nothing
is recorded between runs; an issue reopened counts as open from its creation. A session's stage and
clock are the ones its status line wrote (tools/round-status.py), read from the same files.

Beads is private, so the server listens on this machine alone unless --bind says otherwise.

usage: tools/bead-status.py [--bind ADDRESS] [--port PORT]   (serve the page)
       tools/bead-status.py --test                            (this script's own tests)
"""
import argparse
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import threading
import time
import unittest
import urllib.error
import urllib.request
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

sys.dont_write_bytecode = True  # round-status.py is imported from the tree: leave no __pycache__ in it

AGE = 5
PORT = 8377
PAGE = Path(__file__).with_suffix(".html")
CLOSED_SHOWN = 10
TEXT_SHOWN = 240


def round_status():
    """tools/round-status.py as a module: it says where the status lines keep their clocks."""
    spec = importlib.util.spec_from_file_location("round_status", Path(__file__).with_name("round-status.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


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


def clocks(state):
    """What each session's status line last wrote: the issue it holds, the stage and when the stage began."""
    found = {}
    for file in state.glob("claude-*.json"):
        seen = json.loads(file.read_text())
        issue, _, stage = seen["key"].partition(" ")
        found[file.stem] = {"issue": issue, "stage": stage, "since": seen["since"]}
    return found


def alive(actor):
    """Whether the session claude-<pid> still runs, as a round tells it; None for an assignee that is no session."""
    kind, _, pid = (actor or "").partition("-")
    if kind != "claude" or not pid.isdigit():
        return None
    comm = Path(f"/proc/{pid}/comm")
    return comm.exists() and comm.read_text().strip() == "claude"


def gate_line(log):
    """The last line the landing or the gate wrote of a step, or None when the log has none."""
    if not log.exists():
        return None
    with open(log, "rb") as file:
        file.seek(max(log.stat().st_size - 8192, 0))
        lines = file.read().decode(errors="replace").splitlines()
    steps = [line for line in lines if line.startswith(("gate ", "land: "))]
    return steps[-1][:TEXT_SHOWN] if steps else None


def flights(issues, by_id, seen, running, root):
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
        })
    return rows


def progress(issues):
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
                })
    return sorted(rows, key=lambda row: [(int(part), "") if part.isdigit() else (0, part) for part in row["id"].split(".")])


def summary(issues, ready, seen, running, root, now):
    """What the page draws, from every issue, the ready ones in bd's order and the sessions' clocks."""
    by_id = {issue["id"]: issue for issue in issues}
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
        "flights": flights(issues, by_id, seen, running, root),
        "idle": sorted(actor for actor in seen if running(actor) and actor not in held),
        "questions": [{**brief(issue, by_id), "created": seconds(issue["created_at"])} for issue in questions],
        "ready": [brief(issue, by_id) for issue in ready if issue["issue_type"] != "epic"],
        "epics": progress(issues),
        "closed": [
            {
                **brief(issue, by_id),
                "at": seconds(issue["closed_at"]),
                "actor": issue.get("assignee"),
                "reason": issue["close_reason"][:TEXT_SHOWN],
            }
            for issue in reversed(closed[-CLOSED_SHOWN:])
        ],
    }


def read(root, now):
    """The summary of the tree at this project root as it is now."""
    bd = lambda *arguments: json.loads(subprocess.run(["bd", *arguments, "--json", "--limit", "0"], cwd=root, check=True, capture_output=True, text=True).stdout)
    return summary(bd("list", "--all"), bd("ready"), clocks(round_status().state_dir(root)), alive, root, now)


class Beads:
    """The summary as the body of a reply, read again once it is older than AGE however many pages ask."""

    def __init__(self, root):
        self.root = root
        self.lock = threading.Lock()
        self.read_at = 0
        self.held = b""

    def body(self):
        with self.lock:
            now = time.time()
            if now - self.read_at > AGE:
                self.held = json.dumps(read(self.root, now)).encode()
                self.read_at = now
            return self.held


class Page(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path == "/":
            self.reply(200, "text/html; charset=utf-8", PAGE.read_bytes())
        elif self.path == "/data":
            try:
                self.reply(200, "application/json", self.server.beads.body())
            except subprocess.CalledProcessError as failure:
                # bd is another process, and it gives up when the tree's lock stays held.
                self.reply(503, "text/plain; charset=utf-8", f"bd {failure.cmd[1]} exited {failure.returncode}: {failure.stderr.strip()}".encode())
        else:
            self.reply(404, "text/plain; charset=utf-8", b"not found\n")

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


def main(arguments):
    parser = argparse.ArgumentParser(description="Serve the state of the Beads tree as a page.")
    parser.add_argument("--bind", default="127.0.0.1", help="the address to listen on (default: this machine alone)")
    parser.add_argument("--port", type=int, default=PORT)
    options = parser.parse_args(arguments)
    serving = server(Path(__file__).resolve().parents[2], options.bind, options.port)
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

    def issue(self, name, status="open", kind="task", created="2026-11-10T10:00:00Z", **fields):
        parent = name.rpartition(".")[0]
        issue = {"id": name, "title": f"Title of {name}", "status": status, "priority": 1, "issue_type": kind, "created_at": created, **fields}
        if parent:
            issue["parent"] = parent
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
            "gate": "gate verify: ok in 58.7 s: 0 errors, allowance 0",
        })
        # A clock that names another issue says nothing of this one.
        self.assertEqual((rows[0]["actor"], rows[0]["alive"], rows[0]["stage"], rows[0]["since"], rows[0]["gate"]), ("claude-12", False, None, None, None))
        self.assertEqual((rows[2]["actor"], rows[2]["stage"]), (None, None))

    def test_an_epic_under_the_root_counts_every_issue_below_it(self):
        issues = self.tree() + [self.issue("a.1.2.1", "closed"), self.issue("b", kind="epic"), self.issue("b.1", kind="epic"), self.issue("b.1.1")]
        rows = progress(issues)
        # In the order of their numbers, and without the ones that have nothing below.
        self.assertEqual([row["id"] for row in rows], ["a.1", "a.2", "a.10", "b.1"])
        self.assertEqual(rows[0], {"id": "a.1", "title": "Title of a.1", "status": "open", "total": 4, "closed": 3, "flying": 1})
        self.assertEqual((rows[1]["total"], rows[1]["closed"], rows[1]["flying"]), (2, 0, 0))

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
        # What closed last comes first, with the start of its reason.
        self.assertEqual([(row["id"], row["actor"], len(row["reason"])) for row in found["closed"]], [("a.1.3", "claude-12", TEXT_SHOWN), ("a.1.1", None, 4)])
        json.dumps(found)

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
        self.assertEqual((self.root / "calls").read_text(), "list --all --json --limit 0\nready --json --limit 0\n")

    def test_the_server_gives_the_page_and_nothing_else(self):
        address = self.serve("exit 0")
        with urllib.request.urlopen(f"{address}/") as reply:
            self.assertEqual(reply.headers["Content-Type"], "text/html; charset=utf-8")
            self.assertEqual(reply.read(), PAGE.read_bytes())
        self.assertEqual(self.refused(f"{address}/logs/a-gate.log"), (404, "not found\n"))
        self.assertFalse((self.root / "calls").exists())

    def test_a_bd_that_fails_is_reported_and_asked_again(self):
        address = self.serve("echo 'database is locked' >&2\nexit 3")
        for _ in range(2):
            self.assertEqual(self.refused(f"{address}/data"), (503, "bd list exited 3: database is locked"))
        self.assertEqual((self.root / "calls").read_text(), "list --all --json --limit 0\n" * 2)


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    sys.exit(main(sys.argv[1:]))
