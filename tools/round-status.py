#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The status line of a Claude Code session in this tree: the session's Beads actor, the issue the
session holds, the stage its round is at, and how long it has been at that stage.

.claude/settings.json runs this once a second in every session. A session is the Beads actor
claude-<pid> (.claude/hooks/beads-actor.sh), so the issue it holds is the one in progress under that
name, and the line starts with the actor so an assignee read from bd can be matched to its terminal.
The stage is read from what a round leaves behind as it works, which costs the round nothing
and cannot disagree with what it is doing:

  read      the issue is claimed and has no worktree
  work      its worktree exists
  verify    tools/verify.py runs in the worktree
  gate      tools/land.py runs in the worktree
  fix       the worktree's last landing exited non-zero (the last line of logs/<id>-gate.log)
  close     it exited 0
  prover    the session's newest subagent is the prover
  skeptic   the session's newest subagent is the skeptic

The clock is the time since a status line of the session first saw the stage.

A bd command holds the database's lock while it runs and a second one waits about a second for it,
so a status line never runs bd. The sessions share one list of the issues in progress, and a
detached run of this script rewrites it when it is older than LIST_AGE seconds.

usage: tools/round-status.py             (the status line: Claude Code's session JSON on stdin)
       tools/round-status.py --refresh   (rewrite the shared list of the issues in progress)
       tools/round-status.py --test      (this script's own tests)
"""
import fcntl
import json
import os
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

LIST = "in-progress.json"
LIST_AGE = 15


def state_dir(root):
    """Where the status lines of the tree at this project root keep the shared list and their clocks."""
    return Path(os.environ["XDG_RUNTIME_DIR"]) / "atmo-round-status" / str(root).strip("/").replace("/", "-")


def write(path, value):
    """Replace the file in one step: Claude Code kills a status line that the next one overtakes."""
    scratch = path.with_name(f"{path.name}.{os.getpid()}")
    scratch.write_text(json.dumps(value))
    os.replace(scratch, path)


def fresh(listing, now):
    return listing.exists() and now - listing.stat().st_mtime <= LIST_AGE


def refresh(root, state):
    """Rewrite the shared list from bd, unless another run is doing so or has just done so."""
    state.mkdir(parents=True, exist_ok=True)
    with open(state / "lock", "w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return
        if fresh(state / LIST, time.time()):
            return
        listed = subprocess.run(["bd", "list", "-s", "in_progress", "--json"], cwd=root, check=True, capture_output=True, text=True)
        write(state / LIST, json.loads(listed.stdout))


def held(issues, actor):
    """The issue the actor holds, the one updated last when it holds several, and how many others it holds."""
    mine = sorted((issue for issue in issues if issue.get("assignee") == actor), key=lambda issue: issue["updated_at"])
    return (mine[-1], len(mine) - 1) if mine else (None, 0)


def scripts(worktree):
    """The names the processes working under the worktree were started with: each one's first arguments, not its command line as text."""
    names = set()
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            cwd = Path(os.readlink(f"/proc/{pid}/cwd"))
            arguments = Path(f"/proc/{pid}/cmdline").read_bytes().split(b"\0")[:3]
        except OSError:
            continue  # it exited meanwhile, or it is another user's
        if cwd == worktree or worktree in cwd.parents:
            names.update(os.path.basename(os.fsdecode(argument)) for argument in arguments)
    return names


def gate_exit(log):
    """The exit status the landing command appended to its log, or None when the log has none."""
    if not log.exists():
        return None
    with open(log, "rb") as file:
        file.seek(max(log.stat().st_size - 64, 0))
        lines = file.read().decode(errors="replace").splitlines()
    word, _, status = lines[-1].partition(" ") if lines else ("", "", "")
    return int(status) if word == "exit" and status.isdigit() else None


def agent(transcript):
    """The type of the session's newest subagent, from the files Claude Code keeps beside the transcript."""
    logs = sorted(transcript.with_suffix("").glob("subagents/agent-*.jsonl"), key=lambda log: log.stat().st_mtime)
    meta = logs[-1].with_suffix(".meta.json") if logs else None
    return json.loads(meta.read_text()).get("agentType") if meta and meta.exists() else None


def stage(agent_type, started, landed, worktree):
    """The stage of the round holding an issue, from its newest agent, the scripts running in its worktree, its last landing's exit and whether the worktree exists."""
    if agent_type in ("prover", "skeptic"):
        return agent_type
    if "land.py" in started:
        return "gate"
    if "verify.py" in started:
        return "verify"
    if landed == 0:
        return "close"
    if not worktree:
        return "read"
    return "work" if landed is None else "fix"


def since(clock_file, key, now):
    """When the stage `key` names began: the time of the first call that named it."""
    seen = json.loads(clock_file.read_text()) if clock_file.exists() else {}
    if seen.get("key") != key:
        seen = {"key": key, "since": now}
        write(clock_file, seen)
    return seen["since"]


def clock(seconds):
    minutes, seconds = divmod(int(seconds), 60)
    hours, minutes = divmod(minutes, 60)
    return f"{hours}:{minutes:02}:{seconds:02}" if hours else f"{minutes:02}:{seconds:02}"


def render(issue, others, name, elapsed, columns):
    """What the session holds: the id, the stage and its clock in bold, and as much of the title as the width leaves, dimmed."""
    if issue is None:
        return f"no ticket {clock(elapsed)}"
    head = f"{issue['id']}{f' (+{others})' if others else ''} · "
    timed = f"{name} {clock(elapsed)}"
    room = columns - len(head) - len(timed) - len(" · ")
    title = issue["title"] if len(issue["title"]) <= room else issue["title"][: room - 1] + "…"
    return f"{head}\033[1m{timed}\033[22m" + (f" · \033[2m{title}\033[22m" if room > 1 else "")


def line(root, state, actor, transcript, now, columns):
    """The session's line: its actor, then what it holds."""
    start = f"{actor} · "
    listing = state / LIST
    if not listing.exists():
        return f"{start}reading beads"
    issue, others = held(json.loads(listing.read_text()), actor)
    name = None
    if issue is not None:
        worktree = root / issue["id"]
        name = stage(agent(transcript), scripts(worktree), gate_exit(root / "logs" / f"{issue['id']}-gate.log"), worktree.is_dir())
    key = f"{issue['id']} {name}" if issue else ""
    text = start + render(issue, others, name, now - since(state / f"{actor}.json", key, now), columns - len(start))
    age = int(now - listing.stat().st_mtime)
    return text if age <= 4 * LIST_AGE else f"{text} · beads last read {clock(age)} ago"


def main(arguments):
    root = Path(__file__).resolve().parents[2]
    state = state_dir(root)
    if arguments == ["--refresh"]:
        refresh(root, state)
        return 0
    session = json.load(sys.stdin)
    state.mkdir(parents=True, exist_ok=True)
    now = time.time()
    if not fresh(state / LIST, now):
        subprocess.Popen(
            [sys.executable, __file__, "--refresh"],
            start_new_session=True, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
    # Claude Code draws the line inside its own margin, so the full width would wrap.
    columns = int(os.environ["COLUMNS"]) - 4
    print(line(root, state, f"claude-{os.environ['CLAUDE_PID']}", Path(session["transcript_path"]), now, columns))
    return 0


class Tests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name).resolve()
        self.state = self.root / "state"
        self.state.mkdir()
        (self.root / "logs").mkdir()
        self.transcript = self.root / "transcripts" / "session.jsonl"

    def issue(self, name, assignee, updated="2026-11-10T17:00:00Z", title="A title"):
        return {"id": name, "title": title, "assignee": assignee, "updated_at": updated}

    def subagent(self, name, agent_type, modified):
        directory = self.transcript.with_suffix("") / "subagents"
        directory.mkdir(parents=True, exist_ok=True)
        (directory / f"agent-{name}.jsonl").write_text("{}\n")
        (directory / f"agent-{name}.meta.json").write_text(json.dumps({"agentType": agent_type}))
        os.utime(directory / f"agent-{name}.jsonl", (modified, modified))

    def start(self, directory, script):
        """A process started as that script in that directory, seen in /proc before this returns."""
        directory.mkdir(parents=True, exist_ok=True)
        (directory / script).write_text("import time\ntime.sleep(60)\n")
        process = subprocess.Popen([sys.executable, script], cwd=directory)
        self.addCleanup(process.wait)
        self.addCleanup(process.kill)
        deadline = time.time() + 10
        while script not in scripts(directory):
            self.assertLess(time.time(), deadline, f"{script} never appeared in /proc")
            time.sleep(0.01)

    def test_the_held_issue_is_the_actors_own_updated_last(self):
        issues = [
            self.issue("a-1", "claude-1", "2026-11-10T17:00:00Z"),
            self.issue("a-2", "claude-2", "2026-11-10T17:05:00Z"),
            self.issue("a-3", "claude-1", "2026-11-10T17:03:00Z"),
        ]
        issue, others = held(issues, "claude-1")
        self.assertEqual((issue["id"], others), ("a-3", 1))
        self.assertEqual(held(issues, "claude-2")[1], 0)
        self.assertEqual(held(issues, "claude-9"), (None, 0))

    def test_a_script_is_found_by_its_name_among_the_processes_of_its_worktree_only(self):
        worktree = self.root / "a-1"
        self.start(worktree / "tools", "land.py")
        self.assertIn("land.py", scripts(worktree))
        self.assertNotIn("land.py", scripts(self.root / "a-2"))
        # A worktree whose name another's begins with is not that worktree.
        self.assertNotIn("land.py", scripts(self.root / "a"))

    def test_a_landing_log_gives_its_exit_only_once_the_command_appended_it(self):
        log = self.root / "logs" / "a-1-gate.log"
        self.assertIsNone(gate_exit(log))
        log.write_text("")
        self.assertIsNone(gate_exit(log))
        log.write_bytes(b"land: gating abc on main at def\n   Compiling \xff\xfe scroll v0.11.0\n")
        self.assertIsNone(gate_exit(log))
        log.write_text("gate total: 299.2 s\nland: abc landed as gated\nexit 0\n")
        self.assertEqual(gate_exit(log), 0)
        log.write_text("x" * 500 + "\ngate boot: FAIL in 120.1 s: no exit within 120 s\nexit 1\n")
        self.assertEqual(gate_exit(log), 1)

    def test_the_newest_subagent_names_the_agent(self):
        self.assertIsNone(agent(self.transcript))
        self.subagent("one", "round", 1000)
        self.subagent("two", "prover", 2000)
        self.assertEqual(agent(self.transcript), "prover")
        self.subagent("three", "round", 3000)
        self.assertEqual(agent(self.transcript), "round")

    def test_the_stage_follows_what_the_round_left_behind(self):
        self.assertEqual(stage("round", set(), None, False), "read")
        self.assertEqual(stage("round", {"python3"}, None, True), "work")
        self.assertEqual(stage("round", {"python3", "verify.py"}, None, True), "verify")
        # The gate runs verify.py too, under land.py.
        self.assertEqual(stage("round", {"land.py", "verify.py"}, 1, True), "gate")
        self.assertEqual(stage("round", set(), 1, True), "fix")
        self.assertEqual(stage("round", {"verify.py"}, 1, True), "verify")
        self.assertEqual(stage("round", set(), 0, True), "close")
        # The landing removes the worktree before the round closes the issue.
        self.assertEqual(stage("round", set(), 0, False), "close")
        # A failed landing's log outlives a worktree the round removed.
        self.assertEqual(stage("round", set(), 1, False), "read")
        self.assertEqual(stage("prover", {"verify.py"}, None, True), "prover")
        self.assertEqual(stage("skeptic", set(), None, False), "skeptic")
        self.assertEqual(stage(None, set(), None, True), "work")

    def test_the_clock_starts_when_a_stage_is_first_seen(self):
        clock_file = self.state / "claude-1.json"
        self.assertEqual(since(clock_file, "a-1 work", 100), 100)
        self.assertEqual(since(clock_file, "a-1 work", 160), 100)
        self.assertEqual(since(clock_file, "a-1 gate", 200), 200)
        self.assertEqual(since(clock_file, "a-1 gate", 500), 200)
        self.assertEqual(since(clock_file, "a-1 work", 600), 600)

    def test_the_clock_reads_in_minutes_and_then_in_hours(self):
        self.assertEqual(clock(0), "00:00")
        self.assertEqual(clock(192.9), "03:12")
        self.assertEqual(clock(3599), "59:59")
        self.assertEqual(clock(3600), "1:00:00")
        self.assertEqual(clock(40000), "11:06:40")

    def test_the_line_fits_the_width_by_shortening_the_title(self):
        issue = self.issue("atmo-1.2", "claude-1", title="Keep interrupts masked outside idle")
        plain = lambda text: text.replace("\033[1m", "").replace("\033[2m", "").replace("\033[22m", "")
        self.assertEqual(plain(render(issue, 0, "gate", 192, 80)), "atmo-1.2 · gate 03:12 · Keep interrupts masked outside idle")
        self.assertEqual(plain(render(issue, 0, "gate", 192, 40)), "atmo-1.2 · gate 03:12 · Keep interrupts…")
        self.assertEqual(len(plain(render(issue, 0, "gate", 192, 40))), 40)
        self.assertEqual(plain(render(issue, 2, "work", 5, 32)), "atmo-1.2 (+2) · work 00:05 · Ke…")
        # A title of the ellipsis alone says nothing.
        self.assertEqual(plain(render(issue, 2, "work", 5, 30)), "atmo-1.2 (+2) · work 00:05")
        self.assertEqual(plain(render(issue, 0, "gate", 192, 20)), "atmo-1.2 · gate 03:12")
        self.assertEqual(render(issue, 0, "gate", 192, 80), "atmo-1.2 · \033[1mgate 03:12\033[22m · \033[2mKeep interrupts masked outside idle\033[22m")
        self.assertEqual(render(None, 0, None, 83, 80), "no ticket 01:23")

    def test_a_session_reads_its_own_issue_and_stage_from_the_shared_list(self):
        self.assertEqual(line(self.root, self.state, "claude-1", self.transcript, 1000, 80), "claude-1 · reading beads")
        listing = self.state / LIST
        write(listing, [self.issue("a-1", "claude-1", title="One"), self.issue("a-2", "claude-2", title="Two")])
        os.utime(listing, (1000, 1000))
        self.assertEqual(line(self.root, self.state, "claude-1", self.transcript, 1000, 80), "claude-1 · a-1 · \033[1mread 00:00\033[22m · \033[2mOne\033[22m")
        (self.root / "a-1").mkdir()
        self.assertIn("work 00:00", line(self.root, self.state, "claude-1", self.transcript, 1010, 80))
        self.assertIn("work 00:05", line(self.root, self.state, "claude-1", self.transcript, 1015, 80))
        (self.root / "logs" / "a-1-gate.log").write_text("gate boot: FAIL in 120.1 s: no exit\nexit 1\n")
        self.assertIn("fix 00:00", line(self.root, self.state, "claude-1", self.transcript, 1020, 80))
        self.subagent("one", "prover", 1025)
        self.assertIn("prover 00:00", line(self.root, self.state, "claude-1", self.transcript, 1030, 80))
        self.assertIn("prover 00:10", line(self.root, self.state, "claude-1", self.transcript, 1040, 80))
        # Each session has its own clock, and one that holds nothing says so.
        other = self.root / "transcripts" / "other.jsonl"
        self.assertTrue(line(self.root, self.state, "claude-2", other, 1040, 80).startswith("claude-2 · a-2 · \033[1mread 00:00"))
        self.assertEqual(line(self.root, self.state, "claude-3", self.transcript, 1040, 80), "claude-3 · no ticket 00:00")
        self.assertEqual(line(self.root, self.state, "claude-3", self.transcript, 1055, 80), "claude-3 · no ticket 00:15")

    def test_the_actor_at_the_start_leaves_the_title_less_room(self):
        listing = self.state / LIST
        write(listing, [self.issue("atmo-1.2", "claude-1234567", title="Keep interrupts masked outside idle")])
        os.utime(listing, (1000, 1000))
        plain = lambda text: text.replace("\033[1m", "").replace("\033[2m", "").replace("\033[22m", "")
        self.assertEqual(plain(line(self.root, self.state, "claude-1234567", self.transcript, 1000, 80)), "claude-1234567 · atmo-1.2 · read 00:00 · Keep interrupts masked outside idle")
        self.assertEqual(plain(line(self.root, self.state, "claude-1234567", self.transcript, 1000, 50)), "claude-1234567 · atmo-1.2 · read 00:00 · Keep int…")
        self.assertEqual(len(plain(line(self.root, self.state, "claude-1234567", self.transcript, 1000, 50))), 50)

    def test_a_list_nothing_has_rewritten_says_how_old_it_is(self):
        listing = self.state / LIST
        write(listing, [])
        os.utime(listing, (1000, 1000))
        self.assertEqual(line(self.root, self.state, "claude-1", self.transcript, 1000 + 4 * LIST_AGE, 80), "claude-1 · no ticket 00:00")
        self.assertEqual(line(self.root, self.state, "claude-1", self.transcript, 1125, 80), "claude-1 · no ticket 01:05 · beads last read 02:05 ago")

    def test_the_gate_stage_is_a_landing_running_in_the_issues_worktree(self):
        write(self.state / LIST, [self.issue("a-1", "claude-1")])
        self.start(self.root / "a-1", "land.py")
        self.assertIn("gate 00:00", line(self.root, self.state, "claude-1", self.transcript, time.time(), 80))

    def bd(self, output):
        """A bd on PATH that prints `output` and counts its runs in the file this returns."""
        runs = self.root / "bd-runs"
        (self.root / "bin").mkdir(exist_ok=True)
        (self.root / "bin" / "bd").write_text(f"#!/bin/sh\necho \"$*\" >> {runs}\ncat <<'END'\n{output}\nEND\n")
        (self.root / "bin" / "bd").chmod(0o755)
        path = os.environ["PATH"]
        os.environ["PATH"] = f"{self.root / 'bin'}:{path}"
        self.addCleanup(os.environ.__setitem__, "PATH", path)
        return runs

    def test_a_refresh_writes_the_list_bd_gives_and_leaves_a_fresh_one_alone(self):
        runs = self.bd(json.dumps([self.issue("a-1", "claude-1")]))
        state = self.root / "elsewhere" / "state"
        refresh(self.root, state)
        self.assertEqual(json.loads((state / LIST).read_text())[0]["id"], "a-1")
        self.assertEqual(runs.read_text().splitlines(), ["list -s in_progress --json"])
        refresh(self.root, state)
        self.assertEqual(len(runs.read_text().splitlines()), 1)
        os.utime(state / LIST, (time.time() - LIST_AGE - 1,) * 2)
        refresh(self.root, state)
        self.assertEqual(len(runs.read_text().splitlines()), 2)

    def test_a_refresh_does_nothing_while_another_holds_the_lock(self):
        runs = self.bd("[]")
        with open(self.state / "lock", "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            refresh(self.root, self.state)
        self.assertFalse(runs.exists())
        self.assertFalse((self.state / LIST).exists())


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
