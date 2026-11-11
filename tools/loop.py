#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The round loop, driven from the command line.

Each round is `claude -p --agent round` in the main worktree, a fresh session that ends when the
round does: print mode waits for a background command the round started, such as its landing, and
wakes the round when it exits, so the last result the session streams is the round's report. The
report's lines say what comes next, as the round skill reads them (.claude/skills/round/SKILL.md):

- `Notify: <text>` (or bullets under a bare `Notify:`), each sent with notify-send and printed;
- `Prover: <id>` runs `claude -p --agent prover`, then appends its report to the issue as
  `Prover report:` and sets the issue open; `Skeptic: <review>` does the same with the skeptic;
- `Loop: continue` starts the next round, `Loop: wait` waits (another loop holds the issues in
  progress), `Loop: stop` prints the questions waiting on the human and ends the loop.

The loop is one Beads actor, loop-<pid>, for every session it runs (.claude/hooks/beads-actor.sh),
so an issue a round hands to the prover stays held between the two sessions.

Stopping. SIGINT (Ctrl-C) or SIGTERM, or `tools/loop.py --stop`, lets the agent run in flight finish
and ends the loop; a prover or skeptic pass a finished round handed over is not started, and its
issue is released with a note so the next round picks it up. A second signal, or `--stop --now`
(SIGUSR1), ends the run in flight too: the session's process group gets SIGTERM, then SIGKILL after
30 s, and the next round's orient recovers what it left. Each loop writes its pid to
<project root>/logs/loop/<pid> while it runs; `--stop` signals each such pid that is still a loop.

Tuning. Before each session the loop reads <project root>/loop.toml: a table per kind (round, prover,
skeptic) whose keys model, autocompact, effort and fallback-model become that flag of claude -p; a key
left out passes no flag, so the agent file's model and effort hold. An edit takes effect at the next
session. A file that does not parse or names what claude does not take is reported, and the loop
keeps the last values it read. SIGHUP, or `tools/loop.py --reload`, re-executes the loop after the
run in flight and its hand-off, with the same pid and so the same actor, to take up a change to this
script.

A usage limit waits until the limit's reset and goes on. A run that fails otherwise (no report, or
an error result) is retried after 1, 2 and 4 minutes; the fourth failure in a row ends the loop.

usage: tools/loop.py [--once] [--wait SECONDS]   run rounds until the loop stops
       tools/loop.py --stop [--now] [PID...]     stop running loops, after their run in flight
       tools/loop.py --reload [PID...]           re-execute running loops, after their run in flight
       tools/loop.py --test                      this script's own tests
"""
import argparse
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

ROOT = Path(__file__).resolve().parents[2]
MAIN = ROOT / "main"
PIDS = ROOT / "logs" / "loop"
CONFIG = ROOT / "loop.toml"
KINDS = ("round", "prover", "skeptic")
EFFORTS = ("low", "medium", "high", "xhigh", "max")
ISSUE = r"[a-z][a-z0-9]*-[a-z0-9]+(?:\.[0-9]+)*"
KEY = re.compile(rf"^(Loop|Prover|Skeptic|Notify):\s*(.*)$")
DECORATION = "-*`> \t"
WAIT = 900
FAILURES = 4
KILL_AFTER = 30
SHOWN = 160


@dataclass
class Report:
    """What a round's report asks of the driver."""
    loop: str = None
    prover: str = None
    skeptic: str = None
    notify: list = field(default_factory=list)


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
            elif key in ("Prover", "Skeptic"):
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
    """Plan-weighted tokens: input, cache writes at 1.25, cache reads at 0.1, output at 5."""
    return (usage.get("input_tokens", 0) + 1.25 * usage.get("cache_creation_input_tokens", 0)
            + 0.1 * usage.get("cache_read_input_tokens", 0) + 5 * usage.get("output_tokens", 0))


def glimpse(tool):
    """One line for a tool call: its description, or what it acts on."""
    given = tool.get("input", {})
    what = given.get("description") or given.get("command") or given.get("file_path") or given.get("pattern") or ""
    return f"{tool.get('name')}: {what.splitlines()[0] if what else ''}"


def follow(lines, show):
    """Read a session's stream-json lines, showing its progress; the last result is the report."""
    run = Run()
    for line in lines:
        try:
            event = json.loads(line)
        except ValueError:
            if line.strip():
                show(line.rstrip()[:SHOWN])
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
            if run.error and re.search(r"usage limit|limit reached|rate limit", run.report, re.I):
                run.limited = True
    return run


def options(text):
    """The claude -p flags loop.toml gives each kind. The file is the human's, so a ValueError says what is wrong."""
    try:
        tables = tomllib.loads(text)
    except tomllib.TOMLDecodeError as error:
        raise ValueError(f"not TOML: {error}")
    flags = {}
    for kind, table in tables.items():
        if kind not in KINDS or not isinstance(table, dict):
            raise ValueError(f"{kind}: not a table of {', '.join(KINDS)}")
        flags[kind] = []
        for key, value in table.items():
            if not isinstance(value, str) or not value or value.startswith("-"):
                raise ValueError(f"{kind}.{key}: not a value")
            if key == "autocompact":
                size = re.fullmatch(r"([0-9]+)k|(1)m", value.lower())
                if value != "auto" and not (size and (size.group(2) or 100 <= int(size.group(1)) <= 1000)):
                    raise ValueError(f"{kind}.autocompact: {value} is not auto or 100k to 1M")
            elif key == "effort":
                if value not in EFFORTS:
                    raise ValueError(f"{kind}.effort: {value} is not one of {', '.join(EFFORTS)}")
            elif key not in ("model", "fallback-model"):
                raise ValueError(f"{kind}.{key}: not model, autocompact, effort or fallback-model")
            flags[kind] += [f"--{key}", value]
    return flags


def loop_alive(pid):
    """Whether the process with this pid is a loop: an argument of its argv ends in tools/loop.py."""
    try:
        argv = Path(f"/proc/{pid}/cmdline").read_bytes().split(b"\0")
    except (FileNotFoundError, ProcessLookupError):
        return False
    return any(arg.endswith(b"tools/loop.py") for arg in argv)


class Loop:
    """The driver. The commands and the clock are parameters so the tests can replace them."""

    def __init__(self, claude="claude", bd="bd", notifier="notify-send", cwd=MAIN, pids=PIDS, config=CONFIG,
                 wait=WAIT, sleep=time.sleep, now=time.time, out=sys.stdout):
        self.claude, self.bd, self.notifier = claude, bd, notifier
        self.cwd, self.pids, self.config, self.wait = Path(cwd), Path(pids), Path(config), wait
        self.flags, self.read = {}, None
        self.sleep, self.now, self.out = sleep, now, out
        self.actor = f"loop-{os.getpid()}"
        self.env = {key: value for key, value in os.environ.items() if key != "CLAUDECODE"}
        self.env["BEADS_ACTOR"] = self.actor
        self.stopping = False
        self.halting = False
        self.reloading = False
        self.child = None

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

    # Sessions.

    def tune(self):
        """Take up loop.toml when it changed since the last session; keep the last values when it is wrong."""
        text = self.config.read_text() if self.config.exists() else ""
        if text == self.read:
            return
        self.read = text
        try:
            self.flags = options(text)
        except ValueError as error:
            self.say("loop", f"{self.config.name}: {error}; keeping the last values")
            return
        shown = "; ".join(f"{kind} {' '.join(flags)}" for kind, flags in self.flags.items() if flags)
        self.say("loop", f"{self.config.name}: {shown or 'no flags'}")

    def agent(self, kind, prompt):
        """Run one agent session in the main worktree; its stream is shown as it comes."""
        self.tune()
        command = [self.claude, "-p", "--agent", kind, "--permission-mode", "auto",
                   "--output-format", "stream-json", "--verbose", *self.flags.get(kind, []), prompt]
        started = self.now()
        self.say(kind, f"start: {prompt}")
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
            self.child = None
        minutes = (self.now() - started) / 60
        usage = f", weekly {100 * run.utilization:.0f}%" if run.utilization is not None else ""
        self.say(kind, f"end: exit {run.exit}, {minutes:.1f} min, {run.turns} turns, "
                       f"{run.weighted / 1e6:.2f}M weighted tokens{usage}")
        return run

    def beads(self, *args):
        done = subprocess.run([self.bd, *args], cwd=self.cwd, env=self.env, stdin=subprocess.DEVNULL,
                              capture_output=True, text=True)
        if done.returncode != 0:
            self.say("bd", f"bd {' '.join(args[:2])} failed: {(done.stderr or done.stdout).strip()[:SHOWN]}")
        return done.stdout

    def notify(self, text):
        self.say("notify", text)
        if shutil.which(self.notifier):
            subprocess.run([self.notifier, "atmosphere loop", text], stdin=subprocess.DEVNULL,
                           capture_output=True)

    # The hand-offs.

    def hand_off(self, kind, issue, prompt):
        """Run the prover or the skeptic a round handed over, record its report and release the issue."""
        label = kind.capitalize()
        if self.stopping:
            self.beads("update", issue, "--append-notes",
                       f"{label} not run: the loop stopped before it started; the next round hands it over again.")
        else:
            run = self.agent(kind, prompt)
            report = run.report.strip() if run.report.strip() and not run.error else (
                f"none; the {kind}'s session ended without one (exit {run.exit}"
                f"{', usage limit' if run.limited else ''}).")
            self.beads("update", issue, "--append-notes", f"{label} report: {report}")
        self.beads("update", issue, "-s", "open", "--assignee", "")

    def round(self):
        """One round and its hand-off. The report's Loop word, or None when the round failed."""
        run = self.agent("round", "Run one round.")
        if run.report.strip():
            print(textwrap.indent(run.report.strip(), "    "), file=self.out, flush=True)
        report = parse(run.report) if not run.error else Report()
        for text in report.notify:
            self.notify(text)
        if report.prover:
            self.hand_off("prover", report.prover,
                          f"Issue {report.prover}, worktree {self.cwd.parent / report.prover}. "
                          "Your input is the issue's last Prover input note.")
        if report.skeptic:
            self.hand_off("skeptic", report.skeptic,
                          f"Review {report.skeptic}. Your input is the review's last Skeptic input note.")
        return report.loop, run

    def drive(self, once=False):
        """Rounds until the loop stops. The exit status: 0 for a stop, 1 for repeated failures."""
        failures = 0
        while not self.stopping and not self.reloading:
            loop, run = self.round()
            if loop is not None:
                failures = 0
            if loop == "stop":
                blocked = self.beads("list", "-s", "blocked")
                print(blocked, file=self.out, flush=True)
                questions = sum(1 for line in blocked.splitlines() if re.search(ISSUE, line) and line.lstrip()[:1] in "●○◐")
                self.notify(f"round loop stopped: {questions} questions in bd list -s blocked")
                return 0
            if once or self.stopping or self.reloading:
                break
            if loop == "wait":
                self.pause(self.wait, "nothing ready; another loop holds the issues in progress")
            elif loop is None and run.limited:
                reset = max((run.reset or self.now() + 3600) - self.now(), 0) + 60
                self.pause(reset, "usage limit")
            elif loop is None:
                failures += 1
                if failures >= FAILURES:
                    self.notify(f"round loop stopped: {failures} failed rounds in a row")
                    return 1
                self.pause(60 * 2 ** (failures - 1), f"the round ended without a report (failure {failures})")
        self.say("loop", "reloading" if self.reloading and not self.stopping else "stopped")
        return 0


def main_loop(args):
    loop = Loop(wait=args.wait)
    PIDS.mkdir(parents=True, exist_ok=True)
    pidfile = PIDS / str(os.getpid())
    pidfile.write_text(f"{os.getpid()}\n")
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
        sleep = [sys.executable, "-c", "import time; time.sleep(60)"]
        plain, other = subprocess.Popen(sleep), subprocess.Popen(sleep + ["/x/tools/loop.py"])
        try:
            self.assertEqual((loop_alive(plain.pid), loop_alive(other.pid)), (False, True))
        finally:
            for process in (plain, other):
                process.kill()
                process.wait()

    def test_stop_signals_a_live_loop_and_drops_a_stale_pid_file(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            catcher = "import signal, sys, time\nsignal.signal(signal.SIGTERM, lambda *a: sys.exit(7))\nprint('up', flush=True)\ntime.sleep(60)\n"
            other = subprocess.Popen([sys.executable, "-c", catcher, "/x/tools/loop.py"], stdout=subprocess.PIPE, text=True)
            other.stdout.readline()
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
            self.assertFalse((folder / "4194305").exists())

    def test_loop_toml_gives_each_kind_its_flags(self):
        text = '[round]\nmodel = "opus"\nautocompact = "200k"\n[prover]\neffort = "xhigh"\nfallback-model = "opus"\n[skeptic]\nautocompact = "1M"\n'
        self.assertEqual(options(text), {"round": ["--model", "opus", "--autocompact", "200k"],
                                         "prover": ["--effort", "xhigh", "--fallback-model", "opus"],
                                         "skeptic": ["--autocompact", "1M"]})
        self.assertEqual(options(""), {})

    def test_loop_toml_refuses_what_claude_does_not_take(self):
        for text in ("[round\n", "[driver]\nmodel = \"opus\"\n", "model = \"opus\"\n", "[round]\nturns = \"9\"\n",
                     "[round]\neffort = \"huge\"\n", "[round]\nautocompact = \"50k\"\n", "[round]\nautocompact = \"2m\"\n",
                     "[round]\nautocompact = 200000\n", "[round]\nmodel = \"--dangerously\"\n"):
            with self.assertRaises(ValueError, msg=text):
                options(text)

    # The driver against a fake claude and a fake bd, which log their arguments.

    FAKE_CLAUDE = textwrap.dedent("""\
        import json, os, sys, time
        folder = os.environ["FAKE"]
        open(os.path.join(folder, "claude.log"), "a").write(json.dumps(sys.argv[1:] + [os.environ["BEADS_ACTOR"]]) + "\\n")
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
        open(os.path.join(os.environ["FAKE"], "bd.log"), "a").write(json.dumps(sys.argv[1:]) + "\\n")
        if sys.argv[1:3] == ["list", "-s"]:
            print("● atmo-1.9 ● P2 Should the loop ask?")
        """)

    def driver(self, folder, *replies, **given):
        for name, text in (("claude", self.FAKE_CLAUDE), ("bd", self.FAKE_BD)):
            path = folder / name
            path.write_text(f"#!{sys.executable}\n{text}")
            path.chmod(0o755)
        for number, reply in enumerate(replies):
            (folder / f"reply-{number:03}").write_text(reply)
        os.environ["FAKE"] = str(folder)
        clock = [0.0]
        loop = Loop(claude=str(folder / "claude"), bd=str(folder / "bd"), notifier="no-such-notifier",
                    cwd=folder, pids=folder, config=folder / "loop.toml", sleep=lambda seconds: clock.__setitem__(0, clock[0] + seconds),
                    now=lambda: clock[0], out=open(os.devnull, "w"), **given)
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
            self.assertEqual(self.log(folder, "bd"), [])

    def test_a_second_signal_ends_the_session_in_flight(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            loop, _ = self.driver(folder, "SLEEP")
            started = time.monotonic()
            timer = __import__("threading").Timer(1.0, lambda: (loop.on_stop(signal.SIGTERM, None), loop.on_stop(signal.SIGTERM, None)))
            timer.start()
            self.assertEqual(loop.drive(), 0)
            self.assertLess(time.monotonic() - started, 20)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--once", action="store_true", help="run one round and its hand-off, then stop")
    parser.add_argument("--wait", type=float, default=WAIT, help="seconds to wait on 'Loop: wait'")
    parser.add_argument("--stop", action="store_true", help="stop running loops after their run in flight")
    parser.add_argument("--now", action="store_true", help="with --stop, end the run in flight too")
    parser.add_argument("--reload", action="store_true", help="re-execute running loops after their run in flight")
    parser.add_argument("--test", action="store_true", help="run this script's own tests")
    parser.add_argument("pids", nargs="*", help="with --stop, the loops to stop; all by default")
    args = parser.parse_args()
    if args.test:
        unittest.main(argv=[sys.argv[0]], verbosity=1)
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
