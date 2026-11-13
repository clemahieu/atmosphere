#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Grok's plan meter: the weekly limit's percent used and when it resets, read off Grok's own /usage
window and printed as one line of JSON.

Grok prints the plan's limit only inside its interactive session: `grok usage` on this host's route
says to run /usage inside grok instead. So this starts `grok` in a tmux server of its own, its
socket named for this process in <project root>/scratch/grok-usage, the folder grok runs in, which
holds nothing else and is all Grok is asked to trust. It answers the trust question with yes when
Grok asks it, types /usage once the prompt is up, again every RESEND seconds while no window has
come, and reads the window. Whatever happens it kills its tmux server, and with it Grok, which has
sent the model nothing, and removes the socket.

The window reads, among its borders:

    Weekly limit (SuperGrok Heavy)
    ██░░░░░░░░░░░░░░░░░░░░░░░░░░░░  5%
    Resets: November 20, 01:06

The reset carries no year and no zone: it is this host's local time, in the year that puts it
nearest after the read, so a reset a day behind the clock is still this year's.

Prints {"plan": <str | null>, "percent": <float>, "resets_at": <epoch seconds>, "read": <epoch seconds>}.

Exit status: 0 printed; 1 no reading within TIMEOUT seconds, or a window this does not know, with the
last pane on stderr.

usage: tools/grok-usage.py          (read the meter)
       tools/grok-usage.py --test   (this script's own tests)
"""
import json
import os
import re
import subprocess
import sys
import time
import unittest
from datetime import datetime, timedelta
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FOLDER = ROOT / "scratch" / "grok-usage"
TIMEOUT = 90
RESEND = 8
POLL = 0.5
WIDTH, HEIGHT = 160, 50
TRUST = "Do you trust the contents of this directory?"
PROMPT = "❯"
LIMIT = re.compile(r"Weekly limit(?: \(([^)]*)\))?")
PERCENT = re.compile(r"(\d+(?:\.\d+)?)%")
RESETS = re.compile(r"Resets: ([A-Z][a-z]+ \d{1,2}), (\d{1,2}):(\d{2})")


class Unknown(ValueError):
    """A pane whose usage window is not the one this reads."""


def reading(pane, now):
    """(plan, percent, resets_at) out of a pane that shows the usage window, or None while it does not;
    Unknown when it shows a weekly limit without the percent or the reset this reads."""
    limit = LIMIT.search(pane)
    if not limit:
        return None
    rest = pane[limit.end():]
    percent, resets = PERCENT.search(rest), RESETS.search(rest)
    if not percent or not resets:
        if not resets and "Resets:" not in rest:
            return None  # the window is still being drawn
        raise Unknown("a weekly limit without the percent and the reset this reads")
    day, hour, minute = resets.groups()
    read = datetime.fromtimestamp(now)
    at = datetime.strptime(f"{day} {read.year}", "%B %d %Y").replace(hour=int(hour), minute=int(minute))
    if at < read - timedelta(days=1):
        at = at.replace(year=read.year + 1)
    return limit.group(1), float(percent.group(1)), at.timestamp()


def tmux(socket):
    """Run one tmux command on the server at the path `socket`, returning what it printed."""
    def run(*arguments):
        return subprocess.run(["tmux", "-S", str(socket), *arguments], check=True, capture_output=True, text=True,
                              env={**os.environ, "TERM": os.environ.get("TERM") or "xterm-256color"}).stdout
    return run


def ask(run, folder, now=time.time, sleep=time.sleep, timeout=TIMEOUT):
    """Start grok under the tmux server `run` drives, read its usage window, and kill the server."""
    folder.mkdir(parents=True, exist_ok=True)
    pane = ""
    try:
        run("new-session", "-d", "-x", str(WIDTH), "-y", str(HEIGHT), "-c", str(folder), "grok")
        start, sent = now(), None
        while now() - start < timeout:
            pane = run("capture-pane", "-p", "-t", "0")
            found = reading(pane, now())
            if found:
                plan, percent, resets_at = found
                return {"plan": plan, "percent": percent, "resets_at": resets_at, "read": now()}
            if TRUST in pane:
                run("send-keys", "-t", "0", "y")
            elif PROMPT in pane and (sent is None or now() - sent >= RESEND):
                run("send-keys", "-t", "0", "-l", "/usage")
                run("send-keys", "-t", "0", "Enter")
                sent = now()
            sleep(POLL)
        raise TimeoutError(f"no usage window within {timeout} s")
    except (Unknown, TimeoutError) as failure:
        failure.pane = pane
        raise
    finally:
        try:
            run("kill-server")
        except subprocess.CalledProcessError:
            pass  # the server ended with grok


PANE = """\
 main ~/a/scratch/grok-usage                                                       1.8K / 256K │ [Dashboard]
          ┌───────────────────────────────────────────────────────────── [✗] ─┐
          │  Context usage  Usage limit  Session info                          │
          │────────────────────────────────────────────────────────────────────│
          │ Weekly limit (SuperGrok Heavy)                                     │
          │                                                                    │
          │ ██░░░░░░░░░░░░░░░░░░░░░░░░░░░░  5%                                 │
          │ Resets: November 20, 01:06                                         │
          │                                                                    │
          │               Tab switch  |  ↑/↓ scroll  |  Esc close              │
          └────────────────────────────────────────────────────────────────────┘
 ╭──────────────────────────────────────────────────────────────────────────────╮
 │ ❯                                                                            │
 ╰─────────────────────────────────────────────── Grok 4.7 (xhigh) · always-approve ─╯
"""


class Tests(unittest.TestCase):
    NOW = datetime(2026, 11, 13, 12, 0).timestamp()

    def test_reads_the_weekly_limit_off_the_usage_window(self):
        self.assertEqual(reading(PANE, self.NOW), ("SuperGrok Heavy", 5.0, datetime(2026, 11, 20, 1, 6).timestamp()))

    def test_a_reset_after_new_year_is_next_years_and_one_just_passed_is_this_years(self):
        late = datetime(2026, 12, 30, 12, 0).timestamp()
        self.assertEqual(reading(PANE.replace("November 20", "January 3"), late)[2], datetime(2027, 1, 3, 1, 6).timestamp())
        self.assertEqual(reading(PANE.replace("November 20", "November 13").replace("01:06", "06:00"), self.NOW)[2],
                         datetime(2026, 11, 13, 6, 0).timestamp())

    def test_a_pane_without_the_window_reads_nothing_and_a_changed_window_is_unknown(self):
        self.assertIsNone(reading(" │ ❯  │\n", self.NOW))
        self.assertIsNone(reading("│ Weekly limit (SuperGrok Heavy) │\n│ ██░░ 5% │\n", self.NOW))
        with self.assertRaises(Unknown):
            reading(PANE.replace("Resets: November 20, 01:06", "Resets: in 6 days"), self.NOW)
        self.assertEqual(reading(PANE.replace(" (SuperGrok Heavy)", ""), self.NOW)[0], None)

    def fake(self, panes):
        """A tmux whose pane shows each of `panes` in turn, the last one from then on."""
        calls, clock = [], [0.0]

        def run(*arguments):
            calls.append(arguments)
            if arguments[0] == "capture-pane":
                return panes.pop(0) if len(panes) > 1 else panes[0]
            return ""
        return run, calls, (lambda: clock[0]), (lambda seconds: clock.__setitem__(0, clock[0] + seconds))

    def test_answers_the_trust_question_types_usage_at_the_prompt_and_kills_its_server(self):
        folder = Path(os.environ.get("TMPDIR", "/tmp")) / f"grok-usage-test-{os.getpid()}"
        run, calls, now, sleep = self.fake([TRUST, " │ ❯ │", " │ ❯ │", PANE])
        try:
            found = ask(run, folder, now, sleep)
        finally:
            folder.rmdir()
        self.assertEqual((found["plan"], found["percent"]), ("SuperGrok Heavy", 5.0))
        sent = [call for call in calls if call[0] != "capture-pane"]
        self.assertEqual(sent, [("new-session", "-d", "-x", str(WIDTH), "-y", str(HEIGHT), "-c", str(folder), "grok"),
                                ("send-keys", "-t", "0", "y"),
                                ("send-keys", "-t", "0", "-l", "/usage"), ("send-keys", "-t", "0", "Enter"),
                                ("kill-server",)])

    def test_types_usage_again_while_no_window_comes_and_gives_up_at_the_timeout_killing_its_server(self):
        folder = Path(os.environ.get("TMPDIR", "/tmp")) / f"grok-usage-test-{os.getpid()}"
        run, calls, now, sleep = self.fake([" │ ❯ │"])
        try:
            with self.assertRaises(TimeoutError) as raised:
                ask(run, folder, now, sleep, timeout=20)
        finally:
            folder.rmdir()
        self.assertEqual(raised.exception.pane, " │ ❯ │")
        typed = [call for call in calls if call[-1] == "/usage"]
        self.assertEqual(len(typed), 3)  # at 0, 8 and 16 s
        self.assertEqual(calls[-1], ("kill-server",))


def main():
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]], verbosity=1)
    if sys.argv[1:]:
        sys.exit(f"usage: {sys.argv[0]} [--test]")
    socket = FOLDER / f"tmux-{os.getpid()}"
    try:
        found = ask(tmux(socket), FOLDER)
    except (Unknown, TimeoutError) as failure:
        print(f"grok usage: {failure}\n{failure.pane}", file=sys.stderr)
        sys.exit(1)
    finally:
        socket.unlink(missing_ok=True)
    print(json.dumps(found))


if __name__ == "__main__":
    main()
