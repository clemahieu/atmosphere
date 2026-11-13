#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""What a landed leaf cost, every session counted, by the model its rounds ran on, with the rework beside it.

A setting of the loop (loop.toml: each kind's model and effort) is judged by what the work it lands
costs, not by what a round costs: a cheaper round that needs a second round, the prover, or a fix
after the skeptic refutes it is not cheaper. This harvests the token ledger (tools/token-ledger.py),
reads the Beads tree and the landing logs, and prints, for the leaves closed in a window:

- one line per model the leaves' rounds ran on: the leaves, the share that are rework, a leaf's cost
  (mean, median and 90th percentile), its round sessions, and the share that went to the prover,
  ended an attempt at its bound, were recovered from a round that did not finish, or had a landing
  the gate failed with the change at fault (`exit 1` in logs/<id>-gate.log);
- one line per day: what the loop spent that day, rounds, provers and skeptics, over the leaves
  landed that day that are not rework, which is the figure to compare settings by;
- the reviews closed in the window, passed and refuted.

A landed leaf is a closed issue that is not an epic, a decision or a review, whose close reason names
a commit and which the ledger has a round for. Its cost is every call the ledger counts under its
id, in weekly points: a point is one percent of the plan's seven-day limit, which is what runs out
and what the human budgets in. List dollars are not given, since the meter does not charge by list
price and a dollar on one model moves it further than a dollar on another. Its model is the one its
rounds cost most on. Rework is a leaf labelled `refuted`, filed for a criterion a skeptic pass
refuted. The ledger counts by the hour, so a day's spend starts at the hour the window does. A model
RATES does not hold is named on a last line, and its calls are left out. A model whose id starts
with `grok-` is not one of those: the plan is a flat subscription, so it has no weekly points. Its
round sessions are counted with the leaf's and its calls add nothing to the points. Its cost in
weighted tokens is what tools/offering-report.py shows.

The plan does not publish what a call costs it, so RATES is measured: a call's tokens are weighted
(WEIGHTS: input 1, cache write 1.25, cache read 0.1, output 5, the weights the rates were fitted
under), and a model's rate is the points the meter moved for a million weighted tokens of it. The meter is
the percentage of the week's limit that Claude Code fetches, and each harvest of the ledger keeps
the newest fetch as a row of the `readings` table of logs/token-ledger.sqlite, whose columns the
opening comment of tools/token-ledger.py gives: `fetched_ms` is its time and `percent` the meter.
To measure again, take from that table the readings at both ends of a stretch in which the meter
did not reset, sum the ledger's weighted tokens by model over the same hours (the `totals` table,
every kind, since the meter counts sessions outside the loop too), and divide. The meter resets at
`resets_at`, and whenever the human spends one of the plan's resets, which lowers it and leaves
`resets_at` as it was: a stretch is clean when every reading in it has the same `resets_at` and none
is lower than the one before it. Readings are as close together as the harvests were, so a reset
between two far apart can hide under what was spent after it, and a stretch whose points come to far
fewer than its tokens holds one. A stretch on one model gives that model's rate directly; stretches
that mix models give one equation each, points moved = the sum over models of rate times weighted
millions, solved together. The Fable models have a meter of their own beside it, under `Fable` in
the reading's `scoped`: its `percent` is of an allowance that is `share` points, so its movement
times that share over a hundred is the points Fable moved, apart from every other model's. A meter
steps by whole percents, so a stretch that moves it a few points gives a rate no closer than a step
at each end allows. Put the date beside the rate.

usage: tools/leaf-cost.py [--since WHEN] [--until WHEN]   (local time: 2026-11-12 or 2026-11-12T20:00)
       tools/leaf-cost.py --test                          (this script's own tests)
"""
import argparse
import json
import math
import re
import runpy
import sqlite3
import statistics
import subprocess
import sys
import tempfile
import unittest
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

TREE = Path(__file__).resolve().parents[1]
ROOT = TREE.parent
LEDGER = Path(__file__).with_name("token-ledger.py")
# What a token counts for, in the order of the ledger's columns: input, cache write, cache read, output.
WEIGHTS = (1, 1.25, 0.1, 5)
# Weekly points a million weighted tokens, and the day the rate was measured.
RATES = {
    "claude-fable-5-2": (0.57, "2026-11-12"),
    "claude-fable-5-1": (0.64, "2026-11-10"),
    "claude-opus-5-5": (0.12, "2026-11-10"),
}
LOOP = ("round", "prover", "skeptic")
NOT_LEAVES = ("epic", "decision")
COMMIT = re.compile(r"\b[0-9a-f]{7,40}\b")
FAULT = re.compile(r"^exit 1$", re.M)


@dataclass
class Leaf:
    """A landed leaf: when it closed, what it cost and what it took."""
    id: str
    closed: float
    model: str
    points: float
    rounds: int
    rework: bool
    prover: bool
    attempt: bool
    recovered: bool
    fault: bool


def points(model, counts):
    """Token counts in weekly points at the model's rate, or None for a model RATES does not hold."""
    if model not in RATES:
        return None
    return RATES[model][0] * sum(count * weight for count, weight in zip(counts, WEIGHTS)) / 1e6


def grok_model(model):
    """Whether the model is Grok's. Its plan is a flat subscription, so it has no weekly points."""
    return model == "grok" or model.startswith("grok-")


def spent(ledger):
    """From the ledger: each issue's points by agent kind and model, each issue's round sessions,
    the loop's points by hour, and the models with no rate."""
    db = sqlite3.connect(f"file:{ledger}?mode=ro", uri=True)
    issues, hours, unrated = {}, [], set()
    for issue, kind, model, hour, *counts in db.execute(
            "select issue, kind, model, hour, sum(input), sum(cache_write), sum(cache_read), sum(output) "
            "from totals group by issue, kind, model, hour"):
        cost = points(model, counts)
        if cost is None and not grok_model(model):
            unrated.add(model)
            continue
        if cost is None:
            cost = 0.0
        by = issues.setdefault(issue, {})
        by[kind, model] = by.get((kind, model), 0.0) + cost
        if kind in LOOP and cost:
            hours.append((hour, cost))
    sessions = dict(db.execute("select issue, count(distinct file) from calls where kind = 'round' group by issue"))
    db.close()
    return issues, sessions, hours, unrated


def landed(issue):
    """Whether a Beads issue is a leaf closed on a commit."""
    return (issue["status"] == "closed" and issue.get("issue_type") not in NOT_LEAVES
            and "review" not in (issue.get("labels") or [])
            and COMMIT.search(issue.get("close_reason") or "") is not None)


def leaves(tracker, issues, sessions, logs):
    """The landed leaves the ledger has a round for."""
    found = []
    for issue in tracker:
        costs = issues.get(issue["id"], {})
        rounds = {model: cost for (kind, model), cost in costs.items() if kind == "round"}
        if not rounds or not landed(issue):
            continue
        notes = issue.get("notes") or ""
        log = logs / f"{issue['id']}-gate.log"
        found.append(Leaf(
            id=issue["id"], closed=closed(issue), model=max(rounds, key=rounds.get), points=sum(costs.values()),
            rounds=sessions[issue["id"]], rework="refuted" in (issue.get("labels") or []),
            prover="Prover input" in notes, attempt=re.search(r"Attempt \d+:", notes) is not None,
            recovered="Recovered at orient" in notes,
            fault=log.exists() and FAULT.search(log.read_text(errors="replace")) is not None))
    return found


def closed(issue):
    """When Beads closed an issue, in seconds since the epoch."""
    return datetime.fromisoformat(issue["closed_at"]).timestamp()


def day_of(moment):
    return datetime.fromtimestamp(moment).strftime("%Y-%m-%d")


def share(group, sign):
    return f"{100 * sum(getattr(leaf, sign) for leaf in group) / len(group):.0f}%"


def report(found, hours, tracker, since, until, unrated=()):
    """The lines for the leaves, the spend and the reviews of the window."""
    window = [leaf for leaf in found if since <= leaf.closed < until]
    lines = ["landed leaves by the model of their rounds; weekly points a leaf, every session counted, at the rates of "
             + ", ".join(sorted({measured for _, measured in RATES.values()})),
             f"{'model':<20}{'leaves':>7}{'rework':>8}{'mean':>8}{'median':>8}{'p90':>8}{'rounds':>8}{'prover':>8}"
             f"{'attempt':>9}{'recovered':>11}{'fault':>7}"]
    for model in sorted({leaf.model for leaf in window}):
        group = [leaf for leaf in window if leaf.model == model]
        costs = sorted(leaf.points for leaf in group)
        lines.append(
            f"{model:<20}{len(group):>7}{share(group, 'rework'):>8}{statistics.mean(costs):>8.3f}{statistics.median(costs):>8.3f}"
            f"{costs[math.ceil(0.9 * len(costs)) - 1]:>8.3f}{sum(leaf.rounds for leaf in group) / len(group):>8.2f}"
            f"{share(group, 'prover'):>8}{share(group, 'attempt'):>9}{share(group, 'recovered'):>11}{share(group, 'fault'):>7}")
    days = {}
    for hour, cost in hours:
        if since <= hour < until:
            days.setdefault(day_of(hour), [0.0, 0, 0])[0] += cost
    for leaf in window:
        day = days.setdefault(day_of(leaf.closed), [0.0, 0, 0])
        day[1] += 1
        day[2] += not leaf.rework
    lines.append(f"{'day':<12}{'spent':>9}{'landed':>8}{'not rework':>12}{'a leaf not rework':>19}")
    for day, (cost, count, fresh) in sorted(days.items()):
        lines.append(f"{day:<12}{cost:>9.2f}{count:>8}{fresh:>12}{(f'{cost / fresh:.3f}' if fresh else '-'):>19}")
    reviews = [issue.get("close_reason") or "" for issue in tracker
               if issue["status"] == "closed" and "review" in (issue.get("labels") or []) and since <= closed(issue) < until]
    lines.append(f"reviews closed: {sum(reason.startswith('skeptic pass') for reason in reviews)} passed, "
                 f"{sum(reason.startswith('refuted') for reason in reviews)} refuted")
    lines += [f"no rate for {model}: its calls are left out" for model in sorted(unrated)]
    grok = sorted({leaf.model for leaf in window if grok_model(leaf.model)})
    lines += [f"{model}: sessions are counted and add no weekly points; the plan is a flat subscription, "
              f"and its cost is weighted tokens" for model in grok]
    return lines


def main(arguments):
    parser = argparse.ArgumentParser(description="What a landed leaf cost, by the model of its rounds.")
    parser.add_argument("--since", type=datetime.fromisoformat, metavar="WHEN")
    parser.add_argument("--until", type=datetime.fromisoformat, metavar="WHEN")
    options = parser.parse_args(arguments)
    ledger = ROOT / "logs" / "token-ledger.sqlite"
    harvest = subprocess.run([sys.executable, LEDGER, "--ledger", ledger], capture_output=True, text=True)
    if harvest.returncode != 0:
        sys.exit(f"leaf-cost: token-ledger.py exited {harvest.returncode}: {(harvest.stderr or harvest.stdout).strip()}")
    listed = subprocess.run(["bd", "list", "--all", "--json", "--limit", "0"], cwd=TREE, capture_output=True, text=True)
    if listed.returncode != 0:
        sys.exit(f"leaf-cost: bd list exited {listed.returncode}: {(listed.stderr or listed.stdout).strip()}")
    tracker = json.loads(listed.stdout)
    issues, sessions, hours, unrated = spent(ledger)
    since = options.since.timestamp() if options.since else -math.inf
    until = options.until.timestamp() if options.until else math.inf
    print("\n".join(report(leaves(tracker, issues, sessions, ROOT / "logs"), hours, tracker, since, until, unrated)))
    return 0


class Tests(unittest.TestCase):
    OPUS, FABLE = "claude-opus-5-5", "claude-fable-5-2"

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.logs = Path(directory.name)
        self.ledger = self.logs / "ledger.sqlite"
        self.db = sqlite3.connect(self.ledger)
        self.db.executescript(runpy.run_path(str(LEDGER))["SCHEMA"])  # the ledger's own tables; run_path caches no bytecode in the tree
        self.noon = datetime(2026, 11, 12, 12).timestamp()
        self.calls = 0
        self.files = {}

    def spend(self, issue, kind, model, hour=None, sessions=("s1",), **tokens):
        """One total of the ledger, and a call in each session that made it."""
        counts = [tokens.get(name, 0) for name in ("input", "cache_write", "cache_read", "output")]
        hour = self.noon if hour is None else hour
        self.db.execute("insert into totals values (?, ?, ?, ?, ?, ?, ?, ?, ?)", (issue, kind, model, hour, *counts, len(sessions)))
        for session in sessions:
            self.calls += 1
            file = self.files.setdefault(session, len(self.files) + 1)
            self.db.execute("insert into calls values (?, ?, ?, ?, ?, ?, 0, 0, 0, 0)", (f"r{self.calls}", file, issue, kind, model, hour))
        self.db.commit()

    def issue(self, id, reason="abc1234: done", closed=None, type="task", labels=None, notes="", status="closed"):
        stamp = datetime.fromtimestamp(self.noon if closed is None else closed, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        return {"id": id, "status": status, "issue_type": type, "labels": labels, "notes": notes, "close_reason": reason, "closed_at": stamp}

    def found(self, *tracker):
        issues, sessions, hours, unrated = spent(self.ledger)
        return leaves(list(tracker), issues, sessions, self.logs), hours, unrated

    def test_a_leaf_costs_every_session_under_its_id_at_each_models_rate(self):
        self.spend("a-1", "round", self.OPUS, sessions=("s1", "s2"), output=1_000_000, cache_read=10_000_000)
        self.spend("a-1", "prover", self.FABLE, sessions=("s3",), input=1_000_000, cache_write=1_000_000)
        self.spend("a-2", "round", self.OPUS, sessions=("s4",), output=500_000)
        (leaf,), _, _ = self.found(self.issue("a-1"))
        self.assertEqual((leaf.id, leaf.model, leaf.rounds, leaf.closed), ("a-1", self.OPUS, 2, self.noon))
        self.assertAlmostEqual(leaf.points, 0.12 * (5 + 1) + 0.57 * (1 + 1.25))

    def test_the_same_tokens_are_more_points_on_the_model_the_meter_charges_more_for(self):
        tokens = dict(input=1_000_000, cache_write=1_000_000, cache_read=10_000_000, output=1_000_000)
        self.spend("a-1", "round", self.OPUS, **tokens)
        self.spend("a-2", "round", self.FABLE, sessions=("s2",), **tokens)
        opus, fable = self.found(self.issue("a-1"), self.issue("a-2"))[0]
        self.assertAlmostEqual(opus.points, 0.12 * 8.25)
        self.assertAlmostEqual(fable.points, 0.57 * 8.25)

    def test_a_leafs_model_is_the_one_its_rounds_cost_most_on(self):
        self.spend("a-1", "round", self.OPUS, output=100_000)
        self.spend("a-1", "round", self.FABLE, sessions=("s2",), output=100_000)
        self.spend("a-1", "skeptic", self.OPUS, sessions=("s3",), output=900_000)
        (leaf,), _, _ = self.found(self.issue("a-1"))
        self.assertEqual(leaf.model, self.FABLE)

    def test_only_a_leaf_closed_on_a_commit_with_a_round_in_the_ledger_is_landed(self):
        for id in ("a-1", "a-2", "a-3", "a-4", "a-5", "a-6"):
            self.spend(id, "round", self.OPUS, sessions=(id,), output=1000)
        found, _, _ = self.found(
            self.issue("a-1"), self.issue("a-2", type="epic"), self.issue("a-3", labels=["review"], reason="skeptic pass: abc1234"),
            self.issue("a-4", reason="Already true, no commit"), self.issue("a-5", status="open"), self.issue("a-6", type="decision"),
            self.issue("a-7"))
        self.assertEqual([leaf.id for leaf in found], ["a-1"])

    def test_the_label_the_notes_and_the_gate_log_say_what_a_leaf_took(self):
        for id in ("a-1", "a-2", "a-3"):
            self.spend(id, "round", self.OPUS, sessions=(id,), output=1000)
        (self.logs / "a-1-gate.log").write_text("gate verify: failed\nexit 1\ngate: ok\nexit 0\n")
        (self.logs / "a-2-gate.log").write_text("Permission denied (publickey)\nexit 128\nexit 0\n")
        notes = "Prover input: target 3 verified\nAttempt 1: tried the lemma\nRecovered at orient: worktree absent"
        found, _, _ = self.found(self.issue("a-1", notes=notes, labels=["refuted"]), self.issue("a-2"), self.issue("a-3", notes="Prover report: proved"))
        took = [(leaf.rework, leaf.prover, leaf.attempt, leaf.recovered, leaf.fault) for leaf in found]
        self.assertEqual(took, [(True, True, True, True, True), (False, False, False, False, False), (False, False, False, False, False)])

    def test_a_line_per_model_gives_the_cost_and_the_shares(self):
        for number, cost in enumerate((1, 2, 3, 4, 10)):
            self.spend(f"a-{number}", "round", self.OPUS, sessions=(f"s{number}", f"t{number}")[:1 + (number == 0)], output=cost * 50_000)
        self.spend("b-1", "round", self.FABLE, sessions=("f1",), output=100_000)
        tracker = [self.issue(f"a-{number}", labels=["refuted"] if number == 4 else None, notes="Prover input: x" if number < 2 else "") for number in range(5)]
        found, hours, _ = self.found(*tracker, self.issue("b-1"))
        lines = report(found, hours, tracker, -math.inf, math.inf)
        self.assertEqual(lines[1].split(), ["model", "leaves", "rework", "mean", "median", "p90", "rounds", "prover", "attempt", "recovered", "fault"])
        self.assertEqual(lines[2].split(), [self.FABLE, "1", "0%", "0.285", "0.285", "0.285", "1.00", "0%", "0%", "0%", "0%"])
        self.assertEqual(lines[3].split(), [self.OPUS, "5", "20%", "0.120", "0.090", "0.300", "1.20", "40%", "0%", "0%", "0%"])

    def test_a_day_is_the_loops_spend_over_its_leaves_that_are_not_rework(self):
        self.spend("a-1", "round", self.OPUS, output=250_000)
        self.spend("a-2", "round", self.OPUS, sessions=("s2",), output=250_000)
        self.spend("a-3", "round", self.OPUS, sessions=("s3",), output=250_000)
        self.spend("a-9", "skeptic", self.OPUS, sessions=("s4",), output=300_000)
        self.spend("", "session", self.OPUS, sessions=("s5",), output=5_000_000)
        tracker = [self.issue("a-1"), self.issue("a-2"), self.issue("a-3", labels=["refuted"]),
                   self.issue("a-9", labels=["review"], reason="refuted: criterion 2"), self.issue("a-8", labels=["review"], reason="skeptic pass: abc1234")]
        found, hours, _ = self.found(*tracker)
        lines = report(found, hours, tracker, -math.inf, math.inf)
        day = lines[lines.index(next(line for line in lines if line.startswith("day"))) + 1]
        self.assertEqual(day.split(), ["2026-11-12", "0.63", "3", "2", "0.315"])
        self.assertEqual(lines[-1], "reviews closed: 1 passed, 1 refuted")

    def test_the_window_bounds_the_leaves_the_spend_and_the_reviews(self):
        early, late = self.noon - 86400, self.noon
        self.spend("a-1", "round", self.OPUS, hour=early, output=50_000)
        self.spend("a-2", "round", self.FABLE, hour=late, sessions=("s2",), output=50_000)
        tracker = [self.issue("a-1", closed=early), self.issue("a-2", closed=late), self.issue("a-8", closed=early, labels=["review"], reason="skeptic pass: abc1234")]
        found, hours, _ = self.found(*tracker)
        lines = report(found, hours, tracker, self.noon - 3600, math.inf)
        self.assertEqual([line.split()[0] for line in lines[2:-1]], [self.FABLE, "day", "2026-11-12"])
        self.assertEqual(lines[-1], "reviews closed: 0 passed, 0 refuted")

    def test_a_day_that_landed_only_rework_has_no_cost_a_leaf(self):
        self.spend("a-1", "round", self.OPUS, output=50_000)
        tracker = [self.issue("a-1", labels=["refuted"])]
        found, hours, _ = self.found(*tracker)
        self.assertEqual(report(found, hours, tracker, -math.inf, math.inf)[-2].split(), ["2026-11-12", "0.03", "1", "0", "-"])

    def test_a_leafs_round_count_includes_its_grok_sessions_and_not_their_tokens(self):
        self.spend("a-1", "round", self.OPUS, sessions=("s1",), output=1_000_000)
        self.spend("a-1", "round", "grok-4.7", sessions=("g1", "g2"), output=9_000_000)
        (leaf,), _, unrated = self.found(self.issue("a-1"))
        self.assertEqual(leaf.rounds, 3)
        self.assertAlmostEqual(leaf.points, 0.12 * 5)
        self.assertNotIn("grok-4.7", unrated)

    def test_a_leaf_whose_rounds_are_only_grok_is_counted_with_no_weekly_points(self):
        self.spend("a-1", "round", "grok-4.7", sessions=("g1",), output=1_000_000)
        found, hours, unrated = self.found(self.issue("a-1"))
        self.assertEqual([(leaf.id, leaf.model, leaf.rounds, leaf.points) for leaf in found], [("a-1", "grok-4.7", 1, 0.0)])
        self.assertNotIn("grok-4.7", unrated)
        lines = report(found, hours, [self.issue("a-1")], -math.inf, math.inf, unrated)
        self.assertEqual(lines[-1], "grok-4.7: sessions are counted and add no weekly points; "
                         "the plan is a flat subscription, and its cost is weighted tokens")

    def test_a_model_without_a_rate_is_named_and_left_out(self):
        self.spend("a-1", "round", self.OPUS, output=50_000)
        self.spend("a-1", "round", "claude-next-9", sessions=("s2",), output=9_000_000)
        tracker = [self.issue("a-1")]
        found, hours, unrated = self.found(*tracker)
        self.assertAlmostEqual(found[0].points, 0.03)
        self.assertEqual(report(found, hours, tracker, -math.inf, math.inf, unrated)[-1], "no rate for claude-next-9: its calls are left out")


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    sys.exit(main(sys.argv[1:]))
