#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Each offering's outcome and cost per work kind, so the human orders a route's candidates from evidence.

A route in loop.toml lists the offerings able to do a kind of work, cheapest capable first
(design/loops-select-by-work-kind-and-stage/). Which offering is capable, and which is cheapest for
what it lands, is read here from the loop's session record, logs/loop/sessions.sqlite at the project
root (its columns are in the opening comment of tools/loop.py), and from the Beads tree.

A leaf is an issue the record has a session for that is not an epic, a decision or a review. The
offering that took it is the one its first round ran on, and its work kind the one the loop classified
at claim, or its `kind:` label when no session names one. A leaf is counted in the period when its
first round started in it; what became of it is read as of now. For each work kind and offering:

- taken: the leaves it took;
- landed: those closed on a commit (a close reason naming a SHA);
- first: those landed with no round on them reporting `Retry:`, so no attempt ended at its bound;
- escalated: those with a round on them reporting `Retry:`, whichever offering ran the retry;
- refuted: those landed whose epic had a review close `refuted` after the leaf closed, the epic the
  leaf served being sent back;
- weighted and points a landed leaf: every session recorded under the taken leaves, on any offering,
  prover, retry and skeptic included, over the landed ones, in millions of plan-weighted tokens and in
  weekly points of the Claude plan. An offering that hands its hard leaves to a dearer one carries
  that cost.

Points are weekly points of the Claude plan: weighted tokens at the rates tools/leaf-cost.py measured
(RATES there, one place), by the model id the session's model flag stands for (MODEL_IDS). A session
on another harness has no such rate. An agy session adds no points and its model is named on a last
line; its offering's points are `-` when none of its sessions has a rate. A grok session is not
unrated. The plan is a flat subscription, so it has no weekly points, and its cost is the weighted
column, in millions of weighted tokens. The API-equivalent dollars Grok stamps on a session are list
price, which is not a unit here. Sessions on no leaf (reviews, epic rounds, and the unrouted loop's
rounds, which claim their own issue and record none) follow, one line per offering: sessions, of them
limited, and weighted tokens.

usage: tools/offering-report.py [--since WHEN] [--until WHEN]   (local time: 2026-11-12 or 2026-11-12T20:00)
       tools/offering-report.py --test                          (this script's own tests)
Exits 0, or 1 when bd list fails.
"""
import argparse
import json
import math
import re
import runpy
import subprocess
import sys
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path

sys.dont_write_bytecode = True

TREE = Path(__file__).resolve().parents[1]
ROOT = TREE.parent
RECORD = ROOT / "logs" / "loop"
LOOP = Path(__file__).with_name("loop.py")
RATES = runpy.run_path(str(Path(__file__).with_name("leaf-cost.py")))["RATES"]
# The model id each Claude model flag of loop.toml resolves to today.
MODEL_IDS = {"opus": "claude-opus-5-5", "fable": "claude-fable-5-2"}
NOT_LEAVES = ("epic", "decision")
COMMIT = re.compile(r"\b[0-9a-f]{7,40}\b")


def rate(session):
    """Weekly points a million weighted tokens of the session's model, or None."""
    if session["harness"] != "claude" or not session["model"]:
        return None
    model = MODEL_IDS.get(session["model"], session["model"])
    return RATES[model][0] if model in RATES else None


def closed_at(issue):
    return datetime.fromisoformat(issue["closed_at"]).timestamp() if issue.get("closed_at") else None


def landed(issue):
    return issue["status"] == "closed" and COMMIT.search(issue.get("close_reason") or "") is not None


def a_leaf(issue):
    return issue.get("issue_type") not in NOT_LEAVES and "review" not in (issue.get("labels") or [])


def label_kind(issue):
    return next((label[5:] for label in issue.get("labels") or [] if label.startswith("kind:")), None)


def refutations(tracker):
    """For each epic, the times its reviews closed refuted."""
    times = {}
    for issue in tracker:
        if (issue["status"] == "closed" and "review" in (issue.get("labels") or [])
                and (issue.get("close_reason") or "").startswith("refuted") and issue.get("parent")):
            times.setdefault(issue["parent"], []).append(closed_at(issue))
    return times


def report(sessions, tracker, since=-math.inf, until=math.inf):
    """The lines of the report over the sessions of the record and the issues of the tracker."""
    issues = {issue["id"]: issue for issue in tracker}
    refuted = refutations(tracker)
    by_leaf, other, unrated = {}, [], set()
    saw_grok = False
    for session in sorted(sessions, key=lambda session: session["started"]):
        if session["harness"] == "grok":
            saw_grok = True
        elif rate(session) is None:
            unrated.add(f"{session['harness']} {session['model'] or 'default'}")
        issue = issues.get(session["issue"])
        if issue is not None and a_leaf(issue):
            by_leaf.setdefault(session["issue"], []).append(session)
        elif since <= session["started"] < until:
            other.append(session)
    rows = {}
    for id, worked in by_leaf.items():
        rounds = [session for session in worked if session["session"] == "round"]
        if not rounds or not since <= rounds[0]["started"] < until:
            continue
        issue = issues[id]
        kind = next((session["work_kind"] for session in worked if session["work_kind"]), None) or label_kind(issue) or "-"
        row = rows.setdefault((kind, rounds[0]["offering"] or "-"), dict(
            taken=0, landed=0, first=0, escalated=0, refuted=0, weighted=0.0, points=0.0, rated=False))
        escalated = any(session["retry"] for session in rounds)
        row["taken"] += 1
        row["escalated"] += escalated
        if landed(issue):
            row["landed"] += 1
            row["first"] += not escalated
            row["refuted"] += any(time > closed_at(issue) for time in refuted.get(issue.get("parent"), ()))
        for session in worked:
            row["weighted"] += session["weighted"]
            if rate(session) is not None:
                row["points"] += rate(session) * session["weighted"] / 1e6
                row["rated"] = True
    lines = ["leaves by the work kind and the offering that took them; cost a landed leaf, every session counted, "
             "in millions of weighted tokens and weekly points of the Claude plan",
             f"{'kind':<8}{'offering':<20}{'taken':>6}{'landed':>7}{'first':>6}{'escalated':>10}{'refuted':>8}"
             f"{'weighted':>10}{'points':>8}"]
    for (kind, offering), row in sorted(rows.items()):
        each = (lambda total: total / row["landed"]) if row["landed"] else None
        lines.append(
            f"{kind:<8}{offering:<20}{row['taken']:>6}{row['landed']:>7}{row['first']:>6}{row['escalated']:>10}"
            f"{row['refuted']:>8}{(f'{each(row['weighted']) / 1e6:.2f}' if each else '-'):>10}"
            f"{(f'{each(row['points']):.3f}' if each and row['rated'] else '-'):>8}")
    offerings = {}
    for session in other:
        line = offerings.setdefault(session["offering"] or "-", [0, 0, 0.0])
        line[0] += 1
        line[1] += session["limited"]
        line[2] += session["weighted"]
    lines.append(f"{'on no leaf':<28}{'sessions':>9}{'limited':>8}{'weighted':>10}")
    lines += [f"{offering:<28}{count:>9}{limited:>8}{weighted / 1e6:>10.2f}"
              for offering, (count, limited, weighted) in sorted(offerings.items())]
    lines += [f"no rate for {model}: its sessions add no points" for model in sorted(unrated)]
    if saw_grok:
        lines.append("grok: a landed leaf's cost is the weighted column, in millions of weighted tokens; "
                     "the plan is a flat subscription, so no weekly points")
    return lines


def main(arguments):
    parser = argparse.ArgumentParser(description="Each offering's outcome and cost per work kind.")
    parser.add_argument("--since", type=datetime.fromisoformat, metavar="WHEN")
    parser.add_argument("--until", type=datetime.fromisoformat, metavar="WHEN")
    options = parser.parse_args(arguments)
    listed = subprocess.run(["bd", "list", "--all", "--json", "--limit", "0"], cwd=TREE, capture_output=True, text=True)
    if listed.returncode != 0:
        print(f"offering-report: bd list exited {listed.returncode}: {(listed.stderr or listed.stdout).strip()}", file=sys.stderr)
        return 1
    sessions = runpy.run_path(str(LOOP))["read_sessions"](RECORD)
    since = options.since.timestamp() if options.since else -math.inf
    until = options.until.timestamp() if options.until else math.inf
    print("\n".join(report(sessions, json.loads(listed.stdout), since, until)))
    return 0


class Tests(unittest.TestCase):
    NOON = datetime(2026, 11, 12, 12).timestamp()

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.folder = Path(directory.name)
        self.loop = runpy.run_path(str(LOOP))
        self.minute = 0

    def run_session(self, issue, offering, session="round", kind="tool", weighted=1_000_000, retry=None, limited=0, at=None):
        """One row as tools/loop.py writes it, on an offering of the loop.toml the tests assume."""
        harness, model = {"opus": ("claude", "opus"), "fable-xhigh": ("claude", "fable"),
                          "carbon-high": ("agy", "gemini-4-carbon-high"),
                          "grok-high": ("grok", "grok-4.7")}[offering]
        self.minute += 1
        self.loop["record_session"](self.folder, {
            "actor": "loop-1", "session": session, "issue": issue, "work_kind": kind, "route": kind, "offering": offering,
            "harness": harness, "model": model, "effort": None, "started": (self.NOON if at is None else at) + 60 * self.minute,
            "minutes": 10.0, "turns": 30, "weighted": weighted, "exit": 0, "error": 0, "limited": limited,
            "loop": "continue" if session == "round" else None, "prover": None, "retry": retry, "skeptic": None})

    def issue(self, id, reason="abc1234: landed", status="closed", labels=("kind:tool",), closed=None, type="task"):
        stamp = datetime.fromtimestamp(self.NOON + 86400 if closed is None else closed, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        return {"id": id, "status": status, "issue_type": type, "labels": list(labels), "close_reason": reason,
                "closed_at": stamp if status == "closed" else None, "parent": id.rsplit(".", 1)[0]}

    def lines(self, tracker, **window):
        return report(self.loop["read_sessions"](self.folder), tracker, **window)

    def row(self, lines, kind, offering):
        return next(line.split()[2:] for line in lines if line.split()[:2] == [kind, offering])

    def test_a_landed_an_escalated_and_a_refuted_leaf_on_two_offerings(self):
        # On carbon-high: a-1.1 lands first time; a-1.2 ends its attempt, Fable retries and lands it;
        # a-1.3 lands, then a review of a-1 closes refuted after it.
        self.run_session("a-1.1", "carbon-high", weighted=2_000_000)
        self.run_session("a-1.2", "carbon-high", retry="a-1.2", weighted=3_000_000)
        self.run_session("a-1.2", "fable-xhigh", weighted=1_000_000)
        self.run_session("a-1.3", "carbon-high", weighted=1_000_000)
        # On opus: b-1.1 lands with a prover hand-off; b-1.2 is discarded without a commit.
        self.run_session("b-1.1", "opus", weighted=1_000_000)
        self.run_session("b-1.1", "fable-xhigh", session="prover", weighted=2_000_000)
        self.run_session("b-1.2", "opus", weighted=500_000)
        tracker = [self.issue("a-1.1"), self.issue("a-1.2"), self.issue("a-1.3", closed=self.NOON + 3600),
                   self.issue("a-1.9", reason="refuted: criterion 2", labels=("review",), closed=self.NOON + 7200),
                   self.issue("b-1.1"), self.issue("b-1.2", reason="Already true")]
        lines = self.lines(tracker)
        self.assertEqual(lines[1].split(), ["kind", "offering", "taken", "landed", "first", "escalated", "refuted", "weighted", "points"])
        # a-1.1 lands before the review, so only a-1.3 counts as refuted; a-1.2's points are Fable's retry.
        self.assertEqual(self.row(lines, "tool", "carbon-high"), ["3", "3", "2", "1", "1", "2.33", f"{0.57 / 3:.3f}"])
        self.assertEqual(self.row(lines, "tool", "opus"), ["2", "1", "1", "0", "0", "3.50", f"{0.12 * 1.5 + 0.57 * 2:.3f}"])
        self.assertIn("no rate for agy gemini-4-carbon-high: its sessions add no points", lines)

    def test_the_kind_is_the_loops_or_the_label_and_an_offering_without_a_rate_has_no_points(self):
        self.run_session("a-1.1", "carbon-high", kind=None)
        self.run_session("a-1.2", "carbon-high", kind="spec")
        lines = self.lines([self.issue("a-1.1", labels=("kind:arch",)), self.issue("a-1.2")])
        self.assertEqual(self.row(lines, "arch", "carbon-high")[-1], "-")
        self.assertEqual(self.row(lines, "spec", "carbon-high")[:2], ["1", "1"])

    def test_a_leaf_counts_in_the_period_its_first_round_started_in(self):
        self.run_session("a-1.1", "opus", at=self.NOON - 86400)
        self.run_session("a-1.1", "opus", at=self.NOON)
        self.run_session("a-1.2", "opus", at=self.NOON)
        lines = self.lines([self.issue("a-1.1"), self.issue("a-1.2", status="open")], since=self.NOON - 3600)
        self.assertEqual(self.row(lines, "tool", "opus")[:3], ["1", "0", "0"])

    def test_a_grok_offering_costs_weighted_tokens_and_is_not_unrated(self):
        # g-1.1 lands; g-1.2 ends its attempt and lands; g-1.3 lands, then a review of g-1 closes refuted after it.
        self.run_session("g-1.1", "grok-high", weighted=2_000_000)
        self.run_session("g-1.2", "grok-high", retry="g-1.2", weighted=1_000_000)
        self.run_session("g-1.3", "grok-high", weighted=3_000_000)
        self.run_session("c-1.1", "carbon-high", weighted=1_000_000)
        tracker = [self.issue("g-1.1"), self.issue("g-1.2"), self.issue("g-1.3", closed=self.NOON + 3600),
                   self.issue("g-1.9", reason="refuted: criterion 1", labels=("review",), closed=self.NOON + 7200),
                   self.issue("c-1.1")]
        lines = self.lines(tracker)
        self.assertEqual(self.row(lines, "tool", "grok-high"), ["3", "3", "2", "1", "1", "2.00", "-"])
        self.assertFalse(any(line.startswith("no rate for grok") for line in lines))
        self.assertIn("no rate for agy gemini-4-carbon-high: its sessions add no points", lines)
        self.assertIn("grok: a landed leaf's cost is the weighted column, in millions of weighted tokens; "
                      "the plan is a flat subscription, so no weekly points", lines)

    def test_sessions_on_no_leaf_are_counted_by_offering(self):
        self.run_session("a-1.9", "opus", session="skeptic", kind="review", limited=1, weighted=4_000_000)
        self.run_session(None, "opus", kind=None, weighted=1_000_000)
        self.run_session("a-1", "fable-xhigh", kind=None, weighted=2_000_000)
        lines = self.lines([self.issue("a-1.9", labels=("review",)), self.issue("a-1", type="epic")])
        tail = lines[lines.index(next(line for line in lines if line.startswith("on no leaf"))) + 1:]
        self.assertEqual([line.split() for line in tail], [["fable-xhigh", "1", "0", "2.00"], ["opus", "2", "1", "5.00"]])
        self.assertEqual(lines[2].split()[0], "on")


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    sys.exit(main(sys.argv[1:]))
