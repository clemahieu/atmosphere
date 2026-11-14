#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Each offering's outcome and cost per work kind, so the human orders a route's candidates from evidence.

A route in loop.toml lists the offerings able to do a kind of work, cheapest capable first
(design/loops-select-by-work-kind-and-stage/). Which offering is capable, and which is cheapest for
what it lands, is read here from the loop's session record, logs/loop/sessions.sqlite at the project
root (its columns are in the opening comment of tools/loop.py), and from the Beads tree.

A leaf is an issue the record has a session for that is not an epic, a decision or a review, and also
an issue that is an epic now whose sessions carry a leaf kind: the kind the loop classified when it
took the issue, before a round split it. The offering that took it is the one its first round ran on,
or its first session when it has no round (a hand-off on an issue the round named and this loop had
not claimed). Its work kind is the one recorded on a session, or its `kind:` label when none names
one, so a hand-off recorded before the loop classified such sessions still lands on a line. A leaf is
counted in the period when the session that took it started; what became of it is read as of now. An
epic is not a landed leaf, whatever its close reason names. For each work kind and offering:

- taken: the leaves it took;
- landed: those that are not epics and closed on a commit reachable from main: a close reason with a
  run of 7 to 40 hex digits that starts a commit `git rev-list main` gives, so a pid in an actor's
  name, a count or a commit main does not contain is not one (`landed` of tools/leaf-cost.py, the
  one rule both tools count by);
- first: those landed with no round on them reporting `Retry:`, so no attempt ended at its bound;
- escalated: those with a round on them reporting `Retry:`, whichever offering ran the retry;
- refuted: those landed whose close reason names a commit that the `Origin:` line of a leaf labelled
  `refuted` names, one a prefix of the other, so a refutation is charged to the offering that wrote
  what it cites and not to every offering that worked in the epic; any refuted leaf counts, whenever
  it was filed. After every other line, one line names the refuted leaves filed in the period that
  are on no row: `Origin: none` (nothing implemented the criterion, the split's gap), `Origin: base`
  (main failed by itself), no `Origin:` line (filed before the line existed), and an origin naming no
  landed leaf counted on a row. The rows and that line account for every refuted leaf filed in the
  period;
- weighted and points a landed leaf: every session recorded under the taken leaves, on any offering,
  prover, retry and skeptic included, over the landed ones, in millions of plan-weighted tokens and in
  weekly points of the Claude plan. An offering that hands its hard leaves to a dearer one carries
  that cost. The sum column is that total, in millions, so a row that landed nothing still shows what
  it spent.

A leaf's rounds are its sessions of kind round, in the order they started. Each after the first is given
one cause, the first of these its window shows, the window running from the start of the round before
it to its own start; a gate log counts by when it was last written, a dependency by the created_at of
its edge in bd list --json:

- prover: its route is needs-land, or the round before reported `Prover:`;
- bound: its route is retry, or the round before reported `Retry:`;
- base: a gate log of the leaf, logs/<id>-gate.log or logs/<id>-gate-<n>.log, holds `fails the gate by
  itself` or a line `exit 4`, or the leaf came to wait on an issue titled `main at <sha> fails the gate
  by itself`, the bug a round files for a main that fails by itself. A landing overwrites the leaf's
  gate log, so the bug is often the evidence left;
- fault: such a log holds a line `exit 1`, the change at fault;
- conflict: such a log holds a line `exit 3`, a rebase that stopped;
- waited: the leaf came to wait on another issue;
- duplicate: it overlaps in time another round on the leaf under another actor;
- recovered: the round before exited non-zero, ended in an error or gave no report;
- other: none of these.

One row per work kind and offering gives the rounds beyond the first and each cause's share of them,
and one line per leaf with more than one round names each such round's cause. A session a signal
ended is recorded with weighted 0: its tokens are in the token ledger (tools/token-ledger.py), not in
the record, so the cost columns leave them out.

Points are weekly points of the Claude plan: weighted tokens at the rates tools/leaf-cost.py measured
(RATES there, one place), by the model id the session's model flag stands for (MODEL_IDS there). A session
on another harness has no such rate. An agy session adds no points and its model is named on a last
line; its offering's points are `-` when none of its sessions has a rate. A grok session is not
unrated. The plan is a flat subscription, so it has no weekly points, and its cost is the weighted
column, in millions of weighted tokens. The API-equivalent dollars Grok stamps on a session are list
price, which is not a unit here. A review is an issue labelled `review`. The offering that took it is
the one its first round ran on, or its first session when it has no round, and its cost is every
session on it, the skeptic included. One row per such offering: reviews taken, closed on a skeptic
pass, closed refuted, and that cost. Sessions on no leaf (epic rounds, decisions, and the unrouted
loop's rounds, which claim their own issue and record none) follow, one line per offering: sessions,
of them limited, and weighted tokens. The sum column, the review weighted column and those lines are
printed in hundredths of a million apportioned so the printed figures add to the accounted line:
each starts at the hundredths its own tokens would print, and a hundredth moves onto the rows whose
rounding discarded the most until the sum matches. Rounding each row on its own does not add up.
The accounted line, over the whole record, is every session once.

usage: tools/offering-report.py [--since WHEN] [--until WHEN]   (local time: 2026-11-12 or 2026-11-12T20:00)
       tools/offering-report.py --test                          (this script's own tests)
Exits 0, or 1 when bd list fails.
"""
import argparse
import json
import math
import os
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
LOGS = ROOT / "logs"
LOOP = Path(__file__).with_name("loop.py")
LEAF_COST = runpy.run_path(str(Path(__file__).with_name("leaf-cost.py")))
FLAG_RATE, LANDED, MAIN_COMMITS, HEX = (LEAF_COST["flag_rate"], LEAF_COST["landed"], LEAF_COST["main_commits"],
                                       LEAF_COST["HEX"])
NOT_LEAVES = ("epic", "decision")
LEAF_KINDS = ("tool", "sys", "proof", "spec", "arch")
# Why a leaf took a round after its first, in the order they are tried (the opening comment says each).
CAUSES = ("prover", "bound", "base", "fault", "conflict", "waited", "duplicate", "recovered", "other")
BASE_BUG = re.compile(r"main at [0-9a-f]{7,40} fails the gate by itself")
BASE_LOG = re.compile(r"fails the gate by itself|^exit 4$", re.M)
FAULT_LOG = re.compile(r"^exit 1$", re.M)
CONFLICT_LOG = re.compile(r"^exit 3$", re.M)
ORIGIN = re.compile(r"^Origin:[ \t]*(.*?)[ \t]*$", re.M)


def rate(session):
    """Weekly points a million weighted tokens of the session's model, or None."""
    return FLAG_RATE(session["harness"], session["model"])


def closed_at(issue):
    return datetime.fromisoformat(issue["closed_at"]).timestamp() if issue.get("closed_at") else None


def label_kind(issue):
    return next((label[5:] for label in issue.get("labels") or [] if label.startswith("kind:")), None)


def created_at(issue):
    return datetime.fromisoformat(issue["created_at"]).timestamp()


def origin(issue):
    """A refuted leaf's `Origin:` line: "none", "base", the commits it names as a list, or None when it has none."""
    found = ORIGIN.findall(issue.get("description") or "")
    if not found:
        return None
    return found[-1] if found[-1] in ("none", "base") else HEX.findall(found[-1])


def names_origin(reason, shas):
    """Whether a close reason names one of `shas`: a run of its hex digits and a sha, one a prefix of the other."""
    return any(run.startswith(sha) or sha.startswith(run) for run in HEX.findall(reason) for sha in shas)


def is_review(issue):
    return "review" in (issue.get("labels") or []) or label_kind(issue) == "review"


def keeps_leaf_kind(worked):
    """An epic a round split: its sessions still carry the leaf kind it was taken as."""
    return any(session["work_kind"] in LEAF_KINDS for session in worked)


def taker_of(worked):
    """The session that took the issue: its first round, or its first session when a hand-off is all it has."""
    rounds = [session for session in worked if session["session"] == "round"]
    return rounds[0] if rounds else worked[0]


def gate_logs(logs, id):
    """Each gate log of the issue, logs/<id>-gate.log and logs/<id>-gate-<n>.log, as (modified, text)."""
    found = [Path(logs) / f"{id}-gate.log", *sorted(Path(logs).glob(f"{id}-gate-*.log"))]
    return [(path.stat().st_mtime, path.read_text(errors="replace")) for path in found if path.is_file()]


def dependencies_taken(issue):
    """Each issue `issue` came to wait on, as (when the edge was made, the issue waited on)."""
    return [(datetime.fromisoformat(edge["created_at"]).timestamp(), edge["depends_on_id"])
            for edge in issue.get("dependencies") or [] if edge.get("type") == "blocks"]


def ended(session):
    return session["started"] + 60 * (session["minutes"] or 0)


def round_causes(rounds, issue, issues, logs):
    """The cause of each of a leaf's rounds after its first, from what was written in its window: from the
    start of the round before it to its own start."""
    logged = gate_logs(logs, issue["id"])
    taken = dependencies_taken(issue)
    causes = []
    for before, this in zip(rounds, rounds[1:]):
        def within(when):
            return before["started"] <= when < this["started"]
        texts = [text for when, text in logged if within(when)]
        waited_on = [issues.get(other, {}).get("title") or "" for when, other in taken if within(when)]
        if this["route"] == "needs-land" or before["prover"]:
            causes.append("prover")
        elif this["route"] == "retry" or before["retry"]:
            causes.append("bound")
        elif any(BASE_LOG.search(text) for text in texts) or any(BASE_BUG.match(title) for title in waited_on):
            causes.append("base")
        elif any(FAULT_LOG.search(text) for text in texts):
            causes.append("fault")
        elif any(CONFLICT_LOG.search(text) for text in texts):
            causes.append("conflict")
        elif waited_on:
            causes.append("waited")
        elif any(other is not this and other["actor"] != this["actor"]
                 and other["started"] < ended(this) and this["started"] < ended(other) for other in rounds):
            causes.append("duplicate")
        elif before["exit"] or before["error"] or before["loop"] is None:
            causes.append("recovered")
        else:
            causes.append("other")
    return causes


def millions(tokens):
    """`tokens` as millions, to 0.01."""
    return f"{tokens / 1e6:.2f}"


def printed_hundredths(tokens):
    """The hundredths of a million that `millions` shows, as an int."""
    whole, frac = millions(tokens).split(".")
    return int(whole) * 100 + int(frac)


def apportioned(parts, total):
    """Each part as millions to 0.01, the strings adding to `millions(total)`.

    A part starts at the hundredths printing it on its own would show. That can miss the total's
    hundredths, so the difference moves a hundredth at a time onto the parts whose own rounding
    discarded the most in that direction. A part of zero stays 0.00.
    """
    target = printed_hundredths(total)
    got = [printed_hundredths(part) for part in parts]
    delta = target - sum(got)
    step = 1 if delta > 0 else -1

    def discarded(part, shown):
        return part / 10_000 - shown

    while delta != 0:
        way = [i for i in range(len(parts)) if parts[i] != 0 and got[i] + step >= 0]
        assert way, "the printed total's hundredths have nowhere to land"
        pick = max(way, key=lambda i: step * discarded(parts[i], got[i]))
        got[pick] += step
        delta -= step
    return [f"{value / 100:.2f}" for value in got]


def report(sessions, tracker, commits, since=-math.inf, until=math.inf, logs=LOGS):
    """The lines of the report over the sessions of the record and the issues of the tracker;
    `commits` are main's, which a landed leaf's close reason names one of."""
    issues = {issue["id"]: issue for issue in tracker}
    refuted_leaves = [issue for issue in tracker if "refuted" in (issue.get("labels") or [])]
    origins = {issue["id"]: origin(issue) for issue in refuted_leaves}
    blamed = set()
    by_issue, other = {}, []
    unrated = set()
    saw_grok = False
    for session in sorted(sessions, key=lambda session: session["started"]):
        if session["harness"] == "grok":
            saw_grok = True
        elif rate(session) is None:
            unrated.add(f"{session['harness']} {session['model'] or 'default'}")
        if session["issue"] is None or session["issue"] not in issues:
            other.append(session)
        else:
            by_issue.setdefault(session["issue"], []).append(session)
    leaves, reviews = {}, {}
    for id, worked in by_issue.items():
        issue = issues[id]
        if is_review(issue):
            reviews[id] = worked
        elif issue.get("issue_type") not in NOT_LEAVES or (
                issue.get("issue_type") == "epic" and keeps_leaf_kind(worked)):
            leaves[id] = worked
        else:
            other.extend(worked)
    shown = [0, 0.0]

    def place(worked):
        shown[0] += len(worked)
        shown[1] += sum(session["weighted"] or 0 for session in worked)

    def spend(row, session):
        row["weighted"] += session["weighted"] or 0
        if rate(session) is not None:
            row["points"] += rate(session) * (session["weighted"] or 0) / 1e6
            row["rated"] = True

    rows = {}
    caused = {}
    for id, worked in leaves.items():
        taker = taker_of(worked)
        if not since <= taker["started"] < until:
            continue
        issue = issues[id]
        kind = (next((session["work_kind"] for session in worked if session["work_kind"] in LEAF_KINDS), None)
                or label_kind(issue) or "-")
        row = rows.setdefault((kind, taker["offering"] or "-"), dict(
            taken=0, landed=0, first=0, escalated=0, refuted=0, weighted=0.0, points=0.0, rated=False,
            causes=dict.fromkeys(CAUSES, 0)))
        rounds = [session for session in worked if session["session"] == "round"]
        causes = round_causes(rounds, issue, issues, logs)
        for cause in causes:
            row["causes"][cause] += 1
        if causes:
            caused[id] = (kind, taker["offering"] or "-", causes)
        escalated = any(session["retry"] for session in rounds)
        did_land = LANDED(issue, commits)
        row["taken"] += 1
        row["escalated"] += escalated
        if did_land:
            row["landed"] += 1
            row["first"] += not escalated
            blames = [other for other, shas in origins.items()
                      if isinstance(shas, list) and names_origin(issue.get("close_reason") or "", shas)]
            row["refuted"] += bool(blames)
            blamed.update(blames)
        for session in worked:
            spend(row, session)
        place(worked)
    review_rows = {}
    for id, worked in reviews.items():
        taker = taker_of(worked)
        if not since <= taker["started"] < until:
            continue
        issue = issues[id]
        row = review_rows.setdefault(taker["offering"] or "-", dict(
            taken=0, passed=0, refuted=0, weighted=0.0, points=0.0, rated=False))
        reason = issue.get("close_reason") or ""
        row["taken"] += 1
        row["passed"] += reason.startswith("skeptic pass")
        row["refuted"] += reason.startswith("refuted")
        for session in worked:
            spend(row, session)
        place(worked)
    offerings = {}
    for session in other:
        if not since <= session["started"] < until:
            continue
        line = offerings.setdefault(session["offering"] or "-", [0, 0, 0.0])
        line[0] += 1
        line[1] += session["limited"]
        line[2] += session["weighted"] or 0
        place([session])
    leaf_order = sorted(rows)
    review_order = sorted(review_rows)
    other_order = sorted(offerings)
    parts = ([rows[key]["weighted"] for key in leaf_order]
             + [review_rows[key]["weighted"] for key in review_order]
             + [offerings[key][2] for key in other_order])
    shown_millions = apportioned(parts, shown[1])
    n_leaves, n_reviews = len(leaf_order), len(review_order)
    leaf_millions = shown_millions[:n_leaves]
    review_millions = shown_millions[n_leaves:n_leaves + n_reviews]
    other_millions = shown_millions[n_leaves + n_reviews:]
    lines = ["leaves by the work kind and the offering that took them; cost a landed leaf, every session counted, "
             "in millions of weighted tokens and weekly points of the Claude plan",
             f"{'kind':<8}{'offering':<20}{'taken':>6}{'landed':>7}{'first':>6}{'escalated':>10}{'refuted':>8}"
             f"{'weighted':>10}{'points':>8}{'sum':>8}"]
    for (kind, offering), millions_text in zip(leaf_order, leaf_millions):
        row = rows[(kind, offering)]
        each = (lambda total: total / row["landed"]) if row["landed"] else None
        lines.append(
            f"{kind:<8}{offering:<20}{row['taken']:>6}{row['landed']:>7}{row['first']:>6}{row['escalated']:>10}"
            f"{row['refuted']:>8}{(f'{each(row['weighted']) / 1e6:.2f}' if each else '-'):>10}"
            f"{(f'{each(row['points']):.3f}' if each and row['rated'] else '-'):>8}{millions_text:>8}")
    lines.append("rounds beyond a leaf's first, by the work kind and the offering that took the leaf, "
                 "each by its cause")
    lines.append(f"{'kind':<8}{'offering':<20}{'beyond':>7}" + "".join(f"{cause:>10}" for cause in CAUSES))
    for kind, offering in leaf_order:
        counts = rows[(kind, offering)]["causes"]
        lines.append(f"{kind:<8}{offering:<20}{sum(counts.values()):>7}"
                     + "".join(f"{counts[cause]:>10}" for cause in CAUSES))
    lines.append("leaves with more than one round: the leaf, its kind and offering, and the cause of each round after "
                 "its first")
    lines += [f"  {id} {kind} {offering}: {', '.join(causes)}" for id, (kind, offering, causes) in sorted(caused.items())]
    lines.append("reviews by the offering that took them; taken, closed on a skeptic pass, closed refuted, "
                 "and the cost of every session on them")
    lines.append(f"{'offering':<20}{'taken':>6}{'passed':>8}{'refuted':>8}{'weighted':>10}{'points':>8}")
    for offering, millions_text in zip(review_order, review_millions):
        row = review_rows[offering]
        lines.append(f"{offering:<20}{row['taken']:>6}{row['passed']:>8}{row['refuted']:>8}"
                     f"{millions_text:>10}{(f'{row['points']:.3f}' if row['rated'] else '-'):>8}")
    lines.append(f"{'on no leaf':<28}{'sessions':>9}{'limited':>8}{'weighted':>10}")
    lines += [f"{offering:<28}{offerings[offering][0]:>9}{offerings[offering][1]:>8}{millions_text:>10}"
              for offering, millions_text in zip(other_order, other_millions)]
    lines.append(f"accounted {shown[0]} sessions, {millions(shown[1])}M weighted")
    lines += [f"no rate for {model}: its sessions add no points" for model in sorted(unrated)]
    if saw_grok:
        lines.append("grok: a landed leaf's cost is the weighted column, in millions of weighted tokens; "
                     "the plan is a flat subscription, so no weekly points")
    on_no_row = {"origin none": [], "origin base": [], "no origin line": [], "origin names no leaf on a row": []}
    for issue in sorted(refuted_leaves, key=lambda issue: issue["id"]):
        shas = origins[issue["id"]]
        if not since <= created_at(issue) < until or issue["id"] in blamed:
            continue
        on_no_row["no origin line" if shas is None else f"origin {shas}" if isinstance(shas, str)
                  else "origin names no leaf on a row"].append(issue["id"])
    lines.append("refuted leaves on no row: " + "; ".join(f"{name} {' '.join(ids) or '-'}" for name, ids in on_no_row.items()))
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
    print("\n".join(report(sessions, json.loads(listed.stdout), MAIN_COMMITS(), since, until)))
    return 0


class Tests(unittest.TestCase):
    NOON = datetime(2026, 11, 12, 12).timestamp()
    # Main's commits as the tests assume them: the SHA the default close reason names, and another.
    COMMITS = ["abc1234" + "0" * 33, "def5678" + "0" * 33]

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.folder = Path(directory.name)
        self.loop = runpy.run_path(str(LOOP))
        self.minute = 0

    def run_session(self, issue, offering, session="round", kind="tool", weighted=1_000_000, retry=None, limited=0, at=None,
                    route=None, prover=None, actor="loop-1", minutes=10.0, exit=0, report="continue"):
        """One row as tools/loop.py writes it, on an offering of the loop.toml the tests assume. With `at`, the
        session starts then; otherwise a minute after the one before, from noon."""
        harness, model = {"opus": ("claude", "opus"), "opus-xhigh": ("claude", "opus"),
                          "fable-xhigh": ("claude", "fable"),
                          "carbon-high": ("agy", "gemini-4-carbon-high"),
                          "grok-high": ("grok", "grok-4.7")}[offering]
        self.minute += 1
        self.loop["record_session"](self.folder, {
            "actor": actor, "session": session, "issue": issue, "work_kind": kind, "route": route or kind, "offering": offering,
            "harness": harness, "model": model, "effort": None, "started": self.NOON + 60 * self.minute if at is None else at,
            "minutes": minutes, "turns": 30, "weighted": weighted, "exit": exit, "error": 0, "limited": limited,
            "loop": report if session == "round" else None, "prover": prover, "retry": retry, "skeptic": None})

    def issue(self, id, reason="abc1234: landed", status="closed", labels=("kind:tool",), closed=None, type="task",
              title="", needs=(), description="", created=None):
        """A tracker entry as bd list --json gives it; `needs` holds (issue depended on, epoch seconds the edge was made)."""
        def stamp(at):
            return datetime.fromtimestamp(at, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        return {"id": id, "title": title, "status": status, "issue_type": type, "labels": list(labels), "close_reason": reason,
                "description": description, "created_at": stamp(self.NOON if created is None else created),
                "closed_at": stamp(self.NOON + 86400 if closed is None else closed) if status == "closed" else None,
                "parent": id.rsplit(".", 1)[0],
                "dependencies": [{"issue_id": id, "depends_on_id": other, "type": "blocks",
                                  "created_at": stamp(made)}
                                 for other, made in needs]}

    def lines(self, tracker, **window):
        return report(self.loop["read_sessions"](self.folder), tracker, self.COMMITS, logs=self.folder / "logs", **window)

    def gate_log(self, name, text, at):
        """logs/<name> holding `text`, last written at epoch seconds `at`."""
        path = self.folder / "logs" / name
        path.parent.mkdir(exist_ok=True)
        path.write_text(text)
        os.utime(path, (at, at))

    def cause_row(self, lines, kind, offering):
        header = next(i for i, line in enumerate(lines) if line.startswith("rounds beyond"))
        self.assertEqual(lines[header + 1].split(), ["kind", "offering", "beyond", *CAUSES])
        return next(line.split()[2:] for line in lines[header + 2:] if line.split()[:2] == [kind, offering])

    def test_each_round_after_a_leafs_first_has_the_first_cause_its_window_shows(self):
        hour = 3600

        def rounds(id, *rows):
            """Rounds on `id` an hour apart from noon, each row the run_session options of one."""
            for n, options in enumerate(rows):
                self.run_session(id, "opus", at=self.NOON + n * hour, **options)

        rounds("t-1.1", {})
        rounds("t-1.2", {"prover": "t-1.2"}, {"route": "needs-land"})
        rounds("t-1.3", {"retry": "t-1.3"}, {"route": "retry"})
        rounds("t-1.4", {}, {})
        self.gate_log("t-1.4-gate.log", "land: main at 0123456789ab fails the gate by itself\nexit 4\n", self.NOON + hour / 2)
        rounds("t-1.5", {}, {})
        rounds("t-1.6", {}, {})
        self.gate_log("t-1.6-gate.log", "land: the change is at fault\nexit 1\n", self.NOON + hour / 2)
        rounds("t-1.7", {}, {}, {})
        self.gate_log("t-1.7-gate-1.log", "land: a conflict\nexit 3\n", self.NOON + hour / 2)
        self.gate_log("t-1.7-gate.log", "land: the change is at fault\nexit 1\n", self.NOON + 3 * hour / 2)
        rounds("t-1.8", {}, {})
        # t-1.9's second round starts while another actor's first still runs.
        rounds("t-1.9", {"minutes": 60.0})
        self.run_session("t-1.9", "opus", actor="loop-2", at=self.NOON + 300)
        rounds("t-1.10", {"exit": 143, "report": None}, {})
        # t-1.11's evidence was written before its first round, so it explains neither.
        rounds("t-1.11", {}, {})
        self.gate_log("t-1.11-gate.log", "land: main at 0123456789ab fails the gate by itself\nexit 4\n", self.NOON - hour)
        # t-1.12's third round starts inside its second, under the same actor: not a duplicate.
        rounds("t-1.12", {}, {})
        self.run_session("t-1.12", "opus", at=self.NOON + hour + 60)
        tracker = [self.issue(f"t-1.{n}") for n in (1, 2, 3, 4, 6, 7, 9, 10, 12)] + [
            self.issue("t-1.20", title="main at 0123456789ab fails the gate by itself"), self.issue("t-1.21"),
            self.issue("t-1.5", needs=[("t-1.20", self.NOON + hour / 2)]),
            self.issue("t-1.8", needs=[("t-1.21", self.NOON + hour / 2)]),
            self.issue("t-1.11", needs=[("t-1.20", self.NOON - hour)])]
        lines = self.lines(tracker)
        row = self.cause_row(lines, "tool", "opus")
        counts = dict(zip(CAUSES, map(int, row[1:])))
        self.assertEqual(counts, {"prover": 1, "bound": 1, "base": 2, "fault": 2, "conflict": 1, "waited": 1,
                                  "duplicate": 1, "recovered": 1, "other": 3})
        self.assertEqual(int(row[0]), sum(counts.values()))
        listed = next(i for i, line in enumerate(lines) if line.startswith("leaves with more"))
        causes = {}
        for line in lines[listed + 1:]:
            if not line.startswith("  "):
                break
            leaf, said = line.split(": ")
            causes[leaf.split()[0]] = said
        self.assertEqual(causes, {
            "t-1.2": "prover", "t-1.3": "bound", "t-1.4": "base", "t-1.5": "base", "t-1.6": "fault",
            "t-1.7": "conflict, fault", "t-1.8": "waited", "t-1.9": "duplicate", "t-1.10": "recovered",
            "t-1.11": "other", "t-1.12": "other, other"})

    def test_a_leaf_with_one_round_adds_to_no_cause(self):
        self.run_session("a-1.1", "opus", kind="sys")
        self.run_session("a-1.1", "fable-xhigh", session="prover", kind="sys")
        lines = self.lines([self.issue("a-1.1")])
        self.assertEqual(self.cause_row(lines, "sys", "opus"), ["0"] * (1 + len(CAUSES)))

    def row(self, lines, kind, offering):
        return next(line.split()[2:] for line in lines if line.split()[:2] == [kind, offering])

    def test_a_landed_an_escalated_and_a_refuted_leaf_on_two_offerings(self):
        # On carbon-high: a-1.1 lands first time; a-1.2 ends its attempt, Fable retries and lands it;
        # a-1.3 lands on def5678, which a refuted leaf's Origin line names.
        self.run_session("a-1.1", "carbon-high", weighted=2_000_000)
        self.run_session("a-1.2", "carbon-high", retry="a-1.2", weighted=3_000_000)
        self.run_session("a-1.2", "fable-xhigh", weighted=1_000_000)
        self.run_session("a-1.3", "carbon-high", weighted=1_000_000)
        # On opus: b-1.1 lands with a prover hand-off; b-1.2 is discarded without a commit.
        self.run_session("b-1.1", "opus", weighted=1_000_000)
        self.run_session("b-1.1", "fable-xhigh", session="prover", weighted=2_000_000)
        self.run_session("b-1.2", "opus", weighted=500_000)
        tracker = [self.issue("a-1.1"), self.issue("a-1.2"), self.issue("a-1.3", reason="def5678: landed"),
                   self.issue("a-1.10", status="open", labels=("refuted",), description="Refuted.\nOrigin: def5678"),
                   self.issue("b-1.1"), self.issue("b-1.2", reason="Already true")]
        lines = self.lines(tracker)
        self.assertEqual(lines[1].split(),
                         ["kind", "offering", "taken", "landed", "first", "escalated", "refuted", "weighted", "points", "sum"])
        # Only a-1.3 counts as refuted; a-1.2's points are Fable's retry.
        self.assertEqual(self.row(lines, "tool", "carbon-high"), ["3", "3", "2", "1", "1", "2.33", f"{0.57 / 3:.3f}", "7.00"])
        self.assertEqual(self.row(lines, "tool", "opus"), ["2", "1", "1", "0", "0", "3.50", f"{0.12 * 1.5 + 0.57 * 2:.3f}", "3.50"])
        self.assertIn("no rate for agy gemini-4-carbon-high: its sessions add no points", lines)

    def test_a_leaf_is_refuted_when_a_refuted_leafs_origin_names_its_commit(self):
        # Two leaves of e-1 land on different offerings, and e-1's review closes refuted after both.
        self.run_session("e-1.1", "opus")
        self.run_session("e-1.2", "carbon-high")
        tracker = [self.issue("e-1.1", reason="abc1234: landed", closed=self.NOON + 3600),
                   self.issue("e-1.2", reason="def5678: landed", closed=self.NOON + 3600),
                   self.issue("e-1.9", reason="refuted: criteria 1 to 4", labels=("review",), closed=self.NOON + 7200),
                   # The Origin names the first leaf's commit by a longer prefix than its close reason does.
                   self.issue("e-1.10", status="open", labels=("refuted",),
                              description="Criterion 1 fails.\nThe cited line.\nOrigin: 9999999, abc12340"),
                   self.issue("e-1.11", status="open", labels=("refuted",), description="Criterion 2.\nOrigin: none"),
                   self.issue("e-1.12", status="open", labels=("refuted",), description="Criterion 3.\nOrigin: base"),
                   self.issue("e-1.13", status="open", labels=("refuted",), description="Criterion 4, filed before the line."),
                   # Filed before the period: on no line.
                   self.issue("e-1.14", status="open", labels=("refuted",), description="Origin: none", created=self.NOON - 86400)]
        lines = self.lines(tracker, since=self.NOON - 3600)
        self.assertEqual(self.row(lines, "tool", "opus")[:5], ["1", "1", "1", "0", "1"])
        self.assertEqual(self.row(lines, "tool", "carbon-high")[:5], ["1", "1", "1", "0", "0"])
        self.assertEqual(lines[-1], "refuted leaves on no row: origin none e-1.11; origin base e-1.12; "
                                    "no origin line e-1.13; origin names no leaf on a row -")
        self.assertFalse(any("e-1.10" in line or "e-1.14" in line for line in lines))

    def test_a_refuted_leaf_whose_origin_names_no_landed_leaf_is_on_the_last_line(self):
        self.run_session("e-1.1", "opus")
        tracker = [self.issue("e-1.1"),
                   self.issue("e-1.10", status="open", labels=("refuted",), description="Refuted.\nOrigin: 7777777")]
        lines = self.lines(tracker)
        self.assertEqual(self.row(lines, "tool", "opus")[4], "0")
        self.assertEqual(lines[-1], "refuted leaves on no row: origin none -; origin base -; no origin line -; "
                                    "origin names no leaf on a row e-1.10")

    def test_the_kind_is_the_loops_or_the_label_and_an_offering_without_a_rate_has_no_points(self):
        self.run_session("a-1.1", "carbon-high", kind=None)
        self.run_session("a-1.2", "carbon-high", kind="spec")
        lines = self.lines([self.issue("a-1.1", labels=("kind:arch",)), self.issue("a-1.2")])
        self.assertEqual(self.row(lines, "arch", "carbon-high")[-2], "-")
        self.assertEqual(self.row(lines, "spec", "carbon-high")[:2], ["1", "1"])

    def test_a_leaf_counts_in_the_period_its_first_round_started_in(self):
        self.run_session("a-1.1", "opus", at=self.NOON - 86400)
        self.run_session("a-1.1", "opus", at=self.NOON)
        self.run_session("a-1.2", "opus", at=self.NOON)
        lines = self.lines([self.issue("a-1.1"), self.issue("a-1.2", status="open")], since=self.NOON - 3600)
        self.assertEqual(self.row(lines, "tool", "opus")[:3], ["1", "0", "0"])

    def test_a_grok_offering_costs_weighted_tokens_and_is_not_unrated(self):
        # g-1.1 lands; g-1.2 ends its attempt and lands; g-1.3 lands on a commit a refuted leaf's Origin line names.
        self.run_session("g-1.1", "grok-high", weighted=2_000_000)
        self.run_session("g-1.2", "grok-high", retry="g-1.2", weighted=1_000_000)
        self.run_session("g-1.3", "grok-high", weighted=3_000_000)
        self.run_session("c-1.1", "carbon-high", weighted=1_000_000)
        tracker = [self.issue("g-1.1"), self.issue("g-1.2"), self.issue("g-1.3", reason="def5678: landed"),
                   self.issue("g-1.10", status="open", labels=("refuted",), description="Refuted.\nOrigin: def5678"),
                   self.issue("c-1.1")]
        lines = self.lines(tracker)
        self.assertEqual(self.row(lines, "tool", "grok-high"), ["3", "3", "2", "1", "1", "2.00", "-", "6.00"])
        self.assertFalse(any(line.startswith("no rate for grok") for line in lines))
        self.assertIn("no rate for agy gemini-4-carbon-high: its sessions add no points", lines)
        self.assertIn("grok: a landed leaf's cost is the weighted column, in millions of weighted tokens; "
                      "the plan is a flat subscription, so no weekly points", lines)

    def test_sessions_on_no_leaf_are_counted_by_offering(self):
        self.run_session("a-1.9", "opus", session="skeptic", kind="review", limited=1, weighted=4_000_000)
        self.run_session(None, "opus", kind=None, weighted=1_000_000)
        self.run_session("a-1", "fable-xhigh", kind=None, weighted=2_000_000)
        lines = self.lines([self.issue("a-1.9", labels=("review",)), self.issue("a-1", type="epic")])
        # The review is its own row. The epic round and the round that named no issue stay on no leaf.
        self.assertEqual(self.review_row(lines, "opus"), ["1", "0", "0", "4.00", "0.480"])
        no_leaf = []
        for line in lines[next(i for i, line in enumerate(lines) if line.startswith("on no leaf")) + 1:]:
            if line.startswith(("accounted", "no rate", "grok:")):
                break
            no_leaf.append(line.split())
        self.assertEqual(no_leaf, [["fable-xhigh", "1", "0", "2.00"], ["opus", "1", "0", "1.00"]])
        self.assertIn("accounted 3 sessions, 7.00M weighted", lines)

    def test_a_close_reason_naming_a_pid_and_no_commit_of_main_is_not_landed(self):
        self.run_session("a-1.1", "opus")
        self.run_session("a-1.2", "opus")
        self.run_session("a-1.3", "opus")
        tracker = [self.issue("a-1.1", reason="No commit: the leaves were already true; loop-3251189 and grok-1958135 held it"),
                   self.issue("a-1.2", reason="fedcba9: landed on a branch main does not contain"),
                   self.issue("a-1.3", reason="abc1234: landed")]
        self.assertEqual(self.row(self.lines(tracker[:1]), "tool", "opus")[:2], ["1", "0"])
        self.assertEqual(self.row(self.lines(tracker), "tool", "opus")[:2], ["3", "1"])

    def review_row(self, lines, offering):
        start = next(i for i, line in enumerate(lines) if line.startswith("reviews "))
        end = next(i for i, line in enumerate(lines) if line.startswith("on no leaf"))
        return next(line.split()[1:] for line in lines[start:end] if line.split()[:1] == [offering])

    def test_a_prover_only_issue_a_split_leaf_and_a_review_each_keep_their_cost_and_the_lines_sum(self):
        # p-1.1 lands. p-1 was taken as proof and is an epic now; its close reason names a child SHA.
        self.run_session("p-1.1", "opus", kind="proof", weighted=1_000_000)
        self.run_session("p-1", "opus", kind="proof", weighted=3_000_000)
        # s-1.1 has only a prover session, recorded before hand-offs carried a kind. Its label is spec.
        self.run_session("s-1.1", "fable-xhigh", session="prover", kind=None, weighted=2_000_000)
        # r-1.1's skeptic ran before its round; the round's offering took it. r-1.2 closed on a pass.
        self.run_session("r-1.1", "opus-xhigh", session="skeptic", kind=None, weighted=4_000_000)
        self.run_session("r-1.1", "opus", kind="review", weighted=500_000)
        self.run_session("r-1.2", "opus", kind="review", weighted=500_000)
        # An epic round names no leaf and stays on the offering's other line.
        self.run_session(None, "opus", kind=None, weighted=100_000)
        tracker = [self.issue("p-1.1", labels=("kind:proof",)),
                   self.issue("p-1", type="epic", labels=(), reason="children's evidence: abc1234"),
                   self.issue("s-1.1", status="open", labels=("kind:spec",)),
                   self.issue("r-1.1", labels=("review",), reason="refuted: criterion 1"),
                   self.issue("r-1.2", labels=("review",), reason="skeptic pass: stands")]
        lines = self.lines(tracker)
        # The split's 3M stays in the proof/opus per-leaf cost, and the epic is not a landed leaf.
        self.assertEqual(self.row(lines, "proof", "opus"), ["2", "1", "1", "0", "0", "4.00", f"{0.12 * 4:.3f}", "4.00"])
        self.assertEqual(self.row(lines, "spec", "fable-xhigh"), ["1", "0", "0", "0", "0", "-", "-", "2.00"])
        # Both reviews were taken by opus, the first round's offering, skeptic cost included.
        self.assertEqual(self.review_row(lines, "opus"), ["2", "1", "1", "5.00", f"{0.12 * 5:.3f}"])
        self.assertNotIn("opus-xhigh", [line.split()[0] for line in lines if line.startswith("opus")])
        no_leaf = []
        for line in lines[next(i for i, line in enumerate(lines) if line.startswith("on no leaf")) + 1:]:
            if line.startswith(("accounted", "no rate", "grok:")):
                break
            no_leaf.append(line.split())
        self.assertEqual(no_leaf, [["opus", "1", "0", "0.10"]])
        self.assertIn("accounted 7 sessions, 11.10M weighted", lines)

    def cents(self, text):
        whole, frac = text.split(".")
        return int(whole) * 100 + int(frac)

    def column_hundredths(self, lines):
        """Hundredths of a million on the sum column, the review weighted column and the on-no-leaf column."""
        reviews_at = next(i for i, line in enumerate(lines) if line.startswith("reviews "))
        no_leaf_at = next(i for i, line in enumerate(lines) if line.startswith("on no leaf"))
        leaf_header = next(i for i, line in enumerate(lines) if line.split()[:1] == ["kind"])
        causes_at = next(i for i, line in enumerate(lines) if line.startswith("rounds beyond"))
        sums = [self.cents(line.split()[-1]) for line in lines[leaf_header + 1:causes_at]]
        reviews = [self.cents(line.split()[-2]) for line in lines[reviews_at + 2:no_leaf_at]]
        others = []
        for line in lines[no_leaf_at + 1:]:
            if line.startswith(("accounted", "no rate", "grok:")):
                break
            others.append(self.cents(line.split()[-1]))
        accounted = next(line for line in lines if line.startswith("accounted "))
        total = self.cents(accounted.split()[3][:-1])
        return sums, reviews, others, int(accounted.split()[1]), total

    def sessions_whose_rows_do_not_round_cancel(self, weight):
        """One leaf, one review and one session on no leaf, each of `weight` tokens."""
        self.run_session("a-1.1", "opus", kind="proof", weighted=weight)
        self.run_session("r-1.1", "opus", kind="review", weighted=weight)
        self.run_session(None, "carbon-high", kind=None, weighted=weight)
        lines = self.lines([
            self.issue("a-1.1", labels=("kind:proof",)),
            self.issue("r-1.1", labels=("review",), reason="skeptic pass: stands"),
        ])
        sums, reviews, others, count, total = self.column_hundredths(lines)
        own = self.cents(f"{weight / 1e6:.2f}")
        together = self.cents(f"{3 * weight / 1e6:.2f}")
        self.assertEqual((len(sums), len(reviews), len(others), count), (1, 1, 1, 3))
        self.assertEqual(total, together)
        # Rounding each row on its own misses the accounted line; the fixture is that case.
        self.assertNotEqual(3 * own, together)
        self.assertEqual(sum(sums) + sum(reviews) + sum(others), total)

    def test_rows_that_round_up_past_the_accounted_line_still_add_to_it(self):
        # 1.006M prints as 1.01, and three of them are 3.018M, which prints as 3.02.
        self.sessions_whose_rows_do_not_round_cancel(1_006_000)

    def test_rows_that_round_down_under_the_accounted_line_still_add_to_it(self):
        # 1.004M prints as 1.00, and three of them are 3.012M, which prints as 3.01.
        self.sessions_whose_rows_do_not_round_cancel(1_004_000)


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    sys.exit(main(sys.argv[1:]))
