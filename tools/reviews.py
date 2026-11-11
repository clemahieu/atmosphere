#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The finished epics of the Beads tree, in the order an epic round takes them, each with what it needs.

An epic is finished when it has a child and no child of it is open, in progress or blocked, nor any
issue below a closed child, which is one filed under an epic after it closed. The star, which has no
parent, never closes and is not listed, nor is an epic that is not open: one in progress is held by a
round writing its review. The order is the highest priority first and, among equals, the
deepest, depth being the number of dots in the id.

A review is a child with the label `review`: one skeptic pass over the epic's acceptance criteria.
An epic needs one when it has more than three children, counting closed ones and not its reviews, or
is at depth 1, or carries the label `skeptic`. A review covers its epic when it is the newest one that did not close as `withdrawn`, its
close reason starts `skeptic pass`, and every other issue below the epic closed before the time its
last `Skeptic input <time>:` note carries, so the pass saw all of it. One line per finished epic:

    close <epic>: children's evidence          it needs no review; the round matches criteria to evidence
    close <epic>: review <review>              that review covers it
    review <epic>: first                       it needs a review and none has judged it; the round writes one
    review <epic>: repeat of <review>: <why>   its newest review does not cover it; the round writes a repeat

usage: tools/reviews.py          (the lines, from `bd list --all` run in this tree)
       tools/reviews.py --test   (this script's own tests)
"""
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from datetime import datetime
from pathlib import Path

TREE = Path(__file__).resolve().parents[1]
UNFINISHED = ("open", "in_progress", "blocked")
SMALL = 3
INPUT = re.compile(r"Skeptic input (\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z):")


def depth(issue):
    return issue["id"].count(".")


def order(issue):
    """Round order: priority, then the deepest, then the id as its numbers read."""
    return issue["priority"], -depth(issue), [int(part) if part.isdigit() else part for part in re.split(r"[.]", issue["id"])]


def is_review(issue):
    return "review" in (issue.get("labels") or [])


def moment(text):
    return datetime.fromisoformat(text.replace("Z", "+00:00"))


def verdict(epic, children):
    """What a finished epic needs, as the text after its id."""
    own = children[epic["id"]]
    others = [child for child in own if not is_review(child)]
    if len(others) <= SMALL and depth(epic) != 1 and "skeptic" not in (epic.get("labels") or []):
        return "close", "children's evidence"
    reviews = [child for child in own if is_review(child) and child["status"] == "closed"
               and not (child.get("close_reason") or "").startswith("withdrawn")]
    if not reviews:
        return "review", "first"
    newest = max(reviews, key=lambda review: moment(review["closed_at"]))
    if not (newest.get("close_reason") or "").startswith("skeptic pass"):
        return "review", f"repeat of {newest['id']}: it did not pass and no review follows it"
    stamps = INPUT.findall(newest.get("notes") or "")
    if not stamps:
        return "review", f"repeat of {newest['id']}: its Skeptic input carries no time"
    below, queue = [], list(others)
    while queue:
        issue = queue.pop()
        below.append(issue)
        queue.extend(children[issue["id"]])
    late = sorted((issue for issue in below if issue["status"] == "closed" and moment(issue["closed_at"]) > moment(stamps[-1])), key=lambda issue: order(issue)[2])
    if late:
        return "review", f"repeat of {newest['id']}: {', '.join(issue['id'] for issue in late)} closed after its input"
    return "close", f"review {newest['id']}"


def unfinished(issue, children):
    """Whether work is left at this issue or below it, looking below only what is closed."""
    return issue["status"] in UNFINISHED or issue["status"] == "closed" and any(unfinished(child, children) for child in children[issue["id"]])


def finished(issues):
    """One line per finished epic, in round order."""
    children = {issue["id"]: [] for issue in issues}
    for issue in issues:
        if issue.get("parent") in children:
            children[issue["parent"]].append(issue)
    epics = [issue for issue in issues if issue["issue_type"] == "epic" and issue["status"] == "open" and issue.get("parent")
             and children[issue["id"]] and not any(unfinished(child, children) for child in children[issue["id"]])]
    return [f"{action} {epic['id']}: {why}" for epic in sorted(epics, key=order) for action, why in [verdict(epic, children)]]


def main(arguments):
    if arguments:
        sys.exit(__doc__.strip().split("usage: ")[1].join(["usage: ", ""]))
    listed = subprocess.run(["bd", "list", "--all", "--json", "--limit", "0"], cwd=TREE, capture_output=True, text=True)
    if listed.returncode != 0:
        sys.exit(f"reviews: bd list exited {listed.returncode}: {(listed.stderr or listed.stdout).strip()}")
    for line in finished(json.loads(listed.stdout)):
        print(line)
    return 0


class Tests(unittest.TestCase):
    def tree(self, *issues):
        """Issues from (id, type, status, extra) with the parent read from the id, a closed one closed at noon unless extra says when."""
        made = [{"id": "a", "issue_type": "epic", "status": "open", "priority": 0}]
        for name, kind, status, *extra in issues:
            issue = {"id": name, "issue_type": kind, "status": status, "priority": 2, "parent": name.rpartition(".")[0]}
            if status == "closed":
                issue.update(closed_at="2026-11-11T12:00:00Z", close_reason="abc1234: gate")
            issue.update(extra[0] if extra else {})
            made.append(issue)
        return made

    def leaves(self, epic, count, status="closed"):
        return [(f"{epic}.{number}", "task", status) for number in range(1, count + 1)]

    def review(self, name, reason="skeptic pass: all stand, main abc1234", at="2026-11-11T13:00:00Z", closed="2026-11-11T14:00:00Z"):
        return (name, "task", "closed", {"labels": ["review"], "close_reason": reason, "closed_at": closed,
                                         "notes": f"Skeptic input 2026-11-10T09:00:00Z: tier 1\nSkeptic report: refuted\nSkeptic input {at}: tier 1; evidence\nSkeptic report: stands"})

    def test_an_epic_with_a_child_that_is_open_in_progress_or_blocked_is_not_finished(self):
        for status in UNFINISHED:
            self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.1", "epic", "open"), ("a.1.1.1", "task", "closed"), ("a.1.1.2", "task", status))), [])

    def test_an_issue_filed_under_a_closed_child_keeps_the_epic_unfinished_and_one_under_a_deferred_child_does_not(self):
        base = [("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), ("a.1.1.1", "task", "closed")]
        self.assertEqual(finished(self.tree(*base, ("a.1.1.2", "epic", "closed"), ("a.1.1.2.1", "task", "open"))), [])
        self.assertEqual(finished(self.tree(*base, ("a.1.1.2", "epic", "deferred"), ("a.1.1.2.1", "task", "open"))), ["close a.1.1: children's evidence"])

    def test_an_epic_without_children_and_the_star_are_not_listed(self):
        self.assertEqual(finished(self.tree(("a.1", "epic", "closed"), ("a.2", "epic", "open"))), [])

    def test_an_epic_held_in_progress_is_not_listed(self):
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.1", "epic", "in_progress"), ("a.1.1.1", "task", "closed"))), [])

    def test_a_small_epic_closes_on_its_children_s_evidence_and_a_deferred_child_does_not_hold_it(self):
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), *self.leaves("a.1.1", 2), ("a.1.1.3", "task", "deferred"))),
                         ["close a.1.1: children's evidence"])

    def test_more_than_three_children_depth_1_or_the_label_need_a_review(self):
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.1", "task", "closed"),
                                            ("a.2", "epic", "open"), ("a.2.9", "task", "open"), ("a.2.1", "epic", "open"), *self.leaves("a.2.1", 4),
                                            ("a.2.2", "epic", "open", {"labels": ["skeptic"]}), ("a.2.2.1", "task", "closed"))),
                         ["review a.2.1: first", "review a.2.2: first", "review a.1: first"])

    def test_a_review_is_not_counted_as_a_child_of_a_small_epic(self):
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), *self.leaves("a.1.1", 3), self.review("a.1.1.4"))),
                         ["close a.1.1: children's evidence"])

    def test_a_review_that_passed_after_everything_below_the_epic_closed_covers_it(self):
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), *self.leaves("a.1.1", 4),
                                            ("a.1.1.5", "epic", "closed"), ("a.1.1.5.1", "task", "closed"), self.review("a.1.1.6"))),
                         ["close a.1.1: review a.1.1.6"])

    def test_an_issue_below_the_epic_that_closed_after_the_review_s_input_is_not_covered(self):
        late = {"closed_at": "2026-11-11T13:30:00Z", "close_reason": "def5678: gate"}
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), *self.leaves("a.1.1", 4),
                                            ("a.1.1.5", "epic", "closed", late), ("a.1.1.5.1", "task", "closed", late), ("a.1.1.5.2", "task", "closed"), self.review("a.1.1.6"))),
                         ["review a.1.1: repeat of a.1.1.6: a.1.1.5, a.1.1.5.1 closed after its input"])

    def test_the_newest_review_decides_and_a_withdrawn_one_is_passed_over(self):
        refuted = self.review("a.1.1.6", reason="refuted: criterion 3; filed as a.1.1.5; repeat a.1.1.7", at="2026-11-11T10:00:00Z", closed="2026-11-11T11:00:00Z")
        withdrawn = self.review("a.1.1.8", reason="withdrawn: a.1.1.2 is an epic", closed="2026-11-11T16:00:00Z")
        base = [("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), *self.leaves("a.1.1", 5)]
        self.assertEqual(finished(self.tree(*base, refuted)), ["review a.1.1: repeat of a.1.1.6: it did not pass and no review follows it"])
        self.assertEqual(finished(self.tree(*base, refuted, self.review("a.1.1.7"), withdrawn)), ["close a.1.1: review a.1.1.7"])
        self.assertEqual(finished(self.tree(*base, withdrawn)), ["review a.1.1: first"])

    def test_a_passing_review_without_a_dated_input_covers_nothing(self):
        review = self.review("a.1.1.5")
        review[3]["notes"] = "Skeptic input: tier 1\nSkeptic report: stands"
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), *self.leaves("a.1.1", 4), review)),
                         ["review a.1.1: repeat of a.1.1.5: its Skeptic input carries no time"])

    def test_the_order_is_priority_then_the_deepest_then_the_id(self):
        first = {"priority": 1}
        self.assertEqual(finished(self.tree(("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.10", "epic", "open"), ("a.1.10.1", "task", "closed"),
                                            ("a.1.2", "epic", "open"), ("a.1.2.1", "task", "closed"), ("a.1.2.2", "epic", "open"), ("a.1.2.2.1", "task", "closed"),
                                            ("a.1.3", "epic", "open", first), ("a.1.3.1", "task", "closed"))),
                         ["close a.1.3: children's evidence", "close a.1.2.2: children's evidence", "close a.1.10: children's evidence"])

    def test_the_command_prints_the_lines_of_the_tree_bd_lists(self):
        with tempfile.TemporaryDirectory() as folder:
            folder = Path(folder)
            (folder / "tree.json").write_text(json.dumps(self.tree(("a.1", "epic", "open"), ("a.1.9", "task", "open"), ("a.1.1", "epic", "open"), *self.leaves("a.1.1", 4))))
            (folder / "bd").write_text(f'#!/bin/sh\necho "$*" > "{folder}/call"\ncat "{folder}/tree.json"\n')
            (folder / "bd").chmod(0o755)
            run = subprocess.run([sys.executable, __file__], env={**os.environ, "PATH": f"{folder}:{os.environ['PATH']}"}, capture_output=True, text=True)
            self.assertEqual((run.returncode, run.stdout, run.stderr), (0, "review a.1.1: first\n", ""))
            self.assertEqual((folder / "call").read_text(), "list --all --json --limit 0\n")
            (folder / "bd").write_text("#!/bin/sh\necho 'database is locked' >&2\nexit 3\n")
            run = subprocess.run([sys.executable, __file__], env={**os.environ, "PATH": f"{folder}:{os.environ['PATH']}"}, capture_output=True, text=True)
            self.assertEqual((run.returncode, run.stdout, run.stderr), (1, "", "reviews: bd list exited 3: database is locked\n"))


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        sys.argv[1:] = []
        unittest.main()
    sys.exit(main(sys.argv[1:]))
