#!/usr/bin/env python3
"""Check that each file the tree copies from upstream differs from it only by its recorded delta.

A record is a unified diff under tools/upstream-copies/, one per copied file. Its '---' line names the
upstream file and its '+++' line the copy, both relative to the project root. The check applies each
record to the upstream file as it is now, every hunk at the line its header names and every context
and removed line matching, and passes when the result is the copy byte for byte. So it fails when the
upstream file moves (a Verus pin that changes it) and when the copy changes without its record.

After a deliberate change, --update rewrites every record, or the ones named, from the two files its
header names. A new record starts as its two header lines alone.

usage: tools/check-upstream-copies.py                     (check every record)
       tools/check-upstream-copies.py --update [RECORD]   (rewrite the records from the files)
       tools/check-upstream-copies.py --test              (this script's own tests)
"""
import difflib
import re
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
RECORDS = "tools/upstream-copies"
HUNK = re.compile(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@\n")


class Drift(Exception):
    """A copy that its upstream file and its record do not produce, or a record that cannot be read."""


def read_lines(path):
    text = path.read_text()
    if text and not text.endswith("\n"):
        raise Drift(f"{path}: does not end in a newline")
    return text.splitlines(keepends=True)


def header(record_path):
    lines = record_path.read_text().splitlines(keepends=True)
    if len(lines) < 2 or not lines[0].startswith("--- ") or not lines[1].startswith("+++ "):
        raise Drift(f"{record_path}: does not open with '--- <upstream>' and '+++ <copy>' lines")
    return lines[0][4:].rstrip("\n"), lines[1][4:].rstrip("\n"), lines[2:]


def delta(upstream, upstream_lines, copy, copy_lines):
    """The record for a copy: the unified diff from its upstream file, with three lines of context."""
    return "".join(difflib.unified_diff(upstream_lines, copy_lines, fromfile=upstream, tofile=copy, n=3))


def apply(record_path, upstream_lines, hunk_lines):
    """The upstream lines with the record's hunks applied, each where its header says."""
    out = []
    position = 0
    i = 0
    while i < len(hunk_lines):
        match = HUNK.fullmatch(hunk_lines[i])
        if not match:
            raise Drift(f"{record_path}: expected a hunk header, read {hunk_lines[i]!r}")
        i += 1
        start = int(match.group(1))
        length = 1 if match.group(2) is None else int(match.group(2))
        # A hunk that removes nothing names the line before its insertion.
        index = start if length == 0 else start - 1
        if index < position or index > len(upstream_lines):
            raise Drift(f"{record_path}: hunk at upstream line {start} is out of order or past the end")
        out += upstream_lines[position:index]
        consumed = 0
        while i < len(hunk_lines) and not hunk_lines[i].startswith("@@"):
            kind, text = hunk_lines[i][0], hunk_lines[i][1:]
            i += 1
            if kind == "+":
                out.append(text)
                continue
            if kind not in " -":
                raise Drift(f"{record_path}: cannot read hunk line {kind + text!r}")
            if index >= len(upstream_lines) or upstream_lines[index] != text:
                found = upstream_lines[index] if index < len(upstream_lines) else "end of file"
                raise Drift(f"{record_path}: upstream line {index + 1} is {found!r}, the record expects {text!r}")
            if kind == " ":
                out.append(text)
            index += 1
            consumed += 1
        if consumed != length:
            raise Drift(f"{record_path}: hunk at upstream line {start} covers {consumed} lines, its header {length}")
        position = index
    return out + upstream_lines[position:]


def check(root, record_path):
    upstream, copy, hunk_lines = header(record_path)
    upstream_lines = read_lines(root / upstream)
    copy_lines = read_lines(root / copy)
    expected = apply(record_path, upstream_lines, hunk_lines)
    if expected != copy_lines:
        shown = list(difflib.unified_diff(expected, copy_lines, "upstream plus record", copy, n=1))[:40]
        raise Drift(f"{copy}: is not {upstream} plus {record_path.name}:\n" + "".join(shown))
    added = sum(1 for line in hunk_lines if line.startswith("+"))
    removed = sum(1 for line in hunk_lines if line.startswith("-"))
    return f"{copy}: {upstream} plus {record_path.name}, {removed} lines removed and {added} added"


def update(root, record_path):
    upstream, copy, _ = header(record_path)
    text = delta(upstream, read_lines(root / upstream), copy, read_lines(root / copy))
    record_path.write_text(text or f"--- {upstream}\n+++ {copy}\n")


def records(root, names):
    if names:
        return [Path(name).resolve() for name in names]
    return sorted((root / RECORDS).glob("*.patch"))


def main(argv):
    if argv[:1] == ["--test"]:
        result = unittest.main(argv=[sys.argv[0]], exit=False, verbosity=2).result
        return 0 if result.wasSuccessful() else 1
    if argv[:1] == ["--update"]:
        for record_path in records(REPO, argv[1:]):
            update(REPO, record_path)
            print(f"updated {record_path.relative_to(REPO)}")
        return 0
    if argv:
        print(__doc__, file=sys.stderr)
        return 2
    found = records(REPO, [])
    if not found:
        print(f"no records under {RECORDS}", file=sys.stderr)
        return 1
    failed = False
    for record_path in found:
        try:
            print(check(REPO, record_path))
        except Drift as drift:
            print(f"{drift}\nAfter a deliberate change: tools/check-upstream-copies.py --update", file=sys.stderr)
            failed = True
    return 1 if failed else 0


UPSTREAM = "".join(f"upstream line {n}\n" for n in range(1, 31))


class Tests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        (self.root / "up").mkdir()
        (self.root / "copy").mkdir()
        self.record = self.root / "copy.patch"

    def tearDown(self):
        self.directory.cleanup()

    def write(self, upstream, copy):
        (self.root / "up/file.rs").write_text(upstream)
        (self.root / "copy/file.rs").write_text(copy)

    def record_now(self, upstream, copy):
        self.write(upstream, copy)
        self.record.write_text("--- up/file.rs\n+++ copy/file.rs\n")
        update(self.root, self.record)

    def edited(self, text, old, new):
        self.assertIn(old, text)
        return text.replace(old, new)

    def test_a_recorded_copy_passes(self):
        copy = self.edited(UPSTREAM, "upstream line 10\n", "copy line\n")
        self.record_now(UPSTREAM, copy)
        self.assertIn("1 lines removed and 1 added", check(self.root, self.record))

    def test_insertions_and_removals_at_both_ends_and_in_the_middle_round_trip(self):
        copies = [
            "header\n" + UPSTREAM,
            UPSTREAM + "trailer\n",
            UPSTREAM.replace("upstream line 1\n", ""),
            UPSTREAM.replace("upstream line 30\n", ""),
            UPSTREAM.replace("upstream line 15\n", "").replace("upstream line 5\n", "a\nb\n"),
            "",
            UPSTREAM,
        ]
        for copy in copies:
            with self.subTest(copy=copy[:20]):
                self.record_now(UPSTREAM, copy)
                check(self.root, self.record)
        self.record_now("", "only the copy\n")
        check(self.root, self.record)

    def test_an_upstream_change_outside_every_hunk_fails(self):
        copy = self.edited(UPSTREAM, "upstream line 25\n", "copy line\n")
        self.record_now(UPSTREAM, copy)
        self.write(self.edited(UPSTREAM, "upstream line 3\n", "moved upstream\n"), copy)
        with self.assertRaisesRegex(Drift, "is not up/file.rs plus"):
            check(self.root, self.record)

    def test_an_upstream_change_inside_a_hunk_fails(self):
        copy = self.edited(UPSTREAM, "upstream line 10\n", "copy line\n")
        self.record_now(UPSTREAM, copy)
        self.write(self.edited(UPSTREAM, "upstream line 9\n", "moved upstream\n"), copy)
        with self.assertRaisesRegex(Drift, "upstream line 9 is 'moved upstream"):
            check(self.root, self.record)

    def test_an_upstream_line_added_before_a_hunk_fails(self):
        copy = self.edited(UPSTREAM, "upstream line 20\n", "copy line\n")
        self.record_now(UPSTREAM, copy)
        self.write("new first line\n" + UPSTREAM, copy)
        with self.assertRaises(Drift):
            check(self.root, self.record)

    def test_a_copy_change_without_its_record_fails(self):
        copy = self.edited(UPSTREAM, "upstream line 10\n", "copy line\n")
        self.record_now(UPSTREAM, copy)
        self.write(UPSTREAM, self.edited(copy, "upstream line 28\n", "unrecorded\n"))
        with self.assertRaisesRegex(Drift, "is not up/file.rs plus"):
            check(self.root, self.record)

    def test_update_makes_a_deliberate_change_pass_again(self):
        copy = self.edited(UPSTREAM, "upstream line 10\n", "copy line\n")
        self.record_now(UPSTREAM, copy)
        moved = self.edited(UPSTREAM, "upstream line 3\n", "moved upstream\n")
        changed = self.edited(copy, "upstream line 28\n", "deliberate\n")
        self.write(moved, changed)
        with self.assertRaises(Drift):
            check(self.root, self.record)
        update(self.root, self.record)
        self.assertIn("3 lines removed and 3 added", check(self.root, self.record))

    def test_a_file_without_a_final_newline_is_refused(self):
        self.write(UPSTREAM, UPSTREAM + "no newline")
        self.record.write_text("--- up/file.rs\n+++ copy/file.rs\n")
        with self.assertRaisesRegex(Drift, "does not end in a newline"):
            update(self.root, self.record)

    def test_a_record_without_its_header_is_refused(self):
        self.write(UPSTREAM, UPSTREAM)
        self.record.write_text("@@ -1 +1 @@\n-a\n+b\n")
        with self.assertRaisesRegex(Drift, "does not open with"):
            check(self.root, self.record)

    def test_a_hunk_whose_header_miscounts_its_lines_is_refused(self):
        self.write(UPSTREAM, UPSTREAM.replace("upstream line 1\n", "x\n"))
        self.record.write_text("--- up/file.rs\n+++ copy/file.rs\n@@ -1,2 +1,2 @@\n-upstream line 1\n+x\n")
        with self.assertRaisesRegex(Drift, "covers 1 lines, its header 2"):
            check(self.root, self.record)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
