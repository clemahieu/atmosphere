#!/usr/bin/env python3
"""Check that every external_body in kernel/verified is listed in tools/external-body-list with its reason.

Each live '#[verifier(external_body)]' attribute is followed by a line
'// external_body(<class>): <reason>', where the class is glue, gap or unproven (CLAUDE.md,
Testability), and then by the function it applies to. The list holds one line per attribute: path
under kernel/verified, item, class and reason, separated by tabs. The check passes when the source
and the list hold the same items, counting an item that appears twice in one file twice. The
retired 'old' trees are not scanned.

usage: tools/check-external-body.py           (the tree)
       tools/check-external-body.py --test    (this script's own tests)
"""
import json
import sys
import unittest
from collections import Counter, namedtuple
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
LIST_PATH = "tools/external-body-list"
VERIFIED_ROOT = "kernel/verified"
ATTRIBUTE = "#[verifier(external_body)]"
CLASSES = ("glue", "gap", "unproven")

# One attribute, as the list and the source both state it.
Item = namedtuple("Item", "path name kind reason")


class Unreadable(Exception):
    """A list line, or an attribute in the source, that does not have the required form."""


def parse_list(text):
    items = []
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 4 or fields[2] not in CLASSES or not fields[3].strip():
            raise Unreadable(f"{LIST_PATH}: cannot read {json.dumps(line)}")
        items.append(Item(*fields))
    return items


def parse_reason(line):
    """The class and the reason a reason line states, or None when it is not one."""
    prefix = "// external_body("
    if not line.startswith(prefix) or "): " not in line:
        return None
    kind, reason = line[len(prefix):].split("): ", 1)
    return (kind, reason) if kind in CLASSES and reason.strip() else None


def item_name(line):
    """The name of the function a line declares, or None when it declares none."""
    if line.startswith("//") or line.startswith("#[") or "fn " not in line:
        return None
    after = line.split("fn ", 1)[1]
    for end, char in enumerate(after):
        if not (char.isalnum() or char == "_"):
            return after[:end]
    return None


def scan(path, source):
    """Each live attribute in one file, with the reason line after it and the item it applies to."""
    lines = [line.strip() for line in source.splitlines()]
    items = []
    for index, line in enumerate(lines):
        if not line.startswith(ATTRIBUTE):
            continue
        at = f"{path}:{index + 1}"
        stated = parse_reason(lines[index + 1] if index + 1 < len(lines) else "")
        if stated is None:
            raise Unreadable(f"{at}: no reason line in the form // external_body(<class>): <reason>")
        name = next(filter(None, map(item_name, lines[index + 2:])), None)
        if name is None:
            raise Unreadable(f"{at}: no item follows")
        items.append(Item(path, name, *stated))
    return items


def compare(found, listed):
    """Describes every item only one side has, counting an item once per occurrence."""
    def describe(item):
        return f"{item.path} {item.name} ({item.kind}: {item.reason})"

    remaining = Counter(listed)
    differences = []
    for item in found:
        if remaining[item]:
            remaining[item] -= 1
        else:
            differences.append(f"{describe(item)} is not on the list")
    for item in listed:
        if remaining[item]:
            remaining[item] -= 1
            differences.append(f"{describe(item)} is not in the source")
    return differences


def sources(directory):
    """The Rust sources under a directory, leaving out the retired 'old' trees."""
    for entry in sorted(directory.iterdir()):
        if entry.is_dir():
            if entry.name != "old":
                yield from sources(entry)
        elif entry.suffix == ".rs":
            yield entry


def main(args):
    if args:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    verified = REPO / VERIFIED_ROOT
    try:
        listed = parse_list((REPO / LIST_PATH).read_text(encoding="utf-8"))
        found = []
        for file in sources(verified):
            found.extend(scan(file.relative_to(verified).as_posix(), file.read_text(encoding="utf-8")))
    except Unreadable as error:
        print(error, file=sys.stderr)
        return 1
    differences = compare(found, listed)
    for difference in differences:
        print(difference, file=sys.stderr)
    if differences:
        return 1
    kinds = Counter(item.kind for item in found)
    totals = ", ".join(f"{count} {kind}" for kind, count in sorted(kinds.items()))
    print(f"{len(found)} items listed: {totals}")
    return 0


class Tests(unittest.TestCase):
    def test_scan_reads_the_reason_and_the_item(self):
        source = f"{ATTRIBUTE}\n// external_body(gap): raw write\npub fn set_state(x: u8)\n    ensures true,\n{{}}\n"
        self.assertEqual(scan("a.rs", source), [Item("a.rs", "set_state", "gap", "raw write")])

    def test_scan_handles_proof_fns_and_a_trailing_comment_on_the_attribute(self):
        source = f"    {ATTRIBUTE} // a note\n    // external_body(unproven): axiom\n    pub proof fn page_lemma()\n"
        self.assertEqual(scan("a.rs", source), [Item("a.rs", "page_lemma", "unproven", "axiom")])

    def test_scan_skips_other_attributes_before_the_item(self):
        source = f"{ATTRIBUTE}\n// external_body(glue): hw\n#[inline(always)]\npub const fn zeroed() -> Self {{}}\n"
        self.assertEqual(scan("a.rs", source), [Item("a.rs", "zeroed", "glue", "hw")])

    def test_scan_ignores_a_commented_attribute(self):
        self.assertEqual(scan("a.rs", f"// {ATTRIBUTE}\npub fn f() {{}}\n"), [])

    def test_scan_rejects_a_missing_reason(self):
        with self.assertRaisesRegex(Unreadable, r"^a\.rs:1: no reason line"):
            scan("a.rs", f"{ATTRIBUTE}\npub fn f() {{}}\n")

    def test_scan_rejects_an_unknown_class_and_an_empty_reason(self):
        with self.assertRaises(Unreadable):
            scan("a.rs", f"{ATTRIBUTE}\n// external_body(later): x\npub fn f() {{}}\n")
        with self.assertRaises(Unreadable):
            scan("a.rs", f"{ATTRIBUTE}\n// external_body(gap): \npub fn f() {{}}\n")

    def test_scan_rejects_an_attribute_with_no_item(self):
        with self.assertRaisesRegex(Unreadable, r"^a\.rs:2: no item follows"):
            scan("a.rs", f"\n{ATTRIBUTE}\n// external_body(gap): x\n")

    def test_list_has_four_tab_separated_fields(self):
        self.assertEqual(parse_list("# note\n\na.rs\tf\tgap\traw write\n"), [Item("a.rs", "f", "gap", "raw write")])
        with self.assertRaises(Unreadable):
            parse_list("a.rs\tf\tgap\n")
        with self.assertRaises(Unreadable):
            parse_list("a.rs\tf\tlater\tx\n")

    def test_compare_reports_each_side(self):
        a = Item("a.rs", "f", "gap", "x")
        b = Item("a.rs", "g", "gap", "x")
        self.assertEqual(compare([a], [a]), [])
        self.assertEqual(compare([a, b], [a]), ["a.rs g (gap: x) is not on the list"])
        self.assertEqual(compare([a], [a, b]), ["a.rs g (gap: x) is not in the source"])

    def test_compare_counts_duplicates_in_one_file(self):
        a = Item("trap.rs", "set_self_fast", "unproven", "x")
        self.assertNotEqual(compare([a, a], [a]), [])
        self.assertEqual(compare([a, a], [a, a]), [])

    def test_a_changed_reason_shows_on_both_sides(self):
        self.assertEqual(len(compare([Item("a.rs", "f", "gap", "x")], [Item("a.rs", "f", "gap", "y")])), 2)


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
