#!/usr/bin/env python3
"""Check the trusted surface of every crate marked verified: every attribute that exempts code from a
proof is listed in tools/external-body-list with its reason, and no assume or admit is left.

The crates checked are the workspace members whose Cargo.toml marks them
'[package.metadata.atmosphere] verified = true', the crates tools/verify.py proves; each one's
directory is scanned for Rust sources. Two attributes exempt code: external_body, from the proof of
what a function does, and exec_allows_no_decreases_clause, from the proof that it terminates. Each
live one, spelled '#[verifier::<attribute>]' or '#[verifier(<attribute>)]', is followed by a line
'// <attribute>(<class>): <reason>', where the class is glue, gap or unproven (CLAUDE.md,
Testability), and then by the function it applies to. The list holds one line per attribute: path
from the repository root, item, attribute, class and reason, separated by tabs. The check passes when
the source and the list hold the same items, counting an item that appears twice in one file twice. A call
of assume( or admit( outside a '//' comment fails the check: the marked crates hold none, and a new
one would be an axiom the proof rests on. The retired 'old' trees and build output under 'target'
are not scanned.

usage: tools/check-external-body.py           (the tree)
       tools/check-external-body.py --test    (this script's own tests)
"""
import json
import re
import sys
import tempfile
import tomllib
import unittest
from collections import Counter, namedtuple
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
LIST_PATH = "tools/external-body-list"
SKIPPED_DIRECTORIES = ("old", "target")
ATTRIBUTES = ("external_body", "exec_allows_no_decreases_clause")
ATTRIBUTE = re.compile(r"#\[verifier(?:::(\w+)\]|\((\w+)\)\])")
CLASSES = ("glue", "gap", "unproven")
ASSUMPTION = re.compile(r"\b(assume|admit)\s*\(")

# One attribute, as the list and the source both state it.
Item = namedtuple("Item", "path name attribute kind reason")


class Unreadable(Exception):
    """A list line, or an attribute in the source, that does not have the required form."""


def parse_list(text):
    items = []
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        readable = len(fields) == 5 and fields[2] in ATTRIBUTES and fields[3] in CLASSES and fields[4].strip()
        if not readable:
            raise Unreadable(f"{LIST_PATH}: cannot read {json.dumps(line)}")
        items.append(Item(*fields))
    return items


def attribute(line):
    """The exempting attribute a line opens with, or None when it opens with none."""
    match = ATTRIBUTE.match(line)
    name = match and (match.group(1) or match.group(2))
    return name if name in ATTRIBUTES else None


def parse_reason(attribute, line):
    """The class and the reason a reason line for an attribute states, or None when it is not one."""
    prefix = f"// {attribute}("
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
        exempting = attribute(line)
        if exempting is None:
            continue
        at = f"{path}:{index + 1}"
        stated = parse_reason(exempting, lines[index + 1] if index + 1 < len(lines) else "")
        if stated is None:
            raise Unreadable(f"{at}: no reason line in the form // {exempting}(<class>): <reason>")
        name = next(filter(None, map(item_name, lines[index + 2:])), None)
        if name is None:
            raise Unreadable(f"{at}: no item follows")
        items.append(Item(path, name, exempting, *stated))
    return items


def assumptions(path, source):
    """Each line of one file that calls assume or admit outside a '//' comment, with where it is."""
    found = []
    for index, line in enumerate(source.splitlines()):
        if ASSUMPTION.search(line.split("//", 1)[0]):
            found.append(f"{path}:{index + 1}: {line.strip()}")
    return found


def compare(found, listed):
    """Describes every item only one side has, counting an item once per occurrence."""
    def describe(item):
        return f"{item.path} {item.name} {item.attribute} ({item.kind}: {item.reason})"

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
    """The Rust sources under a directory, leaving out the retired 'old' trees and build output."""
    for entry in sorted(directory.iterdir()):
        if entry.is_dir():
            if entry.name not in SKIPPED_DIRECTORIES:
                yield from sources(entry)
        elif entry.suffix == ".rs":
            yield entry


def marked_crates(repo):
    """The directories, from the repository root, of the workspace members marked verified, in the
    order the workspace lists them."""
    with open(repo / "Cargo.toml", "rb") as manifest:
        members = tomllib.load(manifest)["workspace"]["members"]
    marked = []
    for member in members:
        with open(repo / member / "Cargo.toml", "rb") as manifest:
            package = tomllib.load(manifest)["package"]
        if package.get("metadata", {}).get("atmosphere", {}).get("verified", False):
            marked.append(member)
    return marked


def scan_tree(repo):
    """Each live attribute and each assume or admit in the marked crates, named from the root."""
    found = []
    assumed = []
    for crate in marked_crates(repo):
        for file in sources(repo / crate):
            path = file.relative_to(repo).as_posix()
            source = file.read_text(encoding="utf-8")
            found.extend(scan(path, source))
            assumed.extend(assumptions(path, source))
    return found, assumed


def main(args):
    if args:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    try:
        listed = parse_list((REPO / LIST_PATH).read_text(encoding="utf-8"))
        found, assumed = scan_tree(REPO)
    except Unreadable as error:
        print(error, file=sys.stderr)
        return 1
    differences = compare(found, listed) + [f"{line} assumes what the proof should show" for line in assumed]
    for difference in differences:
        print(difference, file=sys.stderr)
    if differences:
        return 1
    summaries = []
    for exempting in ATTRIBUTES:
        kinds = Counter(item.kind for item in found if item.attribute == exempting)
        totals = ", ".join(f"{count} {kind}" for kind, count in sorted(kinds.items()))
        summaries.append(f"{sum(kinds.values())} {exempting}" + (f" ({totals})" if totals else ""))
    print(f"{'; '.join(summaries)} listed; no assume or admit")
    return 0


ATTR = "#[verifier(external_body)]"


def body(path, name, kind, reason):
    """An external_body item, as the tests that predate the second attribute state it."""
    return Item(path, name, "external_body", kind, reason)


class Tests(unittest.TestCase):
    def test_scan_reads_the_reason_and_the_item(self):
        source = f"{ATTR}\n// external_body(gap): raw write\npub fn set_state(x: u8)\n    ensures true,\n{{}}\n"
        self.assertEqual(scan("a.rs", source), [body("a.rs", "set_state", "gap", "raw write")])

    def test_scan_handles_proof_fns_and_a_trailing_comment_on_the_attribute(self):
        source = f"    {ATTR} // a note\n    // external_body(unproven): axiom\n    pub proof fn page_lemma()\n"
        self.assertEqual(scan("a.rs", source), [body("a.rs", "page_lemma", "unproven", "axiom")])

    def test_scan_skips_other_attributes_before_the_item(self):
        source = f"{ATTR}\n// external_body(glue): hw\n#[inline(always)]\npub const fn zeroed() -> Self {{}}\n"
        self.assertEqual(scan("a.rs", source), [body("a.rs", "zeroed", "glue", "hw")])

    def test_scan_ignores_a_commented_attribute(self):
        self.assertEqual(scan("a.rs", f"// {ATTR}\npub fn f() {{}}\n"), [])

    def test_scan_rejects_a_missing_reason(self):
        with self.assertRaisesRegex(Unreadable, r"^a\.rs:1: no reason line"):
            scan("a.rs", f"{ATTR}\npub fn f() {{}}\n")

    def test_scan_rejects_an_unknown_class_and_an_empty_reason(self):
        with self.assertRaises(Unreadable):
            scan("a.rs", f"{ATTR}\n// external_body(later): x\npub fn f() {{}}\n")
        with self.assertRaises(Unreadable):
            scan("a.rs", f"{ATTR}\n// external_body(gap): \npub fn f() {{}}\n")

    def test_scan_rejects_an_attribute_with_no_item(self):
        with self.assertRaisesRegex(Unreadable, r"^a\.rs:2: no item follows"):
            scan("a.rs", f"\n{ATTR}\n// external_body(gap): x\n")

    def test_list_has_five_tab_separated_fields(self):
        listed = parse_list("# note\n\na.rs\tf\texternal_body\tgap\traw write\n")
        self.assertEqual(listed, [body("a.rs", "f", "gap", "raw write")])
        with self.assertRaises(Unreadable):
            parse_list("a.rs\tf\tgap\traw write\n")
        with self.assertRaises(Unreadable):
            parse_list("a.rs\tf\texternal_body\tlater\tx\n")

    def test_compare_reports_each_side(self):
        a = body("a.rs", "f", "gap", "x")
        b = body("a.rs", "g", "gap", "x")
        self.assertEqual(compare([a], [a]), [])
        self.assertEqual(compare([a, b], [a]), ["a.rs g external_body (gap: x) is not on the list"])
        self.assertEqual(compare([a], [a, b]), ["a.rs g external_body (gap: x) is not in the source"])

    def test_compare_counts_duplicates_in_one_file(self):
        a = body("trap.rs", "set_self_fast", "unproven", "x")
        self.assertNotEqual(compare([a, a], [a]), [])
        self.assertEqual(compare([a, a], [a, a]), [])

    def test_assumptions_finds_a_live_assume_and_admit(self):
        source = "proof fn f() {\n    assume(x == 1);\n    admit();\n}\n"
        self.assertEqual(assumptions("a.rs", source), ["a.rs:2: assume(x == 1);", "a.rs:3: admit();"])

    def test_assumptions_finds_assume_false_and_a_spaced_call(self):
        self.assertEqual(assumptions("a.rs", "    assume (false);\n"), ["a.rs:1: assume (false);"])

    def test_assumptions_ignores_comments(self):
        source = "// assume(false);\n/// admit()\nlet y = 1; // assume(y == 1)\n"
        self.assertEqual(assumptions("a.rs", source), [])

    def test_assumptions_ignores_names_that_only_start_with_assume(self):
        source = "(page_ptr, Tracked::assume_new())\nMaybeUninit::zeroed().assume_init()\nreadmit(x)\n"
        self.assertEqual(assumptions("a.rs", source), [])

    def test_scan_reads_an_exec_allows_no_decreases_clause(self):
        source = (
            "    #[verifier::exec_allows_no_decreases_clause]\n"
            "    // exec_allows_no_decreases_clause(unproven): spins until the holder hands over\n"
            "    pub fn acquire(&self)\n"
        )
        found = scan("lock.rs", source)
        reason = "spins until the holder hands over"
        self.assertEqual(found, [Item("lock.rs", "acquire", "exec_allows_no_decreases_clause", "unproven", reason)])
        self.assertEqual(compare(found, found), [])

    def test_an_unlisted_exec_allows_no_decreases_clause_fails(self):
        source = (
            "#[verifier::exec_allows_no_decreases_clause]\n"
            "// exec_allows_no_decreases_clause(unproven): x\n"
            "fn f()\n"
        )
        self.assertEqual(
            compare(scan("a.rs", source), []),
            ["a.rs f exec_allows_no_decreases_clause (unproven: x) is not on the list"],
        )

    def test_an_exec_allows_no_decreases_clause_needs_its_own_reason_line(self):
        with self.assertRaisesRegex(Unreadable, r"^a\.rs:1: no reason line"):
            scan("a.rs", "#[verifier::exec_allows_no_decreases_clause]\nfn f()\n")
        with self.assertRaisesRegex(Unreadable, r"^a\.rs:1: no reason line"):
            scan("a.rs", "#[verifier::exec_allows_no_decreases_clause]\n// external_body(unproven): x\nfn f()\n")

    def test_scan_reads_both_spellings_of_each_attribute(self):
        for attribute in ATTRIBUTES:
            for spelling in (f"#[verifier::{attribute}]", f"#[verifier({attribute})]"):
                source = f"{spelling}\n// {attribute}(gap): x\nfn f()\n"
                self.assertEqual(scan("a.rs", source), [Item("a.rs", "f", attribute, "gap", "x")])

    def test_the_list_names_the_attribute(self):
        self.assertEqual(
            parse_list("a.rs\tf\texec_allows_no_decreases_clause\tunproven\tx\n"),
            [Item("a.rs", "f", "exec_allows_no_decreases_clause", "unproven", "x")],
        )
        with self.assertRaises(Unreadable):
            parse_list("a.rs\tf\ttrusted\tunproven\tx\n")

    def workspace(self, crates):
        """A workspace in a temporary directory: each crate's directory, whether it is marked
        verified, and its sources by path under the crate."""
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        repo = Path(directory.name)
        members = ", ".join(f'"{crate}"' for crate in crates)
        (repo / "Cargo.toml").write_text(f"[workspace]\nmembers = [{members}]\n")
        for crate, (marked, files) in crates.items():
            manifest = f'[package]\nname = "{crate.replace("/", "-")}"\n'
            if marked:
                manifest += "\n[package.metadata.atmosphere]\nverified = true\n"
            (repo / crate).mkdir(parents=True)
            (repo / crate / "Cargo.toml").write_text(manifest)
            for name, source in files.items():
                (repo / crate / name).parent.mkdir(parents=True, exist_ok=True)
                (repo / crate / name).write_text(source)
        return repo

    def test_marked_crates_are_the_workspace_members_marked_verified(self):
        repo = self.workspace({"kernel/verified": (True, {}), "heap": (True, {}), "dom0": (False, {})})
        self.assertEqual(marked_crates(repo), ["kernel/verified", "heap"])

    def test_every_marked_crate_is_scanned_under_its_repository_path(self):
        glue = f"{ATTR}\n// external_body(glue): a syscall\npub fn back()\n"
        repo = self.workspace({
            "kernel/verified": (True, {"a.rs": f"{ATTR}\n// external_body(gap): x\nfn f()\n"}),
            "heap": (True, {"src/source.rs": glue, "src/lib.rs": "proof fn p() { assume(false); }\n"}),
        })
        found, assumed = scan_tree(repo)
        listed = [body("kernel/verified/a.rs", "f", "gap", "x")]
        self.assertEqual(
            compare(found, listed),
            ["heap/src/source.rs back external_body (glue: a syscall) is not on the list"],
        )
        self.assertEqual(assumed, ["heap/src/lib.rs:1: proof fn p() { assume(false); }"])

    def test_an_unmarked_crate_is_not_scanned(self):
        repo = self.workspace({
            "kernel/verified": (True, {}),
            "dom0": (False, {"src/main.rs": f"{ATTR}\nfn f()\nfn g() {{ assume(false); }}\n"}),
        })
        self.assertEqual(scan_tree(repo), ([], []))

    def test_old_and_target_trees_are_not_scanned(self):
        live = f"{ATTR}\n// external_body(gap): x\nfn f()\n"
        repo = self.workspace({"heap": (True, {"old/a.rs": "fn f() { admit(); }\n", "target/b.rs": live})})
        self.assertEqual(scan_tree(repo), ([], []))

    def test_a_changed_reason_shows_on_both_sides(self):
        self.assertEqual(len(compare([body("a.rs", "f", "gap", "x")], [body("a.rs", "f", "gap", "y")])), 2)


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
