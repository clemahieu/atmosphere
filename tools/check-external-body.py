#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Check the trusted surface of every crate marked verified: every claim the proof takes without
proving it is listed in tools/external-body-list, with who vouches for it or why it stands unproven,
and no assume, admit or other exemption is left.

The crates checked are the workspace members whose Cargo.toml marks them
'[package.metadata.atmosphere] verified = true', the crates tools/verify.py proves; each one's
directory is scanned for Rust sources. Two attributes exempt code: external_body, from the proof of
what a function does, and exec_allows_no_decreases_clause, from the proof that it terminates. Each
live one, spelled '#[verifier::<attribute>]' or '#[verifier(<attribute>)]', is followed by a line
'// <attribute>(<class>): <reason>', where the class is glue, gap or unproven (CLAUDE.md,
Testability), and then by the function it applies to.

An assume_specification item states the specification of a function Verus does not read, and the
lines directly above it say who vouches for it (design/who-vouches-for-an-unproven-claim/). A
hardware guarantee carries one line '// cite: <key> <section, figure or table>' per passage it
restates, each key listed in tools/hardware-documents, and lies in an arch module, under a directory
named arch. A claim the kernel vouches for carries '// kernel: <path from the repository root>
<item>', naming a file that declares the function the item ends in. An item with neither, or with
both, fails the check.

The list holds one line per attribute or assumed specification: path from the repository root, item,
attribute (or assume_specification), class and reason, separated by tabs. An assumed
specification's class is hardware or kernel, and its reason is its citation lines' text, joined by
'; '. The check passes when the source and the list hold the same items, counting an item that
appears twice in one file twice. A call
of assume( or admit( outside a '//' comment fails the check: the marked crates hold none, and a new
one would be an axiom the proof rests on. So does any other way to exempt code: an axiom fn or a
broadcast axiom fn, a verifier::external fn, an external_fn_specification, an attribute above that
does not open its line (after another attribute, inside cfg_attr, or an inner #![...]), and an
assume_specification its line does not open; each word of these outside a '//' comment counts,
whatever attribute or macro spells it. The retired 'old' trees and build output under 'target'
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
ASSUMED = "assume_specification"
VOUCHERS = ("hardware", "kernel")
SPECIFICATION = re.compile(r"(?:pub(?:\([^)]*\))?\s+)?assume_specification\b[^\[]*\[([^\]]+)\]")
CITE = "// cite: "
KERNEL = "// kernel: "
DOCUMENTS_PATH = "tools/hardware-documents"
ASSUMPTION = re.compile(r"\b(assume|admit)\s*\(")
# The words that exempt code from the proof: the two counted attributes, the assumed specification,
# and the forms the marked crates do not use (an axiom fn, an external fn, an external_fn_specification).
EXEMPTING = re.compile(r"\b(axiom|external|external_fn_specification|assume_specification|"
                       r"external_body|exec_allows_no_decreases_clause)\b")

# One attribute or assumed specification, as the list and the source both state it.
Item = namedtuple("Item", "path name attribute kind reason")


class Unreadable(Exception):
    """A list line, a document line, or an attribute or an assumed specification in the source, that
    does not have the required form."""


def parse_list(text):
    items = []
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        classes = CLASSES if fields[2:3] != [ASSUMED] else VOUCHERS
        readable = (len(fields) == 5 and fields[2] in ATTRIBUTES + (ASSUMED,) and fields[3] in classes
                    and fields[4].strip())
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


def in_arch_module(path):
    """Whether a file, named from the repository root, lies in an arch module: under a directory
    named arch, as each crate's per-ISA module does (design/arch-module/)."""
    return "arch" in Path(path).parts[:-1]


def kernel_item_exists(repo, path, item):
    """Whether the file a kernel line names declares the function its item ends in."""
    file = repo / path
    name = item.rsplit("::", 1)[-1]
    return file.is_file() and re.search(rf"\bfn {re.escape(name)}\b", file.read_text(encoding="utf-8"))


def vouchers(path, lines, index, documents, repo):
    """The kind and the reason of the citation lines directly above the assumed specification on line
    index: hardware with each '<key> <locator>', or kernel with each '<path> <item>'."""
    stated = {}
    above = index
    while above > 0 and lines[above - 1].startswith((CITE, KERNEL)):
        above -= 1
    for number in range(above, index):
        line = lines[number]
        at = f"{path}:{number + 1}"
        if line.startswith(CITE):
            key, _, locator = line[len(CITE):].partition(" ")
            if key not in documents:
                raise Unreadable(f"{at}: the document {key} is not listed in {DOCUMENTS_PATH}")
            if not locator.strip():
                raise Unreadable(f"{at}: the citation names no section, figure or table of {key}")
            stated.setdefault("hardware", []).append(f"{key} {locator.strip()}")
        else:
            claim = line[len(KERNEL):].strip()
            kernel_path, _, item = claim.partition(" ")
            if not item.strip() or not kernel_item_exists(repo, kernel_path, item.strip()):
                raise Unreadable(f"{at}: the kernel item {json.dumps(claim)} does not exist")
            stated.setdefault("kernel", []).append(claim)
    at = f"{path}:{index + 1}"
    if not stated:
        raise Unreadable(f"{at}: an assumed specification with no citation: '{CITE}<key> <locator>' or "
                         f"'{KERNEL}<path> <item>' directly above it")
    if len(stated) > 1:
        raise Unreadable(f"{at}: an assumed specification vouched for both by a document and by the kernel")
    (kind, reasons), = stated.items()
    if kind == "hardware" and not in_arch_module(path):
        raise Unreadable(f"{at}: a hardware guarantee outside an arch module")
    return kind, "; ".join(reasons)


def specifications(path, source, documents, repo):
    """Each assumed specification in one file, with who vouches for it and the citations that say so."""
    lines = [line.strip() for line in source.splitlines()]
    items = []
    for index, line in enumerate(lines):
        match = SPECIFICATION.match(line)
        if match is None:
            continue
        name = re.sub(r"\s", "", match.group(1))
        items.append(Item(path, name, ASSUMED, *vouchers(path, lines, index, documents, repo)))
    return items


def parse_documents(text):
    """The documents a hardware guarantee may cite, by key: title, publisher, number and revision."""
    documents = {}
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 5 or not all(field.strip() for field in fields) or fields[0] in documents:
            raise Unreadable(f"{DOCUMENTS_PATH}: cannot read {json.dumps(line)}")
        documents[fields[0]] = tuple(fields[1:])
    return documents


def assumptions(path, source):
    """Each line of one file that calls assume or admit outside a '//' comment, with where it is."""
    found = []
    for index, line in enumerate(source.splitlines()):
        if ASSUMPTION.search(line.split("//", 1)[0]):
            found.append(f"{path}:{index + 1}: {line.strip()}")
    return found


def unread_exemptions(path, source):
    """Each line of one file that exempts code from the proof in a form this check does not count.
    The counted forms are a line opening with one counted attribute in either spelling, and a line
    opening an assumed specification with its name in brackets. Any other word of EXEMPTING outside a
    '//' comment is refused: an axiom fn, an external fn, an external_fn_specification, a counted
    attribute after another attribute, inside cfg_attr or as an inner attribute, and an assumed
    specification the line does not open."""
    refused = []
    for index, line in enumerate(source.splitlines()):
        words = [match.group(1) for match in EXEMPTING.finditer(line.split("//", 1)[0])]
        if not words:
            continue
        stripped = line.strip()
        counted = len(words) == 1 and (
            attribute(stripped) == words[0] or (words[0] == ASSUMED and SPECIFICATION.match(stripped)))
        if not counted:
            refused.append(f"{path}:{index + 1}: {stripped} exempts code from the proof in a form this "
                           "check does not count")
    return refused


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


def scan_tree(repo, documents):
    """Each live attribute and each assumed specification in the marked crates, and each line there
    that assumes, admits or exempts code in a form the list cannot count, named from the root."""
    found = []
    refused = []
    for crate in marked_crates(repo):
        for file in sources(repo / crate):
            path = file.relative_to(repo).as_posix()
            source = file.read_text(encoding="utf-8")
            found.extend(scan(path, source))
            found.extend(specifications(path, source, documents, repo))
            refused.extend(f"{line} assumes what the proof should show" for line in assumptions(path, source))
            refused.extend(unread_exemptions(path, source))
    return found, refused


def main(args):
    if args:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    try:
        listed = parse_list((REPO / LIST_PATH).read_text(encoding="utf-8"))
        documents = parse_documents((REPO / DOCUMENTS_PATH).read_text(encoding="utf-8"))
        found, refused = scan_tree(REPO, documents)
    except Unreadable as error:
        print(error, file=sys.stderr)
        return 1
    differences = compare(found, listed) + refused
    for difference in differences:
        print(difference, file=sys.stderr)
    if differences:
        return 1
    summaries = []
    for exempting in (ASSUMED,) + ATTRIBUTES:
        kinds = Counter(item.kind for item in found if item.attribute == exempting)
        totals = ", ".join(f"{count} {kind}" for kind, count in sorted(kinds.items()))
        summaries.append(f"{sum(kinds.values())} {exempting}" + (f" ({totals})" if totals else ""))
    print(f"{'; '.join(summaries)} listed; no assume, admit or uncounted exemption")
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
        found, assumed = scan_tree(repo, {})
        listed = [body("kernel/verified/a.rs", "f", "gap", "x")]
        self.assertEqual(
            compare(found, listed),
            ["heap/src/source.rs back external_body (glue: a syscall) is not on the list"],
        )
        self.assertEqual(assumed, ["heap/src/lib.rs:1: proof fn p() { assume(false); } assumes what the proof should show"])

    def test_an_unmarked_crate_is_not_scanned(self):
        repo = self.workspace({
            "kernel/verified": (True, {}),
            "dom0": (False, {"src/main.rs": f"{ATTR}\nfn f()\nfn g() {{ assume(false); }}\n"}),
        })
        self.assertEqual(scan_tree(repo, {}), ([], []))

    def test_old_and_target_trees_are_not_scanned(self):
        live = f"{ATTR}\n// external_body(gap): x\nfn f()\n"
        repo = self.workspace({"heap": (True, {"old/a.rs": "fn f() { admit(); }\n", "target/b.rs": live})})
        self.assertEqual(scan_tree(repo, {}), ([], []))

    def test_a_changed_reason_shows_on_both_sides(self):
        self.assertEqual(len(compare([body("a.rs", "f", "gap", "x")], [body("a.rs", "f", "gap", "y")])), 2)


DOCUMENTS = {"amd-apm2": ("AMD64 Architecture Programmer's Manual, Volume 2", "AMD", "24593", "3.46")}
ARCH_FILE = "kernel/verified/arch/x86_64.rs"
FLUSH = (
    "// cite: amd-apm2 5.5.3 TLB Management, Implicit Invalidations\n"
    "// cite: amd-apm2 5.5.1 Process Context Identifier\n"
    "pub assume_specification[flush_every_context](Tracked(model): Tracked<&mut TlbModel>, core: usize)\n"
    "    ensures true,\n"
    ";\n"
)


def guarantee(path, name, reason):
    return Item(path, name, "assume_specification", "hardware", reason)


class SpecificationTests(unittest.TestCase):
    def test_a_cited_guarantee_in_an_arch_module_is_accepted(self):
        reason = "amd-apm2 5.5.3 TLB Management, Implicit Invalidations; amd-apm2 5.5.1 Process Context Identifier"
        self.assertEqual(
            specifications(ARCH_FILE, FLUSH, DOCUMENTS, None),
            [guarantee(ARCH_FILE, "flush_every_context", reason)],
        )

    def test_a_guarantee_without_a_citation_is_refused(self):
        source = "\npub assume_specification[flush_every_context](x: usize);\n"
        with self.assertRaisesRegex(Unreadable, r"^kernel/verified/arch/x86_64\.rs:2: .*no citation"):
            specifications(ARCH_FILE, source, DOCUMENTS, None)

    def test_a_citation_naming_an_unlisted_document_is_refused(self):
        source = "// cite: intel-sdm-3a 4.10.4.1\nassume_specification[flush_every_context](x: usize);\n"
        with self.assertRaisesRegex(Unreadable, r"^kernel/verified/arch/x86_64\.rs:1: .*intel-sdm-3a.*not listed"):
            specifications(ARCH_FILE, source, DOCUMENTS, None)

    def test_a_citation_without_a_locator_is_refused(self):
        with self.assertRaisesRegex(Unreadable, r":1: .*section, figure or table"):
            specifications(ARCH_FILE, "// cite: amd-apm2\nassume_specification[f](x: usize);\n", DOCUMENTS, None)

    def test_a_guarantee_outside_an_arch_module_is_refused(self):
        for path in ("kernel/verified/kernel.rs", "kernel/verified/archive/x86_64.rs"):
            with self.assertRaisesRegex(Unreadable, r":3: .*outside an arch module"):
                specifications(path, FLUSH, DOCUMENTS, None)

    def test_arch_modules_of_every_crate_count(self):
        for path in ("asys/src/arch/aarch64.rs", "aloader/src/arch/x86_64/mod.rs"):
            self.assertEqual(len(specifications(path, FLUSH, DOCUMENTS, None)), 1)

    def test_a_commented_specification_is_not_counted(self):
        self.assertEqual(specifications(ARCH_FILE, "// pub assume_specification[f](x: usize);\n", DOCUMENTS, None), [])

    def kernel_repo(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        repo = Path(directory.name)
        (repo / "kernel/verified/capability").mkdir(parents=True)
        (repo / "kernel/verified/capability/operation.rs").write_text("impl Kernel {\n    pub fn dispatch(&mut self)\n}\n")
        return repo

    def test_a_kernel_claim_naming_an_item_that_exists_is_accepted_anywhere(self):
        source = "// kernel: kernel/verified/capability/operation.rs Kernel::dispatch\npub assume_specification[step](x: usize);\n"
        self.assertEqual(
            specifications("acall/src/step.rs", source, DOCUMENTS, self.kernel_repo()),
            [Item("acall/src/step.rs", "step", "assume_specification", "kernel",
                  "kernel/verified/capability/operation.rs Kernel::dispatch")],
        )

    def test_a_kernel_claim_naming_a_missing_item_or_file_is_refused(self):
        repo = self.kernel_repo()
        for line in ("kernel/verified/capability/operation.rs Kernel::step", "kernel/verified/none.rs Kernel::dispatch"):
            source = f"// kernel: {line}\npub assume_specification[step](x: usize);\n"
            with self.assertRaisesRegex(Unreadable, r"^acall/src/step\.rs:1: .*does not exist"):
                specifications("acall/src/step.rs", source, DOCUMENTS, repo)

    def test_a_specification_vouched_for_both_ways_is_refused(self):
        source = "// kernel: kernel/verified/capability/operation.rs Kernel::dispatch\n" + FLUSH
        with self.assertRaisesRegex(Unreadable, r":4: .*both"):
            specifications(ARCH_FILE, source, DOCUMENTS, self.kernel_repo())

    def test_the_list_holds_assumed_specifications_by_who_vouches(self):
        line = f"{ARCH_FILE}\tflush_every_context\tassume_specification\thardware\tamd-apm2 5.5.3\n"
        self.assertEqual(parse_list(line), [guarantee(ARCH_FILE, "flush_every_context", "amd-apm2 5.5.3")])
        with self.assertRaises(Unreadable):
            parse_list(f"{ARCH_FILE}\tf\tassume_specification\tglue\tx\n")
        with self.assertRaises(Unreadable):
            parse_list(f"{ARCH_FILE}\tf\texternal_body\thardware\tx\n")

    def test_documents_have_five_fields_and_unique_keys(self):
        self.assertEqual(
            parse_documents("# key\ttitle\n\namd-apm2\tAPM 2\tAMD\t24593\t3.46\n"),
            {"amd-apm2": ("APM 2", "AMD", "24593", "3.46")},
        )
        for text in ("amd-apm2\tAPM 2\tAMD\t24593\n", "amd-apm2\tAPM 2\tAMD\t24593\t\n",
                     "a\tt\tp\tn\tr\na\tt\tp\tn\tr\n"):
            with self.assertRaises(Unreadable):
                parse_documents(text)

    def test_the_tracked_document_list_is_readable(self):
        self.assertTrue(parse_documents((REPO / DOCUMENTS_PATH).read_text(encoding="utf-8")))

    def test_every_marked_crate_is_scanned_for_specifications(self):
        repo = Tests.workspace(self, {
            "kernel/verified": (True, {"arch/x86_64.rs": FLUSH}),
            "dom0": (False, {"src/main.rs": "assume_specification[f](x: usize);\n"}),
        })
        found, _ = scan_tree(repo, DOCUMENTS)
        self.assertEqual([item.name for item in found], ["flush_every_context"])
        self.assertEqual(compare(found, []), [
            "kernel/verified/arch/x86_64.rs flush_every_context assume_specification (hardware: amd-apm2 5.5.3 "
            "TLB Management, Implicit Invalidations; amd-apm2 5.5.1 Process Context Identifier) is not on the list"
        ])


class ExemptionFormTests(unittest.TestCase):
    """Every way to exempt code from the proof that the check does not count is refused."""

    FORMS = {
        "axiom fn": "pub axiom fn forged() -> (r: Tracked<BaseRegister>);\n",
        "broadcast axiom fn": "pub broadcast axiom fn forged(core: usize)\n    ensures false,\n;\n",
        "uncited assume_specification on a line it does not open": (
            "#[cfg(verus_keep_ghost)] pub assume_specification[forge](core: usize) -> Tracked<BaseRegister>;\n"
        ),
        "assume_specification split across lines": "pub assume_specification\n    [forge](core: usize);\n",
        "external_fn_specification": "#[verifier::external_fn_specification]\npub fn ex_forge(core: usize) {}\n",
        "verifier::external": "#[verifier::external]\nfn forge() -> Tracked<BaseRegister> { Tracked::assume_new() }\n",
        "verifier(external)": "#[verifier(external)]\nfn forge() {}\n",
        "external_body after another attribute": (
            "#[inline] #[verifier::external_body]\n// external_body(glue): x\nfn forge() {}\n"
        ),
        "external_body inside cfg_attr": (
            "#[cfg_attr(verus_keep_ghost, verifier::external_body)]\n// external_body(glue): x\nfn forge() {}\n"
        ),
        "external_body in an inner attribute": "#![verifier::external_body]\n",
        "exec_allows_no_decreases_clause after another attribute": (
            "#[inline] #[verifier::exec_allows_no_decreases_clause]\nfn spin() {}\n"
        ),
        "exec_allows_no_decreases_clause inside cfg_attr": (
            "#[cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]\nfn spin() {}\n"
        ),
        "exec_allows_no_decreases_clause in an inner attribute": "#![verifier(exec_allows_no_decreases_clause)]\n",
        "verus_verify(external_body)": "#[verus_verify(external_body)]\nfn forge() {}\n",
    }

    def test_each_uncounted_form_is_refused(self):
        for form, source in self.FORMS.items():
            with self.subTest(form):
                refused = unread_exemptions("kernel/verified/capability/mapping.rs", source)
                self.assertTrue(refused, form)
                self.assertTrue(all(line.startswith("kernel/verified/capability/mapping.rs:") for line in refused))

    def test_each_uncounted_form_fails_the_tree(self):
        for form, source in self.FORMS.items():
            with self.subTest(form):
                repo = Tests.workspace(self, {"kernel/verified": (True, {"capability/mapping.rs": source})})
                try:
                    _, refused = scan_tree(repo, DOCUMENTS)
                except Unreadable:
                    continue
                self.assertTrue(refused, form)

    def test_the_counted_forms_are_not_refused(self):
        source = (
            f"{ATTR} // a note\n// external_body(glue): x\nfn f()\n"
            "    #[verifier::exec_allows_no_decreases_clause]\n// exec_allows_no_decreases_clause(unproven): x\nfn g()\n"
            + FLUSH
        )
        self.assertEqual(unread_exemptions(ARCH_FILE, source), [])

    def test_comments_and_longer_names_are_not_refused(self):
        source = (
            "// #[verifier::external] and an axiom fn, in a comment\n"
            "/// external_fn_specification\n"
            "let axiomatic = external_bodyless; // #![verifier::external_body]\n"
        )
        self.assertEqual(unread_exemptions("a.rs", source), [])

if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
