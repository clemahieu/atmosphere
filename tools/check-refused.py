#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Hold each false claim a verified crate keeps to Verus's refusal at the postconditions it names.

A proof that verifies says only what its postconditions say. A false claim kept beside them shows
they say enough: a combinator whose serialiser does not invert its parse, claiming the combinator
interface, must fail at the interface's round trip, and were the round trip stated too weakly it
would verify. design/wire-combinators-written-here/.

A verified crate keeps its false claims in `refused/` beside its library root, one module per
claim, `refused/mod.rs` naming each as `pub mod <name>;` and the library root declaring
`#[cfg(refused)] mod refused;`. No build and no verify run sets that cfg, so they are in no image
and no verify count. Each module's opening comment holds one line per postcondition Verus must
refuse, the function whose body fails it and the clause as its source line states it, without
the trailing comma:

  //! refused: <function>: <clause>

The check, with tools/env.sh sourced, first prepares any missing or stale dependency exports via
tools/verify.py (`--no-verify`), then runs for each crate with a refused directory one `rust_verify --cfg refused --verify-module
refused::<name>...` through the cap tools/verify.py puts on rust_verify, the crates side by side.
It passes when

  every file under refused/ but mod.rs is named in mod.rs and declares at least one line, and the
  library root holds the declaration;
  each error the run reports is `postcondition not satisfied`, at a source line that is the clause
  of a line the module declares, and its body end is in that module's file, in the function the
  line names;
  each declared line is refused exactly once, and the run prints its verification results line.

It prints one line per finding to stderr, under the output of a run that has one, and exits 1, or
prints one line counting the claims and one per refusal, with where Verus refused it, and exits 0.

--coverage says, per inventory line, the refused claim that covers it or none. A module's opening
comment names the lines its claim covers, beside the refused lines:

  //! covers: <path>	<operation>	<way>

The three fields are tools/witness-inventory.py's, separated by tabs. A line is covered when a
module the refused check accepts names it. tools/refused-exempt holds the ways whose specification
admits an unchanged component, each with the clause quoted from the operation's file. An acall
line, and dispatch and enter, are covered when every way of every operation the line reaches is
covered or exempt; an arm that names no operation stays uncovered. The report is one line per
inventory line and then the count:

  <path>	<operation>	<way>	<module>[, <module>...] | exempt | entry | none
  coverage: <n> of <m> lines have no refused claim

A covers line that names an exempt way, an entry or anything but an inventory line fails the check,
as does an exemption whose clause is not a line of the operation's file. The gate's unrefused step,
which runs after this check has held each module to Verus's refusal, holds the lines that are none
to tools/unrefused (design/refused-claim-per-way/).

usage: tools/check-refused.py            the check
       tools/check-refused.py --coverage the report
       tools/check-refused.py --test     this script's own tests; one runs Verus, so tools/env.sh first
"""
import importlib.util
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from collections import namedtuple
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
REFUSED = "refused"
DECLARED = re.compile(r"^//! refused: (\w+): (.+)$", re.M)
MOD = re.compile(r"^pub mod (\w+);$", re.M)
DECLARATION = re.compile(r"#\[cfg\(refused\)\]\s*\n\s*(?:pub(?:\([a-z]+\))? )?mod refused;")
RESULTS = re.compile(r"^verification results:: (\d+) verified, (\d+) errors", re.M)
ERROR = re.compile(r"^error(?:\[\w+\])?: (.*)$")
PRIMARY = re.compile(r"^\s*--> (.+):(\d+):(\d+)$")
SECONDARY = re.compile(r"^\s*::: (.+):(\d+):(\d+)$")
FN = re.compile(r"\bfn (\w+)")
POSTCONDITION = "postcondition not satisfied"

# One false claim: the module's name, its file and the (function, clause) pairs it declares.
Claim = namedtuple("Claim", "name path refusals")
# Ways whose specification admits an unchanged component, so no claim is written. Fields, separated
# by tabs: path, operation, way, and the clause quoted from the operation's file.
EXEMPT_LIST = "tools/refused-exempt"
# dispatch and enter fold every wired operation; an acall line folds the operations its arm names.
ENTRY_FILE = "kernel/verified/capability/operation.rs"
ENTRY_OPERATIONS = {"dispatch", "enter"}
KERNEL_OPERATIONS = "kernel/verified/capability/"
CALLS = "acall/"


def claims(crate_root):
    """The crate's false claims and what is wrong with its refused directory, as (claims, findings).
    No directory is no claims."""
    directory = crate_root / REFUSED
    if not directory.is_dir():
        return [], []
    findings = []
    mod = directory / "mod.rs"
    named = set(MOD.findall(mod.read_text())) if mod.is_file() else set()
    if not mod.is_file():
        findings.append(f"{mod}: missing, so no claim beside it is compiled")
    if not DECLARATION.search((crate_root / "lib.rs").read_text()):
        findings.append(f"{crate_root / 'lib.rs'}: no `#[cfg(refused)] mod refused;`, so no claim is compiled")
    found = []
    for path in sorted(directory.glob("*.rs")):
        if path.name == "mod.rs":
            continue
        refusals = DECLARED.findall(path.read_text())
        if path.stem not in named:
            findings.append(f"{path}: not named in {mod.name}, so not compiled")
        if not refusals:
            findings.append(f"{path}: declares no `//! refused: <function>: <clause>` line")
        found.append(Claim(path.stem, path.resolve(), refusals))
    for name in sorted(named - {path.stem for path in directory.glob("*.rs")}):
        findings.append(f"{mod}: names {name}, which has no file")
    return found, findings


def source_line(path, number):
    """Line number of the file, stripped of its indentation and trailing comma, or None."""
    try:
        lines = path.read_text().splitlines()
    except OSError:
        return None
    return lines[number - 1].strip().removesuffix(",") if 0 < number <= len(lines) else None


def function_at(path, number):
    """The function the line is in: the nearest `fn` at or above it."""
    lines = path.read_text().splitlines()[:number]
    for line in reversed(lines):
        match = FN.search(line)
        if match:
            return match.group(1)
    return None


def shown(path, root):
    return path.relative_to(root) if path.is_relative_to(root) else path


def judge(output, crate_claims, root):
    """What a crate's run shows against its claims: (the findings, the refusals as (claim, function,
    the clause's place))."""
    by_file = {claim.path: claim for claim in crate_claims}
    left = {(claim.path, function, clause) for claim in crate_claims for function, clause in claim.refusals}
    refused, findings = [], []
    lines = output.splitlines()
    for index, line in enumerate(lines):
        match = ERROR.match(line)
        if match is None or match.group(1).startswith("aborting due to"):
            continue
        message = match.group(1)
        primary = PRIMARY.match(lines[index + 1]) if index + 1 < len(lines) else None
        if primary is None:
            findings.append(f"an error with no place, so the compiler's: {message}")
            continue
        clause_path = (root / primary.group(1)).resolve()
        place = f"{shown(clause_path, root)}:{primary.group(2)}"
        if message != POSTCONDITION:
            findings.append(f"{place}: an error that is not a postcondition's: {message}")
            continue
        body = None
        for later in lines[index + 2:]:
            if ERROR.match(later):
                break
            secondary = SECONDARY.match(later)
            if secondary and (root / secondary.group(1)).resolve() in by_file:
                body = ((root / secondary.group(1)).resolve(), int(secondary.group(2)))
                break
        if body is None:
            findings.append(f"{place}: a postcondition failed outside every refused module")
            continue
        claim = by_file[body[0]]
        function = function_at(*body)
        clause = source_line(clause_path, int(primary.group(2)))
        key = (claim.path, function, clause)
        if (function, clause) not in claim.refusals:
            findings.append(f"{shown(claim.path, root)}: {function} refused at {place}, a postcondition it does not declare: {clause}")
        elif key not in left:
            findings.append(f"{shown(claim.path, root)}: {function} refused twice at {place}")
        else:
            left.discard(key)
            refused.append((claim, function, place))
    if RESULTS.search(output) is None:
        findings.append("no verification results line, so the crate did not compile under cfg(refused)")
        return findings, refused
    for path, function, clause in sorted(left):
        findings.append(f"{shown(path, root)}: {function} verifies the postcondition it declares Verus refuses: {clause}")
    return findings, refused


def account(output, crate_claims, root, out_of_memory):
    """(findings, refusals) for one capped run. A run the cgroup killed for memory is reported as
    that, and its output is left unjudged."""
    if out_of_memory:
        return [f"ran out of memory: its run is capped at {verify.MEMORY_MAX}"], []
    return judge(output, crate_claims, root)


def command(crate, crate_claims, verus_out, dep_info=None):
    """rust_verify over a crate's refused modules alone. Nothing is exported, so the crate is named
    as no crate depends on it."""
    extra = ["--cfg", REFUSED]
    for claim in crate_claims:
        extra += ["--verify-module", f"{REFUSED}::{claim.name}"]
    return verify.verify_command(crate, set(), None, verus_out, extra, dep_info=dep_info)


def run(crate, crate_claims, root):
    """The crate's refused modules, through the cap tools/verify.py puts on rust_verify. The output,
    and whether the cgroup killed the run for memory."""
    verus_out = root / "target" / "verus"
    verus_out.mkdir(parents=True, exist_ok=True)
    dep_info = verus_out / f"refused-{crate['crate']}.d"
    unit = f"atmo-refused-{os.getpid()}-{crate['crate']}"
    with tempfile.TemporaryFile() as captured:
        _, out_of_memory = verify.run_capped(
            command(crate, crate_claims, verus_out, dep_info=dep_info),
            unit,
            verify.MEMORY_MAX,
            cwd=root,
            stdin=subprocess.DEVNULL,
            stdout=captured,
            stderr=subprocess.STDOUT,
        )
        captured.flush()
        captured.seek(0)
        return captured.read().decode(), out_of_memory


def check(crates, root):
    """Each crate as (crate, its claims, the tree's findings), run and judged: (findings, the
    report's lines)."""
    findings = [finding for _, _, tree in crates for finding in tree]
    if findings:
        return findings, []
    with_some = [(crate, crate_claims) for crate, crate_claims, _ in crates if crate_claims]
    if with_some:
        verify.prepare_deps([crate for crate, _, _ in crates], {crate["package"] for crate, _ in with_some}, root)
    with ThreadPoolExecutor(max_workers=max(1, len(with_some))) as pool:
        ran = list(pool.map(lambda pair: run(pair[0], pair[1], root), with_some))
    report = []
    for (crate, crate_claims), (output, out_of_memory) in zip(with_some, ran):
        crate_findings, refused = account(output, crate_claims, root, out_of_memory)
        if crate_findings:
            print(output, file=sys.stderr)
        findings += [f"{crate['package']}: {finding}" for finding in crate_findings]
        report += [f"  {shown(claim.path, root)}: {function} refused at {place}: postcondition not satisfied"
                   for claim, function, place in refused]
    count = sum(len(crate_claims) for _, crate_claims in with_some)
    plural = lambda n, word: f"{n} {word}{'' if n == 1 else 's'}"
    return findings, [f"refused: {plural(count, 'false claim')} in {plural(len(with_some), 'crate')}, each refused by "
                      f"Verus at the postconditions it declares and nowhere else", *report]


def normalize_clause(line):
    """A source line as an exemption quotes it: its indentation, a leading &&& and a trailing comma
    removed."""
    text = line.strip()
    if text.startswith("&&&"):
        text = text[3:].strip()
    return text.removesuffix(",")


def clause_lines(text):
    """The file's lines as an exemption would quote them."""
    return {normalize_clause(line) for line in text.splitlines()} - {""}


def is_entry(path, operation):
    """Whether the inventory line is an entry: an acall wrapper, or dispatch or enter."""
    return path.startswith(CALLS) or (path == ENTRY_FILE and operation in ENTRY_OPERATIONS)


def covers_in(text, module):
    """The covers lines of one module, and the lines that are not path, operation and way."""
    findings, found = [], []
    for raw in text.splitlines():
        if not raw.startswith("//! covers:"):
            continue
        match = re.fullmatch(r"//! covers: ([^\t]+)\t([^\t]+)\t([^\t]+)", raw)
        if match is None:
            findings.append(f"{module}: a covers line is not path, operation and way separated by tabs: {raw}")
            continue
        found.append((*match.groups(), module))
    return findings, found


def exemptions_in(text):
    """The exemption list's lines, and the lines that are not path, operation, way and clause."""
    findings, found = [], []
    for raw in text.splitlines():
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != 4:
            findings.append(f"{EXEMPT_LIST}: a line has {len(fields)} fields, not path, operation, way and clause: {raw}")
            continue
        found.append(tuple(fields))
    return findings, found


def kernel_operation_ways(rows):
    """Each kernel operation's inventory lines, entries left out, by the operation's name."""
    found = {}
    for row in rows:
        if is_entry(row.path, row.operation) or not row.path.startswith(KERNEL_OPERATIONS):
            continue
        found.setdefault(row.operation, []).append((row.path, row.operation, row.way))
    return found


def reached_operations(row, wired):
    """The operations an entry line reaches, or None when its arm names none."""
    if row.path.startswith(CALLS):
        if not row.witness:
            return None
        return row.witness.split(", ")
    return sorted(wired)


def account_covers(rows, covers, exemptions, clauses_by_path, wired):
    """What covers the inventory: (findings, one (path, operation, way, status) per row).

    `covers` is (path, operation, way, module). `exemptions` is (path, operation, way, clause).
    `clauses_by_path` is the operation file's quoted lines, or None when the file is absent.
    `wired` is the operations dispatch calls. A line's status is `exempt`, `entry`, the module that
    covers it, or `none`."""
    findings = []
    inventory = {(row.path, row.operation, row.way) for row in rows}
    exempt = set()
    for path, operation, way, clause in exemptions:
        key = (path, operation, way)
        if key not in inventory:
            findings.append(f"{EXEMPT_LIST}: {path}\t{operation}\t{way} is not an inventory line")
            continue
        clauses = clauses_by_path.get(path)
        if clauses is None or clause not in clauses:
            findings.append(f"{EXEMPT_LIST}: {path}\t{operation}\t{way} quotes {clause!r}, which is not a line of {path}")
            continue
        exempt.add(key)
    by_module = {}
    for path, operation, way, module in covers:
        shown_line = f"{path}\t{operation}\t{way}"
        key = (path, operation, way)
        if key not in inventory:
            findings.append(f"{module}: covers {shown_line}, which is not an inventory line")
        elif key in exempt:
            findings.append(f"{module}: covers {shown_line}, which is exempt")
        elif is_entry(path, operation):
            findings.append(f"{module}: covers {shown_line}, an entry a claim does not cover")
        else:
            by_module.setdefault(key, []).append(module)
    ways = kernel_operation_ways(rows)

    def satisfied(names):
        if not names:
            return False
        for name in names:
            lines = ways.get(name)
            if not lines:
                return False
            for line in lines:
                if line not in by_module and line not in exempt:
                    return False
        return True

    report = []
    for row in rows:
        key = (row.path, row.operation, row.way)
        if key in exempt:
            status = "exempt"
        elif is_entry(row.path, row.operation):
            names = reached_operations(row, wired)
            status = "entry" if names is not None and satisfied(names) else "none"
        elif key in by_module:
            status = ", ".join(sorted(set(by_module[key])))
        else:
            status = "none"
        report.append((*key, status))
    return findings, report


def format_coverage(report):
    """The report as the gate reads it, and the count of the lines that are none."""
    none = sum(status == "none" for *_, status in report)
    lines = ["\t".join(row) for row in report]
    lines.append(f"coverage: {none} of {len(report)} lines have no refused claim")
    return "\n".join(lines) + "\n"


def load_witness_inventory():
    """tools/witness-inventory.py, whose file name is not a module name."""
    spec = importlib.util.spec_from_file_location(
        "witness_inventory", Path(__file__).resolve().parent / "witness-inventory.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def covers_of(root):
    """The covers lines of the modules the refused directory structure accepts, and what is wrong
    with a directory. A crate whose directory the refused check would reject contributes none: the
    gate runs this after that check has held each accepted module to Verus's refusal."""
    findings, covers = [], []
    for crate in verify.marked_crates(verify.cargo_metadata()):
        crate_root = Path(crate["src"]).parent
        found, tree = claims(crate_root)
        if tree:
            findings += [f"{crate['package']}: {finding}" for finding in tree]
            continue
        for claim in found:
            module = str(shown(claim.path, root))
            module_findings, module_covers = covers_in(claim.path.read_text(), module)
            findings += module_findings
            covers += module_covers
    return findings, covers


def coverage(root):
    """(findings, the report's rows) for the tree."""
    inventory = load_witness_inventory()
    try:
        rows = inventory.tree_rows(root)
        wired = inventory.wired_operations(root)
    except inventory.Unreadable as error:
        return [str(error)], []
    findings, covers = covers_of(root)
    exempt_path = root / EXEMPT_LIST
    exempt_findings, exemptions = exemptions_in(exempt_path.read_text() if exempt_path.is_file() else "")
    findings += exempt_findings
    clauses = {}
    for path, _, _, _ in exemptions:
        if path not in clauses:
            file = root / path
            clauses[path] = clause_lines(file.read_text()) if file.is_file() else None
    more, report = account_covers(rows, covers, exemptions, clauses, wired)
    return findings + more, report


def main(args):
    if args == ["--coverage"]:
        findings, report = coverage(REPO)
        if findings:
            print("\n".join(f"coverage: {finding}" for finding in findings), file=sys.stderr)
            return 1
        print(format_coverage(report), end="")
        return 0
    if args:
        sys.exit(__doc__.split("usage: ")[1].join(("usage: ", "")).rstrip())
    crates = [(crate, *claims(Path(crate["src"]).parent)) for crate in verify.marked_crates(verify.cargo_metadata())]
    findings, report = check(crates, REPO)
    if findings:
        print("\n".join(f"refused: {finding}" for finding in findings), file=sys.stderr)
        return 1
    print("\n".join(report))
    return 0


CLAIM = """// SPDX-License-Identifier: MIT

//! A claim.
//!
//! refused: lemma_round: self.round(v) == v
//! refused: lemma_other: self.other(v)

verus! {
impl Thing for Wrong {
    proof fn lemma_round(&self, v: u8) {
    }

    proof fn lemma_other(&self, v: u8)
    {
        assert(true);
    }
}
}
"""

LIB = """// SPDX-License-Identifier: MIT
#[cfg(refused)]
mod refused;

verus! {
pub trait Thing {
    proof fn lemma_round(&self, v: u8)
        ensures
            self.round(v) == v,
    ;

    proof fn lemma_other(&self, v: u8)
        ensures
            self.other(v),
            self.third(v),
    ;
}
}
"""


def refusal(clause_line, body_line, message=POSTCONDITION):
    return (f"error: {message}\n   --> src/lib.rs:{clause_line}:13\n    |\n    | ...\n"
            f"   ::: src/refused/wrong.rs:{body_line}:9\n    |\n")


RESULTS_LINE = "verification results:: 3 verified, 2 errors (partial verification with `--verify-*`)\n"


class Tests(unittest.TestCase):
    def tree(self, files):
        root = Path(self.enterContext(tempfile.TemporaryDirectory()))
        for path, text in files.items():
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_text(text)
        return root.resolve()

    def crate(self, extra=None, lib=LIB):
        files = {"src/lib.rs": lib, "src/refused/mod.rs": "pub mod wrong;\n", "src/refused/wrong.rs": CLAIM}
        files.update(extra or {})
        root = self.tree(files)
        return root, *claims(root / "src")

    def test_a_crate_without_the_directory_has_no_claims(self):
        root = self.tree({"src/lib.rs": "\n"})
        self.assertEqual(claims(root / "src"), ([], []))

    def test_the_claims_are_the_modules_with_what_each_declares(self):
        root, found, findings = self.crate()
        self.assertEqual(findings, [])
        self.assertEqual(found, [Claim("wrong", root / "src/refused/wrong.rs",
                                       [("lemma_round", "self.round(v) == v"), ("lemma_other", "self.other(v)")])])

    def test_a_module_mod_rs_does_not_name_or_one_declaring_nothing_is_a_finding(self):
        _, _, findings = self.crate({"src/refused/extra.rs": "// nothing declared\n"})
        self.assertEqual(len(findings), 2)
        self.assertIn("extra.rs: not named in mod.rs", findings[0])
        self.assertIn("extra.rs: declares no", findings[1])

    def test_a_library_root_without_the_declaration_is_a_finding(self):
        _, _, findings = self.crate(lib="// SPDX-License-Identifier: MIT\n")
        self.assertEqual(len(findings), 1)
        self.assertIn("no `#[cfg(refused)] mod refused;`", findings[0])

    def test_each_declared_postcondition_refused_once_passes(self):
        root, found, _ = self.crate()
        output = refusal(9, 10) + refusal(14, 15) + RESULTS_LINE
        findings, refused = judge(output, found, root)
        self.assertEqual(findings, [])
        self.assertEqual([(function, place) for _, function, place in refused],
                         [("lemma_round", "src/lib.rs:9"), ("lemma_other", "src/lib.rs:14")])

    def test_a_declared_postcondition_that_verifies_is_a_finding(self):
        root, found, _ = self.crate()
        findings, _ = judge(refusal(9, 10) + RESULTS_LINE, found, root)
        self.assertEqual(findings, ["src/refused/wrong.rs: lemma_other verifies the postcondition it declares Verus refuses: self.other(v)"])

    def test_a_refusal_at_an_undeclared_postcondition_is_a_finding(self):
        root, found, _ = self.crate()
        findings, _ = judge(refusal(9, 10) + refusal(14, 15) + refusal(15, 15) + RESULTS_LINE, found, root)
        self.assertEqual(findings, ["src/refused/wrong.rs: lemma_other refused at src/lib.rs:15, a postcondition it does not declare: self.third(v)"])

    def test_a_refusal_in_the_wrong_function_is_a_finding(self):
        root, found, _ = self.crate()
        findings, _ = judge(refusal(9, 15) + refusal(14, 15) + RESULTS_LINE, found, root)
        self.assertIn("lemma_other refused at src/lib.rs:9, a postcondition it does not declare: self.round(v) == v", findings[0])

    def test_an_error_other_than_a_postcondition_is_a_finding(self):
        root, found, _ = self.crate()
        findings, _ = judge(refusal(9, 10) + refusal(14, 15) + refusal(16, 16, "assertion failed") + RESULTS_LINE, found, root)
        self.assertEqual(findings, ["src/lib.rs:16: an error that is not a postcondition's: assertion failed"])

    def test_a_postcondition_failed_outside_the_claims_is_a_finding(self):
        root, found, _ = self.crate()
        outside = "error: postcondition not satisfied\n   --> src/lib.rs:9:13\n   ::: src/other.rs:3:1\n"
        findings, _ = judge(refusal(9, 10) + refusal(14, 15) + outside + RESULTS_LINE, found, root)
        self.assertEqual(findings, ["src/lib.rs:9: a postcondition failed outside every refused module"])

    def test_a_run_that_did_not_compile_is_a_finding(self):
        root, found, _ = self.crate()
        findings, _ = judge("error[E0425]: cannot find value\n   --> src/lib.rs:3:1\n", found, root)
        self.assertEqual(findings, ["src/lib.rs:3: an error that is not a postcondition's: cannot find value",
                                    "no verification results line, so the crate did not compile under cfg(refused)"])

    def test_a_run_killed_for_memory_is_reported_unjudged(self):
        root, found, _ = self.crate()
        self.assertEqual(account("", found, root, True), ([f"ran out of memory: its run is capped at {verify.MEMORY_MAX}"], []))

    def test_check_prepares_dependencies_before_running_refused(self):
        root, found, tree = self.crate()
        dep = {"package": "dep", "crate": "dep", "src": str(root / "dep/lib.rs"), "deps": [], "plain": []}
        crate = {"package": "user", "crate": "user", "src": str(root / "src/lib.rs"),
                 "deps": [{"extern": "dep", "crate": "dep", "package": "dep"}], "plain": []}
        order = []

        def fake_prepare(crates, targets, target_root=REPO, triple=None):
            order.append(("prepare", [c["package"] for c in crates], set(targets), target_root))

        def fake_run(target_crate, target_claims, target_root):
            order.append(("run", target_crate["package"]))
            return "refused-output", False

        module = sys.modules[__name__]
        with (mock.patch.object(verify, "prepare_deps", side_effect=fake_prepare),
              mock.patch.object(module, "run", side_effect=fake_run),
              mock.patch.object(module, "account", return_value=([], []))):
            findings, _ = check([(dep, [], []), (crate, found, tree)], root)
        self.assertEqual(findings, [])
        self.assertEqual(order[0], ("prepare", ["dep", "user"], {"user"}, root))
        self.assertEqual(order[1], ("run", "user"))

    def test_run_requests_dep_info_in_target_verus(self):
        root, found, _ = self.crate()
        crate = {"package": "aheap", "crate": "aheap", "src": str(root / "src/lib.rs"), "deps": [], "plain": []}
        calls = []

        def fake_capped(cmd, unit, memory_max, **kwargs):
            calls.append(cmd)
            kwargs["stdout"].write(b"verification results:: 0 verified, 1 errors\n")
            return 1, False

        with mock.patch.object(verify, "run_capped", side_effect=fake_capped):
            run(crate, found, root)
        expected = root / "target" / "verus" / "refused-aheap.d"
        self.assertEqual(calls[0][-2:], ["--", f"--emit=dep-info={expected}"])


class Verus(unittest.TestCase):
    """awire's combinator that serialises little-endian what it parses big-endian, under Verus: as
    the tree holds it, and made to invert its parse, when the check must fail."""

    INVERTING = (
        ("seq![v as u8, (v >> 8u16) as u8]", "seq![(v >> 8u16) as u8, v as u8]"),
        ("out[pos] = *v as u8;\n        out[pos + 1] = (*v >> 8u16) as u8;",
         "out[pos] = (*v >> 8u16) as u8;\n        out[pos + 1] = *v as u8;"),
    )

    def copy(self):
        root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        shutil.copytree(REPO / "awire" / "src", root / "src")
        return root

    def checked(self, root):
        crate = {"package": "awire", "crate": "awire", "src": str(root / "src" / "lib.rs"), "deps": [], "plain": []}
        found, tree = claims(root / "src")
        self.assertEqual(tree, [])
        return check([(crate, found, tree)], root)

    def test_the_combinator_that_does_not_invert_is_refused_at_the_round_trip(self):
        findings, report = self.checked(self.copy())
        self.assertEqual(findings, [])
        # The interface example is refused at its round trip. Other claims in the tree are too;
        # findings above is what holds every one of them.
        names = [line.split(" refused at ")[0].strip() for line in report[1:]]
        self.assertIn("src/refused/u16_be_le.rs: lemma_parse_serialize", names)
        self.assertIn("src/refused/u16_be_le.rs: lemma_serialize_parse", names)

    def test_the_check_fails_when_the_combinator_is_made_to_invert(self):
        root = self.copy()
        path = root / "src" / REFUSED / "u16_be_le.rs"
        text = path.read_text()
        for old, new in self.INVERTING:
            self.assertIn(old, text)
            text = text.replace(old, new)
        path.write_text(text)
        with open(os.devnull, "w") as quiet:
            stderr, sys.stderr = sys.stderr, quiet
            try:
                findings, _ = self.checked(root)
            finally:
                sys.stderr = stderr
        self.assertEqual(findings, [
            "awire: src/refused/u16_be_le.rs: lemma_parse_serialize verifies the postcondition it declares Verus refuses: "
            "self.spec_parse(s) matches Some((n, v)) ==> self.spec_serialize(v) == s.take(n as int)",
            "awire: src/refused/u16_be_le.rs: lemma_serialize_parse verifies the postcondition it declares Verus refuses: "
            "self.spec_parse(self.spec_serialize(v) + rest) == Some((self.spec_serialize(v).len(), v))",
        ])

    def test_a_crate_with_a_marked_dependency_refuses_without_a_prior_verify_run(self):
        root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        rev = verify.pinned_commit(REPO / "Cargo.toml")
        (root / "Cargo.toml").write_text(
            '[workspace]\nmembers = []\n\n[workspace.dependencies.vstd]\n'
            f'git = "https://github.com/verus-lang/verus"\nrev = "{rev}"\n'
        )
        for rel, content in [
            ("dep/src/lib.rs", "use vstd::prelude::*;\nverus! {\npub fn two() -> (r: u32) ensures r == 2u32 { 2u32 }\n}\n"),
            ("user/src/lib.rs", "use vstd::prelude::*;\n#[cfg(refused)]\nmod refused;\nverus! {\npub trait Two {\n    fn doubled(&self) -> (r: u32)\n        ensures\n            r == 4u32,\n    ;\n}\n}\n"),
            ("user/src/refused/mod.rs", "pub mod bad;\n"),
            ("user/src/refused/bad.rs", "//! refused: doubled: r == 4u32\nuse vstd::prelude::*;\nverus! {\nstruct Bad;\nimpl crate::Two for Bad {\n    fn doubled(&self) -> (r: u32) {\n        dep::two() - 1u32\n    }\n}\n}\n"),
        ]:
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        dep = {"package": "dep", "crate": "dep", "src": str(root / "dep/src/lib.rs"), "deps": [], "plain": []}
        user = {"package": "user", "crate": "user", "src": str(root / "user/src/lib.rs"),
                "deps": [{"extern": "dep", "crate": "dep", "package": "dep"}], "plain": []}
        found, tree = claims(root / "user/src")
        self.assertEqual(tree, [])
        findings, _ = check([(dep, [], []), (user, found, tree)], root)
        self.assertEqual(findings, [])


class Coverage(unittest.TestCase):
    """The tie from a covers line or an exemption to an inventory line. Rows are the inventory's."""

    Row = namedtuple("Row", "path operation way witness")

    def ways(self, *rows):
        return [self.Row(*row) for row in rows]

    def account(self, rows, covers=(), exemptions=(), clauses=None, wired=frozenset()):
        return account_covers(rows, covers, exemptions, {} if clauses is None else clauses, wired)

    def test_a_covers_line_names_the_module_and_an_uncovered_way_is_none(self):
        rows = self.ways(("k/retype.rs", "reclaim", "Freed", None), ("k/unmap.rs", "unmap_at", "Some", None))
        findings, report = self.account(rows, [("k/retype.rs", "reclaim", "Freed", "k/refused/reclaim.rs")])
        self.assertEqual(findings, [])
        self.assertEqual(report, [
            ("k/retype.rs", "reclaim", "Freed", "k/refused/reclaim.rs"),
            ("k/unmap.rs", "unmap_at", "Some", "none"),
        ])

    def test_two_modules_covering_one_way_are_both_named(self):
        rows = self.ways(("k/a.rs", "parse", "returns", None))
        _, report = self.account(rows, [("k/a.rs", "parse", "returns", "k/refused/b.rs"),
                                        ("k/a.rs", "parse", "returns", "k/refused/a.rs")])
        self.assertEqual(report[0][3], "k/refused/a.rs, k/refused/b.rs")

    def test_an_exemption_whose_clause_is_a_line_of_the_file_is_exempt(self):
        rows = self.ways(("k/reclaim.rs", "reclaim", "Again", None))
        clause = "ret is Again ==> post == pre"
        findings, report = self.account(
            rows, exemptions=[("k/reclaim.rs", "reclaim", "Again", clause)],
            clauses={"k/reclaim.rs": {clause, "something else"}})
        self.assertEqual(findings, [])
        self.assertEqual(report[0][3], "exempt")

    def test_a_covers_line_that_is_not_an_inventory_line_or_names_an_exempt_way_or_an_entry_fails(self):
        rows = self.ways(("k/reclaim.rs", "reclaim", "Again", None),
                         ("acall/src/m.rs", "nap", "OPERATION_NAP=9", None))
        clause = "ret is Again ==> post == pre"
        findings, _ = self.account(
            rows,
            [("k/gone.rs", "gone", "true", "k/refused/gone.rs"),
             ("k/reclaim.rs", "reclaim", "Again", "k/refused/again.rs"),
             ("acall/src/m.rs", "nap", "OPERATION_NAP=9", "k/refused/nap.rs")],
            [("k/reclaim.rs", "reclaim", "Again", clause)],
            {"k/reclaim.rs": {clause}})
        self.assertEqual(findings, [
            "k/refused/gone.rs: covers k/gone.rs\tgone\ttrue, which is not an inventory line",
            "k/refused/again.rs: covers k/reclaim.rs\treclaim\tAgain, which is exempt",
            "k/refused/nap.rs: covers acall/src/m.rs\tnap\tOPERATION_NAP=9, an entry a claim does not cover",
        ])

    def test_an_exemption_that_is_not_an_inventory_line_or_whose_clause_is_not_in_the_file_fails(self):
        rows = self.ways(("k/reclaim.rs", "reclaim", "Again", None))
        findings, report = self.account(
            rows,
            exemptions=[("k/gone.rs", "gone", "true", "post == pre"),
                        ("k/reclaim.rs", "reclaim", "Again", "post == pre")],
            clauses={"k/reclaim.rs": {"ret is Again ==> post == pre"}})
        self.assertEqual(findings, [
            "tools/refused-exempt: k/gone.rs\tgone\ttrue is not an inventory line",
            "tools/refused-exempt: k/reclaim.rs\treclaim\tAgain quotes 'post == pre', which is not a line of k/reclaim.rs",
        ])
        # A quote the file does not hold exempts nothing, so the way stays uncovered.
        self.assertEqual(report[0][3], "none")

    def test_an_entry_is_covered_when_every_way_it_reaches_is_covered_or_exempt(self):
        rows = self.ways(
            ("kernel/verified/capability/delete.rs", "delete", "Some", None),
            ("kernel/verified/capability/delete.rs", "delete", "Again", None),
            ("acall/src/m.rs", "delete", "OPERATION_DELETE=5", "delete"),
            ("acall/src/m.rs", "empty", "OPERATION_EMPTY=8", None),
            ("kernel/verified/capability/operation.rs", "dispatch", "Some", "witness_root_dispatches"),
            ("kernel/verified/capability/operation.rs", "enter", "Some", "witness_root_enters_the_kernel"))
        clause = "ret is Again ==> post == pre"
        covers = [("kernel/verified/capability/delete.rs", "delete", "Some", "k/refused/delete.rs")]
        exemptions = [("kernel/verified/capability/delete.rs", "delete", "Again", clause)]
        findings, report = self.account(
            rows, covers, exemptions, {"kernel/verified/capability/delete.rs": {clause}}, {"delete"})
        self.assertEqual(findings, [])
        self.assertEqual([status for *_, status in report], ["k/refused/delete.rs", "exempt", "entry", "none", "entry", "entry"])
        # One way of the operation still open, and the entry stays none.
        _, open_report = self.account(rows, (), exemptions, {"kernel/verified/capability/delete.rs": {clause}}, {"delete"})
        self.assertEqual([status for *_, status in open_report], ["none", "exempt", "none", "none", "none", "none"])

    def test_an_entry_whose_arm_names_an_operation_the_inventory_lacks_stays_uncovered(self):
        rows = self.ways(("acall/src/m.rs", "nap", "OPERATION_NAP=9", "missing"))
        _, report = self.account(rows, wired={"missing"})
        self.assertEqual(report[0][3], "none")

    def test_a_covers_line_and_an_exemption_line_are_read_as_tabs(self):
        findings, found = covers_in("//! covers: k/a.rs\top\tway\n//! covers: not tabs\n", "k/refused/a.rs")
        self.assertEqual(found, [("k/a.rs", "op", "way", "k/refused/a.rs")])
        self.assertEqual(findings, ["k/refused/a.rs: a covers line is not path, operation and way separated by tabs: //! covers: not tabs"])
        findings, found = exemptions_in("# header\n\nk/a.rs\top\tway\tpost == pre\nk/a.rs\top\n")
        self.assertEqual(found, [("k/a.rs", "op", "way", "post == pre")])
        self.assertEqual(findings, ["tools/refused-exempt: a line has 2 fields, not path, operation, way and clause: k/a.rs\top"])

    def test_a_quoted_clause_drops_the_indentation_the_conjunction_and_the_comma(self):
        self.assertEqual(normalize_clause("            ret is Again ==> post == pre,"), "ret is Again ==> post == pre")
        self.assertEqual(normalize_clause("        &&& !(ret is Freed) ==> post == pre"), "!(ret is Freed) ==> post == pre")
        self.assertIn("!(ret is Freed) ==> post == pre", clause_lines((REPO / "kernel/verified/capability/reclaim.rs").read_text()))

    def test_each_recorded_exemption_quotes_a_line_of_its_file(self):
        findings, parsed = exemptions_in((REPO / EXEMPT_LIST).read_text())
        self.assertEqual(findings, [])
        self.assertTrue(parsed)
        for path, operation, way, clause in parsed:
            self.assertIn(clause, clause_lines((REPO / path).read_text()), f"{operation} {way}")


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    else:
        sys.exit(main(sys.argv[1:]))
