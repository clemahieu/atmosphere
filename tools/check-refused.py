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

The check, with tools/env.sh sourced and after tools/verify.py, whose exported dependencies it
reads: for each crate with a refused directory, one `rust_verify --cfg refused --verify-module
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

usage: tools/check-refused.py          the check
       tools/check-refused.py --test   this script's own tests; one runs Verus, so tools/env.sh first
"""
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


def command(crate, crate_claims, verus_out):
    """rust_verify over a crate's refused modules alone. Nothing is exported, so the crate is named
    as no crate depends on it."""
    extra = ["--cfg", REFUSED]
    for claim in crate_claims:
        extra += ["--verify-module", f"{REFUSED}::{claim.name}"]
    return verify.verify_command(crate, set(), None, verus_out, extra)


def run(crate, crate_claims, root):
    """The crate's refused modules, through the cap tools/verify.py puts on rust_verify. The output,
    and whether the cgroup killed the run for memory."""
    unit = f"atmo-refused-{os.getpid()}-{crate['crate']}"
    with tempfile.TemporaryFile() as captured:
        _, out_of_memory = verify.run_capped(
            command(crate, crate_claims, root / "target" / "verus"),
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


def main(args):
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
        self.assertEqual([line.split(" refused at ")[0].strip() for line in report[1:]],
                         ["src/refused/u16_be_le.rs: lemma_parse_serialize",
                          "src/refused/u16_be_le.rs: lemma_serialize_parse"])

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


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    else:
        sys.exit(main(sys.argv[1:]))
