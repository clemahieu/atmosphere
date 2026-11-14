#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Hold every root witness to a throwaway that Verus refuses at its own site.

A witness shows a use is reachable only while what it takes from boot is consistent: from
contradictory premises anything verifies. Its throwaway is a function with the witness's parameters
and its requires word for word, a body that is one call of the witness, and `ensures false`. Verus
must refuse it. design/witness-per-way-an-operation-succeeds/, point 5.

The witnesses are found from the source of each crate tools/verify.py verifies: every exec
`pub fn witness_<x>` outside a throwaway module. A root witness, the record's point 3, is

  a method   whose requires holds the conjunct `old(self).booted(...)` and names `self` nowhere else,
             or names `self` nowhere;
  a function whose parameters name no struct or enum its crate declares.

For the root witness `witness_<x>` in `<dir>/<file>.rs` the throwaway is `throwaway_<x>`, alone in
`<dir>/throwaway/<x>.rs`, with `<dir>/throwaway/mod.rs` naming each module and the parent of <dir>'s
modules declaring `#[cfg(throwaway)] pub mod throwaway;`. No build and no verify run sets that cfg, so
a throwaway is in no image and no verify count. The files are this script's to write: it derives each
from the witness's text, with the `use` lines of the witness's file, and the check holds the tree to
exactly those bytes, so a witness whose requires or parameters change fails the check until
--write has been run again.

The check, with tools/env.sh sourced and after tools/verify.py, whose exported dependencies it reads:
for each crate with a throwaway, one `rust_verify --cfg throwaway --verify-module <module>...` at
the verify budget, the crates side by side. Each of those runs goes through the cap tools/verify.py
puts on rust_verify: verify.MEMORY_MAX in a systemd user scope of its own with no swap, so a
throwaway that grows without bound is killed by its cgroup rather than by the kernel's OOM killer.
A run killed for memory is reported as such and fails the check. It passes when

  every root witness has its throwaway file, byte for byte, and no other file is under throwaway/;
  each run verifies nothing and reports exactly one error per throwaway, located in its file;
  each error is `postcondition not satisfied` or the solver budget's (`resource limit (rlimit)
  exceeded`: a solver that ran out looking for a contradiction did not find one), and none is a
  precondition's, which would mean the requires is not the witness's, or the compiler's.

It prints one line per finding to stderr, under the output of a run that has one, and exits 1, or
prints one line counting the throwaways and exits 0.

usage: tools/check-throwaways.py            the check
       tools/check-throwaways.py --write    write the throwaway files the witnesses ask for, remove
                                            the others, and name each parent that lacks the declaration
       tools/check-throwaways.py --list     each witness, as `root` or `not root: <why>`
       tools/check-throwaways.py --test     this script's own tests
"""
import os
import re
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
THROWAWAY = "throwaway"
WITNESS_FN = re.compile(r"^([ \t]*)pub fn witness_(\w+)", re.M)
IMPL = re.compile(r"^impl\b[^{;]*\{", re.M)
USE = re.compile(r"^use\b[^;]*;", re.M)
VERUS_OPEN = re.compile(r"^verus! \{", re.M)
DECLARED = re.compile(r"\b(?:struct|enum)\s+(\w+)")
DECLARATION = re.compile(r"#\[cfg\(throwaway\)\]\s*\n\s*(?:pub(?:\([a-z]+\))? )?mod throwaway;")
BOOTED = re.compile(r"old\(self\)\.booted\(")
SELF = re.compile(r"\bself\b")
CLAUSE = re.compile(r"\b(requires|ensures|fn)\b|[(\[{]|[)\]}]")
RESULTS = re.compile(r"^verification results:: (\d+) verified, (\d+) errors", re.M)
ERROR = re.compile(r"^error(?:\[\w+\])?: (.*)$")
LOCATION = re.compile(r"^\s*--> (.+):(\d+):(\d+)$")
POSTCONDITION = "postcondition not satisfied"
BUDGET = "resource limit (rlimit) exceeded"

# A witness as the source gives it. `impl` is the header of the impl block a method is in, or None.
Witness = namedtuple("Witness", "name file indent generics params requires receiver impl")
# A throwaway the tree must hold: its witness's name, its file, the bytes of it, its module path.
Throwaway = namedtuple("Throwaway", "name path text module")


class Malformed(Exception):
    """A witness this script cannot read; its message names it."""


def masked(text):
    """The text with every comment and string literal blanked, each character in its place, so that
    brackets and words found in it are the code's."""
    out, i, n = list(text), 0, len(text)
    while i < n:
        if text.startswith("//", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
        elif text.startswith("/*", i):
            end = text.find("*/", i)
            end = n if end < 0 else end + 2
        elif text[i] == '"':
            end = i + 1
            while end < n and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            end = min(end + 1, n)
        else:
            i += 1
            continue
        for j in range(i, end):
            if out[j] != "\n":
                out[j] = " "
        i = end
    return "".join(out)


def closing(code, start, pair):
    """The index of the bracket that closes the one at `start`; `pair` is the two characters."""
    depth = 0
    for i in range(start, len(code)):
        if code[i] == pair[0]:
            depth += 1
        elif code[i] == pair[1] and code[i - 1] != "-":
            depth -= 1
            if depth == 0:
                return i
    raise Malformed(f"unclosed {pair[0]}")


def parameters(code):
    """The parameters of a masked parameter list, split at its own commas."""
    parts, depth, start = [], 0, 0
    for i, char in enumerate(code):
        if char in "([{<":
            depth += 1
        elif char in ")]}" or (char == ">" and code[i - 1] != "-"):
            depth -= 1
        elif char == "," and depth == 0:
            parts.append(code[start:i])
            start = i + 1
    parts.append(code[start:])
    return [part.strip() for part in parts if part.strip()]


def clause(code, start):
    """The first of `requires`, `ensures` and `fn` after `start` that no bracket opened after `start`
    encloses, as (word, index), or (None, end of text)."""
    depth = 0
    for match in CLAUSE.finditer(code, start):
        if match.group(1) is None:
            depth += 1 if match.group(0) in "([{" else -1
        elif depth == 0:
            return match.group(1), match.start()
    return None, len(code)


def witnesses(text, file):
    """Every exec `pub fn witness_` of a source file's text, in its order."""
    code = masked(text)
    found = []
    for match in WITNESS_FN.finditer(code):
        name, at = match.group(2), match.end()
        try:
            generics = ""
            if code[at] == "<":
                end = closing(code, at, "<>")
                generics, at = text[at:end + 1], end + 1
            if code[at] != "(":
                raise Malformed("no parameter list")
            close = closing(code, at, "()")
            word, first = clause(code, close + 1)
            requires = ""
            if word == "requires":
                word, second = clause(code, first + len("requires"))
                requires = text[first:second].rstrip()
            if word != "ensures":
                raise Malformed("no ensures, so it claims nothing")
        except Malformed as error:
            raise Malformed(f"{file}: witness_{name}: {error}") from None
        receiver = any(SELF.search(part) and ":" not in part for part in parameters(code[at + 1:close]))
        impl = None
        if receiver:
            headers = [header for header in IMPL.finditer(code, 0, match.start())]
            if not headers:
                raise Malformed(f"{file}: witness_{name}: a method outside an impl block")
            impl = text[headers[-1].start():headers[-1].end()]
        found.append(Witness(name, file, match.group(1), generics, text[at + 1:close], requires, receiver, impl))
    return found


def not_root(witness, declared):
    """Why a witness is not a root witness, or None when it is one. `declared` is the structs and enums
    its crate declares."""
    if not witness.receiver:
        taken = sorted(set(re.findall(r"\w+", masked(witness.params))) & declared)
        return f"takes {', '.join(taken)}, which its crate declares" if taken else None
    body = masked(witness.requires)[len("requires"):]
    if SELF.search(body) is None:
        return None
    match = BOOTED.search(body)
    if match is None:
        return "its requires has no old(self).booted(...)"
    end = closing(body, match.end() - 1, "()")
    before, after = body[:match.start()].rstrip(), body[end + 1:].lstrip()
    if (before and not before.endswith(",")) or (after and not after.startswith(",")):
        return "old(self).booted(...) is not a conjunct of its requires by itself"
    if SELF.search(before + after):
        return "its requires names self outside old(self).booted(...)"
    return None


def module_of(file, crate_root):
    """The module path of a source file in the crate whose root file is `crate_root`, or '' for the root."""
    relative = file.relative_to(crate_root.parent).with_suffix("")
    parts = list(relative.parts)
    if file == crate_root or parts[-1] == "mod":
        parts.pop()
    return "::".join(parts)


def throwaway_text(witness, text, witness_module):
    """The bytes of the throwaway of a witness whose file holds `text`."""
    opened = VERUS_OPEN.search(text)
    if opened is None:
        raise Malformed(f"{witness.file}: no `verus! {{` line")
    uses = [(match.start() < opened.start(), match.group(0)) for match in USE.finditer(text)]
    outside = [use for out, use in uses if out]
    inside = [use for out, use in uses if not out] + [f"use crate::{witness_module}::*;" if witness_module else "use crate::*;"]
    names = [part.split(":")[0].strip().removeprefix("mut ") for part in parameters(masked(witness.params)) if ":" in part]
    call = f"{'self.' if witness.receiver else ''}witness_{witness.name}({', '.join(names)});"
    pad = witness.indent
    function = [f"{pad}pub fn throwaway_{witness.name}{witness.generics}({witness.params})"]
    if witness.requires:
        function.append(f"{pad}    {witness.requires}")
    function += [f"{pad}    ensures", f"{pad}        false,", f"{pad}{{", f"{pad}    {call}", f"{pad}}}"]
    if witness.impl is not None:
        function = [witness.impl, *function, "}"]
    lines = [
        "// SPDX-License-Identifier: MIT",
        "",
        f"//! The throwaway of `witness_{witness.name}`: its parameters, its requires, one call of it and the",
        "//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would",
        "//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled",
        "//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.",
        "#![allow(unused_imports)]",
        *outside,
        "",
        "verus! {",
        "",
        *inside,
        "",
        *function,
        "",
        "} // verus!",
    ]
    return "\n".join(lines) + "\n"


def mod_text(names):
    lines = [
        "// SPDX-License-Identifier: MIT",
        "",
        "//! The throwaways, one module per root witness beside this directory, each claiming `false` from its",
        "//! witness's requires. tools/check-throwaways.py writes them and expects Verus to refuse each;",
        "//! compiled only under cfg(throwaway). design/witness-per-way-an-operation-succeeds/.",
        *[f"pub mod {name};" for name in sorted(names)],
    ]
    return "\n".join(lines) + "\n"


def sources(directory):
    """The crate's source files outside its throwaway modules, in a fixed order."""
    return sorted(path for path in directory.rglob("*.rs") if THROWAWAY not in path.relative_to(directory).parts)


def plan(crate_root):
    """What the crate whose root file is `crate_root` must hold: (the throwaways, the mod.rs of each
    throwaway directory as {path: text}, each witness with why it is not a root or None)."""
    texts = {path: path.read_text() for path in sources(crate_root.parent)}
    declared = {name for text in texts.values() for name in DECLARED.findall(masked(text))}
    throwaways, listed, by_directory = [], [], {}
    for path, text in texts.items():
        for witness in witnesses(text, path):
            why = not_root(witness, declared)
            listed.append((witness, why))
            if why is not None:
                continue
            directory = path.parent / THROWAWAY
            if witness.name in by_directory.setdefault(directory, set()):
                raise Malformed(f"{path}: witness_{witness.name}: a second root witness of that name under {path.parent}")
            by_directory[directory].add(witness.name)
            file = directory / f"{witness.name}.rs"
            throwaways.append(Throwaway(witness.name, file, throwaway_text(witness, text, module_of(path, crate_root)),
                                        module_of(file, crate_root)))
    mods = {directory / "mod.rs": mod_text(names) for directory, names in by_directory.items()}
    return throwaways, mods, listed


def parent_of(directory):
    """The file that declares the modules of a directory, when the tree has it."""
    for candidate in (directory / "mod.rs", directory / "lib.rs", directory / "main.rs", directory.with_suffix(".rs")):
        if candidate.is_file():
            return candidate
    return None


def tree_findings(crate_root, throwaways, mods, root):
    """What the tree lacks of a crate's plan, one line each."""
    name = lambda path: path.relative_to(root)
    findings = []
    wanted = {throwaway.path: throwaway.text for throwaway in throwaways} | mods
    by_name = {throwaway.path: throwaway.name for throwaway in throwaways}
    for path, text in sorted(wanted.items()):
        what = f"the throwaway of witness_{by_name[path]}" if path in by_name else "the throwaway modules' list"
        if not path.is_file():
            findings.append(f"{name(path)}: missing, {what}; run tools/check-throwaways.py --write")
        elif path.read_text() != text:
            findings.append(f"{name(path)}: not {what} as its witness now reads; run tools/check-throwaways.py --write")
    for directory in sorted({path.parent for path in crate_root.parent.rglob(f"{THROWAWAY}/*") if path.parent.name == THROWAWAY}):
        for path in sorted(directory.iterdir()):
            if path not in wanted:
                findings.append(f"{name(path)}: no root witness asks for it; run tools/check-throwaways.py --write")
    for directory in sorted({path.parent for path in mods}):
        parent = parent_of(directory.parent)
        if parent is None or not DECLARATION.search(parent.read_text()):
            where = name(parent) if parent is not None else name(directory.parent)
            findings.append(f"{where}: does not declare `#[cfg(throwaway)] pub mod throwaway;`, so nothing runs {name(directory)}")
    return findings


def write(crate_root, throwaways, mods):
    """Makes the crate's throwaway directories hold exactly the plan; the paths changed."""
    wanted = {throwaway.path: throwaway.text for throwaway in throwaways} | mods
    changed = []
    for path, text in sorted(wanted.items()):
        if not path.is_file() or path.read_text() != text:
            path.parent.mkdir(exist_ok=True)
            path.write_text(text)
            changed.append(path)
    for path in sorted(crate_root.parent.rglob(f"{THROWAWAY}/*")):
        if path.parent.name == THROWAWAY and path not in wanted:
            path.unlink()
            changed.append(path)
    return changed


def judge(output, throwaways, root):
    """What a crate's run shows against its throwaways: (the findings, how many errors were the
    postcondition's, how many the budget's)."""
    by_file = {throwaway.path: throwaway for throwaway in throwaways}
    seen = {path: 0 for path in by_file}
    findings, postcondition, budget = [], 0, 0
    lines = output.splitlines()
    for index, line in enumerate(lines):
        match = ERROR.match(line)
        if match is None or match.group(1).startswith("aborting due to"):
            continue
        message = match.group(1)
        located = LOCATION.match(lines[index + 1]) if index + 1 < len(lines) else None
        if located is None:
            findings.append(f"an error with no place, so the compiler's: {message}")
            continue
        path = (root / located.group(1)).resolve()
        place = f"{path.relative_to(root) if path.is_relative_to(root) else path}:{located.group(2)}"
        if path not in by_file:
            findings.append(f"{place}: an error outside every throwaway's file: {message}")
            continue
        seen[path] += 1
        if message == POSTCONDITION:
            postcondition += 1
        elif BUDGET in message:
            budget += 1
        else:
            findings.append(f"{place}: throwaway_{by_file[path].name} fails, but not on its postcondition or the budget: {message}")
    results = RESULTS.search(output)
    if results is None:
        findings.append("no verification results line, so the crate did not compile under cfg(throwaway)")
        return findings, postcondition, budget
    if int(results.group(1)) != 0:
        findings.append(f"the run verified {results.group(1)} items; a throwaway's module holds nothing that verifies")
    for path, count in seen.items():
        if count == 0:
            findings.append(f"{path.relative_to(root)}: throwaway_{by_file[path].name} verifies: what witness_{by_file[path].name} requires is contradictory")
        elif count > 1:
            findings.append(f"{path.relative_to(root)}: {count} errors, where a throwaway has one")
    return findings, postcondition, budget


def account(output, throwaways, root, out_of_memory):
    """(findings, postcondition count, budget count) for one capped run. A run the cgroup killed
    for memory is reported as that, and its output is left unjudged."""
    if out_of_memory:
        return [f"ran out of memory: its run is capped at {verify.MEMORY_MAX}"], 0, 0
    return judge(output, throwaways, root)


def command(crate, throwaways, verus_out):
    """rust_verify over a crate's throwaway modules alone. Nothing is exported, so the crate is named
    as no crate depends on it."""
    extra = ["--cfg", THROWAWAY]
    for throwaway in throwaways:
        extra += ["--verify-module", throwaway.module]
    return verify.verify_command(crate, set(), None, verus_out, extra)


def run(crate, throwaways, root):
    """The crate's throwaways, through the cap tools/verify.py puts on rust_verify. The output, and
    whether the cgroup killed the run for memory. The scope is per crate, so the crates still run
    side by side."""
    unit = f"atmo-throwaway-{os.getpid()}-{crate['crate']}"
    with tempfile.TemporaryFile() as captured:
        _, out_of_memory = verify.run_capped(
            command(crate, throwaways, root / "target" / "verus"),
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


def planned(root):
    """Each verified crate with its plan."""
    return [(crate, Path(crate["src"]), *plan(Path(crate["src"]))) for crate in verify.marked_crates(verify.cargo_metadata())]


def main(args):
    if args not in ([], ["--write"], ["--list"]):
        sys.exit(__doc__.split("usage: ")[1].join(("usage: ", "")).rstrip())
    try:
        crates = planned(REPO)
    except Malformed as error:
        print(f"throwaways: {error}", file=sys.stderr)
        return 1
    if args == ["--list"]:
        for _, _, _, _, listed in crates:
            for witness, why in listed:
                print(f"{witness.file.relative_to(REPO)}: witness_{witness.name}: {'root' if why is None else 'not root: ' + why}")
        return 0
    if args == ["--write"]:
        for _, crate_root, throwaways, mods, _ in crates:
            for path in write(crate_root, throwaways, mods):
                print(f"throwaways: wrote {path.relative_to(REPO)}" if path.exists() else f"throwaways: removed {path.relative_to(REPO)}")
    findings = [finding for _, crate_root, throwaways, mods, _ in crates for finding in tree_findings(crate_root, throwaways, mods, REPO)]
    if findings or args == ["--write"]:
        print("\n".join(f"throwaways: {finding}" for finding in findings), end="\n" if findings else "", file=sys.stderr)
        return 1 if findings else 0
    with_some = [(crate, throwaways) for crate, _, throwaways, _, _ in crates if throwaways]
    with ThreadPoolExecutor(max_workers=max(1, len(with_some))) as pool:
        ran = list(pool.map(lambda pair: run(pair[0], pair[1], REPO), with_some))
    postcondition = budget = 0
    for (crate, throwaways), (output, out_of_memory) in zip(with_some, ran):
        crate_findings, on_postcondition, on_budget = account(output, throwaways, REPO, out_of_memory)
        if crate_findings:
            print(output, file=sys.stderr)
        findings += [f"{crate['package']}: {finding}" for finding in crate_findings]
        postcondition += on_postcondition
        budget += on_budget
    if findings:
        print("\n".join(f"throwaways: {finding}" for finding in findings), file=sys.stderr)
        return 1
    total = sum(len(throwaways) for _, throwaways in with_some)
    witnessed = sum(len(listed) for _, _, _, _, listed in crates)
    print(f"throwaways: {total} root witnesses of {witnessed} witnesses in {len(with_some)} crates, each with a throwaway Verus "
          f"refuses in its own file: {postcondition} on the postcondition, {budget} on the solver budget")
    return 0


KERNEL = """// SPDX-License-Identifier: MIT

//! Witnesses. A comment's "quote and its { brace.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::device::{
    a, b,
};

pub open spec fn witness_alive(k: CapKernel) -> bool {
    true
}

impl CapKernel {
    /// The root's use.
    pub fn witness_use(
        &mut self,
        root: Ghost<usize>,
        pairs: Ghost<Map<usize, usize>>,
        big: usize,
    ) -> (ret: (bool, Ghost<CapKernel>))
        requires
            old(self).booted(root@, pairs@),
            // big is a block
            forall|c: int| 0 <= c < 4 ==> {
                &&& big > c
            },
        ensures
            ret.0,
    {
        (self.step(big), Ghost(*self))
    }

    pub fn witness_wf_only(&mut self, i: usize)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
    }

    pub fn witness_named_twice(&mut self, root: Ghost<usize>, k: usize)
        requires
            old(self).booted(root@),
            old(self).spaces.kernel_root@ == k,
        ensures
            final(self).wf(),
    {
    }

    fn witness_helper(&mut self)
        ensures
            true,
    {
    }
}

} // verus!
"""

USER = """// SPDX-License-Identifier: MIT
use vstd::prelude::*;

verus! {

use crate::source::*;

pub struct Buddy {
    pub x: usize,
}

pub fn witness_page<S: SpanSource>(src: &mut S, token: &mut Tracked<S::Token>) -> (r: bool)
    requires
        old(src).serves(old(token)@),
    ensures
        r ==> true,
{
    true
}

pub fn witness_given(b: &mut Buddy) -> (r: bool)
    ensures
        r,
{
    true
}

pub fn witness_made() -> (b: Buddy)
    ensures
        b.x == 0,
{
    Buddy { x: 0 }
}

} // verus!
"""

EXPECTED_USE = """// SPDX-License-Identifier: MIT

//! The throwaway of `witness_use`: its parameters, its requires, one call of it and the
//! claim `false`, which Verus must refuse. Were what the witness requires contradictory, this would
//! verify. tools/check-throwaways.py writes this file from the witness and runs it; it is compiled
//! only under cfg(throwaway), which nothing else sets. design/witness-per-way-an-operation-succeeds/.
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::device::{
    a, b,
};
use crate::capability::witness::*;

impl CapKernel {
    pub fn throwaway_use(
        &mut self,
        root: Ghost<usize>,
        pairs: Ghost<Map<usize, usize>>,
        big: usize,
    )
        requires
            old(self).booted(root@, pairs@),
            // big is a block
            forall|c: int| 0 <= c < 4 ==> {
                &&& big > c
            },
        ensures
            false,
    {
        self.witness_use(root, pairs, big);
    }
}

} // verus!
"""


class Tests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name).resolve()
        self.kernel = self.root / "kernel" / "lib.rs"
        (self.root / "kernel" / "capability").mkdir(parents=True)
        self.kernel.write_text("pub mod capability;\n")
        (self.root / "kernel" / "capability" / "mod.rs").write_text("pub mod witness;\n#[cfg(throwaway)]\npub mod throwaway;\n")
        self.witness = self.root / "kernel" / "capability" / "witness.rs"
        self.witness.write_text(KERNEL)
        self.user = self.root / "aheap" / "src" / "lib.rs"
        self.user.parent.mkdir(parents=True)
        self.user.write_text(USER)

    def written(self, crate_root):
        throwaways, mods, _ = plan(crate_root)
        write(crate_root, throwaways, mods)
        return throwaways, mods

    def findings(self, crate_root):
        throwaways, mods, _ = plan(crate_root)
        return tree_findings(crate_root, throwaways, mods, self.root)

    def test_a_method_is_a_root_when_booted_is_all_its_requires_says_of_self(self):
        _, _, listed = plan(self.kernel)
        self.assertEqual([(witness.name, why) for witness, why in listed], [
            ("use", None),
            ("wf_only", "its requires has no old(self).booted(...)"),
            ("named_twice", "its requires names self outside old(self).booted(...)"),
        ])

    def test_a_method_whose_requires_names_self_nowhere_is_a_root(self):
        self.witness.write_text("""// SPDX-License-Identifier: MIT
use vstd::prelude::*;

verus! {

impl CapKernel {
    pub fn witness_kernel_init(&mut self, root: usize) -> (ret: Option<(usize, usize)>)
        requires
            // no prior self state
            Self::aligned(root),
            root > 0,
        ensures
            ret is Some,
    {
        self.kernel_init(root)
    }

    pub fn witness_bare_init(&mut self) -> (ret: Option<(usize, usize)>)
        ensures
            ret is Some,
    {
        self.kernel_init(0)
    }

    pub fn witness_prior_self(&mut self, root: usize) -> (ret: Option<(usize, usize)>)
        requires
            old(self).cores.wf(),
            root > 0,
        ensures
            ret is Some,
    {
        self.kernel_init(root)
    }
}

} // verus!
""")
        throwaways, _, listed = plan(self.kernel)
        self.assertEqual([(witness.name, why) for witness, why in listed], [
            ("kernel_init", None),
            ("bare_init", None),
            ("prior_self", "its requires has no old(self).booted(...)"),
        ])
        self.assertEqual([t.name for t in throwaways], ["kernel_init", "bare_init"])
        self.assertIn(
            "impl CapKernel {\n"
            "    pub fn throwaway_kernel_init(&mut self, root: usize)\n"
            "        requires\n"
            "            // no prior self state\n"
            "            Self::aligned(root),\n"
            "            root > 0,\n"
            "        ensures\n"
            "            false,\n"
            "    {\n"
            "        self.witness_kernel_init(root);\n"
            "    }\n"
            "}\n",
            throwaways[0].text,
        )
        self.assertIn(
            "impl CapKernel {\n"
            "    pub fn throwaway_bare_init(&mut self)\n"
            "        ensures\n"
            "            false,\n"
            "    {\n"
            "        self.witness_bare_init();\n"
            "    }\n"
            "}\n",
            throwaways[1].text,
        )

    def test_a_function_is_a_root_when_it_takes_nothing_its_crate_declares(self):
        _, _, listed = plan(self.user)
        self.assertEqual([(witness.name, why) for witness, why in listed],
                         [("page", None), ("given", "takes Buddy, which its crate declares"), ("made", None)])

    def test_a_throwaway_is_the_witness_parameters_and_requires_word_for_word(self):
        throwaways, mods, _ = plan(self.kernel)
        self.assertEqual([(t.name, t.path, t.module) for t in throwaways],
                         [("use", self.witness.parent / "throwaway" / "use.rs", "capability::throwaway::use")])
        self.assertEqual(throwaways[0].text, EXPECTED_USE)
        self.assertEqual(list(mods), [self.witness.parent / "throwaway" / "mod.rs"])
        self.assertTrue(mods[self.witness.parent / "throwaway" / "mod.rs"].endswith("pub mod use;\n"))

    def test_a_function_throwaway_keeps_its_generics_and_names_the_crate_root(self):
        throwaways, mods, _ = plan(self.user)
        page = throwaways[0].text
        self.assertEqual(throwaways[0].module, "throwaway::page")
        self.assertIn("use crate::source::*;\nuse crate::*;\n\n"
                      "pub fn throwaway_page<S: SpanSource>(src: &mut S, token: &mut Tracked<S::Token>)\n"
                      "    requires\n        old(src).serves(old(token)@),\n    ensures\n        false,\n{\n"
                      "    witness_page(src, token);\n}\n", page)
        self.assertIn("pub fn throwaway_made()\n    ensures\n        false,\n{\n    witness_made();\n}\n", throwaways[1].text)
        self.assertTrue(mods[self.user.parent / "throwaway" / "mod.rs"].endswith("pub mod made;\npub mod page;\n"))

    def test_a_witness_without_ensures_is_refused(self):
        self.user.write_text("verus! {\npub fn witness_nothing()\n{\n}\npub fn witness_next()\n    ensures true,\n{\n}\n}\n")
        with self.assertRaisesRegex(Malformed, "witness_nothing: no ensures"):
            plan(self.user)

    def test_a_root_witness_with_no_throwaway_is_a_finding(self):
        self.assertEqual(self.findings(self.kernel), [
            "kernel/capability/throwaway/mod.rs: missing, the throwaway modules' list; run tools/check-throwaways.py --write",
            "kernel/capability/throwaway/use.rs: missing, the throwaway of witness_use; run tools/check-throwaways.py --write",
        ])
        self.written(self.kernel)
        self.assertEqual(self.findings(self.kernel), [])

    def test_a_throwaway_whose_requires_differs_from_its_witness_is_a_finding(self):
        throwaways, _ = self.written(self.kernel)
        self.witness.write_text(KERNEL.replace("&&& big > c", "&&& big >= c"))
        self.assertEqual(self.findings(self.kernel), [
            "kernel/capability/throwaway/use.rs: not the throwaway of witness_use as its witness now reads; run tools/check-throwaways.py --write"])
        self.witness.write_text(KERNEL)
        throwaways[0].path.write_text(EXPECTED_USE.replace("            old(self).booted(root@, pairs@),\n", ""))
        self.assertEqual(len(self.findings(self.kernel)), 1)

    def test_a_throwaway_of_no_root_witness_is_a_finding_and_write_removes_it(self):
        self.written(self.kernel)
        stray = self.witness.parent / "throwaway" / "named_twice.rs"
        stray.write_text("")
        self.assertEqual(self.findings(self.kernel), [
            "kernel/capability/throwaway/named_twice.rs: no root witness asks for it; run tools/check-throwaways.py --write"])
        self.written(self.kernel)
        self.assertFalse(stray.exists())

    def test_a_parent_that_does_not_declare_the_module_is_a_finding(self):
        self.written(self.user)
        self.assertEqual(self.findings(self.user), [
            "aheap/src/lib.rs: does not declare `#[cfg(throwaway)] pub mod throwaway;`, so nothing runs aheap/src/throwaway"])
        self.user.write_text(USER + "#[cfg(throwaway)]\nmod throwaway;\n")
        self.written(self.user)
        self.assertEqual(self.findings(self.user), [])

    def output(self, *errors, verified=0):
        text = "".join(f"error: {message}\n  --> {place}\n   |\n" for message, place in errors)
        return text + f"error: aborting due to {len(errors)} previous errors\n\nverification results:: {verified} verified, {len(errors)} errors\n"

    def test_one_error_each_on_the_postcondition_or_the_budget_passes(self):
        throwaways, _ = self.written(self.user)
        made, page = "aheap/src/throwaway/made.rs:20:1", f"{self.user.parent}/throwaway/page.rs:18:8"
        output = self.output((POSTCONDITION, made), ("function body check: resource limit (rlimit) exceeded", page))
        self.assertEqual(judge("warning: unused import\n  --> aheap/src/lib.rs:1:1\n" + output, throwaways, self.root), ([], 1, 1))

    def test_a_throwaway_that_verifies_fails(self):
        throwaways, _ = self.written(self.user)
        findings, _, _ = judge(self.output((POSTCONDITION, "aheap/src/throwaway/made.rs:20:1")), throwaways, self.root)
        self.assertEqual(findings, ["aheap/src/throwaway/page.rs: throwaway_page verifies: what witness_page requires is contradictory"])
        findings, _, _ = judge(self.output((POSTCONDITION, "aheap/src/throwaway/made.rs:20:1"), (POSTCONDITION, "aheap/src/throwaway/page.rs:2:1"),
                                           verified=1), throwaways, self.root)
        self.assertEqual(findings, ["the run verified 1 items; a throwaway's module holds nothing that verifies"])

    def test_an_error_that_is_a_preconditions_fails(self):
        throwaways, _ = self.written(self.user)
        findings, _, _ = judge(self.output((POSTCONDITION, "aheap/src/throwaway/made.rs:20:1"),
                                           ("precondition not satisfied", "aheap/src/throwaway/page.rs:21:5")), throwaways, self.root)
        self.assertEqual(findings, ["aheap/src/throwaway/page.rs:21: throwaway_page fails, but not on its postcondition or the budget: precondition not satisfied"])

    def test_an_error_outside_the_throwaways_file_fails(self):
        throwaways, _ = self.written(self.user)
        findings, _, _ = judge(self.output((POSTCONDITION, "aheap/src/throwaway/made.rs:20:1"), (POSTCONDITION, "aheap/src/lib.rs:14:1")),
                               throwaways, self.root)
        self.assertEqual(findings, [
            "aheap/src/lib.rs:14: an error outside every throwaway's file: postcondition not satisfied",
            "aheap/src/throwaway/page.rs: throwaway_page verifies: what witness_page requires is contradictory"])

    def test_a_crate_that_does_not_compile_fails(self):
        throwaways, _ = self.written(self.user)
        findings, _, _ = judge("error[E0425]: cannot find function `witness_page` in this scope\n  --> aheap/src/throwaway/page.rs:21:5\n"
                               "error: aborting due to 1 previous error\n", throwaways, self.root)
        self.assertEqual(findings, [
            "aheap/src/throwaway/page.rs:21: throwaway_page fails, but not on its postcondition or the budget: cannot find function `witness_page` in this scope",
            "no verification results line, so the crate did not compile under cfg(throwaway)"])
        findings, _, _ = judge("error: could not compile\n", throwaways, self.root)
        self.assertEqual(findings[0], "an error with no place, so the compiler's: could not compile")

    def test_two_errors_in_one_throwaway_fail(self):
        throwaways, _ = self.written(self.user)
        made, page = "aheap/src/throwaway/made.rs:20:1", "aheap/src/throwaway/page.rs:18:8"
        findings, _, _ = judge(self.output((POSTCONDITION, made), (POSTCONDITION, page), (POSTCONDITION, page)), throwaways, self.root)
        self.assertEqual(findings, ["aheap/src/throwaway/page.rs: 2 errors, where a throwaway has one"])

    def test_the_run_names_each_throwaway_module_under_the_cfg_and_exports_nothing(self):
        throwaways, _ = self.written(self.user)
        crate = {"package": "aheap", "crate": "aheap", "src": str(self.user), "deps": [], "plain": []}
        self.assertEqual(command(crate, throwaways, self.root / "target" / "verus"), [
            "rust_verify", "--crate-type", "lib", str(self.user), "--rlimit", "100", "--cfg", "throwaway",
            "--verify-module", "throwaway::page", "--verify-module", "throwaway::made"])

    def crate(self, name):
        return {"package": name, "crate": name, "src": str(self.user), "deps": [], "plain": []}

    def capped_calls(self, fn):
        """Run fn while a bare rust_verify is refused and verify.run_capped is recorded."""
        calls = []

        def fake_capped(command, unit, memory_max, **kwargs):
            calls.append({"command": command, "unit": unit, "memory_max": memory_max, "kwargs": kwargs})
            stdout = kwargs.get("stdout")
            if stdout is not None:
                stdout.write(b"verifier-output\n")
            return 0, False

        def bare(command, **kwargs):
            raise AssertionError(f"rust_verify started without the cap: {command[:1]}")

        original_capped, original_run = verify.run_capped, subprocess.run
        verify.run_capped, subprocess.run = fake_capped, bare
        try:
            fn()
        finally:
            verify.run_capped, subprocess.run = original_capped, original_run
        return calls

    def test_each_rust_verify_runs_through_run_capped_at_the_verify_cap(self):
        throwaways, _ = self.written(self.user)
        seen = {}

        def go():
            for name in ("aheap", "aring"):
                seen[name] = run(self.crate(name), throwaways, self.root)

        calls = self.capped_calls(go)
        self.assertEqual([call["memory_max"] for call in calls], [verify.MEMORY_MAX, verify.MEMORY_MAX])
        self.assertEqual(
            [call["unit"] for call in calls],
            [f"atmo-throwaway-{os.getpid()}-aheap", f"atmo-throwaway-{os.getpid()}-aring"],
        )
        for call, name in zip(calls, ("aheap", "aring")):
            self.assertEqual(call["command"], command(self.crate(name), throwaways, self.root / "target" / "verus"))
            self.assertEqual(call["kwargs"]["cwd"], self.root)
            self.assertIs(call["kwargs"]["stdin"], subprocess.DEVNULL)
        self.assertEqual(seen["aheap"], ("verifier-output\n", False))

    def test_a_run_killed_for_memory_is_reported_as_such_and_not_as_a_compile_failure(self):
        throwaways, _ = self.written(self.user)
        findings, postcondition, budget = account("", throwaways, self.root, True)
        self.assertEqual(findings, [f"ran out of memory: its run is capped at {verify.MEMORY_MAX}"])
        self.assertEqual((postcondition, budget), (0, 0))
        judged, _, _ = account("", throwaways, self.root, False)
        self.assertIn("no verification results line, so the crate did not compile under cfg(throwaway)", judged)

if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
