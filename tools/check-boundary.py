#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Hold every site where an unverified crate hands verified code a value the proof cannot check to
tools/boundary-list, each with who vouches for it. design/boundary-into-verified-code-counted/.

A boundary crate is a workspace member not marked '[package.metadata.atmosphere] verified = true'
that depends on one that is: today kernel, dom0 and astd (under its heap feature). CRATES says how
each is compiled; a boundary crate missing from it is a finding. For each, and for each target,
x86_64 by the crate's own .cargo config and aarch64 by its JSON spec, the check runs
`cargo rustc ... -- -Zunpretty=thir-flat` from the crate's directory, into target/boundary of the
tree so its flags never touch the gate's build, and reads rustc's typed intermediate form, in which
every call names its callee's definition. Default features, plus astd's heap. The sites of the two
targets are held as one set.

A site is one of:

- conjure: a call of a function named assume_new (Tracked::assume_new, Ghost::assume_new). Its callee
  field is the call its value is passed to, as '<crate>::<module path>::<name> argument <n>: <type>'
  with the impl index dropped, the receiver counted as argument 0 and the conjured type with
  vstd::prelude:: and erased lifetimes dropped; the value is followed through blocks, struct fields
  and a let binding to the first call that takes it, and 'none' stands for the call when nothing does.
- raw: a raw pointer to a type a marked crate defines, made by an `as` cast or by core's cast,
  transmute or provenance functions. Its callee field is the pointee type.
- call: a call into a marked crate whose specification has a requires. Not counted yet.

tools/boundary-list holds one line per site, fields separated by tabs: the path, the enclosing
function as rustc names it without the crate hash, the kind, the callee, the occurrence among sites
alike in those four fields from 1 in source order, the guarantor's class and its text. '#' starts a
comment line. The classes and what their text must be:

- hardware '<key> <section>', machine '<key> <section>': the key one tools/hardware-documents lists.
- kernel '<path> <item>': the file at path declares the function the item ends in.
- language '<path under rust-src> "<passage>"': the passage word for word in that file of the pinned
  toolchain's rust-src, as tools/check-external-body.py matches a '// rust:' line.
- boot '<witness>': a function of that name, starting witness_, in a marked crate.
- check '"<condition>"': the condition's text in the enclosing function before the site, in a
  statement that holds assert or if.
- nothing '"<what it rests on>"': debt, said in words.

It prints one line per finding to stderr and exits 1: a site the source holds and the list does not,
a line the source has no site for, a line that is not seven fields, a repeated line, a class not
named above, or a text that fails its class's rule. Otherwise it prints one line counting the sites
by kind and by class and exits 0.

usage: tools/check-boundary.py           the check
       tools/check-boundary.py --sites   print the source's sites as list lines, with the guarantor
                                         the list gives each or '?', and exit 0
       tools/check-boundary.py --test    this script's own tests
"""
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from collections import namedtuple
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
LIST = "tools/boundary-list"
TARGET_DIR = "target/boundary"
TARGETS = ("x86_64", "aarch64")
# Each boundary crate: the directory cargo runs from, so its .cargo config applies, cargo rustc's
# arguments, and the aarch64 JSON spec relative to that directory. astd is a library with no config
# of its own, so it is compiled from dom0's, as dom0 builds it.
CRATES = {
    "kernel": ("kernel", ["--bin", "kernel"], "src/aarch64-unknown-aloader.json"),
    "dom0": ("dom0", ["--bin", "dom0"], "src/aarch64-unknown-aloader.json"),
    "astd": ("dom0", ["-p", "astd", "--features", "heap"], "src/aarch64-unknown-aloader.json"),
}
KINDS = ("conjure", "raw", "call")
CLASSES = ("hardware", "machine", "kernel", "language", "boot", "check", "nothing")
FIELDS = 7
# core's functions that make a raw pointer to a type from an address or another pointer's type.
RAW_MAKERS = {"cast", "transmute", "transmute_copy", "with_addr", "map_addr", "with_exposed_provenance",
              "with_exposed_provenance_mut", "without_provenance", "without_provenance_mut"}

HEADER = re.compile(r"^DefId\(\d+:\d+ ~ (\w+)\[[0-9a-f]+\]::(.*)\):$")
DEF = re.compile(r"DefId\(\d+:\d+ ~ (\w+)\[[0-9a-f]+\]::([^)]*)\)")
SPAN = re.compile(r"^(\S+?):(\d+):(\d+): ")
EXPR_REF = re.compile(r"(?<![\w.])e(\d+)\b")
STMT_REF = re.compile(r"(?<![\w.])s(\d+)\b")
BLOCK_REF = re.compile(r"\bblock: b(\d+)\b")
HIR = re.compile(r"HirId\(.*\)")
RAW = re.compile(r"^\*(?:mut|const) \[?(\w+)::")
ARCH = re.compile(r"::arch::(?:x86_64|aarch64)\b")
QUOTED = re.compile(r'^"(.+)"$')

Site = namedtuple("Site", "path function kind callee line column")
Entry = namedtuple("Entry", "path function kind callee occurrence guarantor text")


class Unreadable(Exception):
    pass


def external_body():
    """tools/check-external-body.py as a module, for the rules a language and a kernel voucher share."""
    spec = importlib.util.spec_from_file_location("check_external_body", REPO / "tools/check-external-body.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# --- rustc's THIR, as -Zunpretty=thir-flat prints it ---

def bodies(text):
    """Each body of the dump: (crate, path, lines), the path as rustc names the body's owner."""
    found, current = [], None
    for line in text.splitlines():
        header = HEADER.match(line)
        if header:
            current = (header.group(1), header.group(2), [])
            found.append(current)
        elif current is not None:
            current[2].append(line)
    return found


def sections(lines):
    """A body's arms, blocks, exprs and stmts, each a list of items, each item its lines."""
    found, name, item = {}, None, None
    for line in lines:
        if line.startswith("    ") and not line.startswith("     "):
            field = line.strip()
            name = field.split(":")[0] if field.endswith("[") else None
            if name:
                found[name] = []
            continue
        if name is None:
            continue
        if line.startswith("        ") and not line.startswith("         "):
            if line.strip() in ("},", "}"):
                found[name].append(item)
                item = None
            else:
                item = [line]
        elif item is not None:
            item.append(line)
    return found


def field(lines, indent, name):
    """The rest of the first line of lines at that indent that starts with 'name: '."""
    prefix = " " * indent + name + ": "
    for line in lines:
        if line.startswith(prefix):
            return line[len(prefix):]
    return None


def block_of(lines, indent, name):
    """The lines inside the field 'name' opened at that indent, up to its close."""
    prefix = " " * indent + name + ": "
    for start, line in enumerate(lines):
        if line.startswith(prefix):
            inner = []
            for following in lines[start + 1:]:
                if following.startswith(" " * indent) and not following.startswith(" " * (indent + 1)):
                    break
                inner.append(following)
            return [line] + inner
    return []


def span(text):
    match = SPAN.match(text or "")
    return (match.group(1), int(match.group(2)), int(match.group(3))) if match else None


def one_arch(text):
    """A path with the arch module's per-ISA module dropped, since each ISA's has the same item names
    (design/arch-module/): a site whose callee is in it is one site on both targets."""
    return ARCH.sub("::arch", text)


def plain_path(crate, path):
    """A definition's path with its crate, without impl indices and with one arch module."""
    return one_arch("::".join([crate] + [part for part in path.split("::") if not part.startswith("{impl#")]))


def plain_type(text):
    """A type as the list writes it: no erased lifetimes, no vstd::prelude:: path and one arch module."""
    return one_arch(text.rstrip(",").replace("'{erased} ", "").replace("vstd::prelude::", ""))


class Body:
    """One body's expressions, with what each refers to, and its let bindings."""

    def __init__(self, crate, path, lines):
        self.function = f"{crate}::{path}"
        parts = sections(lines)
        self.exprs = parts.get("exprs", [])
        self.parent = {}
        self.kinds = []
        for index, item in enumerate(self.exprs):
            kind = (field(item, 12, "kind") or "").split(" ")[0].rstrip("{,(")
            self.kinds.append(kind)
            if kind == "Call":
                fun = field(item, 16, "fun")
                for ref in EXPR_REF.findall(fun or ""):
                    self.parent[int(ref)] = (index, None)
                for position, ref in enumerate(EXPR_REF.findall("\n".join(block_of(item, 16, "args")[1:]))):
                    self.parent[int(ref)] = (index, position)
            elif kind == "Block":
                pass
            else:
                for ref in EXPR_REF.findall("\n".join(item[1:])):
                    self.parent.setdefault(int(ref), (index, None))
        blocks = parts.get("blocks", [])
        for index, kind in enumerate(self.kinds):
            if kind == "Block":
                number = BLOCK_REF.search("\n".join(self.exprs[index]))
                if number and int(number.group(1)) < len(blocks):
                    for ref in EXPR_REF.findall("\n".join(block_of(blocks[int(number.group(1))], 12, "expr"))):
                        self.parent.setdefault(int(ref), (index, None))
        self.bound = {}
        for item in parts.get("stmts", []):
            text = "\n".join(item)
            initializer = "\n".join(block_of(item, 16, "initializer"))
            var = HIR.search("\n".join(block_of(item, 24, "var")))
            refs = EXPR_REF.findall(initializer)
            if "kind: Let" in text and var and refs:
                self.bound[int(refs[0])] = var.group(0)
        self.uses = {}
        for index, kind in enumerate(self.kinds):
            if kind == "VarRef":
                var = HIR.search("\n".join(self.exprs[index]))
                if var:
                    self.uses.setdefault(var.group(0), []).append(index)

    def callee(self, index):
        """The crate and path of the function a Call expression calls, or None."""
        match = DEF.search("\n".join(block_of(self.exprs[index], 16, "ty")))
        return (match.group(1), match.group(2)) if match else None

    def taker(self, index, seen=None):
        """The call that takes the value of expression index, and the argument it fills, or None."""
        seen = set() if seen is None else seen
        while index not in seen:
            seen.add(index)
            if index in self.parent:
                parent, position = self.parent[index]
                if self.kinds[parent] == "Call" and position is not None:
                    return parent, position
                index = parent
                continue
            for use in self.uses.get(self.bound.get(index), []):
                found = self.taker(use, seen)
                if found:
                    return found
            return None
        return None

    def sites(self, marked):
        """The conjure and raw sites of this body."""
        found = []
        for index, kind in enumerate(self.kinds):
            item = self.exprs[index]
            ty = plain_type(field(item, 12, "ty") or "")
            where = span(field(item, 12, "span"))
            if kind == "Call":
                callee = self.callee(index)
                if callee and callee[1].split("::")[-1] == "assume_new":
                    where = span(field(item, 16, "fn_span")) or where
                    taker = self.taker(index)
                    if taker:
                        crate, path = self.callee(taker[0]) or ("?", "?")
                        name = f"{plain_path(crate, path)} argument {taker[1]}"
                    else:
                        name = "none"
                    found.append(Site(where[0], self.function, "conjure", f"{name}: {ty}", where[1], where[2]))
                    continue
                if not (callee and callee[0] == "core" and callee[1].split("::")[-1] in RAW_MAKERS):
                    continue
            elif kind != "Cast":
                continue
            raw = RAW.match(ty)
            if raw and raw.group(1) in marked:
                found.append(Site(where[0], self.function, "raw", ty.split(" ", 1)[1], where[1], where[2]))
        return found


def thir_sites(text, marked):
    """Every conjure and raw site of a dump."""
    found = []
    for crate, path, lines in bodies(text):
        found += Body(crate, path, lines).sites(marked)
    return found


def numbered(sites):
    """Each site's key, its path, function, kind, callee and occurrence among sites alike, with the
    site."""
    groups = {}
    for site in sites:
        groups.setdefault(site[:4], []).append(site)
    keyed = {}
    for alike, members in groups.items():
        for occurrence, site in enumerate(sorted(set(members), key=lambda s: (s.line, s.column)), 1):
            keyed[(*alike, occurrence)] = site
    return keyed


# --- the workspace ---

def metadata(repo):
    ran = subprocess.run(["cargo", "metadata", "--no-deps", "--format-version", "1"], cwd=repo,
                         capture_output=True, text=True)
    if ran.returncode != 0:
        raise Unreadable(f"cargo metadata: {ran.stderr.strip()}")
    return json.loads(ran.stdout)


def crates(meta):
    """The marked crates, by the name rustc gives them, and the boundary crates."""
    packages = meta["packages"]
    marked = {package["name"] for package in packages
              if ((package.get("metadata") or {}).get("atmosphere") or {}).get("verified")}
    boundary = {package["name"] for package in packages if package["name"] not in marked
                and any(dependency["name"] in marked for dependency in package["dependencies"])}
    return {name.replace("-", "_") for name in marked}, boundary


def marked_directories(meta):
    return [Path(package["manifest_path"]).parent for package in meta["packages"]
            if ((package.get("metadata") or {}).get("atmosphere") or {}).get("verified")]


def dump(repo, name, target):
    directory, arguments, spec = CRATES[name]
    command = ["cargo", "rustc", "--target-dir", str(repo / TARGET_DIR), *arguments]
    if target == "aarch64":
        command += ["-Zjson-target-spec", "--target", spec]
    command += ["--", "-Zunpretty=thir-flat"]
    ran = subprocess.run(command, cwd=repo / directory, capture_output=True, text=True,
                         env={**os.environ, "RUSTC_BOOTSTRAP": "1"})
    if ran.returncode != 0:
        raise Unreadable(f"{name} on {target}: cargo rustc exited {ran.returncode}:\n{ran.stderr[-4000:]}")
    return ran.stdout


# --- the list ---

def parse_list(text):
    """The list's entries, and a finding for each line that cannot be read."""
    entries, findings = [], []
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        at = f"{LIST}:{number}"
        if len(fields) != FIELDS or not all(part.strip() for part in fields):
            findings.append(f"{at}: not {FIELDS} fields separated by tabs, none empty")
            continue
        if fields[2] not in KINDS:
            findings.append(f"{at}: the kind {fields[2]} is none of {', '.join(KINDS)}")
            continue
        if not fields[4].isdigit() or int(fields[4]) < 1:
            findings.append(f"{at}: the occurrence {fields[4]} is not a number from 1")
            continue
        entries.append((at, Entry(fields[0], fields[1], fields[2], fields[3], int(fields[4]), fields[5],
                                  fields[6])))
    return entries, findings


class Rules:
    """What a guarantor's text must be, by class, against the tree."""

    def __init__(self, repo, documents, rust_src, witnesses, module):
        self.repo, self.documents, self.rust_src = repo, documents, rust_src
        self.witnesses, self.module = witnesses, module

    def judge(self, entry, site):
        """None when the entry's guarantor holds for the site, or what is wrong."""
        guarantor, text = entry.guarantor, entry.text
        if guarantor in ("hardware", "machine"):
            key, _, section = text.partition(" ")
            if key not in self.documents:
                return f"the document {key} is not listed in tools/hardware-documents"
            return None if section.strip() else f"the {guarantor} guarantor names no section of {key}"
        if guarantor == "kernel":
            path, _, item = text.partition(" ")
            if item.strip() and self.module.kernel_item_exists(self.repo, path, item.strip()):
                return None
            return f"the kernel item {json.dumps(text)} does not exist"
        if guarantor == "language":
            try:
                self.module.language_claim("", text, self.rust_src)
            except self.module.Unreadable as error:
                return str(error).lstrip(": ")
            return None
        if guarantor == "boot":
            if text.startswith("witness_") and text in self.witnesses:
                return None
            return f"no witness {text} in a marked crate"
        if guarantor == "check":
            quoted = QUOTED.match(text)
            if not quoted:
                return 'a check names its condition in double quotes: "<condition>"'
            return None if checked(self.repo, site, quoted.group(1)) else (
                f"no assert or if holding {text} in {site.function} before the site")
        if guarantor == "nothing":
            return None if QUOTED.match(text) else 'nothing says what the site rests on in double quotes'
        return f"the class {guarantor} is none of {', '.join(CLASSES)}"


def checked(repo, site, condition, start=None):
    """Whether the condition's text is in an assert or an if of the enclosing function before the site:
    from the first line of the function's body that rustc reports, which start gives, to the site."""
    try:
        lines = (repo / site.path).read_text(encoding="utf-8").splitlines()
    except OSError:
        return False
    first = start if start is not None else site.start
    before = " ".join(" ".join(lines[first - 1:site.line - 1] + [lines[site.line - 1][:site.column - 1]]).split())
    wanted = " ".join(condition.split())
    at = before.find(wanted)
    while at >= 0:
        statement = re.split(r"[;{}]", before[:at])[-1]
        if re.search(r"\bassert\w*!|\bif\b", statement):
            return True
        at = before.find(wanted, at + 1)
    return False


def witnesses(directories):
    names = set()
    for directory in directories:
        for file in directory.rglob("*.rs"):
            if "target" in file.relative_to(directory).parts:
                continue
            names.update(re.findall(r"\bfn (witness_\w+)", file.read_text(encoding="utf-8")))
    return names


StartedSite = namedtuple("StartedSite", Site._fields + ("start",))


def compare(found, entries, rules):
    """The findings of holding the sites found, keyed, to the list's entries."""
    findings, listed = [], {}
    for at, entry in entries:
        key = entry[:5]
        if key in listed:
            findings.append(f"{at}: repeats {listed[key][0]}")
            continue
        listed[key] = (at, entry)
    for key, site in sorted(found.items(), key=lambda item: (item[1].path, item[1].line, item[1].column)):
        if key not in listed:
            findings.append(f"{site.path}:{site.line}: a {site.kind} site the list does not hold: "
                            + "\t".join(map(str, key)))
            continue
        at, entry = listed[key]
        wrong = rules.judge(entry, site)
        if wrong:
            findings.append(f"{at}: {wrong}")
    for key, (at, entry) in listed.items():
        if key not in found:
            findings.append(f"{at}: the source holds no such site: " + "\t".join(map(str, key)))
    return findings


def with_starts(text, marked):
    """Every site of a dump, with the first line of its body in the site's file."""
    found = []
    for crate, path, lines in bodies(text):
        body_sites = Body(crate, path, lines).sites(marked)
        if not body_sites:
            continue
        for site in body_sites:
            starts = [where[1] for line in lines if "span: " in line
                      for where in [span(line.split("span: ", 1)[1])] if where and where[0] == site.path]
            found.append(StartedSite(*site, min(starts + [site.line])))
    return found


def summary(found, entries):
    kinds, classes = {}, {}
    listed = {entry[:5]: entry for _, entry in entries}
    for key, site in found.items():
        kinds[site.kind] = kinds.get(site.kind, 0) + 1
        guarantor = listed[key].guarantor
        classes[guarantor] = classes.get(guarantor, 0) + 1
    count = lambda table: ", ".join(f"{name} {table[name]}" for name in sorted(table))
    return f"boundary: {len(found)} sites ({count(kinds)}); guarantors: {count(classes)}"


def main(argv):
    if argv == ["--test"]:
        runner = unittest.TextTestRunner(stream=sys.stderr, verbosity=1)
        return 0 if runner.run(unittest.defaultTestLoader.loadTestsFromTestCase(Tests)).wasSuccessful() else 1
    if argv not in ([], ["--sites"]):
        print(__doc__.split("usage:")[1], file=sys.stderr)
        return 2
    try:
        meta = metadata(REPO)
        marked, boundary = crates(meta)
        missing = sorted(boundary - set(CRATES))
        if missing:
            raise Unreadable("a boundary crate CRATES does not say how to compile: " + ", ".join(missing))
        sites = []
        for name in CRATES:
            for target in TARGETS:
                sites += with_starts(dump(REPO, name, target), marked)
        found = numbered(sites)
        entries, findings = parse_list((REPO / LIST).read_text(encoding="utf-8"))
    except (Unreadable, OSError) as error:
        print(f"tools/check-boundary.py: {error}", file=sys.stderr)
        return 1
    if argv == ["--sites"]:
        listed = {entry[:5]: entry for _, entry in entries}
        for key, site in sorted(found.items(), key=lambda item: (item[1].path, item[1].line, item[1].column)):
            entry = listed.get(key)
            print("\t".join(map(str, key)) + "\t" + ("\t".join(entry[5:]) if entry else "?\t?"))
        return 0
    module = external_body()
    try:
        documents = module.parse_documents((REPO / module.DOCUMENTS_PATH).read_text(encoding="utf-8"))
    except module.Unreadable as error:
        print(f"tools/check-boundary.py: {error}", file=sys.stderr)
        return 1
    rules = Rules(REPO, documents, module.rust_source_root, witnesses(marked_directories(meta)), module)
    findings += compare(found, entries, rules)
    if findings:
        for finding in findings:
            print(finding, file=sys.stderr)
        return 1
    print(summary(found, entries))
    return 0


# --- tests ---

def call(callee, fun, args, fn_span, ty):
    """A Call expression of a dump, as rustc prints it."""
    lines = ["        Expr {", "            kind: Call {", "                ty: FnDef(",
             f"                    DefId(8:21 ~ {callee}),", "                ),",
             f"                fun: e{fun},"]
    if args:
        lines += ["                args: ["] + [f"                    e{arg}," for arg in args] + ["                ],"]
    else:
        lines += ["                args: [],"]
    lines += [f"                fn_span: {fn_span} (#0),", "            },", f"            ty: {ty},",
              f"            span: {fn_span} (#0),", "        },"]
    return lines


def simple(kind, ty, at, body=()):
    return (["        Expr {", f"            kind: {kind} {{"] + [f"                {line}" for line in body]
            + ["            },", f"            ty: {ty},", f"            span: {at} (#0),", "        },"])


def dump_text(owner, exprs, stmts=(), blocks=()):
    lines = [f"DefId(0:1 ~ {owner}):", "Thir {"]
    for name, items in (("blocks", blocks), ("exprs", exprs), ("stmts", stmts)):
        lines.append(f"    {name}: [")
        for item in items:
            lines += item
        lines.append("    ],")
    lines.append("}")
    return "\n".join(lines) + "\n"


ASSUME = "verus_builtin[5623]::{impl#2}::assume_new"
ENTER = "verified[0d46]::capability::operation::{impl#1}::enter"
STEPS = "vstd::prelude::Tracked<&'{erased} mut verified::capability::steps::Steps>"


def conjure_dump():
    """capability::dispatch passing a conjured Steps to enter, through a scope, as argument 3."""
    exprs = [
        simple("ZstLiteral", "FnDef(", "kernel/src/capability.rs:53:50: 53:69"),
        call(ASSUME, 0, [], "kernel/src/capability.rs:53:50: 53:71", STEPS),
        simple("Scope", STEPS, "kernel/src/capability.rs:53:50: 53:71", ["value: e1,"]),
        simple("ZstLiteral", "FnDef(", "kernel/src/capability.rs:53:31: 53:36"),
        simple("VarRef", "usize", "kernel/src/capability.rs:50:17: 50:22", ["id: LocalVarId(", "    HirId(x.2),", "),"]),
        call(ENTER, 3, [4, 4, 4, 2], "kernel/src/capability.rs:53:24: 53:72", "Option<Outcome>"),
    ]
    return dump_text("kernel[ff92]::capability::dispatch", exprs)


def let_dump():
    """lock::{impl#1}::lock binding a conjured Core and passing the binding to acquire."""
    core = "vstd::prelude::Tracked<&'{erased} mut verified::queue_lock::Core>"
    exprs = [
        simple("ZstLiteral", "FnDef(", "kernel/src/lock.rs:45:40: 45:58"),
        call(ASSUME, 0, [], "kernel/src/lock.rs:45:40: 45:60", core),
        simple("ZstLiteral", "FnDef(", "kernel/src/lock.rs:46:19: 46:26"),
        simple("VarRef", core, "kernel/src/lock.rs:46:32: 46:36",
               ["id: LocalVarId(", "    HirId(DefId(0:619 ~ kernel[ff92]::lock::{impl#1}::lock).24),", "),"]),
        call("verified[0d46]::queue_lock::{impl#0}::acquire", 2, [3, 3, 3], "kernel/src/lock.rs:46:9: 46:37", "()"),
    ]
    stmts = [["        Stmt {", "            kind: Let {", "                pattern: Pat {",
              "                    kind: Binding {", "                        var: LocalVarId(",
              "                            HirId(DefId(0:619 ~ kernel[ff92]::lock::{impl#1}::lock).24),",
              "                        ),", "                    },", "                },",
              "                initializer: Some(", "                    e1,", "                ),",
              "            },", "        },"]]
    return dump_text("kernel[ff92]::lock::{impl#1}::lock", exprs, stmts)


def raw_dump():
    """capability::boot casting an address to a *mut CapKernel, and to a *mut u8, which is no site."""
    exprs = [
        simple("Literal", "usize", "kernel/src/capability.rs:190:35: 190:40"),
        simple("Cast", "*mut verified::capability::kernel::CapKernel", "kernel/src/capability.rs:190:33: 190:76",
               ["source: e0,"]),
        simple("Cast", "*mut u8", "kernel/src/capability.rs:187:33: 187:50", ["source: e0,"]),
    ]
    return dump_text("kernel[ff92]::capability::boot", exprs)


MARKED = {"verified", "acall", "aeager", "aheap"}
DISPATCH = ("kernel/src/capability.rs", "kernel::capability::dispatch", "conjure",
            "verified::capability::operation::enter argument 3: Tracked<&mut verified::capability::steps::Steps>", 1)


class FakeModule:
    """check-external-body's voucher rules, standing in for the real ones."""

    class Unreadable(Exception):
        pass

    @staticmethod
    def kernel_item_exists(repo, path, item):
        return path == "kernel/verified/capability/operation.rs" and item == "CapKernel::enter"

    @staticmethod
    def language_claim(at, claim, rust_src):
        if claim != 'library/core/src/alloc/global.rs "currently allocated via this allocator"':
            raise FakeModule.Unreadable(f"{at}: the passage is not found word for word")
        return claim


class Tests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Path(directory.name)
        source = self.repo / "kernel/src/capability.rs"
        source.parent.mkdir(parents=True)
        lines = [""] * 60
        lines[49] = "pub fn dispatch(frame: Registers) -> Option<Outcome> {"
        lines[50] = "    assert!(core < NUM_CPUS, \"no such core\");"
        lines[51] = "    let core = 0;"
        lines[52] = "    let returned = kernel.enter(core, frame, Tracked::assume_new());"
        source.write_text("\n".join(lines) + "\n")
        self.rules = Rules(self.repo, {"amd-apm2": ("t", "p", "n", "r")}, None, {"witness_boot_state"}, FakeModule)

    def found(self):
        return numbered(with_starts(conjure_dump(), MARKED))

    def entries(self, guarantor, text, key=DISPATCH):
        return parse_list("\t".join(map(str, key)) + f"\t{guarantor}\t{text}\n")[0]

    def test_a_conjured_value_is_named_by_the_call_and_argument_it_fills(self):
        self.assertEqual(list(self.found()), [DISPATCH])
        self.assertEqual(self.found()[DISPATCH].line, 53)

    def test_a_conjured_value_is_followed_through_a_let_binding(self):
        (key,) = numbered(thir_sites(let_dump(), MARKED))
        self.assertEqual(key[3], "verified::queue_lock::acquire argument 2: Tracked<&mut verified::queue_lock::Core>")

    def test_a_conjured_value_no_call_takes_is_still_a_site(self):
        text = dump_text("kernel[ff92]::f", [simple("ZstLiteral", "FnDef(", "kernel/src/a.rs:1:1: 1:2"),
                                             call(ASSUME, 0, [], "kernel/src/a.rs:1:1: 1:5", STEPS)])
        (site,) = thir_sites(text, MARKED)
        self.assertTrue(site.callee.startswith("none: "))

    def test_a_raw_pointer_to_a_marked_type_is_a_site_and_one_to_another_type_is_not(self):
        (site,) = thir_sites(raw_dump(), MARKED)
        self.assertEqual((site.kind, site.callee, site.line), ("raw", "verified::capability::kernel::CapKernel", 190))

    def test_a_callee_in_the_arch_module_is_named_the_same_on_both_targets(self):
        self.assertEqual(plain_path("verified", "arch::x86_64::flush_every_context"), "verified::arch::flush_every_context")
        self.assertEqual(plain_path("verified", "arch::aarch64::flush_every_context"), "verified::arch::flush_every_context")
        self.assertEqual(plain_type("&'{erased} mut verified::arch::aarch64::TlbModel,"), "&mut verified::arch::TlbModel")

    def test_sites_alike_in_one_function_are_counted_in_source_order(self):
        first = Site("a.rs", "k::f", "conjure", "c", 9, 1)
        second = Site("a.rs", "k::f", "conjure", "c", 3, 1)
        keyed = numbered([first, second, first])
        self.assertEqual(keyed[("a.rs", "k::f", "conjure", "c", 1)], second)
        self.assertEqual(keyed[("a.rs", "k::f", "conjure", "c", 2)], first)

    def test_an_unlisted_site_fails(self):
        (finding,) = compare(self.found(), [], self.rules)
        self.assertIn("kernel/src/capability.rs:53: a conjure site the list does not hold", finding)

    def test_a_listed_site_the_source_lacks_fails(self):
        gone = DISPATCH[:4] + (2,)
        entries = self.entries("nothing", '"x"') + self.entries("nothing", '"x"', gone)
        (finding,) = compare(self.found(), entries, self.rules)
        self.assertIn("the source holds no such site", finding)

    def test_a_site_with_no_guarantor_fails(self):
        entries, findings = parse_list("\t".join(map(str, DISPATCH)) + "\n")
        self.assertEqual(entries, [])
        self.assertIn("not 7 fields", findings[0])
        self.assertEqual(len(compare(self.found(), entries, self.rules)), 1)

    def test_a_repeated_line_fails(self):
        entries = self.entries("nothing", '"x"') * 2
        (finding,) = compare(self.found(), entries, self.rules)
        self.assertIn("repeats", finding)

    def test_each_class_accepts_its_rule_and_refuses_text_that_fails_it(self):
        cases = {
            "hardware": ("amd-apm2 5.5.3", "intel-sdm 4.10"),
            "machine": ("amd-apm2 5.5.3", "amd-apm2"),
            "kernel": ("kernel/verified/capability/operation.rs CapKernel::enter", "kernel/src/x.rs enter"),
            "language": ('library/core/src/alloc/global.rs "currently allocated via this allocator"',
                         'library/core/src/alloc/global.rs "made up"'),
            "boot": ("witness_boot_state", "witness_nothing_here"),
            "check": ('"core < NUM_CPUS"', '"core > NUM_CPUS"'),
            "nothing": ('"the glue\'s word"', "unquoted"),
        }
        self.assertEqual(set(cases), set(CLASSES))
        for guarantor, (good, bad) in cases.items():
            with self.subTest(guarantor):
                self.assertEqual(compare(self.found(), self.entries(guarantor, good), self.rules), [])
                (finding,) = compare(self.found(), self.entries(guarantor, bad), self.rules)
                self.assertTrue(finding.startswith(f"{LIST}:1: "), finding)

    def test_a_check_after_the_site_or_outside_an_assert_or_if_does_not_count(self):
        site = self.found()[DISPATCH]
        self.assertTrue(checked(self.repo, site, "core < NUM_CPUS"))
        self.assertFalse(checked(self.repo, site, "let core = 0"))
        self.assertFalse(checked(self.repo, site, "Tracked::assume_new()"))
        self.assertFalse(checked(self.repo, site, "core < NUM_CPUS", start=52))

    def test_an_unknown_class_or_kind_fails(self):
        self.assertIn("none of", compare(self.found(), self.entries("someone", '"x"'), self.rules)[0])
        _, findings = parse_list("a\tb\tghost\tc\t1\tnothing\t\"x\"\n")
        self.assertIn("kind ghost", findings[0])

    def test_the_boundary_crates_are_the_unmarked_members_that_depend_on_a_marked_one(self):
        package = lambda name, verified=False, dependencies=(): {
            "name": name, "metadata": {"atmosphere": {"verified": True}} if verified else None,
            "dependencies": [{"name": dependency} for dependency in dependencies]}
        meta = {"packages": [package("verified", True), package("pager-policy", True),
                             package("kernel", dependencies=["verified"]), package("aloader")]}
        self.assertEqual(crates(meta), ({"verified", "pager_policy"}, {"kernel"}))

    def test_every_boundary_crate_of_the_tree_is_compiled(self):
        _, boundary = crates(metadata(REPO))
        self.assertEqual(boundary - set(CRATES), set())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
