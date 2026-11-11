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
appears twice in one file twice. The word assume, admit or assume_ in code fails the check, as a call, a path or a use that imports it
under another name: the marked crates hold none, and a new one would be an axiom the proof rests on. So does any other way to exempt code: an axiom fn or a broadcast axiom fn, a
verifier::external fn, an external function, trait or type specification, any other verifier
attribute whose name starts with external, any attribute under verus::internal, assume_termination,
assume_unsupported_attributes, an attribute above that does not open its line (after another
attribute, inside cfg_attr, or an inner #![...]), and an assume_specification its line does not open;
each word of these in code counts, whatever attribute or macro spells it. An unstable feature is
refused, since one builds an identifier from pieces and a word above need not appear. vstd's
assume_new constructors, which make a ghost or tracked value from nothing, are refused outside the
body of a counted external_body function, the glue whose claim the list holds; an impl outside
verus! that Verus does not read is no such body. So is the word unsafe, outside that body and the
body of a function an assumed specification in the same file names: safe Rust cannot make a value of
a type whose fields are private to another module or copy one that is neither Copy nor Clone, and
unsafe code can (core::mem::zeroed, core::ptr::read, MaybeUninit::assume_init, transmute), in an impl
outside verus! that verified code reaches through a trait vstd specifies, such as Default or From.
So is any way to state the spec of exec code Verus does not read, which the proof takes on trust: an
impl of one of vstd's trait extensions, any name ending in SpecImpl (FromSpecImpl, PartialEqSpecImpl,
IteratorSpecImpl and the rest), the StructuralEq derive and the exec_spec macros. vstd's From::from
ensures from_spec for any impl with a FromSpecImpl, and nothing holds an impl outside verus! to it, so
safe code there could return no token, or one it was given, while the spec says it returns another.
vstd's proof_from_false is not refused: it requires false, which only an assumption or an exemption
refused here can supply.

A line's code is what rustc reads as code: comments, line or block, and the inside of string and
character literals are left out, so a '//' inside a block comment or a string hides nothing after it.
A first line opening #! is dropped as rustc drops it, unless the next token past whitespace and plain
comments is [, an inner attribute; so a '#!/*' line opens no comment.
Every .rs file under a marked crate is scanned except build output under 'target', and the check
refuses what makes rustc compile any other file: a path attribute, an include!, and a module named
target.

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
SKIPPED_DIRECTORY = "target"
ATTRIBUTES = ("external_body", "exec_allows_no_decreases_clause")
ATTRIBUTE = re.compile(r"#\[verifier(?:::(\w+)\]|\((\w+)\)\])")
CLASSES = ("glue", "gap", "unproven")
ASSUMED = "assume_specification"
VOUCHERS = ("hardware", "kernel")
SPECIFICATION = re.compile(r"(?:pub(?:\([^)]*\))?\s+)?assume_specification\b[^\[]*\[([^\]]+)\]")
CITE = "// cite: "
KERNEL = "// kernel: "
DOCUMENTS_PATH = "tools/hardware-documents"
# vstd's assume, admit and assume_, as words: a call, a path, or a use that imports one under another name.
ASSUMPTION = re.compile(r"\b(assume|admit|assume_)\b")
# The words that exempt code from the proof: the two counted attributes, the assumed specification,
# and the forms the marked crates do not use (an axiom fn, an external fn, an external function, trait
# or type specification, a function assumed to terminate).
EXEMPTING = re.compile(r"\b(axiom|external|external_fn_specification|external_trait_specification|"
                       r"external_type_specification|assume_specification|"
                       r"external_body|exec_allows_no_decreases_clause|assume_termination|"
                       r"assume_unsupported_attributes)\b")
# Any other verifier attribute whose name starts with external, in either spelling, and any attribute
# under verus::internal, the namespace the verus! macro writes its own attributes into.
VERIFIER_EXTERNAL = re.compile(r"verifier\s*(?:::|\()\s*(external\w*)|\b(verus\s*::\s*internal)\b")
# An unstable feature, which the toolchain's RUSTC_BOOTSTRAP lets a crate turn on: one of them builds an
# identifier from pieces, so a word this check looks for need not appear in the source. The marked crates
# turn on none.
FEATURE = re.compile(r"\bfeature\s*\(")
# vstd's constructors of a ghost or tracked value from nothing, allowed only in the body of a counted
# external_body function, whose claim the list holds.
CONJURE = re.compile(r"\bassume_new\w*")
# The unsafe keyword, in a block, a fn, an impl, a trait, an extern block or an attribute: the only way
# safe Rust leaves to make or copy a token it cannot name the fields of, allowed only in counted glue.
UNSAFE = re.compile(r"\bunsafe\b")
# What states the specification of exec code Verus does not read: an impl of one of vstd's trait
# extensions (FromSpecImpl, PartialEqSpecImpl, IteratorSpecImpl and the rest), whose spec vstd's
# specification of the trait's method ensures for an impl of the method outside verus!; the StructuralEq
# derive, which writes a PartialEqSpecImpl for whatever PartialEq the type has; and the exec_spec macros,
# which write one or trust their own exec code. The marked crates use none.
TRUSTED_SPEC = re.compile(r"\b(\w*SpecImpl|StructuralEq|exec_spec(?:_verified|_unverified|_type)?)\b")
# What makes rustc compile a file the scan does not read: a path attribute, in any attribute or
# cfg_attr, an include!, and a module named target, whose directory the scan leaves out.
UNREAD_FILE = re.compile(r"#\s*!?\s*\[\s*path\b|\bpath\s*=\s*(?:r#*)?\"|\binclude\s*!|"
                         r"\bmod\s+(?:r#)?target\b")

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


def code_lines(source):
    """Each line of one file as rustc reads its code: every comment, line or block, nested or not, and
    the inside of every string and character literal are blanked, so a '//' inside a block comment or a
    string opens no comment, and the code after either on the same line is read. The delimiters of a
    literal stay, and each line keeps its length."""
    out = list(source)
    length = len(source)

    def blank(start, end):
        for at in range(start, end):
            if out[at] != "\n":
                out[at] = " "

    def ident(at):
        return 0 <= at < length and (source[at].isalnum() or source[at] == "_")

    i = 0
    if source.startswith("\ufeff"):
        i = 1
    if shebang(source, i):
        end = source.find("\n", i)
        end = length if end < 0 else end
        blank(0, end)
        i = end
    while i < length:
        char = source[i]
        if source.startswith("//", i):
            end = source.find("\n", i)
            end = length if end < 0 else end
            blank(i, end)
            i = end
        elif source.startswith("/*", i):
            depth, end = 1, i + 2
            while end < length and depth:
                if source.startswith("/*", end):
                    depth, end = depth + 1, end + 2
                elif source.startswith("*/", end):
                    depth, end = depth - 1, end + 2
                else:
                    end += 1
            blank(i, end)
            i = end
        elif char == "r" and (not ident(i - 1) or (source[i - 1] in "bc" and not ident(i - 2))):
            hashes = 0
            while i + 1 + hashes < length and source[i + 1 + hashes] == "#":
                hashes += 1
            if i + 1 + hashes < length and source[i + 1 + hashes] == '"':
                start = i + 2 + hashes
                close = '"' + "#" * hashes
                end = source.find(close, start)
                end = length if end < 0 else end
                blank(start, end)
                i = end + len(close)
            else:
                i += 1
        elif char == '"':
            end = i + 1
            while end < length and source[end] != '"':
                end += 2 if source[end] == "\\" else 1
            blank(i + 1, min(end, length))
            i = end + 1
        elif char == "'":
            if source.startswith("\\", i + 1):
                end = source.find("'", i + 3)
            elif i + 2 < length and source[i + 2] == "'":
                end = i + 2
            else:
                end = -1
            if end < 0:
                i += 1
            else:
                blank(i + 1, end)
                i = end + 1
        else:
            i += 1
    return "".join(out).split("\n")[:len(source.splitlines())]


def shebang(source, start):
    """Whether the first line, from start (after a byte order mark), is a shebang rustc drops: it opens
    with #! and the first token after that, past whitespace and comments other than doc comments, is not
    [, which would make it an inner attribute."""
    if not source.startswith("#!", start):
        return False
    i, length = start + 2, len(source)
    while i < length:
        if source[i].isspace():
            i += 1
        elif source.startswith("//", i) and not (source.startswith("//!", i) or
                                                (source.startswith("///", i) and not source.startswith("////", i))):
            end = source.find("\n", i)
            i = length if end < 0 else end
        elif source.startswith("/*", i) and not (source.startswith("/*!", i) or (
                source.startswith("/**", i) and not source.startswith(("/***", "/**/"), i))):
            depth, i = 1, i + 2
            while i < length and depth:
                if source.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            break
    return not source.startswith("[", i)


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
    code = [line.strip() for line in code_lines(source)]
    items = []
    for index, line in enumerate(code):
        exempting = attribute(line)
        if exempting is None:
            continue
        at = f"{path}:{index + 1}"
        stated = parse_reason(exempting, lines[index + 1] if index + 1 < len(lines) else "")
        if stated is None:
            raise Unreadable(f"{at}: no reason line in the form // {exempting}(<class>): <reason>")
        name = next(filter(None, map(item_name, code[index + 2:])), None)
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
    for index, line in enumerate(line.strip() for line in code_lines(source)):
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
    """Each line of one file that names assume, admit or assume_ in its code, outside every comment and
    literal, with where it is."""
    found = []
    for index, (line, code) in enumerate(zip(source.splitlines(), code_lines(source))):
        if ASSUMPTION.search(code):
            found.append(f"{path}:{index + 1}: {line.strip()}")
    return found


def unread_exemptions(path, source):
    """Each line of one file that exempts code from the proof in a form this check does not count.
    The counted forms are a line opening with one counted attribute in either spelling, and a line
    opening an assumed specification with its name in brackets. Any other word of EXEMPTING, or any
    verifier attribute whose name starts with external, in a line's code is refused: an axiom fn, an
    external fn, an external function, trait or type specification, assume_termination, a counted
    attribute after another attribute, inside cfg_attr or as an inner attribute, and an assumed
    specification the line does not open. So is a line that makes rustc compile a file the scan does
    not read: a path attribute, an include!, and a module named target."""
    refused = []
    for index, (line, code) in enumerate(zip(source.splitlines(), code_lines(source))):
        if UNREAD_FILE.search(code):
            refused.append(f"{path}:{index + 1}: {line.strip()} compiles a file this check does not read")
        matches = {match.start(1): match.group(1) for match in EXEMPTING.finditer(code)}
        matches.update({match.start(match.lastindex): match.group(match.lastindex)
                        for match in VERIFIER_EXTERNAL.finditer(code)})
        if FEATURE.search(code):
            refused.append(f"{path}:{index + 1}: {line.strip()} turns on an unstable feature, which may build "
                           "a word this check looks for from pieces")
        words = list(matches.values())
        if not words:
            continue
        opening = code.strip()
        counted = len(words) == 1 and (
            attribute(opening) == words[0] or (words[0] == ASSUMED and SPECIFICATION.match(opening)))
        if not counted:
            refused.append(f"{path}:{index + 1}: {line.strip()} exempts code from the proof in a form this "
                           "check does not count")
    return refused


def body_lines(code, declared):
    """The indices of the lines of the body of the function declared on line declared: from the brace
    that opens it to the brace that closes it; none for a declaration with no body."""
    text = "\n".join(code[declared:])
    opening = text.find("{")
    if opening < 0 or ";" in text[:opening]:
        return set()
    depth = 0
    for at in range(opening, len(text)):
        depth += {"{": 1, "}": -1}.get(text[at], 0)
        if depth == 0:
            break
    return set(range(declared + text.count("\n", 0, opening), declared + text.count("\n", 0, at) + 1))


def glue_bodies(code):
    """The indices of the lines inside the body of each counted external_body function."""
    inside = set()
    for index, line in enumerate(code):
        if attribute(line.strip()) != "external_body":
            continue
        declared = next((at for at in range(index + 2, len(code)) if item_name(code[at].strip())), None)
        if declared is not None:
            inside |= body_lines(code, declared)
    return inside


def specified_bodies(code):
    """The indices of the lines inside the body of each function an assumed specification in the same
    file names: the hardware function or system call whose claim the list holds."""
    named = set()
    for line in code:
        match = SPECIFICATION.match(line.strip())
        if match is not None:
            named.add(re.sub(r"\s", "", match.group(1)).rsplit("::", 1)[-1])
    inside = set()
    for index, line in enumerate(code):
        if item_name(line.strip()) in named and re.search(r"\bfn\b", line):
            inside |= body_lines(code, index)
    return inside


def conjurings(path, source):
    """Each line of one file that makes a ghost or tracked value from nothing, outside the body of a
    counted external_body function."""
    code = code_lines(source)
    allowed = glue_bodies(code)
    return [f"{path}:{index + 1}: {line.strip()}"
            for index, (line, text) in enumerate(zip(source.splitlines(), code))
            if CONJURE.search(text) and index not in allowed]


def unsafe_lines(path, source):
    """Each line of one file whose code says unsafe outside the body of a counted external_body
    function and of a function an assumed specification in the file names. Safe Rust cannot make a
    value of a type whose fields are private to another module, nor copy one that is neither Copy nor
    Clone; only unsafe code can (core::mem::zeroed, core::ptr::read, MaybeUninit::assume_init,
    transmute), and Verus does not read code outside verus! that verified code reaches through a
    trait (design/flush-without-waiting/)."""
    code = code_lines(source)
    allowed = glue_bodies(code) | specified_bodies(code)
    return [f"{path}:{index + 1}: {line.strip()}"
            for index, (line, text) in enumerate(zip(source.splitlines(), code))
            if UNSAFE.search(text) and index not in allowed]


def trusted_specifications(path, source):
    """Each line of one file whose code names a way to state the specification of exec code Verus does
    not read: vstd's From::from, for one, ensures from_spec for any impl with a FromSpecImpl, and nothing
    holds an impl outside verus! to it, so the spec can say a token comes out that the code never made."""
    return [f"{path}:{index + 1}: {line.strip()}"
            for index, (line, code) in enumerate(zip(source.splitlines(), code_lines(source)))
            if TRUSTED_SPEC.search(code)]


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
    """The Rust sources under a directory, leaving out build output under target."""
    for entry in sorted(directory.iterdir()):
        if entry.is_dir():
            if entry.name != SKIPPED_DIRECTORY:
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
            refused.extend(f"{line} makes a ghost or tracked value outside counted glue"
                           for line in conjurings(path, source))
            refused.extend(f"{line} is unsafe code outside counted glue, which may make or copy a value "
                           "the proof cannot see" for line in unsafe_lines(path, source))
            refused.extend(f"{line} states a spec of code Verus does not read, which the proof takes on trust"
                           for line in trusted_specifications(path, source))
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

    def test_assumptions_finds_admit_under_another_name_and_by_path(self):
        source = ("use vstd::prelude::admit as settle;\n"
                  "    vstd::prelude::admit();\n"
                  "use vstd::pervasive::{assume};\n")
        self.assertEqual(len(assumptions("a.rs", source)), 3)

    def test_assumptions_finds_assume_underscore(self):
        self.assertEqual(assumptions("a.rs", "    vstd::prelude::assume_(false);\n"),
                         ["a.rs:1: vstd::prelude::assume_(false);"])

    def test_assumptions_fail_the_tree(self):
        repo = Tests.workspace(self, {"kernel/verified": (True, {
            "capability/mapping.rs": "use vstd::prelude::admit as settle;\nfn f() { settle(); }\n"})})
        _, refused = scan_tree(repo, DOCUMENTS)
        self.assertEqual(refused, ["kernel/verified/capability/mapping.rs:1: use vstd::prelude::admit as settle; "
                                   "assumes what the proof should show"])

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

    def test_build_output_under_target_is_not_scanned(self):
        live = f"{ATTR}\n// external_body(gap): x\nfn f()\n"
        repo = self.workspace({"heap": (True, {"target/b.rs": live, "target/debug/c.rs": "fn f() { admit(); }\n"})})
        self.assertEqual(scan_tree(repo, {}), ([], []))

    def test_a_directory_named_old_is_scanned(self):
        repo = self.workspace({"kernel/verified": (True, {
            "capability/mod.rs": "pub mod old;\n", "capability/old/mod.rs": "fn f() { admit(); }\n"})})
        _, refused = scan_tree(repo, {})
        self.assertEqual(refused, ["kernel/verified/capability/old/mod.rs:1: fn f() { admit(); } "
                                   "assumes what the proof should show"])

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
        "external_trait_specification": (
            "#[verifier::external_trait_specification]\npub trait ExForge { type ExternalTraitSpecificationFor: Forge; }\n"
        ),
        "external_type_specification": (
            "#[verifier::external_type_specification]\npub struct ExForged(Forged);\n"
        ),
        "another verifier::external attribute": "#[verifier::external_trait_extension(F via G)]\npub trait F {}\n",
        "another verifier(external) attribute": "#[verifier(external_derive)]\npub struct S;\n",
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

    def test_a_file_the_scan_does_not_read_is_refused(self):
        forms = {
            "a #[path] module": '#[path = "forge.inc"] pub mod forge;\n',
            "a #[path] module on its own line": '#[path = "forge.inc"]\npub mod forge;\n',
            "a #[path] inside cfg_attr": '#[cfg_attr(verus_keep_ghost, path = "forge.inc")]\nmod forge;\n',
            "an inner #![path]": '#![path = "forge.inc"]\n',
            "an include!": 'include!("forge.inc");\n',
            "an include! by path": 'verus! { core::include!("forge.inc"); }\n',
            "a module named target": "pub mod target;\n",
            "a raw module named target": "mod r#target { }\n",
        }
        for form, source in forms.items():
            with self.subTest(form):
                self.assertTrue(unread_exemptions("kernel/verified/capability/mod.rs", source), form)

    def test_assume_termination_is_refused(self):
        for spelling in ("#[verifier::assume_termination]", "#[verifier(assume_termination)]"):
            source = f"{spelling}\nfn spin() -> Tracked<BaseRegister> {{ spin() }}\n"
            self.assertTrue(unread_exemptions("a.rs", source), spelling)

    def test_names_that_only_look_like_a_path_or_an_include_are_not_refused(self):
        source = ("let ghost path = SpacePath { l4, l3: 0 };\n"
                  "let included = include_count;\n"
                  "mod targets;\n")
        self.assertEqual(unread_exemptions("a.rs", source), [])

    def test_comments_and_longer_names_are_not_refused(self):
        source = (
            "// #[verifier::external] and an axiom fn, in a comment\n"
            "/// external_fn_specification\n"
            "let axiomatic = external_bodyless; // #![verifier::external_body]\n"
        )
        self.assertEqual(unread_exemptions("a.rs", source), [])

class ForgeryTests(unittest.TestCase):
    """The forms a skeptic used to forge a BaseRegister and a TlbModel outside an arch module, each
    refused: rustc reads them as code the check would otherwise not see as such."""

    FORGE = ("proof fn f() -> (tracked r: crate::arch::BaseRegister) { admit(); vstd::pervasive::proof_from_false() }\n")

    def refused(self, path, files):
        repo = Tests.workspace(self, {"kernel/verified": (True, files)})
        _, refused = scan_tree(repo, DOCUMENTS)
        return [line for line in refused if line.startswith(f"kernel/verified/{path}:")]

    def test_a_shebang_line_opening_a_block_comment_is_dropped_as_rustc_drops_it(self):
        for path in ("capability/mapping.rs", "lib.rs"):
            source = f"#!/*\n// SPDX-License-Identifier: MIT\nverus! {{\n{self.FORGE}// */\n}}\n"
            with self.subTest(path):
                self.assertTrue(self.refused(path, {path: source}))

    def test_a_shebang_line_is_blank_and_an_inner_attribute_is_code(self):
        self.assertEqual(code_lines("#!/* x\nadmit(); // */\n"), ["      ", "admit();      "])
        self.assertEqual(code_lines("\ufeff#!/*\nadmit(); */\n"), ["     ", "admit(); */"])
        for source in ("#![no_std] /*\nx */\n", "#! [no_std]\n", "#!/* c */[no_std]\n", "#!\n// c\n[no_std]\n"):
            with self.subTest(source):
                self.assertTrue(code_lines(source)[0].startswith("#!"), source)

    def test_a_shebang_followed_by_a_doc_comment_is_dropped(self):
        self.assertEqual(code_lines("#!/// x\n[no_std]\n")[0].strip(), "")

    def test_a_feature_that_pastes_identifiers_is_refused(self):
        for source in ("#![feature(macro_metavar_expr_concat)]\n", "#![feature(concat_idents)]\n",
                       "#![cfg_attr(verus_keep_ghost, feature (macro_metavar_expr_concat))]\n"):
            with self.subTest(source):
                self.assertTrue(unread_exemptions("kernel/verified/lib.rs", source), source)

    def test_a_cargo_feature_test_is_not_refused(self):
        source = '#[cfg(feature = "lock_stats")]\nfn f() {}\nlet x = cfg!(feature = "a");\n'
        self.assertEqual(unread_exemptions("a.rs", source), [])

    def test_assume_new_in_an_impl_outside_verus_is_refused(self):
        source = ("impl Default for SkBox { fn default() -> Self { SkBox { t: Tracked::assume_new(), "
                  "m: Tracked::assume_new() } } }\nverus! {\npub struct SkBox { pub t: Tracked<BaseRegister> }\n}\n")
        self.assertTrue(self.refused("capability/mapping.rs", {"capability/mapping.rs": source}))
        for spelling in ("Ghost::assume_new()", "Tracked::assume_new_fallback(f)", "Tracked :: assume_new ()"):
            with self.subTest(spelling):
                self.assertTrue(conjurings("a.rs", f"fn f() -> Tracked<T> {{ {spelling} }}\n"), spelling)

    def test_assume_new_in_a_counted_external_body_is_accepted(self):
        source = ("#[verifier::external_body]\n// external_body(gap): conjures\nfn page_permission(x: u8)\n"
                  "    -> (perm: Tracked<PointsToRaw>)\n    ensures perm@.is_range(0, 1),\n{\n"
                  "    Tracked::assume_new()\n}\nfn g() -> Tracked<T> { Tracked::assume_new() }\n")
        self.assertEqual(conjurings("a.rs", source), ["a.rs:9: fn g() -> Tracked<T> { Tracked::assume_new() }"])

    def test_unsafe_outside_counted_glue_is_refused(self):
        forms = {
            "zeroed in a Default impl": "impl Default for SkBox { fn default() -> Self { unsafe { core::mem::zeroed() } } }\n",
            "ptr::read in a From impl": ("impl<'a> From<&'a SkTok> for SkTok { fn from(v: &'a SkTok) -> SkTok "
                                         "{ unsafe { core::ptr::read(v) } } }\n"),
            "assume_init": ("impl Default for SkBox { fn default() -> Self "
                            "{ unsafe { core::mem::MaybeUninit::uninit().assume_init() } } }\n"),
            "transmute": "fn f(x: [u8; 0]) -> SkBox { unsafe { core::mem::transmute(x) } }\n",
            "an unsafe impl": "unsafe impl Send for SkBox {}\n",
            "an unsafe fn": "unsafe fn f() {}\n",
        }
        for name, form in forms.items():
            with self.subTest(name):
                source = f"{form}verus! {{\npub struct SkBox {{ pub t: Tracked<crate::arch::BaseRegister> }}\n}}\n"
                self.assertEqual(len(self.refused("capability/mapping.rs", {"capability/mapping.rs": source})), 1)

    def test_the_from_spec_duplicate_is_refused(self):
        source = ("impl<'a> From<&'a SkTok> for SkTok { fn from(v: &'a SkTok) -> SkTok { unsafe { core::ptr::read(v) } } }\n"
                  "verus! {\npub struct SkTok { pub t: Tracked<crate::arch::BaseRegister> }\n"
                  "#[cfg(verus_keep_ghost)]\nimpl<'a> vstd::std_specs::convert::FromSpecImpl<&'a SkTok> for SkTok {\n"
                  "    open spec fn obeys_from_spec() -> bool { true }\n"
                  "    open spec fn from_spec(v: &'a SkTok) -> SkTok { *v }\n}\n}\n")
        self.assertEqual([line.split(":")[1] for line in self.refused("capability/mapping.rs",
                                                                      {"capability/mapping.rs": source})], ["1", "5"])

    def test_a_safe_from_with_a_from_spec_impl_is_refused(self):
        source = ("impl From<SkSeed> for SkBox { fn from(_v: SkSeed) -> SkBox { SkBox { t: None, m: None } } }\n"
                  "verus! {\npub struct SkSeed {}\n"
                  "pub struct SkBox { pub t: Option<Tracked<crate::arch::BaseRegister>>, "
                  "pub m: Option<Tracked<crate::arch::TlbModel>> }\n"
                  "#[cfg(verus_keep_ghost)]\nimpl vstd::std_specs::convert::FromSpecImpl<SkSeed> for SkBox {\n"
                  "    open spec fn obeys_from_spec() -> bool { true }\n"
                  "    open spec fn from_spec(v: SkSeed) -> SkBox { SkBox { t: Some(vstd::pervasive::arbitrary()), "
                  "m: Some(vstd::pervasive::arbitrary()) } }\n}\n"
                  "pub fn sk_forge() -> (r: (Tracked<crate::arch::BaseRegister>, Tracked<crate::arch::TlbModel>)) "
                  "{ let b = SkBox::from(SkSeed {}); (b.t.unwrap(), b.m.unwrap()) }\n}\n")
        self.assertEqual([line.split(":")[1] for line in self.refused("capability/mapping.rs",
                                                                      {"capability/mapping.rs": source})], ["6"])

    def test_an_identity_from_whose_from_spec_names_a_ghost_field_is_refused(self):
        source = ("impl From<SkHold> for SkOut { fn from(v: SkHold) -> SkOut { SkOut { t: v.t } } }\n"
                  "verus! {\npub struct SkOut { pub t: Tracked<crate::arch::BaseRegister> }\n"
                  "pub struct SkHold { pub t: Tracked<crate::arch::BaseRegister>, pub g: Ghost<SkOut> }\n"
                  "use vstd::std_specs::convert::FromSpecImpl as Renamed;\n"
                  "#[cfg(verus_keep_ghost)]\nimpl Renamed<SkHold> for SkOut {\n"
                  "    open spec fn obeys_from_spec() -> bool { true }\n"
                  "    open spec fn from_spec(v: SkHold) -> SkOut { v.g@ }\n}\n}\n")
        self.assertEqual([line.split(":")[1] for line in self.refused("capability/mapping.rs",
                                                                      {"capability/mapping.rs": source})], ["5"])

    def test_every_spec_vstd_takes_on_trust_for_unread_code_is_refused(self):
        forms = {
            "PartialEqSpecImpl": ("impl PartialEq for SkTok { fn eq(&self, _o: &Self) -> bool { true } }\n"
                                  "verus! {\nimpl vstd::std_specs::cmp::PartialEqSpecImpl for SkTok {\n"
                                  "    open spec fn obeys_eq_spec() -> bool { true }\n"
                                  "    open spec fn eq_spec(&self, o: &Self) -> bool { true }\n}\n}\n"),
            "TryFromSpecImpl": "verus! {\nimpl vstd::std_specs::convert::TryFromSpecImpl<u8> for SkTok {}\n}\n",
            "IteratorSpecImpl": "verus! {\nimpl IteratorSpecImpl for SkIter {}\n}\n",
            "a glob over the spec traits": "use vstd::std_specs::cmp::{PartialEqSpecImpl, OrdSpecImpl};\n",
            "StructuralEq": "verus! {\n#[derive(PartialEq, Eq, StructuralEq)]\npub struct SkTok { pub x: u8 }\n}\n",
            "exec_spec_unverified": "exec_spec_unverified! {\n    spec fn f(x: u8) -> u8 { x }\n}\n",
            "exec_spec_verified": "use vstd::prelude::exec_spec_verified as checked;\n",
        }
        for name, form in forms.items():
            with self.subTest(name):
                self.assertEqual(len(self.refused("lib.rs", {"lib.rs": form})), 1, form)
                self.assertTrue(all("spec of code Verus does not read" in line
                                    for line in self.refused("lib.rs", {"lib.rs": form})))

    def test_names_that_only_contain_a_trusted_spec_word_are_not_refused(self):
        source = ('// impl FromSpecImpl<u8> for X\nlet s = "PartialEqSpecImpl";\n'
                  "fn from_spec_impl_count() {}\nlet exec_specs = 0;\nlet my_exec_spec = 1;\n"
                  "pub struct StructuralEqual {}\n")
        self.assertEqual(self.refused("lib.rs", {"lib.rs": source}), [])

    def test_unsafe_in_a_counted_external_body_is_accepted(self):
        source = ("#[verifier::external_body]\n// external_body(glue): hw\nfn spin_hint()\n{\n"
                  "    unsafe { core::arch::asm!(\"pause\") }\n}\nfn g() { unsafe { core::arch::asm!(\"pause\") } }\n")
        self.assertEqual(unsafe_lines("a.rs", source),
                         ['a.rs:7: fn g() { unsafe { core::arch::asm!("pause") } }'])

    def test_unsafe_under_a_termination_exemption_is_refused(self):
        source = ("#[verifier::exec_allows_no_decreases_clause]\n// exec_allows_no_decreases_clause(unproven): x\n"
                  "fn spin() {\n    unsafe { core::arch::asm!(\"pause\") }\n}\n")
        self.assertEqual(len(unsafe_lines("a.rs", source)), 1)

    def test_unsafe_in_the_function_an_assumed_specification_names_is_accepted(self):
        source = ("verus! {\n// cite: amd-apm2 5.5.1 x\npub assume_specification[flush_every_context](core: usize)\n"
                  "    ensures true;\n}\npub fn flush_every_context(_core: usize) {\n    unsafe {\n"
                  "        core::arch::asm!(\"nop\");\n    }\n}\npub fn other(_core: usize) {\n"
                  "    unsafe { core::arch::asm!(\"nop\") }\n}\n")
        self.assertEqual(unsafe_lines("arch/x86_64.rs", source),
                         ['arch/x86_64.rs:12: unsafe { core::arch::asm!("nop") }'])

    def test_unsafe_in_a_comment_a_string_or_a_longer_name_is_not_refused(self):
        source = ('// unsafe { core::mem::zeroed() }\nlet s = "unsafe";\nlet unsafe_count = 0;\n'
                  "#[allow(unsafe_code)]\n")
        self.assertEqual(unsafe_lines("a.rs", source), [])

    def test_assume_new_under_a_termination_exemption_is_refused(self):
        source = ("#[verifier::exec_allows_no_decreases_clause]\n// exec_allows_no_decreases_clause(unproven): x\n"
                  "fn spin() -> Tracked<T> {\n    Tracked::assume_new()\n}\n")
        self.assertEqual(len(conjurings("a.rs", source)), 1)

    def test_assume_unsupported_attributes_is_refused(self):
        source = "#[verifier::assume_unsupported_attributes]\n#[no_mangle] pub fn sk_named() {}\n"
        self.assertTrue(unread_exemptions("a.rs", source))

    def test_a_verus_internal_attribute_is_refused(self):
        for source in ("#[verus::internal(external_trait_blanket)]\nimpl<T> F for T {}\n",
                       "#[verus :: internal(verus_macro)]\nfn f() {}\n"):
            with self.subTest(source):
                self.assertTrue(unread_exemptions("a.rs", source), source)


class LexTests(unittest.TestCase):
    """The check reads a line as rustc does: a comment ends at its */ and a string at its quote, so code
    after either on the same line is read, and a // inside either opens no comment."""

    FORGE = "proof fn f() -> (tracked r: crate::arch::BaseRegister) { admit(); proof_from_false() }"

    def test_code_after_a_block_comment_holding_slashes_is_read(self):
        source = f"/* // */ {self.FORGE}\n"
        self.assertTrue(assumptions("a.rs", source))

    def test_code_after_a_string_holding_slashes_is_read(self):
        for source in (f'#[doc = "//"] {self.FORGE}\n', f'#[doc = r#"//"#] {self.FORGE}\n',
                       f'#[doc = "\\"//"] {self.FORGE}\n', f"let c = '\"'; {self.FORGE}\n",
                       f"let c = b'\"'; {self.FORGE}\n"):
            with self.subTest(source):
                self.assertTrue(assumptions("a.rs", source))

    def test_a_counted_attribute_after_such_a_comment_is_counted(self):
        source = "/* // */ #[verifier::external_body]\n// external_body(glue): x\nproof fn f() {}\n"
        self.assertEqual(scan("a.rs", source), [body("a.rs", "f", "glue", "x")])
        self.assertEqual(compare(scan("a.rs", source), []), ["a.rs f external_body (glue: x) is not on the list"])
        self.assertEqual(unread_exemptions("a.rs", source), [])

    def test_an_exemption_after_such_a_string_is_refused(self):
        self.assertTrue(unread_exemptions("a.rs", '#[doc = "//"] #[verifier::external] fn f() {}\n'))

    def test_comments_and_strings_hide_what_they_hold(self):
        source = ('/* admit();\n   still a comment /* nested */ admit();\n*/ fn g() {}\n'
                  'let s = "admit(); // #[verifier::external]";\n'
                  'let t = "line one\n  admit();\n";\n'
                  "fn h<'a>(x: &'a u8) -> char { 'x' } // admit();\n"
                  "/// admit()\n")
        self.assertEqual(assumptions("a.rs", source), [])
        self.assertEqual(unread_exemptions("a.rs", source), [])

    def test_an_attribute_inside_a_block_comment_is_not_counted(self):
        source = "/*\n#[verifier::external_body]\n// external_body(glue): x\nfn f() {}\n*/\n"
        self.assertEqual(scan("a.rs", source), [])

    def test_lexing_keeps_every_line(self):
        source = 'a /* x\ny */ b "s\nt" c\n'
        self.assertEqual(code_lines(source), ["a     ", '     b " ', ' " c'])


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
