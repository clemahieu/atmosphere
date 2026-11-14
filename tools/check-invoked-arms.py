#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Name each ensures conjunct an arm of invoked does not carry.

An arm of invoked carries the postcondition of the operation the entry calls for that arm: the
operation's ensures calls it and the arm's spec function calls it.
design/invoked-arm-is-the-operation-postcondition/.

The check reads the verified sources and takes no list of operations. An arm of invoked that calls
spec_retyped, spec_derived, spec_moved, spec_deleted, spec_revoked, spec_linked, spec_mapped,
spec_unmapped or spec_probed is paired, by the Operation variant, with the arm of dispatch. The
operations are the pub fn methods of impl CapKernel that the invoke_* function named there calls
on self. Those calls are read from the invoke_* body and not followed further, and the invoke_*
ensures is not read. A pub fn the bodies of several invoke_* functions in dispatch call is an
operation only of those among them that call no other pub fn; when every one of them calls another
as well, it is an operation of each. The last arm of invoked is post == pre with spec_outcome; its operations are
the pub fn methods the remaining arms of dispatch call on self (print, power_off and inspect). An
operation dispatch does not call is not read.

An ensures is split on top-level &&& and on the commas between its clauses, which Verus conjoins
the same way, after comments and string literals are blanked. A conjunct that mentions the ghost
step counter steps is skipped, and so are final(self).wf() and old(self).wf(). What remains is
carried when it is the whole kernel unchanged (*final(self) == *old(self) or final(self) ==
old(self)) and the arm or its spec function contains post == pre; when, after one leading
implication and a #[trigger] on the call are stripped, it is one call Name(...), Self::Name(...),
old(self).Name(...), final(self).Name(...) or self.Name(...) and the spec function calls Name; or
when it is ret == Name(...), ret == old(self).Name(...) or ret == self.Name(...) and the spec
function calls Name. A field comparison, a quantifier or two calls is not carried.

The check prints one line path:function:conjunct for each conjunct it does not count as carried,
the conjunct with its whitespace collapsed, and the path from the repository root. It prints
nothing and exits 0 when every conjunct is carried. Exit 1 when a conjunct is printed or the
sources cannot be read. Exit 2 on a bad invocation. Throwaway modules are not what the entry
calls, and are not read.

usage: tools/check-invoked-arms.py              the verified sources
       tools/check-invoked-arms.py --root DIR   sources under DIR, or under DIR/kernel/verified
       tools/check-invoked-arms.py --test       this script's own tests
"""

import re
import sys
import tempfile
import unittest
from collections import namedtuple
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
CLAUSES = {
    "requires", "ensures", "decreases", "recommends", "opens_invariants", "invariant", "no_unwind",
}
QUANTS = ("forall", "exists", "choose")
UNCHANGED = ("*final(self) == *old(self)", "final(self) == old(self)")
WF = ("final(self).wf()", "old(self).wf()")
CALL = re.compile(r"^(?:Self::|old\(self\)\.|final\(self\)\.|self\.)?([A-Za-z_]\w*)\s*\(")
RESULT = re.compile(r"^ret == (?:old\(self\)\.|self\.)?([A-Za-z_]\w*)\s*\(")
SELF_CALL = re.compile(r"\bself\.(\w+)\s*\(")
SPEC_CALL = re.compile(r"\b(spec_\w+)\s*\(")
POST_UNCHANGED = re.compile(r"post == pre(?!\s*\.)")

# A method of impl CapKernel. `ensures` is the clause text, `body` the brace block, `full` from
# `fn` through the body, all with comments and string literals blanked.
Function = namedtuple("Function", "name kind ensures body full path")


class Malformed(Exception):
    """The sources are not in the shape this check reads; the message says where."""


def masked(text):
    """The text with every comment, string literal and character literal blanked, each character in
    its place, so that brackets and words found in it are the code's."""
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
        elif text[i] == "'" and i + 2 < n and text[i + 1] != "\\" and text[i + 2] == "'":
            end = i + 3
        elif text[i] == "'" and i + 3 < n and text[i + 1] == "\\" and text[i + 3] == "'":
            end = i + 4
        else:
            i += 1
            continue
        for j in range(i, end):
            if out[j] != "\n":
                out[j] = " "
        i = end
    return "".join(out)


def collapse(text):
    """The text with each run of whitespace turned into one space, and the ends trimmed."""
    return " ".join(text.split())


def word_at(text, i):
    """The identifier starting at i, when i is at its first character, or None."""
    if i >= len(text) or not (text[i].isalpha() or text[i] == "_"):
        return None
    if i > 0 and (text[i - 1].isalnum() or text[i - 1] == "_"):
        return None
    j = i + 1
    while j < len(text) and (text[j].isalnum() or text[j] == "_"):
        j += 1
    return text[i:j]


def at_line_start(text, i):
    """Whether i is the first non-space character of its line."""
    line = text.rfind("\n", 0, i) + 1
    return text[line:i].strip() == ""


def opens_expression(text, i, headed):
    """Whether the `{` at i continues an expression, as `=> {`, `==> {`, `= {` and `else {` do, or
    the block of an `if` or `match` whose header is open (`headed`), rather than opening the
    function body. A body sits after the signature or the ensures, so nothing assigns, implies or
    heads it."""
    if headed:
        return True
    j = i - 1
    while j >= 0 and text[j] in " \t\n":
        j -= 1
    if j >= 0 and text[j] == "=":
        return True
    if j >= 3 and text[j - 3:j + 1] == "else" and word_at(text, j - 3) == "else":
        return True
    return j >= 1 and text[j] == ">" and text[j - 1] == "="


def match_delim(text, open_at, pair):
    """The index of the bracket that closes the one at open_at. `pair` is the two characters."""
    depth = 0
    for i in range(open_at, len(text)):
        if text[i] == pair[0]:
            depth += 1
        elif text[i] == pair[1]:
            depth -= 1
            if depth == 0:
                return i
    raise Malformed(f"unclosed {pair[0]}")


def kind_of(prefix):
    """What the qualifiers before `fn` make the function: an exec method, a public one, a spec or a
    proof."""
    words = prefix.split()
    if "spec" in words:
        return "spec"
    if "proof" in words:
        return "proof"
    if "pub" in words:
        return "exec_pub"
    return "exec"


def skip_angles(text, i):
    """The index after the generic argument list whose `<` is at i."""
    depth = 0
    while i < len(text):
        if text[i] == "<":
            depth += 1
        elif text[i] == ">":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise Malformed("unclosed <")


def parse_after_name(text, i, name):
    """From just after a function's name: its ensures text, its body and the index after it. A
    signature that ends in `;` has an empty body."""
    while i < len(text) and text[i].isspace():
        i += 1
    if i < len(text) and text[i] == "<":
        i = skip_angles(text, i)
        while i < len(text) and text[i].isspace():
            i += 1
    if i >= len(text) or text[i] != "(":
        raise Malformed(f"{name}: no parameter list")
    i = match_delim(text, i, "()") + 1
    depth = 0
    mode = None
    buf = i
    parts = []
    headed = False
    while i < len(text):
        char = text[i]
        if char in "([{":
            if char == "{" and depth == 0:
                if not opens_expression(text, i, headed):
                    if mode == "ensures":
                        parts.append(text[buf:i])
                    body_end = match_delim(text, i, "{}")
                    return "".join(parts), text[i:body_end + 1], body_end + 1
                headed = False
            depth += 1
            i += 1
            continue
        if char in ")]}":
            depth -= 1
            i += 1
            continue
        if depth == 0 and char == ";":
            if mode == "ensures":
                parts.append(text[buf:i])
            return "".join(parts), "", i + 1
        if depth == 0 and word_at(text, i) in ("if", "match"):
            headed = True
            i += 2
            continue
        if depth == 0 and at_line_start(text, i):
            word = word_at(text, i)
            if word in CLAUSES:
                if mode == "ensures":
                    parts.append(text[buf:i])
                mode = "ensures" if word == "ensures" else "other"
                i += len(word)
                buf = i
                continue
        i += 1
    raise Malformed(f"{name}: no body")


def functions_in(text, path):
    """Each method of each impl CapKernel in one masked file."""
    found = []
    key = "impl CapKernel"
    i = 0
    while True:
        j = text.find(key, i)
        if j < 0:
            break
        after = j + len(key)
        before_ok = j == 0 or not (text[j - 1].isalnum() or text[j - 1] == "_")
        after_ok = after >= len(text) or not (text[after].isalnum() or text[after] == "_")
        if not before_ok or not after_ok:
            i = after
            continue
        brace = text.find("{", after)
        if brace < 0:
            break
        end = match_delim(text, brace, "{}")
        found.extend(methods(text, brace + 1, end, path))
        i = end + 1
    return found


def methods(text, start, end, path):
    """The methods between start and end, which is the interior of one impl."""
    found = []
    i = start
    depth = 0
    while i < end:
        char = text[i]
        if char in "([{":
            depth += 1
            i += 1
            continue
        if char in ")]}":
            depth -= 1
            i += 1
            continue
        word = word_at(text, i)
        if word is None:
            i += 1
            continue
        if word == "fn" and depth == 0:
            line = text.rfind("\n", start, i) + 1
            name_at = i + 2
            while name_at < end and text[name_at].isspace():
                name_at += 1
            name = word_at(text, name_at)
            if name is None:
                raise Malformed(f"fn without a name in {path}")
            ensures, body, nxt = parse_after_name(text, name_at + len(name), name)
            found.append(Function(name, kind_of(text[line:i]), ensures, body, text[i:nxt], path))
            i = nxt
            continue
        i += len(word)
    return found


def skip_binder(text, i, depth):
    """The index after a quantifier's `|...|` binder, whose commas are not ensures separators, or
    None when i is not at one."""
    if depth != 0:
        return None
    for word in QUANTS:
        if not text.startswith(word, i) or word_at(text, i) != word:
            continue
        j = i + len(word)
        while j < len(text) and text[j].isspace():
            j += 1
        if j >= len(text) or text[j] != "|":
            return None
        j += 1
        while j < len(text):
            if text[j] == "|" and not text.startswith("||", j):
                return j + 1
            j += 1
        return None
    return None


def split_conjuncts(ensures):
    """The ensures clause split into its top-level conjuncts, whitespace collapsed. A comma and an
    `&&&` count only outside brackets, and a comma inside a quantifier binder does not count."""
    parts, buf, depth, i, n = [], [], 0, 0, len(ensures)
    while i < n:
        jumped = skip_binder(ensures, i, depth)
        if jumped is not None:
            buf.append(ensures[i:jumped])
            i = jumped
            continue
        char = ensures[i]
        if char in "([{":
            depth += 1
            buf.append(char)
            i += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
            buf.append(char)
            i += 1
        elif depth == 0 and ensures.startswith("&&&", i):
            parts.append("".join(buf))
            buf = []
            i += 3
        elif depth == 0 and char == ",":
            parts.append("".join(buf))
            buf = []
            i += 1
        else:
            buf.append(char)
            i += 1
    parts.append("".join(buf))
    return [collapsed for part in parts if (collapsed := collapse(part))]


def calls(text, name):
    """Whether text calls name: the name followed by an argument list."""
    return re.search(r"\b" + re.escape(name) + r"\s*\(", text) is not None


def unchanged(text):
    """Whether text says the kernel is unchanged, as an arm writes post == pre."""
    return POST_UNCHANGED.search(collapse(text)) is not None


def one_call(text):
    """The name of the single call text is, in the shapes the record counts, or None."""
    match = CALL.match(text)
    if match is None:
        return None
    try:
        close = match_delim(text, match.end() - 1, "()")
    except Malformed:
        return None
    if close == len(text) - 1:
        return match.group(1)
    return None


def result_call(text):
    """The name in `ret == <call>`, for the shapes the record counts, or None."""
    match = RESULT.match(text)
    if match is None:
        return None
    try:
        close = match_delim(text, match.end() - 1, "()")
    except Malformed:
        return None
    if close == len(text) - 1:
        return match.group(1)
    return None


def strip_implication(text):
    """The text after one leading `==>` whose arrow is outside brackets, or the text when it has
    none."""
    depth = 0
    i = 0
    while i < len(text):
        char = text[i]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith("==>", i):
            return text[i + 3:].strip()
        i += 1
    return text


def carried(conjunct, spec_text, arm_text):
    """Whether one ensures conjunct is carried by the arm and its spec function, or is one of the
    two shapes the record skips."""
    if re.search(r"\bsteps\b", conjunct):
        return True
    if conjunct in WF:
        return True
    if conjunct in UNCHANGED and (unchanged(arm_text) or unchanged(spec_text)):
        return True
    name = result_call(conjunct)
    if name is not None and calls(spec_text, name):
        return True
    name = one_call(re.sub(r"^#\[trigger\]\s*", "", strip_implication(conjunct)))
    return name is not None and calls(spec_text, name)


def find_operation_match(body):
    """The index of the `{` of the match whose scrutinee names the operation number, or None."""
    i = 0
    while True:
        j = body.find("match", i)
        if j < 0:
            return None
        if word_at(body, j) != "match":
            i = j + 1
            continue
        k = j + len("match")
        depth = 0
        while k < len(body):
            char = body[k]
            if char == "{" and depth == 0:
                if "operation_number" in body[j:k]:
                    return k
                break
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            k += 1
        i = j + len("match")
    return None


def parse_arms(body, open_brace):
    """The (pattern, expression) pairs of the match whose opening brace is open_brace. The pattern
    is whitespace-collapsed; the expression keeps its layout, comments already blanked."""
    end = match_delim(body, open_brace, "{}")
    i = open_brace + 1
    arms = []
    while i < end:
        while i < end and body[i].isspace():
            i += 1
        if i >= end:
            break
        start = i
        depth = 0
        while i < end:
            char = body[i]
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif depth == 0 and body.startswith("=>", i):
                break
            i += 1
        pattern = body[start:i]
        if not body.startswith("=>", i):
            break
        i += 2
        start = i
        depth = 0
        while i < end:
            char = body[i]
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif char == "," and depth == 0:
                break
            i += 1
        if collapse(pattern):
            arms.append((collapse(pattern), body[start:i]))
        if i < end and body[i] == ",":
            i += 1
    return arms


def variant_key(pattern):
    """The Operation variant a match arm names, `_` for the final arm, `*` for Some(_) and `None`
    for the unknown operation number."""
    match = re.fullmatch(r"Some\(Operation::(\w+)\)", pattern)
    if match:
        return match.group(1)
    if pattern in ("_", "*", "Some(_)", "None"):
        return "_" if pattern == "_" else ("*" if pattern == "Some(_)" else "None")
    return pattern


def spec_called(expr):
    """The spec function an invoked arm calls, the last when it names more than one."""
    found = SPEC_CALL.findall(expr)
    return found[-1] if found else None


def invoke_calls(fn, index):
    """The pub fn methods the body of an invoke_* function calls on self, in order, each once."""
    ops = []
    for inner in SELF_CALL.findall(fn.body):
        target = index.get(inner)
        if target is not None and target.kind == "exec_pub":
            ops.append(inner)
    return list(dict.fromkeys(ops))


def owners_of(invokes):
    """For each pub fn the invoke_* bodies call, the invoke_* functions it is an operation of: those
    that call it and no other pub fn, when there is one, and otherwise every one that calls it.
    `invokes` maps each invoke_* name to the pub fn methods its body calls."""
    callers = {}
    for name, ops in invokes.items():
        for op in ops:
            callers.setdefault(op, []).append(name)
    owners = {}
    for op, names in callers.items():
        sole = [name for name in names if invokes[name] == [op]]
        owners[op] = set(sole or names)
    return owners


def operations_of(expr, index, owners):
    """The pub fn methods expr calls on self. An invoke_* call stands for the pub fn methods that
    function's body calls on self and is an operation of (`owners`), and is not itself an
    operation."""
    ops = []
    for name in SELF_CALL.findall(expr):
        fn = index.get(name)
        if fn is None:
            continue
        if name.startswith("invoke_") and fn.kind == "exec":
            ops.extend(op for op in invoke_calls(fn, index) if name in owners[op])
        elif fn.kind == "exec_pub":
            ops.append(name)
    return list(dict.fromkeys(ops))


def operation_match(fn, what):
    """The arms of fn's match on the operation number."""
    brace = find_operation_match(fn.body)
    if brace is None:
        raise Malformed(f"{fn.path}:{fn.name}: no match on the operation number, which {what} reads")
    return parse_arms(fn.body, brace)


def index_of(sources):
    """Each method of impl CapKernel in the sources, by name. `sources` is (path, masked text)
    pairs."""
    index = {}
    for path, text in sources:
        for fn in functions_in(text, path):
            if fn.name in index:
                raise Malformed(f"{fn.name} is a method of CapKernel twice, in {index[fn.name].path} and {fn.path}")
            index[fn.name] = fn
    if "invoked" not in index or "dispatch" not in index:
        raise Malformed("no fn invoked and fn dispatch on impl CapKernel")
    return index


def pairings(index):
    """Each arm of invoked as (spec function name, arm text, operations): the arms paired with an
    arm of dispatch by the Operation variant, then the wildcard arm with the operations of every
    arm of dispatch that invoked does not name. A pub fn the bodies of several invoke_* functions
    dispatch calls is an operation of each owner owners_of names."""
    invoked_arms = operation_match(index["invoked"], "the pairing")
    dispatch_arms = {variant_key(pattern): expr for pattern, expr in operation_match(index["dispatch"], "the operations")}
    invokes = {}
    for expr in dispatch_arms.values():
        for name in SELF_CALL.findall(expr):
            fn = index.get(name)
            if fn is not None and name.startswith("invoke_") and fn.kind == "exec":
                invokes[name] = invoke_calls(fn, index)
    owners = owners_of(invokes)
    groups = []
    wildcard = None
    used = set()
    for pattern, expr in invoked_arms:
        key = variant_key(pattern)
        if key == "_":
            wildcard = (spec_called(expr), expr)
        else:
            used.add(key)
            groups.append((spec_called(expr), expr, operations_of(dispatch_arms.get(key, ""), index, owners)))
    if wildcard is not None:
        spec, arm = wildcard
        ops = []
        for key, expr in dispatch_arms.items():
            if key not in used:
                ops.extend(operations_of(expr, index, owners))
        groups.append((spec, arm, list(dict.fromkeys(ops))))
    return groups


def lines_of(sources):
    """Each uncarried conjunct in the sources, as path:function:conjunct. `sources` is (path, masked
    text) pairs."""
    index = index_of(sources)
    lines = []
    for spec_name, arm, ops in pairings(index):
        spec = index.get(spec_name)
        spec_text = spec.full if spec is not None else ""
        for name in ops:
            fn = index.get(name)
            if fn is None or fn.kind != "exec_pub":
                continue
            for conjunct in split_conjuncts(fn.ensures):
                if not carried(conjunct, spec_text, arm):
                    lines.append(f"{fn.path}:{name}:{conjunct}")
    return lines


def source_files(root):
    """The Rust sources the check reads under root: kernel/verified when that tree is there, and
    never a throwaway module."""
    scan = root / "kernel" / "verified"
    if not scan.is_dir():
        scan = root
    files = []
    for path in sorted(scan.rglob("*.rs")):
        if "throwaway" in path.parts:
            continue
        files.append(path)
    return scan, files


def rel_path(path, root):
    """A source's path from the repository root, or from the root it was read under."""
    resolved = path.resolve()
    try:
        return resolved.relative_to(REPO.resolve()).as_posix()
    except ValueError:
        return resolved.relative_to(root.resolve()).as_posix()


def findings(root):
    """The uncarried conjuncts of the sources under root."""
    _, files = source_files(root)
    if not files:
        raise Malformed(f"no Rust sources under {root}")
    sources = [(rel_path(path, root), masked(path.read_text(encoding="utf-8"))) for path in files]
    return lines_of(sources)


def main(argv):
    if argv == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    root = REPO
    if len(argv) == 2 and argv[0] == "--root":
        root = Path(argv[1])
    elif argv:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    try:
        found = findings(root)
    except Malformed as error:
        print(f"check-invoked-arms: {error}", file=sys.stderr)
        return 1
    for line in found:
        print(line)
    return 1 if found else 0


CARRIED = """\
impl CapKernel {
    pub open spec fn spec_retyped(pre: Self, post: Self) -> bool {
        post == pre && Self::frame_retyped(pre, post) && pre.can_retype_frame(root) && Self::kept(pre, post)
    }
    pub open spec fn spec_outcome(&self) -> Outcome {
        self.holds_console(root)
    }
    pub open spec fn invoked(pre: Self, post: Self) -> bool {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Retype) => Self::spec_retyped(pre, post),
            _ => post == pre && out == pre.spec_outcome(),
        }
    }
    pub fn dispatch(&mut self) -> (ret: Option<Outcome>) {
        match operation(frame.operation_number()) {
            Some(Operation::Retype) => Some(self.invoke_retype()),
            Some(Operation::Print) => Some(self.print()),
            Some(_) => Some(status_only_outcome(STATUS_REFUSED)),
            None => Some(status_only_outcome(STATUS_UNKNOWN)),
        }
    }
    fn invoke_retype(&mut self) -> (ret: Outcome)
        ensures
            final(self).not_the_operation == old(self).not_the_operation,
    {
        self.retype_frame()
    }
    pub fn retype_frame(&mut self) -> (ret: bool)
        ensures
            final(steps).count <= old(steps).count + 1,
            final(self).wf(),
            old(self).wf(),
            *final(self) == *old(self),
            ret ==> Self::frame_retyped(old(self), final(self), root),
            ret == old(self).can_retype_frame(root),
            !(ret is Refused) ==> #[trigger] Self::kept(old(self), final(self)),
    {
        self.helper()
    }
    pub fn helper(&mut self) -> (ret: bool)
        ensures
            final(self).helper_field == old(self).helper_field,
    {
    }
    pub fn print(&mut self) -> (ret: bool)
        ensures
            final(steps).count <= old(steps).count + 1,
            *final(self) == *old(self),
            ret == self.holds_console(root),
    {
    }
    pub fn destroy(&mut self) -> (ret: bool)
        ensures
            final(self).destroyed == old(self).destroyed,
    {
    }
}
"""


SHARED = """\
impl CapKernel {
    pub open spec fn spec_registers_written(pre: Self, post: Self) -> bool {
        Self::frame_written(pre, post)
    }
    pub open spec fn spec_outcome(&self) -> Outcome {
        self.holds_console(root)
    }
    pub open spec fn invoked(pre: Self, post: Self) -> bool {
        match spec_operation(frame.operation_number()) {
            Some(Operation::WriteRegisters) => Self::spec_registers_written(pre, post),
            _ => post == pre && out == pre.spec_outcome(),
        }
    }
    pub fn dispatch(&mut self) -> (ret: Option<Outcome>) {
        match operation(frame.operation_number()) {
            Some(Operation::WriteRegisters) => Some(self.invoke_write_registers()),
            Some(Operation::ReadRegisters) => Some(self.invoke_read_registers()),
            None => Some(status_only_outcome(STATUS_UNKNOWN)),
        }
    }
    fn invoke_write_registers(&mut self) -> (ret: Outcome) {
        let current = self.read_registers();
        self.write_registers(current)
    }
    fn invoke_read_registers(&self) -> (ret: Outcome) {
        SECOND_BODY
    }
    pub fn read_registers(&self) -> (ret: Option<Registers>)
        ensures
            ret is Some ==> self.read_found(root),
    {
    }
    pub fn write_registers(&mut self, input: Registers) -> (ret: bool)
        ensures
            ret ==> Self::frame_written(*old(self), *final(self)),
    {
    }
    pub fn suspend(&mut self) -> (ret: bool)
        ensures
            *final(self) == *old(self),
    {
    }
}
"""


def dropped():
    """The carried fixture plus the field comparison the arm does not share."""
    return CARRIED.replace(
        "            final(self).wf(),\n",
        "            final(self).wf(),\n            final(self).flush_epoch == old(self).flush_epoch,\n",
        1,
    )


class Tests(unittest.TestCase):
    def lines(self, source):
        return lines_of([("op.rs", masked(source))])

    def test_a_fixture_that_meets_the_rule_has_no_conjunct(self):
        self.assertEqual(self.lines(CARRIED), [])

    def test_a_dropped_field_comparison_is_named(self):
        self.assertEqual(
            self.lines(dropped()),
            ["op.rs:retype_frame:final(self).flush_epoch == old(self).flush_epoch"],
        )

    def test_the_cli_exits_0_on_the_carried_fixture_and_names_the_dropped_field(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "op.rs").write_text(CARRIED, encoding="utf-8")
            self.assertEqual(findings(root), [])
            (root / "op.rs").write_text(dropped(), encoding="utf-8")
            self.assertEqual(
                findings(root),
                ["op.rs:retype_frame:final(self).flush_epoch == old(self).flush_epoch"],
            )

    def test_a_quantifier_binder_stays_one_conjunct_and_is_not_carried(self):
        source = CARRIED.replace(
            """            final(steps).count <= old(steps).count + 1,
            final(self).wf(),
            old(self).wf(),
            *final(self) == *old(self),
            ret ==> Self::frame_retyped(old(self), final(self), root),
            ret == old(self).can_retype_frame(root),
            !(ret is Refused) ==> #[trigger] Self::kept(old(self), final(self)),
""",
            "            forall|n: usize, g: usize| held(n, g),\n",
        )
        self.assertEqual(self.lines(source), ["op.rs:retype_frame:forall|n: usize, g: usize| held(n, g)"])

    def test_a_top_level_conjunction_splits_and_a_block_does_not(self):
        split = CARRIED.replace(
            """            final(steps).count <= old(steps).count + 1,
            final(self).wf(),
            old(self).wf(),
            *final(self) == *old(self),
            ret ==> Self::frame_retyped(old(self), final(self), root),
            ret == old(self).can_retype_frame(root),
            !(ret is Refused) ==> #[trigger] Self::kept(old(self), final(self)),
""",
            "            Self::frame_retyped(old(self), final(self)) &&& final(self).flush_epoch == old(self).flush_epoch,\n"
            "            ret is Some ==> {\n"
            "                &&& Self::inside(old(self))\n"
            "            },\n",
        )
        self.assertEqual(
            self.lines(split),
            [
                "op.rs:retype_frame:final(self).flush_epoch == old(self).flush_epoch",
                "op.rs:retype_frame:ret is Some ==> { &&& Self::inside(old(self)) }",
            ],
        )

    def test_a_conjunct_after_a_top_level_if_block_is_read(self):
        source = CARRIED.replace(
            "            ret == old(self).can_retype_frame(root),\n",
            "            ret ==> if old(self).acknowledged(root) {\n"
            "                Self::frame_retyped(old(self), final(self), root)\n"
            "            } else if old(self).pending(root) {\n"
            "                Self::kept(old(self), final(self))\n"
            "            } else {\n"
            "                Self::kept(old(self), final(self))\n"
            "            },\n"
            "            ret == old(self).can_retype_frame(root),\n"
            "            final(self).flush_epoch == old(self).flush_epoch,\n",
        )
        self.assertEqual(
            self.lines(source),
            [
                "op.rs:retype_frame:ret ==> if old(self).acknowledged(root) { "
                "Self::frame_retyped(old(self), final(self), root) } else if old(self).pending(root) "
                "{ Self::kept(old(self), final(self)) } else { Self::kept(old(self), final(self)) }",
                "op.rs:retype_frame:final(self).flush_epoch == old(self).flush_epoch",
            ],
        )

    def test_an_equality_is_not_carried_when_neither_side_says_post_equals_pre(self):
        source = CARRIED.replace(
            "post == pre && Self::frame_retyped(pre, post) && pre.can_retype_frame(root) && Self::kept(pre, post)",
            "Self::frame_retyped(pre, post) && pre.can_retype_frame(root) && Self::kept(pre, post)",
        )
        self.assertIn("op.rs:retype_frame:*final(self) == *old(self)", self.lines(source))
        self.assertNotIn("op.rs:print:*final(self) == *old(self)", self.lines(source))

    def test_two_calls_are_not_carried(self):
        source = CARRIED.replace(
            "            ret == old(self).can_retype_frame(root),\n",
            "            ret == old(self).can_retype_frame(root),\n"
            "            bound_threads(final(self)) == bound_threads(old(self)),\n",
        )
        self.assertIn(
            "op.rs:retype_frame:bound_threads(final(self)) == bound_threads(old(self))",
            self.lines(source),
        )

    def test_the_whole_kernel_unchanged_without_a_star_is_carried(self):
        source = CARRIED.replace(
            "            *final(self) == *old(self),\n",
            "            final(self) == old(self),\n",
        )
        self.assertEqual(self.lines(source), [])

    def test_a_pub_fn_shared_by_two_invoke_bodies_is_the_operation_of_the_one_that_calls_only_it(self):
        source = SHARED.replace("SECOND_BODY", "self.read_registers()")
        ops = {spec: ops for spec, _, ops in pairings(index_of([("op.rs", masked(source))]))}
        self.assertEqual(ops["spec_registers_written"], ["write_registers"])
        self.assertEqual(ops["spec_outcome"], ["read_registers"])
        self.assertEqual(
            self.lines(source),
            ["op.rs:read_registers:ret is Some ==> self.read_found(root)"],
        )

    def test_a_pub_fn_every_caller_calls_beside_another_stays_the_operation_of_each(self):
        source = SHARED.replace("SECOND_BODY", "self.read_registers(); self.suspend()")
        ops = {spec: ops for spec, _, ops in pairings(index_of([("op.rs", masked(source))]))}
        self.assertEqual(ops["spec_registers_written"], ["read_registers", "write_registers"])
        self.assertEqual(ops["spec_outcome"], ["read_registers", "suspend"])

    def test_the_script_is_not_a_gate_step(self):
        gate = (REPO / "tools" / "gate.py").read_text(encoding="utf-8")
        self.assertNotIn("check-invoked-arms", gate)
        self.assertNotIn("invoked arms", gate)

    def test_the_verified_sources_parse(self):
        try:
            found = findings(REPO)
        except Malformed as error:
            self.fail(str(error))
        for line in found:
            path, function, conjunct = line.split(":", 2)
            self.assertTrue(path.endswith(".rs"), line)
            self.assertTrue(function, line)
            self.assertTrue(conjunct, line)
            self.assertNotIn("final(self).wf()", conjunct)
            self.assertNotIn("old(self).wf()", conjunct)
            self.assertNotRegex(conjunct, r"\bsteps\b")


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
