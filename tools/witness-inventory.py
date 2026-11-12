#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""List every way each tier-1 operation succeeds, with the witness that reaches it or none.

A tier-1 component is bounded from below by a witness for each way each of its operations succeeds.
This prints what that asks for and what the tree holds, read from the source and from no list kept
by hand. design/witness-per-way-an-operation-succeeds/, points 1 to 4.

The operations. Of kernel/verified/capability: every exec function that `dispatch` of
`impl CapKernel`, or an `invoke_` function it calls, calls on `self`, the wired operations; and
every other exec `pub fn` of `impl CapKernel` that takes `&mut self`. Of aheap, aeager and adivider:
every exec `pub fn`, and every exec function of a trait the crate implements for a struct or enum it
declares, which another crate can call as it can a `pub fn`. A `pub(crate)` or private function is a
step and is not listed. A file named `witness.rs`, a `witness` or `throwaway` directory and a
function named `witness_` hold no operation.

The ways, from the operation's result type:

  an enum the component declares   each variant but `Refused`       claimed by `x is V`
  bool                             true                             claimed by `x`
  Option<T>                        Some                             claimed by `x is Some`
  Outcome                          STATUS_OK, STATUS_AGAIN          claimed by `x.status == STATUS_OK`
  anything else                    returns                          a call at the top level of the body

The witnesses are the root witnesses tools/check-throwaways.py finds, by its rule. A root witness
reaches a way of operation P when a conjunct of its ensures claims the way over a component of the
value it returns, `ret`, `ret.2`, and that component of the function's last expression is a call of
P, or a name every binding of which in the body, each `let` and each assignment, is a call of P. So
`let mut step = self.p(..); while step is Again { step = self.p(..); }` ending in `step` counts for
p, and a literal, `a && b`, a parameter or a name bound from two operations counts for nothing. A
component that is a call of another `witness_` function, or a name whose one binding is such a call,
destructured or not, is followed into that function when its own ensures claims the same way of that
component. The way `returns` is reached by a statement at the top level of the root witness's own
body that is the call, binds it or assigns it, or by the body's last expression being the call.

A call is `self.p(..)`, `p(..)` or `T::p(..)`, or `x.p(..)` where `x` is a parameter whose type is
`T`, `&T` or `&mut T`, or a name every binding of which is a `let` annotated `T` or a call of a
function that returns `Self` or `T`. In a user crate a claim may be guarded, `g ==> x is V`, by what
the crate's environment answered, and the guard is printed after the witness for a reviewer to
judge; in the kernel a guarded claim counts for nothing. A way of a wired operation also asks for a
proof function named `lemma_entry_reaches_<operation>`: without it the way is none, and the line
says so and names the witnesses that claim it.

An exec `pub fn` of acall whose body calls `step` is a wrapper, the entry seen from user space and
no second operation. It is one line: the call number it passes and the operations `dispatch`'s arm
for that number calls, or none when the arm calls none.

Output, tab-separated, one line per operation and way, then one per wrapper, then the count:

  <path>  <operation>  <way>  <witness>[, <witness>...] | none  [<note>]
  <path>  <wrapper>    <OPERATION_X>=<number>  <operation>[, <operation>...] | none
  witness inventory: <n> of <m> lines are none

Exits 0 with the listing, 1 when a source file cannot be read as the rules above need, naming it.
Holding the lines that are none to a list is the gate's, not this script's.

usage: tools/witness-inventory.py           the listing
       tools/witness-inventory.py --test    this script's own tests
"""
import importlib.util
import re
import sys
import unittest
from collections import namedtuple
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent

KERNEL_CRATE = "kernel/verified"
KERNEL = "kernel/verified/capability"
KERNEL_TYPE = "CapKernel"
ENTRY = "dispatch"
ENTRY_PROOF = "lemma_entry_reaches_"
USERS = ("aheap/src", "aeager/src", "adivider/src")
CALLS = "acall/src"
RETURNS = "returns"

TOKEN = re.compile(r"[A-Za-z_]\w*|\d\w*|<==>|==>|&&&|\|\|\||&&|\|\||==|!=|<=|>=|->|=>|::|[-+*/%^&|]=|\S")
WORD = re.compile(r"[A-Za-z_]\w*\Z")
CHARACTER = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F_]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'")
RAW_STRING = re.compile(r'\br(#*)"')
OPEN = {"(": ")", "[": "]", "{": "}"}
CLOSERS = set(OPEN.values())
CLAUSES = {"requires", "ensures", "decreases", "recommends", "opens_invariants", "no_unwind", "returns", "where", "via",
           "when", "default_ensures"}
# A word that is no operand: a `|` after one opens a closure's parameters.
NOT_OPERAND = {"forall", "exists", "choose", "return", "in", "if", "else", "match", "while", "let", "mut", "move", "as",
               "implies", "by", "is", "invariant"} | CLAUSES
# What a `{` follows when it opens a block inside an expression and not the body the clauses end at.
BEFORE_A_BLOCK = {"==>", "<==>", "&&&", "|||", "&&", "||", "==", "!=", "<=", ">=", "=>", "=", "|", "+", "-", "*", "/", "%",
                  "!", "implies", "else"}
# What a statement follows.
STARTS = {";", "{", "}", "=>"}
COMPOUND = {"+=", "-=", "*=", "/=", "%=", "^=", "&=", "|="}

Row = namedtuple("Row", "path operation way witness note")
Claim = namedtuple("Claim", "path way guard")
# A binding of a name: `simple` binds the whole value of `rhs`, `tuple` its component `index`, and
# `other` is any binding this script does not follow.
Binding = namedtuple("Binding", "kind rhs index annotation")
OTHER = Binding("other", None, None, None)


class Unreadable(Exception):
    """A source file this script cannot read as its rules need; its message names it."""


def load(name):
    """A sibling script as a module."""
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), Path(__file__).resolve().parent / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


throwaways = load("check-throwaways")


def blank(text):
    """The text with the inside of every comment, string and character literal blanked, each character
    in its place."""
    out, i, n = list(text), 0, len(text)
    while i < n:
        raw = RAW_STRING.match(text, i) if text[i] == "r" else None
        if text.startswith("//", i):
            start, end = i, text.find("\n", i)
            end = n if end < 0 else end
        elif text.startswith("/*", i):
            start, end = i, text.find("*/", i)
            end = n if end < 0 else end + 2
        elif raw:
            start, end = raw.end(), text.find('"' + raw.group(1), raw.end())
            end = n if end < 0 else end
        elif text[i] == '"':
            start = end = i + 1
            while end < n and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
        elif text[i] == "'" and CHARACTER.match(text, i):
            start, end = i + 1, CHARACTER.match(text, i).end() - 1
        else:
            i += 1
            continue
        for j in range(start, min(end, n)):
            if out[j] != "\n":
                out[j] = " "
        i = end + 1
    return "".join(out)


class Source:
    """A file as tokens: `tok` the tokens, `at` each one's offset, `mate` each opening bracket's closer."""

    def __init__(self, path, text):
        self.path, self.text, self.tok, self.at, self.mate = path, text, [], [], {}
        for match in TOKEN.finditer(blank(text)):
            self.tok.append(match.group())
            self.at.append(match.start())
        stack = []
        for i, token in enumerate(self.tok):
            if token in OPEN:
                stack.append(i)
            elif token in CLOSERS:
                if not stack or OPEN[self.tok[stack[-1]]] != token:
                    raise Unreadable(f"{path}: line {self.line(i)}: a {token} that closes nothing")
                self.mate[stack.pop()] = i
        if stack:
            raise Unreadable(f"{path}: line {self.line(stack[-1])}: an unclosed {self.tok[stack[-1]]}")

    def line(self, i):
        return self.text.count("\n", 0, self.at[i]) + 1


class Fn:
    """A function as the source gives it. `owner` is the type of the impl block it is in, `trait`
    whether that block implements a trait, `params`, `ret` and `body` token ranges, `clauses` each
    clause's range by its word."""

    def __init__(self, **fields):
        self.__dict__.update(fields)

    def result(self):
        return self.src.tok[self.ret[0]:self.ret[1]] if self.ret else []


def operand(token):
    return token in (")", "]", "}", "@", "?") or (token[0].isalnum() or token[0] == "_") and token not in NOT_OPERAND


def top(src, a, b):
    """The indices in [a, b) outside every bracket opened in it and every closure's parameter list. An
    opening bracket is given; what it encloses and its closer are not."""
    i = a
    while i < b:
        token = src.tok[i]
        if token == "|" and (i == a or not operand(src.tok[i - 1])):
            i += 1
            while i < b and src.tok[i] != "|":
                i = src.mate[i] + 1 if src.tok[i] in OPEN else i + 1
            i += 1
            continue
        yield i
        i = src.mate[i] + 1 if token in OPEN else i + 1


def split(src, a, b):
    """The ranges [a, b) falls into at its own commas, the empty ones dropped."""
    parts, start = [], a
    for i in top(src, a, b):
        if src.tok[i] == ",":
            parts.append((start, i))
            start = i + 1
    parts.append((start, b))
    return [(s, e) for s, e in parts if s < e]


def first(src, a, b, wanted):
    """The first index top() gives in [a, b) whose token is in `wanted`, or None."""
    return next((i for i in top(src, a, b) if src.tok[i] in wanted), None)


def body_brace(src, a, b):
    """The `{` in [a, b) that opens the body clauses end at: the first outside every bracket that
    neither an `if` or a `match` before it is waiting for nor an operator precedes."""
    pending = 0
    for i in top(src, a, b):
        token = src.tok[i]
        if token in ("if", "match"):
            pending += 1
        elif token == "{":
            if pending:
                pending -= 1
            elif src.tok[i - 1] not in BEFORE_A_BLOCK:
                return i
    return None


def value_end(src, a, b):
    """Where the expression that starts at `a` ends: its own `;` or `,`, or the closer of what holds it."""
    return next((i for i in top(src, a, b) if src.tok[i] in (";", ",") or src.tok[i] in CLOSERS), b)


def angles(tokens, i):
    """The index after the `<...>` that opens at tokens[i]."""
    depth = 0
    while i < len(tokens):
        depth += (tokens[i] == "<") - (tokens[i] == ">")
        i += 1
        if depth == 0:
            break
    return i


def impl_header(tokens):
    """(the type an impl block is of, whether it implements a trait) from the tokens between `impl` and `{`."""
    tokens = tokens[angles(tokens, 0):] if tokens and tokens[0] == "<" else tokens
    depth, target = 0, tokens
    for i, token in enumerate(tokens):
        depth += (token == "<") - (token == ">")
        if token == "for" and depth == 0:
            target = tokens[i + 1:]
    name = None
    for token in target:
        if token in ("<", "where"):
            break
        if WORD.match(token) and token not in ("mut", "dyn"):
            name = token
    return name, target is not tokens


def function(src, i, end, quals, owner, trait):
    """The function whose `fn` is at `i`, and the index after it."""
    tok, mate = src.tok, src.mate
    name = tok[i + 1]
    where = f"{src.path}: line {src.line(i)}: fn {name}"
    j = angles(tok, i + 2) if tok[i + 2] == "<" else i + 2
    if tok[j] != "(":
        raise Unreadable(f"{where}: no parameter list")
    params, j = (j + 1, mate[j]), mate[j] + 1
    ret_name = ret = None
    if j < end and tok[j] == "->":
        j += 1
        k = j + 1 + (tok[j + 1] in ("tracked", "ghost"))
        if tok[j] == "(" and WORD.match(tok[k]) and tok[k + 1] == ":":
            ret_name, ret, j = tok[k], (k + 2, mate[j]), mate[j] + 1
        else:
            stop = first(src, j, end, CLAUSES | {"{", ";"})
            ret, j = (j, end if stop is None else stop), end if stop is None else stop
    clauses, word, start, pending, body, stop = {}, None, j, 0, None, None
    for k in top(src, j, end):
        token = tok[k]
        if token == ";":
            stop = k
            break
        if token in CLAUSES:
            if word:
                clauses[word] = (start, k)
            word, start, pending = token, k + 1, 0
        elif token in ("if", "match"):
            pending += 1
        elif token == "{":
            if pending:
                pending -= 1
            elif tok[k - 1] not in BEFORE_A_BLOCK:
                body, stop = (k + 1, mate[k]), k
                break
    if stop is None:
        raise Unreadable(f"{where}: neither a body nor a `;`")
    if word:
        clauses[word] = (start, stop)
    after = mate[stop] + 1 if body else stop + 1
    if after < end and not (WORD.match(tok[after]) or tok[after] == "#"):
        raise Unreadable(f"{where}: a `{{` in its clauses reads as its body; put the expression in parentheses")
    pieces = split(src, *params)
    first_piece = tok[pieces[0][0]:pieces[0][1]] if pieces else []
    receiver = " ".join(first_piece).replace("& ", "&") if "self" in first_piece and ":" not in first_piece else None
    return Fn(src=src, name=name, owner=owner, trait=trait, line=src.line(i),
              vis="pub" if "pub" in quals else "restricted" if "restricted" in quals else "",
              mode="spec" if "spec" in quals else "proof" if "proof" in quals else "exec",
              params=params, receiver=receiver, ret_name=ret_name, ret=ret, clauses=clauses, body=body), after


class Component:
    """The functions, enums and types of some source files, as {path: text}."""

    def __init__(self, texts):
        self.sources = [Source(path, text) for path, text in sorted(texts.items())]
        self.fns, self.enums, self.types = [], {}, set()
        for src in self.sources:
            self.block(src, 0, len(src.tok), None, False)
        self.declared = set(self.types)
        self.types |= {fn.owner for fn in self.fns if fn.owner}
        self.by_key = {}
        for fn in self.fns:
            if fn.mode == "exec":
                self.by_key.setdefault((fn.owner, fn.name), []).append(fn)

    def block(self, src, i, end, owner, trait):
        """Read the items in [i, end), which are in an impl block of `owner` when it is not None."""
        tok, mate, quals = src.tok, src.mate, []
        while i < end:
            token = tok[i]
            following = tok[i + 1] if i + 1 < end else ""
            if token == "#" and tok[i + 1 + (following == "!")] == "[":
                i = mate[i + 1 + (following == "!")] + 1
            elif token == "assume_specification":
                at = first(src, i + 1, end, {";"})
                if at is None:
                    raise Unreadable(f"{src.path}: line {src.line(i)}: `{token}` with no `;`")
                i, quals = at + 1, []
            elif token in ("requires", "ensures"):
                raise Unreadable(f"{src.path}: line {src.line(i)}: `{token}` outside a function")
            elif token == "pub":
                quals.append("restricted" if following == "(" else "pub")
                i = mate[i + 1] + 1 if following == "(" else i + 1
            elif token == "fn" and WORD.match(following) and tok[i + 2] in ("<", "("):
                fn, i = function(src, i, end, quals, owner, trait)
                self.fns.append(fn)
                quals = []
            elif token == "impl" or (token == "verus" and following == "!") or (
                    token in ("mod", "trait", "enum", "struct", "union") and WORD.match(following)):
                at = first(src, i + 1, end, {"{", ";"})
                if at is None:
                    raise Unreadable(f"{src.path}: line {src.line(i)}: `{token}` with neither a block nor a `;`")
                if token in ("enum", "struct", "union"):
                    self.types.add(following)
                if tok[at] == "{" and token == "impl":
                    self.block(src, at + 1, mate[at], *impl_header(tok[i + 1:at]))
                elif tok[at] == "{" and token in ("verus", "mod"):
                    self.block(src, at + 1, mate[at], None, False)
                elif tok[at] == "{" and token == "enum":
                    self.enums[following] = [variant(src, s) for s, _ in split(src, at + 1, mate[at])]
                i = (mate[at] if tok[at] == "{" else at) + 1
                quals = []
            elif token in OPEN:
                i = mate[i] + 1
                quals = [] if token == "{" else quals
            else:
                if token == ";":
                    quals = []
                elif WORD.match(token):
                    quals.append(token)
                i += 1


def variant(src, i):
    """The name of the enum variant whose declaration starts at `i`, past its attributes."""
    while src.tok[i] == "#":
        i = src.mate[i + 1] + 1
    return src.tok[i]


def ways(fn, comp):
    """The ways the function succeeds, from its result type."""
    result = fn.result()
    if result == ["bool"]:
        return ["true"]
    if result[:2] == ["Option", "<"]:
        return ["Some"]
    name = result[-1] if result and all(WORD.match(token) or token == "::" for token in result) else None
    if name == "Outcome":
        return ["STATUS_OK", "STATUS_AGAIN"]
    if name in comp.enums:
        return [each for each in comp.enums[name] if each != "Refused"]
    return [RETURNS]


def claims(fn):
    """The claims of a way among the conjuncts of the function's ensures."""
    src, found = fn.src, []
    if "ensures" not in fn.clauses or fn.ret_name is None:
        return found
    for s, e in split(src, *fn.clauses["ensures"]):
        guard, arrow = None, first(src, s, e, {"==>"})
        if arrow is not None:
            guard, s = " ".join(src.text[src.at[s]:src.at[arrow]].split()), arrow + 1
        rest = src.tok[s:e]
        if not rest or rest[0] != fn.ret_name:
            continue
        i, path = 1, []
        while i + 1 < len(rest) and rest[i] == "." and rest[i + 1].isdigit():
            path.append(int(rest[i + 1]))
            i += 2
        rest = rest[i:]
        if not rest:
            found.append(Claim(tuple(path), "true", guard))
        elif len(rest) == 2 and rest[0] == "is":
            found.append(Claim(tuple(path), rest[1], guard))
        elif len(rest) == 4 and rest[:3] == [".", "status", "=="]:
            found.append(Claim(tuple(path), rest[3], guard))
    return found


def binding(src, name, i, stop, end, conditional):
    """What the `let` at `i`, whose pattern ends at `stop`, binds `name` by, or None when it does not."""
    tok, j = src.tok, i + 1
    colon = first(src, j, stop, {":"})
    pattern = tok[j:stop if colon is None else colon]
    if name not in pattern:
        return None
    if conditional or pattern[0] in ("ghost", "tracked") or tok[stop] != "=":
        return OTHER
    rhs = (stop + 1, value_end(src, stop + 1, end))
    if [token for token in pattern if token != "mut"] == [name]:
        return Binding("simple", rhs, None, None if colon is None else tok[colon + 1:stop])
    if pattern[0] == "(" and src.mate[j] == j + len(pattern) - 1:
        for index, (s, e) in enumerate(split(src, j + 1, src.mate[j])):
            if [token for token in tok[s:e] if token != "mut"] == [name]:
                return Binding("tuple", rhs, index, None)
    return OTHER


def bindings(fn, name):
    """Every binding of the name in the function's body: each `let` and each assignment."""
    src, (a, b) = fn.src, fn.body
    tok, found = src.tok, []
    for i in range(a, b):
        token, start = tok[i], i == a or tok[i - 1] in STARTS
        if token == "let":
            stop = next((k for k in top(src, i + 1, b) if tok[k] in ("=", ";") or tok[k] in CLOSERS), b)
            found.append(binding(src, name, i, stop, b, tok[i - 1] in ("if", "while", "&&")))
        elif token == "for":
            stop = first(src, i + 1, b, {"in"})
            found.append(OTHER if name in tok[i + 1:b if stop is None else stop] else None)
        elif start and token == name and tok[i + 1] == "=":
            found.append(Binding("simple", (i + 2, value_end(src, i + 2, b)), None, None))
        elif start and token == name and tok[i + 1] in COMPOUND:
            found.append(OTHER)
        elif start and token == "(" and tok[src.mate[i] + 1] == "=" and name in tok[i:src.mate[i]]:
            found.append(OTHER)
    return [each for each in found if each is not None]


def type_of(comp, fn, name, seen):
    """The struct or enum of the component that the name is a value of in the function, or None."""
    if (fn, name) in seen:
        return None
    seen = seen | {(fn, name)}
    tok = fn.src.tok
    for s, e in split(fn.src, *fn.params):
        piece = tok[s:e]
        if ":" in piece and [token for token in piece[:piece.index(":")] if token != "mut"] == [name]:
            kind = [token for token in piece[piece.index(":") + 1:] if token not in ("&", "mut")]
            return kind[0] if len(kind) == 1 and kind[0] in comp.types else None
    kinds = set()
    for bound in bindings(fn, name):
        if bound.kind != "simple":
            return None
        if bound.annotation is not None:
            kind = bound.annotation[0] if len(bound.annotation) == 1 else None
        else:
            target = callee(comp, fn, *bound.rhs, seen)
            result = target.result() if target else []
            kind = target.owner if result == ["Self"] else result[0] if len(result) == 1 else None
        if kind not in comp.types:
            return None
        kinds.add(kind)
    return kinds.pop() if len(kinds) == 1 else None


def callee(comp, fn, a, b, seen=frozenset()):
    """The exec function of the component that tokens [a, b) of the function's body are one call of,
    or None."""
    tok, mate = fn.src.tok, fn.src.mate
    last = None
    for last in top(fn.src, a, b):
        pass
    if last is None or tok[last] != "(" or mate[last] != b - 1:
        return None
    head = tok[a:last]
    if head and head[-1] == ">" and "<" in head:
        head = head[:len(head) - 1 - head[::-1].index("<")]
        head = head[:-1] if head and head[-1] == "::" else head
    if not head or not WORD.match(head[-1]):
        return None
    if len(head) == 1:
        owner = None
    elif len(head) == 3 and head[1] == "." and WORD.match(head[0]):
        owner = fn.owner if head[0] == "self" else type_of(comp, fn, head[0], seen)
        if owner is None:
            return None
    elif head[-2] == "::" and all(WORD.match(token) or token == "::" for token in head):
        owner = fn.owner if head[-3] == "Self" else head[-3] if head[-3] in comp.types else None
    else:
        return None
    found = comp.by_key.get((owner, head[-1]), [])
    return found[0] if len(found) == 1 else None


def statements(src, a, b):
    """The statements of the block [a, b) as (start, end, kind): `closed` by a `;`, a `block` that ends
    at its brace, or `open`, the block's last expression."""
    tok, mate, found, i = src.tok, src.mate, [], a
    while i < b:
        token, brace, end = tok[i], None, None
        if token == ";":
            i += 1
            continue
        if token == "if":
            brace = first(src, i + 1, b, {"{"})
            while brace is not None and mate[brace] + 1 < b and tok[mate[brace] + 1] == "else":
                brace = first(src, mate[brace] + 2, b, {"{"})
        elif token in ("while", "for", "loop"):
            brace = body_brace(src, i + 1, b)
        elif token == "match":
            brace = first(src, i + 1, b, {"{"})
        elif token == "{" or (i + 1 < b and tok[i + 1] == "{" and token in ("proof", "unsafe")):
            brace = i if token == "{" else i + 1
        elif i + 2 < b and tok[i + 1] == "!" and tok[i + 2] == "{":
            brace = i + 2
        if brace is not None:
            found.append((i, mate[brace] + 1, "block"))
            i = mate[brace] + 1
            continue
        kind, end = "open", b
        for k in top(src, i, b):
            if tok[k] == ";":
                kind, end = "closed", k
                break
            if tok[k] == "by" and token in ("assert", "assume") and k + 1 < b and tok[k + 1] == "{":
                kind, end = "block", mate[k + 1] + 1
                break
        found.append((i, end, kind))
        i = end
    return found


def resolve(comp, fn, path, way, seen):
    """The function a claim of `way` over component `path` of what `fn` returns is tied to, or None."""
    if fn in seen or fn.body is None:
        return None
    src, body = fn.src, statements(fn.src, *fn.body)
    tok, mate, path = src.tok, src.mate, list(path)
    if not body or body[-1][2] != "open":
        return None
    a, b = body[-1][:2]
    while tok[a] == "(" and mate[a] == b - 1:
        parts = split(src, a + 1, b - 1)
        if len(parts) == 1 and tok[b - 2] != ",":
            a, b = parts[0]
        elif path and path[0] < len(parts):
            a, b = parts[path.pop(0)]
        else:
            return None
    target = callee(comp, fn, a, b)
    if target is None and b - a == 1 and WORD.match(tok[a]):
        if any(tok[e - 1] == tok[a] or tok[s:s + 2] == [tok[a], ":"] for s, e in split(src, *fn.params)):
            return None
        bound = bindings(fn, tok[a])
        targets = [callee(comp, fn, *each.rhs) if each.kind != "other" else None for each in bound]
        if not bound or None in targets:
            return None
        if all(each.kind == "simple" for each in bound) and len(set(targets)) == 1 and not witness(targets[0]):
            return None if path else targets[0]
        if len(bound) != 1 or not witness(targets[0]):
            return None
        target, path = targets[0], ([bound[0].index] if bound[0].kind == "tuple" else []) + path
    if target is None:
        return None
    if not witness(target):
        return None if path else target
    if not any(claim == Claim(tuple(path), way, None) for claim in claims(target)):
        return None
    return resolve(comp, target, path, way, seen | {fn})


def witness(fn):
    return fn.name.startswith("witness_")


def hidden(fn):
    """Whether the function is in what holds no operation: a witness module, or a witness itself."""
    path = Path(fn.src.path)
    return witness(fn) or path.stem == "witness" or "witness" in path.parts[:-1]


def reached(comp, roots, operations, guards):
    """{(operation, way): each root witness that reaches it, with its guard}."""
    found = {}
    for root in roots:
        src, hits = root.src, set()
        for claim in claims(root):
            if claim.way == RETURNS or (claim.guard and not guards):
                continue
            target = resolve(comp, root, claim.path, claim.way, frozenset())
            if target in operations and claim.way in ways(target, comp):
                hits.add((target, claim.way, claim.guard))
        for s, e, kind in statements(src, *root.body):
            if kind == "block":
                continue
            if src.tok[s] == "let" and src.tok[s + 1] not in ("ghost", "tracked"):
                equals = first(src, s, e, {"="})
                s = e if equals is None else equals + 1
            elif WORD.match(src.tok[s]) and s + 1 < e and src.tok[s + 1] == "=":
                s += 2
            target = callee(comp, root, s, e)
            if target in operations and ways(target, comp) == [RETURNS]:
                hits.add((target, RETURNS, None))
        for target, way, guard in hits:
            found.setdefault((target, way), []).append(root.name + (f" if {guard}" if guard else ""))
    return found


def root_witnesses(comp, texts, declared):
    """The root witnesses among the component's functions, by the rule of tools/check-throwaways.py."""
    names = set()
    try:
        for path, text in texts.items():
            for each in throwaways.witnesses(text, path):
                if throwaways.not_root(each, declared) is None:
                    names.add((path, "witness_" + each.name))
    except throwaways.Malformed as error:
        raise Unreadable(str(error)) from None
    roots = [fn for fn in comp.fns if (fn.src.path, fn.name) in names and fn.mode == "exec" and fn.body is not None]
    unread = sorted(names - {(fn.src.path, fn.name) for fn in roots})
    if unread:
        raise Unreadable("; ".join(f"{path}: the root witness {name} is not read as an exec function with a body"
                                   for path, name in unread))
    return roots


def declared_in(texts):
    """The structs and enums the files declare, as tools/check-throwaways.py reads them."""
    return {name for text in texts.values() for name in throwaways.DECLARED.findall(throwaways.masked(text))}


def rows_of(comp, operations, roots, guards, wired, display):
    found = reached(comp, roots, set(operations), guards)
    proofs = {fn.name for fn in comp.fns if fn.mode == "proof"}
    rows = []
    for fn in operations:
        for way in ways(fn, comp):
            witnesses, note = ", ".join(sorted(found.get((fn, way), []))), ""
            if fn.name in wired and ENTRY_PROOF + fn.name not in proofs:
                note = f"no {ENTRY_PROOF}{fn.name}" + (f"; claimed by {witnesses}" if witnesses else "")
                witnesses = ""
            rows.append(Row(fn.src.path, display(fn), way, witnesses or None, note))
    return rows


def called(methods, fn, a, b, seen=frozenset()):
    """The methods that tokens [a, b) of the function call on `self`, an `invoke_` one replaced by
    what it calls, each once and in order."""
    tok, names = fn.src.tok, []
    for i in range(a, b - 3):
        name = tok[i + 2]
        if tok[i] != "self" or tok[i + 1] != "." or tok[i + 3] != "(" or name not in methods:
            continue
        inner = methods[name]
        if not name.startswith("invoke_"):
            names.append(name)
        elif name not in seen and inner.body is not None:
            names += called(methods, inner, *inner.body, seen | {name})
    return list(dict.fromkeys(names))


def entry(comp):
    """(the exec methods of the kernel's type by name, the entry among them)."""
    methods = {fn.name: fn for fn in comp.fns if fn.owner == KERNEL_TYPE and not fn.trait and fn.mode == "exec"}
    if ENTRY not in methods or methods[ENTRY].body is None:
        raise Unreadable(f"no {ENTRY} in an impl {KERNEL_TYPE} under {KERNEL}")
    return methods, methods[ENTRY]


def kernel_rows(texts, declared=None):
    """A line per way of each operation of the kernel component, whose files are {path: text}.
    `declared` is the structs and enums of its whole crate, when that is more than these files."""
    comp = Component(texts)
    methods, dispatch = entry(comp)
    wired = set(called(methods, dispatch, *dispatch.body))
    operations = [fn for fn in comp.fns
                  if fn.owner == KERNEL_TYPE and not fn.trait and fn.mode == "exec" and not hidden(fn)
                  and (fn.name in wired or (fn.vis == "pub" and fn.receiver == "&mut self"))]
    roots = root_witnesses(comp, texts, declared_in(texts) if declared is None else declared)
    return rows_of(comp, operations, roots, False, wired, lambda fn: fn.name)


def user_rows(texts):
    """A line per way of each operation of a user crate, whose files are {path: text}."""
    comp = Component(texts)
    operations = [fn for fn in comp.fns if fn.mode == "exec" and not hidden(fn)
                  and (fn.owner in comp.declared if fn.trait else fn.vis == "pub")]
    roots = root_witnesses(comp, texts, declared_in(texts))
    return rows_of(comp, operations, roots, True, (), lambda fn: f"{fn.owner}::{fn.name}" if fn.owner else fn.name)


def wrapper_rows(kernel_texts, texts):
    """A line per wrapper among the files {path: text}, read against the kernel component's entry."""
    comp, wrappers = Component(kernel_texts), Component(texts)
    methods, dispatch = entry(comp)
    numbers, variants, arms = {}, {}, {}
    for src in comp.sources + wrappers.sources:
        tok = src.tok
        for i in range(len(tok) - 6):
            if tok[i] == "const" and tok[i + 1].startswith("OPERATION_"):
                equals = first(src, i, len(tok), {"=", ";"})
                numbers[tok[i + 1]] = tok[equals + 1]
            elif tok[i].startswith("OPERATION_") and tok[i + 1:i + 6] == ["=>", "Some", "(", "Operation", "::"]:
                variants[tok[i]] = tok[i + 6]
    tok, (a, b) = dispatch.src.tok, dispatch.body
    for i in range(a, b - 7):
        if tok[i:i + 4] == ["Some", "(", "Operation", "::"] and tok[i + 5:i + 7] == [")", "=>"]:
            end = dispatch.src.mate[i + 7] + 1 if tok[i + 7] == "{" else value_end(dispatch.src, i + 7, b)
            arms[tok[i + 4]] = called(methods, dispatch, i + 7, end)
    rows = []
    for fn in wrappers.fns:
        if fn.vis != "pub" or fn.mode != "exec" or fn.body is None:
            continue
        src, passed = fn.src, []
        for i in range(*fn.body):
            if src.tok[i] == "step" and src.tok[i + 1] == "(" and src.tok[i - 1] not in (".", "::", "fn"):
                arguments = split(src, i + 2, src.mate[i + 1])
                if len(arguments) > 1 and arguments[1][1] - arguments[1][0] == 1:
                    passed.append(src.tok[arguments[1][0]])
        for number in dict.fromkeys(passed):
            operations = ", ".join(arms.get(variants.get(number), []))
            rows.append(Row(src.path, fn.name, f"{number}={numbers.get(number, '?')}", operations or None, ""))
    return rows


def read(root, directory):
    """The Rust files under a directory of the tree, outside its throwaway modules, as {path: text}."""
    base = root / directory
    return {str(path.relative_to(root)): path.read_text(encoding="utf-8") for path in sorted(base.rglob("*.rs"))
            if throwaways.THROWAWAY not in path.relative_to(base).parts}


def tree_rows(root):
    """Every line of the tree's inventory."""
    kernel_texts = read(root, KERNEL)
    rows = kernel_rows(kernel_texts, declared_in(read(root, KERNEL_CRATE)))
    for directory in USERS:
        rows += user_rows(read(root, directory))
    return rows + wrapper_rows(kernel_texts, read(root, CALLS))


def listing(rows):
    out = ["\t".join((row.path, row.operation, row.way, row.witness or "none") + ((row.note,) if row.note else ()))
           for row in rows]
    none = sum(row.witness is None for row in rows)
    return "\n".join(out + [f"witness inventory: {none} of {len(rows)} lines are none"]) + "\n"


def main(args):
    if args:
        sys.exit(__doc__.split("usage: ")[1].join(("usage: ", "")).rstrip())
    try:
        rows = tree_rows(REPO)
    except Unreadable as error:
        print(f"witness inventory: {error}", file=sys.stderr)
        return 1
    print(listing(rows), end="")
    return 0



BOOTED = """
        requires
            old(self).booted(root@, process),
"""


def kernel(witnesses="", operations="", arms="", extra=""):
    """A kernel component of two files: the operations, with `dispatch`, and the witnesses."""
    model = f"""
verus! {{
pub enum Step {{ Refused, Again, Done }}
pub enum Other {{ Refused, Made }}
pub struct Outcome {{ pub status: u64 }}
pub const OPERATION_MOVE: u64 = 3;
pub const OPERATION_NAP: u64 = 9;
pub fn operation(number: u64) -> Option<Operation> {{
    match number {{
        OPERATION_MOVE => Some(Operation::Move),
        OPERATION_NAP => Some(Operation::Nap),
        _ => None,
    }}
}}
impl CapKernel {{
    pub fn dispatch(&mut self, c: usize, frame: Registers) -> (ret: Option<Outcome>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            ret is Some ==> {{
                &&& final(self).wf()
            }},
    {{
        match operation(frame.number()) {{
            Some(Operation::Move) => Some(self.invoke_move(frame)),
            Some(Operation::Nap) => Some(refused()),
            {arms}
            Some(_) => Some(refused()),
            None => None,
        }}
    }}
    fn invoke_move(&mut self, frame: Registers) -> (ret: Outcome) {{
        let done = self.move_cap(frame.a(), frame.b());
        refused()
    }}
    pub fn move_cap(&mut self, from: usize, to: usize) -> (ret: bool)
        ensures
            ret == old(self).can_move(from, to),
    {{
        true
    }}
    pub fn retype(&mut self, base: usize) -> (ret: Step)
        ensures
            forall|c: int| 0 <= c < 4 ==> {{
                &&& final(self).wf()
            }},
        decreases base,
    {{
        Step::Done
    }}
    pub fn make(&mut self) -> (ret: Other) {{ Other::Made }}
    pub fn find(&mut self, at: usize) -> (ret: Option<usize>) {{ None }}
    pub fn answer(&mut self) -> (ret: Outcome) {{ refused() }}
    pub fn load(&mut self, core: usize) {{ }}
    pub fn look(&self) -> (ret: bool) {{ true }}
    pub(crate) fn step_of_retype(&mut self) -> (ret: bool) {{ true }}
    fn private_step(&mut self) -> (ret: bool) {{ true }}
    pub open spec fn can_move(&self, from: usize, to: usize) -> bool {{ true }}
    pub proof fn lemma_about(&mut self) {{ }}
    {operations}
}}
{extra}
}}
"""
    witness = f"""
verus! {{
impl CapKernel {{
    {witnesses}
}}
}}
"""
    return {"kernel/verified/capability/model.rs": model, "kernel/verified/capability/witness.rs": witness}


def lines(rows):
    """Rows as {(operation, way): witness or None}."""
    return {(row.operation, row.way): row.witness for row in rows}


class Ways(unittest.TestCase):
    def test_each_result_type_gives_its_ways(self):
        rows = kernel_rows(kernel())
        self.assertEqual(
            [(row.operation, row.way) for row in rows],
            [("dispatch", "Some"), ("move_cap", "true"), ("retype", "Again"), ("retype", "Done"), ("make", "Made"),
             ("find", "Some"), ("answer", "STATUS_OK"), ("answer", "STATUS_AGAIN"), ("load", "returns")])
        self.assertTrue(all(row.path == "kernel/verified/capability/model.rs" for row in rows))

    def test_a_restricted_or_private_function_is_not_listed(self):
        names = {row.operation for row in kernel_rows(kernel())}
        self.assertNotIn("step_of_retype", names)
        self.assertNotIn("private_step", names)

    def test_only_an_exec_function_taking_mut_self_is_listed_unless_it_is_wired(self):
        names = {row.operation for row in kernel_rows(kernel())}
        self.assertFalse(names & {"look", "can_move", "lemma_about", "invoke_move"})
        wired = kernel(operations="fn peek(&self) -> (ret: Outcome) { refused() }",
                       arms="Some(Operation::Peek) => match position(frame.a()) { Some(at) => Some(self.peek()), None => None },")
        self.assertIn(("peek", "STATUS_OK"), lines(kernel_rows(wired)))

    def test_a_witness_module_holds_no_operation(self):
        rows = kernel_rows(kernel(witnesses="pub fn helper(&mut self) -> (ret: bool) { true }"))
        self.assertNotIn("helper", {row.operation for row in rows})


class Claims(unittest.TestCase):
    def witnessed(self, witnesses, **more):
        return lines(kernel_rows(kernel(witnesses=witnesses, **more)))

    def test_a_claimed_way_names_its_witness_and_the_other_way_stays_none(self):
        found = self.witnessed(f"""
    pub fn witness_done(&mut self, root: Ghost<usize>, process: usize) -> (ret: Step){BOOTED}
        ensures
            ret is Done,
    {{
        let step = self.retype(4096);
        step
    }}""")
        self.assertEqual(found[("retype", "Done")], "witness_done")
        self.assertIsNone(found[("retype", "Again")])

    def test_a_witness_that_reaches_only_a_refusal_counts_for_nothing(self):
        found = self.witnessed(f"""
    pub fn witness_refused(&mut self, root: Ghost<usize>, process: usize) -> (ret: Step){BOOTED}
        ensures
            ret is Refused,
    {{
        let step = self.retype(1);
        step
    }}""")
        self.assertIsNone(found[("retype", "Done")])
        self.assertIsNone(found[("retype", "Again")])

    def test_an_operation_no_witness_calls_is_none(self):
        self.assertIsNone(self.witnessed("")[("make", "Made")])

    def test_a_name_bound_from_two_operations_counts_for_nothing(self):
        found = self.witnessed(f"""
    pub fn witness_two(&mut self, root: Ghost<usize>, process: usize) -> (ret: Option<usize>){BOOTED}
        ensures
            ret is Some,
    {{
        let mut at = self.find(1);
        if at is None {{
            at = self.other_find(2);
        }}
        at
    }}""", operations="pub fn other_find(&mut self, at: usize) -> (ret: Option<usize>) { Some(at) }")
        self.assertIsNone(found[("find", "Some")])
        self.assertIsNone(found[("other_find", "Some")])

    def test_a_literal_or_a_conjunction_counts_for_nothing(self):
        found = self.witnessed(f"""
    pub fn witness_literal(&mut self, root: Ghost<usize>, process: usize) -> (ret: (Step, bool)){BOOTED}
        ensures
            ret.0 is Done,
            ret.1,
    {{
        let step = self.retype(4096);
        let a = self.move_cap(1, 2);
        let b = self.move_cap(2, 3);
        (Step::Done, a && b)
    }}""")
        self.assertIsNone(found[("retype", "Done")])
        self.assertIsNone(found[("move_cap", "true")])

    def test_a_parameter_or_a_ghost_binding_counts_for_nothing(self):
        found = self.witnessed(f"""
    pub fn witness_given(&mut self, root: Ghost<usize>, process: usize, given: bool) -> (ret: (bool, bool)){BOOTED}
            given,
        ensures
            ret.0,
            ret.1,
    {{
        let moved = self.move_cap(1, 2);
        let (moved, other) = (true, 1);
        (given, moved)
    }}""")
        self.assertIsNone(found[("move_cap", "true")])

    def test_a_witness_that_does_not_start_from_booted_counts_for_nothing(self):
        for requires in ("\n        requires\n            old(self).wf(),",
                         BOOTED + "            old(self).spaces.len() == 1,"):
            found = self.witnessed(f"""
    pub fn witness_done(&mut self, root: Ghost<usize>, process: usize) -> (ret: Step){requires}
        ensures
            ret is Done,
    {{
        let step = self.retype(4096);
        step
    }}""")
            self.assertIsNone(found[("retype", "Done")])

    def test_a_private_witness_is_no_root(self):
        found = self.witnessed(f"""
    fn witness_done(&mut self, root: Ghost<usize>, process: usize) -> (ret: Step){BOOTED}
        ensures
            ret is Done,
    {{
        self.retype(4096)
    }}""")
        self.assertIsNone(found[("retype", "Done")])

    def test_a_loop_that_rebinds_the_name_by_the_same_operation_counts(self):
        found = self.witnessed(f"""
    pub fn witness_loop(&mut self, root: Ghost<usize>, process: usize) -> (ret: (bool, Step)){BOOTED}
        ensures
            final(self).wf(),
            ret.1 is Done,
    {{
        let ok = true;
        let mut step = self.retype(4096);
        while step is Again
            invariant
                self.wf(),
                step is Again ==> {{
                    &&& self.wf()
                }},
            decreases self.left(),
        {{
            step = self.retype(4096);
        }}
        (ok, step)
    }}""")
        self.assertEqual(found[("retype", "Done")], "witness_loop")
        self.assertIsNone(found[("retype", "Again")])

    def test_the_last_expression_may_be_the_call(self):
        found = self.witnessed(f"""
    pub fn witness_direct(&mut self, root: Ghost<usize>, process: usize) -> (ret: Other){BOOTED}
        ensures
            ret is Made,
    {{
        proof {{
            assert(self.wf());
        }}
        self.make()
    }}""")
        self.assertEqual(found[("make", "Made")], "witness_direct")

    def test_a_claim_of_a_way_the_operation_has_not_counts_for_nothing(self):
        found = self.witnessed(f"""
    pub fn witness_wrong(&mut self, root: Ghost<usize>, process: usize) -> (ret: Step){BOOTED}
        ensures
            ret is Made,
    {{
        self.retype(4096)
    }}""")
        self.assertEqual(set(found.values()), {None})

    def test_an_outcome_is_claimed_by_its_status(self):
        found = self.witnessed(f"""
    pub fn witness_answer(&mut self, root: Ghost<usize>, process: usize) -> (ret: Outcome){BOOTED}
        ensures
            ret.status == STATUS_OK,
    {{
        let out = self.answer();
        out
    }}""")
        self.assertEqual(found[("answer", "STATUS_OK")], "witness_answer")
        self.assertIsNone(found[("answer", "STATUS_AGAIN")])

    def test_two_witnesses_of_one_way_are_both_named(self):
        one = f"""
    pub fn witness_%s(&mut self, root: Ghost<usize>, process: usize) -> (ret: Other){BOOTED}
        ensures
            ret is Made,
    {{
        self.make()
    }}"""
        self.assertEqual(self.witnessed(one % "b" + one % "a")[("make", "Made")], "witness_a, witness_b")

    def test_a_guarded_claim_counts_for_nothing_in_the_kernel(self):
        found = self.witnessed(f"""
    pub fn witness_guarded(&mut self, root: Ghost<usize>, process: usize, lucky: bool) -> (ret: Other){BOOTED}
        ensures
            lucky ==> ret is Made,
    {{
        self.make()
    }}""")
        self.assertIsNone(found[("make", "Made")])


class Followed(unittest.TestCase):
    ROOT = f"""
    pub fn witness_root(&mut self, root: Ghost<usize>, process: usize) -> (ret: (bool, Step)){BOOTED}
        ensures
            ret.1 is Done,
    {{
        let ok = self.move_cap(1, 2);
        let (step, mid) = self.witness_helper(4096);
        (ok, step)
    }}"""

    def helper(self, ensures, tail):
        return f"""
    fn witness_helper(&mut self, base: usize) -> (ret: (Step, Ghost<CapKernel>))
        requires
            old(self).wf(),
        ensures
            {ensures}
    {{
        let step = self.retype(base);
        {tail}
    }}"""

    def test_a_destructured_call_of_a_witness_is_followed_into_it(self):
        found = lines(kernel_rows(kernel(witnesses=self.ROOT + self.helper("ret.0 is Done,", "(step, Ghost(*self))"))))
        self.assertEqual(found[("retype", "Done")], "witness_root")

    def test_the_helper_must_claim_the_same_way_of_that_component(self):
        for ensures in ("final(self).wf(),", "ret.0 is Again,", "ret.1 is Done,"):
            found = lines(kernel_rows(kernel(witnesses=self.ROOT + self.helper(ensures, "(step, Ghost(*self))"))))
            self.assertIsNone(found[("retype", "Done")])

    def test_the_helper_s_component_must_be_a_call_too(self):
        found = lines(kernel_rows(kernel(witnesses=self.ROOT + self.helper("ret.0 is Done,", "(Step::Done, Ghost(*self))"))))
        self.assertIsNone(found[("retype", "Done")])

    def test_a_helper_s_claim_no_root_repeats_is_not_counted(self):
        root = self.ROOT.replace("ret.1 is Done,", "final(self).wf(),")
        found = lines(kernel_rows(kernel(witnesses=root + self.helper("ret.0 is Done,", "(step, Ghost(*self))"))))
        self.assertIsNone(found[("retype", "Done")])

    def test_a_witness_that_calls_itself_ends(self):
        found = lines(kernel_rows(kernel(witnesses=f"""
    pub fn witness_again(&mut self, root: Ghost<usize>, process: usize) -> (ret: Step){BOOTED}
        ensures
            ret is Done,
    {{
        self.witness_again(root, process)
    }}""")))
        self.assertIsNone(found[("retype", "Done")])


class Returns(unittest.TestCase):
    def witnessed(self, body):
        return lines(kernel_rows(kernel(witnesses=f"""
    pub fn witness_load(&mut self, root: Ghost<usize>, process: usize){BOOTED}
        ensures
            final(self).wf(),
    {{
        {body}
    }}""")))[("load", "returns")]

    def test_a_call_at_the_top_level_of_the_body_reaches_it(self):
        self.assertEqual(self.witnessed("let ghost s0 = *self;\n self.load(0);"), "witness_load")
        self.assertEqual(self.witnessed("let got = self.load(0);"), "witness_load")
        self.assertEqual(self.witnessed("assert(true) by { }\n self.load(0)"), "witness_load")

    def test_a_call_inside_a_branch_or_an_argument_does_not(self):
        self.assertIsNone(self.witnessed("if process > 0 { self.load(0); }"))
        self.assertIsNone(self.witnessed("self.keep(self.load(0));"))
        self.assertIsNone(self.witnessed("proof { self.load(0); }"))


class Wired(unittest.TestCase):
    WITNESS = f"""
    pub fn witness_move(&mut self, root: Ghost<usize>, process: usize) -> (ret: bool){BOOTED}
        ensures
            ret,
    {{
        let done = self.move_cap(1, 2);
        done
    }}"""

    def test_a_wired_operation_with_a_witness_and_no_entry_proof_is_none(self):
        row = [row for row in kernel_rows(kernel(witnesses=self.WITNESS)) if row.operation == "move_cap"][0]
        self.assertIsNone(row.witness)
        self.assertEqual(row.note, "no lemma_entry_reaches_move_cap; claimed by witness_move")

    def test_with_the_entry_proof_it_is_witnessed(self):
        proof = "pub proof fn lemma_entry_reaches_move_cap(s: CapKernel) ensures true, { }"
        row = [row for row in kernel_rows(kernel(witnesses=self.WITNESS, extra=proof)) if row.operation == "move_cap"][0]
        self.assertEqual((row.witness, row.note), ("witness_move", ""))

    def test_an_exec_function_of_that_name_is_no_proof(self):
        fake = "pub fn lemma_entry_reaches_move_cap(s: CapKernel) { }"
        row = [row for row in kernel_rows(kernel(witnesses=self.WITNESS, extra=fake)) if row.operation == "move_cap"][0]
        self.assertIsNone(row.witness)

    def test_an_unwired_operation_asks_for_no_entry_proof(self):
        row = [row for row in kernel_rows(kernel()) if row.operation == "make"][0]
        self.assertEqual((row.witness, row.note), (None, ""))

    def test_a_kernel_without_dispatch_is_unreadable(self):
        texts = kernel()
        texts = {path: text.replace("dispatch", "dispatcher") for path, text in texts.items()}
        with self.assertRaisesRegex(Unreadable, "no dispatch"):
            kernel_rows(texts)


USER = """
verus! {
pub enum Cut { Refused, Whole, Half }
pub struct Heap { n: usize }
pub struct Slab { n: usize }
pub struct Refusal;
impl Heap {
    pub fn new(spares: usize) -> (r: Self) { Heap { n: spares } }
    pub fn alloc<S: SpanSource>(&mut self, src: &mut S, size: usize) -> (r: Option<usize>) { None }
    pub fn cut(&mut self) -> (r: Cut) { Cut::Whole }
    pub fn try_run(&mut self) -> (r: Result<usize, Refusal>) { Err(Refusal) }
    pub(crate) fn alloc_part(&mut self) -> (r: Option<usize>) { None }
    fn find(&self) -> (r: bool) { true }
    pub open spec fn wf(&self) -> bool { true }
}
impl Slab {
    pub fn new(spares: usize) -> (r: Slab) { Slab { n: spares } }
    pub fn alloc(&mut self) -> (r: Option<usize>) { None }
}
impl SpanSource for Heap {
    fn reserve(&mut self, blocks: usize) -> (r: Option<usize>) { None }
    proof fn lemma_reserve(&self) { }
}
impl Clone for Foreign {
    fn clone(&self) -> Self { Foreign }
}
pub trait SpanSource {
    fn reserve(&mut self, blocks: usize) -> (r: Option<usize>);
}
pub fn fits(size: usize) -> (r: bool) { size < 10 }
fn inner(size: usize) -> (r: bool) { true }
#[cfg(test)]
mod tests {
    fn fits_passes() { }
}
}
"""


def user(witnesses):
    return {"aheap/src/heap.rs": USER, "aheap/src/witness.rs": "verus! {\n" + witnesses + "\n}\n"}


class UserCrate(unittest.TestCase):
    def test_the_operations_are_the_public_exec_functions_and_a_declared_type_s_trait_functions(self):
        self.assertEqual(
            [(row.path, row.operation, row.way) for row in user_rows(user(""))],
            [("aheap/src/heap.rs", name, way) for name, way in (
                ("Heap::new", "returns"), ("Heap::alloc", "Some"), ("Heap::cut", "Whole"), ("Heap::cut", "Half"),
                ("Heap::try_run", "returns"), ("Slab::new", "returns"), ("Slab::alloc", "Some"),
                ("Heap::reserve", "Some"), ("fits", "true"))])

    def test_a_method_call_counts_for_the_type_its_receiver_was_made_as(self):
        found = lines(user_rows(user("""
pub fn witness_heap<S: SpanSource>(src: &mut S) -> (r: (Option<usize>, bool))
    requires
        old(src).wf(),
    ensures
        r.0 is Some,
        r.1,
{
    let mut heap = Heap::new(0);
    let got = heap.alloc(src, 8);
    let ok = fits(8);
    (got, ok)
}""")))
        self.assertEqual(found[("Heap::alloc", "Some")], "witness_heap")
        self.assertIsNone(found[("Slab::alloc", "Some")])
        self.assertEqual(found[("fits", "true")], "witness_heap")
        self.assertEqual(found[("Heap::new", "returns")], "witness_heap")
        self.assertIsNone(found[("Slab::new", "returns")])

    def test_a_receiver_of_no_known_type_counts_for_nothing(self):
        found = lines(user_rows(user("""
pub fn witness_heap<S: SpanSource>(src: &mut S) -> (r: Option<usize>)
    ensures
        r is Some,
{
    let mut heap = if true { Heap::new(0) } else { Heap::new(1) };
    heap.alloc(src, 8)
}""")))
        self.assertIsNone(found[("Heap::alloc", "Some")])

    def test_an_annotated_receiver_and_a_path_call_count(self):
        found = lines(user_rows(user("""
pub fn witness_slab() -> (r: (Option<usize>, Cut))
    ensures
        r.0 is Some,
        r.1 is Half,
{
    let mut slab: Slab = make();
    let mut heap = Heap::new(0);
    (slab.alloc(), Heap::cut(&mut heap))
}""")))
        self.assertEqual(found[("Slab::alloc", "Some")], "witness_slab")
        self.assertEqual(found[("Heap::cut", "Half")], "witness_slab")
        self.assertIsNone(found[("Heap::cut", "Whole")])

    def test_a_guard_is_printed_beside_the_witness(self):
        found = lines(user_rows(user("""
pub fn witness_heap<S: SpanSource>(src: &mut S) -> (r: Option<usize>)
    ensures
        final(src)@.refusals  ==  old(src)@.refusals ==> r is Some,
{
    let mut heap = Heap::new(0);
    heap.alloc(src, 8)
}""")))
        self.assertEqual(found[("Heap::alloc", "Some")], "witness_heap if final(src)@.refusals == old(src)@.refusals")

    def test_a_witness_taking_a_value_the_crate_declares_is_no_root(self):
        found = lines(user_rows(user("""
pub fn witness_heap(heap: &mut Heap) -> (r: Cut)
    ensures
        r is Whole,
{
    heap.cut()
}""")))
        self.assertIsNone(found[("Heap::cut", "Whole")])

    def test_a_trait_function_is_reached_through_its_type(self):
        found = lines(user_rows(user("""
pub fn witness_reserve() -> (r: Option<usize>)
    ensures
        r is Some,
{
    let mut heap = Heap::new(0);
    let got = heap.reserve(1);
    got
}""")))
        self.assertEqual(found[("Heap::reserve", "Some")], "witness_reserve")


WRAPPERS = {"acall/src/capability.rs": """
verus! {
pub fn move_cap(caller: &mut Tracked<Caller>, from: u64, to: u64) -> (ok: bool)
    ensures
        ok ==> final(caller)@.moved(from, to),
    no_unwind
{
    let out = step(caller, OPERATION_MOVE, from, to, 0, 0, 0, 0);
    out.status == STATUS_OK
}
pub fn nap(caller: &mut Tracked<Caller>) -> (ok: bool) {
    let out = step(caller, OPERATION_NAP, 0, 0, 0, 0, 0, 0);
    out.status == STATUS_OK
}
pub fn dream(caller: &mut Tracked<Caller>) -> (ok: bool) {
    let out = step(caller, OPERATION_DREAM, 0, 0, 0, 0, 0, 0);
    out.status == STATUS_OK
}
pub fn both(caller: &mut Tracked<Caller>) -> (ok: bool) {
    move_cap(caller, 1, 2)
}
pub open spec fn carries(frame: Registers) -> bool { true }
#[verifier::external_body]
pub fn step(caller: &mut Tracked<Caller>, number: u64, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> (out: Outcome) {
    unimplemented!()
}
}
"""}


class Wrappers(unittest.TestCase):
    def test_a_wrapper_is_one_line_with_its_number_and_what_the_arm_calls(self):
        self.assertEqual(
            wrapper_rows(kernel(), WRAPPERS),
            [Row("acall/src/capability.rs", "move_cap", "OPERATION_MOVE=3", "move_cap", ""),
             Row("acall/src/capability.rs", "nap", "OPERATION_NAP=9", None, ""),
             Row("acall/src/capability.rs", "dream", "OPERATION_DREAM=?", None, "")])


class Reading(unittest.TestCase):
    def test_comments_strings_and_characters_hide_nothing_and_add_nothing(self):
        texts = kernel(operations="""
    // pub fn commented(&mut self) { }
    /* pub fn blocked(&mut self) { } */
    pub fn brace(&mut self) -> (ret: bool) { let c = '{'; let s = "pub fn quoted(&mut self) { "; true }
    pub fn after(&mut self) -> (ret: bool) { true }""")
        names = [row.operation for row in kernel_rows(texts)]
        self.assertEqual(names[-2:], ["brace", "after"])
        self.assertFalse(set(names) & {"commented", "blocked", "quoted"})

    def test_an_unclosed_bracket_is_unreadable(self):
        with self.assertRaisesRegex(Unreadable, "model.rs"):
            kernel_rows({"kernel/verified/capability/model.rs": "verus! { impl CapKernel { pub fn dispatch(&mut self) { }"})

    def test_a_clause_outside_a_function_is_unreadable(self):
        texts = kernel(operations="pub fn odd(&mut self) -> (ret: bool) ensures ret == Pair { a: 1 }, { true }")
        with self.assertRaisesRegex(Unreadable, "model.rs"):
            kernel_rows(texts)

    def test_an_assumed_specification_is_no_function_and_no_stray_clause(self):
        texts = kernel(extra="""
pub assume_specification[translates](kernel: Ghost<CapKernel>, page: Ghost<usize>)
    requires
        premises(kernel@, page@),
    ensures
        translated(page@),
    no_unwind;
pub assume_specification<T>[Cell::<T>::take](cell: &mut Cell<T>) -> (ret: T)
    ensures
        ret == Pair { a: 1 }.a,
;""")
        self.assertEqual(kernel_rows(texts), kernel_rows(kernel()))

    def test_the_listing_ends_with_the_count_of_none(self):
        rows = [Row("a.rs", "f", "true", "witness_f", ""), Row("a.rs", "g", "Some", None, "no lemma_entry_reaches_g"),
                Row("w.rs", "wrap", "OPERATION_X=1", None, "")]
        self.assertEqual(listing(rows), "a.rs\tf\ttrue\twitness_f\n"
                                        "a.rs\tg\tSome\tnone\tno lemma_entry_reaches_g\n"
                                        "w.rs\twrap\tOPERATION_X=1\tnone\n"
                                        "witness inventory: 2 of 3 lines are none\n")

    def test_the_tree_is_readable(self):
        rows = tree_rows(REPO)
        self.assertTrue(any(row.operation == "dispatch" for row in rows))


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
