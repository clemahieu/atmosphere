#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Check the license of every package in the dependency graph against tools/license-allowlist.

The allowlist is the only place the allowed set lives (CLAUDE.md, License). A package's license
field is an SPDX expression: OR needs one allowed alternative, AND needs every operand, AND binds
tighter than OR, WITH binds an exception to one id, and '/' is an old spelling of OR. A workspace
member without a license field is covered by the tree's LICENSE. A dependency without one needs a
'package <name> <source> <expression>' entry matching its name and its source at any revision,
whose expression itself passes. Checking the workspace's own graph, an entry that matches no
package fails: it could look like a verified license for a package that is not there.

usage: tools/check-licenses.py                         (the workspace's graph)
       tools/check-licenses.py --manifest-path PATH     (that manifest's graph)
       tools/check-licenses.py --test                   (this script's own tests)
"""
import json
import subprocess
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
ALLOWLIST_PATH = "tools/license-allowlist"


class Unreadable(Exception):
    """An allowlist line or a license expression that does not parse."""


def quoted(text):
    return "None" if text is None else json.dumps(text)


def unrevised(source):
    """A package's source without its revision; a path dependency has none."""
    return (source or "a path").split("#")[0]


class Allowlist:
    def __init__(self, text):
        self.licenses = set()
        # Packages without a license field: (name, source without its revision, verified license).
        self.packages = []
        for line in (line.strip() for line in text.splitlines()):
            if not line or line.startswith("#"):
                continue
            fields = line.split()
            if len(fields) == 2 and fields[0] == "license":
                self.licenses.add(fields[1])
            elif len(fields) >= 4 and fields[0] == "package":
                self.packages.append((fields[1], fields[2], " ".join(fields[3:])))
            else:
                raise Unreadable(f"cannot read {quoted(line)}")
        for name, _, expression in self.packages:
            if not self.allows(expression):
                raise Unreadable(f"{name} names {expression}, which is not allowed")

    def unmatched_entries(self, graph):
        """The package entries naming nothing in `graph`, a list of (name, source)."""
        return [
            f"{name} {source}"
            for name, source, _ in self.packages
            if not any(name == other and source == unrevised(other_source) for other, other_source in graph)
        ]

    def check(self, name, source, license, member):
        """The reason one package fails, or None when it passes."""
        if license is not None:
            try:
                allowed = self.allows(license)
            except Unreadable as error:
                return str(error)
            return None if allowed else f"{license} is not allowed"
        if member:
            return None
        if any(entry[0] == name and entry[1] == unrevised(source) for entry in self.packages):
            return None
        return f"no license field and no entry for {unrevised(source)}"

    def allows(self, expression):
        spaced = expression.replace("(", " ( ").replace(")", " ) ").replace("/", " OR ")
        parser = Expression(spaced.split(), self.licenses)
        allowed = parser.any()
        if parser.peek() is not None:
            raise Unreadable(f"cannot read {quoted(expression)} at {quoted(parser.peek())}")
        return allowed


class Expression:
    """A recursive descent over an SPDX expression. AND binds tighter than OR; WITH binds to one id."""

    OPERATORS = ("AND", "OR", "WITH", "(", ")")

    def __init__(self, tokens, licenses):
        self.tokens = tokens
        self.next = 0
        self.licenses = licenses

    def peek(self):
        return self.tokens[self.next] if self.next < len(self.tokens) else None

    def eat(self, token):
        found = self.peek() == token
        if found:
            self.next += 1
        return found

    def any(self):
        allowed = self.every()
        while self.eat("OR"):
            # Both sides are parsed, so a malformed right side is an error even after an allowed left.
            allowed = self.every() or allowed
        return allowed

    def every(self):
        allowed = self.term()
        while self.eat("AND"):
            allowed = self.term() and allowed
        return allowed

    def term(self):
        if self.eat("("):
            allowed = self.any()
            if not self.eat(")"):
                raise Unreadable("an unclosed parenthesis")
            return allowed
        allowed = self.id() in self.licenses
        if self.eat("WITH"):
            self.id()
        return allowed

    def id(self):
        token = self.peek()
        if token is None or token in self.OPERATORS:
            raise Unreadable(f"expected a license at {quoted(token)}")
        self.next += 1
        return token


def metadata(manifest):
    output = subprocess.run(
        ["cargo", "metadata", "--locked", "--format-version", "1", "--manifest-path", str(manifest)],
        cwd=REPO,
        stdout=subprocess.PIPE,
        stdin=subprocess.DEVNULL,
        check=True,
    ).stdout
    return json.loads(output)


def failures(allowlist, graph, stale):
    """Each package's failure, then, when `stale`, each entry that names nothing in the graph."""
    members = set(graph["workspace_members"])
    found = []
    for package in graph["packages"]:
        reason = allowlist.check(package["name"], package["source"], package["license"], package["id"] in members)
        if reason is not None:
            found.append(f"{package['name']} {package['version']}: {reason}")
    if stale:
        pairs = [(package["name"], package["source"]) for package in graph["packages"]]
        for entry in allowlist.unmatched_entries(pairs):
            found.append(f"{ALLOWLIST_PATH}: the entry for {entry} matches no package in the graph")
    return found


def main(args):
    workspace = REPO / "Cargo.toml"
    if args[:1] == ["--manifest-path"] and len(args) == 2:
        manifest = Path(args[1]).resolve()
    elif not args:
        manifest = workspace
    else:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    try:
        allowlist = Allowlist((REPO / ALLOWLIST_PATH).read_text(encoding="utf-8"))
    except Unreadable as error:
        print(f"{ALLOWLIST_PATH}: {error}", file=sys.stderr)
        return 1
    graph = metadata(manifest)
    # Another manifest's graph is smaller than the workspace's, so only the workspace can show an
    # entry is stale.
    found = failures(allowlist, graph, manifest == workspace)
    for failure in found:
        print(failure, file=sys.stderr)
    if found:
        return 1
    print(f"{len(graph['packages'])} packages within the allowlist")
    return 0


class Tests(unittest.TestCase):
    def allowlist(self):
        return Allowlist(
            "# comment\n\nlicense MIT\nlicense Apache-2.0\nlicense Unicode-3.0\n"
            "package vstd git+https://example.org/verus?branch=mars MIT\n"
        )

    def allows(self, expression):
        return self.allowlist().allows(expression)

    def test_an_entry_must_match_a_package(self):
        source = "git+https://example.org/verus?branch=mars"
        self.assertEqual(self.allowlist().unmatched_entries([("vstd", source + "#abc")]), [])
        other_source = [("vstd", "git+https://example.org/other#abc")]
        self.assertEqual(self.allowlist().unmatched_entries(other_source), ["vstd " + source])
        self.assertEqual(self.allowlist().unmatched_entries([]), ["vstd " + source])

    def test_single_license(self):
        self.assertTrue(self.allows("MIT"))
        self.assertFalse(self.allows("GPL-3.0"))

    def test_or_needs_one_alternative(self):
        self.assertTrue(self.allows("MIT OR GPL-3.0"))
        self.assertFalse(self.allows("GPL-3.0 OR LGPL-2.1"))

    def test_slash_is_or(self):
        self.assertTrue(self.allows("GPL-3.0/MIT"))
        self.assertFalse(self.allows("GPL-3.0/LGPL-2.1"))

    def test_and_needs_every_operand(self):
        self.assertTrue(self.allows("(MIT OR Apache-2.0) AND Unicode-3.0"))
        self.assertFalse(self.allows("MIT AND GPL-3.0"))

    def test_and_binds_tighter_than_or(self):
        self.assertTrue(self.allows("GPL-3.0 AND LGPL-2.1 OR MIT"))
        self.assertTrue(self.allows("MIT OR GPL-3.0 AND LGPL-2.1"))
        self.assertFalse(self.allows("GPL-3.0 OR MIT AND LGPL-2.1"))

    def test_with_follows_its_base(self):
        self.assertTrue(self.allows("Apache-2.0 WITH LLVM-exception"))
        self.assertFalse(self.allows("GPL-2.0 WITH Classpath-exception-2.0"))

    def test_unknown_strings_are_errors(self):
        # An expression that does not parse must fail, not read as allowed or merely as not allowed.
        for expression in ["see the file", "MIT or Apache-2.0", "MIT OR", "(MIT", "MIT)", "", "WITH MIT"]:
            with self.subTest(expression=expression), self.assertRaises(Unreadable):
                self.allows(expression)

    def test_package_with_a_field_is_judged_by_it(self):
        allowlist = self.allowlist()
        self.assertIsNone(allowlist.check("a", "registry+x", "MIT", False))
        self.assertIsNotNone(allowlist.check("a", "registry+x", "GPL-3.0", False))
        self.assertIsNotNone(allowlist.check("a", None, "GPL-3.0", True))

    def test_workspace_member_without_a_field_passes(self):
        self.assertIsNone(self.allowlist().check("a", None, None, True))

    def test_dependency_without_a_field_fails_without_an_entry(self):
        allowlist = self.allowlist()
        self.assertIsNotNone(allowlist.check("a", "registry+x", None, False))
        self.assertIsNotNone(allowlist.check("a", None, None, False))

    def test_entry_must_match_name_and_source_at_any_revision(self):
        allowlist = self.allowlist()
        source = "git+https://example.org/verus?branch=mars#abc123"
        self.assertIsNone(allowlist.check("vstd", source, None, False))
        self.assertIsNotNone(allowlist.check("other", source, None, False))
        self.assertIsNotNone(allowlist.check("vstd", "git+https://example.org/fork#abc123", None, False))

    def test_an_unreadable_field_fails_the_package(self):
        self.assertIsNotNone(self.allowlist().check("a", "registry+x", "see the file", False))

    def test_entry_must_name_an_allowed_license(self):
        with self.assertRaises(Unreadable):
            Allowlist("license MIT\npackage a b GPL-3.0\n")

    def test_malformed_allowlist_is_an_error(self):
        for text in ["licence MIT\n", "license\n", "package a b\n"]:
            with self.subTest(text=text), self.assertRaises(Unreadable):
                Allowlist(text)

    def test_failures_name_each_package_and_stale_entry(self):
        graph = {
            "workspace_members": ["own"],
            "packages": [
                {"id": "own", "name": "own", "version": "0.1.0", "source": None, "license": None},
                {"id": "gpl", "name": "gpl", "version": "1.0.0", "source": "registry+x", "license": "GPL-3.0"},
                {"id": "mit", "name": "mit", "version": "2.0.0", "source": "registry+x", "license": "MIT"},
            ],
        }
        stale = f"{ALLOWLIST_PATH}: the entry for vstd git+https://example.org/verus?branch=mars matches no package in the graph"
        self.assertEqual(failures(self.allowlist(), graph, True), ["gpl 1.0.0: GPL-3.0 is not allowed", stale])
        self.assertEqual(failures(self.allowlist(), graph, False), ["gpl 1.0.0: GPL-3.0 is not allowed"])


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
