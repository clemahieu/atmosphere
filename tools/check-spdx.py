#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Check that every source file in the tree states its license where a reader of that file alone
finds it (CLAUDE.md, License; design/license-stated-in-every-source-file/).

A source is a file git would take, not a symbolic link, whose name ends in one of SUFFIXES or
whose first line starts with '#!'. Its first line, or its second under a '#!' line, is a comment holding nothing but
'SPDX-License-Identifier: ' and an SPDX expression, which tools/license-allowlist must pass as it
passes a package's, read by tools/check-licenses.py. Every other file is under the tree's LICENSE.

usage: tools/check-spdx.py           (the tree)
       tools/check-spdx.py --test    (this script's own tests)
"""
import importlib.util
import re
import subprocess
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
SUFFIXES = (".rs", ".py", ".sh", ".c", ".h", ".S")
SHEBANG = b"#!"
# The tag as a line comment of Rust or C, of Python or shell, or as a C block comment.
TAG = re.compile(r"(?://|#|/\*) SPDX-License-Identifier: (.+?)(?: \*/)?")
# Fewer sources than this means the scan looked in the wrong place.
LEAST_SOURCES = 100

_spec = importlib.util.spec_from_file_location("check_licenses", Path(__file__).with_name("check-licenses.py"))
check_licenses = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_licenses)


def is_source(path, content):
    return path.endswith(SUFFIXES) or content.startswith(SHEBANG)


def stated(content):
    """The expression a source's tag line holds, or None when that line is not a tag."""
    lines = content.split(b"\n", 2)
    at = 1 if lines[0].startswith(SHEBANG) else 0
    match = TAG.fullmatch(lines[at].decode(errors="replace")) if at < len(lines) else None
    return match and match.group(1)


def scan(repo, paths, allowlist):
    """Of the files at paths: how many are sources, how many of them state each expression the
    allowlist passes, and each other source's failure as 'path: reason'."""
    sources, counts, found = 0, Counter(), []
    for path in sorted(paths):
        content = (repo / path).read_bytes()
        if not is_source(path, content):
            continue
        sources += 1
        expression = stated(content)
        if expression is None:
            line = "second line, under its #! line" if content.startswith(SHEBANG) else "first line"
            found.append(f"{path}: no 'SPDX-License-Identifier: <expression>' comment as its {line}")
            continue
        try:
            allowed = allowlist.allows(expression)
        except check_licenses.Unreadable as error:
            found.append(f"{path}: {error}")
            continue
        if allowed:
            counts[expression] += 1
        else:
            found.append(f"{path}: {expression} is not allowed")
    return sources, counts, found


def taken(repo):
    """Every file `git add -A` would take, tracked or not, since the gate runs before the commit;
    one deleted and not yet staged is not among them."""
    listing = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        cwd=repo, stdout=subprocess.PIPE, stdin=subprocess.DEVNULL, check=True).stdout.decode()
    return [path for path in filter(None, listing.split("\0"))
            if (repo / path).is_file() and not (repo / path).is_symlink()]


def main(args):
    if args:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    try:
        allowlist = check_licenses.Allowlist((REPO / check_licenses.ALLOWLIST_PATH).read_text(encoding="utf-8"))
    except check_licenses.Unreadable as error:
        print(f"{check_licenses.ALLOWLIST_PATH}: {error}", file=sys.stderr)
        return 1
    sources, counts, found = scan(REPO, taken(REPO), allowlist)
    if sources < LEAST_SOURCES:
        print(f"found only {sources} sources", file=sys.stderr)
        return 1
    for line in found:
        print(line, file=sys.stderr)
    if found:
        return 1
    each = ", ".join(f"{count} {expression}" for expression, count in sorted(counts.items()))
    print(f"{sources} sources each state a license the allowlist passes: {each}")
    return 0


class Tests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Path(directory.name)
        self.allowlist = check_licenses.Allowlist("license MIT\nlicense BSD-3-Clause\n")

    def scan(self, files):
        for name, content in files.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        return scan(self.repo, list(files), self.allowlist)[1:]

    def test_a_tag_on_the_first_line_passes_in_each_comment_form(self):
        counts, found = self.scan({
            "kernel/src/lib.rs": "// SPDX-License-Identifier: MIT\n//! The kernel.\n",
            "tools/env.sh": "# SPDX-License-Identifier: MIT\nexport A=1\n",
            "shim.c": "/* SPDX-License-Identifier: BSD-3-Clause */\nint x;\n",
            "only.rs": "// SPDX-License-Identifier: MIT",
        })
        self.assertEqual(found, [])
        self.assertEqual(counts, {"MIT": 3, "BSD-3-Clause": 1})

    def test_a_source_with_no_tag_fails_with_its_path(self):
        _, found = self.scan({"a/b.rs": "//! Docs.\nfn f() {}\n", "empty.py": ""})
        self.assertEqual(found, [
            "a/b.rs: no 'SPDX-License-Identifier: <expression>' comment as its first line",
            "empty.py: no 'SPDX-License-Identifier: <expression>' comment as its first line",
        ])

    def test_a_tag_below_the_first_line_is_no_tag(self):
        _, found = self.scan({"a.rs": "//! Docs.\n// SPDX-License-Identifier: MIT\n"})
        self.assertEqual(found, ["a.rs: no 'SPDX-License-Identifier: <expression>' comment as its first line"])

    def test_the_tag_is_the_second_line_under_a_shebang(self):
        counts, found = self.scan({
            "tools/a.py": "#!/usr/bin/env python3\n# SPDX-License-Identifier: MIT\nimport sys\n",
            "tools/b.sh": "#!/bin/bash\nset -e\n# SPDX-License-Identifier: MIT\n",
            "tools/c.sh": "#!/bin/bash",
        })
        self.assertEqual(counts, {"MIT": 1})
        self.assertEqual(found, [
            "tools/b.sh: no 'SPDX-License-Identifier: <expression>' comment as its second line, under its #! line",
            "tools/c.sh: no 'SPDX-License-Identifier: <expression>' comment as its second line, under its #! line",
        ])

    def test_the_line_holds_nothing_but_the_tag(self):
        for line in ("// SPDX-License-Identifier: MIT, see LICENSE", "//SPDX-License-Identifier: MIT",
                     "// License: MIT", "SPDX-License-Identifier: MIT", "//  SPDX-License-Identifier:"):
            with self.subTest(line=line):
                _, found = self.scan({"a.rs": line + "\n"})
                self.assertEqual(len(found), 1, line)

    def test_an_expression_the_allowlist_refuses_fails(self):
        counts, found = self.scan({
            "gpl.c": "// SPDX-License-Identifier: GPL-2.0-only\n",
            "both.rs": "// SPDX-License-Identifier: MIT AND GPL-2.0-only\n",
            "bad.rs": "// SPDX-License-Identifier: MIT OR\n",
        })
        self.assertEqual(found, [
            "bad.rs: expected a license at None",
            "both.rs: MIT AND GPL-2.0-only is not allowed",
            "gpl.c: GPL-2.0-only is not allowed",
        ])
        self.assertEqual(counts, {})

    def test_a_choice_with_an_allowed_side_passes(self):
        counts, found = self.scan({"dual.rs": "// SPDX-License-Identifier: GPL-2.0-only OR MIT\n"})
        self.assertEqual((counts, found), ({"GPL-2.0-only OR MIT": 1}, []))

    def test_a_file_that_is_not_a_source_is_under_the_trees_license(self):
        counts, found = self.scan({
            "README.md": "# Atmosphere\n", "Cargo.toml": "[package]\n", "kernel/src/logo.txt": "x\n",
            "tools/page.html": "<!doctype html>\n", "tools/external-body-list": "# Every attribute\n",
        })
        self.assertEqual((counts, found), ({}, []))

    def test_the_sources_are_counted_whether_or_not_they_pass(self):
        for name, content in {"a.rs": "// SPDX-License-Identifier: MIT\n", "b.rs": "fn f() {}\n", "c.md": "x\n"}.items():
            (self.repo / name).write_text(content)
        self.assertEqual(scan(self.repo, ["a.rs", "b.rs", "c.md"], self.allowlist)[0], 2)

    def test_a_file_that_starts_with_a_shebang_is_a_source_whatever_its_name(self):
        _, found = self.scan({"tools/run": "#!/bin/sh\necho\n"})
        self.assertEqual(found, ["tools/run: no 'SPDX-License-Identifier: <expression>' comment as its second line, under its #! line"])

    def test_a_source_that_is_not_text_fails_as_untagged(self):
        (self.repo / "blob.c").write_bytes(b"\xff\xfe\x00\n")
        _, _, found = scan(self.repo, ["blob.c"], self.allowlist)
        self.assertEqual(len(found), 1)

    def test_this_script_states_its_own(self):
        self.assertEqual(stated(Path(__file__).read_bytes()), "MIT")


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
