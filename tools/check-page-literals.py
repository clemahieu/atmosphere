#!/usr/bin/env python3
"""Check that kernel/verified writes no page size, entries a level or size derived from them as a
literal outside the definitions.

A literal cannot be told from an unrelated number or changed in one place, and the granule is to
become the target's (design/arch-module/). The page-shaped values are the 4K page and its offset
mask, the entries a level and its index mask, the 2M, 1G and 512G regions and their offset masks,
and the pages in a 1G and a 512G region. A number literal of any base, digit grouping or suffix
whose value is one of them is refused, outside '//' and '/* */' comments and string literals. The
definitions are exempt: define.rs and arch/. A line that holds such a value for another reason
says so in a comment '// not a page size: <reason>'.

tools/page-literal-allowance lists the files under kernel/verified not yet converted, one path a
line, '#' starting a comment line. A literal in a listed file passes; a listed file that holds none
fails the check, so the list only shrinks.

usage: tools/check-page-literals.py           (the tree)
       tools/check-page-literals.py --test    (this script's own tests)
"""
import re
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
ALLOWANCE_PATH = "tools/page-literal-allowance"
VERIFIED_ROOT = "kernel/verified"
EXEMPT_FILES = ("define.rs",)
EXEMPT_DIRECTORIES = ("arch",)
MARKER = re.compile(r"//\s*not a page size:\s*\S")

PAGE = 4096
ENTRIES = 512
REGIONS = (PAGE, PAGE * ENTRIES, PAGE * ENTRIES**2, PAGE * ENTRIES**3)
VALUES = frozenset(
    [ENTRIES, ENTRIES - 1, ENTRIES**2, ENTRIES**3]
    + [size for size in REGIONS]
    + [size - 1 for size in REGIONS]
)

NUMBER = re.compile(
    r"\b(0x[0-9a-fA-F_]+|0o[0-7_]+|0b[01_]+|[0-9][0-9_]*)"
    r"(?:[iu](?:8|16|32|64|128|size))?\b"
)
BLOCK_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)
STRING = re.compile(r'"(?:\\.|[^"\\])*"')


class Unreadable(Exception):
    """An allowance line that names no file under kernel/verified."""


def value(token):
    """The value a number token without its suffix spells."""
    digits = token.replace("_", "")
    for prefix, base in (("0x", 16), ("0o", 8), ("0b", 2)):
        if digits.startswith(prefix):
            return int(digits[2:], base)
    return int(digits)


def blank(match):
    """The matched text with everything but its newlines turned to spaces, so lines keep their numbers."""
    return re.sub(r"[^\n]", " ", match.group(0))


def literals(path, source):
    """Each line of one file that writes a page-shaped literal, as 'path:line: text'."""
    code = STRING.sub(blank, BLOCK_COMMENT.sub(blank, source))
    found = []
    for index, (line, original) in enumerate(zip(code.splitlines(), source.splitlines())):
        if MARKER.search(original):
            continue
        live = line.split("//", 1)[0]
        if any(value(match.group(1)) in VALUES for match in NUMBER.finditer(live)):
            found.append(f"{path}:{index + 1}: {original.strip()}")
    return found


def exempt(path):
    """Whether a path under kernel/verified is one of the definitions."""
    return path in EXEMPT_FILES or path.split("/", 1)[0] in EXEMPT_DIRECTORIES


def parse_allowance(text):
    """The paths the allowance lists, in order."""
    paths = []
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        if line != line.strip() or not line.endswith(".rs"):
            raise Unreadable(f"{ALLOWANCE_PATH}: cannot read {line!r}")
        paths.append(line)
    return paths


def judge(found, allowed):
    """The failures for the literals found, keyed by path, against the paths the allowance lists."""
    failures = []
    for path, lines in sorted(found.items()):
        if path not in allowed:
            failures.extend(f"{line}: a page-shaped literal outside the definitions" for line in lines)
    for path in allowed:
        if not found.get(path):
            failures.append(f"{ALLOWANCE_PATH}: {path} holds no page-shaped literal: take it off the list")
    return failures


def sources(directory):
    """The Rust sources under a directory."""
    for entry in sorted(directory.iterdir()):
        if entry.is_dir():
            yield from sources(entry)
        elif entry.suffix == ".rs":
            yield entry


def scan_tree(verified):
    """The page-shaped literal lines of every file under kernel/verified outside the definitions."""
    found = {}
    for file in sources(verified):
        path = file.relative_to(verified).as_posix()
        if exempt(path):
            continue
        lines = literals(path, file.read_text(encoding="utf-8"))
        if lines:
            found[path] = lines
    return found


def main(args):
    if args:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    try:
        allowed = parse_allowance((REPO / ALLOWANCE_PATH).read_text(encoding="utf-8"))
    except Unreadable as error:
        print(error, file=sys.stderr)
        return 1
    found = scan_tree(REPO / VERIFIED_ROOT)
    failures = judge(found, allowed)
    for failure in failures:
        print(failure, file=sys.stderr)
    if failures:
        return 1
    count = sum(len(lines) for lines in found.values())
    print(f"{count} page-shaped literal lines in the {len(allowed)} files on {ALLOWANCE_PATH}; none elsewhere")
    return 0


class Tests(unittest.TestCase):
    def test_each_page_shaped_value_is_caught_in_decimal_and_hex(self):
        for number in sorted(VALUES):
            for spelling in (str(number), hex(number)):
                with self.subTest(spelling=spelling):
                    self.assertEqual(literals("a.rs", f"let x = {spelling};\n"), [f"a.rs:1: let x = {spelling};"])

    def test_the_values_are_the_page_entries_and_regions(self):
        expected = {4096, 4095, 512, 511, 0x20_0000, 0x1f_ffff, 0x4000_0000, 0x3fff_ffff,
                    0x80_0000_0000, 0x7f_ffff_ffff, 262144, 134217728}
        self.assertEqual(VALUES, expected)

    def test_grouped_hex_and_suffixes_are_caught(self):
        for spelling in ("0x20_0000", "0x4000_0000", "0x80_0000_0000", "0x0000_1000", "4096usize",
                         "0x1000u64", "4_096", "0x1FF", "0o10000", "0b1000000000"):
            with self.subTest(spelling=spelling):
                self.assertEqual(len(literals("a.rs", f"x({spelling})\n")), 1)

    def test_a_type_length_and_a_modulus_are_caught(self):
        source = "pub type PageBytes = [u8; 4096];\n    &&& page.addr() % 4096 == 0\n"
        self.assertEqual(literals("a.rs", source), [
            "a.rs:1: pub type PageBytes = [u8; 4096];",
            "a.rs:2: &&& page.addr() % 4096 == 0",
        ])

    def test_identifiers_and_longer_numbers_are_not_literals(self):
        source = "PAGE_SZ_4K x4096 _512 40960 0x1000_0000 5120 1024 0x2000 page_4096 ret.0\n"
        self.assertEqual(literals("a.rs", source), [])

    def test_comments_and_strings_are_not_code(self):
        source = (
            "// a 4096-byte page\n"
            "/// 512 entries\n"
            "let x = 1; // 4096\n"
            "/* 4096\n512 */ let y = 2;\n"
            'let s = "4096";\n'
        )
        self.assertEqual(literals("a.rs", source), [])

    def test_a_block_comment_keeps_the_line_numbers(self):
        self.assertEqual(literals("a.rs", "/* one\ntwo */\nlet x = 512;\n"), ["a.rs:3: let x = 512;"])

    def test_the_marker_with_a_reason_passes_a_line(self):
        self.assertEqual(literals("a.rs", "len == 4096 // not a page size: an IOMMU ring length\n"), [])
        self.assertEqual(len(literals("a.rs", "len == 4096 // not a page size:\n")), 1)

    def test_define_and_arch_are_exempt(self):
        self.assertTrue(exempt("define.rs"))
        self.assertTrue(exempt("arch/x86_64.rs"))
        self.assertFalse(exempt("capability/define.rs"))
        self.assertFalse(exempt("layouts.rs"))
        self.assertFalse(exempt("archive.rs"))

    def test_a_literal_in_an_unlisted_file_fails_with_where_it_is(self):
        found = {"b.rs": ["b.rs:7: x * 4096"]}
        self.assertEqual(judge(found, []), ["b.rs:7: x * 4096: a page-shaped literal outside the definitions"])

    def test_a_literal_in_a_listed_file_passes(self):
        self.assertEqual(judge({"b.rs": ["b.rs:7: x * 4096"]}, ["b.rs"]), [])

    def test_a_listed_file_without_a_literal_fails(self):
        self.assertEqual(
            judge({}, ["b.rs"]),
            [f"{ALLOWANCE_PATH}: b.rs holds no page-shaped literal: take it off the list"],
        )

    def test_the_allowance_is_one_path_a_line(self):
        self.assertEqual(parse_allowance("# files\n\ncapability/map.rs\nlayouts.rs\n"), ["capability/map.rs", "layouts.rs"])
        with self.assertRaises(Unreadable):
            parse_allowance("capability/map.rs extra\n")
        with self.assertRaises(Unreadable):
            parse_allowance(" layouts.rs\n")

    def test_the_tree_scan_skips_the_definitions(self):
        import tempfile

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "arch").mkdir()
            (root / "capability").mkdir()
            (root / "define.rs").write_text("pub const PAGE_SZ: usize = 4096;\n")
            (root / "arch" / "x86_64.rs").write_text("pub const MEM_4K_MASK: u64 = 0xfff;\n")
            (root / "capability" / "map.rs").write_text("let l1 = (va / 0x1000) % 512;\n")
            self.assertEqual(scan_tree(root), {"capability/map.rs": ["capability/map.rs:1: let l1 = (va / 0x1000) % 512;"]})


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
