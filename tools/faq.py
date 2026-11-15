#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Render docs/faq from its templates, with every number taken from the kernel's constants.

An explainer is a template docs/faq/src/<name>.md. Each placeholder {{NAME}} in it, or {{NAME:spec}}
with a Python format spec such as ',' for thousands separators, is replaced by a value: a kernel
constant of CONSTANTS, read from the file the table names for it, or a number DERIVED computes from
those constants. A constant's Rust value may be an integer literal (any base, digit grouping or type
suffix) or an expression of +, -, *, /, %, << and >> over literals and other constants of the table,
so a number in an explainer cannot drift from the code it describes. {{decompose:run}} and
{{decompose:overflow}} are not numbers: each is a Markdown table of a worked memory map, the blocks
order_below and run_blocks give it and, for overflow, which of them largest_blocks keeps. The
rendering is docs/faq/<name>.md, under a line saying it is generated.

docs/faq/README.md is the index: every explainer by its first '# ' heading, in file-name order.

GitHub renders Markdown, Mermaid fences and SVG image files, and not an HTML page, inline SVG or
script, so a template holding an svg, script, html, iframe or style element is refused.

Every file under docs/faq outside src is an output: one no template produces is removed on a write
and reported by --check. With no template there is no output at all.

usage: tools/faq.py           (from anywhere; rewrites docs/faq)
       tools/faq.py --check   (writes nothing; exit 1 naming each output that is not what it would write)
       tools/faq.py --test    (this script's own tests)

exit: 0 when written or current; 1 when a template is refused, a constant cannot be read, or --check
finds an output stale, missing or not produced by any template.
"""
import ast
import re
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
FAQ = Path("docs/faq")
SOURCES = FAQ / "src"
INDEX = "README.md"

# Each constant a template may name, with the file that defines it.
CONSTANTS = {
    "PAGE_SZ": "kernel/verified/define.rs",
    "ENTRIES": "kernel/verified/define.rs",
    "NODES_PER_PAGE": "kernel/verified/capability/list.rs",
    "ROOT_ENTRIES": "kernel/verified/capability/table.rs",
    "LEAF_BYTES": "kernel/verified/capability/table.rs",
    "MAX_ORDER": "kernel/verified/capability/table.rs",
    "ROOT_UNTYPED_SLOT": "kernel/verified/capability/boot.rs",
    "ROOT_FRAME_SLOT": "kernel/verified/capability/boot.rs",
    "ROOT_UNTYPED_SLOTS": "kernel/verified/capability/boot_memory.rs",
    "ROOT_FRAME_SLOTS": "kernel/verified/capability/boot_image.rs",
    "IMAGE_ORDER": "kernel/verified/capability/boot_image.rs",
    "PROCESS_ORDER": "kernel/verified/capability/process.rs",
    "TABLE_PAGE_BYTES": "kernel/verified/capability/space.rs",
}

# Boot's decomposition. order_below and run_blocks are the rule in
# kernel/verified/capability/decompose.rs: from the run's first page, the largest order up to the cap
# that page is aligned to and the run still holds, then the same from the page after that block.
# largest_kept is the selection largest_blocks makes in kernel/src/capability.rs: largest order
# first, and within an order the order the blocks were found, at most as many as the caller asks.
# The worked examples below are illustrations, not a machine's map. Their inputs live here and their
# blocks are computed, so an explainer cannot write the split by hand.


def order_below(start, n, cap):
    """The largest order at most cap that page `start` is aligned to and `n` pages hold, else 0."""
    order = cap
    while order > 0 and not (start % (1 << order) == 0 and (1 << order) <= n):
        order -= 1
    return order


def run_blocks(start, n, cap):
    """The blocks of one run, in address order, each as its first page and its order."""
    blocks = []
    while n > 0:
        order = order_below(start, n, cap)
        blocks.append((start, order))
        size = 1 << order
        start += size
        n -= size
    return blocks


def largest_kept(blocks, cap, slots):
    """The indices largest_blocks would keep, in the order it writes them."""
    kept = []
    for order in range(cap, -1, -1):
        for index, (_, block_order) in enumerate(blocks):
            if block_order == order and len(kept) < slots:
                kept.append(index)
    return kept


# One misaligned run, so alignment, the pages the run holds and the remainder each show.
EXAMPLE_START = 3
EXAMPLE_PAGES = 13
# One short odd-aligned run per untyped slot, so the blocks outnumber the slots.
OVERFLOW_ORIGIN = 1
OVERFLOW_PAGES = 3
OVERFLOW_STRIDE = 4


def example_blocks(cap):
    return run_blocks(EXAMPLE_START, EXAMPLE_PAGES, cap)


def overflow_runs(slots):
    return [(OVERFLOW_ORIGIN + index * OVERFLOW_STRIDE, OVERFLOW_PAGES) for index in range(slots)]


def overflow_blocks(cap, slots):
    blocks = []
    for start, count in overflow_runs(slots):
        blocks.extend(run_blocks(start, count, cap))
    return blocks


def overflow_account(cap, slots):
    """How many blocks the overflow map leaves unused, and how many pages those blocks are."""
    blocks = overflow_blocks(cap, slots)
    kept = set(largest_kept(blocks, cap, slots))
    pages_left = sum(1 << blocks[index][1] for index in range(len(blocks)) if index not in kept)
    return len(blocks) - len(kept), pages_left


def overflow_shape(cap):
    return run_blocks(OVERFLOW_ORIGIN, OVERFLOW_PAGES, cap)


def table_order(constants):
    """The order of a table page: TABLE_PAGE_BYTES is that many pages, a power of two."""
    pages = constants["TABLE_PAGE_BYTES"] // constants["PAGE_SZ"]
    if pages <= 0 or pages & (pages - 1):
        raise Refused(f"TABLE_PAGE_BYTES is {pages} pages, not a power of two")
    return pages.bit_length() - 1


def grouped_orders(blocks, kept, cap):
    """One row per order that occurs: order, pages, how many blocks, how many kept, how many left."""
    kept_set = set(kept)
    rows = []
    for order in range(cap, -1, -1):
        indexes = [index for index, (_, block_order) in enumerate(blocks) if block_order == order]
        if not indexes:
            continue
        keep = sum(1 for index in indexes if index in kept_set)
        rows.append((order, 1 << order, len(indexes), keep, len(indexes) - keep))
    return rows


def decompose_table(numbers, example):
    """The Markdown table a {{decompose:...}} placeholder stands for."""
    example = (example or "").strip()
    cap = numbers["MAX_ORDER"]
    if example == "run":
        lines = ["| Block | First page | Order | Pages |", "| --- | --- | --- | --- |"]
        for index, (page, order) in enumerate(example_blocks(cap)):
            lines.append(f"| {index} | {page} | {order} | {1 << order} |")
        return "\n".join(lines)
    if example == "overflow":
        slots = numbers["ROOT_UNTYPED_SLOTS"]
        blocks = overflow_blocks(cap, slots)
        lines = ["| Order | Pages in the block | Blocks | Kept | Left unused |",
                 "| --- | --- | --- | --- | --- |"]
        for order, pages, count, keep, left in grouped_orders(blocks, largest_kept(blocks, cap, slots), cap):
            lines.append(f"| {order} | {pages} | {count} | {keep} | {left} |")
        return "\n".join(lines)
    raise Refused(f"{{{{decompose}}}} example {example!r} is not run or overflow")


# Each number a template may name that no single constant holds.
DERIVED = {
    "BLOCKS_PER_RUN": lambda c: 2 * (c["MAX_ORDER"] + 1),
    "UNTYPED_LAST_SLOT": lambda c: c["ROOT_UNTYPED_SLOT"] + c["ROOT_UNTYPED_SLOTS"] - 1,
    "FRAME_LAST_SLOT": lambda c: c["ROOT_FRAME_SLOT"] + c["ROOT_FRAME_SLOTS"] - 1,
    "LEAF_SLOTS": lambda c: c["NODES_PER_PAGE"] - 1,
    "IMAGE_PAGES": lambda c: 1 << c["IMAGE_ORDER"],
    "TABLE_ORDER": table_order,
    "EXAMPLE_START": lambda c: EXAMPLE_START,
    "EXAMPLE_PAGES": lambda c: EXAMPLE_PAGES,
    "EXAMPLE_BLOCKS": lambda c: len(example_blocks(c["MAX_ORDER"])),
    "EXAMPLE_BLOCK0_PAGE": lambda c: example_blocks(c["MAX_ORDER"])[0][0],
    "EXAMPLE_BLOCK0_ORDER": lambda c: example_blocks(c["MAX_ORDER"])[0][1],
    "EXAMPLE_BLOCK0_PAGES": lambda c: 1 << example_blocks(c["MAX_ORDER"])[0][1],
    "EXAMPLE_BLOCK1_PAGE": lambda c: example_blocks(c["MAX_ORDER"])[1][0],
    "EXAMPLE_BLOCK1_ORDER": lambda c: example_blocks(c["MAX_ORDER"])[1][1],
    "EXAMPLE_BLOCK1_PAGES": lambda c: 1 << example_blocks(c["MAX_ORDER"])[1][1],
    "EXAMPLE_BLOCK2_PAGE": lambda c: example_blocks(c["MAX_ORDER"])[2][0],
    "EXAMPLE_BLOCK2_ORDER": lambda c: example_blocks(c["MAX_ORDER"])[2][1],
    "EXAMPLE_BLOCK2_PAGES": lambda c: 1 << example_blocks(c["MAX_ORDER"])[2][1],
    "OVERFLOW_ORIGIN": lambda c: OVERFLOW_ORIGIN,
    "OVERFLOW_PAGES": lambda c: OVERFLOW_PAGES,
    "OVERFLOW_STRIDE": lambda c: OVERFLOW_STRIDE,
    "OVERFLOW_RUNS": lambda c: c["ROOT_UNTYPED_SLOTS"],
    "OVERFLOW_BLOCKS": lambda c: len(overflow_blocks(c["MAX_ORDER"], c["ROOT_UNTYPED_SLOTS"])),
    "OVERFLOW_KEPT": lambda c: len(largest_kept(
        overflow_blocks(c["MAX_ORDER"], c["ROOT_UNTYPED_SLOTS"]), c["MAX_ORDER"], c["ROOT_UNTYPED_SLOTS"])),
    "OVERFLOW_LEFT": lambda c: overflow_account(c["MAX_ORDER"], c["ROOT_UNTYPED_SLOTS"])[0],
    "OVERFLOW_PAGES_LEFT": lambda c: overflow_account(c["MAX_ORDER"], c["ROOT_UNTYPED_SLOTS"])[1],
    "OVERFLOW_SMALL_ORDER": lambda c: overflow_shape(c["MAX_ORDER"])[0][1],
    "OVERFLOW_SMALL_PAGES": lambda c: 1 << overflow_shape(c["MAX_ORDER"])[0][1],
    "OVERFLOW_LARGE_ORDER": lambda c: overflow_shape(c["MAX_ORDER"])[1][1],
    "OVERFLOW_LARGE_PAGES": lambda c: 1 << overflow_shape(c["MAX_ORDER"])[1][1],
}

GENERATED = "<!-- GENERATED by tools/faq.py from {source}. Do not hand-edit. -->"
PLACEHOLDER = re.compile(r"\{\{\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?::([^}]*))?\}\}")
HTML = re.compile(r"<\s*/?\s*(svg|script|html|iframe|style)\b", re.IGNORECASE)
INT_SUFFIX = r"(?:u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)?"
LITERAL = re.compile(r"\b(0x[0-9A-Fa-f_]+|0o[0-7_]+|0b[01_]+|[0-9][0-9_]*)" + INT_SUFFIX + r"\b")
OPERATORS = {ast.Add: lambda a, b: a + b, ast.Sub: lambda a, b: a - b, ast.Mult: lambda a, b: a * b,
             ast.Div: lambda a, b: a // b, ast.Mod: lambda a, b: a % b,
             ast.LShift: lambda a, b: a << b, ast.RShift: lambda a, b: a >> b}


class Refused(Exception):
    """A template or a constant this script cannot render from; the message says where."""


def definition(root, name, path):
    """The Rust expression a const item gives name in the file at path."""
    text = (root / path).read_text(encoding="utf-8")
    found = re.findall(rf"\bconst\s+{name}\s*:[^=;]*=\s*([^;]+);", text)
    if len(found) != 1:
        raise Refused(f"{path}: {len(found)} definitions of const {name}, not one")
    return found[0].strip()


def evaluate(root, name, table, done=None, stack=()):
    """The integer value of the constant name, its expression's constants evaluated first."""
    done = {} if done is None else done
    if name in done:
        return done[name]
    if name in stack:
        raise Refused(f"const {name} is defined in terms of itself")
    if name not in table:
        raise Refused(f"const {name} is not in tools/faq.py's CONSTANTS")
    path = table[name]
    expression = definition(root, name, path)
    python = LITERAL.sub(lambda m: str(int(m.group(1).replace("_", ""), 0)), expression)

    def value(node):
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        if isinstance(node, ast.Name):
            return evaluate(root, node.id, table, done, stack + (name,))
        if isinstance(node, ast.BinOp) and type(node.op) in OPERATORS:
            return OPERATORS[type(node.op)](value(node.left), value(node.right))
        raise Refused(f"{path}: const {name} = {expression}: not an integer expression of constants")

    try:
        tree = ast.parse(python, mode="eval")
    except SyntaxError:
        raise Refused(f"{path}: const {name} = {expression}: not an integer expression of constants")
    done[name] = value(tree.body)
    return done[name]


def values(root, table=CONSTANTS, derived=DERIVED):
    """Every value a template may name: each constant of the table, then each derived number."""
    done = {}
    for name in table:
        evaluate(root, name, table, done)
    result = dict(done)
    for name, compute in derived.items():
        result[name] = compute(done)
    return result


def first_heading(source, text):
    for line in text.splitlines():
        if line.startswith("# "):
            return line[2:].strip()
    raise Refused(f"{source}: no '# ' heading to list it by")


def render(source, text, numbers):
    """The rendering of one template, its placeholders filled."""
    for number, line in enumerate(text.splitlines(), 1):
        if HTML.search(line):
            raise Refused(f"{source}:{number}: an HTML element GitHub would not render")
        for match in PLACEHOLDER.finditer(line):
            name, spec = match.group(1), match.group(2)
            if name == "decompose":
                try:
                    decompose_table(numbers, spec)
                except Refused as refused:
                    raise Refused(f"{source}:{number}: {refused}") from None
            elif name not in numbers:
                raise Refused(f"{source}:{number}: {{{{{name}}}}} names no constant or derived number")

    def fill(match):
        if match.group(1) == "decompose":
            return decompose_table(numbers, match.group(2))
        return format(numbers[match.group(1)], match.group(2) or "")

    return GENERATED.format(source=source) + "\n\n" + PLACEHOLDER.sub(fill, text)


def index(entries):
    out = [GENERATED.format(source="docs/faq/src"), "", "# Questions a reader asks first", "",
           "Each explainer answers one question about the design, cites the design record and the kernel "
           "source each claim comes from, and takes every number from the kernel's constants.", ""]
    out += [f"- [{title}](./{name})" for name, title in entries]
    return "\n".join(out) + "\n"


def outputs(root, table=CONSTANTS, derived=DERIVED):
    """Every file docs/faq should hold outside src, by its path under docs/faq, with its text."""
    templates = sorted((root / SOURCES).glob("*.md")) if (root / SOURCES).is_dir() else []
    if not templates:
        return {}
    numbers = values(root, table, derived)
    result, entries = {}, []
    for template in templates:
        source = template.relative_to(root).as_posix()
        text = template.read_text(encoding="utf-8")
        result[template.name] = render(source, text, numbers)
        entries.append((template.name, first_heading(source, text)))
    result[INDEX] = index(entries)
    return result


def present(root):
    """Every file docs/faq holds outside src, by its path under docs/faq."""
    faq = root / FAQ
    if not faq.is_dir():
        return set()
    return {p.relative_to(faq).as_posix() for p in faq.rglob("*")
            if p.is_file() and SOURCES.name not in p.relative_to(faq).parts[:1]}


def differences(root, table=CONSTANTS, derived=DERIVED):
    """Each output that is stale, missing or produced by no template, one line each."""
    wanted = outputs(root, table, derived)
    lines = []
    for name in sorted(present(root) | set(wanted)):
        path = root / FAQ / name
        if name not in wanted:
            lines.append(f"{FAQ / name}: produced by no template")
        elif not path.exists():
            lines.append(f"{FAQ / name}: missing")
        elif path.read_text(encoding="utf-8") != wanted[name]:
            lines.append(f"{FAQ / name}: stale")
    return lines


def write(root, table=CONSTANTS, derived=DERIVED):
    wanted = outputs(root, table, derived)
    for name in present(root) - set(wanted):
        (root / FAQ / name).unlink()
    for name, text in wanted.items():
        path = root / FAQ / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text(encoding="utf-8") != text:
            path.write_text(text, encoding="utf-8")
    return sorted(wanted)


class Tests(unittest.TestCase):
    TABLE = {"PAGE": "define.rs", "LEAF": "table.rs", "SLOTS": "table.rs"}

    def tree(self, templates, define="pub const PAGE: usize = 4096;\n"):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        (root / "define.rs").write_text(define)
        (root / "table.rs").write_text("pub const LEAF: usize = PAGE * 2; // the leaf\n"
                                       "pub(crate) const SLOTS: u8 = (0x1_00u16 - 1) << 1;\n")
        (root / SOURCES).mkdir(parents=True)
        for name, text in templates.items():
            (root / SOURCES / name).write_text(text)
        return root

    def test_a_placeholder_renders_to_its_constants_value(self):
        root = self.tree({"a.md": "# A\n\nA page is {{PAGE}} bytes, or {{PAGE:,}}.\n"})
        self.assertIn("A page is 4096 bytes, or 4,096.", outputs(root, self.TABLE, {})["a.md"])

    def test_a_constant_defined_by_an_expression_evaluates(self):
        root = self.tree({"a.md": "# A\n\n{{LEAF}} and {{SLOTS}}\n"})
        self.assertIn("8192 and 510", outputs(root, self.TABLE, {})["a.md"])

    def test_a_derived_number_is_a_function_of_the_constants(self):
        root = self.tree({"a.md": "# A\n\n{{PAGES}}\n"})
        derived = {"PAGES": lambda c: c["LEAF"] // c["PAGE"]}
        self.assertIn("\n2\n", outputs(root, self.TABLE, derived)["a.md"])

    def test_an_unknown_placeholder_fails_with_its_file_and_line(self):
        root = self.tree({"a.md": "# A\n\n{{NOPE}}\n"})
        with self.assertRaisesRegex(Refused, r"docs/faq/src/a\.md:3: \{\{NOPE\}\}"):
            outputs(root, self.TABLE, {})

    def test_a_constant_outside_the_table_or_defined_twice_is_refused(self):
        root = self.tree({"a.md": "# A\n"}, define="pub const PAGE: usize = OTHER;\n")
        with self.assertRaisesRegex(Refused, "OTHER is not in"):
            outputs(root, self.TABLE, {})
        root = self.tree({"a.md": "# A\n"}, define="const PAGE: usize = 1;\nconst PAGE: usize = 2;\n")
        with self.assertRaisesRegex(Refused, "2 definitions of const PAGE"):
            outputs(root, self.TABLE, {})

    def test_a_changed_constant_changes_the_output(self):
        template = {"a.md": "# A\n\n{{LEAF}}\n"}
        before = outputs(self.tree(template), self.TABLE, {})["a.md"]
        after = outputs(self.tree(template, define="pub const PAGE: usize = 16384;\n"), self.TABLE, {})["a.md"]
        self.assertIn("8192", before)
        self.assertIn("32768", after)

    def test_check_finds_stale_missing_and_stray_outputs_and_passes_a_current_tree(self):
        root = self.tree({"a.md": "# A\n\n{{PAGE}}\n", "b.md": "# B\n"})
        self.assertEqual(differences(root, self.TABLE, {}),
                         ["docs/faq/README.md: missing", "docs/faq/a.md: missing", "docs/faq/b.md: missing"])
        (root / FAQ / "old.svg").write_text("<svg/>")
        write(root, self.TABLE, {})
        self.assertFalse((root / FAQ / "old.svg").exists())
        self.assertEqual(differences(root, self.TABLE, {}), [])
        (root / FAQ / "a.md").write_text("4096\n")
        (root / FAQ / "old.md").write_text("gone\n")
        self.assertEqual(differences(root, self.TABLE, {}),
                         ["docs/faq/a.md: stale", "docs/faq/old.md: produced by no template"])

    def test_no_template_means_no_output(self):
        root = self.tree({})
        self.assertEqual(differences(root, self.TABLE, {}), [])
        (root / FAQ / "README.md").write_text("x")
        self.assertEqual(differences(root, self.TABLE, {}), ["docs/faq/README.md: produced by no template"])

    def test_the_index_lists_every_template_by_its_first_heading_in_file_name_order(self):
        root = self.tree({"b.md": "intro\n# Second\n## Not this\n", "a.md": "# First\n"})
        text = outputs(root, self.TABLE, {})["README.md"]
        self.assertLess(text.index("- [First](./a.md)"), text.index("- [Second](./b.md)"))
        self.assertNotIn("Not this", text)

    def test_a_template_without_a_heading_is_refused(self):
        root = self.tree({"a.md": "## Only a section\n"})
        with self.assertRaisesRegex(Refused, "a.md: no '# ' heading"):
            outputs(root, self.TABLE, {})

    def test_a_template_holding_an_html_element_is_refused(self):
        for element in ("<svg width='1'>", "<script>", "</html>", "<IFRAME src=x>", "< style>"):
            root = self.tree({"a.md": f"# A\n\n{element}\n"})
            with self.assertRaisesRegex(Refused, "a.md:3: an HTML element"):
                outputs(root, self.TABLE, {})

    def test_the_tree_defines_every_constant_of_the_table_once(self):
        self.assertEqual(set(values(REPO)), set(CONSTANTS) | set(DERIVED))

    def test_a_misaligned_run_decomposes_by_boots_rule(self):
        # Page 3 of a 13-page run is aligned only to order 0; page 4 holds an
        # order-2 block; the eight pages at page 8 are one order-3 block.
        self.assertEqual(run_blocks(3, 13, 36), [(3, 0), (4, 2), (8, 3)])
        self.assertEqual(run_blocks(8, 8, 36), [(8, 3)])
        self.assertEqual(run_blocks(0, 16, 2), [(0, 2), (4, 2), (8, 2), (12, 2)])
        self.assertEqual(run_blocks(1, 3, 36), [(1, 0), (2, 1)])

    def test_the_largest_blocks_are_kept_and_the_smallest_stay_unused(self):
        blocks = run_blocks(1, 3, 36) + run_blocks(5, 3, 36)
        self.assertEqual(largest_kept(blocks, 36, 2), [1, 3])
        self.assertEqual([blocks[i] for i in largest_kept(blocks, 36, 2)], [(2, 1), (6, 1)])

    def test_the_worked_examples_follow_the_rule_and_the_slot_count(self):
        numbers = values(REPO)
        cap = numbers["MAX_ORDER"]
        slots = numbers["ROOT_UNTYPED_SLOTS"]
        self.assertEqual(example_blocks(cap), [(3, 0), (4, 2), (8, 3)])
        self.assertEqual(sum(1 << order for _, order in example_blocks(cap)), EXAMPLE_PAGES)
        blocks = []
        for index in range(slots):
            blocks.extend(run_blocks(OVERFLOW_ORIGIN + index * OVERFLOW_STRIDE, OVERFLOW_PAGES, cap))
        self.assertEqual(blocks[0], (1, 0))
        self.assertEqual(blocks[1], (2, 1))
        kept = largest_kept(blocks, cap, slots)
        self.assertEqual(len(blocks), 2 * slots)
        self.assertEqual(len(kept), slots)
        self.assertTrue(all(blocks[i][1] == 1 for i in kept))
        left = [blocks[i] for i in range(len(blocks)) if i not in set(kept)]
        self.assertEqual(left, [(OVERFLOW_ORIGIN + index * OVERFLOW_STRIDE, 0) for index in range(slots)])
        self.assertEqual(numbers["EXAMPLE_BLOCKS"], 3)
        self.assertEqual(numbers["EXAMPLE_BLOCK0_ORDER"], 0)
        self.assertEqual(numbers["EXAMPLE_BLOCK2_PAGES"], 8)
        self.assertEqual(numbers["OVERFLOW_RUNS"], slots)
        self.assertEqual(numbers["OVERFLOW_BLOCKS"], 2 * slots)
        self.assertEqual(numbers["OVERFLOW_KEPT"], slots)
        self.assertEqual(numbers["OVERFLOW_LEFT"], slots)
        self.assertEqual(numbers["OVERFLOW_PAGES_LEFT"], slots)
        self.assertEqual(numbers["OVERFLOW_SMALL_ORDER"], 0)
        self.assertEqual(numbers["OVERFLOW_LARGE_PAGES"], 2)

    def test_boot_slot_numbers_match_the_leaves(self):
        numbers = values(REPO)
        self.assertEqual(numbers["ROOT_UNTYPED_SLOT"] + numbers["ROOT_UNTYPED_SLOTS"], numbers["NODES_PER_PAGE"])
        self.assertEqual(numbers["UNTYPED_LAST_SLOT"], numbers["NODES_PER_PAGE"] - 1)
        self.assertEqual(numbers["LEAF_SLOTS"], numbers["NODES_PER_PAGE"] - 1)
        self.assertEqual(numbers["ROOT_FRAME_SLOT"], numbers["NODES_PER_PAGE"] + 1)
        self.assertEqual(numbers["ROOT_FRAME_SLOTS"], numbers["LEAF_SLOTS"])
        self.assertEqual(numbers["FRAME_LAST_SLOT"], 2 * numbers["NODES_PER_PAGE"] - 1)
        self.assertEqual(numbers["BLOCKS_PER_RUN"], 2 * (numbers["MAX_ORDER"] + 1))
        self.assertLessEqual(numbers["BLOCKS_PER_RUN"], numbers["ROOT_UNTYPED_SLOTS"])
        self.assertEqual(numbers["IMAGE_PAGES"], 1 << numbers["IMAGE_ORDER"])
        pages = numbers["TABLE_PAGE_BYTES"] // numbers["PAGE_SZ"]
        self.assertEqual(pages & (pages - 1), 0)
        self.assertEqual(numbers["TABLE_ORDER"], pages.bit_length() - 1)
        self.assertEqual(numbers["TABLE_ORDER"], 3)

    def test_a_decompose_placeholder_renders_the_computed_blocks(self):
        numbers = values(REPO)
        text = render("docs/faq/src/a.md", "# A\n\n{{decompose:run}}\n\n{{decompose:overflow}}\n", numbers)
        self.assertIn("| 0 | 3 | 0 | 1 |", text)
        self.assertIn("| 2 | 8 | 3 | 8 |", text)
        self.assertIn(f"| 1 | 2 | {numbers['ROOT_UNTYPED_SLOTS']} | {numbers['ROOT_UNTYPED_SLOTS']} | 0 |", text)
        self.assertNotIn("<svg", text)
        with self.assertRaisesRegex(Refused, "decompose"):
            render("docs/faq/src/a.md", "# A\n\n{{decompose:nope}}\n", numbers)


def main(arguments):
    if arguments == ["--test"]:
        sys.argv[1:] = []
        unittest.main(module=__name__, exit=True)
    assert arguments in ([], ["--check"]), __doc__
    try:
        if arguments == ["--check"]:
            lines = differences(REPO)
            if lines:
                sys.exit("\n".join(lines) + "\nrun tools/faq.py")
            print(f"{FAQ} is what tools/faq.py writes")
        else:
            for name in write(REPO):
                print(FAQ / name)
    except Refused as refused:
        sys.exit(str(refused))


if __name__ == "__main__":
    main(sys.argv[1:])
