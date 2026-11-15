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

A template may also name a plot, as a markdown image whose target is <file>.svg or ./<file>.svg and
whose <file>.svg is a key of PLOTS. The plot is an SVG file written beside the rendering from the same
numbers. Chart draws that figure with presentation attributes and no script or style element, which a
later explainer reuses for its own plot. A target that is not a plot is refused. table-growth.svg is
each way of growing the capability table: its slot capacity, its smallest table, its full table and
the memory that capacity holds at each block size.

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
import math
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
    "INDEX_BITS": "kernel/verified/define.rs",
    "PAGES_PER_2M": "kernel/verified/define.rs",
    "PAGES_PER_1G": "kernel/verified/define.rs",
    "SIZE_2M": "kernel/verified/define.rs",
    "SIZE_1G": "kernel/verified/define.rs",
    "NODES_PER_PAGE": "kernel/verified/capability/list.rs",
    "NODE_SPACE": "kernel/verified/capability/list.rs",
    "ROOT_ENTRIES": "kernel/verified/capability/table.rs",
    "LEAF_BYTES": "kernel/verified/capability/table.rs",
    "TABLE_INDICES": "kernel/verified/capability/table.rs",
    "MAX_ORDER": "kernel/verified/capability/table.rs",
    "ROOT_UNTYPED_SLOT": "kernel/verified/capability/boot.rs",
    "ROOT_FRAME_SLOT": "kernel/verified/capability/boot.rs",
    "ROOT_UNTYPED_SLOTS": "kernel/verified/capability/boot_memory.rs",
    "ROOT_FRAME_SLOTS": "kernel/verified/capability/boot_image.rs",
    "IMAGE_ORDER": "kernel/verified/capability/boot_image.rs",
    "PROCESS_ORDER": "kernel/verified/capability/process.rs",
    "PROCESS_BYTES": "kernel/verified/capability/process.rs",
    "PROCESS_RECORD_PAGE": "kernel/verified/capability/process.rs",
    "THREAD_ORDER": "kernel/verified/capability/thread.rs",
    "TABLE_PAGE_BYTES": "kernel/verified/capability/space.rs",
    "SPACE_ROOT_PAGE": "kernel/verified/capability/space.rs",
    "POSITION_INDEX_MASK": "kernel/verified/capability/position.rs",
    "POSITION_THROUGH_SHIFT": "kernel/verified/capability/position.rs",
    "POSITION_WIDTH": "kernel/verified/capability/position.rs",
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


def reach(constants, size):
    """Bytes a full table holds with one block of this size in each slot, and no more than the address space."""
    slots = constants["ROOT_ENTRIES"] * (constants["NODES_PER_PAGE"] - 1)
    return min(slots * constants[size], constants["NODE_SPACE"])


def spare_pages(constants):
    """Pages strictly between the process record and the address-space root.

    spare_kept names each of them. The record's page index and the space root's page index are the
    bounds, so the count is the pages a process block already keeps and does not use.
    """
    pages = constants["SPACE_ROOT_PAGE"] - constants["PROCESS_RECORD_PAGE"] - 1
    if pages <= 0:
        raise Refused(f"{pages} spare pages between the process record and the address space")
    return pages


def root_pages(constants):
    """The root page before the record, plus the spare pages a larger root would use."""
    return constants["PROCESS_RECORD_PAGE"] + spare_pages(constants)


def leaf_pages(constants):
    """Pages in a leaf. A leaf is one node page and one payload page, so the count is even."""
    pages = constants["LEAF_BYTES"] // constants["PAGE_SZ"]
    if pages <= 0 or pages % 2 or constants["LEAF_BYTES"] % constants["PAGE_SZ"]:
        raise Refused(f"LEAF_BYTES is {constants['LEAF_BYTES']} bytes, not a node page and a payload page")
    return pages


def double_node_pages(constants):
    """Node pages in a leaf of twice today's pages. Half of a leaf's pages are node pages."""
    return 2 * (leaf_pages(constants) // 2)


def big_nodes(constants):
    """Nodes in one page of SIZE_2M at a node page's density, NODES_PER_PAGE per PAGE_SZ."""
    if constants["SIZE_2M"] % constants["PAGE_SZ"]:
        raise Refused("SIZE_2M is not a whole number of pages")
    return (constants["SIZE_2M"] // constants["PAGE_SZ"]) * constants["NODES_PER_PAGE"]


def entry_bytes(constants):
    """Bytes of one node and of one payload. The entries fill the page."""
    page, count = constants["PAGE_SZ"], constants["NODES_PER_PAGE"]
    if count <= 0 or page % count:
        raise Refused(f"PAGE_SZ is {page} bytes, not {count} entries")
    return page // count


# Each number a template may name that no single constant holds.
DERIVED = {
    "BLOCKS_PER_RUN": lambda c: 2 * (c["MAX_ORDER"] + 1),
    "UNTYPED_LAST_SLOT": lambda c: c["ROOT_UNTYPED_SLOT"] + c["ROOT_UNTYPED_SLOTS"] - 1,
    "FRAME_LAST_SLOT": lambda c: c["ROOT_FRAME_SLOT"] + c["ROOT_FRAME_SLOTS"] - 1,
    "LEAF_SLOTS": lambda c: c["NODES_PER_PAGE"] - 1,
    # One node, and one payload: the entries fill the page, which the layout claim sizes at one page.
    "ENTRY_BYTES": entry_bytes,
    # One leaf's slots at every root entry. The larger frame order is twice the shift of a 2M block.
    "TABLE_SLOTS": lambda c: c["ROOT_ENTRIES"] * (c["NODES_PER_PAGE"] - 1),
    "ONE_G_ORDER": lambda c: 2 * c["INDEX_BITS"],
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
    "REACH_4K": lambda c: reach(c, "PAGE_SZ"),
    "REACH_2M": lambda c: reach(c, "SIZE_2M"),
    "REACH_1G": lambda c: reach(c, "SIZE_1G"),
    # NODE_SPACE is the end of the address space, one past its last byte, and a power of two.
    "ADDRESS_BITS": lambda c: c["NODE_SPACE"].bit_length() - 1,
    # The position word's index field. The mask admits one index per value it covers.
    "INDEX_FIELD_COUNT": lambda c: c["POSITION_INDEX_MASK"] + 1,
    "INDEX_FIELD_BITS": lambda c: (c["POSITION_INDEX_MASK"] + 1).bit_length() - 1,
    # Growing the root uses the spare pages the process block already keeps.
    "SPARE_PAGES": spare_pages,
    "ROOT_PAGES": root_pages,
    "LEAF_PAGES": leaf_pages,
    "PROCESS_PAGES": lambda c: c["PROCESS_BYTES"] // c["PAGE_SZ"],
    "TABLE_BYTES": lambda c: c["ROOT_ENTRIES"] * c["LEAF_BYTES"],
    "ROOTS_SLOTS": lambda c: root_pages(c) * c["ROOT_ENTRIES"] * (c["NODES_PER_PAGE"] - 1),
    "ROOTS_FULL": lambda c: root_pages(c) * c["ROOT_ENTRIES"] * c["LEAF_BYTES"],
    "ROOTS_INDICES": lambda c: root_pages(c) * c["ROOT_ENTRIES"] * c["NODES_PER_PAGE"],
    # A leaf of twice the pages: the node pages double, and one hidden node remains.
    "DOUBLE_NODE_PAGES": double_node_pages,
    "DOUBLE_PAGES": lambda c: 2 * leaf_pages(c),
    "DOUBLE_NODES": lambda c: double_node_pages(c) * c["NODES_PER_PAGE"],
    "DOUBLE_SLOTS_PER": lambda c: double_node_pages(c) * c["NODES_PER_PAGE"] - 1,
    "DOUBLE_TABLE_SLOTS": lambda c: c["ROOT_ENTRIES"] * (double_node_pages(c) * c["NODES_PER_PAGE"] - 1),
    "DOUBLE_LEAF_BYTES": lambda c: 2 * leaf_pages(c) * c["PAGE_SZ"],
    "DOUBLE_FULL": lambda c: c["ROOT_ENTRIES"] * 2 * leaf_pages(c) * c["PAGE_SZ"],
    "DOUBLE_INDICES": lambda c: c["ROOT_ENTRIES"] * double_node_pages(c) * c["NODES_PER_PAGE"],
    # A leaf whose node page and payload page are each the large page.
    "BIG_NODES": big_nodes,
    "BIG_SLOTS_PER": lambda c: big_nodes(c) - 1,
    "BIG_TABLE_SLOTS": lambda c: c["ROOT_ENTRIES"] * (big_nodes(c) - 1),
    "BIG_LEAF_BYTES": lambda c: 2 * c["SIZE_2M"],
    "BIG_FULL": lambda c: c["ROOT_ENTRIES"] * 2 * c["SIZE_2M"],
    "BIG_INDICES": lambda c: c["ROOT_ENTRIES"] * big_nodes(c),
    # A page of pointers, the root's shape, between the root and the leaf.
    "THIRD_SLOTS": lambda c: c["ROOT_ENTRIES"] * c["ENTRIES"] * (c["NODES_PER_PAGE"] - 1),
    "THIRD_SMALLEST": lambda c: c["PAGE_SZ"] + c["LEAF_BYTES"],
    "THIRD_LEAVES_BYTES": lambda c: c["ROOT_ENTRIES"] * c["ENTRIES"] * c["LEAF_BYTES"],
    "THIRD_MIDDLE_BYTES": lambda c: c["ROOT_ENTRIES"] * c["PAGE_SZ"],
    "THIRD_FULL": lambda c: c["ROOT_ENTRIES"] * c["ENTRIES"] * c["LEAF_BYTES"] + c["ROOT_ENTRIES"] * c["PAGE_SZ"],
    "THIRD_INDICES": lambda c: c["ROOT_ENTRIES"] * c["ENTRIES"] * c["NODES_PER_PAGE"],
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


def xml_text(text):
    """Text safe to place in an SVG text node."""
    return str(text).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def bytes_label(n):
    """n in the largest binary unit that divides it, so a label states the number exactly."""
    for shift, unit in ((40, "TiB"), (30, "GiB"), (20, "MiB"), (10, "KiB")):
        size = 1 << shift
        if n >= size and n % size == 0:
            return f"{n // size:,} {unit}"
    return f"{n:,} B"


def count_label(n):
    """A slot-count tick: a power of two, in thousands when it is large."""
    if n >= 1 << 20 and n % (1 << 20) == 0:
        return f"{n >> 20} M"
    if n >= 1 << 10 and n % (1 << 10) == 0:
        return f"{n >> 10} K"
    return f"{n:,}"


def log2_of(n):
    """log2(n), exact when n is a power of two."""
    if n > 0 and n & (n - 1) == 0:
        return float(n.bit_length() - 1)
    return math.log2(n)


class Chart:
    """A static SVG figure.

    GitHub shows the file as an image, so the figure uses presentation attributes and carries no
    script and no style element. A later explainer draws its own plot with this.
    """

    def __init__(self, width, height):
        self.width = width
        self.height = height
        self.parts = []

    def rect(self, x, y, w, h, fill):
        self.parts.append(
            f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" fill="{fill}"/>'
        )

    def line(self, x1, y1, x2, y2, stroke, width=1.5, dash=None):
        extra = f' stroke-dasharray="{dash}"' if dash else ""
        self.parts.append(
            f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
            f'stroke="{stroke}" stroke-width="{width}"{extra}/>'
        )

    def circle(self, cx, cy, r, fill):
        self.parts.append(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}" fill="{fill}"/>')

    def text(self, x, y, content, size=12, anchor="start", fill="#222222"):
        self.parts.append(
            f'<text x="{x:.1f}" y="{y:.1f}" font-family="sans-serif" font-size="{size}" '
            f'fill="{fill}" text-anchor="{anchor}">{xml_text(content)}</text>'
        )

    def document(self, title, desc):
        body = "\n  ".join(self.parts)
        return (
            '<?xml version="1.0" encoding="UTF-8"?>\n'
            "<!-- GENERATED by tools/faq.py from the kernel's constants. Do not hand-edit. -->\n"
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.width}" height="{self.height}" '
            f'viewBox="0 0 {self.width} {self.height}">\n'
            f"  <title>{xml_text(title)}</title>\n"
            f"  <desc>{xml_text(desc)}</desc>\n"
            f"  {body}\n"
            "</svg>\n"
        )


def slots_versus_memory_svg(numbers):
    """The slots one process needs to hold a memory size as blocks of one size, against the table.

    Both axes are logarithmic. Each diagonal is one capability per block of one size, the horizontal
    lines are the full table and one run's untyped blocks, and each dot is where a diagonal reaches
    the table, or the address space when that comes first. The vertical line is the address space.
    """
    page, size_2m, size_1g = numbers["PAGE_SZ"], numbers["SIZE_2M"], numbers["SIZE_1G"]
    slots, space, bound = numbers["TABLE_SLOTS"], numbers["NODE_SPACE"], numbers["BLOCKS_PER_RUN"]
    # 4K and 2M are frames retype makes. 1G is a block can_retype_large allows and the syscall does not pass.
    series = (
        (page, numbers["REACH_4K"], "#c45c26", "frame"),
        (size_2m, numbers["REACH_2M"], "#1f6aa5", "frame"),
        (size_1g, numbers["REACH_1G"], "#2a7f4f", "block"),
    )
    width, height = 760, 530
    left, right, top, plot_h = 78, 22, 32, 400
    plot_w = width - left - right
    plot_bottom = top + plot_h
    x_lo, x_hi = log2_of(page), log2_of(space)
    y_lo, y_hi = 0.0, max(20.0, math.ceil(log2_of(max(slots, bound))) + 2)

    def sx(x):
        return left + (x - x_lo) / (x_hi - x_lo) * plot_w

    def sy(y):
        return top + (y_hi - y) / (y_hi - y_lo) * plot_h

    chart = Chart(width, height)
    chart.rect(0, 0, width, height, "#ffffff")
    tick = math.ceil(x_lo / 6) * 6
    while tick <= x_hi:
        chart.line(sx(tick), top, sx(tick), plot_bottom, "#ececec", width=1)
        chart.text(sx(tick), plot_bottom + 16, bytes_label(1 << int(tick)), size=11, anchor="middle", fill="#555555")
        tick += 6
    y_tick = 0
    while y_tick <= y_hi:
        chart.line(left, sy(y_tick), left + plot_w, sy(y_tick), "#ececec", width=1)
        chart.text(left - 8, sy(y_tick) + 4, count_label(1 << y_tick), size=11, anchor="end", fill="#555555")
        y_tick += 4
    chart.line(left, plot_bottom, left + plot_w, plot_bottom, "#444444", width=1)
    chart.line(left, top, left, plot_bottom, "#444444", width=1)
    for size, _, color, _ in series:
        lg = log2_of(size)
        x0, x1 = max(x_lo, lg + y_lo), min(x_hi, lg + y_hi)
        chart.line(sx(x0), sy(x0 - lg), sx(x1), sy(x1 - lg), color, width=2)
    table_y, bound_y = log2_of(slots), log2_of(bound)
    chart.line(sx(x_lo), sy(table_y), sx(x_hi), sy(table_y), "#222222", width=1.25)
    chart.text(sx(x_lo) + 6, sy(table_y) - 6, f"{slots:,} slots, the table", size=12, anchor="start")
    chart.line(sx(x_lo), sy(bound_y), sx(x_hi), sy(bound_y), "#6a3d9a", width=1.5, dash="6 4")
    chart.text(sx(x_hi) - 6, sy(bound_y) - 6, f"at most {bound}, one run as untyped blocks",
               size=12, anchor="end", fill="#6a3d9a")
    chart.line(sx(x_hi), sy(y_lo), sx(x_hi), sy(y_hi), "#888888", width=1, dash="2 3")
    chart.text(sx(x_hi) - 6, sy(y_hi) + 14, "address space", size=11, anchor="end", fill="#666666")
    for size, reached, color, _ in series:
        assert reached % size == 0
        rx, ry = log2_of(reached), log2_of(reached // size)
        chart.circle(sx(rx), sy(ry), 4.5, color)
        anchor = "end" if rx > x_hi - 4 else "middle"
        chart.text(sx(rx) - (6 if anchor == "end" else 0), sy(ry) - 12, bytes_label(reached),
                   size=11, anchor=anchor, fill=color)
    chart.text(left + plot_w, plot_bottom + 36, "memory one process holds", size=12, anchor="end", fill="#222222")
    chart.text(left, top - 10, "slots", size=12, anchor="start", fill="#222222")
    for i, (size, _, color, kind) in enumerate(series):
        x = left + plot_w * i / 3
        chart.line(x, height - 28, x + 22, height - 28, color, width=3)
        chart.text(x + 28, height - 24, f"one {bytes_label(size)} {kind}", size=12, anchor="start", fill=color)
    def reached_at(size, reached):
        where = "the table" if reached < space else "the address space"
        return f"{bytes_label(size)} reaches {where} at {bytes_label(reached)}"

    desc = (
        f"Both axes are logarithmic. One capability per block. "
        f"{reached_at(page, numbers['REACH_4K'])}; {reached_at(size_2m, numbers['REACH_2M'])}; "
        f"{reached_at(size_1g, numbers['REACH_1G'])}. The table holds {slots:,} slots. "
        f"One run decomposes into at most {bound} untyped blocks. The address space is {bytes_label(space)}."
    )
    return chart.document("Slots one process needs against the memory it holds", desc)


def table_growth_svg(numbers):
    """The slot capacity of each way of growing the table, and the memory that capacity holds.

    One column per design, on a logarithmic axis of slots. Under the column is the smallest table,
    the full table, and the memory one block per slot reaches at each block size, capped at the
    address space. The same reach a full table has in slots_versus_memory_svg.
    """
    page, size_2m, size_1g = numbers["PAGE_SZ"], numbers["SIZE_2M"], numbers["SIZE_1G"]
    space = numbers["NODE_SPACE"]
    designs = (
        ("today", numbers["TABLE_SLOTS"], numbers["LEAF_BYTES"], numbers["TABLE_BYTES"], "#222222", "#e6e6e6"),
        ("root pages", numbers["ROOTS_SLOTS"], numbers["LEAF_BYTES"], numbers["ROOTS_FULL"], "#1f6aa5", "#d4e4f2"),
        ("doubled leaf", numbers["DOUBLE_TABLE_SLOTS"], numbers["DOUBLE_LEAF_BYTES"], numbers["DOUBLE_FULL"], "#2a7f4f", "#d5eadc"),
        ("large page", numbers["BIG_TABLE_SLOTS"], numbers["BIG_LEAF_BYTES"], numbers["BIG_FULL"], "#c45c26", "#f6ddd0"),
        ("third level", numbers["THIRD_SLOTS"], numbers["THIRD_SMALLEST"], numbers["THIRD_FULL"], "#6a3d9a", "#e6d9f0"),
    )
    sizes = (page, size_2m, size_1g)
    width, height = 780, 380
    left, right, top, plot_h = 58, 16, 28, 220
    plot_w = width - left - right
    plot_bottom = top + plot_h
    caps = [slots for _, slots, _, _, _, _ in designs]
    y_lo = math.floor(log2_of(min(caps))) - 1
    y_hi = math.ceil(log2_of(max(caps))) + 2

    def sy(y):
        return top + (y_hi - y) / (y_hi - y_lo) * plot_h

    chart = Chart(width, height)
    chart.rect(0, 0, width, height, "#ffffff")
    y_tick = math.ceil(y_lo / 2) * 2
    while y_tick <= y_hi:
        chart.line(left, sy(y_tick), left + plot_w, sy(y_tick), "#ececec", width=1)
        chart.text(left - 8, sy(y_tick) + 4, count_label(1 << y_tick), size=11, anchor="end", fill="#555555")
        y_tick += 2
    chart.line(left, plot_bottom, left + plot_w, plot_bottom, "#444444", width=1)
    chart.line(left, top, left, plot_bottom, "#444444", width=1)
    chart.text(left, top - 10, "slots", size=12, anchor="start", fill="#222222")
    described = []
    gap = plot_w / len(designs)
    for index, (name, slots, small, full, color, light) in enumerate(designs):
        cx = left + gap * (index + 0.5)
        dot = sy(log2_of(slots))
        chart.rect(cx - 16, dot, 32, plot_bottom - dot, light)
        chart.circle(cx, dot, 4.5, color)
        chart.text(cx, dot - 10, f"{slots:,}", size=11, anchor="middle", fill=color)
        chart.text(cx, plot_bottom + 18, name, size=12, anchor="middle", fill=color)
        chart.text(cx, plot_bottom + 36, f"smallest {bytes_label(small)}", size=10, anchor="middle", fill="#333333")
        chart.text(cx, plot_bottom + 50, f"full {bytes_label(full)}", size=10, anchor="middle", fill="#333333")
        reaches = []
        for step, size in enumerate(sizes):
            held = min(slots * size, space)
            reaches.append(f"{bytes_label(size)} reaches {bytes_label(held)}")
            chart.text(cx, plot_bottom + 70 + 14 * step, f"{bytes_label(size)}  {bytes_label(held)}",
                       size=10, anchor="middle", fill="#555555")
        described.append(
            f"{name}: {slots:,} slots, smallest {bytes_label(small)}, full {bytes_label(full)}; "
            + "; ".join(reaches)
        )
    return chart.document(
        "Capacity of each way of growing the capability table",
        "Each column is one design, on a logarithmic axis of slots. " + " ".join(described),
    )


# A plot a template may name. Each function takes the numbers values() returns and gives the SVG text.
PLOTS = {
    "slots-versus-memory.svg": slots_versus_memory_svg,
    "table-growth.svg": table_growth_svg,
}

SVG_REF = re.compile(r"\((?:\./)?([A-Za-z0-9][A-Za-z0-9._-]*)\.svg\)")


def referenced_plots(source, text, plots):
    """The plot files a template's markdown images name, in order, refusing one this script has not."""
    names = []
    for number, line in enumerate(text.splitlines(), 1):
        for match in SVG_REF.finditer(line):
            name = f"{match.group(1)}.svg"
            if name not in plots:
                raise Refused(f"{source}:{number}: {name} is not a plot tools/faq.py writes")
            names.append(name)
    return names


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


def outputs(root, table=CONSTANTS, derived=DERIVED, plots=PLOTS):
    """Every file docs/faq should hold outside src, by its path under docs/faq, with its text."""
    templates = sorted((root / SOURCES).glob("*.md")) if (root / SOURCES).is_dir() else []
    if not templates:
        return {}
    numbers = values(root, table, derived)
    result, entries, needed = {}, [], []
    for template in templates:
        source = template.relative_to(root).as_posix()
        text = template.read_text(encoding="utf-8")
        result[template.name] = render(source, text, numbers)
        entries.append((template.name, first_heading(source, text)))
        needed.extend(referenced_plots(source, text, plots))
    result[INDEX] = index(entries)
    for name in dict.fromkeys(needed):
        result[name] = plots[name](numbers)
    return result


def present(root):
    """Every file docs/faq holds outside src, by its path under docs/faq."""
    faq = root / FAQ
    if not faq.is_dir():
        return set()
    return {p.relative_to(faq).as_posix() for p in faq.rglob("*")
            if p.is_file() and SOURCES.name not in p.relative_to(faq).parts[:1]}


def differences(root, table=CONSTANTS, derived=DERIVED, plots=PLOTS):
    """Each output that is stale, missing or produced by no template, one line each."""
    wanted = outputs(root, table, derived, plots)
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


def write(root, table=CONSTANTS, derived=DERIVED, plots=PLOTS):
    wanted = outputs(root, table, derived, plots)
    for name in present(root) - set(wanted):
        (root / FAQ / name).unlink()
    for name, text in wanted.items():
        path = root / FAQ / name
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text(encoding="utf-8") != text:
            path.write_text(text, encoding="utf-8")
    return sorted(wanted)


class Tests(unittest.TestCase):
    # The toy table has none of the names DERIVED reads, so a call on it passes an empty derived map.
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
        got = values(REPO)
        self.assertEqual(set(got), set(CONSTANTS) | set(DERIVED))
        self.assertEqual(got["LEAF_SLOTS"], got["NODES_PER_PAGE"] - 1)
        self.assertEqual(got["ENTRIES"], 1 << got["INDEX_BITS"])
        self.assertEqual(got["TABLE_INDICES"], got["ROOT_ENTRIES"] * got["NODES_PER_PAGE"])
        self.assertEqual(got["TABLE_SLOTS"], got["TABLE_INDICES"] - got["ROOT_ENTRIES"])
        self.assertEqual(got["ONE_G_ORDER"], 2 * got["INDEX_BITS"])
        self.assertEqual(got["PAGES_PER_2M"], got["ENTRIES"])
        self.assertEqual(got["PAGES_PER_1G"], got["ENTRIES"] * got["ENTRIES"])
        self.assertEqual(got["SIZE_2M"], got["PAGE_SZ"] * got["PAGES_PER_2M"])
        self.assertEqual(got["SIZE_1G"], got["PAGE_SZ"] * got["PAGES_PER_1G"])

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

    def test_a_referenced_plot_is_written_and_an_unknown_one_is_refused(self):
        def plot(numbers):
            return f"<svg>{numbers['PAGE']}</svg>\n"

        root = self.tree({"a.md": "# A\n\n![memory](./slots.svg)\n"})
        out = outputs(root, self.TABLE, {}, {"slots.svg": plot})
        self.assertEqual(out["slots.svg"], "<svg>4096</svg>\n")
        self.assertIn("![memory](./slots.svg)", out["a.md"])
        root = self.tree({"a.md": "# A\n\n![memory](./missing.svg)\n"})
        with self.assertRaisesRegex(Refused, r"docs/faq/src/a\.md:3: missing\.svg"):
            outputs(root, self.TABLE, {}, {"slots.svg": plot})

    def test_check_holds_a_plot_to_what_the_template_references(self):
        def plot(numbers):
            return "<svg>ok</svg>\n"

        root = self.tree({"a.md": "# A\n\n![memory](slots.svg)\n"})
        plots = {"slots.svg": plot}
        self.assertEqual(differences(root, self.TABLE, {}, plots),
                         ["docs/faq/README.md: missing", "docs/faq/a.md: missing", "docs/faq/slots.svg: missing"])
        write(root, self.TABLE, {}, plots)
        self.assertEqual(differences(root, self.TABLE, {}, plots), [])
        (root / FAQ / "slots.svg").write_text("stale\n")
        self.assertEqual(differences(root, self.TABLE, {}, plots), ["docs/faq/slots.svg: stale"])

    def test_the_reaches_follow_the_table_the_frame_sizes_and_the_address_space(self):
        v = values(REPO)
        slots = v["TABLE_SLOTS"]
        self.assertEqual(v["SIZE_2M"], v["PAGE_SZ"] << v["INDEX_BITS"])
        self.assertEqual(v["SIZE_1G"], v["PAGE_SZ"] << v["ONE_G_ORDER"])
        self.assertEqual(v["PAGE_SZ"] << v["MAX_ORDER"], v["NODE_SPACE"])
        self.assertEqual(v["NODE_SPACE"] & (v["NODE_SPACE"] - 1), 0)
        self.assertEqual(v["ADDRESS_BITS"], v["NODE_SPACE"].bit_length() - 1)
        for size, reach_name in (("PAGE_SZ", "REACH_4K"), ("SIZE_2M", "REACH_2M"), ("SIZE_1G", "REACH_1G")):
            self.assertEqual(v[reach_name], min(slots * v[size], v["NODE_SPACE"]))
            self.assertLess(v[reach_name], v["NODE_SPACE"])
        self.assertEqual(v["BLOCKS_PER_RUN"], 2 * (v["MAX_ORDER"] + 1))
        self.assertLess(v["BLOCKS_PER_RUN"], slots)
        operation = (REPO / "kernel/verified/capability/operation.rs").read_text(encoding="utf-8")
        retype = (REPO / "kernel/verified/capability/retype.rs").read_text(encoding="utf-8")
        self.assertIn(f"order == {v['INDEX_BITS']} || order == {v['ONE_G_ORDER']}", retype)
        large = [line.strip() for line in operation.splitlines()
                 if "RETYPE_LARGE_FRAME" in line and "can_retype_large" in line]
        self.assertEqual(large, [
            "||| frame.argument(1) == RETYPE_LARGE_FRAME && self.can_retype_large("
            f"root, from, frame.argument(3) as usize, base, {v['INDEX_BITS']})"
        ])
        self.assertIn(f"(order == {v['INDEX_BITS']} || order == {v['ONE_G_ORDER']})", operation)
        decompose = (REPO / "kernel/verified/capability/decompose.rs").read_text(encoding="utf-8")
        self.assertIn("run_blocks(start, n, cap).len() <= 2 * (MAX_ORDER + 1)", decompose)

    def test_the_slots_plot_names_the_table_and_each_reach_and_carries_no_script(self):
        v = values(REPO)
        svg = slots_versus_memory_svg(v)
        self.assertIn(f"{v['TABLE_SLOTS']:,}", svg)
        self.assertIn(str(v["BLOCKS_PER_RUN"]), svg)
        for reach_name in ("REACH_4K", "REACH_2M", "REACH_1G"):
            self.assertIn(bytes_label(v[reach_name]), svg)
        self.assertIn("one 4 KiB frame", svg)
        self.assertIn("one 1 GiB block", svg)
        self.assertNotRegex(svg, r"<\s*/?\s*(script|style|html|iframe)\b")
        self.assertEqual(svg, slots_versus_memory_svg(v))

    def test_bytes_label_uses_the_largest_binary_unit_that_divides(self):
        self.assertEqual(bytes_label(4096), "4 KiB")
        self.assertEqual(bytes_label(1 << 21), "2 MiB")
        self.assertEqual(bytes_label(1 << 30), "1 GiB")
        self.assertEqual(bytes_label(65024 << 30), "65,024 GiB")
        self.assertEqual(bytes_label(3), "3 B")

    def test_the_growth_explainer_types_no_number_and_renders_each_design(self):
        text = (REPO / SOURCES / "growing-the-table.md").read_text(encoding="utf-8")
        # A digit inside an item's name, such as SIZE_2M, is the name. A typed number stands alone.
        self.assertIsNone(re.search(r"(?<![A-Za-z0-9_])\d", PLACEHOLDER.sub("", text)))
        out = outputs(REPO)
        page = out["growing-the-table.md"]
        v = values(REPO)
        for name, spec in PLACEHOLDER.findall(text):
            self.assertIn(format(v[name], spec or ""), page)
        self.assertEqual(v["PAGE_SZ"] // v["ENTRIES"], 8)
        self.assertEqual(v["ROOT_ENTRIES"], v["ENTRIES"])
        self.assertEqual(v["PAGE_SZ"] // v["NODES_PER_PAGE"], 32)
        self.assertEqual(v["INDEX_FIELD_COUNT"], v["POSITION_INDEX_MASK"] + 1)
        self.assertEqual(v["INDEX_FIELD_COUNT"], v["TABLE_INDICES"])
        self.assertEqual(v["INDEX_FIELD_BITS"], (v["POSITION_INDEX_MASK"] + 1).bit_length() - 1)
        self.assertEqual(v["POSITION_THROUGH_SHIFT"], v["INDEX_FIELD_BITS"])
        self.assertEqual(v["SPARE_PAGES"], v["SPACE_ROOT_PAGE"] - v["PROCESS_RECORD_PAGE"] - 1)
        self.assertEqual(v["ROOT_PAGES"], v["PROCESS_RECORD_PAGE"] + v["SPARE_PAGES"])
        self.assertEqual(v["LEAF_PAGES"], v["LEAF_BYTES"] // v["PAGE_SZ"])
        self.assertEqual(v["TABLE_BYTES"], v["ROOT_ENTRIES"] * v["LEAF_BYTES"])
        self.assertEqual(v["ROOTS_SLOTS"], v["ROOT_PAGES"] * v["ROOT_ENTRIES"] * v["LEAF_SLOTS"])
        self.assertEqual(v["ROOTS_FULL"], v["ROOT_PAGES"] * v["ROOT_ENTRIES"] * v["LEAF_BYTES"])
        self.assertEqual(v["ROOTS_INDICES"], v["ROOT_PAGES"] * v["ROOT_ENTRIES"] * v["NODES_PER_PAGE"])
        self.assertEqual(v["DOUBLE_NODE_PAGES"], v["LEAF_PAGES"])
        self.assertEqual(v["DOUBLE_PAGES"], 2 * v["LEAF_PAGES"])
        self.assertEqual(v["DOUBLE_NODES"], v["DOUBLE_NODE_PAGES"] * v["NODES_PER_PAGE"])
        self.assertEqual(v["DOUBLE_SLOTS_PER"], v["DOUBLE_NODES"] - 1)
        self.assertEqual(v["DOUBLE_TABLE_SLOTS"], v["ROOT_ENTRIES"] * v["DOUBLE_SLOTS_PER"])
        self.assertEqual(v["DOUBLE_LEAF_BYTES"], v["DOUBLE_PAGES"] * v["PAGE_SZ"])
        self.assertEqual(v["DOUBLE_FULL"], v["ROOT_ENTRIES"] * v["DOUBLE_LEAF_BYTES"])
        self.assertEqual(v["DOUBLE_INDICES"], v["ROOT_ENTRIES"] * v["DOUBLE_NODES"])
        self.assertEqual(v["BIG_NODES"], (v["SIZE_2M"] // v["PAGE_SZ"]) * v["NODES_PER_PAGE"])
        self.assertEqual(v["BIG_SLOTS_PER"], v["BIG_NODES"] - 1)
        self.assertEqual(v["BIG_TABLE_SLOTS"], v["ROOT_ENTRIES"] * v["BIG_SLOTS_PER"])
        self.assertEqual(v["BIG_LEAF_BYTES"], 2 * v["SIZE_2M"])
        self.assertEqual(v["BIG_FULL"], v["ROOT_ENTRIES"] * v["BIG_LEAF_BYTES"])
        self.assertEqual(v["BIG_INDICES"], v["ROOT_ENTRIES"] * v["BIG_NODES"])
        self.assertEqual(v["THIRD_SLOTS"], v["ROOT_ENTRIES"] * v["ENTRIES"] * v["LEAF_SLOTS"])
        self.assertEqual(v["THIRD_SMALLEST"], v["PAGE_SZ"] + v["LEAF_BYTES"])
        self.assertEqual(v["THIRD_LEAVES_BYTES"], v["ROOT_ENTRIES"] * v["ENTRIES"] * v["LEAF_BYTES"])
        self.assertEqual(v["THIRD_MIDDLE_BYTES"], v["ROOT_ENTRIES"] * v["PAGE_SZ"])
        self.assertEqual(v["THIRD_FULL"], v["THIRD_LEAVES_BYTES"] + v["THIRD_MIDDLE_BYTES"])
        self.assertEqual(v["THIRD_INDICES"], v["ROOT_ENTRIES"] * v["ENTRIES"] * v["NODES_PER_PAGE"])
        self.assertNotIn(v["DOUBLE_PAGES"], (1, v["LEAF_PAGES"], v["PROCESS_BYTES"] // v["PAGE_SZ"]))
        process = (REPO / "kernel/verified/capability/process.rs").read_text(encoding="utf-8")
        for page_index in range(v["PROCESS_RECORD_PAGE"] + 1, v["SPACE_ROOT_PAGE"]):
            self.assertIn(f"spare_kept(processes, p, {page_index})", process)
        block = (REPO / "kernel/verified/capability/block.rs").read_text(encoding="utf-8")
        self.assertIn("order == 0 || order == 1 || order == 3", block)
        self.assertIn("if order == 0 { 1 } else if order == 1 { 2 } else { 8 }", block)
        self.assertIn("block cannot write its page entries in a bounded step", block)
        self.assertEqual(v["PROCESS_PAGES"], v["PROCESS_BYTES"] // v["PAGE_SZ"])
        self.assertEqual(v["LEAF_PAGES"], 2)
        self.assertEqual(v["PROCESS_PAGES"], 8)
        self.assertEqual(v["DOUBLE_PAGES"], 4)
        table = (REPO / "kernel/verified/capability/table.rs").read_text(encoding="utf-8")
        self.assertIn("32 bytes", table)
        self.assertEqual(v["PAGE_SZ"] // v["NODES_PER_PAGE"], 32)
        for name in ("TABLE_SLOTS", "ROOTS_SLOTS", "DOUBLE_TABLE_SLOTS", "BIG_TABLE_SLOTS", "THIRD_SLOTS",
                     "LEAF_BYTES", "TABLE_BYTES", "ROOTS_FULL", "DOUBLE_LEAF_BYTES", "DOUBLE_FULL",
                     "BIG_LEAF_BYTES", "BIG_FULL", "THIRD_SMALLEST", "THIRD_FULL", "THIRD_LEAVES_BYTES",
                     "THIRD_MIDDLE_BYTES", "TABLE_INDICES", "ROOTS_INDICES", "DOUBLE_INDICES",
                     "BIG_INDICES", "THIRD_INDICES", "INDEX_FIELD_COUNT", "SPARE_PAGES", "ROOT_PAGES",
                     "DOUBLE_SLOTS_PER", "BIG_SLOTS_PER", "ENTRIES", "LEAF_SLOTS"):
            self.assertIn(f"{v[name]:,}", page)
        for name in ("ROOTS_INDICES", "DOUBLE_INDICES", "BIG_INDICES", "THIRD_INDICES"):
            self.assertGreater(v[name], v["INDEX_FIELD_COUNT"])
        self.assertIn("(./table-growth.svg)", page)
        self.assertNotRegex(page, r"<\s*/?\s*(svg|script|html|iframe|style)\b")
        svg = out["table-growth.svg"]
        for name in ("TABLE_SLOTS", "ROOTS_SLOTS", "DOUBLE_TABLE_SLOTS", "BIG_TABLE_SLOTS", "THIRD_SLOTS"):
            self.assertIn(f"{v[name]:,}", svg)
        for name in ("LEAF_BYTES", "TABLE_BYTES", "ROOTS_FULL", "DOUBLE_LEAF_BYTES", "DOUBLE_FULL",
                     "BIG_LEAF_BYTES", "BIG_FULL", "THIRD_SMALLEST", "THIRD_FULL"):
            self.assertIn(bytes_label(v[name]), svg)
        self.assertNotRegex(svg, r"<\s*/?\s*(script|style|html|iframe)\b")
        self.assertEqual(svg, table_growth_svg(v))
        self.assertIn("Growing the capability table, and what each way costs", out["README.md"])

    def test_the_budget_explainer_types_no_number_and_renders_its_reaches(self):
        text = (REPO / SOURCES / "where-the-budget-runs-out.md").read_text(encoding="utf-8")
        # A digit inside an item's name, such as SIZE_2M, is the name. A typed number stands alone.
        self.assertIsNone(re.search(r"(?<![A-Za-z0-9_])\d", PLACEHOLDER.sub("", text)))
        out = outputs(REPO)
        page = out["where-the-budget-runs-out.md"]
        v = values(REPO)
        for name in ("TABLE_SLOTS", "REACH_4K", "REACH_2M", "REACH_1G", "NODE_SPACE", "PAGE_SZ", "SIZE_2M", "SIZE_1G"):
            self.assertIn(f"{v[name]:,}", page)
        self.assertIn(str(v["BLOCKS_PER_RUN"]), page)
        self.assertIn(str(v["INDEX_BITS"]), page)
        self.assertIn(str(v["ONE_G_ORDER"]), page)
        self.assertIn(str(v["LEAF_SLOTS"]), page)
        self.assertIn(str(v["ADDRESS_BITS"]), page)
        self.assertIn(str(v["MAX_ORDER"]), page)
        self.assertIn("(./slots-versus-memory.svg)", page)
        self.assertNotRegex(page, r"<\s*/?\s*(svg|script|html|iframe|style)\b")
        self.assertIn(bytes_label(v["REACH_4K"]), out["slots-versus-memory.svg"])
        self.assertIn("Where a process's slot budget runs out", out["README.md"])

    def test_the_frame_explainer_types_no_number_and_states_each_order(self):
        text = (REPO / SOURCES / "frame-backs-many-mappings.md").read_text(encoding="utf-8")
        # A digit inside an item's name, such as SIZE_2M, is the name. A typed number stands alone.
        self.assertIsNone(re.search(r"(?<![A-Za-z0-9_])\d", PLACEHOLDER.sub("", text)))
        out = outputs(REPO)
        page = out["frame-backs-many-mappings.md"]
        v = values(REPO)
        for name, spec in PLACEHOLDER.findall(text):
            self.assertIn(format(v[name], spec or ""), page)
        self.assertEqual(1 << v["INDEX_BITS"], v["PAGES_PER_2M"])
        self.assertEqual(v["PAGES_PER_1G"], v["ENTRIES"] * v["ENTRIES"])
        self.assertEqual(v["PAGES_PER_1G"] // v["PAGES_PER_2M"], v["ENTRIES"])
        self.assertEqual(v["ONE_G_ORDER"], 2 * v["INDEX_BITS"])
        self.assertEqual(v["SIZE_2M"], v["PAGE_SZ"] * v["PAGES_PER_2M"])
        self.assertEqual(v["SIZE_1G"], v["PAGE_SZ"] * v["PAGES_PER_1G"])
        self.assertEqual(v["TABLE_ORDER"], 3)
        self.assertEqual((v["TABLE_PAGE_BYTES"] // v["PAGE_SZ"]).bit_length() - 1, v["TABLE_ORDER"])
        for name in ("PAGE_SZ", "SIZE_2M", "SIZE_1G", "PAGES_PER_1G", "TABLE_PAGE_BYTES"):
            self.assertIn(f"{v[name]:,}", page)
        for name in ("PAGES_PER_2M", "INDEX_BITS", "ONE_G_ORDER", "ENTRIES", "TABLE_ORDER", "IMAGE_ORDER"):
            self.assertIn(str(v[name]), page)
        self.assertIn("backs one mapping of", page)
        self.assertIn("backs no mapping of", page)
        self.assertIn("```mermaid", page)
        self.assertIn("flowchart TD", page)
        self.assertNotRegex(page, r"<\s*/?\s*(svg|script|html|iframe|style)\b")
        map_rs = (REPO / "kernel/verified/capability/map.rs").read_text(encoding="utf-8")
        self.assertIn("if (level != 1 && level != 2) || !entry_named(va, level)", map_rs)
        self.assertIn(
            f"if cap.order != {v['INDEX_BITS']} && cap.order != {v['ONE_G_ORDER']}", map_rs)
        self.assertIn("page % PAGES_PER_2M != 0", map_rs)
        self.assertIn(
            "(page as int) * PAGE_SZ < block_bytes(self.payload_of(f).order)", map_rs)
        self.assertIn("if level == 1 {\n        PAGE_SZ as u64", map_rs)
        self.assertIn("} else if level == 2 {\n        SIZE_2M as u64", map_rs)
        self.assertIn("} else if level == 3 {\n        SIZE_1G as u64", map_rs)
        operation = (REPO / "kernel/verified/capability/operation.rs").read_text(encoding="utf-8")
        self.assertIn(
            "self.map_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), "
            "frame.argument(3) as usize, frame.argument(4) as usize)",
            operation)
        retype = (REPO / "kernel/verified/capability/retype.rs").read_text(encoding="utf-8")
        self.assertIn("self.can_retype_block(root, from, to, base, 0)", retype)
        space = (REPO / "kernel/verified/capability/space.rs").read_text(encoding="utf-8")
        self.assertIn(
            "pub fn retype_table_page(&mut self, root: usize, from: usize, base: usize, level: usize,",
            space)
        self.assertIn("assert(block_bytes(3) == TABLE_PAGE_BYTES);", space)
        self.assertIn("How one frame capability backs many mappings", out["README.md"])

    def test_the_block_explainer_types_no_number_and_names_one_slot(self):
        text = (REPO / SOURCES / "slot-names-a-block.md").read_text(encoding="utf-8")
        # A digit inside an item's name, such as SIZE_2M, is the name. A typed number stands alone.
        self.assertIsNone(re.search(r"(?<![A-Za-z0-9_])\d", PLACEHOLDER.sub("", text)))
        v = values(REPO)
        self.assertEqual(v["PAGE_SZ"] % v["NODES_PER_PAGE"], 0)
        self.assertEqual(v["ENTRY_BYTES"], v["PAGE_SZ"] // v["NODES_PER_PAGE"])
        self.assertEqual(v["ENTRY_BYTES"] * v["NODES_PER_PAGE"], v["PAGE_SZ"])
        self.assertEqual(v["PAGE_SZ"] << v["MAX_ORDER"], v["NODE_SPACE"])
        self.assertEqual(v["TABLE_SLOTS"], v["ROOT_ENTRIES"] * v["LEAF_SLOTS"])
        self.assertEqual(v["TABLE_INDICES"], v["ROOT_ENTRIES"] * v["NODES_PER_PAGE"])
        out = outputs(REPO)
        page = out["slot-names-a-block.md"]
        for name, spec in PLACEHOLDER.findall(text):
            self.assertIn(format(v[name], spec or ""), page)
        for name in ("TABLE_SLOTS", "TABLE_INDICES", "LEAF_BYTES", "PAGE_SZ", "SIZE_2M", "SIZE_1G", "NODE_SPACE"):
            self.assertIn(f"{v[name]:,}", page)
        for name in ("ENTRY_BYTES", "LEAF_SLOTS", "NODES_PER_PAGE", "ROOT_ENTRIES", "LEAF_PAGES",
                     "MAX_ORDER", "INDEX_BITS", "ONE_G_ORDER", "ADDRESS_BITS"):
            self.assertIn(str(v[name]), page)
        self.assertIn("```mermaid", page)
        self.assertIn("flowchart TD", page)
        self.assertNotRegex(page, r"<\s*/?\s*(svg|script|html|iframe|style)\b")
        for cite in ("design/process-holds-capabilities/", "design/capability-names-a-block/",
                     "design/teardown-driven-by-retype/", "design/revoke-by-depth-first-list/"):
            self.assertIn(cite, text)
        table = (REPO / "kernel/verified/capability/table.rs").read_text(encoding="utf-8")
        self.assertIn(f"pub const MAX_ORDER: u8 = {v['MAX_ORDER']};", table)
        self.assertIn("p.order <= MAX_ORDER", table)
        self.assertIn("!(k is Device) && !(k is Console) && !(k is Power) && !(k is Core)", table)
        self.assertIn("Some((leaf + slot, *payloads.entries.get(slot)))", table)
        self.assertIn("PPtr::<PayloadPage>::from_usize(leaf + PAGE_SZ)", table)
        self.assertIn("final(self).leaf(root, r) == NO_LEAF", table)
        layouts = (REPO / "kernel/verified/layouts.rs").read_text(encoding="utf-8")
        self.assertIn(f"global layout NodePage is size == {v['PAGE_SZ']}, align == 8;", layouts)
        self.assertIn(f"global layout PayloadPage is size == {v['PAGE_SZ']}, align == 8;", layouts)
        retype = (REPO / "kernel/verified/capability/retype.rs").read_text(encoding="utf-8")
        self.assertIn("self.can_retype_block(root, from, to, base, 0)", retype)
        self.assertIn(f"order == {v['INDEX_BITS']} || order == {v['ONE_G_ORDER']}", retype)
        operation = (REPO / "kernel/verified/capability/operation.rs").read_text(encoding="utf-8")
        self.assertIn(
            "||| frame.argument(1) == RETYPE_LARGE_FRAME && self.can_retype_large("
            f"root, from, frame.argument(3) as usize, base, {v['INDEX_BITS']})",
            operation)
        self.assertIn(
            "self.retype_large_frame(root, frame.slot() as usize, frame.argument(3) as usize, "
            f"frame.argument(2) as usize, {v['INDEX_BITS']}, Tracked(steps))",
            operation)
        derive = (REPO / "kernel/verified/capability/derive.rs").read_text(encoding="utf-8")
        self.assertIn("order <= parent.order", derive)
        self.assertIn("parent.kind is Untyped || parent.kind is Frame", derive)
        self.assertIn("How one capability slot names a block of pages", out["README.md"])


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
