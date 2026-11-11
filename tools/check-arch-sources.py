#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Check that the kernel's sources outside kernel/src/arch name no x86 item and hold no inline
assembly.

The rest of kernel/src builds for every target and reaches the target only through the arch
module's names (design/arch-module/ item 5). A line names x86 when one of its lower-case words,
the runs of ASCII letters and digits between its punctuation, is one of an x86 kernel's
instructions, registers or descriptor tables, or when it holds one of those names capitalised as
part of a type's name, or 'asm!'. A line that names target_arch is the selection itself and passes.

usage: tools/check-arch-sources.py           (the tree)
       tools/check-arch-sources.py --test    (this script's own tests)
"""
import re
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
SOURCES = "kernel/src"
ARCH = "arch"
# Fewer shared sources than this means the scan looked in the wrong place.
LEAST_SOURCES = 10

# What only an x86 kernel names: its instructions, registers and descriptor tables, as the
# lower-case words between a source's punctuation.
X86_WORDS = frozenset([
    "x86", "rdtsc", "tsc", "msr", "gdt", "tss", "idt", "ist", "cr0", "cr3", "cr4", "pcid", "pcide",
    "rsp", "rip", "rax", "rdi", "rsi", "apic", "ioapic", "iopl", "sysret", "lgdt", "hlt",
])
# The same names as the capitalised parts of a type's name, and inline assembly for any target.
ARCH_ONLY_TEXT = ("Gdt", "Tss", "Idt", "Ist", "Apic", "Msr", "asm!")
SELECTION = "target_arch"
WORD = re.compile(r"[a-z0-9]+")


def named(path, source):
    """Each x86 name one file's lines hold, as 'path:line: name', in the order of its lines."""
    found = []
    for number, line in enumerate(source.splitlines(), 1):
        if SELECTION in line:
            continue
        words = [word for word in WORD.findall(line.lower()) if word in X86_WORDS]
        texts = [text for text in ARCH_ONLY_TEXT if text in line]
        found.extend(f"{path}:{number}: {name}" for name in words + texts)
    return found


def sources(directory, skip):
    """The Rust sources under a directory, outside the directory 'skip'."""
    for entry in sorted(directory.iterdir()):
        if entry.is_dir():
            if entry != skip:
                yield from sources(entry, skip)
        elif entry.suffix == ".rs":
            yield entry


def scan_tree(repo):
    """The number of shared sources under the kernel's source directory and each x86 name they
    hold, with paths from the repository root."""
    root = repo / SOURCES
    files = list(sources(root, root / ARCH))
    found = []
    for file in files:
        found.extend(named(file.relative_to(repo).as_posix(), file.read_text(encoding="utf-8")))
    return len(files), found


def main(args):
    if args:
        print(__doc__.split("usage: ")[1], file=sys.stderr)
        return 2
    count, found = scan_tree(REPO)
    if count <= LEAST_SOURCES:
        print(f"found only {count} shared sources under {SOURCES}", file=sys.stderr)
        return 1
    for line in found:
        print(f"{line}: x86 named outside {SOURCES}/{ARCH}", file=sys.stderr)
    if found:
        return 1
    print(f"{count} sources under {SOURCES} outside {ARCH}/ name no x86 and hold no inline assembly")
    return 0


class Tests(unittest.TestCase):
    def test_a_source_that_names_x86_fails_with_where_it_is(self):
        source = "use core::fmt;\nlet t = rdtsc();\nfn f(table: &Gdt) {}\n"
        self.assertEqual(named("cpu.rs", source), ["cpu.rs:2: rdtsc", "cpu.rs:3: gdt", "cpu.rs:3: Gdt"])

    def test_each_word_is_caught_between_punctuation(self):
        for word in sorted(X86_WORDS):
            with self.subTest(word=word):
                self.assertEqual(named("a.rs", f"x.{word.upper()}(1);\n"), [f"a.rs:1: {word}"])

    def test_inline_assembly_and_capitalised_names_are_caught(self):
        for text in ARCH_ONLY_TEXT:
            with self.subTest(text=text):
                self.assertIn(f"a.rs:1: {text}", named("a.rs", f"let v = {text}Frame;\n"))
        self.assertEqual(named("a.rs", "core::arch::asm!(\"wfi\");\n"), ["a.rs:1: asm!"])

    def test_a_word_inside_a_longer_word_is_not_named(self):
        self.assertEqual(named("a.rs", "let list = distance + x86ish + rips + tscale;\n"), [])

    def test_a_target_arch_line_passes(self):
        source = '#[cfg(target_arch = "x86_64")]\nlet x86 = 1;\n'
        self.assertEqual(named("a.rs", source), ["a.rs:2: x86"])

    def tree(self, files):
        """A repository in a temporary directory holding the sources by path under kernel/src."""
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        repo = Path(directory.name)
        for name, source in files.items():
            path = repo / SOURCES / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
        return repo

    def test_a_source_under_arch_is_not_scanned(self):
        repo = self.tree({
            "arch/x86_64/gdt.rs": "pub struct Gdt; asm!(\"lgdt\");\n",
            "arch/mod.rs": "let tsc = rdtsc();\n",
            "cpu.rs": "pub fn f() {}\n",
        })
        self.assertEqual(scan_tree(repo), (1, []))

    def test_the_tree_scan_names_each_shared_source_from_the_repository(self):
        repo = self.tree({
            "boot/mod.rs": "fn f() {}\nlet a = apic;\n",
            "lock.rs": "fn g() {}\n",
            "notes.txt": "x86\n",
            "archive/x.rs": "let msr = 1;\n",
        })
        self.assertEqual(scan_tree(repo), (3, [
            "kernel/src/archive/x.rs:1: msr",
            "kernel/src/boot/mod.rs:2: apic",
        ]))


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
