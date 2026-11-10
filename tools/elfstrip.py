#!/usr/bin/env python3
"""Drop .debug_* sections from ELF copies written into an initrd.

The binaries in target/ stay as the compiler wrote them: tools/gdb.py loads those files, and
tools/check-boot-stack.py disassembles main from the kernel there. Only the bytes concatenated into
the initrd are stripped. A file that is not an ELF, or that has no .debug_* section, is copied
unchanged.

usage: tools/elfstrip.py <elf> [<elf> ...]   (stripped bytes on stdout, concatenated)
       tools/elfstrip.py --test
"""
import struct
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True


def section_names(data):
    """Section names of an ELF64 file, or none when `data` has no section table."""
    if len(data) < 64 or data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        return []
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
    if e_shoff == 0 or e_shnum == 0 or e_shstrndx >= e_shnum or e_shentsize < 64:
        return []
    table_end = e_shoff + e_shentsize * e_shnum
    if table_end > len(data):
        return []
    str_header = e_shoff + e_shstrndx * e_shentsize
    sh_offset, sh_size = struct.unpack_from("<QQ", data, str_header + 24)
    if sh_offset + sh_size > len(data):
        return []
    strings = data[sh_offset:sh_offset + sh_size]
    names = []
    for index in range(e_shnum):
        name_off = struct.unpack_from("<I", data, e_shoff + index * e_shentsize)[0]
        if name_off >= len(strings):
            continue
        end = strings.find(b"\0", name_off)
        names.append(strings[name_off:end if end >= 0 else None].decode("ascii", "replace"))
    return names


def objcopy():
    """The pinned toolchain's llvm-objcopy (rust-toolchain.toml's llvm-tools), which takes an ELF of
    any architecture; the host's binutils objcopy takes only the host's."""
    tree = Path(__file__).resolve().parent.parent

    def rustc(*args):
        return subprocess.run(["rustc", *args], cwd=tree, check=True, text=True, capture_output=True).stdout

    host = next(line.split()[1] for line in rustc("-vV").splitlines() if line.startswith("host:"))
    return f"{rustc('--print', 'sysroot').strip()}/lib/rustlib/{host}/bin/llvm-objcopy"


def without_debug(path):
    """The bytes of `path` with .debug_* removed. `path` itself is not modified."""
    path = Path(path)
    data = path.read_bytes()
    if not any(name.startswith(".debug_") for name in section_names(data)):
        return data
    with tempfile.TemporaryDirectory() as directory:
        stripped = Path(directory) / "stripped"
        subprocess.run([objcopy(), "--strip-debug", str(path), str(stripped)], check=True)
        return stripped.read_bytes()


def write_initrd(destination, images):
    """Writes each image, debug sections removed, concatenated, and returns the byte count."""
    size = 0
    with open(destination, "wb") as initrd:
        for image in images:
            blob = without_debug(image)
            initrd.write(blob)
            size += len(blob)
    return size


EM_X86_64 = 62
EM_AARCH64 = 183


def elf_with_debug_section(machine=EM_X86_64):
    """A small ELF64 for `machine` whose section table names .debug_info, for the initrd tests."""
    shstr = b"\0.text\0.debug_info\0.shstrtab\0"
    text = b"\x90\x90\x90\x90"
    debug = b"DEBUGINF"
    text_off = 0x80
    debug_off = text_off + len(text)
    shstr_off = debug_off + len(debug)
    shoff = (shstr_off + len(shstr) + 7) & ~7

    def shdr(name, typ, flags, off, size):
        return struct.pack("<IIQQQQIIQQ", name, typ, flags, 0, off, size, 0, 0, 1, 0)

    sections = b"".join([
        shdr(0, 0, 0, 0, 0),
        shdr(1, 1, 6, text_off, len(text)),
        shdr(7, 1, 0, debug_off, len(debug)),
        shdr(19, 3, 0, shstr_off, len(shstr)),
    ])
    program = struct.pack("<IIQQQQQQ", 1, 5, text_off, 0, 0, len(text), len(text), 0x1000)
    header = struct.pack("<16sHHIQQQIHHHHHH",
                         b"\x7fELF\x02\x01\x01" + b"\0" * 9,
                         3, machine, 1, 0, 64, shoff, 0, 64, 56, 1, 64, 4, 3)
    blob = header + program
    blob += b"\0" * (text_off - len(blob))
    blob += text + debug + shstr
    blob += b"\0" * (shoff - len(blob))
    return blob + sections


class Tests(unittest.TestCase):
    """tools/run.py --test runs these with its own, so the gate does."""

    def stripped(self, data):
        with tempfile.TemporaryDirectory() as directory:
            image = Path(directory) / "image"
            image.write_bytes(data)
            blob = without_debug(image)
            self.assertEqual(image.read_bytes(), data)
            return blob

    def test_an_elf_of_either_architecture_loses_its_debug_sections_and_keeps_the_rest(self):
        for machine in (EM_X86_64, EM_AARCH64):
            with self.subTest(machine=machine):
                source = elf_with_debug_section(machine)
                self.assertEqual(section_names(source), ["", ".text", ".debug_info", ".shstrtab"])
                blob = self.stripped(source)
                self.assertEqual(section_names(blob), ["", ".text", ".shstrtab"])
                self.assertEqual(struct.unpack_from("<H", blob, 18)[0], machine)
                self.assertIn(b"\x90\x90\x90\x90", blob)
                self.assertNotIn(b"DEBUGINF", blob)

    def test_a_file_that_is_not_an_elf_is_copied_unchanged(self):
        self.assertEqual(self.stripped(b"MZ not an ELF"), b"MZ not an ELF")

    def test_the_initrd_is_the_stripped_images_in_order(self):
        with tempfile.TemporaryDirectory() as directory:
            elf = Path(directory) / "elf"
            elf.write_bytes(elf_with_debug_section(EM_AARCH64))
            plain = Path(directory) / "plain"
            plain.write_bytes(b"payload")
            initrd = Path(directory) / "initrd"
            size = write_initrd(initrd, [elf, plain])
            self.assertEqual(initrd.read_bytes(), without_debug(elf) + b"payload")
            self.assertEqual(size, initrd.stat().st_size)


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    for image in sys.argv[1:]:
        sys.stdout.buffer.write(without_debug(image))
