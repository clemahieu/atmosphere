#!/usr/bin/env python3
"""Check that no function in an ELF executable has a stack frame over a limit.

The kernel, dom0 and user crates build with -Z emit-stack-sizes, so LLVM puts each function's
frame in the section .stack_sizes as pairs of its address (8 bytes, little-endian) and its frame
in bytes (ULEB128). The function at an address is each FUNC symbol of .symtab defined there,
with the NOTYPE symbols there as its aliases. A frame over the limit fails the check, which then
names the ten largest frames.

usage: tools/check-stack-sizes.py ELF [--limit BYTES]   (default limit 16 MiB)
       tools/check-stack-sizes.py --test                (this script's own tests)
"""
import struct
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

DEFAULT_LIMIT = 16 * 1024 * 1024
TOP = 10

SHT_SYMTAB = 2
STT_NOTYPE = 0
STT_FUNC = 2
ELF_HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
SECTION_HEADER = struct.Struct("<IIQQQQIIQQ")
SYMBOL = struct.Struct("<IBBHQQ")


class ElfError(Exception):
    pass


def c_string(table, offset):
    end = table.index(b"\0", offset)
    return table[offset:end].decode("utf-8", "replace")


def sections(data):
    """Each section of a little-endian ELF64 file as (name, type, link, contents)."""
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise ElfError("not a little-endian ELF64 file")
    header = ELF_HEADER.unpack_from(data)
    shoff, shentsize, shnum, shstrndx = header[6], header[11], header[12], header[13]
    if shentsize != SECTION_HEADER.size:
        raise ElfError(f"section header size {shentsize}")
    raw = [SECTION_HEADER.unpack_from(data, shoff + i * shentsize) for i in range(shnum)]
    names = raw[shstrndx]
    name_table = data[names[4]:names[4] + names[5]]
    return [
        (c_string(name_table, s[0]), s[1], s[6], data[s[4]:s[4] + s[5]])
        for s in raw
    ]


def uleb128(data, at):
    """The value of the ULEB128 at an offset, and the offset after it."""
    value = shift = 0
    while True:
        if at >= len(data):
            raise ElfError("a ULEB128 runs past the end of .stack_sizes")
        byte = data[at]
        at += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if byte < 0x80:
            return value, at


def frames(data):
    """Each function's frame as (bytes, its names), the largest first, and the names with ties in
    the order of their addresses."""
    found = sections(data)
    by_name = {name: (kind, link, contents) for name, kind, link, contents in found}
    if ".stack_sizes" not in by_name:
        raise ElfError("no .stack_sizes section: was it built with -Z emit-stack-sizes?")
    symtab = [(link, contents) for _, kind, link, contents in found if kind == SHT_SYMTAB]
    if not symtab:
        raise ElfError("no .symtab section")
    link, contents = symtab[0]
    strings = found[link][3]
    functions, aliases = {}, {}
    for at in range(0, len(contents), SYMBOL.size):
        name, info, _, _, value, size = SYMBOL.unpack_from(contents, at)
        kind = info & 0xF
        if kind == STT_FUNC and not (value == 0 and size == 0):
            functions.setdefault(value, []).append(c_string(strings, name))
        elif kind == STT_NOTYPE and name:
            aliases.setdefault(value, []).append(c_string(strings, name))
    stack_sizes = by_name[".stack_sizes"][2]
    sizes = {}
    at = 0
    while at < len(stack_sizes):
        if at + 8 > len(stack_sizes):
            raise ElfError("an address runs past the end of .stack_sizes")
        (address,) = struct.unpack_from("<Q", stack_sizes, at)
        frame, at = uleb128(stack_sizes, at + 8)
        if address not in functions:
            raise ElfError(f".stack_sizes names {address:#x}, where no function is defined")
        sizes[address] = max(frame, sizes.get(address, 0))
    result = [(frame, functions[address] + aliases.get(address, [])) for address, frame in sizes.items()]
    result.sort(key=lambda item: -item[0])
    return result


def check(path, limit):
    """The check's exit status, its line on stdout, and on failure the largest frames on stderr."""
    try:
        found = frames(Path(path).read_bytes())
    except (OSError, ElfError, struct.error) as error:
        print(f"{path}: {error}", file=sys.stderr)
        return 1
    if not found:
        print(f"{path}: .stack_sizes is empty", file=sys.stderr)
        return 1
    frame, names = found[0]
    if frame > limit:
        print("largest stack frames:", file=sys.stderr)
        for size, aliases in found[:TOP]:
            print(f"  {size}: {', '.join(aliases)}", file=sys.stderr)
        print(f"{path}: the frame of {names[0]} is {frame} bytes, over the limit of {limit}", file=sys.stderr)
        return 1
    print(f"{path}: {len(found)} functions, the largest frame {frame} bytes in {names[0]}, limit {limit}")
    return 0


def main(args):
    if len(args) == 1:
        return check(args[0], DEFAULT_LIMIT)
    if len(args) == 3 and args[1] == "--limit" and args[2].isdigit():
        return check(args[0], int(args[2]))
    print(__doc__.split("usage: ")[1], file=sys.stderr)
    return 2


def encode_uleb128(value):
    out = bytearray()
    while True:
        byte = value & 0x7F
        value >>= 7
        if value:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def elf(functions, aliases=(), entries=None):
    """A little-endian ELF64 file holding .stack_sizes, .symtab, .strtab and .shstrtab, with a FUNC
    symbol for each (name, address, frame) and a NOTYPE symbol for each (name, address) alias.
    'entries' replaces the .stack_sizes contents."""
    strtab = bytearray(b"\0")
    symbols = bytearray(SYMBOL.pack(0, 0, 0, 0, 0, 0))

    def symbol(name, kind, address, size):
        offset = len(strtab)
        strtab.extend(name.encode() + b"\0")
        symbols.extend(SYMBOL.pack(offset, kind, 0, 1, address, size))

    for name, address, _ in functions:
        symbol(name, STT_FUNC, address, 16)
    for name, address in aliases:
        symbol(name, STT_NOTYPE, address, 0)
    if entries is None:
        entries = b"".join(struct.pack("<Q", a) + encode_uleb128(f) for _, a, f in functions)
    shstrtab = b"\0.stack_sizes\0.symtab\0.strtab\0.shstrtab\0"
    bodies = [entries, bytes(symbols), bytes(strtab), shstrtab]
    offset = ELF_HEADER.size
    layout = []
    for body in bodies:
        layout.append((offset, len(body)))
        offset += len(body)
    shoff = offset
    # name offset in .shstrtab, type, link
    kinds = [(1, 1, 0), (14, SHT_SYMTAB, 3), (22, 3, 0), (30, 3, 0)]
    headers = SECTION_HEADER.pack(0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    for (name, kind, link), (at, size) in zip(kinds, layout):
        headers += SECTION_HEADER.pack(name, kind, 0, 0, at, size, link, 0, 1, 0)
    ident = b"\x7fELF\x02\x01\x01" + bytes(9)
    header = ELF_HEADER.pack(ident, 3, 62, 1, 0, 0, shoff, 0, ELF_HEADER.size, 0, 0,
                             SECTION_HEADER.size, 5, 4)
    return header + b"".join(bodies) + headers


class Tests(unittest.TestCase):
    def file(self, data):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "image"
        path.write_bytes(data)
        return path

    def test_frames_are_read_largest_first_with_aliases(self):
        data = elf([("small", 0x1000, 24), ("large", 0x2000, 300), ("middle", 0x3000, 128)],
                   aliases=[("large_alias", 0x2000)])
        self.assertEqual(frames(data), [(300, ["large", "large_alias"]), (128, ["middle"]), (24, ["small"])])

    def test_a_frame_under_the_limit_passes(self):
        path = self.file(elf([("f", 0x1000, 4096), ("g", 0x1100, 64)]))
        self.assertEqual(check(path, 4096), 0)

    def test_a_frame_over_the_limit_fails(self):
        path = self.file(elf([("f", 0x1000, 4097), ("g", 0x1100, 64)]))
        self.assertEqual(check(path, 4096), 1)

    def test_a_frame_over_the_default_limit_fails_from_the_command_line(self):
        path = self.file(elf([("huge", 0x1000, DEFAULT_LIMIT + 1)]))
        self.assertEqual(main([str(path)]), 1)
        self.assertEqual(main([str(path), "--limit", str(DEFAULT_LIMIT + 1)]), 0)

    def test_a_multi_byte_uleb128_frame_is_read_whole(self):
        for frame in (127, 128, 16384, DEFAULT_LIMIT, 2**40):
            with self.subTest(frame=frame):
                self.assertEqual(frames(elf([("f", 0x1000, frame)])), [(frame, ["f"])])

    def test_an_address_without_a_function_fails(self):
        entries = struct.pack("<Q", 0x9000) + encode_uleb128(8)
        path = self.file(elf([("f", 0x1000, 8)], entries=entries))
        self.assertEqual(check(path, DEFAULT_LIMIT), 1)

    def test_a_truncated_section_fails(self):
        entries = struct.pack("<Q", 0x1000) + b"\x80"
        with self.assertRaises(ElfError):
            frames(elf([("f", 0x1000, 8)], entries=entries))

    def test_a_file_that_is_not_elf64_fails(self):
        self.assertEqual(check(self.file(b"MZ" + bytes(100)), DEFAULT_LIMIT), 1)

    def test_bad_arguments_print_usage(self):
        self.assertEqual(main([]), 2)
        self.assertEqual(main(["a", "--limit", "x"]), 2)


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
