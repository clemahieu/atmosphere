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


def without_debug(path):
    """The bytes of `path` with .debug_* removed. `path` itself is not modified."""
    path = Path(path)
    data = path.read_bytes()
    if not any(name.startswith(".debug_") for name in section_names(data)):
        return data
    with tempfile.TemporaryDirectory() as directory:
        stripped = Path(directory) / "stripped"
        subprocess.run(["objcopy", "--strip-debug", str(path), str(stripped)], check=True)
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


def elf_with_debug_section():
    """A small ELF64 whose section table names .debug_info, for the initrd test."""
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
                         3, 62, 1, 0, 64, shoff, 0, 64, 56, 1, 64, 4, 3)
    blob = header + program
    blob += b"\0" * (text_off - len(blob))
    blob += text + debug + shstr
    blob += b"\0" * (shoff - len(blob))
    return blob + sections


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        sys.exit("tools/elfstrip.py has no tests of its own; tools/run.py --test covers it")
    for image in sys.argv[1:]:
        sys.stdout.buffer.write(without_debug(image))
