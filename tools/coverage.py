#!/usr/bin/env python3
"""Report line and branch coverage per crate from a boot under KVM.

The kernel and dom0 have no profiler runtime, so they cannot write a profile themselves. An
instrumented build keeps its counters in the __llvm_prf_cnts section. After dom0 finishes, this reads
them from guest memory through the QEMU monitor and assembles the raw profile the runtime would have
written: the header below, then __llvm_prf_data and __llvm_prf_names from the ELF, with the counters
from the guest in between. The layout is the one LLVM 23 (Rust 1.99.1) writes, raw version 11.

The kernel's counters are read by physical address. dom0's are read by virtual address, which works
because dom0 is the last thing running when its exit stops the guest. A workspace member under user/
that no image runs is listed as not run.

usage: tools/coverage.py          (from the workspace root)
       tools/coverage.py --test   (this script's own tests)
"""
import importlib.util
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
import time
import tomllib
import unittest

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("check_boot_stack", "tools/check-boot-stack.py")
check_boot_stack = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_boot_stack)

OUT = "target/coverage"
KERNEL = f"{OUT}/x86_64-unknown-aloader/debug/kernel"
DOM0 = f"{OUT}/x86_64-unknown-aloader/debug/dom0"
RAW_MAGIC = 0xff6c70726f667281
RAW_VERSION = 11
VALUE_KIND_LAST = 2
FLAGS = "-Z emit-stack-sizes -C instrument-coverage -Z coverage-options=branch -Z no-profiler-runtime"
# Standard library and dependency sources are built with the kernel, but are not its coverage.
FOREIGN = r"/rustlib/|/\.cargo/|/\.rustup/"


def run(*args, **kwargs):
    return subprocess.run(args, check=True, text=True, capture_output=True, **kwargs).stdout


def tool(name):
    sysroot = run("rustc", "--print", "sysroot").strip()
    return f"{sysroot}/lib/rustlib/x86_64-unknown-linux-gnu/bin/{name}"


def build():
    env = {**os.environ, "RUSTC_BOOTSTRAP": "1"}
    for crate in ("kernel", "dom0"):
        subprocess.run(["cargo", "build", "-q", "--target-dir", f"../{OUT}"], cwd=crate, check=True,
                       env={**env, "RUSTFLAGS": FLAGS})
    check_boot_stack.build_loader("debug")


def sections(path):
    """Returns {name: (address, file offset, size)}."""
    found = {}
    for line in run("readelf", "-SW", path).splitlines():
        match = re.search(r"\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
        if match:
            found[match.group(1)] = tuple(int(match.group(i), 16) for i in (2, 3, 4))
    return found


def entry_point(path):
    return int(re.search(r"Entry point address:\s+(0x[0-9a-f]+)", run("readelf", "-hW", path)).group(1), 16)


def read_guest(sock, command, base, size):
    """Saves guest memory with the monitor's pmemsave (physical) or memsave (virtual) command."""
    path = f"{OUT}/counters.bin"
    if os.path.exists(path):
        os.unlink(path)
    sock.sendall(f"{command} {base:#x} {size:#x} {path}\n".encode())
    for _ in range(120):
        if os.path.exists(path) and os.path.getsize(path) == size:
            break
        time.sleep(0.25)
    time.sleep(0.25)
    with open(path, "rb") as f:
        return f.read()


def raw_profile(elf, found, counters):
    data_addr, data_offset, data_size = found["__llvm_prf_data"]
    counters_addr, _, counters_size = found["__llvm_prf_cnts"]
    names_addr, names_offset, names_size = found["__llvm_prf_names"]
    wrap = (1 << 64) - 1
    header = struct.pack(
        "<19Q",
        RAW_MAGIC,
        RAW_VERSION,
        0,  # binary ids
        data_size // 72,  # a data record is 72 bytes
        0,  # padding before counters
        counters_size // 8,
        0,  # padding after counters
        0,  # bitmap bytes
        0,  # padding after bitmap
        0,  # uniform counters
        0,  # padding after uniform counters
        0,  # reserved
        names_size,
        (counters_addr - data_addr) & wrap,
        (0 - data_addr) & wrap,  # no bitmap section
        names_addr,
        0,  # vtables
        0,  # vtable names
        VALUE_KIND_LAST,
    )
    names = elf[names_offset : names_offset + names_size]
    padding = bytes(-names_size % 8)
    return header + elf[data_offset : data_offset + data_size] + counters + names + padding


def crate_of(path):
    """Names the crate a source path belongs to, or None for a path outside the tree's crates."""
    if "/kernel/verified/" in path:
        return "verified"
    match = re.search(r"/(?:user/)?([\w-]+)/src/", path)
    return match.group(1) if match else None


def not_run(ran, manifest="Cargo.toml"):
    """Names the user crates among the workspace's members that no image ran."""
    with open(manifest, "rb") as f:
        members = tomllib.load(f)["workspace"]["members"]
    user = (member.removeprefix("user/") for member in members if member.startswith("user/"))
    return sorted(crate for crate in user if crate not in ran)


def report(image, sock, command, bias):
    """Returns each crate's llvm-cov summary from one image's counters."""
    found = sections(image)
    counters_addr, _, counters_size = found["__llvm_prf_cnts"]
    counters = read_guest(sock, command, bias + counters_addr, counters_size)
    with open(image, "rb") as f:
        elf = f.read()
    name = os.path.basename(image)
    raw, merged = f"{OUT}/{name}.profraw", f"{OUT}/{name}.profdata"
    with open(raw, "wb") as f:
        f.write(raw_profile(elf, found, counters))
    run(tool("llvm-profdata"), "merge", "-sparse", raw, "-o", merged)
    export = json.loads(run(tool("llvm-cov"), "export", image, f"-instr-profile={merged}", "-summary-only",
                            f"-ignore-filename-regex={FOREIGN}"))
    crates = {}
    for entry in export["data"][0]["files"]:
        crate = crate_of(entry["filename"])
        if crate is None:
            continue
        totals = crates.setdefault(crate, {"lines": [0, 0], "branches": [0, 0]})
        for kind in totals:
            totals[kind][0] += entry["summary"][kind]["covered"]
            totals[kind][1] += entry["summary"][kind]["count"]
    return crates


def main():
    os.makedirs(OUT, exist_ok=True)
    build()
    log, qemu, sock = check_boot_stack.boot("debug", OUT, kernel=KERNEL, dom0=DOM0)
    entry = int(re.search(r"Calling into kernel @ (?:0x)?([0-9a-f]+)", log).group(1), 16)
    kernel_bias = entry - entry_point(KERNEL)
    dom0_log = log[log.index("Loading dom0"):]
    dom0_bias = int(re.search(r"Load Bias: 0x([0-9a-f]+)", dom0_log).group(1), 16)
    try:
        images = {
            "kernel": report(KERNEL, sock, "pmemsave", kernel_bias),
            "dom0": report(DOM0, sock, "memsave", dom0_bias),
        }
    finally:
        sock.sendall(b"quit\n")
        qemu.wait(timeout=30)
    for image, crates in images.items():
        for crate, totals in sorted(crates.items()):
            print(f"{image}/{crate}: " + ", ".join(
                f"{kind} {covered}/{count} ({100 * covered / max(count, 1):.1f}%)"
                for kind, (covered, count) in totals.items()))
    for crate in not_run({crate for crates in images.values() for crate in crates}):
        print(f"{crate}: not run")
    return 0


class Tests(unittest.TestCase):
    def manifest(self, members):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = os.path.join(directory.name, "Cargo.toml")
        with open(path, "w") as f:
            f.write("[workspace]\nmembers = [" + ", ".join(f'"{m}"' for m in members) + "]\n")
        return path

    def test_a_user_crate_no_image_ran_is_listed(self):
        self.assertEqual(not_run({"kernel", "dom0"}, self.manifest(["kernel", "dom0", "user/hello"])), ["hello"])

    def test_a_user_crate_an_image_ran_is_not_listed(self):
        self.assertEqual(not_run({"dom0", "hello"}, self.manifest(["dom0", "user/hello"])), [])

    def test_a_crate_outside_user_is_not_listed(self):
        self.assertEqual(not_run(set(), self.manifest(["aelf", "kernel/verified"])), [])

    def test_an_added_user_crate_is_listed_and_a_removed_one_is_not(self):
        self.assertEqual(not_run(set(), self.manifest(["user/hello", "user/time"])), ["hello", "time"])
        self.assertEqual(not_run(set(), self.manifest(["user/time"])), ["time"])

    def test_the_workspace_lists_its_user_crates(self):
        self.assertEqual(not_run(set(), "Cargo.toml"), ["hello"])


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main())
