#!/usr/bin/env python3
"""Report line and branch coverage of the kernel from a boot under KVM.

The kernel has no profiler runtime, so it cannot write a profile itself. An instrumented build keeps
its counters in the __llvm_prf_cnts section. After dom0 finishes, this reads them from guest memory
through the QEMU monitor and assembles the raw profile the runtime would have written: the header
below, then __llvm_prf_data and __llvm_prf_names from the ELF, with the counters from the guest in
between. The layout is the one LLVM 23 (Rust 1.99.1) writes, raw version 11.

usage: tools/coverage.py   (from the workspace root)
"""
import importlib.util
import json
import os
import re
import struct
import subprocess
import sys
import time

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("check_boot_stack", "tools/check-boot-stack.py")
check_boot_stack = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_boot_stack)

OUT = "target/coverage"
KERNEL = f"{OUT}/x86_64-unknown-aloader/debug/kernel"
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
    subprocess.run(["cargo", "build", "-q", "--target-dir", f"../{OUT}"], cwd="kernel", check=True,
                   env={**env, "RUSTFLAGS": FLAGS})
    for crate in ("aloader", "dom0"):
        subprocess.run(["cargo", "build", "-q"], cwd=crate, check=True, env=env)


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


def read_guest(sock, base, size):
    path = f"{OUT}/counters.bin"
    if os.path.exists(path):
        os.unlink(path)
    sock.sendall(f"pmemsave {base:#x} {size:#x} {path}\n".encode())
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


def summarize(export):
    """Sums llvm-cov's per-file summaries by crate."""
    crates = {}
    for entry in export["data"][0]["files"]:
        name = entry["filename"]
        crate = "verified" if "/kernel/verified/" in name else "kernel" if "/kernel/src/" in name else None
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
    log, qemu, sock = check_boot_stack.boot("debug", OUT, kernel=KERNEL)
    entry = int(re.search(r"Calling into kernel @ (?:0x)?([0-9a-f]+)", log).group(1), 16)
    bias = entry - entry_point(KERNEL)
    found = sections(KERNEL)
    counters_addr, _, counters_size = found["__llvm_prf_cnts"]
    counters = read_guest(sock, bias + counters_addr, counters_size)
    sock.sendall(b"quit\n")
    qemu.wait(timeout=30)

    with open(KERNEL, "rb") as f:
        elf = f.read()
    raw, merged = f"{OUT}/kernel.profraw", f"{OUT}/kernel.profdata"
    with open(raw, "wb") as f:
        f.write(raw_profile(elf, found, counters))
    run(tool("llvm-profdata"), "merge", "-sparse", raw, "-o", merged)
    export = json.loads(run(tool("llvm-cov"), "export", KERNEL, f"-instr-profile={merged}", "-summary-only",
                            f"-ignore-filename-regex={FOREIGN}"))
    for crate, totals in sorted(summarize(export).items()):
        print(f"{crate}: " + ", ".join(
            f"{kind} {covered}/{count} ({100 * covered / max(count, 1):.1f}%)"
            for kind, (covered, count) in totals.items()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
