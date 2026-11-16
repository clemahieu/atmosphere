#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Boot a pinned KVM Linux guest and save the mapped microbenchmarks as perftest JSON.

The guest is tools/linux-bench.c: one static init binary, no C library and no
distribution userland, on the host kernel. vCPUs are pinned the way tools/bench.py
pins dom0 (tools/measure-pinned.py). A timing pass uses -cpu host,pmu=off,-perfctr-core;
a counter pass uses -cpu host,pmu=on and the guest opens perf events. The saved
record is a bench.py run, so tools/bench.py --compare-linux joins the two by label.
x86_64 only. The suite reports and never gates. What each row includes is the Linux
guest section of design/synthetic-benchmark-suite/.

Usage:
  tools/linux-bench.py [within0|within1|across] [options]

Options:
  within0|within1|across  Pinned vCPU placement (default: within0)
  --boots N               Boots (default: 5). One boot is a timing pass and,
                          unless --no-counters, a counter pass
  --counters              Counter passes too (default)
  --no-counters           Timing passes only
  --output PATH           Saved run JSON (default: logs/linux-bench-<ts>-<sha>-<mode>.json)
  --kernel PATH           Host kernel image (default: /boot/vmlinuz-$(uname -r))
  --timeout SEC           Per-pass QEMU timeout (default: 180)
  --force                 Measure despite runnable tasks or IRQs on the pinned CPUs
  --test                  Unit tests, no QEMU

Exit statuses:
  0  Run saved, or tests passed
  1  Host refused, or the guest failed to compile, boot, or emit JSON
  2  Invalid arguments
"""

from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
import math
import os
import platform
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
TREE = TOOLS.parent
ROOT = TREE.parent
LOGS_DIR = ROOT / "logs"
SCRATCH_DIR = ROOT / "scratch"
SRC = TOOLS / "linux-bench.c"

JSON_BEGIN = "--- FUCHSIAPERF JSON BEGIN ---"
JSON_END = "--- FUCHSIAPERF JSON END ---"
SUITE = "linux.microbenchmarks"
PERFTEST_KEYS = ("label", "test_suite", "unit", "values")

# Atmosphere catalogue names. tools/linux-bench.c emits each of these, and the
# design record's Linux table is this list.
MAPPED = (
    "Null",
    "NoOpLoop/100",
    "NoOpLoop/1000",
    "NoOpLoop/10000",
    "Syscall/Null",
    "Notification/Signal",
    "Notification/RoundTrip_SameCore",
    "Notification/RoundTrip_DiffCore",
    "ContextSwitch/SameProcess",
    "Thread/CreateStartJoin",
    "Process/SpawnWait",
    "Mmu/MapUnmap/4K",
    "UserPager/PageFault/Sequential",
    "Atomic/Increment/32bit",
    "Atomic/Increment/64bit",
    "Atomic/Cmpxchg/32bit",
    "Atomic/Cmpxchg/64bit",
    "Atomic/ContendedCmpxchg/DiffCore",
    "Mutex/FastLockUnlock",
    "Memcpy/1000bytes",
    "Memcpy/100000bytes",
    "TicksGet",
)

TIMING_CPU = "host,pmu=off,-perfctr-core"
COUNTER_CPU = "host,pmu=on"
GCC = (
    "gcc",
    "-std=gnu11",
    "-ffreestanding",
    "-fno-stack-protector",
    "-fno-pic",
    "-fno-builtin",
    "-fno-tree-loop-distribute-patterns",
    "-fno-asynchronous-unwind-tables",
    "-fno-unwind-tables",
    "-Os",
    "-Wall",
    "-Wextra",
    "-Werror",
    "-nostdlib",
    "-static",
    "-no-pie",
    "-Wl,-e,_start",
    "-Wl,--build-id=none",
)


class LinuxBenchError(Exception):
    """A refused host, a failed compile, or a guest that did not emit the mapped JSON."""


def load_bench():
    """Load tools/bench.py by path. Its run record is what this command saves."""
    path = TOOLS / "bench.py"
    spec = importlib.util.spec_from_file_location("bench_tool", path)
    if spec is None or spec.loader is None:
        raise LinuxBenchError(f"cannot load {path}")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def compile_guest(src: Path, out: Path) -> None:
    """Link the freestanding guest. No C library: the binary issues syscalls itself."""
    proc = subprocess.run([*GCC, "-o", str(out), str(src)], capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip()
        raise LinuxBenchError(f"gcc failed:\n{detail}")


def static_elf(data: bytes) -> bool:
    """True for an ELF64 whose program headers include no PT_INTERP (no dynamic loader)."""
    if len(data) < 64 or data[:4] != b"\x7fELF" or data[4] != 2:
        return False
    e_phoff = int.from_bytes(data[32:40], "little")
    e_phentsize = int.from_bytes(data[54:56], "little")
    e_phnum = int.from_bytes(data[56:58], "little")
    if e_phentsize < 4 or e_phoff < 0 or e_phnum < 1:
        return False
    end = e_phoff + e_phnum * e_phentsize
    if end > len(data):
        return False
    for i in range(e_phnum):
        off = e_phoff + i * e_phentsize
        p_type = int.from_bytes(data[off : off + 4], "little")
        if p_type == 3:
            return False
    return True


def _cpio_add(out: bytearray, ino: int, name: str, mode: int, data: bytes, rdev: tuple[int, int]) -> None:
    """One newc header, name, and payload, each padded to 4 bytes. The layout is the
    newc archive the kernel's initramfs loader accepts."""
    nb = name.encode() + b"\0"
    fields = (ino, mode, 0, 0, 1, 0, len(data), 0, 0, rdev[0], rdev[1], len(nb), 0)
    hdr = "070701" + "".join(f"{x:08x}" for x in fields)
    out.extend(hdr.encode() + nb)
    out.extend(b"\0" * ((-len(out)) % 4))
    out.extend(data)
    out.extend(b"\0" * ((-len(out)) % 4))


def cpio_bytes(entries: list[tuple[str, int, bytes | tuple[int, int]]]) -> bytes:
    """A newc archive of entries, then TRAILER!!!. A device entry's payload is (major, minor)."""
    out = bytearray()
    for ino, (name, mode, payload) in enumerate(entries, 1):
        if isinstance(payload, tuple):
            _cpio_add(out, ino, name, mode, b"", payload)
        else:
            _cpio_add(out, ino, name, mode, payload, (0, 0))
    _cpio_add(out, 0, "TRAILER!!!", 0, b"", (0, 0))
    return bytes(out)


def cpio_entries(blob: bytes) -> list[tuple[str, int, bytes]]:
    """(name, mode, data) for each newc member, including the trailer."""
    found: list[tuple[str, int, bytes]] = []
    i = 0
    while i + 110 <= len(blob):
        if blob[i : i + 6] != b"070701":
            raise LinuxBenchError(f"cpio magic at {i}")

        def field(n: int, at: int = i) -> int:
            start = at + 6 + n * 8
            return int(blob[start : start + 8], 16)

        mode = field(1)
        filesize = field(6)
        namesize = field(11)
        name_off = i + 110
        if name_off + namesize > len(blob):
            raise LinuxBenchError("cpio name runs past the archive")
        name = blob[name_off : name_off + namesize].split(b"\0", 1)[0].decode()
        data_off = (name_off + namesize + 3) & ~3
        if data_off + filesize > len(blob):
            raise LinuxBenchError(f"cpio data for {name} runs past the archive")
        data = blob[data_off : data_off + filesize]
        found.append((name, mode, bytes(data)))
        i = (data_off + filesize + 3) & ~3
        if name == "TRAILER!!!":
            return found
    raise LinuxBenchError("cpio has no trailer")


def initramfs_bytes(init_elf: bytes) -> bytes:
    """The initramfs: dev, dev/console, proc, and the static init. Nothing else."""
    entries: list[tuple[str, int, bytes | tuple[int, int]]] = [
        ("dev", stat.S_IFDIR | 0o755, b""),
        ("dev/console", stat.S_IFCHR | 0o600, (5, 1)),
        ("proc", stat.S_IFDIR | 0o755, b""),
        ("init", stat.S_IFREG | 0o755, init_elf),
    ]
    return cpio_bytes(entries)


def extract_guest_json(text: str) -> list[dict]:
    """The perftest array between the guest's markers. Entries are the runtime schema."""
    start = text.find(JSON_BEGIN)
    end = text.find(JSON_END, start + len(JSON_BEGIN) if start >= 0 else 0)
    if start < 0 or end < 0:
        raise LinuxBenchError("guest JSON markers missing")
    body = text[start + len(JSON_BEGIN) : end].strip()
    try:
        data = json.loads(body)
    except json.JSONDecodeError as exc:
        raise LinuxBenchError(f"guest JSON: {exc}") from exc
    if not isinstance(data, list) or not data:
        raise LinuxBenchError("guest JSON is not a non-empty array")
    for item in data:
        if not isinstance(item, dict) or set(item) != set(PERFTEST_KEYS):
            raise LinuxBenchError("guest entry keys are not label, test_suite, unit, values")
        if item["test_suite"] != SUITE:
            raise LinuxBenchError(f"guest suite is {item['test_suite']!r}")
        values = item["values"]
        if not isinstance(values, list) or not values:
            raise LinuxBenchError(f"empty values for {item['label']}")
        for value in values:
            if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
                raise LinuxBenchError(f"non-finite value for {item['label']}")
    return data


def require_series(entries: list[dict], suffix: str, unit: str) -> None:
    """Every mapped name is present as name+suffix with this unit."""
    found = {entry["label"]: entry["unit"] for entry in entries}
    missing = []
    for name in MAPPED:
        label = name + suffix
        if label not in found:
            missing.append(label)
        elif found[label] != unit:
            raise LinuxBenchError(f"{label} unit is {found[label]!r}, want {unit}")
    if missing:
        raise LinuxBenchError("missing " + ", ".join(missing))


def boot_pass(
    qemu: str,
    kernel: Path,
    initrd: Path,
    append: str,
    cpu: str,
    pair: tuple[int, int],
    others: set[int],
    clock_paths: dict,
    measure,
    timeout: int,
    serial_log: Path,
) -> tuple[list[dict], int, dict]:
    """One pinned QEMU boot. A guest that printed the mapped JSON is a pass, whatever
    QEMU's status: power-off is how the guest asks QEMU to exit."""
    if serial_log.exists():
        serial_log.unlink()
    args = [
        qemu,
        "-enable-kvm",
        "-cpu",
        cpu,
        "-machine",
        "q35,kernel_irqchip=split",
        "-name",
        "guest=linux,debug-threads=on",
        "-smp",
        "2",
        "-m",
        "512",
        "-nographic",
        "-no-reboot",
        "-serial",
        f"file:{serial_log}",
        "-monitor",
        "none",
        "-kernel",
        str(kernel),
        "-initrd",
        str(initrd),
        "-append",
        append,
    ]
    done = threading.Event()
    moved: list = []
    samples: dict = {cpu_id: [] for cpu_id in clock_paths}
    orig = os.sched_getaffinity(0)
    proc = None
    confine_thread = None
    clock_thread = None
    try:
        os.sched_setaffinity(0, set(others))
        proc = subprocess.Popen(
            args,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            preexec_fn=lambda: os.sched_setaffinity(0, set(others)),
        )
        try:
            measure.pin_vcpus(proc.pid, pair)
        except SystemExit as exc:
            raise LinuxBenchError(f"vCPU pin failed: {exc}") from exc
        confine_thread = threading.Thread(
            target=measure.confine, args=(proc.pid, others, done, moved), daemon=True
        )
        clock_thread = threading.Thread(
            target=measure.sample_clocks, args=(clock_paths, others, done, samples), daemon=True
        )
        confine_thread.start()
        clock_thread.start()
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
            tail = serial_log.read_text(encoding="utf-8", errors="replace")[-1500:] if serial_log.is_file() else ""
            raise LinuxBenchError(f"QEMU timed out after {timeout}s; tail:\n{tail}") from exc
    finally:
        done.set()
        if proc is not None and proc.poll() is None:
            proc.kill()
            proc.wait()
        if confine_thread is not None:
            confine_thread.join(timeout=2.0)
        if clock_thread is not None:
            clock_thread.join(timeout=2.0)
        os.sched_setaffinity(0, orig)
    serial = serial_log.read_text(encoding="utf-8", errors="replace") if serial_log.is_file() else ""
    try:
        entries = extract_guest_json(serial)
    except LinuxBenchError as exc:
        status = proc.returncode if proc is not None else None
        raise LinuxBenchError(f"{exc}; qemu status {status}; tail:\n{serial[-1500:]}") from exc
    status = proc.returncode if proc is not None and proc.returncode is not None else 1
    return entries, status, samples


def run(args: argparse.Namespace) -> int:
    """Compile the guest, boot it pinned, and save a bench.py run record."""
    if platform.machine() != "x86_64":
        raise LinuxBenchError("linux-bench boots an x86_64 guest")
    qemu = shutil.which("qemu-system-x86_64")
    if not qemu:
        raise LinuxBenchError("qemu-system-x86_64 not on PATH")
    kernel = args.kernel if args.kernel is not None else Path(f"/boot/vmlinuz-{os.uname().release}")
    if not kernel.is_file():
        raise LinuxBenchError(f"kernel image not found: {kernel}")
    bench = load_bench()
    git_state = bench.collect_git_state(TREE)
    pair, sibs, others, clock_paths = bench._isolation_context(args.mode, args.force)
    tsc_hz = bench.measure_tsc_hz()
    host_state = bench.collect_host_state(args.mode, pair, sibs, tsc_hz, args.force, args.counters)
    measure = bench.load_tool("measure-pinned.py")
    base_append = "console=ttyS0 quiet panic=-1 rdinit=/init"
    SCRATCH_DIR.mkdir(parents=True, exist_ok=True)
    boots = []
    with tempfile.TemporaryDirectory(prefix="linux-bench-", dir=SCRATCH_DIR) as tmp_name:
        tmp = Path(tmp_name)
        init = tmp / "init"
        compile_guest(SRC, init)
        elf = init.read_bytes()
        if not static_elf(elf):
            raise LinuxBenchError("guest linked with a dynamic loader")
        initrd = tmp / "init.cpio"
        initrd.write_bytes(initramfs_bytes(elf))
        for idx in range(args.boots):
            print(f"Boot {idx + 1}/{args.boots} on pinned pair {pair}...", flush=True)
            timing, timing_status, timing_clocks = boot_pass(
                qemu,
                kernel,
                initrd,
                base_append,
                TIMING_CPU,
                pair,
                others,
                clock_paths,
                measure,
                args.timeout,
                tmp / f"serial-{idx}-timing.log",
            )
            require_series(timing, ".tsc_cycles", "cycles")
            counter = None
            counter_status = None
            counter_clocks = None
            if args.counters:
                counter, counter_status, counter_clocks = boot_pass(
                    qemu,
                    kernel,
                    initrd,
                    base_append + " bench.counters=1",
                    COUNTER_CPU,
                    pair,
                    others,
                    clock_paths,
                    measure,
                    args.timeout,
                    tmp / f"serial-{idx}-counter.log",
                )
                require_series(counter, ".cycles", "cycles")
                require_series(counter, ".instructions", "instructions")
                require_series(counter, ".fills", "count")
            merged = bench.merge_pass_entries(timing, counter, tsc_hz)
            boots.append(
                bench.build_boot_record(
                    idx,
                    merged,
                    timing_exit=timing_status,
                    counter_exit=counter_status,
                    timing_clocks=timing_clocks,
                    counter_clocks=counter_clocks,
                )
            )
            print(f"  timing qemu status {timing_status}, counter qemu status {counter_status}", flush=True)
    ts = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    record = bench._assemble_run_record(git_state, host_state, args.mode, pair, args.counters, boots, ts)
    record["guest"] = "linux"
    record["kernel_release"] = os.uname().release
    record["kernel_image"] = str(kernel)
    out = args.output or bench.default_output_path(LOGS_DIR, git_state, args.mode, ts, prefix="linux-bench")
    bench.save_json(out, record)
    print(f"Saved run: {out}")
    print()
    print(bench.format_run_table(record))
    return 0


def _fake_series(suffix: str, unit: str, drop: str | None = None) -> list[dict]:
    entries = []
    for name in MAPPED:
        label = name + suffix
        if label == drop:
            continue
        entries.append(
            {"label": label, "test_suite": SUITE, "unit": unit, "values": [1.0, 2.0]}
        )
    return entries


def _wrap(entries: list[dict]) -> str:
    return "kernel noise\n" + JSON_BEGIN + "\n" + json.dumps(entries) + "\n" + JSON_END + "\n"


class Tests(unittest.TestCase):
    """Tier-3 tests: the initramfs carries no C library, the parser requires every mapped
    name, the guest source names those operations and includes nothing, and the link is static."""

    def test_initramfs_is_only_the_static_init(self) -> None:
        elf = b"\x7fELFguest"
        blob = initramfs_bytes(elf)
        entries = cpio_entries(blob)
        names = [name for name, _mode, _data in entries]
        self.assertEqual(names, ["dev", "dev/console", "proc", "init", "TRAILER!!!"])
        by_name = {name: data for name, _mode, data in entries}
        self.assertEqual(by_name["init"], elf)
        self.assertEqual(by_name["dev/console"], b"")
        self.assertFalse(any("libc" in name or "ld-linux" in name or name.startswith("lib") for name in names))
        self.assertNotIn(b"libc.so", blob)
        self.assertNotIn(b"ld-linux", blob)

    def test_extract_requires_every_mapped_name(self) -> None:
        good = extract_guest_json(_wrap(_fake_series(".tsc_cycles", "cycles")))
        require_series(good, ".tsc_cycles", "cycles")
        dropped = extract_guest_json(_wrap(_fake_series(".tsc_cycles", "cycles", drop="Syscall/Null.tsc_cycles")))
        with self.assertRaisesRegex(LinuxBenchError, "Syscall/Null.tsc_cycles"):
            require_series(dropped, ".tsc_cycles", "cycles")
        with self.assertRaisesRegex(LinuxBenchError, "markers"):
            extract_guest_json("no json here")
        wrong = [{"label": "Syscall/Null.tsc_cycles", "test_suite": "other", "unit": "cycles", "values": [1.0]}]
        with self.assertRaisesRegex(LinuxBenchError, "suite"):
            extract_guest_json(_wrap(wrong))
        bad_value = [
            {"label": "Syscall/Null.tsc_cycles", "test_suite": SUITE, "unit": "cycles", "values": [float("nan")]}
        ]
        with self.assertRaisesRegex(LinuxBenchError, "non-finite"):
            extract_guest_json(_wrap(bad_value))

    def test_guest_source_names_the_mapped_operations(self) -> None:
        text = SRC.read_text(encoding="utf-8")
        self.assertNotIn("#include", text)
        for name in MAPPED:
            self.assertIn(f'"{name}"', text)

    def test_compile_is_static_elf(self) -> None:
        if platform.machine() != "x86_64" or shutil.which("gcc") is None:
            self.skipTest("host gcc for x86_64")
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "init"
            compile_guest(SRC, out)
            data = out.read_bytes()
        self.assertEqual(data[:4], b"\x7fELF")
        self.assertTrue(static_elf(data))
        self.assertFalse(static_elf(b"\x7fELF" + b"\x00" * 60))


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="tools/linux-bench.py",
        description="Boot a pinned KVM Linux guest and save the mapped microbenchmarks.",
    )
    parser.add_argument(
        "mode",
        nargs="?",
        default="within0",
        choices=("within0", "within1", "across"),
        help="Pinned core placement (default: within0)",
    )
    parser.add_argument("--boots", type=int, default=5, help="Boots (default: 5)")
    counters = parser.add_mutually_exclusive_group()
    counters.add_argument("--counters", dest="counters", action="store_true", default=True, help="Counter passes (default)")
    counters.add_argument("--no-counters", dest="counters", action="store_false", help="Timing passes only")
    parser.add_argument("--output", type=Path, default=None, help="Saved run JSON path")
    parser.add_argument("--kernel", type=Path, default=None, help="Host kernel image")
    parser.add_argument("--timeout", type=int, default=180, help="Per-pass QEMU timeout in seconds (default: 180)")
    parser.add_argument("--force", action="store_true", help="Measure despite host noise on the pinned CPUs")
    parser.add_argument("--test", action="store_true", help="Run unit tests and exit")
    args = parser.parse_args(argv)
    if args.boots < 1:
        parser.error("--boots must be at least 1")
    if args.timeout < 1:
        parser.error("--timeout must be at least 1")
    return args


def run_tests() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.test:
        return run_tests()
    try:
        return run(args)
    except LinuxBenchError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
