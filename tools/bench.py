#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Boot the microbenchmark suite pinned, save results, and detect regressions.

Runs the bench-enabled Atmosphere payload under KVM with tools/measure-pinned.py
CPU affinity and noise checks, extracts the perftest JSON from the serial log,
records the commit and host state under logs/ at the project root, and compares
against a recorded baseline across at least 5 boots. Timing boots pass
`-cpu host,pmu=off,-perfctr-core` to avoid QEMU vPMU RDPMC overhead; separate
PMU counter boots pass `-cpu host,pmu=on` for cycles, instructions, and fills.
Reports results and never gates. tools/linux-bench.py saves a Linux guest run in
the same record; --compare-linux prints the two side by side by label.

Usage:
  tools/bench.py [within0|within1|across] [options]

Options:
  within0|within1|across  Pinned vCPU placement mode from measure-pinned.py (default: within0)
  --boots N               Boots per run (default: 5; comparison requires >= 5)
  --counters              Also run PMU counter boots (-cpu host,pmu=on) (default: enabled)
  --no-counters           Skip PMU counter boots; collect timings only
  --save-baseline         Also write the saved run to logs/bench-baseline.json
  --baseline PATH         Compare against a saved baseline run JSON
  --interleave REF        Build git ref REF in a temporary scratch worktree and
                          interleave baseline and candidate boots on the same pinned cores
  --compare-only BASE CAND
                          Compare two already-saved run JSON files without booting QEMU
  --compare-linux ATMOSPHERE LINUX
                          Show medians of an Atmosphere run and a Linux run side by side
                          by label, without booting. A gap is the two operations in
                          design/synthetic-benchmark-suite/, not a regression.
  --no-compare            Skip automatic comparison against logs/bench-baseline.json
  --output PATH           Override saved run JSON path (default: logs/bench-<ts>-<sha>-<mode>.json)
  --timeout SEC           Per-boot QEMU timeout in seconds (default: 60)
  --force                 Proceed despite runnable tasks or IRQs on target CPUs
  --no-build              Reuse existing release artifacts in target/
  --lock-stats            Build kernel with --features lock_stats
  --test                  Run unit tests without booting QEMU

Exit statuses:
  0  Completed successfully (including when benchmarks moved; suite never gates)
  1  Refusal or failure (host noise without --force, < 5 runs, boot/JSON/build error)
  2  Invalid command-line arguments
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
import datetime
import importlib.util
import io
import json
import mmap
import os
import platform
import re
import shutil
import socket
import statistics
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path


TOOLS_DIR = Path(__file__).resolve().parent
TREE = TOOLS_DIR.parent
ROOT = TREE.parent
LOGS_DIR = ROOT / "logs"
SCRATCH_DIR = ROOT / "scratch"
DEFAULT_BASELINE_NAME = "bench-baseline.json"

TIMING_CPU = "host,pmu=off,-perfctr-core"
COUNTER_CPU = "host,pmu=on"
MIN_COMPARISON_RUNS = 5
PERFTEST_KEYS = ("label", "test_suite", "unit", "values")
ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]")
RDTSC_X86_64 = b"\x0f\x31\x48\xc1\xe2\x20\x48\x09\xd0\xc3"


class BenchError(Exception):
    """Raised when benchmark execution, extraction, or comparison cannot proceed."""


def load_tool(filename: str):
    """Load a sibling script from tools/ by filename without writing .pyc files."""
    path = TOOLS_DIR / filename
    module_name = "tools_" + path.stem.replace("-", "_")
    if module_name in sys.modules:
        return sys.modules[module_name]
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise BenchError(f"cannot load tool module {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def strip_ansi(text: str) -> str:
    """Remove ANSI escape sequences and carriage returns from serial output."""
    return ANSI_RE.sub("", text).replace("\r", "")


def extract_perftest_json(serial: str) -> list[dict]:
    """Extract and validate perftest JSON entries from a guest serial log."""
    check_boot_log = load_tool("check-boot-log.py")
    cleaned = strip_ansi(serial)
    try:
        entries = check_boot_log.perftest_results_accepted(cleaned)
    except check_boot_log.Refused as exc:
        raise BenchError(str(exc)) from exc
    return [
        {key: list(entry[key]) if key == "values" else entry[key] for key in PERFTEST_KEYS}
        for entry in entries
    ]


def add_nanosecond_series(entries: list[dict], tsc_hz: int | None) -> list[dict]:
    """Append derived .nanoseconds series for each .tsc_cycles entry when tsc_hz > 0."""
    result = [
        {key: list(entry[key]) if key == "values" else entry[key] for key in PERFTEST_KEYS}
        for entry in entries
    ]
    if not tsc_hz or tsc_hz <= 0:
        return result
    ns_per_cycle = 1_000_000_000.0 / float(tsc_hz)
    seen = {entry["label"] for entry in result}
    for entry in entries:
        label = entry["label"]
        if not label.endswith(".tsc_cycles"):
            continue
        ns_label = label[: -len(".tsc_cycles")] + ".nanoseconds"
        if ns_label in seen:
            continue
        seen.add(ns_label)
        result.append(
            {
                "label": ns_label,
                "test_suite": entry["test_suite"],
                "unit": "nanoseconds",
                "values": [float(v) * ns_per_cycle for v in entry["values"]],
            }
        )
    return result


def merge_pass_entries(
    timing_entries: list[dict],
    counter_entries: list[dict] | None,
    tsc_hz: int | None,
) -> list[dict]:
    """Combine timing entries (+ nanoseconds) with non-tsc PMU counter entries."""
    merged = add_nanosecond_series(timing_entries, tsc_hz)
    if not counter_entries:
        return merged
    seen = {entry["label"] for entry in merged}
    for entry in counter_entries:
        label = entry["label"]
        # PMU boots incur vPMU/RDPMC exit overhead; never mix their tsc_cycles into timings.
        if label.endswith(".tsc_cycles") or label in seen:
            continue
        seen.add(label)
        merged.append(
            {key: list(entry[key]) if key == "values" else entry[key] for key in PERFTEST_KEYS}
        )
    return merged


def summarize_values(values: list[float]) -> dict[str, float | int]:
    """Compute batch statistics (count, min, median, mean, std_dev, max)."""
    if not values:
        raise BenchError("cannot summarize empty benchmark series")
    nums = [float(v) for v in values]
    return {
        "count": len(nums),
        "min": min(nums),
        "median": statistics.median(nums),
        "mean": statistics.fmean(nums),
        "std_dev": statistics.stdev(nums) if len(nums) > 1 else 0.0,
        "max": max(nums),
    }


def build_boot_record(boot_index: int, entries: list[dict], **meta) -> dict:
    """Attach per-entry batch summaries to one merged boot record."""
    results = []
    for entry in entries:
        item = {key: list(entry[key]) if key == "values" else entry[key] for key in PERFTEST_KEYS}
        item["summary"] = summarize_values(item["values"])
        results.append(item)
    record = {"boot_index": boot_index, "results": results}
    record.update(meta)
    return record


def aggregate_boots(boots: list[dict]) -> tuple[dict[str, dict], list[dict]]:
    """Aggregate per-boot summaries and build top-level perftest schema array."""
    ordered_labels: list[str] = []
    grouped: dict[str, list[dict]] = {}
    for boot in boots:
        for entry in boot.get("results", []):
            label = entry["label"]
            if label not in grouped:
                ordered_labels.append(label)
                grouped[label] = []
            grouped[label].append(entry)

    summary_by_label: dict[str, dict] = {}
    perftest_array: list[dict] = []
    for label in ordered_labels:
        items = grouped[label]
        first = items[0]
        boot_medians = []
        boot_mins = []
        boot_means = []
        boot_maxes = []
        all_values: list[float] = []
        for item in items:
            s = item.get("summary") or summarize_values(item["values"])
            boot_medians.append(float(s["median"]))
            boot_mins.append(float(s["min"]))
            boot_means.append(float(s["mean"]))
            boot_maxes.append(float(s["max"]))
            all_values.extend(float(v) for v in item["values"])
        summary_by_label[label] = {
            "test_suite": first["test_suite"],
            "unit": first["unit"],
            "runs": len(boot_medians),
            "boot_medians": boot_medians,
            "boot_mins": boot_mins,
            "boot_means": boot_means,
            "boot_maxes": boot_maxes,
            "median": statistics.median(boot_medians),
            "spread_min": min(boot_medians),
            "spread_max": max(boot_medians),
            "min": min(boot_mins),
            "mean": statistics.fmean(boot_means),
            "max": max(boot_maxes),
        }
        perftest_array.append(
            {
                "label": label,
                "test_suite": first["test_suite"],
                "unit": first["unit"],
                "values": all_values,
            }
        )
    return summary_by_label, perftest_array


def _run_summary(run: dict) -> tuple[dict[str, dict], int]:
    """Extract summary map and total boot count from a saved run dict."""
    boots = run.get("boots")
    if not isinstance(boots, list):
        raise BenchError("saved run is missing 'boots' list")
    summary = run.get("summary")
    if not isinstance(summary, dict) or not summary:
        summary, _ = aggregate_boots(boots)
    return summary, len(boots)


def compare_runs(
    baseline: dict,
    candidate: dict,
    min_runs: int = MIN_COMPARISON_RUNS,
) -> dict:
    """Compare candidate against baseline; flag medians outside baseline run spread."""
    if min_runs < MIN_COMPARISON_RUNS:
        raise BenchError(f"comparison requires min_runs >= {MIN_COMPARISON_RUNS}, got {min_runs}")
    base_summary, base_boots = _run_summary(baseline)
    cand_summary, cand_boots = _run_summary(candidate)
    if base_boots < min_runs or cand_boots < min_runs:
        raise BenchError(
            f"comparison requires at least {min_runs} runs per side "
            f"(baseline={base_boots}, candidate={cand_boots})"
        )

    labels = list(base_summary.keys()) + [k for k in cand_summary.keys() if k not in base_summary]
    rows: list[dict] = []
    moved: list[dict] = []
    missing: list[str] = []
    new: list[str] = []

    for label in labels:
        base_entry = base_summary.get(label)
        cand_entry = cand_summary.get(label)
        if base_entry is not None and cand_entry is None:
            missing.append(label)
            rows.append({"label": label, "unit": base_entry["unit"], "status": "missing_in_candidate", "moved": False})
            continue
        if base_entry is None and cand_entry is not None:
            new.append(label)
            rows.append({"label": label, "unit": cand_entry["unit"], "status": "new_in_candidate", "moved": False})
            continue
        assert base_entry is not None and cand_entry is not None
        if base_entry["runs"] < min_runs or cand_entry["runs"] < min_runs:
            raise BenchError(
                f"benchmark '{label}' needs at least {min_runs} runs on each side "
                f"(baseline={base_entry['runs']}, candidate={cand_entry['runs']})"
            )

        base_med = float(base_entry["median"])
        base_low = float(base_entry["spread_min"])
        base_high = float(base_entry["spread_max"])
        cand_med = float(cand_entry["median"])
        cand_low = float(cand_entry["spread_min"])
        cand_high = float(cand_entry["spread_max"])

        if cand_med < base_low:
            is_moved = True
            direction = "faster"
            status = "moved_faster"
        elif cand_med > base_high:
            is_moved = True
            direction = "slower"
            status = "moved_slower"
        else:
            is_moved = False
            direction = "same"
            status = "unchanged"

        delta = cand_med - base_med
        if base_med != 0.0:
            delta_pct: float | None = (delta / base_med) * 100.0
        elif delta == 0.0:
            delta_pct = 0.0
        else:
            delta_pct = None

        row = {
            "label": label,
            "unit": cand_entry["unit"],
            "status": status,
            "moved": is_moved,
            "direction": direction,
            "baseline_runs": base_entry["runs"],
            "candidate_runs": cand_entry["runs"],
            "baseline_median": base_med,
            "baseline_spread_min": base_low,
            "baseline_spread_max": base_high,
            "candidate_median": cand_med,
            "candidate_spread_min": cand_low,
            "candidate_spread_max": cand_high,
            "delta": delta,
            "delta_pct": delta_pct,
        }
        rows.append(row)
        if is_moved:
            moved.append(row)

    unchanged_count = sum(1 for r in rows if r["status"] == "unchanged")
    return {
        "schema_version": 1,
        "min_runs": min_runs,
        "baseline_commit": baseline.get("commit", "unknown"),
        "candidate_commit": candidate.get("commit", "unknown"),
        "baseline_boots": base_boots,
        "candidate_boots": cand_boots,
        "moved_count": len(moved),
        "unchanged_count": unchanged_count,
        "moved": moved,
        "missing": missing,
        "new": new,
        "rows": rows,
    }


def replace_cpu_arg(qemu_args: list[str], cpu_spec: str) -> list[str]:
    """Return a copy of qemu_args with the -cpu option replaced by cpu_spec."""
    updated = list(qemu_args)
    for idx, arg in enumerate(updated):
        if arg == "-cpu" and idx + 1 < len(updated):
            updated[idx + 1] = cpu_spec
            return updated
    raise BenchError("-cpu argument not found in QEMU command line")


def interleave_order(boots: int) -> list[tuple[str, int]]:
    """Return alternating (role, boot_index) schedule of length 2 * boots."""
    schedule: list[tuple[str, int]] = []
    for idx in range(boots):
        schedule.append(("baseline", idx))
        schedule.append(("candidate", idx))
    return schedule


def _fmt_num(val: float, unit: str) -> str:
    if unit == "nanoseconds":
        return f"{val:.2f}"
    if abs(val) >= 100.0 or val == int(val):
        return f"{val:.1f}"
    return f"{val:.3f}"


def format_run_table(run: dict) -> str:
    """Format a human-readable summary table for a saved single run."""
    host = run.get("host", {})
    dirty = " (dirty)" if run.get("dirty") else ""
    lines = [
        f"Commit: {run.get('short_commit', 'unknown')}{dirty} [{run.get('branch', '?')}]  "
        f"Mode: {run.get('mode', '?')} pair={run.get('pair')}  Boots: {len(run.get('boots', []))}  "
        f"TSC Hz: {host.get('tsc_hz')}  Isolation: {host.get('isolation_state', '?')}",
        "",
        f"{'Benchmark':<42} {'Unit':<12} {'Runs':>4} {'Min':>10} {'Median':>10} {'Mean':>10} {'Spread (min..max)':>23}",
        "-" * 117,
    ]
    for label, entry in run.get("summary", {}).items():
        unit = entry["unit"]
        spread = f"{_fmt_num(entry['spread_min'], unit)}..{_fmt_num(entry['spread_max'], unit)}"
        lines.append(
            f"{label:<42} {unit:<12} {entry['runs']:>4} "
            f"{_fmt_num(entry['min'], unit):>10} "
            f"{_fmt_num(entry['median'], unit):>10} "
            f"{_fmt_num(entry['mean'], unit):>10} "
            f"{spread:>23}"
        )
    return "\n".join(lines)


def format_comparison_table(comparison: dict) -> str:
    """Format a comparison table highlighting every benchmark whose median moved."""
    lines = [
        f"Comparison (min_runs={comparison['min_runs']}): "
        f"baseline {comparison['baseline_commit'][:12]} ({comparison['baseline_boots']} boots) vs "
        f"candidate {comparison['candidate_commit'][:12]} ({comparison['candidate_boots']} boots)",
        "",
        f"{'Benchmark':<40} {'Unit':<11} {'Base Med [min..max]':>24} "
        f"{'Cand Med [min..max]':>24} {'Delta %':>9} {'Status':<16}",
        "-" * 130,
    ]
    for row in comparison["rows"]:
        status = row["status"]
        if status in ("missing_in_candidate", "new_in_candidate"):
            lines.append(f"{row['label']:<40} {row['unit']:<11} {'-':>24} {'-':>24} {'-':>9} {status:<16}")
            continue
        unit = row["unit"]
        base_col = (
            f"{_fmt_num(row['baseline_median'], unit)} "
            f"[{_fmt_num(row['baseline_spread_min'], unit)}..{_fmt_num(row['baseline_spread_max'], unit)}]"
        )
        cand_col = (
            f"{_fmt_num(row['candidate_median'], unit)} "
            f"[{_fmt_num(row['candidate_spread_min'], unit)}..{_fmt_num(row['candidate_spread_max'], unit)}]"
        )
        pct = row["delta_pct"]
        pct_col = "n/a" if pct is None else f"{pct:+.2f}%"
        if row["moved"]:
            badge = f"MOVED ({row['direction']})"
        else:
            badge = "within spread"
        lines.append(
            f"{row['label']:<40} {unit:<11} {base_col:>24} {cand_col:>24} {pct_col:>9} {badge:<16}"
        )

    lines.append("")
    moved = comparison["moved"]
    if moved:
        lines.append(f"Moved benchmarks ({len(moved)}):")
        for row in moved:
            pct = "n/a" if row["delta_pct"] is None else f"{row['delta_pct']:+.2f}%"
            lines.append(
                f"  - {row['label']}: {row['direction']} "
                f"(candidate {_fmt_num(row['candidate_median'], row['unit'])} vs "
                f"baseline spread {_fmt_num(row['baseline_spread_min'], row['unit'])}.."
                f"{_fmt_num(row['baseline_spread_max'], row['unit'])}, {pct})"
            )
    else:
        lines.append("Moved benchmarks (0): none")
    return "\n".join(lines)


def format_side_by_side(atmosphere: dict, linux_run: dict) -> str:
    """Medians of an Atmosphere run and a Linux run, joined by label.

    A label only one run has is printed with a dash on the other side and listed
    again at the bottom. The two numbers are the two operations in
    design/synthetic-benchmark-suite/, not a regression of either run.
    """
    a_sum, a_boots = _run_summary(atmosphere)
    l_sum, l_boots = _run_summary(linux_run)
    linux_name = linux_run.get("kernel_release") or linux_run.get("short_commit", "linux")
    lines = [
        f"Atmosphere {atmosphere.get('short_commit', 'unknown')} ({a_boots} boots) beside "
        f"Linux {linux_name} ({l_boots} boots)",
        "",
        f"{'Benchmark':<52} {'Unit':<13} {'Atmosphere':>14} {'Linux':>14}",
        "-" * 96,
    ]
    only_atmosphere: list[str] = []
    only_linux: list[str] = []
    labels = list(a_sum) + [label for label in l_sum if label not in a_sum]
    for label in labels:
        a_entry = a_sum.get(label)
        l_entry = l_sum.get(label)
        if a_entry is None:
            only_linux.append(label)
            unit = l_entry["unit"]
            a_col = "-"
            l_col = _fmt_num(float(l_entry["median"]), unit)
        elif l_entry is None:
            only_atmosphere.append(label)
            unit = a_entry["unit"]
            a_col = _fmt_num(float(a_entry["median"]), unit)
            l_col = "-"
        else:
            unit = a_entry["unit"]
            a_col = _fmt_num(float(a_entry["median"]), unit)
            l_col = _fmt_num(float(l_entry["median"]), l_entry["unit"])
        lines.append(f"{label:<52} {unit:<13} {a_col:>14} {l_col:>14}")
    lines.append("")
    lines.append("Only in Atmosphere: " + (", ".join(only_atmosphere) if only_atmosphere else "none"))
    lines.append("Only in Linux: " + (", ".join(only_linux) if only_linux else "none"))
    lines.append(
        "A gap is the two operations in design/synthetic-benchmark-suite/, not a regression of either run."
    )
    return "\n".join(lines)


def default_output_path(
    logs_dir: Path,
    git_state: dict,
    mode: str,
    timestamp_utc: str,
    prefix: str = "bench",
) -> Path:
    """Build deterministic filename under logs/ for a saved benchmark or comparison run."""
    compact_ts = re.sub(r"[-:]", "", timestamp_utc)
    short = git_state.get("short_commit") or str(git_state.get("commit", "unknown"))[:12]
    safe_short = re.sub(r"[^0-9A-Za-z._-]", "", short) or "unknown"
    return logs_dir / f"{prefix}-{compact_ts}-{safe_short}-{mode}.json"


def load_run_json(path: Path) -> dict:
    """Load and validate a previously saved bench.py run JSON file."""
    if not path.is_file():
        raise BenchError(f"baseline/run file not found: {path}")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise BenchError(f"invalid JSON in {path}: {exc}") from exc
    if not isinstance(data, dict) or "boots" not in data:
        raise BenchError(f"{path} is not a bench.py run record")
    return data


def save_json(path: Path, payload: dict) -> None:
    """Atomically write JSON payload to path, creating parent directories if needed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path = path.with_suffix(path.suffix + f".tmp.{os.getpid()}")
    tmp_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    tmp_path.replace(path)


def measure_tsc_hz(samples: int = 3, window_s: float = 0.02) -> int | None:
    """Calibrate host invariant TSC frequency against CLOCK_MONOTONIC_RAW on x86_64."""
    if platform.machine() != "x86_64":
        return None
    buf = None
    c_buf = None
    fn = None
    try:
        buf = mmap.mmap(-1, 4096, prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
        buf.write(RDTSC_X86_64)
        c_buf = ctypes.c_char.from_buffer(buf)
        fn = ctypes.CFUNCTYPE(ctypes.c_uint64)(ctypes.addressof(c_buf))
        rates = []
        for _ in range(samples):
            t0, c0 = time.monotonic_ns(), fn()
            time.sleep(window_s)
            t1, c1 = time.monotonic_ns(), fn()
            dt = t1 - t0
            if dt > 0 and c1 > c0:
                rates.append(((c1 - c0) * 1_000_000_000) // dt)
        return int(statistics.median(rates)) if rates else None
    except OSError:
        return None
    finally:
        fn = None
        c_buf = None
        if buf is not None:
            buf.close()


def _git_output(tree: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(tree), *args],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise BenchError(f"git {' '.join(args)} failed: {proc.stderr.strip()}")
    return proc.stdout.strip()


def collect_git_state(tree: Path) -> dict:
    """Capture commit hash, branch, subject, and dirty status for a git worktree."""
    commit = _git_output(tree, "rev-parse", "HEAD")
    short_commit = _git_output(tree, "rev-parse", "--short=12", "HEAD")
    branch = _git_output(tree, "rev-parse", "--abbrev-ref", "HEAD")
    subject = _git_output(tree, "log", "-1", "--format=%s", "HEAD")
    dirty = bool(_git_output(tree, "status", "--porcelain"))
    return {
        "commit": commit,
        "short_commit": short_commit,
        "branch": branch,
        "subject": subject,
        "dirty": dirty,
        "worktree": str(tree),
    }


def _cpu_model_name() -> str:
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.is_file():
        for line in cpuinfo.read_text(encoding="utf-8", errors="replace").splitlines():
            if line.lower().startswith("model name") and ":" in line:
                return line.split(":", 1)[1].strip()
    return "unknown"


def _governors(cpus: list[int]) -> dict[str, str]:
    result: dict[str, str] = {}
    for cpu in cpus:
        gov_path = Path(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor")
        if gov_path.is_file():
            result[str(cpu)] = gov_path.read_text(encoding="utf-8").strip()
    return result


def collect_host_state(
    mode: str,
    pair: tuple[int, int],
    siblings: list[int],
    tsc_hz: int | None,
    forced: bool,
    counters: bool,
) -> dict:
    """Capture host CPU, frequency, isolation, and load state alongside a run."""
    measure_pinned = load_tool("measure-pinned.py")
    iso_path = Path(measure_pinned.ISOLATION_STATE)
    isolation_state = iso_path.read_text(encoding="utf-8").strip() if iso_path.is_file() else "absent"
    return {
        "hostname": socket.gethostname(),
        "kernel": os.uname().release,
        "machine": platform.machine(),
        "cpu_model": _cpu_model_name(),
        "tsc_hz": tsc_hz,
        "tsc_source": "rdtsc_monotonic_raw" if tsc_hz else "unavailable",
        "isolation_state": isolation_state,
        "mode": mode,
        "pair": list(pair),
        "siblings": list(siblings),
        "governors": _governors(siblings),
        "loadavg": list(os.getloadavg()),
        "forced": forced,
        "qemu_timing_cpu": TIMING_CPU,
        "qemu_counter_cpu": COUNTER_CPU if counters else None,
        "clock_source": {str(c): measure_pinned.clock_source(c) for c in pair},
    }


def build_release(tree: Path, lock_stats: bool = False) -> dict[str, Path]:
    """Build release aloader, kernel, bench-enabled dom0, and hello payload in tree."""
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    env.setdefault("CARGO_TERM_PROGRESS_WHEN", "never")

    kernel_args = ["cargo", "build", "-q", "--release"]
    if lock_stats:
        kernel_args.extend(["--features", "lock_stats"])

    steps = [
        (tree / "aloader", ["cargo", "build", "-q", "--release", "--target", "x86_64-unknown-uefi"]),
        (tree / "kernel", kernel_args),
        (tree / "dom0", ["cargo", "build", "-q", "--release", "--features", "bench"]),
        (tree / "user/hello", ["cargo", "build", "-q", "--release"]),
    ]
    for cwd, cmd in steps:
        proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False)
        if proc.returncode != 0:
            raise BenchError(f"build failed in {cwd}: {proc.stderr.strip() or proc.stdout.strip()}")

    return {
        "loader": tree / "target/x86_64-unknown-uefi/release/aloader.efi",
        "kernel": tree / "target/x86_64-unknown-aloader/release/kernel",
        "dom0": tree / "target/x86_64-unknown-aloader/release/dom0",
        "hello": tree / "target/x86_64-unknown-aloader/release/hello",
    }


def artifacts_from_tree(tree: Path) -> dict[str, Path]:
    """Resolve expected release binary paths in tree without compiling."""
    paths = {
        "loader": tree / "target/x86_64-unknown-uefi/release/aloader.efi",
        "kernel": tree / "target/x86_64-unknown-aloader/release/kernel",
        "dom0": tree / "target/x86_64-unknown-aloader/release/dom0",
        "hello": tree / "target/x86_64-unknown-aloader/release/hello",
    }
    missing = [str(p) for p in paths.values() if not p.is_file()]
    if missing:
        raise BenchError(f"missing release build artifacts (omit --no-build): {', '.join(missing)}")
    return paths


def _run_qemu_pinned(
    artifacts: dict[str, Path],
    pair: tuple[int, int],
    others: set[int],
    clock_paths: dict[int, Path],
    cpu_spec: str,
    timeout: int,
) -> tuple[list[dict], int, dict]:
    """Boot QEMU once with pinned vCPUs and confined support threads; return perftest entries."""
    measure_pinned = load_tool("measure-pinned.py")
    firmware = load_tool("firmware.py")
    run_mod = load_tool("run.py")

    ovmf_code, ovmf_vars, qemu_bin = firmware.require("qemu-system-x86_64")
    SCRATCH_DIR.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="atmo-bench-", dir=SCRATCH_DIR) as tmp:
        run_dir = Path(tmp)
        serial_log = run_dir / "serial.log"
        run_mod.lay_out_esp(
            run_dir,
            artifacts["loader"],
            [artifacts["kernel"], artifacts["dom0"], artifacts["hello"]],
            False,
            Path(ovmf_vars),
        )
        args = run_mod.qemu_args(
            run_dir,
            serial_log,
            kvm=True,
            iommu=False,
            gdb_socket=None,
            ovmf_code=Path(ovmf_code),
            memory_mib=run_mod.MEMORY_MIB,
        )
        args = replace_cpu_arg(args, cpu_spec)

        done = threading.Event()
        moved: list = []
        samples: dict[int, list[float]] = {c: [] for c in clock_paths}
        orig_affinity = os.sched_getaffinity(0)
        os.sched_setaffinity(0, set(others))
        proc = None
        confine_thread = None
        clock_thread = None
        try:
            proc = subprocess.Popen(
                [qemu_bin, *args],
                cwd=run_dir,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                text=True,
                preexec_fn=lambda: os.sched_setaffinity(0, set(others)),
            )
            measure_pinned.pin_vcpus(proc.pid, pair)
            confine_thread = threading.Thread(
                target=measure_pinned.confine,
                args=(proc.pid, others, done, moved),
                daemon=True,
            )
            clock_thread = threading.Thread(
                target=measure_pinned.sample_clocks,
                args=(clock_paths, others, done, samples),
                daemon=True,
            )
            confine_thread.start()
            clock_thread.start()
            _, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            if proc is not None:
                proc.kill()
                proc.communicate()
            tail = serial_log.read_text(encoding="utf-8", errors="replace")[-800:] if serial_log.is_file() else ""
            raise BenchError(f"QEMU timed out after {timeout}s (cpu={cpu_spec}); tail:\n{tail}") from exc
        except BaseException:
            if proc is not None and proc.poll() is None:
                proc.kill()
                proc.wait()
            raise
        finally:
            done.set()
            if confine_thread is not None:
                confine_thread.join(timeout=2.0)
            if clock_thread is not None:
                clock_thread.join(timeout=2.0)
            os.sched_setaffinity(0, orig_affinity)

        status = run_mod.exit_status(proc.returncode)
        serial = serial_log.read_text(encoding="utf-8", errors="replace") if serial_log.is_file() else ""
        if status != 0:
            tail = serial[-1000:] if serial else (stderr or "")
            raise BenchError(f"QEMU exited with status {status} (cpu={cpu_spec}); tail:\n{tail}")
        entries = extract_perftest_json(serial)
        return entries, status, samples


def _isolation_context(mode: str, force: bool) -> tuple[tuple[int, int], list[int], set[int], dict[int, Path]]:
    """Select pinned pair via measure-pinned.py, check host noise, and build affinity sets."""
    measure_pinned = load_tool("measure-pinned.py")
    pair = measure_pinned.choose(mode)
    measure_pinned.check_noise(pair, force)
    sibs = measure_pinned.siblings(pair)
    online = set(measure_pinned.expand(measure_pinned.read(Path("/sys/devices/system/cpu/online"))))
    others = online - set(sibs)
    if not others:
        raise BenchError("no host CPUs left outside reserved pinned pair and siblings")
    clock_paths = {
        c: Path(f"/sys/devices/system/cpu/cpu{c}/cpufreq/{src}")
        for c in pair
        if (src := measure_pinned.clock_source(c))
    }
    return pair, sibs, others, clock_paths


def _assemble_run_record(
    git_state: dict,
    host_state: dict,
    mode: str,
    pair: tuple[int, int],
    counters: bool,
    boots: list[dict],
    timestamp_utc: str,
) -> dict:
    summary, perftest = aggregate_boots(boots)
    return {
        "schema_version": 1,
        "timestamp_utc": timestamp_utc,
        "commit": git_state["commit"],
        "short_commit": git_state["short_commit"],
        "branch": git_state["branch"],
        "subject": git_state["subject"],
        "dirty": git_state["dirty"],
        "mode": mode,
        "pair": list(pair),
        "counters": counters,
        "host": host_state,
        "boots": boots,
        "summary": summary,
        "perftest": perftest,
    }


def _boot_pass_record(
    boot_idx: int,
    artifacts: dict[str, Path],
    pair: tuple[int, int],
    others: set[int],
    clock_paths: dict[int, Path],
    tsc_hz: int | None,
    counters: bool,
    timeout: int,
) -> dict:
    timing_entries, timing_status, timing_clocks = _run_qemu_pinned(
        artifacts, pair, others, clock_paths, TIMING_CPU, timeout
    )
    counter_entries = None
    counter_status = None
    counter_clocks = None
    if counters:
        counter_entries, counter_status, counter_clocks = _run_qemu_pinned(
            artifacts, pair, others, clock_paths, COUNTER_CPU, timeout
        )
    merged = merge_pass_entries(timing_entries, counter_entries, tsc_hz)
    return build_boot_record(
        boot_idx,
        merged,
        timing_exit=timing_status,
        counter_exit=counter_status,
        timing_clocks=timing_clocks,
        counter_clocks=counter_clocks,
    )


def run_single(args: argparse.Namespace) -> int:
    """Execute pinned boots for the current tree, save under logs/, and optionally compare."""
    baseline_path = args.baseline
    if baseline_path is None and not args.no_compare and not args.save_baseline:
        candidate_default = LOGS_DIR / DEFAULT_BASELINE_NAME
        if candidate_default.is_file():
            baseline_path = candidate_default
    baseline_record = load_run_json(baseline_path) if baseline_path is not None else None
    if baseline_record is not None and args.boots < MIN_COMPARISON_RUNS:
        raise BenchError(f"baseline comparison requires at least {MIN_COMPARISON_RUNS} boots, got {args.boots}")

    git_state = collect_git_state(TREE)
    artifacts = artifacts_from_tree(TREE) if args.no_build else build_release(TREE, args.lock_stats)
    pair, sibs, others, clock_paths = _isolation_context(args.mode, args.force)
    tsc_hz = measure_tsc_hz()
    host_state = collect_host_state(args.mode, pair, sibs, tsc_hz, args.force, args.counters)

    boots = []
    for idx in range(args.boots):
        print(f"Boot {idx + 1}/{args.boots} on pinned pair {pair}...", flush=True)
        boots.append(
            _boot_pass_record(idx, artifacts, pair, others, clock_paths, tsc_hz, args.counters, args.timeout)
        )

    ts = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    run_record = _assemble_run_record(git_state, host_state, args.mode, pair, args.counters, boots, ts)

    out_path = args.output or default_output_path(LOGS_DIR, git_state, args.mode, ts)
    save_json(out_path, run_record)
    print(f"Saved run: {out_path}")

    if args.save_baseline:
        baseline_out = LOGS_DIR / DEFAULT_BASELINE_NAME
        save_json(baseline_out, run_record)
        print(f"Saved default baseline: {baseline_out}")

    print()
    print(format_run_table(run_record))

    if baseline_record is not None:
        comp = compare_runs(baseline_record, run_record)
        print()
        print(f"Baseline: {baseline_path}")
        print(format_comparison_table(comp))
    return 0


def run_interleaved(args: argparse.Namespace) -> int:
    """Build ref in a scratch worktree, interleave boots with HEAD, save, and compare."""
    if args.boots < MIN_COMPARISON_RUNS:
        raise BenchError(f"--interleave requires at least {MIN_COMPARISON_RUNS} boots, got {args.boots}")

    baseline_sha = _git_output(TREE, "rev-parse", "--verify", f"{args.interleave}^{{commit}}")
    cand_git = collect_git_state(TREE)
    cand_artifacts = artifacts_from_tree(TREE) if args.no_build else build_release(TREE, args.lock_stats)

    SCRATCH_DIR.mkdir(parents=True, exist_ok=True)
    wt_dir = SCRATCH_DIR / f"bench-ref-{os.getpid()}"
    try:
        proc = subprocess.run(
            ["git", "-C", str(TREE), "worktree", "add", "--detach", str(wt_dir), baseline_sha],
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            raise BenchError(f"git worktree add failed for {args.interleave}: {proc.stderr.strip()}")
        base_git = collect_git_state(wt_dir)
        base_artifacts = build_release(wt_dir, args.lock_stats)

        pair, sibs, others, clock_paths = _isolation_context(args.mode, args.force)
        tsc_hz = measure_tsc_hz()
        host_state = collect_host_state(args.mode, pair, sibs, tsc_hz, args.force, args.counters)

        base_boots: list[dict] = []
        cand_boots: list[dict] = []
        for order_idx, (role, boot_idx) in enumerate(interleave_order(args.boots)):
            art = base_artifacts if role == "baseline" else cand_artifacts
            print(
                f"Interleaved boot {order_idx + 1}/{args.boots * 2}: "
                f"{role} ({boot_idx + 1}/{args.boots}) on pair {pair}...",
                flush=True,
            )
            rec = _boot_pass_record(
                boot_idx, art, pair, others, clock_paths, tsc_hz, args.counters, args.timeout
            )
            rec["interleave_order"] = order_idx
            if role == "baseline":
                base_boots.append(rec)
            else:
                cand_boots.append(rec)
    finally:
        if wt_dir.exists():
            subprocess.run(
                ["git", "-C", str(TREE), "worktree", "remove", "--force", str(wt_dir)],
                capture_output=True,
                text=True,
                check=False,
            )
            shutil.rmtree(wt_dir, ignore_errors=True)
        subprocess.run(
            ["git", "-C", str(TREE), "worktree", "prune"],
            capture_output=True,
            text=True,
            check=False,
        )

    ts = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    base_record = _assemble_run_record(base_git, host_state, args.mode, pair, args.counters, base_boots, ts)
    cand_record = _assemble_run_record(cand_git, host_state, args.mode, pair, args.counters, cand_boots, ts)

    base_path = default_output_path(LOGS_DIR, base_git, args.mode, ts, prefix="bench-baseline")
    cand_path = args.output or default_output_path(LOGS_DIR, cand_git, args.mode, ts)
    save_json(base_path, base_record)
    save_json(cand_path, cand_record)
    print(f"Saved baseline run:  {base_path}")
    print(f"Saved candidate run: {cand_path}")
    if args.save_baseline:
        default_base = LOGS_DIR / DEFAULT_BASELINE_NAME
        save_json(default_base, cand_record)
        print(f"Saved default baseline: {default_base}")

    comp = compare_runs(base_record, cand_record)
    comp["baseline_file"] = str(base_path)
    comp["candidate_file"] = str(cand_path)
    comp_path = default_output_path(LOGS_DIR, cand_git, args.mode, ts, prefix="bench-compare")
    save_json(comp_path, comp)
    print(f"Saved comparison:    {comp_path}")
    print()
    print(format_comparison_table(comp))
    return 0


def run_compare_linux(args: argparse.Namespace) -> int:
    """Print medians of an Atmosphere run and a Linux run, joined by label."""
    atmosphere_path, linux_path = args.compare_linux
    atmosphere = load_run_json(atmosphere_path)
    linux_run = load_run_json(linux_path)
    print(f"Atmosphere: {atmosphere_path}")
    print(f"Linux:      {linux_path}")
    print(format_side_by_side(atmosphere, linux_run))
    return 0


def run_compare_only(args: argparse.Namespace) -> int:
    """Load two saved run JSON files and print their comparison table."""
    base_path, cand_path = args.compare_only
    base_record = load_run_json(base_path)
    cand_record = load_run_json(cand_path)
    comp = compare_runs(base_record, cand_record)
    print(f"Baseline:  {base_path}")
    print(f"Candidate: {cand_path}")
    print(format_comparison_table(comp))
    return 0


class Tests(unittest.TestCase):
    """Tier-3 unit tests covering JSON extraction, merging, stats, and comparison."""

    @staticmethod
    def _sample_entries(scale: float = 1.0, with_pmu: bool = False) -> list[dict]:
        check_boot_log = load_tool("check-boot-log.py")
        entries = [
            {
                "label": label,
                "test_suite": check_boot_log.EXPECTED_TEST_SUITE,
                "unit": "cycles",
                "values": [round((base + i) * scale, 3) for i in range(5)],
            }
            for base, label in enumerate(check_boot_log.REQUIRED_BENCHMARKS, start=100)
        ]
        if with_pmu:
            entries.extend([
                {
                    "label": "Syscall/Null.cycles",
                    "test_suite": check_boot_log.EXPECTED_TEST_SUITE,
                    "unit": "cycles",
                    "values": [round((600 + i) * scale, 3) for i in range(5)],
                },
                {
                    "label": "Syscall/Null.instructions",
                    "test_suite": check_boot_log.EXPECTED_TEST_SUITE,
                    "unit": "count",
                    "values": [round((800 + i) * scale, 3) for i in range(5)],
                },
                {
                    "label": "Syscall/Null.fills",
                    "test_suite": check_boot_log.EXPECTED_TEST_SUITE,
                    "unit": "count",
                    "values": [round(0.5 * scale, 3) for _ in range(5)],
                },
                {
                    "label": "Syscall/Null.ccx_fills",
                    "test_suite": check_boot_log.EXPECTED_TEST_SUITE,
                    "unit": "count",
                    "values": [0.0 for _ in range(5)],
                },
            ])
        return entries

    @staticmethod
    def _synthetic_run(
        boot_value_lists: dict[str, list[list[float]]],
        commit: str = "1111111111111111111111111111111111111111",
    ) -> dict:
        check_boot_log = load_tool("check-boot-log.py")
        first_key = next(iter(boot_value_lists))
        n_boots = len(boot_value_lists[first_key])
        boots = []
        for idx in range(n_boots):
            entries = [
                {
                    "label": label,
                    "test_suite": check_boot_log.EXPECTED_TEST_SUITE,
                    "unit": "nanoseconds" if label.endswith(".nanoseconds") else "cycles",
                    "values": list(per_boot[idx]),
                }
                for label, per_boot in boot_value_lists.items()
            ]
            boots.append(build_boot_record(idx, entries))
        summary, perftest = aggregate_boots(boots)
        return {
            "schema_version": 1,
            "timestamp_utc": "2026-11-15T20:00:00Z",
            "commit": commit,
            "short_commit": commit[:12],
            "dirty": False,
            "branch": "main",
            "mode": "within0",
            "pair": [6, 7],
            "host": {"tsc_hz": 4_000_000_000, "isolation_state": "absent"},
            "boots": boots,
            "summary": summary,
            "perftest": perftest,
        }

    def test_extract_perftest_json_valid_with_ansi(self) -> None:
        check_boot_log = load_tool("check-boot-log.py")
        payload = self._sample_entries()
        serial = (
            "\x1b[32mdom0: starting\x1b[0m\r\n"
            + f"\x1b[1m{check_boot_log.JSON_BEGIN_MARKER}\x1b[0m\r\n"
            + json.dumps(payload)
            + "\r\n"
            + f"{check_boot_log.JSON_END_MARKER}\r\n"
            + "dom0 capability done\r\n"
        )
        extracted = extract_perftest_json(serial)
        self.assertEqual(len(extracted), len(payload))
        self.assertEqual(extracted[-1]["label"], "Syscall/Null.tsc_cycles")

    def test_extract_perftest_json_rejects_bad_inputs(self) -> None:
        check_boot_log = load_tool("check-boot-log.py")
        with self.assertRaises(BenchError):
            extract_perftest_json("no markers at all")
        with self.assertRaises(BenchError):
            extract_perftest_json(f"{check_boot_log.JSON_BEGIN_MARKER}\n[]\n")
        with self.assertRaises(BenchError):
            extract_perftest_json(
                f"{check_boot_log.JSON_BEGIN_MARKER}\n{{not json\n{check_boot_log.JSON_END_MARKER}\n"
            )
        incomplete = [self._sample_entries()[0]]
        with self.assertRaises(BenchError):
            extract_perftest_json(
                f"{check_boot_log.JSON_BEGIN_MARKER}\n{json.dumps(incomplete)}\n"
                f"{check_boot_log.JSON_END_MARKER}\n"
            )

    def test_merge_pass_entries_keeps_timing_separate_from_pmu(self) -> None:
        timing = self._sample_entries(scale=1.0, with_pmu=False)
        counter = self._sample_entries(scale=30.0, with_pmu=True)
        merged = merge_pass_entries(timing, counter, tsc_hz=4_000_000_000)
        by_label = {entry["label"]: entry for entry in merged}

        self.assertEqual(by_label["Syscall/Null.tsc_cycles"]["values"], timing[-1]["values"])
        expected_ns = [v / 4.0 for v in timing[-1]["values"]]
        self.assertEqual(by_label["Syscall/Null.nanoseconds"]["unit"], "nanoseconds")
        self.assertEqual(by_label["Syscall/Null.nanoseconds"]["values"], expected_ns)
        self.assertIn("Syscall/Null.cycles", by_label)
        self.assertIn("Syscall/Null.instructions", by_label)
        self.assertIn("Syscall/Null.fills", by_label)
        self.assertIn("Syscall/Null.ccx_fills", by_label)

        no_tsc = merge_pass_entries(timing, None, tsc_hz=None)
        self.assertFalse(any(e["label"].endswith(".nanoseconds") for e in no_tsc))

    def test_summarize_and_aggregate_boots(self) -> None:
        summary = summarize_values([10.0, 20.0, 30.0, 40.0])
        self.assertEqual(summary["count"], 4)
        self.assertEqual(summary["min"], 10.0)
        self.assertEqual(summary["median"], 25.0)
        self.assertEqual(summary["mean"], 25.0)
        self.assertEqual(summary["max"], 40.0)
        self.assertAlmostEqual(summary["std_dev"], statistics.stdev([10.0, 20.0, 30.0, 40.0]))

        run = self._synthetic_run({
            "Syscall/Null.tsc_cycles": [
                [100.0, 100.0],
                [101.0, 101.0],
                [102.0, 102.0],
                [103.0, 103.0],
                [104.0, 104.0],
            ]
        })
        agg = run["summary"]["Syscall/Null.tsc_cycles"]
        self.assertEqual(agg["runs"], 5)
        self.assertEqual(agg["median"], 102.0)
        self.assertEqual(agg["spread_min"], 100.0)
        self.assertEqual(agg["spread_max"], 104.0)
        self.assertEqual(agg["min"], 100.0)
        self.assertEqual(agg["mean"], 102.0)
        self.assertEqual(
            set(run["perftest"][0].keys()),
            {"label", "test_suite", "unit", "values"},
        )
        self.assertEqual(len(run["perftest"][0]["values"]), 10)

    def test_compare_runs_detects_moved_outside_spread(self) -> None:
        baseline = self._synthetic_run(
            {
                "Stable.tsc_cycles": [[100.0], [102.0], [104.0], [101.0], [103.0]],
                "Regressed.tsc_cycles": [[200.0], [202.0], [204.0], [201.0], [203.0]],
                "Improved.tsc_cycles": [[300.0], [302.0], [304.0], [301.0], [303.0]],
                "ZeroSpread.ccx_fills": [[0.0], [0.0], [0.0], [0.0], [0.0]],
                "ZeroBroken.ccx_fills": [[0.0], [0.0], [0.0], [0.0], [0.0]],
                "Removed.tsc_cycles": [[50.0], [50.0], [50.0], [50.0], [50.0]],
            },
            commit="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        )
        candidate = self._synthetic_run(
            {
                "Stable.tsc_cycles": [[101.0], [103.0], [105.0], [102.0], [104.0]],
                "Regressed.tsc_cycles": [[203.0], [204.0], [205.0], [206.0], [207.0]],
                "Improved.tsc_cycles": [[297.0], [298.0], [299.0], [300.0], [301.0]],
                "ZeroSpread.ccx_fills": [[0.0], [0.0], [0.0], [0.0], [0.0]],
                "ZeroBroken.ccx_fills": [[0.5], [0.5], [0.5], [0.5], [0.5]],
                "Added.tsc_cycles": [[75.0], [75.0], [75.0], [75.0], [75.0]],
            },
            commit="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        )
        comp = compare_runs(baseline, candidate)
        by_label = {r["label"]: r for r in comp["rows"]}
        self.assertFalse(by_label["Stable.tsc_cycles"]["moved"])
        self.assertEqual(by_label["Stable.tsc_cycles"]["direction"], "same")

        self.assertTrue(by_label["Regressed.tsc_cycles"]["moved"])
        self.assertEqual(by_label["Regressed.tsc_cycles"]["direction"], "slower")

        self.assertTrue(by_label["Improved.tsc_cycles"]["moved"])
        self.assertEqual(by_label["Improved.tsc_cycles"]["direction"], "faster")

        self.assertFalse(by_label["ZeroSpread.ccx_fills"]["moved"])
        self.assertTrue(by_label["ZeroBroken.ccx_fills"]["moved"])
        self.assertIsNone(by_label["ZeroBroken.ccx_fills"]["delta_pct"])

        self.assertEqual(
            [m["label"] for m in comp["moved"]],
            ["Regressed.tsc_cycles", "Improved.tsc_cycles", "ZeroBroken.ccx_fills"],
        )
        self.assertEqual(comp["missing"], ["Removed.tsc_cycles"])
        self.assertEqual(comp["new"], ["Added.tsc_cycles"])

        rendered = format_comparison_table(comp)
        self.assertIn("Regressed.tsc_cycles", rendered)
        self.assertIn("Improved.tsc_cycles", rendered)
        self.assertIn("MOVED", rendered)

    def test_compare_runs_requires_at_least_five_runs(self) -> None:
        four = self._synthetic_run({"Null.tsc_cycles": [[10.0], [10.0], [10.0], [10.0]]})
        five = self._synthetic_run({"Null.tsc_cycles": [[10.0], [10.0], [10.0], [10.0], [10.0]]})
        with self.assertRaisesRegex(BenchError, "5"):
            compare_runs(four, five)
        with self.assertRaisesRegex(BenchError, "5"):
            compare_runs(five, four)
        with self.assertRaisesRegex(BenchError, "5"):
            compare_runs(five, five, min_runs=4)

    def test_replace_cpu_arg_and_interleave_schedule(self) -> None:
        original = ["-machine", "q35", "-cpu", "Haswell-IBRS,pmu=on,+perfctr-core", "-enable-kvm"]
        updated = replace_cpu_arg(original, TIMING_CPU)
        self.assertEqual(original[3], "Haswell-IBRS,pmu=on,+perfctr-core")
        self.assertEqual(updated[3], "host,pmu=off,-perfctr-core")
        self.assertEqual(replace_cpu_arg(original, COUNTER_CPU)[3], "host,pmu=on")
        with self.assertRaises(BenchError):
            replace_cpu_arg(["-machine", "q35"], TIMING_CPU)

        self.assertEqual(
            interleave_order(3),
            [
                ("baseline", 0),
                ("candidate", 0),
                ("baseline", 1),
                ("candidate", 1),
                ("baseline", 2),
                ("candidate", 2),
            ],
        )

    def test_metadata_capture_and_save_reload_roundtrip(self) -> None:
        git_state = collect_git_state(TREE)
        self.assertEqual(len(git_state["commit"]), 40)
        self.assertIn("branch", git_state)
        host_state = collect_host_state("within0", (6, 7), [6, 7, 22, 23], 4_300_000_000, True, True)
        self.assertEqual(host_state["qemu_timing_cpu"], TIMING_CPU)
        self.assertEqual(host_state["qemu_counter_cpu"], COUNTER_CPU)
        self.assertEqual(host_state["pair"], [6, 7])
        self.assertEqual(len(host_state["loadavg"]), 3)

        with tempfile.TemporaryDirectory() as tmp:
            tmp_dir = Path(tmp)
            run = self._synthetic_run(
                {"Syscall/Null.tsc_cycles": [[250.0], [252.0], [251.0], [253.0], [254.0]]}
            )
            out_path = default_output_path(tmp_dir, run, "within0", "2026-11-15T20:00:00Z")
            self.assertEqual(out_path.name, "bench-20261115T200000Z-111111111111-within0.json")
            save_json(out_path, run)
            reloaded = load_run_json(out_path)
            self.assertEqual(reloaded["commit"], run["commit"])
            self.assertIn("Syscall/Null.tsc_cycles", format_run_table(reloaded))

        args = parse_args(["across", "--boots", "7", "--no-counters", "--save-baseline", "--force"])
        self.assertEqual(args.mode, "across")
        self.assertEqual(args.boots, 7)
        self.assertFalse(args.counters)
        self.assertTrue(args.save_baseline)
        self.assertTrue(args.force)

    def test_side_by_side_joins_by_name(self) -> None:
        atmosphere = self._synthetic_run(
            {
                "Syscall/Null.tsc_cycles": [[100.0, 100.0], [110.0, 110.0]],
                "Null5Step.step1.tsc_cycles": [[1.0, 1.0], [1.0, 1.0]],
            }
        )
        linux_run = self._synthetic_run(
            {
                "Syscall/Null.tsc_cycles": [[50.0, 50.0], [60.0, 60.0]],
                "Thread/CreateStartJoin.tsc_cycles": [[9.0, 9.0], [9.0, 9.0]],
            }
        )
        linux_run["kernel_release"] = "7.2.15-test"
        text = format_side_by_side(atmosphere, linux_run)
        self.assertIn("Linux 7.2.15-test", text)
        syscall = next(line for line in text.splitlines() if line.startswith("Syscall/Null.tsc_cycles"))
        self.assertIn("105.0", syscall)
        self.assertIn("55.0", syscall)
        self.assertIn("Only in Atmosphere: Null5Step.step1.tsc_cycles", text)
        self.assertIn("Only in Linux: Thread/CreateStartJoin.tsc_cycles", text)
        self.assertIn("not a regression", text)
        joined = parse_args(["--compare-linux", "atmo.json", "linux.json"])
        self.assertEqual([str(path) for path in joined.compare_linux], ["atmo.json", "linux.json"])
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            parse_args(["--compare-linux", "a.json", "b.json", "--compare-only", "c.json", "d.json"])


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        prog="tools/bench.py",
        description="Boot the benchmark suite pinned, save JSON under logs/, and compare runs.",
    )
    parser.add_argument(
        "mode",
        nargs="?",
        default="within0",
        choices=("within0", "within1", "across"),
        help="Pinned core placement mode from measure-pinned.py (default: within0)",
    )
    parser.add_argument(
        "--boots",
        type=int,
        default=MIN_COMPARISON_RUNS,
        help=f"Number of boots per run (default: {MIN_COMPARISON_RUNS})",
    )
    counters = parser.add_mutually_exclusive_group()
    counters.add_argument(
        "--counters",
        dest="counters",
        action="store_true",
        default=True,
        help="Run separate PMU counter boots (-cpu host,pmu=on) (default)",
    )
    counters.add_argument(
        "--no-counters",
        dest="counters",
        action="store_false",
        help="Skip PMU counter boots; run timing boots only",
    )
    parser.add_argument(
        "--save-baseline",
        action="store_true",
        help=f"Also write run as default baseline ({DEFAULT_BASELINE_NAME})",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        default=None,
        help="Path to recorded baseline run JSON",
    )
    parser.add_argument(
        "--interleave",
        metavar="REF",
        default=None,
        help="Build git ref REF and interleave baseline and candidate boots",
    )
    parser.add_argument(
        "--compare-only",
        nargs=2,
        metavar=("BASELINE", "CANDIDATE"),
        type=Path,
        default=None,
        help="Compare two saved run JSON files without booting QEMU",
    )
    parser.add_argument(
        "--compare-linux",
        nargs=2,
        metavar=("ATMOSPHERE", "LINUX"),
        type=Path,
        default=None,
        help="Show an Atmosphere run and a Linux run side by side by label, without booting",
    )
    parser.add_argument(
        "--no-compare",
        action="store_true",
        help="Do not compare against default logs/bench-baseline.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Explicit output JSON path",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="Per-boot QEMU timeout in seconds (default: 60)",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Continue when measure-pinned noise checks warn of tasks/IRQs",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Reuse existing target/ release artifacts for the current tree",
    )
    parser.add_argument(
        "--lock-stats",
        action="store_true",
        help="Build kernel with --features lock_stats",
    )
    parser.add_argument(
        "--test",
        action="store_true",
        help="Run unit tests and exit",
    )
    args = parser.parse_args(argv)
    if args.boots < 1:
        parser.error("--boots must be at least 1")
    if args.timeout < 1:
        parser.error("--timeout must be at least 1")
    if args.compare_linux is not None and args.compare_only is not None:
        parser.error("--compare-linux and --compare-only are mutually exclusive")
    return args


def run_tests() -> int:
    """Execute unit tests and return 0 on success, 1 on failure."""
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def main(argv: list[str] | None = None) -> int:
    """Entry point for CLI execution."""
    args = parse_args(argv)
    if args.test:
        return run_tests()
    try:
        if args.compare_linux is not None:
            return run_compare_linux(args)
        if args.compare_only is not None:
            return run_compare_only(args)
        if args.interleave is not None:
            return run_interleaved(args)
        return run_single(args)
    except BenchError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
