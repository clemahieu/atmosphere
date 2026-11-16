#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Hold a dom0 boot's serial log to the checks a boot must pass, on the PC or on QEMU virt.

The log shows, in order, the kernel's line for each of the root's fixed slots with its kind, among them
the free 1G region as one untyped (1 to 2 GiB on x86_64, 2 to 3 GiB on aarch64,
design/test-guest-memory/), dom0's check line, exit marker, own thread's consumed cycles line, eager source line, heap line, freed frame
line, process line, thread line and thread times, registers line, placed thread line, switched thread line, core 1 thread line, both cores' invocation counts, core 1 unmap acknowledged, started thread line, preempted counts, on aarch64 the thread pointer line, on x86_64 the GS line and the segments line, suspended thread line, core 1 stop and restart, killed thread line and its lag, destroyed process line, CPU 1 idle on a syscall stack of its own, a flush IPI acknowledged and both cores contending for the kernel's lock.
Each of CPU 0 and CPU 1 prints its processor report once; on x86_64 its invpcid bit is the host's, CPUID
Fn0000_0007 EBX bit 10 as /proc/cpuinfo's invpcid flag gives it, which the output records, and its specres bit
is clear; on aarch64 its x86_64 bits are clear.
With --translation it also shows the kernel enabling the IOMMU's translation.

usage: tools/check-boot-log.py --arch x86_64|aarch64 [--translation] <serial-log | ->
       tools/check-boot-log.py --test    (this script's own tests)

Prints what held and exits 0, or prints the first check that failed and exits 1.
"""
import argparse
import re
import subprocess
import sys
import tempfile
import unittest
import unittest.mock
from pathlib import Path

sys.dont_write_bytecode = True

# The line dom0 prints through its console when every fixed-slot check held.
CONSOLE_LINE = "dom0 slot checks held"

# The line dom0 prints after that check line, and only then exits with success.
EXIT_MARKER = "dom0 capability done"

# The line dom0 prints once inspect on its own thread, at root slot 2, reported a nonzero result 5, the
# cycles each of the thread's kernel entries charged it: the result word reached the process.
# design/cpu-time-as-capability/.
OWN_CONSUMED_LINE = "dom0 own thread consumed cycles"

# The line dom0 prints once its eager span source reserved a span, backed it a page at a time until the
# source refused, wrote and read it, released it, backed a page of it again and gave it all back: the 64
# pages dom0 gives the source, less the three table pages of eight pages each the path to the span takes,
# are 40 frames.
EAGER_LINE = "dom0 eager backed 40"

# The line dom0 prints once the global allocator, aheap's heap over an eager source of its own, gave it an
# object of the smallest class, one between a page and a block and one over a block, each written and read
# back and freed, refused a run-sized object once its source was exhausted, and gave one again after
# every one of them was freed.
HEAP_LINE = "dom0 heap allocator held"

# The line dom0 prints once it retyped a 4K frame, deleted its last capability, freed the dead frame
# through retype's free kind and retyped the page again.
FREED_LINE = "dom0 freed frame retyped"

# The line dom0 prints once it retyped a child process from an untyped and inspect found it, after the
# retypes a process must refuse were refused.
PROCESS_LINE = "dom0 process retyped"

# The line dom0 prints once it retyped threads bound to its child process and inspect found one, after the
# retypes a thread must refuse were refused.
THREADS_LINE = "dom0 threads retyped"

# The line dom0 prints once it placed a thread of its child on core 0 through its core capability, after the
# places a placed thread and a priority above a core capability's maximum must refuse were refused.
PLACED_LINE = "dom0 thread placed"

# The line dom0 prints once it started the thread it placed, after the starts an unplaced thread and a
# started one must refuse were refused.
STARTED_LINE = "dom0 thread started"

# The line dom0 prints once a thread of its child, started above dom0, ran in the child's space after a
# reschedule IPI, wrote a word dom0 reads through a frame both spaces map, and suspended itself, so its core
# ran dom0 again.
SWITCHED_LINE = "dom0 thread switched"

# The line dom0 prints once a thread of its child, placed through the root's capability for core 1 and
# started, wrote a word dom0 reads on core 0 through a frame both spaces map while dom0 never left core 0:
# the reschedule IPI reached CPU 1, which ran the thread in the child's space.
CORE_1_LINE = "dom0 thread ran on core 1"

# The lines dom0 prints once a thread of its child on core 1 made invocations while dom0 made its own on
# core 0, until the thread stopped at its count: dom0's count, then the count the thread wrote, neither zero.
INVOKED_COUNTS = re.compile(r"^dom0 invoked [1-9][0-9]* times on core 0\r?\nthread invoked [1-9][0-9]* times on core 1\r?$", re.M)

# The lines dom0 prints around its unmap of a page in its child's space while a thread of the child spins
# on CPU 1, having written the page: before the unmap, and once the page's frame, its capability deleted,
# was freed and retyped, which retype's free allows only once every core that loaded a space has
# acknowledged the unmap's flush. Between them the kernel logs CPU 1 acknowledging the unmap's flush on
# the flush IPI, which the unmap's glue sent it. design/flush-without-waiting/.
CORE_1_UNMAP_LINE = "dom0 unmaps a page core 1 wrote"
CORE_1_FREED_LINE = "dom0 freed the page core 1 wrote"
CORE_1_ACKNOWLEDGED = "CPU 1 acknowledged flush epoch "

# The lines dom0 prints once it and the thread it started, both at priority 0 on core 0, each counted while
# the timer handed the core between them, until dom0 saw the thread's count change three times: dom0's count,
# then the thread's, neither zero.
PREEMPTED_COUNTS = re.compile(r"^dom0 counted [1-9][0-9]* in 3 turns\r?\nthread counted [1-9][0-9]* in 3 turns\r?$", re.M)

# The line dom0 prints on aarch64 once a thread of its child, resumed on core 0 after dom0 wrote TPIDR_EL0, found
# it 0: a core does not pass a thread's TPIDR_EL0 to the next thread it resumes. design/thread-pointer-cleared-on-switch/.
THREAD_POINTER_LINE = "dom0 tpidr_el0 not passed on"
# The line dom0 prints on x86_64 once it made a system call and was taken off core 0 by the timer with GS loaded
# with its own data selector, whose base is 0: the kernel found its core's block without the GS base a process sets.
GS_LOADED_LINE = "dom0 gs loaded across entries"

# The line dom0 prints on x86_64 once a thread of its child, resumed on core 0 after dom0 loaded FS, DS and ES with
# its own data selector, found all three null and an FS base of 0: a core does not pass them from one thread to the next.
SEGMENTS_LINE = "dom0 segments not passed on"

# The lines dom0 prints once every register the syscall ABI preserves kept a distinct value across a
# cheap invocation and across a timer preemption, on both targets. design/syscall-abi-in-registers/.
SYSCALL_REGISTERS_LINE = "dom0 syscall registers held"
PREEMPTION_REGISTERS_LINE = "dom0 preemption registers held"

# The line dom0 prints once acontext starts a second context 16-byte aligned and keeps every saved
# register and stack pointer across switches, on both targets. design/register-convention-of-an-assembly-leaf/.
CONTEXT_SWITCH_REGISTERS_LINE = "dom0 context switch registers held"

# The line dom0 prints once it suspended the thread it started, twice, and started it again, after the
# suspends a slot without a thread and a copy without control must refuse were refused.
SUSPENDED_LINE = "dom0 thread suspended"

# The line dom0 prints once it destroyed its child process and claimed a capability from the dead child's
# table by a move, after the destroys and the derive a dead process must refuse were refused.
DESTROYED_LINE = "dom0 process destroyed"

# The lines dom0 prints once it stopped a thread of its child counting on core 1 from core 0 and started it
# again: how many again returns the suspend took, at least one since the thread was Running on another
# core, before it returned ok and the count held still; then that the count moved after the start.
CORE_1_RESTARTED = re.compile(r"^core 1 stop took [1-9][0-9]* again\r?\ndom0 thread restarted on core 1\r?$", re.M)

# The lines dom0 prints once a thread of its child counting on core 1 stopped counting after dom0 destroyed
# the child: destroy's IPI reached CPU 1, which moved the thread off at that entry. Then how far the count
# went past the value dom0 read as the destroy returned, which a stop by the next tick instead of the IPI
# makes about a slice's worth of counts.
KILLED_LINE = "dom0 thread killed on core 1"
KILL_LAG = re.compile(r"^core 1 lag [0-9]+ counts\r?$", re.M)

# The line dom0 prints once it wrote an entry and a stack into its child's first thread and read them back,
# after the reads and writes the frame must refuse were refused.
REGISTERS_LINE = "dom0 thread registers set"

# The lines dom0 prints before THREADS_LINE: the best and the mean cycles of a thread's retype, each beside
# new_thread's before number.
THREAD_TIMES = re.compile(r"thread best \d+ before 57405\r?\nthread mean \d+ before 59384\r?$", re.M)

# What the kernel logs of the root's untyped and frame capabilities, before it prints each slot.
ROOT_HOLDS = "root holds "

# What the kernel logs for each fixed slot of the root's table, followed by the slot and its kind.
ROOT_SLOT = "root slot "

# The first core, untyped and frame slots of the root's table, and how many cores boot hands the root,
# design/root-process-at-boot/.
ROOT_CORE_SLOT = 5
ROOT_CORES = 32
ROOT_UNTYPED_SLOT = 37
ROOT_FRAME_SLOT = 129

# What the kernel logs once CPU 1 has taken a flush IPI and acknowledged it.
FLUSH_ACKNOWLEDGED = "flush IPI acknowledged by CPU 1"

# What the kernel logs once both cores have contended for its lock with the protected pair intact.
LOCK_CONTENDED = "lock contended by 2 cores: pair intact at 400000"

# What the kernel logs when it turns on the IOMMU's translation.
TRANSLATION_ENABLED = "Enabling translation"

# The base of the 1G region the test guest leaves wholly free. The loader allocates in the first GiB of
# RAM and the firmware above the second, and RAM starts at 0 on the PC and at 1 GiB on QEMU virt:
# design/test-guest-memory/.
FREE_GIGABYTE = {"x86_64": 0x4000_0000, "aarch64": 0x8000_0000}


class Refused(Exception):
    """A check the log does not pass."""


# The line each core's kernel prints once it read its processor report in its own init, with each bit the
# report holds: design/processor-report-read-once/. Every core of the test guest prints one.
PROCESSOR_REPORT = re.compile(r"CPU (\d+) report: invpcid ([01]), pcid ([01]), ibpb ([01]), l1d_flush ([01]), "
                              r"specres ([01])(?:\x1b\[0m)?$")
PROCESSOR_BITS = ("invpcid", "pcid", "ibpb", "l1d_flush", "specres")
REPORTING_CORES = (0, 1)

# The bits a report on each architecture never sets: the x86_64 read leaves specres clear and the aarch64
# read leaves every x86_64 bit clear.
NEVER_SET = {"x86_64": ("specres",), "aarch64": ("invpcid", "pcid", "ibpb", "l1d_flush")}


def processor_reports(serial):
    """Each reporting core's bits, by core; Refused when a core reports twice."""
    reports = {}
    for line in lines(serial):
        match = PROCESSOR_REPORT.search(line)
        if match is None:
            continue
        core = int(match.group(1))
        if core in reports:
            raise Refused(f"the serial log shows CPU {core} reports twice; its report is read once, at boot")
        reports[core] = {bit: match.group(2 + at) == "1" for at, bit in enumerate(PROCESSOR_BITS)}
    return reports


def cpuinfo_invpcid(path):
    """Whether the host's processor sets CPUID Fn0000_0007 EBX bit 10, which Linux names the flag invpcid
    in its first processor's flags line of `path`."""
    for line in path.read_text().splitlines():
        if line.startswith("flags"):
            return "invpcid" in line.split(":", 1)[1].split()
    raise Refused(f"{path} has no flags line to read the host's invpcid from")


def host_invpcid():
    """Whether the host this check runs on, the one the gate boots under KVM on, sets INVPCID."""
    return cpuinfo_invpcid(Path("/proc/cpuinfo"))


def processor_reports_held(serial, arch, invpcid):
    """What held of the cores' processor reports on `arch`, or Refused. On x86_64 each core's invpcid
    bit is `invpcid`, the host's."""
    reports = processor_reports(serial)
    if sorted(reports) != list(REPORTING_CORES):
        raise Refused("the serial log does not show one processor report for each of CPU 0 and CPU 1, "
                      f"but for {', '.join(f'CPU {core}' for core in sorted(reports)) or 'none'}")
    for core in REPORTING_CORES:
        for bit in NEVER_SET[arch]:
            if reports[core][bit]:
                raise Refused(f"the serial log shows CPU {core} reports {bit}, which {arch} never sets")
        if arch == "x86_64" and reports[core]["invpcid"] != invpcid:
            raise Refused(f"the serial log shows CPU {core} reports invpcid {int(reports[core]['invpcid'])}, "
                          f"and the host's CPUID 7 EBX bit 10 is {int(invpcid)}")
    if arch == "x86_64":
        return (f"processor reports of CPU 0 and CPU 1, invpcid {int(invpcid)} as the host's CPUID 7 EBX bit 10, "
                f"pcid {' '.join(str(int(reports[core]['pcid'])) for core in REPORTING_CORES)}, "
                f"ibpb {' '.join(str(int(reports[core]['ibpb'])) for core in REPORTING_CORES)}, "
                f"l1d_flush {' '.join(str(int(reports[core]['l1d_flush'])) for core in REPORTING_CORES)}")
    return (f"processor reports of CPU 0 and CPU 1, "
            f"specres {' '.join(str(int(reports[core]['specres'])) for core in REPORTING_CORES)}")


def lines(text):
    """The log's lines, each without its line ending, as the kernel and dom0 print them."""
    pieces = text.split("\n")
    if pieces and pieces[-1] == "":
        pieces.pop()
    return [piece[:-1] if piece.endswith("\r") else piece for piece in pieces]


def line_printed(serial, wanted):
    """Whether the log holds `wanted` as a line of its own."""
    return any(line.rstrip("\r") == wanted for line in lines(serial))


def after(line, marker):
    """What follows the first `marker` on `line`, or None when it has none."""
    at = line.find(marker)
    return None if at < 0 else line[at + len(marker):]


def fixed_slots_printed(serial):
    """The root's untyped and frame counts when the log prints, in order, one line per fixed slot with its
    kind: process at 1, thread at 2, console at 3, power at 4, the 32 cores from 5, the untyped from 37 and
    the frames from 129, as many as the kernel says the root holds, at least one of each."""
    holds = next((rest for rest in (after(line, ROOT_HOLDS) for line in lines(serial)) if rest is not None), None)
    if holds is None:
        raise Refused("the serial log does not say what the root holds")
    words = [word for word in re.split(r"[^0-9A-Za-z]", holds) if word]
    if len(words) < 5 or words[1:3] != ["untyped", "and"] or words[4] != "frames":
        raise Refused(f"the root's holdings are not counted: {holds}")
    untyped, frames = (int(word) if re.fullmatch(r"[0-9]+", word) else None for word in (words[0], words[3]))
    if not untyped or not frames:
        raise Refused(f"the root holds no untyped or no frames: {holds}")
    expected = [(1, "process"), (2, "thread"), (3, "console"), (4, "power")]
    expected += [(ROOT_CORE_SLOT + c, "core") for c in range(ROOT_CORES)]
    expected += [(ROOT_UNTYPED_SLOT + k, "untyped") for k in range(untyped)]
    expected += [(ROOT_FRAME_SLOT + k, "frame") for k in range(frames)]
    printed = []
    for line in lines(serial):
        slot = after(line, ROOT_SLOT)
        if slot is None:
            continue
        index, _, rest = slot.partition(":")
        kind = re.match(r"[A-Za-z]*", rest.lstrip()).group()
        printed.append((int(index) if re.fullmatch(r"[0-9]+", index) else 0, kind))
    for (number, kind), (want_number, want_kind) in zip(printed, expected):
        if (number, kind) != (want_number, want_kind):
            raise Refused(f'root slot {want_number} prints as "{kind}", not {want_kind}')
    if len(printed) != len(expected):
        raise Refused(f"the serial log prints {len(printed)} of the root's slots, not {len(expected)}")
    return untyped, frames


def gigabyte_untyped_printed(serial, base):
    """Whether the log shows the root holding the 1G region at `base` as one untyped, a 1G block."""
    untyped = f": untyped base {base:#x} order 18 "
    return any(slot.lstrip("0123456789").startswith(untyped)
               for slot in (after(line, ROOT_SLOT) for line in lines(serial)) if slot is not None)


def syscall_stack(serial, label):
    """The hexadecimal address after the first `label` in the log."""
    rest = after(serial, label)
    if rest is None or not rest.startswith("0x"):
        return None
    digits = re.match(r"[0-9A-Fa-f]*", rest[2:]).group()
    return int(digits, 16) if digits else None


def second_core_idle(serial):
    """Whether the log shows CPU 1 reaching its idle loop, on a different syscall stack from CPU 0."""
    first = syscall_stack(serial, "CPU 0 syscall stack ")
    second = syscall_stack(serial, "CPU 1 idle, syscall stack ")
    return first is not None and second is not None and first != second


def core_1_unmap_acknowledged(serial):
    """Whether the log shows dom0's line before its unmap of a page CPU 1 wrote, then the kernel's line for
    CPU 1 acknowledging a flush epoch on a flush IPI, then dom0's line that the page's frame was freed."""
    printed = lines(serial)
    unmapped = next((k for k, line in enumerate(printed) if line == CORE_1_UNMAP_LINE), None)
    freed = next((k for k, line in enumerate(printed) if line == CORE_1_FREED_LINE), None)
    return (unmapped is not None and freed is not None
            and any(CORE_1_ACKNOWLEDGED in line for line in printed[unmapped + 1:freed]))


JSON_BEGIN_MARKER = "--- FUCHSIAPERF JSON BEGIN ---"
JSON_END_MARKER = "--- FUCHSIAPERF JSON END ---"
EXPECTED_TEST_SUITE = "atmosphere.microbenchmarks"
REQUIRED_BENCHMARKS = (
    "Null.tsc_cycles",
    "Null5Step.step1.tsc_cycles",
    "NoOpLoop/100.tsc_cycles",
    "NoOpLoop/1000.tsc_cycles",
    "NoOpLoop/10000.tsc_cycles",
    "Syscall/Null.tsc_cycles",
)
PERFTEST_ENTRY_KEYS = frozenset({"label", "test_suite", "unit", "values"})


def perftest_results_accepted(serial):
    """Extracts and validates one fuchsiaperf.json array between markers, returning parsed entries."""
    import json
    import math

    clean = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", serial)
    raw_lines = clean.splitlines()
    begin = next((i for i, line in enumerate(raw_lines) if line.strip() == JSON_BEGIN_MARKER), None)
    if begin is None:
        raise Refused(f'the serial log does not contain "{JSON_BEGIN_MARKER}"')
    end = next((i for i in range(begin + 1, len(raw_lines)) if raw_lines[i].strip() == JSON_END_MARKER), None)
    if end is None:
        raise Refused(f'the serial log does not contain "{JSON_END_MARKER}" after "{JSON_BEGIN_MARKER}"')
    payload = "\n".join(raw_lines[begin + 1:end]).strip()
    try:
        data = json.loads(payload)
    except json.JSONDecodeError as exc:
        raise Refused(f"perftest JSON is invalid: {exc}") from exc
    if not isinstance(data, list) or not data:
        raise Refused("perftest JSON must be a non-empty array")
    seen_labels = set()
    for index, entry in enumerate(data):
        if not isinstance(entry, dict) or set(entry.keys()) != PERFTEST_ENTRY_KEYS:
            raise Refused(f"perftest entry {index} does not match expected schema keys")
        label = entry["label"]
        suite = entry["test_suite"]
        unit = entry["unit"]
        values = entry["values"]
        if not isinstance(label, str) or not label:
            raise Refused(f"perftest entry {index} has invalid label")
        if label in seen_labels:
            raise Refused(f"duplicate perftest label: {label}")
        seen_labels.add(label)
        if suite != EXPECTED_TEST_SUITE:
            raise Refused(f"perftest entry {label} has unexpected test_suite {suite!r}")
        if not isinstance(unit, str) or not unit:
            raise Refused(f"perftest entry {label} has invalid unit")
        if not isinstance(values, list) or not values:
            raise Refused(f"perftest entry {label} has empty or non-array values")
        for value in values:
            if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value):
                raise Refused(f"perftest entry {label} has non-finite value {value!r}")
    for required in REQUIRED_BENCHMARKS:
        if required not in seen_labels:
            raise Refused(f"perftest JSON is missing required benchmark series {required!r}")
    return data


def boot_log_accepted(serial, arch, translation=False, bench=False, invpcid=None):
    """What held of a successful boot's log on `arch`, or Refused naming the first check that failed.
    `invpcid` is the host's INVPCID bit, read from it when None."""
    untyped, frames = fixed_slots_printed(serial)
    base = FREE_GIGABYTE[arch]
    gigabyte = f"{base >> 30} to {(base >> 30) + 1} GiB as one 1G untyped"
    if not gigabyte_untyped_printed(serial, base):
        raise Refused(f"the serial log does not show the root holding {gigabyte}")
    if not line_printed(serial, CONSOLE_LINE):
        raise Refused("the serial log does not hold dom0's check line")
    if not line_printed(serial, EXIT_MARKER):
        raise Refused("the serial log does not show dom0's exit marker")
    if not line_printed(serial, OWN_CONSUMED_LINE):
        raise Refused(f'the serial log does not show inspect reporting dom0\'s own thread\'s consumed cycles: "{OWN_CONSUMED_LINE}"')
    if not line_printed(serial, EAGER_LINE):
        raise Refused(f'the serial log does not show dom0\'s eager source backing 40 pages: "{EAGER_LINE}"')
    if not line_printed(serial, HEAP_LINE):
        raise Refused(f'the serial log does not show dom0\'s heap allocator check: "{HEAP_LINE}"')
    if not line_printed(serial, FREED_LINE):
        raise Refused(f'the serial log does not show dom0 retyping a freed frame: "{FREED_LINE}"')
    if not line_printed(serial, PROCESS_LINE):
        raise Refused(f'the serial log does not show dom0 retyping a child process: "{PROCESS_LINE}"')
    if not line_printed(serial, THREADS_LINE):
        raise Refused(f'the serial log does not show dom0 retyping threads into its child: "{THREADS_LINE}"')
    if not line_printed(serial, REGISTERS_LINE):
        raise Refused(f'the serial log does not show dom0 setting and reading back a thread\'s registers: "{REGISTERS_LINE}"')
    if not line_printed(serial, PLACED_LINE):
        raise Refused(f'the serial log does not show dom0 placing a thread on core 0: "{PLACED_LINE}"')
    if not line_printed(serial, STARTED_LINE):
        raise Refused(f'the serial log does not show dom0 starting a thread: "{STARTED_LINE}"')
    if not line_printed(serial, SWITCHED_LINE):
        raise Refused(f'the serial log does not show dom0 reading the word a thread of its child wrote: "{SWITCHED_LINE}"')
    if not line_printed(serial, CORE_1_LINE):
        raise Refused(f'the serial log does not show CPU 1 running a thread of dom0\'s child: "{CORE_1_LINE}"')
    if not INVOKED_COUNTS.search(serial):
        raise Refused("the serial log does not show dom0 on core 0 and a thread of its child on core 1 both invoking")
    if not core_1_unmap_acknowledged(serial):
        raise Refused("the serial log does not show CPU 1 acknowledging the flush of dom0's unmap of a page a thread "
                      f'on CPU 1 wrote, between "{CORE_1_UNMAP_LINE}" and "{CORE_1_FREED_LINE}"')
    if not PREEMPTED_COUNTS.search(serial):
        raise Refused("the serial log does not show dom0 and a thread of its child both counting on core 0 under the timer")
    if arch == "aarch64" and not line_printed(serial, THREAD_POINTER_LINE):
        raise Refused(f'the serial log does not show a thread finding TPIDR_EL0 0 after dom0 wrote it: "{THREAD_POINTER_LINE}"')
    if arch == "x86_64" and not line_printed(serial, GS_LOADED_LINE):
        raise Refused(f'the serial log does not show dom0 entering the kernel with GS loaded: "{GS_LOADED_LINE}"')
    if arch == "x86_64" and not line_printed(serial, SEGMENTS_LINE):
        raise Refused(f'the serial log does not show a thread finding null segments after dom0 loaded them: "{SEGMENTS_LINE}"')
    if not line_printed(serial, SYSCALL_REGISTERS_LINE):
        raise Refused(f'the serial log does not show dom0 keeping preserved registers across an invocation: "{SYSCALL_REGISTERS_LINE}"')
    if not line_printed(serial, PREEMPTION_REGISTERS_LINE):
        raise Refused(f'the serial log does not show dom0 keeping preserved registers across a preemption: "{PREEMPTION_REGISTERS_LINE}"')
    if not line_printed(serial, CONTEXT_SWITCH_REGISTERS_LINE):
        raise Refused(f'the serial log does not show dom0 keeping saved registers across a context switch: "{CONTEXT_SWITCH_REGISTERS_LINE}"')
    if not line_printed(serial, SUSPENDED_LINE):
        raise Refused(f'the serial log does not show dom0 suspending a thread: "{SUSPENDED_LINE}"')
    if not CORE_1_RESTARTED.search(serial):
        raise Refused("the serial log does not show dom0 stopping a thread on core 1, after again, and restarting it")
    if not line_printed(serial, DESTROYED_LINE):
        raise Refused(f'the serial log does not show dom0 destroying its child and claiming a slot: "{DESTROYED_LINE}"')
    if not line_printed(serial, KILLED_LINE):
        raise Refused(f'the serial log does not show a thread of dom0\'s child on core 1 stopped by the destroy: "{KILLED_LINE}"')
    if not KILL_LAG.search(serial):
        raise Refused("the serial log does not show how far the count on core 1 went past the destroy")
    if not THREAD_TIMES.search(serial):
        raise Refused("the serial log does not show a thread retype's best and mean cycles beside the before numbers")
    if not second_core_idle(serial):
        raise Refused("the serial log does not show CPU 1 idle on a syscall stack of its own")
    if FLUSH_ACKNOWLEDGED not in serial:
        raise Refused("the serial log does not show CPU 1 acknowledging a flush IPI")
    if LOCK_CONTENDED not in serial:
        raise Refused("the serial log does not show both cores contending for the kernel's lock")
    reports = processor_reports_held(serial, arch, host_invpcid() if invpcid is None and arch == "x86_64" else invpcid)
    held = (f"exit status 0, the kernel's per-slot lines with their kinds ({untyped} untyped, {frames} frames), "
            f"{gigabyte}, dom0's check line, exit marker, own thread's consumed cycles line, eager source line, heap line, freed frame line, process line, thread line and thread times, registers line, placed thread line, switched thread line, core 1 thread line, both cores' invocation counts, core 1 unmap acknowledged, started thread line, preempted counts, "
            f"{'thread pointer line, ' if arch == 'aarch64' else ''}{'GS line, segments line, ' if arch == 'x86_64' else ''}syscall registers line, preemption registers line, context switch registers line, suspended thread line, core 1 stop and restart, killed thread line and its lag, destroyed process line, "
            f"CPU 1 idle on its own stack, "
            f"a flush IPI acknowledged, the lock contended, {reports}")
    if translation:
        if TRANSLATION_ENABLED not in serial:
            raise Refused("the serial log does not show the IOMMU's translation enabled")
        held = f"translation enabled; {held}"
    if bench:
        entries = perftest_results_accepted(serial)
        held = f"{held}; perftest JSON ({len(entries)} series)"
    return held


def main(argv):
    parser = argparse.ArgumentParser(prog="tools/check-boot-log.py", description=__doc__.split("\n")[0])
    parser.add_argument("--arch", choices=sorted(FREE_GIGABYTE))
    parser.add_argument("--translation", action="store_true",
                        help="require the kernel to have enabled the IOMMU's translation")
    parser.add_argument("--bench", action="store_true",
                        help="require a valid fuchsiaperf.json benchmark payload in the log")
    parser.add_argument("log", help="the serial log, or - for standard input")
    options = parser.parse_args(argv)
    if options.arch is None and not options.bench:
        parser.error("--arch is required unless --bench validates only perftest output")
    data = sys.stdin.buffer.read() if options.log == "-" else Path(options.log).read_bytes()
    serial = data.decode("utf-8", errors="replace")
    try:
        if options.arch is None:
            entries = perftest_results_accepted(serial)
            print(f"perftest JSON accepted ({len(entries)} series)")
        else:
            print(boot_log_accepted(serial, options.arch, options.translation, options.bench))
    except Refused as refused:
        print(refused)
        return 1
    return 0


def slot_lines(frame_kind):
    """The kernel's slot lines for a root with two untyped and one frame."""
    return (" INFO root holds 2 untyped and 1 frames\x1b[0m\n INFO root slot 1: process base 0x8000\n"
            " INFO root slot 2: thread\n INFO root slot 3: console\n"
            " INFO root slot 4: power base 0x2000000001000 order 0 rights 0x0\n"
            + "".join(f" INFO root slot {5 + c}: core base {0x2000000002000 + c * 0x1000:#x} order 0 rights 0x0\n"
                      for c in range(32))
            + " INFO root slot 37: untyped base 0x40000000 order 18 rights 0x8\n"
            "\x1b[34m INFO root slot 38: untyped\x1b[0m\n"
            f" INFO root slot 129: {frame_kind} order 0\n")


def boot_log():
    """A boot log with the lines the checks keep, and no capability-entry line."""
    return (slot_lines("frame")
            + "dom0 own thread consumed cycles\n"
            "dom0 freed frame retyped\n"
            "dom0 process retyped\n"
            "thread best 31000 before 57405\n"
            "thread mean 33000 before 59384\n"
            "dom0 threads retyped\n"
            "dom0 thread registers set\n"
            "dom0 thread placed\n"
            "dom0 thread switched\n"
            "dom0 thread ran on core 1\n"
            "dom0 invoked 90000 times on core 0\n"
            "thread invoked 4096 times on core 1\n"
            "dom0 unmaps a page core 1 wrote\n"
            "\x1b[34m INFO CPU 1 acknowledged flush epoch 812\x1b[0m\n"
            "dom0 freed the page core 1 wrote\n"
            "dom0 thread started\n"
            "dom0 counted 41000000 in 3 turns\n"
            "thread counted 39000000 in 3 turns\n"
            "dom0 tpidr_el0 not passed on\n"
            "dom0 gs loaded across entries\n"
            "dom0 segments not passed on\n"
            "dom0 syscall registers held\n"
            "dom0 preemption registers held\n"
            "dom0 context switch registers held\n"
            "dom0 thread suspended\n"
            "core 1 stop took 2 again\n"
            "dom0 thread restarted on core 1\n"
            "dom0 thread killed on core 1\n"
            "core 1 lag 2000 counts\n"
            "dom0 process destroyed\n"
            "dom0 eager backed 40\n"
            "dom0 heap allocator held\n"
            "dom0 slot checks held\n"
            "dom0 capability done\n"
            "\x1b[34m INFO CPU 0 report: invpcid 0, pcid 0, ibpb 0, l1d_flush 0, specres 0\x1b[0m\n"
            " INFO CPU 1 report: invpcid 0, pcid 0, ibpb 0, l1d_flush 0, specres 0\n"
            "\x1b[34m INFO CPU 0 syscall stack 0x1000\x1b[0m\n"
            " INFO CPU 1 idle, syscall stack 0x2000\n"
            "flush IPI acknowledged by CPU 1\n"
            "lock contended by 2 cores: pair intact at 400000\n")


class Tests(unittest.TestCase):
    def setUp(self):
        # The fixture's cores report no INVPCID, so the host the tests run on is taken not to either.
        patcher = unittest.mock.patch.object(sys.modules[__name__], "host_invpcid", lambda: False)
        patcher.start()
        self.addCleanup(patcher.stop)

    def refused(self, serial, arch="x86_64", translation=False):
        with self.assertRaises(Refused) as caught:
            boot_log_accepted(serial, arch, translation)
        return str(caught.exception)

    def test_a_boot_without_a_capability_entry_line_passes(self):
        log = boot_log()
        self.assertNotIn("capability entry", log)
        self.assertIn("1 to 2 GiB as one 1G untyped", boot_log_accepted(log, "x86_64"))
        self.assertIn("(2 untyped, 1 frames)", boot_log_accepted(log, "x86_64"))

    def test_each_line_the_boot_must_print_is_checked(self):
        log = boot_log()
        for removed, named in [
            ("dom0 slot checks held\n", "check line"),
            ("dom0 eager backed 40\n", "eager source"),
            ("dom0 heap allocator held\n", "heap allocator"),
            ("dom0 own thread consumed cycles\n", "own thread's consumed cycles"),
            ("dom0 freed frame retyped\n", "freed frame"),
            ("dom0 process retyped\n", "child process"),
            ("dom0 threads retyped\n", "threads"),
            ("dom0 thread registers set\n", "a thread's registers"),
            ("dom0 thread placed\n", "placing a thread"),
            ("dom0 thread switched\n", "a thread of its child wrote"),
            ("dom0 thread ran on core 1\n", "CPU 1 running a thread"),
            ("dom0 invoked 90000 times on core 0\n", "both invoking"),
            ("thread invoked 4096 times on core 1\n", "both invoking"),
            ("dom0 unmaps a page core 1 wrote\n", "CPU 1 acknowledging the flush"),
            ("\x1b[34m INFO CPU 1 acknowledged flush epoch 812\x1b[0m\n", "CPU 1 acknowledging the flush"),
            ("dom0 freed the page core 1 wrote\n", "CPU 1 acknowledging the flush"),
            ("dom0 thread started\n", "starting a thread"),
            ("dom0 counted 41000000 in 3 turns\n", "both counting"),
            ("thread counted 39000000 in 3 turns\n", "both counting"),
            ("dom0 gs loaded across entries\n", "GS loaded"),
            ("dom0 segments not passed on\n", "null segments"),
            ("dom0 syscall registers held\n", "across an invocation"),
            ("dom0 preemption registers held\n", "across a preemption"),
            ("dom0 context switch registers held\n", "across a context switch"),
            ("dom0 thread suspended\n", "suspending a thread"),
            ("core 1 stop took 2 again\n", "stopping a thread on core 1"),
            ("dom0 thread restarted on core 1\n", "stopping a thread on core 1"),
            ("dom0 thread killed on core 1\n", "stopped by the destroy"),
            ("core 1 lag 2000 counts\n", "past the destroy"),
            ("dom0 process destroyed\n", "destroying its child"),
            ("thread mean 33000 before 59384\n", "mean cycles"),
            ("dom0 capability done\n", "exit marker"),
            ("CPU 1 idle, syscall stack 0x2000\n", "CPU 1 idle"),
            ("flush IPI acknowledged by CPU 1\n", "flush IPI"),
            ("lock contended by 2 cores: pair intact at 400000\n", "contending"),
            (" INFO root slot 4: power base 0x2000000001000 order 0 rights 0x0\n", "root slot 4"),
        ]:
            self.assertIn(removed, log)
            self.assertIn(named, self.refused(log.replace(removed, "")), removed)
        self.refused(log.replace(" INFO root slot 2: thread\n", ""))

    def test_the_thread_pointer_line_is_asked_only_on_aarch64(self):
        virt = boot_log().replace("base 0x40000000 order 18", "base 0x80000000 order 18")
        self.assertIn("thread pointer line", boot_log_accepted(virt, "aarch64"))
        without = "dom0 tpidr_el0 not passed on\n"
        self.assertIn("TPIDR_EL0", self.refused(virt.replace(without, ""), "aarch64"))
        held = boot_log_accepted(boot_log().replace(without, ""), "x86_64")
        self.assertNotIn("thread pointer line", held)

    def test_the_gs_and_segments_lines_are_asked_only_on_x86_64(self):
        virt = boot_log().replace("base 0x40000000 order 18", "base 0x80000000 order 18")
        without = virt.replace("dom0 gs loaded across entries\n", "").replace("dom0 segments not passed on\n", "")
        held = boot_log_accepted(without, "aarch64")
        self.assertNotIn("GS line", held)
        self.assertNotIn("segments line", held)
        held = boot_log_accepted(boot_log(), "x86_64")
        self.assertIn("GS line", held)
        self.assertIn("segments line", held)

    def test_the_preserved_register_lines_are_asked_on_both_targets(self):
        virt = boot_log().replace("base 0x40000000 order 18", "base 0x80000000 order 18")
        self.assertIn("syscall registers line", boot_log_accepted(virt, "aarch64"))
        self.assertIn("preemption registers line", boot_log_accepted(virt, "aarch64"))
        self.assertIn("across an invocation", self.refused(virt.replace("dom0 syscall registers held\n", ""), "aarch64"))
        self.assertIn("across a preemption", self.refused(virt.replace("dom0 preemption registers held\n", ""), "aarch64"))

    def test_each_core_reports_once(self):
        log = boot_log()
        core_1 = " INFO CPU 1 report: invpcid 0, pcid 0, ibpb 0, l1d_flush 0, specres 0\n"
        self.assertIn(core_1, log)
        self.assertIn("one processor report for each of CPU 0 and CPU 1", self.refused(log.replace(core_1, "")))
        self.assertIn("CPU 1 reports twice", self.refused(log.replace(core_1, core_1 + core_1)))
        self.assertIn("one processor report", self.refused(log.replace(core_1, core_1.replace("CPU 1", "CPU 2"))))
        self.assertIn("one processor report", self.refused(log.replace(core_1, core_1.replace("specres 0", "specres"))))
        self.assertEqual(processor_reports(core_1), {1: {"invpcid": False, "pcid": False, "ibpb": False,
                                                         "l1d_flush": False, "specres": False}})

    def test_invpcid_is_the_host_s_on_x86_64(self):
        log = boot_log()
        self.assertIn("processor reports of CPU 0 and CPU 1, invpcid 0 as the host's CPUID 7 EBX bit 10",
                      boot_log_accepted(log, "x86_64"))
        with self.assertRaises(Refused) as caught:
            boot_log_accepted(log, "x86_64", invpcid=True)
        self.assertIn("CPU 0 reports invpcid 0, and the host's CPUID 7 EBX bit 10 is 1", str(caught.exception))
        both = log.replace("invpcid 0", "invpcid 1")
        self.assertIn("invpcid 1 as the host's", boot_log_accepted(both, "x86_64", invpcid=True))
        one = log.replace("CPU 1 report: invpcid 0", "CPU 1 report: invpcid 1")
        self.assertIn("CPU 1 reports invpcid 1, and the host's CPUID 7 EBX bit 10 is 0", self.refused(one))
        self.assertIn("CPU 0 reports specres, which x86_64 never sets",
                      self.refused(log.replace("CPU 0 report: invpcid 0, pcid 0, ibpb 0, l1d_flush 0, specres 0",
                                               "CPU 0 report: invpcid 0, pcid 1, ibpb 0, l1d_flush 0, specres 1")))

    def test_aarch64_reports_no_x86_64_bit(self):
        virt = boot_log().replace("base 0x40000000 order 18", "base 0x80000000 order 18")
        self.assertIn("processor reports of CPU 0 and CPU 1, specres 0 0", boot_log_accepted(virt, "aarch64"))
        self.assertIn("specres 1 1", boot_log_accepted(virt.replace("specres 0", "specres 1"), "aarch64"))
        for bit in ("invpcid", "pcid", "ibpb", "l1d_flush"):
            self.assertIn(f"CPU 0 reports {bit}, which aarch64 never sets",
                          self.refused(virt.replace(f" {bit} 0,", f" {bit} 1,", 1), "aarch64"))

    def test_the_host_s_invpcid_is_its_cpuinfo_flag(self):
        with tempfile.TemporaryDirectory() as directory:
            cpuinfo = Path(directory) / "cpuinfo"
            cpuinfo.write_text("processor\t: 0\nflags\t\t: fpu pcid invpcid_single\n\nprocessor\t: 1\n")
            self.assertFalse(cpuinfo_invpcid(cpuinfo))
            cpuinfo.write_text("flags\t\t: fpu pcid invpcid erms\n")
            self.assertTrue(cpuinfo_invpcid(cpuinfo))
            cpuinfo.write_text("processor\t: 0\n")
            with self.assertRaises(Refused):
                cpuinfo_invpcid(cpuinfo)

    def test_the_eager_line_names_forty_pages(self):
        self.assertIn("eager source", self.refused(boot_log().replace("backed 40\n", "backed 39\n")))

    def test_both_counts_advanced(self):
        self.assertIn("both counting", self.refused(boot_log().replace("thread counted 39000000", "thread counted 0")))
        self.assertIn("both counting", self.refused(boot_log().replace("dom0 counted 41000000", "dom0 counted 0")))
        self.assertIn("both counting", self.refused(boot_log().replace("41000000 in 3 turns", "41000000 in 2 turns")))

    def test_the_stop_on_core_1_returned_again(self):
        self.assertIn("stopping a thread on core 1", self.refused(boot_log().replace("took 2 again", "took 0 again")))

    def valid_bench_log(self):
        import json
        payload = json.dumps([
            {
                "label": label,
                "test_suite": "atmosphere.microbenchmarks",
                "unit": "cycles",
                "values": [10.0, 11.5, 9.75],
            }
            for label in (
                "Null.tsc_cycles",
                "Null5Step.step1.tsc_cycles",
                "NoOpLoop/100.tsc_cycles",
                "NoOpLoop/1000.tsc_cycles",
                "NoOpLoop/10000.tsc_cycles",
                "Syscall/Null.tsc_cycles",
            )
        ])
        return (
            boot_log()
            + "\n--- FUCHSIAPERF JSON BEGIN ---\n"
            + payload
            + "\n--- FUCHSIAPERF JSON END ---\n"
        )

    def test_bench_accepts_perftest_json_with_required_metrics(self):
        log = self.valid_bench_log()
        parsed = perftest_results_accepted(log)
        self.assertEqual(len(parsed), 6)
        self.assertIn("perftest JSON", boot_log_accepted(log, "x86_64", bench=True))

    def test_bench_rejects_missing_or_malformed_perftest_json(self):
        with self.assertRaises(Refused):
            boot_log_accepted(boot_log(), "x86_64", bench=True)
        for bad_json in [
            "not json",
            "{}",
            "[]",
            '[{"label":"Syscall/Null.tsc_cycles","test_suite":"wrong","unit":"cycles","values":[1.0]}]',
            '[{"label":"Syscall/Null.tsc_cycles","test_suite":"atmosphere.microbenchmarks","unit":"cycles","values":[1.0],"extra":1}]',
            '[{"label":"Syscall/Null.tsc_cycles","test_suite":"atmosphere.microbenchmarks","unit":"cycles","values":[]}]',
            '[{"label":"Syscall/Null.tsc_cycles","test_suite":"atmosphere.microbenchmarks","unit":"cycles","values":[null]}]',
            '[{"label":"Null.tsc_cycles","test_suite":"atmosphere.microbenchmarks","unit":"cycles","values":[1.0]}]',
        ]:
            log = (
                boot_log()
                + "\n--- FUCHSIAPERF JSON BEGIN ---\n"
                + bad_json
                + "\n--- FUCHSIAPERF JSON END ---\n"
            )
            with self.assertRaises(Refused, msg=bad_json):
                perftest_results_accepted(log)

    def test_both_cores_invoked(self):
        self.assertIn("both invoking", self.refused(boot_log().replace("invoked 4096 times", "invoked 0 times")))
        self.assertIn("both invoking", self.refused(boot_log().replace("invoked 90000 times", "invoked 0 times")))
        swapped = boot_log().replace("dom0 invoked 90000 times on core 0\nthread invoked 4096 times on core 1\n",
                                     "thread invoked 4096 times on core 1\ndom0 invoked 90000 times on core 0\n")
        self.assertIn("both invoking", self.refused(swapped))

    def test_core_1_acknowledges_between_the_unmap_and_the_free(self):
        log = boot_log()
        acknowledged = "\x1b[34m INFO CPU 1 acknowledged flush epoch 812\x1b[0m\n"
        before = log.replace(acknowledged, "").replace("dom0 unmaps a page core 1 wrote\n",
                                                       acknowledged + "dom0 unmaps a page core 1 wrote\n")
        self.assertIn("CPU 1 acknowledging the flush", self.refused(before))
        after = log.replace(acknowledged, "").replace("dom0 freed the page core 1 wrote\n",
                                                      "dom0 freed the page core 1 wrote\n" + acknowledged)
        self.assertIn("CPU 1 acknowledging the flush", self.refused(after))
        other = log.replace("INFO CPU 1 acknowledged", "INFO CPU 0 acknowledged")
        self.assertIn("CPU 1 acknowledging the flush", self.refused(other))

    def test_the_thread_times_stand_beside_the_before_numbers(self):
        self.assertIn("mean cycles", self.refused(boot_log().replace("before 57405", "before 1")))

    def test_a_slot_of_another_kind_is_named(self):
        self.assertIn("not power", self.refused(boot_log().replace("root slot 4: power", "root slot 4: console")))
        self.assertIn('prints as "console"', self.refused(boot_log().replace("root slot 4: power", "root slot 4: console")))

    def test_the_free_gigabyte_must_be_one_block(self):
        self.assertIn("1G untyped", self.refused(boot_log().replace("base 0x40000000 order 18", "base 0x40000000 order 17")))

    def test_virt_s_gigabyte_is_two_to_three_gib(self):
        log = boot_log()
        virt = log.replace("base 0x40000000 order 18", "base 0x80000000 order 18")
        self.assertIn("2 to 3 GiB as one 1G untyped", boot_log_accepted(virt, "aarch64"))
        self.assertIn("1 to 2 GiB as one 1G untyped", self.refused(virt, "x86_64"))
        self.assertIn("2 to 3 GiB as one 1G untyped", self.refused(log, "aarch64"))

    def test_translation_is_asked_only_under_its_flag(self):
        log = boot_log()
        self.assertIn("translation enabled", self.refused(log, translation=True))
        enabled = log + "\x1b[34m INFO Enabling translation\x1b[0m\n"
        held = boot_log_accepted(enabled, "x86_64", translation=True)
        self.assertTrue(held.startswith("translation enabled; exit status 0, "), held)
        self.assertEqual(boot_log_accepted(log, "x86_64"), boot_log_accepted(enabled, "x86_64"))

    def test_console_line_is_a_line_of_its_own(self):
        self.assertTrue(line_printed(" INFO root slot 3: console\ndom0 slot checks held\n INFO root slot 4: power\n",
                                     CONSOLE_LINE))
        self.assertTrue(line_printed("x\r\ndom0 slot checks held\r\n", CONSOLE_LINE))
        self.assertFalse(line_printed(" INFO dom0 slot checks held\n", CONSOLE_LINE))
        self.assertFalse(line_printed("dom0 slot checks\n", CONSOLE_LINE))

    def test_the_free_gigabyte_is_one_untyped(self):
        pc = FREE_GIGABYTE["x86_64"]
        self.assertEqual(pc, 0x4000_0000)
        self.assertTrue(gigabyte_untyped_printed(slot_lines("frame"), pc))
        self.assertTrue(gigabyte_untyped_printed(
            " INFO root slot 9: untyped base 0x40000000 order 18 rights 0x8\x1b[0m\r\n", pc))
        # Another kind, another base, another order, and a base or an order this one is a prefix of.
        for other in [
            " INFO root slot 129: frame base 0x40000000 order 18 rights 0x8\n",
            " INFO root slot 37: untyped base 0x0 order 18 rights 0x8\n",
            " INFO root slot 37: untyped base 0x40000000 order 9 rights 0x8\n",
            " INFO root slot 37: untyped base 0x400000000 order 18 rights 0x8\n",
            " INFO root slot 37: untyped base 0x40000000 order 180 rights 0x8\n",
            " INFO root holds 2 untyped and 1 frames\n",
        ]:
            self.assertFalse(gigabyte_untyped_printed(other, pc), other)
        # The kernel's line for QEMU virt's block, where RAM starts at 1 GiB.
        virt = FREE_GIGABYTE["aarch64"]
        self.assertEqual(virt, 0x8000_0000)
        self.assertTrue(gigabyte_untyped_printed(" INFO root slot 37: untyped base 0x80000000 order 18 rights 0x8\n", virt))
        self.assertFalse(gigabyte_untyped_printed(" INFO root slot 37: untyped base 0x80000000 order 16 rights 0x8\n", virt))
        self.assertFalse(gigabyte_untyped_printed(slot_lines("frame"), virt))

    def test_a_log_missing_the_exit_marker_does_not_pass(self):
        slots = slot_lines("frame")
        self.assertEqual(fixed_slots_printed(slots), (2, 1))
        self.assertFalse(line_printed(slots, EXIT_MARKER))
        self.assertTrue(line_printed(slots + "dom0 capability done\n", EXIT_MARKER))
        self.assertTrue(line_printed("x\r\ndom0 capability done\r\n", EXIT_MARKER))
        self.assertFalse(line_printed(" INFO dom0 capability done\n", EXIT_MARKER))

    def test_fixed_slots_are_each_printed_with_their_kind(self):
        self.assertEqual(fixed_slots_printed(slot_lines("frame")), (2, 1))
        for wrong in [
            slot_lines("page"),
            slot_lines("untyped"),
            slot_lines("frame").replace(" INFO root slot 2: thread\n", ""),
            slot_lines("frame") + " INFO root slot 130: frame\n",
            slot_lines("frame").replace("holds 2 untyped", "holds 0 untyped"),
            slot_lines("frame").replace("holds 2 untyped", "holds two untyped"),
            " INFO root slot 1: process\n",
        ]:
            with self.assertRaises(Refused, msg=wrong):
                fixed_slots_printed(wrong)

    def test_second_core_idle_on_its_own_stack(self):
        self.assertTrue(second_core_idle("\x1b[34m INFO CPU 0 syscall stack 0x1000\x1b[0m\n"
                                         " INFO CPU 1 idle, syscall stack 0x2000\n"))

    def test_second_core_sharing_a_stack_is_not_idle(self):
        self.assertFalse(second_core_idle("CPU 0 syscall stack 0x1000\nCPU 1 idle, syscall stack 0x1000\n"))

    def test_no_second_core_is_not_idle(self):
        self.assertFalse(second_core_idle("CPU 0 syscall stack 0x1000\n"))
        self.assertFalse(second_core_idle("CPU 0 syscall stack 0x1000\nCPU 1 idle, syscall stack 0x\n"))

    def run_script(self, args, log):
        return subprocess.run([sys.executable, str(Path(__file__).resolve())] + args, input=log.encode(),
                              capture_output=True)

    def test_the_command_reads_standard_input_and_exits_by_the_result(self):
        host = int(cpuinfo_invpcid(Path("/proc/cpuinfo")))
        passed = self.run_script(["--arch", "x86_64", "-"], boot_log().replace("invpcid 0", f"invpcid {host}"))
        self.assertEqual(passed.returncode, 0, passed)
        self.assertTrue(passed.stdout.decode().startswith("exit status 0, the kernel's per-slot lines"), passed)
        failed = self.run_script(["--arch", "aarch64", "-"], boot_log())
        self.assertEqual(failed.returncode, 1, failed)
        self.assertEqual(failed.stdout.decode(),
                         "the serial log does not show the root holding 2 to 3 GiB as one 1G untyped\n")
        refused = self.run_script(["--arch", "x86_64", "--translation", "-"],
                                  boot_log().replace("invpcid 0", f"invpcid {host}"))
        self.assertEqual(refused.returncode, 1, refused)
        self.assertIn("translation enabled", refused.stdout.decode())


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
