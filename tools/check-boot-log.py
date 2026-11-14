#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Hold a dom0 boot's serial log to the checks a boot must pass, on the PC or on QEMU virt.

The log shows, in order, the kernel's line for each of the root's fixed slots with its kind, among them
the free 1G region as one untyped (1 to 2 GiB on x86_64, 2 to 3 GiB on aarch64,
design/test-guest-memory/), dom0's check line, exit marker, eager source line, heap line, freed frame
line, process line, thread line and thread times, registers line, placed thread line, started thread line, suspended thread line, destroyed process line, CPU 1 idle on a syscall stack of its own, a flush IPI acknowledged and both cores contending for the kernel's lock.
With --translation it also shows the kernel enabling the IOMMU's translation.

usage: tools/check-boot-log.py --arch x86_64|aarch64 [--translation] <serial-log | ->
       tools/check-boot-log.py --test    (this script's own tests)

Prints what held and exits 0, or prints the first check that failed and exits 1.
"""
import argparse
import re
import subprocess
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

# The line dom0 prints through its console when every fixed-slot check held.
CONSOLE_LINE = "dom0 slot checks held"

# The line dom0 prints after that check line, and only then exits with success.
EXIT_MARKER = "dom0 capability done"

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

# The line dom0 prints once it suspended the thread it started, twice, and started it again, after the
# suspends a slot without a thread and a copy without control must refuse were refused.
SUSPENDED_LINE = "dom0 thread suspended"

# The line dom0 prints once it destroyed its child process and claimed a capability from the dead child's
# table by a move, after the destroys and the derive a dead process must refuse were refused.
DESTROYED_LINE = "dom0 process destroyed"

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


def boot_log_accepted(serial, arch, translation=False):
    """What held of a successful boot's log on `arch`, or Refused naming the first check that failed."""
    untyped, frames = fixed_slots_printed(serial)
    base = FREE_GIGABYTE[arch]
    gigabyte = f"{base >> 30} to {(base >> 30) + 1} GiB as one 1G untyped"
    if not gigabyte_untyped_printed(serial, base):
        raise Refused(f"the serial log does not show the root holding {gigabyte}")
    if not line_printed(serial, CONSOLE_LINE):
        raise Refused("the serial log does not hold dom0's check line")
    if not line_printed(serial, EXIT_MARKER):
        raise Refused("the serial log does not show dom0's exit marker")
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
    if not line_printed(serial, SUSPENDED_LINE):
        raise Refused(f'the serial log does not show dom0 suspending a thread: "{SUSPENDED_LINE}"')
    if not line_printed(serial, DESTROYED_LINE):
        raise Refused(f'the serial log does not show dom0 destroying its child and claiming a slot: "{DESTROYED_LINE}"')
    if not THREAD_TIMES.search(serial):
        raise Refused("the serial log does not show a thread retype's best and mean cycles beside the before numbers")
    if not second_core_idle(serial):
        raise Refused("the serial log does not show CPU 1 idle on a syscall stack of its own")
    if FLUSH_ACKNOWLEDGED not in serial:
        raise Refused("the serial log does not show CPU 1 acknowledging a flush IPI")
    if LOCK_CONTENDED not in serial:
        raise Refused("the serial log does not show both cores contending for the kernel's lock")
    held = (f"exit status 0, the kernel's per-slot lines with their kinds ({untyped} untyped, {frames} frames), "
            f"{gigabyte}, dom0's check line, exit marker, eager source line, heap line, freed frame line, process line, thread line and thread times, registers line, placed thread line, started thread line, suspended thread line, destroyed process line, "
            f"CPU 1 idle on its own stack, "
            f"a flush IPI acknowledged, the lock contended")
    if not translation:
        return held
    if TRANSLATION_ENABLED not in serial:
        raise Refused("the serial log does not show the IOMMU's translation enabled")
    return f"translation enabled; {held}"


def main(argv):
    parser = argparse.ArgumentParser(prog="tools/check-boot-log.py", description=__doc__.split("\n")[0])
    parser.add_argument("--arch", required=True, choices=sorted(FREE_GIGABYTE))
    parser.add_argument("--translation", action="store_true",
                        help="require the kernel to have enabled the IOMMU's translation")
    parser.add_argument("log", help="the serial log, or - for standard input")
    options = parser.parse_args(argv)
    data = sys.stdin.buffer.read() if options.log == "-" else Path(options.log).read_bytes()
    try:
        print(boot_log_accepted(data.decode("utf-8", errors="replace"), options.arch, options.translation))
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
            + "dom0 freed frame retyped\n"
            "dom0 process retyped\n"
            "thread best 31000 before 57405\n"
            "thread mean 33000 before 59384\n"
            "dom0 threads retyped\n"
            "dom0 thread registers set\n"
            "dom0 thread placed\n"
            "dom0 thread started\n"
            "dom0 thread suspended\n"
            "dom0 process destroyed\n"
            "dom0 eager backed 40\n"
            "dom0 heap allocator held\n"
            "dom0 slot checks held\n"
            "dom0 capability done\n"
            "\x1b[34m INFO CPU 0 syscall stack 0x1000\x1b[0m\n"
            " INFO CPU 1 idle, syscall stack 0x2000\n"
            "flush IPI acknowledged by CPU 1\n"
            "lock contended by 2 cores: pair intact at 400000\n")


class Tests(unittest.TestCase):
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
            ("dom0 freed frame retyped\n", "freed frame"),
            ("dom0 process retyped\n", "child process"),
            ("dom0 threads retyped\n", "threads"),
            ("dom0 thread registers set\n", "a thread's registers"),
            ("dom0 thread placed\n", "placing a thread"),
            ("dom0 thread started\n", "starting a thread"),
            ("dom0 thread suspended\n", "suspending a thread"),
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

    def test_the_eager_line_names_forty_pages(self):
        self.assertIn("eager source", self.refused(boot_log().replace("backed 40\n", "backed 39\n")))

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
        passed = self.run_script(["--arch", "x86_64", "-"], boot_log())
        self.assertEqual(passed.returncode, 0, passed)
        self.assertTrue(passed.stdout.decode().startswith("exit status 0, the kernel's per-slot lines"), passed)
        failed = self.run_script(["--arch", "aarch64", "-"], boot_log())
        self.assertEqual(failed.returncode, 1, failed)
        self.assertEqual(failed.stdout.decode(),
                         "the serial log does not show the root holding 2 to 3 GiB as one 1G untyped\n")
        refused = self.run_script(["--arch", "x86_64", "--translation", "-"], boot_log())
        self.assertEqual(refused.returncode, 1, refused)
        self.assertIn("translation enabled", refused.stdout.decode())


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
