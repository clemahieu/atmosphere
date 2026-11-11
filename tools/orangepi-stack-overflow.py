#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Boot an aarch64 kernel that overflows one of its stacks under KVM on orangepi5 and check its report.

With --stack boot, the default, the loader is built with small_kernel_stack, a stack below the depth
of the kernel's boot, so the boot runs into the guard the loader leaves unmapped under it. With
--stack syscall the kernel is built with small_syscall_stack, a syscall stack below a call's depth,
so dom0's first call runs into the guard the kernel unmapped under CPU 0's syscall stack. The kernel
must then report once: a synchronous exception from EL1 whose FAR_EL1 lies in the guard the loader
or the kernel logged, with the frame on the core's emergency stack, and stop. The serial log goes to
stdout, and to --log when given.

When ssh cannot reach the board this prints tools/orangepi-kvm.py's skip line and exits 0. This
command is not part of the gate.

usage: tools/orangepi-stack-overflow.py [--stack boot|syscall] [--log FILE]   (from the workspace root)
       tools/orangepi-stack-overflow.py --test
"""
import argparse
import re
import subprocess
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

TREE = Path(__file__).resolve().parent.parent
ESP = "target/orangepi-stack-overflow/{stack}/esp"
MEMORY_MIB = "2560"  # the test guest's, design/test-guest-memory/
BOOT_TIMEOUT = "40"


class Stack:
    """A stack the run overflows: the build that makes it too shallow, the line that names its guard,
    and what is wrong when that line is missing."""

    def __init__(self, build_option, feature, guard, missing):
        self.build_option, self.feature, self.guard, self.missing = build_option, feature, re.compile(guard), missing


STACKS = {
    "boot": Stack("--loader-feature", "small_kernel_stack", r"Kernel stack guard: ([0-9a-f]+)-([0-9a-f]+)",
                  "the loader did not log the stack guard"),
    "syscall": Stack("--kernel-feature", "small_syscall_stack",
                     r"CPU 0 syscall stack 0x[0-9a-f]+-0x[0-9a-f]+, guard 0x([0-9a-f]+)-0x([0-9a-f]+)",
                     "the kernel did not log CPU 0's syscall stack guard"),
}
REPORT = re.compile(r"CPU (\d+): (.+?) from ([^:]+): ESR_EL1 0x([0-9a-f]+), FAR_EL1 0x([0-9a-f]+)")
# The kernel's last line, which ends the run.
STOPPED_TEXT = "stopped. The report ran on the emergency stack"
STOPPED = re.compile(
    r"CPU (\d+): " + re.escape(STOPPED_TEXT) + r" 0x([0-9a-f]+)-0x([0-9a-f]+), and the frame is at 0x([0-9a-f]+)")
KERNEL_LINE = re.compile(r"CPU \d+|panic!")
WHERE = "taken where a vector saves its frame"


def check(log, stack=STACKS["boot"]):
    """What is wrong with the serial log of a run that overflows `stack`; nothing when the report is
    as it must be."""
    failures = []
    guard = stack.guard.search(log)
    if not guard:
        return [stack.missing]
    low, high = (int(guard.group(i), 16) for i in (1, 2))
    reports = list(REPORT.finditer(log))
    if len(reports) != 1:
        return [f"{len(reports)} exception reports, not one"]
    report = reports[0]
    kind, source, address = report.group(2), report.group(3), int(report.group(5), 16)
    if kind != "Synchronous exception" or not source.startswith("EL1,") or WHERE not in source:
        failures.append(f"the report is '{kind} from {source}', not a synchronous exception from EL1, {WHERE}")
    if not low <= address < high:
        failures.append(f"FAR_EL1 {address:#x} is outside the guard {low:#x}-{high:#x}")
    stopped = list(STOPPED.finditer(log))
    if len(stopped) != 1 or stopped[0].start() < report.end():
        return failures + ["the core did not log that it stopped, once, after the report"]
    bottom, top, frame = (int(stopped[0].group(i), 16) for i in (2, 3, 4))
    if stopped[0].group(1) != report.group(1):
        failures.append(f"CPU {stopped[0].group(1)} stopped where CPU {report.group(1)} reported")
    if not bottom <= frame < top:
        failures.append(f"the frame at {frame:#x} is outside the emergency stack {bottom:#x}-{top:#x}")
    if bottom < high and low < top:
        failures.append(f"the emergency stack {bottom:#x}-{top:#x} reaches into the guard {low:#x}-{high:#x}")
    after = KERNEL_LINE.search(log, stopped[0].end())
    if after:
        failures.append(f"the kernel logged after it stopped: {log[after.start():].splitlines()[0]}")
    return failures


def run(name):
    """Builds the partition that overflows the stack `name`, boots it on the board and returns
    orangepi-kvm's output."""
    stack, esp = STACKS[name], ESP.format(stack=name)
    build = subprocess.run(
        [sys.executable, str(TREE / "tools/aarch64-esp.py"), esp, stack.build_option, stack.feature],
        cwd=TREE, capture_output=True, text=True)
    if build.returncode != 0:
        sys.exit(build.stdout + build.stderr)
    guest = subprocess.run(
        [sys.executable, str(TREE / "tools/orangepi-kvm.py"), "--esp", esp, "--memory-mib", MEMORY_MIB,
         "--boot-timeout", BOOT_TIMEOUT, "--wait-for", STOPPED_TEXT],
        cwd=TREE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return guest.stdout.decode(errors="replace")


class Tests(unittest.TestCase):
    LOADER = " INFO Kernel stack guard: 401ec000-402ec000\n INFO Kernel stack: 402ec000-402ee000, boot info at de8e57d8\n"
    REPORT = ("ERROR CPU 0: Synchronous exception from EL1, taken where a vector saves its frame: "
              "ESR_EL1 0x96000047, FAR_EL1 0x402ebd40: Registers {\n    x0: 0x1,\n    spsr_el1: 0x600003c5,\n}\n")
    STOPPED = ("ERROR CPU 0: stopped. The report ran on the emergency stack 0x40092000-0x400a2000, "
               "and the frame is at 0x400a1ef0\n")

    def test_one_report_in_the_guard_on_the_emergency_stack_passes(self):
        log = self.LOADER + self.REPORT + self.STOPPED + "qemu-system-aarch64: terminating on signal 15\n"
        self.assertEqual(check(log), [])

    def test_colour_codes_around_a_line_do_not_hide_it(self):
        log = self.LOADER + "\x1b[31m" + self.REPORT.rstrip("\n") + "\x1b[0m\n\x1b[31m" + self.STOPPED
        self.assertEqual(check(log), [])

    def test_a_log_without_the_guard_fails(self):
        self.assertEqual(check(self.REPORT + self.STOPPED), ["the loader did not log the stack guard"])

    def test_no_report_fails(self):
        self.assertEqual(check(self.LOADER), ["0 exception reports, not one"])

    def test_two_reports_fail(self):
        self.assertEqual(check(self.LOADER + self.REPORT + self.REPORT + self.STOPPED), ["2 exception reports, not one"])

    def test_a_fault_outside_the_guard_fails(self):
        log = self.LOADER + self.REPORT.replace("0x402ebd40", "0x402ec000") + self.STOPPED
        self.assertEqual(check(log), ["FAR_EL1 0x402ec000 is outside the guard 0x401ec000-0x402ec000"])

    def test_a_report_that_is_not_the_frame_save_s_fails(self):
        log = self.LOADER + self.REPORT.replace(", taken where a vector saves its frame", "") + self.STOPPED
        self.assertEqual(len(check(log)), 1)
        log = self.LOADER + self.REPORT.replace("Synchronous exception", "SError") + self.STOPPED
        self.assertEqual(len(check(log)), 1)

    def test_a_report_without_the_stop_fails(self):
        self.assertEqual(check(self.LOADER + self.REPORT),
                         ["the core did not log that it stopped, once, after the report"])
        self.assertEqual(check(self.LOADER + self.STOPPED + self.REPORT),
                         ["the core did not log that it stopped, once, after the report"])

    def test_a_frame_off_the_emergency_stack_fails(self):
        log = self.LOADER + self.REPORT + self.STOPPED.replace("0x400a1ef0", "0x400a2000")
        self.assertEqual(check(log), ["the frame at 0x400a2000 is outside the emergency stack 0x40092000-0x400a2000"])

    def test_an_emergency_stack_in_the_guard_fails(self):
        log = self.LOADER + self.REPORT + self.STOPPED.replace("0x40092000-0x400a2000", "0x402eb000-0x402ed000").replace(
            "0x400a1ef0", "0x402ecef0")
        self.assertEqual(check(log), ["the emergency stack 0x402eb000-0x402ed000 reaches into the guard 0x401ec000-0x402ec000"])

    def test_a_kernel_line_after_the_stop_fails(self):
        log = self.LOADER + self.REPORT + self.STOPPED + " INFO CPU 0 syscall stack 0x400a2130\n"
        self.assertEqual(check(log), ["the kernel logged after it stopped: CPU 0 syscall stack 0x400a2130"])

    SYSCALL = " INFO CPU 0 syscall stack 0x40213000-0x40213400, guard 0x40212000-0x40213000\n"

    def test_a_syscall_stack_overflow_in_its_guard_passes(self):
        log = self.SYSCALL + self.REPORT.replace("0x402ebd40", "0x40212f20") + self.STOPPED
        self.assertEqual(check(log, STACKS["syscall"]), [])

    def test_a_syscall_stack_overflow_checks_the_kernel_s_guard_not_the_loader_s(self):
        log = self.LOADER + self.SYSCALL + self.REPORT + self.STOPPED
        self.assertEqual(check(log, STACKS["syscall"]),
                         ["FAR_EL1 0x402ebd40 is outside the guard 0x40212000-0x40213000"])

    def test_a_syscall_stack_overflow_without_the_kernel_s_guard_fails(self):
        log = self.LOADER + self.REPORT + self.STOPPED
        self.assertEqual(check(log, STACKS["syscall"]), ["the kernel did not log CPU 0's syscall stack guard"])

    def test_another_core_s_stop_fails(self):
        log = self.LOADER + self.REPORT + self.STOPPED.replace("CPU 0", "CPU 1")
        self.assertEqual(check(log), ["CPU 1 stopped where CPU 0 reported"])


def main(argv):
    if argv == ["--test"]:
        return unittest.main(argv=[sys.argv[0]])
    parser = argparse.ArgumentParser(prog="tools/orangepi-stack-overflow.py", description=__doc__.split("\n")[0])
    parser.add_argument("--stack", choices=STACKS, default="boot", help="the stack the run overflows")
    parser.add_argument("--log", type=Path, metavar="FILE", help="where the serial log is also written")
    args = parser.parse_args(argv)
    log = run(args.stack)
    if args.log:
        args.log.write_text(log)
    sys.stdout.write(log)
    if log.startswith("skip:"):
        return 0
    failures = check(log, STACKS[args.stack])
    for failure in failures:
        print("FAIL:", failure)
    print(f"{args.stack} stack overflow: {'FAIL' if failures else 'ok'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
