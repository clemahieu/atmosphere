#!/usr/bin/env python3
"""Boot a kernel whose timer fires for nothing, on both targets, and check that the core reports it and stops.

The kernel is built with stray_timer, which arms CPU 0's timer as it enters dom0, outside the boot
check that waits for the timer on aarch64; nothing else arms it. The kernel must then log one line
naming the stray timer interrupt, on CPU 0, and stop that core, so dom0 never reaches its exit
marker. x86_64 boots under KVM on this host, as tools/check-boot-stack.py boots; the run waits a
while after the report for a second one or the marker. aarch64 boots under KVM on orangepi5, as
tools/orangepi-stack-overflow.py boots, and the run ends at the report; when ssh cannot reach the
board this prints tools/orangepi-kvm.py's skip line and that target passes. This command is not part
of the gate.

usage: tools/check-stray-timer.py [--target x86_64|aarch64] [--log DIR]   (from the workspace root)
       tools/check-stray-timer.py --test
"""
import argparse
import importlib.util
import re
import subprocess
import sys
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

TREE = Path(__file__).resolve().parent.parent
FEATURE = "stray_timer"
# The kernel's report, in kernel/src/arch/*/interrupt.
REPORT_TEXT = "stray timer interrupt"
REPORT = re.compile(r"CPU (\d+): " + REPORT_TEXT)
EXIT_MARKER = "dom0 capability done"
# How long the x86_64 run goes on after the report: room for a second one, or for dom0 to finish.
AFTER_REPORT_S = 2
X86_OUT = "target/stray-timer-check"
AARCH64_ESP = "target/stray-timer-check/aarch64/esp"
MEMORY_MIB = "2560"  # the test guest's, design/test-guest-memory/
BOOT_TIMEOUT = "40"


def check(log):
    """What is wrong with the serial log of a stray_timer run; nothing when the core reported the
    interrupt once, on CPU 0, and stopped before dom0 finished."""
    reports = REPORT.findall(log)
    if len(reports) != 1:
        return [f"{len(reports)} stray timer reports, not one"]
    failures = []
    if reports[0] != "0":
        failures.append(f"the report is on CPU {reports[0]}, not CPU 0, whose timer the build arms")
    if EXIT_MARKER in log:
        failures.append(f"dom0 reached '{EXIT_MARKER}': the core did not stop at the report")
    return failures


def boot_stack_check():
    """tools/check-boot-stack.py, whose build and boot the x86_64 run shares."""
    spec = importlib.util.spec_from_file_location("check_boot_stack", TREE / "tools/check-boot-stack.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_x86_64():
    """Builds the debug images with the kernel's stray_timer, boots them until the report and a
    while after it, and returns the serial log."""
    boot = boot_stack_check()
    Path(X86_OUT).mkdir(parents=True, exist_ok=True)
    boot.build("debug", kernel_features=[FEATURE])
    _, qemu, sock = boot.boot("debug", X86_OUT, marker=REPORT_TEXT.encode())
    time.sleep(AFTER_REPORT_S)
    log = open(f"{X86_OUT}/serial.log", "rb").read().decode(errors="replace")
    sock.sendall(b"quit\n")
    qemu.wait(timeout=30)
    return log


def run_aarch64():
    """Builds the partition with the kernel's stray_timer, boots it on the board until the report and
    returns orangepi-kvm's output."""
    build = subprocess.run(
        [sys.executable, str(TREE / "tools/aarch64-esp.py"), AARCH64_ESP, "--kernel-feature", FEATURE],
        cwd=TREE, capture_output=True, text=True)
    if build.returncode != 0:
        sys.exit(build.stdout + build.stderr)
    guest = subprocess.run(
        [sys.executable, str(TREE / "tools/orangepi-kvm.py"), "--esp", AARCH64_ESP, "--memory-mib", MEMORY_MIB,
         "--boot-timeout", BOOT_TIMEOUT, "--wait-for", REPORT_TEXT],
        cwd=TREE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = guest.stdout.decode(errors="replace")
    if guest.returncode != 0:
        sys.exit(output + f"tools/check-stray-timer.py: the aarch64 run failed with status {guest.returncode}")
    return output


RUNS = {"x86_64": run_x86_64, "aarch64": run_aarch64}


class Tests(unittest.TestCase):
    BOOT = " INFO CPU 0 syscall stack 0x40213000-0x40223000, guard 0x40212000-0x40213000\n INFO initial_sp: 0x7f0000\n"
    REPORT = "ERROR CPU 0: stray timer interrupt, which nothing armed the timer for: Registers {\n    rax: 0x0,\n}\n"

    def test_one_report_on_cpu_0_passes(self):
        self.assertEqual(check(self.BOOT + self.REPORT), [])

    def test_colour_codes_around_the_report_do_not_hide_it(self):
        self.assertEqual(check(self.BOOT + "\x1b[31m" + self.REPORT.rstrip("\n") + "\x1b[0m\n"), [])

    def test_no_report_fails(self):
        self.assertEqual(check(self.BOOT), ["0 stray timer reports, not one"])

    def test_two_reports_fail(self):
        self.assertEqual(check(self.BOOT + self.REPORT + self.REPORT), ["2 stray timer reports, not one"])

    def test_a_report_on_another_core_fails(self):
        self.assertEqual(check(self.BOOT + self.REPORT.replace("CPU 0", "CPU 1")),
                         ["the report is on CPU 1, not CPU 0, whose timer the build arms"])

    def test_dom0_finishing_fails(self):
        self.assertEqual(check(self.BOOT + self.REPORT + " INFO dom0 capability done\n"),
                         ["dom0 reached 'dom0 capability done': the core did not stop at the report"])


def main(argv):
    if argv == ["--test"]:
        return unittest.main(argv=[sys.argv[0]])
    parser = argparse.ArgumentParser(prog="tools/check-stray-timer.py", description=__doc__.split("\n")[0])
    parser.add_argument("--target", choices=RUNS, action="append", help="the target to boot; may repeat (default both)")
    parser.add_argument("--log", type=Path, metavar="DIR", help="where each target's serial log is also written")
    args = parser.parse_args(argv)
    status = 0
    for target in args.target or list(RUNS):
        log = RUNS[target]()
        if args.log:
            args.log.mkdir(parents=True, exist_ok=True)
            (args.log / f"stray-timer-{target}.log").write_text(log)
        sys.stdout.write(log)
        if log.startswith("skip:"):
            print(f"{target} stray timer: skipped")
            continue
        failures = check(log)
        for failure in failures:
            print("FAIL:", failure)
        print(f"{target} stray timer: {'FAIL' if failures else 'ok'}")
        status |= 1 if failures else 0
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
