#!/usr/bin/env python3
"""Boot a kernel that panics at boot, on both targets, and check that the panic ends the run with a failure.

The kernel is built with boot_panic, which panics on CPU 0 once its command line is read. The kernel
must log the panic and end the run through the machine's failure shutdown, so QEMU exits with status
1 by itself instead of running until the runner's timeout. x86_64 boots under tools/run.py --kernel-feature
boot_panic on this host, and QEMU must exit within AFTER_PANIC_S of the panic line. aarch64 boots
under KVM on orangepi5 through tools/orangepi-kvm.py --until-exit, which brings the serial log back
only when QEMU has exited, and QEMU must exit by itself within the boot timeout; when ssh cannot
reach the board this prints tools/orangepi-kvm.py's skip line and that target passes. This command is
not part of atmo test.

usage: tools/check-boot-panic.py [--target x86_64|aarch64] [--log DIR]   (from the workspace root)
       tools/check-boot-panic.py --test
"""
import argparse
import os
import re
import signal
import subprocess
import sys
import threading
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

TREE = Path(__file__).resolve().parent.parent
FEATURE = "boot_panic"
# The kernel's panic handler's line, in kernel/src/main.rs, with the panic boot_panic asks for.
PANIC = re.compile(r"panic! .*boot_panic: the panic this build asks for")
# What the machine's shutdown logs first, in machine/*/src/shutdown.rs.
SHUTDOWN = "The system is shutting down..."
EXIT_MARKER = "dom0 capability done"
# How long QEMU may run on after the panic line: the failure shutdown is a few port or register writes.
AFTER_PANIC_S = 5
# How long the x86_64 run may take in all, build included, before it counts as spinning.
X86_TIMEOUT_S = 600
# orangepi-kvm.py's line for QEMU's own exit, and its status for a guest that writes pvpanic.
BOARD_EXIT = re.compile(r"^qemu: exit (\d+)$", re.M)
FAILURE_STATUS = 1
AARCH64_ESP = "target/boot-panic-check/aarch64/esp"
MEMORY_MIB = "2560"  # the test guest's, design/test-guest-memory/
# Firmware and loader take most of this; a kernel that spun after its panic would run to its end.
BOOT_TIMEOUT = "40"


def check(log, status):
    """What is wrong with a boot_panic run's serial log and exit status; nothing when the kernel
    logged the panic once, the machine's shutdown followed it, dom0 never ran and QEMU exited with
    the failure status."""
    failures = []
    panics = [m.start() for m in PANIC.finditer(log)]
    if len(panics) != 1:
        failures.append(f"{len(panics)} boot_panic panic lines, not one")
    elif log.find(SHUTDOWN, panics[0]) < 0:
        failures.append(f"no '{SHUTDOWN}' after the panic line: the handler did not take the failure shutdown")
    if EXIT_MARKER in log:
        failures.append(f"dom0 reached '{EXIT_MARKER}': the kernel did not stop at the panic")
    if status != FAILURE_STATUS:
        failures.append(f"QEMU's status is {status}, not {FAILURE_STATUS}")
    return failures


def check_after_panic(seconds):
    """What is wrong with how long QEMU ran on after the panic line; None when it was never seen."""
    if seconds is None:
        return []
    if seconds > AFTER_PANIC_S:
        return [f"QEMU ran {seconds:.1f} s after the panic line, more than {AFTER_PANIC_S} s"]
    return []


def run_x86_64():
    """Boots tools/run.py with the kernel's boot_panic and returns (serial log, QEMU's status, the
    seconds QEMU ran after the panic line). A run still going AFTER_PANIC_S after the panic line is
    stopped, QEMU with it, and its status is None."""
    # A session of its own, so stopping the run stops the QEMU it started.
    run = subprocess.Popen([sys.executable, str(TREE / "tools/run.py"), "--kernel-feature", FEATURE],
                           cwd=TREE, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           start_new_session=True)
    lines = []
    seen = []
    def read():
        for line in run.stdout:
            lines.append(line)
            if not seen and PANIC.search(line.decode(errors="replace")):
                seen.append(time.monotonic())
    reader = threading.Thread(target=read)
    reader.start()
    deadline = time.monotonic() + X86_TIMEOUT_S
    status = None
    while status is None and time.monotonic() < deadline:
        if seen and time.monotonic() > seen[0] + AFTER_PANIC_S:
            break
        status = run.poll()
        time.sleep(0.1)
    ended = time.monotonic()
    if status is None:
        # SIGTERM, which run.py takes as a reason to remove its run directory.
        os.killpg(run.pid, signal.SIGTERM)
        run.wait()
    reader.join()
    log = b"".join(lines).decode(errors="replace")
    after = ended - seen[0] if seen else None
    if status is None:
        log += "tools/check-boot-panic.py: QEMU still running, stopped\n"
    return log, status, after


def run_aarch64():
    """Builds the partition with the kernel's boot_panic, boots it on the board until QEMU exits and
    returns (orangepi-kvm's output, QEMU's status, None). The status is None when the board was not
    reached or QEMU did not exit by itself."""
    build = subprocess.run(
        [sys.executable, str(TREE / "tools/aarch64-esp.py"), AARCH64_ESP, "--kernel-feature", FEATURE],
        cwd=TREE, capture_output=True, text=True)
    if build.returncode != 0:
        sys.exit(build.stdout + build.stderr)
    guest = subprocess.run(
        [sys.executable, str(TREE / "tools/orangepi-kvm.py"), "--esp", AARCH64_ESP, "--memory-mib", MEMORY_MIB,
         "--boot-timeout", BOOT_TIMEOUT, "--until-exit"],
        cwd=TREE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = guest.stdout.decode(errors="replace")
    exits = BOARD_EXIT.findall(output)
    return output, int(exits[-1]) if exits else None, None


RUNS = {"x86_64": run_x86_64, "aarch64": run_aarch64}


class Tests(unittest.TestCase):
    BOOT = " INFO Command line: qemu_debug_exit_io_base=244\n"
    PANIC = ("ERROR panic! PanicInfo { message: boot_panic: the panic this build asks for, location: "
             "Location { file: \"src/main.rs\", line: 79, col: 9 } }\n")
    SHUTDOWN = " INFO The system is shutting down...\n"

    def test_a_panic_then_the_failure_shutdown_passes(self):
        self.assertEqual(check(self.BOOT + self.PANIC + self.SHUTDOWN, 1), [])

    def test_colour_codes_around_the_lines_do_not_hide_them(self):
        log = self.BOOT + "\x1b[31m" + self.PANIC.rstrip("\n") + "\x1b[0m\n" + self.SHUTDOWN
        self.assertEqual(check(log, 1), [])

    def test_no_panic_fails(self):
        self.assertEqual(check(self.BOOT + self.SHUTDOWN, 1), ["0 boot_panic panic lines, not one"])

    def test_a_panic_without_the_shutdown_fails(self):
        self.assertEqual(check(self.BOOT + self.PANIC, 1),
                         ["no 'The system is shutting down...' after the panic line: "
                          "the handler did not take the failure shutdown"])

    def test_a_shutdown_only_before_the_panic_fails(self):
        self.assertEqual(check(self.BOOT + self.SHUTDOWN + self.PANIC, 1),
                         ["no 'The system is shutting down...' after the panic line: "
                          "the handler did not take the failure shutdown"])

    def test_dom0_finishing_fails(self):
        self.assertEqual(check(self.BOOT + self.PANIC + self.SHUTDOWN + " INFO dom0 capability done\n", 1),
                         ["dom0 reached 'dom0 capability done': the kernel did not stop at the panic"])

    def test_a_power_off_fails(self):
        self.assertEqual(check(self.BOOT + self.PANIC + self.SHUTDOWN, 0), ["QEMU's status is 0, not 1"])

    def test_a_run_that_was_stopped_fails(self):
        self.assertEqual(check(self.BOOT + self.PANIC, None),
                         ["no 'The system is shutting down...' after the panic line: "
                          "the handler did not take the failure shutdown",
                          "QEMU's status is None, not 1"])

    def test_an_exit_soon_after_the_panic_passes(self):
        self.assertEqual(check_after_panic(0.3), [])

    def test_an_exit_long_after_the_panic_fails(self):
        self.assertEqual(check_after_panic(5.5), ["QEMU ran 5.5 s after the panic line, more than 5 s"])

    def test_the_board_s_exit_line_is_qemu_s_status(self):
        out = "guest: started\n" + self.PANIC + "qemu: exit 1\n"
        self.assertEqual(BOARD_EXIT.findall(out), ["1"])

    def test_a_board_run_that_was_stopped_has_no_exit_line(self):
        self.assertEqual(BOARD_EXIT.findall("guest: started\nqemu: still running after 40 s\n"), [])


def main(argv):
    if argv == ["--test"]:
        return unittest.main(argv=[sys.argv[0]])
    parser = argparse.ArgumentParser(prog="tools/check-boot-panic.py", description=__doc__.split("\n")[0])
    parser.add_argument("--target", choices=RUNS, action="append", help="the target to boot; may repeat (default both)")
    parser.add_argument("--log", type=Path, metavar="DIR", help="where each target's serial log is also written")
    args = parser.parse_args(argv)
    status = 0
    for target in args.target or list(RUNS):
        log, qemu_status, after = RUNS[target]()
        if args.log:
            args.log.mkdir(parents=True, exist_ok=True)
            (args.log / f"boot-panic-{target}.log").write_text(log)
        sys.stdout.write(log)
        if log.startswith("skip:"):
            print(f"{target} boot panic: skipped")
            continue
        failures = check(log, qemu_status) + check_after_panic(after)
        for failure in failures:
            print("FAIL:", failure)
        timing = f", QEMU exited {after:.1f} s after the panic line" if after is not None and not failures else ""
        print(f"{target} boot panic: {'FAIL' if failures else 'ok'}{timing}")
        status |= 1 if failures else 0
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
