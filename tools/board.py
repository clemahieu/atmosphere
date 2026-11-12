#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Boot dom0 on QEMU virt under KVM on the Orange Pi and hold the run to the boot checks.

The run builds the aarch64 images and lays out the partition with tools/aarch64-esp.py, boots it on the
board with tools/orangepi-kvm.py until QEMU exits, writes what the runner printed, the serial log among
it, to target/orangepi-serial.log, and holds it to the checks the gate holds the x86_64 boot to
(tools/check-boot-log.py, with 2 to 3 GiB as the free untyped), the host and KVM named and QEMU's exit
0. A run that fails is also kept under logs/ at the project root, named on a 'kept:' line.

--gate is the gate's aarch64 boot: the build's and the runner's own tests, then the run with an SMMUv3
on the machine, whose translation the kernel must enable, then the run without, so the serial log left
behind has none, as on x86_64. A board ssh cannot reach does not fail it: the runner's skip line is
printed on a line of its own, which the round procedure looks for in a gate log.

The last line on stdout is what held, or `board: FAIL: <what failed>` with exit 1.

usage: tools/board.py [--boot-timeout S] [--command-line LINE] [--iommu]   (from anywhere)
       tools/board.py --gate [--boot-timeout S]
       tools/board.py --test    (this script's own tests)
"""
import argparse
import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

TREE = Path(__file__).resolve().parent.parent

_spec = importlib.util.spec_from_file_location("check_boot_log", TREE / "tools/check-boot-log.py")
check_boot_log = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_boot_log)

# Builds the aarch64 images and lays out the partition the board boots, relative to the project root.
ESP_BUILD = "tools/aarch64-esp.py"

# Boots a partition on the board, relative to the project root; --test runs its own tests.
BOARD_RUN = "tools/orangepi-kvm.py"

# What the runner prints first: the name of the host the guest ran on.
HOST = "host: "

# What the runner prints when it launches QEMU with KVM as its only accelerator.
KVM = "kvm: accel kvm"

# What the runner prints, as its only line, when ssh cannot reach the board.
SKIP = "skip: "

# The partition, relative to the project root.
ESP = "target/orangepi-esp"

# What the board run printed, the serial log among it, relative to the project root.
SERIAL_LOG = "target/orangepi-serial.log"

# The guest's memory: enough that 2 to 3 GiB is free RAM on virt, design/test-guest-memory/.
MEMORY_MIB = 2560

# The command-line key under which the kernel leaves TCR_EL1.HA and HD clear, so that its own faults
# keep the access flag and the dirty state. design/arch-module/ item 5.
FAULT_KEPT = "access_dirty=fault"

# What the kernel logs at the power-off of a run: the faults it served in the walker's place.
FAULTS_SERVED = "Served from EL0: "


class Failed(Exception):
    """A run, or a step before it, that does not pass."""


def skip_line(output):
    """The runner's skip line, when it printed one."""
    return next((line for line in output.splitlines() if line.startswith(SKIP)), None)


def boot_log_accepted(output, translation):
    """What the boot log check holds of the serial log on virt, or Failed naming the check that failed."""
    try:
        return check_boot_log.boot_log_accepted(output, "aarch64", translation)
    except check_boot_log.Refused as refused:
        raise Failed(str(refused)) from None


def faults_served(output):
    """The counts of the kernel's line `Served from EL0: <a> access-flag faults, <d> dirty-state faults`,
    or None when the log has no such line."""
    line = next((line.split(FAULTS_SERVED, 1)[1] for line in output.splitlines() if FAULTS_SERVED in line), None)
    if line is None:
        return None
    access, _, dirty = line.partition(" access-flag faults, ")
    dirty, found, _ = dirty.partition(" dirty-state faults")
    if not found or not access.isdigit() or not dirty.isdigit():
        return None
    return int(access), int(dirty)


def board_run_accepted(code, output, command_line=None, translation=False):
    """What held of a board run that is a successful boot: the board was reached, the runner named the host
    and launched QEMU under KVM, QEMU exited by itself with status 0, which on virt follows only the
    power-off of a run that succeeded, and the serial log passes the boot log check, with the SMMUv3's
    translation enabled under `translation`. Under a `command_line` holding FAULT_KEPT the kernel must
    also have served at least one access-flag fault and one dirty-state fault."""
    skip = skip_line(output)
    if skip is not None:
        raise Failed(f"no run: {skip}")
    host = next((line[len(HOST):] for line in output.splitlines() if line.startswith(HOST)), None)
    if host is None:
        raise Failed(f"{BOARD_RUN} did not name the host it ran on")
    if KVM not in output.splitlines():
        raise Failed(f"{BOARD_RUN} did not say it launched QEMU under KVM")
    if code != 0:
        # The runner's last line says how QEMU ended: `qemu: exit <status>` or `qemu: still running`.
        ended = next((line for line in reversed(output.splitlines()) if line.startswith("qemu: ")), "no 'qemu:' line")
        try:
            boot_log_accepted(output, translation)
        except Failed as failed:
            raise Failed(f"{BOARD_RUN} exited with {code} ({ended}): {failed}") from None
        raise Failed(f"{BOARD_RUN} exited with {code} ({ended}) after a serial log that holds every check")
    held = f"on {host} under KVM: {boot_log_accepted(output, translation)}"
    if command_line is None or FAULT_KEPT not in command_line.split(" "):
        return held
    served = faults_served(output)
    if served is None:
        raise Failed(f"under {FAULT_KEPT} the log has no line '{FAULTS_SERVED.rstrip()}'")
    access, dirty = served
    if access == 0 or dirty == 0:
        raise Failed(f"under {FAULT_KEPT} the kernel served {access} access-flag and {dirty} dirty-state faults, "
                     f"and both kinds must reach it")
    return f"{held}; {access} access-flag and {dirty} dirty-state faults served"


def gate_run_accepted(code, output):
    """What the gate takes from its first board run, the one with an SMMUv3: the skip line of a board that
    was not reached, or what board_run_accepted holds of one that was, the translation enabled among it."""
    skip = skip_line(output)
    if skip is not None and code == 0:
        return f"{skip}: this commit did not boot on aarch64"
    return board_run_accepted(code, output, translation=True)


def kept_prefix(worktree):
    """Where the runner keeps a failed run's output: logs/ at the project root, the worktree's parent,
    beside the gate logs, under the worktree's name, since the next gate in that worktree overwrites
    the serial log."""
    worktree = Path(worktree)
    return worktree.parent / "logs" / f"{worktree.name}-orangepi"


def checked(args):
    """Runs a program from the tree at the project root, its output going to this script's own."""
    status = subprocess.run([str(TREE / args[0])] + args[1:], cwd=TREE, stdin=subprocess.DEVNULL).returncode
    if status != 0:
        raise Failed(f"{' '.join(args)}: exit {status}")


def build(command_line=None):
    """Builds the partition, with `command_line` in its cmdline file when given."""
    checked([ESP_BUILD, ESP] + (["--command-line", command_line] if command_line is not None else []))


def boot(timeout, iommu):
    """Boots the partition on the board until QEMU exits, with an SMMUv3 on the machine under `iommu`;
    returns the runner's exit status and what it printed, which also goes to the serial log."""
    args = [str(TREE / BOARD_RUN), "--esp", ESP, "--memory-mib", str(MEMORY_MIB), "--boot-timeout", str(timeout),
            "--until-exit", "--keep-failed", str(kept_prefix(TREE))] + (["--iommu"] if iommu else [])
    ran = subprocess.run(args, cwd=TREE, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE)
    (TREE / SERIAL_LOG).write_bytes(ran.stdout)
    return ran.returncode, ran.stdout.decode("utf-8", errors="replace")


def gate(timeout, self_tests=None, build=build, boot=boot):
    """The gate's aarch64 boot, as the line it reports. `self_tests`, `build` and `boot` are this
    module's own unless a test gives stand-ins."""
    for program in (ESP_BUILD, BOARD_RUN):
        (self_tests or checked)([program, "--test"])
    build()
    code, output = boot(timeout, True)
    held = gate_run_accepted(code, output)
    if held.startswith(SKIP):
        print(output.rstrip("\n"), flush=True)
    else:
        code, output = boot(timeout, False)
        held = f"with an SMMUv3, {held}; without, {board_run_accepted(code, output)}"
    return f"{ESP_BUILD}'s and {BOARD_RUN}'s tests pass; {held}"


def main(argv):
    parser = argparse.ArgumentParser(prog="tools/board.py", description=__doc__.split("\n")[0])
    parser.add_argument("--boot-timeout", type=int, default=60,
                        help="seconds the guest has to boot, finish and power off (default 60)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--gate", action="store_true", help="the gate's aarch64 boot")
    mode.add_argument("--command-line", metavar="LINE",
                      help=f"the kernel's command line; under {FAULT_KEPT} both kinds of fault must be served")
    parser.add_argument("--iommu", action="store_true",
                        help="put an SMMUv3 on the machine and require its translation enabled")
    options = parser.parse_args(argv)
    if options.gate and options.iommu:
        parser.error("--gate runs with an SMMUv3 and without")
    try:
        if options.gate:
            print(gate(options.boot_timeout))
            return 0
        build(options.command_line)
        code, output = boot(options.boot_timeout, options.iommu)
        print(f"board serial log: {TREE / SERIAL_LOG}")
        print(f"board: ok: {board_run_accepted(code, output, options.command_line, options.iommu)}")
        return 0
    except Failed as failed:
        print(f"board: FAIL: {failed}")
        return 1


def boot_log():
    """The serial log of a boot on the PC that passes the boot log check."""
    return (" INFO root holds 2 untyped and 1 frames\x1b[0m\n INFO root slot 1: process base 0x8000\n"
            " INFO root slot 2: thread\n INFO root slot 3: console\n"
            " INFO root slot 4: power base 0x2000000001000 order 0 rights 0x0\n"
            " INFO root slot 5: untyped base 0x40000000 order 18 rights 0x8\n"
            "\x1b[34m INFO root slot 6: untyped\x1b[0m\n"
            " INFO root slot 129: frame order 0\n"
            "dom0 freed frame retyped\n"
            "dom0 eager backed 40\n"
            "dom0 heap allocator held\n"
            "dom0 slot checks held\n"
            "dom0 capability done\n"
            "\x1b[34m INFO CPU 0 syscall stack 0x1000\x1b[0m\n"
            " INFO CPU 1 idle, syscall stack 0x2000\n"
            "flush IPI acknowledged by CPU 1\n"
            "lock contended by 2 cores: pair intact at 400000\n")


def board_output():
    """A board run's output: the runner's lines, the serial log of a boot on virt, and QEMU's exit."""
    serial = boot_log().replace("base 0x40000000 order 18", "base 0x80000000 order 18")
    return (f"host: orangepi5\nkvm: accel kvm\nguest: started\n{serial}"
            "\x1b[34m INFO The system is shutting down...\x1b[0m\nqemu: exit 0\n")


SHUTTING_DOWN = "\x1b[34m INFO The system is shutting down"


def fault_kept_output(access, dirty):
    """A board run under the key, with the kernel's line of the faults it served."""
    return board_output().replace(
        SHUTTING_DOWN,
        f"\x1b[34m INFO Served from EL0: {access} access-flag faults, {dirty} dirty-state faults\x1b[0m\n{SHUTTING_DOWN}")


def iommu_output():
    """A board run with an SMMUv3, whose kernel enabled its translation."""
    return board_output().replace(SHUTTING_DOWN, f"\x1b[34m INFO Enabling translation\x1b[0m\n{SHUTTING_DOWN}")


FAILED_CHECKS = ("dom0 slot checks held\ndom0 capability done\n", "dom0 slot checks failed\n")


class Tests(unittest.TestCase):
    def failed(self, *args, **kwargs):
        with self.assertRaises(Failed) as caught:
            board_run_accepted(*args, **kwargs)
        return str(caught.exception)

    def test_a_run_that_powered_off_after_every_check_passes(self):
        self.assertIn("2 to 3 GiB as one 1G untyped", board_run_accepted(0, board_output()))

    def test_a_run_still_on_at_the_timeout_fails(self):
        output = board_output().replace("qemu: exit 0\n", "qemu: still running after 60 s\n")
        self.assertIn("qemu: still running after 60 s", self.failed(1, output))

    def test_a_run_that_failed_and_ended_qemu_names_the_check_that_failed(self):
        output = board_output().replace(*FAILED_CHECKS).replace("qemu: exit 0\n", "qemu: exit 1\n")
        error = self.failed(1, output)
        self.assertIn("qemu: exit 1", error)
        self.assertIn("check line", error)

    def test_a_run_whose_checks_failed_fails_whatever_qemu_did(self):
        output = board_output().replace(*FAILED_CHECKS)
        self.failed(1, output)
        self.assertIn("check line", self.failed(0, output))

    def test_a_run_without_the_eager_source_line_fails(self):
        self.assertIn("eager source", self.failed(0, board_output().replace("dom0 eager backed 40\n", "")))

    def test_a_run_without_the_heap_allocator_line_fails(self):
        self.assertIn("heap allocator", self.failed(0, board_output().replace("dom0 heap allocator held\n", "")))

    def test_a_run_on_the_pc_s_memory_map_fails(self):
        output = board_output().replace("base 0x80000000 order 18", "base 0x40000000 order 18")
        self.assertIn("2 to 3 GiB", self.failed(0, output))

    def test_a_run_under_the_key_that_served_both_faults_passes(self):
        held = board_run_accepted(0, fault_kept_output(310, 42), "nologo access_dirty=fault")
        self.assertIn("310 access-flag and 42 dirty-state faults served", held)

    def test_a_run_under_the_key_that_served_none_of_a_kind_fails(self):
        self.assertIn("310 access-flag and 0 dirty-state", self.failed(0, fault_kept_output(310, 0), "access_dirty=fault"))
        self.failed(0, fault_kept_output(0, 42), "access_dirty=fault")

    def test_a_run_under_the_key_without_the_line_fails(self):
        self.assertIn("has no line", self.failed(0, board_output(), "access_dirty=fault"))

    def test_the_line_is_not_asked_of_a_run_without_the_key(self):
        board_run_accepted(0, board_output(), "nologo")
        board_run_accepted(0, fault_kept_output(0, 0))
        board_run_accepted(0, board_output(), "access_dirty=faults")

    def test_a_run_names_the_host_it_ran_on_and_kvm(self):
        self.assertTrue(board_run_accepted(0, board_output()).startswith("on orangepi5 under KVM: "))

    def test_a_run_that_does_not_name_its_host_or_kvm_fails(self):
        self.assertIn("host", self.failed(0, board_output().replace("host: orangepi5\n", "")))
        self.assertIn("KVM", self.failed(0, board_output().replace("kvm: accel kvm\n", "")))

    def test_the_gate_takes_an_unreachable_board_as_a_skip(self):
        held = gate_run_accepted(0, "skip: orangepi5 unreachable\n")
        self.assertTrue(held.startswith("skip: orangepi5 unreachable"), held)

    def test_the_gate_holds_a_reached_board_to_the_boot_checks(self):
        self.assertTrue(gate_run_accepted(0, iommu_output()).startswith("on orangepi5 under KVM: translation enabled; "))
        with self.assertRaises(Failed):
            gate_run_accepted(1, board_output().replace(*FAILED_CHECKS))
        with self.assertRaises(Failed):
            gate_run_accepted(2, "host: orangepi5\nkvm: accel kvm\n")

    def test_a_run_with_an_smmu_that_enabled_translation_passes(self):
        held = board_run_accepted(0, iommu_output(), translation=True)
        self.assertTrue(held.startswith("on orangepi5 under KVM: translation enabled; "), held)

    def test_a_run_with_an_smmu_that_did_not_enable_translation_fails(self):
        self.assertIn("translation enabled", self.failed(0, board_output(), translation=True))
        with self.assertRaises(Failed):
            gate_run_accepted(0, board_output())

    def test_a_failed_run_is_kept_beside_the_gate_logs_under_the_worktree_s_name(self):
        self.assertEqual(kept_prefix("/project/atmo-1.2"), Path("/project/logs/atmo-1.2-orangepi"))

    def test_an_unreachable_board_is_no_run(self):
        self.assertIn("no run: skip: orangepi5 unreachable", self.failed(0, "skip: orangepi5 unreachable\n"))

    def gate_with(self, runs, tests_fail=False):
        """Runs the gate with stand-ins: `runs` are the board runs' (status, output) in turn. Returns the
        line it reported or the Failed it raised, what it printed, and the calls made, in order."""
        calls = []

        def self_tests(args):
            calls.append(" ".join(args))
            if tests_fail:
                raise Failed(f"{' '.join(args)}: exit 1")

        def boot(timeout, iommu):
            calls.append(f"boot {timeout} {'with' if iommu else 'without'}")
            return runs.pop(0)

        printed = []
        stdout, sys.stdout = sys.stdout, type("Out", (), {"write": lambda self, s: printed.append(s),
                                                            "flush": lambda self: None})()
        try:
            result = gate(90, self_tests, lambda: calls.append("build"), boot)
        except Failed as failed:
            result = failed
        finally:
            sys.stdout = stdout
        return result, "".join(printed), calls

    def test_the_gate_boots_with_an_smmu_first_then_without(self):
        line, printed, calls = self.gate_with([(0, iommu_output()), (0, board_output())])
        self.assertEqual(calls, [f"{ESP_BUILD} --test", f"{BOARD_RUN} --test", "build", "boot 90 with", "boot 90 without"])
        self.assertTrue(line.startswith(f"{ESP_BUILD}'s and {BOARD_RUN}'s tests pass; with an SMMUv3, on orangepi5 "
                                        "under KVM: translation enabled; "), line)
        self.assertIn("; without, on orangepi5 under KVM: exit status 0", line)
        self.assertEqual(printed, "")

    def test_the_gate_prints_the_skip_line_on_its_own_and_boots_once(self):
        line, printed, calls = self.gate_with([(0, "skip: orangepi5 unreachable\n")])
        self.assertEqual(calls[-1], "boot 90 with")
        self.assertEqual(printed, "skip: orangepi5 unreachable\n")
        self.assertTrue(line.endswith("tests pass; skip: orangepi5 unreachable: this commit did not boot on aarch64"), line)

    def test_the_gate_fails_on_either_run(self):
        failed, _, _ = self.gate_with([(0, board_output())])
        self.assertIn("translation enabled", str(failed))
        failed, _, calls = self.gate_with([(0, iommu_output()), (1, board_output().replace("qemu: exit 0\n", "qemu: exit 1\n"))])
        self.assertIsInstance(failed, Failed)
        self.assertIn("qemu: exit 1", str(failed))
        self.assertEqual(calls[-1], "boot 90 without")

    def test_the_gate_stops_when_a_tool_s_own_tests_fail(self):
        failed, _, calls = self.gate_with([], tests_fail=True)
        self.assertEqual(str(failed), f"{ESP_BUILD} --test: exit 1")
        self.assertEqual(calls, [f"{ESP_BUILD} --test"])

    def test_the_gate_and_the_iommu_flag_are_refused_together(self):
        ran = subprocess.run([sys.executable, str(Path(__file__).resolve()), "--gate", "--iommu"],
                             capture_output=True, text=True)
        self.assertEqual(ran.returncode, 2, ran)


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
