#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The gate: what makes a commit tested (CLAUDE.md, Gate).

Runs every step in its order, each a check under tools/ or a cargo command from the project root,
then prints one line per step, 'gate <step>: ok|FAIL in <s> s: <detail>', and 'gate total: <s> s'.
It exits 0 when every step it ran passed and 1 otherwise. The steps' own output, a build's or a
boot's, comes above those lines as each step runs. tools/land.py runs it with tools/env.sh sourced.

--target aarch64 runs that target's verify and its boot on the Orange Pi; --target x86_64 runs every
other step, since the workstation that checks the tree as a whole is the x86_64 host. --step runs the
steps it names, in the gate's order, to see one step again without the rest.

usage: tools/gate.py [--target x86_64|aarch64] [--step NAME]... [--boot-timeout SECONDS]
       tools/gate.py --test    (this script's own tests)
"""
import argparse
import os
import subprocess
import sys
import tempfile
import time
import unittest
from collections import namedtuple
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
X86_64, AARCH64 = "x86_64", "aarch64"
# Seconds dom0 has to boot and finish before a run counts as a hang.
BOOT_TIMEOUT = 120

# The largest file the tree may hold. The largest source is a seventh of this, so anything over it is
# a build or solver output that .gitignore missed.
MAX_FILE_BYTES = 1 << 20
VERIFY = "tools/verify.py"
# The number of verification errors the gate accepts, for each target alone.
VERIFY_ALLOWANCE = "tools/verify-allowance"
# Marks Verus's results line, one per crate.
VERIFY_RESULTS = "verification results:: "
BUILD = "tools/build.py"
STACK_SIZES_CHECK = "tools/check-stack-sizes.py"
LICENSE_CHECK = "tools/check-licenses.py"
SOURCE_LICENSE_CHECK = "tools/check-spdx.py"
HOOK_TESTS = (".claude/hooks/license-guard-test.sh", ".claude/hooks/beads-actor-test.sh")
EXTERNAL_BODY_CHECK = "tools/check-external-body.py"
PAGE_LITERALS_CHECK = "tools/check-page-literals.py"
ARCH_SOURCES_CHECK = "tools/check-arch-sources.py"
UPSTREAM_COPIES_CHECK = "tools/check-upstream-copies.py"
DESIGN_INDEX = "tools/build-design-index.py"
BOOT_STACK_CHECK = "tools/check-boot-stack.py"
COVERAGE = "tools/coverage.py"
RUN = "tools/run.py"
GDB = "tools/gdb.py"
BOOT_LOG_CHECK = "tools/check-boot-log.py"
# The boot's serial log, which tools/run.py writes at the project root.
SERIAL_LOG = "serial.log"
BOARD = "tools/board.py"
# cargo's arguments for every workspace member's tests, each test's output in the log.
WORKSPACE_TESTS = ("test", "--workspace", "--", "--nocapture")
# Marks cargo test's result line, one per test binary, and the line of a binary with a failing test.
TEST_RESULT = "test result: "
TEST_FAILED = "test result: FAILED"
# timeout's status when the command it ran did not exit in time.
TIMED_OUT = 124


class Failure(Exception):
    """A step that does not hold; its message is the step's detail."""


Ran = namedtuple("Ran", "code stdout")


class Gate:
    """Runs the gate's programs from the project root. The tests replace call."""

    def __init__(self, root, boot_timeout):
        self.root = Path(root)
        self.boot_timeout = boot_timeout

    def call(self, argv, capture=False, merge=False, stdin=None):
        """Runs a program, a path relative to the root or a name on PATH, at the root: its exit
        status, and its stdout when captured, with its stderr too under merge. Its uncaptured output
        goes to the gate's own."""
        sys.stdout.flush()
        program = str(self.root / argv[0]) if "/" in argv[0] else argv[0]
        try:
            done = subprocess.run(
                [program, *argv[1:]], cwd=self.root,
                input=stdin.encode() if stdin is not None else None,
                stdin=subprocess.DEVNULL if stdin is None else None,
                stdout=subprocess.PIPE if capture else None,
                stderr=subprocess.STDOUT if merge else None)
        except OSError as error:
            raise Failure(f"{argv[0]}: {error.strerror}") from None
        return Ran(done.returncode, done.stdout.decode(errors="replace") if capture else "")


def status(code):
    """An exit status as a line names it."""
    return f"signal: {-code}" if code < 0 else f"exit status: {code}"


def run_check(gate, *argv):
    """Runs a check, its output in the gate's; fails with its exit status."""
    code = gate.call(argv).code
    if code != 0:
        raise Failure(f"{' '.join(argv)}: {status(code)}")


def check_output(gate, program):
    """Runs a check and returns what it printed to stdout; its stderr goes to the gate's."""
    ran = gate.call([program], capture=True)
    if ran.code != 0:
        raise Failure(f"{program}: {status(ran.code)}")
    return ran.stdout


def self_tested(program):
    """The step that runs a check's own tests, then the check, and gives what the check printed."""
    def step(gate):
        run_check(gate, program, "--test")
        return check_output(gate, program).rstrip()
    return step


def oversized(sizes):
    return [path for path, size in sizes if size > MAX_FILE_BYTES]


def file_sizes(gate):
    """Looks at everything `git add -A` would take, tracked or not, since the gate runs before the
    commit."""
    ran = gate.call(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], capture=True)
    if ran.code != 0:
        raise Failure(f"git ls-files: {status(ran.code)}")
    sizes = []
    for path in filter(None, ran.stdout.split("\0")):
        try:
            sizes.append((path, os.lstat(gate.root / path).st_size))
        except FileNotFoundError:
            pass  # Deleted and not yet staged, so the commit will not hold it.
    over = oversized(sizes)
    if over:
        raise Failure(f"over {MAX_FILE_BYTES} bytes: {', '.join(over)}")
    return f"{len(sizes)} files, none over {MAX_FILE_BYTES} bytes"


def last_line(text):
    lines = text.splitlines()
    return lines[-1] if lines else ""


def build(gate):
    """The stack frame check's and the build's own tests, then the build, which runs that check on
    each ELF it makes. The build's last line says what it built, or what failed."""
    run_check(gate, STACK_SIZES_CHECK, "--test")
    run_check(gate, BUILD, "--test")
    ran = gate.call([BUILD], capture=True)
    if ran.code != 0:
        raise Failure(f"{BUILD}: {status(ran.code)}: {last_line(ran.stdout)}")
    return last_line(ran.stdout)


def marked_lines(output, marker):
    """The lines of a run's output that hold marker, each on a line of its own."""
    return "".join(f"\n  {line.strip()}" for line in output.splitlines() if marker in line)


def test_totals(output):
    """What cargo test's result lines add up to: the tests that passed, and the test binaries that
    ran one."""
    passed = binaries = 0
    for line in output.splitlines():
        if TEST_RESULT not in line:
            continue
        words = line.split()
        at = words.index("passed;") - 1 if "passed;" in words else -1
        if at < 0 or not words[at].isdigit():
            raise Failure(f"no count of passed tests in: {line.strip()}")
        passed += int(words[at])
        binaries += int(words[at]) > 0
    return passed, binaries


def workspace_tests(gate):
    """Every workspace member's host tests, unit, integration and doc, by one cargo test from the
    root: a member built for bare metal runs its tests here as a host program. After the build,
    since the dom0 run check in boot-host-tests reads the built dom0. boot-host-tests holds the
    loader map check, whose lines start with 'free page ranges:', and the dom0 run check, whose lines
    start with 'mapped runs:'."""
    command = "cargo " + " ".join(WORKSPACE_TESTS)
    ran = gate.call(["cargo", *WORKSPACE_TESTS], capture=True)
    print(ran.stdout, end="")
    if ran.code != 0:
        raise Failure(f"{command}: {status(ran.code)}{marked_lines(ran.stdout, TEST_FAILED)}")
    passed, binaries = test_totals(ran.stdout)
    if passed == 0:
        raise Failure(f"{command}: no test ran")
    return f"{passed} tests passed in {binaries} test binaries"


def hooks(gate):
    for test in HOOK_TESTS:
        run_check(gate, test)
    return "the license guard refuses what it must; the actor hook names the session"


def parse_allowance(text):
    text = text.strip()
    return int(text) if text.isdigit() else None


def parse_verify_errors(line):
    """The error count of a 'verification results:: N verified, M errors' line, or None."""
    _, marker, results = line.partition(VERIFY_RESULTS)
    fields = results.split(", ")
    if not marker or len(fields) < 2:
        return None
    count = fields[1].split(" ")[0]
    return int(count) if count.isdigit() else None


def verify_for(*args):
    """Verus for one target, the host's with no arguments or the one --target names, against the
    allowance. The script exits non-zero whenever a crate has an error, so its status alone does not
    decide the step. The detail carries each crate's results line."""
    def step(gate):
        allowance = parse_allowance((gate.root / VERIFY_ALLOWANCE).read_text())
        if allowance is None:
            raise Failure(f"{VERIFY_ALLOWANCE} does not hold a number")
        command = " ".join([VERIFY, *args])
        ran = gate.call([VERIFY, *args], capture=True, merge=True)
        counts = [count for count in map(parse_verify_errors, ran.stdout.splitlines()) if count is not None]
        if not counts:
            # A crate that does not compile prints no results line, which is not zero errors.
            raise Failure(f"{command}: {status(ran.code)}, no verification results line: {last_line(ran.stdout)}")
        errors = sum(counts)
        if errors == 0 and ran.code != 0:
            raise Failure(f"{command}: {status(ran.code)} with no errors counted")
        results = marked_lines(ran.stdout, VERIFY_RESULTS)
        if errors > allowance:
            raise Failure(f"{command}: {errors} errors, allowance {allowance}{results}")
        return f"{errors} errors, allowance {allowance}{results}"
    return step


def verify(gate):
    run_check(gate, VERIFY, "--test")
    return verify_for()(gate)


def design_index(gate):
    """design/INDEX.md is generated from the records, so a record edited without regenerating it
    would leave the index saying something the records do not."""
    run_check(gate, DESIGN_INDEX, "--check")
    return "design/INDEX.md is current"


def boot_stack(gate):
    # Each profile's overflow builds come first, so the images left behind are the normal ones.
    for args in (["--test"], ["debug", "overflow"], ["debug", "syscall-overflow"], ["debug"],
                 ["release", "overflow"], ["release", "syscall-overflow"], ["release"]):
        run_check(gate, BOOT_STACK_CHECK, *args)
    return "its own tests, then debug and release, normal, boot stack overflow and syscall stack overflow"


def coverage(gate):
    """Coverage per crate after the script's own tests pass. A low number does not fail the gate:
    only a capture that fails does."""
    run_check(gate, COVERAGE, "--test")
    report = check_output(gate, COVERAGE).rstrip()
    return "\n  " + report.replace("\n", "\n  ")


def boot_with(*args):
    """A boot by tools/run.py with args in which dom0 exited with success, which it does only when
    the kernel gave the statuses it expected, and whose serial log passes the boot log check, with
    the IOMMU's translation enabled under --iommu. Gives what the check saw."""
    def step(gate):
        log = gate.root / SERIAL_LOG
        log.unlink(missing_ok=True)
        # timeout signals its whole process group, which takes QEMU down with the script.
        code = gate.call(["timeout", str(gate.boot_timeout), RUN, *args]).code
        if code == TIMED_OUT:
            raise Failure(f"no exit within {gate.boot_timeout} s")
        if code != 0:
            raise Failure(f"{RUN}: {status(code)}")
        check = [BOOT_LOG_CHECK, "--arch", X86_64, *(["--translation"] if "--iommu" in args else []), "-"]
        ran = gate.call(check, capture=True, stdin=log.read_text(errors="replace"))
        said = ran.stdout.rstrip()
        if ran.code == 0:
            return said
        raise Failure(said if ran.code == 1 else f"{BOOT_LOG_CHECK}: {status(ran.code)}")
    return step


def boot(gate):
    run_check(gate, RUN, "--test")
    run_check(gate, GDB, "--test")
    return f"{RUN}'s and {GDB}'s tests pass; {boot_with()(gate)}"


def board(gate):
    """The aarch64 boot by tools/board.py --gate. Its last line on stdout is what held or what failed;
    the lines above it, the runner's skip line of an unreachable board among them, go to the gate's
    output, where the round procedure looks for that line."""
    ran = gate.call([BOARD, "--gate", "--boot-timeout", str(gate.boot_timeout)], capture=True)
    print(ran.stdout, end="")
    if ran.code != 0:
        raise Failure(f"{BOARD} --gate: {status(ran.code)}: {last_line(ran.stdout)}")
    return f"{BOARD} --gate: {last_line(ran.stdout)}"


Step = namedtuple("Step", "name target check")

STEPS = (
    Step("file sizes", X86_64, file_sizes),
    Step("build", X86_64, build),
    Step("workspace tests", X86_64, workspace_tests),
    Step("license", X86_64, self_tested(LICENSE_CHECK)),
    Step("source licenses", X86_64, self_tested(SOURCE_LICENSE_CHECK)),
    Step("hooks", X86_64, hooks),
    Step("verify", X86_64, verify),
    Step("verify aarch64", AARCH64, verify_for("--target", AARCH64)),
    Step("external body", X86_64, self_tested(EXTERNAL_BODY_CHECK)),
    Step("page literals", X86_64, self_tested(PAGE_LITERALS_CHECK)),
    Step("arch sources", X86_64, self_tested(ARCH_SOURCES_CHECK)),
    Step("upstream copies", X86_64, self_tested(UPSTREAM_COPIES_CHECK)),
    Step("design index", X86_64, design_index),
    Step("boot stack", X86_64, boot_stack),
    Step("coverage", X86_64, coverage),
    # The plain boot comes after it, so the serial.log the gate leaves has no IOMMU.
    Step("iommu boot", X86_64, boot_with("--iommu")),
    Step("boot", X86_64, boot),
    Step("aarch64 boot", AARCH64, board),
)


def chosen(target=None, names=None):
    """The steps the gate runs, in its order: those of target, or of both, and of names when given."""
    return [step for step in STEPS
            if (target is None or step.target == target) and (names is None or step.name in names)]


def step_line(name, ok, detail, seconds):
    """A step's result line, with its wall time, so a log shows what each step costs."""
    return f"gate {name}: {'ok' if ok else 'FAIL'} in {seconds:.1f} s: {detail}"


def total_line(seconds):
    """The gate's last line: its wall time from the first step's start to the last step's end."""
    return f"gate total: {seconds:.1f} s"


def run_gate(gate, steps, clock=time.monotonic):
    """Runs the steps in turn, each to its end whatever the others did; the result lines and the exit
    status."""
    lines, failed = [], False
    started = clock()
    for step in steps:
        start = clock()
        try:
            ok, detail = True, step.check(gate)
        except (Failure, OSError) as error:
            ok, detail = False, str(error)
        failed |= not ok
        lines.append(step_line(step.name, ok, detail, clock() - start))
    lines.append(total_line(clock() - started))
    return lines, 1 if failed else 0


def arguments(argv):
    parser = argparse.ArgumentParser(prog="tools/gate.py", description="The gate: what makes a commit tested.")
    parser.add_argument("--target", choices=(X86_64, AARCH64),
                        help="one target's steps: aarch64 is its verify and its boot on the Orange Pi, x86_64 every other step")
    parser.add_argument("--step", action="append", choices=[step.name for step in STEPS], metavar="NAME",
                        help="run this step; repeat for more (default every step)")
    parser.add_argument("--boot-timeout", type=int, default=BOOT_TIMEOUT,
                        help=f"seconds dom0 has to boot and finish before the run counts as a hang (default {BOOT_TIMEOUT})")
    return parser.parse_args(argv)


def main(argv):
    args = arguments(argv)
    lines, code = run_gate(Gate(REPO, args.boot_timeout), chosen(args.target, args.step))
    print()
    print("\n".join(lines))
    return code


class FakeGate(Gate):
    """A gate whose programs answer from a table, a command line or a program to (exit status,
    stdout), with every other program exiting 0 with nothing to say; a boot that exits 0 leaves an
    empty serial log. It records each call."""

    def __init__(self, root, answers=None, boot_timeout=BOOT_TIMEOUT):
        super().__init__(root, boot_timeout)
        self.answers = answers or {}
        self.calls = []

    def call(self, argv, capture=False, merge=False, stdin=None):
        self.calls.append(list(argv))
        code, stdout = self.answers.get(" ".join(argv), self.answers.get(argv[0], (0, "")))
        if argv[0] == "timeout" and code == 0:
            (self.root / SERIAL_LOG).write_text("")
        return Ran(code, stdout if capture else "")


class Tests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "tools").mkdir()
        (self.root / VERIFY_ALLOWANCE).write_text("2\n")

    def test_runs_both_targets_unless_one_is_named(self):
        self.assertIsNone(arguments([]).target)
        self.assertEqual(arguments(["--target", "aarch64"]).target, AARCH64)
        self.assertEqual(arguments(["--target", "x86_64"]).target, X86_64)
        self.assertEqual(arguments([]).boot_timeout, BOOT_TIMEOUT)

    def test_the_aarch64_target_is_its_verify_and_the_board_boot(self):
        names = lambda steps: [step.name for step in steps]
        self.assertEqual(names(chosen(AARCH64)), ["verify aarch64", "aarch64 boot"])
        x86_64 = names(chosen(X86_64))
        for name in ("boot", "verify", "source licenses", "page literals", "arch sources"):
            self.assertIn(name, x86_64)
        # The dom0 run check among the workspace's tests reads the built dom0.
        self.assertLess(x86_64.index("build"), x86_64.index("workspace tests"))
        self.assertNotIn("verify aarch64", x86_64)
        both = names(chosen())
        self.assertEqual(len(both), len(x86_64) + 2)
        self.assertEqual(both[-1], "aarch64 boot")

    def test_named_steps_run_in_the_gates_order(self):
        self.assertEqual([step.name for step in chosen(names=["boot", "file sizes"])], ["file sizes", "boot"])
        self.assertEqual(chosen(AARCH64, ["boot"]), [])

    def test_each_step_line_carries_its_wall_time(self):
        self.assertEqual(step_line("verify", True, "0 errors, allowance 0", 212.449),
                         "gate verify: ok in 212.4 s: 0 errors, allowance 0")
        self.assertEqual(step_line("boot", False, "no exit within 120 s", 120.051),
                         "gate boot: FAIL in 120.1 s: no exit within 120 s")
        self.assertEqual(step_line("hooks", True, "x", 0), "gate hooks: ok in 0.0 s: x")
        self.assertEqual(total_line(431.96), "gate total: 432.0 s")

    def test_a_file_over_the_limit_is_named(self):
        sizes = [("small.rs", MAX_FILE_BYTES), ("solver.profile", MAX_FILE_BYTES + 1)]
        self.assertEqual(oversized(sizes), ["solver.profile"])
        self.assertEqual(oversized(sizes[:1]), [])

    def test_file_sizes_read_what_git_would_take(self):
        (self.root / "small.rs").write_bytes(b"x")
        (self.root / "solver.profile").write_bytes(b"x" * (MAX_FILE_BYTES + 1))
        listing = "small.rs\0gone.rs\0"
        self.assertEqual(file_sizes(FakeGate(self.root, {"git": (0, listing)})), f"1 files, none over {MAX_FILE_BYTES} bytes")
        with self.assertRaisesRegex(Failure, "over 1048576 bytes: solver.profile$"):
            file_sizes(FakeGate(self.root, {"git": (0, listing + "solver.profile\0")}))

    def test_allowance_is_one_number(self):
        self.assertEqual(parse_allowance("2\n"), 2)
        self.assertIsNone(parse_allowance("two\n"))
        self.assertIsNone(parse_allowance(""))

    def test_verify_errors_come_from_the_results_line(self):
        self.assertEqual(parse_verify_errors("verification results:: 513 verified, 2 errors"), 2)
        self.assertEqual(parse_verify_errors("verification results:: 7 verified, 0 errors"), 0)
        self.assertIsNone(parse_verify_errors("error: cannot find macro"))

    def test_verify_results_lines_are_each_crates_line(self):
        output = "warning: x\nverification results:: 1345 verified, 0 errors\nnote: y\nverification results:: 5 verified, 0 errors\n"
        self.assertEqual(marked_lines(output, VERIFY_RESULTS),
                         "\n  verification results:: 1345 verified, 0 errors\n  verification results:: 5 verified, 0 errors")

    def test_verify_holds_the_errors_to_the_allowance(self):
        two = "verification results:: 9 verified, 1 errors\nverification results:: 5 verified, 1 errors\n"
        self.assertEqual(verify_for()(FakeGate(self.root, {VERIFY: (1, two)})),
                         "2 errors, allowance 2\n  verification results:: 9 verified, 1 errors\n  verification results:: 5 verified, 1 errors")
        three = two + "verification results:: 1 verified, 1 errors\n"
        with self.assertRaisesRegex(Failure, "^tools/verify.py --target aarch64: 3 errors, allowance 2"):
            verify_for("--target", AARCH64)(FakeGate(self.root, {VERIFY: (1, three)}))
        with self.assertRaisesRegex(Failure, "no verification results line: error: aborting$"):
            verify_for()(FakeGate(self.root, {VERIFY: (1, "error: aborting\n")}))
        with self.assertRaisesRegex(Failure, "exit status: 1 with no errors counted"):
            verify_for()(FakeGate(self.root, {VERIFY: (1, "verification results:: 9 verified, 0 errors\n")}))
        (self.root / VERIFY_ALLOWANCE).write_text("two\n")
        with self.assertRaisesRegex(Failure, "does not hold a number"):
            verify_for()(FakeGate(self.root))

    def test_test_totals_add_up_each_binarys_line(self):
        output = ("running 2 tests\ntest a ... ok\nfree page ranges: rejected x\ntest result: ok. 2 passed; 0 failed; 0 ignored\n\n"
                  "running 0 tests\ntest result: ok. 0 passed; 0 failed; 0 ignored\n\ntest result: ok. 61 passed; 0 failed; 0 ignored\n")
        self.assertEqual(test_totals(output), (63, 2))
        self.assertEqual(test_totals("error: could not compile\n"), (0, 0))
        with self.assertRaises(Failure):
            test_totals("test result: ok. some passed\n")

    def test_failed_result_lines_are_the_failing_binaries(self):
        output = "test result: ok. 2 passed; 0 failed\ntest b ... FAILED\ntest result: FAILED. 8 passed; 1 failed\n"
        self.assertEqual(marked_lines(output, TEST_FAILED), "\n  test result: FAILED. 8 passed; 1 failed")
        cargo = "cargo " + " ".join(WORKSPACE_TESTS)
        with self.assertRaisesRegex(Failure, "exit status: 101\n  test result: FAILED. 8 passed; 1 failed$"):
            workspace_tests(FakeGate(self.root, {cargo: (101, output)}))
        with self.assertRaisesRegex(Failure, "no test ran"):
            workspace_tests(FakeGate(self.root, {cargo: (0, "test result: ok. 0 passed; 0 failed\n")}))

    def test_a_boot_that_hangs_or_fails_its_log_check_fails(self):
        (self.root / SERIAL_LOG).write_text("old\n")
        hang = FakeGate(self.root, {"timeout": (TIMED_OUT, "")}, boot_timeout=7)
        with self.assertRaisesRegex(Failure, "^no exit within 7 s$"):
            boot_with()(hang)
        self.assertFalse((self.root / SERIAL_LOG).exists())
        held = FakeGate(self.root, {BOOT_LOG_CHECK: (0, "exit status 0, translation enabled\n")})
        self.assertEqual(boot_with("--iommu")(held), "exit status 0, translation enabled")
        self.assertEqual(held.calls[-1], [BOOT_LOG_CHECK, "--arch", X86_64, "--translation", "-"])
        with self.assertRaisesRegex(Failure, "^no exit marker$"):
            boot_with()(FakeGate(self.root, {BOOT_LOG_CHECK: (1, "no exit marker\n")}))

    def test_every_step_fails_the_gate_when_a_program_it_runs_fails(self):
        """One failing run per step: each program a step runs, in turn, exits 1 with nothing said."""
        good = {VERIFY: (0, "verification results:: 1 verified, 0 errors\n"),
                "cargo " + " ".join(WORKSPACE_TESTS): (0, "test result: ok. 1 passed; 0 failed\n")}
        for step in STEPS:
            passing = FakeGate(self.root, dict(good))
            lines, code = run_gate(passing, [step])
            self.assertEqual(code, 0, lines)
            for program in [" ".join(argv) for argv in passing.calls]:
                with self.subTest(step=step.name, program=program):
                    lines, code = run_gate(FakeGate(self.root, {**good, program: (1, "")}), [step])
                    self.assertEqual(code, 1)
                    self.assertRegex(lines[0], f"^gate {step.name}: FAIL in ")

    def test_a_failing_step_does_not_stop_the_steps_after_it(self):
        ticks = iter(range(100))
        lines, code = run_gate(FakeGate(self.root, {"git": (128, "")}), chosen(names=["file sizes", "hooks"]), lambda: next(ticks))
        self.assertEqual(code, 1)
        self.assertEqual(lines, ["gate file sizes: FAIL in 1.0 s: git ls-files: exit status: 128",
                                 "gate hooks: ok in 1.0 s: the license guard refuses what it must; the actor hook names the session",
                                 "gate total: 5.0 s"])

    def test_a_program_that_cannot_start_fails_its_step(self):
        with self.assertRaisesRegex(Failure, "^tools/missing.py: No such file or directory$"):
            Gate(self.root, BOOT_TIMEOUT).call(["tools/missing.py"])


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
