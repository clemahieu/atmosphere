#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The gate: what makes a commit tested (CLAUDE.md, Gate).

Runs every step in its order, each a check under tools/ or a cargo command from the project root,
then prints one line per step, 'gate <step>: ok|FAIL in <s> s: <detail>', and 'gate total: <s> s'.
It exits 0 when every step it ran passed and 1 otherwise. The steps' own output, a build's or a
boot's, comes above those lines as each step runs. It sets the toolchain's environment itself (tools/toolchain.py).

--target aarch64 runs that target's verify and its boot on the Orange Pi; --target x86_64 runs every
other step, since the workstation that checks the tree as a whole is the x86_64 host. --step runs the
steps it names, in the gate's order, to see one step again without the rest. --since BASE selects
only unbounded steps and the bounded steps whose declared inputs intersect the diff since BASE.
--steps prints the selected step names without running them. --unread prints tracked files covered
by no bounded step. --check-inputs materializes a sibling hardlinked tree holding only each bounded
step's declared inputs and runs selected bounded steps inside those isolated views.

usage: tools/gate.py [--target x86_64|aarch64] [--step NAME]... [--since BASE] [--steps] [--check-inputs] [--boot-timeout SECONDS]
       tools/gate.py --unread
       tools/gate.py --test    (this script's own tests)
"""
import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
import unittest
from collections import Counter, namedtuple
from pathlib import Path, PurePosixPath
from unittest import mock

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
X86_64, AARCH64 = "x86_64", "aarch64"
# Seconds dom0 has to boot and finish before a run counts as a hang.
BOOT_TIMEOUT = 120

# The largest file the tree may hold. The largest source is a seventh of this, so anything over it is
# a build or solver output that .gitignore missed.
MAX_FILE_BYTES = 1 << 20
# Everything `git add -A` would take, tracked or not, NUL-separated.
FILE_LISTING = ("git", "ls-files", "-z", "--cached", "--others", "--exclude-standard")
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
LAYOUT_CLAIMS_CHECK = "tools/check-layout-claims.py"
BOUNDARY_CHECK = "tools/check-boundary.py"
THROWAWAY_CHECK = "tools/check-throwaways.py"
REFUSED_CHECK = "tools/check-refused.py"
INVOKED_ARMS_CHECK = "tools/check-invoked-arms.py"
WITNESS_INVENTORY = "tools/witness-inventory.py"
# Every way an operation succeeds that no witness reaches, one line each: path, operation and way,
# separated by tabs.
UNWITNESSED = "tools/unwitnessed"
# Every way with no refused claim, not exempt and not an entry the operations it reaches cover.
UNREFUSED = "tools/unrefused"
PAGE_LITERALS_CHECK = "tools/check-page-literals.py"
ARCH_SOURCES_CHECK = "tools/check-arch-sources.py"
UPSTREAM_COPIES_CHECK = "tools/check-upstream-copies.py"
DESIGN_INDEX = "tools/build-design-index.py"
FAQ_RENDER = "tools/faq.py"
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
# The workspace's members, whose manifests cargo names by absolute path.
WORKSPACE_MEMBERS = ("cargo", "metadata", "--no-deps", "--format-version", "1")
# The forced lint check runs from each member's directory for the target its .cargo config names,
# the host's when it has none, then from these directories for the aarch64 targets the aarch64
# build makes: a JSON spec relative to the directory, or a triple rustc has built in.
FORCED_LINT_AARCH64 = (
    ("kernel/verified", "../src/aarch64-unknown-aloader.json"),
    ("kernel", "src/aarch64-unknown-aloader.json"),
    ("dom0", "src/aarch64-unknown-aloader.json"),
    ("user/hello", "../aarch64-unknown-aloader.json"),
    ("aloader", "aarch64-unknown-uefi"),
)
# Forced, so no allow in the source hides dead code or an unused import.
FORCED_LINT_ENV = {"RUSTFLAGS": "--force-warn dead_code --force-warn unused_imports"}
FORCED_LINT_CHECK = ("cargo", "check", "--message-format=json")
FORCED_LINT_TARGET = ("-Zjson-target-spec", "--target")
# A warning as rustc renders it: its header line, then the line that locates its primary span.
WARNING_HEADER = re.compile(r"^warning(?:\[\w+\])?: (.*)$")
WARNING_LOCATION = re.compile(r"^\s*--> (.+):(\d+):(\d+)$")
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

    def call(self, argv, capture=False, merge=False, stdin=None, cwd=None, env=None):
        """Runs a program, a path relative to the root or a name on PATH, at the root or in its
        directory cwd, with env added to the gate's environment: its exit status, and its stdout
        when captured, with its stderr too under merge. Its uncaptured output goes to the gate's
        own."""
        sys.stdout.flush()
        program = str(self.root / argv[0]) if "/" in argv[0] else argv[0]
        try:
            done = subprocess.run(
                [program, *argv[1:]], cwd=self.root / (cwd or ""),
                env={**os.environ, **env} if env else None,
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


def check_output(gate, *argv):
    """Runs a check and returns what it printed to stdout; its stderr goes to the gate's."""
    ran = gate.call(argv, capture=True)
    if ran.code != 0:
        raise Failure(f"{' '.join(argv)}: {status(ran.code)}")
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
    ran = gate.call(list(FILE_LISTING), capture=True)
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


def located_in_tree(path, root):
    """Whether a path a diagnostic names is in the tree at root: rustc names a workspace member's file
    relative to the root, and the toolchain's, the registry's and Verus's by a path outside it."""
    return (Path(root) / path).resolve().is_relative_to(Path(root).resolve())


def tree_warnings(output, root):
    """Each warning in a build's output whose primary span rustc locates in the tree, once, as
    'path:line:column: message'. A path rustc prints relative is relative to the root, the workspace's;
    one outside the root, the toolchain's build-std sources among them, is not the tree's, and a
    warning with no location, cargo's own or its count of a crate's warnings, names no line."""
    found, lines = [], output.splitlines()
    for header, following in zip(lines, lines[1:]):
        warning, location = WARNING_HEADER.match(header), WARNING_LOCATION.match(following)
        if not warning or not location:
            continue
        if not located_in_tree(location[1], root):
            continue
        line = f"{location[1]}:{location[2]}:{location[3]}: {warning[1]}"
        if line not in found:
            found.append(line)
    return found


def hold_warnings(gate, output):
    """Fails on any warning a build located in the tree, at the lint levels the source sets: a
    warning that lands is one every later build repeats and nobody reads."""
    warnings = tree_warnings(output, gate.root)
    if warnings:
        raise Failure("warnings located in the tree:" + "".join(f"\n  {line}" for line in warnings))


def build(gate):
    """The stack frame check's and the build's own tests, then the build, which runs that check on
    each ELF it makes. The build's last line says what it built, or what failed. Any rustc warning
    located in the tree, in any build it makes, fails the step; one in the toolchain's sources does
    not."""
    run_check(gate, STACK_SIZES_CHECK, "--test")
    run_check(gate, BUILD, "--test")
    ran = gate.call([BUILD], capture=True, merge=True)
    print(ran.stdout, end="")
    if ran.code != 0:
        raise Failure(f"{BUILD}: {status(ran.code)}: {last_line(ran.stdout)}")
    hold_warnings(gate, ran.stdout)
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
    start with 'mapped runs:'. Any rustc warning located in the tree, in the host builds of the tests,
    fails the step, as in the build step."""
    command = "cargo " + " ".join(WORKSPACE_TESTS)
    ran = gate.call(["cargo", *WORKSPACE_TESTS], capture=True, merge=True)
    print(ran.stdout, end="")
    if ran.code != 0:
        raise Failure(f"{command}: {status(ran.code)}{marked_lines(ran.stdout, TEST_FAILED)}")
    hold_warnings(gate, ran.stdout)
    passed, binaries = test_totals(ran.stdout)
    if passed == 0:
        raise Failure(f"{command}: no test ran")
    return f"{passed} tests passed in {binaries} test binaries"


def in_tree_messages(output, root):
    """The compiler messages among cargo's JSON messages whose primary span is in the tree at root,
    each once: its 'path:line: level: message' and its rendered text. cargo names a workspace
    member's file relative to the root, and the toolchain's and the registry's by an absolute path
    outside it."""
    found = {}
    for line in output.splitlines():
        if not line.startswith("{"):
            continue
        message = json.loads(line)
        if message.get("reason") != "compiler-message":
            continue
        message = message["message"]
        for span in message["spans"]:
            if span["is_primary"] and located_in_tree(span["file_name"], root):
                where = f"{span['file_name']}:{span['line_start']}: {message['level']}: {message['message']}"
                found.setdefault(where, message["rendered"])
    return list(found.items())


def workspace_members(gate):
    """The directory of each workspace member, relative to the root, in cargo's order."""
    ran = gate.call(list(WORKSPACE_MEMBERS), capture=True)
    if ran.code != 0:
        raise Failure(f"{' '.join(WORKSPACE_MEMBERS)}: {status(ran.code)}")
    root = Path(gate.root).resolve()
    return [str(Path(package["manifest_path"]).resolve().parent.relative_to(root))
            for package in json.loads(ran.stdout)["packages"]]


def forced_lints(gate):
    """The forced lint check: cargo check of every workspace member, from its own directory for the
    target its .cargo config names, and of the crates the aarch64 build makes for their aarch64
    targets, with dead_code and unused_imports forced to warn, which overrides any allow in the
    source, fails on any warning located in the tree. A proof-only field or item compiles only under
    cfg(verus_keep_ghost), so a cargo build has nothing for the lint to find, instead of hiding
    under an allow. The toolchain's build of core and the registry's crates print their own
    warnings, which are not the tree's and do not count. A check stays a check, not a test build, so
    an item only tests use is outside it."""
    members = workspace_members(gate)
    checks = [(directory, ()) for directory in members]
    checks += [(directory, (*FORCED_LINT_TARGET, target)) for directory, target in FORCED_LINT_AARCH64]
    found = {}
    for directory, target in checks:
        argv = [*FORCED_LINT_CHECK, *target]
        ran = gate.call(argv, capture=True, cwd=directory, env=FORCED_LINT_ENV)
        here = in_tree_messages(ran.stdout, gate.root)
        if ran.code != 0:
            # The JSON holds the diagnostics, so an error that stops the check is shown here.
            print("".join(rendered for _, rendered in here), end="")
            raise Failure(f"{' '.join(argv)} in {directory}: {status(ran.code)}"
                          + "".join(f"\n  {where}" for where, _ in here))
        found.update(here)
    if found:
        print("".join(found.values()), end="")
        raise Failure(f"{len(found)} warning{'s' if len(found) > 1 else ''} located in the tree:"
                      + "".join(f"\n  {where}" for where in found))
    return (f"no warning located in the tree: {len(members)} workspace members, each from its own directory, "
            f"and {', '.join(directory for directory, _ in FORCED_LINT_AARCH64)} for aarch64")


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


def unit_lines(units):
    return "".join(f"\n  {unit}" for unit in sorted(units.elements()))


def unwitnessed(gate):
    """The witness inventory's own tests, then the inventory, held to the list: the step fails unless
    the units the inventory finds with no witness, each an operation and one way it succeeds, are
    exactly the lines of tools/unwitnessed. So a way that loses its witness and an operation that
    lands without one fail it, as does a line left behind by the change that witnessed its way, and
    the list's length is the number unwitnessed. tools/land.py lets the list grow only with the
    human's approval (design/witness-per-way-an-operation-succeeds/)."""
    run_check(gate, WITNESS_INVENTORY, "--test")
    rows = [line.split("\t") for line in check_output(gate, WITNESS_INVENTORY).splitlines() if "\t" in line]
    found = Counter("\t".join(row[:3]) for row in rows if row[3] == "none")
    listed = Counter(line for line in (gate.root / UNWITNESSED).read_text().splitlines()
                     if line and not line.startswith("#"))
    unlisted, stale = found - listed, listed - found
    if unlisted or stale:
        raise Failure("\n".join(
            said + unit_lines(units) for said, units in (
                (f"no witness and no line in {UNWITNESSED}:", unlisted),
                (f"a line in {UNWITNESSED} and not without a witness, to remove:", stale)) if units))
    return f"{len(found)} of {len(rows)} lines have no witness, each a line of {UNWITNESSED}"


def unrefused(gate):
    """The refused-claim coverage, held to the list. The refused step, which comes first, has run
    this check's tests and held each claim to Verus's refusal; a module counts here only once that
    has accepted it. The step fails unless the inventory lines the report gives as none, each a way
    with no refused claim, no exemption and not an entry the operations it reaches cover, are
    exactly the lines of tools/unrefused. So a way that lands without a claim and a line left
    behind by the change that covered its way both fail it, and the list's length is the number
    with no claim. tools/land.py lets the list grow only with the human's approval
    (design/refused-claim-per-way/)."""
    report = check_output(gate, REFUSED_CHECK, "--coverage")
    rows = [line.split("\t") for line in report.splitlines() if "\t" in line]
    if any(len(row) < 4 for row in rows):
        raise Failure(f"{REFUSED_CHECK} --coverage: a line with fewer than 4 fields")
    found = Counter("\t".join(row[:3]) for row in rows if row[3] == "none")
    listed = Counter(line for line in (gate.root / UNREFUSED).read_text().splitlines()
                     if line and not line.startswith("#"))
    unlisted, stale = found - listed, listed - found
    if unlisted or stale:
        raise Failure("\n".join(
            said + unit_lines(units) for said, units in (
                (f"no refused claim and no line in {UNREFUSED}:", unlisted),
                (f"a line in {UNREFUSED} and not without a refused claim, to remove:", stale)) if units))
    return f"{len(found)} of {len(rows)} lines have no refused claim, each a line of {UNREFUSED}"


def invoked_arms(gate):
    """The check's own tests, then the check, which prints each conjunct of an operation's ensures
    that its arm of invoked does not carry: the step fails on any line it prints, as on its exit
    status, so a change that drops a field from an arm fails the gate
    (design/invoked-arm-is-the-operation-postcondition/)."""
    run_check(gate, INVOKED_ARMS_CHECK, "--test")
    ran = gate.call([INVOKED_ARMS_CHECK], capture=True)
    printed = ran.stdout.rstrip()
    if ran.code != 0 or printed:
        raise Failure(f"{INVOKED_ARMS_CHECK}: {status(ran.code)}" + "".join(f"\n  {line}" for line in printed.splitlines()))
    return "every arm of invoked carries its operation's ensures"


def design_index(gate):
    """design/INDEX.md is generated from the records, so a record edited without regenerating it
    would leave the index saying something the records do not."""
    run_check(gate, DESIGN_INDEX, "--check")
    return "design/INDEX.md is current"


def faq(gate):
    """docs/faq is rendered from its templates with the kernel's constants, so a template edited
    without rendering, or a constant changed under an explainer that names it, would leave the
    explainer saying something the kernel does not."""
    run_check(gate, FAQ_RENDER, "--test")
    return check_output(gate, FAQ_RENDER, "--check").rstrip()


def boot_stack(gate):
    # Each profile's overflow builds come first, so the images left behind are the normal ones.
    for args in (["--test"], ["debug", "overflow"], ["debug", "syscall-overflow"], ["debug"],
                 ["release", "overflow"], ["release", "syscall-overflow"], ["release"]):
        run_check(gate, BOOT_STACK_CHECK, *args)
    return "its own tests, then debug and release, normal, boot stack overflow and syscall stack overflow"


def coverage(gate):
    """Coverage per crate after the script's own tests pass. A low number does not fail the gate:
    only a capture that fails does, or a stack the instrumented boot left less of than it wrote."""
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


INPUT_ISOLATION_STEP = "step inputs"

# Bounded steps exercised inside input-only hardlinked sibling views during a gate run.
# Excludes heavy Z3 proof, QEMU boot, and physical board steps so tooling/manifest edits stay fast.
ISOLATED_CHECK_STEPS = (
    "license",
    "hooks",
    "unwitnessed",
    "unrefused",
    "external body",
    "layout claims",
    "boundary",
    "invoked arms",
    "page literals",
    "arch sources",
    "upstream copies",
    "design index",
    "faq",
    "build",
    "workspace tests",
    "forced lints",
)


def step_inputs(gate):
    """Verifies declared step inputs via metadata unit tests and isolated hardlink sandboxes."""
    run_check(gate, GATE_SELF[0], "--test")
    argv = [GATE_SELF[0], "--check-inputs"]
    for name in ISOLATED_CHECK_STEPS:
        argv += ["--step", name]
    run_check(gate, *argv)
    return f"self-tests and {len(ISOLATED_CHECK_STEPS)} bounded steps verified in isolated input views"


# Cargo/Verus steps whose generated .d dep-info and build/*/output files are audited after running.
DEP_INFO_STEPS = frozenset((
    "build",
    "workspace tests",
    "forced lints",
    "verify",
    "verify aarch64",
    "throwaways",
    "refused",
    "layout claims",
    "boundary",
    "boot stack",
    "coverage",
    "iommu boot",
    "boot",
    "aarch64 boot",
))


GATE_SELF = ("tools/gate.py",)
TOOLCHAIN_PINS = ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "tools/toolchain.py")

VERIFIED_CRATES = (
    "kernel/verified/**",
    "aheap/**",
    "acall/**",
    "aeager/**",
    "aring/**",
    "amailbox/**",
    "afanin/**",
    "pager-policy/**",
    "adivider/**",
    "awire/**",
    "asys/**",
)
BOUNDARY_CRATES = tuple(dict.fromkeys((
    "kernel/**",
    "dom0/**",
    "astd/**",
    "abench/**",
    "acontext/**",
    "asys/**",
    "kernel-logger/**",
    "machine/**",
    "ns16550a/**",
    *VERIFIED_CRATES,
)))
IMAGE_CRATES = tuple(dict.fromkeys((
    "aloader/**",
    "aelf/**",
    "kernel/**",
    "dom0/**",
    "user/hello/**",
    "user/.cargo/**",
    "user/*-unknown-aloader.json",
    "astd/**",
    "acall/**",
    "aeager/**",
    "aheap/**",
    "asys/**",
    "kernel-logger/**",
    "machine/**",
    "ns16550a/**",
    "abench/**",
    "acontext/**",
    "kernel/verified/**",
)))
WORKSPACE_CRATES = tuple(dict.fromkeys((
    *IMAGE_CRATES,
    "aring/**",
    "amailbox/**",
    "afanin/**",
    "pager-policy/**",
    "adivider/**",
    "awire/**",
    "file-service/**",
    "boot-host-tests/**",
)))
WORKSPACE_MANIFESTS = (
    "abench/Cargo.toml",
    "acall/Cargo.toml",
    "acontext/Cargo.toml",
    "adivider/Cargo.toml",
    "aeager/Cargo.toml",
    "aelf/Cargo.toml",
    "afanin/Cargo.toml",
    "aheap/Cargo.toml",
    "aloader/Cargo.toml",
    "amailbox/Cargo.toml",
    "aring/Cargo.toml",
    "astd/Cargo.toml",
    "asys/Cargo.toml",
    "awire/Cargo.toml",
    "boot-host-tests/Cargo.toml",
    "dom0/Cargo.toml",
    "file-service/Cargo.toml",
    "kernel-logger/Cargo.toml",
    "kernel/Cargo.toml",
    "kernel/verified/Cargo.toml",
    "machine/pc/Cargo.toml",
    "machine/virt/Cargo.toml",
    "ns16550a/Cargo.toml",
    "pager-policy/Cargo.toml",
    "user/hello/Cargo.toml",
)
# Entrypoints required on disk by `cargo metadata --locked` when loading workspace manifests.
WORKSPACE_CARGO_TARGETS = (
    "*/src/lib.rs",
    "*/src/main.rs",
    "*/build.rs",
    "file-service/tests/*.rs",
    "kernel/verified/lib.rs",
    "machine/*/src/lib.rs",
    "user/*/src/main.rs",
)
HOOK_INPUTS = (
    "AGENTS.md",
    ".agents/hooks.json",
    ".claude/hooks/**",
)
GATE_TOOLS_AND_CONFIGS = (
    BUILD,
    STACK_SIZES_CHECK,
    LICENSE_CHECK,
    "tools/license-allowlist",
    SOURCE_LICENSE_CHECK,
    VERIFY,
    VERIFY_ALLOWANCE,
    THROWAWAY_CHECK,
    WITNESS_INVENTORY,
    UNWITNESSED,
    REFUSED_CHECK,
    "tools/refused-exempt",
    UNREFUSED,
    EXTERNAL_BODY_CHECK,
    "tools/external-body-list",
    "tools/hardware-documents",
    LAYOUT_CLAIMS_CHECK,
    BOUNDARY_CHECK,
    "tools/boundary-list",
    INVOKED_ARMS_CHECK,
    PAGE_LITERALS_CHECK,
    ARCH_SOURCES_CHECK,
    UPSTREAM_COPIES_CHECK,
    "tools/upstream-copies/**",
    DESIGN_INDEX,
    FAQ_RENDER,
    BOOT_STACK_CHECK,
    COVERAGE,
    RUN,
    GDB,
    "tools/gdb-helper.py",
    "tools/elfstrip.py",
    "tools/firmware.py",
    BOOT_LOG_CHECK,
    BOARD,
    "tools/aarch64-esp.py",
    "tools/orangepi-kvm.py",
)


def bounded(*globs):
    """Inputs for a bounded step: gate runner, toolchain pins, and step-specific globs."""
    return tuple(dict.fromkeys((*GATE_SELF, *TOOLCHAIN_PINS, *globs)))


Step = namedtuple("Step", "name target check inputs")

STEPS = (
    Step("file sizes", X86_64, file_sizes, None),
    Step("build", X86_64, build, bounded(BUILD, STACK_SIZES_CHECK, *WORKSPACE_CRATES)),
    Step("workspace tests", X86_64, workspace_tests, bounded(*WORKSPACE_CRATES, INVOKED_ARMS_CHECK)),
    Step("forced lints", X86_64, forced_lints, bounded(*WORKSPACE_CRATES)),
    Step("license", X86_64, self_tested(LICENSE_CHECK),
         bounded(LICENSE_CHECK, "tools/license-allowlist", *WORKSPACE_MANIFESTS, *WORKSPACE_CARGO_TARGETS)),
    Step("source licenses", X86_64, self_tested(SOURCE_LICENSE_CHECK), None),
    Step("hooks", X86_64, hooks, bounded(
        "AGENTS.md", ".agents/hooks.json",
        ".claude/hooks/license-guard.sh", ".claude/hooks/license-guard-test.sh",
        ".claude/hooks/beads-actor.sh", ".claude/hooks/beads-actor-test.sh",
        ".claude/hooks/agy-session-start.sh",
    )),
    Step("verify", X86_64, verify, bounded(VERIFY, VERIFY_ALLOWANCE, *VERIFIED_CRATES)),
    # After verify, whose exported crates a throwaway run of a crate that depends on one reads.
    Step("throwaways", X86_64, self_tested(THROWAWAY_CHECK), bounded(VERIFY, THROWAWAY_CHECK, *VERIFIED_CRATES)),
    Step("unwitnessed", X86_64, unwitnessed, bounded(VERIFY, THROWAWAY_CHECK, WITNESS_INVENTORY, UNWITNESSED, *VERIFIED_CRATES)),
    # After verify too: a false claim a verified crate keeps, held to Verus's refusal where it says.
    Step("refused", X86_64, self_tested(REFUSED_CHECK), bounded(VERIFY, THROWAWAY_CHECK, WITNESS_INVENTORY, REFUSED_CHECK, *VERIFIED_CRATES)),
    # After refused, whose accepted modules are the ones a covers line may name.
    Step("unrefused", X86_64, unrefused, bounded(VERIFY, THROWAWAY_CHECK, WITNESS_INVENTORY, REFUSED_CHECK, "tools/refused-exempt", UNREFUSED, *VERIFIED_CRATES)),
    Step("verify aarch64", AARCH64, verify_for("--target", AARCH64), bounded(VERIFY, VERIFY_ALLOWANCE, *VERIFIED_CRATES)),
    Step("external body", X86_64, self_tested(EXTERNAL_BODY_CHECK), bounded(EXTERNAL_BODY_CHECK, "tools/external-body-list", "tools/hardware-documents", *VERIFIED_CRATES, "kernel/**")),
    # Verus takes a layout claim as stated; the build checks it, for both targets.
    Step("layout claims", X86_64, self_tested(LAYOUT_CLAIMS_CHECK), bounded(LAYOUT_CLAIMS_CHECK, *VERIFIED_CRATES)),
    # What unverified crates hand verified code unchecked, from rustc's THIR of both targets.
    Step("boundary", X86_64, self_tested(BOUNDARY_CHECK), bounded(BOUNDARY_CHECK, EXTERNAL_BODY_CHECK, "tools/boundary-list", "tools/hardware-documents", *BOUNDARY_CRATES)),
    Step("invoked arms", X86_64, invoked_arms, bounded(INVOKED_ARMS_CHECK, "kernel/verified/**")),
    Step("page literals", X86_64, self_tested(PAGE_LITERALS_CHECK), bounded(PAGE_LITERALS_CHECK, *VERIFIED_CRATES)),
    Step("arch sources", X86_64, self_tested(ARCH_SOURCES_CHECK), bounded(ARCH_SOURCES_CHECK, "kernel/src/**")),
    Step("upstream copies", X86_64, self_tested(UPSTREAM_COPIES_CHECK), bounded(UPSTREAM_COPIES_CHECK, "tools/upstream-copies/**", "kernel/verified/pptr.rs")),
    Step("design index", X86_64, design_index, bounded(DESIGN_INDEX, "design/*/DECISION.md", "design/INDEX.md")),
    Step("faq", X86_64, faq, bounded(FAQ_RENDER, "docs/faq/**", "kernel/verified/define.rs", "kernel/verified/layouts.rs", "kernel/verified/capability/**")),
    Step("boot stack", X86_64, boot_stack, bounded(BOOT_STACK_CHECK, RUN, "tools/elfstrip.py", "tools/firmware.py", *IMAGE_CRATES)),
    Step("coverage", X86_64, coverage, bounded(COVERAGE, BOOT_STACK_CHECK, RUN, "tools/elfstrip.py", "tools/firmware.py", *IMAGE_CRATES, "user/**")),
    # The plain boot comes after it, so the serial.log the gate leaves has no IOMMU.
    Step("iommu boot", X86_64, boot_with("--iommu"), bounded(RUN, "tools/elfstrip.py", "tools/firmware.py", BOOT_LOG_CHECK, *IMAGE_CRATES)),
    Step("boot", X86_64, boot, bounded(RUN, GDB, "tools/gdb-helper.py", "tools/elfstrip.py", "tools/firmware.py", BOOT_LOG_CHECK, *IMAGE_CRATES)),
    Step(INPUT_ISOLATION_STEP, X86_64, step_inputs,
         bounded(*GATE_TOOLS_AND_CONFIGS, *HOOK_INPUTS, *WORKSPACE_MANIFESTS, "boot-host-tests/**")),
    Step("aarch64 boot", AARCH64, board, bounded(BOARD, "tools/aarch64-esp.py", BUILD, STACK_SIZES_CHECK, "tools/elfstrip.py", "tools/orangepi-kvm.py", BOOT_LOG_CHECK, *IMAGE_CRATES)),
)


def normalize_repo_path(path):
    """Normalizes a repo-relative path to POSIX form without leading './'."""
    text = str(path).replace("\\", "/")
    while text.startswith("./"):
        text = text[2:]
    if not text or text == ".":
        return ""
    norm = PurePosixPath(text).as_posix()
    return "" if norm == "." else norm


def matches_globs(path, globs):
    """Whether a repo-relative path matches any glob in globs under PurePosixPath.full_match."""
    norm = normalize_repo_path(path)
    if not norm:
        return False
    posix = PurePosixPath(norm)
    return any(posix.full_match(glob) for glob in globs)


def parse_ls_tree(raw):
    """Parses `git ls-tree -r -z` output into sorted-ready `(mode, sha, path)` entries."""
    text = raw.decode("utf-8", errors="surrogateescape") if isinstance(raw, (bytes, bytearray)) else raw
    entries = []
    for record in text.split("\0"):
        if not record:
            continue
        meta, path = record.split("\t", 1)
        mode, kind, sha = meta.split(" ", 2)
        if kind == "tree":
            continue
        entries.append((mode, sha, normalize_repo_path(path)))
    return entries


def input_slice_digest(entries, inputs):
    """SHA-256 hex digest over sorted `(mode, blob_sha, path)` entries matching `inputs`, or None."""
    if inputs is None:
        return None
    matched = sorted(
        (mode, sha, norm)
        for mode, sha, path in entries
        if (norm := normalize_repo_path(path)) and matches_globs(norm, inputs)
    )
    digest = hashlib.sha256()
    for mode, sha, path in matched:
        digest.update(f"{mode} {sha}\t{path}\0".encode("utf-8"))
    return digest.hexdigest()


def git_run(root, *args):
    """Runs git in `root`, raising Failure on nonzero exit, and returns raw stdout bytes."""
    done = subprocess.run(["git", "-C", str(root), *args], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode != 0:
        err = done.stderr.decode(errors="replace").strip()
        raise Failure(f"git {' '.join(args)}: {err or status(done.returncode)}")
    return done.stdout


def ls_tree_entries(root, tree):
    """`(mode, sha, path)` entries of `git ls-tree -r -z tree` in `root`."""
    return parse_ls_tree(git_run(root, "ls-tree", "-r", "-z", tree))


def input_hash(root, tree, step):
    """Input-slice digest for `step` at `tree` in `root`, or None for an unbounded step."""
    if step.inputs is None:
        return None
    return input_slice_digest(ls_tree_entries(root, tree), step.inputs)


def input_hashes(root, tree, steps=STEPS):
    """Map of step name to input-slice digest (or None) for `steps` at `tree` in `root`."""
    entries = ls_tree_entries(root, tree)
    return {step.name: input_slice_digest(entries, step.inputs) for step in steps}


def parse_nul_paths(raw):
    """Normalized non-empty paths from NUL-delimited git output."""
    text = raw.decode("utf-8", errors="surrogateescape") if isinstance(raw, (bytes, bytearray)) else raw
    return [norm for entry in text.split("\0") if entry and (norm := normalize_repo_path(entry))]


def changed_paths_since(root, base):
    """Sorted unique repo-relative paths changed between `base` and the working tree (incl. untracked)."""
    diffed = parse_nul_paths(git_run(root, "diff", "--name-only", "-z", "--no-renames", base))
    untracked = parse_nul_paths(git_run(root, "ls-files", "-z", "--others", "--exclude-standard"))
    return sorted(set(diffed) | set(untracked))


def tracked_paths(root):
    """Normalized tracked files in `root` from `git ls-files -z`."""
    return parse_nul_paths(git_run(root, "ls-files", "-z"))


def step_affected(step, changed):
    """Whether `step` is affected by `changed`; unbounded steps (`inputs is None`) always run."""
    if step.inputs is None:
        return True
    return any(matches_globs(path, step.inputs) for path in changed)


def is_covered(path, steps=STEPS):
    """Whether any bounded step in `steps` declares an input glob matching `path`."""
    return any(step.inputs is not None and matches_globs(path, step.inputs) for step in steps)


def unread_paths(paths, steps=STEPS):
    """Normalized paths from `paths` covered by no bounded step in `steps`."""
    return [norm for path in paths if (norm := normalize_repo_path(path)) and not is_covered(norm, steps)]


def load_cargo_metadata(repo=REPO):
    """Workspace package manifests and direct dependency declarations via cargo metadata."""
    done = subprocess.run(list(WORKSPACE_MEMBERS), cwd=repo, stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if done.returncode != 0:
        raise Failure(f"{' '.join(WORKSPACE_MEMBERS)}: {done.stderr.strip() or status(done.returncode)}")
    return json.loads(done.stdout)


def load_faq_paths(repo=REPO):
    """Paths read by tools/faq.py (constants files, layouts, template/output dirs)."""
    spec = importlib.util.spec_from_file_location("atmo_faq", repo / FAQ_RENDER)
    faq_mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(faq_mod)
    paths = set(faq_mod.CONSTANTS.values())
    paths.add(f"{faq_mod.FAQ.as_posix()}/README.md")
    paths.add(f"{faq_mod.SOURCES.as_posix()}/sample.md")
    paths.add("kernel/verified/layouts.rs")
    return sorted(paths)


def load_patch_targets(repo=REPO):
    """Patch files and in-repo source/target paths named in tools/upstream-copies/*.patch headers."""
    targets = []
    for patch in sorted((repo / "tools/upstream-copies").glob("*.patch")):
        targets.append(patch.relative_to(repo).as_posix())
        lines = patch.read_text(encoding="utf-8").splitlines()
        for prefix, line in (("--- ", lines[0]), ("+++ ", lines[1])):
            if not line.startswith(prefix):
                continue
            target = line[len(prefix):].strip()
            if target and not target.startswith("../"):
                targets.append(normalize_repo_path(target))
    return sorted(set(targets))


def collect_step_tool_calls():
    """Runs every bounded step against FakeGate to capture repo-relative tools invoked by gate.py."""
    verified = (0, "verification results:: 1 verified, 0 errors\n")
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        (root / "tools").mkdir()
        (root / VERIFY_ALLOWANCE).write_text("2\n")
        (root / UNWITNESSED).write_text("# a comment\n")
        (root / UNREFUSED).write_text("# a comment\n")
        answers = {
            VERIFY: verified,
            f"{VERIFY} --target {AARCH64}": verified,
            "cargo " + " ".join(WORKSPACE_TESTS): (0, "test result: ok. 1 passed; 0 failed\n"),
            " ".join(WORKSPACE_MEMBERS): (0, json.dumps({"packages": [{"manifest_path": str(root / "aheap/Cargo.toml")}]})),
        }
        calls = {}
        for step in STEPS:
            if step.inputs is None:
                continue
            fake = FakeGate(root, dict(answers))
            step.check(fake)
            calls[step.name] = [argv[0] for argv in fake.calls if "/" in argv[0]]
        return calls


def workspace_dep_closure(metadata, roots, repo, include_dev=False):
    """Transitive workspace member directories reachable from `roots`."""
    repo_resolved = Path(repo).resolve()
    by_dir = {}
    by_name = {}
    for pkg in metadata["packages"]:
        rel_dir = Path(pkg["manifest_path"]).resolve().parent.relative_to(repo_resolved).as_posix()
        by_dir[rel_dir] = pkg
        by_name[pkg["name"]] = (rel_dir, pkg)
    by_abs = {str((repo_resolved / rel_dir).resolve()): rel_dir for rel_dir in by_dir}

    seen = set()
    stack = list(roots)
    while stack:
        rel_dir = stack.pop()
        if rel_dir in seen or rel_dir not in by_dir:
            continue
        seen.add(rel_dir)
        for dep in by_dir[rel_dir].get("dependencies") or []:
            kind = dep.get("kind")
            if not include_dev and kind in ("dev", "build"):
                continue
            target_dir = None
            dep_path = dep.get("path")
            if dep_path:
                resolved = str((repo_resolved / dep_path).resolve()) if not Path(dep_path).is_absolute() else str(Path(dep_path).resolve())
                target_dir = by_abs.get(resolved)
            if target_dir is None and dep["name"] in by_name:
                target_dir = by_name[dep["name"]][0]
            if target_dir is not None and target_dir not in seen:
                stack.append(target_dir)
    return sorted(seen)


def step_input_errors(steps, repo=REPO, metadata=None, faq_paths=None, patch_targets=None, tool_calls=None):
    """Returns error messages for any missing or incomplete Step.inputs entry in `steps`."""
    errors = []
    by_name = {step.name: step for step in steps}
    if metadata is None:
        metadata = load_cargo_metadata(repo)
    if faq_paths is None:
        faq_paths = load_faq_paths(repo)
    if patch_targets is None:
        patch_targets = load_patch_targets(repo)
    if tool_calls is None:
        tool_calls = collect_step_tool_calls()

    def require_covers(step_name, path, reason):
        step = by_name.get(step_name)
        if step is None:
            errors.append(f"missing step {step_name!r}")
            return
        if step.inputs is None or not matches_globs(path, step.inputs):
            errors.append(f"step {step_name!r} inputs do not cover {path!r} ({reason})")

    def require_crate(step_name, rel_dir, reason):
        require_covers(step_name, f"{rel_dir}/Cargo.toml", reason)
        require_covers(step_name, f"{rel_dir}/src/probe.rs", reason)

    for name in ("file sizes", "source licenses"):
        if name not in by_name or by_name[name].inputs is not None:
            errors.append(f"unbounded step {name!r} must have inputs=None")

    for step in steps:
        if step.name in ("file sizes", "source licenses"):
            continue
        if not isinstance(step.inputs, tuple) or not step.inputs:
            errors.append(f"bounded step {step.name!r} must declare a non-empty tuple of inputs")
            continue
        for shared in (*GATE_SELF, *TOOLCHAIN_PINS):
            require_covers(step.name, shared, "shared pin")

    repo_resolved = Path(repo).resolve()
    member_dirs = []
    verified_dirs = []
    for pkg in metadata["packages"]:
        rel_dir = Path(pkg["manifest_path"]).resolve().parent.relative_to(repo_resolved).as_posix()
        member_dirs.append(rel_dir)
        if ((pkg.get("metadata") or {}).get("atmosphere") or {}).get("verified"):
            verified_dirs.append(rel_dir)

    for rel_dir in member_dirs:
        require_covers("license", f"{rel_dir}/Cargo.toml", "workspace member manifest")
        require_covers(INPUT_ISOLATION_STEP, f"{rel_dir}/Cargo.toml", "workspace member manifest")
        for step_name in ("build", "workspace tests", "forced lints"):
            require_crate(step_name, rel_dir, "workspace member")

    for pkg in metadata["packages"]:
        for target in pkg.get("targets") or []:
            rel_src = Path(target["src_path"]).resolve().relative_to(repo_resolved).as_posix()
            require_covers("license", rel_src, "workspace target root for cargo metadata")

    for path in ("boot-host-tests/Cargo.toml", "boot-host-tests/src/lib.rs",
                 "AGENTS.md", ".agents/hooks.json", ".claude/hooks/license-guard.sh"):
        require_covers(INPUT_ISOLATION_STEP, path, "step inputs isolation watch path")

    verified_closure = workspace_dep_closure(metadata, verified_dirs, repo)
    for step_name in ("verify", "verify aarch64", "throwaways", "unwitnessed", "refused", "unrefused",
                      "page literals", "layout claims"):
        for rel_dir in verified_closure:
            require_crate(step_name, rel_dir, "verified crate or transitive dep")

    for rel_dir in [*verified_closure, "kernel"]:
        require_crate("external body", rel_dir, "verified crate closure or kernel target")

    for rel_dir in workspace_dep_closure(metadata, ["kernel/verified"], repo):
        require_crate("invoked arms", rel_dir, "kernel/verified closure")

    for rel_dir in workspace_dep_closure(metadata, ["kernel", "dom0", "astd", *verified_dirs], repo):
        require_crate("boundary", rel_dir, "boundary crate or transitive dep")

    image_closure = workspace_dep_closure(metadata, ["aloader", "kernel", "dom0", "user/hello"], repo)
    for step_name in ("boot stack", "coverage", "iommu boot", "boot", "aarch64 boot"):
        for rel_dir in image_closure:
            require_crate(step_name, rel_dir, "boot image crate or transitive dep")
        require_covers(step_name, "user/.cargo/config.toml", "user cargo config")
        require_covers(step_name, "user/x86_64-unknown-aloader.json", "user target spec")
        require_covers(step_name, "user/aarch64-unknown-aloader.json", "user aarch64 target spec")

    for rel_dir in member_dirs:
        if rel_dir.startswith("user/"):
            require_crate("coverage", rel_dir, "user workspace member")

    for rel_dir in workspace_dep_closure(metadata, member_dirs, repo, include_dev=True):
        require_crate("workspace tests", rel_dir, "workspace test dependency")
    require_covers("workspace tests", "kernel/src/boot/free_ranges.rs", "boot-host-tests #[path]")
    require_covers("workspace tests", "kernel/src/boot/mapped_runs.rs", "boot-host-tests #[path]")
    require_covers("workspace tests", INVOKED_ARMS_CHECK, "boot-host-tests invoked_arms_test")

    for directory, target in FORCED_LINT_AARCH64:
        require_covers("forced lints", f"{directory}/Cargo.toml", "FORCED_LINT_AARCH64 member")
        if target.endswith(".json"):
            spec_path = posixpath.normpath(f"{directory}/{target}")
            for step_name in ("forced lints", "build", "workspace tests", "boot stack", "coverage",
                              "iommu boot", "boot", "aarch64 boot"):
                require_covers(step_name, spec_path, "FORCED_LINT_AARCH64 target spec")

    for target in patch_targets:
        require_covers("upstream copies", target, "upstream-copies patch or target")

    for path in faq_paths:
        require_covers("faq", path, "tools/faq.py path")

    extra_tools = {
        "license": ("tools/license-allowlist",),
        "hooks": ("AGENTS.md", ".agents/hooks.json", ".claude/hooks/license-guard.sh",
                  ".claude/hooks/beads-actor.sh", ".claude/hooks/agy-session-start.sh", *HOOK_TESTS),
        "design index": ("design/INDEX.md", "design/example/DECISION.md"),
        "arch sources": ("kernel/src/main.rs",),
        "verify": (VERIFY_ALLOWANCE,),
        "verify aarch64": (VERIFY_ALLOWANCE,),
        "unwitnessed": (VERIFY, THROWAWAY_CHECK, UNWITNESSED),
        "refused": (VERIFY, THROWAWAY_CHECK, WITNESS_INVENTORY),
        "unrefused": (VERIFY, THROWAWAY_CHECK, WITNESS_INVENTORY, "tools/refused-exempt", UNREFUSED),
        "external body": ("tools/external-body-list", "tools/hardware-documents"),
        "boundary": (EXTERNAL_BODY_CHECK, "tools/boundary-list", "tools/hardware-documents"),
        "boot stack": (RUN, "tools/elfstrip.py", "tools/firmware.py"),
        "coverage": (BOOT_STACK_CHECK, RUN, "tools/elfstrip.py", "tools/firmware.py"),
        "iommu boot": ("tools/elfstrip.py", "tools/firmware.py"),
        "boot": ("tools/gdb-helper.py", "tools/elfstrip.py", "tools/firmware.py"),
        "aarch64 boot": ("tools/aarch64-esp.py", BUILD, STACK_SIZES_CHECK, "tools/elfstrip.py",
                         "tools/orangepi-kvm.py", BOOT_LOG_CHECK),
    }
    for step_name, paths in extra_tools.items():
        for path in paths:
            require_covers(step_name, path, "step tool or config")

    for step_name, invoked in tool_calls.items():
        for tool in invoked:
            require_covers(step_name, tool, "tool invoked by step")
            require_covers(INPUT_ISOLATION_STEP, tool, "tool invoked by bounded step")

    return errors


def _dep_info_tokens(rhs):
    """Split a Makefile dep-info rule RHS on unescaped whitespace, unescaping backslash escapes."""
    tokens, current = [], []
    i, n = 0, len(rhs)
    escapes = {" ": " ", "\\": "\\", "#": "#", ":": ":", "$": "$", "\t": "\t"}
    while i < n:
        ch = rhs[i]
        if ch in " \t":
            if current:
                tokens.append("".join(current))
                current.clear()
            i += 1
        elif ch == "\\" and i + 1 < n and rhs[i + 1] in escapes:
            current.append(escapes[rhs[i + 1]])
            i += 2
        else:
            current.append(ch)
            i += 1
    if current:
        tokens.append("".join(current))
    return tokens


def parse_dep_info(text):
    """Dependency paths named on the right-hand side of Makefile rules in a `.d` file."""
    joined = text.replace("\\\r\n", " ").replace("\\\n", " ")
    deps = []
    for line in joined.splitlines():
        stripped = line.lstrip()
        if not stripped or stripped.startswith("#"):
            continue
        sep = -1
        for idx, ch in enumerate(line):
            if ch != ":":
                continue
            backslashes = 0
            j = idx - 1
            while j >= 0 and line[j] == "\\":
                backslashes += 1
                j -= 1
            if backslashes % 2 == 0:
                sep = idx
                break
        if sep >= 0:
            deps.extend(_dep_info_tokens(line[sep + 1:]))
    return deps


def parse_rerun_if_changed(text):
    """Paths emitted by build.rs via `cargo:rerun-if-changed=...`."""
    return [line.split("=", 1)[1].strip() for line in text.splitlines()
            if line.startswith("cargo:rerun-if-changed=") and line.split("=", 1)[1].strip()]


def workspace_package_dirs(root):
    """Map workspace Cargo package names to repo-relative manifest directories without subprocesses."""
    root = Path(root)
    manifest = root / "Cargo.toml"
    if not manifest.is_file():
        return {}
    members = (tomllib.loads(manifest.read_text(encoding="utf-8")).get("workspace") or {}).get("members") or ()
    dirs = {}
    for member in members:
        pkg_manifest = root / member / "Cargo.toml"
        if not pkg_manifest.is_file():
            continue
        pkg = tomllib.loads(pkg_manifest.read_text(encoding="utf-8")).get("package") or {}
        if "name" in pkg:
            dirs[pkg["name"]] = normalize_repo_path(member)
    return dirs


def repo_dep_paths(raw_path, base_dir, repo_abs, repo_real):
    """Normalized repo-relative paths referenced by `raw_path`, omitting target/ build outputs."""
    cand = raw_path if os.path.isabs(raw_path) else os.path.join(base_dir, raw_path)
    norm = Path(os.path.normpath(cand))
    found = []
    if norm.is_relative_to(repo_abs):
        rel = normalize_repo_path(norm.relative_to(repo_abs).as_posix())
        if rel and rel != "target" and not rel.startswith("target/"):
            found.append(rel)
    resolved = norm.resolve()
    if resolved.is_relative_to(repo_real):
        rel = normalize_repo_path(resolved.relative_to(repo_real).as_posix())
        if rel and rel != "target" and not rel.startswith("target/") and rel not in found:
            found.append(rel)
    return found


def snapshot_dep_files(root):
    """Return `{full_path: (mtime_ns, size)}` for `.d` and `build/*/output` files under `target/`."""
    target_dir = Path(root) / "target"
    if not target_dir.is_dir():
        return {}
    skip_dirs = {"incremental", ".fingerprint", "tmp", "esp", "orangepi-esp", "flush-cost-esp"}
    found = {}
    for dirpath, dirnames, filenames in os.walk(target_dir):
        dirnames[:] = [d for d in dirnames if d not in skip_dirs]
        grandparent = os.path.basename(os.path.dirname(dirpath))
        for name in filenames:
            if name.endswith(".d") or (name == "output" and grandparent == "build"):
                full = os.path.join(dirpath, name)
                try:
                    st = os.stat(full)
                except FileNotFoundError:
                    continue
                found[full] = (st.st_mtime_ns, st.st_size)
    return found


def dep_info_errors(step, root, changed_files):
    """Check `changed_files` (`.d` and `build/*/output`) against `step.inputs`."""
    if step.inputs is None or not changed_files:
        return []
    repo_abs = Path(os.path.abspath(str(root)))
    repo_real = Path(root).resolve()
    pkg_dirs = workspace_package_dirs(root)
    violations = []
    seen = set()
    for path_str in changed_files:
        dep_path = Path(path_str)
        try:
            text = dep_path.read_text(encoding="utf-8", errors="replace")
            dep_rel = dep_path.relative_to(root).as_posix()
        except OSError:
            continue
        if dep_path.name == "output":
            pkg_tag = dep_path.parent.name
            pkg_name = pkg_tag.rsplit("-", 1)[0] if "-" in pkg_tag else pkg_tag
            rel_pkg = pkg_dirs.get(pkg_name)
            entries = [(p, str(repo_abs / rel_pkg) if rel_pkg is not None else None)
                       for p in parse_rerun_if_changed(text)]
        else:
            entries = [(p, str(repo_abs)) for p in parse_dep_info(text)]
        for raw, base_dir in entries:
            if base_dir is None and not os.path.isabs(raw):
                continue
            for rel in repo_dep_paths(raw, base_dir or str(repo_abs), repo_abs, repo_real):
                if not matches_globs(rel, step.inputs) and (dep_rel, rel) not in seen:
                    seen.add((dep_rel, rel))
                    violations.append(f"undeclared dep-info input in {dep_rel}: {rel}")
    return violations


def repo_listing(root):
    """Non-ignored repo-relative paths in `root` using git when available, else os.walk."""
    root = Path(root)
    if (root / ".git").exists():
        return parse_nul_paths(git_run(root, *FILE_LISTING[1:]))
    paths = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in (".git", "target"))
        for name in sorted(filenames):
            rel = normalize_repo_path((Path(dirpath) / name).relative_to(root).as_posix())
            if rel:
                paths.append(rel)
    return paths


def filter_workspace_manifest(text, keep_members):
    """Rewrite `[workspace] members` in Cargo.toml text to `keep_members`, preserving the rest."""
    section = re.search(r"(?m)^\[workspace\]\s*$", text)
    if section is None:
        return text
    next_section = re.search(r"(?m)^\[", text[section.end():])
    section_end = section.end() + next_section.start() if next_section else len(text)
    members = re.search(r"(?m)^members\s*=\s*\[", text[section.end():section_end])
    if members is None:
        return text
    open_bracket = section.end() + members.end() - 1
    depth, i, in_string = 0, open_bracket, None
    while i < section_end:
        ch = text[i]
        if in_string == '"':
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = None
        elif in_string == "'":
            if ch == "'":
                in_string = None
        elif ch in ('"', "'"):
            in_string = ch
        elif ch == "#":
            end = text.find("\n", i)
            i = section_end if end < 0 else end + 1
            continue
        elif ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                lines = "".join(f'  "{member}",\n' for member in keep_members)
                replacement = f"[\n{lines}]" if keep_members else "[]"
                return text[:open_bracket] + replacement + text[i + 1:]
        i += 1
    return text


def materialize_input_view(repo, step, sandbox, all_paths=None):
    """Hardlink only files matching `step.inputs` from `repo` into sibling directory `sandbox`."""
    repo = Path(repo)
    sandbox = Path(sandbox)
    if all_paths is None:
        all_paths = repo_listing(repo)
    for rel in all_paths:
        if not matches_globs(rel, step.inputs):
            continue
        src = repo / rel
        dst = sandbox / rel
        if os.path.islink(src):
            dst.parent.mkdir(parents=True, exist_ok=True)
            os.symlink(os.readlink(src), dst)
        elif src.is_file():
            dst.parent.mkdir(parents=True, exist_ok=True)
            # Cargo opens Cargo.lock R/W and partial slices rewrite Cargo.toml; never hardlink either.
            if rel in ("Cargo.toml", "Cargo.lock"):
                shutil.copy2(src, dst)
            else:
                try:
                    os.link(src, dst)
                except OSError:
                    shutil.copy2(src, dst)
    manifest = sandbox / "Cargo.toml"
    if manifest.is_file():
        text = manifest.read_text(encoding="utf-8")
        members = (tomllib.loads(text).get("workspace") or {}).get("members") or []
        keep = [m for m in members if (sandbox / m / "Cargo.toml").is_file()]
        if len(keep) != len(members):
            manifest.unlink()
            manifest.write_text(filter_workspace_manifest(text, keep), encoding="utf-8")
    # Initialize an empty repository boundary so Cargo/git tools stay inside the sandbox instead
    # of walking up to the project root's bare worktree control files ($root/.git -> .bare).
    subprocess.run(["git", "init", "-q"], cwd=sandbox, stdin=subprocess.DEVNULL,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)


def run_steps_isolated(repo, steps, boot_timeout, clock=time.monotonic):
    """Execute each bounded step inside its own sibling hardlinked input view next to `repo`."""
    repo = Path(repo).resolve()
    parent = repo.parent
    all_paths = repo_listing(repo)
    lines, failed = [], False
    started = clock()
    for step in steps:
        if step.inputs is None or step.name == INPUT_ISOLATION_STEP:
            continue
        start = clock()
        with tempfile.TemporaryDirectory(dir=parent, prefix=".gate-inputs-") as td:
            sandbox = Path(td)
            materialize_input_view(repo, step, sandbox, all_paths=all_paths)
            step_lines, step_code = run_gate(Gate(sandbox, boot_timeout), [step], clock=clock)
        ok = step_code == 0
        failed |= not ok
        detail = step_lines[0].split(": ", 2)[-1] if step_lines else "no output"
        lines.append(step_line(step.name, ok, detail, clock() - start))
    lines.append(total_line(clock() - started))
    return lines, 1 if failed else 0


def chosen(target=None, names=None, changed=None):
    """The steps the gate runs, in its order: those of target, of names, and affected by changed."""
    return [step for step in STEPS
            if (target is None or step.target == target)
            and (names is None or step.name in names)
            and (changed is None or step_affected(step, changed))]


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
        audit = step.inputs is not None and step.name in DEP_INFO_STEPS
        before = snapshot_dep_files(gate.root) if audit else None
        try:
            ok, detail = True, step.check(gate)
        except (Failure, OSError) as error:
            ok, detail = False, str(error)
        if audit:
            after = snapshot_dep_files(gate.root)
            changed = sorted(p for p, sig in after.items() if before.get(p) != sig)
            audit_errors = dep_info_errors(step, gate.root, changed)
            if audit_errors:
                ok = False
                joined = "".join(f"\n  {err}" for err in audit_errors)
                detail = f"{detail}; {joined.lstrip()}" if detail else "".join(f"\n  {err}" for err in audit_errors).lstrip()
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
    parser.add_argument("--since", metavar="BASE",
                        help="select only unbounded steps and bounded steps whose inputs changed since BASE")
    parser.add_argument("--steps", action="store_true",
                        help="print the selected step names in gate order instead of running them")
    parser.add_argument("--unread", action="store_true",
                        help="print tracked files covered by no bounded step and exit")
    parser.add_argument("--check-inputs", action="store_true",
                        help="execute selected bounded steps inside sibling hardlinked views of declared inputs only")
    parser.add_argument("--boot-timeout", type=int, default=BOOT_TIMEOUT,
                        help=f"seconds dom0 has to boot and finish before the run counts as a hang (default {BOOT_TIMEOUT})")
    args = parser.parse_args(argv)
    if args.unread and (args.since or args.steps or args.step or args.target or args.check_inputs):
        parser.error("--unread cannot be combined with --target, --step, --since, --steps, or --check-inputs")
    return args


def main(argv, repo=REPO):
    args = arguments(argv)
    if args.unread:
        for path in unread_paths(tracked_paths(repo)):
            print(path)
        return 0
    try:
        changed = changed_paths_since(repo, args.since) if args.since is not None else None
    except Failure as error:
        print(f"tools/gate.py: {error}", file=sys.stderr)
        return 1
    selected = chosen(args.target, args.step, changed)
    if args.check_inputs:
        selected = [s for s in selected if s.inputs is not None and s.name != INPUT_ISOLATION_STEP]
    if args.steps:
        for step in selected:
            print(step.name)
        return 0
    lines, code = (run_steps_isolated(repo, selected, args.boot_timeout) if args.check_inputs
                   else run_gate(Gate(repo, args.boot_timeout), selected))
    print()
    print("\n".join(lines))
    return code


class FakeGate(Gate):
    """A gate whose programs answer from a table, a whole command line to (exit status, stdout),
    with every other command line exiting 0 with nothing to say; a boot that exits 0 leaves an empty
    serial log. It records each call. An answer is for the one command line it names, so a failure
    meant for a check does not also fail the check's own tests."""

    def __init__(self, root, answers=None, boot_timeout=BOOT_TIMEOUT):
        super().__init__(root, boot_timeout)
        self.answers = answers or {}
        self.calls = []
        self.contexts = []

    def call(self, argv, capture=False, merge=False, stdin=None, cwd=None, env=None):
        self.calls.append(list(argv))
        self.contexts.append((list(argv), cwd, env))
        code, stdout = self.answers.get(" ".join(argv), (0, ""))
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
        (self.root / UNWITNESSED).write_text("# a comment\n")
        (self.root / UNREFUSED).write_text("# a comment\n")

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
        self.assertEqual(file_sizes(FakeGate(self.root, {" ".join(FILE_LISTING): (0, listing)})), f"1 files, none over {MAX_FILE_BYTES} bytes")
        with self.assertRaisesRegex(Failure, "over 1048576 bytes: solver.profile$"):
            file_sizes(FakeGate(self.root, {" ".join(FILE_LISTING): (0, listing + "solver.profile\0")}))

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
            verify_for("--target", AARCH64)(FakeGate(self.root, {f"{VERIFY} --target {AARCH64}": (1, three)}))
        with self.assertRaisesRegex(Failure, "no verification results line: error: aborting$"):
            verify_for()(FakeGate(self.root, {VERIFY: (1, "error: aborting\n")}))
        with self.assertRaisesRegex(Failure, "exit status: 1 with no errors counted"):
            verify_for()(FakeGate(self.root, {VERIFY: (1, "verification results:: 9 verified, 0 errors\n")}))
        (self.root / VERIFY_ALLOWANCE).write_text("two\n")
        with self.assertRaisesRegex(Failure, "does not hold a number"):
            verify_for()(FakeGate(self.root))

    # An inventory's listing: a witnessed way, two with none, one of them wired, and a wrapper with none.
    INVENTORY = ("k/retype.rs\tretype\tFreed\twitness_root_frees_a_frame\n"
                 "k/retype.rs\tretype\tSlice\tnone\n"
                 "k/unmap.rs\tunmap_at\tSome\tnone\tno lemma_entry_reaches_unmap_at; claimed by witness_root_unmaps\n"
                 "acall/src/m.rs\tnap\tOPERATION_NAP=9\tnone\n"
                 "witness inventory: 3 of 4 lines are none\n")
    LISTED = ("k/retype.rs\tretype\tSlice\n", "k/unmap.rs\tunmap_at\tSome\n", "acall/src/m.rs\tnap\tOPERATION_NAP=9\n")

    def unwitnessed_with(self, *lines):
        (self.root / UNWITNESSED).write_text("# a comment\n" + "".join(lines))
        return unwitnessed(FakeGate(self.root, {WITNESS_INVENTORY: (0, self.INVENTORY)}))

    def test_the_units_with_no_witness_are_the_lists_lines(self):
        self.assertEqual(self.unwitnessed_with(*self.LISTED),
                         "3 of 4 lines have no witness, each a line of tools/unwitnessed")
        # The order of the list's lines decides nothing.
        self.assertEqual(self.unwitnessed_with(*reversed(self.LISTED)),
                         "3 of 4 lines have no witness, each a line of tools/unwitnessed")

    def test_a_unit_with_no_witness_that_the_list_lacks_fails(self):
        with self.assertRaisesRegex(Failure, "^no witness and no line in tools/unwitnessed:\n  k/unmap.rs\tunmap_at\tSome$"):
            self.unwitnessed_with(self.LISTED[0], self.LISTED[2])

    def test_a_listed_unit_that_has_a_witness_or_is_gone_fails(self):
        witnessed = "k/retype.rs\tretype\tFreed\n"
        with self.assertRaisesRegex(Failure, "^a line in tools/unwitnessed and not without a witness, to remove:\n  k/retype.rs\tretype\tFreed$"):
            self.unwitnessed_with(*self.LISTED, witnessed)
        with self.assertRaisesRegex(Failure, "to remove:\n  k/gone.rs\tgone\ttrue$"):
            self.unwitnessed_with(*self.LISTED, "k/gone.rs\tgone\ttrue\n")
        # A line twice is one line too many, so the list's length is the count.
        with self.assertRaisesRegex(Failure, "to remove:\n  k/retype.rs\tretype\tSlice$"):
            self.unwitnessed_with(*self.LISTED, self.LISTED[0])

    def test_a_change_that_witnesses_one_way_and_loses_another_fails_on_both(self):
        with self.assertRaisesRegex(Failure, "^no witness and no line in tools/unwitnessed:\n  k/retype.rs\tretype\tSlice\n"
                                             "a line in tools/unwitnessed and not without a witness, to remove:\n  k/retype.rs\tretype\tFreed$"):
            self.unwitnessed_with("k/retype.rs\tretype\tFreed\n", *self.LISTED[1:])

    def test_the_unwitnessed_step_runs_the_inventorys_tests_and_comes_after_the_throwaways(self):
        gate = FakeGate(self.root, {WITNESS_INVENTORY: (0, "witness inventory: 0 of 0 lines are none\n")})
        self.assertEqual(unwitnessed(gate), "0 of 0 lines have no witness, each a line of tools/unwitnessed")
        self.assertEqual(gate.calls, [[WITNESS_INVENTORY, "--test"], [WITNESS_INVENTORY]])
        names = [step.name for step in chosen(X86_64)]
        self.assertEqual(names.index("unwitnessed"), names.index("throwaways") + 1)

    def test_the_refused_step_runs_the_checks_tests_then_the_check_after_verify(self):
        said = "refused: 1 false claim in 1 crate, each refused by Verus at the postconditions it declares and nowhere else"
        gate = FakeGate(self.root, {REFUSED_CHECK: (0, said + "\n")})
        step = next(step for step in STEPS if step.name == "refused")
        self.assertEqual(step.check(gate), said)
        self.assertEqual(gate.calls, [[REFUSED_CHECK, "--test"], [REFUSED_CHECK]])
        names = [step.name for step in chosen(X86_64)]
        self.assertLess(names.index("verify"), names.index("refused"))

    # A coverage report: one way a claim covers, one exempt, one entry the rule covers, two with none.
    COVERAGE = ("k/retype.rs\treclaim\tFreed\tk/refused/reclaim.rs\n"
                "k/reclaim.rs\treclaim\tAgain\texempt\n"
                "acall/src/m.rs\tdelete\tOPERATION_DELETE=5\tentry\n"
                "k/unmap.rs\tunmap_at\tSome\tnone\n"
                "k/op.rs\tdispatch\tSome\tnone\n"
                "coverage: 2 of 5 lines have no refused claim\n")
    UNCOVERED = ("k/unmap.rs\tunmap_at\tSome\n", "k/op.rs\tdispatch\tSome\n")

    def unrefused_with(self, *lines, report=None):
        (self.root / UNREFUSED).write_text("# a comment\n" + "".join(lines))
        return unrefused(FakeGate(self.root, {f"{REFUSED_CHECK} --coverage": (0, self.COVERAGE if report is None else report)}))

    def test_the_ways_with_no_refused_claim_are_the_lists_lines(self):
        self.assertEqual(self.unrefused_with(*self.UNCOVERED),
                         "2 of 5 lines have no refused claim, each a line of tools/unrefused")
        self.assertEqual(self.unrefused_with(*reversed(self.UNCOVERED)),
                         "2 of 5 lines have no refused claim, each a line of tools/unrefused")

    def test_a_way_added_without_a_claim_fails(self):
        """A throwaway inventory line with no claim and no list line is the gate's failure."""
        with self.assertRaisesRegex(Failure, "^no refused claim and no line in tools/unrefused:\n  k/unmap.rs\tunmap_at\tSome$"):
            self.unrefused_with(self.UNCOVERED[1])

    def test_removing_a_covered_claim_fails(self):
        """A throwaway that drops the claim, so the way the list does not hold is now none."""
        dropped = self.COVERAGE.replace("k/retype.rs\treclaim\tFreed\tk/refused/reclaim.rs",
                                        "k/retype.rs\treclaim\tFreed\tnone")
        with self.assertRaisesRegex(Failure, "^no refused claim and no line in tools/unrefused:\n  k/retype.rs\treclaim\tFreed$"):
            self.unrefused_with(*self.UNCOVERED, report=dropped)

    def test_a_listed_way_that_has_a_claim_or_is_gone_fails(self):
        covered = "k/retype.rs\treclaim\tFreed\n"
        with self.assertRaisesRegex(Failure, "^a line in tools/unrefused and not without a refused claim, to remove:\n  k/retype.rs\treclaim\tFreed$"):
            self.unrefused_with(*self.UNCOVERED, covered)
        with self.assertRaisesRegex(Failure, "to remove:\n  k/gone.rs\tgone\ttrue$"):
            self.unrefused_with(*self.UNCOVERED, "k/gone.rs\tgone\ttrue\n")
        # A line twice is one line too many, so the list's length is the count.
        with self.assertRaisesRegex(Failure, "to remove:\n  k/unmap.rs\tunmap_at\tSome$"):
            self.unrefused_with(*self.UNCOVERED, self.UNCOVERED[0])

    def test_the_unrefused_step_reads_the_coverage_and_comes_after_refused(self):
        gate = FakeGate(self.root, {f"{REFUSED_CHECK} --coverage": (0, "coverage: 0 of 0 lines have no refused claim\n")})
        (self.root / UNREFUSED).write_text("# a comment\n")
        self.assertEqual(unrefused(gate), "0 of 0 lines have no refused claim, each a line of tools/unrefused")
        self.assertEqual(gate.calls, [[REFUSED_CHECK, "--coverage"]])
        names = [step.name for step in chosen(X86_64)]
        self.assertEqual(names.index("unrefused"), names.index("refused") + 1)
        with self.assertRaisesRegex(Failure, r"^tools/check-refused.py --coverage: exit status: 1$"):
            unrefused(FakeGate(self.root, {f"{REFUSED_CHECK} --coverage": (1, "")}))

    def test_the_invoked_arms_step_fails_on_a_printed_conjunct(self):
        gate = FakeGate(self.root)
        self.assertEqual(invoked_arms(gate), "every arm of invoked carries its operation's ensures")
        self.assertEqual(gate.calls, [[INVOKED_ARMS_CHECK, "--test"], [INVOKED_ARMS_CHECK]])
        dropped = "kernel/verified/capability/revoke.rs:revoke:final(self).flush_epoch >= old(self).flush_epoch\n"
        with self.assertRaisesRegex(Failure, "^tools/check-invoked-arms.py: exit status: 1\n  kernel/verified/capability/revoke.rs:revoke:final"):
            invoked_arms(FakeGate(self.root, {INVOKED_ARMS_CHECK: (1, dropped)}))
        # A line printed is a conjunct not carried, whatever the status says.
        with self.assertRaisesRegex(Failure, "^tools/check-invoked-arms.py: exit status: 0\n  kernel/"):
            invoked_arms(FakeGate(self.root, {INVOKED_ARMS_CHECK: (0, dropped)}))
        self.assertIn("invoked arms", [step.name for step in chosen(X86_64)])

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

    def test_forced_lints_fail_on_a_warning_located_in_the_tree(self):
        def message(level, path, line, text):
            return json.dumps({"reason": "compiler-message", "message": {
                "level": level, "message": text, "rendered": f"{level}: {text}\n",
                "spans": [{"file_name": path, "line_start": line, "is_primary": True}]}})
        outside = message("warning", "/home/u/.rustup/toolchains/t/lib/rustlib/src/rust/library/core/src/pin.rs", 925, "unused import")
        registry = message("warning", "/home/u/.cargo/registry/src/heapless-0.7.17/src/sealed.rs", 42, "never used")
        inside = message("warning", "kernel/verified/pptr.rs", 12, "field `perm` is never read")
        artifact = json.dumps({"reason": "compiler-artifact"})
        self.assertEqual(in_tree_messages("\n".join([outside, registry, artifact]), self.root), [])
        self.assertEqual(in_tree_messages("\n".join([outside, inside, inside]), self.root),
                         [("kernel/verified/pptr.rs:12: warning: field `perm` is never read", "warning: field `perm` is never read\n")])
        members = {" ".join(WORKSPACE_MEMBERS): (0, self.workspace("aheap", "kernel/verified"))}
        clean = FakeGate(self.root, {**members, " ".join(FORCED_LINT_CHECK): (0, outside + "\n")})
        self.assertEqual(forced_lints(clean),
                         "no warning located in the tree: 2 workspace members, each from its own directory, "
                         "and kernel/verified, kernel, dom0, user/hello, aloader for aarch64")
        # Each member from its own directory, since its .cargo config names its target and holds
        # build-std, then each aarch64 target, every one with the lints forced.
        self.assertEqual(clean.contexts[1:],
                         [([*FORCED_LINT_CHECK], "aheap", FORCED_LINT_ENV),
                          ([*FORCED_LINT_CHECK], "kernel/verified", FORCED_LINT_ENV)]
                         + [([*FORCED_LINT_CHECK, *FORCED_LINT_TARGET, target], directory, FORCED_LINT_ENV)
                            for directory, target in FORCED_LINT_AARCH64])
        with self.assertRaisesRegex(Failure, "^1 warning located in the tree:\n  kernel/verified/pptr.rs:12: warning: field `perm` is never read$"):
            forced_lints(FakeGate(self.root, {**members, " ".join(FORCED_LINT_CHECK): (0, inside + "\n")}))
        error = message("error", "kernel/src/main.rs", 3, "cannot find value `x`")
        with self.assertRaisesRegex(Failure, "in aheap: exit status: 101\n  kernel/src/main.rs:3: error: cannot find value `x`$"):
            forced_lints(FakeGate(self.root, {**members, " ".join(FORCED_LINT_CHECK): (101, error + "\n")}))
        with self.assertRaisesRegex(Failure, "^cargo metadata --no-deps --format-version 1: exit status: 101$"):
            forced_lints(FakeGate(self.root, {" ".join(WORKSPACE_MEMBERS): (101, "")}))

    def workspace(self, *directories):
        """cargo metadata's JSON for a workspace whose members are these directories under the root."""
        return json.dumps({"packages": [{"manifest_path": str(self.root / directory / "Cargo.toml")}
                                        for directory in directories]})

    # A warning as rustc renders it in the tree, and one in the toolchain's build-std sources.
    IN_TREE = ("warning: variable does not need to be mutable\n"
               "    --> aheap/src/small.rs:1704:13\n     |\n1704 |         let mut x = 0;\n\n")
    OUTSIDE = ("warning: unused import: `Foo`\n"
               "  --> /home/u/.rustup/toolchains/t/lib/rustlib/src/rust/library/core/src/lib.rs:9:5\n\n"
               "warning: `core` (lib) generated 1 warning\n")

    def test_a_warning_counts_when_rustc_locates_it_in_the_tree(self):
        absolute = f"warning[E0170]: pattern binds\n --> {self.root}/kernel/src/main.rs:3:1\n"
        escaping = "warning: unused\n --> ../verus/source/vstd/lib.rs:1:1\n"
        unplaced = "warning: unused manifest key: x\nwarning: `kernel` (bin) generated 1 warning\n --> nowhere\n"
        self.assertEqual(tree_warnings(self.IN_TREE + self.OUTSIDE + absolute + escaping + unplaced + self.IN_TREE, self.root),
                         ["aheap/src/small.rs:1704:13: variable does not need to be mutable",
                          f"{self.root}/kernel/src/main.rs:3:1: pattern binds"])
        self.assertEqual(tree_warnings(self.OUTSIDE, self.root), [])

    def test_build_and_workspace_tests_fail_on_a_warning_in_the_tree_only(self):
        built = "build x86_64: 9 workspace members\n"
        self.assertEqual(build(FakeGate(self.root, {BUILD: (0, self.OUTSIDE + built)})), built.strip())
        with self.assertRaisesRegex(Failure, "^warnings located in the tree:\n  aheap/src/small.rs:1704:13: variable"):
            build(FakeGate(self.root, {BUILD: (0, self.IN_TREE + built)}))
        cargo = "cargo " + " ".join(WORKSPACE_TESTS)
        tested = "test result: ok. 3 passed; 0 failed\n"
        self.assertEqual(workspace_tests(FakeGate(self.root, {cargo: (0, self.OUTSIDE + tested)})),
                         "3 tests passed in 1 test binaries")
        with self.assertRaisesRegex(Failure, "^warnings located in the tree:\n  aheap/src/small.rs:1704:13: variable"):
            workspace_tests(FakeGate(self.root, {cargo: (0, self.IN_TREE + tested)}))

    def test_a_boot_that_hangs_or_fails_its_log_check_fails(self):
        (self.root / SERIAL_LOG).write_text("old\n")
        hang = FakeGate(self.root, {f"timeout 7 {RUN}": (TIMED_OUT, "")}, boot_timeout=7)
        with self.assertRaisesRegex(Failure, "^no exit within 7 s$"):
            boot_with()(hang)
        self.assertFalse((self.root / SERIAL_LOG).exists())
        held = FakeGate(self.root, {f"{BOOT_LOG_CHECK} --arch {X86_64} --translation -": (0, "exit status 0, translation enabled\n")})
        self.assertEqual(boot_with("--iommu")(held), "exit status 0, translation enabled")
        self.assertEqual(held.calls[-1], [BOOT_LOG_CHECK, "--arch", X86_64, "--translation", "-"])
        with self.assertRaisesRegex(Failure, "^no exit marker$"):
            boot_with()(FakeGate(self.root, {f"{BOOT_LOG_CHECK} --arch {X86_64} -": (1, "no exit marker\n")}))

    def test_the_faq_step_runs_the_scripts_tests_then_holds_docs_faq_to_what_it_writes(self):
        gate = FakeGate(self.root, {f"{FAQ_RENDER} --check": (0, "docs/faq is what tools/faq.py writes\n")})
        self.assertEqual(faq(gate), "docs/faq is what tools/faq.py writes")
        self.assertEqual(gate.calls, [[FAQ_RENDER, "--test"], [FAQ_RENDER, "--check"]])
        with self.assertRaisesRegex(Failure, "^tools/faq.py --check: exit status: 1$"):
            faq(FakeGate(self.root, {f"{FAQ_RENDER} --check": (1, "")}))
        self.assertIn("faq", [step.name for step in chosen(X86_64)])

    def test_every_step_fails_the_gate_when_a_program_it_runs_fails(self):
        """One failing run per step: each program a step runs, in turn, exits 1 with nothing said."""
        verified = (0, "verification results:: 1 verified, 0 errors\n")
        good = {VERIFY: verified, f"{VERIFY} --target {AARCH64}": verified,
                "cargo " + " ".join(WORKSPACE_TESTS): (0, "test result: ok. 1 passed; 0 failed\n"),
                " ".join(WORKSPACE_MEMBERS): (0, self.workspace("aheap"))}
        for step in STEPS:
            passing = FakeGate(self.root, dict(good))
            lines, code = run_gate(passing, [step])
            self.assertEqual(code, 0, lines)
            for at, argv in enumerate(passing.calls):
                program = " ".join(argv)
                if argv in passing.calls[:at]:
                    continue
                with self.subTest(step=step.name, program=program):
                    failing = FakeGate(self.root, {**good, program: (1, "")})
                    lines, code = run_gate(failing, [step])
                    self.assertEqual(code, 1)
                    self.assertRegex(lines[0], f"^gate {step.name}: FAIL in ")
                    # The program itself ran and failed the step, after every call before it passed.
                    self.assertEqual(failing.calls, passing.calls[:at + 1])

    def test_a_failing_step_does_not_stop_the_steps_after_it(self):
        ticks = iter(range(100))
        lines, code = run_gate(FakeGate(self.root, {" ".join(FILE_LISTING): (128, "")}), chosen(names=["file sizes", "hooks"]), lambda: next(ticks))
        self.assertEqual(code, 1)
        self.assertEqual(lines, ["gate file sizes: FAIL in 1.0 s: git ls-files: exit status: 128",
                                 "gate hooks: ok in 1.0 s: the license guard refuses what it must; the actor hook names the session",
                                 "gate total: 5.0 s"])

    def test_a_program_that_cannot_start_fails_its_step(self):
        with self.assertRaisesRegex(Failure, "^tools/missing.py: No such file or directory$"):
            Gate(self.root, BOOT_TIMEOUT).call(["tools/missing.py"])

    def test_glob_matching_follows_posix_tree_semantics(self):
        self.assertTrue(matches_globs("kernel/verified/pptr.rs", ("kernel/verified/**",)))
        self.assertTrue(matches_globs("./kernel/verified/capability/retype.rs", ("kernel/verified/**",)))
        self.assertFalse(matches_globs("kernel/verified-extra/a.rs", ("kernel/verified/**",)))
        self.assertTrue(matches_globs("kernel/.cargo/config.toml", ("kernel/**",)))
        self.assertTrue(matches_globs("user/x86_64-unknown-aloader.json", ("user/*-unknown-aloader.json",)))
        self.assertFalse(matches_globs("user/hello/x86_64-unknown-aloader.json", ("user/*-unknown-aloader.json",)))
        self.assertTrue(matches_globs("design/gate-runs-steps-whose-inputs-changed/DECISION.md", ("design/*/DECISION.md",)))
        self.assertFalse(matches_globs("design/README.md", ("design/*/DECISION.md",)))
        self.assertTrue(matches_globs("Cargo.toml", ("Cargo.toml",)))
        self.assertFalse(matches_globs("kernel/Cargo.toml", ("Cargo.toml",)))
        self.assertFalse(matches_globs("", ("**",)))

    def test_input_slice_digest_hashes_only_matching_entries_deterministically(self):
        base_entries = [
            ("100644", "b" * 40, ".claude/agents/round.md"),
            ("100644", "a" * 40, "kernel/verified/lib.rs"),
            ("100644", "c" * 40, "kernel/src/main.rs"),
        ]
        verify_step = next(step for step in STEPS if step.name == "verify")
        self.assertIsNone(input_slice_digest(base_entries, None))
        d1 = input_slice_digest(base_entries, verify_step.inputs)
        d2 = input_slice_digest(reversed(base_entries), verify_step.inputs)
        self.assertEqual(d1, d2)
        # An edit outside verify.inputs keeps the exact same digest.
        touched_unverified = [
            ("100644", "b" * 40, ".claude/agents/round.md"),
            ("100644", "a" * 40, "kernel/verified/lib.rs"),
            ("100644", "d" * 40, "kernel/src/main.rs"),
        ]
        self.assertEqual(input_slice_digest(touched_unverified, verify_step.inputs), d1)
        # An edit to mode or blob SHA inside verify.inputs changes the digest.
        touched_mode = [
            ("100644", "b" * 40, ".claude/agents/round.md"),
            ("100755", "a" * 40, "kernel/verified/lib.rs"),
            ("100644", "c" * 40, "kernel/src/main.rs"),
        ]
        self.assertNotEqual(input_slice_digest(touched_mode, verify_step.inputs), d1)
        touched_blob = [
            ("100644", "b" * 40, ".claude/agents/round.md"),
            ("100644", "e" * 40, "kernel/verified/lib.rs"),
            ("100644", "c" * 40, "kernel/src/main.rs"),
        ]
        self.assertNotEqual(input_slice_digest(touched_blob, verify_step.inputs), d1)

    def test_parse_ls_tree_reads_nul_records(self):
        raw = b"100644 blob " + b"1" * 40 + b"\tCargo.toml\x00120000 blob " + b"2" * 40 + b"\tAGENTS.md\x00"
        self.assertEqual(parse_ls_tree(raw), [
            ("100644", "1" * 40, "Cargo.toml"),
            ("120000", "2" * 40, "AGENTS.md"),
        ])

    def test_step_selection_for_diff_and_unread_paths(self):
        names = lambda changed: [step.name for step in chosen(changed=changed)]
        self.assertEqual(names([".claude/agents/round.md"]), ["file sizes", "source licenses"])
        self.assertEqual(names(["CLAUDE.md", "tools/loop.py"]), ["file sizes", "source licenses"])

        unverified_kernel = names(["kernel/src/boot/free_ranges.rs"])
        for omitted in ("verify", "verify aarch64", "throwaways", "unwitnessed", "refused", "unrefused",
                        "page literals", "invoked arms", "layout claims", "upstream copies", "faq"):
            self.assertNotIn(omitted, unverified_kernel)
        for included in ("file sizes", "source licenses", "build", "workspace tests", "forced lints",
                         "external body", "boundary", "arch sources", "boot stack", "coverage",
                         "iommu boot", "boot", "aarch64 boot"):
            self.assertIn(included, unverified_kernel)

        verified_kernel = names(["kernel/verified/kernel.rs"])
        self.assertIn("verify", verified_kernel)
        self.assertIn("verify aarch64", verified_kernel)

        cargo_change = names(["Cargo.toml"])
        self.assertEqual(cargo_change, [step.name for step in STEPS])

        self.assertEqual(
            unread_paths(["Cargo.toml", ".claude/agents/round.md", "kernel/src/main.rs", "tools/loop.py", "README.md"]),
            [".claude/agents/round.md", "tools/loop.py", "README.md"],
        )

    def test_real_steps_inputs_are_complete_against_repo_metadata(self):
        self.assertEqual(step_input_errors(STEPS, repo=REPO), [])

    def test_missing_workspace_transitive_or_tool_glob_is_caught(self):
        base_meta = load_cargo_metadata(REPO)
        faq_paths = load_faq_paths(REPO)
        patch_targets = load_patch_targets(REPO)
        tool_calls = collect_step_tool_calls()

        def drop_glob(step_name, glob):
            mutated = []
            for step in STEPS:
                if step.name == step_name:
                    reduced = tuple(g for g in step.inputs if g != glob)
                    self.assertNotEqual(reduced, step.inputs, f"{glob} not in {step_name}")
                    mutated.append(step._replace(inputs=reduced))
                else:
                    mutated.append(step)
            return tuple(mutated)

        # Missing workspace member glob in build and in license.
        self.assertTrue(step_input_errors(drop_glob("build", "file-service/**"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        self.assertTrue(step_input_errors(drop_glob("license", "file-service/Cargo.toml"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        # Missing transitive dependency glob in verify (asys) and in boot (aelf).
        self.assertTrue(step_input_errors(drop_glob("verify", "asys/**"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        self.assertTrue(step_input_errors(drop_glob("boot", "aelf/**"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        # Missing tool glob in boot (tools/gdb.py) and in build (tools/check-stack-sizes.py) and in faq (tools/faq.py).
        self.assertTrue(step_input_errors(drop_glob("boot", "tools/gdb.py"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        self.assertTrue(step_input_errors(drop_glob("build", "tools/check-stack-sizes.py"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        self.assertTrue(step_input_errors(drop_glob("faq", "tools/faq.py"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        # Missing upstream patch target or faq constant path.
        self.assertTrue(step_input_errors(drop_glob("upstream copies", "kernel/verified/pptr.rs"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        self.assertTrue(step_input_errors(drop_glob("faq", "kernel/verified/define.rs"), REPO, base_meta, faq_paths, patch_targets, tool_calls))
        # Missing FORCED_LINT_AARCH64 target spec.
        self.assertTrue(step_input_errors(drop_glob("forced lints", "user/*-unknown-aloader.json"), REPO, base_meta, faq_paths, patch_targets, tool_calls))

        # Simulated new workspace crate and new transitive verified crate dependency.
        extra_meta = json.loads(json.dumps(base_meta))
        extra_meta["packages"].append({
            "name": "new-crate",
            "manifest_path": str(REPO / "new-crate/Cargo.toml"),
            "metadata": {"atmosphere": {"verified": True}},
            "dependencies": [],
        })
        self.assertTrue(step_input_errors(STEPS, REPO, extra_meta, faq_paths, patch_targets, tool_calls))

    def test_since_and_steps_and_unread_cli_in_temp_git_repo(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            subprocess.run(["git", "init", "-q", "-b", "main", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.name", "t"], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.email", "t@t.invalid"], check=True)
            for rel in ("Cargo.toml", ".claude/agents/round.md", "kernel/src/main.rs", "kernel/verified/lib.rs"):
                p = repo / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("seed\n")
            subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
            subprocess.run(["git", "-C", str(repo), "commit", "-q", "-m", "seed"], check=True)
            base = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()

            self.assertEqual(unread_paths(tracked_paths(repo)), [".claude/agents/round.md"])

            (repo / ".claude/agents/round.md").write_text("edited\n")
            subprocess.run(["git", "-C", str(repo), "commit", "-qam", "doc"], check=True)
            self.assertEqual([s.name for s in chosen(changed=changed_paths_since(repo, base))],
                             ["file sizes", "source licenses"])
            entries_base = ls_tree_entries(repo, base)
            entries_head = ls_tree_entries(repo, "HEAD")
            verify_step = next(s for s in STEPS if s.name == "verify")
            self.assertEqual(input_slice_digest(entries_base, verify_step.inputs),
                             input_slice_digest(entries_head, verify_step.inputs))

            (repo / "kernel/src/main.rs").write_text("edited\n")
            subprocess.run(["git", "-C", str(repo), "commit", "-qam", "src"], check=True)
            since_src = [s.name for s in chosen(changed=changed_paths_since(repo, "HEAD~1"))]
            self.assertNotIn("verify", since_src)
            self.assertIn("build", since_src)

            (repo / "kernel/verified/lib.rs").write_text("edited\n")
            subprocess.run(["git", "-C", str(repo), "commit", "-qam", "ver"], check=True)
            since_ver = [s.name for s in chosen(changed=changed_paths_since(repo, "HEAD~1"))]
            self.assertIn("verify", since_ver)
            self.assertIn("verify aarch64", since_ver)

            unread_out = io.StringIO()
            with contextlib.redirect_stdout(unread_out):
                self.assertEqual(main(["--unread"], repo=repo), 0)
            self.assertEqual(unread_out.getvalue().splitlines(), [".claude/agents/round.md"])

            steps_out = io.StringIO()
            with contextlib.redirect_stdout(steps_out):
                self.assertEqual(main(["--since", "HEAD~2", "--steps"], repo=repo), 0)
            steps_lines = steps_out.getvalue().splitlines()
            self.assertIn("file sizes", steps_lines)
            self.assertIn("source licenses", steps_lines)
            self.assertIn("verify", steps_lines)

            err_out = io.StringIO()
            with contextlib.redirect_stderr(err_out):
                self.assertEqual(main(["--since", "no-such-ref", "--steps"], repo=repo), 1)
            self.assertIn("tools/gate.py:", err_out.getvalue())

    def test_arguments_accept_since_steps_and_unread(self):
        args = arguments(["--since", "main", "--steps"])
        self.assertEqual(args.since, "main")
        self.assertTrue(args.steps)
        self.assertFalse(args.unread)
        self.assertTrue(arguments(["--unread"]).unread)

    def test_arguments_accept_check_inputs_and_reject_unread_combo(self):
        args = arguments(["--check-inputs", "--step", "hooks"])
        self.assertTrue(args.check_inputs)
        self.assertEqual(args.step, ["hooks"])
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                arguments(["--unread", "--check-inputs"])

    def test_parse_dep_info_handles_continuations_escapes_and_comments(self):
        text = (
            "# env-dep:CARGO_MANIFEST_DIR=/tmp/x\n"
            "/t/foo.d: a/src/lib.rs \\\n"
            "  a/src/with\\ space.rs a/src/foo\\#1.rs\n\n"
            "a/src/lib.rs:\n"
        )
        self.assertEqual(
            parse_dep_info(text),
            ["a/src/lib.rs", "a/src/with space.rs", "a/src/foo#1.rs"],
        )

    def test_dep_info_audit_rejects_undeclared_include_str_path_and_build_rs(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            (repo / "Cargo.toml").write_text('[workspace]\nresolver = "2"\nmembers = ["a", "secret", "other"]\n')
            for crate in ("a", "secret", "other"):
                (repo / crate / "src").mkdir(parents=True)
                (repo / crate / "Cargo.toml").write_text(f'[package]\nname = "{crate}"\nversion = "0.1.0"\nedition = "2021"\n')
            (repo / "secret" / "data.txt").write_text("top-secret\n")
            (repo / "other" / "mod.rs").write_text("pub fn helper() -> u32 { 7 }\n")
            (repo / "a" / "src" / "lib.rs").write_text(
                '#[path = "../../other/mod.rs"] mod extra;\n'
                'pub fn val() -> (&\'static str, u32) { (include_str!("../../secret/data.txt"), extra::helper()) }\n'
            )

            # Pre-existing untouched stale .d outside step.inputs should not trigger false failures.
            stale_dir = repo / "target/debug/deps"
            stale_dir.mkdir(parents=True)
            stale_d = stale_dir / "old.d"
            stale_d.write_text(f"{stale_d}: unrelated/old.rs\n")

            def compile_a(gate):
                out_dir = gate.root / "target/debug/deps"
                out_dir.mkdir(parents=True, exist_ok=True)
                done = gate.call([
                    "rustc", "--crate-type", "lib", "--edition", "2021",
                    "--emit=dep-info=" + str(out_dir / "liba.d"),
                    "--emit=metadata=" + str(out_dir / "liba.rmeta"),
                    str(gate.root / "a/src/lib.rs"),
                ], capture=True, merge=True)
                if done.code != 0:
                    raise Failure(done.stdout)
                return "compiled"

            bounded_a = Step("build", X86_64, compile_a, bounded("a/**"))
            lines, code = run_gate(Gate(repo, BOOT_TIMEOUT), [bounded_a])
            self.assertEqual(code, 1, lines)
            self.assertIn("secret/data.txt", lines[0])
            self.assertIn("other/mod.rs", lines[0])

            # build.rs cargo:rerun-if-changed outside step.inputs fails too.
            def build_script_only(gate):
                build_out = gate.root / "target/debug/build/a-0123456789abcdef"
                build_out.mkdir(parents=True, exist_ok=True)
                (build_out / "output").write_text("cargo:rerun-if-changed=../secret/blob.bin\n")
                # Allowed external & target-generated paths should not fail by themselves.
                (stale_dir / "ext.d").write_text(
                    f"{stale_dir / 'ext.d'}: a/src/lib.rs ../reference/lmdb/lmdb.h target/debug/build/a/out/gen.rs\n"
                )
                return "ok"

            lines2, code2 = run_gate(Gate(repo, BOOT_TIMEOUT), [Step("build", X86_64, build_script_only, bounded("a/**"))])
            self.assertEqual(code2, 1, lines2)
            self.assertIn("secret/blob.bin", lines2[0])

            # Allowed dep-info passes when stale.d stays untouched.
            def clean_compile(gate):
                (repo / "target/debug/build/a-0123456789abcdef/output").unlink()
                ok_d = gate.root / "target/debug/deps/ok.d"
                ok_d.write_text(f"{ok_d}: a/src/lib.rs ../reference/lmdb/lmdb.h /usr/include/stdio.h target/debug/out/x.bin\n")
                return "ok"

            lines3, code3 = run_gate(Gate(repo, BOOT_TIMEOUT), [Step("build", X86_64, clean_compile, bounded("a/**"))])
            self.assertEqual(code3, 0, lines3)

    def test_check_inputs_sandbox_catches_undeclared_read_and_preserves_siblings(self):
        with tempfile.TemporaryDirectory() as outer_td:
            outer = Path(outer_td)
            (outer / "reference").mkdir()
            (outer / "reference/ref.txt").write_text("from-reference\n")
            (outer / "verus").mkdir()
            (outer / "verus/marker").write_text("v\n")
            repo = outer / "repo"
            repo.mkdir()
            (repo / "Cargo.toml").write_text('[workspace]\nresolver = "2"\nmembers = ["a", "b"]\n')
            (repo / "Cargo.lock").write_text("# lock\n")
            for name in ("a", "b"):
                (repo / name / "src").mkdir(parents=True)
                (repo / name / "Cargo.toml").write_text(f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n')
                (repo / name / "src/lib.rs").write_text("pub fn ok() {}\n")
            (repo / "CLAUDE.md").write_text("rules\n")
            os.symlink("CLAUDE.md", repo / "AGENTS.md")
            (repo / "undeclared").mkdir()
            (repo / "undeclared/secret.txt").write_text("hidden\n")
            (repo / "declared").mkdir()
            (repo / "declared/ok.txt").write_text("visible\n")
            (repo / "tools").mkdir()
            probe = repo / "tools/probe.py"
            probe.write_text(
                "#!/usr/bin/env python3\n"
                "from pathlib import Path\n"
                "import os, sys, tomllib\n"
                "root = Path(__file__).resolve().parent.parent\n"
                "assert (root.parent / 'reference/ref.txt').read_text().strip() == 'from-reference'\n"
                "assert (root.parent / 'verus/marker').read_text().strip() == 'v'\n"
                "assert (root / 'declared/ok.txt').read_text().strip() == 'visible'\n"
                "assert os.path.islink(root / 'AGENTS.md') and os.readlink(root / 'AGENTS.md') == 'CLAUDE.md'\n"
                "members = tomllib.loads((root / 'Cargo.toml').read_text())['workspace']['members']\n"
                "assert members == ['a'], members\n"
                "assert (root / 'Cargo.lock').stat().st_ino != int(os.environ['ORIG_LOCK_INO'])\n"
                "if os.environ.get('TRY_UNDECLARED') == '1':\n"
                "    (root / 'undeclared/secret.txt').read_text()\n"
                "print('probe-ok')\n"
            )
            probe.chmod(0o755)
            probe_step = Step(
                "probe",
                X86_64,
                lambda gate: check_output(gate, "tools/probe.py").strip(),
                ("tools/probe.py", "declared/**", "a/**", "Cargo.toml", "Cargo.lock", "AGENTS.md"),
            )
            orig_lock_ino = str((repo / "Cargo.lock").stat().st_ino)
            with mock.patch.dict(os.environ, {"TRY_UNDECLARED": "0", "ORIG_LOCK_INO": orig_lock_ino}):
                lines, code = run_steps_isolated(repo, [probe_step], BOOT_TIMEOUT)
            self.assertEqual(code, 0, lines)
            self.assertIn("probe-ok", lines[0])
            # Narrowing Cargo.toml inside sandbox must never mutate original repo/Cargo.toml.
            self.assertIn('"b"', (repo / "Cargo.toml").read_text())

            with mock.patch.dict(os.environ, {"TRY_UNDECLARED": "1", "ORIG_LOCK_INO": orig_lock_ino}):
                lines_fail, code_fail = run_steps_isolated(repo, [probe_step], BOOT_TIMEOUT)
            self.assertEqual(code_fail, 1, lines_fail)
            self.assertIn("FAIL", lines_fail[0])

            # Adding an undeclared workspace path dependency in Cargo.toml fails inside sandbox.
            (repo / "a/Cargo.toml").write_text(
                '[package]\nname = "a"\nversion = "0.1.0"\nedition = "2021"\n'
                '[dependencies]\nb = { path = "../b" }\n'
            )
            cargo_step = Step(
                "cargo probe",
                X86_64,
                lambda gate: check_output(gate, "cargo", "metadata", "--no-deps", "--format-version", "1"),
                ("a/**", "Cargo.toml", "Cargo.lock"),
            )
            lines_meta, code_meta = run_steps_isolated(repo, [cargo_step], BOOT_TIMEOUT)
            self.assertEqual(code_meta, 1, lines_meta)

            # --check-inputs --steps excludes unbounded steps and step inputs itself.
            steps_out = io.StringIO()
            with contextlib.redirect_stdout(steps_out):
                self.assertEqual(main(["--check-inputs", "--steps"], repo=REPO), 0)
            isolated_names = steps_out.getvalue().splitlines()
            self.assertNotIn("file sizes", isolated_names)
            self.assertNotIn("source licenses", isolated_names)
            self.assertNotIn(INPUT_ISOLATION_STEP, isolated_names)
            self.assertIn("hooks", isolated_names)

    def test_step_inputs_step_exists_before_aarch64_boot_and_covers_tools(self):
        names = [s.name for s in STEPS]
        self.assertIn("step inputs", names)
        si = next(s for s in STEPS if s.name == "step inputs")
        self.assertEqual(si.target, X86_64)
        self.assertLess(names.index("step inputs"), names.index("aarch64 boot"))
        for sample in ("tools/gate.py", "tools/verify.py", ".claude/hooks/license-guard.sh",
                       "dom0/Cargo.toml", "boot-host-tests/src/lib.rs", "AGENTS.md"):
            self.assertTrue(matches_globs(sample, si.inputs), sample)


if __name__ == "__main__":
    import toolchain
    toolchain.apply()
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
