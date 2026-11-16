#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Gate the change in this worktree selectively and land it on main, with no lock around either.

Run from a task worktree whose change is committed. The branch is rebased
onto main and tools/gate.py runs selectively on that: all unbounded steps (file sizes, source
licenses) always run, and each bounded step runs unless its input-slice digest is unchanged since base
and logs/gate-ledger already holds a pass for that (step_name, slice_hash)
(design/gate-runs-steps-whose-inputs-changed/). When the selected steps pass, the branch is rebased
again, since main may have moved while the gate ran, merged into main as a fast-forward and pushed.
git refuses a fast-forward that main moved under and a merge while main's index is taken, so both
are tried again from the rebase. A rebase that is clean lands without a second gate: what landed
beside it is gated per changed step with whatever change is gated on top of it next
(design/land-without-regating/).

The ledger, logs/gate-ledger at the project root, holds per-step verdicts keyed by
(step_name, input_slice_hash), alongside legacy whole-tree entries during migration. When aarch64
boot passes only because tools/board.py emitted 'skip: orangepi5 unreachable', no pass is recorded
for aarch64 boot so an unreachable board never suppresses later hardware checks.

When the gate fails, blame and --judge-base operate per failing step. A base whose failing step
already passed in logs/gate-ledger means the change is at fault. A base with no verdict on a
failing step is unjudged, and the tool says so and stops: most failures are plainly the change's,
and a gate of the base would be spent to learn nothing. When the failure is not plainly the
change's, --judge-base gates only the failing/unjudged steps on the base by itself, detached in
this worktree, its output in logs/base-<commit>-gate.log, and its verdicts join the ledger, where
other loops' landings find them instead of gating the same base again. A base that fails a step is
printed with that step's suspects: commits since the last recorded pass for that step whose diff
touched the step's declared inputs.

An external_body or exec_allows_no_decreases_clause item in tools/external-body-list is a claim
nobody vouches for, debt whatever class its line states, and adding one lowers what the proof covers,
which is the human's to allow (CLAUDE.md, Testability). So before the gate the list on the branch is
compared with the list on the base, by path, item and attribute: such an item the base does not hold,
new or turned from an assumed specification, stops the landing and is named, unless --approve names
it, once the human's answer is on the question the change waits on. A line of tools/unwitnessed is
a way an operation succeeds that no witness reaches, and adding one lowers what the proof shows from
below, which is the human's to allow the same way (design/witness-per-way-an-operation-succeeds/):
a line the base's list does not hold stops the landing and is named, as path:operation:way, unless
--approve names it. A line of tools/unrefused is a way with no refused claim, and a line of
tools/refused-exempt is a way whose specification admits an unchanged component; adding either
lowers what the check shows, which is the human's to allow the same way
(design/refused-claim-per-way/). A line of either list the base's does not hold stops the landing
and is named, as path:operation:way, unless --approve names it. The committer is not the adversary
(design/committer-is-not-the-adversary/), so this is a tripwire, not a lock.

Exit status:
  0  landed and pushed
  1  the gate fails and the base passes: the change is at fault
  2  not run: no branch, the base's own branch, or uncommitted changes
  3  the rebase stopped on a conflict; resolve it, continue the rebase and land again
  4  the base fails the gate by itself; main is broken and the change is not judged
  5  the change is cleared to land and did not reach origin: the merge or the push kept failing
  6  the gate fails and no gate has judged the base: fix the change, or settle it with --judge-base
  7  not gated: the change adds an external_body or exec_allows_no_decreases_clause item, or a line of
     tools/unwitnessed, tools/unrefused or tools/refused-exempt, the human has not approved

usage: tools/land.py [--onto BRANCH] [--gate COMMAND] [--approve PATH:ITEM:ATTRIBUTE | PATH:OPERATION:WAY]...
       tools/land.py --judge-base [--onto BRANCH] [--gate COMMAND] [--step NAME]...    (exits 1 or 4)
       tools/land.py --test    (this script's own tests)
"""
import argparse
import fcntl
import importlib.util
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

LANDED, CHANGE_FAILS, NOT_RUN, CONFLICT, BASE_FAILS, NOT_LANDED, BASE_UNJUDGED, UNAPPROVED = range(8)
LEDGER = "logs/gate-ledger"
BASE_LOCK = "logs/gate-base.lock"
GATE = "tools/gate.py"
BOARD_STEP = "aarch64 boot"
BOARD_SKIP = "skip: orangepi5 unreachable"
STEP_LINE = re.compile(r"^gate (.+?): (ok|FAIL) in \d+\.\d+ s:(?: (.*))?$")
# The list of every claim a verified crate takes unproven, and the attributes of it that nobody vouches
# for: every item but an assumed specification, which names who does.
EXEMPTIONS = "tools/external-body-list"
UNVOUCHED = ("external_body", "exec_allows_no_decreases_clause")
# The list of every way an operation succeeds that no witness reaches, which the gate holds equal to
# the witness inventory: path, operation, way.
UNWITNESSED = "tools/unwitnessed"
# The same shape of list for the ways with no refused claim, and for the ways the check exempts.
UNREFUSED = "tools/unrefused"
REFUSED_EXEMPT = "tools/refused-exempt"
# How often the rebase and the fast-forward are tried while other landings move main.
MERGE_TRIES = 30
PUSH_TRIES = 3
# How far back a broken base's suspects are listed when no tree before them passed.
SUSPECT_LIMIT = 50


def say(text):
    print(f"land: {text}", flush=True)


def git(where, *args):
    """A git command that cannot fail short of a bug here; its output."""
    return subprocess.run(["git", "-C", str(where), *args], check=True, stdout=subprocess.PIPE, text=True).stdout.strip()


def tried(where, *args):
    """A git command that may be refused; whether it went through. Its output goes to ours."""
    return subprocess.run(["git", "-C", str(where), *args], stdout=sys.stdout, stderr=subprocess.STDOUT).returncode == 0


def tree(where, commit):
    return git(where, "rev-parse", f"{commit}^{{tree}}")


def load_gate_module(worktree):
    """Loads tools/gate.py from worktree when present, else the sibling gate.py beside this script."""
    candidate = Path(worktree) / GATE
    source = candidate if candidate.is_file() else Path(__file__).with_name("gate.py")
    spec = importlib.util.spec_from_file_location(f"atmo_gate_{abs(hash(str(source)))}", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def gate_command_for_steps(gate_command, steps):
    flags = " ".join(f"--step {shlex.quote(step.name)}" for step in steps)
    return f"{gate_command} {flags}" if flags else gate_command


def run_gate_command(worktree, gate_command, steps, output):
    """Runs gate_command with --step flags for steps, streaming output and capturing lines."""
    cmd = gate_command_for_steps(gate_command, steps)
    proc = subprocess.Popen(
        cmd,
        shell=True,
        cwd=worktree,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        errors="replace",
    )
    lines = []
    for line in proc.stdout:
        output.write(line)
        output.flush()
        lines.append(line)
    code = proc.wait()
    return code, lines


def parse_step_results(lines, selected_steps, exit_code):
    """Maps each selected step name to 'pass', 'fail', or 'skip' (unreachable hardware)."""
    names = {step.name for step in selected_steps}
    raw_status = {}
    board_skipped = False
    for raw_line in lines:
        line = raw_line.rstrip("\r\n")
        if line.strip() == BOARD_SKIP:
            board_skipped = True
        match = STEP_LINE.match(line)
        if match and match.group(1) in names:
            step_name, verdict, detail = match.group(1), match.group(2), match.group(3) or ""
            if step_name == BOARD_STEP and verdict == "ok" and BOARD_SKIP in detail:
                board_skipped = True
            raw_status[step_name] = "ok" if verdict == "ok" else "fail"
    results = {}
    if raw_status:
        for step in selected_steps:
            st = raw_status.get(step.name)
            if st == "ok":
                results[step.name] = "skip" if (step.name == BOARD_STEP and board_skipped) else "pass"
            elif st == "fail":
                results[step.name] = "fail"
            elif exit_code != 0:
                results[step.name] = "fail"
        if exit_code != 0 and "fail" not in results.values():
            for step in selected_steps:
                results[step.name] = "fail"
    else:
        verdict = "pass" if exit_code == 0 else "fail"
        for step in selected_steps:
            if verdict == "pass" and step.name == BOARD_STEP and board_skipped:
                results[step.name] = "skip"
            else:
                results[step.name] = verdict
    return results


def record_step(root, step_name, slice_hash, verdict, commit):
    """One per-step verdict line written at once so concurrent loops do not tear each other's."""
    with open(root / LEDGER, "a", encoding="utf-8") as ledger:
        ledger.write(f"{step_name}\t{slice_hash}\t{verdict}\t{commit}\t{int(time.time())}\n")


def load_ledger(root):
    """Reads per-step (step_name, slice_hash) and legacy whole-tree verdicts from logs/gate-ledger."""
    ledger = root / LEDGER
    lines = ledger.read_text(encoding="utf-8", errors="replace").splitlines() if ledger.exists() else []
    step_verdicts = {}
    legacy_verdicts = {}
    passed_commits = set()
    for line in lines:
        if not line.strip() or line.startswith("#"):
            continue
        if "\t" in line:
            parts = line.split("\t")
            if len(parts) == 5 and parts[2] in ("pass", "fail"):
                step_name, slice_hash, verdict, commit, _ = parts
                step_verdicts[(step_name, slice_hash)] = (verdict, commit)
                if verdict == "pass":
                    passed_commits.add(commit)
        else:
            parts = line.split()
            if len(parts) == 4 and parts[1] in ("pass", "fail"):
                tree_id, verdict, commit, _ = parts
                legacy_verdicts[tree_id] = (verdict, commit)
                if verdict == "pass":
                    passed_commits.add(commit)
    return step_verdicts, legacy_verdicts, passed_commits


def select_steps(steps, head_hashes, base_hashes, step_verdicts):
    """All unbounded steps, plus bounded steps changed since base or lacking base pass in ledger."""
    selected = []
    for step in steps:
        if step.inputs is None:
            selected.append(step)
            continue
        head_h = head_hashes[step.name]
        base_h = base_hashes[step.name]
        base_passed = step_verdicts.get((step.name, base_h), ("", ""))[0] == "pass"
        if head_h != base_h or not base_passed:
            selected.append(step)
    return selected


def record_passed_steps(root, steps, step_results, slice_hashes, commit, only_matching=None):
    for step in steps:
        if step.inputs is None:
            continue
        if step_results.get(step.name) == "pass":
            sh = slice_hashes[step.name]
            if only_matching is not None and sh != only_matching.get(step.name):
                continue
            record_step(root, step.name, sh, "pass", commit)


def judge_hint_path(worktree):
    git_dir = Path(git(worktree, "rev-parse", "--path-format=absolute", "--git-dir"))
    return git_dir / "land-judge-steps.json"


def base_log(commit):
    return f"logs/base-{commit[:12]}-gate.log"


def commit_changed_paths(worktree, commit):
    raw = subprocess.run(
        ["git", "-C", str(worktree), "diff-tree", "--no-commit-id", "--name-only",
         "--no-renames", "-r", "--root", "-z", "-m", "--first-parent", commit],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    text = raw.decode("utf-8", errors="surrogateescape")
    return [p for p in text.split("\0") if p]


def suspects(root, worktree, base, step, gate_mod, step_verdicts, legacy_verdicts, passed_commits):
    """The commits since the last recorded pass for step whose diff touched step.inputs."""
    found = []
    history = git(worktree, "log", "--first-parent", f"--max-count={SUSPECT_LIMIT}", "--format=%H %T %s", base)
    for line in history.splitlines():
        commit, tree_id, subject = line.split(" ", 2)
        if step.inputs is None:
            if commit in passed_commits or legacy_verdicts.get(tree_id, ("", ""))[0] == "pass":
                return found, True
            found.append((commit, subject))
        else:
            slice_h = gate_mod.input_hash(worktree, tree_id, step)
            if (step_verdicts.get((step.name, slice_h), ("", ""))[0] == "pass"
                    or legacy_verdicts.get(tree_id, ("", ""))[0] == "pass"):
                return found, True
            changed = commit_changed_paths(worktree, commit)
            if any(gate_mod.matches_globs(path, step.inputs) for path in changed):
                found.append((commit, subject))
    return found, False


def blame_steps(root, worktree, onto, base, target_steps, gate_mod, base_hashes,
                step_verdicts, legacy_verdicts, passed_commits, local_results=None):
    """Says whose failure the failing steps are from per-step base verdicts."""
    local_results = local_results or {}
    base_tree = tree(worktree, base)
    base_failed = []
    base_unjudged = []
    base_passed = []
    for step in target_steps:
        if step.name in local_results:
            verdict = local_results[step.name]
            judged_as = base
        elif step.inputs is None:
            if base in passed_commits or legacy_verdicts.get(base_tree, ("", ""))[0] == "pass":
                verdict, judged_as = "pass", base
            else:
                verdict, judged_as = None, None
        else:
            known = step_verdicts.get((step.name, base_hashes[step.name]))
            verdict, judged_as = known if known is not None else (None, None)
        if verdict == "fail":
            base_failed.append((step, judged_as))
        elif verdict is None:
            base_unjudged.append(step)
        else:
            base_passed.append(step)

    if base_failed:
        for step, judged_as in base_failed:
            say(f"{onto} at {base} fails the gate by itself ({base_log(judged_as)}) on {step.name}: {onto} is broken and the change is not judged")
            found, bounded = suspects(root, worktree, base, step, gate_mod, step_verdicts, legacy_verdicts, passed_commits)
            for commit, subject in found:
                say(f"suspect {commit} {subject} (for {step.name})")
            if not bounded:
                say(f"no tree among the last {SUSPECT_LIMIT} commits passed {step.name}: the suspects go further back")
        return BASE_FAILS

    if base_unjudged:
        hint = {"base": base, "steps": [step.name for step in base_unjudged]}
        judge_hint_path(worktree).write_text(json.dumps(hint), encoding="utf-8")
        names = ", ".join(step.name for step in base_unjudged)
        say(f"the gate fails ({names}) and no gate has judged {base} on {names}, which the change was rebased onto: fix the change when the failing lines are its doing, otherwise tools/land.py --judge-base")
        return BASE_UNJUDGED

    names = ", ".join(step.name for step in base_passed)
    say(f"the gate fails here ({names}) and passes on {base}, which the change was rebased onto: the change is at fault")
    return CHANGE_FAILS


def change_branch(worktree, onto):
    """The branch a worktree's change is on, or None, said, when it is in no state to gate."""
    branch = subprocess.run(
        ["git", "-C", str(worktree), "symbolic-ref", "--short", "-q", "HEAD"], stdout=subprocess.PIPE, text=True
    ).stdout.strip()
    if not branch or branch == onto:
        say(f"not run: this worktree is on {branch or 'no branch'}, and a change lands from its own branch")
        return None
    if git(worktree, "status", "--porcelain"):
        say("not run: the worktree has uncommitted changes, which the gate would see and the landing would not take")
        return None
    return branch


def listed(worktree, commit, path):
    """The lines of a list at a commit, its comments left out, each as its fields; none when the
    commit holds no such list."""
    shown = subprocess.run(
        ["git", "-C", str(worktree), "show", f"{commit}:{path}"], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True
    )
    return [line.split("\t") for line in shown.stdout.splitlines() if line and not line.startswith("#")]


def unvouched(worktree, commit):
    """The items of the exemption list at a commit that nobody vouches for, as path:item:attribute."""
    return {f"{path}:{item}:{attribute}" for path, item, attribute, *_ in listed(worktree, commit, EXEMPTIONS)
            if attribute in UNVOUCHED}


def way_lines(worktree, commit, path):
    """The lines of a path, operation, way list at a commit, as path:operation:way. An exemption's
    clause is not part of the name. Empty when the commit holds no such list."""
    return {":".join(fields[:3]) for fields in listed(worktree, commit, path) if len(fields) >= 3}


def unwitnessed(worktree, commit):
    """The lines of the unwitnessed list at a commit, as path:operation:way."""
    return way_lines(worktree, commit, UNWITNESSED)


def unapproved(worktree, base, approved):
    """What the change adds that the human has not approved, each said: an unvouched item, new or
    turned from an assumed specification, and a line of the unwitnessed, unrefused or refused-exempt
    list. The approved ones are said too."""
    added = {item: f"an unvouched item {EXEMPTIONS}" for item in unvouched(worktree, "HEAD") - unvouched(worktree, base)}
    for path in (UNWITNESSED, UNREFUSED, REFUSED_EXEMPT):
        added.update((line, f"a line {path}") for line in way_lines(worktree, "HEAD", path) - way_lines(worktree, base, path))
    for item in sorted(added.keys() & approved):
        say(f"approved by the human: {item}")
    missing = sorted(added.keys() - approved)
    for item in missing:
        say(f"not approved: {item} is {added[item]} on {base} does not hold")
    if missing:
        say("adding one is a decision only the human can make: file the question, and land with --approve for each item once its answer is on it")
    return missing


def judge(worktree, onto, gate_command, explicit_steps=()):
    """Settles failed/unjudged steps on base without re-running unrelated passed steps."""
    root = worktree.parent
    branch = change_branch(worktree, onto)
    if branch is None:
        return NOT_RUN
    base = git(worktree, "merge-base", "HEAD", onto)
    gate_mod = load_gate_module(worktree)
    base_tree = tree(worktree, base)
    hint_path = judge_hint_path(worktree)
    hint = json.loads(hint_path.read_text(encoding="utf-8")) if hint_path.exists() else None
    if explicit_steps:
        target_names = list(explicit_steps)
    elif hint and hint.get("base") == base and hint.get("steps"):
        target_names = list(hint["steps"])
    else:
        step_verdicts, _, _ = load_ledger(root)
        base_hashes = gate_mod.input_hashes(worktree, base_tree, gate_mod.STEPS)
        unjudged = [s.name for s in gate_mod.STEPS
                    if s.inputs is not None and (s.name, base_hashes[s.name]) not in step_verdicts]
        target_names = unjudged or [s.name for s in gate_mod.STEPS if s.inputs is None]

    local_results = {}
    base_gate_mod = gate_mod
    target_steps = [s for s in gate_mod.STEPS if s.name in set(target_names)]
    base_hashes = gate_mod.input_hashes(worktree, base_tree, target_steps)
    # One loop judges a base step; others that failed on it wait here and read its verdict.
    with open(root / BASE_LOCK, "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        step_verdicts, _, _ = load_ledger(root)
        git(worktree, "checkout", "-q", "--detach", base)
        try:
            base_gate_mod = load_gate_module(worktree)
            base_by_name = {s.name: s for s in base_gate_mod.STEPS}
            target_steps = [base_by_name[name] for name in target_names if name in base_by_name]
            for name in target_names:
                if name not in base_by_name:
                    local_results[name] = "pass"
            base_hashes = base_gate_mod.input_hashes(worktree, base_tree, target_steps)
            need_run = [
                s for s in target_steps
                if s.inputs is None or (s.name, base_hashes[s.name]) not in step_verdicts
            ]
            already_failed = any(
                s.inputs is not None and step_verdicts.get((s.name, base_hashes[s.name]), ("", ""))[0] == "fail"
                for s in target_steps
            )
            if need_run and not already_failed:
                say(f"gating {base} by itself ({', '.join(s.name for s in need_run)}) into {base_log(base)}")
                with open(root / base_log(base), "a", encoding="utf-8") as output:
                    code, lines = run_gate_command(worktree, gate_command, need_run, output)
                parsed = parse_step_results(lines, need_run, code)
                for step in need_run:
                    verdict = parsed[step.name]
                    local_results[step.name] = "pass" if verdict == "skip" else verdict
                    if step.inputs is not None and verdict in ("pass", "fail"):
                        record_step(root, step.name, base_hashes[step.name], verdict, base)
        finally:
            git(worktree, "checkout", "-q", branch)

    if hint_path.exists():
        hint_path.unlink()
    step_verdicts, legacy_verdicts, passed_commits = load_ledger(root)
    return blame_steps(
        root, worktree, onto, base, target_steps, base_gate_mod, base_hashes,
        step_verdicts, legacy_verdicts, passed_commits, local_results=local_results,
    )


def land(worktree, onto, gate_command, approved=frozenset()):
    root = worktree.parent
    target = root / onto
    branch = change_branch(worktree, onto)
    if branch is None:
        return NOT_RUN

    if not tried(worktree, "rebase", onto):
        say(f"the rebase onto {onto} stopped on a conflict: resolve it, git rebase --continue, and land again")
        return CONFLICT
    base = git(worktree, "merge-base", "HEAD", onto)
    if unapproved(worktree, base, set(approved)):
        return UNAPPROVED
    commits = int(git(worktree, "rev-list", "--count", f"{base}..HEAD"))
    gated = git(worktree, "rev-parse", "HEAD")

    gate_mod = load_gate_module(worktree)
    steps = gate_mod.STEPS
    head_hashes = gate_mod.input_hashes(worktree, f"{gated}^{{tree}}", steps)
    base_hashes = gate_mod.input_hashes(worktree, f"{base}^{{tree}}", steps)
    step_verdicts, legacy_verdicts, passed_commits = load_ledger(root)
    selected = select_steps(steps, head_hashes, base_hashes, step_verdicts)
    skipped_count = len(steps) - len(selected)
    step_summary = ", ".join(s.name for s in selected)
    say(f"gating {gated} on {onto} at {base}: running {step_summary} (skipping {skipped_count} unchanged passed)")

    code, lines = run_gate_command(worktree, gate_command, selected, sys.stdout)
    step_results = parse_step_results(lines, selected, code)
    if code != 0:
        record_passed_steps(root, selected, step_results, head_hashes, base, only_matching=base_hashes)
        failed_steps = [s for s in selected if step_results.get(s.name) == "fail"] or list(selected)
        step_verdicts, legacy_verdicts, passed_commits = load_ledger(root)
        return blame_steps(
            root, worktree, onto, base, failed_steps, gate_mod, base_hashes,
            step_verdicts, legacy_verdicts, passed_commits,
        )
    record_passed_steps(root, selected, step_results, head_hashes, gated)

    hint_path = judge_hint_path(worktree)
    if hint_path.exists():
        hint_path.unlink()

    for _ in range(MERGE_TRIES):
        if not tried(worktree, "rebase", onto):
            say(f"{onto} moved since the first rebase and the change conflicts with it: resolve it, git rebase --continue, and land again")
            return CONFLICT
        if tried(target, "merge", "--ff-only", branch):
            break
        time.sleep(1)
    else:
        say(f"{onto} did not take the change in {MERGE_TRIES} tries")
        return NOT_LANDED
    landed = git(worktree, "rev-parse", "HEAD")
    for _ in range(PUSH_TRIES):
        if tried(target, "push", "origin", onto):
            break
        time.sleep(1)
    else:
        say(f"{landed} is merged into {onto} and the push to origin failed {PUSH_TRIES} times")
        return NOT_LANDED

    unseen = int(git(worktree, "rev-list", "--count", f"{base}..{landed}")) - commits
    if landed == gated:
        say(f"{landed} landed as gated")
    else:
        say(f"{landed} landed on {unseen} commit{'' if unseen == 1 else 's'} the gate did not see: the composition is gated with the next change on it")
    return LANDED


MOCK_GATE_SCRIPT = """#!/usr/bin/env python3
import argparse, json, os, subprocess, sys
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--step", action="append", default=[])
args, _ = parser.parse_known_args()

root = Path(os.environ["MOCK_GATE_ROOT"])
cfg_path = root / "mock_gate_config.json"
cfg = json.loads(cfg_path.read_text()) if cfg_path.exists() else {}

with open(root / "gates", "a") as f:
    f.write("run\\n")
with open(root / "gates.jsonl", "a") as f:
    f.write(json.dumps(args.step) + "\\n")

shell = cfg.get("shell")
shell_ok = True
if shell:
    shell_ok = subprocess.run(shell, shell=True, cwd=os.getcwd()).returncode == 0

steps_to_report = args.step or ["mock"]
fail_steps = set(cfg.get("fail_steps", []))
fail_if_exists = cfg.get("fail_if_exists", {})
skip_board = cfg.get("skip_board", False)
max_file_bytes = cfg.get("max_file_bytes")
check_spdx_missing = cfg.get("check_spdx", False)

failed = False
for step in steps_to_report:
    step_failed = False
    if step in fail_steps:
        step_failed = True
    if step in fail_if_exists and any(Path(p).exists() for p in fail_if_exists[step]):
        step_failed = True
    if step == cfg.get("shell_step") and not shell_ok:
        step_failed = True
    if cfg.get("shell_step") is None and not shell_ok:
        step_failed = True
    if step == "file sizes" and max_file_bytes is not None:
        for p in Path(".").rglob("*"):
            if ".git" in p.parts:
                continue
            if p.is_file() and p.lstat().st_size > max_file_bytes:
                step_failed = True
    if step == "source licenses" and check_spdx_missing:
        for p in Path(".").rglob("*"):
            if ".git" in p.parts or not p.is_file():
                continue
            data = p.read_bytes()
            if p.name.endswith((".rs", ".py", ".sh")) or data.startswith(b"#!"):
                if b"SPDX-License-Identifier: MIT" not in data.splitlines()[:2]:
                    step_failed = True
    if step == "aarch64 boot" and skip_board and not step_failed:
        print("skip: orangepi5 unreachable")
        print("gate aarch64 boot: ok in 0.0 s: tools/board.py --gate: skip: orangepi5 unreachable: this commit did not boot on aarch64")
        continue
    if step_failed:
        failed = True
        print(f"gate {step}: FAIL in 0.0 s: failed")
    else:
        print(f"gate {step}: ok in 0.0 s: ok")

sys.exit(1 if failed else 0)
"""


class Tests(unittest.TestCase):
    """Each test builds a project root: main, a task worktree beside it, an origin and logs/."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.main, self.task = self.root / "main", self.root / "task"
        (self.root / "logs").mkdir()
        self.mock_gate = self.root / "mock_gate.py"
        self.mock_gate.write_text(MOCK_GATE_SCRIPT)
        self.mock_gate.chmod(0o755)
        self.mock_config = self.root / "mock_gate_config.json"
        self.gate_mod = self._load_gate_mod()
        subprocess.run(["git", "init", "-q", "-b", "main", str(self.main)], check=True)
        self.git(self.main, "config", "user.name", "land test")
        self.git(self.main, "config", "user.email", "land@test.invalid")
        self.commit(self.main, "seed")
        subprocess.run(["git", "init", "-q", "--bare", str(self.root / "origin.git")], check=True)
        self.git(self.main, "remote", "add", "origin", str(self.root / "origin.git"))
        self.git(self.main, "push", "-q", "origin", "main")
        self.git(self.main, "worktree", "add", "-q", "../task", "-b", "task")

    def tearDown(self):
        self.directory.cleanup()

    def _load_gate_mod(self):
        spec = importlib.util.spec_from_file_location("test_gate_ref", Path(__file__).with_name("gate.py"))
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod

    def git(self, where, *args):
        return subprocess.run(
            ["git", "-C", str(where), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        ).stdout.strip()

    def commit(self, where, name, text="x"):
        (where / name).parent.mkdir(parents=True, exist_ok=True)
        (where / name).write_text(text)
        self.git(where, "add", name)
        self.git(where, "commit", "-q", "-m", f"add {name}")
        return self.git(where, "rev-parse", "HEAD")

    def land(self, *arguments, gate="true", **config):
        """Runs the tool in the task worktree against mock_gate.py. Records run steps in gates.jsonl."""
        cfg = dict(config)
        if gate and gate != "true":
            cfg["shell"] = gate
        self.mock_config.write_text(json.dumps(cfg))
        return subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--gate", f"{sys.executable} {self.mock_gate}", *arguments],
            cwd=self.task,
            env={**os.environ, "MOCK_GATE_ROOT": str(self.root)},
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )

    def gates(self):
        return len((self.root / "gates").read_text().splitlines()) if (self.root / "gates").exists() else 0

    def gate_runs(self):
        path = self.root / "gates.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def step_ledger(self):
        path = self.root / LEDGER
        if not path.exists():
            return []
        return [line.split("\t")[:4] for line in path.read_text().splitlines() if "\t" in line]

    def legacy_ledger(self):
        path = self.root / LEDGER
        if not path.exists():
            return []
        return [line.split()[:3] for line in path.read_text().splitlines() if "\t" not in line and line.strip()]

    def slice_hash(self, commit, step_name):
        step = next(s for s in self.gate_mod.STEPS if s.name == step_name)
        return self.gate_mod.input_hash(self.main, f"{commit}^{{tree}}", step)

    def tree(self, commit):
        return self.git(self.main, "rev-parse", f"{commit}^{{tree}}")

    def origin(self):
        return self.git(self.root / "origin.git", "rev-parse", "main")

    def test_unread_is_deleted_from_land_py(self):
        impl = Path(__file__).read_text(encoding="utf-8").split("MOCK_GATE_SCRIPT", 1)[0]
        for removed in ("UNREAD", "needs_no_gate", "held_everywhere", "MAX_FILE_BYTES", "check_spdx"):
            self.assertNotIn(removed, impl)

    def test_a_change_whose_gate_passes_lands_as_gated_and_is_pushed(self):
        change = self.commit(self.task, "kernel/src/a.rs")
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)
        self.assertEqual(self.origin(), change)
        self.assertTrue((self.main / "kernel/src/a.rs").exists())
        entries = self.step_ledger()
        bounded_names = {s.name for s in self.gate_mod.STEPS if s.inputs is not None}
        self.assertEqual({row[0] for row in entries}, bounded_names)
        for step_name, slice_h, verdict, commit in entries:
            self.assertEqual(verdict, "pass")
            self.assertEqual(commit, change)
            self.assertEqual(slice_h, self.slice_hash(change, step_name))
        self.assertIn(f"land: {change} landed as gated", result.stdout)

    def test_a_main_that_moved_under_the_gate_takes_the_change_without_a_second_gate(self):
        self.commit(self.task, "kernel/src/a.rs")
        other = "[ -e ../moved ] || { touch ../moved; mkdir -p ../main/kernel/src; echo y > ../main/kernel/src/b.rs; git -C ../main add kernel/src/b.rs; git -C ../main commit -q -m b; }"
        result = self.land(gate=other)
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.gates(), 1)
        self.assertTrue((self.main / "kernel/src/a.rs").exists() and (self.main / "kernel/src/b.rs").exists())
        landed = self.git(self.main, "rev-parse", "main")
        self.assertEqual(self.origin(), landed)
        self.assertIn(f"land: {landed} landed on 1 commit the gate did not see", result.stdout)
        # The ledger holds the slice the gate saw, not the composition's slice for boot.
        boot_hashes = [row[1] for row in self.step_ledger() if row[0] == "boot"]
        self.assertNotIn(self.slice_hash(landed, "boot"), boot_hashes)

    def test_a_merge_that_finds_main_s_index_taken_is_tried_again(self):
        change = self.commit(self.task, "kernel/src/a.rs")
        lock = Path(self.git(self.main, "rev-parse", "--path-format=absolute", "--git-path", "index.lock"))
        lock.write_text("")
        timer = threading.Timer(1.5, lock.unlink)
        timer.start()
        self.addCleanup(timer.cancel)
        result = self.land()
        timer.join()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.origin(), change)

    def test_a_rebase_that_conflicts_stops_before_the_gate(self):
        before = self.commit(self.main, "f", "main's")
        self.commit(self.task, "f", "the change's")
        result = self.land()
        self.assertEqual(result.returncode, CONFLICT, result.stdout)
        self.assertFalse((self.root / "gates").exists())
        self.assertEqual(self.git(self.main, "rev-parse", "main"), before)

    def test_a_conflict_with_what_landed_during_the_gate_lands_nothing(self):
        self.commit(self.task, "f", "the change's")
        other = "echo theirs > ../main/f; git -C ../main add f; git -C ../main commit -q -m f"
        result = self.land(gate=other)
        self.assertEqual(result.returncode, CONFLICT, result.stdout)
        self.assertEqual((self.main / "f").read_text(), "theirs\n")
        self.assertEqual(self.gates(), 1)

    def test_a_failing_gate_on_a_base_that_passed_blames_the_change_without_gating_the_base(self):
        self.commit(self.task, "kernel/src/a.rs")
        self.assertEqual(self.land().returncode, LANDED)
        base = self.git(self.main, "rev-parse", "main")
        self.commit(self.task, "kernel/src/bad.rs")
        result = self.land(fail_if_exists={"boot": ["kernel/src/bad.rs"]})
        self.assertEqual(result.returncode, CHANGE_FAILS, result.stdout)
        self.assertEqual(self.gates(), 2)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), base)
        self.assertIn("the change is at fault", result.stdout)

    def test_a_failing_gate_on_an_unjudged_base_says_so_and_leaves_the_base_ungated(self):
        base = self.commit(self.main, "kernel/src/b.rs")
        self.commit(self.task, "kernel/src/bad.rs")
        result = self.land(fail_if_exists={"boot": ["kernel/src/bad.rs"]})
        self.assertEqual(result.returncode, BASE_UNJUDGED, result.stdout)
        self.assertEqual(self.gates(), 1)
        boot_entries = [row for row in self.step_ledger() if row[0] == "boot"]
        self.assertEqual(boot_entries, [])
        self.assertIn(f"no gate has judged {base}", result.stdout)
        self.assertIn("--judge-base", result.stdout)

    def test_judging_a_base_that_passes_blames_the_change_and_records_the_base(self):
        base = self.commit(self.main, "kernel/src/b.rs")
        change = self.commit(self.task, "kernel/src/bad.rs")
        self.assertEqual(self.land(fail_if_exists={"boot": ["kernel/src/bad.rs"]}).returncode, BASE_UNJUDGED)
        result = self.land("--judge-base", fail_if_exists={"boot": ["kernel/src/bad.rs"]})
        self.assertEqual(result.returncode, CHANGE_FAILS, result.stdout)
        self.assertEqual(self.gates(), 2)
        # Only the unjudged failing step ("boot") was run on base, not unrelated steps like "verify".
        self.assertEqual(self.gate_runs()[-1], ["boot"])
        self.assertIn(["boot", self.slice_hash(base, "boot"), "pass", base], self.step_ledger())
        self.assertTrue((self.root / "logs" / f"base-{base[:12]}-gate.log").exists())
        # The worktree is back on the change, rebased onto the base.
        self.assertEqual(self.git(self.task, "symbolic-ref", "--short", "HEAD"), "task")
        self.assertEqual(self.git(self.task, "rev-parse", "HEAD~1"), base)
        self.assertNotEqual(self.git(self.task, "rev-parse", "HEAD"), change)
        self.assertEqual(self.git(self.task, "status", "--porcelain"), "")

    def test_claude_agents_edit_runs_only_file_sizes_and_source_licenses(self):
        self.commit(self.task, "kernel/src/seed.rs")
        self.assertEqual(self.land().returncode, LANDED)
        change = self.commit(self.task, ".claude/agents/round.md", "updated\n")
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.gate_runs()[-1], ["file sizes", "source licenses"])
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)
        self.assertIn(f"land: {change} landed as gated", result.stdout)

    def test_kernel_src_glue_edit_skips_verify_and_verify_aarch64_when_base_passed(self):
        self.commit(self.task, "kernel/src/seed.rs")
        self.assertEqual(self.land().returncode, LANDED)
        change = self.commit(self.task, "kernel/src/main.rs", "fn main() {}\n")
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        ran = self.gate_runs()[-1]
        self.assertNotIn("verify", ran)
        self.assertNotIn("verify aarch64", ran)
        self.assertNotIn("throwaways", ran)
        self.assertNotIn("faq", ran)
        self.assertIn("file sizes", ran)
        self.assertIn("source licenses", ran)
        self.assertIn("build", ran)
        self.assertIn("boot", ran)
        self.assertIn("aarch64 boot", ran)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def test_ungated_composed_base_where_two_commits_modified_same_step_reruns_that_step(self):
        # Seed base where every step passed.
        self.commit(self.task, "kernel/src/seed.rs")
        self.assertEqual(self.land().returncode, LANDED)
        # Landing 1 touches kernel/src/a1.rs (boot+build, not verify) while main concurrently receives
        # kernel/src/a2.rs (also boot+build, not verify), producing an ungated composed tip on main.
        self.commit(self.task, "kernel/src/a1.rs", "fn a1() {}\n")
        other = (
            "[ -e ../moved ] || { touch ../moved; mkdir -p ../main/kernel/src; "
            "echo 'fn a2() {}' > ../main/kernel/src/a2.rs; "
            "git -C ../main add kernel/src/a2.rs; git -C ../main commit -q -m a2; }"
        )
        self.assertEqual(self.land(gate=other).returncode, LANDED)
        # An unrelated doc edit over the ungated composed tip must re-run boot/build while skipping verify.
        self.commit(self.task, ".claude/agents/round.md", "doc edit\n")
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        landed = self.git(self.main, "rev-parse", "main")
        ran = self.gate_runs()[-1]
        self.assertIn("boot", ran)
        self.assertIn("build", ran)
        self.assertNotIn("verify", ran)
        self.assertNotIn("verify aarch64", ran)
        self.assertIn(["boot", self.slice_hash(landed, "boot"), "pass", landed], self.step_ledger())

    def test_skip_orangepi5_unreachable_does_not_write_pass_for_aarch64_boot(self):
        self.commit(self.task, "kernel/src/seed.rs")
        self.assertEqual(self.land(skip_board=True).returncode, LANDED)
        entries = self.step_ledger()
        self.assertIn("build", {row[0] for row in entries})
        self.assertNotIn("aarch64 boot", {row[0] for row in entries})
        # Next edit touching only .claude/agents/ skips build/verify, but MUST re-run aarch64 boot.
        self.commit(self.task, ".claude/agents/round.md", "note\n")
        result = self.land(skip_board=True)
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.gate_runs()[-1], ["file sizes", "source licenses", "aarch64 boot"])
        self.assertNotIn("aarch64 boot", {row[0] for row in self.step_ledger()})
        # Once the board returns and boots cleanly, aarch64 boot writes pass and subsequent doc edits skip it.
        c3 = self.commit(self.task, ".claude/agents/round.md", "note2\n")
        self.assertEqual(self.land(skip_board=False).returncode, LANDED)
        self.assertIn(["aarch64 boot", self.slice_hash(c3, "aarch64 boot"), "pass", c3], self.step_ledger())
        self.commit(self.task, ".claude/agents/round.md", "note3\n")
        self.assertEqual(self.land(skip_board=False).returncode, LANDED)
        self.assertEqual(self.gate_runs()[-1], ["file sizes", "source licenses"])

    def test_per_step_judge_base_and_suspects_blame(self):
        self.commit(self.task, "kernel/src/a.rs")
        self.assertEqual(self.land().returncode, LANDED)
        gated = self.git(self.main, "rev-parse", "main")
        # Two changes that each pass and fail together: kernel/src/b.rs lands on main ungated,
        # followed by an unrelated .claude/agents/ doc edit on main.
        suspect = self.commit(self.main, "kernel/src/b.rs")
        doc_commit = self.commit(self.main, ".claude/agents/note.md", "doc\n")
        self.commit(self.task, "kernel/src/c.rs")
        shell_rule = "! { [ -e kernel/src/a.rs ] && [ -e kernel/src/b.rs ]; }"
        first = self.land(gate=shell_rule, shell_step="boot")
        self.assertEqual(first.returncode, BASE_UNJUDGED, first.stdout)
        runs_before = len(self.gate_runs())
        result = self.land("--judge-base", gate=shell_rule, shell_step="boot")
        self.assertEqual(result.returncode, BASE_FAILS, result.stdout)
        # --judge-base runs ONLY the failing/unjudged step ("boot"), not unrelated steps like verify.
        self.assertEqual(self.gate_runs()[runs_before], ["boot"])
        self.assertIn(["boot", self.slice_hash(doc_commit, "boot"), "fail", doc_commit], self.step_ledger())
        self.assertIn(f"logs/base-{doc_commit[:12]}-gate.log", result.stdout)
        self.assertIn(f"land: suspect {suspect}", result.stdout)
        self.assertNotIn(f"land: suspect {doc_commit}", result.stdout)
        self.assertNotIn(f"land: suspect {gated}", result.stdout)
        # Next landing over that broken base reuses the cached fail verdict for boot and names suspect.
        again = self.land(gate=shell_rule, shell_step="boot")
        self.assertEqual(again.returncode, BASE_FAILS, again.stdout)
        self.assertIn(f"land: suspect {suspect}", again.stdout)

    def test_partial_head_pass_on_unjudged_base_skips_unrelated_steps_in_judge_base(self):
        # Unjudged base where neither verify nor boot has a ledger pass yet.
        base = self.commit(self.main, "kernel/verified/v.rs", "fn v() {}\n")
        self.commit(self.task, "kernel/src/bad.rs")
        # verify passes on HEAD while boot fails; landing exits BASE_UNJUDGED and saves only boot.
        first = self.land(fail_if_exists={"boot": ["kernel/src/bad.rs"]})
        self.assertEqual(first.returncode, BASE_UNJUDGED, first.stdout)
        self.assertIn(["verify", self.slice_hash(base, "verify"), "pass", base], self.step_ledger())
        runs_before = len(self.gate_runs())
        second = self.land("--judge-base", fail_if_exists={"boot": ["kernel/src/bad.rs"]})
        self.assertEqual(second.returncode, CHANGE_FAILS, second.stdout)
        # --judge-base only executes "boot", never re-running "verify".
        self.assertEqual(self.gate_runs()[runs_before], ["boot"])

    def test_different_failing_steps_on_same_unjudged_base_judge_independently(self):
        base = self.commit(self.main, "kernel/src/b.rs")
        self.commit(self.task, "kernel/src/bad.rs")
        # First failure on boot -> --judge-base judges boot as passing on base.
        self.assertEqual(self.land(fail_if_exists={"boot": ["kernel/src/bad.rs"]}).returncode, BASE_UNJUDGED)
        self.assertEqual(self.land("--judge-base", fail_if_exists={"boot": ["kernel/src/bad.rs"]}).returncode, CHANGE_FAILS)
        # A second distinct step ("build") failing on base still triggers --judge-base for build alone.
        self.assertEqual(self.land(fail_steps=["build"]).returncode, BASE_UNJUDGED)
        runs_before = len(self.gate_runs())
        res = self.land("--judge-base", fail_steps=["build"])
        self.assertEqual(res.returncode, BASE_FAILS, res.stdout)
        self.assertEqual(self.gate_runs()[runs_before], ["build"])
        self.assertIn(["build", self.slice_hash(base, "build"), "fail", base], self.step_ledger())

    def test_legacy_whole_tree_ledger_lines_are_handled_cleanly(self):
        c0 = self.commit(self.main, "kernel/src/seed.rs")
        c1 = self.commit(self.main, "kernel/src/b.rs")
        # Write legacy whole-tree entries: c0 passed, an older tree failed.
        (self.root / LEDGER).write_text(
            f"{self.tree(c0)} pass {c0} 1700000000\n"
            f"0000000000000000000000000000000000000000 fail {c0} 1700000001\n"
        )
        # Suspects stops cleanly at legacy whole-tree pass c0 when boot fails on c1.
        self.commit(self.task, ".claude/agents/round.md", "doc\n")
        fail_rule = "! [ -e kernel/src/b.rs ]"
        self.assertEqual(self.land(gate=fail_rule, shell_step="boot").returncode, BASE_UNJUDGED)
        judged = self.land("--judge-base", gate=fail_rule, shell_step="boot")
        self.assertEqual(judged.returncode, BASE_FAILS, judged.stdout)
        self.assertIn(f"land: suspect {c1}", judged.stdout)
        self.assertNotIn(f"land: suspect {c0}", judged.stdout)
        self.assertNotIn("suspects go further back", judged.stdout)
        # Remove the failing boot verdict line and re-test clean landing writing per-step entries.
        (self.root / LEDGER).write_text(
            f"{self.tree(c0)} pass {c0} 1700000000\n"
            f"0000000000000000000000000000000000000000 fail {c0} 1700000001\n"
        )
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        landed = self.git(self.main, "rev-parse", "main")
        self.assertIn("boot", self.gate_runs()[-1])
        self.assertEqual(len(self.legacy_ledger()), 2)
        self.assertIn(["boot", self.slice_hash(landed, "boot"), "pass", landed], self.step_ledger())

    def test_a_file_over_the_gate_s_size_limit_is_gated_whatever_its_path(self):
        self.commit(self.task, "kernel/src/seed.rs")
        self.assertEqual(self.land().returncode, LANDED)
        self.commit(self.task, "CLAUDE.md", "x" * 1025)
        result = self.land(max_file_bytes=1024)
        self.assertNotEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.gate_runs()[-1], ["file sizes", "source licenses"])

    def test_a_source_that_does_not_state_an_allowed_license_is_gated_whatever_its_path(self):
        self.commit(self.task, "kernel/src/seed.rs")
        self.assertEqual(self.land().returncode, LANDED)
        for name, text in ((".claude/skills/round/run.sh", "echo\n"), (".claude/agents/run", "#!/bin/sh\necho\n"),
                           ("tools/loop.py", "# SPDX-License-Identifier: GPL-2.0-only\n")):
            with self.subTest(name=name):
                self.git(self.task, "reset", "-q", "--hard", "main")
                self.commit(self.task, name, text)
                result = self.land(check_spdx=True)
                self.assertNotEqual(result.returncode, LANDED, result.stdout)
                self.assertEqual(self.gate_runs()[-1], ["file sizes", "source licenses"])

    LISTED = {
        "hardware": "k/arch/a.rs\tleaf\tassume_specification\thardware\tmanual 3 PAUSE",
        "unproven": "k/q.rs\tacquire\texec_allows_no_decreases_clause\tunproven\tthe spin is not proven to end",
    }

    def listing(self, where, *lines):
        """Commits an exemption list holding a header and these lines."""
        return self.commit(where, EXEMPTIONS, "".join(f"{line}\n" for line in ("# header", *lines)))

    def test_a_branch_that_adds_an_external_body_or_a_wait_is_refused_until_the_flag_names_it(self):
        # Every external_body and exec_allows_no_decreases_clause is debt, whatever class its line states.
        self.listing(self.main, self.LISTED["hardware"])
        for kind, line, item in (
            ("gap", "u/g.rs\tstep\texternal_body\tgap\tnothing proves the premise", "u/g.rs:step:external_body"),
            ("unproven", self.LISTED["unproven"], "k/q.rs:acquire:exec_allows_no_decreases_clause"),
            ("any other class", "k/arch/a.rs\twrite_cr3\texternal_body\tglue\twrites CR3",
             "k/arch/a.rs:write_cr3:external_body"),
        ):
            with self.subTest(kind=kind):
                self.git(self.task, "reset", "-q", "--hard", "main")
                change = self.listing(self.task, self.LISTED["hardware"], line)
                before = self.gates() if (self.root / "gates").exists() else 0
                result = self.land()
                self.assertEqual(result.returncode, UNAPPROVED, result.stdout)
                self.assertIn(f"land: not approved: {item}", result.stdout)
                self.assertEqual(self.gates() if (self.root / "gates").exists() else 0, before)
                self.assertNotEqual(self.git(self.main, "rev-parse", "main"), change)
                result = self.land("--approve", item)
                self.assertEqual(result.returncode, LANDED, result.stdout)
                self.assertIn(f"land: approved by the human: {item}", result.stdout)
                self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def test_a_branch_that_turns_a_hardware_item_into_an_external_body_is_refused(self):
        self.listing(self.main, self.LISTED["hardware"])
        self.git(self.task, "reset", "-q", "--hard", "main")
        self.listing(self.task, "k/arch/a.rs\tleaf\texternal_body\tgap\tnothing proves it")
        result = self.land()
        self.assertEqual(result.returncode, UNAPPROVED, result.stdout)
        self.assertIn("land: not approved: k/arch/a.rs:leaf:external_body", result.stdout)
        # Approving another item does not approve this one.
        result = self.land("--approve", "k/arch/a.rs:leaf:exec_allows_no_decreases_clause")
        self.assertEqual(result.returncode, UNAPPROVED, result.stdout)

    def test_a_branch_that_removes_rewords_or_adds_vouched_items_lands_with_no_flag(self):
        gap = "u/g.rs\tstep\texternal_body\tgap\tnothing proves the premise"
        self.listing(self.main, self.LISTED["hardware"], self.LISTED["unproven"], gap)
        changes = (
            ("reclasses a gap item to unproven", (self.LISTED["hardware"], self.LISTED["unproven"],
                                                  gap.replace("\tgap\t", "\tunproven\t"))),
            ("removes that item", (self.LISTED["hardware"], self.LISTED["unproven"])),
            ("rewords a reason", (self.LISTED["hardware"], self.LISTED["unproven"].replace("not proven", "not yet proven"))),
            ("adds hardware, kernel and language items", (
                self.LISTED["hardware"], self.LISTED["unproven"],
                "k/arch/x.rs\tpause\tassume_specification\thardware\tmanual 3 PAUSE",
                "u/c.rs\tcall\tassume_specification\tkernel\tkernel/s.rs dispatch",
                "u/m.rs\tread\tassume_specification\tlanguage\tcore/src/ptr/mod.rs \"a read\"",
            )),
        )
        for name, lines in changes:
            with self.subTest(name=name):
                self.git(self.task, "reset", "-q", "--hard", "main")
                change = self.listing(self.task, *lines)
                result = self.land()
                self.assertEqual(result.returncode, LANDED, result.stdout)
                self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def unwitnessed(self, where, *units):
        """Commits an unwitnessed list holding a header and these units, each path, operation, way."""
        return self.commit(where, UNWITNESSED, "".join(f"{line}\n" for line in ("# header", *("\t".join(unit) for unit in units))))

    SLICE, UNMAP, START = ("k/retype.rs", "retype", "Slice"), ("k/unmap.rs", "unmap_at", "Some"), ("k/thread.rs", "start", "true")

    def test_a_branch_that_adds_a_line_to_the_unwitnessed_list_is_refused_until_the_flag_names_it(self):
        self.unwitnessed(self.main, self.SLICE)
        self.git(self.task, "reset", "-q", "--hard", "main")
        change = self.unwitnessed(self.task, self.SLICE, self.UNMAP, self.START)
        result = self.land()
        self.assertEqual(result.returncode, UNAPPROVED, result.stdout)
        self.assertIn("land: not approved: k/unmap.rs:unmap_at:Some is a line tools/unwitnessed on", result.stdout)
        self.assertIn("land: not approved: k/thread.rs:start:true is a line tools/unwitnessed on", result.stdout)
        self.assertNotIn("k/retype.rs:retype:Slice", result.stdout)
        self.assertFalse((self.root / "gates").exists())
        # Approving one of two lines does not approve the other.
        result = self.land("--approve", "k/unmap.rs:unmap_at:Some")
        self.assertEqual(result.returncode, UNAPPROVED, result.stdout)
        self.assertIn("land: approved by the human: k/unmap.rs:unmap_at:Some", result.stdout)
        self.assertNotEqual(self.git(self.main, "rev-parse", "main"), change)
        result = self.land("--approve", "k/unmap.rs:unmap_at:Some", "--approve", "k/thread.rs:start:true")
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def test_a_branch_that_removes_or_reorders_lines_of_the_unwitnessed_list_lands_with_no_flag(self):
        self.unwitnessed(self.main, self.SLICE, self.UNMAP, self.START)
        for name, units in (("reorders", (self.START, self.SLICE, self.UNMAP)), ("removes one", (self.START, self.UNMAP)),
                            ("removes every line", ())):
            with self.subTest(name=name):
                self.git(self.task, "reset", "-q", "--hard", "main")
                change = self.unwitnessed(self.task, *units)
                result = self.land()
                self.assertEqual(result.returncode, LANDED, result.stdout)
                self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def test_a_branch_that_changes_a_line_s_way_adds_a_line(self):
        self.unwitnessed(self.main, self.SLICE)
        self.git(self.task, "reset", "-q", "--hard", "main")
        self.unwitnessed(self.task, ("k/retype.rs", "retype", "Unlinked"))
        result = self.land()
        self.assertEqual(result.returncode, UNAPPROVED, result.stdout)
        self.assertIn("land: not approved: k/retype.rs:retype:Unlinked", result.stdout)

    def test_a_list_on_a_base_that_has_none_is_every_line_added(self):
        change = self.unwitnessed(self.task, self.SLICE)
        self.assertEqual(self.land().returncode, UNAPPROVED)
        result = self.land("--approve", "k/retype.rs:retype:Slice")
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def listed_ways(self, where, path, *units):
        """Commits a path/operation/way list, an exemption's units carrying the clause as a fourth field."""
        return self.commit(where, path, "".join(f"{line}\n" for line in ("# header", *("\t".join(unit) for unit in units))))

    def test_a_branch_that_adds_a_line_to_the_unrefused_list_is_refused_until_the_flag_names_it(self):
        self.listed_ways(self.main, UNREFUSED, self.SLICE)
        self.git(self.task, "reset", "-q", "--hard", "main")
        change = self.listed_ways(self.task, UNREFUSED, self.SLICE, self.UNMAP)
        result = self.land()
        self.assertEqual(result.returncode, UNAPPROVED, result.stdout)
        self.assertIn("land: not approved: k/unmap.rs:unmap_at:Some is a line tools/unrefused on", result.stdout)
        self.assertNotIn("k/retype.rs:retype:Slice", result.stdout)
        self.assertFalse((self.root / "gates").exists())
        result = self.land("--approve", "k/unmap.rs:unmap_at:Some")
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertIn("land: approved by the human: k/unmap.rs:unmap_at:Some", result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def test_a_branch_that_removes_a_line_of_the_unrefused_list_lands_with_no_flag(self):
        self.listed_ways(self.main, UNREFUSED, self.SLICE, self.UNMAP)
        self.git(self.task, "reset", "-q", "--hard", "main")
        change = self.listed_ways(self.task, UNREFUSED, self.UNMAP)
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def test_a_branch_that_adds_an_exemption_is_refused_until_the_flag_names_it(self):
        kept = ("k/reclaim.rs", "reclaim", "Again", "ret is Again ==> post == pre")
        added = ("k/reclaim.rs", "reclaim_frame", "Again", "!(ret is Freed) ==> post == pre")
        self.listed_ways(self.main, REFUSED_EXEMPT, kept)
        self.git(self.task, "reset", "-q", "--hard", "main")
        # Rewording the clause is not a new line.
        reworded = ("k/reclaim.rs", "reclaim", "Again", "ret is Again ==> *final(self) == *old(self)")
        change = self.listed_ways(self.task, REFUSED_EXEMPT, reworded)
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)
        self.git(self.task, "reset", "-q", "--hard", "main")
        change = self.listed_ways(self.task, REFUSED_EXEMPT, kept, added)
        result = self.land()
        self.assertEqual(result.returncode, UNAPPROVED, result.stdout)
        self.assertIn("land: not approved: k/reclaim.rs:reclaim_frame:Again is a line tools/refused-exempt on", result.stdout)
        self.assertNotIn("reclaim:Again", result.stdout)
        result = self.land("--approve", "k/reclaim.rs:reclaim_frame:Again")
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)

    def test_a_worktree_with_uncommitted_changes_is_not_run(self):
        self.commit(self.task, "a")
        (self.task / "stray").write_text("x")
        result = self.land()
        self.assertEqual(result.returncode, NOT_RUN, result.stdout)
        self.assertFalse((self.root / "gates").exists())

    def test_the_base_s_own_branch_is_not_run(self):
        result = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--gate", "true"], cwd=self.main, stdout=subprocess.PIPE, text=True
        )
        self.assertEqual(result.returncode, NOT_RUN, result.stdout)


def main():
    parser = argparse.ArgumentParser(
        usage="tools/land.py [--onto BRANCH] [--gate COMMAND] [--approve PATH:ITEM:ATTRIBUTE | PATH:OPERATION:WAY]... | "
              "--judge-base [--onto BRANCH] [--gate COMMAND] [--step NAME]... | --test")
    parser.add_argument("--onto", default="main", help="the branch landed on, whose worktree is its sibling (default main)")
    parser.add_argument("--gate", default=GATE, help=f"the gate, a shell command run in the worktree (default {GATE!r})")
    parser.add_argument("--judge-base", action="store_true", help="gate the base the change stands on instead of the change")
    parser.add_argument("--step", action="append", default=[], metavar="NAME", help="with --judge-base, judge only these steps")
    parser.add_argument(
        "--approve", action="append", default=[], metavar="PATH:ITEM:ATTRIBUTE",
        help=f"an external_body or exec_allows_no_decreases_clause item of {EXEMPTIONS}, or a line of {UNWITNESSED}, "
             f"{UNREFUSED} or {REFUSED_EXEMPT} as PATH:OPERATION:WAY, that the change adds and the human approved; once per item",
    )
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        return 0 if unittest.main(argv=[sys.argv[0]], exit=False).result.wasSuccessful() else 1
    worktree = subprocess.run(["git", "rev-parse", "--show-toplevel"], stdout=subprocess.PIPE, text=True)
    if worktree.returncode != 0:
        return NOT_RUN
    if args.judge_base:
        return judge(Path(worktree.stdout.strip()), args.onto, args.gate, args.step)
    return land(Path(worktree.stdout.strip()), args.onto, args.gate, frozenset(args.approve))


if __name__ == "__main__":
    sys.exit(main())
