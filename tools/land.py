#!/usr/bin/env python3
"""Gate the change in this worktree and land it on main, with no lock around either.

Run from a task worktree whose change is committed, with tools/env.sh sourced. The branch is rebased
onto main and the gate runs on that. When it passes the branch is rebased again, since main may
have moved while the gate ran, merged into main as a fast-forward and pushed. git refuses a
fast-forward that main moved under and a merge while main's index is taken, so both are tried again
from the rebase. A rebase that is clean lands without a second gate: what landed beside it is gated
with whatever change is gated on top of it next (design/land-without-regating/).

A change that touches only what no gate step reads, UNREAD below, lands without a gate: the gate
would say of it what it says of the base (design/no-gate-for-what-no-step-reads/). Its tree joins
the ledger with the base's verdict when the base has one.

When the gate fails, the question is whether the change fails or the main it was rebased onto does.
The ledger, logs/gate-ledger at the project root, holds a line for every tree a gate has judged:
tree, pass or fail, the commit, the time. A base whose tree passed is sound, so the change is at
fault. A base with no line is unjudged, and the tool says so and stops: most failures are plainly
the change's, and a gate of the base would be spent to learn nothing. When the failure is not
plainly the change's, --judge-base gates the base by itself, detached in this worktree, its output
in logs/base-<commit>-gate.log, and its verdict joins the ledger, where the other loops' landings
find it instead of gating the same base again. A base that fails is printed with its suspects: the
commits since the last one on main whose tree passed.

Exit status:
  0  landed and pushed
  1  the gate fails and the base passes: the change is at fault
  2  not run: no branch, the base's own branch, or uncommitted changes
  3  the rebase stopped on a conflict; resolve it, continue the rebase and land again
  4  the base fails the gate by itself; main is broken and the change is not judged
  5  the change is cleared to land and did not reach origin: the merge or the push kept failing
  6  the gate fails and no gate has judged the base: fix the change, or settle it with --judge-base

usage: tools/land.py [--onto BRANCH] [--gate COMMAND]
       tools/land.py --judge-base [--onto BRANCH] [--gate COMMAND]    (exits 1 or 4)
       tools/land.py --test    (this script's own tests)
"""
import argparse
import fcntl
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

LANDED, CHANGE_FAILS, NOT_RUN, CONFLICT, BASE_FAILS, NOT_LANDED, BASE_UNJUDGED = range(7)
LEDGER = "logs/gate-ledger"
BASE_LOCK = "logs/gate-base.lock"
GATE = "tools/gate.py"
# How often the rebase and the fast-forward are tried while other landings move main.
MERGE_TRIES = 30
PUSH_TRIES = 3
# How far back a broken base's suspects are listed when no tree before them passed.
SUSPECT_LIMIT = 50
# What no gate step reads, so a change to these alone cannot move the gate's result: a file, or with
# a closing slash everything under a directory (design/no-gate-for-what-no-step-reads/).
UNREAD = (".claude/agents/", ".claude/skills/", "CLAUDE.md")
# The gate's limit on a file's size, the one thing it holds every path to.
MAX_FILE_BYTES = 1 << 20


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


def gate_passes(worktree, gate_command, output):
    return subprocess.run(gate_command, shell=True, cwd=worktree, stdout=output, stderr=subprocess.STDOUT).returncode == 0


def record(root, tree_id, verdict, commit):
    """One line, written at once, so loops that land side by side do not tear each other's."""
    with open(root / LEDGER, "a") as ledger:
        ledger.write(f"{tree_id} {verdict} {commit} {int(time.time())}\n")


def verdicts(root):
    """Each judged tree's last verdict and the commit it was judged as."""
    ledger = root / LEDGER
    lines = ledger.read_text().splitlines() if ledger.exists() else []
    return {tree_id: (verdict, commit) for tree_id, verdict, commit, _ in map(str.split, lines)}


def base_log(commit):
    return f"logs/base-{commit[:12]}-gate.log"


def judge_base(root, worktree, branch, base, gate_command):
    """The base's verdict and the commit it was judged as, gating it here when no gate has judged its tree."""
    base_tree = tree(worktree, base)
    # One loop gates a base; the others that failed on it wait here and read its verdict.
    with open(root / BASE_LOCK, "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        known = verdicts(root).get(base_tree)
        if known is not None:
            return known
        say(f"gating {base} by itself into {base_log(base)}")
        git(worktree, "checkout", "-q", "--detach", base)
        try:
            with open(root / base_log(base), "w") as output:
                verdict = "pass" if gate_passes(worktree, gate_command, output) else "fail"
        finally:
            git(worktree, "checkout", "-q", branch)
        record(root, base_tree, verdict, base)
        return verdict, base


def suspects(root, worktree, base):
    """The commits a broken base may owe its failure to: back to the last whose tree passed."""
    judged = verdicts(root)
    found = []
    history = git(worktree, "log", "--first-parent", f"--max-count={SUSPECT_LIMIT}", "--format=%H %T %s", base)
    for line in history.splitlines():
        commit, tree_id, subject = line.split(" ", 2)
        if judged.get(tree_id, ("", ""))[0] == "pass":
            return found, True
        found.append((commit, subject))
    return found, False


def blame(root, worktree, onto, base, verdict, judged_as):
    """Says whose failure a failed gate is, from the base's verdict; the exit status that names it."""
    if verdict == "pass":
        say(f"the gate fails here and passes on {base}, which the change was rebased onto: the change is at fault")
        return CHANGE_FAILS
    say(f"{onto} at {base} fails the gate by itself ({base_log(judged_as)}): {onto} is broken and the change is not judged")
    found, bounded = suspects(root, worktree, base)
    for commit, subject in found:
        say(f"suspect {commit} {subject}")
    if not bounded:
        say(f"no tree among the last {SUSPECT_LIMIT} commits passed a gate: the suspects go further back")
    return BASE_FAILS


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


def unread(path):
    return any(path == entry or (entry.endswith("/") and path.startswith(entry)) for entry in UNREAD)


def needs_no_gate(worktree, base):
    """Whether the change since the base touches only what no gate step reads, each file within the size limit."""
    changed = git(worktree, "diff", "--name-only", "--no-renames", base, "HEAD").splitlines()
    kept = [worktree / path for path in changed if (worktree / path).is_symlink() or (worktree / path).exists()]
    return bool(changed) and all(map(unread, changed)) and all(path.lstat().st_size <= MAX_FILE_BYTES for path in kept)


def judge(worktree, onto, gate_command):
    """Settles a failed gate on an unjudged base: gates the base the change stands on and says whose failure it is."""
    root = worktree.parent
    branch = change_branch(worktree, onto)
    if branch is None:
        return NOT_RUN
    base = git(worktree, "merge-base", "HEAD", onto)
    return blame(root, worktree, onto, base, *judge_base(root, worktree, branch, base, gate_command))


def land(worktree, onto, gate_command):
    root = worktree.parent
    target = root / onto
    branch = change_branch(worktree, onto)
    if branch is None:
        return NOT_RUN

    if not tried(worktree, "rebase", onto):
        say(f"the rebase onto {onto} stopped on a conflict: resolve it, git rebase --continue, and land again")
        return CONFLICT
    base = git(worktree, "merge-base", "HEAD", onto)
    commits = int(git(worktree, "rev-list", "--count", f"{base}..HEAD"))
    gated = git(worktree, "rev-parse", "HEAD")
    known = verdicts(root).get(tree(worktree, base))
    ungated = needs_no_gate(worktree, base)
    if ungated:
        say(f"not gating {gated}: it changes only what no gate step reads ({', '.join(UNREAD)})")
        # The gate would say of this tree what it said of the base, so the ledger does too.
        if known is not None:
            record(root, tree(worktree, gated), *known)
    else:
        say(f"gating {gated} on {onto} at {base}")
        if not gate_passes(worktree, gate_command, sys.stdout):
            if known is None:
                say(f"the gate fails and no gate has judged {base}, which the change was rebased onto: fix the change when the failing lines are its doing, otherwise tools/land.py --judge-base")
                return BASE_UNJUDGED
            return blame(root, worktree, onto, base, *known)
        record(root, tree(worktree, gated), "pass", gated)

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
    if ungated:
        say(f"{landed} landed without a gate")
    elif landed == gated:
        say(f"{landed} landed as gated")
    else:
        say(f"{landed} landed on {unseen} commit{'' if unseen == 1 else 's'} the gate did not see: the composition is gated with the next change on it")
    return LANDED


class Tests(unittest.TestCase):
    """Each test builds a project root: main, a task worktree beside it, an origin and logs/."""

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.main, self.task = self.root / "main", self.root / "task"
        (self.root / "logs").mkdir()
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

    def land(self, gate="true", *arguments):
        """Runs the tool in the task worktree. Every gate run adds a line to the root's `gates`."""
        return subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--gate", f"echo run >> ../gates; {gate}", *arguments],
            cwd=self.task,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )

    def gates(self):
        return len((self.root / "gates").read_text().splitlines())

    def ledger(self):
        return [line.split()[:3] for line in (self.root / LEDGER).read_text().splitlines()]

    def tree(self, commit):
        return self.git(self.main, "rev-parse", f"{commit}^{{tree}}")

    def origin(self):
        return self.git(self.root / "origin.git", "rev-parse", "main")

    def test_a_change_whose_gate_passes_lands_as_gated_and_is_pushed(self):
        change = self.commit(self.task, "a")
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)
        self.assertEqual(self.origin(), change)
        self.assertTrue((self.main / "a").exists())
        self.assertEqual(self.ledger(), [[self.tree(change), "pass", change]])
        self.assertIn(f"land: {change} landed as gated", result.stdout)

    def test_a_main_that_moved_under_the_gate_takes_the_change_without_a_second_gate(self):
        self.commit(self.task, "a")
        other = "[ -e ../moved ] || { touch ../moved; echo y > ../main/b; git -C ../main add b; git -C ../main commit -q -m b; }"
        result = self.land(other)
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.gates(), 1)
        self.assertTrue((self.main / "a").exists() and (self.main / "b").exists())
        landed = self.git(self.main, "rev-parse", "main")
        self.assertEqual(self.origin(), landed)
        self.assertIn(f"land: {landed} landed on 1 commit the gate did not see", result.stdout)
        # The ledger holds the tree the gate saw, not the composition that landed.
        self.assertNotIn(self.tree(landed), [line[0] for line in self.ledger()])

    def test_a_merge_that_finds_main_s_index_taken_is_tried_again(self):
        change = self.commit(self.task, "a")
        lock = Path(self.git(self.main, "rev-parse", "--path-format=absolute", "--git-path", "index.lock"))
        lock.write_text("")
        timer = threading.Timer(1.5, lock.unlink)
        timer.start()
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
        result = self.land(other)
        self.assertEqual(result.returncode, CONFLICT, result.stdout)
        self.assertEqual((self.main / "f").read_text(), "theirs\n")
        self.assertEqual(self.gates(), 1)

    def test_a_failing_gate_on_a_base_that_passed_blames_the_change_without_gating_the_base(self):
        self.commit(self.task, "a")
        self.assertEqual(self.land().returncode, LANDED)
        base = self.git(self.main, "rev-parse", "main")
        self.commit(self.task, "bad")
        result = self.land("[ ! -e bad ]")
        self.assertEqual(result.returncode, CHANGE_FAILS, result.stdout)
        self.assertEqual(self.gates(), 2)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), base)
        self.assertIn("the change is at fault", result.stdout)

    def test_a_failing_gate_on_an_unjudged_base_says_so_and_leaves_the_base_ungated(self):
        base = self.commit(self.main, "b")
        self.commit(self.task, "bad")
        result = self.land("[ ! -e bad ]")
        self.assertEqual(result.returncode, BASE_UNJUDGED, result.stdout)
        self.assertEqual(self.gates(), 1)
        self.assertFalse((self.root / LEDGER).exists())
        self.assertIn(f"no gate has judged {base}", result.stdout)
        self.assertIn("--judge-base", result.stdout)

    def test_judging_a_base_that_passes_blames_the_change_and_records_the_base(self):
        base = self.commit(self.main, "b")
        change = self.commit(self.task, "bad")
        self.assertEqual(self.land("[ ! -e bad ]").returncode, BASE_UNJUDGED)
        result = self.land("[ ! -e bad ]", "--judge-base")
        self.assertEqual(result.returncode, CHANGE_FAILS, result.stdout)
        self.assertEqual(self.gates(), 2)
        self.assertEqual(self.ledger(), [[self.tree(base), "pass", base]])
        self.assertTrue((self.root / "logs" / f"base-{base[:12]}-gate.log").exists())
        # The worktree is back on the change, rebased onto the base.
        self.assertEqual(self.git(self.task, "symbolic-ref", "--short", "HEAD"), "task")
        self.assertEqual(self.git(self.task, "rev-parse", "HEAD~1"), base)
        self.assertNotEqual(self.git(self.task, "rev-parse", "HEAD"), change)
        self.assertEqual(self.git(self.task, "status", "--porcelain"), "")

    def test_a_base_judged_to_fail_by_itself_is_named_with_its_suspects_and_gated_once(self):
        self.commit(self.task, "a")
        self.assertEqual(self.land().returncode, LANDED)
        gated = self.git(self.main, "rev-parse", "main")
        # Two changes that each pass and fail together: b lands on a with no gate of the two.
        composition = "! { [ -e a ] && [ -e b ]; }"
        suspect = self.commit(self.main, "b")
        self.commit(self.task, "c")
        self.assertEqual(self.land(composition).returncode, BASE_UNJUDGED)
        result = self.land(composition, "--judge-base")
        self.assertEqual(result.returncode, BASE_FAILS, result.stdout)
        self.assertEqual(self.gates(), 3)
        self.assertIn([self.tree(suspect), "fail", suspect], self.ledger())
        self.assertIn(f"logs/base-{suspect[:12]}-gate.log", result.stdout)
        self.assertIn(f"land: suspect {suspect}", result.stdout)
        self.assertNotIn(f"land: suspect {gated}", result.stdout)
        self.assertEqual(self.git(self.main, "rev-parse", "main"), suspect)
        # The verdict is in the ledger: the next landing on that base gates only its own change.
        again = self.land(composition)
        self.assertEqual(again.returncode, BASE_FAILS, again.stdout)
        self.assertEqual(self.gates(), 4)
        self.assertIn(f"land: suspect {suspect}", again.stdout)

    def test_a_change_to_paths_no_gate_step_reads_lands_without_a_gate(self):
        self.commit(self.task, ".claude/agents/round.md")
        self.commit(self.task, ".claude/skills/round/SKILL.md")
        change = self.commit(self.task, "CLAUDE.md")
        result = self.land("false")
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertFalse((self.root / "gates").exists())
        self.assertEqual(self.git(self.main, "rev-parse", "main"), change)
        self.assertEqual(self.origin(), change)
        self.assertIn(f"land: {change} landed without a gate", result.stdout)

    def test_a_change_that_also_touches_a_path_the_gate_reads_is_gated(self):
        self.commit(self.task, ".claude/agents/round.md")
        change = self.commit(self.task, ".claude/hooks/guard.sh")
        result = self.land()
        self.assertEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.gates(), 1)
        self.assertIn(f"land: {change} landed as gated", result.stdout)

    def test_a_file_over_the_gate_s_size_limit_is_gated_whatever_its_path(self):
        self.commit(self.task, "CLAUDE.md", "x" * (MAX_FILE_BYTES + 1))
        result = self.land("false")
        self.assertNotEqual(result.returncode, LANDED, result.stdout)
        self.assertEqual(self.gates(), 1)

    def test_an_ungated_change_takes_the_verdict_of_the_base_it_stands_on(self):
        base = self.commit(self.task, "a")
        self.assertEqual(self.land().returncode, LANDED)
        ungated = self.commit(self.task, "CLAUDE.md")
        self.assertEqual(self.land("false").returncode, LANDED)
        self.assertIn([self.tree(ungated), "pass", base], self.ledger())
        # So a change that fails on it is blamed without a gate of the base.
        self.commit(self.task, "bad")
        result = self.land("[ ! -e bad ]")
        self.assertEqual(result.returncode, CHANGE_FAILS, result.stdout)
        self.assertEqual(self.gates(), 2)

    def test_an_ungated_change_on_an_unjudged_base_adds_nothing_to_the_ledger(self):
        self.commit(self.main, "b")
        self.commit(self.task, "CLAUDE.md")
        self.assertEqual(self.land("false").returncode, LANDED)
        self.assertFalse((self.root / LEDGER).exists())

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
    parser = argparse.ArgumentParser(usage="tools/land.py [--judge-base] [--onto BRANCH] [--gate COMMAND] | --test")
    parser.add_argument("--onto", default="main", help="the branch landed on, whose worktree is its sibling (default main)")
    parser.add_argument("--gate", default=GATE, help=f"the gate, a shell command run in the worktree (default {GATE!r})")
    parser.add_argument("--judge-base", action="store_true", help="gate the base the change stands on instead of the change")
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        return 0 if unittest.main(argv=[sys.argv[0]], exit=False).result.wasSuccessful() else 1
    worktree = subprocess.run(["git", "rev-parse", "--show-toplevel"], stdout=subprocess.PIPE, text=True)
    if worktree.returncode != 0:
        return NOT_RUN
    return (judge if args.judge_base else land)(Path(worktree.stdout.strip()), args.onto, args.gate)


if __name__ == "__main__":
    sys.exit(main())
