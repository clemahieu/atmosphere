#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""What is recorded under an epic, held to the tree: the mechanical part of matching an epic's criteria to evidence.

A round runs it before it hands the epic's review to the skeptic (.claude/agents/round.md, section 6),
so that a pass is spent on evidence that is there. The evidence is what the closed issues below the
epic record, its reviews aside: the commits their close reasons name and the logs their close reasons
and notes name, a log being a path ending in `.log`, read from the project root unless absolute, with
`*` matching as in a shell. One line per finding, then the logs that hold, then the count:

    missing <issue>: commit <sha>      the close reason names a commit the repository does not have
    missing <issue>: log <path>        a named log is not there
    off-main <issue>: commit <sha>     the commit exists and main does not contain it
    no-commit <issue>: <reason>        a closed task or bug whose close reason names no commit
    gone <issue>: <file> of <sha>      a file the commit wrote is not on main
    stale <issues>: <logs> ...         a file the logs attest has changed on main since they were made
    current <issues>: <logs>           the logs are there and nothing they attest has changed

A log attests the files changed by the commits of the issues that name it. One changed since the log
was made when a commit on main, other than those, touches it and was committed after the log was last
written; the line names each such file with the newest such commit. Logs that the same issues name
and that the same files have changed under share a line. A stale log is the record of its commit and
not of main: most are stale in a tree that moves, and what was true at their commit is re-run on main.

It finds what is absent or older than the tree, and not what is weak: whether a log shows what a
criterion asks is the round's reading, and then the skeptic's.

usage: tools/review-evidence.py EPIC     (from `bd list --all` run in this tree)
       tools/review-evidence.py --test   (this script's own tests)
"""
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TREE = Path(__file__).resolve().parents[1]
COMMIT = re.compile(r"(?<![\w./-])[0-9a-f]{7,40}(?![\w-])")
LOG = re.compile(r"(?<![\w$~/.*<>-])[\w$~.*<>-]*/[\w$~/.*<>-]*\.log\b")
SHORT = 8
LISTED = 6


def git(tree, *arguments):
    """What a git command printed, or None when it failed."""
    ran = subprocess.run(["git", "-C", str(tree), *arguments], capture_output=True, text=True)
    return ran.stdout if ran.returncode == 0 else None


def below(issues, epic):
    """The closed issues below the epic, its reviews and theirs aside, in the order bd listed them."""
    children = {}
    for issue in issues:
        children.setdefault(issue.get("parent"), []).append(issue)
    found, queue = [], list(children.get(epic, []))
    while queue:
        issue = queue.pop(0)
        if "review" in (issue.get("labels") or []):
            continue
        if issue["status"] == "closed":
            found.append(issue)
        queue.extend(children.get(issue["id"], []))
    return found


def commits(tree, issue):
    """The commits a close reason names as (token, full hash or None): a token that is hex, and read as a commit when it has a digit and a letter or resolves."""
    named = []
    for token in dict.fromkeys(COMMIT.findall(issue.get("close_reason") or "")):
        full = git(tree, "rev-parse", "--verify", "--quiet", f"{token}^{{commit}}")
        if full or re.search(r"\d", token) and re.search(r"[a-f]", token):
            named.append((token, full.strip() if full else None))
    return named


def logs(root, issue):
    """The logs an issue names as (name as written, the paths it resolves to), a name with a `<placeholder>` aside."""
    named = []
    for token in dict.fromkeys(LOG.findall(f"{issue.get('close_reason') or ''}\n{issue.get('notes') or ''}")):
        if "<" in token or ">" in token:
            continue
        path = os.path.expanduser(token.removeprefix("$root/"))
        named.append((token, sorted(glob.glob(str(Path(root) / path)))))
    return named


def changed_since(tree, files, moment, own):
    """For each of the files a commit on main touched after the moment, the newest such commit, those in `own` aside."""
    newest, commit = {}, None
    for line in (git(tree, "log", "--format=@%H %ct", "--name-only", "main", "--", *files) or "").splitlines():
        if line.startswith("@"):
            name, stamp = line[1:].split()
            commit = name if int(stamp) > moment and name not in own else None
        elif line and commit and line in files:
            newest.setdefault(line, commit)
    return newest


def evidence(issues, epic, tree, root):
    """The lines for the epic, as the opening comment gives them."""
    found, held, wrote = [], {}, {}
    closed = below(issues, epic)
    on_main = set(git(tree, "ls-tree", "-r", "--name-only", "main").splitlines())
    total = 0
    for issue in closed:
        named = commits(tree, issue)
        total += len(named)
        own = set()
        for token, full in named:
            if not full:
                found.append(f"missing {issue['id']}: commit {token}")
            elif git(tree, "merge-base", "--is-ancestor", full, "main") is None:
                found.append(f"off-main {issue['id']}: commit {token}")
            else:
                own.add(full)
                changes = [line.split("\t") for line in git(tree, "show", "--format=", "--name-status", "--no-renames", full).splitlines() if line]
                wrote[full] = {file for _, file in changes}
                found.extend(f"gone {issue['id']}: {file} of {token}" for status, file in changes if status != "D" and file not in on_main)
        if not named and issue["issue_type"] != "epic":
            found.append(f"no-commit {issue['id']}: {' '.join((issue.get('close_reason') or '').split())[:80]}")
        for token, paths in logs(root, issue):
            if not paths:
                found.append(f"missing {issue['id']}: log {token}")
            for path in paths:
                namers, theirs = held.setdefault(path, ({}, set()))
                namers[issue["id"]] = None
                theirs.update(own)
    groups = {}
    for path, (namers, own) in held.items():
        files = {file for commit in own for file in wrote[commit]}
        newest = changed_since(tree, files, os.path.getmtime(path), own) if files else {}
        groups.setdefault((", ".join(namers), len(files), tuple(sorted(newest.items()))), []).append(os.path.relpath(path, root))
    current = []
    for (namers, count, newest), paths in groups.items():
        if newest:
            shown = [f"{file} {commit[:SHORT]}" for file, commit in newest]
            more = f"; and {len(shown) - LISTED} more" if len(shown) > LISTED else ""
            found.append(f"stale {namers}: {', '.join(paths)}: {len(newest)} of their {count} files changed on main since: {'; '.join(shown[:LISTED])}{more}")
        else:
            current.append(f"current {namers}: {', '.join(paths)}")
    return found + current + [f"{len(closed)} closed issues, {total} commits, {len(held)} logs: {len(found)} findings"]


def main(arguments):
    usage = __doc__.strip().split("usage: ")[1].join(["usage: ", ""])
    if len(arguments) != 1 or arguments[0].startswith("-"):
        sys.exit(usage)
    listed = subprocess.run(["bd", "list", "--all", "--json", "--limit", "0"], cwd=TREE, capture_output=True, text=True)
    if listed.returncode != 0:
        sys.exit(f"review-evidence: bd list exited {listed.returncode}: {(listed.stderr or listed.stdout).strip()}")
    issues = json.loads(listed.stdout)
    if not any(issue["id"] == arguments[0] for issue in issues):
        sys.exit(f"review-evidence: bd lists no issue {arguments[0]}")
    for line in evidence(issues, arguments[0], TREE, TREE.parent):
        print(line)
    return 0


class Tests(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        self.tree = self.root / "main"
        (self.root / "logs").mkdir()
        subprocess.run(["git", "init", "-q", "-b", "main", str(self.tree)], check=True)
        self.clock = 1000

    def commit(self, **files):
        """Commits the files a tick after everything before it; gives the short hash."""
        self.clock += 10
        for name, text in files.items():
            path = self.tree / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        when = {"GIT_AUTHOR_DATE": f"@{self.clock} +0000", "GIT_COMMITTER_DATE": f"@{self.clock} +0000"}
        identity = ["-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
        subprocess.run(["git", "-C", str(self.tree), "add", "-A"], check=True)
        subprocess.run(["git", "-C", str(self.tree), *identity, "commit", "-q", "-m", "change"], check=True, env={**os.environ, **when})
        return git(self.tree, "rev-parse", "--short=8", "HEAD").strip()

    def log(self, name):
        """Writes a log a tick after everything before it."""
        self.clock += 10
        path = self.root / "logs" / name
        path.write_text("exit 0\n")
        os.utime(path, (self.clock, self.clock))
        return f"logs/{name}"

    def issues(self, *made):
        """Issues from (id, close reason or None for an open one, extra), the parent read from the id."""
        listed = [{"id": "a.1", "issue_type": "epic", "status": "open", "parent": "a"}]
        for name, reason, *extra in made:
            issue = {"id": name, "issue_type": "task", "parent": name.rpartition(".")[0], "status": "closed" if reason is not None else "open", "close_reason": reason}
            issue.update(extra[0] if extra else {})
            listed.append(issue)
        return listed

    def lines(self, *made):
        return evidence(self.issues(*made), "a.1", self.tree, self.root)

    def test_a_commit_and_a_log_that_are_there_are_current(self):
        first = self.commit(a="1\n")
        log = self.log("a.1.1-gate.log")
        self.assertEqual(self.lines(("a.1.1", f"{first}: gate exit 0, {log}")),
                         ["current a.1.1: logs/a.1.1-gate.log", "1 closed issues, 1 commits, 1 logs: 0 findings"])

    def test_a_commit_the_repository_lacks_and_a_log_that_is_gone_are_missing(self):
        self.commit(a="1\n")
        self.assertEqual(self.lines(("a.1.1", "abc1234f: verified 1048576 of them, defaced nothing; /tmp/claude-1000/pad/gate.log", {"notes": "ran $root/logs/a.1.1-verify.log, and logs/<id>-gate.log is where a gate goes"})),
                         ["missing a.1.1: commit abc1234f", "missing a.1.1: log /tmp/claude-1000/pad/gate.log", "missing a.1.1: log $root/logs/a.1.1-verify.log",
                          "1 closed issues, 1 commits, 0 logs: 3 findings"])

    def test_a_commit_main_does_not_contain_is_off_main(self):
        self.commit(a="1\n")
        subprocess.run(["git", "-C", str(self.tree), "checkout", "-q", "-b", "side"], check=True)
        side = self.commit(a="2\n")
        subprocess.run(["git", "-C", str(self.tree), "checkout", "-q", "main"], check=True)
        self.assertEqual(self.lines(("a.1.1", f"{side}: gate"))[0], f"off-main a.1.1: commit {side}")

    def test_a_closed_task_that_names_no_commit_is_listed_and_an_epic_is_not(self):
        first = self.commit(a="1\n")
        self.assertEqual(self.lines(("a.1.1", "superseded by   a.1.2"), ("a.1.2", "children's evidence", {"issue_type": "epic"}), ("a.1.2.1", f"{first}: gate")),
                         ["no-commit a.1.1: superseded by a.1.2", "3 closed issues, 1 commits, 0 logs: 1 findings"])

    def test_reviews_open_issues_and_issues_outside_the_epic_are_not_read(self):
        self.commit(a="1\n")
        self.assertEqual(self.lines(("a.1.1", "refuted: abc1234f", {"labels": ["review"]}), ("a.1.2", None, {"notes": "logs/gone.log"}), ("a.2", "abc1234f: gate")),
                         ["0 closed issues, 0 commits, 0 logs: 0 findings"])

    def test_a_log_is_stale_when_another_commit_changed_a_file_its_issue_s_commits_changed(self):
        self.commit(a="1\n", b="1\n", c="1\n")
        log = self.log("a.1.1-throwaway.log")
        own = self.commit(a="2\n", b="2\n")
        made = [("a.1.1", f"{own}: throwaway {log}")]
        self.assertEqual(self.lines(*made)[0], "current a.1.1: logs/a.1.1-throwaway.log")
        self.commit(c="2\n")
        self.assertEqual(self.lines(*made)[0], "current a.1.1: logs/a.1.1-throwaway.log")
        self.commit(a="3\n")
        later = self.commit(a="4\n", c="3\n")
        gate = self.log("a.1.1-gate.log")
        self.assertEqual(self.lines(*made, ("a.1.2", f"{later}: gate"))[0], f"stale a.1.1: logs/a.1.1-throwaway.log: 1 of their 2 files changed on main since: a {later}")
        self.assertEqual(self.lines(("a.1.1", f"{own}: throwaway {log}, gate {gate}", {"notes": f"ran {log}"}))[:2],
                         [f"stale a.1.1: logs/a.1.1-throwaway.log: 1 of their 2 files changed on main since: a {later}", "current a.1.1: logs/a.1.1-gate.log"])

    def test_a_log_made_after_the_last_change_is_current_and_a_pattern_names_each_log_it_matches(self):
        first = self.commit(a="1\n")
        self.commit(a="2\n")
        self.log("a.1.1-verify-x86_64.log")
        self.log("a.1.1-verify-aarch64.log")
        self.assertEqual(self.lines(("a.1.1", f"{first}: logs/a.1.1-verify*.log")),
                         ["current a.1.1: logs/a.1.1-verify-aarch64.log, logs/a.1.1-verify-x86_64.log", "1 closed issues, 1 commits, 2 logs: 0 findings"])

    def test_a_file_a_commit_wrote_that_main_no_longer_has_is_gone(self):
        wrote = self.commit(a="1\n", test="1\n", old="1\n")
        subprocess.run(["git", "-C", str(self.tree), "mv", "test", "moved"], check=True)
        (self.tree / "old").unlink()
        removed = self.commit()
        self.assertEqual(self.lines(("a.1.1", f"{wrote}: gate"), ("a.1.2", f"{removed}: gate")),
                         [f"gone a.1.1: old of {wrote}", f"gone a.1.1: test of {wrote}", "2 closed issues, 2 commits, 0 logs: 2 findings"])

    def test_the_command_reads_the_tree_bd_lists_and_refuses_an_unknown_epic(self):
        first = self.commit(a="1\n")
        (self.tree / "tools").mkdir()
        shutil.copy(__file__, self.tree / "tools" / "review-evidence.py")
        (self.root / "tree.json").write_text(json.dumps(self.issues(("a.1.1", f"{first}: gate"))))
        (self.root / "bd").write_text(f'#!/bin/sh\necho "$*" > "{self.root}/call"\ncat "{self.root}/tree.json"\n')
        (self.root / "bd").chmod(0o755)
        def run(*arguments):
            ran = subprocess.run([sys.executable, str(self.tree / "tools" / "review-evidence.py"), *arguments],
                                 env={**os.environ, "PATH": f"{self.root}:{os.environ['PATH']}"}, capture_output=True, text=True)
            return ran.returncode, ran.stdout, ran.stderr
        self.assertEqual(run("a.1"), (0, "1 closed issues, 1 commits, 0 logs: 0 findings\n", ""))
        self.assertEqual((self.root / "call").read_text(), "list --all --json --limit 0\n")
        self.assertEqual(run("a.9"), (1, "", "review-evidence: bd lists no issue a.9\n"))
        for bad in ([], ["--witness", "a=b"], ["a.1", "--witness", "name=log"], ["a.1", "b"]):
            self.assertEqual(run(*bad)[0], 1)
            self.assertTrue(run(*bad)[2].startswith("usage: tools/review-evidence.py EPIC"))


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        sys.argv[1:] = []
        unittest.main()
    sys.exit(main(sys.argv[1:]))
