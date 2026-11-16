#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Hold every file of a verified crate that claims a layout to a build that refuses a wrong claim.

Verus takes a `global layout T is size == N, align == A;` or `global size_of T == N;` claim as
stated: the proof uses N and A, and rust_verify does not compare them with rustc's layout. What
checks a claim is the build. The verus! macro, when it erases ghost code for cargo, turns each claim
into a constant that panics at compile time when size_of::<T>() is not N or align_of::<T>() is not
A. So the claims need no counted list as long as that holds, and this check holds it: a later Verus
whose erased expansion stops checking fails it.

The files are the Rust sources under each workspace member marked
'[package.metadata.atmosphere] verified = true', the crates tools/verify.py proves, that hold a claim
outside a comment. The check copies the verified workspace members, their transitive path
dependencies and workspace manifests to a temporary directory, and in the copy makes one claim of
each file wrong: the first that no `#[cfg(`
attribute guards, its size raised by 8. A file whose every claim is under a cfg is a finding. Then
for each target, x86_64-unknown-linux-gnu and aarch64-unknown-none, one
`cargo check --offline --keep-going` of the marked crates that hold claims, from the copy's root,
with RUSTC_BOOTSTRAP set and the target directory target/layout-claims of the tree, so vstd is
checked once across runs. A file is expected to be refused on both targets, unless a component of
its path is named for one architecture (arch/x86_64.rs, arch/aarch64/...), which only that target
compiles. Refused means an error whose message says the type `does not have the expected size`,
whose outermost expansion is in that file.

It prints one line per finding to stderr, with the target's other errors under it, and exits 1, or
prints one line counting the claims and the files and exits 0.

usage: tools/check-layout-claims.py           the check
       tools/check-layout-claims.py --test    this script's own tests
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent
# Each architecture the gate builds, and the triple the check compiles it for: rustc ships both, and
# a claim's type has the same layout under the kernel's JSON specs, which only add build-std.
TARGETS = {"x86_64": "x86_64-unknown-linux-gnu", "aarch64": "aarch64-unknown-none"}
# A claim, up to the size it states, and the size.
CLAIM = re.compile(r"^(\s*global\s+(?:layout|size_of)\b[^=]*==\s*)(\d+)")
# The amount a wrong claim's size is off by: a multiple of every alignment, so only the size is wrong.
WRONG_BY = 8
# The message of the constant the erased claim panics in, when the size is not the claim's.
REFUSAL = "does not have the expected size"
TARGET_DIR = REPO / "target/layout-claims"


def claims(text):
    """The claims of a file: for each, its line index and whether a #[cfg( attribute guards it."""
    lines = text.splitlines()
    found = []
    for index, line in enumerate(lines):
        if not CLAIM.match(line):
            continue
        above = index - 1
        guarded = False
        while above >= 0 and lines[above].lstrip().startswith(("#[", "//")):
            guarded = guarded or lines[above].lstrip().startswith("#[cfg(")
            above -= 1
        found.append((index, guarded))
    return found


def make_wrong(text):
    """The text with its first unguarded claim's size raised by WRONG_BY, and that line's number; or
    None when every claim is guarded."""
    unguarded = [index for index, guarded in claims(text) if not guarded]
    if not unguarded:
        return None
    lines = text.splitlines(keepends=True)
    index = unguarded[0]
    lines[index] = CLAIM.sub(lambda m: m.group(1) + str(int(m.group(2)) + WRONG_BY), lines[index], count=1)
    return "".join(lines), index + 1


def targets_of(path):
    """The architectures that compile a file: the one a component of its path is named for, or all."""
    parts = Path(path).with_suffix("").parts
    named = [arch for arch in TARGETS if arch in parts]
    return named or list(TARGETS)


def outermost_file(span):
    """The file of the span a macro expansion started from."""
    while span.get("expansion"):
        span = span["expansion"]["span"]
    return span["file_name"]


def refused_files(output, root):
    """The files, relative to root, an error of cargo's JSON output refuses a claim in, and the
    rendered text of every other error."""
    refused, others = set(), []
    for line in output.splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if message.get("reason") != "compiler-message" or message["message"]["level"] != "error":
            continue
        body = message["message"]
        primary = [span for span in body["spans"] if span["is_primary"]]
        if REFUSAL in body["message"] and primary:
            name = Path(outermost_file(primary[0]))
            if name.is_absolute():
                name = name.relative_to(root) if name.is_relative_to(root) else name
            refused.add(name.as_posix())
        elif body.get("rendered"):
            others.append(body["rendered"].rstrip())
    return refused, others


def findings(files, refused):
    """A line for each file a target that compiles it does not refuse; files maps each to its
    architectures, refused maps each architecture to the files refused there."""
    return [f"{path}: a wrong claim at line {line} builds for {arch}"
            for path, (line, archs) in sorted(files.items())
            for arch in archs if path not in refused[arch]]


def load_toml(path):
    with open(path, "rb") as file:
        return tomllib.load(file)


def path_deps(manifest, member_dir, root, workspace_deps):
    """Relative workspace directory paths referenced as path dependencies by manifest."""
    root_resolved = root.resolve()
    tables = [manifest.get(key) or {} for key in ("dependencies", "dev-dependencies", "build-dependencies")]
    for target in (manifest.get("target") or {}).values():
        if isinstance(target, dict):
            tables.extend(target.get(key) or {} for key in ("dependencies", "dev-dependencies", "build-dependencies"))
    deps = []
    for table in tables:
        for name, spec in table.items():
            if not isinstance(spec, dict):
                continue
            raw_path = spec.get("path")
            base = root_resolved / member_dir
            if raw_path is None and spec.get("workspace"):
                wspec = workspace_deps.get(spec.get("package") or name)
                if isinstance(wspec, dict):
                    raw_path = wspec.get("path")
                    base = root_resolved
            if raw_path is None:
                continue
            resolved = (base / raw_path).resolve()
            if resolved.is_relative_to(root_resolved):
                deps.append(resolved.relative_to(root_resolved))
    return deps


def selected_members(root):
    """Verified workspace members [(package, dir)] and ordered workspace dirs needed to build them."""
    workspace = load_toml(root / "Cargo.toml").get("workspace") or {}
    workspace_deps = workspace.get("dependencies") or {}
    packages = {}
    for raw in workspace.get("members") or []:
        member_dir = Path(raw)
        manifest_path = root / member_dir / "Cargo.toml"
        if not manifest_path.is_file():
            continue
        manifest = load_toml(manifest_path)
        package = manifest["package"]
        atmosphere = (package.get("metadata") or {}).get("atmosphere") or {}
        packages[member_dir] = (package["name"], bool(atmosphere.get("verified", False)), manifest)
    verified = [directory for directory, (_, is_verified, _) in packages.items() if is_verified]
    selected_set = set(verified)
    queue = list(verified)
    while queue:
        current = queue.pop(0)
        for dep_dir in path_deps(packages[current][2], current, root, workspace_deps):
            if dep_dir in packages and dep_dir not in selected_set:
                selected_set.add(dep_dir)
                queue.append(dep_dir)
    members = [(packages[directory][0], directory) for directory in verified]
    selected = [directory for directory in packages if directory in selected_set]
    return members, selected


def workspace_manifest(text, keep_members):
    """Rewrite [workspace] members in Cargo.toml text to keep_members, preserving the rest."""
    section = re.search(r"(?m)^\[workspace\]\s*$", text)
    if section is None:
        raise ValueError("missing [workspace] in Cargo.toml")
    next_section = re.search(r"(?m)^\[", text[section.end():])
    section_end = section.end() + next_section.start() if next_section else len(text)
    members = re.search(r"(?m)^members\s*=\s*\[", text[section.end():section_end])
    if members is None:
        raise ValueError("missing workspace members in Cargo.toml")
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
    raise ValueError("unterminated workspace members array in Cargo.toml")


def workspace_files(root, selected):
    """Files inside selected workspace directories, using git when present and skipping build dirs."""
    if not selected:
        return []
    if (root / ".git").exists():
        listed = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--cached", "--others", "--exclude-standard",
             "--", *(directory.as_posix() for directory in selected)],
            check=True, stdout=subprocess.PIPE,
        ).stdout
        return [Path(name) for name in listed.decode().split("\0") if name and (root / name).is_file()]
    files, seen = [], set()
    for directory in selected:
        for dirpath, dirs, filenames in os.walk(root / directory):
            dirs[:] = sorted(d for d in dirs if d not in ("target", ".git"))
            for name in sorted(filenames):
                full = Path(dirpath) / name
                rel = full.relative_to(root)
                if full.is_file() and rel not in seen:
                    seen.add(rel)
                    files.append(rel)
    return files


def owner(path, members):
    """The package whose directory holds path most closely."""
    holding = [(len(directory.parts), name) for name, directory in members
               if path.is_relative_to(directory)]
    return max(holding)[1]


def main():
    members, selected = selected_members(REPO)
    manifest = workspace_manifest((REPO / "Cargo.toml").read_text(), [directory.as_posix() for directory in selected])
    paths = workspace_files(REPO, selected)
    problems, files, packages, total = [], {}, set(), 0
    with tempfile.TemporaryDirectory(prefix="layout-claims-") as copy:
        copy = Path(copy)
        for name in ("Cargo.lock", "rust-toolchain.toml"):
            if (REPO / name).is_file():
                shutil.copy2(REPO / name, copy / name)
        (copy / "Cargo.toml").write_text(manifest)
        for path in paths:
            (copy / path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(REPO / path, copy / path)
        for path in paths:
            if path.suffix != ".rs" or not any(path.is_relative_to(d) for _, d in members):
                continue
            text = (REPO / path).read_text()
            count = len(claims(text))
            if not count:
                continue
            total += count
            wrong = make_wrong(text)
            if wrong is None:
                problems.append(f"{path}: every claim is under a #[cfg(, so no target is sure to compile one")
                continue
            (copy / path).write_text(wrong[0])
            files[path.as_posix()] = (wrong[1], targets_of(path))
            packages.add(owner(path, members))
        refused, runs = {}, {}
        env = {**os.environ, "RUSTC_BOOTSTRAP": "1", "CARGO_TARGET_DIR": str(TARGET_DIR)}
        for arch, triple in TARGETS.items():
            command = ["cargo", "check", "--offline", "--keep-going", "--message-format=json",
                       "--target", triple] + [arg for name in sorted(packages) for arg in ("-p", name)]
            ran = subprocess.run(command, cwd=copy, env=env, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True) if packages else None
            refused[arch], others = refused_files(ran.stdout, copy) if ran else (set(), [])
            runs[arch] = (command, ran and ran.returncode, others)
        missed = findings(files, refused)
        for arch, (command, code, others) in runs.items():
            if any(line.endswith(f"builds for {arch}") for line in missed):
                print(f"{' '.join(command)}: exit status {code}", file=sys.stderr)
                for text in others:
                    print(text, file=sys.stderr)
        problems += missed
    for line in problems:
        print(line, file=sys.stderr)
    if problems:
        return 1
    print(f"{total} layout claims in {len(files)} files: a wrong claim in each file is refused by the build "
          f"on each target that compiles it")
    return 0


class Tests(unittest.TestCase):
    def test_a_claim_is_either_form(self):
        text = ("global layout Node is size == 1032, align == 8;\n"
                "    global size_of usize == 8;\n"
                "// global layout Comment is size == 1, align == 1;\n"
                "let global = 3;\n")
        self.assertEqual(claims(text), [(0, False), (1, False)])

    def test_a_cfg_attribute_above_a_claim_guards_it_and_cfg_attr_does_not(self):
        text = ("#[cfg(target_arch = \"x86_64\")]\n"
                "global layout ThreadRecord is size == 280, align == 8;\n"
                "#[cfg_attr(not(verus_keep_ghost), allow(unused_braces))]\n"
                "global size_of usize == 8;\n")
        self.assertEqual(claims(text), [(1, True), (3, False)])

    def test_the_first_unguarded_claim_is_made_wrong_and_nothing_else(self):
        text = ("#[cfg(target_arch = \"aarch64\")]\n"
                "global layout ThreadRecord is size == 384, align == 8;\n"
                "global layout QueueRecord is size == 32, align == 8;\n"
                "global layout ReplyRecord is size == 16, align == 8;\n")
        wrong, line = make_wrong(text)
        self.assertEqual(line, 3)
        self.assertEqual(wrong.splitlines(), [
            "#[cfg(target_arch = \"aarch64\")]",
            "global layout ThreadRecord is size == 384, align == 8;",
            "global layout QueueRecord is size == 40, align == 8;",
            "global layout ReplyRecord is size == 16, align == 8;"])
        self.assertEqual(make_wrong("global size_of usize == 8;\n")[0], "global size_of usize == 16;\n")

    def test_a_file_whose_every_claim_is_guarded_has_none_to_make_wrong(self):
        self.assertIsNone(make_wrong("#[cfg(x)]\nglobal layout A is size == 8, align == 8;\n"))

    def test_an_architectures_file_is_compiled_for_it_alone(self):
        self.assertEqual(targets_of("aheap/src/arch/x86_64.rs"), ["x86_64"])
        self.assertEqual(targets_of("kernel/verified/arch/aarch64/table.rs"), ["aarch64"])
        self.assertEqual(targets_of("kernel/verified/layouts.rs"), ["x86_64", "aarch64"])

    @staticmethod
    def message(text, primary_file, outer, level="error"):
        span = {"file_name": primary_file, "is_primary": True,
                "expansion": {"span": {"file_name": outer, "expansion": None}} if outer else None}
        return json.dumps({"reason": "compiler-message", "message": {
            "level": level, "message": text, "spans": [span], "rendered": f"error: {text}\n"}})

    def test_a_refusal_is_located_by_its_outermost_expansion(self):
        root = Path("/copy")
        output = "\n".join([
            self.message("evaluation panicked: does not have the expected size",
                         "/rust/library/core/src/panic.rs", "kernel/verified/layouts.rs"),
            self.message("evaluation panicked: does not have the expected size",
                         "/rust/library/core/src/panic.rs", "/copy/aheap/src/arch/x86_64.rs"),
            self.message("mismatched types", "kernel/verified/lib.rs", None),
            self.message("does not have the expected size", "kernel/verified/lib.rs", None, level="warning"),
            "not json",
            json.dumps({"reason": "build-finished", "success": False})])
        refused, others = refused_files(output, root)
        self.assertEqual(refused, {"kernel/verified/layouts.rs", "aheap/src/arch/x86_64.rs"})
        self.assertEqual(others, ["error: mismatched types"])

    def test_a_file_is_a_finding_on_each_target_that_compiles_it_and_does_not_refuse_it(self):
        files = {"kernel/verified/layouts.rs": (30, ["x86_64", "aarch64"]),
                 "aheap/src/arch/x86_64.rs": (39, ["x86_64"])}
        self.assertEqual(findings(files, {"x86_64": set(files), "aarch64": set()}),
                         ["kernel/verified/layouts.rs: a wrong claim at line 30 builds for aarch64"])
        self.assertEqual(findings(files, {"x86_64": {"kernel/verified/layouts.rs"},
                                          "aarch64": {"kernel/verified/layouts.rs"}}),
                         ["aheap/src/arch/x86_64.rs: a wrong claim at line 39 builds for x86_64"])

    def test_a_file_belongs_to_the_member_whose_directory_holds_it_most_closely(self):
        members = [("kernel", Path("kernel")), ("verified", Path("kernel/verified"))]
        self.assertEqual(owner(Path("kernel/verified/lib.rs"), members), "verified")

    def test_workspace_manifest_filters_members_and_preserves_other_sections(self):
        text = (
            '[workspace]\n'
            'resolver = "2"\n'
            'members = [\n'
            '  "asys",\n'
            '  "dom0",\n'
            '  "kernel/verified",\n'
            ']\n\n'
            '# Keep comments and pinned deps\n'
            '[workspace.dependencies.vstd]\n'
            'git = "https://github.com/verus-lang/verus"\n'
            'rev = "abc123"\n'
        )
        filtered = workspace_manifest(text, ["asys", "kernel/verified"])
        parsed = tomllib.loads(filtered)
        self.assertEqual(parsed["workspace"]["members"], ["asys", "kernel/verified"])
        self.assertEqual(parsed["workspace"]["dependencies"]["vstd"]["rev"], "abc123")
        self.assertIn("# Keep comments and pinned deps", filtered)

    def test_selected_members_and_workspace_files_ignore_unrelated_and_missing_members_without_git(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Cargo.toml").write_text(
                '[workspace]\nmembers = ["plain_dep", "verified_pkg", "unused", "absent_pkg"]\n'
            )
            for rel, content in [
                ("README.md", "docs\n"),
                ("docs/note.md", "note\n"),
                ("plain_dep/Cargo.toml", '[package]\nname = "plain_dep"\nversion = "0.1.0"\n'),
                ("plain_dep/src/lib.rs", "pub fn ok() {}\n"),
                ("plain_dep/target/ignored.rs", "stale\n"),
                ("verified_pkg/Cargo.toml",
                 '[package]\nname = "verified_pkg"\nversion = "0.1.0"\n'
                 '[package.metadata.atmosphere]\nverified = true\n'
                 '[dependencies]\nplain_dep = { path = "../plain_dep" }\n'),
                ("verified_pkg/src/lib.rs", "pub fn checked() {}\n"),
                ("unused/Cargo.toml", '[package]\nname = "unused"\nversion = "0.1.0"\n'),
                ("unused/src/lib.rs", "pub fn nope() {}\n"),
            ]:
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            members, selected = selected_members(root)
            self.assertEqual(members, [("verified_pkg", Path("verified_pkg"))])
            self.assertEqual(selected, [Path("plain_dep"), Path("verified_pkg")])
            self.assertEqual(
                {path.as_posix() for path in workspace_files(root, selected)},
                {
                    "plain_dep/Cargo.toml",
                    "plain_dep/src/lib.rs",
                    "verified_pkg/Cargo.toml",
                    "verified_pkg/src/lib.rs",
                },
            )


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    elif sys.argv[1:]:
        sys.exit(__doc__)
    else:
        sys.exit(main())
