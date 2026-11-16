#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Verify the crates marked for verification with Verus.

A crate is marked by '[package.metadata.atmosphere] verified = true' in its Cargo.toml. Each marked
crate's library root goes to rust_verify as a lib crate, with a solver budget of --rlimit 100
(slinkedlist::remove_helper7 needs more than the default). Extra arguments go to rust_verify after
those, for every crate. Marked crates run in dependency order. A marked crate that another marked
crate depends on is also passed --crate-name, --export target/verus/<crate>.vir and --compile,
which writes lib<crate>.rlib under target/verus/. A marked crate with marked dependencies is passed --extern and --import
for each of them, and a crate with any dependency is passed -L target/verus/, where rustc finds a
dependency's own dependencies. A crate that no marked crate depends on, and that itself depends on no marked
crate, is invoked as before. A marked crate may also depend on a workspace member that is not marked
and has no dependencies of its own, such as asys, whose calls the marked crate makes only from
external_body glue: that member is compiled once by plain rustc, for the same target, into
lib<crate>.rlib under target/verus/, and the marked crate is passed --extern for it with no --import,
since it has no specifications. rust_verify prints one 'verification results:: N verified, M errors'
line per crate. The script exits 0 when every crate verifies, and otherwise with the first failing
crate's status. A dependency that failed verification is not followed by its dependents, and the
script names both.

Each rust_verify runs in a systemd user scope of its own, capped at MEMORY_MAX of memory with no
swap, and the solver it starts runs inside the same cap. A proof that grows past it is killed by
its own cgroup, alone, and the script says that crate ran out of memory and exits nonzero; the
kernel's OOM killer is never reached, so the user manager does not stop the unit that started the
script and everything else in it. An ordinary verify of a crate peaks near 4 GiB.

With --target aarch64 every crate is checked under target_arch = "aarch64": rust_verify gets
--target aarch64-unknown-none and takes vstd and verus_builtin from the aarch64 build that
tools/setup-verus.sh writes beside the host one, and the shared crates' rlibs go under
target/verus/aarch64-unknown-none/. With no --target the crates are checked for the host, x86_64.
design/arch-module/ says why one run per target.

It first checks that the Verus checkout, verus at the project root, beside the worktrees, is at the
Verus commit the workspace Cargo.toml pins as vstd's revision, and exits naming both commits when it is
not, since the crates would otherwise be checked by a Verus other than the one their vstd comes from.

Expects tools/env.sh to be sourced, which puts rust_verify on PATH.

usage: tools/verify.py [--target aarch64] [rust_verify argument...]
       tools/verify.py --test    (this script's own tests)
"""
import json
import os
import subprocess
import sys
import tempfile
import time
import tomllib
import unittest
from contextlib import redirect_stderr
from io import StringIO
from pathlib import Path
from unittest import mock

REPO = Path(__file__).resolve().parent.parent

# The Verus checkout tools/setup-verus.sh builds and tools/env.sh puts on PATH: one at the project root,
# outside every tree, which every worktree's tools read.
VERUS = REPO.parent / "verus"

# The rustc target each --target names. tools/setup-verus.sh builds vstd and verus_builtin for each
# under source/target-verus/<triple> in the checkout.
TARGETS = {"aarch64": "aarch64-unknown-none"}

# The memory each rust_verify run, its solvers included, may hold, in systemd's notation.
MEMORY_MAX = "16G"


def cargo_metadata():
    return json.loads(
        subprocess.run(
            ["cargo", "metadata", "--no-deps", "--format-version", "1"],
            cwd=REPO,
            check=True,
            stdout=subprocess.PIPE,
        ).stdout
    )


def marked_crates(metadata):
    """Library crates marked for verification, in metadata order, with marked dependencies and plain
    ones: workspace members that are not marked, each with its edition and library root."""
    crates = []
    by_package = {}
    members = {package["name"]: package for package in metadata["packages"]}
    for package in metadata["packages"]:
        atmosphere = (package.get("metadata") or {}).get("atmosphere") or {}
        if not atmosphere.get("verified", False):
            continue
        crate = {
            "package": package["name"],
            "crate": lib_target(package)["name"].replace("-", "_"),
            "src": lib_target(package)["src_path"],
            "deps": [],
            "plain": [],
        }
        crates.append(crate)
        by_package[package["name"]] = crate
    for package in metadata["packages"]:
        crate = by_package.get(package["name"])
        if crate is None:
            continue
        seen = set()
        for dep in package.get("dependencies") or []:
            if dep.get("kind") in ("dev", "build") or dep["name"] in seen:
                continue
            seen.add(dep["name"])
            dep_crate = by_package.get(dep["name"])
            if dep_crate is not None:
                extern = dep.get("rename") or dep_crate["crate"]
                crate["deps"].append({"extern": extern, "crate": dep_crate["crate"], "package": dep_crate["package"]})
            elif dep.get("path") is not None and dep["name"] in members:
                crate["plain"].append(plain_crate(members[dep["name"]], dep, package["name"]))
    return order_crates(crates)


def lib_target(package):
    libs = [t for t in package["targets"] if t["kind"] == ["lib"] and t["crate_types"] == ["lib"]]
    if not libs:
        sys.exit(f"verify: package {package['name']} has no lib crate")
    return libs[0]


def plain_crate(package, dep, dependent):
    """A workspace member a marked crate depends on that is not marked. It is compiled by plain rustc,
    which takes no dependencies, so one with dependencies of its own is refused."""
    if any(d.get("kind") not in ("dev", "build") for d in package.get("dependencies") or []):
        sys.exit(f"verify: {dependent} depends on {package['name']}, which is not marked and has dependencies")
    lib = lib_target(package)
    crate = lib["name"].replace("-", "_")
    return {"extern": dep.get("rename") or crate, "crate": crate, "src": lib["src_path"], "edition": package["edition"]}


def emit_dep_info_args(dep_info, compile_artifact=False):
    """Compiler flags that write a dep-info file without dropping compiled outputs."""
    return (["--emit=link"] if compile_artifact else []) + [f"--emit=dep-info={dep_info}"]


def append_rustc_args(command, rustc_args):
    """Append rustc pass-through flags to a rust_verify command without duplicating `--`."""
    return [*command, *rustc_args] if "--" in command else [*command, "--", *rustc_args]


def plain_command(plain, triple, verus_out, dep_info=None):
    """The rustc command that compiles a plain dependency into verus_out for the triple."""
    command = ["rustc", "--crate-type", "lib", "--crate-name", plain["crate"], "--edition", plain["edition"]]
    if triple is not None:
        command += ["--target", triple]
    command += [plain["src"], "--out-dir", str(verus_out)]
    if dep_info is not None:
        command += emit_dep_info_args(dep_info, compile_artifact=True)
    return command


def order_crates(crates):
    """Dependencies before the crates that use them. Independent crates keep metadata order."""
    by_package = {crate["package"]: crate for crate in crates}
    indegree = {crate["package"]: len(crate["deps"]) for crate in crates}
    dependents = {crate["package"]: [] for crate in crates}
    for crate in crates:
        for dep in crate["deps"]:
            dependents[dep["package"]].append(crate["package"])
    ready = [crate["package"] for crate in crates if indegree[crate["package"]] == 0]
    ordered = []
    while ready:
        package = ready.pop(0)
        ordered.append(by_package[package])
        for dependent in dependents[package]:
            indegree[dependent] -= 1
            if indegree[dependent] == 0:
                ready.append(dependent)
    if len(ordered) != len(crates):
        left = [crate["package"] for crate in crates if crate not in ordered]
        sys.exit(f"verify: marked crates cycle: {', '.join(left)}")
    return ordered


def verify_command(crate, depended_on, triple, verus_out, extra_args, dep_info=None):
    command = ["rust_verify", "--crate-type", "lib", crate["src"], "--rlimit", "100"]
    if triple is not None:
        command += ["--target", triple]
    if crate["deps"] or crate["plain"]:
        # A dependency's own dependencies are found by search, not named by --extern.
        command += ["-L", str(verus_out)]
    for dep in crate["deps"]:
        rlib = verus_out / f"lib{dep['crate']}.rlib"
        vir = verus_out / f"{dep['crate']}.vir"
        command += ["--extern", f"{dep['extern']}={rlib}", "--import", f"{dep['extern']}={vir}"]
    for plain in crate["plain"]:
        command += ["--extern", f"{plain['extern']}={verus_out / ('lib' + plain['crate'] + '.rlib')}"]
    compile_artifact = crate["package"] in depended_on
    if compile_artifact:
        # lib.rs would otherwise compile as crate `lib`, and the rlib name follows the crate name.
        command += [
            "--crate-name",
            crate["crate"],
            "--export",
            str(verus_out / f"{crate['crate']}.vir"),
            "--compile",
            "--out-dir",
            str(verus_out),
        ]
    command += extra_args
    if dep_info is not None:
        command = append_rustc_args(command, emit_dep_info_args(dep_info, compile_artifact=compile_artifact))
    return command


def capped(command, unit, memory_max):
    """The command run in the user scope named unit, holding at most memory_max and no swap.
    systemd-run --scope executes the command itself, so its environment, directory, streams and
    exit status are the command's."""
    return [
        "systemd-run", "--user", "--scope", "--quiet", f"--unit={unit}",
        "-p", f"MemoryMax={memory_max}", "-p", "MemorySwapMax=0", "--", *command,
    ]


def scope_state(unit):
    """What the user manager holds for the scope: its LoadState, ActiveState and Result."""
    shown = subprocess.run(
        ["systemctl", "--user", "show", f"{unit}.scope", "-p", "LoadState", "-p", "ActiveState", "-p", "Result"],
        check=True, stdout=subprocess.PIPE, text=True,
    ).stdout
    return dict(line.split("=", 1) for line in shown.splitlines())


def run_capped(command, unit, memory_max, **kwargs):
    """Run the command capped, and return its status and whether its cgroup killed it for memory.
    A scope ends with no record unless the OOM killer failed it, which leaves it loaded with Result
    oom-kill until the failure is reset; the manager may mark it a moment after the command ends."""
    status = subprocess.run(capped(command, unit, memory_max), **kwargs).returncode
    if status != -9:
        return status, False
    deadline = time.monotonic() + 10
    state = scope_state(unit)
    while state["ActiveState"] in ("active", "deactivating") and time.monotonic() < deadline:
        time.sleep(0.1)
        state = scope_state(unit)
    out_of_memory = state["Result"] == "oom-kill"
    if state["LoadState"] == "loaded":
        subprocess.run(["systemctl", "--user", "reset-failed", f"{unit}.scope"], check=True)
    return status, out_of_memory


def pinned_commit(manifest):
    """The Verus commit the workspace manifest pins: its vstd dependency's git revision."""
    with open(manifest, "rb") as file:
        return tomllib.load(file)["workspace"]["dependencies"]["vstd"]["rev"]


def checkout_mismatch(manifest, checkout):
    """Why the Verus checkout is not the one the manifest pins, or None when it is."""
    pinned = pinned_commit(manifest)
    checked_out = subprocess.run(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], check=True, stdout=subprocess.PIPE, text=True
    ).stdout.strip()
    if checked_out == pinned:
        return None
    return f"{checkout} is at {checked_out}, but {manifest} pins {pinned}; run tools/setup-verus.sh"


def split_target(args):
    """The --target the script takes for itself, as a rustc triple or None, and the rest of args."""
    if args[:1] != ["--target"]:
        return None, args
    if len(args) < 2 or args[1] not in TARGETS:
        sys.exit(f"verify: --target takes one of: {', '.join(TARGETS)}")
    return TARGETS[args[1]], args[2:]


def target_env(triple):
    """rust_verify's environment: VERUS_ROOT names the vstd and verus_builtin built for the triple."""
    env = dict(os.environ)
    if triple is not None:
        root = Path(env["VERUS_ROOT"]).parent / triple
        if not (root / "vstd.vir").is_file():
            sys.exit(f"verify: no vstd for {triple} under {root}; run tools/setup-verus.sh")
        env["VERUS_ROOT"] = str(root)
    return env


def verus_out_dir(root=REPO, triple=None):
    """Where exported .vir and compiled dependency .rlib artifacts live for triple."""
    verus_out = root / "target" / "verus"
    return verus_out / triple if triple is not None else verus_out


def needed_deps(crates, targets):
    """Marked dependency package names reachable from targets."""
    by_package = {crate["package"]: crate for crate in crates}
    stack = [dep["package"] for crate in crates if crate["package"] in targets for dep in crate["deps"]]
    needed = set()
    while stack:
        package = stack.pop()
        if package in needed or package not in by_package:
            continue
        needed.add(package)
        stack.extend(dep["package"] for dep in by_package[package]["deps"])
    return needed


def crate_dir(src_path, root):
    """Root directory holding crate src_path (marked by Cargo.toml inside root)."""
    root = root.resolve()
    directory = Path(src_path).resolve().parent
    while directory != root and directory.parent != directory:
        if (directory / "Cargo.toml").is_file():
            return directory
        directory = directory.parent
    return Path(src_path).parent


def crate_inputs(src_path, root):
    """Files whose changes invalidate exported artifacts for the crate rooted at src_path."""
    base = crate_dir(src_path, root)
    inputs = [root / "Cargo.toml", root / "Cargo.lock", base / "Cargo.toml"]
    for dirpath, dirs, filenames in os.walk(base):
        dirs[:] = [d for d in dirs if d not in ("target", ".git", "throwaway", "refused")]
        for name in filenames:
            if name.endswith(".rs"):
                inputs.append(Path(dirpath) / name)
    return inputs


def stale_or_missing(outputs, inputs):
    """Whether any output is missing or older than an existing input."""
    if any(not path.exists() for path in outputs):
        return True
    oldest = min(path.stat().st_mtime for path in outputs)
    newest = max((path.stat().st_mtime for path in inputs if path.exists()), default=0)
    return newest > oldest


def prepare_deps(crates, targets, root=REPO, triple=None, checkout=VERUS):
    """Ensure plain and marked dependencies needed by targets are compiled/exported (--no-verify)."""
    target_set = set(targets)
    needed = needed_deps(crates, target_set)
    ordered = order_crates(crates)
    plain_deps = []
    seen_plain = set()
    for crate in ordered:
        if crate["package"] not in target_set and crate["package"] not in needed:
            continue
        for plain in crate["plain"]:
            if plain["crate"] not in seen_plain:
                seen_plain.add(plain["crate"])
                plain_deps.append(plain)
    verus_out = verus_out_dir(root, triple)
    if not needed and not plain_deps:
        return verus_out
    env = None

    def ready_env():
        nonlocal env
        if env is not None:
            return env
        mismatch = checkout_mismatch(root / "Cargo.toml", checkout)
        if mismatch is not None:
            sys.exit(f"verify: {mismatch}")
        env = target_env(triple)
        verus_out.mkdir(parents=True, exist_ok=True)
        return env

    for plain in plain_deps:
        output = verus_out / f"lib{plain['crate']}.rlib"
        dep_info = verus_out / f"{plain['crate']}.d"
        if not stale_or_missing([output], crate_inputs(plain["src"], root)):
            continue
        result = subprocess.run(
            plain_command(plain, triple, verus_out, dep_info=dep_info),
            cwd=root,
            env=ready_env(),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if result.returncode != 0:
            if result.stdout:
                print(result.stdout, end="", file=sys.stderr)
            sys.exit(result.returncode)

    for crate in ordered:
        if crate["package"] not in needed:
            continue
        outputs = [verus_out / f"{crate['crate']}.vir", verus_out / f"lib{crate['crate']}.rlib"]
        dep_outputs = [
            *(verus_out / f"{dep['crate']}.vir" for dep in crate["deps"]),
            *(verus_out / f"lib{dep['crate']}.rlib" for dep in crate["deps"]),
            *(verus_out / f"lib{plain['crate']}.rlib" for plain in crate["plain"]),
        ]
        if not stale_or_missing(outputs, crate_inputs(crate["src"], root) + dep_outputs):
            continue
        command = verify_command(crate, needed, triple, verus_out, ["--no-verify"],
                                 dep_info=verus_out / f"{crate['crate']}.d")
        unit = f"atmo-verify-deps-{os.getpid()}-{crate['crate']}"
        with tempfile.TemporaryFile(mode="w+") as log:
            returncode, out_of_memory = run_capped(
                command, unit, MEMORY_MAX, cwd=root, env=ready_env(),
                stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
            )
            if returncode != 0:
                log.seek(0)
                output = log.read()
                if output:
                    print(output, end="" if output.endswith("\n") else "\n", file=sys.stderr)
                if out_of_memory:
                    print(f"verify: {crate['package']} ran out of memory: its run is capped at {MEMORY_MAX}", file=sys.stderr)
                sys.exit(returncode)
    return verus_out


def main(args):
    triple, extra_args = split_target(args)
    mismatch = checkout_mismatch(REPO / "Cargo.toml", VERUS)
    if mismatch is not None:
        sys.exit(f"verify: {mismatch}")
    env = target_env(triple)
    verus_out = verus_out_dir(REPO, triple)
    crates = marked_crates(cargo_metadata())
    depended_on = {dep["package"] for crate in crates for dep in crate["deps"]}
    verus_out.mkdir(parents=True, exist_ok=True)
    failed = set()
    status = 0
    compiled = set()
    for crate in crates:
        for plain in crate["plain"]:
            if plain["crate"] not in compiled:
                subprocess.run(
                    plain_command(plain, triple, verus_out, dep_info=verus_out / f"{plain['crate']}.d"),
                    cwd=REPO, env=env, check=True,
                )
                compiled.add(plain["crate"])
        blocked = [dep for dep in crate["deps"] if dep["package"] in failed]
        if blocked:
            for dep in blocked:
                print(
                    f"verify: not verifying {crate['package']}: dependency {dep['package']} failed",
                    file=sys.stderr,
                )
            failed.add(crate["package"])
            continue
        command = verify_command(crate, depended_on, triple, verus_out, extra_args,
                                 dep_info=verus_out / f"{crate['crate']}.d")
        unit = f"atmo-verify-{os.getpid()}-{crate['crate']}"
        returncode, out_of_memory = run_capped(command, unit, MEMORY_MAX, cwd=REPO, env=env, stdin=subprocess.DEVNULL)
        if out_of_memory:
            print(f"verify: {crate['package']} ran out of memory: its run is capped at {MEMORY_MAX}", file=sys.stderr)
        if returncode != 0:
            failed.add(crate["package"])
            if status == 0:
                status = returncode
    return status


class Tests(unittest.TestCase):
    """The gate runs these with tools/verify.py --test before it verifies."""

    def git(self, checkout, *args):
        return subprocess.run(
            ["git", "-C", str(checkout), "-c", "user.name=test", "-c", "user.email=test@invalid", *args],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()

    def manifest(self, directory, rev):
        manifest = Path(directory) / "Cargo.toml"
        manifest.write_text(
            '[workspace]\nmembers = []\n\n[workspace.dependencies.vstd]\n'
            f'git = "https://github.com/verus-lang/verus"\nrev = "{rev}"\ndefault-features = false\n'
        )
        return manifest

    def package(self, name, verified=False, dependencies=()):
        return {
            "name": name,
            "edition": "2021",
            "metadata": {"atmosphere": {"verified": True}} if verified else None,
            "targets": [{"kind": ["lib"], "crate_types": ["lib"], "name": name, "src_path": f"/w/{name}/src/lib.rs"}],
            "dependencies": list(dependencies),
        }

    def dependency(self, name, path=True, kind=None):
        return {"name": name, "path": f"/w/{name}" if path else None, "kind": kind}

    def test_an_unmarked_member_is_a_plain_dependency_passed_without_import(self):
        metadata = {"packages": [
            self.package("asys"),
            self.package("aheap", verified=True),
            self.package("aeager", verified=True, dependencies=[
                self.dependency("aheap"), self.dependency("asys"), self.dependency("vstd", path=False),
                self.dependency("other", kind="dev"),
            ]),
            self.package("other"),
        ]}
        crates = {crate["package"]: crate for crate in marked_crates(metadata)}
        self.assertEqual([plain["crate"] for plain in crates["aeager"]["plain"]], ["asys"])
        self.assertEqual(crates["aheap"]["plain"], [])
        out = Path("/out")
        command = verify_command(crates["aeager"], set(), None, out, [])
        self.assertIn("asys=/out/libasys.rlib", command)
        self.assertIn("aheap=/out/libaheap.rlib", command)
        self.assertNotIn("asys=/out/asys.vir", command)
        self.assertIn("aheap=/out/aheap.vir", command)

    def test_a_crate_with_dependencies_searches_the_output_for_theirs(self):
        metadata = {"packages": [
            self.package("asys"),
            self.package("verified", verified=True),
            self.package("acall", verified=True, dependencies=[self.dependency("verified"), self.dependency("asys")]),
            self.package("aeager", verified=True, dependencies=[self.dependency("acall")]),
            self.package("aring", verified=True),
        ]}
        crates = {crate["package"]: crate for crate in marked_crates(metadata)}
        out = Path("/out")
        command = verify_command(crates["aeager"], {"acall", "verified"}, None, out, [])
        self.assertEqual(command[command.index("-L") + 1], "/out")
        self.assertNotIn("-L", verify_command(crates["aring"], {"acall", "verified"}, None, out, []))

    def test_a_plain_dependency_compiles_for_the_target(self):
        plain = {"extern": "asys", "crate": "asys", "src": "/w/asys/src/lib.rs", "edition": "2021"}
        host = plain_command(plain, None, Path("/out"))
        self.assertEqual(host[0], "rustc")
        self.assertNotIn("--target", host)
        self.assertEqual(host[-2:], ["--out-dir", "/out"])
        arm = plain_command(plain, "aarch64-unknown-none", Path("/out"))
        self.assertEqual(arm[arm.index("--target") + 1], "aarch64-unknown-none")

    def test_a_plain_dependency_with_dependencies_is_refused(self):
        metadata = {"packages": [
            self.package("astd", dependencies=[self.dependency("asys")]),
            self.package("asys"),
            self.package("aheap", verified=True, dependencies=[self.dependency("astd")]),
        ]}
        with self.assertRaises(SystemExit):
            marked_crates(metadata)

    def test_rust_verify_runs_in_its_own_scope_capped_at_16_gib_with_no_swap(self):
        command = capped(["rust_verify", "lib.rs"], "atmo-verify-1-verified", MEMORY_MAX)
        self.assertEqual(command[:3], ["systemd-run", "--user", "--scope"])
        self.assertIn("--unit=atmo-verify-1-verified", command)
        self.assertIn("MemoryMax=16G", command)
        self.assertIn("MemorySwapMax=0", command)
        self.assertEqual(command[-3:], ["--", "rust_verify", "lib.rs"])

    def test_a_run_within_its_cap_keeps_its_status_and_its_environment(self):
        unit = f"atmo-verify-test-{os.getpid()}-within"
        env = dict(os.environ, ATMO_VERIFY_PROBE="seen")
        probe = [sys.executable, "-c", "import os, sys; sys.exit(3 if os.environ['ATMO_VERIFY_PROBE'] == 'seen' else 4)"]
        self.assertEqual(run_capped(probe, unit, "64M", cwd=REPO, env=env), (3, False))

    def test_the_pin_is_the_workspace_vstd_revision(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(pinned_commit(self.manifest(directory, "0123abcd")), "0123abcd")

    def test_the_trees_manifest_pins_a_full_commit(self):
        self.assertRegex(pinned_commit(REPO / "Cargo.toml"), r"^[0-9a-f]{40}$")

    def test_every_crate_on_vstd_takes_the_workspace_pin(self):
        with_vstd = []
        for package in cargo_metadata()["packages"]:
            with open(package["manifest_path"], "rb") as manifest:
                vstd = tomllib.load(manifest).get("dependencies", {}).get("vstd")
            if vstd is not None:
                with_vstd.append(package["name"])
                self.assertEqual(vstd, {"workspace": True}, package["name"])
        self.assertIn("verified", with_vstd)

    def test_env_sh_and_this_script_read_the_one_checkout_outside_the_tree(self):
        """A build inside a tree would be one worktree's alone; every worktree's tools read this one."""
        self.assertNotIn(REPO, VERUS.parents)
        root = subprocess.run(
            ["bash", "-c", 'source "$1" && printf %s "$VERUS_ROOT"', "bash", str(REPO / "tools" / "env.sh")],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout
        self.assertEqual(Path(root), VERUS / "source" / "target-verus" / "release")

    def test_a_checkout_at_the_pin_passes_and_one_elsewhere_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory) / "verus"
            checkout.mkdir()
            self.git(checkout, "init", "--quiet")
            self.git(checkout, "commit", "--quiet", "--allow-empty", "-m", "pinned")
            pinned = self.git(checkout, "rev-parse", "HEAD")
            self.git(checkout, "commit", "--quiet", "--allow-empty", "-m", "later")
            later = self.git(checkout, "rev-parse", "HEAD")
            manifest = self.manifest(directory, pinned)
            refusal = checkout_mismatch(manifest, checkout)
            self.assertIsNotNone(refusal)
            self.assertIn(pinned, refusal)
            self.assertIn(later, refusal)
            self.git(checkout, "checkout", "--quiet", pinned)
            self.assertIsNone(checkout_mismatch(manifest, checkout))

    def test_needed_deps_walks_transitive_dependencies_without_adding_standalone_targets(self):
        crates = [
            {"package": "base", "crate": "base", "src": "base/lib.rs", "deps": [], "plain": []},
            {"package": "mid", "crate": "mid", "src": "mid/lib.rs",
             "deps": [{"extern": "base", "crate": "base", "package": "base"}], "plain": []},
            {"package": "top", "crate": "top", "src": "top/lib.rs",
             "deps": [{"extern": "mid", "crate": "mid", "package": "mid"}], "plain": []},
            {"package": "other", "crate": "other", "src": "other/lib.rs",
             "deps": [{"extern": "base", "crate": "base", "package": "base"}], "plain": []},
        ]
        self.assertEqual(needed_deps(crates, {"top", "other"}), {"base", "mid"})
        self.assertEqual(needed_deps(crates, {"base"}), set())

    def test_prepare_deps_skips_when_fresh_and_prepares_missing_or_stale_in_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.manifest(root, "deadbeef")
            for rel, content in [
                ("asys/Cargo.toml", "[package]\nname = \"asys\"\nversion = \"0.1.0\"\n"),
                ("asys/src/lib.rs", "pub fn noop() {}\n"),
                ("base/Cargo.toml", "[package]\nname = \"base\"\nversion = \"0.1.0\"\n"),
                ("base/src/lib.rs", "pub fn base() {}\n"),
                ("base/src/throwaway/w.rs", "fn witness() {}\n"),
                ("consumer/src/lib.rs", "pub fn use_base() {}\n"),
            ]:
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            plain_asys = {"extern": "asys", "crate": "asys", "src": str(root / "asys/src/lib.rs"), "edition": "2021"}
            crates = [
                {"package": "consumer", "crate": "consumer", "src": str(root / "consumer/src/lib.rs"),
                 "deps": [{"extern": "base", "crate": "base", "package": "base"}], "plain": []},
                {"package": "base", "crate": "base", "src": str(root / "base/src/lib.rs"),
                 "deps": [], "plain": [plain_asys]},
            ]
            verus_out = root / "target" / "verus"
            calls = []

            def fake_subprocess(cmd, **kwargs):
                calls.append(cmd)
                verus_out.mkdir(parents=True, exist_ok=True)
                (verus_out / "libasys.rlib").write_text("rlib")
                return subprocess.CompletedProcess(cmd, 0, stdout="")

            def fake_capped(cmd, unit, memory_max, **kwargs):
                calls.append(cmd)
                (verus_out / "base.vir").write_text("vir")
                (verus_out / "libbase.rlib").write_text("rlib")
                return 0, False

            with (mock.patch.object(sys.modules[__name__], "checkout_mismatch", return_value=None),
                  mock.patch.object(subprocess, "run", side_effect=fake_subprocess),
                  mock.patch.object(sys.modules[__name__], "run_capped", side_effect=fake_capped)):
                prepare_deps(crates, {"consumer"}, root=root)
                self.assertEqual(len(calls), 2)
                self.assertEqual(calls[0], plain_command(plain_asys, None, verus_out, dep_info=verus_out / "asys.d"))
                self.assertEqual(calls[1], verify_command(crates[1], {"base"}, None, verus_out, ["--no-verify"],
                                                          dep_info=verus_out / "base.d"))

                # Fresh artifacts are skipped without running rustc or rust_verify.
                calls.clear()
                prepare_deps(crates, {"consumer"}, root=root)
                self.assertEqual(calls, [])

                # Changes under throwaway/ do not invalidate dependencies.
                later = (verus_out / "base.vir").stat().st_mtime + 10
                os.utime(root / "base/src/throwaway/w.rs", (later, later))
                prepare_deps(crates, {"consumer"}, root=root)
                self.assertEqual(calls, [])

                # A newer source file in base rebuilds base only, not fresh plain deps.
                os.utime(root / "base/src/lib.rs", (later, later))
                prepare_deps(crates, {"consumer"}, root=root)
                self.assertEqual(len(calls), 1)
                self.assertEqual(calls[0], verify_command(crates[1], {"base"}, None, verus_out, ["--no-verify"],
                                                          dep_info=verus_out / "base.d"))

    def test_prepare_deps_reports_oom_and_checkout_mismatch(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.manifest(root, "deadbeef")
            (root / "base").mkdir()
            (root / "base/lib.rs").write_text("")
            (root / "consumer").mkdir()
            (root / "consumer/lib.rs").write_text("")
            crates = [
                {"package": "base", "crate": "base", "src": str(root / "base/lib.rs"), "deps": [], "plain": []},
                {"package": "consumer", "crate": "consumer", "src": str(root / "consumer/lib.rs"),
                 "deps": [{"extern": "base", "crate": "base", "package": "base"}], "plain": []},
            ]
            with mock.patch.object(sys.modules[__name__], "checkout_mismatch", return_value="wrong verus"):
                with self.assertRaises(SystemExit) as caught:
                    prepare_deps(crates, {"consumer"}, root=root)
                self.assertIn("wrong verus", str(caught.exception))

            def oom_capped(cmd, unit, memory_max, **kwargs):
                kwargs["stdout"].write("boom details\n")
                return -9, True

            stderr = StringIO()
            with (mock.patch.object(sys.modules[__name__], "checkout_mismatch", return_value=None),
                  mock.patch.object(sys.modules[__name__], "run_capped", side_effect=oom_capped),
                  redirect_stderr(stderr)):
                with self.assertRaises(SystemExit):
                    prepare_deps(crates, {"consumer"}, root=root)
            self.assertIn("ran out of memory", stderr.getvalue())
            self.assertIn("boom details", stderr.getvalue())

    def test_dep_info_adds_emit_flags_without_dropping_compile_output(self):
        plain = {"extern": "asys", "crate": "asys", "src": "/w/asys/src/lib.rs", "edition": "2021"}
        dep_path = Path("/out/asys.d")
        self.assertEqual(
            plain_command(plain, None, Path("/out"), dep_info=dep_path)[-2:],
            ["--emit=link", "--emit=dep-info=/out/asys.d"],
        )
        crate = {"package": "aheap", "crate": "aheap", "src": "/w/aheap/src/lib.rs", "deps": [], "plain": []}
        exported = verify_command(crate, {"aheap"}, None, Path("/out"), [], dep_info=Path("/out/aheap.d"))
        self.assertEqual(exported[-3:], ["--", "--emit=link", "--emit=dep-info=/out/aheap.d"])
        leaf = verify_command(crate, set(), None, Path("/out"), ["--", "--cfg", "x"], dep_info=Path("/out/aheap.d"))
        self.assertEqual(leaf.count("--"), 1)
        self.assertEqual(leaf[-3:], ["--cfg", "x", "--emit=dep-info=/out/aheap.d"])


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
