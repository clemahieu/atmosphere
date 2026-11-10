#!/usr/bin/env python3
"""Verify the crates marked for verification with Verus.

A crate is marked by '[package.metadata.atmosphere] verified = true' in its Cargo.toml. Each marked
crate's library root goes to rust_verify as a lib crate, with a solver budget of --rlimit 100
(slinkedlist::remove_helper7 needs more than the default). Extra arguments go to rust_verify after
those, for every crate. Marked crates run in dependency order. A marked crate that another marked
crate depends on is also passed --crate-name, --export target/verus/<crate>.vir and --compile,
which writes lib<crate>.rlib under target/verus/. A marked crate with marked dependencies is passed --extern and --import
for each of them. A crate that no marked crate depends on, and that itself depends on no marked
crate, is invoked as before. rust_verify prints one 'verification results:: N verified, M errors'
line per crate. The script exits 0 when every crate verifies, and otherwise with the first failing
crate's status. A dependency that failed verification is not followed by its dependents, and the
script names both.

With --target aarch64 every crate is checked under target_arch = "aarch64": rust_verify gets
--target aarch64-unknown-none and takes vstd and verus_builtin from the aarch64 build that
tools/setup-verus.sh writes beside the host one, and the shared crates' rlibs go under
target/verus/aarch64-unknown-none/. With no --target the crates are checked for the host, x86_64.
design/arch-module/ says why one run per target.

It first checks that tools/verus is checked out at the Verus commit the workspace Cargo.toml pins as
vstd's revision, and exits naming both commits when it is not, since the crates would otherwise be
checked by a Verus other than the one their vstd comes from.

Expects tools/env.sh to be sourced, which puts rust_verify on PATH.

usage: tools/verify.py [--target aarch64] [rust_verify argument...]
       tools/verify.py --test    (this script's own tests)
"""
import json
import os
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# The rustc target each --target names. tools/setup-verus.sh builds vstd and verus_builtin for each
# under tools/verus/source/target-verus/<triple>.
TARGETS = {"aarch64": "aarch64-unknown-none"}


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
    """Library crates marked for verification, in metadata order, with marked dependencies."""
    crates = []
    by_package = {}
    for package in metadata["packages"]:
        atmosphere = (package.get("metadata") or {}).get("atmosphere") or {}
        if not atmosphere.get("verified", False):
            continue
        libs = [t for t in package["targets"] if t["kind"] == ["lib"] and t["crate_types"] == ["lib"]]
        if not libs:
            sys.exit(f"verify: package {package['name']} is marked verified but has no lib crate")
        lib = libs[0]
        crate = {
            "package": package["name"],
            "crate": lib["name"].replace("-", "_"),
            "src": lib["src_path"],
            "deps": [],
        }
        crates.append(crate)
        by_package[package["name"]] = crate
    for package in metadata["packages"]:
        crate = by_package.get(package["name"])
        if crate is None:
            continue
        seen = set()
        for dep in package.get("dependencies") or []:
            if dep.get("kind") in ("dev", "build"):
                continue
            dep_crate = by_package.get(dep["name"])
            if dep_crate is None or dep_crate["package"] in seen:
                continue
            seen.add(dep_crate["package"])
            extern = dep.get("rename") or dep_crate["crate"]
            crate["deps"].append({"extern": extern, "crate": dep_crate["crate"], "package": dep_crate["package"]})
    return order_crates(crates)


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


def verify_command(crate, depended_on, triple, verus_out, extra_args):
    command = ["rust_verify", "--crate-type", "lib", crate["src"], "--rlimit", "100"]
    if triple is not None:
        command += ["--target", triple]
    for dep in crate["deps"]:
        rlib = verus_out / f"lib{dep['crate']}.rlib"
        vir = verus_out / f"{dep['crate']}.vir"
        command += ["--extern", f"{dep['extern']}={rlib}", "--import", f"{dep['extern']}={vir}"]
    if crate["package"] in depended_on:
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
    return command


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


def main(args):
    triple, extra_args = split_target(args)
    mismatch = checkout_mismatch(REPO / "Cargo.toml", REPO / "tools" / "verus")
    if mismatch is not None:
        sys.exit(f"verify: {mismatch}")
    env = target_env(triple)
    verus_out = REPO / "target" / "verus"
    if triple is not None:
        verus_out = verus_out / triple
    crates = marked_crates(cargo_metadata())
    depended_on = {dep["package"] for crate in crates for dep in crate["deps"]}
    if depended_on:
        verus_out.mkdir(parents=True, exist_ok=True)
    failed = set()
    status = 0
    for crate in crates:
        blocked = [dep for dep in crate["deps"] if dep["package"] in failed]
        if blocked:
            for dep in blocked:
                print(
                    f"verify: not verifying {crate['package']}: dependency {dep['package']} failed",
                    file=sys.stderr,
                )
            failed.add(crate["package"])
            continue
        command = verify_command(crate, depended_on, triple, verus_out, extra_args)
        result = subprocess.run(command, cwd=REPO, env=env, stdin=subprocess.DEVNULL)
        if result.returncode != 0:
            failed.add(crate["package"])
            if status == 0:
                status = result.returncode
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


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main(sys.argv[1:]))
