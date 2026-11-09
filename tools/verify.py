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

Expects tools/env.sh to be sourced, which puts rust_verify on PATH.

usage: tools/verify.py [rust_verify argument...]
"""
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
VERUS_OUT = REPO / "target" / "verus"


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


def verify_command(crate, depended_on, extra_args):
    command = ["rust_verify", "--crate-type", "lib", crate["src"], "--rlimit", "100"]
    for dep in crate["deps"]:
        rlib = VERUS_OUT / f"lib{dep['crate']}.rlib"
        vir = VERUS_OUT / f"{dep['crate']}.vir"
        command += ["--extern", f"{dep['extern']}={rlib}", "--import", f"{dep['extern']}={vir}"]
    if crate["package"] in depended_on:
        # lib.rs would otherwise compile as crate `lib`, and the rlib name follows the crate name.
        command += [
            "--crate-name",
            crate["crate"],
            "--export",
            str(VERUS_OUT / f"{crate['crate']}.vir"),
            "--compile",
            "--out-dir",
            str(VERUS_OUT),
        ]
    command += extra_args
    return command


def main(extra_args):
    crates = marked_crates(cargo_metadata())
    depended_on = {dep["package"] for crate in crates for dep in crate["deps"]}
    if depended_on:
        VERUS_OUT.mkdir(parents=True, exist_ok=True)
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
        result = subprocess.run(verify_command(crate, depended_on, extra_args), cwd=REPO, stdin=subprocess.DEVNULL)
        if result.returncode != 0:
            failed.add(crate["package"])
            if status == 0:
                status = result.returncode
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
