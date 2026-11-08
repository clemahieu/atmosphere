#!/usr/bin/env python3
"""Verify the crates marked for verification with Verus.

A crate is marked by '[package.metadata.atmosphere] verified = true' in its Cargo.toml. Each marked
crate's library root goes to rust_verify as a lib crate, with a solver budget of --rlimit 100
(slinkedlist::remove_helper7 needs more than the default). Extra arguments go to rust_verify after
those, for every crate. rust_verify prints one 'verification results:: N verified, M errors' line
per crate. The script exits 0 when every crate verifies, and otherwise with the first failing
crate's status.

Expects tools/env.sh to be sourced, which puts rust_verify on PATH.

usage: tools/verify.py [rust_verify argument...]
"""
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def verified_crates():
    """Returns the library roots of the workspace's crates marked for verification."""
    metadata = json.loads(
        subprocess.run(
            ["cargo", "metadata", "--no-deps", "--format-version", "1"],
            cwd=REPO,
            check=True,
            stdout=subprocess.PIPE,
        ).stdout
    )
    roots = []
    for package in metadata["packages"]:
        atmosphere = (package.get("metadata") or {}).get("atmosphere") or {}
        if not atmosphere.get("verified", False):
            continue
        libs = [t for t in package["targets"] if t["kind"] == ["lib"] and t["crate_types"] == ["lib"]]
        if not libs:
            sys.exit(f"verify: package {package['name']} is marked verified but has no lib crate")
        roots.append(libs[0]["src_path"])
    return roots


def main(extra_args):
    status = 0
    for root in verified_crates():
        command = ["rust_verify", "--crate-type", "lib", root, "--rlimit", "100", *extra_args]
        result = subprocess.run(command, cwd=REPO, stdin=subprocess.DEVNULL)
        if status == 0:
            status = result.returncode
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
