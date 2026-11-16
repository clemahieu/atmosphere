#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""The environment Verus and the kernel crates build in, derived from where this tree is.

Verus is the build tools/setup-verus.sh makes under verus at the project root, the parent of
this tree, beside the worktrees and in no tree. From it: VERUS_ROOT, the release directory that
holds rust_verify, vstd and verus_builtin; VERUS_Z3_PATH, the z3 beside its source; and
rust_verify on PATH. The Verus binaries link to the sysroot of the Rust that rust-toolchain.toml
pins, which `rustc --print sysroot` in the tree names, so its lib goes on LD_LIBRARY_PATH. The
kernel crates use unstable features on that nightly, so RUSTC_BOOTSTRAP is 1.

There is one place to look and no search: when rust_verify, z3 or vstd.vir is not where the
derivation says, the tool stops at once, naming the path and tools/setup-verus.sh.

gate.py, verify.py, check-refused.py and check-throwaways.py call apply() before anything else,
so they and land.py, which runs the gate, need nothing set beforehand. tools/env.sh evals this
script's output for a shell that runs cargo or rust_verify by hand.

usage: tools/toolchain.py          (the environment as shell exports; exit 1 when Verus is missing)
       tools/toolchain.py --test   (this script's own tests)
"""
import os
import shlex
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TREE = Path(__file__).resolve().parent.parent
VERUS = TREE.parent / "verus"


def sysroot(tree=TREE):
    """The sysroot of the Rust that the tree's rust-toolchain.toml pins."""
    return Path(subprocess.run(["rustc", "--print", "sysroot"], cwd=tree, check=True,
                               stdout=subprocess.PIPE, text=True).stdout.strip())


def environment(base, verus=VERUS, rust=None):
    """`base` with the toolchain's variables set. Exits naming what is missing when the Verus build
    is not under `verus`. `rust` is the sysroot, asked of rustc when not given."""
    source = verus / "source"
    release = source / "target-verus" / "release"
    for needed in (release / "rust_verify", source / "z3", release / "vstd.vir"):
        if not needed.is_file():
            sys.exit(f"toolchain: no Verus build at {verus}: {needed} is missing; run tools/setup-verus.sh")
    rust = sysroot() if rust is None else rust
    joined = lambda first, rest: f"{first}:{rest}" if rest else str(first)
    return {
        **base,
        "VERUS_ROOT": str(release),
        "VERUS_Z3_PATH": str(source / "z3"),
        "LD_LIBRARY_PATH": joined(rust / "lib", base.get("LD_LIBRARY_PATH")),
        "RUSTC_BOOTSTRAP": "1",
        "PATH": joined(release, base.get("PATH")),
    }


def apply():
    """Set the toolchain's variables in this process, so every child it starts has them."""
    os.environ.update(environment(os.environ))


NAMES = ("VERUS_ROOT", "VERUS_Z3_PATH", "LD_LIBRARY_PATH", "RUSTC_BOOTSTRAP", "PATH")


def main():
    found = environment(os.environ)
    print("\n".join(f"export {name}={shlex.quote(found[name])}" for name in NAMES))
    return 0


class Tests(unittest.TestCase):
    def setUp(self):
        made = tempfile.TemporaryDirectory()
        self.addCleanup(made.cleanup)
        self.verus = Path(made.name) / "verus"
        self.release = self.verus / "source" / "target-verus" / "release"
        self.release.mkdir(parents=True)
        for built in (self.release / "rust_verify", self.verus / "source" / "z3", self.release / "vstd.vir"):
            built.write_text("")
        self.rust = Path(made.name) / "sysroot"

    def test_the_variables_come_from_the_verus_build_and_the_pinned_sysroot(self):
        found = environment({"PATH": "/usr/bin", "HOME": "/h"}, self.verus, self.rust)
        self.assertEqual(found, {
            "PATH": f"{self.release}:/usr/bin",
            "HOME": "/h",
            "VERUS_ROOT": str(self.release),
            "VERUS_Z3_PATH": str(self.verus / "source" / "z3"),
            "LD_LIBRARY_PATH": str(self.rust / "lib"),
            "RUSTC_BOOTSTRAP": "1",
        })
        self.assertEqual(environment({"LD_LIBRARY_PATH": "/x"}, self.verus, self.rust)["LD_LIBRARY_PATH"], f"{self.rust / 'lib'}:/x")

    def test_a_missing_build_stops_at_once_naming_the_path_and_the_setup(self):
        for missing in (self.release / "rust_verify", self.verus / "source" / "z3", self.release / "vstd.vir"):
            missing.unlink()
            with self.assertRaises(SystemExit) as stopped:
                environment({}, self.verus, self.rust)
            self.assertEqual(str(stopped.exception), f"toolchain: no Verus build at {self.verus}: {missing} is missing; run tools/setup-verus.sh")
            missing.write_text("")

    def test_the_verus_looked_for_is_the_one_at_the_project_root_outside_the_tree(self):
        self.assertEqual(VERUS, TREE.parent / "verus")
        self.assertNotIn(TREE, VERUS.parents)

    def test_env_sh_in_a_shell_with_none_of_the_variables_sets_them_as_the_tools_do(self):
        bare = {key: value for key, value in os.environ.items() if key not in NAMES}
        bare["PATH"] = os.environ["PATH"]
        shown = subprocess.run(["bash", "-c", 'source "$1" && env -0', "bash", str(TREE / "tools" / "env.sh")],
                               env=bare, check=True, stdout=subprocess.PIPE, text=True).stdout
        got = dict(line.split("=", 1) for line in shown.split("\0") if line)
        wanted = environment(bare)
        for name in NAMES:
            self.assertEqual(got[name], wanted[name], name)

    def test_apply_gives_a_child_the_variables_its_parent_lacked(self):
        bare = {key: value for key, value in os.environ.items() if key not in NAMES[:-2]}
        probe = "import os, sys; sys.path.insert(0, sys.argv[1]); import toolchain; toolchain.apply(); os.execvp('sh', ['sh', '-c', 'printf %s \"$VERUS_ROOT\"'])"
        shown = subprocess.run([sys.executable, "-c", probe, str(TREE / "tools")], env=bare, check=True,
                               stdout=subprocess.PIPE, text=True).stdout
        self.assertEqual(shown, str(VERUS / "source" / "target-verus" / "release"))


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    sys.exit(main())
