#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Build the workspace as the gate does, or the loader, kernel, dom0 and payload for aarch64.

x86_64, the default, is the gate's build: `cargo build` in every workspace member's own directory,
since each no_std crate takes its target from its own .cargo config and a member built only as
another's dependency, or not at all, could otherwise stop building unseen; then the loader, the
kernel with lock_stats (the measuring build, which no boot here runs, so that it cannot rot unseen),
the kernel, dom0 and the payload from their own directories. aarch64 builds the loader as an EFI
application for aarch64-unknown-uefi and the kernel, dom0 and the payload against their aarch64 JSON
specs, then holds each image to file(1): an aarch64 EFI application for the loader, an aarch64
static-pie ELF for the rest, the only kind the loader places. Each kernel, dom0 and payload ELF
passes tools/check-stack-sizes.py; the loader is PE, which that check does not read.

The last line on stdout is `build <target>: <what was built>`, the file(1) line of each image for
aarch64; a failure exits 1 with `tools/build.py: <what failed>` as that line. Everything else, cargo's
and the stack check's output among it, goes to stderr.

usage: tools/build.py [--target x86_64|aarch64]   (from anywhere)
       tools/build.py --test                      (this script's own tests)
"""
import argparse
import json
import os
import subprocess
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

TREE = Path(__file__).resolve().parent.parent
STACK_SIZES_CHECK = TREE / "tools/check-stack-sizes.py"
# The payload tools/run.py loads, and the user program that links asys.
PAYLOAD = "hello"
# The triple the aarch64 loader is built for, one rustc has built in; aloader's own config names the
# x86_64 one.
LOADER_AARCH64_TARGET = "aarch64-unknown-uefi"
# The ELFs the aarch64 build makes, each with its target spec.
AARCH64_ELF_SPECS = [
    ("kernel", "kernel/src/aarch64-unknown-aloader.json"),
    ("dom0", "dom0/src/aarch64-unknown-aloader.json"),
    (PAYLOAD, "user/aarch64-unknown-aloader.json"),
]
# The crates' .cargo configs use -Z flags and an [unstable] table, and a JSON target spec on the
# command line needs the bootstrap env on a stable compiler too.
CARGO_ENV = {**os.environ, "RUSTC_BOOTSTRAP": "1"}

ELF = "ELF"
EFI_APPLICATION = "EFI application"


class BuildError(Exception):
    pass


def crate_dir(name):
    """The directory a crate builds from: the loader, the kernel and dom0 at the root, a user program under user/."""
    return {"aloader": "aloader", "kernel": "kernel", "dom0": "dom0"}.get(name, f"user/{name}")


def cargo_args(features=(), target=None):
    """cargo's arguments for the build of one crate with these features, for `target` when given."""
    args = ["cargo", "build", "--message-format=json-render-diagnostics"]
    if features:
        args += ["--features", ",".join(features)]
    if target is not None:
        args += ["-Zjson-target-spec", "--target", str(target)]
    return args


def executable(messages, name):
    """The executable cargo's JSON messages name for the target `name`, or None."""
    for line in messages.splitlines():
        message = json.loads(line)
        if (message.get("reason") == "compiler-artifact" and message["target"]["name"] == name
                and message.get("executable")):
            return Path(message["executable"])
    return None


def build(name, features=(), target=None):
    """Builds a crate from its own directory, so its .cargo config applies, checks the stack frames of an
    ELF it makes, and returns its executable."""
    result = subprocess.run(cargo_args(features, target), cwd=TREE / crate_dir(name), env=CARGO_ENV,
                            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, text=True)
    what = name + "".join(f" with {feature}" for feature in features)
    if result.returncode != 0:
        raise BuildError(f"{what}: cargo build exited with {result.returncode}")
    path = executable(result.stdout, name)
    if path is None:
        raise BuildError(f"{what}: cargo build produced no executable {name}")
    if name != "aloader":
        checked = subprocess.run([str(STACK_SIZES_CHECK), str(path)], stdin=subprocess.DEVNULL, stdout=sys.stderr)
        if checked.returncode != 0:
            raise BuildError(f"{STACK_SIZES_CHECK.relative_to(TREE)} {path}: exit {checked.returncode}")
    return path


def member_dirs(metadata):
    """The directory of each workspace member, from `cargo metadata --no-deps`'s JSON."""
    return [(package["name"], Path(package["manifest_path"]).parent) for package in json.loads(metadata)["packages"]]


def build_members():
    """Builds every workspace member from its own directory and returns how many there are."""
    metadata = subprocess.run(["cargo", "metadata", "--no-deps", "--format-version", "1"], cwd=TREE,
                              stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, text=True, check=True).stdout
    members = member_dirs(metadata)
    failed = [name for name, directory in members
              if subprocess.run(["cargo", "build"], cwd=directory, stdin=subprocess.DEVNULL,
                                stdout=sys.stderr).returncode != 0]
    if failed:
        raise BuildError(f"from its own directory, does not build: {', '.join(failed)}")
    return len(members)


def x86_64_build():
    members = build_members()
    build("aloader")
    build("kernel", ["lock_stats"])
    build("kernel")
    build("dom0")
    build(PAYLOAD)
    return (f"{members} workspace members, then the loader, kernel, dom0 and payload from their own directories; "
            "no stack frame over 16 MiB in the kernel, dom0 or payload")


def describes(image, description):
    """Whether file(1)'s line for an image says it is an aarch64 image of this kind."""
    if image == ELF:
        return ("ELF 64-bit" in description and "pie executable, ARM aarch64" in description
                and "static-pie linked" in description)
    return "PE32+ executable for EFI (application), ARM64" in description


def aarch64_build():
    images = [(build("aloader", target=LOADER_AARCH64_TARGET), EFI_APPLICATION)]
    images += [(build(name, target=TREE / spec), ELF) for name, spec in AARCH64_ELF_SPECS]
    lines = []
    for path, image in images:
        file = subprocess.run(["file", str(path)], stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, text=True)
        if file.returncode != 0:
            raise BuildError(f"file {path}: exit {file.returncode}")
        line = file.stdout.strip()
        if not describes(image, line):
            raise BuildError(f"{path} is not an aarch64 {image}: {line}")
        lines.append(line)
    return "; ".join(lines)


def relocation(spec):
    """A spec's lines that decide whether its executable can be placed at any address: the relocation
    model the compiler generates code for, and the linker's own flag for the image."""
    return [line.strip() for line in spec.splitlines() if "relocation-model" in line or "-pie" in line]


def parser():
    parser = argparse.ArgumentParser(prog="tools/build.py", description=__doc__.split("\n")[0])
    parser.add_argument("--target", choices=["x86_64", "aarch64"], default="x86_64",
                        help="x86_64, the gate's build, or aarch64, the images the board boots")
    return parser


class Tests(unittest.TestCase):
    def spec_text(self, path):
        return (TREE / path).read_text()

    def test_the_aarch64_build_lists_the_kernel_with_dom0_and_the_payload(self):
        """The aarch64 build makes the kernel, then dom0 and the user program, each from the spec beside its
        x86 one."""
        self.assertEqual(AARCH64_ELF_SPECS, [
            ("kernel", "kernel/src/aarch64-unknown-aloader.json"),
            ("dom0", "dom0/src/aarch64-unknown-aloader.json"),
            ("hello", "user/aarch64-unknown-aloader.json"),
        ])
        self.assertEqual([crate_dir(name) for name, _ in AARCH64_ELF_SPECS], ["kernel", "dom0", "user/hello"])

    def test_aarch64_specs_have_the_x86_specs_role(self):
        """The aarch64 spec beside each x86 spec: no OS, no red zone, soft float, panic abort, and the x86
        spec's relocation model, a static position-independent executable, which is the only kind the
        loader places (aelf's `NotRelocatable`)."""
        for _, path in AARCH64_ELF_SPECS:
            text = self.spec_text(path)
            for needle in ['"arch": "aarch64"', '"os": "none"', '"disable-redzone": true', '"abi": "softfloat"',
                           '"rustc-abi": "softfloat"', '"panic-strategy": "abort"']:
                self.assertIn(needle, text, path)
            x86_path = path.replace("aarch64", "x86_64")
            x86 = self.spec_text(x86_path)
            self.assertEqual(relocation(x86), ['"relocation-model": "pie",', '"-pie",'], x86_path)
            self.assertEqual(relocation(text), relocation(x86), f"{path} against {x86_path}")

    # file(1)'s line for each image the aarch64 build makes, and for the x86_64 ones beside them.
    AARCH64_ELF = ("dom0: ELF 64-bit LSB pie executable, ARM aarch64, version 1 (SYSV), static-pie linked, "
                   "with debug_info, not stripped")
    # The same image linked at a fixed address, which the loader refuses.
    AARCH64_FIXED_ELF = ("dom0: ELF 64-bit LSB executable, ARM aarch64, version 1 (SYSV), statically linked, "
                         "with debug_info, not stripped")
    X86_64_ELF = ("dom0: ELF 64-bit LSB pie executable, x86-64, version 1 (SYSV), static-pie linked, "
                  "with debug_info, not stripped")
    AARCH64_EFI = "aloader.efi: PE32+ executable for EFI (application), ARM64, 4 sections"
    X86_64_EFI = "aloader.efi: PE32+ executable for EFI (application), x86-64, 5 sections"

    def test_an_aarch64_image_is_told_from_an_x86_64_one_and_an_elf_from_an_efi_application(self):
        self.assertTrue(describes(ELF, self.AARCH64_ELF))
        self.assertTrue(describes(EFI_APPLICATION, self.AARCH64_EFI))
        for other in [self.AARCH64_FIXED_ELF, self.X86_64_ELF, self.AARCH64_EFI, self.X86_64_EFI]:
            self.assertFalse(describes(ELF, other), other)
        for other in [self.AARCH64_ELF, self.X86_64_ELF, self.X86_64_EFI]:
            self.assertFalse(describes(EFI_APPLICATION, other), other)
        # An EFI image of another kind is not one the firmware starts as an application.
        self.assertFalse(describes(EFI_APPLICATION,
                                   "driver.efi: PE32+ executable for EFI (boot service driver), ARM64, 4 sections"))

    def test_build_defaults_to_x86_64(self):
        self.assertEqual(parser().parse_args([]).target, "x86_64")
        self.assertEqual(parser().parse_args(["--target", "aarch64"]).target, "aarch64")
        with self.assertRaises(SystemExit):
            parser().parse_args(["--target", "riscv64"])

    def test_each_workspace_member_builds_from_the_directory_of_its_manifest(self):
        metadata = json.dumps({"packages": [
            {"name": "kernel", "manifest_path": "/w/kernel/Cargo.toml"},
            {"name": "hello", "manifest_path": "/w/user/hello/Cargo.toml"},
        ]})
        self.assertEqual(member_dirs(metadata), [("kernel", Path("/w/kernel")), ("hello", Path("/w/user/hello"))])

    def test_a_target_is_a_json_spec_or_a_triple_on_the_command_line(self):
        self.assertEqual(cargo_args(), ["cargo", "build", "--message-format=json-render-diagnostics"])
        self.assertEqual(cargo_args(["lock_stats"])[3:], ["--features", "lock_stats"])
        self.assertEqual(cargo_args(target="aarch64-unknown-uefi")[3:],
                         ["-Zjson-target-spec", "--target", "aarch64-unknown-uefi"])

    def test_the_executable_is_the_artifact_of_the_crate_s_own_target(self):
        messages = "\n".join(json.dumps(message) for message in [
            {"reason": "compiler-artifact", "target": {"name": "aelf"}, "executable": None},
            {"reason": "compiler-artifact", "target": {"name": "dom0"}, "executable": "/w/target/dom0"},
            {"reason": "build-finished", "success": True},
        ])
        self.assertEqual(executable(messages, "dom0"), Path("/w/target/dom0"))
        self.assertIsNone(executable(messages, "kernel"))


def main(argv):
    if argv == ["--test"]:
        return unittest.main(argv=[sys.argv[0]])
    target = parser().parse_args(argv).target
    try:
        detail = x86_64_build() if target == "x86_64" else aarch64_build()
    except BuildError as error:
        print(f"tools/build.py: {error}")
        return 1
    print(f"build {target}: {detail}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
