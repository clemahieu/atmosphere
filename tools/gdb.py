#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Attach gdb to a run started by tools/run.py --gdb, with the kernel's and dom0's symbols.

tools/run.py --gdb writes .gdb at the workspace root once the loader has logged where it loaded each
binary and waits for the debugger (aloader/src/debugger.rs): the loader, the run's gdb socket, and
each binary's ELF with the bias the loader added to its addresses. This script starts gdb on the
loader, connects to the socket, adds each binary's symbols at its bias, and sources
tools/gdb-helper.py, which lets the loader go on into the kernel and stops where the kernel calls
kernel::debugger::breakpoint. Then it continues the guest, unless --pause keeps it stopped in the
loader. Arguments after the options go to gdb before that continue.

usage: tools/gdb.py [--pause] [--] [gdb arguments...]   (from anywhere)
       tools/gdb.py --test                              (this script's own tests)
"""
import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
# What tools/run.py --gdb writes while its loader waits.
INFO = REPO / ".gdb"
HELPER = REPO / "tools" / "gdb-helper.py"
# gdb 18 asks whether to fetch debug info from the network for the loader; nothing there to fetch.
NO_DEBUGINFOD = ["-iex", "set debuginfod enabled off"]


def parse(argv):
    """Returns (pause, the arguments for gdb)."""
    pause = argv[:1] == ["--pause"]
    if pause:
        argv = argv[1:]
    if argv[:1] == ["--"]:
        argv = argv[1:]
    return pause, argv


def gdb_args(info, helper, pause, extra):
    """gdb's arguments for the connection info `info`, as tools/run.py writes it."""
    commands = [f"file {info['file']}", f"target remote {info['socket']}"]
    commands += [f"add-symbol-file {binary['path']} -o {binary['bias']:#x}" for binary in info["binaries"].values()]
    commands.append(f"source {helper}")
    args = ["-q"] + NO_DEBUGINFOD
    for command in commands:
        args += ["-ex", command]
    args += extra
    if not pause:
        args += ["-ex", "c"]
    return args


def main(argv):
    pause, extra = parse(argv)
    if not INFO.exists():
        print(f"tools/gdb.py: {INFO} does not exist; start a run with tools/run.py --gdb", file=sys.stderr)
        return 1
    args = gdb_args(json.loads(INFO.read_text()), HELPER, pause, extra)
    os.execvp("gdb", ["gdb"] + args)


class Tests(unittest.TestCase):
    INFO = {
        "file": "/t/aloader.efi",
        "socket": "/r/gdb.sock",
        "binaries": {"kernel": {"path": "/t/kernel", "bias": 0x14005f000},
                     "dom0": {"path": "/t/dom0", "bias": 0x8000000000}},
    }

    def commands(self, args):
        return [args[i + 1] for i, arg in enumerate(args) if arg == "-ex"]

    def test_attaches_to_the_loader_on_the_socket(self):
        commands = self.commands(gdb_args(self.INFO, Path("/w/helper.py"), False, []))
        self.assertEqual(commands[:2], ["file /t/aloader.efi", "target remote /r/gdb.sock"])

    def test_adds_each_binary_at_its_bias_before_the_helper(self):
        commands = self.commands(gdb_args(self.INFO, Path("/w/helper.py"), False, []))
        helper = commands.index("source /w/helper.py")
        self.assertEqual(sorted(commands[2:helper]), ["add-symbol-file /t/dom0 -o 0x8000000000",
                                                      "add-symbol-file /t/kernel -o 0x14005f000"])

    def test_continues_after_the_extra_arguments(self):
        args = gdb_args(self.INFO, Path("/w/helper.py"), False, ["-batch", "-ex", "break kernel::boot_cpu0"])
        self.assertEqual(args[-6:], ["source /w/helper.py", "-batch", "-ex", "break kernel::boot_cpu0", "-ex", "c"])

    def test_pause_stays_in_the_loader(self):
        args = gdb_args(self.INFO, Path("/w/helper.py"), True, ["-batch"])
        self.assertEqual(args[-3:], ["-ex", "source /w/helper.py", "-batch"])

    def test_debuginfod_is_off_before_the_loader_is_read(self):
        args = gdb_args(self.INFO, Path("/w/helper.py"), False, [])
        self.assertEqual(args[:3], ["-q"] + NO_DEBUGINFOD)

    def test_parse_takes_pause_and_passes_the_rest_to_gdb(self):
        self.assertEqual(parse([]), (False, []))
        self.assertEqual(parse(["--pause"]), (True, []))
        self.assertEqual(parse(["--pause", "--", "-batch", "--pause"]), (True, ["-batch", "--pause"]))
        self.assertEqual(parse(["-batch", "-ex", "bt"]), (False, ["-batch", "-ex", "bt"]))
        self.assertEqual(parse(["--", "--pause"]), (False, ["--pause"]))

    def test_reads_what_run_py_writes(self):
        spec = importlib.util.spec_from_file_location("run", REPO / "tools" / "run.py")
        run = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(run)
        info = run.gdb_info(Path("/t/aloader.efi"), {"kernel": Path("/t/kernel"), "dom0": Path("/t/dom0")},
                            {"kernel": 0x14005f000, "dom0": 0x8000000000}, Path("/r/gdb.sock"))
        self.assertEqual(gdb_args(json.loads(json.dumps(info)), Path("/w/helper.py"), False, []),
                         gdb_args(self.INFO, Path("/w/helper.py"), False, []))

    def test_the_helper_is_in_the_tree(self):
        self.assertTrue(HELPER.is_file())


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    else:
        sys.exit(main(sys.argv[1:]))
