#!/usr/bin/env python3
"""Build the loader, kernel, dom0 and payload, and boot them under QEMU on OVMF.

OVMF boots the loader, the UEFI application, from a directory QEMU serves as the EFI system
partition; the loader reads the kernel, dom0 and payload ELF images concatenated in the file initrd
beside it (aloader/src/boot/uefi.rs). The serial log is serial.log at the workspace root. KVM is used
whenever /dev/kvm is writable; --no-kvm forces TCG. --iommu adds QEMU's emulated IOMMU. --gdb puts
a gdb server on the guest and the file gdb on the ESP, which makes the loader wait before it enters
the kernel (aloader/src/debugger.rs); once the loader has logged where it loaded each binary and that
it waits, .gdb at the workspace root holds what tools/gdb.py attaches with.

The firmware's output on the terminal ends with control sequences that reset it, so everything
before the loader's banner is dropped there; serial.log keeps it.

Exit status: 0 when dom0 reports success or the guest shuts down; otherwise QEMU's: 1 when the
kernel fails, 5 when an invocation of dom0's returns a status it did not expect, 7 when dom0
panics. 1 when QEMU dies by a signal, and 1 when a build fails.

usage: tools/run.py [--no-kvm] [--iommu] [--gdb]   (from anywhere)
       tools/run.py --test                         (this script's own tests)
"""
import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest
from io import BytesIO
from pathlib import Path

sys.dont_write_bytecode = True
# importlib loading does not put this file's directory on the path.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import firmware

REPO = Path(__file__).resolve().parent.parent
# Where OVMF looks for an application on removable media, and where the loader looks for the initrd.
ESP_LOADER = "EFI/BOOT/BOOTX64.EFI"
ESP_INITRD = "initrd"
# Whose presence on the ESP makes the loader wait for gdb (aloader/src/boot/uefi.rs).
ESP_GDB = "gdb"
# What the loader logs of each binary it loads, and before it waits for gdb (aloader/src/debugger.rs).
DEBUGGER_BIAS = re.compile(rb"debugger: (\w+) at bias (0x[0-9a-f]+)")
DEBUGGER_WAITING = b"debugger: waiting"
# dom0 ends the run by writing to this port (dom0/src/main.rs).
DEBUG_EXIT_PORT = 0xf4
# isa-debug-exit makes QEMU exit with `code << 1 | 1`, and dom0 writes 0x10 on success.
DOM0_SUCCESS_STATUS = 33
# Guest RAM, in MiB. The minimum machine the gate, the boot-stack check, the pinned
# measurement and the syscall benchmark boot. design/test-guest-memory/.
MEMORY_MIB = 512
# The only program under user/, which the loader hands dom0.
PAYLOAD = "hello"
# What the loader prints first: its name, then a clear screen and the cursor home
# (aloader/src/console/mod.rs).
LOADER_MARKER = b"ALOADER\x1b[2J\x1b[0;0H"
# Each crate's .cargo config uses -Z flags and an [unstable] table; the configs' [env] reaches only
# rustc, so cargo needs it too.
CARGO_ENV = {**os.environ, "RUSTC_BOOTSTRAP": "1"}


def build(crate_dir, name):
    """Builds a crate from its own directory, so its .cargo config applies, and returns its executable."""
    args = ["cargo", "build", "--message-format=json-render-diagnostics"]
    result = subprocess.run(args, cwd=REPO / crate_dir, env=CARGO_ENV, stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, text=True)
    if result.returncode != 0:
        sys.exit(f"tools/run.py: building {crate_dir} failed with status {result.returncode}")
    path = executable(result.stdout, name)
    if path is None:
        sys.exit(f"tools/run.py: building {crate_dir} produced no executable {name}")
    return path


def executable(messages, name):
    """The executable cargo's JSON messages name for the target `name`, or None."""
    for line in messages.splitlines():
        message = json.loads(line)
        if (message.get("reason") == "compiler-artifact" and message["target"]["name"] == name
                and message.get("executable")):
            return Path(message["executable"])
    return None


def use_kvm(no_kvm, device):
    """Whether to pass -enable-kvm: unless told not to, whenever QEMU could open the device."""
    if no_kvm:
        return False
    try:
        os.close(os.open(device, os.O_RDWR))
    except OSError:
        return False
    return True


def exit_status(returncode):
    """This script's exit status for QEMU's; a negative returncode is a signal."""
    if returncode in (0, DOM0_SUCCESS_STATUS):
        return 0
    if returncode < 0:
        return 1
    return returncode


def esp_args(run_dir, ovmf_code):
    """The QEMU arguments that boot OVMF from the ESP under `run_dir`. The disk is writable because
    q35's AHCI disk cannot be read-only; nothing in the guest writes to it. `ovmf_code` is the
    firmware file, read-only; the variable store is the copy under `run_dir`, since OVMF writes it."""
    return [
        "-drive", f"if=pflash,format=raw,unit=0,readonly=on,file={ovmf_code}",
        "-drive", f"if=pflash,format=raw,unit=1,file={run_dir / 'OVMF_VARS.fd'}",
        "-drive", f"format=raw,file=fat:rw:{run_dir / 'esp'}",
    ]


def qemu_args(run_dir, serial_log, kvm, iommu, gdb_socket, ovmf_code):
    args = esp_args(run_dir, ovmf_code) + [
        "-nographic",
        "-serial", "chardev:char0",
        "-mon", "chardev=char0",
        "-chardev", f"stdio,id=char0,mux=on,logfile={serial_log},signal=off",
        "-smp", "2",
        "-m", str(MEMORY_MIB),
        "-device", f"isa-debug-exit,iobase={DEBUG_EXIT_PORT:#x},iosize=0x04",
        "-no-reboot",
        "-machine", "q35,kernel_irqchip=split",
        "-cpu", "Haswell-IBRS",
    ]
    if iommu:
        args += ["-device", "intel-iommu,intremap=on,aw-bits=48,caching-mode=on",
                 "--trace", "vtd_*", "--trace", "iommufd_*", "-D", "/tmp/qemu-log.txt"]
    if kvm:
        args.append("-enable-kvm")
    if gdb_socket is not None:
        args += ["-gdb", f"unix:{gdb_socket},server,nowait"]
    return args


def gdb_info(loader, binaries, biases, socket):
    """The connection info tools/gdb.py reads from .gdb: the loader, the gdb socket, and each of
    `binaries`, a path by name, with the bias the loader logged for it."""
    return {
        "file": str(loader),
        "socket": str(socket),
        "binaries": {name: {"path": str(path), "bias": biases[name]} for name, path in binaries.items()},
    }


def drop_firmware_output(src, dst):
    """Reads src up to the loader's banner and copies what follows it on that line to dst."""
    while True:
        line = src.readline()
        if not line:
            return
        if LOADER_MARKER in line:
            dst.write(line.split(LOADER_MARKER, 1)[1])
            dst.flush()
            return


def await_debugger(src, dst):
    """Copies src to dst line by line until the loader logs that it waits for gdb, and returns the
    load bias it logged for each binary, by name; None when src ends first."""
    biases = {}
    while True:
        line = src.readline()
        if not line:
            return None
        dst.write(line)
        dst.flush()
        match = DEBUGGER_BIAS.search(line)
        if match:
            biases[match[1].decode()] = int(match[2], 16)
        elif DEBUGGER_WAITING in line:
            return biases


def copy_output(src, dst):
    while True:
        chunk = src.read(65536)
        if not chunk:
            return
        dst.write(chunk)
        dst.flush()


def lay_out_esp(run_dir, loader, images, gdb, ovmf_vars):
    loader_path = run_dir / "esp" / ESP_LOADER
    loader_path.parent.mkdir(parents=True)
    shutil.copy(loader, loader_path)
    with open(run_dir / "esp" / ESP_INITRD, "wb") as initrd:
        for image in images:
            initrd.write(image.read_bytes())
    if gdb:
        (run_dir / "esp" / ESP_GDB).touch()
    shutil.copy(ovmf_vars, run_dir / "OVMF_VARS.fd")


def main(argv):
    parser = argparse.ArgumentParser(prog="tools/run.py", description=__doc__.split("\n")[0])
    parser.add_argument("--no-kvm", action="store_true", help="use TCG even if /dev/kvm is writable")
    parser.add_argument("--iommu", action="store_true", help="add QEMU's emulated IOMMU")
    parser.add_argument("--gdb", action="store_true", help="wait for tools/gdb.py before entering the kernel")
    options = parser.parse_args(argv)
    # Fail before the build when the firmware or QEMU is not there.
    ovmf_code, ovmf_vars, qemu_bin = firmware.require("tools/run.py")

    kernel = build("kernel", "kernel")
    loader = build("aloader", "aloader")
    dom0 = build("dom0", "dom0")
    payload = build(f"user/{PAYLOAD}", PAYLOAD)

    # A timeout's SIGTERM unwinds through the with below, so the run directory goes too.
    signal.signal(signal.SIGTERM, lambda signum, frame: sys.exit(128 + signum))
    gdb_path = REPO / ".gdb"
    with tempfile.TemporaryDirectory(prefix="atmo-run-") as directory:
        run_dir = Path(directory)
        lay_out_esp(run_dir, loader, [kernel, dom0, payload], options.gdb, ovmf_vars)
        socket = run_dir / "gdb.sock" if options.gdb else None
        args = qemu_args(run_dir, REPO / "serial.log", use_kvm(options.no_kvm, "/dev/kvm"), options.iommu, socket,
                         ovmf_code)
        print(f"Starting {qemu_bin} " + " ".join(args), file=sys.stderr)
        try:
            qemu = subprocess.Popen([qemu_bin] + args, cwd=REPO, stdout=subprocess.PIPE, bufsize=0)
            drop_firmware_output(qemu.stdout, sys.stdout.buffer)
            if socket is not None:
                biases = await_debugger(qemu.stdout, sys.stdout.buffer)
                if biases is not None:
                    info = gdb_info(loader, {"kernel": kernel, "dom0": dom0}, biases, socket)
                    gdb_path.write_text(json.dumps(info))
                    print("Run tools/gdb.py in another terminal. The loader waits for it before entering the kernel.",
                          file=sys.stderr)
            copy_output(qemu.stdout, sys.stdout.buffer)
            returncode = qemu.wait()
        finally:
            if socket is not None:
                gdb_path.unlink(missing_ok=True)
    if exit_status(returncode) != 0:
        print(f"tools/run.py: QEMU exited with status {returncode}", file=sys.stderr)
    return exit_status(returncode)


class Tests(unittest.TestCase):
    def device(self, mode):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "kvm"
        path.touch()
        path.chmod(mode)
        return path

    def test_writable_device_uses_kvm(self):
        self.assertTrue(use_kvm(False, self.device(0o666)))

    def test_no_kvm_overrides_a_writable_device(self):
        self.assertFalse(use_kvm(True, self.device(0o666)))

    def test_read_only_device_does_not_use_kvm(self):
        self.assertFalse(use_kvm(False, self.device(0o444)))

    def test_missing_device_does_not_use_kvm(self):
        with tempfile.TemporaryDirectory() as directory:
            self.assertFalse(use_kvm(False, Path(directory) / "kvm"))

    def test_dom0_success_and_a_guest_shutdown_are_success(self):
        self.assertEqual(exit_status(33), 0)
        self.assertEqual(exit_status(0), 0)

    def test_kernel_failure_is_status_1(self):
        # The kernel's failure shutdown writes 0 to the isa-debug-exit port.
        self.assertEqual(exit_status(1), 1)

    def test_dom0_failure_is_its_code_shifted(self):
        # dom0 writes 2 when a status was not the one it expected, and 3 when it panics.
        self.assertEqual(exit_status(5), 5)
        self.assertEqual(exit_status(7), 7)

    def test_killed_is_failure(self):
        self.assertEqual(exit_status(-15), 1)

    def present(self, paths):
        return lambda path: path in paths

    def test_an_override_that_is_present_wins(self):
        # A default that also exists must not beat the override.
        paths = {"/scratch/code.fd", "/scratch/vars.fd", *firmware.CANDIDATES[0]}
        self.assertEqual(firmware.resolve_ovmf(
            {"ATMO_OVMF_CODE": "/scratch/code.fd", "ATMO_OVMF_VARS": "/scratch/vars.fd"},
            self.present(paths)), ("/scratch/code.fd", "/scratch/vars.fd"))

    def test_an_override_that_is_absent_names_the_variable(self):
        with self.assertRaises(firmware.Missing) as raised:
            firmware.resolve_ovmf(
                {"ATMO_OVMF_CODE": "/scratch/missing.fd", "ATMO_OVMF_VARS": "/scratch/vars.fd"},
                self.present({"/scratch/vars.fd"}))
        self.assertIn("ATMO_OVMF_CODE", str(raised.exception))
        with self.assertRaises(firmware.Missing) as raised:
            firmware.resolve_ovmf(
                {"ATMO_OVMF_CODE": "/scratch/code.fd", "ATMO_OVMF_VARS": "/scratch/missing.fd"},
                self.present({"/scratch/code.fd"}))
        self.assertIn("ATMO_OVMF_VARS", str(raised.exception))
        with self.assertRaises(firmware.Missing) as raised:
            firmware.resolve_ovmf({"ATMO_OVMF_CODE": "/scratch/code.fd"}, self.present({"/scratch/code.fd"}))
        self.assertIn("ATMO_OVMF_VARS", str(raised.exception))

    def test_no_override_finds_the_first_existing_default(self):
        first_code, first_vars = firmware.CANDIDATES[0]
        later = firmware.CANDIDATES[2]
        self.assertEqual(firmware.resolve_ovmf({}, self.present({first_code, first_vars})), (first_code, first_vars))
        # A code file whose variable store is absent is not a hit.
        self.assertEqual(firmware.resolve_ovmf({}, self.present({first_code, *later})), later)

    def test_nothing_found_names_the_variable(self):
        with self.assertRaises(firmware.Missing) as raised:
            firmware.resolve_ovmf({}, lambda path: False)
        self.assertIn("ATMO_OVMF_CODE", str(raised.exception))
        self.assertIn("ATMO_OVMF_VARS", str(raised.exception))

    def test_qemu_override_wins_and_an_absent_one_names_the_variable(self):
        self.assertEqual(firmware.resolve_qemu({"ATMO_QEMU": "/opt/qemu"}, lambda name: name), "/opt/qemu")
        with self.assertRaises(firmware.Missing) as raised:
            firmware.resolve_qemu({"ATMO_QEMU": "/opt/missing"}, lambda name: None)
        self.assertIn("ATMO_QEMU", str(raised.exception))
        self.assertEqual(firmware.resolve_qemu({}, lambda name: "/usr/bin/" + name),
                         "/usr/bin/" + firmware.QEMU_NAME)
        with self.assertRaises(firmware.Missing) as raised:
            firmware.resolve_qemu({}, lambda name: None)
        self.assertIn("ATMO_QEMU", str(raised.exception))

    def test_esp_args_boot_ovmf_from_the_directory(self):
        self.assertEqual(esp_args(Path("/run/x"), "/ovmf/OVMF_CODE.fd"), [
            "-drive", "if=pflash,format=raw,unit=0,readonly=on,file=/ovmf/OVMF_CODE.fd",
            "-drive", "if=pflash,format=raw,unit=1,file=/run/x/OVMF_VARS.fd",
            "-drive", "format=raw,file=fat:rw:/run/x/esp",
        ])

    def options(self, args, option):
        return [args[i + 1] for i, arg in enumerate(args) if arg == option]

    def test_qemu_args_shut_down_on_isa_debug_exit(self):
        args = qemu_args(Path("/run/x"), Path("/w/serial.log"), False, False, None, "/ovmf/OVMF_CODE.fd")
        self.assertIn("isa-debug-exit,iobase=0xf4,iosize=0x04", self.options(args, "-device"))
        self.assertIn("-no-reboot", args)
        self.assertNotIn("-no-shutdown", args)
        self.assertEqual(self.options(args, "-smp"), ["2"])
        self.assertEqual(self.options(args, "-cpu"), ["Haswell-IBRS"])
        self.assertIn("stdio,id=char0,mux=on,logfile=/w/serial.log,signal=off", self.options(args, "-chardev"))

    def test_guest_ram_is_the_minimum_test_machine(self):
        # design/test-guest-memory/. 512 MiB holds the loader pools. The kernel
        # tracks 8 GiB of pages, so a larger guest is not what this run needs,
        # and a 32 GiB guest has pages it cannot track.
        self.assertEqual(MEMORY_MIB, 512)
        self.assertLess(MEMORY_MIB, 8 * 1024)
        self.assertNotEqual(MEMORY_MIB, 32 * 1024)
        args = qemu_args(Path("/run/x"), Path("/w/serial.log"), False, False, None,
                         "/ovmf/OVMF_CODE.fd")
        self.assertEqual(self.options(args, "-m"), [str(MEMORY_MIB)])

    def test_kvm_iommu_and_gdb_each_add_their_arguments(self):
        plain = qemu_args(Path("/run/x"), Path("/w/serial.log"), False, False, None, "/ovmf/OVMF_CODE.fd")
        for absent in ("-enable-kvm", "-S", "-gdb"):
            self.assertNotIn(absent, plain)
        self.assertFalse(any("iommu" in arg for arg in plain))
        args = qemu_args(Path("/run/x"), Path("/w/serial.log"), True, True, Path("/run/x/gdb.sock"), "/ovmf/OVMF_CODE.fd")
        self.assertIn("-enable-kvm", args)
        self.assertIn("intel-iommu,intremap=on,aw-bits=48,caching-mode=on", self.options(args, "-device"))
        self.assertEqual(self.options(args, "-gdb"), ["unix:/run/x/gdb.sock,server,nowait"])

    def test_gdb_does_not_freeze_the_guest(self):
        # The loader waits for gdb itself, once it has logged where it loaded each binary.
        args = qemu_args(Path("/run/x"), Path("/w/serial.log"), False, False, Path("/run/x/gdb.sock"),
                         "/ovmf/OVMF_CODE.fd")
        self.assertNotIn("-S", args)

    def test_gdb_info_holds_the_socket_and_each_binary_s_bias(self):
        info = gdb_info(Path("/t/aloader.efi"), {"kernel": Path("/t/kernel"), "dom0": Path("/t/dom0")},
                        {"kernel": 0x14005f000, "dom0": 0x8000000000}, Path("/r/gdb.sock"))
        self.assertEqual(json.loads(json.dumps(info)), {
            "file": "/t/aloader.efi",
            "socket": "/r/gdb.sock",
            "binaries": {"kernel": {"path": "/t/kernel", "bias": 0x14005f000},
                         "dom0": {"path": "/t/dom0", "bias": 0x8000000000}},
        })

    def test_gdb_info_needs_every_binary_s_bias(self):
        with self.assertRaises(KeyError):
            gdb_info(Path("/t/aloader.efi"), {"kernel": Path("/t/kernel"), "dom0": Path("/t/dom0")},
                     {"kernel": 0x14005f000}, Path("/r/gdb.sock"))

    def test_the_esp_asks_the_loader_to_wait_only_under_gdb(self):
        for gdb in (False, True):
            with tempfile.TemporaryDirectory() as directory:
                run_dir = Path(directory)
                loader = run_dir / "aloader.efi"
                loader.write_bytes(b"MZ")
                image = run_dir / "kernel"
                image.write_bytes(b"\x7fELF")
                vars_fd = run_dir / "vars.fd"
                vars_fd.write_bytes(b"VARS")
                lay_out_esp(run_dir, loader, [image, image], gdb, vars_fd)
                self.assertEqual((run_dir / "esp" / ESP_INITRD).read_bytes(), b"\x7fELF\x7fELF")
                self.assertEqual((run_dir / "OVMF_VARS.fd").read_bytes(), b"VARS")
                self.assertEqual((run_dir / "esp" / ESP_GDB).exists(), gdb)

    def awaited(self, data):
        out = BytesIO()
        biases = await_debugger(BytesIO(data), out)
        return biases, out.getvalue()

    def test_the_biases_are_read_from_the_loader_s_lines_up_to_its_wait(self):
        lines = (b" INFO debugger: kernel at bias 0x14005f000\r\n"
                 b"DEBUG     Load Bias: 0x8000000000\r\n"
                 b" INFO debugger: dom0 at bias 0x8000000000\r\n"
                 b" INFO debugger: waiting\r\n")
        self.assertEqual(self.awaited(lines + b" INFO Calling into kernel\r\n"),
                         ({"kernel": 0x14005f000, "dom0": 0x8000000000}, lines))

    def test_no_biases_when_the_output_ends_before_the_wait(self):
        lines = b" INFO debugger: kernel at bias 0x14005f000\r\n"
        self.assertEqual(self.awaited(lines), (None, lines))

    def test_executable_is_the_named_artifact(self):
        messages = "\n".join(json.dumps(m) for m in [
            {"reason": "compiler-artifact", "target": {"name": "aelf"}, "executable": None},
            {"reason": "compiler-message", "message": {}},
            {"reason": "compiler-artifact", "target": {"name": "kernel"}, "executable": "/t/kernel"},
            {"reason": "build-finished", "success": True},
        ])
        self.assertEqual(executable(messages, "kernel"), Path("/t/kernel"))
        self.assertIsNone(executable(messages, "dom0"))

    def filtered(self, data):
        src, out = BytesIO(data), BytesIO()
        drop_firmware_output(src, out)
        copy_output(src, out)
        return out.getvalue()

    def test_firmware_output_before_the_loader_is_dropped(self):
        firmware = b"\x1b[2J\x1b[01;01HBdsDxe: loading Boot0001\r\n"
        loader = b"\x1b[0m   " + LOADER_MARKER + b"Loading kernel\r\n"
        self.assertEqual(self.filtered(firmware + loader + b"dom0 capability done\r\n"),
                         b"Loading kernel\r\ndom0 capability done\r\n")

    def test_nothing_passes_without_the_loader(self):
        self.assertEqual(self.filtered(b"BdsDxe: failed to load Boot0001\r\n"), b"")


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    else:
        sys.exit(main(sys.argv[1:]))
