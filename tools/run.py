#!/usr/bin/env python3
"""Build the loader, kernel, dom0 and payload, and boot them under QEMU on OVMF.

OVMF boots the loader, the UEFI application, from a directory QEMU serves as the EFI system
partition; the loader reads the kernel, dom0 and payload ELF images concatenated in the file initrd
beside it (aloader/src/boot/uefi.rs). The serial log is serial.log at the workspace root. KVM is used
whenever /dev/kvm is writable; --no-kvm forces TCG. --iommu adds QEMU's emulated IOMMU. --gdb
freezes the guest at its first instruction behind a gdb server, and writes .gdb at the workspace root
for atmo gdb to attach with.

The firmware's output on the terminal ends with control sequences that reset it, so everything
before the loader's banner is dropped there; serial.log keeps it.

Exit status: 0 when dom0 reports success or the guest shuts down; otherwise QEMU's: 1 when the
kernel fails, 3 when a dom0 timer fails. 1 when QEMU dies by a signal, and 1 when a build fails.

usage: tools/run.py [--no-kvm] [--iommu] [--gdb]   (from anywhere)
       tools/run.py --test                         (this script's own tests)
"""
import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest
from io import BytesIO
from pathlib import Path

sys.dont_write_bytecode = True

REPO = Path(__file__).resolve().parent.parent
# OVMF's code read-only, and a copy of its variable store, since OVMF writes the store.
OVMF_CODE = "/usr/share/edk2/ovmf/OVMF_CODE.fd"
OVMF_VARS = "/usr/share/edk2/ovmf/OVMF_VARS.fd"
# Where OVMF looks for an application on removable media, and where the loader looks for the initrd.
ESP_LOADER = "EFI/BOOT/BOOTX64.EFI"
ESP_INITRD = "initrd"
# dom0 ends the run by writing to this port (dom0/src/syscall_benchmark.rs).
DEBUG_EXIT_PORT = 0xf4
# isa-debug-exit makes QEMU exit with `code << 1 | 1`, and dom0 writes 0x10 on success.
DOM0_SUCCESS_STATUS = 33
MEMORY_MIB = 32 * 1024
# The only program under user/, which dom0 is given to load.
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


def esp_args(run_dir):
    """The QEMU arguments that boot OVMF from the ESP under `run_dir`. The disk is writable because
    q35's AHCI disk cannot be read-only; nothing in the guest writes to it."""
    return [
        "-drive", f"if=pflash,format=raw,unit=0,readonly=on,file={OVMF_CODE}",
        "-drive", f"if=pflash,format=raw,unit=1,file={run_dir / 'OVMF_VARS.fd'}",
        "-drive", f"format=raw,file=fat:rw:{run_dir / 'esp'}",
    ]


def qemu_args(run_dir, serial_log, kvm, iommu, gdb_socket):
    args = esp_args(run_dir) + [
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
        args += ["-S", "-gdb", f"unix:{gdb_socket},server,nowait"]
    return args


def gdb_info(loader, kernel, dom0, socket):
    """The connection info atmo gdb reads from .gdb (build-tool/src/emulator/gdb.rs)."""
    return {
        "file": str(loader),
        "server": {"Unix": str(socket)},
        "binaries": {"kernel": str(kernel), "dom0": str(dom0)},
    }


def filter_output(src, dst):
    """Copies src to dst from just after the loader's banner on, dropping what comes before it."""
    while True:
        line = src.readline()
        if not line:
            return
        if LOADER_MARKER in line:
            dst.write(line.split(LOADER_MARKER, 1)[1])
            dst.flush()
            break
    while True:
        chunk = src.read(65536)
        if not chunk:
            return
        dst.write(chunk)
        dst.flush()


def lay_out_esp(run_dir, loader, images):
    loader_path = run_dir / "esp" / ESP_LOADER
    loader_path.parent.mkdir(parents=True)
    shutil.copy(loader, loader_path)
    with open(run_dir / "esp" / ESP_INITRD, "wb") as initrd:
        for image in images:
            initrd.write(image.read_bytes())
    shutil.copy(OVMF_VARS, run_dir / "OVMF_VARS.fd")


def main(argv):
    parser = argparse.ArgumentParser(prog="tools/run.py", description=__doc__.split("\n")[0])
    parser.add_argument("--no-kvm", action="store_true", help="use TCG even if /dev/kvm is writable")
    parser.add_argument("--iommu", action="store_true", help="add QEMU's emulated IOMMU")
    parser.add_argument("--gdb", action="store_true", help="wait for atmo gdb at the first instruction")
    options = parser.parse_args(argv)

    kernel = build("kernel", "kernel")
    loader = build("aloader", "aloader")
    dom0 = build("dom0", "dom0")
    payload = build(f"user/{PAYLOAD}", PAYLOAD)

    # A timeout's SIGTERM unwinds through the with below, so the run directory goes too.
    signal.signal(signal.SIGTERM, lambda signum, frame: sys.exit(128 + signum))
    gdb_path = REPO / ".gdb"
    with tempfile.TemporaryDirectory(prefix="atmo-run-") as directory:
        run_dir = Path(directory)
        lay_out_esp(run_dir, loader, [kernel, dom0, payload])
        socket = run_dir / "gdb.sock" if options.gdb else None
        if socket is not None:
            gdb_path.write_text(json.dumps(gdb_info(loader, kernel, dom0, socket)))
            print("Run `atmo gdb` in another terminal. The guest is frozen until you continue in the debugger.",
                  file=sys.stderr)
        args = qemu_args(run_dir, REPO / "serial.log", use_kvm(options.no_kvm, "/dev/kvm"), options.iommu, socket)
        print("Starting qemu-system-x86_64 " + " ".join(args), file=sys.stderr)
        try:
            qemu = subprocess.Popen(["qemu-system-x86_64"] + args, cwd=REPO, stdout=subprocess.PIPE, bufsize=0)
            filter_output(qemu.stdout, sys.stdout.buffer)
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

    def test_dom0_failure_is_status_3(self):
        # dom0's bench_fail writes 1.
        self.assertEqual(exit_status(3), 3)

    def test_killed_is_failure(self):
        self.assertEqual(exit_status(-15), 1)

    def test_esp_args_boot_ovmf_from_the_directory(self):
        self.assertEqual(esp_args(Path("/run/x")), [
            "-drive", f"if=pflash,format=raw,unit=0,readonly=on,file={OVMF_CODE}",
            "-drive", "if=pflash,format=raw,unit=1,file=/run/x/OVMF_VARS.fd",
            "-drive", "format=raw,file=fat:rw:/run/x/esp",
        ])

    def options(self, args, option):
        return [args[i + 1] for i, arg in enumerate(args) if arg == option]

    def test_qemu_args_shut_down_on_isa_debug_exit(self):
        args = qemu_args(Path("/run/x"), Path("/w/serial.log"), False, False, None)
        self.assertIn("isa-debug-exit,iobase=0xf4,iosize=0x04", self.options(args, "-device"))
        self.assertIn("-no-reboot", args)
        self.assertNotIn("-no-shutdown", args)
        self.assertEqual(self.options(args, "-smp"), ["2"])
        self.assertEqual(self.options(args, "-cpu"), ["Haswell-IBRS"])
        self.assertIn("stdio,id=char0,mux=on,logfile=/w/serial.log,signal=off", self.options(args, "-chardev"))

    def test_kvm_iommu_and_gdb_each_add_their_arguments(self):
        plain = qemu_args(Path("/run/x"), Path("/w/serial.log"), False, False, None)
        for absent in ("-enable-kvm", "-S", "-gdb"):
            self.assertNotIn(absent, plain)
        self.assertFalse(any("iommu" in arg for arg in plain))
        args = qemu_args(Path("/run/x"), Path("/w/serial.log"), True, True, Path("/run/x/gdb.sock"))
        self.assertIn("-enable-kvm", args)
        self.assertIn("intel-iommu,intremap=on,aw-bits=48,caching-mode=on", self.options(args, "-device"))
        self.assertIn("-S", args)
        self.assertEqual(self.options(args, "-gdb"), ["unix:/run/x/gdb.sock,server,nowait"])

    def test_gdb_info_is_what_atmo_gdb_reads(self):
        info = gdb_info(Path("/t/aloader.efi"), Path("/t/kernel"), Path("/t/dom0"), Path("/r/gdb.sock"))
        self.assertEqual(json.loads(json.dumps(info)), {
            "file": "/t/aloader.efi",
            "server": {"Unix": "/r/gdb.sock"},
            "binaries": {"kernel": "/t/kernel", "dom0": "/t/dom0"},
        })

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
        out = BytesIO()
        filter_output(BytesIO(data), out)
        return out.getvalue()

    def test_firmware_output_before_the_loader_is_dropped(self):
        firmware = b"\x1b[2J\x1b[01;01HBdsDxe: loading Boot0001\r\n"
        loader = b"\x1b[0m   " + LOADER_MARKER + b"Loading kernel\r\n"
        self.assertEqual(self.filtered(firmware + loader + b" INFO dom0 benchmark done\r\n"),
                         b"Loading kernel\r\n INFO dom0 benchmark done\r\n")

    def test_nothing_passes_without_the_loader(self):
        self.assertEqual(self.filtered(b"BdsDxe: failed to load Boot0001\r\n"), b"")


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
    else:
        sys.exit(main(sys.argv[1:]))
