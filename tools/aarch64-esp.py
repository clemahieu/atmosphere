#!/usr/bin/env python3
"""Build the aarch64 loader, kernel, dom0 and payload and lay out the EFI system partition they boot from.

The directory gets EFI/BOOT/BOOTAA64.EFI, the loader, which EDK2 boots as removable media, and
initrd, the kernel, dom0 and the payload with their debug sections dropped, concatenated as the
loader reads them. tools/orangepi-kvm.py --esp takes the directory. A directory already there is
replaced.

The images are the debug build of `atmo build --target aarch64`. With --loader-feature the loader
is then built again with those features, small_kernel_stack for a kernel stack the boot overflows.

usage: tools/aarch64-esp.py DIR [--loader-feature FEATURE ...]   (from the workspace root)
       tools/aarch64-esp.py --test
"""
import argparse
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import elfstrip

TREE = Path(__file__).resolve().parent.parent
LOADER_TARGET = "aarch64-unknown-uefi"
LOADER = f"target/{LOADER_TARGET}/debug/aloader.efi"
IMAGES = [f"target/aarch64-unknown-aloader/debug/{name}" for name in ("kernel", "dom0", "hello")]


def build(loader_features):
    """Builds the four images, the loader last so that its features are the ones asked for."""
    subprocess.run([str(TREE / "tools/bin/atmo"), "build", "--target", "aarch64"], cwd=TREE, check=True)
    if loader_features:
        subprocess.run(
            ["cargo", "build", "-q", "--target", LOADER_TARGET, "--features", ",".join(loader_features)],
            cwd=TREE / "aloader", check=True, env={**os.environ, "RUSTC_BOOTSTRAP": "1"})


def lay_out(directory, loader, images):
    """Makes `directory` the partition: the loader where the firmware looks for it, and the initrd.
    Returns the initrd's size."""
    directory = Path(directory)
    shutil.rmtree(directory, ignore_errors=True)
    (directory / "EFI" / "BOOT").mkdir(parents=True)
    shutil.copy(loader, directory / "EFI" / "BOOT" / "BOOTAA64.EFI")
    return elfstrip.write_initrd(directory / "initrd", images)


class Tests(unittest.TestCase):
    def files(self, root):
        return sorted(str(path.relative_to(root)) for path in Path(root).rglob("*") if path.is_file())

    def test_the_partition_holds_the_loader_and_the_images_in_order(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            (tmp / "loader").write_bytes(b"loader\0")
            names = []
            for name in ("kernel", "dom0", "hello"):
                (tmp / name).write_bytes(name.encode() + b"\n")
                names.append(tmp / name)
            size = lay_out(tmp / "esp", tmp / "loader", names)
            self.assertEqual(self.files(tmp / "esp"), ["EFI/BOOT/BOOTAA64.EFI", "initrd"])
            self.assertEqual((tmp / "esp/EFI/BOOT/BOOTAA64.EFI").read_bytes(), b"loader\0")
            self.assertEqual((tmp / "esp/initrd").read_bytes(), b"kernel\ndom0\nhello\n")
            self.assertEqual(size, len(b"kernel\ndom0\nhello\n"))

    def test_a_directory_already_there_is_replaced(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            (tmp / "esp" / "EFI" / "BOOT").mkdir(parents=True)
            (tmp / "esp" / "cmdline").write_bytes(b"left over")
            (tmp / "esp" / "EFI" / "BOOT" / "BOOTAA64.EFI").write_bytes(b"old loader")
            (tmp / "loader").write_bytes(b"new loader")
            (tmp / "kernel").write_bytes(b"kernel")
            lay_out(tmp / "esp", tmp / "loader", [tmp / "kernel"])
            self.assertEqual(self.files(tmp / "esp"), ["EFI/BOOT/BOOTAA64.EFI", "initrd"])
            self.assertEqual((tmp / "esp/EFI/BOOT/BOOTAA64.EFI").read_bytes(), b"new loader")

    def test_an_image_that_is_missing_stops_the_layout(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            (tmp / "loader").write_bytes(b"loader")
            with self.assertRaises(FileNotFoundError):
                lay_out(tmp / "esp", tmp / "loader", [tmp / "kernel"])


def main(argv):
    if argv == ["--test"]:
        return unittest.main(argv=[sys.argv[0]])
    parser = argparse.ArgumentParser(prog="tools/aarch64-esp.py", description=__doc__.split("\n")[0])
    parser.add_argument("directory", type=Path, metavar="DIR", help="the partition's directory, replaced when present")
    parser.add_argument("--loader-feature", action="append", default=[], metavar="FEATURE",
                        help="a feature the loader is built with; may repeat")
    args = parser.parse_args(argv)
    build(args.loader_feature)
    size = lay_out(args.directory, TREE / LOADER, [TREE / image for image in IMAGES])
    print(f"{args.directory}: {LOADER} as EFI/BOOT/BOOTAA64.EFI, initrd of {size} bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
