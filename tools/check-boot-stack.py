#!/usr/bin/env python3
# SPDX-License-Identifier: MIT

"""Boot dom0 under KVM, dump guest memory after it finishes and check where the kernel's and dom0's stacks went.

The loader fills the kernel's boot stack and dom0's stack with a pattern before either runs (aloader's
stack.rs), so the lowest word that no longer holds it is how far down the boot wrote. Each stack must
have at least that much left below it, as much again as the boot used. Memory the guest never wrote is
zero, so the boot page tables' non-zero pages show where they reach.

usage: tools/check-boot-stack.py debug|release [overflow|syscall-overflow]   (from the workspace root)

Every build first checks that the kernel's entry point probes no large frame.

With overflow, the loader gets a stack below the kernel's depth and the kernel must fault at the guard.
With syscall-overflow, the kernel gets a syscall stack below a syscall's depth and must fault once, in the
guard it logged under CPU 0's syscall stack.
"""
import os
import re
import shutil
import socket
import subprocess
import sys
import time

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import elfstrip
import firmware
import run as guest

KIB = 1 << 10
PAGE = 4096
PAINT = b"loadrstk"  # what the loader fills a stack with: aloader's stack.rs
ENTRY_FRAME = PAGE  # main's frame stays under this: the overflow build's stack is two pages


def build(profile, overflow=False, kernel_features=()):
    args = ["cargo", "build", "-q"] + (["--release"] if profile == "release" else [])
    for crate in ("kernel", "dom0", "user/hello"):
        features = ["--features", ",".join(kernel_features)] if crate == "kernel" and kernel_features else []
        subprocess.run(args + features, cwd=crate, check=True, env={**os.environ, "RUSTC_BOOTSTRAP": "1"})
    build_loader(profile, ["small_kernel_stack"] if overflow else [])
    check_entry_frame(f"target/x86_64-unknown-aloader/{profile}/kernel")


def build_loader(profile, features=()):
    """Builds aloader as the UEFI application OVMF boots."""
    args = ["cargo", "build", "-q", "--target", "x86_64-unknown-uefi"]
    args += (["--release"] if profile == "release" else []) + (["--features", ",".join(features)] if features else [])
    subprocess.run(args, cwd="aloader", check=True, env={**os.environ, "RUSTC_BOOTSTRAP": "1"})


def esp(profile, out, initrd, ovmf_code, ovmf_vars):
    """Lays out the EFI system partition under out and returns QEMU's arguments to boot it."""
    root = f"{out}/esp"
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(f"{root}/EFI/BOOT")
    shutil.copy(f"target/x86_64-unknown-uefi/{profile}/aloader.efi", f"{root}/EFI/BOOT/BOOTX64.EFI")
    shutil.copy(initrd, f"{root}/initrd")
    shutil.copy(ovmf_vars, f"{out}/OVMF_VARS.fd")
    return ["-drive", f"if=pflash,format=raw,unit=0,readonly=on,file={ovmf_code}",
            "-drive", f"if=pflash,format=raw,unit=1,file={out}/OVMF_VARS.fd",
            "-drive", f"format=raw,file=fat:rw:{root}"]


def check_entry_frame(kernel):
    """main's prologue runs before the IDT exists, so an overflow it probes faults with no report."""
    text = subprocess.run(["objdump", "-d", "-M", "intel", "--disassemble=main", kernel],
                          check=True, capture_output=True, text=True).stdout
    assert "<main>:" in text, f"no main in {kernel}"
    sizes = [int(size, 16) for size in re.findall(r"sub\s+(?:r11|rsp),0x([0-9a-f]+)", text)]
    if sizes and max(sizes) >= ENTRY_FRAME:
        sys.exit(f"FAIL: main in {kernel} probes a frame of {max(sizes):#x} bytes before the IDT exists")


def boot(profile, out, marker=b"dom0 capability done", kernel=None, dom0=None, payload=None):
    """Boots until the marker appears in the serial log and returns (serial log, qemu, monitor socket).
    The initrd is the kernel, dom0 and the payload, as tools/run.py lays it out."""
    images = [image or f"target/x86_64-unknown-aloader/{profile}/{name}"
              for image, name in ((kernel, "kernel"), (dom0, "dom0"), (payload, "hello"))]
    initrd = f"{out}/initrd"
    elfstrip.write_initrd(initrd, images)
    log = f"{out}/serial.log"
    mon = f"{out}/mon"  # relative: a unix socket path is limited to about 100 bytes
    for path in (log, mon):
        if os.path.exists(path):
            os.unlink(path)
    ovmf_code, ovmf_vars, qemu_bin = firmware.require("tools/check-boot-stack.py")
    qemu = subprocess.Popen(
        [qemu_bin, "-enable-kvm", "-cpu", "host", "-machine", "q35,kernel_irqchip=split",
         "-smp", "2", "-m", str(guest.MEMORY_MIB), "-nographic", "-serial", f"file:{log}",
         "-monitor", f"unix:{mon},server,nowait", "-no-reboot", "-no-shutdown",
         "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04"] + esp(profile, out, initrd, ovmf_code, ovmf_vars),
        stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    deadline = time.time() + 120
    while time.time() < deadline:
        if os.path.exists(log) and marker in open(log, "rb").read():
            time.sleep(1)
            sock = socket.socket(socket.AF_UNIX)
            sock.connect(mon)
            return open(log, "rb").read().decode(errors="replace"), qemu, sock
        time.sleep(1)
    qemu.kill()
    sys.exit(f"FAIL: {marker.decode()} did not appear; see {log}")


def dump(sock, out, base, size):
    """Returns the guest's memory in [base, base + size)."""
    path = f"{out}/dump"
    if os.path.exists(path):
        os.unlink(path)
    sock.sendall(f"pmemsave {base:#x} {size:#x} {path}\n".encode())
    for _ in range(240):
        if os.path.exists(path) and os.path.getsize(path) == size:
            break
        time.sleep(0.5)
    time.sleep(0.5)
    with open(path, "rb") as f:
        data = f.read()
    os.unlink(path)
    return data


def written(sock, out, base, size):
    """Returns the addresses of the non-zero pages in [base, base + size)."""
    data = dump(sock, out, base, size)
    zero = bytes(PAGE)
    return [base + i for i in range(0, size, PAGE) if data[i:i + PAGE] != zero]


def depth(data):
    """The bytes of a painted stack counted down from its top to the lowest word that no longer
    holds the pattern. A word written with the pattern itself is not seen, so this is a lower bound."""
    untouched = 0
    while untouched + 8 <= len(data) and data[untouched:untouched + 8] == PAINT:
        untouched += 8
    return len(data) - untouched


def stack_failures(name, size, used):
    """What is wrong with a stack of size bytes whose boot wrote used bytes of it: the boot must have
    run on it and left at least as much below as it wrote."""
    if used == 0:
        return [f"nothing ran on the {name} stack"]
    if size - used < used:
        return [f"the {name} stack has {(size - used) // KIB} KiB left, less than the {used // KIB} KiB written"]
    return []


def check_stack(sock, out, log, name, line):
    """Reads the stack the loader logged on the line starting with line and returns its failures."""
    found = re.search(line + r": ([0-9a-f]+)-([0-9a-f]+)", log)
    if not found:
        return [f"the loader did not log the {name} stack"]
    base, top = (int(found.group(i), 16) for i in (1, 2))
    used = depth(dump(sock, out, base, top - base))
    print(f"{name} stack {base:#x}-{top:#x} ({(top - base) // KIB} KiB): "
          f"{used // KIB} KiB written, {(top - base - used) // KIB} KiB left")
    return stack_failures(name, top - base, used)


def check_overflow(profile, out):
    build(profile, overflow=True)
    # The kernel's own report, which a fault in a process does not print.
    log, qemu, sock = boot(profile, out, marker=b"Page Fault (address")
    sock.sendall(b"quit\n")
    qemu.wait(timeout=30)
    guard = re.search(r"Kernel stack guard: ([0-9a-f]+)-([0-9a-f]+)", log)
    fault = re.search(r"Page Fault \(address 0x([0-9a-f]+)", log)
    if not guard:
        print("FAIL: the loader did not log the stack guard")
        return 1
    low, high, address = int(guard.group(1), 16), int(guard.group(2), 16), int(fault.group(1), 16)
    print(f"guard {low:#x}-{high:#x}, fault at {address:#x}")
    if not low <= address < high:
        print(f"{profile} overflow: FAIL, the fault is outside the guard")
        return 1
    print(f"{profile} overflow: ok")
    return 0


def syscall_overflow_failures(log):
    """What is wrong with the serial log of a boot whose syscall stack overflows: it must report one
    kernel page fault, on CPU 0, inside the guard the kernel logged under CPU 0's syscall stack."""
    guard = re.search(r"CPU 0 syscall stack 0x[0-9a-f]+-0x[0-9a-f]+, guard 0x([0-9a-f]+)-0x([0-9a-f]+)", log)
    faults = re.findall(r"CPU (\d+): Page Fault \(address 0x([0-9a-f]+)", log)
    if not guard:
        return ["the kernel did not log CPU 0's syscall stack guard"]
    low, high = int(guard.group(1), 16), int(guard.group(2), 16)
    if len(faults) != 1:
        return [f"{len(faults)} kernel page fault reports, not one"]
    cpu, address = int(faults[0][0]), int(faults[0][1], 16)
    print(f"syscall stack guard {low:#x}-{high:#x}, CPU {cpu} fault at {address:#x}, one report")
    failures = []
    if cpu != 0:
        failures.append(f"the fault is on CPU {cpu}, not CPU 0")
    if not low <= address < high:
        failures.append("the fault is outside the guard")
    return failures


def check_syscall_overflow(profile, out):
    build(profile, kernel_features=["small_syscall_stack"])
    log, qemu, sock = boot(profile, out, marker=b"Page Fault (address")
    time.sleep(2)  # room for a second report, which would mean the first did not stop the core
    log = open(f"{out}/serial.log", "rb").read().decode(errors="replace")
    sock.sendall(b"quit\n")
    qemu.wait(timeout=30)
    failures = syscall_overflow_failures(log)
    for failure in failures:
        print("FAIL:", failure)
    print(f"{profile} syscall overflow: {'FAIL' if failures else 'ok'}")
    return 1 if failures else 0


def main():
    if sys.argv[1:] == ["--test"]:
        return test()
    profile = sys.argv[1]
    out = f"target/boot-stack-check-{profile}"
    os.makedirs(out, exist_ok=True)
    if sys.argv[2:] == ["overflow"]:
        return check_overflow(profile, out)
    if sys.argv[2:] == ["syscall-overflow"]:
        return check_syscall_overflow(profile, out)
    build(profile)
    log, qemu, sock = boot(profile, out)
    failures = []

    # The boot page tables grow from the bottom of their region and stay small; anything in the
    # upper half is a stack that ran off its end.
    tables = re.search(r"region\.base\(\) ([0-9a-f]+), region\.end_inclusive\(\) ([0-9a-f]+), page_type PageTable", log)
    tbase, tend = (int(tables.group(1), 16) + PAGE) & ~(PAGE - 1), int(tables.group(2), 16) & ~(PAGE - 1)
    middle = tbase + (tend - tbase) // 2
    stray = written(sock, out, middle, tend - middle)
    print(f"boot page tables {tbase:#x}-{tend:#x}: {len(stray)} written pages in the upper half")
    if stray:
        failures.append(f"writes in the upper half of the boot page tables, from {stray[0]:#x}")

    failures += check_stack(sock, out, log, "kernel", "Kernel stack")
    failures += check_stack(sock, out, log, "dom0", "Dom0 stack")

    sock.sendall(b"quit\n")
    qemu.wait(timeout=30)
    for failure in failures:
        print("FAIL:", failure)
    print(f"{profile}: {'FAIL' if failures else 'ok'}")
    return 1 if failures else 0


def test():
    import unittest

    guard = "CPU 0 syscall stack 0x10000-0x10400, guard 0xf000-0x10000\n"

    def fault(cpu, address):
        return f"CPU {cpu}: Page Fault (address {address:#x}, error code 2): Registers {{}}\n"

    class SyscallOverflow(unittest.TestCase):
        def test_one_fault_in_the_guard_passes(self):
            self.assertEqual(syscall_overflow_failures(guard + fault(0, 0xfff8)), [])

        def test_no_guard_line_fails(self):
            self.assertEqual(syscall_overflow_failures(fault(0, 0xfff8)),
                             ["the kernel did not log CPU 0's syscall stack guard"])

        def test_no_fault_fails(self):
            self.assertEqual(syscall_overflow_failures(guard), ["0 kernel page fault reports, not one"])

        def test_two_faults_fail(self):
            self.assertEqual(syscall_overflow_failures(guard + fault(0, 0xfff8) + fault(0, 0xfff0)),
                             ["2 kernel page fault reports, not one"])

        def test_a_fault_outside_the_guard_fails(self):
            self.assertEqual(syscall_overflow_failures(guard + fault(0, 0x10008)), ["the fault is outside the guard"])

        def test_a_fault_on_another_core_fails(self):
            self.assertEqual(syscall_overflow_failures(guard + fault(1, 0xfff8)), ["the fault is on CPU 1, not CPU 0"])

    class Stack(unittest.TestCase):
        def test_an_untouched_stack_has_nothing_written(self):
            self.assertEqual(depth(PAINT * 64), 0)

        def test_the_depth_runs_from_the_top_to_the_lowest_word_written(self):
            self.assertEqual(depth(PAINT * 54 + bytes(8) + PAINT + bytes(64)), 80)

        def test_a_stack_written_to_its_bottom_is_written_whole(self):
            self.assertEqual(depth(bytes(512)), 512)

        def test_as_much_left_as_written_passes(self):
            self.assertEqual(stack_failures("dom0", 128 * KIB, 64 * KIB), [])

        def test_less_left_than_written_fails(self):
            self.assertEqual(stack_failures("dom0", 128 * KIB, 68 * KIB),
                             ["the dom0 stack has 60 KiB left, less than the 68 KiB written"])

        def test_a_stack_nothing_ran_on_fails(self):
            self.assertEqual(stack_failures("kernel", 128 * KIB, 0), ["nothing ran on the kernel stack"])

    tests = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromTestCase(case) for case in (SyscallOverflow, Stack))
    result = unittest.TextTestRunner().run(tests)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
