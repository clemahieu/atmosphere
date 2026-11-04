#!/usr/bin/env python3
"""Boot dom0 under KVM, dump guest memory after it finishes and check where the kernel's stack went.

Memory the guest never wrote is zero, so non-zero pages show the stack's reach as a lower bound.

usage: tools/check-boot-stack.py debug|release [overflow]   (from the workspace root)

With overflow, the loader gets a stack below the kernel's depth and the kernel must fault at the guard.
"""
import os
import re
import socket
import subprocess
import sys
import time

MIB = 1 << 20
PAGE = 4096
MARGIN = 16 * MIB  # the least room the stack must have left
LOADER_SHARE = 16 * MIB  # how far below boot_info the loader's own calls may write


def build(profile, overflow=False):
    args = ["cargo", "build", "-q"] + (["--release"] if profile == "release" else [])
    for crate in ("aloader", "kernel", "dom0"):
        extra = ["--features", "small_kernel_stack"] if overflow and crate == "aloader" else []
        subprocess.run(args + extra, cwd=crate, check=True, env={**os.environ, "RUSTC_BOOTSTRAP": "1"})


def boot(profile, out, marker=b"dom0 benchmark done"):
    """Boots until the marker appears in the serial log and returns (serial log, qemu, monitor socket)."""
    kernel = f"target/x86_64-unknown-aloader/{profile}/kernel"
    dom0 = f"target/x86_64-unknown-aloader/{profile}/dom0"
    initrd = f"{out}/initrd"
    with open(initrd, "wb") as f:
        f.write(open(kernel, "rb").read() + open(dom0, "rb").read())
    log = f"{out}/serial.log"
    mon = f"{out}/mon"  # relative: a unix socket path is limited to about 100 bytes
    for path in (log, mon):
        if os.path.exists(path):
            os.unlink(path)
    qemu = subprocess.Popen(
        ["qemu-system-x86_64", "-enable-kvm", "-cpu", "host", "-machine", "q35,kernel_irqchip=split",
         "-smp", "2", "-m", "8192", "-nographic", "-serial", f"file:{log}",
         "-monitor", f"unix:{mon},server,nowait", "-no-reboot", "-no-shutdown",
         "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
         "-kernel", f"target/x86_64-unknown-none/{profile}/aloader", "-initrd", initrd],
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


def written(sock, out, base, size):
    """Returns the addresses of the non-zero pages in [base, base + size)."""
    path = f"{out}/dump"
    if os.path.exists(path):
        os.unlink(path)
    sock.sendall(f"pmemsave {base:#x} {size:#x} {path}\n".encode())
    for _ in range(240):
        if os.path.exists(path) and os.path.getsize(path) == size:
            break
        time.sleep(0.5)
    time.sleep(0.5)
    pages = []
    zero = bytes(PAGE)
    with open(path, "rb") as f:
        for i in range(size // PAGE):
            if f.read(PAGE) != zero:
                pages.append(base + i * PAGE)
    os.unlink(path)
    return pages


def check_overflow(profile, out):
    build(profile, overflow=True)
    log, qemu, sock = boot(profile, out, marker=b"Page Fault")
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


def main():
    profile = sys.argv[1]
    out = f"target/boot-stack-check-{profile}"
    os.makedirs(out, exist_ok=True)
    if sys.argv[2:] == ["overflow"]:
        return check_overflow(profile, out)
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

    stack = re.search(r"Kernel stack: ([0-9a-f]+)-([0-9a-f]+), boot info at ([0-9a-f]+)", log)
    if not stack:
        failures.append("the loader did not log the kernel stack")
    else:
        base, top, boot_info = (int(stack.group(i), 16) for i in (1, 2, 3))
        pages = written(sock, out, base, top - base)
        low = pages[0] if pages else top
        depth, room = top - low, low - base
        print(f"kernel stack {base:#x}-{top:#x} ({(top - base) // MIB} MiB): "
              f"depth at least {depth / MIB:.1f} MiB, {room / MIB:.1f} MiB left")
        if not pages:
            failures.append("the kernel did not run on its stack")
        if room < MARGIN:
            failures.append(f"less than {MARGIN // MIB} MiB of the stack left")
        below = written(sock, out, boot_info - 2 * LOADER_SHARE, LOADER_SHARE)
        print(f"loader stack below boot info {boot_info:#x}: {len(below)} written pages past the loader's share")
        if below:
            failures.append(f"writes on the loader's stack, from {below[0]:#x}")

    sock.sendall(b"quit\n")
    qemu.wait(timeout=30)
    for failure in failures:
        print("FAIL:", failure)
    print(f"{profile}: {'FAIL' if failures else 'ok'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
