#!/usr/bin/env python3
"""Boot dom0 under KVM with its two vCPUs pinned, and print the kernel's own timing lines.

usage: tools/measure-pinned.py within|across [boots] [--lock-stats]   (from the workspace root)

Numbers from a host with other work on it do not mean much, so this reports the load average. It
pins vCPU 0 and 1 to separate physical cores, sharing an L3 for within and on different L3s for across,
and keeps QEMU's other threads off both. KVM inflates IPI cost, so the IPI number is an upper bound.
"""
import glob
import os
import re
import subprocess
import sys
import time

LINES = re.compile(r"IPC round trip|sys_mresolve:|flush IPI|kernel lock:|contention test lock:")


def read(path):
    with open(path) as f:
        return f.read().strip()


def expand(cpus):
    out = []
    for part in cpus.split(","):
        low, _, high = part.partition("-")
        out.extend(range(int(low), int(high or low) + 1))
    return out


def physical_cores_by_l3():
    """Maps each L3's CPU list to one logical CPU per online physical core in it. An offline CPU
    has no topology to read."""
    groups = {}
    for cpu in expand(read("/sys/devices/system/cpu/online")):
        path = f"/sys/devices/system/cpu/cpu{cpu}"
        if expand(read(f"{path}/topology/thread_siblings_list"))[0] != cpu:
            continue
        groups.setdefault(read(f"{path}/cache/index3/shared_cpu_list"), []).append(cpu)
    return list(groups.values())


def choose(mode):
    groups = physical_cores_by_l3()
    if mode == "within":
        return groups[0][-2], groups[0][-1]
    return groups[0][-1], groups[1][-1]


def build(lock_stats):
    subprocess.run(["cargo", "build", "-q", "--release"] + (["--features", "lock_stats"] if lock_stats else []),
                   cwd="kernel", check=True, env={**os.environ, "RUSTC_BOOTSTRAP": "1"})
    for crate in ("aloader", "dom0"):
        subprocess.run(["cargo", "build", "-q", "--release"], cwd=crate, check=True,
                       env={**os.environ, "RUSTC_BOOTSTRAP": "1"})


def pin_vcpus(pid, pair):
    """Waits for QEMU's vCPU threads, by the names debug-threads gives them, and pins them."""
    deadline = time.time() + 30
    pinned = set()
    while time.time() < deadline and len(pinned) < 2:
        for task in glob.glob(f"/proc/{pid}/task/*"):
            try:
                name = read(f"{task}/comm")
            except OSError:
                continue
            match = re.match(r"CPU (\d)/KVM", name)
            if match and int(match.group(1)) not in pinned:
                os.sched_setaffinity(int(task.split("/")[-1]), {pair[int(match.group(1))]})
                pinned.add(int(match.group(1)))
        time.sleep(0.001)
    if len(pinned) < 2:
        sys.exit("FAIL: did not find both vCPU threads")


def boot(pair, out):
    initrd, log = f"{out}/initrd", f"{out}/serial.log"
    with open(initrd, "wb") as f:
        for name in ("kernel", "dom0"):
            f.write(open(f"target/x86_64-unknown-aloader/release/{name}", "rb").read())
    if os.path.exists(log):
        os.unlink(log)
    others = set(os.sched_getaffinity(0)) - set(pair)
    qemu = subprocess.Popen(
        ["qemu-system-x86_64", "-enable-kvm", "-cpu", "host", "-machine", "q35,kernel_irqchip=split",
         "-name", "guest=atmo,debug-threads=on", "-smp", "2", "-m", "8192", "-nographic",
         "-serial", f"file:{log}", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
         "-kernel", "target/x86_64-unknown-none/release/aloader", "-initrd", initrd],
        stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        preexec_fn=lambda: os.sched_setaffinity(0, others))
    pin_vcpus(qemu.pid, pair)
    try:
        qemu.wait(timeout=300)
    except subprocess.TimeoutExpired:
        qemu.kill()
        sys.exit(f"FAIL: no exit within 300 s; see {log}")
    return open(log, "rb").read().decode(errors="replace")


def main():
    mode = sys.argv[1]
    rest = sys.argv[2:]
    lock_stats = "--lock-stats" in rest
    boots = next((int(a) for a in rest if a.isdigit()), 3)
    pair = choose(mode)
    out = "target/measure-pinned"
    os.makedirs(out, exist_ok=True)
    build(lock_stats)
    print(f"{mode}: vCPUs on host CPUs {pair}, lock_stats {lock_stats}, load {os.getloadavg()[0]:.2f}")
    for i in range(boots):
        log = boot(pair, out)
        if "dom0 benchmark done" not in log:
            sys.exit(f"FAIL: boot {i} did not finish; see {out}/serial.log")
        print(f"boot {i}, load {os.getloadavg()[0]:.2f}")
        last = {}
        for line in log.splitlines():
            if LINES.search(line):
                last[LINES.search(line).group(0)] = re.sub(r"\x1b\[[0-9;]*m", "", line).strip()
        for line in last.values():
            print(f"  {line}")


if __name__ == "__main__":
    main()
