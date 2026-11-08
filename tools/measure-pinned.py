#!/usr/bin/env python3
"""Boot dom0 under KVM with its two vCPUs pinned, and print the kernel's own timing lines.

usage: tools/measure-pinned.py within|across [boots] [--lock-stats]   (from the workspace root)

Numbers from a host with other work on it do not mean much, so this reports the load average. It
pins vCPU 0 and 1 to separate physical cores, sharing an L3 for within and on different L3s for across,
and keeps QEMU's other threads off both. KVM inflates IPI cost, so the IPI number is an upper bound.
A cycle in the timing lines is a TSC tick, not a core cycle, so each boot also prints the clock of both
measured cores over the boot: from cpuinfo_avg_freq, the kernel's APERF/MPERF average, or from
scaling_cur_freq where that file is absent, sampled from a thread kept off the measured cores. An idle
core reports the cpufreq policy's clock, so the minimum takes in the moments a vCPU was halted.

What needs root to keep the host off the measured cores is tools/isolate-pinned.sh, which the human
runs around the measurements: apply stops irqbalance, points the IRQs away from the measured CPUs and
their SMT siblings, takes the siblings offline, turns boost off and pins the measured CPUs' cpufreq
minimum to their maximum; undo restores each. Give it every CPU the runs use; on a 16-core part with
two L3s, within uses CPUs 6 and 7 and across 7 and 15:

    sudo tools/isolate-pinned.sh apply 6 7 15
    tools/measure-pinned.py within; tools/measure-pinned.py across
    sudo tools/isolate-pinned.sh undo
"""
import glob
import os
import re
import subprocess
import sys
import threading
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


def clock_source(cpu):
    """The cpufreq file, in kHz, that reports the clock of cpu: the APERF/MPERF average where the kernel has it."""
    for name in ("cpuinfo_avg_freq", "scaling_cur_freq"):
        if os.path.exists(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/{name}"):
            return name
    sys.exit(f"FAIL: CPU {cpu} has no cpufreq clock to read")


def sample_clocks(paths, others, done, samples):
    """Reads the clock in each of paths every 10 ms until done is set, from a thread kept on others."""
    os.sched_setaffinity(0, others)
    while not done.wait(0.01):
        for cpu, path in paths.items():
            try:
                samples[cpu].append(int(read(path)) / 1000)
            except (OSError, ValueError):
                continue


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
    samples = {cpu: [] for cpu in pair}
    done = threading.Event()
    paths = {cpu: f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/{clock_source(cpu)}" for cpu in pair}
    sampler = threading.Thread(target=sample_clocks, args=(paths, others, done, samples))
    sampler.start()
    try:
        qemu.wait(timeout=300)
    except subprocess.TimeoutExpired:
        qemu.kill()
        sys.exit(f"FAIL: no exit within 300 s; see {log}")
    finally:
        done.set()
        sampler.join()
    return open(log, "rb").read().decode(errors="replace"), samples


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
        log, samples = boot(pair, out)
        if "dom0 benchmark done" not in log:
            sys.exit(f"FAIL: boot {i} did not finish; see {out}/serial.log")
        print(f"boot {i}, load {os.getloadavg()[0]:.2f}")
        last = {}
        for line in log.splitlines():
            if LINES.search(line):
                last[LINES.search(line).group(0)] = re.sub(r"\x1b\[[0-9;]*m", "", line).strip()
        for line in last.values():
            print(f"  {line}")
        for cpu, mhz in samples.items():
            if not mhz:
                sys.exit(f"FAIL: no clock sample of CPU {cpu} over boot {i}")
            print(f"  clock of CPU {cpu}: min {min(mhz):.0f}, mean {sum(mhz) / len(mhz):.0f}, "
                  f"max {max(mhz):.0f} MHz over {len(mhz)} samples, from {clock_source(cpu)}")


if __name__ == "__main__":
    main()
