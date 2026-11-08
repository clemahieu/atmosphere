#!/usr/bin/env python3
"""Boot dom0 under KVM with its two vCPUs pinned, and print the kernel's own timing lines.

usage: tools/measure-pinned.py within0|within1|across [boots] [--lock-stats] [--force]   (from the workspace root)

Numbers from a host with other work on it do not mean much, so this reports the load average. It
pins vCPU 0 and 1 to separate physical cores and keeps QEMU's other threads, and its own clock sampler,
off both and off their SMT siblings, which share a core's execution units, L1 and L2. It prints the
siblings, from thread_siblings_list, and the CPUs left to those threads. A thread a vCPU starts after
its pin, such as KVM's kvm-nx-lpage-re worker, inherits that pin, so through each boot the tool moves
every QEMU thread but the two vCPUs back to those CPUs and prints each one it moved, or each one the
kernel would not let it move. The placement
picks the cores: within0 takes two cores sharing the L3 that holds CPU 0 (CCD 0 on a 9950X3D, the one
with the V-cache), within1 two cores sharing the next L3 (CCD 1), and across one core from each. The
first line names each measured CPU's L3 by its shared_cpu_list. KVM inflates IPI cost, so the IPI
number is an upper bound.
A cycle in the timing lines is a TSC tick, not a core cycle, so each boot also prints the clock of both
measured cores over the boot: from cpuinfo_avg_freq, the kernel's APERF/MPERF average, or from
scaling_cur_freq where that file is absent, sampled from a thread kept off the measured cores. An idle
core reports the cpufreq policy's clock, so the minimum takes in the moments a vCPU was halted.

Before the first boot it looks at the measured CPUs and their SMT siblings for half a second and
prints what it finds there: other tasks seen runnable, from /proc/*/task/*/stat; device IRQs routed
there, from /proc/irq/*/effective_affinity_list, or taken there, from the counts in /proc/interrupts;
and the CPU-local interrupts (the local timer, rescheduling, function call and TLB IPIs) taken there.
A runnable task or a device IRQ makes it refuse to boot; --force boots anyway and prints the finding
as a warning above the numbers. The CPU-local interrupts are printed and do not refuse: no affinity
setting moves them, and only nohz_full at host boot would quiet the timer.

What needs root to keep the host off the measured cores is tools/isolate-pinned.sh, which the human
runs around the measurements: apply stops irqbalance, points the IRQs away from the measured CPUs and
their SMT siblings, takes the siblings offline, turns boost off and pins the measured CPUs' cpufreq
minimum to their maximum; undo restores each. Give it every CPU the runs use; on a 16-core part with
two L3s, within0 uses CPUs 6 and 7, within1 14 and 15, and across 7 and 15:

    sudo tools/isolate-pinned.sh apply 6 7 14 15
    tools/measure-pinned.py within0; tools/measure-pinned.py within1; tools/measure-pinned.py across
    sudo tools/isolate-pinned.sh undo
"""
import glob
import os
import re
import subprocess
import sys
import threading
import time

LINES = re.compile(r"IPC round trip|sys_mresolve (?:alone|contended):|flush IPI|kernel lock:|contention test lock:")


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
    """The two host CPUs the placement mode names, from physical_cores_by_l3() in the order of each
    L3's first CPU."""
    groups = physical_cores_by_l3()
    within = re.fullmatch(r"within(\d)", mode)
    if within and int(within.group(1)) < len(groups):
        return groups[int(within.group(1))][-2], groups[int(within.group(1))][-1]
    if mode == "across" and len(groups) > 1:
        return groups[0][-1], groups[1][-1]
    sys.exit(f"FAIL: no placement {mode} on a host with {len(groups)} L3s; "
             + __doc__.splitlines()[2])


def siblings(pair):
    """The measured CPUs and their online SMT siblings."""
    return sorted({sib for cpu in pair
                   for sib in expand(read(f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list"))})


def cpu_list(cpus):
    """cpus in the kernel's list format, such as 0-5,8-21."""
    runs = []
    for cpu in sorted(cpus):
        if runs and runs[-1][1] == cpu - 1:
            runs[-1][1] = cpu
        else:
            runs.append([cpu, cpu])
    return ",".join(f"{low}" if low == high else f"{low}-{high}" for low, high in runs)


def runnable_tasks(cpus):
    """(tid, comm, cpu) of each task outside this process that is runnable on one of cpus. The
    fields after comm's closing parenthesis start at state; processor is field 39 of stat."""
    found = set()
    for stat in glob.glob("/proc/[0-9]*/task/[0-9]*/stat"):
        if stat.startswith(f"/proc/{os.getpid()}/"):
            continue
        try:
            text = read(stat)
        except OSError:
            continue
        comm = text[text.index("(") + 1:text.rindex(")")]
        fields = text[text.rindex(")") + 2:].split()
        if fields[0] == "R" and int(fields[36]) in cpus:
            found.add((int(stat.split("/")[4]), comm, int(fields[36])))
    return found


def interrupts():
    """Maps each /proc/interrupts row that counts per online CPU to its description and those
    counts. ERR and MIS carry one machine-wide count and are left out."""
    with open("/proc/interrupts") as f:
        columns = [int(name[3:]) for name in f.readline().split()]
        rows = {}
        for line in f:
            name, _, rest = line.partition(":")
            words = rest.split()
            if len(words) >= len(columns) and all(word.isdigit() for word in words[:len(columns)]):
                rows[name.strip()] = (" ".join(words[len(columns):]),
                                      dict(zip(columns, map(int, words[:len(columns)]))))
    return rows


def routed_irqs(cpus):
    """Maps each IRQ whose effective affinity takes in one of cpus to those CPUs."""
    routed = {}
    for path in glob.glob("/proc/irq/[0-9]*/effective_affinity_list"):
        text = read(path)
        hit = set(expand(text)) & set(cpus) if text else set()
        if hit:
            routed[path.split("/")[3]] = sorted(hit)
    return routed


def noise(cpus, seconds=0.5):
    """What lands on cpus over seconds: runnable tasks, device IRQs routed or taken there, and the
    CPU-local interrupts taken there. Returns the lines that refuse a run and the lines that do not."""
    before, tasks = interrupts(), set()
    deadline = time.time() + seconds
    while time.time() < deadline:
        tasks |= runnable_tasks(cpus)
        time.sleep(0.02)
    after = interrupts()
    routed = routed_irqs(cpus)
    refusing = [f"task {tid} ({comm}) runnable on CPU {cpu}" for tid, comm, cpu in sorted(tasks)]
    local = []
    for name, (what, counts) in after.items():
        taken = {cpu: counts[cpu] - before.get(name, ("", {}))[1].get(cpu, 0) for cpu in cpus if cpu in counts}
        taken = {cpu: n for cpu, n in taken.items() if n}
        if name.isdigit() and (taken or name in routed):
            on = ", ".join(f"CPU {cpu}" for cpu in routed.get(name, []))
            fired = ", ".join(f"{n} on CPU {cpu}" for cpu, n in taken.items())
            refusing.append(f"IRQ {name} ({what})" + (f" routed to {on}" if on else "")
                            + (f", taken {fired}" if fired else ""))
        elif not name.isdigit() and taken:
            local.append(f"{name} ({what}): " + ", ".join(f"{n} on CPU {cpu}" for cpu, n in taken.items()))
    return refusing, local


def check_noise(pair, force):
    """Prints what noise() finds on the measured CPUs and their siblings, and exits before any boot
    when something there refuses the run and force is not set."""
    cpus = siblings(pair)
    refusing, local = noise(cpus)
    print(f"noise on CPUs {cpus} (measured and SMT siblings) over 0.5 s:")
    for line in refusing:
        print(f"  {'WARNING: ' if force else ''}{line}")
    for line in local:
        print(f"  local {line}")
    if not refusing:
        print("  no runnable task or device IRQ")
    elif force:
        print(f"WARNING: --force: measuring with {len(refusing)} tasks and IRQs on the measured CPUs or siblings")
    else:
        sys.exit(f"FAIL: {len(refusing)} tasks and IRQs on the measured CPUs or siblings; "
                 "see tools/isolate-pinned.sh, or pass --force to measure anyway")


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


def confine(pid, others, done, moved):
    """Until done is set, moves every thread of pid but the vCPU threads onto others whenever it may run
    elsewhere, and records (tid, comm, cpus it was allowed outside others, refusal or None) once per
    thread in moved; a refused thread is not tried again. Runs from a thread kept on others, after
    pin_vcpus has named and pinned both vCPU threads."""
    os.sched_setaffinity(0, others)
    seen, refused = set(), set()
    while not done.wait(0.001):
        for task in glob.glob(f"/proc/{pid}/task/*"):
            tid = int(task.split("/")[-1])
            try:
                name = read(f"{task}/comm")
                allowed = os.sched_getaffinity(tid)
            except OSError:
                continue
            if re.match(r"CPU \d/KVM", name) or allowed <= others or tid in refused:
                continue
            try:
                os.sched_setaffinity(tid, others)
            except OSError as error:
                refused.add(tid)
                moved.append((tid, name, sorted(allowed - others), error.strerror))
                continue
            if tid not in seen:
                seen.add(tid)
                moved.append((tid, name, sorted(allowed - others), None))


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


def boot(pair, others, out):
    initrd, log = f"{out}/initrd", f"{out}/serial.log"
    with open(initrd, "wb") as f:
        for name in ("kernel", "dom0"):
            f.write(open(f"target/x86_64-unknown-aloader/release/{name}", "rb").read())
    if os.path.exists(log):
        os.unlink(log)
    qemu = subprocess.Popen(
        ["qemu-system-x86_64", "-enable-kvm", "-cpu", "host", "-machine", "q35,kernel_irqchip=split",
         "-name", "guest=atmo,debug-threads=on", "-smp", "2", "-m", "8192", "-nographic",
         "-serial", f"file:{log}", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
         "-kernel", "target/x86_64-unknown-none/release/aloader", "-initrd", initrd],
        stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        preexec_fn=lambda: os.sched_setaffinity(0, others))
    pin_vcpus(qemu.pid, pair)
    samples = {cpu: [] for cpu in pair}
    moved = []
    done = threading.Event()
    paths = {cpu: f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/{clock_source(cpu)}" for cpu in pair}
    workers = [threading.Thread(target=sample_clocks, args=(paths, others, done, samples)),
               threading.Thread(target=confine, args=(qemu.pid, others, done, moved))]
    for worker in workers:
        worker.start()
    try:
        qemu.wait(timeout=300)
    except subprocess.TimeoutExpired:
        qemu.kill()
        sys.exit(f"FAIL: no exit within 300 s; see {log}")
    finally:
        done.set()
        for worker in workers:
            worker.join()
    return open(log, "rb").read().decode(errors="replace"), samples, moved


def main():
    mode = sys.argv[1]
    rest = sys.argv[2:]
    lock_stats = "--lock-stats" in rest
    force = "--force" in rest
    boots = next((int(a) for a in rest if a.isdigit()), 3)
    pair = choose(mode)
    out = "target/measure-pinned"
    os.makedirs(out, exist_ok=True)
    build(lock_stats)
    others = set(os.sched_getaffinity(0)) - set(siblings(pair))
    print(f"{mode}: vCPUs on host CPUs {pair}, lock_stats {lock_stats}, load {os.getloadavg()[0]:.2f}")
    print(f"  measured and SMT siblings: {cpu_list(siblings(pair))}; QEMU's other threads on {cpu_list(others)}")
    for cpu in pair:
        print(f"  L3 of CPU {cpu}: {read(f'/sys/devices/system/cpu/cpu{cpu}/cache/index3/shared_cpu_list')}")
    check_noise(pair, force)
    for i in range(boots):
        log, samples, moved = boot(pair, others, out)
        if "dom0 benchmark done" not in log:
            sys.exit(f"FAIL: boot {i} did not finish; see {out}/serial.log")
        print(f"boot {i}, load {os.getloadavg()[0]:.2f}")
        for tid, name, cpus, refused in moved:
            if refused:
                print(f"  WARNING: thread {tid} ({name}) could not be moved off CPUs {cpu_list(cpus)}: {refused}")
            else:
                print(f"  moved thread {tid} ({name}) off CPUs {cpu_list(cpus)}")
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
