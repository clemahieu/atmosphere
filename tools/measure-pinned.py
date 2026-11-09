#!/usr/bin/env python3
"""Boot dom0 under KVM with its two vCPUs pinned, and print the kernel's own timing lines.

usage: tools/measure-pinned.py within0|within1|across [boots] [--lock-stats] [--force]   (from the workspace root)
       tools/measure-pinned.py --test                                                      (this script's own tests)

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
A runnable task, a device IRQ taken there, or a device IRQ routed there that the isolation could move
makes it refuse to boot; --force boots anyway and prints the finding as a warning above the numbers.
A device IRQ routed there that the kernel would not move, which tools/isolate-pinned.sh apply records
in its state, is printed as fixed and does not refuse unless it fired: such an IRQ is managed, as an
NVMe queue's is, held to the CPUs that submit its I/O, and nothing submits I/O from a measured CPU
while only a vCPU thread runs there. The CPU-local interrupts are printed and do not refuse: no
affinity setting moves them, and only nohz_full at host boot would quiet the timer.

What needs root to keep the host off the measured cores is tools/isolate-pinned.sh, which the human
runs around the measurements: apply stops irqbalance, points the IRQs away from the measured CPUs and
their SMT siblings, turns boost off, pins the measured CPUs' cpufreq minimum to their maximum and
takes the siblings offline; undo restores each. Give it every CPU the runs use; on a 16-core part with
two L3s, within0 uses CPUs 6 and 7, within1 14 and 15, and across 7 and 15:

    sudo tools/isolate-pinned.sh apply 6 7 14 15
    tools/measure-pinned.py within0; tools/measure-pinned.py within1; tools/measure-pinned.py across
    sudo tools/isolate-pinned.sh undo
"""
import glob
import os
import re
import shutil
import subprocess
import tempfile
import sys
import threading
import time
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import firmware
import run as guest

# What tools/isolate-pinned.sh apply changed, for its undo; its fixed lines name the IRQs it could not move.
ISOLATION_STATE = "/run/atmo-isolate-pinned"
LINES = re.compile(r"flush IPI|kernel lock:|contention test lock:")


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


def fixed_irqs(state=ISOLATION_STATE):
    """Maps each IRQ the kernel refused to move under tools/isolate-pinned.sh apply to the refusal, from
    the fixed lines of the state it writes; empty when the isolation is not applied."""
    try:
        with open(state) as f:
            lines = f.read().splitlines()
    except FileNotFoundError:
        return {}
    fixed = {}
    for line in lines:
        kind, _, rest = line.partition(" ")
        if kind == "fixed":
            irq, _, reason = rest.partition(" ")
            fixed[irq] = reason
    return fixed


def classify(cpus, before, after, routed, fixed, tasks):
    """Sorts what landed on cpus into the lines that refuse a run, the lines for IRQs routed there that
    no affinity write can move and that did not fire, and the CPU-local interrupts taken there. before
    and after are interrupts() around the sample, routed is routed_irqs(cpus), fixed is fixed_irqs(),
    and tasks is runnable_tasks(cpus) over the sample. A device IRQ refuses when it fired on cpus, or
    when it is routed there and the isolation could have moved it."""
    refusing = [f"task {tid} ({comm}) runnable on CPU {cpu}" for tid, comm, cpu in sorted(tasks)]
    held, local = [], []
    for name, (what, counts) in after.items():
        taken = {cpu: counts[cpu] - before.get(name, ("", {}))[1].get(cpu, 0) for cpu in cpus if cpu in counts}
        taken = {cpu: n for cpu, n in taken.items() if n}
        on = ", ".join(f"CPU {cpu}" for cpu in routed.get(name, []))
        if name.isdigit() and (taken or (name in routed and name not in fixed)):
            fired = ", ".join(f"{n} on CPU {cpu}" for cpu, n in taken.items())
            refusing.append(f"IRQ {name} ({what})" + (f" routed to {on}" if on else "")
                            + (f", taken {fired}" if fired else ""))
        elif name.isdigit() and name in routed:
            held.append(f"IRQ {name} ({what}) routed to {on}, which the kernel would not move "
                        f"({fixed[name]}), did not fire")
        elif not name.isdigit() and taken:
            local.append(f"{name} ({what}): " + ", ".join(f"{n} on CPU {cpu}" for cpu, n in taken.items()))
    return refusing, held, local


def noise(cpus, seconds=0.5):
    """classify() over what lands on cpus over seconds."""
    before, tasks = interrupts(), set()
    deadline = time.time() + seconds
    while time.time() < deadline:
        tasks |= runnable_tasks(cpus)
        time.sleep(0.02)
    return classify(cpus, before, interrupts(), routed_irqs(cpus), fixed_irqs(), tasks)


def check_noise(pair, force):
    """Prints what noise() finds on the measured CPUs and their siblings, and exits before any boot
    when something there refuses the run and force is not set."""
    cpus = siblings(pair)
    refusing, held, local = noise(cpus)
    print(f"noise on CPUs {cpus} (measured and SMT siblings) over 0.5 s:")
    for line in refusing:
        print(f"  {'WARNING: ' if force else ''}{line}")
    for line in held:
        print(f"  fixed {line}")
    for line in local:
        print(f"  local {line}")
    if not refusing:
        print("  no runnable task, and no device IRQ that fired there or that the isolation could move")
    elif force:
        print(f"WARNING: --force: measuring with {len(refusing)} tasks and IRQs on the measured CPUs or siblings")
    else:
        sys.exit(f"FAIL: {len(refusing)} tasks and IRQs on the measured CPUs or siblings; "
                 "see tools/isolate-pinned.sh, or pass --force to measure anyway")


def build(lock_stats):
    subprocess.run(["cargo", "build", "-q", "--release"] + (["--features", "lock_stats"] if lock_stats else []),
                   cwd="kernel", check=True, env={**os.environ, "RUSTC_BOOTSTRAP": "1"})
    subprocess.run(["cargo", "build", "-q", "--release"], cwd="dom0", check=True,
                   env={**os.environ, "RUSTC_BOOTSTRAP": "1"})
    # The loader is the UEFI application OVMF boots.
    subprocess.run(["cargo", "build", "-q", "--release", "--target", "x86_64-unknown-uefi"], cwd="aloader",
                   check=True, env={**os.environ, "RUSTC_BOOTSTRAP": "1"})


def esp(out, ovmf_code, ovmf_vars):
    """Lays out the EFI system partition under out as tools/run.py does, and returns
    QEMU's arguments to boot it under OVMF: OVMF boots EFI/BOOT/BOOTX64.EFI, and the loader reads the
    kernel and dom0 ELF images concatenated in the file initrd beside it. OVMF writes its variable
    store, so it gets a copy."""
    root = f"{out}/esp"
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(f"{root}/EFI/BOOT")
    shutil.copy("target/x86_64-unknown-uefi/release/aloader.efi", f"{root}/EFI/BOOT/BOOTX64.EFI")
    with open(f"{root}/initrd", "wb") as f:
        for name in ("kernel", "dom0"):
            f.write(open(f"target/x86_64-unknown-aloader/release/{name}", "rb").read())
    shutil.copy(ovmf_vars, f"{out}/OVMF_VARS.fd")
    return ["-drive", f"if=pflash,format=raw,unit=0,readonly=on,file={ovmf_code}",
            "-drive", f"if=pflash,format=raw,unit=1,file={out}/OVMF_VARS.fd",
            "-drive", f"format=raw,file=fat:rw:{root}"]


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
    log = f"{out}/serial.log"
    ovmf_code, ovmf_vars, qemu_bin = firmware.require("tools/measure-pinned.py")
    drives = esp(out, ovmf_code, ovmf_vars)
    if os.path.exists(log):
        os.unlink(log)
    qemu = subprocess.Popen(
        [qemu_bin, "-enable-kvm", "-cpu", "host", "-machine", "q35,kernel_irqchip=split",
         "-name", "guest=atmo,debug-threads=on", "-smp", "2", "-m", str(guest.MEMORY_MIB), "-nographic",
         "-serial", f"file:{log}", "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04"] + drives,
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
        if "dom0 capability done" not in log:
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


class Tests(unittest.TestCase):
    CPUS = [6, 22]

    def counts(self, **rows):
        """interrupts() as it reads, from name=(description, count on CPU 6)."""
        return {name: (what, {6: n, 22: 0, 0: 100}) for name, (what, n) in rows.items()}

    def test_a_fixed_irq_routed_there_that_did_not_fire_does_not_refuse(self):
        before = self.counts(**{"123": ("nvme1q5", 40)})
        refusing, fixed, local = classify(self.CPUS, before, before, {"123": [6]}, {"123": "Input/output error"}, set())
        self.assertEqual(refusing, [])
        self.assertEqual(len(fixed), 1)
        self.assertIn("IRQ 123 (nvme1q5) routed to CPU 6", fixed[0])
        self.assertIn("Input/output error", fixed[0])

    def test_a_fixed_irq_that_fired_there_refuses(self):
        before = self.counts(**{"123": ("nvme1q5", 40)})
        after = self.counts(**{"123": ("nvme1q5", 42)})
        refusing, fixed, _ = classify(self.CPUS, before, after, {"123": [6]}, {"123": "Input/output error"}, set())
        self.assertEqual(refusing, ["IRQ 123 (nvme1q5) routed to CPU 6, taken 2 on CPU 6"])
        self.assertEqual(fixed, [])

    def test_an_irq_the_isolation_could_move_refuses_when_routed_there(self):
        before = self.counts(**{"142": ("amdgpu", 7)})
        refusing, fixed, _ = classify(self.CPUS, before, before, {"142": [6]}, {}, set())
        self.assertEqual(refusing, ["IRQ 142 (amdgpu) routed to CPU 6"])
        self.assertEqual(fixed, [])

    def test_an_irq_routed_elsewhere_refuses_when_it_fired_there(self):
        before = self.counts(**{"142": ("amdgpu", 7)})
        after = self.counts(**{"142": ("amdgpu", 8)})
        refusing, _, _ = classify(self.CPUS, before, after, {}, {}, set())
        self.assertEqual(refusing, ["IRQ 142 (amdgpu), taken 1 on CPU 6"])

    def test_an_irq_routed_elsewhere_that_did_not_fire_there_is_not_reported(self):
        before = self.counts(**{"142": ("amdgpu", 7)})
        self.assertEqual(classify(self.CPUS, before, before, {}, {}, set()), ([], [], []))

    def test_cpu_local_interrupts_are_printed_and_do_not_refuse(self):
        before = self.counts(LOC=("Local timer interrupts", 1000))
        after = self.counts(LOC=("Local timer interrupts", 1250))
        refusing, fixed, local = classify(self.CPUS, before, after, {}, {}, set())
        self.assertEqual((refusing, fixed), ([], []))
        self.assertEqual(local, ["LOC (Local timer interrupts): 250 on CPU 6"])

    def test_a_runnable_task_refuses(self):
        refusing, _, _ = classify(self.CPUS, {}, {}, {}, {}, {(4242, "stress", 22)})
        self.assertEqual(refusing, ["task 4242 (stress) runnable on CPU 22"])

    def test_fixed_irqs_reads_the_isolations_refusals_from_its_state(self):
        with tempfile.NamedTemporaryFile("w") as state:
            state.write("irqbalance\ndefault ffffffff\nirq 142 19\nfixed 123 Input/output error\n"
                        "fixed 141 Input/output error\noffline 22\n")
            state.flush()
            self.assertEqual(fixed_irqs(state.name), {"123": "Input/output error", "141": "Input/output error"})

    def test_fixed_irqs_is_empty_without_the_isolation(self):
        self.assertEqual(fixed_irqs("/nonexistent/atmo-isolate-pinned"), {})


if __name__ == "__main__":
    if sys.argv[1:] == ["--test"]:
        unittest.main(argv=sys.argv[:1])
    else:
        main()
