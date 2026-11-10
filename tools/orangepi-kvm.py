#!/usr/bin/env python3
"""Start one aarch64 KVM guest on orangepi5 and bring its serial log back.

The launch is the one recorded for this board: pinned to the A76 cluster, QEMU virt
with GICv3, KVM, no NIC, EDK2 as firmware, 512 MiB unless --memory-mib says otherwise,
and with --iommu an SMMUv3 in front of the PCI devices (iommu=smmuv3).
With --esp the directory goes to the board over the same ssh session and the guest
gets it as a FAT drive, which EDK2 boots as removable media from
EFI/BOOT/BOOTAA64.EFI; the board's copy is removed with the run. The guest runs
until the --wait-for line is in the log, the UEFI shell banner by default, or until
the boot timeout. With --until-exit it runs until QEMU exits by itself, which it does
when the guest powers off, and this exits with QEMU's status; a guest still on at the
boot timeout is stopped and the run fails. The board holds an exclusive lock, so it runs one guest
at a time: a second run waits for the lock for up to the boot timeout, then fails without starting
a guest. The remote side watches this process's stdin and kills QEMU when
the local side dies. A timeout here does the same.

When ssh cannot reach the host, this prints one skip line naming orangepi5 and
exits 0. A guest that starts and then fails is a failure. atmo test runs it as
its aarch64 boot, which takes the skip line as a pass.

usage: tools/orangepi-kvm.py [--ssh-host HOST] [--connect-timeout SEC] [--boot-timeout SEC]
                             [--esp DIR] [--memory-mib MIB] [--iommu] [--wait-for LINE | --until-exit]
       tools/orangepi-kvm.py --test
"""

import argparse
import ctypes
import io
import os
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import threading
from pathlib import Path

sys.dont_write_bytecode = True

BOARD = "orangepi5"
SHELL_MARK = "UEFI Interactive Shell"

# Reads the boot timeout, the guest's memory, whether it has an SMMUv3, the awaited line, whether the run waits
# for QEMU's exit instead, the ESP archive's size and the script's size from stdin, one per line, runs that many bytes as a
# bash script, and leaves the rest of stdin, which starts with the ESP archive,
# open for the script.
BOOTSTRAP = """
read -r boot_timeout || exit 1
read -r memory_mib || exit 1
read -r iommu || exit 1
IFS= read -r wait_for || exit 1
read -r until_exit || exit 1
read -r esp_bytes || exit 1
read -r n || exit 1
script=$(mktemp)
head -c "$n" > "$script" || exit 1
ATMO_BOOT_TIMEOUT=$boot_timeout ATMO_MEMORY_MIB=$memory_mib ATMO_IOMMU=$iommu ATMO_WAIT_FOR=$wait_for ATMO_UNTIL_EXIT=$until_exit ATMO_ESP_BYTES=$esp_bytes bash "$script"
status=$?
rm -f "$script"
exit "$status"
"""

# The board runs this. stdin stays open; EOF means the local side is gone.
REMOTE = r"""
set -u
case ${ATMO_BOOT_TIMEOUT:-20} in
    ''|*[!0-9]*) boot_timeout=20 ;;
    *) boot_timeout=$ATMO_BOOT_TIMEOUT ;;
esac
# One guest at a time. A run that finds the board taken waits its turn, for as long as one guest
# may take, so gates that overlap queue here.
lock=${ATMO_LOCK:-$HOME/.atmo-orangepi-kvm.lock}
exec 9>"$lock"
if ! flock -w "$boot_timeout" 9; then
    echo "atmo-orangepi-kvm: lock held for $boot_timeout s, not starting a second guest" >&2
    exit 2
fi
log=
err=
esp=
qpid=
aborted=0
until_exit=${ATMO_UNTIL_EXIT:-0}

stop_qemu() {
    if [ -n "$qpid" ]; then
        pid=$qpid
        qpid=
        # The guest is its own process group, so this also stops a child QEMU left behind.
        kill -- -"$pid" 2>/dev/null || kill "$pid" 2>/dev/null || true
        n=0
        while kill -0 "$pid" 2>/dev/null && [ "$n" -lt 20 ]; do
            sleep 0.1
            n=$((n + 1))
        done
        kill -9 -- -"$pid" 2>/dev/null || kill -9 "$pid" 2>/dev/null || true
        wait "$pid" 2>/dev/null || true
    fi
}

cleanup() {
    stop_qemu
    [ -n "$log" ] && rm -f "$log"
    [ -n "$err" ] && rm -f "$err"
    [ -n "$esp" ] && rm -rf "$esp"
}

on_signal() {
    aborted=1
    exit 1
}

trap on_signal HUP INT TERM
trap cleanup EXIT

echo "host: $(hostname)"
echo "kvm: accel kvm"
log=$(mktemp)
err=$(mktemp)
drive=()
if [ "$ATMO_ESP_BYTES" -gt 0 ]; then
    esp=$(mktemp -d -t atmo-esp.XXXXXX)
    head -c "$ATMO_ESP_BYTES" | tar -x -C "$esp" || exit 1
    drive=(-drive "if=none,id=esp,format=raw,file=fat:rw:$esp" -device virtio-blk-pci,drive=esp)
fi
machine=virt,gic-version=3
if [ "${ATMO_IOMMU:-0}" -eq 1 ]; then
    machine=$machine,iommu=smmuv3
fi
# Own process group so stopping the guest does not signal this shell.
set -m
# Recorded launch: taskset -c 4-7, virt with GICv3, KVM only, no NIC, EDK2.
# Serial goes to a file so the awaited line can be read back after QEMU exits.
taskset -c 4-7 qemu-system-aarch64 \
    -M "$machine" -accel kvm -cpu host -smp 2 -m "$ATMO_MEMORY_MIB" \
    -nographic -monitor none -nic none \
    -bios /usr/share/qemu-efi-aarch64/QEMU_EFI.fd \
    "${drive[@]}" \
    -serial "file:$log" \
    < /dev/null >"$err" 2>&1 &
qpid=$!
if ! kill -0 "$qpid" 2>/dev/null; then
    stop_qemu
    cat "$log" "$err"
    exit 1
fi
echo "guest: started"
deadline=$((SECONDS + boot_timeout))
while kill -0 "$qpid" 2>/dev/null; do
    if [ "$until_exit" -eq 0 ] && { grep -q -s -F -- "$ATMO_WAIT_FOR" "$log" || grep -q -s -F -- "$ATMO_WAIT_FOR" "$err"; }; then
        break
    fi
    if [ "$SECONDS" -ge "$deadline" ]; then
        break
    fi
    # `if read; then` would hide the status: a failed read makes the if return 0.
    IFS= read -r -t 1 _
    read_status=$?
    if [ "$read_status" -eq 0 ]; then
        continue
    fi
    if [ "$read_status" -le 128 ]; then
        aborted=1
        break
    fi
done
if [ "$until_exit" -eq 1 ]; then
    if [ "$aborted" -eq 1 ]; then
        exit 1
    fi
    if kill -0 "$qpid" 2>/dev/null; then
        stop_qemu
        cat "$log"
        cat "$err"
        echo "qemu: still running after $boot_timeout s"
        exit 1
    fi
    wait "$qpid"
    status=$?
    qpid=
    cat "$log"
    cat "$err"
    echo "qemu: exit $status"
    exit "$status"
fi
stop_qemu
seen=0
if [ "$aborted" -eq 0 ]; then
    if grep -q -s -F -- "$ATMO_WAIT_FOR" "$log" || grep -q -s -F -- "$ATMO_WAIT_FOR" "$err"; then
        seen=1
    fi
fi
cat "$log"
cat "$err"
if [ "$seen" -eq 1 ]; then
    exit 0
fi
exit 1
"""

_LIBC = ctypes.CDLL(None, use_errno=True)


def _die_with_parent():
    """SIGHUP this process if its parent dies, including by SIGKILL."""
    _LIBC.prctl(1, 1)


def _unreachable(blob):
    needles = (
        b"ssh: connect to host",
        b"Could not resolve",
        b"Name or service not known",
        b"No route to host",
        b"Network is unreachable",
        b"Connection timed out",
        b"Connection refused",
    )
    return any(needle in blob for needle in needles)


def _read_all(pipe, sink):
    sink.append(pipe.read())


def _esp_archive(directory):
    """The ESP directory's files as a tar archive, for the board to unpack."""
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w", dereference=True) as archive:
        archive.add(directory, arcname=".")
    return buffer.getvalue()


def _payload(boot_timeout, memory_mib, wait_for, esp, until_exit=False, iommu=False):
    """What BOOTSTRAP reads from stdin: the parameters, the remote script, the ESP archive."""
    script = REMOTE.encode()
    head = f"{boot_timeout}\n{memory_mib}\n{int(iommu)}\n{wait_for}\n{int(until_exit)}\n{len(esp)}\n{len(script)}\n"
    return head.encode() + script + esp


def _held(args, payload, env, timeout, preexec_fn=None):
    """Run a process with stdin left open so the remote script does not see EOF."""
    proc = subprocess.Popen(
        args,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        preexec_fn=preexec_fn,
    )
    assert proc.stdin is not None
    out_parts, err_parts = [], []
    threads = [
        threading.Thread(target=_read_all, args=(proc.stdout, out_parts)),
        threading.Thread(target=_read_all, args=(proc.stderr, err_parts)),
    ]
    for thread in threads:
        thread.start()
    try:
        proc.stdin.write(payload)
        proc.stdin.flush()
    except BrokenPipeError:
        # The process ended before reading everything, as ssh does when it cannot connect.
        pass
    try:
        code = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        code = proc.wait()
    for thread in threads:
        thread.join()
    return code, b"".join(out_parts), b"".join(err_parts)


def run(ssh_host, connect_timeout, boot_timeout, memory_mib, wait_for, esp_dir, until_exit, iommu):
    """Run the guest. Return a process exit code. 0 and a skip line when ssh cannot connect."""
    esp = _esp_archive(esp_dir) if esp_dir is not None else b""
    code, out, err = _held(
        [
            "ssh",
            "-o", "BatchMode=yes",
            "-o", f"ConnectTimeout={connect_timeout}",
            ssh_host,
            "bash -c " + shlex.quote(BOOTSTRAP),
        ],
        _payload(boot_timeout, memory_mib, wait_for, esp, until_exit, iommu),
        None,
        # The wait for the board's lock, then the guest's own run.
        2 * boot_timeout + connect_timeout + 30,
        preexec_fn=_die_with_parent,
    )
    if code == 255 and _unreachable(out + err):
        sys.stdout.write(f"skip: {BOARD} unreachable\n")
        return 0
    sys.stdout.buffer.write(out)
    sys.stderr.buffer.write(err)
    if code < 0:
        return 1
    return code


# Stand-ins for the board's commands, for --test. The fake QEMU records its
# arguments, reads the ESP it was given, and writes ATMO_FAKE_SERIAL to its serial log.
FAKE_TASKSET = r"""#!/bin/bash
if [ "$1" != "-c" ] || [ "$2" != "4-7" ]; then echo "bad taskset $*" >> "$ATMO_ARGV"; exit 9; fi
shift 2
printf '%s\n' "$@" >> "$ATMO_ARGV"
exec "$@"
"""

FAKE_QEMU = r"""#!/bin/bash
printf '%s\n' "$@" >> "$ATMO_ARGV"
log=
esp=
args=("$@")
i=0
while [ "$i" -lt "${#args[@]}" ]; do
  case ${args[$i]} in
    -serial) spec=${args[$((i+1))]}; log=${spec#file:} ;;
    -drive) spec=${args[$((i+1))]}; esp=${spec##*file=fat:rw:} ;;
  esac
  i=$((i+1))
done
echo $$ > "$ATMO_QEMU_PID"
if [ -n "$esp" ]; then
  echo "$esp" > "$ATMO_ESP_SEEN"
  cat "$esp/EFI/BOOT/BOOTAA64.EFI" "$esp/initrd" > "$ATMO_ESP_READ"
fi
if [ -n "$ATMO_FAKE_SERIAL" ]; then printf '%s\n' "$ATMO_FAKE_SERIAL" >> "$log"; fi
if [ -n "$ATMO_FAKE_EXIT" ]; then exit "$ATMO_FAKE_EXIT"; fi
sleep 60
"""

# Runs the remote command here, as the board's login shell would.
FAKE_SSH = r"""#!/bin/bash
exec bash -c "${@: -1}"
"""


def self_test():
    """Offline checks: the skip line, the recorded launch, the ESP, the awaited line, the lock, and stdin EOF."""
    failures = []

    def check(name, ok, detail=""):
        if ok:
            print(f"ok   {name}")
        else:
            failures.append(name)
            print(f"FAIL {name} {detail}")

    skip = subprocess.run(
        [sys.executable, str(Path(__file__).resolve()), "--ssh-host", "192.0.2.1", "--connect-timeout", "3"],
        capture_output=True,
        text=True,
    )
    check(
        "unreachable host skips",
        skip.returncode == 0 and skip.stdout == f"skip: {BOARD} unreachable\n",
        f"code={skip.returncode} stdout={skip.stdout!r} stderr={skip.stderr!r}",
    )

    tmp = Path(tempfile.mkdtemp(prefix="atmo-opi-"))
    try:
        fake_bin = tmp / "bin"
        fake_bin.mkdir()
        argv_file = tmp / "argv"
        pid_file = tmp / "qemu.pid"
        for name, text in (("taskset", FAKE_TASKSET), ("qemu-system-aarch64", FAKE_QEMU), ("ssh", FAKE_SSH)):
            (fake_bin / name).write_text(text)
            os.chmod(fake_bin / name, 0o755)
        env = os.environ.copy()
        env["PATH"] = f"{fake_bin}:/usr/bin:/bin"
        env["ATMO_ARGV"] = str(argv_file)
        env["ATMO_QEMU_PID"] = str(pid_file)
        env["ATMO_LOCK"] = str(tmp / "lock")
        env["ATMO_FAKE_SERIAL"] = f"{SHELL_MARK} v2.2"
        env["ATMO_ESP_SEEN"] = str(tmp / "esp-seen")
        env["ATMO_ESP_READ"] = str(tmp / "esp-read")

        def gone(path):
            if not path.exists():
                return True
            try:
                os.kill(int(path.read_text().strip()), 0)
            except OSError:
                return True
            return False

        payload = _payload(15, 512, SHELL_MARK, b"")
        code, out, err = _held(["bash", "-c", BOOTSTRAP], payload, env, 20)
        text = out.decode(errors="replace")
        recorded = argv_file.read_text() if argv_file.exists() else ""
        check("fake guest reaches the shell", code == 0 and SHELL_MARK in text and "kvm: accel kvm" in text and text.startswith("host: "), f"code={code} out={text!r} err={err!r}")
        check("fake guest is gone", gone(pid_file), f"pid file {pid_file.read_text() if pid_file.exists() else 'missing'}")
        for needle in ("-M\nvirt,gic-version=3\n", "-accel\nkvm\n", "-m\n512\n", "-nographic", "-nic\nnone\n", "QEMU_EFI.fd"):
            check(f"launch has {needle!r}", needle in recorded, recorded)
        check("launch without an ESP has no drive", "-drive" not in recorded and "-device" not in recorded, recorded)
        check("launch without --iommu has no SMMU", "iommu" not in recorded, recorded)

        argv_file.unlink()
        code, out, err = _held(["bash", "-c", BOOTSTRAP], _payload(15, 512, SHELL_MARK, b"", iommu=True), env, 20)
        recorded = argv_file.read_text() if argv_file.exists() else ""
        check(
            "launch with --iommu puts an SMMUv3 on virt",
            code == 0 and "-M\nvirt,gic-version=3,iommu=smmuv3\n" in recorded,
            f"code={code} argv={recorded!r} err={err!r}",
        )
        check("guest with an SMMUv3 is gone", gone(pid_file))

        # The command line, over a fake ssh that runs the remote side here: an ESP
        # directory reaches QEMU as a FAT drive, the guest gets the memory asked for,
        # the run ends on the awaited line, and the copy of the ESP is removed.
        esp = tmp / "esp"
        (esp / "EFI" / "BOOT").mkdir(parents=True)
        (esp / "EFI" / "BOOT" / "BOOTAA64.EFI").write_bytes(b"loader\x00bytes\n")
        (esp / "initrd").write_bytes(bytes(range(256)) * 1024)
        argv_file.unlink()
        env_cli = dict(env)
        env_cli["ATMO_FAKE_SERIAL"] = f"{SHELL_MARK} v2.2\natmo: handoff to the kernel"
        cli = [sys.executable, str(Path(__file__).resolve()), "--boot-timeout", "15"]
        booted = subprocess.run(
            cli + ["--esp", str(esp), "--memory-mib", "2560", "--iommu", "--wait-for", "atmo: handoff"],
            capture_output=True,
            text=True,
            env=env_cli,
            timeout=60,
        )
        recorded = argv_file.read_text() if argv_file.exists() else ""
        seen = Path(env["ATMO_ESP_SEEN"])
        read_back = Path(env["ATMO_ESP_READ"])
        check(
            "run with an ESP ends on the awaited line",
            booted.returncode == 0 and "atmo: handoff to the kernel" in booted.stdout,
            f"code={booted.returncode} out={booted.stdout!r} err={booted.stderr!r}",
        )
        check("launch has the memory asked for", "-m\n2560\n" in recorded, recorded)
        check("--iommu on the command line reaches the launch", "-M\nvirt,gic-version=3,iommu=smmuv3\n" in recorded, recorded)
        check(
            "launch boots the ESP as a virtio FAT drive",
            seen.exists()
            and f"-drive\nif=none,id=esp,format=raw,file=fat:rw:{seen.read_text().strip()}\n" in recorded
            and "-device\nvirtio-blk-pci,drive=esp\n" in recorded,
            recorded,
        )
        check(
            "guest reads the ESP's files",
            read_back.exists() and read_back.read_bytes() == b"loader\x00bytes\n" + bytes(range(256)) * 1024,
        )
        check(
            "copy of the ESP is removed",
            seen.exists() and seen.read_text().strip() != str(esp) and not Path(seen.read_text().strip()).exists(),
            seen.read_text() if seen.exists() else "no ESP seen",
        )
        check("guest with an ESP is gone", gone(pid_file))

        # An ESP larger than a pipe holds does not turn an unreachable board into a failure.
        skip = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--ssh-host", "192.0.2.1", "--connect-timeout", "3", "--esp", str(esp)],
            capture_output=True,
            text=True,
            timeout=60,
        )
        check(
            "unreachable host skips with an ESP to send",
            skip.returncode == 0 and skip.stdout == f"skip: {BOARD} unreachable\n",
            f"code={skip.returncode} stdout={skip.stdout!r} stderr={skip.stderr!r}",
        )

        # The awaited line decides the run: the shell banner alone does not end it.
        env_cli["ATMO_FAKE_SERIAL"] = f"{SHELL_MARK} v2.2"
        missed = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), "--boot-timeout", "2", "--wait-for", "atmo: handoff"],
            capture_output=True,
            text=True,
            env=env_cli,
            timeout=60,
        )
        check(
            "run without the awaited line fails at the timeout",
            missed.returncode == 1 and SHELL_MARK in missed.stdout and "atmo: handoff" not in missed.stdout,
            f"code={missed.returncode} out={missed.stdout!r} err={missed.stderr!r}",
        )
        check("guest that missed the line is gone", gone(pid_file))

        # With --until-exit the run ends when QEMU does, with QEMU's status, and the awaited line
        # does not end it: a guest that prints its last line and stays on fails at the timeout.
        last_line = "The system is shutting down..."
        for status in (0, 3):
            env_exit = dict(env_cli)
            env_exit["ATMO_FAKE_SERIAL"] = f"{SHELL_MARK} v2.2\n{last_line}"
            env_exit["ATMO_FAKE_EXIT"] = str(status)
            ended = subprocess.run(cli + ["--until-exit"], capture_output=True, text=True, env=env_exit, timeout=60)
            check(
                f"run until exit ends with QEMU's status {status}",
                ended.returncode == status and last_line in ended.stdout and f"qemu: exit {status}\n" in ended.stdout,
                f"code={ended.returncode} out={ended.stdout!r} err={ended.stderr!r}",
            )
            check(f"guest that exited with {status} is gone", gone(pid_file))
        env_on = dict(env_cli)
        env_on["ATMO_FAKE_SERIAL"] = f"{SHELL_MARK} v2.2\n{last_line}"
        stayed = subprocess.run(
            cli + ["--boot-timeout", "2", "--until-exit"], capture_output=True, text=True, env=env_on, timeout=60
        )
        check(
            "run until exit fails when the guest is still on at the timeout",
            stayed.returncode == 1 and last_line in stayed.stdout and "qemu: still running after 2 s\n" in stayed.stdout,
            f"code={stayed.returncode} out={stayed.stdout!r} err={stayed.stderr!r}",
        )
        check("guest still on at the timeout is gone", gone(pid_file))

        for name, extra in (
            ("ESP that is not a directory", ["--esp", str(esp / "initrd")]),
            ("empty awaited line", ["--wait-for", ""]),
            ("awaited text of two lines", ["--wait-for", "one\ntwo"]),
            ("guest without memory", ["--memory-mib", "0"]),
            ("awaited line with --until-exit", ["--until-exit", "--wait-for", "atmo: handoff"]),
        ):
            argv_file.unlink(missing_ok=True)
            refused = subprocess.run(cli + extra, capture_output=True, text=True, env=env_cli, timeout=60)
            check(
                f"{name} is refused before ssh",
                refused.returncode == 2 and not argv_file.exists(),
                f"code={refused.returncode} err={refused.stderr!r}",
            )

        # A second run while the first holds the lock waits for it, and starts no guest when the
        # wait outlasts its boot timeout.
        env2 = dict(env)
        env2["ATMO_FAKE_SERIAL"] = ""
        env2["ATMO_QEMU_PID"] = str(tmp / "qemu2.pid")
        payload = _payload(20, 512, SHELL_MARK, b"")
        first = subprocess.Popen(
            ["bash", "-c", BOOTSTRAP],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env2,
        )
        assert first.stdin is not None and first.stdout is not None
        first.stdin.write(payload)
        first.stdin.flush()
        started = b""
        while b"guest: started" not in started:
            chunk = first.stdout.read(1)
            if not chunk:
                break
            started += chunk
        code2, sout, serr = _held(["bash", "-c", BOOTSTRAP], _payload(2, 512, SHELL_MARK, b""), env2, 15)
        check(
            "second run whose wait runs out does not start a guest",
            code2 == 2 and b"not starting a second guest" in serr and b"guest: started" not in sout,
            f"code={code2} out={sout!r} err={serr!r}",
        )
        env3 = dict(env)
        env3["ATMO_QEMU_PID"] = str(tmp / "qemu3.pid")
        queued = subprocess.Popen(
            ["bash", "-c", BOOTSTRAP],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env3,
        )
        assert queued.stdin is not None
        queued.stdin.write(payload)
        queued.stdin.flush()
        try:
            queued.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass
        check("second run waits while the first holds the board", queued.poll() is None, f"code={queued.poll()}")
        first.stdin.close()
        first.wait(timeout=15)
        check("closing stdin stops the guest", gone(tmp / "qemu2.pid"))
        # Its stdin stays open until it ends: EOF there means the local side is gone.
        queued.wait(timeout=20)
        assert queued.stdout is not None and queued.stderr is not None
        qout, qerr = queued.stdout.read(), queued.stderr.read()
        queued.stdin.close()
        check(
            "second run starts its guest once the first is gone",
            queued.returncode == 0 and b"guest: started" in qout and SHELL_MARK.encode() in qout,
            f"code={queued.returncode} out={qout!r} err={qerr!r}",
        )
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        print(f"{len(failures)} failed")
        return 1
    return 0


def main(argv):
    parser = argparse.ArgumentParser(prog="tools/orangepi-kvm.py", description=__doc__.split("\n")[0])
    parser.add_argument("--ssh-host", default=BOARD, help="ssh destination (default orangepi5)")
    parser.add_argument("--connect-timeout", type=int, default=8)
    parser.add_argument("--boot-timeout", type=int, default=20)
    parser.add_argument("--esp", type=Path, metavar="DIR", help="directory the guest boots as its EFI system partition")
    parser.add_argument("--memory-mib", type=int, default=512, help="guest memory (default 512)")
    parser.add_argument("--iommu", action="store_true", help="put an SMMUv3 in front of the guest's PCI devices")
    end = parser.add_mutually_exclusive_group()
    end.add_argument("--wait-for", default=SHELL_MARK, metavar="LINE", help="serial text that ends the run (default the UEFI shell banner)")
    end.add_argument("--until-exit", action="store_true", help="run until QEMU exits by itself and exit with its status")
    parser.add_argument("--test", action="store_true", help="run this script's own tests")
    args = parser.parse_args(argv)
    if args.test:
        return self_test()
    if args.connect_timeout < 1 or args.boot_timeout < 1:
        print("timeouts are whole seconds", file=sys.stderr)
        return 2
    if args.memory_mib < 1:
        print("memory is a whole number of MiB", file=sys.stderr)
        return 2
    if not args.wait_for or "\n" in args.wait_for:
        print("the awaited text is one line and not empty", file=sys.stderr)
        return 2
    if args.esp is not None and not args.esp.is_dir():
        print(f"{args.esp} is not a directory", file=sys.stderr)
        return 2
    return run(
        args.ssh_host, args.connect_timeout, args.boot_timeout, args.memory_mib, args.wait_for, args.esp, args.until_exit, args.iommu
    )


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
