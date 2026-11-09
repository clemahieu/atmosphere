#!/usr/bin/env python3
"""Start one aarch64 KVM guest on orangepi5 and bring its serial log back.

The launch is the one recorded for this board: pinned to the A76 cluster, QEMU virt
with GICv3, KVM, 512 MiB, no NIC, EDK2 as firmware. The guest runs until the UEFI
shell is in the log, or until the boot timeout. The board holds an exclusive lock
so a second run does not start a second guest. The remote side watches this
process's stdin and kills QEMU when the local side dies. A timeout here does the
same.

When ssh cannot reach the host, this prints one skip line naming orangepi5 and
exits 0. A guest that starts and then fails is a failure. This command is not
part of atmo test.

usage: tools/orangepi-kvm.py [--ssh-host HOST] [--connect-timeout SEC] [--boot-timeout SEC]
       tools/orangepi-kvm.py --test
"""

import argparse
import ctypes
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
from pathlib import Path

sys.dont_write_bytecode = True

BOARD = "orangepi5"
SHELL_MARK = "UEFI Interactive Shell"

# Reads a boot-timeout line and a byte count from stdin, runs that many bytes
# as a bash script, and leaves the rest of stdin open for the script.
BOOTSTRAP = """
read -r boot_timeout || exit 1
read -r n || exit 1
script=$(mktemp)
head -c "$n" > "$script" || exit 1
ATMO_BOOT_TIMEOUT=$boot_timeout bash "$script"
status=$?
rm -f "$script"
exit "$status"
"""

# The board runs this. stdin stays open; EOF means the local side is gone.
REMOTE = r"""
set -u
lock=${ATMO_LOCK:-$HOME/.atmo-orangepi-kvm.lock}
exec 9>"$lock"
if ! flock -n 9; then
    echo "atmo-orangepi-kvm: lock held, not starting a second guest" >&2
    exit 2
fi
log=
err=
qpid=
aborted=0
case ${ATMO_BOOT_TIMEOUT:-20} in
    ''|*[!0-9]*) boot_timeout=20 ;;
    *) boot_timeout=$ATMO_BOOT_TIMEOUT ;;
esac

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
# Own process group so stopping the guest does not signal this shell.
set -m
# Recorded launch: taskset -c 4-7, virt with GICv3, KVM only, 512 MiB, no NIC, EDK2.
# Serial goes to a file so the shell banner can be read back after QEMU exits.
taskset -c 4-7 qemu-system-aarch64 \
    -M virt,gic-version=3 -accel kvm -cpu host -smp 2 -m 512 \
    -nographic -monitor none -nic none \
    -bios /usr/share/qemu-efi-aarch64/QEMU_EFI.fd \
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
    if grep -q -s -F 'UEFI Interactive Shell' "$log" || grep -q -s -F 'UEFI Interactive Shell' "$err"; then
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
stop_qemu
seen=0
if [ "$aborted" -eq 0 ]; then
    if grep -q -s -F 'UEFI Interactive Shell' "$log" || grep -q -s -F 'UEFI Interactive Shell' "$err"; then
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


def run(ssh_host, connect_timeout, boot_timeout):
    """Run the guest. Return a process exit code. 0 and a skip line when ssh cannot connect."""
    payload = f"{boot_timeout}\n{len(REMOTE.encode())}\n".encode() + REMOTE.encode()
    proc = subprocess.Popen(
        [
            "ssh",
            "-o", "BatchMode=yes",
            "-o", f"ConnectTimeout={connect_timeout}",
            ssh_host,
            "bash -c " + shlex.quote(BOOTSTRAP),
        ],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        preexec_fn=_die_with_parent,
    )
    assert proc.stdin is not None
    proc.stdin.write(payload)
    proc.stdin.flush()
    out_parts, err_parts = [], []
    threads = [
        threading.Thread(target=_read_all, args=(proc.stdout, out_parts)),
        threading.Thread(target=_read_all, args=(proc.stderr, err_parts)),
    ]
    for thread in threads:
        thread.start()
    try:
        code = proc.wait(timeout=boot_timeout + connect_timeout + 30)
    except subprocess.TimeoutExpired:
        proc.kill()
        code = proc.wait()
    for thread in threads:
        thread.join()
    out = b"".join(out_parts)
    err = b"".join(err_parts)
    if code == 255 and _unreachable(out + err):
        sys.stdout.write(f"skip: {BOARD} unreachable\n")
        return 0
    sys.stdout.buffer.write(out)
    sys.stderr.buffer.write(err)
    if code < 0:
        return 1
    return code


def _held(args, payload, env, timeout):
    """Run a process with stdin left open so the remote script does not see EOF."""
    proc = subprocess.Popen(
        args,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
    )
    assert proc.stdin is not None
    proc.stdin.write(payload)
    proc.stdin.flush()
    out_parts, err_parts = [], []
    threads = [
        threading.Thread(target=_read_all, args=(proc.stdout, out_parts)),
        threading.Thread(target=_read_all, args=(proc.stderr, err_parts)),
    ]
    for thread in threads:
        thread.start()
    try:
        code = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        code = proc.wait()
    for thread in threads:
        thread.join()
    return code, b"".join(out_parts), b"".join(err_parts)


def self_test():
    """Offline checks: the skip line, the recorded launch, the lock, and stdin EOF."""
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
        (fake_bin / "taskset").write_text(
            "#!/bin/bash\n"
            "if [ \"$1\" != \"-c\" ] || [ \"$2\" != \"4-7\" ]; then echo \"bad taskset $*\" >> \"$ATMO_ARGV\"; exit 9; fi\n"
            "shift 2\n"
            "printf '%s\\n' \"$@\" >> \"$ATMO_ARGV\"\n"
            "exec \"$@\"\n"
        )
        (fake_bin / "qemu-system-aarch64").write_text(
            "#!/bin/bash\n"
            "printf '%s\\n' \"$@\" >> \"$ATMO_ARGV\"\n"
            "log=\n"
            "args=(\"$@\")\n"
            "i=0\n"
            "while [ \"$i\" -lt \"${#args[@]}\" ]; do\n"
            "  if [ \"${args[$i]}\" = \"-serial\" ]; then spec=${args[$((i+1))]}; log=${spec#file:}; fi\n"
            "  i=$((i+1))\n"
            "done\n"
            "echo $$ > \"$ATMO_QEMU_PID\"\n"
            "if [ -n \"$log\" ]; then echo \"" + SHELL_MARK + " v2.2\" >> \"$log\"; fi\n"
            "sleep 60\n"
        )
        os.chmod(fake_bin / "taskset", 0o755)
        os.chmod(fake_bin / "qemu-system-aarch64", 0o755)
        env = os.environ.copy()
        env["PATH"] = f"{fake_bin}:/usr/bin:/bin"
        env["ATMO_ARGV"] = str(argv_file)
        env["ATMO_QEMU_PID"] = str(pid_file)
        env["ATMO_LOCK"] = str(tmp / "lock")
        env["ATMO_BOOT_TIMEOUT"] = "15"
        script = REMOTE.encode()
        payload = f"15\n{len(script)}\n".encode() + script
        code, out, err = _held(["bash", "-c", BOOTSTRAP], payload, env, 20)
        text = out.decode(errors="replace")
        recorded = argv_file.read_text() if argv_file.exists() else ""
        qemu_dead = True
        if pid_file.exists():
            pid = int(pid_file.read_text().strip())
            try:
                os.kill(pid, 0)
                qemu_dead = False
            except OSError:
                qemu_dead = True
        check("fake guest reaches the shell", code == 0 and SHELL_MARK in text and "kvm: accel kvm" in text and text.startswith("host: "), f"code={code} out={text!r} err={err!r}")
        check("fake guest is gone", qemu_dead, f"pid file {pid_file.read_text() if pid_file.exists() else 'missing'}")
        for needle in ("virt,gic-version=3", "-accel", "kvm", "-m", "512", "-nographic", "-nic", "none", "QEMU_EFI.fd"):
            check(f"launch has {needle}", needle in recorded, recorded)

        # A second run while the first holds the lock does not start a guest.
        sleeper = (fake_bin / "qemu-system-aarch64").read_text().replace(
            f'echo "{SHELL_MARK} v2.2" >> "$log"',
            "sleep 1",
        )
        (fake_bin / "qemu-system-aarch64").write_text(sleeper)
        env2 = dict(env)
        env2["ATMO_BOOT_TIMEOUT"] = "20"
        env2["ATMO_QEMU_PID"] = str(tmp / "qemu2.pid")
        first = subprocess.Popen(
            ["bash", "-c", BOOTSTRAP],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env2,
        )
        assert first.stdin is not None and first.stdout is not None
        first.stdin.write(f"20\n{len(script)}\n".encode() + script)
        first.stdin.flush()
        started = b""
        while b"guest: started" not in started:
            chunk = first.stdout.read(1)
            if not chunk:
                break
            started += chunk
        code2, sout, serr = _held(
            ["bash", "-c", BOOTSTRAP],
            f"20\n{len(script)}\n".encode() + script,
            env2,
            15,
        )
        check(
            "second run does not start a guest",
            code2 == 2 and b"not starting a second guest" in serr and b"guest: started" not in sout,
            f"code={code2} out={sout!r} err={serr!r}",
        )
        first.stdin.close()
        first.wait(timeout=15)
        qemu_dead = True
        pid_path = tmp / "qemu2.pid"
        if pid_path.exists():
            pid = int(pid_path.read_text().strip())
            try:
                os.kill(pid, 0)
                qemu_dead = False
            except OSError:
                qemu_dead = True
        check("closing stdin stops the guest", qemu_dead)
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
    parser.add_argument("--test", action="store_true", help="run this script's own tests")
    args = parser.parse_args(argv)
    if args.test:
        return self_test()
    if args.connect_timeout < 1 or args.boot_timeout < 1:
        print("timeouts are whole seconds", file=sys.stderr)
        return 2
    return run(args.ssh_host, args.connect_timeout, args.boot_timeout)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
