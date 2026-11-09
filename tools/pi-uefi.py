#!/usr/bin/env python3
"""Boot a 512 MiB aarch64 virt guest on orangepi5 until the UEFI shell.

The guest is this proof's size. The Atmosphere run passes the size in
tools/run.py, and atmo-6x9.13.1.12 is what adds that run to the gate. This
command is not part of atmo test. A board ssh cannot reach exits 0 and prints
one skip line; a guest that starts and then fails is a failure.

Pin the guest to the A76 cores. A guest that spans both clusters fails vCPU
init on this big.LITTLE board. No NIC: this QEMU build has no efi-virtio.rom,
and the shell proof does not need one.

usage: tools/pi-uefi.py [--host orangepi5] [--timeout SECONDS]
       tools/pi-uefi.py --test
"""

import argparse
import os
import select
import shlex
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from pathlib import Path

HOST = "orangepi5"
CONNECT_TIMEOUT = 8
DEFAULT_TIMEOUT = 30
LOCK_PATH = "/tmp/atmo-pi-uefi.lock"
# PR_SET_PDEATHSIG. The ssh child gets SIGTERM when this process dies, including
# SIGKILL, so the board's QEMU is not left running.
PR_SET_PDEATHSIG = 1
QEMU_COMMAND = (
    "taskset -c 4-7 qemu-system-aarch64 -M virt,gic-version=3 -accel kvm "
    "-cpu host -smp 2 -m 512 -nographic -nic none "
    "-bios /usr/share/qemu-efi-aarch64/QEMU_EFI.fd -serial mon:stdio"
)
SHELL_MARKERS = (b"UEFI Interactive Shell", b"Shell>")
SKIP = b"skip: orangepi5 unreachable\n"


def remote_script():
    """The board-side script. ATMO_PI_LOCK and ATMO_PI_QEMU override the proof's
    lock and the QEMU command so a test can run it locally."""
    return textwrap.dedent(f"""\
        set -u
        lock=${{ATMO_PI_LOCK:-{LOCK_PATH}}}
        exec 9>"$lock"
        if ! flock -n 9; then
          echo "atmo-pi-uefi: lock held" >&2
          exit 2
        fi
        echo "host=orangepi5 accel=kvm hostname=$(hostname)"
        pid=
        catpid=
        out=
        cleanup() {{
          if [ -n "$pid" ]; then
            kill "$pid" 2>/dev/null || true
            wait "$pid" 2>/dev/null || true
            pid=
          fi
          if [ -n "$catpid" ]; then
            kill "$catpid" 2>/dev/null || true
            wait "$catpid" 2>/dev/null || true
            catpid=
          fi
          if [ -n "$out" ]; then
            rm -f "$out"
            out=
          fi
        }}
        trap cleanup EXIT HUP INT TERM
        if [ -n "${{ATMO_PI_QEMU:-}}" ]; then
          "$ATMO_PI_QEMU" </dev/null &
          pid=$!
        else
          # QEMU's serial is a fifo, not ssh's stdin. `read` blocks on that
          # stdin and returns when the local side closes it or dies, and the
          # trap then kills QEMU. -nographic would own the ssh stdin itself.
          out=/tmp/atmo-pi-uefi.$$.serial
          mkfifo "$out"
          cat "$out" &
          catpid=$!
          {QEMU_COMMAND} </dev/null >"$out" 2>&1 &
          pid=$!
        fi
        read -r _ || true
        cleanup
        """)


def ssh_command(host, script):
    # ssh joins its arguments and the remote shell parses the result, so the
    # script has to be one quoted word. Otherwise only `set` runs and the rest
    # is a second command.
    remote = "bash --noprofile --norc -c " + shlex.quote(script)
    return [
        "ssh",
        "-o", "BatchMode=yes",
        "-o", f"ConnectTimeout={CONNECT_TIMEOUT}",
        "-o", "ServerAliveInterval=2",
        "-o", "ServerAliveCountMax=2",
        host,
        remote,
    ]


def _release(proc):
    """Close stdin so the board-side read returns and kills QEMU, then wait
    until that shell has exited."""
    if proc.stdin is not None and not proc.stdin.closed:
        try:
            proc.stdin.close()
        except BrokenPipeError:
            pass
    try:
        proc.wait(timeout=8)
    except subprocess.TimeoutExpired:
        _stop(proc)
        return
    if proc.stdout is not None:
        proc.stdout.close()
        proc.stdout = None


def die_with_parent():
    """Ask the kernel to signal this process when its parent dies."""
    import ctypes
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(PR_SET_PDEATHSIG, signal.SIGTERM) != 0:
        os._exit(127)
    if os.getppid() == 1:
        os._exit(127)


def _stop(proc):
    if proc.poll() is None:
        proc.terminate()
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=2)
    if proc.stdout is not None:
        proc.stdout.close()
        proc.stdout = None


def drive(argv, script, timeout, release=False):
    """Run `argv` with `script` on stdin. Return (status, log).

    Status 0 and the skip line when ssh never starts a session. A session that
    reaches the UEFI shell is status 0. Anything else is the remote status, or
    1 when a timeout cuts off a session that did start.
    """
    proc = subprocess.Popen(
        argv,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        preexec_fn=die_with_parent,
    )
    if script is not None:
        try:
            proc.stdin.write(script.encode())
            proc.stdin.close()
        except BrokenPipeError:
            pass
    chunks = []
    deadline = time.monotonic() + timeout
    timed_out = False
    fd = proc.stdout.fileno()
    os.set_blocking(fd, False)
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            timed_out = True
            break
        ready, _, _ = select.select([fd], [], [], min(remaining, 0.2))
        if not ready:
            if proc.poll() is not None:
                break
            continue
        try:
            data = os.read(fd, 4096)
        except BlockingIOError:
            continue
        if not data:
            break
        chunks.append(data)
        if any(marker in b"".join(chunks) for marker in SHELL_MARKERS):
            (_release if release else _stop)(proc)
            return 0, b"".join(chunks)
    while True:
        try:
            data = os.read(fd, 4096)
        except BlockingIOError:
            break
        if not data:
            break
        chunks.append(data)
    (_release if release else _stop)(proc)
    log = b"".join(chunks)
    if any(marker in log for marker in SHELL_MARKERS):
        return 0, log
    started = b"host=orangepi5" in log
    if not started and proc.returncode == 255:
        return 0, SKIP
    if timed_out or proc.returncode in (0, None):
        return 1, log
    return proc.returncode, log


def run(host, timeout):
    return drive(ssh_command(host, remote_script()), None, timeout, release=True)


def main(argv):
    if argv == ["--test"]:
        unittest.main(argv=[sys.argv[0]])
        return 0
    parser = argparse.ArgumentParser(prog="tools/pi-uefi.py", description=__doc__.split("\n")[0])
    parser.add_argument("--host", default=HOST)
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    args = parser.parse_args(argv)
    status, log = run(args.host, args.timeout)
    sys.stdout.buffer.write(log)
    return status


class Tests(unittest.TestCase):
    def test_the_remote_script_locks_pins_and_kills(self):
        script = remote_script()
        self.assertIn("flock -n 9", script)
        self.assertIn(QEMU_COMMAND, script)
        self.assertIn("trap cleanup EXIT HUP INT TERM", script)
        self.assertIn("-m 512", script)
        self.assertIn("-accel kvm", script)
        self.assertIn("taskset -c 4-7", script)

    def test_ssh_is_batch_and_times_out_the_connect(self):
        command = ssh_command(HOST, "true")
        self.assertEqual(command[0], "ssh")
        self.assertNotIn("-tt", command)
        self.assertIn("BatchMode=yes", command)
        self.assertIn(f"ConnectTimeout={CONNECT_TIMEOUT}", command)
        self.assertEqual(command[-1], "bash --noprofile --norc -c " + shlex.quote("true"))
        self.assertIn(HOST, command)

    def test_unreachable_is_one_skip_line(self):
        code = "import sys; sys.stdout.write('ssh: connect to host orangepi5 port 22: Connection timed out\\n'); sys.exit(255)"
        status, log = drive([sys.executable, "-c", code], "unused", 5)
        self.assertEqual(status, 0)
        self.assertEqual(log, SKIP)
        self.assertEqual(log.count(b"\n"), 1)
        self.assertIn(b"orangepi5", log)

    def test_a_guest_that_fails_is_not_a_skip(self):
        code = (
            "import sys; sys.stdout.write('host=orangepi5 accel=kvm hostname=orangepi5\\n');"
            "sys.stdout.write('Failed to put registers after init\\n'); sys.exit(1)"
        )
        status, log = drive([sys.executable, "-c", code], "unused", 5)
        self.assertNotEqual(status, 0)
        self.assertNotIn(b"skip:", log)
        self.assertIn(b"Failed to put registers", log)

    def test_a_held_lock_is_not_a_skip(self):
        status, log = drive([sys.executable, "-c", "import sys; sys.exit(2)"], "unused", 5)
        self.assertEqual(status, 2)
        self.assertFalse(log.startswith(b"skip:"))

    def test_the_shell_stops_the_guest(self):
        code = (
            "import sys, time; sys.stdout.write('host=orangepi5 accel=kvm hostname=orangepi5\\n');"
            "sys.stdout.write('UEFI Interactive Shell v2.2\\n'); sys.stdout.flush(); time.sleep(30)"
        )
        started = time.monotonic()
        status, log = drive([sys.executable, "-c", code], "unused", 5)
        self.assertLess(time.monotonic() - started, 3)
        self.assertEqual(status, 0)
        self.assertIn(b"UEFI Interactive Shell", log)
        self.assertIn(b"accel=kvm", log)
        self.assertIn(b"orangepi5", log)

    def test_a_timeout_stops_a_guest_that_misses_the_shell(self):
        code = (
            "import sys, time; sys.stdout.write('host=orangepi5 accel=kvm hostname=orangepi5\\n');"
            "sys.stdout.flush(); time.sleep(30)"
        )
        started = time.monotonic()
        status, log = drive([sys.executable, "-c", code], "unused", 0.4)
        self.assertLess(time.monotonic() - started, 3)
        self.assertEqual(status, 1)
        self.assertNotIn(b"skip:", log)

    def test_a_second_run_does_not_start_a_guest_and_hangup_kills_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pidfile = root / "qemu.pid"
            guest = root / "guest.py"
            guest.write_text(textwrap.dedent(f"""\
                #!/usr/bin/env python3
                import os, signal, time
                signal.signal(signal.SIGHUP, signal.SIG_IGN)
                open({str(pidfile)!r}, "w").write(str(os.getpid()))
                while True:
                    time.sleep(0.05)
                """))
            guest.chmod(0o755)
            env = os.environ.copy()
            env["ATMO_PI_LOCK"] = str(root / "lock")
            env["ATMO_PI_QEMU"] = str(guest)
            first = subprocess.Popen(
                ["bash", "--noprofile", "--norc", "-c", remote_script()],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, env=env,
            )
            try:
                deadline = time.monotonic() + 5
                while not pidfile.exists():
                    if first.poll() is not None:
                        self.fail(first.stdout.read().decode())
                    self.assertLess(time.monotonic(), deadline)
                    time.sleep(0.05)
                second = subprocess.run(
                    ["bash", "-s"], input=remote_script().encode(),
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=env,
                )
                self.assertEqual(second.returncode, 2)
                self.assertIn(b"lock held", second.stdout)
                self.assertTrue(pidfile.exists())
                # Closing stdin is what a dead ssh does. `read` returns and the
                # trap kills the guest, which ignores SIGHUP.
                first.stdin.close()
                first.wait(timeout=5)
                qemu = int(pidfile.read_text())
                deadline = time.monotonic() + 2
                while Path(f"/proc/{qemu}").exists() and time.monotonic() < deadline:
                    time.sleep(0.05)
                self.assertFalse(Path(f"/proc/{qemu}").exists())
            finally:
                if first.poll() is None:
                    first.kill()
                    first.wait(timeout=2)

    def test_the_ssh_child_dies_with_the_local_side(self):
        parent = subprocess.Popen(
            [sys.executable, "-c", textwrap.dedent("""\
                import os, subprocess, sys, time
                sys.path.insert(0, sys.argv[1])
                import importlib.util
                spec = importlib.util.spec_from_file_location("pi_uefi", sys.argv[2])
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                child = subprocess.Popen(
                    [sys.executable, "-c", "import time; time.sleep(30)"],
                    preexec_fn=mod.die_with_parent,
                )
                os.write(1, str(child.pid).encode() + bytes([10]))
                time.sleep(30)
            """), str(Path(__file__).parent), str(Path(__file__))],
            stdout=subprocess.PIPE,
        )
        child_pid = int(parent.stdout.readline())
        os.kill(parent.pid, signal.SIGKILL)
        parent.wait(timeout=5)
        deadline = time.monotonic() + 2
        while Path(f"/proc/{child_pid}").exists() and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertFalse(Path(f"/proc/{child_pid}").exists())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
