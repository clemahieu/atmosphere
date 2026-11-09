#!/usr/bin/env python3
"""Find OVMF and QEMU: an override wins, then the known distribution paths.

ATMO_OVMF_CODE and ATMO_OVMF_VARS name the firmware files. ATMO_QEMU names the
emulator. With no override, the first candidate pair that exists is OVMF, and
qemu-system-x86_64 is taken from PATH. A miss names the variable to set.

tools/env.sh evals this script. The Python tools import it, so a test resolves
against files of its own.
"""
import os
import shlex
import shutil
import sys

# Code and variable-store pairs of one size. Fedora, then Debian's 2M names and
# its 4M names, then Arch's 4M names and its unsuffixed names.
CANDIDATES = (
    ("/usr/share/edk2/ovmf/OVMF_CODE.fd", "/usr/share/edk2/ovmf/OVMF_VARS.fd"),
    ("/usr/share/OVMF/OVMF_CODE.fd", "/usr/share/OVMF/OVMF_VARS.fd"),
    ("/usr/share/OVMF/OVMF_CODE_4M.fd", "/usr/share/OVMF/OVMF_VARS_4M.fd"),
    ("/usr/share/edk2/x64/OVMF_CODE.4m.fd", "/usr/share/edk2/x64/OVMF_VARS.4m.fd"),
    ("/usr/share/edk2/x64/OVMF_CODE.fd", "/usr/share/edk2/x64/OVMF_VARS.fd"),
)

QEMU_NAME = "qemu-system-x86_64"


class Missing(Exception):
    """The firmware or the emulator is not there. The message names the override."""


def resolve_ovmf(env, isfile):
    """The OVMF code and variable-store paths for `env`. `isfile` decides existence."""
    code = env.get("ATMO_OVMF_CODE", "")
    vars_ = env.get("ATMO_OVMF_VARS", "")
    if code or vars_:
        if not code:
            raise Missing("ATMO_OVMF_VARS is set but ATMO_OVMF_CODE is not")
        if not vars_:
            raise Missing("ATMO_OVMF_CODE is set but ATMO_OVMF_VARS is not")
        if not isfile(code):
            raise Missing(f"ATMO_OVMF_CODE={code} does not exist")
        if not isfile(vars_):
            raise Missing(f"ATMO_OVMF_VARS={vars_} does not exist")
        return code, vars_
    for candidate_code, candidate_vars in CANDIDATES:
        if isfile(candidate_code) and isfile(candidate_vars):
            return candidate_code, candidate_vars
    raise Missing("no OVMF firmware found; set ATMO_OVMF_CODE and ATMO_OVMF_VARS")


def resolve_qemu(env, which):
    """The QEMU binary for `env`. `which` is shutil.which: a name or a path."""
    override = env.get("ATMO_QEMU", "")
    if override:
        found = which(override)
        if found is None:
            raise Missing(f"ATMO_QEMU={override} does not exist")
        return found
    found = which(QEMU_NAME)
    if found is None:
        raise Missing(f"{QEMU_NAME} is not on PATH; set ATMO_QEMU")
    return found


def assignments(env=None, isfile=os.path.isfile, which=shutil.which):
    """Shell assignments that export the resolved paths."""
    env = os.environ if env is None else env
    code, vars_ = resolve_ovmf(env, isfile)
    qemu = resolve_qemu(env, which)
    return "\n".join([
        f"export ATMO_OVMF_CODE={shlex.quote(code)}",
        f"export ATMO_OVMF_VARS={shlex.quote(vars_)}",
        f"export ATMO_QEMU={shlex.quote(qemu)}",
    ])


def require(program):
    """The code file, the variable store and the QEMU binary.

    A miss exits with a message that names the override.
    """
    try:
        code, vars_ = resolve_ovmf(os.environ, os.path.isfile)
        qemu = resolve_qemu(os.environ, shutil.which)
    except Missing as error:
        sys.exit(f"{program}: {error}")
    return code, vars_, qemu


def main():
    try:
        print(assignments())
    except Missing as error:
        print(f"tools/firmware.py: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
