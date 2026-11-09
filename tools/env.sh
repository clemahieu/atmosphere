# Source this file to get the Atmosphere toolchain on PATH.
#
#   source tools/env.sh
#
# Expects: rustup (rust-toolchain.toml picks the nightly), a Verus build under
# tools/verus made by tools/setup-verus.sh, and qemu, edk2-ovmf and gdb
# from the system package manager.

ATMO_TOOLS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS_SRC="$ATMO_TOOLS/verus/source"

# Verus is built against the Rust that rust-toolchain.toml pins, and its binaries link to that sysroot.
VERUS_RUST_LIB="$(cd "$ATMO_TOOLS" && rustc --print sysroot)/lib"

export VERUS_ROOT="$VERUS_SRC/target-verus/release"
export VERUS_Z3_PATH="$VERUS_SRC/z3"
export LD_LIBRARY_PATH="$VERUS_RUST_LIB${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

# The kernel crates use unstable features on a pinned nightly.
export RUSTC_BOOTSTRAP=1

export PATH="$ATMO_TOOLS/bin:$VERUS_ROOT:$PATH"

# OVMF and QEMU. An override already in the environment wins; otherwise the known
# distribution paths. The Python tools import firmware.py themselves.
if firmware=$(python3 "$ATMO_TOOLS/firmware.py"); then
    eval "$firmware"
fi
unset firmware
