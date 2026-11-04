# Source this file to get the Atmosphere toolchain on PATH.
#
#   source tools/env.sh
#
# Expects: rustup (rust-toolchain.toml picks the nightly), a Verus build under
# tools/verus made by tools/setup-verus.sh, and nasm, qemu, gdb, grub and
# xorriso from the system package manager.

ATMO_TOOLS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS_SRC="$ATMO_TOOLS/verus/source"

# Verus is built against Rust 1.76.0 and its binaries link to that sysroot.
VERUS_RUST_LIB="$(rustup run 1.76.0 rustc --print sysroot)/lib"

export VERUS_ROOT="$VERUS_SRC/target-verus/release"
export VERUS_Z3_PATH="$VERUS_SRC/z3"
export LD_LIBRARY_PATH="$VERUS_RUST_LIB${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

# The kernel crates use unstable features on a pinned nightly.
export RUSTC_BOOTSTRAP=1

# Where grub-mkrescue finds the i386-pc modules for the bootable ISO.
export GRUB_X86_MODULES=/usr/lib/grub/i386-pc

export PATH="$ATMO_TOOLS/bin:$VERUS_ROOT:$PATH"
