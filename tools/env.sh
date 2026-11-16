# SPDX-License-Identifier: MIT

# Source this file for a shell that runs cargo, rust_verify or QEMU by hand.
#
#   source tools/env.sh
#
# The tools set this environment themselves; a shell needs it only for commands it runs directly.
# tools/toolchain.py derives Verus's variables, the pinned sysroot and RUSTC_BOOTSTRAP, and
# tools/firmware.py finds OVMF and QEMU (an override already in the environment wins).

ATMO_TOOLS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if toolchain=$(python3 "$ATMO_TOOLS/toolchain.py"); then
    eval "$toolchain"
fi
if firmware=$(python3 "$ATMO_TOOLS/firmware.py"); then
    eval "$firmware"
fi
unset toolchain firmware
