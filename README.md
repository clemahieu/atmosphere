# Atmosphere

Atmosphere is a proving ground for novel isolation techniques and formal verification, written in Rust.

## Development Setup

Install [rustup](https://rustup.rs) (the pinned nightly comes from
`rust-toolchain.toml`) and, from the system package manager, `qemu`,
`edk2-ovmf` (at `/usr/share/edk2/ovmf`), `gdb` and `jq`. Then build the Verus
version used for verification and put the toolchain on `PATH`:

```bash
tools/setup-verus.sh
source tools/env.sh
```

You can now build and boot Atmosphere under QEMU with `tools/run.py`. A run
started with `tools/run.py --gdb` waits in the loader until `tools/gdb.py`,
in another terminal, attaches gdb with the kernel's and dom0's symbols.

## Atmo

Atmosphere builds with `atmo`, a build system that extends Cargo.
Run `atmo help` for more information.

## Test

```bash
atmo test
```

`atmo test` is the gate: a commit is tested when it exits 0. It checks that the workspace builds, that every dependency's license is on `tools/license-allowlist` (`tools/check-licenses.py`), that the license guard refuses what it must, that verification reports no more errors than `tools/verify-allowance`, that the kernel's boot stack holds and an overflow faults, and that dom0 boots under KVM to a clean exit. It also reports line and branch coverage per crate from a boot, by the mechanism described in `tools/coverage.py`.

## Run verification

```bash
tools/verify.py
```
