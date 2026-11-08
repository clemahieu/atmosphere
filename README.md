# Atmosphere

Atmosphere is a proving ground for novel isolation techniques and formal verification, written in Rust.

## Development Setup

Install [rustup](https://rustup.rs) (the pinned nightly comes from
`rust-toolchain.toml`) and, from the system package manager, `nasm`, `qemu`,
`gdb`, `jq` and, for bootable ISOs, `grub2` and `xorriso`. Then build the Verus
version used for verification and put the toolchain on `PATH`:

```bash
tools/setup-verus.sh
source tools/env.sh
```

You can now build and run Atmosphere with `cd kernel && cargo run`.

## Atmo

Atmosphere builds with `atmo`, a build system that extends Cargo.
Run `atmo help` for more information.

## Test

```bash
atmo test
```

`atmo test` is the gate: a commit is tested when it exits 0. It checks that the workspace builds, that every dependency's license is on `tools/license-allowlist`, that the license guard refuses what it must, that verification reports no more errors than `tools/verify-allowance`, that the kernel's boot stack holds and an overflow faults, and that dom0 boots under KVM to a clean exit. It also reports line and branch coverage per crate from a boot, by the mechanism described in `tools/coverage.py`.

## Run verification

```bash
atmo verify
```

## Boot on real hardware

* Copy the bootable binaries. If you have built with `debug` mode, look for the
  below binaries under the `debug` directory instead of `release`.

```bash
sudo cp target/x86_64-unknown-none/release/aloader /boot/
cat target/x86_64-unknown-aloader/release/{kernel,dom0} | sudo tee /boot/atmo >/dev/null
```

* Add menuentry to grub.cfg (`/boot/grub/grub.cfg`)

```
menuentry "Atmosphere" {
  set root=(hd0,msdos1)
  echo "Loading Atmosphere..."
  multiboot2 /boot/aloader
  module2 /boot/atmo atmo
  boot
}
```

* Update grub and reboot to select Atmo from the grub menu

```bash
sudo update-grub && sudo reboot
```
