# Atmosphere

Atmosphere is a proving ground for novel isolation techniques and formal verification, written in Rust.

## Development Setup

Install [rustup](https://rustup.rs) (the pinned nightly comes from
`rust-toolchain.toml`) and, from the system package manager, `nasm`, `qemu`,
`gdb`, `jq` and, for bootable ISOs, `grub2` and `xorriso`. Then build the Verus
fork used for verification and put the toolchain on `PATH`:

```bash
tools/setup-verus.sh
source tools/env.sh
```

You can now build and run Atmosphere with `cd kernel && cargo run`.

## Atmo

Atmosphere builds with `atmo`, a build system that extends Cargo.
Run `atmo help` for more information.

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

## TODO

Wire up IPI for killing threads and TLB flush. 

Wire up hugepages. 

Kill container (halfway there..). 

Bring back verification for Kernel init(). 

Adjust triggers in ProcessManager (almost there).
