# build-tool

`atmo` is a build helper tool for Atmosphere.
It's designed to *augment* the Cargo experience rather than replace it.

It's set as the `runner` executable so `cargo run` and `cargo test` will *just work*.
The `atmo` command provides Atmosphere-specific options, like booting under QEMU's emulated IOMMU (`atmo run --iommu`).

## Terminal output

By default, the tool suppresses initial outputs from the emulator (the firmware, etc.) so the terminal isn't messed up by the control sequences they contain.
