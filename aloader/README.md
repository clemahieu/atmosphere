# Early Loader

The Early Loader is responsible for setting up memory and loading the microkernel and the initial domain.
This is akin to the [Elfloader](https://docs.sel4.systems/projects/elfloader) in seL4.

After control is handed off to the kernel, other domains can subsequently be loaded and launched the initial domain.

## Boot Protocol

The loader boots from UEFI, built for `x86_64-unknown-uefi` (`src/boot/uefi.rs`). `atmo run` boots it under OVMF from a directory served as the EFI system partition, with the loader at `EFI/BOOT/BOOTX64.EFI` and the kernel, dom0 and payload concatenated in `initrd` beside it.

## Boot Process

- The UEFI firmware starts the Early Loader, which reads the ELF images of the microkernel and the first domain from `initrd` into memory as plain binary, no relocations.
- The Early Loader computes the usable memory regions.

## Initial Allocator

In order to load the microkernel and the first
