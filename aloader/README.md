# Early Loader

The Early Loader is responsible for setting up memory and loading the microkernel and the initial domain.
This is akin to the [Elfloader](https://docs.sel4.systems/projects/elfloader) in seL4.

After control is handed off to the kernel, other domains can subsequently be loaded and launched the initial domain.

## Boot Protocol

The loader boots from UEFI, built for `x86_64-unknown-uefi` (`src/boot/uefi.rs`). `tools/run.py` boots it under OVMF from a directory served as the EFI system partition, with the loader at `EFI/BOOT/BOOTX64.EFI` and the kernel, dom0 and payload concatenated in `initrd` beside it. A file `cmdline` there is the kernel's command line; without one the line is empty. Built for `aarch64-unknown-uefi` (`cargo build --target aarch64-unknown-uefi`, which `atmo build --target aarch64` runs), it is `EFI/BOOT/BOOTAA64.EFI`, which EDK2 on QEMU virt starts; `tools/orangepi-kvm.py --esp` boots such a directory under KVM. What differs between the two is `src/arch/`.

## Boot Process

- The UEFI firmware starts the Early Loader, which reads the ELF images of the microkernel and the first domain from `initrd` into memory as plain binary, no relocations.
- The Early Loader computes the usable memory regions.

## Initial Allocator

In order to load the microkernel and the first
