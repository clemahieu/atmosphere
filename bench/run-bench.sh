#!/usr/bin/env bash
# Builds the release loader, kernel and dom0, then runs dom0's syscall timers once under KVM.
# Prints the benchmark lines and the QEMU exit status; the full serial log stays in target/bench/.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="$root/target/bench"
mkdir -p "$out"

# Rust 1.99.1 comes from rust-toolchain.toml; each crate's .cargo config sets its target and
# build-std, so cargo must run inside the crate directory, as tools/run.py does. The configs' [env]
# RUSTC_BOOTSTRAP=1 reaches only rustc; the stable cargo needs it too for their [unstable] table.
export RUSTC_BOOTSTRAP=1
# The loader is the UEFI application OVMF boots, so it builds for x86_64-unknown-uefi.
for crate in aloader kernel dom0; do
    args=(--release)
    [ "$crate" = aloader ] && args+=(--target x86_64-unknown-uefi)
    if ! (cd "$root/$crate" && cargo build "${args[@]}") >"$out/build-$crate.log" 2>&1; then
        tail -n 40 "$out/build-$crate.log"
        echo "build of $crate failed (full log: $out/build-$crate.log)" >&2
        exit 2
    fi
done

loader="$root/target/x86_64-unknown-uefi/release/aloader.efi"
kernel="$root/target/x86_64-unknown-aloader/release/kernel"
dom0="$root/target/x86_64-unknown-aloader/release/dom0"

# The EFI system partition as tools/run.py lays it out: OVMF boots
# EFI/BOOT/BOOTX64.EFI from removable media, and the loader reads the kernel and dom0 ELF images
# concatenated in the file initrd beside it; dom0 needs no payload. The file cmdline is the kernel's
# command line: the port of the isa-debug-exit device below, in decimal, which the kernel's failure
# shutdown writes. OVMF writes its variable store, so it gets a copy.
esp="$out/esp"
rm -rf "$esp"
mkdir -p "$esp/EFI/BOOT"
cp "$loader" "$esp/EFI/BOOT/BOOTX64.EFI"
# .debug_* stays in target/. Release files keep it too, so the initrd copy drops it.
python3 "$root/tools/elfstrip.py" "$kernel" "$dom0" >"$esp/initrd"
echo "qemu_debug_exit_io_base=$((0xf4))" >"$esp/cmdline"
# The same resolver the Python tools import: an override wins, then the known paths.
if ! firmware=$(python3 "$root/tools/firmware.py"); then
    exit 1
fi
eval "$firmware"
unset firmware
cp "$ATMO_OVMF_VARS" "$out/OVMF_VARS.fd"

log="$out/run-$(date +%Y%m%d-%H%M%S).log"
status=0
# Guest RAM is tools/run.py MEMORY_MIB. design/test-guest-memory/.
taskset -c 0-15 timeout 300 "$ATMO_QEMU" \
    -enable-kvm -cpu host -machine q35,kernel_irqchip=split -smp 4 -m 2560 -mem-prealloc \
    -nographic -serial mon:stdio -no-reboot \
    -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
    -drive if=pflash,format=raw,unit=0,readonly=on,file="$ATMO_OVMF_CODE" \
    -drive if=pflash,format=raw,unit=1,file="$out/OVMF_VARS.fd" \
    -drive format=raw,file=fat:rw:"$esp" </dev/null >"$log" 2>&1 || status=$?

grep -a -E 'null syscall:|mmap 4K:|IPC round trip:|new_thread:|dom0 benchmark (done|FAILED)|failed:' "$log" \
    | sed 's/\x1b\[[0-9;]*m//g' || true
echo "qemu exit status: $status (33 = dom0 finished, 3 = a timer failed, 1 = the kernel failed, 124 = timeout); log: $log"
[ "$status" -eq 33 ]
