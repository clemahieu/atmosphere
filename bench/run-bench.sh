#!/usr/bin/env bash
# Builds the release loader, kernel and dom0, then runs dom0's syscall timers once under KVM.
# Prints the benchmark lines and the QEMU exit status; the full serial log stays in target/bench/.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
out="$root/target/bench"
mkdir -p "$out"

# Rust 1.99.1 comes from rust-toolchain.toml; each crate's .cargo config sets its target and
# build-std, so cargo must run inside the crate directory, as atmo does. The configs' [env]
# RUSTC_BOOTSTRAP=1 reaches only rustc; the stable cargo needs it too for their [unstable] table.
export RUSTC_BOOTSTRAP=1
for crate in aloader kernel dom0; do
    if ! (cd "$root/$crate" && cargo build --release) >"$out/build-$crate.log" 2>&1; then
        tail -n 40 "$out/build-$crate.log"
        echo "build of $crate failed (full log: $out/build-$crate.log)" >&2
        exit 2
    fi
done

loader="$root/target/x86_64-unknown-none/release/aloader"
kernel="$root/target/x86_64-unknown-aloader/release/kernel"
dom0="$root/target/x86_64-unknown-aloader/release/dom0"

# The loader takes the kernel and dom0 ELF images concatenated in one multiboot module (atmo's
# JumboBinary, README's /boot/atmo); dom0 needs no payload.
initrd="$out/atmo.initrd"
cat "$kernel" "$dom0" >"$initrd"

log="$out/run-$(date +%Y%m%d-%H%M%S).log"
status=0
taskset -c 0-15 timeout 300 /usr/bin/qemu-system-x86_64 \
    -enable-kvm -cpu host -machine q35,kernel_irqchip=split -smp 4 -m 6144 -mem-prealloc \
    -nographic -serial mon:stdio -no-reboot \
    -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
    -kernel "$loader" -initrd "$initrd" </dev/null >"$log" 2>&1 || status=$?

grep -a -E 'null syscall:|mmap 4K:|IPC round trip:|new_thread:|dom0 benchmark (done|FAILED)|failed:' "$log" \
    | sed 's/\x1b\[[0-9;]*m//g' || true
echo "qemu exit status: $status (33 = dom0 finished, 3 = a timer failed, 1 = the kernel failed, 124 = timeout); log: $log"
[ "$status" -eq 33 ]
