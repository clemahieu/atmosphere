# dom0 syscall benchmark

`bench/run-bench.sh` builds the release loader, kernel and dom0 and runs dom0's syscall
timers (`dom0/src/syscall_benchmark.rs`) once under KVM. It needs no sudo, unlike `atmo run`.

## Toolchain

- Rust 1.99.1 from `rust-toolchain.toml` (rustup); `build-std` builds `core` and `alloc` from its
  `rust-src` for the loader's `x86_64-unknown-uefi` target, so no target needs installing.
- The crate `.cargo` configs use `-Z` flags, `build-std` and an `[unstable]` table on a stable
  compiler; the script exports `RUSTC_BOOTSTRAP=1` so cargo accepts them as well as rustc.
- `/usr/bin/qemu-system-x86_64` (8.2.2 was used) and `/dev/kvm` access (`kvm` group).
- OVMF at `/usr/share/edk2/ovmf` (`OVMF_CODE.fd` and `OVMF_VARS.fd`, from edk2-ovmf).

## Running

One run:

    bench/run-bench.sh

N interleaved runs against another kernel (take the median of each line over the runs):

    for i in $(seq 5); do bench/run-bench.sh; <other kernel's run>; done

The build step is a no-op once the images are current. Each run's full serial log goes to
`target/bench/run-<time>.log`.

## Output

All numbers are TSC cycles:

- `null syscall:` an unassigned syscall number (returns from the entry stub), and `mresolve` of a
  mapped page; best of 5 rounds of 100,000 calls.
- `mmap 4K:` two lines, mapping and touching 16,384 fresh 4K pages with 64 pages per call and with
  1 page per call; mean per page.
- `IPC round trip:` `receive_empty` plus the partner's `send_empty_try_schedule`, two syscalls and
  two thread switches; mean over 1,000 rounds.
- `new_thread:` best and mean over 32 creations.

Atmosphere boots only CPU 0 and has no timer interrupt, so all timers run on one CPU.

## QEMU line

    taskset -c 0-15 timeout 300 /usr/bin/qemu-system-x86_64 -enable-kvm -cpu host \
      -machine q35,kernel_irqchip=split -smp 4 -m 6144 -mem-prealloc \
      -nographic -serial mon:stdio -no-reboot -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
      -drive if=pflash,format=raw,unit=0,readonly=on,file=/usr/share/edk2/ovmf/OVMF_CODE.fd \
      -drive if=pflash,format=raw,unit=1,file=target/bench/OVMF_VARS.fd \
      -drive format=raw,file=fat:rw:target/bench/esp

- `-m 6144`: the loader needs more than 2 GiB of contiguous memory.
- `-mem-prealloc`: backs guest memory before boot, so host page faults do not pollute the
  fresh-page mmap timing.
- The ESP, `target/bench/esp`, is the directory QEMU serves as a FAT disk, laid out as `atmo run`
  lays it out: OVMF boots the loader at `EFI/BOOT/BOOTX64.EFI`, and the loader reads `initrd`, the
  kernel and dom0 ELF images concatenated.
- `OVMF_VARS.fd` is a copy of OVMF's variable store, which OVMF writes.

## Exit status

dom0 ends the run through the isa-debug-exit device, which makes QEMU exit with `code << 1 | 1`:

- `33`: dom0 finished all timers (the script then exits 0).
- `3`: a timer failed; the log has a `... failed:` and `dom0 benchmark FAILED` line.
- `1`: the kernel shut down on a failure.
- `124`: `timeout` killed QEMU after 300 s.
- `0` or anything else: QEMU stopped without dom0 finishing (for example a triple fault, which
  `-no-reboot` turns into a clean exit); read the log.

The script exits 2 if a build fails.
