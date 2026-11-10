---
title: "Machine glue is a crate per machine below the kernel: the kernel calls its free functions, and it names nothing in kernel/"
date: 2026-11-10
status: active
tags: [portability, boot, interrupt, iommu, glue]
one_line: "Boot discovery, the console, the interrupt controller and timer, secondary-core start, shutdown and the IOMMU driver live in one crate per machine (machine/pc for the x86_64 PC, machine/virt for aarch64 on QEMU virt), each exporting the same free functions and constants, and machine/virt one more that names the interrupt an IRQ carries, which the x86_64 IDT gives by the vector taken; the kernel depends on the crate its target selects and re-exports it as crate::machine; the crate depends on nothing in kernel/ or kernel/verified, takes cpu indices as arguments, owns the interrupt vectors and its own per-core state, and issues its own MSR and port instructions."
revisit_if: "Two machines must be supported on one architecture (bare Apple silicon beside QEMU virt), when target_arch no longer selects the crate and a cargo feature or a second build target must; or a machine needs a kernel service at interrupt or boot time that cannot be passed as an argument, which would make the dependency two-way."
confidence: "A judgement from a survey of kernel/src at 569f164: the item list and signatures follow today's callers. machine/virt tests that the same list fits QEMU virt: its PL011, PSCI power-off, PSCI core start, GICv3 and generic timer items are written to these signatures and run under KVM with two cores, and the list needed one item more, the acknowledgement. The Cargo constraint that rules out one renamed dependency per target was checked with cargo."
---

# Machine glue below the kernel

## Decision

`design/arch-module/` puts what the ISA fixes in an arch module and what the platform fixes in a per-machine crate. This record says what that crate is and how the kernel calls it.

**Crates.** One crate per machine, each a `no_std` workspace member:

```
machine/pc/      package machine-pc     the x86_64 PC as QEMU q35 gives it: xAPIC, IOAPIC, 8259, COM1, VT-d, INIT-SIPI
machine/virt/    package machine-virt   QEMU virt on aarch64: GICv3, generic timer, PL011, PSCI, SMMUv3 refusing every stream
```

**Selection.** The kernel depends on each crate under its target and re-exports the one its target selects, as the arch module does:

```
# kernel/Cargo.toml
[target.'cfg(target_arch = "x86_64")'.dependencies]
machine-pc = { path = "../machine/pc" }

// kernel/src/machine.rs
#[cfg(target_arch = "x86_64")]
pub use machine_pc::*;
```

Kernel code calls `machine::item`. Every machine crate defines the same names with the same signatures; there is no trait, for the reason `design/arch-module/` gives: one implementation per target. A crate that lacks an item, or gives it another signature, fails to build. An item that only one target's arch module calls is in that target's machine crate alone: `acknowledge_interrupt` below is the one there is.

**Dependency direction.** The kernel depends on the machine crate. The machine crate depends on nothing in `kernel/` or `kernel/verified`: its dependencies are `astd` (for `BootInfo` and `Mutex`), `ns16550a`, `log`, `spin` and `bit_field`. It logs through the `log` facade, which the kernel's logger serves. Three things follow:

- *The cpu index is an argument.* The kernel names cores by its dense index; an item that acts on a named core takes `cpu: usize`. The crate maps the index to the hardware's name for the core: the APIC ID on the PC, which is the index today; the MPIDR affinity on virt. No item reads the kernel's per-CPU block. An item that acts on the calling core acts on what that core's hardware shows it.
- *The crate owns the interrupt numbering.* It exports `TIMER_VECTOR`, `IOMMU_FAULT_VECTOR` and `FLUSH_VECTOR: u8`, and the kernel installs its handlers at them. The platform fixes some of these numbers (the EL1 physical timer is PPI 30 on QEMU virt), so the kernel cannot choose them. On the PC the crate chooses 32, 33 and 34, today's `IRQ_OFFSET + IRQ_TIMER`, `+ IRQ_IOMMU_FAULT` and `+ IRQ_FLUSH` in `kernel/src/interrupt/mod.rs`. On x86_64 the IDT gives each number a vector of its own, so the handler entered names the interrupt. On aarch64 every IRQ enters through one vector, and the kernel's IRQ entry asks the crate which arrived: `acknowledge_interrupt` returns one of the three constants as the GIC's INTID, and the entry runs that interrupt's handler, which ends with `end_of_interrupt` as the PC's does.
- *The crate owns its per-core state.* The PC crate has none: the local APIC's registers sit at the same physical address on every core, and each core reaches its own through it, so the crate keeps one register base and `cpu::Cpu` loses its `xapic` field. A machine whose state is per core keeps an array indexed by the cpu index, of length `MAX_CPUS`, which every machine crate exports. On virt there are two: the Redistributors, which the GIC itself lays out as an array of frames in one region, and the interrupt each core acknowledged and has not ended, which `end_of_interrupt` writes back; an item that takes no index finds the calling core's by its `MPIDR_EL1`. The kernel asserts at compile time that `machine::MAX_CPUS >= verified::define::NUM_CPUS`, as `kernel/src/boot/mod.rs` already asserts the map check's bounds.

The crate issues the instructions it needs itself: `rdmsr` and `wrmsr` of `IA32_APIC_BASE`, and `inb`, `outb` and `outw`. `kernel/src/arch` keeps the MSRs the kernel writes (`GS_BASE`, `STAR`, `LSTAR`, `CSTAR`, `SF_MASK`, `EFER`). Once the glue has moved, `kernel/src` does no port I/O, and `arch::io` goes.

**The items**, each with the file it comes from today:

| Item | Today |
|---|---|
| `unsafe fn init(boot: &BootInfo)`: once on the boot core, after the kernel copies `BootInfo`; keeps what the machine needs, the IOMMU base (`boot.iommu_base`) and the IOAPIC base | `boot::get_boot_info` read in `iommu::init_iommu`; `interrupt/mps.rs` `probe_ioapic` |
| `fn set_option(key: &str, value: &str) -> bool`: the kernel's command-line parser offers each key it does not own; true when the machine took the key and its value parsed, false makes the parser reject it as it rejects an unknown key | `qemu_debug_exit_io_base` and `bochs_apm_io_base` in `boot/command_line.rs` |
| `unsafe fn console_init()`, then `fn console() -> Console` where each crate's `Console` implements `core::fmt::Write` and holds the port's lock while it lives | `console/mod.rs` `early_init`, `get_writer`; called by `logging.rs` |
| `unsafe fn interrupt_init()`: once on the boot core before any `interrupt_init_core`; masks the 8259s and finds the IOAPIC; on virt turns the GIC's Distributor on with affinity routing and Group 1 | the PIC masking at the top of `interrupt/mod.rs` `init`; `interrupt/ioapic.rs` `init` |
| `unsafe fn interrupt_init_core(cpu: usize)`: once on each core; enables its local APIC and points its one-shot timer at `TIMER_VECTOR`, unarmed; on virt wakes the core's Redistributor, enables the flush SGI and the timer's PPI, turns its CPU interface on through the ICC system registers and disables its timer | `interrupt/lapic.rs` `init`, `x86_xapic.rs` `attach`, `tsc_enable` |
| `unsafe fn route_external(cpu: usize)`: routes the IOAPIC's inputs to `cpu`; on virt nothing, since the crate enables no SPI | `interrupt/ioapic.rs` `init_cpu` |
| `fn set_timer(ticks: u64)`: arms this core's one-shot timer; on virt the EL1 physical timer, `ticks` of the physical count from now | `interrupt/lapic.rs` `set_timer(Cycles)` |
| `fn acknowledge_interrupt() -> Option<u32>`, in machine/virt alone: acknowledges the interrupt this core took and returns its id, or nothing when none was pending, in which case there is nothing to end; called only by the aarch64 IRQ entry | none: the IDT's vector names the interrupt |
| `fn end_of_interrupt()`: on virt ends the interrupt this core acknowledged last | `interrupt/lapic.rs` |
| `fn send_ipi(cpu: usize, vector: u8)`: returns once this core's interrupt controller has taken it; on virt `vector` is an SGI | `interrupt/lapic.rs` |
| `unsafe fn start_core(cpu: usize, stack: u64, entry: extern "C" fn(u64) -> !, root: u64)`: starts `cpu` on `stack`, translating through `root`, at `entry` with `cpu` as its argument; on virt PSCI `CPU_ON` for the core's MPIDR affinity, at an entry in the crate that turns translation on and calls `entry` | `interrupt/lapic.rs` `boot_ap(cpu_id: u32, stack: u64, code: u64)`; `boot/ap_start.rs` |
| `unsafe fn shutdown(success: bool) -> !`: ends the run, then halts in its own loop | `boot/mod.rs` `shutdown` |
| `unsafe fn iommu_init()`: with no IOMMU in `BootInfo`, does nothing; otherwise installs the tables, routes faults to CPU 0 at `IOMMU_FAULT_VECTOR` and enables translation. On virt the SMMUv3's stream table aborts every stream, `iommu_map` and `iommu_invalidate` refuse, and its event interrupt is not yet routed, so `iommu_fault_dump` runs only when called | `iommu.rs` `init_iommu` |
| `unsafe fn iommu_map(bus: usize, device: usize, function: usize, root: u64) -> Result<(), &'static str>` | `iommu.rs` `map` |
| `unsafe fn iommu_invalidate(bus: usize, device: usize, function: usize, page: u64) -> Result<(), &'static str>` | `iommu.rs` `invalidate_iotlb` |
| `fn iommu_fault_dump() -> Result<(), &'static str>` | `iommu.rs` `dump_iommu_fault`; called by the fault handler in `interrupt/mod.rs` |

`root` in `start_core` is the value the new core loads into its translation base, composed by the kernel's arch module: on x86_64 the kernel's PML4 with `CR3_NO_FLUSH` when PCIDE is on, which `boot_ap` composes from `BootInfo` today. On the PC, the trampoline turns PCIDE on when that bit is set, as now. On aarch64 it is TTBR0_EL1's value, the kernel's root table under address-space id 0. A core `CPU_ON` starts has translation off, where every address is its own, so the crate's entry runs at its physical address, reads the calling core's TCR_EL1, MAIR_EL1 and SCTLR_EL1, `root`, the stack and `entry` from a block under the stack's top, which `CPU_ON` hands it as its context, and turns translation on where it stands: `root` maps the kernel at its physical addresses, as the loader's table does. The calling core cleans the entry and the block to memory first, since the new core reads both past the caches.

The timer is a one-shot on every machine. The local APIC's stops by itself when it fires. The generic timer's interrupt is a level that stays asserted while the count is past the compare value, so on virt the acknowledgement of the timer's interrupt disables the timer, and the kernel's timer handler is the same on both: arm it again or not, then end the interrupt.

A device id reaches `iommu_map` and `iommu_invalidate` from a process, so the kernel checks it against `verified::device::DeviceId` before the call, as `iommu.rs` `device_in_range` does today. The crate asserts its own bound (bus below 256, device below 32, function below 8), since a caller in the kernel that passes a bad id is a bug. Nothing in `kernel/src` calls `map` or `invalidate_iotlb` today.

**What stays in `kernel/src`.** The machine-neutral boot code: `boot/command_line.rs` (with the machine's keys handed to `set_option`), `boot/free_ranges.rs`, `boot/mapped_runs.rs`, and `boot/mod.rs`'s copy of `BootInfo` with `get_boot_info` and `get_command_line`. The ISA's share goes to the arch module (`design/arch-module/` item 5): the vector table and handlers in `interrupt/mod.rs`, `idt.rs` and `exception.rs`, `gdt/`, the syscall entry, `spin_forever` and `PCIDE`. What is neither stays where it is: `cpu.rs`'s per-CPU block, `flush.rs`'s epoch protocol (which calls `send_ipi` with `FLUSH_VECTOR`), `lock.rs`, `write_protect.rs`, and `logging.rs`'s formatting over `machine::console`.

## Reasoning

A crate rather than a module of the kernel, because the crate boundary is what holds the dependency direction: the compiler rejects a machine file that reaches into `crate::cpu` or `crate::interrupt`, which today's `lapic.rs`, `ioapic.rs` and `iommu.rs` all do. A module under `kernel/src/machine/` would let that coupling back in with one `use`.

The calls go one way because the glue is what changes per machine and the kernel is what stays. A crate that reads the kernel's per-CPU block or its vector constants would carry the x86 per-CPU layout into the aarch64 crate. Every such read today is a value the kernel already has at the call: the cpu index, or a vector the crate can own.

The crate owns the vectors rather than taking them as arguments because on aarch64 the timer's and the IOMMU's interrupt numbers are fixed by the platform, and only the SGIs used for IPIs are free. On x86 the choice is free either way, so letting the machine choose costs nothing there.

Each machine is its own dependency with a re-export, because Cargo refuses one dependency name with different paths per target ("Dependency 'machine' has different source paths depending on the build target", from `cargo build` on a scratch workspace with `machine = { package = ... }` under two `target.'cfg(...)'` tables).

The machine's command-line keys go through `set_option` so the parser stays one machine-neutral piece in `kernel/src` and `KernelCommandLine` has no field that exists for one machine.

## Alternatives rejected

- **A `Machine` trait.** One implementation per target, as for the arch module; a trait adds a type parameter for dispatch the kernel never does.
- **The glue as a module of the kernel crate under `cfg`.** Lighter, but it does not stop the glue depending on the kernel, as above.
- **The crate reading the cpu id and vectors from the kernel, as today.** It makes the dependency two-way, which Cargo forbids between crates, and puts the x86 per-CPU layout in every machine.
- **The kernel choosing the vectors and passing them in.** The platform fixes them on aarch64.
- **The aarch64 IRQ entry reading the GIC's acknowledge register itself.** The entry is the ISA's, but which register names the interrupt is the interrupt controller's, and a machine with another controller on the same ISA (bare Apple silicon) acknowledges another way. The acknowledgement sits with the end of interrupt, in the crate that owns the controller.
- **An `acknowledge_interrupt` on the PC as well, for one list of names.** It would have nothing to return that the vector taken has not already said, and no caller.
- **`end_of_interrupt` taking the id.** The PC's names nothing, and the signature is shared. The GIC wants the id back, so machine/virt keeps the last one each core acknowledged; the kernel takes one interrupt at a time on a core, so one slot a core is enough.
- **A shared crate of x86 instruction wrappers for the kernel and the PC crate.** A crate for five one-line functions, each side using a few; each side keeps the ones it issues.

## What this does not settle

- `BootInfo`'s shape on aarch64. It lives in `astd::boot`, shared with the loader, and carries ISA fields (`pml4`, `pcide`) beside the machine's (`iommu_base`); the loader's port decides it.
- How many cores there are. `start_core` takes an index the kernel chooses, and nothing discovers the core count today (no MADT walk on the PC, no device tree walk on virt).
- Whether the IOAPIC routes are wanted. Today inputs 0 and 1 go to vectors 32 and 33, which are also the timer's and the IOMMU fault's; `route_external` keeps that.
- The verified IOMMU model in `kernel/verified` beyond its command ring, which `design/arch-module/` puts in the arch module and otherwise leaves open. This record moves only the unverified driver.
