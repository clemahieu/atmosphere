---
title: "Every target uses a 4K granule, 48-bit VA and four levels; what differs per ISA is a fixed item set in an arch module chosen by target cfg"
date: 2026-11-09
status: active
tags: [portability, pagetable, verified, abi]
one_line: "Page sizes 4K/2M/1G, 512 entries a level and four levels stay fixed constants the proofs use on every target; only an entry's bit layout is per-ISA, including where the walker sets accessed and dirty and whether it does. A per-ISA arch module, selected by cfg(target_arch) with no traits, supplies five items: page-entry encoding, trap frame and user-return checks, address-space switch and flush token, syscall register table, and exception and interrupt entry glue. Platform glue is a separate per-machine crate."
revisit_if: "A target the project must run on offers no 4K granule to the kernel or its IOMMU (bare Apple silicon, whose DART uses 16K pages), a workload needs more than 48 bits of VA (x86 LA57, Arm LPA2), or a second implementation of an item has to coexist on one target, which is when a trait starts to pay."
confidence: "A judgement made before the second target exists. That the 4K-granule aarch64 table has the x86_64 shape is arithmetic on both architectures' translation formats; that five items cover the ISA is a survey of the tree, and the first aarch64 build is what tests it."
---

# The arch module, and why the page granule is fixed

## Decision

This is the default the aarch64 port's plan chose. The human may override it, and an override revises this record.

**Granule.** Every target translates with a 4K granule, 48-bit virtual addresses and four levels of 512 entries. `PAGE_SZ_4k`, `PAGE_SZ_2m` and `PAGE_SZ_1g` in `kernel/verified/define.rs`, the 512-entry table page and the four-level walk (`va2index`, `pagetable_map_4k_page`) stay shared constants and shared code, the same on every target. What differs per architecture is the bit layout of an entry: which bits say valid, block or page, writable, user-accessible and not executable, and where the address sits. On x86_64 that is the long-mode PTE; on aarch64 it is the VMSAv8-64 stage-1 descriptor for the 4K granule with `TCR_EL1.T0SZ = 16`. The kernel's share of every table stays the top-level entries below `KERNEL_MEM_END_L4INDEX`, copied into each process table, so on aarch64 the kernel and the process share `TTBR0_EL1` and `TTBR1_EL1` walks are disabled; the spec's split of a table into kernel and user entries does not change.

**Arch module.** Code the ISA fixes lives in an arch module, one implementation per target, chosen by `cfg(target_arch)`:

```
kernel/verified/arch/mod.rs        #[cfg(target_arch = "x86_64")] mod x86_64; pub use x86_64::*;  (and aarch64)
kernel/verified/arch/x86_64.rs     items verified code names, with their specs
kernel/src/arch/x86_64/            the same target's unverified entry glue and instruction wrappers
```

Each implementation defines the same names with the same signatures and the same `ensures`. There is no trait: shared code calls `arch::item`, and a target that lacks an item, or whose item promises less, fails to build or to verify. The specs are written over the abstract structs that already exist (`PageEntry`, `PageEntryPerm`, `Flushed`, the thread record), so the proofs above the arch module do not know which ISA they run on.

**The item set**, and where each item lives today:

1. *Page-entry encoding and decoders.* Encode an abstract entry at a level into a word and decode a word at a level back. On x86_64: the `PAGE_ENTRY_*` bit masks and the `MEM_MASK`, `MEM_4k_MASK`, `MEM_2m_MASK` and `MEM_1g_MASK` address masks in `kernel/verified/arch/x86_64.rs`, read by the `usize2*` decoders and `page_entry2usize` in `kernel/verified/pagetable/entry.rs` and by the address checks in `util/page_ptr_util_u.rs`, `capability/map.rs` and `capability/link.rs`, each of which names the masks it reads. `KERNEL_MEM_END_L4INDEX` is not an entry bit: it is the kernel's share of a top-level table, the same on every target, and stays in `define.rs`. The decoders take the level, because aarch64's bit 1 means table at levels 0 to 2 and page at level 3, where x86's PS bit means a large page; x86 ignores the argument where PS is undefined.

   The item also places the two bits the walker sets, accessed and dirty, and reports two facts: whether the target maintains the accessed bit and whether it maintains the dirty bit. On x86_64 the bits are `PAGE_ENTRY_ACCESSED_MASK` and `PAGE_ENTRY_DIRTY_MASK` (bits 5 and 6) and the facts are `maintains_accessed` and `maintains_dirty`, both true always. On aarch64 `ID_AA64MMFR1_EL1.HAFDBS` (FEAT_HAFDBS) says none, the access flag only, or both; the dirty state there is DBM, the hardware clearing the read-only permission of an entry marked dirty-bit-modifier, which the decoder presents as write permission plus the same abstract dirty bit. On RISC-V, Svadu says both and its absence says neither. The processor sets these bits on any core at any time, also while a core holds the kernel, so they are not part of `PageEntry`: the abstract `PageEntryStatus` holds them, the decoder reads them from a word apart from the entry, and the encoder writes them clear, so a map leaves them clear. Two words that differ only in them decode to the same entry (`lemma_status_outside_entry` in `kernel/verified/pagetable/entry.rs`), and a table whose words differ only there is well formed with the same view (`lemma_status_outside_view` in `pagetable/pagemap.rs`), so every proof over a table's view holds whatever values they take.
2. *Trap frame and user-return checks.* The register frame a thread record holds, the values a return to user writes (code and stack selectors on x86, `SPSR_EL1` for EL0 on aarch64) and the check that a user-supplied program counter is a user address. On x86_64: `Registers`, the all-zero frame (`zero_registers`, `zero_frame`), the selectors `USER_CS` and `USER_SS`, the flag masks `USER_FLAGS` and `FORCED_FLAGS` that `user_frame` and `user_frame_of` apply to a written frame, and `USER_RIP_END` with `user_rip`, all in `kernel/verified/arch/x86_64.rs`, which `capability/thread.rs` reads. The user bound differs: 2^47 on x86 (canonical lower half), 2^48 under `TTBR0_EL1` with `T0SZ = 16`.
3. *Address-space switch and flush token.* Switch this core to (root table, address-space id), and flush every context on this core, returning the `Flushed` token. On x86_64: `switch_address_space(root, asid)` in `kernel/src/arch.rs`, which every switch in `kernel/src/` calls and which composes CR3 with its no-flush bit; `flush_every_context` in `kernel/verified/arch/x86_64.rs`, which toggles CR4.PGE. The `Flushed` token, the epoch model and the IPI protocol of `design/flush-without-waiting/` stay shared; the 12-bit PCID and a 16-bit ASID both hold `PCID_MAX`. The flush stays a counted `external_body` glue leaf on each target.
4. *Syscall register table.* Which register carries each position of an invocation (the operation number, the slot, arguments 1 to 5, the status word and result words 1 to 5), the instruction, and what the call preserves and clobbers. The x86_64 and aarch64 tables are under Registers in `design/syscall-abi-in-registers/`. On x86_64: the `Registers` accessors `operation_number`, `slot` and `argument(k)` with their specs, `spec_status_word` and `spec_result(k)`, and `write_outcome`, which writes an `Outcome`'s status word and result words at their positions, all in `kernel/verified/arch/x86_64.rs`; the dispatch in `capability/operation.rs` reads the frame only through them, and the syscall handler in `kernel/src/syscalls/mod.rs` writes back only through `write_outcome`. `asys` does not link `kernel/verified`, so it carries its own copy of the table, `syscall` in `asys/src/arch/<target>.rs`, selected by the same cfg; that record is the one source both follow, for each target.
5. *Exception and interrupt entry glue.* The vector table, the stubs that save the trap frame and enter the kernel, and the instruction wrappers the stubs and the switch use. Today: `kernel/src/interrupt/mod.rs`, `interrupt/idt.rs` and `interrupt/exception.rs`, the syscall entry in `kernel/src/syscalls/mod.rs`, `kernel/src/gdt/` and `kernel/src/arch.rs`. All of it is unverified glue under `kernel/src/arch/<target>/`.

**Machine glue is not the arch module.** What the platform fixes rather than the ISA (boot and discovery, the interrupt controller, the timer, the console, secondary-core start, the IOMMU) goes to a per-machine glue crate: for the PC, today's shutdown and secondary-core start in `kernel/src/boot/`, `kernel/src/console/`, `interrupt/lapic.rs`, `ioapic.rs`, `mps.rs`, `x86_xapic.rs` and `kernel/src/iommu.rs`; for aarch64, a QEMU virt crate (GICv3, generic timer, PL011, PSCI). The crate's items and the direction of the dependency are `design/machine-glue-below-the-kernel/`.

## Reasoning

Parameterizing an entry's bit layout is cheap: the spec reads entries through the abstract `PageEntry`, and only the decoders touch bits, so a second layout is a second set of decoders proven against the same `ensures`. Parameterizing page size or level count is not: the sizes and the four-level walk appear in the page-table invariants, the memory manager's free lists, the block orders of `design/capability-names-a-block/` and the lemmas over them, and every one would become a function of the target.

Nothing chosen needs that. The aarch64 4K granule with 48-bit VA is four levels of 512 eight-byte entries indexed by 9 bits each, blocks at level 1 (1G) and level 2 (2M), pages at level 3 (4K), with the output address in bits 47:12, 47:21 and 47:30: the x86_64 shape, down to the address masks. Level 0 maps no block on either.

Selecting by cfg rather than by trait follows from there being one implementation per target. A trait in Verus carries its specs on the trait and its proofs on each impl, threads a type parameter through every caller, and buys dispatch the kernel never does. A cfg-selected module with the same names gets the same checking from the compiler and the verifier, provided `tools/verify.py` runs once per target.

Sharing `TTBR0_EL1` with the kernel keeps the kernel/user table split the spec already has. Giving the kernel `TTBR1_EL1` would be the native aarch64 layout, but it moves the kernel's entries out of every process table and changes the invariant that a table's low top-level entries are the kernel's.

## Alternatives rejected

- **A 16K or 64K granule on aarch64.** 16K gives 2048 entries a level and 32M blocks; 64K gives 8192 entries, 512M blocks and three levels. Either makes the page sizes and level count per-target through the proofs. QEMU virt and the cores under test offer 4K.
- **A trait per item, or one `Arch` trait.** Heavier in Verus, as above, for no second implementation on any one target.
- **A portability layer over the hardware**, such as a generic MMU or interrupt abstraction. The principles forbid one beyond the arch module and the machine glue, and five items do not need it.
- **The kernel in the upper half through `TTBR1_EL1`.** Native to aarch64, but it changes the page-table spec on one target only.

## What this does not settle

- The IOMMU. The AMD IOMMU's device IDs, command opcodes and root-table format sit in the verified tree beside the kernel model, not in an arch item; SMMUv3 on QEMU virt is a separate model, and DART on bare Apple silicon would reopen the granule.
- The aarch64 values of each item but the syscall table: the descriptor bits, the EL1 frame, the memory attributes. Each is written from the Arm Architecture Reference Manual by the leaf that adds it.
- How `tools/verify.py` verifies the aarch64 module from this x86_64 host.
