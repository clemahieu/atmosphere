---
title: "One syscall entry, and every operation carries its arguments in registers"
date: 2026-11-10
status: active
tags: [abi, ipc, memory, portability]
one_line: "One entry, by position: the operation number, the capability's slot and five arguments in; a status word (status in its low 16 bits, ok 0, refused 1, unknown 2, again 3, and a badge in the upper 48) and five result words out, each output in the register of the input at its position. A table per target names the registers: syscall on x86_64, svc on aarch64. A send carries five words, four with a grant; the kernel copies nothing from user memory, and larger data goes through shared frames. A place in a space is a virtual address and a level, which the kernel splits into the path. Inspect, operation 15, returns a held capability's kind, base, order and rights in results 1 to 4. Unmap returns the cleared entry's accessed and dirty bits in results 1 and 2. Probe, operation 17, reads and clears the accessed and dirty bits of up to 64 level 1 entries and returns them as two masks in results 1 and 2. Power-off, operation 18, ends the run through a power capability, with argument 1 saying whether the run succeeded."
revisit_if: "A message that does not fit five words is on a hot path and the shared-frame ring is measured as its cost, an operation needs more than five argument words, a second entry is needed for a different privilege transition, or a target's instruction leaves fewer than seven registers free to carry an invocation."
confidence: "A packing judgement; each target's preserved set is the one its C convention keeps across a call, the memory operations' positions are counted against the verified functions' parameters in kernel/verified/capability, and the aarch64 table is written from the Arm Architecture Reference Manual; dom0's checks run through it at EL0 under KVM on a Cortex-A76, which tests the positions and that an immediate other than 0 returns unknown."
---

# The syscall ABI, in registers

## Decision

One entry. An invocation carries the operation number, the slot of the capability it invokes, and arguments 1 to 5. It returns the status word and result words 1 to 5. The status is the status word's low 16 bits; on a receive the badge is its upper 48. Each output comes back in the register that carried the input at the same position: the status word in the operation number's, result 1 in the slot's, and results 2 to 5 in arguments 1 to 4's. Argument 5 returns no result. Every name a process passes resolves within the caller's kernel instance, `design/one-kernel-instance/`. An operation reads only the positions it names here, and the others are ignored; a result position it does not name holds nothing the caller may use.

### Registers

One table per target, with the reasons for each. This section is the only place a register is named; the rest of this record names positions.

x86_64:

| Position | Register |
|---|---|
| operation number, then status word | `rax` |
| slot, then result 1 | `rdi` |
| argument 1, then result 2 | `rsi` |
| argument 2, then result 3 | `rdx` |
| argument 3, then result 4 | `r8` |
| argument 4, then result 5 | `r9` |
| argument 5 | `r10` |
| instruction | `syscall`; the kernel returns with `sysretq` to the instruction after it |
| preserved | `rbx`, `rbp`, `r12` to `r15`, `rsp`, `rflags` |
| clobbered | `rcx` and `r11`, which `syscall` overwrites with the return address and the flags; `r10` |

aarch64:

| Position | Register |
|---|---|
| operation number, then status word | `x8` |
| slot, then result 1 | `x0` |
| argument 1, then result 2 | `x1` |
| argument 2, then result 3 | `x2` |
| argument 3, then result 4 | `x3` |
| argument 4, then result 5 | `x4` |
| argument 5 | `x5` |
| instruction | `svc #0` from EL0; the kernel returns with `eret` to the instruction after it. An immediate other than 0 returns unknown. |
| preserved | `x18` to `x29`, `SP_EL0`, the condition flags `NZCV` |
| clobbered | `x5` to `x7`, `x9` to `x17`, `x30` |

Each table's preserved set is the one the target's C convention keeps across a call, and every other register the invocation does not return is clobbered. On x86_64 `syscall` itself takes `rcx` and `r11`. On aarch64 `svc` takes the exception to EL1, writes the address of the instruction after it to `ELR_EL1` and the caller's `PSTATE` to `SPSR_EL1`, and records exception class `0x15` with the immediate in `ESR_EL1`; it changes no general-purpose register, and the handler runs on `SP_EL1`, so the caller's `SP_EL0` is untouched (Arm Architecture Reference Manual, DDI 0487 M.d: `SVC` §C6.2.466; preferred exception return address §D1.4.1.5, rule RDKWPP; exception entry §D1.4.2; `ESR_EL1` §D24.2.44). The split there is the kernel's choice, not the instruction's. The Rust Reference's inline-assembly chapter gives the aarch64 C convention as the registers `clobber_abi("C")` leaves out, `x19` to `x29`. `x18` is preserved as well, because it is reserved on some aarch64 targets, where an `asm!` block cannot name it as clobbered; `x19` and `x29` cannot be named on any target. `x30` is the link register, which the C convention does not keep across a call.

The aarch64 operation number goes in `x8`, outside `x0` to `x7`, the registers the C convention passes arguments in, so the slot and the five arguments sit in the first six of them, in order. The status word comes back in `x8` too, by the position rule, which puts the five results in `x0` to `x4`: a server that hands a received message to a handler function passes it in that function's first five argument registers with no move. Two aarch64 tables were weighed and rejected:

- **The status word in `x0`, the C return register, and the results in `x1` to `x5`.** The C convention returns at most two words in registers, so no function call carries six results either way, and the position rule would differ between the targets.
- **The operation number in the `svc` immediate.** The number would be fixed per call site, so a library invoking an operation it is handed needs a branch per number, and the kernel reads it out of `ESR_EL1` rather than from a saved register.

The statuses:

| Status | Number | Meaning |
|---|---|---|
| ok | 0 | The operation is done. |
| refused | 1 | The capability, its rights or the arguments do not allow the operation; nothing changed. |
| unknown | 2 | No operation has the number in the operation position. |
| again | 3 | The operation took a bounded step and is not finished; invoke it again with the same inputs to go on, `design/one-lock-bounded-steps/`. |

`busy` takes the next number when an operation first returns it.

### IPC

A send carries five message words in arguments 1 to 5; with a grant, argument 5 names the capability, leaving four. A receive names the reply capability in argument 1 and a destination slot in argument 2, and returns the words in results 1 to 5, with a status flag if a capability arrived. A call also receives a reply, so it names a destination slot in argument 1 and carries four words in arguments 2 to 5, or three with a grant. `reply_recv` is one operation, since it is a server's hot path: the slot names the endpoint, argument 1 the reply capability and argument 2 the destination slot, with three reply words in arguments 3 to 5.

The kernel copies nothing from user memory for IPC. Larger data goes through shared frames. The thread's saved set is the preserved registers plus the seven positions, so a blocked thread's partial frame copy is well defined. Debug print is an operation on a console capability that takes words.

### Memory operations

A slot is an index in the caller's capability table. A base is a physical address inside the block of the capability that authorises the operation, as `design/capability-names-a-block/` defines it. A page offset counts 4K pages from the start of a frame capability's block.

| Operation | Slot | Argument 1 | Argument 2 | Argument 3 | Argument 4 |
|---|---|---|---|---|---|
| retype | untyped | kind | base | destination slot | table level |
| derive | source | destination slot | rights | base | order |
| move | source | destination slot | | | |
| delete | the capability | | | | |
| revoke | the capability | | | | |
| map | space | virtual address | level | frame | page offset |
| link | space | virtual address | level | untyped | table page base |
| unmap | space | virtual address | level | | |
| probe | space | virtual address | count | | |

Retype's kind in argument 1:

| Kind | Number | Reads | Result |
|---|---|---|---|
| 4K frame | 0 | base, destination slot | A frame capability of order 0 in the slot. |
| 2M frame | 1 | base, destination slot | `again` while the block is zeroed a slice at a time, then ok with a frame capability of order 9 in the slot. A later retype naming the same block goes on where an earlier one stopped. |
| table page | 2 | base, table level | An unlinked table page of level 1, 2 or 3 at the base. No capability names it, so it takes no slot; link names it by its base. |

Any other kind is refused. Revoke returns `again` while its run is not empty after its budget of steps, ok when it is, and refused when the slot names no capability, or when the flush epoch is at its limit, since a further step could not record its staleness.

Map, link and unmap name a place in a space the same way: the space capability in the slot, which must allow writing the space, a virtual address in argument 1 and a level in argument 2. The kernel splits the address into the four 9-bit indices of the path, bits 47 to 39, 38 to 30, 29 to 21 and 20 to 12, and refuses it unless:

- bits 63 to 47 are zero, so the address is canonical and in the lower half, the half a user mapping stays in;
- the bits below what one entry at the level covers are zero: 12 bits at level 1, 21 at level 2, 30 at level 3, 39 at level 4;
- the level is one the operation accepts.

An address in the root entries a process space keeps for the kernel is refused by the operation itself, as every entry the kernel holds is. So each accepted value names exactly one entry, and no two values name the same one.

- **map** writes the entry at the level: at level 1 the 4K page at the page offset of the frame capability in argument 3; at level 2 the 2M page there, whose offset is a multiple of 512. The entry must be empty and the tables above it linked.
- **link**, operation 16, writes the entry at the level with the table page at the base in argument 4, whose level is one below it, so argument 2 is 2, 3 or 4 and the table page's own level is argument 2 minus 1. The untyped in argument 3 must cover the table page's block. The tables above the entry must be linked; a space's root is level 4.
- **unmap** clears the entry at the level, which must map a frame. Level 1 is the only level it accepts.

Unmap reads the entry's word in the same atomic step that clears it, and returns ok with:

| Result | What |
|---|---|
| 1 | 1 when the entry's accessed bit was set as it was cleared, else 0 |
| 2 | 1 when the entry's dirty bit was set as it was cleared, else 0 |
| 3 | 1 when the target maintains the accessed bit, else 0 |
| 4 | 1 when the target maintains the dirty bit, else 0 |

A bit the target does not maintain says nothing, as for probe. A translation another core still caches stays usable until the unmap's flush, `design/flush-without-waiting/`, and a write through it sets no bit the unmap read, so a pager treats the page as possibly written until that flush is done.

### Probe

Probe is operation 17. It names a place as map does, at level 1 always, so argument 2 carries a count of entries in place of the level: the count entries from the one the address names, 1 to 64, which must lie in that one level 1 table. The address is refused by the rules above for level 1, and the probe is refused for a count of 0 or over 64, for a range that leaves the table, and when the tables above it are not linked. For each present entry it reads and clears the accessed and dirty bits the processor sets, and it returns ok with:

| Result | What |
|---|---|
| 1 | the accessed mask: bit i is entry i's accessed bit as read |
| 2 | the dirty mask: bit i is entry i's dirty bit as read |
| 3 | 1 when the target maintains the accessed bit, else 0 |
| 4 | 1 when the target maintains the dirty bit, else 0 |

An absent entry's bits are clear in both masks, as is every bit at or past the count. A mask whose bit the target does not maintain says nothing, and a pager falls back to unmapping and taking the fault, `design/arch-module/`. Probe changes no mapping and does not flush, so a translation still cached may hide a use until its next walk: the caller treats that as sampling error, and confirms with an unmap when it matters.

### Power-off

Power-off is operation 18. It names a power capability in the slot, which boot hands the root at `ROOT_POWER_SLOT`, `design/root-process-at-boot/`, and asks for no right but holding it, as print asks of a console. Argument 1 says how the run ended: not zero for a run that succeeded, zero for one that failed. It is refused when the slot holds no power capability, a console among the rest, and nothing changed. Accepted, it does not return: the verified dispatch answers ok with the kernel unchanged, and the entry, once the kernel's lock is released, calls the machine's `shutdown` with that answer, `design/machine-glue-below-the-kernel/`, on every target. What each ending looks like from outside is the machine's: on the PC a success is the ACPI power-off and a failure the write to the test device named on the kernel's command line, and on QEMU virt a success is PSCI `SYSTEM_OFF`.

### Inspect

Inspect is operation 15. It names a capability in the slot and asks for no right but holding it. It returns ok with the capability's kind in result 1, the physical base of its block in result 2, its order in result 3 and its rights in result 4, and refused when the slot holds no capability. It changes nothing.

The kinds in result 1:

| Kind | Number |
|---|---|
| untyped | 0 |
| frame | 1 |
| process | 2 |
| thread | 3 |
| endpoint | 4 |
| reply | 5 |
| notification | 6 |
| space | 7 |
| device | 8 |
| console | 9 |
| power | 10 |

## Reasoning

Copying nothing from user memory keeps every operation a bounded step with no page walk on its arguments, `design/one-lock-bounded-steps/`, and keeps the reach theorem's IPC relation to a fixed delivery into the receiver's frame, `design/theorem-over-reach/`. A first packing did not add up for a grant or a receive, which is why the slot and reply positions are fixed here rather than left to a leaf.

Naming positions rather than registers keeps every operation, the dispatch and this record the same on each target; only the table differs, and it is the arch module's syscall item, `design/arch-module/`. Returning each output in its input's register makes the write-back one rule on every target: the status over the operation number, the results over the slot and the first four arguments. Clobbering everything outside the C convention's preserved set lets a thread that blocked in an invocation be resumed by restoring only the preserved registers and the outputs and clearing the rest, without storing what the process had in the others.

The memory operations fit five words because a place in a space is one address, not four indices. The verified map takes the space, four path indices, the frame and the offset, seven values beyond the table root; with the path packed into the address it is five with the level. The address is also what a process already knows of where a page goes, and refusing every bit the split does not use keeps one address to one entry, so a map at a kernel-half or non-canonical address is refused by the same rule that splits every accepted one.

Link names its parent by the address and the level rather than by the parent table's physical base, so a process never tracks where its tables sit and the kernel never trusts a physical address as a table: it walks from the space's root, as map does. The level is passed rather than taken from the table page's record, so a link whose table page has the wrong level for the entry the address reaches is refused rather than linked somewhere the caller did not mean.

Every retype names a base inside its untyped's block, and the bases and orders of the untyped boot hands the root depend on the machine's memory, `design/root-process-at-boot/`. Inspect is how the root learns them, and how any process reads back what its own retypes, derives and moves left in its slots. Reading one slot is a bounded step that copies nothing, and it stays current after the process changes its table.

Unmap returns the bits because it reads and clears the entry anyway: a pager evicting a page learns in the same call whether it was used and whether it must be written back, as L4 X.2's unmap delivers the referenced and written status of what it unmaps. The read and the clear are one exchange, so a bit another core's walk sets between them is not lost.

Probe returns its masks in result words because 64 entries' two bits are 128 bits, which two words carry, and reading them into user memory would be the copy this record rules out. It reads at most 64 entries under the lock, a bounded step, `design/one-lock-bounded-steps/`, and stays in one level 1 table so the walk to it is one, as map's is. It does not flush because the bits are a sample a pager reads repeatedly: a flush per probe would cost the IPIs the bits exist to avoid, and a write always reaches the entry, since the processor walks to set dirty through a translation cached with it clear.

Power-off is an operation because ending the run is the machine's to do, and a process holds no port, no firmware call and no I/O privilege to do it with: the root reports how its run ended and the kernel's glue does the rest, the same way on every target. It asks for a power capability, a kind of its own, and not for the console, so that a process handed the console to print through cannot stop the machine, `design/root-process-at-boot/`; a process without a power capability cannot.

Retype is one operation whose kind is an argument, since every kind consumes the same authority, an untyped and a base; separate numbers per kind would spend operation numbers on what is one check. A large frame and a revoke return `again` because both do more work than one bounded step allows.

## Alternatives rejected

- **A message buffer in user memory.** A copy the kernel must walk and bound, and a relation the theorem must widen.
- **Separate reply and receive operations.** Two entries on every server round trip.
- **The path as four index arguments.** With the space, the frame and the offset that is seven, two more than the entry carries.
- **Accepting the upper canonical half.** A second rule for the sign extension, for space no process needs; the lower half is where the boot check on dom0's runs already keeps every user mapping.
- **Boot writing a description of every slot into a frame the root maps.** It needs a frame and a format, and it is stale once the root retypes, moves or deletes.
- **Finding an untyped's base by probing retype.** One refused invocation per aligned candidate base across physical memory, per order.
- **The root ending its run with a port write of its own.** It needs the process to run with I/O privilege, ambient authority over every port, and it exists on one machine: QEMU virt has no such port.
- **A separate operation number for the large map.** The level already says which entry is written, and the same argument says it for link and unmap.

The rejected aarch64 tables are under Registers.

## What this does not settle

- The kinds a retype of a space, a process or a thread takes, and the positions of claim, destroy and the thread and process operations: they take the next kind numbers and argument positions when they are wired, inside the five words.
- A 1G frame: retype accepts no kind for it, since nothing maps one.
- An unmap of a 2M entry: unmap accepts level 2 when one is proven.
- The SIMD and floating-point registers and the user thread-pointer register: the kernel uses none of them, and where they sit in a thread's saved state is not decided here.
