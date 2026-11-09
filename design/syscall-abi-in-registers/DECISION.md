---
title: "One syscall entry, and every operation carries its arguments in registers"
date: 2026-11-09
status: active
tags: [abi, ipc, memory]
one_line: "One entry: rax the operation, rdi the capability index, rsi, rdx, r8, r9 and r10 the arguments; rax returns status in its low 16 bits (ok 0, refused 1, unknown 2, again 3) and a badge in the upper 48. A send carries five words, four with a grant; the kernel copies nothing from user memory, and larger data goes through shared frames. A place in a space is a virtual address in rsi and a level in rdx, which the kernel splits into the path. Inspect, operation 15, returns a held capability's kind, base, order and rights in rdi, rsi, rdx and r8."
revisit_if: "A message that does not fit five words is on a hot path and the shared-frame ring is measured as its cost, an operation needs more than five argument words, or a second entry is needed for a different privilege transition."
confidence: "A packing judgement; the preserved-register set is the one the existing syscall convention keeps, and the memory operations' registers are counted against the verified functions' parameters in kernel/verified/capability."
---

# The syscall ABI, in registers

## Decision

One entry. `rax` holds the operation, `rdi` the capability index, and `rsi`, `rdx`, `r8`, `r9` and `r10` arguments. On return `rax` holds status in its low 16 bits, and on a receive the badge in its upper 48; those five and `rdi` hold results. `rbx`, `rbp`, `r12` to `r15`, `rsp`, `rip` and flags are preserved and `rcx` and `r11` clobbered, the convention the kernel already keeps. Every name a process passes resolves within the caller's kernel instance, `design/one-kernel-instance/`. An operation reads only the registers it names here; the others are ignored.

The statuses:

| Status | Number | Meaning |
|---|---|---|
| ok | 0 | The operation is done. |
| refused | 1 | The capability, its rights or the arguments do not allow the operation; nothing changed. |
| unknown | 2 | No operation has the number in `rax`. |
| again | 3 | The operation took a bounded step and is not finished; invoke it again with the same registers to go on, `design/one-lock-bounded-steps/`. |

`busy` takes the next number when an operation first returns it.

### IPC

A send carries five message words in `rsi`, `rdx`, `r8`, `r9` and `r10`; with a grant, `r10` names the capability, leaving four. A receive names the reply capability in `rsi` and a destination slot in `rdx`, and returns the words in `rdi`, `rsi`, `rdx`, `r8` and `r9`, with a status flag if a capability arrived. A call also receives a reply, so it names a destination slot in `rsi` and carries four words, or three with a grant. `reply_recv` is one operation, since it is a server's hot path: `rdi` names the endpoint, `rsi` the reply capability and `rdx` the destination slot, with three reply words in `r8`, `r9` and `r10`.

The kernel copies nothing from user memory for IPC. Larger data goes through shared frames. The thread's saved set is the preserved registers plus these six plus `rax`, so a blocked thread's partial frame copy is well defined. Debug print is an operation on a console capability that takes words.

### Memory operations

A slot is an index in the caller's capability table. A base is a physical address inside the block of the capability that authorises the operation, as `design/capability-names-a-block/` defines it. A page offset counts 4K pages from the start of a frame capability's block.

| Operation | `rdi` | `rsi` | `rdx` | `r8` | `r9` |
|---|---|---|---|---|---|
| retype | untyped | kind | base | destination slot | table level |
| derive | source | destination slot | rights | base | order |
| move | source | destination slot | | | |
| delete | the capability | | | | |
| revoke | the capability | | | | |
| map | space | virtual address | level | frame | page offset |
| link | space | virtual address | level | untyped | table page base |
| unmap | space | virtual address | level | | |

Retype's kind in `rsi`:

| Kind | Number | Reads | Result |
|---|---|---|---|
| 4K frame | 0 | base, destination slot | A frame capability of order 0 in the slot. |
| 2M frame | 1 | base, destination slot | `again` while the block is zeroed a slice at a time, then ok with a frame capability of order 9 in the slot. A later retype naming the same block goes on where an earlier one stopped. |
| table page | 2 | base, table level | An unlinked table page of level 1, 2 or 3 at the base. No capability names it, so it takes no slot; link names it by its base. |

Any other kind is refused. Revoke returns `again` while its run is not empty after its budget of steps, ok when it is, and refused when the slot names no capability, or when the flush epoch is at its limit, since a further step could not record its staleness.

Map, link and unmap name a place in a space the same way: the space capability in `rdi`, which must allow writing the space, a virtual address in `rsi` and a level in `rdx`. The kernel splits the address into the four 9-bit indices of the path, bits 47 to 39, 38 to 30, 29 to 21 and 20 to 12, and refuses it unless:

- bits 63 to 47 are zero, so the address is canonical and in the lower half, the half a user mapping stays in;
- the bits below what one entry at the level covers are zero: 12 bits at level 1, 21 at level 2, 30 at level 3, 39 at level 4;
- the level is one the operation accepts.

An address in the root entries a process space keeps for the kernel is refused by the operation itself, as every entry the kernel holds is. So each accepted value names exactly one entry, and no two values name the same one.

- **map** writes the entry at the level: at level 1 the 4K page at the page offset of the frame capability in `r8`; at level 2 the 2M page there, whose offset is a multiple of 512. The entry must be empty and the tables above it linked.
- **link**, operation 16, writes the entry at the level with the table page at the base in `r9`, whose level is one below it, so `rdx` is 2, 3 or 4 and the table page's own level is `rdx` minus 1. The untyped in `r8` must cover the table page's block. The tables above the entry must be linked; a space's root is level 4.
- **unmap** clears the entry at the level, which must map a frame. Level 1 is the only level it accepts.

### Inspect

Inspect is operation 15. It names a capability in `rdi` and asks for no right but holding it. It returns ok with the capability's kind in `rdi`, the physical base of its block in `rsi`, its order in `rdx` and its rights in `r8`, and refused when the slot holds no capability. It changes nothing.

The kinds in `rdi`:

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

## Reasoning

Copying nothing from user memory keeps every operation a bounded step with no page walk on its arguments, `design/one-lock-bounded-steps/`, and keeps the reach theorem's IPC relation to a fixed delivery into the receiver's frame, `design/theorem-over-reach/`. A first packing did not add up for a grant or a receive, which is why the slot and reply positions are fixed here rather than left to a leaf.

The memory operations fit five words because a place in a space is one address, not four indices. The verified map takes the space, four path indices, the frame and the offset, seven values beyond the table root; with the path packed into the address it is five with the level. The address is also what a process already knows of where a page goes, and refusing every bit the split does not use keeps one address to one entry, so a map at a kernel-half or non-canonical address is refused by the same rule that splits every accepted one.

Link names its parent by the address and the level rather than by the parent table's physical base, so a process never tracks where its tables sit and the kernel never trusts a physical address as a table: it walks from the space's root, as map does. The level is passed rather than taken from the table page's record, so a link whose table page has the wrong level for the entry the address reaches is refused rather than linked somewhere the caller did not mean.

Every retype names a base inside its untyped's block, and the bases and orders of the untyped boot hands the root depend on the machine's memory, `design/root-process-at-boot/`. Inspect is how the root learns them, and how any process reads back what its own retypes, derives and moves left in its slots. Reading one slot is a bounded step that copies nothing, and it stays current after the process changes its table.

Retype is one operation whose kind is an argument, since every kind consumes the same authority, an untyped and a base; separate numbers per kind would spend operation numbers on what is one check. A large frame and a revoke return `again` because both do more work than one bounded step allows.

## Alternatives rejected

- **A message buffer in user memory.** A copy the kernel must walk and bound, and a relation the theorem must widen.
- **Separate reply and receive operations.** Two entries on every server round trip.
- **The path as four index registers.** With the space, the frame and the offset that is seven, two more than the entry carries.
- **Accepting the upper canonical half.** A second rule for the sign extension, for space no process needs; the lower half is where the boot check on dom0's runs already keeps every user mapping.
- **Boot writing a description of every slot into a frame the root maps.** It needs a frame and a format, and it is stale once the root retypes, moves or deletes.
- **Finding an untyped's base by probing retype.** One refused invocation per aligned candidate base across physical memory, per order.
- **A separate operation number for the large map.** The level already says which entry is written, and the same register says it for link and unmap.

## What this does not settle

- The kinds a retype of a space, a process or a thread takes, and the registers of claim, destroy and the thread and process operations: they take the next kind numbers and argument positions when they are wired, inside the five words.
- A 1G frame: retype accepts no kind for it, since nothing maps one.
- An unmap of a 2M entry: unmap accepts level 2 when one is proven.
