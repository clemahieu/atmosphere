---
title: "One syscall entry, and every operation carries its arguments in registers"
date: 2026-11-14
status: active
tags: [abi, ipc, memory, portability]
one_line: "One entry, by position: the operation number, the capability's slot and five arguments in; a status word (status in its low 16 bits, ok 0, refused 1, unknown 2, again 3, and a badge in the upper 48) and five result words out, each output in the register of the input at its position. A table per target names the registers: syscall on x86_64, svc on aarch64. A send carries five words, four with a grant; the kernel copies nothing from user memory, and larger data goes through shared frames. A place in a space is a virtual address and a level, which the kernel splits into the path. A table position is one word: the index in bits 0 to 15, and in bits 16 to 31 one more than the slot of a process capability with control in the caller's table, or 0 for the caller's own; any higher bit is refused. Inspect, operation 15, returns a held capability's kind, base, order and rights in results 1 to 4. Unmap returns the cleared entry's accessed and dirty bits in results 1 and 2. Probe, operation 17, reads and clears the accessed and dirty bits of up to 64 level 1 entries and returns them as two masks in results 1 and 2. Power-off, operation 18, ends the run through a power capability, with argument 1 saying whether the run succeeded. Retype kind 5 is a process and kind 6 a thread, whose process slot is argument 4, an index in the caller's own table. Destroy, operation 9, names a process or a thread. Reading and writing a thread's saved frame are operations 19 and 20: argument 1 is a word index, a multiple of four, and four words travel in results 1 to 4 or in arguments 2 to 5; every other word stays, and a write then applies the user-return rule to the whole frame. Place is operation 21, with the core capability's slot in argument 1 and the priority in argument 2. Start is operation 22 and suspend is operation 23, each naming only the thread. Derive's argument 5 is the child's badge: 0 keeps the parent's, and any other value is accepted only from a capability whose own badge is 0, an endpoint's below 2^48 or a notification's below 2^63."
revisit_if: "A message that does not fit five words is on a hot path and the shared-frame ring is measured as its cost, an operation needs more than five argument words, a second entry is needed for a different privilege transition, or a target's instruction leaves fewer than seven registers free to carry an invocation."
confidence: "A packing judgement; each target's preserved set is the one its C convention keeps across a call, the operations' positions are counted against the verified functions' parameters in kernel/verified/capability, and the aarch64 table is written from the Arm Architecture Reference Manual; dom0's checks run through it at EL0 under KVM on a Cortex-A76, which tests the positions and that an immediate other than 0 returns unknown."
---

# The syscall ABI, in registers

## Decision

One entry. An invocation carries the operation number, the slot of the capability it invokes, and arguments 1 to 5. It returns the status word and result words 1 to 5. The status is the status word's low 16 bits; on a receive the badge is its upper 48. Each output comes back in the register that carried the input at the same position: the status word in the operation number's, result 1 in the slot's, and results 2 to 5 in arguments 1 to 4's. Argument 5 returns no result. Every name a process passes resolves within the caller's kernel instance, `design/one-kernel-instance/`. An operation reads only the positions it names here, and the others are ignored; a result position it does not name holds nothing the caller may use.

### Registers

One table per target, with the reasons for each. The invocation tables here, and the saved-frame tables under Thread and process operations, are the only places a register is named; the rest of this record names positions.

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

### Table positions

A table position names a slot, or a root entry for a leaf, in the caller's own table or, through a process capability with the control right in the caller's own table, in that process's table, `design/process-holds-capabilities/`. It travels as one word:

| Bits | What |
|---|---|
| 0 to 15 | the index: a slot's, or a root entry's |
| 16 to 31 | 0 for the caller's own table; otherwise one more than the slot of the process capability whose process's table the index is in |
| 32 to 63 | zero; a word with any of them set is refused |

So one word names one position, and a slot number of the caller's own table is its own position word. The capability a position goes through is always in the caller's own table, so a slot from 0 to 65534 can be gone through. Derive reads its source, in the slot, and its destination, in argument 1, as positions; move its source and destination the same way; delete, revoke and inspect the capability in the slot; and retype's leaf kind its root entry, in argument 3. A derive whose source names another process's table is refused: derive's parent is the caller's own. Every other operation names the capability it exercises by an index in the caller's own table.

### Memory operations

A slot is an index in the caller's capability table, and a position is the word above. A base is a physical address inside the block of the capability that authorises the operation, as `design/capability-names-a-block/` defines it. A page offset counts 4K pages from the start of a frame capability's block.

| Operation | Slot | Argument 1 | Argument 2 | Argument 3 | Argument 4 | Argument 5 |
|---|---|---|---|---|---|---|
| retype | untyped | kind | base | destination slot | table level | |
| derive | source position | destination position | rights | base | order | badge |
| move | source position | destination position | | | | |
| delete | the capability's position | | | | | |
| revoke | the capability's position | | | | | |
| map | space | virtual address | level | frame | page offset | |
| link | space | virtual address | level | untyped | table page base | |
| unmap | space | virtual address | level | | | |
| probe | space | virtual address | count | | | |

Derive's badge marks the child for whoever the object delivers it to: an endpoint's receiver, who reads it in the upper 48 bits of the status word, or a notification's waiter, who reads it ORed into the word. 0 keeps the parent's badge. Any other value is refused unless the parent's own badge is 0 and the parent is an endpoint capability with the value below 2^48, or a notification capability with the value below 2^63, which leaves the word's waiter bit to the kernel (`design/notification-word-reserves-the-waiter-bit/`). So a badge, once set, stays the same in the whole subtree below it.

Retype's kind in argument 1:

| Kind | Number | Reads | Result |
|---|---|---|---|
| 4K frame | 0 | base, destination slot | A frame capability of order 0 in the slot. |
| 2M frame | 1 | base, destination slot | `again` while the block is zeroed a slice at a time, then ok with a frame capability of order 9 in the slot. A later retype naming the same block goes on where an earlier one stopped. |
| table page | 2 | base, table level | An unlinked table page of level 1, 2 or 3 at the base. No capability names it, so it takes no slot; link names it by its base. |
| table leaf | 3 | base, the root entry's position in argument 3 | A table leaf of the two pages at the base in the empty root entry: of the caller's table, or of a live process's it controls, whose table it gives that entry's 127 slots. No capability names it, so it takes no slot. |
| free | 4 | base, the frame's order in argument 4: 0, 9 or 18 | Frees the dead frame at the base, one whose last capability is gone: `again` while a core may still hold a translation to it, then ok with the block free, so a later retype can type it again. |
| process | 5 | base, destination slot | A process capability in the slot, `design/process-holds-capabilities/`. |
| thread | 6 | base, destination slot, the process's slot in argument 4 | A thread capability in the slot, bound to that process. The process slot is an index in the caller's own table, of a live process capability with control. |

Any other kind is refused. A thread whose argument 4 is not such a slot is refused, as is one whose process capability is at the depth limit or whose process block cannot take another reference, and a refusal changes nothing. The destination slot stays in argument 3 for every kind that takes one. Revoke returns `again` while its run is not empty after its budget of steps, ok when it is, and refused when the slot names no capability, or when the flush epoch is at its limit, since a further step could not record its staleness.

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

Inspect is operation 15. It names a capability by the position in the slot and asks for no right but commanding it: holding it, or controlling the process that does. It returns ok with the capability's kind in result 1, the physical base of its block in result 2, its order in result 3 and its rights in result 4, and refused when the position holds no capability. It changes nothing.

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
| core | 11 |

### Thread and process operations

Destroy is operation 9. The slot names a process or a thread capability with control, and the operation reads no argument. It is refused when the slot holds no such capability, or when that object is already dead, and a refusal changes nothing. Accepted, a process's record is dead and each core that has its space loaded is sent an IPI, so that core finds its current thread's process dead at its next kernel entry; the process's threads, table, space and capabilities stay, and a holder claims a slot afterwards by a move whose source position names the dead process's table, `design/process-holds-capabilities/`. A thread that is Running gets a pending stop that makes it dead, and, when it runs on a core other than the caller's, that core is sent the stop IPI. Any other thread is dead at once. Either way its capabilities and its process binding stay. When the capability names the caller's own process or the caller's own thread, the caller does not return to user mode: the entry's check moves it off. Otherwise the status is ok.

| Operation | Number | Slot | Argument 1 | Argument 2 | Argument 3 | Argument 4 | Argument 5 |
|---|---|---|---|---|---|---|---|
| destroy | 9 | process or thread | | | | | |
| read registers | 19 | thread | word index | | | | |
| write registers | 20 | thread | word index | word 0 | word 1 | word 2 | word 3 |
| place | 21 | thread | core slot | priority | | | |
| start | 22 | thread | | | | | |
| suspend | 23 | thread | | | | | |

Each of these asks for the control right on the capability in the slot. Place also names a core capability, by the slot index in argument 1, and a thread retype names its process by the slot index in argument 4. Both indices name the caller's own table.

Read registers and write registers move the Inactive thread's saved frame, four words at a call. Argument 1 is the index of the first word. A write is refused, and nothing changes, when the index is not a multiple of four or not below the frame's length, when the slot holds no live thread capability with control, when the thread is not Inactive, or when the program counter the resulting frame would hold is not a user address. A read has those refusals apart from the program counter. A call that is accepted transfers the words that remain, up to four: a write takes them from arguments 2 onward and ignores an argument past the frame, and a read returns them in results 1 onward with a result past the frame holding zero. Repeating the call at each multiple of four covers the frame.

The words are the frame's field order, which is the target's, so the same index names different registers on the two targets. x86_64 has 21 words:

| Word | What a write sets, and a read returns |
|---|---|
| 0 | `r15` |
| 1 | `r14` |
| 2 | `r13` |
| 3 | `r12` |
| 4 | `rbp` |
| 5 | `rbx` |
| 6 | `r11` |
| 7 | `r10` |
| 8 | `r9` |
| 9 | `r8` |
| 10 | `rcx` |
| 11 | `rdx` |
| 12 | `rsi` |
| 13 | `rdi` |
| 14 | `rax` |
| 15 | error code |
| 16 | `rip`, the program counter |
| 17 | `cs` |
| 18 | `rflags` |
| 19 | `rsp`, the stack pointer |
| 20 | `ss` |

aarch64 has 34 words. Words 0 to 30 are `x0` to `x30`. Word 31 is `SP_EL0`, the stack pointer. Word 32 is `ELR_EL1`, the program counter. Word 33 is `SPSR_EL1`.

A write stores its window and then applies the user-return rule to the whole frame, `user_frame` in `kernel/verified/arch/`, including when the window did not cover the words the rule owns. On x86_64 the code and stack selectors become the user selectors, and the flags keep only those user mode can set, with interrupts enabled. On aarch64 `SPSR_EL1` keeps the condition flags and the mode is EL0. Every word outside the window keeps what the frame held, apart from that rule, so every accepted write leaves the selectors as user mode's. A read returns the words as stored: after a write, the selectors and the flags are what the rule stored, and a thread that has never been written still reads as zero. A frame saved at a system call reads as that partial copy, the preserved registers, the seven invocation positions and the return state, with the clobbered registers zero.

One x86_64 invocation at index 16 carries the program counter, `cs`, `rflags` and the stack pointer. An aarch64 stack pointer is word 31, in the window at 28, and its program counter is word 32, in the window at 32.

Place names the thread in the slot and puts it on a core at a priority. Argument 1 is the slot of a core capability in the caller's own table, and argument 2 is the priority: a greater number outranks a lesser one, and the number must be at or below that capability's maximum, which is at most 255. It is refused when the thread is not Inactive, when it is already placed, when argument 1 holds no live core capability, when that capability is at the depth limit, or when the priority is above its maximum, and a refusal changes nothing. Accepted, the thread's placement is a binding under the core capability, `design/cpu-time-as-capability/`.

Start names the thread in the slot and reads no argument. The thread must be Inactive, bound to a process and placed; otherwise the start is refused and nothing changes. Accepted, the thread is Runnable at the back of its priority on the core it is placed on, and when it outranks what that core runs, the core is sent a reschedule IPI, `design/cpu-time-as-capability/`. The priority is the placement's.

Suspend names the thread in the slot and reads no argument. An Inactive thread, a Runnable thread, or the caller's current thread is Inactive afterwards, and when it was the caller's current thread the core runs nothing; the status is ok. A thread Running on another core gets a pending stop and that core a stop IPI, and the status is again: the same invocation later sees the thread Inactive, once that core has entered the kernel, `design/one-lock-bounded-steps/`. A thread that is blocked or dead, or a capability without control, is refused, and nothing changes.

## Reasoning

Copying nothing from user memory keeps every operation a bounded step with no page walk on its arguments, `design/one-lock-bounded-steps/`, and keeps the reach theorem's IPC relation to a fixed delivery into the receiver's frame, `design/theorem-over-reach/`. A first packing did not add up for a grant or a receive, which is why the slot and reply positions are fixed here rather than left to a leaf.

Naming positions rather than registers keeps every operation, the dispatch and this record the same on each target; only the table differs, and it is the arch module's syscall item, `design/arch-module/`. Returning each output in its input's register makes the write-back one rule on every target: the status over the operation number, the results over the slot and the first four arguments. Clobbering everything outside the C convention's preserved set lets a thread that blocked in an invocation be resumed by restoring only the preserved registers and the outputs and clearing the rest, without storing what the process had in the others.

The memory operations fit five words because a place in a space is one address, not four indices. The verified map takes the space, four path indices, the frame and the offset, seven values beyond the table root; with the path packed into the address it is five with the level. The address is also what a process already knows of where a page goes, and refusing every bit the split does not use keeps one address to one entry, so a map at a kernel-half or non-canonical address is refused by the same rule that splits every accepted one.

Link names its parent by the address and the level rather than by the parent table's physical base, so a process never tracks where its tables sit and the kernel never trusts a physical address as a table: it walks from the space's root, as map does. The level is passed rather than taken from the table page's record, so a link whose table page has the wrong level for the entry the address reaches is refused rather than linked somewhere the caller did not mean.

Every retype names a base inside its untyped's block, and the bases and orders of the untyped boot hands the root depend on the machine's memory, `design/root-process-at-boot/`. Inspect is how the root learns them, and how any process reads back what its own retypes, derives and moves left in its slots. Reading one slot is a bounded step that copies nothing, and it stays current after the process changes its table.

Unmap returns the bits because it reads and clears the entry anyway: a pager evicting a page learns in the same call whether it was used and whether it must be written back, as L4 X.2's unmap delivers the referenced and written status of what it unmaps. The read and the clear are one exchange, so a bit another core's walk sets between them is not lost.

Probe returns its masks in result words because 64 entries' two bits are 128 bits, which two words carry, and reading them into user memory would be the copy this record rules out. It reads at most 64 entries under the lock, a bounded step, `design/one-lock-bounded-steps/`, and stays in one level 1 table so the walk to it is one, as map's is. It does not flush because the bits are a sample a pager reads repeatedly: a flush per probe would cost the IPIs the bits exist to avoid, and a write always reaches the entry, since the processor walks to set dirty through a translation cached with it clear.

Power-off is an operation because ending the run is the machine's to do, and a process holds no port, no firmware call and no I/O privilege to do it with: the root reports how its run ended and the kernel's glue does the rest, the same way on every target. It asks for a power capability, a kind of its own, and not for the console, so that a process handed the console to print through cannot stop the machine, `design/root-process-at-boot/`; a process without a power capability cannot.

A table position is one word of two 16-bit fields because a table has 65,536 indices and a position goes through at most one capability, which is in the caller's own table: both fit with room to spare, so no operation that takes a position needs a second argument for it and none changed its argument count. The table field holds one more than the slot so that 0, the value of every slot number a process already passes, names the caller's own table. Refusing every bit above bit 31 keeps one word to one position, as the address rule keeps one address to one entry.

Retype is one operation whose kind is an argument, since every kind consumes the same authority, an untyped and a base; separate numbers per kind would spend operation numbers on what is one check. A large frame and a revoke return `again` because both do more work than one bounded step allows. A process is one more kind, and a thread is another whose extra word names the process it is bound into, because that binding is made at retype, `design/thread-bound-at-retype/`.

Destroy takes operation 9, the number between unmap and send. Place carries the two words `place` takes, the core capability's slot and the priority. Start and suspend name only the thread, because the priority is already the placement's and a suspend that stops another core returns again, as a revoke does.

The saved frame is longer than five words, and the kernel copies nothing from user memory, so a read or a write moves four words at an index. Four is what results 1 to 4 hold, and what arguments 2 to 5 hold with the index in argument 1. The index is a multiple of four, so each word belongs to one call, and the call at the tail is shorter than four where the frame's length is not a multiple of four. Repeating it covers the frame a holder writes whole, `design/process-holds-capabilities/`. The user-return rule runs on the whole frame after every write, so a window that carries neither selector nor flags still leaves them as user mode's, and a write grants nothing the thread could not do to itself.

## Alternatives rejected

- **A message buffer in user memory.** A copy the kernel must walk and bound, and a relation the theorem must widen.
- **Separate reply and receive operations.** Two entries on every server round trip.
- **The path as four index arguments.** With the space, the frame and the offset that is seven, two more than the entry carries.
- **Accepting the upper canonical half.** A second rule for the sign extension, for space no process needs; the lower half is where the boot check on dom0's runs already keeps every user mapping.
- **Boot writing a description of every slot into a frame the root maps.** It needs a frame and a format, and it is stale once the root retypes, moves or deletes.
- **Finding an untyped's base by probing retype.** One refused invocation per aligned candidate base across physical memory, per order.
- **The root ending its run with a port write of its own.** It needs the process to run with I/O privilege, ambient authority over every port, and it exists on one machine: QEMU virt has no such port.
- **A separate operation number for the large map.** The level already says which entry is written, and the same argument says it for link and unmap.
- **A write that sets the program counter and the stack pointer and clears every other word.** A holder could not put the rest of a saved frame back.
- **A count beside the index, with the frame's words after it.** The count would spend one of the five words, so a call would move three. A fixed four, shorter at the tail, needs no count.
- **The frame through a shared page.** A copy from user memory, on a path a controller walks once.
- **A new operation number for destroy.** Operation 9 already sits between unmap and send.

The rejected aarch64 tables are under Registers.

## What this does not settle

- The kind a retype of a space takes. It takes the next kind number after the thread's, and which word carries its space kind, when a space is wired.
- A 1G frame: retype accepts no kind for it, since nothing maps one.
- An unmap of a 2M entry: unmap accepts level 2 when one is proven.
- The SIMD and floating-point registers and the user thread-pointer register: the kernel uses none of them, and where they sit in a thread's saved state is not decided here. Read and write of the saved frame do not transfer them.
