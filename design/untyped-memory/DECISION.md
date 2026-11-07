---
title: "The kernel allocates nothing after boot: memory is untyped capabilities retyped from user space"
date: 2026-11-05
status: active
tags: [capability, memory, purity]
one_line: "Physical memory is held as untyped capabilities and retyped into kernel objects and frames from user space; containers and kernel quotas are gone; mapping, paging and allocation policy live in a standard pager and allocator library an application can swap."
revisit_if: "It follows from the purity principle in CLAUDE.md; it is wrong only if an application class cannot be served by any user-space pager, which would be a reason to revisit the principle, not this record alone."
confidence: "A purity judgement by the human with its costs priced and accepted: a user-level memory manager to build, and most of the container-based proof to rewrite."
---

# The kernel allocates nothing after boot

## Decision

Everything the kernel holds after boot is retyped from untyped memory by user space. Untyped is free memory. The object kinds are frame, process, thread, endpoint, reply, notification, table leaf and table page; each is a power-of-two block of 4K pages. A process holds an address space root and a capability table root. Retyping requires a capability to the untyped memory with the retype right. Containers, kernel quotas, the process tree and the kernel's free lists do not exist. Boot-sized and never retyped: page metadata, per-CPU state, and the capabilities boot hands the root process, `design/root-process-at-boot/`.

Mapping, paging and allocation policy live in user space. A standard pager and allocator library ships as the default and an application can swap it; most users never think about it. Revocation is required, since a pager must take frames back to page them out.

## Context

Before this, endpoints sat in per-thread slots, pages in per-process tables and devices in a per-process table, and creating memory, threads, processes or endpoints needed only container quota, which is close to ambient authority. The options were to keep containers, to add capabilities beside them, or to make memory itself a capability. Removing containers was known to be cross-cutting: at the time `owning_container` appeared 822 times and `quota` 311 times across the kernel and process manager, with the allocator at 3,565 lines and the container and quota files at 5,105 of 39,377 verified lines.

## Reasoning

The human chose untyped memory for purity and because it gives applications the most flexibility: the kernel decides no allocation policy, so a process can only consume what it was granted, and no kernel resource can be exhausted by a process that was not given it. This is seL4's published model as described in Elkaduwe, Derrin and Elphinstone 2008 and the seL4 SOSP 2009 paper, read as papers; no seL4 code was read.

The costs were discussed and accepted: a user-level memory manager to build, and much of the container-based proof to rewrite. The design later sized the migration as roughly 10,000 verified lines kept and adapted (the page table module, base types, arrays, lists, pointers, device, trap and lemmas) and roughly 30,000 replaced, built as new proven modules beside the old kernel, `design/cut-over-on-a-branch/`.

## Alternatives rejected

- **Keep containers and quotas.** Quota is authority the kernel grants ambiently; a container's children can create objects without holding anything that names them.
- **Capabilities beside containers.** Two sources of authority, with the proof having to relate them.

## What this does not settle

- The pager library itself, and its tier, `design/trust-boundary/`.
- What any one retype produces, which `design/capability-names-a-block/` and `design/teardown-driven-by-retype/` settle.
