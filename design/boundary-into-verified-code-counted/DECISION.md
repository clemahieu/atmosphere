---
title: "The boundary into verified code is counted from rustc's resolved calls: every value unverified code conjures for it and every requires it is trusted to meet, each with who vouches for it"
date: 2026-11-15
status: active
tags: [verified, proof, trusted-base, gate]
one_line: "An unverified crate that depends on a crate marked verified (kernel, dom0, astd) meets the proof at sites: a ghost or tracked value it conjures, a raw pointer it makes to a verified type, and a call to a verified function whose specification has a requires. A gate check finds them in rustc's THIR, which resolves every call to its definition, on both targets, and holds them equal to a list naming each by path, enclosing function, callee and occurrence, with one guarantor: hardware, machine, kernel, language, boot, check, or nothing, which is debt."
revisit_if: "rustc drops or reshapes -Zunpretty=thir-flat so that a call's resolved callee or its span can no longer be read from it, or Verus comes to verify a crate's calls into another crate's requires itself, which would make the call half of the list a proof instead of a count."
confidence: "The enumeration was tried on main d59ac881: rustc's THIR found every Tracked::assume_new the source holds, and in kernel/src 34 calls into kernel/verified where a textual index of kernel/verified's function names matched 158 lines. Which guarantors there are is a judgement built on design/who-vouches-for-an-unproven-claim/."
---

# The boundary into verified code is counted

## Decision

`tools/external-body-list` counts what a crate marked verified takes on trust inside itself. This record is the other side: where code Verus does not verify hands the proof something it cannot check.

**The crates.** A boundary crate is a workspace member that is not marked verified and depends on one that is: today `kernel` (on `kernel/verified`), `dom0` (on `acall`, `aeager` and `aheap`) and `astd` (on the same three, under its `heap` feature).

**A site.** In a boundary crate, each of these is one site:

- **conjure**: a ghost or tracked value made from nothing, `Tracked::assume_new`, `Ghost::assume_new` or any other `assume_new`, passed to verified code. It claims whatever the receiving function's requires and ensures read of it.
- **raw**: a raw pointer to a type a marked crate defines, made from an address or a cast, such as the `CapKernel` that `kernel/src/capability.rs` places on zeroed pages. Whatever it points at is taken to be a well-formed value of that type.
- **call**: a call to an exec function of a marked crate whose specification has a `requires`, on the function itself or on the `assume_specification` that states it. Verus proves the requires at each verified call; at this one nothing does.

A call whose callee has no requires is no site unless a conjured value is passed to it, which is a site of its own.

**How the check finds them.** It reads rustc's typed intermediate form, `cargo rustc -- -Zunpretty=thir-flat` for each boundary crate, which `RUSTC_BOOTSTRAP` allows. Every call there names its callee's definition, crate and module path included, and its span: a method call such as `kernel.enter(core, frame, Tracked::assume_new())` reads as a call of `verified::capability::operation::{impl#1}::enter` at `kernel/src/capability.rs:53`. A conjure site is a call of `verus_builtin`'s `assume_new`, and a raw site an expression whose type is a raw pointer to a marked crate's type. Whether a callee has a requires is read from its definition in the marked crate's source, at the module path the THIR names. The check runs both targets, x86_64 and aarch64, since each compiles its own arch module, and holds the union.

**The list.** One line per site, fields separated by tabs: path from the repository root; the enclosing function as rustc names it, without the crate hash; the kind; the callee, by its module path and name without the impl index, and for a conjure site the argument it fills; the occurrence among sites alike in that function, from 1; the guarantor's class; and its text. Lines are named this way, not by line number, so moving code does not churn the list. The check fails when the source holds a site the list does not, when the list holds one the source does not, or when a guarantor's text fails its class's rule.

**The guarantors.** Each site names one:

- **hardware** `<key> <section>`: what the site owes is the hardware's doing, cited as an assumed specification's `// cite:` line is, the key one `tools/hardware-documents` lists.
- **machine** `<key> <section>`: what it owes is a fact of the machine that a published firmware or platform specification states, such as that the memory UEFI's map reports as conventional memory is RAM nobody else holds (UEFI 2.11 section 7.2.1). The key is listed in the same file. It is its own class because `design/who-vouches-for-an-unproven-claim/` keeps a machine fact from ever being cited as a hardware guarantee: it holds only for the machine whose firmware says it.
- **kernel** `<path> <item>`: what it owes is what the kernel's proof gives a process, as dom0's caller token is the entry value of `design/region-map-owns-the-address-space/`. The path names a file that declares the item.
- **language** `<path under rust-src> "<passage>"`: what it owes is the caller's side of a contract the language's documentation states, such as `GlobalAlloc::dealloc`'s, which `astd/src/heap.rs`'s free permission rests on. The passage is matched word for word at the pinned toolchain, as `tools/check-external-body.py` matches one.
- **boot** `<witness>`: what it owes is a verified witness's requires, a `witness_*` function the check finds, whose requires state what the boot code that holds the site meets. The witness shows that the values the site conjures are consistent; the boot code meeting them is what a boot of the gate shows.
- **check** `"<condition>"`: a run-time check in the enclosing function before the site, an `assert!` or a branch that refuses, whose condition's text the check finds there. This is the guarantor `design/committer-is-not-the-adversary/`'s committer can most cheaply add, and what most calls should end with.
- **nothing** `"<what it rests on>"`: debt. No document, proof or check vouches for it. The text says what the site rests on, in words, since the tree does not name the private tracker; the count of these is kept on the tracker's boundary epic, and a change that adds one files an issue saying why.

A site with more than one guarantor names the one that carries most; the list is a count of who vouches, not a proof.

**The skeptic.** The list counts the boundary, so a skeptic pass reports no uncounted site; `.claude/agents/skeptic.md` points it at the list. A site the list holds with a guarantor that does not hold on a path the running system takes refutes a criterion, as any false claim does.

## Context

The gate held every exemption inside a marked crate to a list, and nothing at all of the code that calls in. The unverified kernel conjures every core's base register, the TLB and IOTLB models and every boot page's permission, and calls `CapKernel::enter` trusting that it meets `wf()` and `c < NUM_CPUS`; dom0 conjures its caller token and calls acall's wrappers trusting their requires. A skeptic pass found these one by one and reported them as notes, more than a hundred of them, the same sites found again by each pass. Counting them is the human's direction: each assumption gets its own issue, and the count says how much of the proof's floor is on nobody's word.

## Reasoning

The trial, on main d59ac881, x86_64:

| crate | conjure sites | calls into marked crates | of which with a requires |
|---|---|---|---|
| kernel | 17, on 16 lines | 34 | 26 |
| dom0 | 1 | 120 | 118 |
| astd | 1 | 4 | 2 |

The resolved calls name their callee exactly. The alternative, an index of the 333 public exec function names in `kernel/verified` matched against the boundary crate's text, matched 158 lines of `kernel/src` outside its aarch64 module (180 with it) against those 34 calls: the names `new`, `get`, `set` and `lock` belong to many types, and the text cannot tell `kernel.enter` from any other `enter`. A list built on it would be mostly lines that are not sites, each needing a guarantor someone writes by hand.

Each crate's dump took about 12 seconds, its dependencies built included. The check builds into its own target directory, so its flags never touch the gate's build.

Why the requires is read from the source rather than from Verus: Verus does not compile the boundary crates, and the marked crates' sources are already read by `tools/check-external-body.py`, which knows where a function's `requires` starts and ends.

Why name a site by its function and occurrence: line numbers move with every edit above them, while a function's name and the order of its calls change only when the site itself is touched. `tools/external-body-list` is keyed the same way, by path and item.

## Alternatives rejected

- **Verus's `--no-cheating` and `--no-external-by-default` on the boundary crates.** A prototype in a spike ran the marked crates this way to enumerate what Verus refuses inside them; nobody checked it, and it says nothing of calls from a crate Verus does not compile. Making Verus compile `kernel/src` would make it a verified crate, which is that crate's own work.
- **The textual index**, above.
- **Every guarantor `nothing` until it is proven.** The count would not tell the sites a manual or a run-time check vouches for from those nobody does, and it is the second kind the count exists to show shrinking.
- **The tracker issue on each `nothing` line.** The tree is published and the tracker is not; the line says what the site rests on and the issue names the site.

## What this does not settle

- Which sites can be removed, checked or witnessed, and in what order: each is its own issue.
- The `global layout` and `global size_of` claims inside the marked crates, which Verus takes as stated: whether the build refuses a wrong one, or they join `tools/external-body-list`.
- Which sites a user process or a device can reach, and the boot tests that try to break them.
