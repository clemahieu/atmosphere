---
title: "An unproven claim in a verified crate is written by who vouches for it: a hardware guarantee is an assumed specification citing its manual, a system call's is one naming the kernel's proof, and external_body is debt"
date: 2026-11-11
status: active
tags: [verified, proof, arch, trusted-base]
one_line: "A hardware guarantee is a plain Rust function outside verus!, marked external, holding only the instruction or register access, with an assume_specification beside it in the arch module that cites the manual section it restates; a user-side system call is the same form naming the kernel-side item whose proof vouches for it; every external_body left in a verified crate is debt that nothing outside the proof vouches for."
revisit_if: "Verus drops or changes assume_specification so that it no longer binds a spec to an external function with tracked arguments, or a hardware guarantee needs a body that is more than one instruction sequence and a wait on the device, which is when the line between the leaf and the verified code above it has to be drawn again."
confidence: "The mechanism was tried on flush_every_context on both targets: it verifies with the same counts as external_body, and dropping one conjunct of the assumed specification fails Kernel::acknowledge, so callers rest on it. That a citation is the right warrant for a hardware claim is judgement."
---

# Who vouches for an unproven claim

## Decision

Verus proves what a verified crate does above a floor of claims it cannot check. Each such claim is written by who vouches for it, and the source shows which.

- **A hardware guarantee.** A manual vouches for it. It is a function outside `verus!`, which Verus treats as external with no attribute, whose body holds only the instruction or the register access the manual describes: no branch, no arithmetic beyond forming the operand, and no loop but a wait on the device itself. Its specification is a separate `assume_specification` item inside `verus!`, about the model token the instruction changes (the TLB model, the IOTLB model, a `BaseRegister`), and says what the cited text says and no more. Both sit in the arch module, `design/arch-module/`, one per ISA under the same name: the specification where the item would stand in the file, the bodies after the file's `verus!` block. The lines directly above the specification cite the text, one line each: `// cite: <key> <section, figure or table>`. A guarantee that rests on several passages cites each. The keys are listed in `tools/hardware-documents`, one line per document with its title, publisher, number and revision.
- **A claim the kernel vouches for.** A user-side system call is the one place user code cannot prove, and its effect is what the kernel proves of the system call. It is written the same way, an external function and an assumed specification, in the user crate, and the line above the specification names the kernel-side item whose proof it restates: `// kernel: <path from the repository root> <item>`, for example the step that restates `Kernel::dispatch`. Every wrapper over that step is verified and rests on the kernel's per-operation lemmas, so a crate holds one such claim, not one per operation.
- **Debt.** Every `external_body` left in a verified crate. Nothing outside the proof vouches for it, and `tools/external-body-list` classes it `gap` or `unproven`.

`tools/check-external-body.py` counts all three, requires each assumed specification to carry a citation naming a listed document or a kernel item that exists, and refuses a hardware guarantee outside an arch module.

## Context

Every exempted function was spelled `external_body`, whether a manual vouched for what it claimed or nothing did, and only a class in the list told them apart. Some cited a manual in a comment, some cited nothing, and several held loops, ring arithmetic and command encoding inside the exempted body, which no manual vouches for. A reader could not tell from the source which exemptions were the floor the project accepts and which were proof not yet written.

## Reasoning

`assume_specification` separates the claim from the code. The body is ordinary Rust that Verus never reads, so inline assembly and register access need no Verus-acceptable form, and the specification is an item of its own that a check can find, count and hold to a citation. Verus requires the specification's signature to match the function's exactly, `Tracked<&mut TlbModel>` included, so the two cannot drift apart in shape. With every hardware claim in this form, the word `external_body` in a verified crate means debt and nothing else.

The spike, on flush_every_context: on x86_64 `tools/verify.py` reports `1674 verified, 0 errors` for the kernel's verified crate and on aarch64 `1637 verified, 0 errors`, the same as with `external_body`. Removing `final(model)[core as int] == Set::<TlbEntry>::empty()` from the x86_64 specification gives `1673 verified, 1 errors` at `Kernel::acknowledge`, which is how the claim is seen to bind. The attribute on the body has to be `cfg_attr(verus_keep_ghost, ...)`: a plain `#[verifier::external]` outside `verus!` does not build under cargo.

The body is held narrow because a citation vouches for what the hardware does when asked, not for the code that asks. Loops, ring arithmetic and command encoding above the leaf are verified code that calls it.

## Alternatives rejected

- **A macro in the crate that expands to `external_body`, with a marker line a tool reads.** It keeps the specification and the body as one item, but the item is still `external_body` to Verus and to anything reading the expansion, the body must still be written in a form `verus!` accepts, and the distinction lives only in the spelling a tool knows. Not tried, since the first candidate works.
- **`external_body` with a citation in its reason line.** The source would still spell a hardware claim and an unproven lemma the same way, which is what this decision exists to end.
- **One assumed specification per user-side system call wrapper.** Each would restate a kernel lemma unchecked; a wrong restatement would be assumed rather than fail its wrapper's proof.

## What a citation does not vouch for

- The code that asks the hardware: hence the narrow body and everything above it verified.
- The model matching the hardware: that the TLB, IOTLB and base-register models describe what the silicon holds is the stated assumption of `design/flush-without-waiting/` and `design/arch-module/`, not something a manual section proves.
- Which device sits at a port or an address. That is a machine fact: firmware's description or the platform's convention says it, no chip manual does, and it belongs to the machine glue, `design/machine-glue-below-the-kernel/`. A hardware guarantee's specification says nothing that depends on which device is at the address it is given, and a machine fact is never cited as a hardware guarantee.
- The compiler and assembler emitting the instructions as written, which the project trusts through mass usage.
- That a wait on the device ends. An assumed specification is taken to return; the citation must name the device state that ends the wait.

A kernel-vouched claim likewise does not vouch for the trap path and the register convention carrying the call to the kernel's dispatch; the boot checks hold those.

## What this does not settle

Which document keys the list holds and their revisions are the check's to state, as is how `tools/external-body-list` shows the three kinds. The hardware items still spelled `external_body` are glue in the list until each is converted to this form.
