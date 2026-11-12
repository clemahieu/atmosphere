---
title: "The committer is not the proof's adversary, and rustc, Verus and vstd are trusted tools"
date: 2026-11-11
status: active
tags: [process, gate, verified, skeptic]
one_line: "The proof is defended against user processes, devices, other cores and a specification weaker than its intent. It is not defended against whoever writes the tree: the gate counts every exemption from the proof that is written openly, on purpose or by accident, and claims nothing about one that is disguised; a hole in what Verus trusts is the tool's, kept in a backlog and not defended against in the tree; and a skeptic pass refutes a criterion by a proof hole or by what the running system allows, not by what a committer could add."
revisit_if: "Commits land from someone the human does not direct, such as an outside contributor or a pull request, which makes the committer a party to defend against and needs a check the committer cannot edit; or an exemption that was disguised, not merely unlisted, is found in the tree."
confidence: "A judgement by the human, made on one day's measurement of what the other choice cost. That no check kept in the tree holds against a committer who can edit it is an argument, not a measurement."
---

## Decision

The adversaries of the proof are outside the tree: a user process, a device, another core, and a specification that says less than was meant. The committer is not one of them. Whoever writes the tree, a round, a prover or the human, is taken not to hide what they write, and rustc, Verus and vstd are trusted tools, as `CLAUDE.md` trusts the compiler.

Three things follow.

- **The gate counts what is written openly.** `tools/check-external-body.py` holds every claim a crate marked verified takes without proving it to `tools/external-body-list`, and refuses an exemption written any other way, including the ones that arrive by accident: an attribute nobody listed, an impl or a derive that Verus takes without verifying. That is what the step is for and all that the records claim from it. It is not claimed to catch an exemption its author disguised.
- **A hole in what Verus trusts is Verus's.** When Verus accepts code it did not verify, or accepts what it should refuse, the finding is kept, with a source that shows it, in a backlog of tool hardening; whether and when it goes to the Verus project is the human's call. The tree is not changed to defend against it unless ordinary code could fall into it by accident.
- **The skeptic attacks from outside.** A pass refutes a criterion by a proof hole or by something the running system allows, with throwaways that use the tree's items as they stand. A throwaway that adds an exemption, changes the item it then attacks, or hides something from a check by how it is spelled refutes nothing; `.claude/agents/skeptic.md` says what the pass reports instead.

## Context

A criterion asked that "a throwaway making a token outside `kernel/verified/arch` fails verify or a gate step". It reads as a property of the kernel's ghost tokens. It is a claim about every source file a committer could write, and nothing in it says where that stops.

## Reasoning

The criterion was refuted in nine skeptic passes in a row on 2026-11-11, each by a new way to add an exemption or to hide one from the check: an `axiom fn`, `admit` imported under another name, a block comment that hid the rest of a line, a first line that opened a comment, a macro that pasted a name together, an impl outside `verus!`, a derived `Default`, a raw identifier. None of them was in the tree. Each was answered by the narrowest rule that refused it, and the next pass, with no memory of the last, found the neighbouring form.

What that cost, measured the same day:

- `tools/check-external-body.py` grew from 369 lines to 1,538, by `git show <commit>:tools/check-external-body.py | wc -l` at the first and last commits of the day that touch it.
- The work under that one criterion took 1.27 million output tokens, 4% of the project's output tokens to that day, and its skeptic passes 13% of all output by skeptic passes, from `tools/token-ledger.py`'s ledger summed over the issues filed for it.
- The nine rounds changed no proof. Outside the script they changed comments in `kernel/verified/arch/mod.rs`, one clause of `CLAUDE.md` and one sentence each of three records, which they extended at every round.

The defence could not have held in any case. The check, its tests and the counted list are files in the tree, and a committer who would disguise an exemption can change them in the same commit. A text check also reads the source otherwise than rustc does, so it has to follow the compiler's lexer, its module resolution, its macros and its derives, and about half of the nine forms existed only because it did not.

The other half were real: Verus takes code outside `verus!`, and some derived impls, without verifying them, and verified code can reach that code through a trait. Ordinary code can fall into that, a `derive(Default)` added for convenience, so the check keeps the rules that catch it. That Verus allows it silently is a matter for the Verus project.

The skeptic pass is kept for what a proof cannot catch, a specification weaker than its intent, and for the boundary where unverified glue hands verified code what a user process or the hardware produced. Passes spent on the committer are passes not spent there.

## Alternatives rejected

- **Harden the text check until no pass refutes it.** This is what the nine rounds did. A pass that finds nothing shows that one reviewer found nothing in one session; and the check stays editable by the party it is meant to stop.
- **Enforce the boundary with the compiler: the trusted glue in its own crate, the proven crates under Verus's `--no-cheating` and `#![forbid(unsafe_code)]`.** This removes the forms that exist only because a script is not the compiler, and it may still be the better way to count what is written openly. It was not taken as a defence against the committer, who can change a crate's flags as easily as a script.
- **A check outside the committer's reach**, a list only the human edits or a review of every change to the trusted surface. That is what a real defence would need. It is not wanted while every commit comes from a session the human directs.

## What this does not settle

- Which rules of `tools/check-external-body.py` stay. It holds rules today that only stop a disguised exemption, an allow-list of macros and a ban on raw identifiers among them; nothing rests on those, and a marked crate that needs what one refuses is a reason to remove it.
- Whether Verus's own flags should enumerate the claims inside a marked crate in place of the script.
- What counts the other side of the proof: the ghost values unverified code conjures and the preconditions it is trusted to meet when it calls verified code.
