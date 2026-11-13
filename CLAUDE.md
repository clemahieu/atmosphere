# Atmosphere

A capability-based microkernel for x86_64, written in Rust and proven with Verus, under copy-permissive licenses.

The star: computing security is failing because mainstream kernels are huge and grant ambient authority, and virtualization and tooling only patch symptoms. The fix is a formally verified, capability-based microkernel with a small attack surface, written and proven with maintained tooling (Rust and Verus), under copy-permissive licenses only, with AI-assisted proving as the force multiplier. The base is Atmosphere from mars-research (MIT, Rust plus Verus, L4-like); this project is independent of mars-research. seL4 is not the base: C, GPL, embedded-focused, with a less supported prover. The compiler is trusted through mass usage for now and may be proven later.

The project root holds the bare repository, one worktree per branch, the reference library, the logs and `scratch`. From a worktree it is `dirname "$(git rev-parse --show-toplevel)"`. A temporary file goes under `scratch` there, which is on disk, and not under `/tmp`, which is held in memory: `tools/loop.py` gives each session it runs that directory as `TMPDIR` and as `CLAUDE_CODE_TMPDIR`. The Beads tree is `.beads` there. It is local and is not published; a clone does not have it. Its root epic carries the star. Every issue must be derivable from the star and the principles below; one that cannot be is wrong. Run `bd prime` at session start.

# Principles

## License

Every line in the tree and every dependency is under an OSI-listed copy-permissive license: MIT, BSD, Apache-2.0, ISC, 0BSD, Zlib, BSL-1.0, OLDAP-2.8, BSD-2-Clause-Patent and the like. No copyleft, weak copyleft or closed source: GPL, LGPL, AGPL, MPL, CDDL and EPL are out.

Each source file says which. Its first line, or its second under a `#!` line, is a comment holding `SPDX-License-Identifier:` and the file's license as an SPDX expression: `// SPDX-License-Identifier: MIT` for a Rust file written here. A source file is one ending in `.rs`, `.py`, `.sh`, `.c`, `.h` or `.S`, or starting with `#!`; every other file is under `LICENSE`. A file taken from another source states that source's license and keeps its copyright and notice lines as they came. `design/license-stated-in-every-source-file/`.

The rule covers reading, not only copying. Never open, fetch, grep or summarise such code; it would taint the tree. Before reading any external source for the first time, check its license and record the source and the license on the issue.

Known allowed: this tree; crates.io dependencies with a permissive license field; Verus and vstd (MIT); Rust std (MIT or Apache-2.0); DragonFly HAMMER2 (BSD-3; copy at `reference/hammer2` under the project root, design document at `sys/vfs/hammer2/DESIGN` in it, usable for design only); Redox (MIT); edk2 and OVMF (BSD-2-Clause-Patent); published specifications (copies under `reference` at the project root, beside the worktrees and in no tree, indexed by its `SOURCES.md`).

Known forbidden: Linux; the seL4 kernel and anything derived from it; GRUB; the QEMU, gdb and binutils sources; ZFS; anything Windows. Running a GPL tool (QEMU, gdb, binutils) is allowed; shipping or reading its code is not. A checkout's path goes in the license guard's untracked local list.

## Purity, with virtualization as the escape hatch

The native system follows the capability model without compromise: no ambient authority, no POSIX-shaped compatibility layer in the native API. Backwards compatibility comes from virtualization: the system runs a full guest OS for software that cannot be ported. That is a top-level commitment, not a stopgap, because incompatible software will exist for the foreseeable future. The VMM is an ordinary user process; the kernel exposes the hardware virtualization primitives as capabilities. A design decision is judged by whether it keeps the native system pure and keeps that path plausible.

## Testability, in tiers

- Tier 1: proven correct with Verus specifications. Required for the kernel and the network protocol stack (`design/network-stack-proven-at-tier-1/`); the target for the filesystem stack.
- Tier 2: full line and branch coverage, with fault injection where a branch cannot be reached otherwise. Accepted for the filesystem stack until it reaches tier 1.
- Tier 3: best-effort tests, as extensive as reasonable. Everything else.

A tier-1 proof bounds a component from both sides. From above, the component changes only what its specification allows, as the reach theorem says for the kernel. From below, each operation's specification says exactly when it refuses, and each use the component exists for has a witness: a verified sequence of its operations, built into no image, that reaches the use from any state boot can produce, beside a throwaway variant claiming more that does not verify. A specification that a component refusing everything satisfies says nothing about what it can do. A witness covers the proven model; a boot checks the glue and the hardware against it. A witness lands with what it witnesses: a change that adds an operation, or a way one succeeds, carries the witness that reaches it, and when nothing can reach it yet, the witness becomes a criterion of the open issue that adds what it needs.

Every epic states the tier its acceptance criteria require. Tiers rise as tooling and understanding mature; lowering one is a human decision. Unverified code is allowed only as leaf glue for hardware and assembly, and its claim is written by who vouches for it (`design/who-vouches-for-an-unproven-claim/`). A hardware guarantee is a function outside `verus!` holding only the instruction or register access, or nothing for a standing property no instruction asks for, with an `assume_specification` in an arch module and, directly above it, one line `// cite: <key> <section, figure or table>` per passage it restates, the key one `tools/hardware-documents` lists. A user-side system call is the same form with `// kernel: <path> <item>` naming the kernel item whose proof it restates, and a claim only the language's rules make is the same form with `// rust: <path> "<passage>"` quoting the pinned toolchain's rust-src word for word. Every `external_body` in a crate marked verified is debt, which nothing outside the proof vouches for, with a reason and the class `gap` or `unproven`; `exec_allows_no_decreases_clause`, which exempts a function from the proof that it ends, is debt the same way. `tools/external-body-list` counts all of them and every assumed specification. A new `external_body` or `exec_allows_no_decreases_clause` item, or an assumed specification turned into one, lowers what the proof covers, so it is a decision only the human can make, as lowering a tier is: filed as a question the change waits on, and landed with `tools/land.py --approve` naming the item once the answer is on the question. Removing an item, rewording a reason, moving an item between `gap` and `unproven` and adding a `hardware`, `kernel` or `language` item need no decision. The count is of what is written openly, on purpose or by accident: the committer is not the proof's adversary, and rustc, Verus and vstd are trusted as the compiler is (`design/committer-is-not-the-adversary/`). Development is test-first: an implement round writes the failing test, then the change.

## Portability

Two targets are tested, and the gate boots dom0 on both: x86_64 on AMD, the PC as QEMU q35 gives it under KVM on this host, and aarch64 under QEMU virt, under KVM on the Orange Pi. Code that makes another architecture or vendor implausible is not written. What a target fixes goes through two mechanisms and no others. The arch module holds what the instruction set fixes: one implementation per ISA, chosen by `cfg(target_arch)`, each with the same item names, signatures and specs and no trait (`kernel/verified/arch/`, `kernel/src/arch/`, and the loader's and asys's own); `design/arch-module/`. The machine glue holds what the platform fixes, one crate per machine below the kernel (`machine/pc`, `machine/virt`); `design/machine-glue-below-the-kernel/`. No other portability layer is written. Existing untestable code (Intel VT-d) stays until a tested replacement exists.

## One kernel instance

One kernel instance holds every core, and a process lives inside it; the kernel does not span instances. Several instances are deferred work that nothing depends on, kept cheap to add by four rules. The reasoning is `design/one-kernel-instance/`.

- Kernel state stays inside the `Kernel` value, and `kernel/verified` has no statics.
- A capability, and any name a process passes to the kernel, resolves within the caller's instance. The ABI has no machine-wide names.
- The root process treats what boot gave it as all there is, and does not assume it owns the machine.
- The pager library draws from the pool it was given, not from all memory.

A change that breaks a rule or adds kernel spanning is a decision only the human can make: file it as a question, with what it costs the multi-instance path, the alternative that keeps the rule, and why the change is wanted.

## Rounds, commits and the stack

Work happens in rounds. `/round` runs one; `tools/loop.py` (auto-routing across harnesses and model difficulties from `[routes]` in `loop.toml`, or running a single slice with `--profile <name>`; `design/loops-select-by-work-kind-and-stage/`), or `/loop /round` in a session, runs them until everything open is blocked on the human. Several loops run at once, one per terminal, each its own actor (`loop-<pid>` for `tools/loop.py` and every session it runs, `claude-<pid>` from a hook at session start otherwise); a round recovers an issue held by its own actor or by a loop that ended, leaves another live loop's alone, claims atomically, and lands without a lock. The procedure is `.claude/agents/round.md`, which `/round` runs in a fresh subagent. The rules:

- A round takes the next ready issue and discards it (close with the reason), redefines it (rewrite the outcome and the acceptance criteria), splits it (one issue per independent change, dependencies only where one blocks another) or implements it (one discrete change, one tested commit, merge to main, push, remove the worktree, close). A round that redefines goes on to implement the issue it rewrote, and a round that splits goes on to implement the first piece, while the context that understood them is at hand; a round lands one implementation at most. Only implement commits.
- A round writes the tool its work needs, when a check is slow, an output is hard to read or a step is repeated by hand: under `tools/`, tested at tier 3, as its own commit ahead of the change that uses it. A tool does not change what the gate requires.
- Work is a stack. An issue discovered mid-round is pushed as a new issue that blocks the current one and resolved in isolation with its own tested commit; then pop back and re-read the blocked issue's directive before resuming, because the premise may have changed. A bug's commit includes the test that exercises it.
- When `bd ready` has no leaf, an epic round runs. Closing an epic whose every child is closed comes first, whatever its priority, since closing it releases the leaves that depend on it, and a finished epic that lacks the review it needs gets one; only when no epic is finished does a split round run, on an epic that has no children yet and that nothing blocks. Among the epics eligible for the same kind of round, the highest priority goes first, the deepest among equals. That finishes the work nearest done first and keeps the tree self-extending toward the star.
- A leaf closes on the gate. A small epic, at depth 2 or deeper with three children or fewer and without the label `skeptic`, closes on its children's evidence: the round matches each acceptance criterion to the SHAs, logs and verify output its children recorded, and a criterion nothing shows becomes an issue. Any other epic closes only on a review: a leaf under the epic, labelled `review`, that waits on the epic's other children and is one skeptic pass, in which a reviewer spawned with no prior context tries to refute each of the epic's acceptance criteria from recorded evidence (logs, commit SHAs, verify output). A round claims the review like any leaf and first matches each criterion to the evidence recorded under the epic, with `tools/review-evidence.py` for what is missing, gone from main or older than it: a criterion nothing shows becomes an issue the review waits on, with no pass and no refutation counted. Otherwise the driver runs the pass, and the round that claims it next closes it on the report. A refuted criterion becomes an issue under the epic, and a repeat review waits on those issues; its pass re-judges what the last pass refuted, what was reworded since and what main has changed under its evidence since the commit it judged, and every other criterion stands on that report. Refuted reviews are counted per epic: the second is reported to the human with the kind of refutation it is, and nothing waits on that; from the third, the issues it files wait on a question to the human, and so does an issue filed for a refutation when it would split into more than three pieces. `design/third-refuted-review-waits-on-the-human/`. The epic closes when its newest review passed after every other issue below it closed, which `tools/reviews.py` decides; an epic is never claimed for a pass. `design/review-is-a-leaf-of-its-epic/`. The skeptic is kept for what a proof cannot catch, a specification weaker than the epic's intent, which verifies cleanly; the label `skeptic` marks a small epic whose criteria state such an intent.
- A decision only the human can make is its own issue, status blocked, filed before the round ends. One question, the options, and what each implies. Its parent is the epic the question is about. When the current issue must wait, it depends on that issue and stays open. When work can continue either way, the question is filed and nothing depends on it. An answer is a note on the question, then status open when a later round must carry it out, or closed when the answer is the whole outcome. The questions are `bd list -s blocked`. The loop stops only when nothing is ready and every remaining open issue is an epic, a question on that list, or blocked only by such a question; then it prints the questions. A loop that finds nothing ready while another loop holds an issue in progress waits instead. There is no other stop; the human monitors budget.

## Git

Single-person local repository. `origin` is `clemahieu/atmosphere`; no pull requests, and no review gate besides the skeptic pass. The project root holds the bare repository in `.bare` and one worktree per branch beside it; `main` is the worktree `main`. Each task is a worktree sibling named for its branch, off `main`. An implement round merges its branch into `main`, pushes `main` to `origin`, and removes the worktree. It gates the branch on the main it rebased onto and lands on the main of that moment by a fast-forward, with no lock and no second gate when the rebase is clean, so main's tip may be a composition no gate has run on until the next change is gated on top of it. `tools/land.py` does this and, when a gate fails, tells a failing change from a main that fails by itself; `design/land-without-regating/`. One logical change per commit; the message says why. Superseded code is deleted in the same change. Living files describe today, not history.

Beads lives at `.beads` in the project root, shared by every worktree, kept out of the tree by `.bare/info/exclude`, local only: no Dolt remote, no auto-push, no backup. It is not published.

## Gate

A commit is tested when the gate, `tools/gate.py`, exits 0, or when it changes only what no gate step reads (`.claude/agents/`, `.claude/skills/`, `CLAUDE.md`, the list in `tools/land.py`) and leaves no source file there, which lands without a gate; `design/no-gate-for-what-no-step-reads/`.

What the gate holds is its steps, the `STEPS` of `tools/gate.py`: each step's function, and the opening comment of the check it runs, says what must be true. No step holds the next three, so the committer does. Among the workspace's host tests, in `boot-host-tests`, which compiles the kernel's boot checks on the host, the loader memory-map check rejects an unaligned page, a repeated page and an out-of-range page (lines starting `free page ranges:`), the dom0 run check accepts a real dom0 load shape and rejects an unaligned run, an empty run, a run outside the reservation, a run in the kernel's entries, and a physically and a virtually overlapping pair (lines starting `mapped runs:`). The verify steps accept no more errors than `tools/verify-allowance`, which equals the count on the proof-debt epic, and a proof leaf lowers both in the same commit. The aarch64 boot is on the Orange Pi; when ssh cannot reach the board, the step passes on the runner's line `skip: orangepi5 unreachable`, which the round procedure records on one blocked question.

An implement round's gate output is `logs/<id>-gate.log` at the project root, beside the worktrees and outside every tree.

# Design decisions

`design/` holds the decisions made under these principles, one per directory, entered at `design/INDEX.md`; `design/README.md` says how a record is written and revised. A comment that explains a design choice points at `design/<slug>/`, never at a tracker issue, since the tracker is private. Before changing how something is done, read its record; a change that reverses a decision revises its record in the same commit, and a decision someone arriving fresh would re-propose gets a record.

# Working in the tree

Each tool's opening comment is its manual: what it does, its options and its exit statuses. A line here says only when to reach for it.

```
source tools/env.sh     # Verus and RUSTC_BOOTSTRAP
tools/gate.py           # the gate; --target and --step run part of it
cargo test --workspace  # every member's host tests, from the root, after a build
tools/run.py            # build the images and boot them under QEMU; --iommu, --no-kvm, --gdb, --kernel-feature FEATURE
tools/verify.py         # Verus over kernel/verified; extra arguments go to rust_verify
tools/build.py          # the gate's build; --target aarch64 builds that target's images
tools/land.py           # from a task worktree: rebase onto main, gate, land by fast-forward and push
tools/gdb.py            # attach gdb to a tools/run.py --gdb run
tools/check-upstream-copies.py --update   # rewrite the recorded delta of a copied upstream file
tools/check-boot-log.py --arch ARCH LOG   # hold a dom0 boot's serial log to the gate's boot checks
tools/check-throwaways.py --write   # after adding a root witness or changing one's parameters or requires: rewrite the throwaways the gate runs; --list says which witnesses are roots
tools/aarch64-esp.py    # build the aarch64 images and lay out the ESP the board boots
tools/board.py          # boot dom0 on the Orange Pi under KVM and hold the run to the gate's boot checks; fails when the board is unreachable
```

Not part of the gate:

```
tools/loop.py           # run rounds until the loop stops; loop.toml [routes] auto-selects harness and model per work kind and stage (--profile runs one slice; --check shows matching ready work)
tools/reviews.py        # the finished epics, in the order an epic round takes them, each with what it needs
tools/review-evidence.py EPIC      # before a review goes to the skeptic: the commits and logs recorded under its epic that are missing, gone from main or older than it
tools/bead-status.py    # serve the state of the Beads tree as a page at http://127.0.0.1:8377/
tools/token-ledger.py   # harvest the transcripts' token counts and the plan's meter reading into logs/token-ledger.sqlite at the project root
tools/leaf-cost.py      # what a landed leaf cost, every session counted, by the model of its rounds, with the rework beside it
tools/witness-inventory.py         # before writing a witness or adding an operation: every way each tier-1 operation succeeds, with the witness that reaches it or none
tools/check-stray-timer.py         # a kernel whose timer fires for nothing reports it once and stops, on both targets
tools/check-boot-panic.py          # a kernel that panics at boot ends QEMU with status 1, on both targets
tools/orangepi-stack-overflow.py   # an aarch64 kernel that overflows a stack on the board reports it once
```

`tools/setup-verus.sh` builds Verus under `verus` at the project root, beside the worktrees and in no tree, at the commit the workspace `Cargo.toml` pins as vstd's revision; every worktree's tools read that one build, so a new worktree needs no setup. The host is an AMD Ryzen 9 9950X3D; `/dev/kvm` is world-writable; edk2-ovmf is at `/usr/share/edk2/ovmf`.
