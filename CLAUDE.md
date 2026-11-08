# Atmosphere

A capability-based microkernel for x86_64, written in Rust and proven with Verus, under copy-permissive licenses.

The star: computing security is failing because mainstream kernels are huge and grant ambient authority, and virtualization and tooling only patch symptoms. The fix is a formally verified, capability-based microkernel with a small attack surface, written and proven with maintained tooling (Rust and Verus), under copy-permissive licenses only, with AI-assisted proving as the force multiplier. The base is Atmosphere from mars-research (MIT, Rust plus Verus, L4-like); this project is independent of mars-research. seL4 is not the base: C, GPL, embedded-focused, with a less supported prover. The compiler is trusted through mass usage for now and may be proven later.

The Beads tree at `~/atmosphere.src/.beads` is the plan. Its root epic carries the star. Every issue must be derivable from the star and the principles below; one that cannot be is wrong. Run `bd prime` at session start.

# Principles

## License

Every line in the tree and every dependency is under an OSI-listed copy-permissive license: MIT, BSD, Apache-2.0, ISC, 0BSD, Zlib, BSL-1.0, OLDAP-2.8, BSD-2-Clause-Patent and the like. No copyleft, weak copyleft or closed source: GPL, LGPL, AGPL, MPL, CDDL and EPL are out.

The rule covers reading, not only copying. Never open, fetch, grep or summarise such code; it would taint the tree. Before reading any external source for the first time, check its license and record the source and the license on the issue.

Known allowed: this tree; crates.io dependencies with a permissive license field; Verus and vstd (MIT); Rust std (MIT or Apache-2.0); DragonFly HAMMER2 (BSD-3; copy at `~/atmosphere.src/reference/hammer2`, design document at `sys/vfs/hammer2/DESIGN` in it, usable for design only); Redox (MIT); edk2 and OVMF (BSD-2-Clause-Patent); published specifications (copies under `~/atmosphere.src/reference`, beside the worktrees and in no tree, indexed by its `SOURCES.md`).

Known forbidden: Linux; the seL4 kernel at `~/sel4/sel4.src`; GRUB; the QEMU, gdb and binutils sources; ZFS; anything Windows. Running a GPL tool (QEMU, gdb, binutils) is allowed; shipping or reading its code is not.

## Purity, with virtualization as the escape hatch

The native system follows the capability model without compromise: no ambient authority, no POSIX-shaped compatibility layer in the native API. Backwards compatibility comes from virtualization: the system runs a full guest OS for software that cannot be ported. That is a top-level commitment, not a stopgap, because incompatible software will exist for the foreseeable future. The VMM is an ordinary user process; the kernel exposes the hardware virtualization primitives as capabilities. A design decision is judged by whether it keeps the native system pure and keeps that path plausible.

## Testability, in tiers

- Tier 1: proven correct with Verus specifications. Required for the kernel; the target for the filesystem and network stacks.
- Tier 2: full line and branch coverage, with fault injection where a branch cannot be reached otherwise. Accepted for the filesystem and network stacks until they reach tier 1.
- Tier 3: best-effort tests, as extensive as reasonable. Everything else.

Every epic states the tier its acceptance criteria require. Tiers rise as tooling and understanding mature; lowering one is a human decision. Unverified code is allowed only as `external_body` leaf glue for hardware and assembly: counted, with a reason per item, and the count does not grow without an issue saying why. `tools/external-body-list` is that count; items it classes `gap` or `unproven` are debt, not glue. Development is test-first: an implement round writes the failing test, then the change.

## Portability

x86_64 on AMD is the only tested target. Code that makes another architecture or vendor implausible is not written; portability layers are not written either. Existing untestable code (Intel VT-d) stays until a tested replacement exists.

## One kernel instance

One kernel instance holds every core, and a process lives inside it; the kernel does not span instances. Several instances are deferred work that nothing depends on, kept cheap to add by four rules. The reasoning is `design/one-kernel-instance/`.

- Kernel state stays inside the `Kernel` value, and `kernel/verified` has no statics.
- A capability, and any name a process passes to the kernel, resolves within the caller's instance. The ABI has no machine-wide names.
- The root process treats what boot gave it as all there is, and does not assume it owns the machine.
- The pager library draws from the pool it was given, not from all memory.

A change that breaks a rule or adds kernel spanning is a decision only the human can make: file it as a question, with what it costs the multi-instance path, the alternative that keeps the rule, and why the change is wanted.

## Rounds, commits and the stack

Work happens in rounds. `/round` runs one; `/loop /round` runs them until everything open is blocked on the human. Several loops run at once, one per terminal, each started with its own `BEADS_ACTOR`; a round recovers only its own actor's abandoned issue and leaves another actor's live one alone, claims atomically, and lands under one lock. The procedure is `.claude/agents/round.md`, which `/round` runs in a fresh subagent. The rules:

- A round takes the next ready issue and does exactly one of: discard (close with the reason), redefine (rewrite the outcome and the acceptance criteria), split (one issue per independent change, dependencies only where one blocks another), implement (one discrete change, one tested commit, merge to main, push, remove the worktree, close). Only implement commits.
- Work is a stack. An issue discovered mid-round is pushed as a new issue that blocks the current one and resolved in isolation with its own tested commit; then pop back and re-read the blocked issue's directive before resuming, because the premise may have changed. A bug's commit includes the test that exercises it.
- When `bd ready` has no leaf, the shallowest open epic with no ready children and none in progress gets a split round. That keeps the tree self-extending toward the star.
- A leaf closes on the gate. An epic closes only after a skeptic pass: a reviewer spawned with no prior context tries to refute each acceptance criterion from recorded evidence (logs, commit SHAs, verify output). A refuted criterion keeps the epic open and becomes an issue.
- A decision only the human can make is its own issue, status blocked, filed before the round ends. One question, the options, and what each implies. Its parent is the epic the question is about. When the current issue must wait, it depends on that issue and stays open. When work can continue either way, the question is filed and nothing depends on it. An answer is a note on the question, then status open when a later round must carry it out, or closed when the answer is the whole outcome. The questions are `bd list -s blocked`. The loop stops only when nothing is ready and every remaining open issue is an epic, a question on that list, or blocked only by such a question; then it prints the questions. A loop that finds nothing ready while another loop holds an issue in progress waits instead. There is no other stop; the human monitors budget.

## Git

Single-person local repository. `origin` is `clemahieu/atmosphere`; no pull requests, and no review gate besides the skeptic pass. `~/atmosphere.src` holds the bare repository in `.bare` and one worktree per branch beside it; `main` is `~/atmosphere.src/main`. Each task is a worktree sibling named for its branch, off `main`. An implement round merges its branch into `main`, pushes `main` to `origin`, and removes the worktree. One logical change per commit; the message says why. Superseded code is deleted in the same change. Living files describe today, not history.

Beads lives at `~/atmosphere.src/.beads`, shared by every worktree, kept out of the tree by `.bare/info/exclude`, local only: no Dolt remote, no auto-push, no backup.

## Gate

A commit is tested when `atmo test` exits 0. It holds when no file `git add -A` would take is over 1 MiB; the workspace builds (`cargo build` in every workspace member's own directory, then the loader, kernel, dom0 and payload as `atmo run` builds them); every package in `Cargo.lock` passes the license check against `tools/license-allowlist`; the license guard's tests pass; `atmo verify` reports no more errors than `tools/verify-allowance`, which equals the count on the proof-debt epic, and a proof leaf lowers both in the same commit; every `external_body` in `kernel/verified` has a reason and matches `tools/external-body-list`; `tools/check-boot-stack.py` passes in debug and release, with and without a forced overflow; `tools/coverage.py` captures line and branch coverage per crate, whose numbers are reported and do not fail the gate; `tools/build-design-index.py --check` finds `design/INDEX.md` current; on the cut-over branch, `atmo run --capability` boots the capability kernel's syscall entry and its dom0 to exit status 0, with the first operation refused in the serial log; `atmo run --iommu` boots dom0 under QEMU's emulated IOMMU with the device syscalls returning 0; and `atmo run` boots dom0 to a clean exit within a timeout (exit status 0, serial log ending in `dom0 benchmark done`). An implement round's gate output is `~/atmosphere.src/logs/<id>-gate.log`, beside the worktrees and outside every tree.

# Design decisions

`design/` holds the decisions made under these principles, one per directory, entered at `design/INDEX.md`; `design/README.md` says how a record is written and revised. A comment that explains a design choice points at `design/<slug>/`, never at a tracker issue, since the tracker is private. Before changing how something is done, read its record; a change that reverses a decision revises its record in the same commit, and a decision someone arriving fresh would re-propose gets a record.

# Working in the tree

```
source tools/env.sh     # Verus, RUSTC_BOOTSTRAP and tools/bin on PATH
atmo test               # the gate
atmo run                # build loader, kernel, dom0 and payload; boot under QEMU, with KVM when /dev/kvm is writable; --no-kvm forces TCG
atmo verify             # Verus over kernel/verified
atmo gdb                # attach to a run started with --gdb
```

`tools/setup-verus.sh` builds Verus under `tools/verus`, which git ignores. The host is an AMD Ryzen 9 9950X3D; `/dev/kvm` is world-writable; edk2-ovmf is at `/usr/share/edk2/ovmf`.
