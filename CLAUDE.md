# Atmosphere

A capability-based microkernel for x86_64, written in Rust and proven with Verus, under copy-permissive licenses.

The star: computing security is failing because mainstream kernels are huge and grant ambient authority, and virtualization and tooling only patch symptoms. The fix is a formally verified, capability-based microkernel with a small attack surface, written and proven with maintained tooling (Rust and Verus), under copy-permissive licenses only, with AI-assisted proving as the force multiplier. The base is Atmosphere from mars-research (MIT, Rust plus Verus, L4-like); this project is independent of mars-research. seL4 is not the base: C, GPL, embedded-focused, with a less supported prover. The compiler is trusted through mass usage for now and may be proven later.

The project root holds the bare repository, one worktree per branch, the reference library and the logs. From a worktree it is `dirname "$(git rev-parse --show-toplevel)"`. The Beads tree is `.beads` there. It is local and is not published; a clone does not have it. Its root epic carries the star. Every issue must be derivable from the star and the principles below; one that cannot be is wrong. Run `bd prime` at session start.

# Principles

## License

Every line in the tree and every dependency is under an OSI-listed copy-permissive license: MIT, BSD, Apache-2.0, ISC, 0BSD, Zlib, BSL-1.0, OLDAP-2.8, BSD-2-Clause-Patent and the like. No copyleft, weak copyleft or closed source: GPL, LGPL, AGPL, MPL, CDDL and EPL are out.

The rule covers reading, not only copying. Never open, fetch, grep or summarise such code; it would taint the tree. Before reading any external source for the first time, check its license and record the source and the license on the issue.

Known allowed: this tree; crates.io dependencies with a permissive license field; Verus and vstd (MIT); Rust std (MIT or Apache-2.0); DragonFly HAMMER2 (BSD-3; copy at `reference/hammer2` under the project root, design document at `sys/vfs/hammer2/DESIGN` in it, usable for design only); Redox (MIT); edk2 and OVMF (BSD-2-Clause-Patent); published specifications (copies under `reference` at the project root, beside the worktrees and in no tree, indexed by its `SOURCES.md`).

Known forbidden: Linux; the seL4 kernel and anything derived from it; GRUB; the QEMU, gdb and binutils sources; ZFS; anything Windows. Running a GPL tool (QEMU, gdb, binutils) is allowed; shipping or reading its code is not. A checkout's path goes in the license guard's untracked local list.

## Purity, with virtualization as the escape hatch

The native system follows the capability model without compromise: no ambient authority, no POSIX-shaped compatibility layer in the native API. Backwards compatibility comes from virtualization: the system runs a full guest OS for software that cannot be ported. That is a top-level commitment, not a stopgap, because incompatible software will exist for the foreseeable future. The VMM is an ordinary user process; the kernel exposes the hardware virtualization primitives as capabilities. A design decision is judged by whether it keeps the native system pure and keeps that path plausible.

## Testability, in tiers

- Tier 1: proven correct with Verus specifications. Required for the kernel; the target for the filesystem and network stacks.
- Tier 2: full line and branch coverage, with fault injection where a branch cannot be reached otherwise. Accepted for the filesystem and network stacks until they reach tier 1.
- Tier 3: best-effort tests, as extensive as reasonable. Everything else.

A tier-1 proof bounds a component from both sides. From above, the component changes only what its specification allows, as the reach theorem says for the kernel. From below, each operation's specification says exactly when it refuses, and each use the component exists for has a witness: a verified sequence of its operations, built into no image, that reaches the use from any state boot can produce, beside a throwaway variant claiming more that does not verify. A specification that a component refusing everything satisfies says nothing about what it can do. A witness covers the proven model; a boot checks the glue and the hardware against it.

Every epic states the tier its acceptance criteria require. Tiers rise as tooling and understanding mature; lowering one is a human decision. Unverified code is allowed only as `external_body` leaf glue for hardware and assembly: counted, with a reason per item, and the count does not grow without an issue saying why. `exec_allows_no_decreases_clause`, which exempts a function from the proof that it ends, is counted the same way. `tools/external-body-list` is that count of both; items it classes `gap` or `unproven` are debt, not glue. Development is test-first: an implement round writes the failing test, then the change.

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

Work happens in rounds. `/round` runs one; `/loop /round` runs them until everything open is blocked on the human. Several loops run at once, one per terminal, each session its own actor (`claude-<pid>` from a hook at session start); a round recovers an issue held by its own session or by one that ended, leaves another live session's alone, claims atomically, and lands under one lock. The procedure is `.claude/agents/round.md`, which `/round` runs in a fresh subagent. The rules:

- A round takes the next ready issue and discards it (close with the reason), redefines it (rewrite the outcome and the acceptance criteria), splits it (one issue per independent change, dependencies only where one blocks another) or implements it (one discrete change, one tested commit, merge to main, push, remove the worktree, close). A round that redefines goes on to implement the issue it rewrote, and a round that splits goes on to implement the first piece, while the context that understood them is at hand; a round lands one implementation at most. Only implement commits.
- A round writes the tool its work needs, when a check is slow, an output is hard to read or a step is repeated by hand: under `tools/`, tested at tier 3, as its own commit ahead of the change that uses it. A tool does not change what the gate requires.
- Work is a stack. An issue discovered mid-round is pushed as a new issue that blocks the current one and resolved in isolation with its own tested commit; then pop back and re-read the blocked issue's directive before resuming, because the premise may have changed. A bug's commit includes the test that exercises it.
- When `bd ready` has no leaf, an epic round runs. A skeptic pass on an epic whose every child is closed comes first, whatever its priority, since closing it releases the leaves that depend on it; only when no epic qualifies does a split round run on an epic with no ready children and none in progress. Among the epics eligible for the same kind of round, the highest priority goes first, the deepest among equals. That finishes the work nearest done first and keeps the tree self-extending toward the star.
- A leaf closes on the gate. An epic closes only after a skeptic pass: a reviewer spawned with no prior context tries to refute each acceptance criterion from recorded evidence (logs, commit SHAs, verify output). A refuted criterion keeps the epic open and becomes an issue.
- A decision only the human can make is its own issue, status blocked, filed before the round ends. One question, the options, and what each implies. Its parent is the epic the question is about. When the current issue must wait, it depends on that issue and stays open. When work can continue either way, the question is filed and nothing depends on it. An answer is a note on the question, then status open when a later round must carry it out, or closed when the answer is the whole outcome. The questions are `bd list -s blocked`. The loop stops only when nothing is ready and every remaining open issue is an epic, a question on that list, or blocked only by such a question; then it prints the questions. A loop that finds nothing ready while another loop holds an issue in progress waits instead. There is no other stop; the human monitors budget.

## Git

Single-person local repository. `origin` is `clemahieu/atmosphere`; no pull requests, and no review gate besides the skeptic pass. The project root holds the bare repository in `.bare` and one worktree per branch beside it; `main` is the worktree `main`. Each task is a worktree sibling named for its branch, off `main`. An implement round merges its branch into `main`, pushes `main` to `origin`, and removes the worktree. One logical change per commit; the message says why. Superseded code is deleted in the same change. Living files describe today, not history.

Beads lives at `.beads` in the project root, shared by every worktree, kept out of the tree by `.bare/info/exclude`, local only: no Dolt remote, no auto-push, no backup. It is not published.

## Gate

A commit is tested when `atmo test` exits 0. It holds when no file `git add -A` would take is over 1 MiB; the workspace builds (`cargo build` in every workspace member's own directory, then the loader, kernel, dom0 and payload from their own directories); the loader memory-map check rejects an unaligned page, a repeated page and an out-of-range page (`cargo test` of build-tool, lines starting `free page ranges:`); the dom0 run check accepts a real dom0 load shape and rejects an unaligned run, an empty run, a run outside the reservation, a run in the kernel's entries, and a physically and a virtually overlapping pair (`cargo test` of build-tool, lines starting `mapped runs:`); every package in `Cargo.lock` passes `tools/check-licenses.py` against `tools/license-allowlist`, and the script's own tests pass; the hooks' tests pass (`.claude/hooks/license-guard-test.sh` and `.claude/hooks/beads-actor-test.sh`); `tools/verify.py` reports no more errors than `tools/verify-allowance`, which equals the count on the proof-debt epic, and a proof leaf lowers both in the same commit; every `external_body` and every `exec_allows_no_decreases_clause` in `kernel/verified` has a reason and matches `tools/external-body-list`, and no `assume(` or `admit(` is left there outside a comment, under `tools/check-external-body.py`, whose own tests pass; `tools/check-boot-stack.py` passes its own tests and, in debug and release, a normal boot, a forced overflow of the boot stack and a forced overflow of the syscall stack, which must fault once in the guard page under it; `tools/coverage.py` captures line and branch coverage per crate, whose numbers are reported and do not fail the gate; `tools/build-design-index.py --check` finds `design/INDEX.md` current; and `tools/run.py --iommu`, under QEMU's emulated IOMMU with its translation enabled, and `tools/run.py`, without one, each boot dom0 to a clean exit within a timeout: exit status 0, the kernel's line for each of the root's fixed slots with its kind, one of them the untyped that is all of 1 to 2 GiB, dom0's first invocation refused with its five arguments in place, dom0's check line and its exit marker `dom0 capability done`, and CPU 1 idle on a syscall stack of its own, acknowledging a flush IPI and contending with CPU 0 for the kernel's lock; and the aarch64 images boot dom0 on the Orange Pi under KVM (`atmo board`'s run, after `tools/aarch64-esp.py --test` and `tools/orangepi-kvm.py --test`) to the same checks of its serial log, with 2 to 3 GiB as the untyped, the host and KVM named in the log, or, when ssh cannot reach the board, the runner's line `skip: orangepi5 unreachable`, which passes. `atmo test --target aarch64` runs only the aarch64 verify and boot, `--target x86_64` every other step. An implement round's gate output is `logs/<id>-gate.log` at the project root, beside the worktrees and outside every tree.

# Design decisions

`design/` holds the decisions made under these principles, one per directory, entered at `design/INDEX.md`; `design/README.md` says how a record is written and revised. A comment that explains a design choice points at `design/<slug>/`, never at a tracker issue, since the tracker is private. Before changing how something is done, read its record; a change that reverses a decision revises its record in the same commit, and a decision someone arriving fresh would re-propose gets a record.

# Working in the tree

```
source tools/env.sh     # Verus, RUSTC_BOOTSTRAP and tools/bin on PATH
atmo test               # the gate
tools/run.py            # build loader, kernel, dom0 and payload; boot under QEMU, with KVM when /dev/kvm is writable; --no-kvm forces TCG
tools/verify.py         # Verus over kernel/verified; extra arguments go to rust_verify
tools/gdb.py            # attach gdb to a tools/run.py --gdb run, with the kernel's symbols
tools/aarch64-esp.py    # build the aarch64 loader, kernel, dom0 and payload and lay out the ESP that tools/orangepi-kvm.py --esp boots on the board
atmo board              # build the aarch64 images, boot dom0 on the Orange Pi under KVM until QEMU exits, and hold the exit and the serial log (target/orangepi-serial.log) to the gate's boot checks, as the gate's aarch64 boot does but failing when the board is unreachable; --command-line LINE writes the kernel's command line to the partition
tools/orangepi-stack-overflow.py   # boot an aarch64 kernel that overflows its boot stack, or with --stack syscall its syscall stack, on the board and check its one report; not part of the gate
```

`tools/setup-verus.sh` builds Verus under `tools/verus`, which git ignores. The host is an AMD Ryzen 9 9950X3D; `/dev/kvm` is world-writable; edk2-ovmf is at `/usr/share/edk2/ovmf`.
