---
title: Each gate step declares its inputs and a landing runs only the steps whose inputs changed
date: 2026-11-15
status: active
tags: [gate, landing, process]
one_line: Each gate step declares the repo-relative path globs it reads (or unbounded for file sizes and source licenses), a landing skips bounded steps whose inputs did not change and whose base input-slice hash passed in logs/gate-ledger, UNREAD is deleted, and the map is checked mechanically.
revisit_if: External host dependencies unpinned by Cargo.toml, rust-toolchain.toml, or tools/env.sh affect step outcomes; every gate step becomes fast enough that selective gating is unnecessary; or a hermetic build system replaces the custom gate and ledger.
confidence: high
---

## Decision

1. **Every `Step` in `tools/gate.py` declares its inputs.**
   `Step` becomes `namedtuple("Step", "name target check inputs")`. `inputs` is either:
   - `None` (unbounded) for whole-repository checks that inspect arbitrary changed or tracked files (`file sizes` and `source licenses`); or
   - a tuple of repo-relative path globs (`PurePosixPath` / `**` glob semantics matching normalized git tree paths) naming every file in the repository the step, its tests, or any tool or crate it invokes can read.

   Two shared sets enter every bounded step:
   - `GATE_SELF`: `("tools/gate.py",)` because changing the runner can change any step's command, filter, or declared inputs.
   - `TOOLCHAIN_PINS`: `("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "tools/env.sh")` because workspace manifests, crate lock versions, the pinned `vstd` revision (checked against `../verus`), the Rust toolchain and `rust-src` sysroot, and Verus/OVMF/QEMU environment variables govern builds, verification, and boots.

   Using shorthand constants:
   - `VERIFIED_CRATES` = the crates carrying `[package.metadata.atmosphere] verified = true` (`kernel/verified/**`, `aheap/**`, `acall/**`, `aeager/**`, `aring/**`, `amailbox/**`, `afanin/**`, `pager-policy/**`, `adivider/**`, `awire/**`) plus their non-dev workspace dependency `asys/**`.
   - `BOUNDARY_CRATES` = the boundary crates (`kernel/**`, `dom0/**`, `astd/**`), all their transitive workspace dependencies (`abench/**`, `acontext/**`, `asys/**`, `kernel-logger/**`, `machine/**`, `ns16550a/**`), and all verified crates (`VERIFIED_CRATES`).
   - `IMAGE_CRATES` = every crate linked by the boot images (`aloader`, `kernel`, `dom0`, `user/hello`) plus their transitive workspace dependencies and target configs: `aloader/**`, `aelf/**`, `kernel/**`, `dom0/**`, `user/hello/**`, `user/.cargo/**`, `user/*-unknown-aloader.json`, `astd/**`, `acall/**`, `aeager/**`, `aheap/**`, `asys/**`, `kernel-logger/**`, `machine/**`, `ns16550a/**`, `abench/**`, `acontext/**`, `kernel/verified/**`. (Note that `kernel/**` covers `kernel/.cargo/**`, `kernel/src/*.json`, `kernel/src/logo.txt`, and `kernel/verified/**`.)
   - `WORKSPACE_CRATES` = every workspace member in `Cargo.toml` (`IMAGE_CRATES` plus `aring/**`, `amailbox/**`, `afanin/**`, `pager-policy/**`, `adivider/**`, `awire/**`, `file-service/**`, `boot-host-tests/**`).

   Each of the 27 steps declares:

   | Step | Target | Inputs (`GATE_SELF + TOOLCHAIN_PINS + ...` when bounded) |
   | --- | --- | --- |
   | `file sizes` | `x86_64` | `None` (unbounded; always runs) |
   | `source licenses` | `x86_64` | `None` (unbounded; always runs) |
   | `license` | `x86_64` | `tools/check-licenses.py`, `tools/license-allowlist`, every workspace member's `Cargo.toml` (`<member>/Cargo.toml`) |
   | `hooks` | `x86_64` | `AGENTS.md`, `.agents/hooks.json`, `.claude/hooks/license-guard.sh`, `.claude/hooks/license-guard-test.sh`, `.claude/hooks/beads-actor.sh`, `.claude/hooks/beads-actor-test.sh`, `.claude/hooks/agy-session-start.sh` |
   | `design index` | `x86_64` | `tools/build-design-index.py`, `design/*/DECISION.md`, `design/INDEX.md` |
   | `faq` | `x86_64` | `tools/faq.py`, `docs/faq/**`, `kernel/verified/define.rs`, `kernel/verified/layouts.rs`, `kernel/verified/capability/**` |
   | `arch sources` | `x86_64` | `tools/check-arch-sources.py`, `kernel/src/**` |
   | `upstream copies` | `x86_64` | `tools/check-upstream-copies.py`, `tools/upstream-copies/**`, and every target path named in those patch headers (currently `kernel/verified/pptr.rs`) |
   | `page literals` | `x86_64` | `tools/check-page-literals.py`, `VERIFIED_CRATES` |
   | `invoked arms` | `x86_64` | `tools/check-invoked-arms.py`, `kernel/verified/**` |
   | `external body` | `x86_64` | `tools/check-external-body.py`, `tools/external-body-list`, `tools/hardware-documents`, `VERIFIED_CRATES`, `kernel/**` (for `// kernel:` guarantor targets) |
   | `layout claims` | `x86_64` | `tools/check-layout-claims.py`, `VERIFIED_CRATES` |
   | `verify` | `x86_64` | `tools/verify.py`, `tools/verify-allowance`, `VERIFIED_CRATES` |
   | `verify aarch64` | `aarch64` | `tools/verify.py`, `tools/verify-allowance`, `VERIFIED_CRATES` |
   | `throwaways` | `x86_64` | `tools/verify.py`, `tools/check-throwaways.py`, `VERIFIED_CRATES` |
   | `unwitnessed` | `x86_64` | `tools/verify.py`, `tools/check-throwaways.py`, `tools/witness-inventory.py`, `tools/unwitnessed`, `VERIFIED_CRATES` |
   | `refused` | `x86_64` | `tools/verify.py`, `tools/check-throwaways.py`, `tools/witness-inventory.py`, `tools/check-refused.py`, `VERIFIED_CRATES` |
   | `unrefused` | `x86_64` | `tools/verify.py`, `tools/check-throwaways.py`, `tools/witness-inventory.py`, `tools/check-refused.py`, `tools/refused-exempt`, `tools/unrefused`, `VERIFIED_CRATES` |
   | `boundary` | `x86_64` | `tools/check-boundary.py`, `tools/check-external-body.py`, `tools/boundary-list`, `tools/hardware-documents`, `BOUNDARY_CRATES` |
| `build` | `x86_64` | `tools/build.py`, `tools/check-stack-sizes.py`, `WORKSPACE_CRATES` |
   | `workspace tests` | `x86_64` | `WORKSPACE_CRATES`, `tools/check-invoked-arms.py` (`boot-host-tests` invokes `tools/check-invoked-arms.py` and includes `../../kernel/src/boot/*.rs`) |
   | `forced lints` | `x86_64` | `WORKSPACE_CRATES` (checks host workspace members plus `FORCED_LINT_AARCH64` targets `aloader`, `kernel`, `dom0`, `user/hello`) |
   | `boot stack` | `x86_64` | `tools/check-boot-stack.py`, `tools/run.py`, `tools/elfstrip.py`, `tools/firmware.py`, `IMAGE_CRATES` |
   | `coverage` | `x86_64` | `tools/coverage.py`, `tools/check-boot-stack.py`, `tools/run.py`, `tools/elfstrip.py`, `tools/firmware.py`, `IMAGE_CRATES`, `user/**` |
   | `iommu boot` | `x86_64` | `tools/run.py`, `tools/elfstrip.py`, `tools/firmware.py`, `tools/check-boot-log.py`, `IMAGE_CRATES` |
   | `boot` | `x86_64` | `tools/run.py`, `tools/gdb.py`, `tools/gdb-helper.py`, `tools/elfstrip.py`, `tools/firmware.py`, `tools/check-boot-log.py`, `IMAGE_CRATES` |
   | `aarch64 boot` | `aarch64` | `tools/board.py`, `tools/aarch64-esp.py`, `tools/build.py`, `tools/check-stack-sizes.py`, `tools/elfstrip.py`, `tools/orangepi-kvm.py`, `tools/check-boot-log.py`, `IMAGE_CRATES` |

   Every step added in the future declares its own `inputs` alongside its runner, and `tools/gate.py` exposes the set of uncovered paths dynamically (`--unread`) instead of maintaining an exception list.

2. **Steps are self-contained with respect to `target/`.**
   A skipped step must never leave a downstream step missing `target/` build outputs. `tools/check-throwaways.py` and `tools/check-refused.py` ensure the exported crate artifacts in `target/verus/` exist when `verify` did not run beforehand; `workspace tests` (`boot-host-tests`) ensures the `dom0` and `hello` `x86_64-unknown-aloader` binaries exist when `build` was skipped; and `tools/check-layout-claims.py` stages only workspace crates and manifests instead of copying the entire git file list.

3. **Per-step verdicts and input-slice hashing in `logs/gate-ledger`.**
   Define `input_hash(tree, step)` for any git tree object `tree` and bounded `step` as a cryptographic digest over the sorted `(mode, blob_sha, path)` entries of `git ls-tree -r tree` whose `path` matches `step.inputs`.

   `logs/gate-ledger` records one line per judged bounded step run:
   `<step_name> <slice_hash> <verdict> <commit> <ts>` (with `<step_name>` URL- or underscore/tab-delimited cleanly so multi-word step names parse unambiguously). Whole-tree entries can remain readable as legacy records during migration, or wait behind a clean line tag; unbounded steps (`file sizes`, `source licenses`) always run on every landing and never rely on a cached skip.

   - **Hardware unreachable non-verdict**: When `aarch64 boot` exits 0 only because `tools/board.py` emitted `skip: orangepi5 unreachable`, the landing proceeds as before, and `tools/land.py` does **not** record `"pass"` for `(aarch64 boot, slice_hash)`. Only a real boot pass writes `"pass"`, so an unreachable board never suppresses hardware testing on later landings.

4. **How `tools/land.py` picks steps to run and interacts with ungated compositions.**
   When landing branch `HEAD` rebased onto `base`:
   - All unbounded steps (`file sizes`, `source licenses`) always run.
   - Each bounded step `S` runs unless **both**:
     1. `input_hash(HEAD, S) == input_hash(base, S)` (the branch modified no file matching `S.inputs`), **and**
     2. `logs/gate-ledger` contains `"pass"` for `(S.name, input_hash(base, S))`.
   - When both hold, `S` is skipped and retains `base`'s `"pass"` verdict for `S` (since `input_hash(HEAD, S)` equals `input_hash(base, S)`). When `S` runs and exits 0 (and did not skip hardware cleanly as unreachable), `land.py` appends `<S.name> <input_hash(HEAD, S)> pass <commit> <ts>` to `logs/gate-ledger`; when `S` fails, `land.py` records `fail` if applicable and resolves blame per step.

   **Meaning when `main`'s tip is an ungated composition (`design/land-without-regating/`):**
   Two concurrent clean rebases land `B = merge(A, C)` without running a combined gate on `B`. Because `logs/gate-ledger` indexes bounded verdicts by `(S.name, input_hash(tree, S))`:
   - For any step `S` whose `inputs` were touched by at most one side of the composition (for instance, loop 1 modified `kernel/src/boot.rs`, which leaves `verify` untouched, and loop 2 modified `tools/faq.py`, which leaves `build` and `boot` untouched), `input_hash(B, S)` already equals a passed slice hash recorded by one of those landings, so subsequent changes that do not touch `S.inputs` safely skip `S`.
   - For any step `S` whose `inputs` were modified by **both** concurrent commits, `input_hash(B, S)` is a new slice hash absent from `logs/gate-ledger`. Condition (2) above is false, so the very next landing that arrives over `B`—even a doc-only change—cannot skip `S`; it runs `S` against `B` and records the result for `input_hash(B, S)`. If `S` fails on that branch when `input_hash(HEAD, S) == input_hash(B, S)` or when `input_hash(B, S)` is unjudged, `tools/land.py --judge-base` only needs to run the failing/unjudged steps on `base` (not unrelated slow steps like `verify`), and `suspects` searches commits since the last recorded pass for `S` whose diff touched `S.inputs`.

5. **Delete `UNREAD` and retire `design/no-gate-for-what-no-step-reads/`.**
   Once `tools/gate.py` declares `inputs` and `tools/land.py` selects steps per-step, `UNREAD` and its duplicate size/SPDX re-implementation in `tools/land.py` (`needs_no_gate`, `bad_sizes`, `source_licenses`) are deleted. Edits to `.claude/agents/**`, `.claude/skills/**`, `CLAUDE.md`, `README.md`, `tools/loop.py`, or any other uncovered file trigger only the two unbounded steps (`file sizes`, `source licenses`). This record replaces `design/no-gate-for-what-no-step-reads/`, which is deleted.

6. **How the input map is kept true by a mechanical check.**
   The map is enforced by two complementary checks in `tools/gate.py` (never maintained by trusting hand-inspection):
   - **Post-run Cargo `.d` dep-info audit**: Every Cargo/Verus step that compiles Rust (`build`, `workspace tests`, `forced lints`, `layout claims`, `boundary`, `verify`, `verify aarch64`, `throwaways`, `refused`, and the image boot steps) runs as usual in the shared `target/` directory, after which `tools/gate.py` reads the compiler/Cargo `.d` files written during that step and fails if any source, `#[path = ...]`, `include_str!`/`include_bytes!`, or `build.rs` repo path lies outside `step.inputs`. This adds only milliseconds to normal gates and immediately catches cross-crate Rust source inclusions without compiling everything twice.
   - **Sandboxed input-isolation check (`--check-inputs`) plus metadata tests**: Because Python scripts, shell hooks, and `cargo metadata` graph changes are not captured by existing `.d` files alone, `tools/gate.py --check-inputs` materializes a sibling hardlinked tree (next to `../verus` and `../reference`, mirroring normal task worktree layout) holding **only** the repository paths matching `step.inputs` and executes the bounded step inside that isolated view so any undeclared file read fails immediately. This isolation check guards changes to gate/tool scripts, hooks, `Cargo.toml` manifests, and `boot-host-tests/**`, paired with fast unit assertions in `tools/gate.py --test` checking every workspace crate closure (`cargo metadata`), `verified = true` crate set, `FORCED_LINT_AARCH64`, and `tools/upstream-copies/*.patch` targets against `Step.inputs`.

## Context

Previously, `design/no-gate-for-what-no-step-reads/` avoided running the gate only when every changed path lived inside `UNREAD` in `tools/land.py`. Any change touching even one path outside `UNREAD`—such as unverified kernel glue (`kernel/src/`), `docs/faq/`, `.claude/hooks/`, or a verified tool check—ran the entire 27-step gate, including minutes of Verus verification (`verify` and `verify aarch64`), x86_64 IOMMU/non-IOMMU QEMU boots, coverage builds, and the physical Orange Pi aarch64 boot. Meanwhile, `UNREAD` had to be extended by hand whenever a new loop, status, or review tool landed under `tools/`.

## Reasoning

- **Explicit positive `inputs` on `Step` instead of an `UNREAD` exception list.** New tools outside bounded steps default to running only the cheap whole-tree hygiene checks (`file sizes` and `source licenses`), instead of defaulting to a 20-minute Verus+QEMU gate until someone adds another directory or filename to `UNREAD`.
- **Keying `logs/gate-ledger` by `(step, input_slice_hash)` instead of `(commit_or_tree, step_mask)`.** Two concurrent branches can merge cleanly into an ungated composition `B` on `main`. Keying by the hash of only the files matched by `step.inputs` proves automatically which steps already passed on identical inputs (`disjoint` steps) and which steps see an unseen combined input tree (`overlapping` steps) and therefore must run—preserving the lockless invariant of `design/land-without-regating/`.
- **Not recording `"pass"` when `aarch64 boot` skips an unreachable board.** Under per-step caching, a single false `"pass"` would allow subsequent landings that modify kernel or bootloader glue to inherit a bogus cached `"pass"` even after the Orange Pi comes back online. Treating unreachable hardware as unjudged keeps the existing offline workflow intact without poisoning future gates.
- **Hybrid mechanical check (`.d` dep-info audit + `--check-inputs` sandbox view + `cargo metadata` invariant tests).** Checking only command-line arguments fails immediately because Cargo, `cargo metadata`, `#[path = ...]`, `include_str!`, and Python test files read repo paths not named on CLI flags. Conversely, running heavy Verus + QEMU sandboxes on every trivial `.rs` line edit would erase much of the latency win. Auditing `.d` files after every Rust/Verus step costs milliseconds on every code change, while `--check-inputs` hardlink sandboxes verify Python, hook, manifest, and script changes end-to-end against empty `target/`.

## Alternatives rejected

- **Keep `UNREAD` and add coarse category buckets (such as "docs", "unverified kernel", "tools") without a step map.** Rejected earlier in `design/no-gate-for-what-no-step-reads/` and rejected again here: unverified files like `kernel/src/boot/free_ranges.rs` are read by `workspace tests` (`boot-host-tests`), `kernel/src/` files are `// kernel:` targets for `external body` and boundary sites for `boundary`, and `kernel/verified/` constants are read by `faq`. Without per-step declarations held true by checks, coarse buckets either drift into unsound skips or degrade back to gating everything.
- **Check only paths named in each step's CLI invocation.** Rejected because `cargo build`, `cargo test`, `tools/verify.py`, `tools/check-boundary.py`, `tools/check-external-body.py`, and `tools/faq.py` discover workspace crates and read repo files internally rather than receiving them as command-line arguments.
- **Run every bounded step inside a fresh isolated hardlink directory with no shared `target/` on every landing.** Rejected for normal landings because `build`, `forced lints`, `workspace tests`, `boundary`, `boot stack`, `coverage`, `iommu boot`, `boot`, and `aarch64 boot` reuse compiled crates across `target/`, and `verify` -> `throwaways`/`refused` share compiled stdlib/vstd dependencies. Keeping normal execution in one worktree `target/` while checking `.d` files and running `--check-inputs` sandboxes when tooling or manifests change preserves incremental compilation speed while still checking every input edge.
- **Record skipped step verdicts under the composed `tree_id` without hashing each step's input slice.** Rejected because if two concurrent loops both change `kernel/src/` (or both change `kernel/verified/`) and merge cleanly via `design/land-without-regating/`, attributing base `"pass"` to a combined `tree_id` on an un-run step would skip testing their interaction on the next doc-only change.

## What this does not settle

- **Parallel execution of independent steps.** Declaring `inputs` and decoupling `target/` assumptions (`throwaways`/`refused`/`workspace tests`) enables running independent steps concurrently later, but step scheduling within `tools/gate.py` stays sequential for now.
- **Shared `target/` or sccache across worktrees.** Skipping untouched steps avoids running them at all; speeding up steps that *do* run on a changed input by warming caches from `main` is left separate.
- **External environment mutations not tracked in git.** Changes to the host OS, QEMU/OVMF packages, LLVM, or an unpinned dirty checkout in `../verus` outside `Cargo.toml` and `tools/env.sh` are outside git-tree hashing; `verify.py` continues checking the clean `vstd` revision match explicitly.
