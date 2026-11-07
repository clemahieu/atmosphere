---
title: "The new kernel is built beside the old one and cut over on a branch that boots both"
date: 2026-11-05
status: active
tags: [process, gate, verified]
one_line: "New proven modules land on main beside the old kernel while boot keeps using the old one. The cut-over is a branch off main: a build feature selects old or new kernel entry and dom0, the branch gate boots both so each syscall is booted in the commit that wires it, the last commits delete the old kernel and the feature, and the branch merges with a merge commit. Main never contains the selection."
revisit_if: "The cut-over branch has merged, when this record has done its work and the shim rule in CLAUDE.md applies to the whole tree again."
confidence: "A process choice by the human after an independent review judged a single landing too large to finish in one round and its parts unable to pass the gate on their own."
---

# The cut-over is a branch

## Decision

Editing the old kernel in place cannot keep the gate green while hundreds of container uses change, so the new kernel is built as new proven modules beside the old one, and boot keeps using the old one, whose proofs stay valid. Each new module lands on main under the gate.

The cut-over is a branch, not a second kernel on main and not one unbooted landing. It branches off main once the new modules it needs have landed. On that branch a build feature selects the old or new kernel entry and dom0, and the branch gate boots both, so each syscall is booted in the commit that wires it. The last commits on the branch delete the old kernel and the feature. The branch joins main with a merge commit. The merged tree has one kernel and one boot; main never contains the selection, and main's gate boots once throughout. Leaves of the cut-over branch from it and fast-forward back into it, and while it is open it takes main's commits. Dom0's existing checks are the behaviour the new kernel re-expresses.

## Reasoning

The cut-over switches the syscall table, boot, the user-space syscall crate and dom0 and deletes about 30,000 lines, `design/untyped-memory/`. Too large for one round, and its parts cannot each pass the gate alone. A temporary selection is not a compatibility layer under the global rule, since nothing is released and it has a fixed end, but it is two kernels in one tree for a while, which that rule says to be wary of. Confining it to a branch pays the double boot only on the cut-over commits and keeps the shim rule unchanged on main.

## Alternatives rejected

- **Two kernels on main behind a feature.** Gate time doubles for everyone and the selection lingers.
- **One landing.** No real boot of any new syscall until it lands, and likely many attempts.
