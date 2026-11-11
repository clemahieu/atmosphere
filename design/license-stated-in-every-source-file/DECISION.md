---
title: "Every source file states its license on its first line"
date: 2026-11-11
status: active
tags: [process, gate, license]
one_line: "Each Rust, Python, shell, C and assembly file, and any file starting with #!, carries an SPDX-License-Identifier comment as its first line, or its second under the #! line; the gate holds the expression to tools/license-allowlist, and every other file is under LICENSE."
revisit_if: "The tree is distributed in pieces whose recipients need each file's copyright holder from the file alone, or a scanner or a downstream packager asks for REUSE compliance; then the copyright tag, the LICENSES directory and the manifest are added."
confidence: "A judgement about cost against a risk that has not yet occurred: no file under a second license is in the tree today. That the check holds is tested."
---

## Decision

A source file is a file whose name ends in `.rs`, `.py`, `.sh`, `.c`, `.h` or `.S`, or whose first line starts with `#!`. Its first line, or its second under a `#!` line, is a comment that holds `SPDX-License-Identifier:` and the file's license as an SPDX expression, and nothing else:

```
// SPDX-License-Identifier: MIT
```

A file written here says `MIT`. A file taken from another source says that source's license, and keeps its copyright and notice lines as they came.

`tools/check-spdx.py` is a gate step. It fails on a source without the line, and on an expression that `tools/license-allowlist` does not pass, read by the same parser that reads a package's license field.

Every other file, the documentation, the manifests, the target descriptions, `Cargo.lock` and the data files under `tools/`, is under the tree's `LICENSE` and says nothing of its own.

## Context

`CLAUDE.md`'s License principle covers every line in the tree. The gate held the dependencies to it through `tools/check-licenses.py` and held the tree's own files to nothing.

The tree is under one license, MIT, and `LICENSE` says so. Four files derive from other sources: `kernel/verified/pptr.rs` from Verus, `kernel/src/arch/x86_64/interrupt/idt.rs` and `mod.rs` from BlogOS, and `aelf/src/lib.rs` from nix-ld-rs. All four are MIT. They differ from the rest in their copyright holders, which each file names.

## Reasoning

A tag that every source must carry turns a missing one into a failure. Without the requirement, a file that says nothing is taken to be the tree's own under the tree's license, and a file copied in from elsewhere makes that claim by default. The check does not prove a tag true. It makes the author of a new file state the license at the moment the file arrives, and it refuses a stated license that the allowlist does not hold.

A kernel's files are read and copied one at a time: the four derived files came into this tree that way. A file that travels alone carries its license with it.

The cost is one line in each of 215 files and a gate step of a tenth of a second.

The tag is on a fixed line so that the check is a comparison and a reader knows where to look.

## Alternatives rejected

- **The tree's `LICENSE` alone.** It is the usual declaration for a tree under one license, and it is what most Rust crates do. It leaves the principle unchecked for the tree's own files, and a file that says nothing cannot be told from a file nobody looked at.
- **A tag on the exceptions only.** The exceptions today are exceptions of copyright holder, not of license, so their tags would repeat the tree's. And absence would again mean the default, which is the case the check exists to remove.
- **REUSE compliance**: a copyright tag on every file, the license texts under `LICENSES/`, and a manifest for the files that cannot hold a comment. It answers who holds the copyright of each file from the file alone, which nothing asks of a tree whose `LICENSE` names its holders and whose derived files name their own.

## What this does not settle

What ships beside a binary. The dependencies are under MIT, most by choice against Apache-2.0, BSD-3-Clause and Unicode-3.0, and a distributed image owes the notices of those it links; the tree has no release artifact yet.

The copyright lines of a derived file. The check reads the license tag and cannot tell whether a file's notice lines were kept; that is the author's care and the reviewer's.
