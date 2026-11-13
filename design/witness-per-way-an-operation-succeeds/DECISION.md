---
title: "Every way an operation succeeds is listed, and a witness's ensures claims it"
date: 2026-11-13
status: active
tags: [verified, witness, gate, tools]
one_line: "The inventory's unit is an operation and one value of its result type that is not a refusal. Operations are found from the source, by what the entry calls and by visibility, and the verified crates from their Cargo.toml marker, not from a list. A witness is of the model's operation and claims an outcome in its ensures, over a returned value every binding of which is a call of that operation; the entry is covered by one witness and one proof per wired operation. A throwaway is a function in the tree behind a cfg, calling the witness and claiming false, one module each, and a gate step expects each to fail. What has no witness is a list in the tree that the gate holds equal to the inventory and that only the human lengthens."
revisit_if: "The linkage the tool reads from text lets a witness count that reaches nothing, found by a skeptic or by accident; or the throwaway step costs more than the verify step it runs beside; or an operation's success cannot be told from a value it returns."
confidence: "The throwaway's cost is measured, below. That a claim in an ensures is checked is Verus's. The rule that ties a claim to a call is read from text by a tool, and holds against accident, not against intent: design/committer-is-not-the-adversary/. The split between a witness of the model and a proof of the entry is a judgement about cost."
---

# Every way an operation succeeds is listed, and a witness's ensures claims it

## Decision

A tier-1 component is bounded from below by a witness for each way each of its operations succeeds. Six things make that checkable.

**1. The unit is an operation and one way it succeeds.** A way is a value of the operation's result type that is not a refusal, read from the type:

| result type | the ways | a claim of one, over a value `x` |
|---|---|---|
| an enum the component declares | each variant but `Refused` | `x is V` |
| `bool` | `true` | `x` |
| `Option<T>` | `Some` | `x is Some` |
| `Outcome` | `STATUS_OK`, `STATUS_AGAIN` | `x.status == STATUS_OK` |
| anything else | one, `returns` | a call at the top level of the witness's body |

The last row is for a type that cannot say a refusal, `()` above all. An operation that refuses through such a type, as `print` and `power_off` return the status word itself, or one where both values of a `bool` are ways, as `check_current` says whether it moved the thread off, is given a type that says so by the change that witnesses it. The type is the declaration, and rustc holds every caller to it.

**2. The operations are found from the source.** For `kernel/verified/capability`:

- every exec function that `dispatch`, or an `invoke_` function it calls, calls on `self`: the wired operations;
- every other `pub fn` of `impl CapKernel` that takes `&mut self`: what the glue calls (`kernel_init`, `enter`, `acknowledge`, `load_space`, `switch_space`, `enter_boot_thread`) and each model operation not wired yet (`start`, `suspend`, `bind_device` and the rest).

A step of an operation that is not one itself is `pub(crate)` or private, which rustc holds: the glue is another crate and cannot call it.

The verified user crates are found the same way: every workspace member whose `Cargo.toml` says `[package.metadata.atmosphere] verified = true`, other than `kernel/verified` and acall, read from the directory of its library root. Today that is adivider, aeager, afanin, aheap, amailbox, aring and pager-policy. A user crate's operations are its `pub fn` exec items, and the exec functions of a trait it implements for a type it declares, by the same rule. pager-policy holds only the specifications and proofs of the S3-FIFO policy the pager library implements, so it has no operation and yields no line. Witness and throwaway modules hold no operation.

The rest of `kernel/verified`, outside `capability`:

- `queue_lock.rs` is read by the user-crate rule, as a component of its own: `CapKernel` does not call it, and the kernel's lock glue conjures its core tokens, so no witness of the capability component reaches it.
- `define.rs`, `layouts.rs` and `util/` hold constants, layouts, specifications and proofs, and no exec function: nothing to list.
- `array.rs`, `pptr.rs` (held to upstream vstd's `simple_pptr`) and `pagetable/` are data-structure libraries internal to the kernel. None of their functions refuses: each is exact under its requires, and `CapKernel`'s operations call them where its witnesses reach. They are steps of the capability component, not a component.
- `arch/` holds the leaf hardware guarantees outside `verus!`, vouched for by the manual passages they cite and checked by the boots, and the per-ISA encodings and token wrappers `CapKernel`'s operations call. design/arch-module/ and design/who-vouches-for-an-unproven-claim/ say who vouches for each; no witness can reach past an assumed specification.

A new module of `kernel/verified` outside `capability` is one of these, or a component this list gains in the change that adds it. An acall wrapper is not a second operation: it is the entry seen from user space, verified over `step`. It is listed on one line with the call number it passes and the kernel operations that number's arm calls, and counts as unwitnessed only when the arm calls none.

**3. A witness is of the model's operation.** It calls `retype_large_frame`, not the entry with a frame that encodes the call. Two things cover the entry:

- one witness that `enter` answers, which the rule of point 2 already asks for, since `enter` is an operation with the way `Some`;
- for each wired operation, one proof named `lemma_entry_reaches_<operation>`: of an invocation that `invoked` relates, whose frame selects the operation's arm and whose decoded arguments meet the condition the operation succeeds on, the returned status is the one the arm gives each way. A way of a wired operation is witnessed when a witness claims it and this proof exists.

A root witness starts from what boot ensures. In the kernel it is a `pub fn witness_` of `impl CapKernel` whose requires holds `old(self).booted(...)` and no other conjunct naming `self`: the rest bound boot's inputs and the caller's choices. The witness of an operation that makes the state, `kernel_init`, names no state at all. In a user crate a root witness takes no value of a struct or enum the crate declares, so every such value is one the crate's own constructors made; it takes its environment as that environment's contract gives it (a span source, a caller token, a page's permission). Where the environment may refuse, a claim may be guarded by what the environment answered, `g ==> x is V`, and the inventory prints the guard beside the witness. No witness is written over a single acall wrapper.

**4. A claim is a conjunct of a root witness's ensures, and the tool ties it to a call by one rule.** The claim is over a component of the returned value, `ret.2 is Freed`. The tool takes the function's last expression, finds the name in that component, and counts the claim for operation P when every binding of the name in the body, each `let` and each assignment, is a call `self.P(...)`, or `P(...)` for a free function. A name bound by destructuring one call of another `witness_` function is followed into that function, whose own ensures must claim the same way of the same component. Anything else resolves to no operation and counts for nothing: a literal, `ok && ok5`, a name bound from two operations. So a loop that repeats an operation until it is done is written `let mut step = self.P(..); while step is Again { step = self.P(..); }` and returns `step`.

Verus proves the function ends and that the returned value is what the ensures says. The rule gives that the value came from a call of P. A helper's claim that no root witness's ensures repeats is not counted.

**5. A throwaway is a function in the tree that a gate step expects to fail.** For the witness `witness_x`, the function `throwaway_x` has the witness's parameters and its requires word for word, a body that is one call of the witness, and `ensures false`. Each is its own module file under a `throwaway` module beside the witnesses, behind `#[cfg(throwaway)]`, which no build and no verify run sets, so it is in no image and no verify count. A check, a gate step on x86_64, runs `rust_verify` once per crate with `--cfg throwaway --verify-module <the throwaway module>` at the verify budget and passes when:

- every root witness has exactly one throwaway, and its requires is the witness's text;
- the run verifies nothing and reports one error per throwaway, located in that throwaway's file;
- each error is the postcondition's or the solver budget's, and none is a precondition's or the compiler's.

**6. What has no witness is a list in the tree, `tools/unwitnessed`.** One line per unit: path, operation, way. The gate step that runs the inventory fails unless the units it finds with no witness are exactly the list's lines. A change that witnesses a way removes its line in the same commit. `tools/land.py` refuses a landing whose list holds a line the base's does not, unless `--approve` names it, as it does for a new `external_body`: lengthening the list lowers what the proof shows from below, so it is a decision only the human can make. The count the tracker keeps is the list's length.

## Context

A witness was written only for a use an epic's text named, and only that epic's review asked for it. Nothing listed what should be witnessed, so `start` came to refuse on every state boot can reach with no check saying so. A search of `kernel/verified/capability/witness.rs` found no call of `unmap`, `probe`, `print`, `power_off`, `inspect`, `start` or `check_current`, no witness naming `RevokeStep::Exhausted`, and none through `dispatch`. A throwaway was run once, logged outside the tree and held only to the last change of its witness's own text, so a change to `booted` or to an operation's specification left it standing.

## Reasoning

**The way, not the operation.** `retype` under the free kind returns `Again`, `Freed`, `Unlinked` or `Slice` by what the block is, and each is a different path through the proof. A witness that reaches `Freed` says nothing of `Slice`. Counting operations would have called `reclaim` witnessed after its first.

**Found, not listed.** The gap this closes is an operation nobody named. A list of operations kept by hand has the same gap: a new operation is missed until someone adds its line. Reading the source turns the default around: a new `pub fn` is counted until its author narrows it, and narrowing it is a statement rustc checks.

**The model, with a proof for the entry.** `dispatch` already ensures `invoked`, and `invoked` is stated in the predicates the model's operations are exact about: `allows_retype` is `can_retype_frame`, `can_retype_large` and the rest by the kind. So that the entry reaches an operation is one short proof per operation, from the operation's own condition. Rewriting each witness through the entry would encode every argument into a frame at every step of 8,412 lines of witnesses, and would lose the ways the entry folds together: the entry answers `STATUS_OK` for `Freed` and refuses for `Unlinked` and `Slice` under the free kind, and operations not wired yet have no entry at all.

**The ensures, and one rule of text.** A comment or a name is not checked by anything. A conjunct of an ensures is: Verus proves it of every run from the requires. An assertion in the body is weaker, since one inside a branch that is never taken is proven of nothing. What the ensures cannot say is which call produced the value, and no cheap device in Verus ties a value to its call. The every-binding rule is the smallest one that stays true whatever order the bindings run in, and it fits a loop. It is read from text, so it holds against accident and not against intent, which is the standard design/committer-is-not-the-adversary/ sets.

**A wrapper claiming false.** A throwaway shows a witness is not hollow: were its premises contradictory, the variant would verify. A wrapper tests exactly that, the requires together with the witness's ensures, and a verified function that ends cannot have contradictory ensures unless its requires are. Claiming `false` is the most a variant can claim and needs no choice per witness. A solver that runs out of budget looking for a contradiction has not found one, so that error counts as the failure it is; a precondition's error means the requires drifted from the witness's, and does not.

Measured on main `73c16509`, on the gate's host, an AMD Ryzen 9 9950X3D with other gates running, with three such wrappers, of `witness_root_claims_a_capability`, `witness_root_retypes_a_freed_2m_frame` and `witness_dead_table_page_freed`. Wall time around `rust_verify --crate-type lib lib.rs --rlimit 100 --cfg throwaway` from `kernel/verified`:

| run | wall |
|---|---|
| `--verify-only-module` of a module with nothing to prove: the front end | 14.1 s |
| each alone by `--verify-function` | 19.2 s, 18.5 s, 42.0 s |
| the three in one module | 66.2 s |
| the same at `--rlimit 10` | 26.1 s |
| one module each, one process, `--verify-module` three times | 41.3 s |
| `--verify-only-module capability::witness`, what copies of the bodies would at least add | 71.8 s |

Two of the three ended on the budget and one on the postcondition. The solver's share is 4 to 28 s each. One module each lets Verus check them side by side, so the step costs the front end and the slowest throwaway while cores are free, about 45 s beside a verify step of 105 s in a gate of 401 s. One module for all would cost their sum, several minutes at thirty witnesses.

**A list, not a number.** With a number, a change that witnesses one way and loses another leaves the count where it was. With lines, the step compares sets. `tools/land.py` already refuses an added line of `tools/external-body-list` without the human's approval, and this is the same decision about the same kind of debt.

## Alternatives rejected

- **The operation as the unit.** Hides every way but the first.
- **A list of operations kept by hand.** Misses what nobody added, which is how the gap arose.
- **Every witness through the entry.** The cost above, and the model's ways are finer than the entry's statuses.
- **A claim as an assertion after the call, or as a comment.** An assertion in a dead branch proves nothing; a comment is checked by nothing.
- **A throwaway as a copy of the witness's body with one line changed.** It re-proves the witness, 71.8 s for the module against 4 to 28 s a wrapper, doubles the witnesses' text, and drifts from the witness it copies. What a chosen change showed, that a step of the sequence is needed, is what the operation's specification says by being exact about refusal.
- **A lower solver budget for the step.** At `--rlimit 10` the three cost 26 s in one module, but a contradiction the verify run can find at its budget could then be missed by the step meant to find it.
- **Hiding `booted` in the throwaway to make it fail fast.** A bound that contradicts `booted` would no longer be seen.
- **Throwaways kept as logs outside the tree.** Nothing runs them again.
- **Running the step on aarch64 too.** The premises a throwaway tests are the model's, which the target does not change; the verify step already runs the witnesses on both.
- **An allowance that the count may fall below.** Room between the two is room for an unwitnessed way to land unseen.

## What this does not settle

- Whether a `lemma_entry_reaches_` proof says what point 3 asks. The tool sees the name; the statement is for a reviewer.
- Whether a guard on a user crate's claim is only its environment's answer. The inventory prints it; a reviewer judges it.
- A use made of several operations in sequence from user space, as acall's `read_only_child`. Between two calls other callers step, so what it can claim waits on what is proven of them.
- That `kernel_init` succeeds on a real machine. The boot in the gate shows it on two; its witness shows only that some inputs are accepted.
- Which bounds on boot's inputs a witness may take. A throwaway shows they are consistent with `booted`, not that a real boot meets them.
