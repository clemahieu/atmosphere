---
title: "An arm of invoked is the operation's postcondition, one predicate both sides call"
date: 2026-11-15
status: active
tags: [capability, verified, entry]
one_line: "Each arm of invoked carries the postcondition of the operation the entry calls: the arm and the ensures call the same predicates, and a source check holds the pairing."
revisit_if: "A caller that has invoked and not dispatched needs a conjunct the allowlist skips, or a skeptic finds a shared predicate whose body drops a field the ensures used to state beside the call."
confidence: "A judgement about where a postcondition is written, in the form of the text rule in design/witness-per-way-an-operation-succeeds/. The check holds against accident, not against intent, as design/committer-is-not-the-adversary/ sets."
---

# An arm of invoked is the operation's postcondition, one predicate both sides call

## Decision

An arm of `invoked` in `kernel/verified/capability/operation.rs` carries the postcondition of the operation the entry calls for that arm. The postcondition is written once. The operation's `ensures` calls it, and the arm calls it.

**Which operation.** For an arm that calls `spec_retyped`, `spec_derived`, `spec_moved`, `spec_deleted`, `spec_revoked`, `spec_linked`, `spec_mapped`, `spec_unmapped` or `spec_probed`, the operations are the `pub fn` methods of `impl CapKernel` that the matching `invoke_*` function calls on `self`. The check reads those calls from the body. It does not follow them into further calls, and it does not read `invoke_*`'s own ensures. A `pub fn` that the bodies of two `invoke_*` functions in `dispatch` call is an operation only of an `invoke_*` that calls no other `pub fn`: `invoke_write_registers` reads the saved frame with `read_registers` before it stores one with `write_registers`, and `read_registers` is the operation of `invoke_read_registers`, which calls nothing else. When every caller also calls another `pub fn`, it stays an operation of each caller, so a call cannot drop out of the check. A `pub fn` one body calls is that body's operation, as `invoke_retype`'s several are retype's.

The last arm of `invoked` is `spec_outcome_carried(...)`. Its operations are the `pub fn` methods `dispatch` calls on `self` in the arms `invoked` does not name: `print`, `power_off`, `inspect` and `read_registers`. `spec_outcome_carried` is that arm's spec function. It says the kernel is unchanged and the outcome is `spec_outcome`, and it calls the predicates those four operations' ensures call, so the arm's value depends on each predicate. `Send`, `Receive`, `Call` and `ReplyRecv`, which `dispatch` does not call, and a number no operation has, are the constant refusal and `STATUS_UNKNOWN` inside `spec_outcome`. The check reads no model ensures for them.

**Which conjuncts.** The check splits an `ensures` on top-level `&&&`, after collapsing whitespace. It skips two shapes:

- a conjunct that mentions the ghost step counter `steps`, which `design/one-lock-bounded-steps/` places on the exec function and which `dispatch` and `enter` bound for the entry;
- a conjunct that is `final(self).wf()` or `old(self).wf()`, which `step_ok` states for every step `dispatched` relates (`kernel/verified/capability/kernel.rs`).

Every other conjunct must be carried.

**Carried.** A conjunct is carried in one of these ways. A call carries a conjunct only when the arm's value depends on it.

1. Whole kernel unchanged. The conjunct is `*final(self) == *old(self)` or `final(self) == old(self)`, and the arm's value or its spec function's value contains `post == pre`. A `post == pre` that occurs only in a let binding the value does not use does not count.
2. One call. Strip one leading implication, so `ret ==> P(...)` and `!(ret is Refused) ==> P(...)` leave `P(...)`, and strip a `#[trigger]` on that call. What remains is one call `Name(...)`, `Self::Name(...)`, `old(self).Name(...)`, `final(self).Name(...)` or `self.Name(...)`, and the spec function's value depends on a call of `Name`.
3. Result equals one call. The conjunct is `ret == Name(...)`, `ret == old(self).Name(...)` or `ret == self.Name(...)`, and the spec function's value depends on a call of `Name`.

The value depends on a call when the call is a conjunct of the expression the function returns, or of a disjunct of that expression: a `|||` arm, a `match` arm or an `if` branch. It also depends on a call in a `let` whose name that expression uses, including through a chain of such lets, because the name is how the conjunct names the call. A call in a `let` the value does not use, including `let _x = Name(...)`, is not a conjunct of the arm or of the disjunct for that outcome. The binding is thrown away, and the call does not carry.

A conjunct with two calls, a comparison of fields, or a quantifier is not carried. It becomes one named predicate that both the ensures and the spec function call. That predicate is a `pub open spec fn`, with or without `#[verifier::opaque]`. Opacity does not change what the predicate means: a caller reveals what it needs, and a missing reveal fails verification. A closed or uninterpreted body is not revealable, so it is not how a field is carried. Every body below that predicate is the same, a `pub open spec fn` with or without `#[verifier::opaque]`.

The spec function decodes the frame into the operation's arguments and the `Outcome` into the operation's result. Where one status stands for two results, as revoke's `Refused` and `Exhausted` both return `STATUS_REFUSED`, the arm is a disjunction of two calls of the same predicate. The ensures keeps the operation's own result.

**The check.** `tools/check-invoked-arms.py` reads the tree and takes no list of operations. It reads the name the conjunct calls, not the predicate's body, and it does not walk into helper bodies. A `pub open spec fn` carries, with or without `#[verifier::opaque]`. A call of `Name` is printed when a spec fn of that name is closed or uninterpreted, because a caller cannot reveal it. A closed or uninterpreted helper below the called name is the committer's to keep out: the check does not see it, and every body below the predicate stays one a caller can reveal. The check prints one line `path:function:conjunct` for each conjunct it does not count as carried, the conjunct's text with whitespace collapsed, and exits 0 when it prints nothing. A gate step named `invoked arms` runs it on x86_64 and fails otherwise. The pairing comes from the matches in `invoked` and `dispatch`, so a new arm is checked as soon as both name it.

`lemma_entry_reaches_` shows the status each way, as `design/witness-per-way-an-operation-succeeds/` point 3 asks. A stronger arm keeps that lemma provable. The lemma is not the check: its ensures can drop a field and still verify.

## Context

`invoked` is what `dispatched` gives a caller that received an outcome. The arms were written beside the operations' ensures. `invoke_retype` ensures `spec_retyped`, and `retype_frame` ensures `final(self).flush_epoch == old(self).flush_epoch` beside `ret ==> Self::frame_retyped(...)`. The 4K arm of `spec_retyped` calls `frame_retyped` and does not state the epoch. `revoke` ensures how many nodes an `Again` took and a bound on the flush epoch; `spec_revoked`'s `Again` arm states the count and not the bound. Each gap showed up when a review asked what the entry promises, and the fix added the one field that review named.

## Reasoning

A proof that the arm implies the ensures fails when a field is missing, which is the right direction. The lemma that states the implication can drop the field itself, and then it verifies. The text rule has no second copy to shorten: the ensures conjunct and the arm name the same predicate, or the check prints the conjunct. This is the shape of the witness inventory's rule that a claim counts only when every binding of the name is a call of the operation, `design/witness-per-way-an-operation-succeeds/` point 4.

Opacity keeps a quantifier out of the solver's context. It does not change what the predicate means, and a caller that needs the body writes a reveal; a missing reveal fails verification rather than proving anything false. The predicate the arm and the ensures call is `pub open`, so that reveal is possible, and so is each helper below it. A closed or uninterpreted body has nothing a caller can reveal, so a field that lives only there is not carried.

The entry's step bound is `dispatch`'s and `enter`'s, so the operation's `steps` conjunct stays on the exec function. `step_ok` is every step `dispatched` relates, so an arm does not restate `wf()`. A caller that has only `invoked` does not get `wf()` from the arm. The operation's ensures still states it, and `dispatched` is the spec of a step.

## Alternatives rejected

- **Requiring every body to be open and not opaque, so a caller sees each field with no reveal.** A caller reveals the predicate it needs. Banning opacity puts every helper's quantifiers into every caller's context, and a text check still misses the next shape of the expression.
- **Each review adds the field it found.** The epoch bound, the taken count and the 4K epoch each landed that way, and the arm still had further fields unstated.
- **A lemma whose ensures is a hand copy of the operation's ensures.** Verus checks the copy it is given. A shorter copy verifies.
- **Generating the arm from the ensures text.** The arm decodes a frame and an `Outcome`; the ensures speaks of the operation's own result, a `RevokeStep` or a `bool`. The shared predicate is the part that is the same, and the decoding stays in the arm.
- **Carrying `invoke_*`'s ensures, including `cores` unchanged.** Those conjuncts are the wrapper's. The model operation does not state them, and `invoke_*` proves them. They are accounting around the call of `spec_*`, not part of the operation's postcondition.

## What this does not settle

- What an operation does when the flush epoch is at its limit. The arm carries whatever the ensures says about that case.
- Whether repeating a call that returned again reaches ok, and within what bound.
- `invoke_*`'s conjuncts beside the `spec_*` call: the wrapper's step bound, `wf()`, and `cores` unchanged. A caller of `invoked` does not get `cores` unchanged from the arm.
- Operations the entry does not call. Their postconditions become the entry's when an arm calls them.
