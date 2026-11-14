---
title: "An arm of invoked is the operation's postcondition, one predicate both sides call"
date: 2026-11-14
status: active
tags: [capability, verified, entry]
one_line: "Each arm of invoked carries the postcondition of the operation the entry calls: the arm and the ensures call the same predicates, and a source check holds the pairing."
revisit_if: "A caller that has invoked and not dispatched needs a conjunct the allowlist skips, or a skeptic finds a shared predicate whose body drops a field the ensures used to state beside the call."
confidence: "A judgement about where a postcondition is written, in the form of the text rule in design/witness-per-way-an-operation-succeeds/. The check holds against accident, not against intent, as design/committer-is-not-the-adversary/ sets."
---

# An arm of invoked is the operation's postcondition, one predicate both sides call

## Decision

An arm of `invoked` in `kernel/verified/capability/operation.rs` carries the postcondition of the operation the entry calls for that arm. The postcondition is written once. The operation's `ensures` calls it, and the arm calls it.

**Which operation.** For an arm that calls `spec_retyped`, `spec_derived`, `spec_moved`, `spec_deleted`, `spec_revoked`, `spec_linked`, `spec_mapped`, `spec_unmapped` or `spec_probed`, the operations are the `pub fn` methods of `impl CapKernel` that the matching `invoke_*` function calls on `self`. The check reads those calls from the body. It does not follow them into further calls, and it does not read `invoke_*`'s own ensures.

The last arm of `invoked` is `post == pre && out == spec_outcome(...)`. Its operations are `print`, `power_off` and `inspect`, which `dispatch` calls on `self`. `spec_outcome` is that arm's spec function. `Destroy`, `Send`, `Receive`, `Call` and `ReplyRecv`, which `dispatch` does not call, and a number no operation has, are the constant refusal and `STATUS_UNKNOWN` inside `spec_outcome`. The check reads no model ensures for them.

**Which conjuncts.** The check splits an `ensures` on top-level `&&&`, after collapsing whitespace. It skips two shapes:

- a conjunct that mentions the ghost step counter `steps`, which `design/one-lock-bounded-steps/` places on the exec function and which `dispatch` and `enter` bound for the entry;
- a conjunct that is `final(self).wf()` or `old(self).wf()`, which `step_ok` states for every step `dispatched` relates (`kernel/verified/capability/kernel.rs`).

Every other conjunct must be carried.

**Carried.** A conjunct is carried in one of these ways.

1. Whole kernel unchanged. The conjunct is `*final(self) == *old(self)` or `final(self) == old(self)`, and the arm or its spec function contains `post == pre`.
2. One call. Strip one leading implication, so `ret ==> P(...)` and `!(ret is Refused) ==> P(...)` leave `P(...)`, and strip a `#[trigger]` on that call. What remains is one call `Name(...)`, `Self::Name(...)`, `old(self).Name(...)`, `final(self).Name(...)` or `self.Name(...)`, and the spec function calls `Name`.
3. Result equals one call. The conjunct is `ret == Name(...)`, `ret == old(self).Name(...)` or `ret == self.Name(...)`, and the spec function calls `Name`.

A conjunct with two calls, a comparison of fields, or a quantifier is not carried. It becomes one named `open spec fn`, without `#[verifier::opaque]`, that both the ensures and the spec function call. The body of that predicate is the conjunct, so a caller sees it without a reveal.

The spec function decodes the frame into the operation's arguments and the `Outcome` into the operation's result. Where one status stands for two results, as revoke's `Refused` and `Exhausted` both return `STATUS_REFUSED`, the arm is a disjunction of two calls of the same predicate. The ensures keeps the operation's own result.

**The check.** `tools/check-invoked-arms.py` reads the tree and takes no list of operations. It prints one line `path:function:conjunct` for each conjunct it does not count as carried, the conjunct's text with whitespace collapsed, and exits 0 when it prints nothing. A gate step named `invoked arms` runs it on x86_64 and fails otherwise. The pairing comes from the matches in `invoked` and `dispatch`, so a new arm is checked as soon as both name it.

`lemma_entry_reaches_` shows the status each way, as `design/witness-per-way-an-operation-succeeds/` point 3 asks. A stronger arm keeps that lemma provable. The lemma is not the check: its ensures can drop a field and still verify.

## Context

`invoked` is what `dispatched` gives a caller that received an outcome. The arms were written beside the operations' ensures. `invoke_retype` ensures `spec_retyped`, and `retype_frame` ensures `final(self).flush_epoch == old(self).flush_epoch` beside `ret ==> Self::frame_retyped(...)`. The 4K arm of `spec_retyped` calls `frame_retyped` and does not state the epoch. `revoke` ensures how many nodes an `Again` took and a bound on the flush epoch; `spec_revoked`'s `Again` arm states the count and not the bound. Each gap showed up when a review asked what the entry promises, and the fix added the one field that review named.

## Reasoning

A proof that the arm implies the ensures fails when a field is missing, which is the right direction. The lemma that states the implication can drop the field itself, and then it verifies. The text rule has no second copy to shorten: the ensures conjunct and the arm name the same predicate, or the check prints the conjunct. This is the shape of the witness inventory's rule that a claim counts only when every binding of the name is a call of the operation, `design/witness-per-way-an-operation-succeeds/` point 4.

An opaque predicate both sides call would satisfy the names and hide the field from a caller who does not reveal it. The shared predicate stays open. A leaf that needs a smaller solver context hides a helper the open predicate calls; the field stays in the open body.

The entry's step bound is `dispatch`'s and `enter`'s, so the operation's `steps` conjunct stays on the exec function. `step_ok` is every step `dispatched` relates, so an arm does not restate `wf()`. A caller that has only `invoked` does not get `wf()` from the arm. The operation's ensures still states it, and `dispatched` is the spec of a step.

## Alternatives rejected

- **Each review adds the field it found.** The epoch bound, the taken count and the 4K epoch each landed that way, and the arm still had further fields unstated.
- **A lemma whose ensures is a hand copy of the operation's ensures.** Verus checks the copy it is given. A shorter copy verifies.
- **Generating the arm from the ensures text.** The arm decodes a frame and an `Outcome`; the ensures speaks of the operation's own result, a `RevokeStep` or a `bool`. The shared predicate is the part that is the same, and the decoding stays in the arm.
- **Carrying `invoke_*`'s ensures, including `cores` unchanged.** Those conjuncts are the wrapper's. The model operation does not state them, and `invoke_*` proves them. They are accounting around the call of `spec_*`, not part of the operation's postcondition.

## What this does not settle

- What an operation does when the flush epoch is at its limit. The arm carries whatever the ensures says about that case.
- Whether repeating a call that returned again reaches ok, and within what bound.
- `invoke_*`'s conjuncts beside the `spec_*` call: the wrapper's step bound, `wf()`, and `cores` unchanged. A caller of `invoked` does not get `cores` unchanged from the arm.
- A field hidden by marking the shared predicate opaque. The record forbids the attribute; the check reads names.
- Operations the entry does not call. Their postconditions become the entry's when an arm calls them.
