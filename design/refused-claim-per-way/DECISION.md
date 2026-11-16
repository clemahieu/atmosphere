---
title: "Each way an operation succeeds carries a refused claim of the form for its kind, and a way whose specification admits an unchanged component is exempt"
date: 2026-11-16
status: active
tags: [verified, witness, gate, tools]
one_line: "A state change and an again are refused by an unchanged component meeting the way's postcondition, a query by a result other than the one the state gives, and a pure function by a wrong output, as the round trip does. A way whose specification admits the unchanged component is exempt, quoted from that arm. A claim names the inventory lines it covers; the ways with neither a claim nor an exemption are a list in the tree that only the human lengthens. An entry line is covered by the operations it reaches."
revisit_if: "A claim the table calls a state change verifies, because the specification admits an unchanged component for that way; or the refused step, once the ways have claims, costs more than the verify step it runs beside; or an empty proof whose ensures the requires meet is no longer refused by Verus."
confidence: "The placement of the rows was checked against tools/witness-inventory.py on c9fb16bad228. An in-image boot check is not a row. That a refused postcondition shows the ensures says enough is Verus's. Which form a kind takes, and which ways are exempt, is judgement, argued below. The cost is measured for the one claim the tree holds."
---

# Each way an operation succeeds carries a refused claim of the form for its kind

## Decision

A way is one line of `tools/witness-inventory.py`: an operation and one value of its result type that is not a refusal, as `design/witness-per-way-an-operation-succeeds/` point 1 decides. The claim that the way's postcondition says enough is a false claim under the crate's `refused/`, which `tools/check-refused.py` already runs and passes only when Verus refuses each declared postcondition and nothing else. The form depends on the kind.

The claim is a `proof fn` with an empty body, in its own module under `refused/`, unless the pure form below uses a false value whose proofs are the real ones. Its `requires` are the operation's `requires`. Its `ensures` is the operation's `ensures`, which is what the module declares with `//! refused:`. Verus refuses it at that clause.

| kind | the claim |
|---|---|
| state change | the component the operation writes is unchanged, and the result is this way |
| again | the same, unless the way is exempt |
| query | the state that the specification says gives one result, and the result is another |
| pure | the operation's `ensures` at an output the `ensures` excludes |
| entry | no claim of its own; covered by the operations the line reaches |
| exempt | no claim; the specification's arm admits the unchanged component, and the arm is quoted |

**State change.** The `requires` add that the component is unchanged: `post == pre`, or `*final(self) == *old(self)`, and every buffer the operation writes is unchanged. The result is this way (`ret is Freed`, `ret == true`, `ret is Some`). The caller's view of a memory operation is the same claim on the contract: `pre.wf()`, the call allowed, `post == pre`, and the contract with that status. `enter_flush` is this kind. Its `ensures` holds of an unchanged kernel when the core is already at the epoch, and it requires `final(self).acked(c as int) == final(self).flush_epoch`, so an unchanged kernel whose core is behind the epoch fails it. The `requires` stay the operation's. A premise that keeps only the states where unchanged already works would make the claim verify, and `tools/check-refused.py` would reject the module.

**Again.** The same claim, with the result the `Again` variant. Three ways are exempt instead, below.

**Query.** The specification holds of an unchanged component, and what it claims is the result. The `requires` add a state the specification says gives a result R, and the result in the `ensures` is a different one: `false` where the way is `true` and the slot holds the capability, `None` or another payload where the way is `Some`, `Kept` where a thread should leave. The component is unchanged, since that is the specification's own post for this way.

**Pure.** There is no component to leave unchanged. The `ensures` is the operation's at a wrong output: a producer whose head is not 0 where `Producer::new` ensures 0, `ok != layout_ok(...)` where `check` ensures equality, `p.held() == c.held()` where `held_apart` ensures they differ. A combinator's parse and serialize are the two round-trip postconditions, the form `awire/src/refused/u16_be_le.rs` uses and `design/wire-combinators-written-here/` describes. That module names no inventory line: it is a different type, and it shows the interface. A way of `U16Be` is covered by a claim about `U16Be`. One module may name both the parse line and the serialize line when both clauses are the round trip. `length` is a `Some` of the wrong length, or `None` where the value fits. `Elements::push` is a state change: an unchanged buffer meets `final(self)@ == old(self)@.push(t@)`.

**Entry.** An acall line, and `dispatch` and `enter` of `kernel/verified/capability/operation.rs`, whose one way `Some` is every wired operation. An acall line is covered when every way of every operation the inventory names on that line is covered or exempt. `dispatch` and `enter` are covered when every way of every wired operation is covered or exempt. A line whose arm names no operation is uncovered. An unchanged kernel meets `enter`'s `Some` through `print` and `inspect`, so `enter` is not given the state-change claim.

**Exempt.** The specification's arm for this way is an unchanged component, so the state-change claim verifies and is not written. The exemption is a line of `tools/refused-exempt`:

```
<path>	<operation>	<way>	<clause>
```

The clause is a source line of the operation's file with its indentation, a leading `&&&` and a trailing comma removed, and that text is a line of the file. The three lines today, all in `kernel/verified/capability/reclaim.rs`:

| operation | way | clause |
|---|---|---|
| `reclaim` | `Again` | `ret is Refused \|\| ret is Again ==> *final(self) == *old(self)` |
| `reclaim_frame` | `Again` | `!(ret is Freed) ==> post == pre` |
| `reclaim_large_frame` | `Again` | `!(ret is Freed) ==> post == pre` |

The second clause is `frame_reclaim_answered` and the third is `large_reclaim_answered`, each called from the operation's `ensures`. The free kind's again arm of `retype_contract` in `kernel/verified/capability/caller.rs` asserts `post == pre`. That arm is this fact stated for the entry. It is not an inventory line, and a claim of it is not written. Adding a line to `tools/refused-exempt` is the same decision as lengthening `tools/unrefused`: `tools/land.py` refuses the landing unless `--approve` names the line as `path:operation:way`.

**The tie.** A module's opening comment holds one line per inventory line the claim covers, beside the `//! refused:` lines `tools/check-refused.py` already reads:

```
//! covers: <path>	<operation>	<way>
```

The three fields are the inventory's, separated by tabs. A line is covered when a module that the refused step accepts names it. A module that names an exempt line fails the check. A name that is not an inventory line fails it.

**The list.** `tools/unrefused` holds the inventory lines that are not covered, not exempt and not an entry line the rule above covers. One line per way, the inventory's three fields, tab-separated. The gate step that runs the inventory and reads the `covers` lines fails unless the two sets are equal. A change that covers a way removes its line in the same commit. `tools/land.py` refuses a landing whose list holds a line the base's does not, unless `--approve` names it, as it does for `tools/unwitnessed`. The count is the list's length.

## Where today's lines fall

The rows are 19 entry, 3 exempt, 3 again, 17 query, 76 pure and 70 state change. An in-image boot check is not a row (design/witness-per-way-an-operation-succeeds/).

**Entry, 19.** The 17 acall lines, each of which names an operation. `kernel/verified/capability/operation.rs` `dispatch` `Some` and `enter` `Some`.

**Exempt, 3.** The table above.

**Again, 3.** `retype_large_frame` `Again` (`kernel/verified/capability/retype.rs`), whose arm is `large_frame_zeroing`. `revoke` `Again` (`kernel/verified/capability/revoke.rs`), whose arm shortens the list by `REVOKE_BUDGET`. `suspend` `Again` (`kernel/verified/capability/thread.rs`), whose arm sets a pending stop and sends the IPI.

**Query, 17.** The result is determined by the state, and the specification holds of an unchanged component.

| path | operation | way |
|---|---|---|
| `kernel/verified/capability/console.rs` | `print` | `true` |
| `kernel/verified/capability/power.rs` | `power_off` | `true` |
| `kernel/verified/capability/inspect.rs` | `inspect` | `Some` |
| `kernel/verified/capability/thread.rs` | `read_registers` | `Some` |
| `kernel/verified/capability/thread.rs` | `check_current` | `Kept` |
| `kernel/verified/capability/switch.rs` | `tick` | `Kept` |
| `aring/src/lib.rs` | `Producer::index` | `returns` |
| `aring/src/lib.rs` | `Producer::free` | `returns` |
| `aring/src/lib.rs` | `Producer::slot` | `returns` |
| `aring/src/lib.rs` | `Consumer::index` | `returns` |
| `aring/src/lib.rs` | `Consumer::available` | `returns` |
| `aring/src/lib.rs` | `Consumer::slot` | `returns` |
| `aring/src/lib.rs` | `Consumer::read` | `returns` |
| `amailbox/src/lib.rs` | `Consumer::read` | `returns` |
| `aheap/src/allocator.rs` | `Allocator::has_token` | `true` |
| `afanin/src/lib.rs` | `scan` | `Idle` |
| `afanin/src/lib.rs` | `scan` | `Ready` |

`print` and `power_off` ensure the kernel is unchanged and the `bool` is whether the slot holds the capability. `inspect` and `read_registers` return what the slot holds. `check_current`'s `Kept` ensures `*final(self) == *old(self)` and `ret is Kept == !old(self).must_leave(c as int)`. `tick`'s `Kept` ensures `post == pre` and that no selected thread preempts. `scan`'s `Idle` is every ring having nothing available; `Ready` is the first ring that has a slot. The ring and mailbox reads and `has_token` ensure the result equals a function of the receiver.

**Pure, 76.** Every `awire` line except `awire/src/repeat.rs` `Elements::push` `returns` (66 lines). And these:

| path | operation | way |
|---|---|---|
| `aring/src/lib.rs` | `Producer::new` | `returns` |
| `aring/src/lib.rs` | `Consumer::new` | `returns` |
| `amailbox/src/lib.rs` | `Mailbox::new` | `returns` |
| `amailbox/src/lib.rs` | `held_apart` | `returns` |
| `adivider/src/lib.rs` | `check` | `true` |
| `aheap/src/heap.rs` | `layout_fits` | `true` |
| `aheap/src/heap.rs` | `Heap::new` | `returns` |
| `aheap/src/allocator.rs` | `Allocator::new` | `returns` |
| `aeager/src/allocator.rs` | `new_allocator` | `Ready` |
| `kernel/verified/queue_lock.rs` | `QueueLock::new` | `returns` |

`new_allocator`'s `Ready` ensures `Eager::new_ok` and the fields of the arguments. The claim is a `Ready` where `new_ok` is false.

**State change, 70.** Every remaining line. They are the kernel operations that return a success other than the query, again and exempt rows above (`kernel_init`, `charge`, `delete`, `derive`, `destroy`, the device and retype operations, `map_nested`, `link_at`, `map_at`, `load_space`, `switch_space`, `move_cap`, `signal`, `wait`, `enter_flush`, `acknowledge`, `flush_iommu`, `probe_at`, `reclaim`'s `Freed`, `Unlinked` and `Slice`, `reclaim_frame` and `reclaim_large_frame`'s `Freed`, `retype_large_frame`'s `Done`, `revoke`'s `Done` and `Exhausted`, `tick`'s `Switched` and `Dropped`, `switch_thread`, `check_current`'s `MovedOff`, `enter_boot_thread`, `place`, `start`, `suspend`'s `Suspended`, `write_registers`, `unmap_at`), `QueueLock::acquire` and `QueueLock::release`, the ring and mailbox updates (`Producer::write`, `Producer::publish`, `Consumer::consume`, `Producer::observe`, `Consumer::observe`, and the mailbox's `write`, `publish` and `observe`), `Elements::push`, `Allocator::alloc`, `Allocator::free`, `Allocator::lend`, `Allocator::give_back`, `Heap::alloc`, `Heap::free`, and eager's `new`, `reserve`, `back`, `release` and `release_span`. `probe_at`'s `Some` clears accessed and dirty bits in the table page; the view is unchanged and the words are not. `observe`'s `true` ensures the end moved.

## Context

A witness shows a way is reachable. It says nothing about a postcondition a call that changes nothing also meets, or a result the state does not give. Such a postcondition verifies. The refused step already holds one false claim, the round trip of a combinator that does not invert its parse, in `awire/src/refused/`. The kernel has no `refused/` directory. The caller's contracts in `kernel/verified/capability/caller.rs` are where an unchanged post has met an ok arm.

## Reasoning

The kind is what an unchanged component, or a wrong result, does to the `ensures`. One shape for every way fails on the ways whose specification is the unchanged component: the claim verifies, and the step that expects a refusal rejects the module. The query and the pure function have the same gap in the other direction. An unchanged producer meets `index`'s `ensures` at the head it holds, and a wrong head does not.

The entry is not a second way. `design/witness-per-way-an-operation-succeeds/` point 2 already lists an acall wrapper as the entry seen from user space, covered by the operations its arm calls. `dispatch` and `enter` are the same folding one level down. A claim on `enter`'s `Some` with an unchanged kernel verifies for `print`.

The exemption is quoted because a comment alone would drop a way from the check. The quote is text, as the witness inventory's rule is text: it holds against accident, which is the standard `design/committer-is-not-the-adversary/` sets. The line is approved because an exemption lowers what the check shows, as a new line of `tools/unwitnessed` does.

The `covers` line is the whole tie. The tool does not infer the kind. The table above is the placement a claim is written from, and a new operation is placed by the same rows when its claim is written. Until then the inventory puts it on `tools/unrefused`.

Measured on main `c9fb16bad228`, on this host, an AMD Ryzen 9 9950X3D. `tools/check-refused.py` three times, the one claim in `awire`, two postconditions: wall 0.90 s, 0.93 s, 0.90 s. The gate step runs the script's own tests and then the check. The gate log of that commit records `gate refused: ok in 3.0 s`. Gate logs of the same one claim on this host, with other gates running, record the step from 1.7 s to 5.6 s. The ways that take a claim are not in the tree yet, so their cost is not a number. A claim is an empty proof refused at one clause. The front end is most of today's step.

## Alternatives rejected

- **The unchanged-post claim for every way.** It verifies for `print`, `inspect`, `reclaim`'s `Again` and every pure function, and the refused step then fails on the claim that was meant to pass by being refused.
- **A query claim for an exempt again**, the state that has been acknowledged ensuring `Again`. It is a real check, and it is a second claim on a way whose specified success is the unchanged kernel. The exemption is the decision that the way does not get one.
- **The existing round-trip module covering every combinator.** It is one false `u16`, and a weakened `U16Be` would not disturb it. The interface stays as `design/wire-combinators-written-here/` holds it.
- **An exemption as a comment in the operation, with no line in the tree.** Nothing would record that the human accepted it, and the uncovered list would shrink in the commit that added the comment.
- **Generating the false `ensures` from the operation's text.** The negation of an `ensures` is not one substitution. The author writes the value the kind names, and Verus decides whether the operation's `ensures` rejects it.

## What this does not settle

- An exempt again that answers `Again` after the frame is acknowledged. The quoted clause says the kernel is unchanged on `Again`. It does not say `Again` is refused once the acknowledgement has arrived. That would be the query claim the alternative above rejects.
- Whether a `covers` line names a way whose `ensures` the claim does not use. The refused step sees that Verus refused the declared clause. It does not see that the clause is the operation's. A reviewer does, as with a witness's guard.
- The cost of a claim per way. The number above is one claim.
- A use of several operations in sequence. The unit is the inventory line, as the witness record's is.
