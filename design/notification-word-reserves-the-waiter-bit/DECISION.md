---
title: "A signal ORs a badge into a notification's word, whose top bit belongs to the kernel and says a thread waits"
date: 2026-11-14
status: active
tags: [ipc, notification, capability]
one_line: "Signal ORs its badge into the word, never blocks and returns only ok or refused; wait returns the word and clears it, blocking while it is zero; the word's bit 63 is the kernel's waiter bit, so a badge uses bits 0 to 62 and a derive that sets bit 63 is refused; a notification may queue several waiters; one-bit badges are the convention for a sender that may later take a hardware path. This keeps a lock-free signal and hardware user interrupts addable without an ABI change."
revisit_if: "A lock-free signal or a user-interrupt path is built and needs a word or a result the kernel path does not give, or a workload needs signal to report whether it woke a thread."
confidence: "The fast paths are not built; the semantics are chosen so that they stay possible, which is reasoned from how a single fetch_or and a 64-bit user-interrupt request word work, not measured."
---

# A notification is a word and a queue, and the word's top bit says a thread waits

## Decision

A notification is a kernel object holding one 64-bit word and a queue of waiting threads. `design/ipc-with-reply-object/` gives its place beside endpoints; this record says what its operations do.

- **Signal** ORs the badge of the capability it is invoked through into the word. It never blocks, and when a thread waits it wakes the first one, which follows the reschedule rule of `design/cpu-time-as-capability/`. It returns ok or refused and nothing else: in particular not whether it woke a thread.
- **Wait** returns the word and clears it. While the word is zero it blocks the caller on the notification's queue.
- **The waiter bit.** Bit 63 of the word belongs to the kernel and is set exactly while a thread waits. A badge uses bits 0 to 62. A derive that sets bit 63 in a notification capability's badge is refused, so no signal can set or clear the waiter bit.
- **Several waiters.** A notification may queue several waiting threads. A signal wakes one of them, and the word is cleared into that thread's wait.
- **One-bit badges** are the convention for a sender that may later want a hardware path. A badge with several bits works on the kernel path.

## Context

Two fast paths are wanted later and must not need an ABI change when they come.

- A signal that skips the kernel lock when nobody waits. Most signals land on a notification no thread is blocked on, typically a ring's wakeup that the consumer checks before it sleeps (`design/fan-in-over-private-rings/`).
- Hardware user interrupts (Intel UINTR). A receiver's descriptor holds a 64-bit request word, and the sender's SENDUIPI ORs one bit into it, chosen by the sender's table entry.

## Reasoning

A lock-free signal must decide, in one atomic step, both that its bits are delivered and whether a thread must be woken. When the waiter state lives in the same word the signal ORs into, one `fetch_or` does both: the bits are in, and the old value's bit 63 says whether to take the lock and wake. A waiter state kept elsewhere needs a second read that races the waiter's block, which brings the lock back. So the waiter bit is in the word from the start, and the badge's range stops at bit 62, which costs one bit nobody has asked for.

Signal reporting whether it woke a thread would tie the fast path to that answer: with the lock skipped, the answer is the old value's bit 63, which a later wait may already have changed, and a hardware path has no answer at all. Ok or refused is what every path can return.

A user interrupt sets exactly one bit of a 64-bit word. A notification whose senders use one-bit badges has a word that a hardware request word can stand in for, with the same meaning for every bit the receiver reads. A multi-bit badge has no hardware equivalent, so it stays a kernel-path convention rather than being refused: a sender that will never take the hardware path loses nothing by it.

Several waiters cost nothing on the kernel path, which already keeps queues over the intrusive list for endpoints. A hardware-backed notification would bind one receiver when it is typed, so the queue does not get in its way.

## Alternatives rejected

- **The waiter state in a separate field.** Every signal would need the lock to read it consistently with a blocking waiter, which is the cost the lock-free path exists to remove.
- **Signal returns whether it woke a thread.** Neither the lock-free path nor a hardware path can give that answer, so it would have to be withdrawn when they come, which is an ABI change.
- **Refuse a badge with more than one bit.** Correct only for senders that want the hardware path; others would lose the ability to say several things in one signal for no gain.
- **One waiter per notification.** Simpler to prove, but a pool of threads serving one event source would need one notification each and a fan-out the queue already gives.

## What this does not settle

- The operation numbers and which result word carries the word wait returns, which `design/syscall-abi-in-registers/` records when signal and wait land. The status word's 48-bit badge field cannot hold a 63-bit word.
- Suppressing signals from user space, so that a producer does not enter the kernel while the consumer is known to be running.
- Whether the lock-free signal is built at all, which waits on measurements of how often a signal finds nobody waiting.
- How an interrupt vector or a core's timer is bound to a notification and with what badge, beyond its binding being a node under the notification capability used (`design/revoke-by-depth-first-list/`).
