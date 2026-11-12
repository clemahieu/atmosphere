---
title: "The network protocol stack is tier 1, built from proven combinators with fixed nesting, linear work, transitions equal to their specifications and no allocation per packet"
date: 2026-11-10
status: active
tags: [network, tiers, verified, parsing]
one_line: "The network protocol stack is tier 1 required, written in Rust inside Verus with no unverified protocol library: wire formats only through combinators proven once, nesting depths fixed in each format, per-packet work bounded linearly in the packet's length by a ghost step counter, each protocol a transition equal to a specification of its RFC state machine, and no allocation per packet."
revisit_if: "A wire format the stack must accept cannot be written in the combinators under a fixed nesting bound, or a format written in them still needs a proof as large as a hand-written parser's, which reopens rule 1; lowering the tier is the human's decision."
confidence: "The tier is the human's choice, made 2026-11-10. The five rules are a judgement on how to make a tier-1 stack affordable; the first formats written in the combinators settle whether the per-format proof is as small as expected."
---

# The network protocol stack is proven at tier 1

## Decision

The network protocol stack is tier 1 required, not a tier-1 target with tier 2 accepted meanwhile. The stack is the wire formats, the protocol transitions and the socket state the network service process exposes to its clients. It is written in Rust inside Verus, using only language features and std functions that vstd specifies or the tree proves. No unverified protocol library is in it.

Five rules shape it:

1. **Proven combinators.** Every wire format is parsed and serialised only through a combinator library whose properties are proven once per combinator: it ends, it consumes at most its input, it accepts or refuses every byte string, and serialising inverts parsing. A format written in the combinators inherits these properties. No parser in the stack is written by hand.
2. **Fixed nesting.** Each format states the depth of everything a sender can nest or repeat: VLAN tags, IPv6 extension headers, IP and TCP options. Bounded repetition takes its bound as a parameter, and a packet past a bound is refused, so depth is never something a loop merely happens to handle.
3. **Linear work.** Per-packet work is bounded linearly in the packet's length, `steps <= k * len + c`, by a ghost step counter in each parser's and transition's postcondition, the way `design/one-lock-bounded-steps/` bounds the kernel's operations. A hostile packet costs no more than its size.
4. **Transitions equal to their specifications.** Each protocol is a function `(state, packet or request or timer) -> (state, outputs)` that ensures its result equals a specification function written from the RFC's state machine. Determinism is that equality, and each refusal is specified.
5. **No allocation per packet.** Flow and buffer state come from a pool fixed when the service is created, from the memory it was given (`design/untyped-memory/`).

## Context

The stack was a tier-1 target that accepted tier 2: smoltcp, unverified, behind Verus specifications at the service boundary. The network stack is where input controlled by an attacker arrives, with a length and a nesting depth the sender chooses. Tier 2 is coverage: it says the tests reached every branch, and gives no termination, no bound on the work a packet causes, and no statement of which packets are refused. The first real workload, a nano node, needs TCP and UDP, so the stack is on the path to it either way.

## Reasoning

P4, the language for programmable switches, gets bounded work, explicit refusal and no allocation by making the violations inexpressible: no loops in its control blocks, fixed-size header stacks, a reject state. Its parsers' termination is still left to the compiler's target, and its guarantees rest on that compiler and on unverified externs. Verus gives the same properties by proof, and a combinator library makes that proof cheap: termination, the bound on bytes consumed, total acceptance or refusal and the round trip are proven once per combinator rather than once per format. That is P4's by-construction ergonomics with a proof underneath instead of a trusted compiler.

The kernel needed none of rules 1 to 3 because its inputs are fixed-shape registers (`design/syscall-abi-in-registers/`). The rest of the framework already holds what the stack needs besides: the step counter, the pool a component is given, and the tier-1 rule that a specification says exactly when an operation refuses. Stating each protocol as a transition gives the stack the shape of the kernel's own operations, and a parser's specification becomes a lemma for the protocol above it, which a separately tested parser cannot be.

## Alternatives rejected

- **smoltcp behind boundary specifications, at tier 2 meanwhile.** Specifications at the service boundary say what the service promises its clients, not that a packet cannot make the stack loop, panic or take unbounded time. The code that reads hostile input would carry no proof.
- **The parsing layer at tier 1 and the protocol logic at tier 2.** It proves the layer where hostile bytes arrive and leaves the state machines to coverage; coverage of TCP says the tests reached each branch, not that the transitions are the RFC's.
- **A packet language with a trusted compiler, as P4 is.** The trust moves into the compiler and its externs, outside the counted `external_body` list, and its parsers' termination rests on the target.
- **No loops, as P4's control blocks have none.** Verus proves loops end, and the step counter bounds them.
- **Hand-written parsers, each with its own proof.** Every format would repeat the termination, bound and round-trip proofs that the combinators prove once.

## What this does not settle

- Whether the combinators come from an existing Verus combinator library or are written in the tree. A library's license is checked and recorded before its source is read.
- The constants of each step bound. The counter counts what the code tells it to count: it is a model of cost, not of cycles, and the stack depth of the code is not reasoned about.
- The virtio-net driver, whose access to the device is a hardware guarantee, `design/who-vouches-for-an-unproven-claim/`.
- Protocols above TCP and UDP, which this record does not cover.
- The filesystem stack's tier, which stays a tier-1 target with tier 2 accepted.
