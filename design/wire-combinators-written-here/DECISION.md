---
title: "The wire combinators are written in the tree, after Vest's specification shape, with the step counter and no allocation in the interface"
date: 2026-11-15
status: active
tags: [network, parsing, verified]
one_line: "The parser and serialiser combinators every wire format is written in are a verified crate in the tree, awire, not a dependency on Vest: one trait whose spec parse is total over byte strings and whose exec parse and serialise ensure equality with it, the bytes consumed within the input, both round trips, and a ghost step count linear in the bytes read; values borrow the input and repetition has a fixed capacity, so nothing allocates."
revisit_if: "Vest, or another Verus combinator library under a copy-permissive license, takes a step bound and fixed-capacity repetition into its interface and builds against the Verus this workspace pins, so adopting it costs less than keeping awire; or the combinators written here grow past what the formats need into a second Vest."
confidence: "A judgement on cost. Vest's absences (the counter, allocation-free repetition, its trusted byte conversions, its own vstd release) were read from its source at dbe198ca297e; that writing six combinators here costs less than adapting Vest's 31,000 lines of core and combinators is a bet the first combinator leaves settle."
---

# The wire combinators are written in the tree

## Decision

The combinators of `design/network-stack-proven-at-tier-1/`, rule 1, are a workspace crate written here, `awire`, marked verified, under MIT like the rest of the tree. It holds the six combinators the stack's formats need: fixed-width unsigned integers in each byte order, byte runs of a length given as a parameter, sequence, choice, length-prefixed and bounded repetition. Its specification shape follows Vest (github.com/secure-foundations/vest, MIT), the Verus combinator library of the Secure Foundations Lab: a total spec parse returning the bytes consumed and a value, exec functions proven equal to it, and round-trip theorems. No Vest code is copied or depended on.

Every combinator implements one trait:

- `spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, Self::V)>`. It is defined on every byte string, so each is accepted, with the bytes consumed and the value, or refused.
- `spec fn spec_serialize(&self, v: Self::V) -> Seq<u8>` and `spec fn valid(&self, v: Self::V) -> bool`, the values the format can carry: a byte run's of its length, a repetition's of at most its bound, a length-prefixed value's whose length fits its integer.
- `spec fn wf(&self) -> bool`, the parameters the combinator was built with being usable, which each exec function requires.
- The properties, proof functions proven once per combinator and, for sequence, choice, length-prefixed and repetition, from those of their parts for any parts that meet the trait. `spec_parse(s) == Some((n, v))` implies `n <= s.len()`, `valid(v)` and `spec_serialize(v) == s.take(n)`: parsing consumes at most its input and serialising gives back exactly the bytes parsed. And `valid(v)` implies `spec_parse(spec_serialize(v) + rest) == Some((spec_serialize(v).len(), v))` for every `rest`: a serialised value parses back to itself whatever follows it, which is what sequence needs of its first part and choice of its alternatives.
- `fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, Self::T)>)`, with `Self::T: View<V = Self::V>`. It ensures its result is the spec parse of `input@`, with each conjunct of the properties above stated again on `r` so a caller needs no lemma call, and that `steps.count` rose by at most `K * n + C` when it consumed `n` bytes and by at most `K * input.len() + C` when it refused, `K` and `C` constants of the combinator's specification. It has no `exec_allows_no_decreases_clause`, so Verus proves it ends.
- `fn length(&self, v: &Self::T, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>)`. It returns `spec_serialize(v@).len()` exactly when `v@` is `valid` and that length is at most `cap`, and `None` otherwise, its count rising by at most `K * n + C` when it returned `n` and `K * cap + C` when it refused. A composite whose parts are written one after another (sequence, repetition, length-prefixed) asks it of each part, within the room left, before writing any: once a part's bytes are written the bytes they replaced are gone, so checking first is the only way its serialise can refuse leaving `out` as it was.
- `fn serialize(&self, v: &Self::T, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>)`. It writes `spec_serialize(v@)` at `pos` and returns its length, leaving every other byte of `out` as it was, or refuses, leaving `out` as it was, exactly when `v@` is not `valid` or the bytes do not fit; its count is bounded the same way by the bytes it writes, and by `K * room + C` when it refused, `room` the bytes of `out` from `pos` on, since a composite's refusal is found by asking its parts' lengths within that room.

`Steps` is the crate's own ghost counter, the shape `design/one-lock-bounded-steps/` gives the kernel's: one unit per iteration of an exec loop, a callee's units adding to its caller's. A refusal is charged the input's length, or the room it was given, because a refusal ends the parse or the serialisation of the whole packet, so a format is charged it once. Bounded repetition requires its part to consume at least one byte on each element, so its iterations are at most the bytes it reads and its count is linear in them whatever its bound.

The properties are stated strongly enough to refuse a combinator that breaks them, and the tree keeps one to show it: `awire/src/refused/` holds a `u16` parsed big-endian and serialised little-endian, whose proofs are those a big-endian serialiser verifies with, compiled only under `cfg(refused)`. The gate's refused step, `tools/check-refused.py`, runs Verus on it and passes only when Verus refuses it at the two round-trip postconditions and nowhere else. Each property of a parse is its own ensures clause, so a refusal names the one it fails.

Nothing allocates (rule 5). A byte run's exec value borrows the input, `&'a [u8]`, and copies nothing. A repetition's value has the capacity of its bound, fixed when the format is written, and the bound is a parameter of the format, as rule 2 asks. Integers are assembled from bytes by shifts the bit-vector solver proves, with no call to `from_be_bytes` or its kin, so the crate has no `external_body` and no assumed specification.

## Context

`design/network-stack-proven-at-tier-1/` left open whether the combinators come from an existing Verus combinator library or are written here. Vest is the one such library: MIT, maintained, and the combinator layer of Verdict, the verified X.509 validator (Apache-2.0). Its license was checked and recorded before its source was read. A dependency the stack's proofs rest on has to meet every rule of that record and the tree's rules on what is trusted, so the question was what adopting it would cost.

## Reasoning

Read at commit dbe198ca297e, Vest's specification shape is the one the stack wants, and it is taken: a total spec parse into consumed length and value, exec functions proven equal to it, and a theorem for each direction of the round trip. Adopting the library itself would cost more than writing the six combinators.

- It has no step counter. Rule 3 bounds every parser's work in its postcondition, so the counter would have to be threaded through every exec function of the library.
- Its repetition collects into a `Vec`, which allocates per packet, against rule 5.
- Its integer and byte-array combinators rest on twenty-five `external_body` functions around `from_le_bytes`, `to_be_bytes` and their kin, and an assumed specification of `TryFrom` for arrays; its fixed-count repetition on two more. In this tree each of those is proof debt or a claim someone vouches for (`design/who-vouches-for-an-unproven-claim/`), and the network epic's criterion allows no `external_body` outside the driver glue.
- It builds against the vstd release it names on crates.io, while the workspace pins one Verus commit for every crate (`tools/setup-verus.sh`). A dependency on it would move that pin on Vest's schedule.
- Its properties are traits a format opts into, with invariants, beside the exec functions, and its core and combinators are about 31,000 lines beside ASN.1 and CBOR support the stack does not use. The stack needs six combinators whose exec functions carry the properties themselves.

Writing them here keeps every proof under the tree's gate and its counts, and leaves the interface free to carry rules 2, 3 and 5 from the first combinator.

## Alternatives rejected

- **Vest as a dependency.** The counter, the allocation-free repetition and the removal of its trusted conversions would be changes to a library we do not own, and its trust would sit outside `tools/external-body-list`.
- **A copy of Vest's core and combinators, adapted.** The adaptation touches every exec function, so the copy would be a fork from the first commit, tens of thousands of lines kept in step with an upstream it no longer resembles.
- **The properties as lemmas only, with exec functions ensuring just equality with the spec.** Each caller would call the lemmas itself; stating the properties on the result costs one proof per combinator and saves one at every use.
- **A step bound linear in the input on success too.** A sequence of fixed-width fields over a long packet would be charged the packet once per field, which is quadratic for the format.

## What this does not settle

- The constants `K` and `C` of each combinator, which its leaf proves.
- Combinators beyond the six, such as a tail that takes the rest of the input or a checksum; each is added when a format needs it, with the same trait.
- Whether a repetition's value is an array with a count or a view that parses its elements again on access; either keeps the capacity of the bound and allocates nothing.
- The wire formats themselves, and how each states its nesting bounds.
