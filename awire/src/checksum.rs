// SPDX-License-Identifier: MIT

//! RFC 1071 16-bit ones'-complement internet checksum over byte strings.
//!
//! `spec_checksum` pairs adjacent bytes in big-endian order, padding an odd trailing byte on the
//! right with zero, and folds their sum into 16 bits with end-around carry (`0` stays `0`, any
//! positive sum folds modulo `0xffff` into `1..=0xffff`). `checksum` computes it over a slice in
//! linear steps (`k = 1`, `c = 0`), `fold_add` adds two 16-bit ones'-complement sums,
//! `lemma_checksum_append` splits an even-length prefix (such as a pseudo-header) from what follows,
//! and `lemma_checksum_fill` proves that writing the bitwise complement of the zeroed sum into a
//! 16-bit field at an even offset makes the whole string sum to `0xffff`.

use crate::*;

verus! {

/// Steps per byte of `checksum`.
pub open spec fn checksum_k() -> nat {
    1
}

/// Constant steps of `checksum`.
pub open spec fn checksum_c() -> nat {
    0
}

/// The un-folded sum of big-endian 16-bit words of `s`, padding an odd trailing byte with zero.
pub open spec fn spec_raw_sum(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        be16(s[0], 0u8) as nat
    } else {
        be16(s[0], s[1]) as nat + spec_raw_sum(s.skip(2))
    }
}

/// Folds a non-negative integer into a 16-bit ones'-complement sum (`0` stays `0`; any positive
/// sum folds modulo `0xffff` into `1..=0xffff`).
pub open spec fn spec_fold(n: nat) -> u16 {
    if n == 0 {
        0
    } else {
        (((n - 1) % 0xffff) + 1) as u16
    }
}

/// The 16-bit ones'-complement sum of two 16-bit words with end-around carry.
pub open spec fn spec_fold_add(a: u16, b: u16) -> u16 {
    spec_fold(a as nat + b as nat)
}

/// The 16-bit ones'-complement sum of `s` (RFC 1071): big-endian 16-bit words summed with
/// end-around carry, an odd final byte padded on the right with zero.
pub open spec fn spec_checksum(s: Seq<u8>) -> u16 {
    spec_fold(spec_raw_sum(s))
}

proof fn lemma_fold_split(n: nat) -> (q: nat)
    ensures
        n == 0 <==> spec_fold(n) == 0,
        n > 0 ==> 1 <= spec_fold(n) <= 0xffff,
        n == q * 0xffff + spec_fold(n),
{
    if n == 0 {
        0
    } else {
        let m: nat = (n - 1) as nat;
        let q: nat = m / 0xffff;
        let r: nat = m % 0xffff;
        assert(m == q * 0xffff + r) by (nonlinear_arith)
            requires
                q == m / 0xffff,
                r == m % 0xffff,
        ;
        assert(n == q * 0xffff + (r + 1));
        q
    }
}

proof fn lemma_fold_u16(w: u16)
    ensures
        spec_fold(w as nat) == w,
{
    if w > 0 {
        let m: nat = (w - 1) as nat;
        assert(m % 0xffff == m) by (nonlinear_arith)
            requires
                m < 0xffff,
        ;
    }
}

proof fn lemma_fold_add_raw(x: nat, y: nat)
    ensures
        spec_fold(x + y) == spec_fold(spec_fold(x) as nat + spec_fold(y) as nat),
{
    let qx = lemma_fold_split(x);
    let qy = lemma_fold_split(y);
    if x == 0 && y > 0 {
        let fy = spec_fold(y) as nat;
        assert((fy - 1) % 0xffff == fy - 1) by (nonlinear_arith)
            requires
                1 <= fy,
                fy <= 0xffff,
        ;
    } else if y == 0 && x > 0 {
        let fx = spec_fold(x) as nat;
        assert((fx - 1) % 0xffff == fx - 1) by (nonlinear_arith)
            requires
                1 <= fx,
                fx <= 0xffff,
        ;
    } else if x > 0 && y > 0 {
        let fx = spec_fold(x) as nat;
        let fy = spec_fold(y) as nat;
        assert(x + y - 1 == (qx + qy) * 0xffff + (fx + fy - 1)) by (nonlinear_arith)
            requires
                x == qx * 0xffff + fx,
                y == qy * 0xffff + fy,
                1 <= fx,
                1 <= fy,
        ;
        assert((((qx + qy) * 0xffff + (fx + fy - 1)) as nat) % 0xffff == ((fx + fy - 1) as nat) % 0xffff) by (nonlinear_arith)
            requires
                1 <= fx,
                1 <= fy,
        ;
    }
}

proof fn lemma_raw_sum_append(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() % 2 == 0,
    ensures
        spec_raw_sum(a + b) == spec_raw_sum(a) + spec_raw_sum(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b)[1] == a[1]);
        assert((a + b).skip(2) =~= a.skip(2) + b);
        lemma_raw_sum_append(a.skip(2), b);
    }
}

/// Adds two 16-bit ones'-complement sums with end-around carry.
pub fn fold_add(a: u16, b: u16) -> (r: u16)
    ensures
        r == spec_fold_add(a, b),
{
    let sum: u32 = a as u32 + b as u32;
    assert((sum & 0xffffu32) <= 0xffffu32 && (sum >> 16u32) <= 1u32) by (bit_vector)
        requires
            sum <= 0x1_fffeu32,
    ;
    let lo: u16 = (sum & 0xffffu32) as u16;
    let hi: u16 = (sum >> 16u32) as u16;
    assert(sum == (hi as u32) * (0xffffu32 + 1u32) + (lo as u32) && (hi == 1u16 ==> lo <= 0xfffeu16)) by (bit_vector)
        requires
            sum <= 0x1_fffeu32,
            lo == (sum & 0xffffu32) as u16,
            hi == (sum >> 16u32) as u16,
    ;
    let r = lo + hi;
    proof {
        if sum == 0 {
        } else if hi == 0 {
            assert(((sum - 1) as nat) % 0xffff == (sum - 1) as nat) by (nonlinear_arith)
                requires
                    1 <= sum,
                    sum <= 0xffff,
            ;
        } else {
            assert(((sum - 1) as nat) % 0xffff == (sum - 0xffff - 1) as nat) by (nonlinear_arith)
                requires
                    0xffff < sum,
                    sum <= 0x1_fffe,
            ;
        }
    }
    r
}

/// Computes the 16-bit ones'-complement sum of `data`, adding at most `checksum_k() * data.len() + checksum_c()` steps.
pub fn checksum(data: &[u8], Tracked(steps): Tracked<&mut Steps>) -> (r: u16)
    ensures
        r == spec_checksum(data@),
        final(steps).count <= old(steps).count + checksum_k() * data.len() + checksum_c(),
{
    let ghost count = steps.count;
    let mut acc: u16 = 0;
    let mut i: usize = 0;
    assert(data@.take(0) =~= Seq::<u8>::empty());
    while data.len() - i >= 2
        invariant
            i <= data.len(),
            i % 2 == 0,
            acc == spec_checksum(data@.take(i as int)),
            steps.count <= count + i,
        decreases data.len() - i,
    {
        let word: u16 = ((data[i] as u16) << 8u16) | (data[i + 1] as u16);
        proof {
            let prefix = data@.take(i as int);
            let pair_seq = seq![data@[i as int], data@[i + 1]];
            assert(data@.take((i + 2) as int) =~= prefix + pair_seq);
            assert(pair_seq.skip(2) =~= Seq::<u8>::empty());
            assert(spec_raw_sum(pair_seq.skip(2)) == 0nat);
            assert(spec_raw_sum(pair_seq) == word as nat);
            lemma_fold_u16(word);
            assert(spec_checksum(pair_seq) == word);
            lemma_checksum_append(prefix, pair_seq);
        }
        acc = fold_add(acc, word);
        proof {
            steps.step();
        }
        i = i + 2;
    }
    if i < data.len() {
        let b: u8 = data[i];
        let word: u16 = (b as u16) << 8u16;
        assert(word == be16(b, 0u8)) by (bit_vector)
            requires
                word == ((b as u16) << 8u16),
        ;
        proof {
            let prefix = data@.take(i as int);
            let tail_seq = seq![b];
            assert(data@.take((i + 1) as int) =~= prefix + tail_seq);
            assert(data@ =~= data@.take((i + 1) as int));
            lemma_fold_u16(word);
            assert(spec_checksum(tail_seq) == word);
            lemma_checksum_append(prefix, tail_seq);
        }
        acc = fold_add(acc, word);
        proof {
            steps.step();
        }
    } else {
        assert(data@.take(i as int) =~= data@);
    }
    acc
}

/// The sum of two byte strings, the first of even length, is the folded sum of their sums.
pub proof fn lemma_checksum_append(a: Seq<u8>, b: Seq<u8>)
    requires
        a.len() % 2 == 0,
    ensures
        spec_checksum(a + b) == spec_fold_add(spec_checksum(a), spec_checksum(b)),
{
    lemma_raw_sum_append(a, b);
    lemma_fold_add_raw(spec_raw_sum(a), spec_raw_sum(b));
}

proof fn lemma_complement_sum(v: u16)
    ensures
        (v as nat) + ((!v) as nat) == 0xffffnat,
{
    assert((v as nat) + ((!v) as nat) == 0xffffnat) by (bit_vector);
}

proof fn lemma_be16_serialize_value(v: u16)
    ensures
        be16(U16Be.spec_serialize(v)[0], U16Be.spec_serialize(v)[1]) == v,
{
    assert(((((v >> 8u16) as u8) as u16) << 8u16) | ((v as u8) as u16) == v) by (bit_vector);
}

proof fn lemma_be16_zero()
    ensures
        be16(0u8, 0u8) == 0u16,
{
    assert((0u16 << 8u16) | 0u16 == 0u16) by (bit_vector);
}

/// Writing the complement of the sum taken with the 16-bit field zero into that field at an even
/// offset makes the whole string sum to `0xffff`.
pub proof fn lemma_checksum_fill(s: Seq<u8>, offset: int)
    requires
        0 <= offset,
        offset % 2 == 0,
        offset + 2 <= s.len(),
    ensures
        ({
            let zeroed = written(s, offset, seq![0u8, 0u8]);
            let csum = !spec_checksum(zeroed);
            spec_checksum(written(s, offset, U16Be.spec_serialize(csum))) == 0xffffu16
        }),
        (s[offset] == 0 && s[offset + 1] == 0) ==> ({
            let csum = !spec_checksum(s);
            spec_checksum(written(s, offset, U16Be.spec_serialize(csum))) == 0xffffu16
        }),
{
    let prefix = s.take(offset);
    let suffix = s.skip(offset + 2);
    let zero_field = seq![0u8, 0u8];
    let zeroed = written(s, offset, zero_field);
    assert(zeroed =~= prefix + (zero_field + suffix));
    lemma_raw_sum_append(prefix, zero_field + suffix);
    assert((zero_field + suffix).skip(2) =~= suffix);
    lemma_be16_zero();
    assert(spec_raw_sum(zeroed) == spec_raw_sum(prefix) + spec_raw_sum(suffix));

    let csum = !spec_checksum(zeroed);
    let csum_bytes = U16Be.spec_serialize(csum);
    let filled = written(s, offset, csum_bytes);
    assert(filled =~= prefix + (csum_bytes + suffix));
    lemma_raw_sum_append(prefix, csum_bytes + suffix);
    assert((csum_bytes + suffix).skip(2) =~= suffix);
    lemma_be16_serialize_value(csum);
    assert(spec_raw_sum(filled) == spec_raw_sum(zeroed) + csum as nat);

    lemma_complement_sum(spec_checksum(zeroed));
    let r = spec_raw_sum(zeroed);
    let q = lemma_fold_split(r);
    if r == 0 {
        assert(spec_raw_sum(filled) == 0xffffnat);
        assert((0xffffnat - 1) % 0xffff == 0xfffe) by (nonlinear_arith);
    } else {
        assert(spec_raw_sum(filled) == (q + 1) * 0xffff) by (nonlinear_arith)
            requires
                r == q * 0xffff + spec_checksum(zeroed),
                spec_raw_sum(filled) == r + (0xffff - spec_checksum(zeroed)),
        ;
        assert((((q + 1) * 0xffff - 1) as nat) % 0xffff == 0xfffe) by (nonlinear_arith);
    }

    if s[offset] == 0 && s[offset + 1] == 0 {
        assert(zeroed =~= s);
    }
}

/// RFC 1071 Section 3 numerical example: `00 01 f2 03 f4 f5 f6 f7` sums to `0xddf2`.
proof fn lemma_rfc1071_section_3()
    ensures
        spec_checksum(seq![0x00u8, 0x01u8, 0xf2u8, 0x03u8, 0xf4u8, 0xf5u8, 0xf6u8, 0xf7u8]) == 0xddf2u16,
{
    let s0 = seq![0x00u8, 0x01u8, 0xf2u8, 0x03u8, 0xf4u8, 0xf5u8, 0xf6u8, 0xf7u8];
    let s1 = s0.skip(2);
    let s2 = s1.skip(2);
    let s3 = s2.skip(2);
    let s4 = s3.skip(2);
    assert(s4 =~= Seq::<u8>::empty());
    assert(be16(0x00u8, 0x01u8) == 0x0001u16) by (bit_vector);
    assert(be16(0xf2u8, 0x03u8) == 0xf203u16) by (bit_vector);
    assert(be16(0xf4u8, 0xf5u8) == 0xf4f5u16) by (bit_vector);
    assert(be16(0xf6u8, 0xf7u8) == 0xf6f7u16) by (bit_vector);
    assert(spec_raw_sum(s4) == 0nat);
    assert(spec_raw_sum(s3) == 0xf6f7nat);
    assert(spec_raw_sum(s2) == 0xf4f5nat + 0xf6f7nat);
    assert(spec_raw_sum(s1) == 0xf203nat + 0xf4f5nat + 0xf6f7nat);
    assert(spec_raw_sum(s0) == 0x2ddf0nat);
    assert((0x2ddf0nat - 1) % 0xffff == 0xddf1) by (nonlinear_arith);
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    verus! {
        fn run_checksum(data: &[u8]) -> u16 {
            let tracked mut steps = Steps::fresh();
            checksum(data, Tracked(&mut steps))
        }
    }

    #[test]
    fn rfc1071_section_3_example() {
        let bytes = [0x00u8, 0x01, 0xf2, 0x03, 0xf4, 0xf5, 0xf6, 0xf7];
        assert_eq!(run_checksum(&bytes), 0xddf2);
    }

    #[test]
    fn empty_and_odd_and_carry_cases() {
        assert_eq!(run_checksum(&[]), 0x0000);
        assert_eq!(run_checksum(&[0x00]), 0x0000);
        assert_eq!(run_checksum(&[0x12]), 0x1200);
        assert_eq!(run_checksum(&[0x00, 0x01, 0x02]), 0x0201);
        assert_eq!(run_checksum(&[0xff, 0xff]), 0xffff);
        assert_eq!(run_checksum(&[0xff, 0xff, 0xff, 0xff]), 0xffff);
        assert_eq!(run_checksum(&[0xff, 0xff, 0x00, 0x00]), 0xffff);
        assert_eq!(run_checksum(&[0x00, 0x00, 0xff, 0xff]), 0xffff);
    }

    #[test]
    fn filled_checksum_verifies_for_even_and_odd_and_zero_inputs() {
        let cases: [(&[u8], usize); 5] = [
            (&[0x00, 0x00], 0),
            (&[0x00, 0x00, 0x00], 0),
            (&[0xff, 0xff, 0x00, 0x00], 2),
            (&[0x00, 0x00, 0x00, 0x01, 0xf2, 0x03, 0xf4, 0xf5, 0xf6, 0xf7], 0),
            (&[0x45, 0x00, 0x00, 0x3c, 0x1c, 0x46, 0x40, 0x00, 0x40, 0x06, 0x00, 0x00, 0xac, 0x10, 0x0a, 0x63, 0xac, 0x10, 0x0a, 0x0c], 10),
        ];
        for (idx, (base, offset)) in cases.iter().enumerate() {
            let sum = run_checksum(base);
            let csum = !sum;
            let mut pkt = base.to_vec();
            pkt[*offset] = (csum >> 8) as u8;
            pkt[*offset + 1] = csum as u8;
            assert_eq!(run_checksum(&pkt), 0xffff, "case {idx} failed");
        }
    }

    #[test]
    fn append_splits_even_prefix() {
        let pseudo = [0xc0u8, 0xa8, 0x01, 0x01, 0xc0, 0xa8, 0x01, 0x02, 0x00, 0x11, 0x00, 0x0b];
        let udp = [0x1f, 0x90, 0x00, 0x35, 0x00, 0x0b, 0x00, 0x00, b'a', b'b', b'c'];
        let mut combined = pseudo.to_vec();
        combined.extend_from_slice(&udp);
        assert_eq!(
            run_checksum(&combined),
            fold_add(run_checksum(&pseudo), run_checksum(&udp))
        );
    }
}
