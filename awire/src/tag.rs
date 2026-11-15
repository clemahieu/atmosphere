// SPDX-License-Identifier: MIT

//! `Tag`, a constant run of bytes the input must start with, its value the unit: what a format tells
//! its alternatives apart by (an ethertype, an option kind), and what makes the alternatives of a
//! `Choice` disjoint. Comparing and copying the run take a step per byte of it, and its length is
//! read in no step, so the count is a constant of the tag: its `k` is 0 and its `c` the run's length.

use crate::*;

verus! {

/// The bytes `bytes`, exactly.
pub struct Tag<'t> {
    pub bytes: &'t [u8],
}

impl<'a, 't> Combinator<'a> for Tag<'t> {
    type V = ();

    type T = ();

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, ())> {
        if self.bytes@.len() <= s.len() && s.take(self.bytes@.len() as int) == self.bytes@ {
            Some((self.bytes@.len(), ()))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: ()) -> Seq<u8> {
        self.bytes@
    }

    open spec fn valid(&self, v: ()) -> bool {
        true
    }

    open spec fn k(&self) -> nat {
        0
    }

    open spec fn c(&self) -> nat {
        self.bytes@.len()
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
    }

    proof fn lemma_serialize_parse(&self, v: (), rest: Seq<u8>) {
        assert((self.bytes@ + rest).take(self.bytes@.len() as int) =~= self.bytes@);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, ())>) {
        let tag: &[u8] = self.bytes;
        if tag.len() > input.len() {
            return None;
        }
        let ghost count = steps.count;
        let mut i: usize = 0;
        while i < tag.len()
            invariant
                tag@ == self.bytes@,
                tag.len() <= input.len(),
                i <= tag.len(),
                forall|j: int| 0 <= j < i ==> input@[j] == tag@[j],
                count == old(steps).count,
                steps.count == count + i,
            decreases tag.len() - i,
        {
            if input[i] != tag[i] {
                assert(input@.take(tag.len() as int)[i as int] == input@[i as int]);
                return None;
            }
            proof {
                steps.step();
            }
            i = i + 1;
        }
        assert(input@.take(tag.len() as int) =~= tag@);
        Some((tag.len(), ()))
    }

    fn length(&self, _v: &(), cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        if self.bytes.len() > cap {
            None
        } else {
            Some(self.bytes.len())
        }
    }

    fn serialize(&self, _v: &(), out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let tag: &[u8] = self.bytes;
        if pos > out.len() || out.len() - pos < tag.len() {
            return None;
        }
        let ghost before = out@;
        let ghost count = steps.count;
        let mut i: usize = 0;
        while i < tag.len()
            invariant
                tag@ == self.bytes@,
                i <= tag.len(),
                pos + tag.len() <= before.len(),
                out@.len() == before.len(),
                out.len() == before.len(),
                out@ == written(before, pos as int, tag@.take(i as int)),
                steps.count == count + i,
            decreases tag.len() - i,
        {
            out[pos + i] = tag[i];
            proof {
                steps.step();
                assert(out@ =~= written(before, pos as int, tag@.take(i + 1)));
            }
            i = i + 1;
        }
        assert(tag@.take(i as int) =~= tag@);
        Some(tag.len())
    }
}

} // verus!
