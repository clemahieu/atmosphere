// SPDX-License-Identifier: MIT

//! `Bytes`, a run of `len` bytes. Its exec value borrows the input, so a parse copies nothing and
//! adds no step; its length is the run's, read in no step; a serialisation copies the run a byte per
//! step.

use vstd::slice::slice_subrange;

use crate::*;

verus! {

/// A run of exactly `len` bytes.
pub struct Bytes {
    pub len: usize,
}

impl<'a> Combinator<'a> for Bytes {
    type V = Seq<u8>;

    type T = &'a [u8];

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, Seq<u8>)> {
        if self.len <= s.len() {
            Some((self.len as nat, s.take(self.len as int)))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Seq<u8>) -> Seq<u8> {
        v
    }

    open spec fn valid(&self, v: Seq<u8>) -> bool {
        v.len() == self.len
    }

    open spec fn k(&self) -> nat {
        1
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
    }

    proof fn lemma_serialize_parse(&self, v: Seq<u8>, rest: Seq<u8>) {
        assert((v + rest).take(self.len as int) =~= v);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, &'a [u8])>) {
        if self.len <= input.len() {
            let run = slice_subrange(input, 0, self.len);
            assert(run@ =~= input@.take(self.len as int));
            Some((self.len, run))
        } else {
            None
        }
    }

    fn length(&self, v: &&'a [u8], cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let run: &[u8] = *v;
        if run.len() != self.len || run.len() > cap {
            None
        } else {
            Some(run.len())
        }
    }

    fn serialize(&self, v: &&'a [u8], out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        let run: &[u8] = *v;
        if run.len() != self.len || pos > out.len() || out.len() - pos < run.len() {
            return None;
        }
        let ghost before = out@;
        let ghost count = steps.count;
        let mut i: usize = 0;
        while i < run.len()
            invariant
                i <= run.len(),
                pos + run.len() <= before.len(),
                out@.len() == before.len(),
                out.len() == before.len(),
                out@ == written(before, pos as int, run@.take(i as int)),
                steps.count == count + i,
            decreases run.len() - i,
        {
            out[pos + i] = run[i];
            proof {
                steps.step();
                assert(out@ =~= written(before, pos as int, run@.take(i + 1)));
            }
            i = i + 1;
        }
        assert(run@.take(i as int) =~= run@);
        assert(self.k() * run.len() == run.len()) by (nonlinear_arith)
            requires
                self.k() == 1,
        ;
        Some(run.len())
    }
}

} // verus!
