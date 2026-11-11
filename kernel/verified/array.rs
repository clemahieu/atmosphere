// SPDX-License-Identifier: MIT

use vstd::prelude::*;
verus! {
pub struct Array<A, const N: usize>{
    pub seq: Ghost<Seq<A>>,
    pub ar: [A;N]
}

impl<A: Copy, const N: usize> Array<A, N> {
    /// An array with every element fill.
    pub fn new(fill: A) -> (ret: Self)
        ensures
            ret.wf(),
            forall|i: int| 0 <= i < N ==> #[trigger] ret@[i] == fill,
    {
        let ar = [fill; N];
        Self { ar, seq: Ghost(ar@) }
    }
}

impl<A, const N: usize> Array<A, N> {

    pub fn get(&self, i: usize) -> (out: &A)
        requires
            0 <= i < N,
            self.wf(),
        ensures
            *out == self.seq@[i as int],
    {
        &self.ar[i]
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A
        recommends self.seq@.len() == N,
                   0 <= i < N,
    {
        self.seq@[i]
    }

    #[verifier(inline)]
    pub open spec fn view(&self) -> Seq<A>{
        self.seq@
    }

    pub open spec fn wf(&self) -> bool{
        &&& self.seq@.len() == N
        &&& self.seq_matches_array()
    }

    /// The ghost sequence the proofs read is what the array holds.
    pub closed spec fn seq_matches_array(&self) -> bool {
        self.seq@ =~= self.ar@
    }

}

impl<A, const N: usize> Array<A, N> {
    pub fn set(&mut self, i: usize, out: A)
        requires
            0 <= i < N,
            old(self).wf(),
        ensures
            final(self).seq@ =~= old(self).seq@.update(i as int, out),
            final(self).wf(),
    {
        self.ar[i] = out;
        proof {
            self.seq = Ghost(self.ar@);
        }
    }
}

}
