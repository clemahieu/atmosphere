use vstd::prelude::*;

verus! {

use crate::define::*;
use crate::util::page_ptr_util_u::*;

#[derive(Clone, Copy)]
pub struct VaRange4K {
    pub start: VAddr,
    pub len: usize,
    pub view: Ghost<Seq<VAddr>>,
}

impl VaRange4K {
    pub proof fn va_range_lemma(&self)
        requires
            self.wf(),
        ensures
            forall|i: usize|
                0 <= i < self.len ==> self@[i as int] == spec_va_add_range(self.start, i),
            forall|i: usize|
                0 <= i < self.len ==> self@[i as int] == self.start + i * 4096,
    {
        assert forall|i: usize| 0 <= i < self.len implies self@[i as int] == spec_va_add_range(
            self.start,
            i,
        ) && self@[i as int] == self.start + i * 4096 by {
            assert(spec_va_add_range(self.start, i) == self@[i as int]);
            assert(i * 4096 <= self.len * 4096);
        }
    }

    pub closed spec fn view(&self) -> Seq<VAddr> {
        self.view@
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.start + self.len * 4096 < usize::MAX
        &&& spec_va_4k_valid(self.start)
        &&& self@.len() == self.len
        &&& self@.no_duplicates()
        &&& forall|i: int| #![trigger self@[i]] 0 <= i < self.len ==> spec_va_4k_valid(self@[i])
        &&& self.view_match_spec()
    }

    pub closed spec fn view_match_spec(&self) -> bool {
        &&& forall|i: usize|
            #![trigger spec_va_add_range(self.start, i)]
            0 <= i < self.len ==> spec_va_add_range(self.start, i) == self@[i as int]
    }

    pub fn new(va: VAddr, len: usize) -> (ret: Self)
        requires
            spec_va_4k_valid(va),
            va_4k_range_valid(va, len),
            va < usize::MAX - len * 4096,
        ensures
            ret.wf(),
            ret.start == va,
            ret.len == len,
    {
        proof {
            va_range_lemma();
        }
        let seq = Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize)));
        Self { start: va, len: len, view: seq }
    }

    pub fn index(&self, i: usize) -> (ret: VAddr)
        requires
            self.wf(),
            0 <= i < self.len,
        ensures
            ret == self@[i as int],
    {
        va_add_range(self.start, i)
    }
}

} // verus!
