use vstd::prelude::*;
verus! {

use crate::slinkedlist::spec_impl_u::*;
use crate::define::SLLIndex;
use core::mem::MaybeUninit;

impl<T: Copy, const N: usize> StaticLinkedList<T, N> {
    #[verifier(external_body)]
    // external_body(gap): builds a value from zeroed memory, which Verus cannot check
    pub const fn new() -> (ret: Self)
        ensures
            ret.array_wf(),
    {
        unsafe {
            let ret = Self {
                spec_seq: Ghost(Seq::empty()),
                value_list: Ghost(Seq::empty()),
                value_list_head: 0,
                value_list_tail: 0,
                value_list_len: 0,
                free_list: Ghost(Seq::empty()),
                free_list_head: 0,
                free_list_tail: 0,
                free_list_len: 0,
                size: Ghost(N),
                arr_seq: Ghost(Seq::empty()),
                ar: MaybeUninit::zeroed().assume_init(),
            };

            ret
        }
    }

}

} // verus!
