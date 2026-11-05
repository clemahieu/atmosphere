use vstd::prelude::*;
verus! {

// use crate::slinkedlist::define::*;
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

    // //TODO: prove this
    // #[verifier(external_body)]
    // pub fn put_ptr(&mut self, new_ptr: usize)
    //     requires
    //         old(self).array_wf(),
    //     ensures
    //     self.array_wf(),
    //     forall|i:int| #![auto] 0<=i<self.arr_seq@.len() ==>
    //         self.arr_seq@[i].next == old(self).arr_seq@[i].next && self.arr_seq@[i].prev == old(self).arr_seq@[i].prev && self.arr_seq@[i].value == old(self).arr_seq@[i].value,
    //     self.spec_seq@ == old(self).spec_seq@.push(new_ptr),
    //     self.value_list@ == old(self).value_list@,
    //     self.free_list@ == old(self).free_list@,
    //     self.value_list_head == old(self).value_list_head,
    //     self.value_list_tail == old(self).value_list_tail,
    //     self.value_list_len == old(self).value_list_len,
    //     self.free_list_head == old(self).free_list_head,
    //     self.free_list_tail == old(self).free_list_tail,
    //     self.free_list_len == old(self).free_list_len,
    //     old(self).free_list_wf() ==> self.free_list_wf(),
    //     old(self).value_list_wf() ==> self.value_list_wf(),
    // {
    //     //self.spec_seq@ = self.spec_seq@.push(new_ptr);
    // }
}

} // verus!
