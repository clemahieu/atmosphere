use vstd::prelude::*;
verus! {

use crate::arch::{PAGE_ENTRY_ACCESSED_MASK, PAGE_ENTRY_DIRTY_MASK};
use crate::array::*;
use crate::util::page_ptr_util_u::*;

use crate::pagetable::entry::*;

pub struct PageMap {
    pub ar: Array<usize, 512>,
    pub spec_seq: Ghost<Seq<PageEntry>>,  // pub level: Ghost<usize>,
    // not used for now.
}

impl PageMap {
    pub fn init(&mut self)
        requires
            old(self).ar.wf(),
            old(self).spec_seq@.len() == 512,
        ensures
            final(self).wf(),
            forall|i: int| #![trigger final(self)@[i].is_empty()] 0 <= i < 512 ==> final(self)@[i].is_empty(),
    {
        for i in 0..512
            invariant
                0 <= i <= 512,
                self.ar.wf(),
                self.spec_seq@.len() == 512,
                forall|j: int|
                    #![trigger usize2page_entry(self.ar@[j])]
                    0 <= j < i ==> (usize2page_entry(self.ar@[j]) =~= self.spec_seq@[j]),
                forall|j: int|
                    #![trigger self.ar@[j]]
                    0 <= j < i ==> (usize2page_entry(self.ar@[j]).is_empty() <==> self.ar@[j] == 0),
                forall|j: int|
                    #![trigger self.ar@[j]]
                    0 <= j < i ==> usize2page_entry(self.ar@[j]).is_empty(),
                forall|j: int| #![trigger self@[j].is_empty()] 0 <= j < i ==> self@[j].is_empty(),
        {
            let ghost_view = Ghost(self@);
            self.ar.set(i, 0usize);
            assert(self@ == ghost_view);
            proof {
                zero_leads_is_empty_page_entry();
                assert(usize2page_entry(0usize).is_empty());
                self.spec_seq@ = self.spec_seq@.update(i as int, usize2page_entry(0usize));
            }
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.ar.wf()
        &&& self.spec_seq@.len() == 512
        &&& forall|i: int|
            #![trigger usize2page_entry(self.ar@[i])]
            0 <= i < 512 ==> (usize2page_entry(self.ar@[i])
                =~= self.spec_seq@[i])

    }

    pub open spec fn view(&self) -> Seq<PageEntry> {
        self.spec_seq@
    }

    /// The accessed and dirty bits of entry i as its word holds them. The processor sets them at any
    /// time, so the view leaves them out (lemma_status_outside_view) and a value read here holds only
    /// for the moment of the read.
    pub open spec fn status(&self, i: int) -> PageEntryStatus {
        spec_usize2page_entry_status(self.ar@[i])
    }

    /// A table whose words differ from a well-formed table's only in the accessed and dirty bits is well
    /// formed with the same view: whatever the processor sets there, every proof over a table's view
    /// holds.
    pub proof fn lemma_status_outside_view(&self, other: &PageMap)
        requires
            self.wf(),
            other.ar.wf(),
            other.spec_seq@ == self.spec_seq@,
            forall|i: int|
                #![trigger other.ar@[i]]
                0 <= i < 512 ==> other.ar@[i] & (!(PAGE_ENTRY_ACCESSED_MASK | PAGE_ENTRY_DIRTY_MASK)) as usize
                    == self.ar@[i] & (!(PAGE_ENTRY_ACCESSED_MASK | PAGE_ENTRY_DIRTY_MASK)) as usize,
        ensures
            other.wf(),
            other@ == self@,
    {
        assert forall|i: int|
            #![trigger usize2page_entry(other.ar@[i])]
            0 <= i < 512 implies usize2page_entry(other.ar@[i]) =~= other.spec_seq@[i] by {
            lemma_status_outside_entry(other.ar@[i], self.ar@[i]);
        }
    }

    pub open spec fn spec_index(&self, index: usize) -> PageEntry
        recommends
            0 <= index < 512,
    {
        self.spec_seq@[index as int]
    }

    pub open spec fn is_empty(&self) -> bool
        recommends
            self.wf(),
    {
        forall|x: u16| #![auto] 0 <= x < 512 ==> self.spec_seq@[x as int].perm.present == false
    }

    pub fn set(&mut self, index: usize, value: PageEntry)
        requires
            old(self).wf(),
            0 <= index < 512,
            value.perm.present ==> MEM_valid(value.addr),
            value.perm.present == false ==> value.is_empty(),
        ensures
            final(self).wf(),
            final(self)@ =~= old(self)@.update(index as int, value),
            final(self).status(index as int).is_clear(),
    {
        if value.perm.present == false {
            self.ar.set(index, 0usize);
            proof {
                assert(0usize & (0x1u64 << 5u64) as usize == 0 && 0usize & (0x1u64 << 6u64) as usize == 0)
                    by (bit_vector);
                zero_leads_is_empty_page_entry();
                self.spec_seq@ = self.spec_seq@.update(index as int, usize2page_entry(0usize));
            }
            return ;
        } else {
            let u = page_entry2usize(&value);
            self.ar.set(index, u);

            assert(usize2present(u) == value.perm.present);
            assert(usize2present(u) == true);
            assert(u != 0) by (bit_vector)
                requires
                    (u & 0x1u64 as usize) != 0 == true,
            ;

            proof {
                self.spec_seq@ = self.spec_seq@.update(index as int, value);
            }

            return ;
        }
    }

    pub fn index(&self, index: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            0 <= index < 512,
        ensures
            ret =~= self[index],
    {
        return usize2page_entry(*self.ar.get(index));
    }

    pub fn get(&self, index: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            0 <= index < 512,
        ensures
            ret =~= self[index],
    {
        return self.index(index);
    }
}

} // verus!
