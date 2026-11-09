use vstd::prelude::*;
verus! {

use crate::arch::*;
use crate::array::*;
use crate::util::page_ptr_util_u::*;

use crate::pagetable::entry::*;

pub struct PageMap {
    pub ar: Array<usize, 512>,
    pub spec_seq: Ghost<Seq<PageEntry>>,
    /// The table's level in the kernel's numbering on every target: 4 for a root, 1 for a table of 4K
    /// leaves. Ghost, so the struct stays the hardware page.
    pub level: Ghost<usize>,
}

impl PageMap {
    pub fn init(&mut self)
        requires
            old(self).ar.wf(),
            old(self).spec_seq@.len() == 512,
        ensures
            final(self).wf(),
            final(self).level == old(self).level,
            forall|i: int| #![trigger final(self)@[i].is_empty()] 0 <= i < 512 ==> final(self)@[i].is_empty(),
    {
        for i in 0..512
            invariant
                0 <= i <= 512,
                self.ar.wf(),
                self.spec_seq@.len() == 512,
                forall|j: int|
                    #![trigger usize2page_entry(self.ar@[j], self.level@)]
                    0 <= j < i ==> (usize2page_entry(self.ar@[j], self.level@) =~= self.spec_seq@[j]),
                forall|j: int|
                    #![trigger self.ar@[j]]
                    0 <= j < i ==> self.ar@[j] == 0,
                forall|j: int| #![trigger self@[j].is_empty()] 0 <= j < i ==> self@[j].is_empty(),
        {
            let ghost_view = Ghost(self@);
            self.ar.set(i, 0usize);
            assert(self@ == ghost_view);
            proof {
                zero_leads_is_empty_page_entry(self.level@);
                self.spec_seq@ = self.spec_seq@.update(i as int, usize2page_entry(0usize, self.level@));
            }
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.ar.wf()
        &&& self.spec_seq@.len() == 512
        &&& forall|i: int|
            #![trigger usize2page_entry(self.ar@[i], self.level@)]
            0 <= i < 512 ==> (usize2page_entry(self.ar@[i], self.level@) =~= self.spec_seq@[i])

    }

    pub open spec fn view(&self) -> Seq<PageEntry> {
        self.spec_seq@
    }

    /// The accessed and dirty bits of entry i as its word holds them. The processor sets them at any
    /// time, so the view leaves them out (lemma_status_outside_view) and a value read here holds only
    /// for the moment of the read.
    pub open spec fn status(&self, i: int) -> PageEntryStatus {
        spec_usize2page_entry_status(self.ar@[i], self.level@)
    }

    /// A table whose words differ from a well-formed table's only in the accessed and dirty bits is well
    /// formed with the same view: whatever the processor sets there, every proof over a table's view
    /// holds.
    pub proof fn lemma_status_outside_view(&self, other: &PageMap)
        requires
            self.wf(),
            other.ar.wf(),
            other.spec_seq@ == self.spec_seq@,
            other.level == self.level,
            forall|i: int|
                #![trigger other.ar@[i]]
                0 <= i < 512 ==> spec_without_status(other.ar@[i]) == spec_without_status(self.ar@[i]),
        ensures
            other.wf(),
            other@ == self@,
    {
        assert forall|i: int|
            #![trigger usize2page_entry(other.ar@[i], other.level@)]
            0 <= i < 512 implies usize2page_entry(other.ar@[i], other.level@) =~= other.spec_seq@[i] by {
            lemma_status_outside_entry(other.ar@[i], self.ar@[i], self.level@);
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

    pub fn set(&mut self, index: usize, value: PageEntry, level: usize)
        requires
            old(self).wf(),
            level == old(self).level@,
            0 <= index < 512,
            value.perm.present ==> MEM_valid(value.addr),
            value.perm.present == false ==> value.is_empty(),
        ensures
            final(self).wf(),
            final(self).level == old(self).level,
            final(self)@ =~= old(self)@.update(index as int, value),
            final(self).status(index as int).is_clear(),
    {
        if value.perm.present == false {
            self.ar.set(index, 0usize);
            proof {
                zero_leads_is_empty_page_entry(level);
                self.spec_seq@ = self.spec_seq@.update(index as int, usize2page_entry(0usize, level));
            }
            return ;
        } else {
            let u = page_entry2usize(&value, level);
            self.ar.set(index, u);

            proof {
                self.spec_seq@ = self.spec_seq@.update(index as int, value);
            }

            return ;
        }
    }

    pub fn get(&self, index: usize, level: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            0 <= index < 512,
            level == self.level@,
        ensures
            ret =~= self[index],
    {
        return usize2page_entry(*self.ar.get(index), level);
    }
}

} // verus!
