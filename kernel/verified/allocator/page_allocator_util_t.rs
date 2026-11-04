use vstd::prelude::*;
verus! {

use crate::define::*;

// use crate::allocator::page::*;
// use crate::array::*;
// use crate::slinkedlist::spec_impl_u::*;
use crate::util::page_ptr_util_u::*;
use crate::allocator::page_allocator_spec_impl::*;
use crate::pptr::*;

impl PageAllocator {
    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn set_state(&mut self, index: usize, state: PageState)
        requires
            old(self).page_array.wf(),
            0 <= index < NUM_PAGES,
        ensures
            final(self).page_array.wf(),
            forall|i: int|
                #![trigger final(self).page_array@[i]]
                #![trigger old(self).page_array@[i]]
                #![trigger final(self).page_array@[i].ref_count]
                #![trigger old(self).page_array@[i].ref_count]
                0 <= i < NUM_PAGES && i != index ==> final(self).page_array@[i] =~= old(
                    self,
                ).page_array@[i],
            final(self).page_array@[index as int].addr =~= old(self).page_array@[index as int].addr,
            // self.page_array@[index as int].state =~= old(self).page_array@[index as int].state,
            final(self).page_array@[index as int].is_io_page =~= old(
                self,
            ).page_array@[index as int].is_io_page,
            final(self).page_array@[index as int].rev_pointer =~= old(
                self,
            ).page_array@[index as int].rev_pointer,
            final(self).page_array@[index as int].ref_count =~= old(
                self,
            ).page_array@[index as int].ref_count,
            final(self).page_array@[index as int].owning_container =~= old(
                self,
            ).page_array@[index as int].owning_container,
            final(self).page_array@[index as int].mappings =~= old(
                self,
            ).page_array@[index as int].mappings,
            final(self).page_array@[index as int].io_mappings =~= old(
                self,
            ).page_array@[index as int].io_mappings,
            final(self).page_array@[index as int].state =~= state,
            final(self).free_pages_4k == old(self).free_pages_4k,
            final(self).free_pages_2m == old(self).free_pages_2m,
            final(self).free_pages_1g == old(self).free_pages_1g,
            final(self).allocated_pages_4k == old(self).allocated_pages_4k,
            final(self).allocated_pages_2m == old(self).allocated_pages_2m,
            final(self).allocated_pages_1g == old(self).allocated_pages_1g,
            final(self).mapped_pages_4k == old(self).mapped_pages_4k,
            final(self).mapped_pages_2m == old(self).mapped_pages_2m,
            final(self).mapped_pages_1g == old(self).mapped_pages_1g,
            final(self).page_perms_4k == old(self).page_perms_4k,
            final(self).page_perms_2m == old(self).page_perms_2m,
            final(self).page_perms_1g == old(self).page_perms_1g,
            final(self).container_map_4k == old(self).container_map_4k,
            final(self).container_map_2m == old(self).container_map_2m,
            final(self).container_map_1g == old(self).container_map_1g,
    {
        self.page_array.ar[index].state = state;
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn set_rev_pointer(&mut self, index: usize, rev_pointer: SLLIndex)
        requires
            old(self).page_array.wf(),
            0 <= index < NUM_PAGES,
        ensures
            final(self).page_array.wf(),
            forall|i: int|
                #![trigger final(self).page_array@[i]]
                #![trigger old(self).page_array@[i]]
                0 <= i < NUM_PAGES && i != index ==> final(self).page_array@[i] =~= old(
                    self,
                ).page_array@[i],
            final(self).page_array@[index as int].addr =~= old(self).page_array@[index as int].addr,
            final(self).page_array@[index as int].state =~= old(self).page_array@[index as int].state,
            final(self).page_array@[index as int].is_io_page =~= old(
                self,
            ).page_array@[index as int].is_io_page,
            // self.page_array@[index as int].rev_pointer =~= old(self).page_array@[index as int].rev_pointer,
            final(self).page_array@[index as int].ref_count =~= old(
                self,
            ).page_array@[index as int].ref_count,
            final(self).page_array@[index as int].owning_container =~= old(
                self,
            ).page_array@[index as int].owning_container,
            final(self).page_array@[index as int].mappings =~= old(
                self,
            ).page_array@[index as int].mappings,
            final(self).page_array@[index as int].io_mappings =~= old(
                self,
            ).page_array@[index as int].io_mappings,
            final(self).page_array@[index as int].rev_pointer =~= rev_pointer,
            final(self).free_pages_4k == old(self).free_pages_4k,
            final(self).free_pages_2m == old(self).free_pages_2m,
            final(self).free_pages_1g == old(self).free_pages_1g,
            final(self).allocated_pages_4k == old(self).allocated_pages_4k,
            final(self).allocated_pages_2m == old(self).allocated_pages_2m,
            final(self).allocated_pages_1g == old(self).allocated_pages_1g,
            final(self).mapped_pages_4k == old(self).mapped_pages_4k,
            final(self).mapped_pages_2m == old(self).mapped_pages_2m,
            final(self).mapped_pages_1g == old(self).mapped_pages_1g,
            final(self).page_perms_4k == old(self).page_perms_4k,
            final(self).page_perms_2m == old(self).page_perms_2m,
            final(self).page_perms_1g == old(self).page_perms_1g,
            final(self).container_map_4k == old(self).container_map_4k,
            final(self).container_map_2m == old(self).container_map_2m,
            final(self).container_map_1g == old(self).container_map_1g,
    {
        self.page_array.ar[index].rev_pointer = rev_pointer;
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn set_ref_count(&mut self, index: usize, ref_count: usize)
        requires
            old(self).page_array.wf(),
            0 <= index < NUM_PAGES,
        ensures
            final(self).page_array.wf(),
            forall|i: int|
                #![trigger final(self).page_array@[i]]
                #![trigger old(self).page_array@[i]]
                0 <= i < NUM_PAGES && i != index ==> final(self).page_array@[i] =~= old(
                    self,
                ).page_array@[i],
            final(self).page_array@[index as int].addr =~= old(self).page_array@[index as int].addr,
            final(self).page_array@[index as int].state =~= old(self).page_array@[index as int].state,
            final(self).page_array@[index as int].is_io_page =~= old(
                self,
            ).page_array@[index as int].is_io_page,
            final(self).page_array@[index as int].rev_pointer =~= old(
                self,
            ).page_array@[index as int].rev_pointer,
            final(self).page_array@[index as int].ref_count =~= ref_count,
            final(self).page_array@[index as int].owning_container =~= old(
                self,
            ).page_array@[index as int].owning_container,
            final(self).page_array@[index as int].mappings =~= old(
                self,
            ).page_array@[index as int].mappings,
            final(self).page_array@[index as int].io_mappings =~= old(
                self,
            ).page_array@[index as int].io_mappings,
            final(self).free_pages_4k == old(self).free_pages_4k,
            final(self).free_pages_2m == old(self).free_pages_2m,
            final(self).free_pages_1g == old(self).free_pages_1g,
            final(self).allocated_pages_4k == old(self).allocated_pages_4k,
            final(self).allocated_pages_2m == old(self).allocated_pages_2m,
            final(self).allocated_pages_1g == old(self).allocated_pages_1g,
            final(self).mapped_pages_4k == old(self).mapped_pages_4k,
            final(self).mapped_pages_2m == old(self).mapped_pages_2m,
            final(self).mapped_pages_1g == old(self).mapped_pages_1g,
            final(self).page_perms_4k == old(self).page_perms_4k,
            final(self).page_perms_2m == old(self).page_perms_2m,
            final(self).page_perms_1g == old(self).page_perms_1g,
            final(self).container_map_4k == old(self).container_map_4k,
            final(self).container_map_2m == old(self).container_map_2m,
            final(self).container_map_1g == old(self).container_map_1g,
    {
        self.page_array.ar[index].ref_count = ref_count;
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn set_mapping(&mut self, index: usize, mapping: Ghost<Set<(Pcid, VAddr)>>)
        requires
            old(self).page_array.wf(),
            0 <= index < NUM_PAGES,
        ensures
            final(self).page_array.wf(),
            forall|i: int|
                #![trigger final(self).page_array@[i]]
                #![trigger old(self).page_array@[i]]
                0 <= i < NUM_PAGES && i != index ==> final(self).page_array@[i] =~= old(
                    self,
                ).page_array@[i],
            final(self).page_array@[index as int].addr =~= old(self).page_array@[index as int].addr,
            final(self).page_array@[index as int].state =~= old(self).page_array@[index as int].state,
            final(self).page_array@[index as int].is_io_page =~= old(
                self,
            ).page_array@[index as int].is_io_page,
            final(self).page_array@[index as int].rev_pointer =~= old(
                self,
            ).page_array@[index as int].rev_pointer,
            final(self).page_array@[index as int].ref_count =~= old(
                self,
            ).page_array@[index as int].ref_count,
            final(self).page_array@[index as int].owning_container =~= old(
                self,
            ).page_array@[index as int].owning_container,
            final(self).page_array@[index as int].mappings =~= mapping,
            final(self).page_array@[index as int].io_mappings =~= old(
                self,
            ).page_array@[index as int].io_mappings,
            final(self).free_pages_4k == old(self).free_pages_4k,
            final(self).free_pages_2m == old(self).free_pages_2m,
            final(self).free_pages_1g == old(self).free_pages_1g,
            final(self).allocated_pages_4k == old(self).allocated_pages_4k,
            final(self).allocated_pages_2m == old(self).allocated_pages_2m,
            final(self).allocated_pages_1g == old(self).allocated_pages_1g,
            final(self).mapped_pages_4k == old(self).mapped_pages_4k,
            final(self).mapped_pages_2m == old(self).mapped_pages_2m,
            final(self).mapped_pages_1g == old(self).mapped_pages_1g,
            final(self).page_perms_4k == old(self).page_perms_4k,
            final(self).page_perms_2m == old(self).page_perms_2m,
            final(self).page_perms_1g == old(self).page_perms_1g,
            final(self).container_map_4k == old(self).container_map_4k,
            final(self).container_map_2m == old(self).container_map_2m,
            final(self).container_map_1g == old(self).container_map_1g,
    {
        // self.page_array.ar[index].ref_count = self.page_array.ar[index].ref_count + 1;
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn set_io_mapping(&mut self, index: usize, io_mapping: Ghost<Set<(IOid, VAddr)>>)
        requires
            old(self).page_array.wf(),
            0 <= index < NUM_PAGES,
        ensures
            final(self).page_array.wf(),
            forall|i: int|
                #![trigger final(self).page_array@[i]]
                #![trigger old(self).page_array@[i]]
                0 <= i < NUM_PAGES && i != index ==> final(self).page_array@[i] =~= old(
                    self,
                ).page_array@[i],
            final(self).page_array@[index as int].addr =~= old(self).page_array@[index as int].addr,
            final(self).page_array@[index as int].state =~= old(self).page_array@[index as int].state,
            final(self).page_array@[index as int].is_io_page =~= old(
                self,
            ).page_array@[index as int].is_io_page,
            final(self).page_array@[index as int].rev_pointer =~= old(
                self,
            ).page_array@[index as int].rev_pointer,
            final(self).page_array@[index as int].ref_count =~= old(
                self,
            ).page_array@[index as int].ref_count,
            final(self).page_array@[index as int].owning_container =~= old(
                self,
            ).page_array@[index as int].owning_container,
            final(self).page_array@[index as int].mappings =~= old(
                self,
            ).page_array@[index as int].mappings,
            final(self).page_array@[index as int].io_mappings =~= io_mapping,
            final(self).free_pages_4k == old(self).free_pages_4k,
            final(self).free_pages_2m == old(self).free_pages_2m,
            final(self).free_pages_1g == old(self).free_pages_1g,
            final(self).allocated_pages_4k == old(self).allocated_pages_4k,
            final(self).allocated_pages_2m == old(self).allocated_pages_2m,
            final(self).allocated_pages_1g == old(self).allocated_pages_1g,
            final(self).mapped_pages_4k == old(self).mapped_pages_4k,
            final(self).mapped_pages_2m == old(self).mapped_pages_2m,
            final(self).mapped_pages_1g == old(self).mapped_pages_1g,
            final(self).page_perms_4k == old(self).page_perms_4k,
            final(self).page_perms_2m == old(self).page_perms_2m,
            final(self).page_perms_1g == old(self).page_perms_1g,
            final(self).container_map_4k == old(self).container_map_4k,
            final(self).container_map_2m == old(self).container_map_2m,
            final(self).container_map_1g == old(self).container_map_1g,
    {
        // self.page_array.ar[index].ref_count = self.page_array.ar[index].ref_count + 1;
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn set_owning_container(&mut self, index: usize, owning_container_op: Option<ContainerPtr>)
        requires
            old(self).page_array.wf(),
            0 <= index < NUM_PAGES,
        ensures
            final(self).page_array.wf(),
            forall|i: int|
                #![trigger final(self).page_array@[i]]
                #![trigger old(self).page_array@[i]]
                0 <= i < NUM_PAGES && i != index ==> final(self).page_array@[i] =~= old(
                    self,
                ).page_array@[i],
            final(self).page_array@[index as int].addr =~= old(self).page_array@[index as int].addr,
            final(self).page_array@[index as int].state =~= old(self).page_array@[index as int].state,
            final(self).page_array@[index as int].is_io_page =~= old(
                self,
            ).page_array@[index as int].is_io_page,
            final(self).page_array@[index as int].rev_pointer =~= old(
                self,
            ).page_array@[index as int].rev_pointer,
            final(self).page_array@[index as int].ref_count =~= old(
                self,
            ).page_array@[index as int].ref_count,
            // self.page_array@[index as int].owning_container =~= old(self).page_array@[index as int].owning_container,
            final(self).page_array@[index as int].owning_container =~= owning_container_op,
            final(self).page_array@[index as int].mappings =~= old(
                self,
            ).page_array@[index as int].mappings,
            final(self).page_array@[index as int].io_mappings =~= old(
                self,
            ).page_array@[index as int].io_mappings,
            final(self).free_pages_4k == old(self).free_pages_4k,
            final(self).free_pages_2m == old(self).free_pages_2m,
            final(self).free_pages_1g == old(self).free_pages_1g,
            final(self).allocated_pages_4k == old(self).allocated_pages_4k,
            final(self).allocated_pages_2m == old(self).allocated_pages_2m,
            final(self).allocated_pages_1g == old(self).allocated_pages_1g,
            final(self).mapped_pages_4k == old(self).mapped_pages_4k,
            final(self).mapped_pages_2m == old(self).mapped_pages_2m,
            final(self).mapped_pages_1g == old(self).mapped_pages_1g,
            final(self).page_perms_4k == old(self).page_perms_4k,
            final(self).page_perms_2m == old(self).page_perms_2m,
            final(self).page_perms_1g == old(self).page_perms_1g,
            final(self).container_map_4k == old(self).container_map_4k,
            final(self).container_map_2m == old(self).container_map_2m,
            final(self).container_map_1g == old(self).container_map_1g,
    {
        self.page_array.ar[index].owning_container = owning_container_op;
    }
}

#[verifier(external_body)]
// external_body(gap): takes its permission from Tracked::assume_new, which Verus cannot check
pub fn merge_4k_pages_to_2m_page(target_page_idx:usize, page_perms: Tracked<Map<usize, PagePerm4k>>) -> (ret: Tracked<PagePerm2m>)
    requires
        target_page_idx + 512 <= NUM_PAGES,
        forall|i:usize|
            #![auto]
            0<=i<512 
            ==>
            page_perms@.dom().contains(i)
            &&
            page_perms@[i].is_uninit()
            &&
            page_perms@[i].addr() == page_index2page_ptr((target_page_idx + i) as usize),
    ensures
        ret@.is_uninit(),
        ret@.addr() == page_index2page_ptr(target_page_idx),
    {
        Tracked::assume_new()
    }

#[verifier(external_body)]
// external_body(gap): takes its permission from Tracked::assume_new, which Verus cannot check
pub fn split_2m_pages_to_pages(target_page_idx:usize, page_perm: Tracked<PagePerm2m>) -> (ret: Tracked<Map<usize, PagePerm4k>>)
    requires
        page_perm@.is_uninit(),
        page_perm@.addr() == page_index2page_ptr(target_page_idx),
    ensures
        forall|i:usize|
            #![trigger ret@.dom().contains(i)]
            #![trigger ret@[i]]
            target_page_idx<=i<512 + target_page_idx 
            ==>
            ret@.dom().contains(i)
            &&
            ret@[i].is_uninit()
            &&
            ret@[i].addr() == page_index2page_ptr(i),
    {
        Tracked::assume_new()
    }

} // verus!
