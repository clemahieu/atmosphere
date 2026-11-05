use vstd::prelude::*;
verus! {

use crate::pptr::*;
use crate::pagetable::pagetable_spec::*;
use crate::array::Array;
use crate::define::*;
use crate::pagetable::pagemap::*;
use crate::util::page_ptr_util_u::*;
use crate::pagetable::entry::*;

impl Array<Option<PageTable>, PCID_MAX> {
    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn pagetable_array_create_pagetable_l4_entry_t(
        &mut self,
        pcid: Pcid,
        target_l4i: L4Index,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self)@[pcid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self)@[pcid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[pcid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            final(self).wf(),
            forall|p: Pcid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < PCID_MAX && p != pcid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[pcid as int].is_Some(),
            final(self)@[pcid as int].unwrap().wf(),
            final(self)@[pcid as int].unwrap().pcid == old(self)@[pcid as int].unwrap().pcid,
            final(self)@[pcid as int].unwrap().kernel_l4_end == old(
                self,
            )@[pcid as int].unwrap().kernel_l4_end,
            final(self)@[pcid as int].unwrap().page_closure() =~= old(
                self,
            )@[pcid as int].unwrap().page_closure().insert(page_map_ptr),
            final(self)@[pcid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_4k(),
            final(self)@[pcid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_2m(),
            final(self)@[pcid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_1g(),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_Some(),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).get_Some_0().addr
                == page_map_ptr,
            final(self)@[pcid as int].unwrap().kernel_entries =~= old(
                self,
            )@[pcid as int].unwrap().kernel_entries,
    {
        self.ar[pcid].as_mut().unwrap().create_entry_l4(
            target_l4i,
            page_map_ptr,
            Tracked(page_map_perm),
        );
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn pagetable_array_create_pagetable_l3_entry_t(
        &mut self,
        pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self)@[pcid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_Some(),
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i).unwrap().addr
                == target_l3_p,
            page_ptr_valid(page_map_ptr),
            old(self)@[pcid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[pcid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            final(self).wf(),
            forall|p: Pcid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < PCID_MAX && p != pcid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[pcid as int].is_Some(),
            final(self)@[pcid as int].unwrap().wf(),
            final(self)@[pcid as int].unwrap().pcid == old(self)@[pcid as int].unwrap().pcid,
            final(self)@[pcid as int].unwrap().kernel_l4_end == old(
                self,
            )@[pcid as int].unwrap().kernel_l4_end,
            final(self)@[pcid as int].unwrap().page_closure() =~= old(
                self,
            )@[pcid as int].unwrap().page_closure().insert(page_map_ptr),
            final(self)@[pcid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_4k(),
            final(self)@[pcid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_2m(),
            final(self)@[pcid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_1g(),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i) == old(
                self,
            )@[pcid as int].unwrap().spec_resolve_mapping_l4(target_l4i),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some(),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).get_Some_0().addr == page_map_ptr,
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            final(self)@[pcid as int].unwrap().kernel_entries =~= old(
                self,
            )@[pcid as int].unwrap().kernel_entries,
    {
        self.ar[pcid].as_mut().unwrap().create_entry_l3(
            target_l4i,
            target_l3i,
            target_l3_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn pagetable_array_create_pagetable_l2_entry_t(
        &mut self,
        pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self)@[pcid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).is_Some(),
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).unwrap().addr == target_l2_p,
            page_ptr_valid(page_map_ptr),
            old(self)@[pcid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[pcid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            final(self).wf(),
            forall|p: Pcid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < PCID_MAX && p != pcid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[pcid as int].is_Some(),
            final(self)@[pcid as int].unwrap().wf(),
            final(self)@[pcid as int].unwrap().pcid == old(self)@[pcid as int].unwrap().pcid,
            final(self)@[pcid as int].unwrap().kernel_l4_end == old(
                self,
            )@[pcid as int].unwrap().kernel_l4_end,
            final(self)@[pcid as int].unwrap().page_closure() =~= old(
                self,
            )@[pcid as int].unwrap().page_closure().insert(page_map_ptr),
            final(self)@[pcid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_4k(),
            final(self)@[pcid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_2m(),
            final(self)@[pcid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_1g(),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i) == old(
                self,
            )@[pcid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i) == old(
                self,
            )@[pcid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == page_map_ptr,
            final(self)@[pcid as int].unwrap().spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_None(),
            final(self)@[pcid as int].unwrap().kernel_entries =~= old(
                self,
            )@[pcid as int].unwrap().kernel_entries,
    {
        self.ar[pcid].as_mut().unwrap().create_entry_l2(
            target_l4i,
            target_l3i,
            target_l2i,
            target_l2_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn pagetable_array_map_4k_page_t(
        &mut self,
        pcid: Pcid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,
    )
        requires
            old(self).wf(),
            old(self)@[pcid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == target_l1_p,
            old(self)@[pcid as int].unwrap().spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ).is_None() || old(self)@[pcid as int].unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == false,
            old(self)@[pcid as int].unwrap().page_closure().contains(target_entry.addr) == false,
            page_ptr_valid(target_entry.addr),
        ensures
            final(self).wf(),
            forall|p: Pcid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < PCID_MAX && p != pcid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[pcid as int].is_Some(),
            final(self)@[pcid as int].unwrap().wf(),
            final(self)@[pcid as int].unwrap().pcid == old(self)@[pcid as int].unwrap().pcid,
            final(self)@[pcid as int].unwrap().kernel_l4_end == old(
                self,
            )@[pcid as int].unwrap().kernel_l4_end,
            final(self)@[pcid as int].unwrap().page_closure() =~= old(
                self,
            )@[pcid as int].unwrap().page_closure(),
            final(self)@[pcid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_4k().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            final(self)@[pcid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_2m(),
            final(self)@[pcid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[pcid as int].unwrap().mapping_1g(),
            final(self)@[pcid as int].unwrap().kernel_entries =~= old(
                self,
            )@[pcid as int].unwrap().kernel_entries,
    {
        self.ar[pcid].as_mut().unwrap().map_4k_page(
            target_l4i,
            target_l3i,
            target_l2i,
            target_l1i,
            target_l1_p,
            target_entry,
        );
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn iommu_table_array_create_iommu_table_l4_entry_t(
        &mut self,
        ioid: IOid,
        target_l4i: L4Index,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self)@[ioid as int].unwrap().wf(),
            0 <= target_l4i < 512,
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self)@[ioid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[ioid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            final(self).wf(),
            forall|p: IOid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < IOID_MAX && p != ioid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[ioid as int].is_Some(),
            final(self)@[ioid as int].unwrap().wf(),
            final(self)@[ioid as int].unwrap().ioid == old(self)@[ioid as int].unwrap().ioid,
            final(self)@[ioid as int].unwrap().kernel_l4_end == old(
                self,
            )@[ioid as int].unwrap().kernel_l4_end,
            final(self)@[ioid as int].unwrap().page_closure() =~= old(
                self,
            )@[ioid as int].unwrap().page_closure().insert(page_map_ptr),
            final(self)@[ioid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_4k(),
            final(self)@[ioid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_2m(),
            final(self)@[ioid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_1g(),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_Some(),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l4(target_l4i).get_Some_0().addr
                == page_map_ptr,
            final(self)@[ioid as int].unwrap().kernel_entries =~= old(
                self,
            )@[ioid as int].unwrap().kernel_entries,
    {
        self.ar[ioid].as_mut().unwrap().create_entry_l4(
            target_l4i,
            page_map_ptr,
            Tracked(page_map_perm),
        );
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn iommu_table_array_create_iommu_table_l3_entry_t(
        &mut self,
        ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self)@[ioid as int].unwrap().wf(),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_l4(target_l4i).is_Some(),
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_l4(target_l4i).unwrap().addr
                == target_l3_p,
            page_ptr_valid(page_map_ptr),
            old(self)@[ioid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[ioid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            final(self).wf(),
            forall|p: IOid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < IOID_MAX && p != ioid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[ioid as int].is_Some(),
            final(self)@[ioid as int].unwrap().wf(),
            final(self)@[ioid as int].unwrap().ioid == old(self)@[ioid as int].unwrap().ioid,
            final(self)@[ioid as int].unwrap().kernel_l4_end == old(
                self,
            )@[ioid as int].unwrap().kernel_l4_end,
            final(self)@[ioid as int].unwrap().page_closure() =~= old(
                self,
            )@[ioid as int].unwrap().page_closure().insert(page_map_ptr),
            final(self)@[ioid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_4k(),
            final(self)@[ioid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_2m(),
            final(self)@[ioid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_1g(),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l4(target_l4i) == old(
                self,
            )@[ioid as int].unwrap().spec_resolve_mapping_l4(target_l4i),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some(),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).get_Some_0().addr == page_map_ptr,
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            final(self)@[ioid as int].unwrap().kernel_entries =~= old(
                self,
            )@[ioid as int].unwrap().kernel_entries,
    {
        self.ar[ioid].as_mut().unwrap().create_entry_l3(
            target_l4i,
            target_l3i,
            target_l3_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn iommu_table_array_create_iommu_table_l2_entry_t(
        &mut self,
        ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self)@[ioid as int].unwrap().wf(),
            0 <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).is_Some(),
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).unwrap().addr == target_l2_p,
            page_ptr_valid(page_map_ptr),
            old(self)@[ioid as int].unwrap().page_closure().contains(page_map_ptr) == false,
            old(self)@[ioid as int].unwrap().page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            final(self).wf(),
            forall|p: IOid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < IOID_MAX && p != ioid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[ioid as int].is_Some(),
            final(self)@[ioid as int].unwrap().wf(),
            final(self)@[ioid as int].unwrap().ioid == old(self)@[ioid as int].unwrap().ioid,
            final(self)@[ioid as int].unwrap().kernel_l4_end == old(
                self,
            )@[ioid as int].unwrap().kernel_l4_end,
            final(self)@[ioid as int].unwrap().page_closure() =~= old(
                self,
            )@[ioid as int].unwrap().page_closure().insert(page_map_ptr),
            final(self)@[ioid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_4k(),
            final(self)@[ioid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_2m(),
            final(self)@[ioid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_1g(),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i) == old(
                self,
            )@[ioid as int].unwrap().spec_resolve_mapping_1g_l3(target_l4i, target_l3i),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i) == old(
                self,
            )@[ioid as int].unwrap().spec_resolve_mapping_l3(target_l4i, target_l3i),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == page_map_ptr,
            final(self)@[ioid as int].unwrap().spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_None(),
            final(self)@[ioid as int].unwrap().kernel_entries =~= old(
                self,
            )@[ioid as int].unwrap().kernel_entries,
    {
        self.ar[ioid].as_mut().unwrap().create_entry_l2(
            target_l4i,
            target_l3i,
            target_l2i,
            target_l2_p,
            page_map_ptr,
            Tracked(page_map_perm),
        );
    }

    #[verifier(external_body)]
    // external_body(unproven): an array element access not proven yet
    pub fn iommu_table_array_map_4k_page_t(
        &mut self,
        ioid: IOid,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,
    )
        requires
            old(self).wf(),
            old(self)@[ioid as int].unwrap().wf(),
            KERNEL_MEM_END_L4INDEX <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).get_Some_0().addr == target_l1_p,
            old(self)@[ioid as int].unwrap().spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ).is_None() || old(self)@[ioid as int].unwrap().mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == false,
            old(self)@[ioid as int].unwrap().page_closure().contains(target_entry.addr) == false,
            page_ptr_valid(target_entry.addr),
        ensures
            final(self).wf(),
            forall|p: IOid|
                #![trigger final(self)@[p as int]]
                #![trigger old(self)@[p as int]]
                0 <= p < IOID_MAX && p != ioid ==> final(self)@[p as int] =~= old(self)@[p as int],
            final(self)@[ioid as int].is_Some(),
            final(self)@[ioid as int].unwrap().wf(),
            final(self)@[ioid as int].unwrap().ioid == old(self)@[ioid as int].unwrap().ioid,
            final(self)@[ioid as int].unwrap().kernel_l4_end == old(
                self,
            )@[ioid as int].unwrap().kernel_l4_end,
            final(self)@[ioid as int].unwrap().page_closure() =~= old(
                self,
            )@[ioid as int].unwrap().page_closure(),
            final(self)@[ioid as int].unwrap().mapping_4k() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_4k().insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            final(self)@[ioid as int].unwrap().mapping_2m() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_2m(),
            final(self)@[ioid as int].unwrap().mapping_1g() =~= old(
                self,
            )@[ioid as int].unwrap().mapping_1g(),
            final(self)@[ioid as int].unwrap().kernel_entries =~= old(
                self,
            )@[ioid as int].unwrap().kernel_entries,
    {
        self.ar[ioid].as_mut().unwrap().map_4k_page(
            target_l4i,
            target_l3i,
            target_l2i,
            target_l1i,
            target_l1_p,
            target_entry,
        );
    }
}

} // verus!
