use vstd::prelude::*;

verus! {

use crate::arch::{PAGE_ENTRY_ACCESSED_MASK, PAGE_ENTRY_DIRTY_MASK};
use crate::define::*;
use crate::pptr::*;
use crate::util::page_ptr_util_u::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicUsize, Ordering};
use crate::array::Array;
use crate::lemma::lemma_u::*;

pub fn page_map_set_kernel_entry_range(
    kernel_entries: &Array<usize, KERNEL_MEM_END_L4INDEX>,
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        kernel_entries.wf(),
        kernel_entries@.len() == KERNEL_MEM_END_L4INDEX,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value()[i]]
            KERNEL_MEM_END_L4INDEX <= i < 512 ==> final(page_map_perm).value()[i] =~= old(
                page_map_perm,
            ).value()[i],
        forall|i: usize|
            #![trigger final(page_map_perm).value()[i]]
            0 <= i < KERNEL_MEM_END_L4INDEX ==> final(page_map_perm).value()[i] =~= usize2page_entry(
                kernel_entries@[i as int],
            ),
{
    for index in 0..KERNEL_MEM_END_L4INDEX
        invariant
            0 <= index <= KERNEL_MEM_END_L4INDEX,
            kernel_entries.wf(),
            kernel_entries@.len() == KERNEL_MEM_END_L4INDEX,
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i]]
                KERNEL_MEM_END_L4INDEX <= i < 512 ==> page_map_perm.value()[i] =~= old(
                    page_map_perm,
                ).value()[i],
            forall|i: usize|
                #![trigger page_map_perm.value()[i]]
                0 <= i < index ==> page_map_perm.value()[i] =~= usize2page_entry(
                    kernel_entries@[i as int],
                ),
    {
        page_map_set_no_requires(
            page_map_ptr,
            Tracked(page_map_perm),
            index,
            usize2page_entry(*kernel_entries.get(index)),
        );
    }
}

#[verifier(external_body)]
// external_body(glue): writes a hardware page table through a raw pointer
pub fn page_map_set_no_requires(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
    value: PageEntry,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        0 <= index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value()[i]]
            0 <= i < 512 && i != index ==> final(page_map_perm).value()[i] =~= old(
                page_map_perm,
            ).value()[i],
        final(page_map_perm).value()[index] =~= value,
{
    unsafe {
        let uptr = page_map_ptr as *mut MaybeUninit<PageMap>;
        (*uptr).assume_init_mut().set(index, value);
    }
}

#[verifier(external_body)]
// external_body(glue): writes a hardware page table through a raw pointer
pub fn page_map_set(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
    value: PageEntry,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        value.perm.present ==> MEM_valid(value.addr),
        value.perm.present == false ==> value.is_empty(),
        0 <= index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value()[i]]
            0 <= i < 512 && i != index ==> final(page_map_perm).value()[i] =~= old(
                page_map_perm,
            ).value()[i],
        final(page_map_perm).value()[index] =~= value,
        final(page_map_perm).value().status(index as int).is_clear(),
{
    unsafe {
        let uptr = page_map_ptr as *mut MaybeUninit<PageMap>;
        (*uptr).assume_init_mut().set(index, value);
    }
}

/// The bits of an entry's word that are not the processor's accessed and dirty bits.
pub open spec fn status_kept_mask() -> usize {
    (!(PAGE_ENTRY_ACCESSED_MASK | PAGE_ENTRY_DIRTY_MASK)) as usize
}

#[verifier(external_body)]
// external_body(glue): clears the processor's accessed and dirty bits in a hardware page table word atomically, since another core's walk may set one between a read and a write
pub fn page_map_take_status(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
) -> (ret: usize)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().ar.wf(),
        final(page_map_perm).value().spec_seq == old(page_map_perm).value().spec_seq,
        ret & status_kept_mask() == old(page_map_perm).value().ar@[index as int] & status_kept_mask(),
        final(page_map_perm).value().ar@ == old(page_map_perm).value().ar@.update(index as int, ret & status_kept_mask()),
{
    unsafe {
        let word = core::ptr::addr_of_mut!((*(page_map_ptr as *mut PageMap)).ar.ar[index]);
        (*(word as *const AtomicUsize)).fetch_and(
            !((PAGE_ENTRY_ACCESSED_MASK | PAGE_ENTRY_DIRTY_MASK) as usize),
            Ordering::Relaxed,
        )
    }
}

/// Reads and clears the accessed and dirty bits of entry `index`, returning its word as read. The table
/// keeps its view, and the word read is the entry's: only those bits can differ from what the table
/// held, since only the processor sets them.
pub fn page_map_clear_status(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
) -> (ret: usize)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        final(page_map_perm).value()@ == old(page_map_perm).value()@,
        final(page_map_perm).value().status(index as int).is_clear(),
        forall|j: int|
            #![trigger final(page_map_perm).value().ar@[j]]
            0 <= j < 512 && j != index ==> final(page_map_perm).value().ar@[j] == old(page_map_perm).value().ar@[j],
        spec_usize2page_entry(ret) == old(page_map_perm).value()@[index as int],
{
    let ghost before = page_map_perm.value();
    let ret = page_map_take_status(page_map_ptr, Tracked(page_map_perm), index);
    proof {
        let after = page_map_perm.value();
        let w = before.ar@[index as int];
        assert((ret & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) & (!((0x1u64 << 5u64) | (0x1u64
            << 6u64))) as usize == w & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) by (bit_vector)
            requires
                ret & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize == w & (!((0x1u64 << 5u64) | (
                0x1u64 << 6u64))) as usize,
        ;
        assert((ret & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) & (0x1u64 << 5u64) as usize == 0
            && (ret & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize) & (0x1u64 << 6u64) as usize == 0)
            by (bit_vector);
        assert forall|i: int|
            #![trigger after.ar@[i]]
            0 <= i < 512 implies after.ar@[i] & status_kept_mask() == before.ar@[i] & status_kept_mask() by {}
        before.lemma_status_outside_view(&after);
        lemma_status_outside_entry(ret, w);
        assert(usize2page_entry(before.ar@[index as int]) =~= before.spec_seq@[index as int]);
    }
    ret
}

#[verifier(external_body)]
// external_body(glue): clears a hardware page table word and returns it in one atomic exchange, since another core's walk may set the accessed or dirty bit between a read and a write
pub fn page_map_take(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
) -> (ret: usize)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().ar.wf(),
        final(page_map_perm).value().spec_seq@ == old(page_map_perm).value().spec_seq@.update(index as int, usize2page_entry(0usize)),
        ret & status_kept_mask() == old(page_map_perm).value().ar@[index as int] & status_kept_mask(),
        final(page_map_perm).value().ar@ == old(page_map_perm).value().ar@.update(index as int, 0usize),
{
    unsafe {
        let word = core::ptr::addr_of_mut!((*(page_map_ptr as *mut PageMap)).ar.ar[index]);
        (*(word as *const AtomicUsize)).swap(0, Ordering::Relaxed)
    }
}

/// Clears entry `index`, returning its word as read in the same step: the word decodes to the entry the
/// table held, and its accessed and dirty bits are the processor's as they stood when it was cleared.
pub fn page_map_clear_take(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
) -> (ret: usize)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value()[i]]
            0 <= i < 512 && i != index ==> final(page_map_perm).value()[i] =~= old(
                page_map_perm,
            ).value()[i],
        final(page_map_perm).value()[index].is_empty(),
        final(page_map_perm).value().status(index as int).is_clear(),
        spec_usize2page_entry(ret) == old(page_map_perm).value()@[index as int],
{
    let ghost before = page_map_perm.value();
    let ret = page_map_take(page_map_ptr, Tracked(page_map_perm), index);
    proof {
        let after = page_map_perm.value();
        let w = before.ar@[index as int];
        zero_leads_is_empty_page_entry();
        assert(0usize & (0x1u64 << 5u64) as usize == 0 && 0usize & (0x1u64 << 6u64) as usize == 0)
            by (bit_vector);
        assert forall|i: int|
            #![trigger usize2page_entry(after.ar@[i])]
            0 <= i < 512 implies usize2page_entry(after.ar@[i]) =~= after.spec_seq@[i] by {
            if i != index as int {
                assert(usize2page_entry(before.ar@[i]) =~= before.spec_seq@[i]);
            }
        }
        assert(after.wf());
        lemma_status_outside_entry(ret, w);
        assert(usize2page_entry(w) =~= before.spec_seq@[index as int]);
    }
    ret
}

#[verifier(external_body)]
// external_body(glue): writes a hardware page table through a raw pointer
pub fn page_perm_to_page_map(page_ptr: PagePtr, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (
    PageMapPtr,
    Tracked<PointsTo<PageMap>>,
))
    requires
        page_perm.is_uninit(),
        page_perm.addr() == page_ptr,
    ensures
        ret.0 == page_ptr,
        ret.1@.addr() == ret.0,
        ret.1@.is_init(),
        ret.1@.value().wf(),
        forall|i: usize|
            #![trigger ret.1@.value()[i].is_empty()]
            0 <= i < 512 ==> ret.1@.value()[i].is_empty(),
{
    unsafe {
        let uptr = page_ptr as *mut MaybeUninit<PageMap>;
        for i in 0..512 {
            (*uptr).assume_init_mut().set(i, PageEntry::empty());
        }
    }
    (page_ptr, Tracked::assume_new())
}

pub fn flush_tlb_4kentry(tlbmap_4k: Ghost<Seq<Map<VAddr, MapEntry>>>, va: Ghost<VAddr>) -> (ret:
    Ghost<Seq<Map<VAddr, MapEntry>>>)
    requires
        NUM_CPUS > 0,
        tlbmap_4k@.len() == NUM_CPUS,
    ensures
        ret@.len() == NUM_CPUS,
        forall|cpu_id: CpuId|
            #![auto]
            0 <= cpu_id < NUM_CPUS ==> !(ret@[cpu_id as int].contains_key(va@)),
        forall|cpu_id: CpuId|
            #![auto]
            0 <= cpu_id < NUM_CPUS ==> ret@[cpu_id as int].submap_of(tlbmap_4k@[cpu_id as int]),
{
    let mut cpu_id = 0;
    let mut ret_map = tlbmap_4k;

    broadcast use map_equal_implies_submap_each_other;

    assert(forall|cpu_id: CpuId|
        #![auto]
        0 <= cpu_id < NUM_CPUS ==> ret_map@[cpu_id as int] =~= tlbmap_4k@[cpu_id as int]);
    assert(forall|cpu_id: CpuId|
        #![auto]
        0 <= cpu_id < NUM_CPUS ==> ret_map@[cpu_id as int].submap_of(tlbmap_4k@[cpu_id as int]));

    // #[verifier::loop_isolation(false)]
    for cpu_id in 0..NUM_CPUS
        invariant
            0 <= cpu_id <= NUM_CPUS,
            tlbmap_4k@.len() == NUM_CPUS,
            ret_map@.len() == NUM_CPUS,
            ret_map@[0].submap_of(tlbmap_4k@[0]),
            forall|cpu_i: CpuId|
                #![auto]
                0 <= cpu_i < cpu_id ==> ret_map@[cpu_i as int].contains_key(va@) == false,
            forall|cpu_i: CpuId|
                #![auto]
                0 <= cpu_i < cpu_id ==> ret_map@[cpu_i as int].submap_of(tlbmap_4k@[cpu_i as int]),
            forall|cpu_i: CpuId|
                #![auto]
                cpu_id <= cpu_i < NUM_CPUS ==> ret_map@[cpu_i as int].submap_of(tlbmap_4k@[cpu_i as int]),
    {
        proof {
            //assert(ret_map@[cpu_id as int].submap_of(tlbmap_4k@[cpu_id as int]));
            // prove ret_map[i] has no key va
            assert(cpu_id < ret_map@.len());
            let tlbmap = ret_map@[cpu_id as int].remove(va@);
            assert(!tlbmap.contains_key(va@));
            let tlbseq = ret_map@.update(cpu_id as int, tlbmap);
            assert(tlbseq.index(cpu_id as int) =~= tlbmap);
            assert(tlbseq.contains(tlbmap));
            ret_map@ = tlbseq;
            assert(!ret_map@[cpu_id as int].contains_key(va@));

        }
    }
    ret_map
}

} // verus!
