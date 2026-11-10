use vstd::prelude::*;

verus! {

use crate::arch::*;
use crate::define::*;
use crate::pptr::*;
use crate::util::page_ptr_util_u::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicUsize, Ordering};
use crate::array::Array;

pub fn page_map_set_kernel_entry_range(
    kernel_entries: &Array<usize, KERNEL_MEM_END_L4INDEX>,
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        old(page_map_perm).value().level@ == 4,
        kernel_entries.wf(),
        kernel_entries@.len() == KERNEL_MEM_END_L4INDEX,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().level == old(page_map_perm).value().level,
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
                4,
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
            page_map_perm.value().level == old(page_map_perm).value().level,
            page_map_perm.value().level@ == 4,
            forall|i: usize|
                #![trigger page_map_perm.value()[i]]
                KERNEL_MEM_END_L4INDEX <= i < 512 ==> page_map_perm.value()[i] =~= old(
                    page_map_perm,
                ).value()[i],
            forall|i: usize|
                #![trigger page_map_perm.value()[i]]
                0 <= i < index ==> page_map_perm.value()[i] =~= usize2page_entry(
                    kernel_entries@[i as int],
                    4,
                ),
    {
        page_map_set_no_requires(
            page_map_ptr,
            Tracked(page_map_perm),
            index,
            usize2page_entry(*kernel_entries.get(index), 4),
            4,
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
    level: usize,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        level == old(page_map_perm).value().level@,
        0 <= index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().level == old(page_map_perm).value().level,
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
        (*uptr).assume_init_mut().set(index, value, level);
    }
}

#[verifier(external_body)]
// external_body(glue): writes a hardware page table through a raw pointer
pub fn page_map_set(
    page_map_ptr: PageMapPtr,
    Tracked(page_map_perm): Tracked<&mut PointsTo<PageMap>>,
    index: usize,
    value: PageEntry,
    level: usize,
)
    requires
        old(page_map_perm).addr() == page_map_ptr,
        old(page_map_perm).is_init(),
        old(page_map_perm).value().wf(),
        level == old(page_map_perm).value().level@,
        value.perm.present ==> MEM_valid(value.addr),
        value.perm.present == false ==> value.is_empty(),
        0 <= index < 512,
    ensures
        final(page_map_perm).addr() == page_map_ptr,
        final(page_map_perm).is_init(),
        final(page_map_perm).value().level == old(page_map_perm).value().level,
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
        (*uptr).assume_init_mut().set(index, value, level);
    }
}

#[verifier(external_body)]
// external_body(glue): replaces a hardware page table word with the arch module's without_status of it in a compare-exchange, since another core's walk may set a status bit between a read and a write
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
        final(page_map_perm).value().level == old(page_map_perm).value().level,
        final(page_map_perm).value().ar.wf(),
        final(page_map_perm).value().spec_seq == old(page_map_perm).value().spec_seq,
        spec_without_status(ret) == spec_without_status(old(page_map_perm).value().ar@[index as int]),
        final(page_map_perm).value().ar@ == old(page_map_perm).value().ar@.update(index as int, spec_without_status(ret)),
{
    unsafe {
        let word = core::ptr::addr_of_mut!((*(page_map_ptr as *mut PageMap)).ar.ar[index]);
        (*(word as *const AtomicUsize)).update(Ordering::Relaxed, Ordering::Relaxed, without_status)
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
        final(page_map_perm).value().level == old(page_map_perm).value().level,
        final(page_map_perm).value().wf(),
        final(page_map_perm).value()@ == old(page_map_perm).value()@,
        final(page_map_perm).value().status(index as int).is_clear(),
        forall|j: int|
            #![trigger final(page_map_perm).value().ar@[j]]
            0 <= j < 512 && j != index ==> final(page_map_perm).value().ar@[j] == old(page_map_perm).value().ar@[j],
        spec_usize2page_entry(ret, old(page_map_perm).value().level@) == old(page_map_perm).value()@[index as int],
{
    let ghost before = page_map_perm.value();
    let ret = page_map_take_status(page_map_ptr, Tracked(page_map_perm), index);
    proof {
        let after = page_map_perm.value();
        let w = before.ar@[index as int];
        lemma_without_status(ret, before.level@);
        assert forall|i: int|
            #![trigger after.ar@[i]]
            0 <= i < 512 implies spec_without_status(after.ar@[i]) == spec_without_status(before.ar@[i]) by {}
        before.lemma_status_outside_view(&after);
        lemma_status_outside_entry(ret, w, before.level@);
        assert(usize2page_entry(before.ar@[index as int], before.level@) =~= before.spec_seq@[index as int]);
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
        final(page_map_perm).value().level == old(page_map_perm).value().level,
        final(page_map_perm).value().ar.wf(),
        final(page_map_perm).value().spec_seq@ == old(page_map_perm).value().spec_seq@.update(index as int, usize2page_entry(0usize, old(page_map_perm).value().level@)),
        spec_without_status(ret) == spec_without_status(old(page_map_perm).value().ar@[index as int]),
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
        final(page_map_perm).value().level == old(page_map_perm).value().level,
        final(page_map_perm).value().wf(),
        forall|i: usize|
            #![trigger final(page_map_perm).value()[i]]
            0 <= i < 512 && i != index ==> final(page_map_perm).value()[i] =~= old(
                page_map_perm,
            ).value()[i],
        final(page_map_perm).value()[index].is_empty(),
        final(page_map_perm).value().status(index as int).is_clear(),
        spec_usize2page_entry(ret, old(page_map_perm).value().level@) == old(page_map_perm).value()@[index as int],
{
    let ghost before = page_map_perm.value();
    let ret = page_map_take(page_map_ptr, Tracked(page_map_perm), index);
    proof {
        let after = page_map_perm.value();
        let w = before.ar@[index as int];
        let level = before.level@;
        zero_leads_is_empty_page_entry(level);
        assert forall|i: int|
            #![trigger usize2page_entry(after.ar@[i], after.level@)]
            0 <= i < 512 implies usize2page_entry(after.ar@[i], after.level@) =~= after.spec_seq@[i] by {
            if i != index as int {
                assert(usize2page_entry(before.ar@[i], level) =~= before.spec_seq@[i]);
            }
        }
        assert(after.wf());
        lemma_status_outside_entry(ret, w, level);
        assert(usize2page_entry(w, level) =~= before.spec_seq@[index as int]);
    }
    ret
}

#[verifier(external_body)]
// external_body(glue): writes a hardware page table through a raw pointer
pub fn page_perm_to_page_map(page_ptr: PagePtr, level: Ghost<usize>, Tracked(page_perm): Tracked<PagePerm4k>) -> (ret: (
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
        ret.1@.value().level == level,
        forall|i: usize|
            #![trigger ret.1@.value()[i].is_empty()]
            0 <= i < 512 ==> ret.1@.value()[i].is_empty(),
{
    unsafe {
        let uptr = page_ptr as *mut MaybeUninit<PageMap>;
        (*uptr).assume_init_mut().init();
    }
    (page_ptr, Tracked::assume_new())
}

} // verus!
