// SPDX-License-Identifier: MIT

//! The system calls the eager source makes, each a verified call of acall's kernel step, threading the
//! process's ghost of the kernel from one call to the next. Retype, link and map go through acall's
//! wrappers, whose ensures are their proven caller's-view contracts; unmap, which has no such contract,
//! goes through the step itself, and takes the permission to the page's bytes so that nothing the
//! source's caller holds is in the page it unmaps. The one trusted item is `page_permission`: a map the
//! kernel accepted puts the frame's page at the address in the space's tables, as the map contract
//! says, and only this item turns that into the permission to the page's bytes. The tables are what the
//! calling core reads once no translation of the address from an earlier mapping is left on it: an
//! unmap that moves the flush epoch has the calling core acknowledge before it returns, and the other
//! cores only once an IPI reaches them (design/flush-without-waiting/), so the item relies on the
//! source's thread running on the core that made each of the source's unmaps.
use vstd::prelude::*;
use vstd::raw_ptr::*;

use acall::memory;
#[cfg(verus_keep_ghost)]
use acall::memory::lemma_own_position;
use acall::step::*;
#[cfg(verus_keep_ghost)]
use aheap::arch::*;
#[cfg(verus_keep_ghost)]
use verified::capability::reach::Right;
#[cfg(verus_keep_ghost)]
use verified::capability::view::right_bit;
use verified::capability::kernel::CapKernel;
use verified::capability::operation::*;
use verified::capability::position::POSITION_INDEX_MASK;

verus! {

/// The level whose entry maps one page.
const PAGE_LEVEL: u64 = 1;

/// The write right's bit, as inspect returns rights.
const RIGHT_WRITE: u64 = 2;

/// Retypes the free page at physical `base`, inside the untyped at `untyped`, as a frame whose
/// capability goes in the empty slot `destination`. Whether the kernel accepted.
pub fn retype_frame(caller: &mut Tracked<Caller>, untyped: u64, base: u64, destination: u64) -> bool
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
    no_unwind
{
    memory::retype(caller, untyped, RETYPE_FRAME, base, destination, 0).status == STATUS_OK
}

/// Retypes the free order-3 block at physical `base`, inside the untyped at `untyped`, as an unlinked
/// table page of `level`. Whether the kernel accepted.
pub fn retype_table_page(caller: &mut Tracked<Caller>, untyped: u64, base: u64, level: u64) -> bool
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
    no_unwind
{
    memory::retype(caller, untyped, RETYPE_TABLE_PAGE, base, 0, level).status == STATUS_OK
}

/// Links the unlinked table page at physical `table`, inside the untyped at `untyped`, into the entry
/// at `level` that `address` names in the space at `space`. Whether the kernel accepted.
pub fn link(caller: &mut Tracked<Caller>, space: u64, address: usize, level: u64, untyped: u64, table: u64) -> bool
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
    no_unwind
{
    memory::link(caller, space, address as u64, level, untyped, table).status == STATUS_OK
}

/// Maps the frame whose capability is at `frame`, which no entry maps, at the page `address` in the
/// space at `space`: on success the permission to the page's bytes, with `provenance`. The frame is
/// inspected first and mapped only with the write right, so the page is one the hardware lets the
/// caller write; a frame whose capability lacks it, or a slot no inspect of the caller's own table
/// names, is refused here.
pub fn map_page(caller: &mut Tracked<Caller>, space: u64, address: usize, frame: u64, provenance: Ghost<Provenance>) -> (r: Option<Tracked<PointsToRaw>>)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        match r {
            Some(perm) => perm@.is_range(address as int, PAGE_BYTES as int) && perm@.provenance() == provenance@,
            None => true,
        },
    no_unwind
{
    if frame > POSITION_INDEX_MASK {
        return None;
    }
    proof {
        lemma_own_position(frame);
    }
    let seen = memory::inspect(caller, frame);
    if seen.status != STATUS_OK || seen.result_4 & RIGHT_WRITE == 0 {
        return None;
    }
    let ghost before = caller@.kernel();
    let ghost root = caller@.root();
    proof {
        let rights = before.table_view(root)[frame as usize].rights;
        assert(rights as u64 == seen.result_4);
        assert(rights & 2u32 != 0) by (bit_vector)
            requires
                (rights as u64) & 2u64 != 0;
    }
    let out = memory::map(caller, space, address as u64, PAGE_LEVEL, frame, 0);
    if out.status == STATUS_OK {
        Some(page_permission(Ghost(before), Ghost(caller@.kernel()), Ghost(root), space, address, frame, Ghost(out), provenance))
    } else {
        None
    }
}

/// The permission to the bytes of the page at `address`, once the kernel accepted a map of the frame
/// at `frame` there in the space at `space`, as the map contract says of the call by the process whose
/// table is at `root` that took the kernel from `before` to `after`, with the frame's capability
/// holding the write right, so the entry the map wrote is writable.
#[verifier(external_body)]
// external_body(gap): conjures the permission to a mapped page's bytes; the map contract puts the frame's page in the space's tables, writable since the frame's capability has the write right, and nothing proves that the calling thread runs in that space, that the calling core holds no translation of the address from an earlier mapping, which the kernel's unmap drops on the core that makes it before returning and the source keeps by running on that core, that no other permission covers the page or that the page is memory Rust may read and write
fn page_permission(
    before: Ghost<CapKernel>,
    after: Ghost<CapKernel>,
    root: Ghost<usize>,
    space: u64,
    address: usize,
    frame: u64,
    out: Ghost<Outcome>,
    provenance: Ghost<Provenance>,
) -> (perm: Tracked<PointsToRaw>)
    requires
        out@.status == STATUS_OK,
        CapKernel::map_contract(before@, after@, root@, space as usize, address as u64, PAGE_LEVEL, frame as usize, 0, out@),
        before@.table_view(root@)[frame as usize].rights & right_bit(Right::Write) != 0,
    ensures
        perm@.is_range(address as int, PAGE_BYTES as int),
        perm@.provenance() == provenance@,
    no_unwind
{
    Tracked::assume_new()
}

/// Unmaps the page at `address` in the space at `space`, taking the permission to its bytes. Whether
/// the kernel accepted.
pub fn unmap_page(caller: &mut Tracked<Caller>, space: u64, address: usize, perm: Tracked<PointsToRaw>) -> bool
    requires
        old(caller)@.wf(),
        perm@.is_range(address as int, PAGE_BYTES as int),
    ensures
        final(caller)@.wf(),
    no_unwind
{
    // The caller gave up the permission to every byte of the page, so nothing it uses is there.
    step(caller, OPERATION_UNMAP, space, address as u64, PAGE_LEVEL, 0, 0, 0).status == STATUS_OK
}

} // verus!
