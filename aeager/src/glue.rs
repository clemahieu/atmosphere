// SPDX-License-Identifier: MIT

//! The system calls the eager source makes, each a verified call of acall's kernel step, threading the
//! process's ghost of the kernel from one call to the next. Retype, link, map and unmap go through
//! acall's wrappers, whose ensures are their proven caller's-view contracts, and unmap takes the
//! permission to the page's bytes so that nothing the source's caller holds is in the page it unmaps. The one trusted item is `page_permission`: a map the
//! kernel accepted puts the frame's page at the address in the space's tables, as the map contract
//! says, and only this item turns that into the permission to the page's bytes. The tables are what the
//! calling core reads once no translation of the address from an earlier mapping is left on it: every
//! call returns with its core caught up on the flush epoch, whichever core's unmap moved it
//! (design/flush-without-waiting/), as acall's step says, so map_page has that from the map's own step.
//! No other entry maps the frame's page when the map returns: the frames the source holds are threaded
//! through every call here, and the page's block is counted by the frame's capability and the map's
//! entry alone. The item relies on no other entry coming to map the page, and on the entry at the
//! address keeping that frame or none, until `unmap_page` takes the permission back: verified code
//! holding the caller can map the frame again through acall's map, and nothing ties the entry to the
//! kernel's state once the map returns.
use vstd::prelude::*;
use vstd::iset::ISet;
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
use verified::capability::caller::view_frame;
#[cfg(verus_keep_ghost)]
use verified::capability::view::right_bit;
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::refs::{block_ref, block_refs, block_typed, blocks_refs_changed};
#[cfg(verus_keep_ghost)]
use verified::capability::link::tree_of;
#[cfg(verus_keep_ghost)]
use verified::capability::map::{address_path, frame_map_entry, walk_table};
#[cfg(verus_keep_ghost)]
use verified::capability::mapping::{space_mapping, walk};
#[cfg(verus_keep_ghost)]
use verified::capability::table::block_bytes;
#[cfg(verus_keep_ghost)]
use verified::define::PAGE_SZ;
use verified::capability::operation::*;
use verified::capability::position::POSITION_INDEX_MASK;

verus! {

/// The count of the block that holds page `page`: one for each capability that holds the block and
/// one for each entry that maps a page of it.
pub open spec fn frame_refs(k: CapKernel, page: usize) -> usize {
    block_refs(&k.blocks, block_ref(&k.blocks, page))
}

/// The first page of the block the capability at `slot` of the table at `root` holds.
pub open spec fn slot_page(k: CapKernel, root: usize, slot: usize) -> usize {
    view_frame(k.table_view(root)[slot], 0)
}

/// The frames a source holds, by key: each `(slot, at)` is a one-page frame capability at `slot` of the
/// table at `root`, mapped at the address `at` in the space keyed at `root` by the one entry there that
/// maps its page, its block counting that capability and that entry alone, or mapped nowhere, its block
/// counting the capability alone. No two hold the same block.
pub open spec fn frames_held(k: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>) -> bool {
    let v = k.table_view(root);
    let m = space_mapping(tree_of(&k.table_pages, &k.spaces), root);
    &&& forall|i: int| #[trigger] frames.contains_key(i) ==> {
        let slot = frames[i].0;
        &&& v.contains_key(slot)
        &&& v[slot].kind is Frame
        &&& v[slot].order == 0
        &&& frame_refs(k, slot_page(k, root, slot)) == if frames[i].1 is Some { 2usize } else { 1usize }
        &&& frames[i].1 is Some ==> {
            &&& m.contains_key(address_path(frames[i].1->0 as u64))
            &&& m[address_path(frames[i].1->0 as u64)].addr / PAGE_SZ == slot_page(k, root, slot)
        }
    }
    &&& forall|i: int, j: int|
        frames.contains_key(i) && frames.contains_key(j) && i != j ==> block_ref(&k.blocks, slot_page(k, root, #[trigger] frames[i].0))
            != block_ref(&k.blocks, slot_page(k, root, #[trigger] frames[j].0))
}

/// The page a frame capability in a table's view holds first is a page the block table tracks, in a
/// typed block, at the capability's base.
pub proof fn lemma_slot_page(k: CapKernel, root: usize, slot: usize)
    requires
        k.wf(),
        k.table_view(root).contains_key(slot),
        k.table_view(root)[slot].kind is Frame,
    ensures
        k.blocks.tracks(slot_page(k, root, slot) as int),
        block_typed(&k.blocks, block_ref(&k.blocks, slot_page(k, root, slot))),
        slot_page(k, root, slot) * PAGE_SZ == k.table_view(root)[slot].base,
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(0 < block_bytes(k.table_view(root)[slot].order)) by {
        vstd::arithmetic::power2::lemma_pow2_pos(k.table_view(root)[slot].order as nat);
    }
    k.lemma_table_view(root, slot);
    let n = k.tables.node_of(root, slot);
    k.lemma_frame_page(n, 0);
}

/// Every frame capability the source holds is in the table's view: each key's slot is one.
pub proof fn lemma_frames_slots(k: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>)
    requires
        k.wf(),
        frames_held(k, root, frames),
    ensures
        forall|i: int| #[trigger] frames.contains_key(i) ==> {
            &&& k.blocks.tracks(slot_page(k, root, frames[i].0) as int)
            &&& block_typed(&k.blocks, block_ref(&k.blocks, slot_page(k, root, frames[i].0)))
            &&& slot_page(k, root, frames[i].0) * PAGE_SZ == k.table_view(root)[frames[i].0].base
        },
{
    assert forall|i: int| #[trigger] frames.contains_key(i) implies {
        &&& k.blocks.tracks(slot_page(k, root, frames[i].0) as int)
        &&& block_typed(&k.blocks, block_ref(&k.blocks, slot_page(k, root, frames[i].0)))
        &&& slot_page(k, root, frames[i].0) * PAGE_SZ == k.table_view(root)[frames[i].0].base
    } by {
        lemma_slot_page(k, root, frames[i].0);
    }
}

/// A step that leaves the root's table view, every block and the root's space's mapping as they were
/// keeps every frame the source holds.
pub proof fn lemma_frames_same(pre: CapKernel, post: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>)
    requires
        frames_held(pre, root, frames),
        post.table_view(root) == pre.table_view(root),
        post.blocks == pre.blocks,
        space_mapping(tree_of(&post.table_pages, &post.spaces), root) == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root),
    ensures
        frames_held(post, root, frames),
{
}

/// Dropping a frame keeps the rest held.
pub proof fn lemma_frames_drop(k: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>, key: int)
    requires
        frames_held(k, root, frames),
    ensures
        frames_held(k, root, frames.remove(key)),
{
    let f = frames.remove(key);
    assert forall|i: int| #[trigger] f.contains_key(i) implies frames.contains_key(i) && f[i] == frames[i] by {}
    assert forall|i: int, j: int| f.contains_key(i) && f.contains_key(j) && i != j implies block_ref(&k.blocks, slot_page(k, root, #[trigger] f[i].0))
        != block_ref(&k.blocks, slot_page(k, root, #[trigger] f[j].0)) by {
        assert(frames[i] == f[i] && frames[j] == f[j]);
    }
}

/// A step that leaves the root's table view as it was, every frame capability's blocks and their counts
/// as they were, and every space's mapping as it was keeps every frame the source holds.
pub proof fn lemma_frames_kept(pre: CapKernel, post: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>)
    requires
        pre.wf(),
        frames_held(pre, root, frames),
        post.table_view(root) == pre.table_view(root),
        CapKernel::frame_blocks_kept(pre, post),
        CapKernel::mappings_kept(pre, post),
    ensures
        frames_held(post, root, frames),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(space_mapping(tree_of(&post.table_pages, &post.spaces), root) == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root));
    assert forall|i: int| #[trigger] frames.contains_key(i) implies block_ref(&post.blocks, slot_page(pre, root, frames[i].0))
        == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0)) && frame_refs(post, slot_page(pre, root, frames[i].0))
        == frame_refs(pre, slot_page(pre, root, frames[i].0)) by {
        let j = frames[i].0;
        assert((0 as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order));
        assert(block_ref(&post.blocks, view_frame(pre.table_view(root)[j], 0)) == block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], 0)));
    }
    assert forall|i: int, j: int| frames.contains_key(i) && frames.contains_key(j) && i != j implies block_ref(&post.blocks, slot_page(post, root, #[trigger] frames[i].0))
        != block_ref(&post.blocks, slot_page(post, root, #[trigger] frames[j].0)) by {
        assert(frames.contains_key(i) && frames.contains_key(j));
    }
}

/// A frame retype into `slot`, a slot no frame the source holds is in, while every frame the source
/// holds is mapped, keeps each and holds the new frame, mapped nowhere: its block has a count of one
/// and every other frame's two, so no other frame holds that block.
proof fn lemma_frames_retyped(
    pre: CapKernel,
    post: CapKernel,
    root: usize,
    frames: Map<int, (usize, Option<usize>)>,
    key: int,
    slot: usize,
    base: usize,
    parent: usize,
)
    requires
        pre.wf(),
        post.wf(),
        frames_held(pre, root, frames),
        !frames.contains_key(key),
        forall|i: int| #[trigger] frames.contains_key(i) ==> frames[i].1 is Some && frames[i].0 != slot,
        post.table_view(root) == pre.table_view(root).insert(slot, verified::capability::caller::frame_view(base, 0, parent)),
        block_refs(&post.blocks, block_ref(&post.blocks, base / PAGE_SZ)) == 1,
        CapKernel::frame_blocks_kept(pre, post),
        CapKernel::mappings_kept(pre, post),
    ensures
        frames_held(post, root, frames.insert(key, (slot, None))),
{
    vstd::arithmetic::power2::lemma2_to64();
    let f = frames.insert(key, (slot, None::<usize>));
    assert(space_mapping(tree_of(&post.table_pages, &post.spaces), root) == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root));
    assert(slot_page(post, root, slot) == base / PAGE_SZ);
    assert forall|i: int| #[trigger] frames.contains_key(i) implies {
        &&& slot_page(post, root, frames[i].0) == slot_page(pre, root, frames[i].0)
        &&& block_ref(&post.blocks, slot_page(pre, root, frames[i].0)) == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0))
        &&& frame_refs(post, slot_page(pre, root, frames[i].0)) == 2
    } by {
        let j = frames[i].0;
        assert((0 as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order));
        assert(block_ref(&post.blocks, view_frame(pre.table_view(root)[j], 0)) == block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], 0)));
    }
    assert forall|i: int| #[trigger] f.contains_key(i) implies {
        let slot = f[i].0;
        let v = post.table_view(root);
        let m = space_mapping(tree_of(&post.table_pages, &post.spaces), root);
        &&& v.contains_key(slot)
        &&& v[slot].kind is Frame
        &&& v[slot].order == 0
        &&& frame_refs(post, slot_page(post, root, slot)) == if f[i].1 is Some { 2usize } else { 1usize }
        &&& f[i].1 is Some ==> {
            &&& m.contains_key(address_path(f[i].1->0 as u64))
            &&& m[address_path(f[i].1->0 as u64)].addr / PAGE_SZ == slot_page(post, root, slot)
        }
    } by {
        if i != key {
            assert(frames.contains_key(i));
        }
    }
    assert forall|i: int, j: int| f.contains_key(i) && f.contains_key(j) && i != j implies block_ref(&post.blocks, slot_page(post, root, #[trigger] f[i].0))
        != block_ref(&post.blocks, slot_page(post, root, #[trigger] f[j].0)) by {
        if i != key {
            assert(frames.contains_key(i));
        }
        if j != key {
            assert(frames.contains_key(j));
        }
    }
}

/// A map at `address` of the frame the source holds under `key`, mapped nowhere, in the space keyed at
/// `root`, which the kernel accepted, keeps every other frame and holds that one mapped there: its block
/// counts its capability and the new entry, and the entry went to a path where no frame was mapped.
proof fn lemma_frames_mapped(
    pre: CapKernel,
    post: CapKernel,
    root: usize,
    space: usize,
    address: usize,
    frames: Map<int, (usize, Option<usize>)>,
    key: int,
    out: Outcome,
)
    requires
        pre.wf(),
        frames_held(pre, root, frames),
        frames.contains_key(key),
        frames[key].1 is None,
        pre.table_view(root)[space].base == root,
        CapKernel::map_contract(pre, post, root, space, address as u64, PAGE_LEVEL, frames[key].0, 0, out),
        out.status == STATUS_OK,
    ensures
        frames_held(post, root, frames.insert(key, (frames[key].0, Some(address)))),
        frame_refs(post, slot_page(pre, root, frames[key].0)) == 2,
{
    vstd::arithmetic::power2::lemma2_to64();
    lemma_frames_slots(pre, root, frames);
    let f = frames.insert(key, (frames[key].0, Some(address)));
    let from = frames[key].0;
    let v = pre.table_view(root);
    let a = tree_of(&pre.table_pages, &pre.spaces);
    let b = tree_of(&post.table_pages, &post.spaces);
    let p = address_path(address as u64);
    let br = block_ref(&pre.blocks, slot_page(pre, root, from));
    assert(pre.map_allowed(root, space, address as u64, PAGE_LEVEL, from, 0));
    assert(!space_mapping(a, root).contains_key(p)) by {
        let t = walk_table(a, root, p)->0;
        assert(a.entry(t, p.l1).is_empty());
        assert(walk(a, root, p) is None);
    }
    assert(space_mapping(b, root) == space_mapping(a, root).insert(p, frame_map_entry(slot_page(pre, root, from), v[from].rights, false)));
    assert(blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, verified::capability::refs::block_dead(&pre.blocks, br)));
    let page = slot_page(pre, root, from);
    assert((page * PAGE_SZ) as usize / PAGE_SZ == page) by {
        assert(page * PAGE_SZ == v[from].base);
        assert((page as int * PAGE_SZ as int) / PAGE_SZ as int == page as int) by (nonlinear_arith)
            requires PAGE_SZ > 0;
    }
    assert(frame_refs(post, page) == 2) by {
        assert(block_ref(&post.blocks, page) == br);
    }
    assert forall|i: int| #[trigger] frames.contains_key(i) && i != key implies {
        &&& block_ref(&post.blocks, slot_page(pre, root, frames[i].0)) == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0))
        &&& frame_refs(post, slot_page(pre, root, frames[i].0)) == frame_refs(pre, slot_page(pre, root, frames[i].0))
        &&& frames[i].1 is Some ==> address_path(frames[i].1->0 as u64) != p
    } by {
        let x = block_ref(&pre.blocks, slot_page(pre, root, frames[i].0));
        assert(block_typed(&pre.blocks, x));
        assert(x != br);
    }
    assert forall|i: int| #[trigger] frames.contains_key(i) implies block_ref(&post.blocks, slot_page(post, root, frames[i].0))
        == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0)) by {
        assert(slot_page(post, root, frames[i].0) == slot_page(pre, root, frames[i].0));
    }
    assert forall|i: int| #[trigger] f.contains_key(i) implies {
        let slot = f[i].0;
        let w = post.table_view(root);
        let m = space_mapping(b, root);
        &&& w.contains_key(slot)
        &&& w[slot].kind is Frame
        &&& w[slot].order == 0
        &&& frame_refs(post, slot_page(post, root, slot)) == if f[i].1 is Some { 2usize } else { 1usize }
        &&& f[i].1 is Some ==> {
            &&& m.contains_key(address_path(f[i].1->0 as u64))
            &&& m[address_path(f[i].1->0 as u64)].addr / PAGE_SZ == slot_page(post, root, slot)
        }
    } by {
        assert(post.table_view(root) == v);
        if i != key {
            assert(frames.contains_key(i));
        }
    }
    assert forall|i: int, j: int| f.contains_key(i) && f.contains_key(j) && i != j implies block_ref(&post.blocks, slot_page(post, root, #[trigger] f[i].0))
        != block_ref(&post.blocks, slot_page(post, root, #[trigger] f[j].0)) by {
        assert(frames.contains_key(i) && frames.contains_key(j));
        assert(f[i].0 == frames[i].0 && f[j].0 == frames[j].0);
    }
}

/// An unmap at `address` of the frame the source holds under `key`, mapped there in the space keyed at
/// `root`, which the kernel accepted, keeps every other frame and holds that one mapped nowhere: the
/// entry it removed was that frame's, so that frame's block lost the count.
proof fn lemma_frames_unmapped(
    pre: CapKernel,
    post: CapKernel,
    root: usize,
    space: usize,
    address: usize,
    frames: Map<int, (usize, Option<usize>)>,
    key: int,
    out: Outcome,
)
    requires
        pre.wf(),
        frames_held(pre, root, frames),
        frames.contains_key(key),
        frames[key].1 == Some(address),
        pre.table_view(root)[space].base == root,
        CapKernel::unmap_contract(pre, post, root, space, address as u64, PAGE_LEVEL, out),
        out.status == STATUS_OK,
    ensures
        frames_held(post, root, frames.insert(key, (frames[key].0, None))),
{
    lemma_frames_slots(pre, root, frames);
    let f = frames.insert(key, (frames[key].0, None::<usize>));
    let from = frames[key].0;
    let v = pre.table_view(root);
    let a = tree_of(&pre.table_pages, &pre.spaces);
    let b = tree_of(&post.table_pages, &post.spaces);
    let p = address_path(address as u64);
    let page = slot_page(pre, root, from);
    let br = block_ref(&pre.blocks, page);
    assert(space_mapping(a, root)[p].addr / PAGE_SZ == page);
    assert(space_mapping(b, root) == space_mapping(a, root).remove(p));
    assert(blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) - 1) as usize,
        verified::capability::refs::block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1));
    assert(frame_refs(post, page) == 1) by {
        assert(block_ref(&post.blocks, page) == br);
    }
    assert forall|i: int| #[trigger] frames.contains_key(i) && i != key implies {
        &&& block_ref(&post.blocks, slot_page(pre, root, frames[i].0)) == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0))
        &&& frame_refs(post, slot_page(pre, root, frames[i].0)) == frame_refs(pre, slot_page(pre, root, frames[i].0))
        &&& frames[i].1 is Some ==> address_path(frames[i].1->0 as u64) != p
    } by {
        let x = block_ref(&pre.blocks, slot_page(pre, root, frames[i].0));
        assert(block_typed(&pre.blocks, x));
        assert(x != br);
    }
    assert forall|i: int| #[trigger] frames.contains_key(i) implies block_ref(&post.blocks, slot_page(post, root, frames[i].0))
        == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0)) by {
        assert(slot_page(post, root, frames[i].0) == slot_page(pre, root, frames[i].0));
    }
    assert forall|i: int| #[trigger] f.contains_key(i) implies {
        let slot = f[i].0;
        let w = post.table_view(root);
        let m = space_mapping(b, root);
        &&& w.contains_key(slot)
        &&& w[slot].kind is Frame
        &&& w[slot].order == 0
        &&& frame_refs(post, slot_page(post, root, slot)) == if f[i].1 is Some { 2usize } else { 1usize }
        &&& f[i].1 is Some ==> {
            &&& m.contains_key(address_path(f[i].1->0 as u64))
            &&& m[address_path(f[i].1->0 as u64)].addr / PAGE_SZ == slot_page(post, root, slot)
        }
    } by {
        assert(post.table_view(root) == v);
        if i != key {
            assert(frames.contains_key(i));
        }
    }
    assert forall|i: int, j: int| f.contains_key(i) && f.contains_key(j) && i != j implies block_ref(&post.blocks, slot_page(post, root, #[trigger] f[i].0))
        != block_ref(&post.blocks, slot_page(post, root, #[trigger] f[j].0)) by {
        assert(frames.contains_key(i) && frames.contains_key(j));
        assert(f[i].0 == frames[i].0 && f[j].0 == frames[j].0);
    }
}

/// The slot at `space` of the caller's own table holds a capability naming the space keyed at the
/// caller's root, which is its own process's space.
pub open spec fn names_own_space(caller: Caller, space: u64) -> bool {
    let v = caller.kernel().table_view(caller.root());
    &&& v.contains_key(space as usize)
    &&& v[space as usize].base == caller.root()
}

/// Every slot that names the caller's own space in `pre` still does in `post`.
pub open spec fn keeps_own_space(pre: Caller, post: Caller) -> bool {
    forall|space: u64| #[trigger] names_own_space(pre, space) ==> names_own_space(post, space)
}

/// The level whose entry maps one page.
const PAGE_LEVEL: u64 = 1;

/// The write right's bit, as inspect returns rights.
const RIGHT_WRITE: u64 = 2;

/// Retypes the free page at physical `base`, inside the untyped at `untyped`, as a frame whose
/// capability goes in the empty slot `destination`. Whether the kernel accepted. Every frame of `frames`
/// is mapped and none is in `destination`; each is kept, and the new frame, mapped nowhere, is held under
/// `key` once the kernel accepted.
pub fn retype_frame(caller: &mut Tracked<Caller>, untyped: u64, base: u64, destination: u64, frames: Ghost<Map<int, (usize, Option<usize>)>>, key: Ghost<int>) -> (r: bool)
    requires
        old(caller)@.wf(),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
        !frames@.contains_key(key@),
        forall|i: int| #[trigger] frames@.contains_key(i) ==> frames@[i].1 is Some && frames@[i].0 != destination as usize,
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        keeps_own_space(old(caller)@, final(caller)@),
        r ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.insert(key@, (destination as usize, None))),
        !r ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@),
    no_unwind
{
    let ghost pre = caller@;
    let out = memory::retype(caller, untyped, RETYPE_FRAME, base, destination, 0);
    proof {
        // A frame goes only into an empty slot, which holds no capability, so not the one naming the space.
        assert forall|space: u64| #[trigger] names_own_space(pre, space) implies names_own_space(caller@, space) by {
            pre.kernel().lemma_table_view(pre.root(), destination as usize);
        }
        let root = pre.root();
        if out.status == STATUS_OK {
            let parent = pre.kernel().tables.node_of(root, untyped as usize);
            lemma_frames_retyped(pre.kernel(), caller@.kernel(), root, frames@, key@, destination as usize, base as usize, parent);
        } else {
            lemma_frames_same(pre.kernel(), caller@.kernel(), root, frames@);
        }
    }
    out.status == STATUS_OK
}

/// Retypes the free order-3 block at physical `base`, inside the untyped at `untyped`, as an unlinked
/// table page of `level`. Whether the kernel accepted.
/// Every frame of `frames` is kept.
pub fn retype_table_page(caller: &mut Tracked<Caller>, untyped: u64, base: u64, level: u64, frames: Ghost<Map<int, (usize, Option<usize>)>>) -> bool
    requires
        old(caller)@.wf(),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        keeps_own_space(old(caller)@, final(caller)@),
        frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@),
    no_unwind
{
    let ghost pre = caller@;
    let out = memory::retype(caller, untyped, RETYPE_TABLE_PAGE, base, 0, level);
    proof {
        if out.status == STATUS_OK {
            lemma_frames_kept(pre.kernel(), caller@.kernel(), pre.root(), frames@);
        } else {
            lemma_frames_same(pre.kernel(), caller@.kernel(), pre.root(), frames@);
        }
    }
    out.status == STATUS_OK
}

/// Links the unlinked table page at physical `table`, inside the untyped at `untyped`, into the entry
/// at `level` that `address` names in the space at `space`. Whether the kernel accepted.
/// Every frame of `frames` is kept.
pub fn link(caller: &mut Tracked<Caller>, space: u64, address: usize, level: u64, untyped: u64, table: u64, frames: Ghost<Map<int, (usize, Option<usize>)>>) -> bool
    requires
        old(caller)@.wf(),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        keeps_own_space(old(caller)@, final(caller)@),
        frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@),
    no_unwind
{
    let ghost pre = caller@;
    let out = memory::link(caller, space, address as u64, level, untyped, table);
    proof {
        assert(space_mapping(tree_of(&caller@.kernel().table_pages, &caller@.kernel().spaces), pre.root())
            == space_mapping(tree_of(&pre.kernel().table_pages, &pre.kernel().spaces), pre.root()));
        lemma_frames_same(pre.kernel(), caller@.kernel(), pre.root(), frames@);
    }
    out.status == STATUS_OK
}

/// Maps the frame whose capability is at `frame`, which the source holds under `key` of `frames`,
/// mapped nowhere, at the page `address` in the space at `space`: on success the permission to the
/// page's bytes, with `provenance`, and the frame held mapped there; otherwise every frame kept. The frame is
/// inspected first and mapped only with the write right, so the page is one the hardware lets the
/// caller write; a frame whose capability lacks it, or a slot no inspect of the caller's own table
/// names, is refused here. The slot at `space` names the caller's own space, the one its thread runs
/// in. `live` holds every address of the window whose page's permission the caller holds or has handed
/// out, and `address` is not among them.
pub fn map_page(
    caller: &mut Tracked<Caller>,
    space: u64,
    address: usize,
    frame: u64,
    provenance: Ghost<Provenance>,
    live: Ghost<ISet<usize>>,
    frames: Ghost<Map<int, (usize, Option<usize>)>>,
    key: Ghost<int>,
) -> (r: Option<Tracked<PointsToRaw>>)
    requires
        old(caller)@.wf(),
        names_own_space(old(caller)@, space),
        !live@.contains(address),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
        frames@.contains_key(key@),
        frames@[key@] == (frame as usize, None::<usize>),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        keeps_own_space(old(caller)@, final(caller)@),
        match r {
            Some(perm) => {
                &&& perm@.is_range(address as int, PAGE_BYTES as int)
                &&& perm@.provenance() == provenance@
                &&& frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.insert(key@, (frame as usize, Some(address))))
            },
            None => frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@),
        },
    no_unwind
{
    if frame > POSITION_INDEX_MASK {
        return None;
    }
    proof {
        lemma_own_position(frame);
    }
    let ghost first = caller@;
    let seen = memory::inspect(caller, frame);
    proof {
        assert(space_mapping(tree_of(&caller@.kernel().table_pages, &caller@.kernel().spaces), first.root())
            == space_mapping(tree_of(&first.kernel().table_pages, &first.kernel().spaces), first.root()));
        lemma_frames_same(first.kernel(), caller@.kernel(), first.root(), frames@);
    }
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
    proof {
        if out.status == STATUS_OK {
            lemma_frames_mapped(before, caller@.kernel(), root, space as usize, address, frames@, key@, out);
        } else {
            lemma_frames_same(before, caller@.kernel(), root, frames@);
        }
    }
    if out.status == STATUS_OK {
        Some(page_permission(Ghost(before), Ghost(caller@.kernel()), Ghost(root), space, address, frame, Ghost(out), provenance, live))
    } else {
        None
    }
}

/// The permission to the bytes of the page at `address`, once the kernel accepted a map of the frame
/// at `frame` there in the space at `space`, as the map contract says of the call by the process whose
/// table is at `root` that took the kernel from `before` to `after`, with the frame's capability
/// holding the write right, so the entry the map wrote is writable, the kernel holding the
/// permission of the frame's page, as it has since boot, and the frame's block counted by its
/// capability and the entry the map wrote alone, so no other entry maps the page when the map returns;
/// nothing proves that none comes to map it before `unmap_page` takes the permission back. The slot
/// at `space` names the caller's own space, which a core had loaded across the call and which that core, the one the call ran on,
/// returned from caught up on the flush epoch, holding nothing stale of the space. `live` holds every address
/// of the window whose page's permission the caller holds or has handed out, and `address` is not among
/// them.
#[verifier(external_body)]
// external_body(gap): conjures the permission to a mapped page's bytes; the map contract puts the frame's page in the space's tables, writable since the frame's capability has the write right, its block counted twice, by that capability and that entry, so no other entry in any space maps it when the map returns, with the kernel holding that page's permission as it has since boot, and the core that made the call holding that space, the caller's own, loaded and caught up on the flush epoch, holding no translation of that space to a page no space maps, as the step says, and nothing proves that no permission outside the ones live names covers the page, which the creator of the source promises by handing it a window nothing else maps, that no other entry, in this space or another, comes to map the frame's page until unmap_page takes the permission back, which verified code holding the caller can make through acall's map or through a derived copy of the frame's capability mapped elsewhere, that the entry at the address keeps that frame or none until unmap_page takes the permission back, which nothing ties to the kernel's state once the map returns, that a core loads and stores the page's bytes through that entry, or that those bytes may be held as a PointsToRaw
fn page_permission(
    before: Ghost<CapKernel>,
    after: Ghost<CapKernel>,
    root: Ghost<usize>,
    space: u64,
    address: usize,
    frame: u64,
    out: Ghost<Outcome>,
    provenance: Ghost<Provenance>,
    live: Ghost<ISet<usize>>,
) -> (perm: Tracked<PointsToRaw>)
    requires
        out@.status == STATUS_OK,
        !live@.contains(address),
        CapKernel::map_contract(before@, after@, root@, space as usize, address as u64, PAGE_LEVEL, frame as usize, 0, out@),
        before@.table_view(root@)[space as usize].base == root@,
        returned_on(before@, after@, before@.table_view(root@)[space as usize].base),
        before@.table_view(root@)[frame as usize].rights & right_bit(Right::Write) != 0,
        after@.frames@.contains_key(view_frame(before@.table_view(root@)[frame as usize], 0)),
        frame_refs(after@, view_frame(before@.table_view(root@)[frame as usize], 0)) == 2,
    ensures
        perm@.is_range(address as int, PAGE_BYTES as int),
        perm@.provenance() == provenance@,
    no_unwind
{
    Tracked::assume_new()
}

/// Unmaps the page at `address` in the space at `space`, the caller's own, taking the permission to its
/// bytes. Whether the kernel accepted. The frame the source holds under `key` of `frames` is the one
/// mapped there: once the kernel accepted it is held mapped nowhere, and otherwise it is dropped.
pub fn unmap_page(
    caller: &mut Tracked<Caller>,
    space: u64,
    address: usize,
    perm: Tracked<PointsToRaw>,
    frames: Ghost<Map<int, (usize, Option<usize>)>>,
    key: Ghost<int>,
) -> (r: bool)
    requires
        old(caller)@.wf(),
        names_own_space(old(caller)@, space),
        perm@.is_range(address as int, PAGE_BYTES as int),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
        frames@.contains_key(key@),
        frames@[key@].1 == Some(address),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        keeps_own_space(old(caller)@, final(caller)@),
        r ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.insert(key@, (frames@[key@].0, None))),
        !r ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.remove(key@)),
    no_unwind
{
    let ghost pre = caller@;
    // The caller gave up the permission to every byte of the page, so nothing it uses is there.
    let out = memory::unmap(caller, space, address as u64, PAGE_LEVEL);
    proof {
        let root = pre.root();
        assert forall|s: u64| #[trigger] names_own_space(pre, s) implies names_own_space(caller@, s) by {
            assert(caller@.kernel().table_view(root) == pre.kernel().table_view(root));
        }
        if out.status == STATUS_OK {
            lemma_frames_unmapped(pre.kernel(), caller@.kernel(), root, space as usize, address, frames@, key@, out);
        } else {
            lemma_frames_same(pre.kernel(), caller@.kernel(), root, frames@);
            lemma_frames_drop(caller@.kernel(), root, frames@, key@);
        }
    }
    out.status == STATUS_OK
}

} // verus!
