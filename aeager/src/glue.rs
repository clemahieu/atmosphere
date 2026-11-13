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
//! entry alone. What the source knows of its frames, its space and its process is stated in the form the
//! kernel's rely keeps, removal only, so `lemma_frames_rely` carries it across another caller's steps,
//! and map_page still finds the count exact once the frame's slot is present. The item relies on no other entry coming to map the page, and on the entry at the
//! address keeping that frame or none, until `unmap_page` takes the permission back: verified code
//! holding the caller can map the frame again through acall's map, and nothing ties the entry to the
//! kernel's state once the map returns.
use vstd::prelude::*;
use vstd::iset::ISet;
use vstd::raw_ptr::*;

#[cfg(verus_keep_ghost)]
use acall::arch::{translates, translation_premises};
use acall::arch::translates_page;
use acall::memory;
#[cfg(verus_keep_ghost)]
use acall::memory::lemma_own_position;
use acall::step::*;
#[cfg(verus_keep_ghost)]
use aheap::arch::*;
#[cfg(verus_keep_ghost)]
use verified::capability::reach::Right;
#[cfg(verus_keep_ghost)]
use verified::capability::caller::{frame_view, view_frame, view_writes_space};
#[cfg(verus_keep_ghost)]
use verified::capability::view::right_bit;
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::refs::{block_dead, block_ref, block_refs, block_typed, blocks_refs_changed, BlockRef};
#[cfg(verus_keep_ghost)]
use verified::capability::link::tree_of;
#[cfg(verus_keep_ghost)]
use verified::capability::map::{address_path, frame_map_entry, names_entry, LOWER_HALF_END};
#[cfg(verus_keep_ghost)]
use verified::capability::mapping::{space_mapping, SpacePath};
#[cfg(verus_keep_ghost)]
use verified::capability::rely::same_cap;
#[cfg(verus_keep_ghost)]
use verified::define::NUM_CPUS;
#[cfg(verus_keep_ghost)]
use verified::capability::table::block_bytes;
#[cfg(verus_keep_ghost)]
use verified::define::{ENTRIES, PAGE_SZ, SIZE_1G, SIZE_2M, SIZE_512G};
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

/// The process whose table is at the caller's root is sealed, no other table holding a slot that names
/// it, and recorded, its space keyed at its root. While it is, a step another caller takes only takes
/// from what the process holds (CapKernel::rely), so what frames_held and names_own_space say stays true
/// across it: lemma_frames_rely.
pub open spec fn own_process(caller: Caller) -> bool {
    &&& caller.kernel().sealed(caller.root())
    &&& caller.kernel().processes.records@.contains_key(caller.root())
}

/// One frame a source holds, `(slot, at)`: `at`, when there is one, is an address one entry maps; while
/// `slot` of the table at `root` holds a capability, it is a one-page frame whose block no other table
/// holds a capability of, counted at most by that capability and the entry at `at`, or by the capability
/// alone when there is no `at`, and the entry at `at`, while there is one, maps that frame's page.
pub open spec fn frame_held(k: CapKernel, root: usize, f: (usize, Option<usize>)) -> bool {
    let v = k.table_view(root);
    let m = space_mapping(tree_of(&k.table_pages, &k.spaces), root);
    &&& f.1 is Some ==> names_entry(f.1->0 as u64, 1)
    &&& v.contains_key(f.0) ==> {
        &&& v[f.0].kind is Frame
        &&& v[f.0].order == 0
        &&& k.held_by(block_ref(&k.blocks, slot_page(k, root, f.0)), root)
        &&& frame_refs(k, slot_page(k, root, f.0)) <= if f.1 is Some { 2usize } else { 1usize }
        &&& f.1 is Some && m.contains_key(address_path(f.1->0 as u64))
            ==> m[address_path(f.1->0 as u64)].addr / PAGE_SZ == slot_page(k, root, f.0)
    }
}

/// The frames a source holds, by key, each as frame_held says, no two of those the table still holds
/// holding the same block. Each clause allows a slot, an entry or a count to go and none to come, as a
/// revoke of an ancestor may take them, so it holds across any step another caller takes while the
/// process is its own (lemma_frames_rely); the source's own map is what raises a count, and its own
/// unmap what lowers it again.
pub open spec fn frames_held(k: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>) -> bool {
    &&& forall|i: int| #[trigger] frames.contains_key(i) ==> frame_held(k, root, frames[i])
    &&& forall|i: int, j: int|
        frames.contains_key(i) && frames.contains_key(j) && i != j
            && k.table_view(root).contains_key(#[trigger] frames[i].0) && k.table_view(root).contains_key(#[trigger] frames[j].0)
            ==> block_ref(&k.blocks, slot_page(k, root, frames[i].0)) != block_ref(&k.blocks, slot_page(k, root, frames[j].0))
}

/// The slot at `space` of the table at `root`, while it holds a capability that writes a space, holds
/// one naming the space keyed at `root`, the process's own.
pub open spec fn names_space(k: CapKernel, root: usize, space: u64) -> bool {
    let v = k.table_view(root);
    v.contains_key(space as usize) && view_writes_space(v[space as usize]) ==> v[space as usize].base == root
}

/// The slot at `space` of the caller's own table names the caller's own space, the one its thread runs
/// in, whenever it holds a capability a map or an unmap can use.
pub open spec fn names_own_space(caller: Caller, space: u64) -> bool {
    names_space(caller.kernel(), caller.root(), space)
}

/// Every slot that names the caller's own space in `pre` still does in `post`.
pub open spec fn keeps_own_space(pre: Caller, post: Caller) -> bool {
    forall|space: u64| #[trigger] names_own_space(pre, space) ==> names_own_space(post, space)
}

/// The page a frame capability in a table's view holds first is a page the block table tracks, in a
/// typed block counted at least once, at the capability's base.
pub proof fn lemma_slot_page(k: CapKernel, root: usize, slot: usize)
    requires
        k.wf(),
        k.table_view(root).contains_key(slot),
        k.table_view(root)[slot].kind is Frame,
    ensures
        k.blocks.tracks(slot_page(k, root, slot) as int),
        block_typed(&k.blocks, block_ref(&k.blocks, slot_page(k, root, slot))),
        frame_refs(k, slot_page(k, root, slot)) > 0,
        slot_page(k, root, slot) * PAGE_SZ == k.table_view(root)[slot].base,
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(0 < block_bytes(k.table_view(root)[slot].order)) by {
        vstd::arithmetic::power2::lemma_pow2_pos(k.table_view(root)[slot].order as nat);
    }
    k.lemma_table_view(root, slot);
    let n = k.tables.node_of(root, slot);
    k.lemma_frame_page(n, 0);
    k.lemma_view_frame_counted(root, slot, 0);
}

/// Two addresses that each name one page's entry, and differ, take different paths through a space.
proof fn lemma_paths_differ(a: u64, b: u64)
    requires
        names_entry(a, 1),
        names_entry(b, 1),
        a != b,
    ensures
        address_path(a) != address_path(b),
{
    lemma_path_page(a);
    lemma_path_page(b);
}

/// An address that names one page's entry is its path's four indices read as digits base ENTRIES, in
/// pages.
proof fn lemma_path_page(va: u64)
    requires
        names_entry(va, 1),
    ensures
        va as int == PAGE_SZ as int * (ENTRIES as int * (ENTRIES as int * (ENTRIES as int
            * address_path(va).l4 as int + address_path(va).l3 as int) + address_path(va).l2 as int)
            + address_path(va).l1 as int),
{
    use vstd::arithmetic::div_mod::*;
    let e = ENTRIES as int;
    let x = va as int;
    assert(SIZE_2M == PAGE_SZ * ENTRIES);
    assert(SIZE_1G == SIZE_2M * ENTRIES);
    assert(SIZE_512G == SIZE_1G * ENTRIES);
    assert(LOWER_HALF_END as int == SIZE_512G as int * (e / 2));
    let p1 = x / (PAGE_SZ as int);
    let p2 = x / (SIZE_2M as int);
    let p3 = x / (SIZE_1G as int);
    let p4 = x / (SIZE_512G as int);
    lemma_div_denominator(x, PAGE_SZ as int, e);
    lemma_div_denominator(x, SIZE_2M as int, e);
    lemma_div_denominator(x, SIZE_1G as int, e);
    assert(p2 == p1 / e && p3 == p2 / e && p4 == p3 / e);
    lemma_fundamental_div_mod(x, PAGE_SZ as int);
    lemma_fundamental_div_mod(p1, e);
    lemma_fundamental_div_mod(p2, e);
    lemma_fundamental_div_mod(p3, e);
    lemma_div_pos_is_pos(x, SIZE_512G as int);
    lemma_multiply_divide_lt(x, SIZE_512G as int, e / 2);
    lemma_small_mod(p4 as nat, e as nat);
    assert(address_path(va).l4 as int == p4);
    assert(address_path(va).l3 as int == p3 % e);
    assert(address_path(va).l2 as int == p2 % e);
    assert(address_path(va).l1 as int == p1 % e);
}

/// A step under which the slots of root's table that the source's frames name are only taken, with
/// the capability they held, root's space only loses entries, and while root is sealed no block that
/// only root's table holds gains a count or a holder keeps every frame the source holds.
pub proof fn lemma_frames_shrunk(pre: CapKernel, post: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>)
    requires
        frames_held(pre, root, frames),
        pre.sealed(root),
        forall|i: int| #[trigger] frames.contains_key(i) && post.table_view(root).contains_key(frames[i].0)
            ==> pre.table_view(root).contains_key(frames[i].0) && same_cap(post.table_view(root)[frames[i].0], pre.table_view(root)[frames[i].0]),
        forall|p: SpacePath| #[trigger] space_mapping(tree_of(&post.table_pages, &post.spaces), root).contains_key(p)
            ==> space_mapping(tree_of(&pre.table_pages, &pre.spaces), root).contains_key(p)
                && space_mapping(tree_of(&post.table_pages, &post.spaces), root)[p] == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root)[p],
        CapKernel::count_kept(pre, post, root),
    ensures
        frames_held(post, root, frames),
{
    vstd::arithmetic::power2::lemma2_to64();
    let a = space_mapping(tree_of(&pre.table_pages, &pre.spaces), root);
    let b = space_mapping(tree_of(&post.table_pages, &post.spaces), root);
    assert forall|i: int| #[trigger] frames.contains_key(i) && post.table_view(root).contains_key(frames[i].0) implies {
        &&& pre.table_view(root).contains_key(frames[i].0)
        &&& slot_page(post, root, frames[i].0) == slot_page(pre, root, frames[i].0)
        &&& block_ref(&post.blocks, slot_page(pre, root, frames[i].0)) == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0))
    } by {
        let j = frames[i].0;
        assert(frame_held(pre, root, frames[i]));
        assert((0 as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order));
        assert(block_ref(&post.blocks, view_frame(pre.table_view(root)[j], 0)) == block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], 0)));
    }
    assert forall|i: int| #[trigger] frames.contains_key(i) implies frame_held(post, root, frames[i]) by {
        let j = frames[i].0;
        assert(frame_held(pre, root, frames[i]));
        if post.table_view(root).contains_key(j) {
            assert((0 as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order));
            assert(block_ref(&post.blocks, view_frame(pre.table_view(root)[j], 0)) == block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], 0)));
            if frames[i].1 is Some && b.contains_key(address_path(frames[i].1->0 as u64)) {
                assert(a.contains_key(address_path(frames[i].1->0 as u64)));
            }
        }
    }
    assert forall|i: int, j: int|
        frames.contains_key(i) && frames.contains_key(j) && i != j
            && post.table_view(root).contains_key(#[trigger] frames[i].0) && post.table_view(root).contains_key(#[trigger] frames[j].0)
            implies block_ref(&post.blocks, slot_page(post, root, frames[i].0)) != block_ref(&post.blocks, slot_page(post, root, frames[j].0)) by {
        assert(frames.contains_key(i) && post.table_view(root).contains_key(frames[i].0));
        assert(frames.contains_key(j) && post.table_view(root).contains_key(frames[j].0));
    }
}

/// What a source carries across a step another caller takes, as `CapKernel::rely` allows it, while its
/// process is its own: the process stays sealed and recorded, every frame it holds stays held, and the
/// slot that names its space still does. The rely is the only premise relating the two states.
pub proof fn lemma_frames_rely(k1: CapKernel, k2: CapKernel, root: usize, space: u64, frames: Map<int, (usize, Option<usize>)>)
    requires
        k2.wf(),
        CapKernel::rely(k1, k2, root),
        k1.sealed(root),
        k1.processes.records@.contains_key(root),
        frames_held(k1, root, frames),
        names_space(k1, root, space),
    ensures
        k2.sealed(root),
        k2.processes.records@.contains_key(root),
        frames_held(k2, root, frames),
        names_space(k2, root, space),
{
    let a = space_mapping(tree_of(&k1.table_pages, &k1.spaces), root);
    let b = space_mapping(tree_of(&k2.table_pages, &k2.spaces), root);
    assert forall|p: SpacePath| #[trigger] b.contains_key(p) implies a.contains_key(p) && b[p] == a[p] by {}
    lemma_frames_shrunk(k1, k2, root, frames);
    if k2.table_view(root).contains_key(space as usize) {
        assert(same_cap(k2.table_view(root)[space as usize], k1.table_view(root)[space as usize]));
    }
}

/// A step that leaves every table's view as it was, every block, and the root's space's mapping keeps
/// every frame the source holds.
pub proof fn lemma_frames_same(pre: CapKernel, post: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>)
    requires
        frames_held(pre, root, frames),
        pre.sealed(root),
        forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
        post.blocks == pre.blocks,
        space_mapping(tree_of(&post.table_pages, &post.spaces), root) == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root),
    ensures
        frames_held(post, root, frames),
{
    CapKernel::lemma_blocks_kept_keeps_count(pre, post, root);
    assert(post.table_view(root) == pre.table_view(root));
    lemma_frames_shrunk(pre, post, root, frames);
}

/// A step that leaves every table's view as it was, every frame capability's pages in their blocks at
/// their counts, and every space's mapping as it was keeps every frame the source holds.
pub proof fn lemma_frames_kept(pre: CapKernel, post: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>)
    requires
        pre.wf(),
        pre.sealed(root),
        frames_held(pre, root, frames),
        forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
        CapKernel::frame_blocks_kept(pre, post),
        CapKernel::mappings_kept(pre, post),
    ensures
        frames_held(post, root, frames),
{
    assert(space_mapping(tree_of(&post.table_pages, &post.spaces), root) == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root));
    lemma_frame_blocks_keep_count(pre, post, root);
    assert(post.table_view(root) == pre.table_view(root));
    lemma_frames_shrunk(pre, post, root, frames);
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
    assert forall|i: int, j: int|
        f.contains_key(i) && f.contains_key(j) && i != j
            && k.table_view(root).contains_key(#[trigger] f[i].0) && k.table_view(root).contains_key(#[trigger] f[j].0)
            implies block_ref(&k.blocks, slot_page(k, root, f[i].0)) != block_ref(&k.blocks, slot_page(k, root, f[j].0)) by {
        assert(frames[i] == f[i] && frames[j] == f[j]);
    }
}

/// The frame held under `key`, whose block counts at most its capability while the table holds it,
/// stays held mapped nowhere.
proof fn lemma_frames_parked(k: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>, key: int)
    requires
        frames_held(k, root, frames),
        frames.contains_key(key),
        k.table_view(root).contains_key(frames[key].0) ==> frame_refs(k, slot_page(k, root, frames[key].0)) <= 1,
    ensures
        frames_held(k, root, frames.insert(key, (frames[key].0, None))),
{
    let f = frames.insert(key, (frames[key].0, None::<usize>));
    assert forall|i: int| #[trigger] f.contains_key(i) implies frame_held(k, root, f[i]) by {
        assert(frames.contains_key(i));
        assert(frame_held(k, root, frames[i]));
    }
    assert forall|i: int, j: int|
        f.contains_key(i) && f.contains_key(j) && i != j
            && k.table_view(root).contains_key(#[trigger] f[i].0) && k.table_view(root).contains_key(#[trigger] f[j].0)
            implies block_ref(&k.blocks, slot_page(k, root, f[i].0)) != block_ref(&k.blocks, slot_page(k, root, f[j].0)) by {
        assert(frames.contains_key(i) && frames.contains_key(j));
        assert(f[i].0 == frames[i].0 && f[j].0 == frames[j].0);
    }
}

/// A step that leaves every other table's view as it was, and every frame capability's pages in their
/// blocks at their counts, keeps count_kept for root.
proof fn lemma_frame_blocks_keep_count(pre: CapKernel, post: CapKernel, root: usize)
    requires
        pre.wf(),
        forall|t: usize| t != root ==> #[trigger] post.table_view(t) == pre.table_view(t),
        CapKernel::frame_blocks_kept(pre, post),
    ensures
        CapKernel::count_kept(pre, post, root),
{
    assert forall|t: usize, j: usize|
        t != root && !(t == root && j == 0usize) && #[trigger] post.table_view(t).contains_key(j) && post.table_view(t)[j].kind is Frame
            implies exists|t2: usize, j2: usize| t2 != root && #[trigger] pre.table_view(t2).contains_key(j2)
                && same_cap(pre.table_view(t2)[j2], post.table_view(t)[j]) by {
        assert(post.table_view(t) == pre.table_view(t));
        assert(pre.table_view(t).contains_key(j));
    }
    CapKernel::lemma_frames_kept_keeps_count(pre, post, root, root, 0);
}

/// A step that leaves every table's view as it was and every tracked page in its block keeps each
/// block that no other table holds a capability of so.
proof fn lemma_held_kept(pre: CapKernel, post: CapKernel, root: usize, x: BlockRef)
    requires
        pre.wf(),
        forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
        forall|i: usize| pre.blocks.tracks(i as int) ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
        pre.held_by(x, root),
    ensures
        post.held_by(x, root),
{
    assert forall|t: usize, j: usize, page: usize|
        t != root && post.table_view(t).contains_key(j) && post.table_view(t)[j].kind is Frame
            && (page as int) * PAGE_SZ < block_bytes(post.table_view(t)[j].order)
            implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[j], page)) != x by {
        assert(post.table_view(t) == pre.table_view(t));
        pre.lemma_view_frame_counted(t, j, page);
        assert(block_ref(&pre.blocks, view_frame(pre.table_view(t)[j], page)) != x);
    }
}

/// A frame retype into `slot`, a slot no frame the source holds names, keeps each and holds the new
/// frame, mapped nowhere: its block is new, counted once, and no other table holds a capability of it.
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
        pre.sealed(root),
        frames_held(pre, root, frames),
        !frames.contains_key(key),
        forall|i: int| #[trigger] frames.contains_key(i) ==> frames[i].0 != slot,
        post.table_view(root) == pre.table_view(root).insert(slot, frame_view(base, 0, parent)),
        forall|t: usize| t != root ==> #[trigger] post.table_view(t) == pre.table_view(t),
        block_refs(&post.blocks, block_ref(&post.blocks, base / PAGE_SZ)) == 1,
        CapKernel::frame_blocks_kept(pre, post),
        CapKernel::frame_block_new(pre, post, frame_view(base, 0, parent)),
        CapKernel::mappings_kept(pre, post),
    ensures
        frames_held(post, root, frames.insert(key, (slot, None))),
{
    vstd::arithmetic::power2::lemma2_to64();
    let fv = frame_view(base, 0, parent);
    let f = frames.insert(key, (slot, None::<usize>));
    assert(space_mapping(tree_of(&post.table_pages, &post.spaces), root) == space_mapping(tree_of(&pre.table_pages, &pre.spaces), root));
    lemma_frame_blocks_keep_count(pre, post, root);
    lemma_frames_shrunk(pre, post, root, frames);
    assert(slot_page(post, root, slot) == base / PAGE_SZ);
    let nb = block_ref(&post.blocks, view_frame(fv, 0));
    assert((0 as int) * PAGE_SZ < block_bytes(fv.order));
    assert(post.held_by(nb, root)) by {
        assert forall|t: usize, j: usize, q: usize|
            t != root && post.table_view(t).contains_key(j) && post.table_view(t)[j].kind is Frame
                && (q as int) * PAGE_SZ < block_bytes(post.table_view(t)[j].order)
                implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[j], q)) != nb by {
            assert(post.table_view(t) == pre.table_view(t));
            assert(block_ref(&post.blocks, view_frame(pre.table_view(t)[j], q)) == block_ref(&pre.blocks, view_frame(pre.table_view(t)[j], q)));
            assert(block_ref(&post.blocks, view_frame(fv, 0)) != block_ref(&pre.blocks, view_frame(pre.table_view(t)[j], q)));
        }
    }
    assert(frame_held(post, root, (slot, None::<usize>)));
    assert forall|i: int| #[trigger] f.contains_key(i) implies frame_held(post, root, f[i]) by {
        if i != key {
            assert(frames.contains_key(i));
        }
    }
    // A frame the source held before, still in the table, keeps its block, which the new frame's is not.
    assert forall|i: int| #[trigger] frames.contains_key(i) && post.table_view(root).contains_key(frames[i].0)
        implies block_ref(&post.blocks, slot_page(post, root, frames[i].0)) != nb by {
        let j = frames[i].0;
        assert(post.table_view(root)[j] == pre.table_view(root)[j]);
        assert(pre.table_view(root).contains_key(j));
        assert(frame_held(pre, root, frames[i]));
        assert((0 as int) * PAGE_SZ < block_bytes(pre.table_view(root)[j].order));
        assert(block_ref(&post.blocks, view_frame(pre.table_view(root)[j], 0)) == block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], 0)));
        assert(block_ref(&post.blocks, view_frame(fv, 0)) != block_ref(&pre.blocks, view_frame(pre.table_view(root)[j], 0)));
    }
    assert forall|i: int, j: int|
        f.contains_key(i) && f.contains_key(j) && i != j
            && post.table_view(root).contains_key(#[trigger] f[i].0) && post.table_view(root).contains_key(#[trigger] f[j].0)
            implies block_ref(&post.blocks, slot_page(post, root, f[i].0)) != block_ref(&post.blocks, slot_page(post, root, f[j].0)) by {
        if i != key {
            assert(frames.contains_key(i) && f[i] == frames[i]);
        }
        if j != key {
            assert(frames.contains_key(j) && f[j] == frames[j]);
        }
    }
}

/// A map at `address` of the frame the source holds under `key`, mapped nowhere, in the space the slot
/// at `space` names, which the kernel accepted, keeps every other frame and holds that one mapped
/// there: the space is the source's own, the frame's block was counted by its capability alone and now
/// by the new entry too, and no other frame is at `address`, so the entry went to a path no other frame
/// is at.
proof fn lemma_frames_mapped(
    pre: CapKernel,
    post: CapKernel,
    root: usize,
    space: u64,
    address: usize,
    frames: Map<int, (usize, Option<usize>)>,
    key: int,
    out: Outcome,
)
    requires
        pre.wf(),
        frames_held(pre, root, frames),
        names_space(pre, root, space),
        frames.contains_key(key),
        frames[key].1 is None,
        forall|i: int| #[trigger] frames.contains_key(i) && frames[i].1 is Some ==> frames[i].1->0 != address,
        CapKernel::map_contract(pre, post, root, space as usize, address as u64, PAGE_LEVEL, frames[key].0, 0, out),
        out.status == STATUS_OK,
    ensures
        pre.table_view(root)[space as usize].base == root,
        frames_held(post, root, frames.insert(key, (frames[key].0, Some(address)))),
        frame_refs(post, slot_page(pre, root, frames[key].0)) == 2,
{
    vstd::arithmetic::power2::lemma2_to64();
    let f = frames.insert(key, (frames[key].0, Some(address)));
    let from = frames[key].0;
    let v = pre.table_view(root);
    let a = space_mapping(tree_of(&pre.table_pages, &pre.spaces), root);
    let b = space_mapping(tree_of(&post.table_pages, &post.spaces), root);
    let p = address_path(address as u64);
    let page = slot_page(pre, root, from);
    let br = block_ref(&pre.blocks, page);
    assert(pre.map_allowed(root, space as usize, address as u64, PAGE_LEVEL, from, 0));
    assert(v[space as usize].base == root);
    assert(post.table_view(root) == v);
    assert(b == a.insert(p, frame_map_entry(page, v[from].rights, false)));
    assert(blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br)));
    lemma_slot_page(pre, root, from);
    assert(frame_held(pre, root, frames[key]));
    assert(frame_refs(pre, page) == 1);
    assert((page * PAGE_SZ) as usize / PAGE_SZ == page) by {
        assert((page as int * PAGE_SZ as int) / PAGE_SZ as int == page as int) by (nonlinear_arith)
            requires PAGE_SZ > 0;
    }
    assert(frame_refs(post, page) == 2) by {
        assert(block_ref(&post.blocks, page) == br);
    }
    lemma_held_kept(pre, post, root, br);
    assert forall|i: int| #[trigger] frames.contains_key(i) && i != key && v.contains_key(frames[i].0) implies {
        &&& block_ref(&post.blocks, slot_page(pre, root, frames[i].0)) == block_ref(&pre.blocks, slot_page(pre, root, frames[i].0))
        &&& frame_refs(post, slot_page(pre, root, frames[i].0)) == frame_refs(pre, slot_page(pre, root, frames[i].0))
        &&& post.held_by(block_ref(&pre.blocks, slot_page(pre, root, frames[i].0)), root)
    } by {
        let x = block_ref(&pre.blocks, slot_page(pre, root, frames[i].0));
        assert(frame_held(pre, root, frames[i]));
        lemma_slot_page(pre, root, frames[i].0);
        lemma_held_kept(pre, post, root, x);
        assert(x != br);
    }
    assert forall|i: int| #[trigger] frames.contains_key(i) && i != key && frames[i].1 is Some implies address_path(frames[i].1->0 as u64) != p by {
        assert(frame_held(pre, root, frames[i]));
        lemma_paths_differ(frames[i].1->0 as u64, address as u64);
    }
    assert forall|i: int| #[trigger] f.contains_key(i) implies frame_held(post, root, f[i]) by {
        if i != key {
            assert(frames.contains_key(i));
            assert(frame_held(pre, root, frames[i]));
        }
    }
    assert forall|i: int, j: int|
        f.contains_key(i) && f.contains_key(j) && i != j
            && post.table_view(root).contains_key(#[trigger] f[i].0) && post.table_view(root).contains_key(#[trigger] f[j].0)
            implies block_ref(&post.blocks, slot_page(post, root, f[i].0)) != block_ref(&post.blocks, slot_page(post, root, f[j].0)) by {
        assert(frames.contains_key(i) && frames.contains_key(j));
        assert(f[i].0 == frames[i].0 && f[j].0 == frames[j].0);
        lemma_slot_page(pre, root, frames[i].0);
        lemma_slot_page(pre, root, frames[j].0);
    }
}

/// An unmap at `address`, the address of the frame the source holds under `key`, in the space the slot
/// at `space` names, which the kernel accepted, keeps every frame the source holds and holds that one
/// mapped nowhere: the space is the source's own, so the entry it removed was that frame's, while the
/// table still holds it, and that frame's block lost the count.
proof fn lemma_frames_unmapped(
    pre: CapKernel,
    post: CapKernel,
    root: usize,
    space: u64,
    address: usize,
    frames: Map<int, (usize, Option<usize>)>,
    key: int,
    out: Outcome,
)
    requires
        pre.wf(),
        pre.sealed(root),
        frames_held(pre, root, frames),
        names_space(pre, root, space),
        frames.contains_key(key),
        frames[key].1 == Some(address),
        CapKernel::unmap_contract(pre, post, root, space as usize, address as u64, PAGE_LEVEL, out),
        out.status == STATUS_OK,
    ensures
        frames_held(post, root, frames.insert(key, (frames[key].0, None))),
{
    let v = pre.table_view(root);
    let a = space_mapping(tree_of(&pre.table_pages, &pre.spaces), root);
    let b = space_mapping(tree_of(&post.table_pages, &post.spaces), root);
    let p = address_path(address as u64);
    assert(pre.unmap_allowed(root, space as usize, address as u64, PAGE_LEVEL));
    assert(v[space as usize].base == root);
    let br = block_ref(&pre.blocks, a[p].addr / PAGE_SZ);
    let refs = (block_refs(&pre.blocks, br) - 1) as usize;
    assert(b == a.remove(p));
    assert(blocks_refs_changed(&pre.blocks, &post.blocks, br, refs, block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1));
    CapKernel::lemma_counted_keeps_count(pre, post, root, br, refs, block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1);
    assert(post.table_view(root) == v);
    lemma_frames_shrunk(pre, post, root, frames);
    let from = frames[key].0;
    if v.contains_key(from) {
        let page = slot_page(pre, root, from);
        assert(frame_held(pre, root, frames[key]));
        assert(a[p].addr / PAGE_SZ == page);
        lemma_slot_page(pre, root, from);
        assert(block_ref(&post.blocks, page) == br);
        assert(frame_refs(post, slot_page(post, root, from)) <= 1);
    }
    lemma_frames_parked(post, root, frames, key);
}

/// The level whose entry maps one page.
const PAGE_LEVEL: u64 = 1;

/// The write right's bit, as inspect returns rights.
const RIGHT_WRITE: u64 = 2;

/// Retypes the free page at physical `base`, inside the untyped at `untyped`, as a frame whose
/// capability goes in the slot `destination`. Whether the kernel accepted. No frame of `frames` names
/// `destination`; each is kept, and the new frame, mapped nowhere, is held under `key` once the kernel
/// accepted.
pub(crate) fn retype_frame(caller: &mut Tracked<Caller>, untyped: u64, base: u64, destination: u64, frames: Ghost<Map<int, (usize, Option<usize>)>>, key: Ghost<int>) -> (r: bool)
    requires
        old(caller)@.wf(),
        own_process(old(caller)@),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
        !frames@.contains_key(key@),
        forall|i: int| #[trigger] frames@.contains_key(i) ==> frames@[i].0 != destination as usize,
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        own_process(final(caller)@),
        keeps_own_space(old(caller)@, final(caller)@),
        r ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.insert(key@, (destination as usize, None))),
        !r ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@),
    no_unwind
{
    let ghost pre = caller@;
    let out = memory::retype(caller, untyped, RETYPE_FRAME, base, destination, 0);
    proof {
        // The destination comes to hold a frame, which writes no space.
        assert forall|space: u64| #[trigger] names_own_space(pre, space) implies names_own_space(caller@, space) by {}
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
pub(crate) fn retype_table_page(caller: &mut Tracked<Caller>, untyped: u64, base: u64, level: u64, frames: Ghost<Map<int, (usize, Option<usize>)>>) -> bool
    requires
        old(caller)@.wf(),
        own_process(old(caller)@),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        own_process(final(caller)@),
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
pub(crate) fn link(caller: &mut Tracked<Caller>, space: u64, address: usize, level: u64, untyped: u64, table: u64, frames: Ghost<Map<int, (usize, Option<usize>)>>) -> bool
    requires
        old(caller)@.wf(),
        own_process(old(caller)@),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        own_process(final(caller)@),
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
/// in, and no other frame of `frames` is at `address`. `live` holds every address of the window whose
/// page's permission the caller holds or has handed out, and `address` is not among them.
pub(crate) fn map_page(
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
        own_process(old(caller)@),
        names_own_space(old(caller)@, space),
        !live@.contains(address),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
        frames@.contains_key(key@),
        frames@[key@] == (frame as usize, None::<usize>),
        forall|i: int| #[trigger] frames@.contains_key(i) && frames@[i].1 is Some ==> frames@[i].1->0 != address,
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        own_process(final(caller)@),
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
            lemma_frames_mapped(before, caller@.kernel(), root, space, address, frames@, key@, out);
        } else {
            lemma_frames_same(before, caller@.kernel(), root, frames@);
        }
    }
    if out.status == STATUS_OK {
        Some(mapped_permission(Ghost(before), Ghost(caller@.kernel()), Ghost(root), space, address, frame, Ghost(out), provenance, live))
    } else {
        None
    }
}

/// The core a call from `pre` to `post` by the process whose space is keyed at `root` ran on and
/// returned from clean, as returned_on says one is.
pub open spec fn returned_core(pre: CapKernel, post: CapKernel, root: usize) -> int {
    choose|c: int| 0 <= c < NUM_CPUS && #[trigger] pre.cores@[c].space == Some(root) && returned_clean(post, root, c)
}

/// A map of a frame whose capability holds the write right, which the kernel accepted, meets the
/// target's translation premises on the core the call returned on: the entry it wrote is a present
/// writable user leaf for the frame's page, and every entry above it is open, as the kernel's
/// invariant keeps every link.
proof fn lemma_translation(before: CapKernel, after: CapKernel, root: usize, space: u64, address: usize, frame: u64, out: Outcome)
    requires
        after.wf(),
        out.status == STATUS_OK,
        CapKernel::map_contract(before, after, root, space as usize, address as u64, PAGE_LEVEL, frame as usize, 0, out),
        returned_on(before, after, before.table_view(root)[space as usize].base),
        before.table_view(root)[frame as usize].rights & right_bit(Right::Write) != 0,
    ensures
        translation_premises(after, before.table_view(root)[space as usize].base, returned_core(before, after, before.table_view(root)[space as usize].base), address, view_frame(before.table_view(root)[frame as usize], 0)),
{
    let s = before.table_view(root)[space as usize].base;
    let c = returned_core(before, after, s);
    after.lemma_mapping_open(s, address_path(address as u64));
    assert(0 <= c < NUM_CPUS && returned_clean(after, s, c));
}

/// The permission to the bytes of the page at `address` that page_permission gives, once the target's
/// translation guarantee says the core the map returned on reaches the frame's page there.
fn mapped_permission(
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
        after@.wf(),
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
    let ghost s = before@.table_view(root@)[space as usize].base;
    let ghost core = returned_core(before@, after@, s);
    let ghost page = view_frame(before@.table_view(root@)[frame as usize], 0);
    proof {
        lemma_translation(before@, after@, root@, space, address, frame, out@);
    }
    translates_page(after, Ghost(s), Ghost(core), Ghost(address), Ghost(page));
    page_permission(before, after, root, Ghost(core), space, address, frame, out, provenance, live)
}

/// The permission to the bytes of the page at `address`, once the kernel accepted a map of the frame
/// at `frame` there in the space at `space`, as the map contract says of the call by the process whose
/// table is at `root` that took the kernel from `before` to `after`, with the frame's capability
/// holding the write right, so the entry the map wrote is writable, the kernel holding the
/// permission of the frame's page, as it has since boot, and the frame's block counted by its
/// capability and the entry the map wrote alone, so no other entry maps the page when the map returns;
/// nothing proves that none comes to map it before `unmap_page` takes the permission back. The slot
/// at `space` names the caller's own space, which a core had loaded across the call and which that core, the one the call ran on,
/// returned from caught up on the flush epoch, holding nothing stale of the space; on that core the
/// target's translation guarantee says user loads and stores at `address` reach the frame's page. `live` holds every address
/// of the window whose page's permission the caller holds or has handed out, and `address` is not among
/// them.
#[verifier(external_body)]
// external_body(gap): conjures the permission to a mapped page's bytes; the map contract puts the frame's page in the space's tables, writable since the frame's capability has the write right, its block counted twice, by that capability and that entry, so no other entry in any space maps it when the map returns, with the kernel holding that page's permission as it has since boot, and the core that made the call holding that space, the caller's own, loaded and caught up on the flush epoch, holding no translation of that space to a page no space maps, as the step says, and nothing proves that no permission outside the ones live names covers the page, which the creator of the source promises by handing it a window nothing else maps, that no other entry, in this space or another, comes to map the frame's page until unmap_page takes the permission back, which verified code holding the caller can make through acall's map or through a derived copy of the frame's capability mapped elsewhere, that the entry at the address keeps that frame or none until unmap_page takes the permission back, which nothing ties to the kernel's state once the map returns, that a core the caller's thread runs on later, other than the one the map returned on, translates the address as that one does, which the target's translation guarantee says of that core alone, or that bytes a core loads and stores through a mapping may be held as a PointsToRaw
fn page_permission(
    before: Ghost<CapKernel>,
    after: Ghost<CapKernel>,
    root: Ghost<usize>,
    core: Ghost<int>,
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
        translates(core@, address, view_frame(before@.table_view(root@)[frame as usize], 0)),
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
pub(crate) fn unmap_page(
    caller: &mut Tracked<Caller>,
    space: u64,
    address: usize,
    perm: Tracked<PointsToRaw>,
    frames: Ghost<Map<int, (usize, Option<usize>)>>,
    key: Ghost<int>,
) -> (r: bool)
    requires
        old(caller)@.wf(),
        own_process(old(caller)@),
        names_own_space(old(caller)@, space),
        perm@.is_range(address as int, PAGE_BYTES as int),
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
        frames@.contains_key(key@),
        frames@[key@].1 == Some(address),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        own_process(final(caller)@),
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
            lemma_frames_unmapped(pre.kernel(), caller@.kernel(), root, space, address, frames@, key@, out);
        } else {
            lemma_frames_same(pre.kernel(), caller@.kernel(), root, frames@);
            lemma_frames_drop(caller@.kernel(), root, frames@, key@);
        }
    }
    out.status == STATUS_OK
}

} // verus!
