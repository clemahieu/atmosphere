// SPDX-License-Identifier: MIT

//! A verified use of the wrappers: retype a frame, derive a read-only child of it and inspect the
//! child. Its ensures is proven from the wrappers' contracts and the rely alone: between two calls
//! another caller's step may take the frame or the child, as an ancestor's revoke does, but a slot that
//! stays says what it said while the caller is sealed, so when the kernel accepted all three calls the
//! inspect says a frame of the page with the read right and no other.
//! A proof of the page tokens beside it: a set of empty pages claimed as one token, one page's token
//! taken out of it and put back, and one call from an empty history pinning `start` to its entry
//! state so a page empty there may be claimed with no fact of the conjured start.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verified::capability::caller::view_frame;
#[cfg(verus_keep_ghost)]
use verified::capability::inspect::CAP_KIND_FRAME;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::link::tree_of;
#[cfg(verus_keep_ghost)]
use verified::capability::map::address_path;
#[cfg(verus_keep_ghost)]
use verified::capability::mapping::{space_mapping, SpacePath};
#[cfg(verus_keep_ghost)]
use verified::capability::position::*;
#[cfg(verus_keep_ghost)]
use verified::capability::refs::{block_ref, block_refs};
#[cfg(verus_keep_ghost)]
use verified::capability::rely::same_cap;
#[cfg(verus_keep_ghost)]
use verified::capability::table::block_bytes;
#[cfg(verus_keep_ghost)]
use verified::define::PAGE_SZ;
use verified::capability::operation::*;

use crate::memory::*;
use crate::step::*;

verus! {

/// The read right's bit, as inspect returns rights and derive takes them.
pub const RIGHT_READ: u64 = 1;

/// What inspect said of the read-only child.
pub struct Inspected {
    pub kind: u64,
    pub base: u64,
    pub order: u64,
    pub rights: u64,
}

/// Retypes the page at `base` under the untyped at index `untyped` of the caller's table as a frame
/// into the empty slot at index `frame`, derives from it a child with the read right alone into the
/// empty slot at index `child`, and inspects the child. None when the kernel refused the retype, the
/// derive or the inspect; otherwise what the inspect said, which is the child the derive made. The
/// caller is sealed, so what another caller's step leaves of its table is what it held.
pub fn read_only_child(caller: &mut Tracked<Caller>, untyped: u64, base: u64, frame: u64, child: u64) -> (ret: Option<Inspected>)
    requires
        old(caller)@.wf(),
        old(caller)@.kernel().sealed(old(caller)@.root()),
        frame <= POSITION_INDEX_MASK,
        child <= POSITION_INDEX_MASK,
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        ret matches Some(c) ==> c.kind == CAP_KIND_FRAME && c.base == base && c.order == 0 && c.rights == RIGHT_READ,
{
    let ghost root = caller@.root();
    if retype(caller, untyped, RETYPE_FRAME, base, frame, 0).status != STATUS_OK {
        return None;
    }
    let ghost made = caller@.kernel().table_view(root)[frame as usize];
    proof {
        lemma_own_position(frame);
        lemma_own_position(child);
        assert(made.kind is Frame && made.base == base as usize && made.order == 0);
    }
    if derive(caller, frame, child, RIGHT_READ, base, 0).status != STATUS_OK {
        return None;
    }
    proof {
        // The derive was accepted from its entry state, which held the frame as the retype left it.
        let e = caller@.entry();
        assert(e.table_view(root).contains_key(frame as usize));
        assert(same_cap(e.table_view(root)[frame as usize], made));
        let v = caller@.kernel().table_view(root)[child as usize];
        assert(caller@.kernel().table_view(root).contains_key(child as usize));
        assert(v.kind is Frame && v.base == base as usize && v.order == 0 && v.rights == RIGHT_READ as u32);
    }
    let ghost derived = caller@.kernel().table_view(root)[child as usize];
    let out = inspect(caller, child);
    if out.status != STATUS_OK {
        return None;
    }
    proof {
        // The inspect was accepted from its entry state, which held the child as the derive left it.
        let e = caller@.entry();
        assert(e.table_view(root).contains_key(child as usize));
        assert(same_cap(e.table_view(root)[child as usize], derived));
    }
    Some(Inspected { kind: out.result_1, base: out.result_2, order: out.result_3, rights: out.result_4 })
}

/// Slot `slot` in `root`'s table holds a frame capability whose every page lies in a block that
/// no other table holds a frame capability of.
pub open spec fn sole_frame(k: CapKernel, root: usize, slot: usize) -> bool {
    &&& k.table_view(root).contains_key(slot)
    &&& k.table_view(root)[slot].kind is Frame
    &&& forall|page: usize|
        (page as int) * PAGE_SZ < block_bytes(k.table_view(root)[slot].order)
            ==> k.held_by(
                #[trigger] block_ref(&k.blocks, view_frame(k.table_view(root)[slot], page)),
                root,
            )
}

/// Every page of the frame capability at `slot` in `root`'s table keeps its capability fields,
/// its block, a count no higher than in `pre`, and `held_by` in `post`.
pub open spec fn frame_pages_kept(pre: CapKernel, post: CapKernel, root: usize, slot: usize) -> bool {
    forall|page: usize|
        (page as int) * PAGE_SZ < block_bytes(pre.table_view(root)[slot].order)
            ==> {
            let v0 = pre.table_view(root)[slot];
            let v1 = post.table_view(root)[slot];
            let br = block_ref(&pre.blocks, view_frame(v0, page));
            &&& same_cap(v1, v0)
            &&& #[trigger] block_ref(&post.blocks, view_frame(post.table_view(root)[slot], page)) == br
            &&& block_refs(&post.blocks, br) <= block_refs(&pre.blocks, br)
            &&& post.held_by(br, root)
        }
}

/// Derives from a non-frame capability at index `src` of the caller's table into `child` while
/// tracking a frame capability at index `kept` whose block only this caller holds. Using
/// `derive`'s `count_kept` ensures and the rely alone, if `kept` remains in the caller's table,
/// every page of `kept` keeps its block, a count no higher than before, and sole ownership by this
/// caller.
pub fn derive_non_frame_keeps_frame(
    caller: &mut Tracked<Caller>,
    src: u64,
    child: u64,
    rights: u64,
    base: u64,
    order: u64,
    kept: u64,
) -> (out: Outcome)
    requires
        old(caller)@.wf(),
        old(caller)@.kernel().sealed(old(caller)@.root()),
        src <= POSITION_INDEX_MASK,
        child <= POSITION_INDEX_MASK,
        child != kept,
        sole_frame(old(caller)@.kernel(), old(caller)@.root(), kept as usize),
        old(caller)@.kernel().table_view(old(caller)@.root()).contains_key(src as usize)
            ==> !(old(caller)@.kernel().table_view(old(caller)@.root())[src as usize].kind is Frame),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.kernel().sealed(final(caller)@.root()),
        final(caller)@.kernel().table_view(final(caller)@.root()).contains_key(kept as usize)
            ==> frame_pages_kept(old(caller)@.kernel(), final(caller)@.kernel(), final(caller)@.root(), kept as usize),
{
    hide(CapKernel::frame_blocks_kept);
    let ghost pre = caller@;
    let ghost root = pre.root();
    proof {
        lemma_own_position(src);
        lemma_own_position(child);
    }
    let out = derive(caller, src, child, rights, base, order);
    proof {
        let entry = caller@.entry();
        let post = caller@.kernel();
        assert(CapKernel::count_kept(entry, post, root));
        if post.table_view(root).contains_key(kept as usize) {
            assert(entry.table_view(root).contains_key(kept as usize));
            let v0 = pre.kernel().table_view(root)[kept as usize];
            assert forall|page: usize|
                (page as int) * PAGE_SZ < block_bytes(v0.order)
                    implies {
                    let v1 = post.table_view(root)[kept as usize];
                    let br = block_ref(&pre.kernel().blocks, view_frame(v0, page));
                    &&& same_cap(v1, v0)
                    &&& #[trigger] block_ref(&post.blocks, view_frame(post.table_view(root)[kept as usize], page)) == br
                    &&& block_refs(&post.blocks, br) <= block_refs(&pre.kernel().blocks, br)
                    &&& post.held_by(br, root)
                } by {
                let br = block_ref(&pre.kernel().blocks, view_frame(v0, page));
                assert(block_ref(&entry.blocks, view_frame(v0, page)) == br);
                assert(block_ref(&post.blocks, view_frame(entry.table_view(root)[kept as usize], page)) == br);
            };
        }
    }
    out
}

/// Derives from a frame capability at index `src` into `child` while tracking a frame capability
/// at index `kept` in another block whose block only this caller holds. Using `derive`'s
/// frame-source ensures and the rely alone, if `kept` remains in the caller's table, every page of
/// `kept` keeps its block, count (equal across the call step, no higher across the rely), and
/// `held_by`.
pub fn derive_other_frame_keeps_frame(
    caller: &mut Tracked<Caller>,
    src: u64,
    child: u64,
    rights: u64,
    base: u64,
    order: u64,
    kept: u64,
) -> (out: Outcome)
    requires
        old(caller)@.wf(),
        old(caller)@.kernel().sealed(old(caller)@.root()),
        src <= POSITION_INDEX_MASK,
        child <= POSITION_INDEX_MASK,
        child != kept,
        sole_frame(old(caller)@.kernel(), old(caller)@.root(), kept as usize),
        old(caller)@.kernel().table_view(old(caller)@.root()).contains_key(src as usize),
        old(caller)@.kernel().table_view(old(caller)@.root())[src as usize].kind is Frame,
        old(caller)@.kernel().held_by(
            block_ref(&old(caller)@.kernel().blocks, view_frame(old(caller)@.kernel().table_view(old(caller)@.root())[src as usize], 0)),
            old(caller)@.root(),
        ),
        forall|page: usize|
            (page as int) * PAGE_SZ < block_bytes(old(caller)@.kernel().table_view(old(caller)@.root())[kept as usize].order)
                ==> #[trigger] block_ref(&old(caller)@.kernel().blocks, view_frame(old(caller)@.kernel().table_view(old(caller)@.root())[kept as usize], page))
                    != block_ref(&old(caller)@.kernel().blocks, view_frame(old(caller)@.kernel().table_view(old(caller)@.root())[src as usize], 0)),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.kernel().sealed(final(caller)@.root()),
        final(caller)@.kernel().table_view(final(caller)@.root()).contains_key(kept as usize)
            ==> {
            &&& frame_pages_kept(old(caller)@.kernel(), final(caller)@.kernel(), final(caller)@.root(), kept as usize)
            &&& forall|page: usize|
                (page as int) * PAGE_SZ < block_bytes(old(caller)@.kernel().table_view(old(caller)@.root())[kept as usize].order)
                    ==> {
                    let br = block_ref(&old(caller)@.kernel().blocks, view_frame(old(caller)@.kernel().table_view(old(caller)@.root())[kept as usize], page));
                    &&& #[trigger] block_ref(&final(caller)@.kernel().blocks, view_frame(final(caller)@.kernel().table_view(final(caller)@.root())[kept as usize], page)) == br
                    &&& block_refs(&final(caller)@.kernel().blocks, br) == block_refs(&final(caller)@.entry().blocks, br)
                }
        },
{
    let ghost pre = caller@;
    let ghost root = pre.root();
    proof {
        lemma_own_position(src);
        lemma_own_position(child);
    }
    let out = derive(caller, src, child, rights, base, order);
    proof {
        let entry = caller@.entry();
        let post = caller@.kernel();
        if post.table_view(root).contains_key(kept as usize) {
            assert(entry.table_view(root).contains_key(kept as usize));
            let v0 = pre.kernel().table_view(root)[kept as usize];
            let s0 = pre.kernel().table_view(root)[src as usize];
            if out.status == STATUS_OK {
                assert(entry.table_view(root).contains_key(src as usize));
                assert((0usize as int) * PAGE_SZ < block_bytes(s0.order)) by {
                    vstd::arithmetic::power2::lemma_pow2_pos(s0.order as nat);
                }
                let src_br = block_ref(&pre.kernel().blocks, view_frame(s0, 0));
                assert(block_ref(&entry.blocks, view_frame(s0, 0)) == src_br);
            }
            assert forall|page: usize|
                (page as int) * PAGE_SZ < block_bytes(v0.order)
                    implies {
                    let v1 = post.table_view(root)[kept as usize];
                    let br = block_ref(&pre.kernel().blocks, view_frame(v0, page));
                    &&& same_cap(v1, v0)
                    &&& #[trigger] block_ref(&post.blocks, view_frame(post.table_view(root)[kept as usize], page)) == br
                    &&& block_refs(&post.blocks, br) == block_refs(&entry.blocks, br)
                    &&& block_refs(&post.blocks, br) <= block_refs(&pre.kernel().blocks, br)
                    &&& post.held_by(br, root)
                } by {
                let br = block_ref(&pre.kernel().blocks, view_frame(v0, page));
                assert(block_ref(&entry.blocks, view_frame(v0, page)) == br);
                assert(block_ref(&post.blocks, view_frame(entry.table_view(root)[kept as usize], page)) == br);
            };
        }
    }
    out
}

/// Claims a set of the caller's pages, each empty at the first call's entry and now, as one
/// token, takes the token of one page out of it and puts it back: the set says again that no frame is
/// mapped at any of its pages, and the caller's tokens still agree with its space.
pub proof fn page_set_round_trip(tracked caller: &mut Caller, s: Set<SpacePath>, p: SpacePath) -> (tracked set: PageSet)
    requires
        old(caller).pages_wf(),
        old(caller).history().len() > 0,
        s.disjoint(old(caller).pages().dom()),
        s.contains(p),
        forall|q: SpacePath| #[trigger] s.contains(q) ==> {
            &&& page_agrees(space_mapping(tree_of(&old(caller).start().table_pages, &old(caller).start().spaces), old(caller).root()), q, None)
            &&& page_agrees(space_mapping(tree_of(&old(caller).kernel().table_pages, &old(caller).kernel().spaces), old(caller).root()), q, None)
        },
    ensures
        final(caller).pages_wf(),
        set.pages() == none_at(s),
        set.id() == final(caller).pages_id(),
{
    let tracked mut set = claim_set(caller, s);
    let tracked token = set.take(p);
    assert(token.path() == p && token.frame() is None);
    set.put(token);
    assert(set.pages() =~= none_at(s));
    set
}

/// After one call through `acall` from a caller whose history is empty, `Caller::start` equals
/// that call's entry state regardless of the conjured `start`, and a page empty there (kept empty
/// from `old(caller)@.kernel()` across the rely and `inspect`) may be claimed with no fact about
/// `old(caller)@.start()`.
pub fn first_call_pins_start(caller: &mut Tracked<Caller>, at: u64, va: u64) -> (ret: (Outcome, Tracked<PageToken>))
    requires
        old(caller)@.wf(),
        old(caller)@.pages_wf(),
        old(caller)@.history().len() == 0,
        page_agrees(space_mapping(tree_of(&old(caller)@.kernel().table_pages, &old(caller)@.kernel().spaces), old(caller)@.root()), address_path(va), None),
    ensures
        final(caller)@.wf(),
        final(caller)@.pages_wf(),
        final(caller)@.history().len() == 1,
        final(caller)@.start() == final(caller)@.entry(),
        final(caller)@.pages() == old(caller)@.pages().insert(address_path(va), None),
        ret.1@.id() == final(caller)@.pages_id(),
        ret.1@.path() == address_path(va),
        ret.1@.frame() is None,
{
    let ghost pre = caller@;
    let ghost p = address_path(va);
    let out = inspect(caller, at);
    proof {
        let root = caller@.root();
        assert(caller@.start() == caller@.entry());
        let m_pre = space_mapping(tree_of(&pre.kernel().table_pages, &pre.kernel().spaces), root);
        let m_entry = space_mapping(tree_of(&caller@.entry().table_pages, &caller@.entry().spaces), root);
        let m_post = space_mapping(tree_of(&caller@.kernel().table_pages, &caller@.kernel().spaces), root);
        let one = Map::<SpacePath, Option<usize>>::empty().insert(p, None);
        assert forall|q: SpacePath| #[trigger] one.contains_key(q) implies page_agrees(m_pre, q, one[q]) by {
            assert(q == p);
        };
        lemma_shrunk_keeps_agree(m_pre, m_entry, one);
        lemma_shrunk_keeps_agree(m_entry, m_post, one);
        assert(one.contains_key(p));
        assert(page_agrees(m_entry, p, None));
        assert(page_agrees(m_post, p, None));
    }
    let tracked token = claim(caller.borrow_mut(), address_path(va));
    (out, Tracked(token))
}

} // verus!
