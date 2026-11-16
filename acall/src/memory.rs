// SPDX-License-Identifier: MIT

//! The memory operations, each a verified call of the kernel step whose ensures is the operation's
//! contract over the caller's view, proven from the step's ensures by the operation's lemma in
//! kernel/verified/capability/caller.rs.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verified::arch::Registers;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
use verified::capability::operation::*;
#[cfg(verus_keep_ghost)]
use verified::capability::position::*;
#[cfg(verus_keep_ghost)]
use verified::capability::rely::{reaches_through, same_cap};
#[cfg(verus_keep_ghost)]
use verified::capability::caller::{derived_view, view_frame};
#[cfg(verus_keep_ghost)]
use verified::capability::link::tree_of;
#[cfg(verus_keep_ghost)]
use verified::capability::map::{address_path, frame_map_entry};
#[cfg(verus_keep_ghost)]
use verified::capability::mapping::{space_mapping, SpacePath};
#[cfg(verus_keep_ghost)]
use verified::capability::refs::{block_dead, block_ref, block_refs, blocks_refs_changed};
#[cfg(verus_keep_ghost)]
use verified::capability::table::block_bytes;
#[cfg(verus_keep_ghost)]
use verified::define::PAGE_SZ;

use crate::step::*;

verus! {

/// The calling core's catching up, from `mid` to `post`, changes nothing the additional facts of
/// retype's contract for a frame read, so they hold of `post` when they hold of `mid`.
proof fn lemma_returned_retype_frame_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize, from: usize, base: usize, to: usize)
    requires
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::retype_frame_contract_fields(pre, mid, root, from, base, to)
            ==> CapKernel::retype_frame_contract_fields(pre, post, root, from, base, to),
{
    reveal(CapKernel::retype_frame_contract_fields);
}

/// The same of the additional facts of retype's contract for a table page.
proof fn lemma_returned_retype_table_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, base: usize)
    requires
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::retype_table_contract_fields(pre, mid, base) ==> CapKernel::retype_table_contract_fields(pre, post, base),
{
    reveal(CapKernel::retype_table_contract_fields);
}

/// The same of the binding retype's contract states for a thread.
proof fn lemma_returned_retype_thread_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize, base: usize, j: usize)
    requires
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::retype_thread_contract_fields(pre, mid, root, base, j)
            ==> CapKernel::retype_thread_contract_fields(pre, post, root, base, j),
{
    reveal(CapKernel::retype_thread_contract_fields);
}

/// The same of the additional facts of inspect's contract.
proof fn lemma_returned_inspect_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int)
    requires
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::inspect_contract_fields(pre, mid) ==> CapKernel::inspect_contract_fields(pre, post),
{
    reveal(CapKernel::inspect_contract_fields);
}

/// The same of the additional facts of link's contract.
proof fn lemma_returned_link_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int)
    requires
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::link_contract_fields(pre, mid) ==> CapKernel::link_contract_fields(pre, post),
{
    reveal(CapKernel::link_contract_fields);
}

/// The same of the additional facts of map's contract.
proof fn lemma_returned_map_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize)
    requires
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::map_contract_fields(pre, mid, root, slot, va, level, from, page)
            ==> CapKernel::map_contract_fields(pre, post, root, slot, va, level, from, page),
{
    reveal(CapKernel::map_contract_fields);
}

/// The same of the additional facts of unmap's contract.
proof fn lemma_returned_unmap_fields(pre: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize, slot: usize, va: u64)
    requires
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::unmap_contract_fields(pre, mid, root, slot, va) ==> CapKernel::unmap_contract_fields(pre, post, root, slot, va),
{
    reveal(CapKernel::unmap_contract_fields);
}

/// Retypes, on the authority of the untyped at index `untyped` of the caller's table, the block at
/// `base` as `kind`: a frame into the empty slot at index `word`, a 2M frame the same, a table page of
/// `level`, a leaf into the root entry the position `word` names, a process into the empty slot at index
/// `word`, or a thread into that slot bound to the process whose capability is at index `level`.
pub fn retype(caller: &mut Tracked<Caller>, untyped: u64, kind: u64, base: u64, word: u64, level: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        pages_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        CapKernel::retype_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), kind, untyped as usize, base as usize, word, level as usize, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                && (kind != RETYPE_PROCESS || word as usize != s
                    || final(caller)@.entry().table_view(final(caller)@.root()).contains_key(s))
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_RETYPE, untyped, kind, base, word, level, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_RETYPE, untyped, kind, base, word, level, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Retype);
        CapKernel::lemma_retype_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_retype_frame_fields(entry, mid, caller@.kernel(), c, pre.root(), untyped as usize, base as usize, word as usize);
        lemma_returned_retype_table_fields(entry, mid, caller@.kernel(), c, base as usize);
        lemma_returned_retype_thread_fields(entry, mid, caller@.kernel(), c, pre.root(), base as usize, level as usize);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_retype_keeps_count(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert forall|s: usize|
                #[trigger] slot_names_own_space(pre.kernel(), pre.root(), s)
                    && (kind != RETYPE_PROCESS || word as usize != s
                        || entry.table_view(pre.root()).contains_key(s))
                implies slot_names_own_space(caller@.kernel(), pre.root(), s) by {
                lemma_rely_keeps_slot_names_own_space(pre.kernel(), entry, pre.root(), s);
                assert(caller@.kernel().table_view(pre.root()) == mid.table_view(pre.root()));
                entry.lemma_table_view(pre.root(), s);
            };
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// The capability `from` names in `root`'s table is a frame capability.
pub open spec fn derive_from_frame(k: CapKernel, root: usize, from: u64) -> bool {
    let f = spec_position(from);
    &&& f is Some
    &&& k.table_view(root).contains_key(f->0.index)
    &&& k.table_view(root)[f->0.index].kind is Frame
}

/// A derive that is refused or whose source is not a frame keeps `count_kept`; one from a frame
/// source keeps the block, the count and `held_by` of every frame in `root`'s table whose page
/// lies in another block.
proof fn lemma_derive_keeps_counts(
    entry: CapKernel,
    post: CapKernel,
    root: usize,
    from: u64,
    to: u64,
    rights: u64,
    base: u64,
    order: u64,
    out: Outcome,
)
    requires
        entry.wf(),
        CapKernel::derive_contract(entry, post, root, spec_position(from), spec_position(to), rights, base as usize, order, 0, out),
    ensures
        (out.status != STATUS_OK || !derive_from_frame(entry, root, from))
            ==> CapKernel::count_kept(entry, post, root),
        out.status == STATUS_OK && derive_from_frame(entry, root, from)
            ==> forall|j: usize, page: usize|
                entry.table_view(root).contains_key(j)
                    && entry.table_view(root)[j].kind is Frame
                    && (page as int) * PAGE_SZ < block_bytes(entry.table_view(root)[j].order)
                    && block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page))
                        != block_ref(&entry.blocks, view_frame(entry.table_view(root)[spec_position(from)->0.index], 0))
                    ==> {
                    let br = block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page));
                    &&& #[trigger] block_ref(&post.blocks, view_frame(entry.table_view(root)[j], page)) == br
                    &&& block_refs(&post.blocks, br) == block_refs(&entry.blocks, br)
                    &&& entry.held_by(br, root) ==> post.held_by(br, root)
                },
{
    let from_pos = spec_position(from);
    let to_pos = spec_position(to);
    if out.status != STATUS_OK {
        CapKernel::lemma_blocks_kept_keeps_count(entry, post, root);
        return;
    }
    let i = from_pos->0.index;
    let source = entry.table_view(root)[i];
    let table = entry.view_table_at(root, to_pos->0.through)->0;
    let slot = to_pos->0.index;
    let child = derived_view(source, rights as u32, base as usize, order as u8, entry.tables.node_of(root, i));
    if !(source.kind is Frame) {
        assert forall|t: usize, j: usize, page: usize|
            entry.table_view(t).contains_key(j) && entry.table_view(t)[j].kind is Frame
                && (page as int) * PAGE_SZ < block_bytes(entry.table_view(t)[j].order) implies {
                let br = block_ref(&entry.blocks, view_frame(entry.table_view(t)[j], page));
                &&& #[trigger] block_ref(&post.blocks, view_frame(entry.table_view(t)[j], page)) == br
                &&& block_refs(&post.blocks, br) <= block_refs(&entry.blocks, br) || !entry.held_by(br, root)
            } by {
            assert(CapKernel::frame_blocks_kept(entry, post));
        }
        assert forall|t: usize, j: usize|
            t != root && !(t == root && j == 0usize) && #[trigger] post.table_view(t).contains_key(j)
                && post.table_view(t)[j].kind is Frame
                implies exists|t2: usize, j2: usize| t2 != root && #[trigger] entry.table_view(t2).contains_key(j2)
                    && same_cap(entry.table_view(t2)[j2], post.table_view(t)[j]) by {
            assert(entry.table_view(t).contains_key(j));
        }
        CapKernel::lemma_frames_kept_keeps_count(entry, post, root, root, 0);
        return;
    }
    let src_br = block_ref(&entry.blocks, view_frame(source, 0));
    assert(blocks_refs_changed(&entry.blocks, &post.blocks, src_br, (block_refs(&entry.blocks, src_br) + 1) as usize, block_dead(&entry.blocks, src_br)));
    assert forall|j: usize, page: usize|
        entry.table_view(root).contains_key(j)
            && entry.table_view(root)[j].kind is Frame
            && (page as int) * PAGE_SZ < block_bytes(entry.table_view(root)[j].order)
            && block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page)) != src_br
            implies {
            let br = block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page));
            &&& #[trigger] block_ref(&post.blocks, view_frame(entry.table_view(root)[j], page)) == br
            &&& block_refs(&post.blocks, br) == block_refs(&entry.blocks, br)
            &&& entry.held_by(br, root) ==> post.held_by(br, root)
        } by {
        let br = block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page));
        entry.lemma_view_frame_counted(root, j, page);
        if entry.held_by(br, root) {
            assert forall|t: usize, k: usize, p: usize|
                t != root && post.table_view(t).contains_key(k) && post.table_view(t)[k].kind is Frame
                    && (p as int) * PAGE_SZ < block_bytes(post.table_view(t)[k].order)
                    implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[k], p)) != br by {
                if t == table && k == slot {
                    let n = vstd::arithmetic::power2::pow2(child.order as nat) as int;
                    let m = vstd::arithmetic::power2::pow2(source.order as nat) as int;
                    vstd::arithmetic::power2::lemma_pow2_pos(source.order as nat);
                    vstd::arithmetic::power2::lemma_pow2_pos(child.order as nat);
                    let b = base as usize;
                    let q = (b / PAGE_SZ + p - source.base / PAGE_SZ) as usize;
                    assert(block_bytes(child.order) == n * PAGE_SZ);
                    assert(block_bytes(source.order) == m * PAGE_SZ);
                    assert(p < n);
                    assert((b + n * PAGE_SZ) / (PAGE_SZ as int) == b / PAGE_SZ + n);
                    assert((source.base + m * PAGE_SZ) / (PAGE_SZ as int) == source.base / PAGE_SZ + m);
                    assert(0 <= b / PAGE_SZ + p - source.base / PAGE_SZ < m);
                    assert((q as int) * PAGE_SZ < block_bytes(source.order));
                    assert(view_frame(child, p) == view_frame(source, q));
                    entry.lemma_table_view(root, i);
                    entry.lemma_frame_page(entry.tables.node_of(root, i), q);
                    entry.lemma_frame_page(entry.tables.node_of(root, i), 0);
                    assert(view_frame(source, 0) == source.base / PAGE_SZ);
                    assert(block_ref(&entry.blocks, view_frame(source, q)) == src_br);
                } else {
                    assert(entry.table_view(t).contains_key(k));
                    entry.lemma_view_frame_counted(t, k, p);
                }
            }
        }
    }
}

/// Derives from the capability at the position `from` names, in the caller's own table, a child with
/// `rights` and the block of `order` at `base` into the empty position `to` names.
pub fn derive(caller: &mut Tracked<Caller>, from: u64, to: u64, rights: u64, base: u64, order: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        pages_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() && !reaches_through(to) ==> final(caller)@.pages_wf(),
        CapKernel::derive_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(from), spec_position(to), rights, base as usize, order, 0, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        (out.status != STATUS_OK || !derive_from_frame(final(caller)@.entry(), final(caller)@.root(), from))
            ==> CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        out.status == STATUS_OK && derive_from_frame(final(caller)@.entry(), final(caller)@.root(), from)
            ==> forall|j: usize, page: usize|
                final(caller)@.entry().table_view(final(caller)@.root()).contains_key(j)
                    && final(caller)@.entry().table_view(final(caller)@.root())[j].kind is Frame
                    && (page as int) * PAGE_SZ < block_bytes(final(caller)@.entry().table_view(final(caller)@.root())[j].order)
                    && block_ref(&final(caller)@.entry().blocks, view_frame(final(caller)@.entry().table_view(final(caller)@.root())[j], page))
                        != block_ref(&final(caller)@.entry().blocks, view_frame(final(caller)@.entry().table_view(final(caller)@.root())[spec_position(from)->0.index], 0))
                    ==> {
                    let br = block_ref(&final(caller)@.entry().blocks, view_frame(final(caller)@.entry().table_view(final(caller)@.root())[j], page));
                    &&& #[trigger] block_ref(&final(caller)@.kernel().blocks, view_frame(final(caller)@.entry().table_view(final(caller)@.root())[j], page)) == br
                    &&& block_refs(&final(caller)@.kernel().blocks, br) == block_refs(&final(caller)@.entry().blocks, br)
                    &&& final(caller)@.entry().held_by(br, final(caller)@.root())
                        ==> final(caller)@.kernel().held_by(br, final(caller)@.root())
                },
        !reaches_through(to) ==> (old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root())),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                && ((!reaches_through(to) && (spec_position(to) is None || spec_position(to)->0.index != s))
                    || (!reaches_through(from) && spec_position(from) is Some
                        && slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), spec_position(from)->0.index))
                    || final(caller)@.entry().table_view(final(caller)@.root()).contains_key(s))
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_DERIVE, from, to, rights, base, order, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_DERIVE, from, to, rights, base, order, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Derive);
        CapKernel::lemma_derive_contract(entry, mid, pre.root(), frame, out);
        lemma_derive_keeps_counts(entry, caller@.kernel(), pre.root(), from, to, rights, base, order, out);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        if !reaches_through(to) {
            CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        }
        if pre.kernel().sealed(pre.root()) {
            assert forall|s: usize|
                #[trigger] slot_names_own_space(pre.kernel(), pre.root(), s)
                    && ((!reaches_through(to) && (spec_position(to) is None || spec_position(to)->0.index != s))
                        || (!reaches_through(from) && spec_position(from) is Some
                            && slot_names_own_space(pre.kernel(), pre.root(), spec_position(from)->0.index))
                        || entry.table_view(pre.root()).contains_key(s))
                implies slot_names_own_space(caller@.kernel(), pre.root(), s) by {
                lemma_rely_keeps_slot_names_own_space(pre.kernel(), entry, pre.root(), s);
                assert(caller@.kernel().table_view(pre.root()) == mid.table_view(pre.root()));
                if mid.table_view(pre.root()).contains_key(s) {
                    if entry.table_view(pre.root()).contains_key(s) {
                        entry.lemma_table_view(pre.root(), s);
                    } else {
                        assert(out == status_only(STATUS_OK));
                        let f = spec_position(from)->0;
                        let d = spec_position(to)->0;
                        let src = entry.view_table_at(pre.root(), f.through)->0;
                        let dst = entry.view_table_at(pre.root(), d.through)->0;
                        assert(dst == pre.root() && d.index == s);
                        assert(!reaches_through(from));
                        assert(src == pre.root());
                        lemma_rely_keeps_slot_names_own_space(pre.kernel(), entry, pre.root(), f.index);
                        let v = entry.table_view(pre.root())[f.index];
                        lemma_derived_keeps_slot_names_own_space(v, rights as u32, base as usize, order as u8, entry.tables.node_of(pre.root(), f.index), pre.root());
                    }
                }
            };
        }
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.pages_wf() && !reaches_through(to) {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Reads the kind, the base, the order and the rights of the capability at the position `at` names,
/// and for a thread capability the cycles the thread has run.
pub fn inspect(caller: &mut Tracked<Caller>, at: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        pages_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        CapKernel::inspect_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), spec_position(at), out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_INSPECT, at, 0, 0, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_INSPECT, at, 0, 0, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Inspect);
        CapKernel::lemma_inspect_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_inspect_fields(entry, mid, caller@.kernel(), c);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_inspect_keeps_count(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Links the unlinked table page at `child`, covered by the untyped at index `from` of the caller's
/// table, into the entry at `level` that the address `va` names in the space of the capability at index
/// `slot`.
pub fn link(caller: &mut Tracked<Caller>, slot: u64, va: u64, level: u64, from: u64, child: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        pages_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        CapKernel::link_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, level, from as usize, child as usize, out),
        CapKernel::space_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        CapKernel::count_kept(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_LINK, slot, va, level, from, child, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_LINK, slot, va, level, from, child, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Link);
        CapKernel::lemma_link_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_link_fields(entry, mid, caller@.kernel(), c);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
        lemma_returned_space_kept(entry, mid, caller@.kernel(), c, pre.root());
        CapKernel::lemma_link_keeps_count(entry, mid, pre.root(), frame, out, pre.root());
        lemma_returned_count_kept(entry, mid, caller@.kernel(), c, pre.root());
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Maps the page at offset `page` of the frame capability at index `from` of the caller's table into
/// the entry at `level` that the address `va` names in the space of the capability at index `slot`,
/// another process's: the caller's own space is mapped by map_own, against its page token.
pub fn map(caller: &mut Tracked<Caller>, slot: u64, va: u64, level: u64, from: u64, page: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
        slot_names_other_space(old(caller)@.kernel(), old(caller)@.root(), slot as usize),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        pages_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        CapKernel::map_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, level, from as usize, page as usize, out),
        returned_on(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_MAP, slot, va, level, from, page, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_MAP, slot, va, level, from, page, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Map);
        CapKernel::lemma_map_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_map_fields(entry, mid, caller@.kernel(), c, pre.root(), slot as usize, va, level, from as usize, page as usize);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            let root = pre.root();
            let a = space_mapping(tree_of(&entry.table_pages, &entry.spaces), root);
            let b = space_mapping(tree_of(&mid.table_pages, &mid.spaces), root);
            if out == status_only(STATUS_OK) {
                // The slot held at entry the capability it held when the caller called, which names
                // another's space, so the map left the caller's own alone.
                let v = entry.table_view(root);
                let u = pre.kernel().table_view(root);
                assert(v.contains_key(slot as usize));
                assert(same_cap(v[slot as usize], u[slot as usize]));
                assert(v[slot as usize].base != root);
            }
            assert(b == a);
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Unmaps the level 1 entry at `level` that the address `va` names in the space of the capability at
/// index `slot`, another process's: the caller's own space is unmapped by unmap_own, against its page
/// token.
pub fn unmap(caller: &mut Tracked<Caller>, slot: u64, va: u64, level: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
        slot_names_other_space(old(caller)@.kernel(), old(caller)@.root(), slot as usize),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        pages_kept(old(caller)@, final(caller)@),
        old(caller)@.pages_wf() ==> final(caller)@.pages_wf(),
        CapKernel::unmap_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, level, out),
        old(caller)@.kernel().sealed(old(caller)@.root()) ==> final(caller)@.kernel().sealed(final(caller)@.root()),
        old(caller)@.kernel().sealed(old(caller)@.root()) && old(caller)@.kernel().processes.records@.contains_key(old(caller)@.root())
            ==> final(caller)@.kernel().processes.records@.contains_key(final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    let out = step(caller, OPERATION_UNMAP, slot, va, level, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_UNMAP, slot, va, level, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), pre.root(), frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Unmap);
        CapKernel::lemma_unmap_contract(entry, mid, pre.root(), frame, out);
        lemma_returned_unmap_fields(entry, mid, caller@.kernel(), c, pre.root(), slot as usize, va);
        CapKernel::lemma_own_step_keeps_record(entry, mid, pre.root(), frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, pre.root(), frame, out);
        if pre.kernel().sealed(pre.root()) {
            assert(forall|j: usize| #[trigger] caller@.kernel().table_view(pre.root()).contains_key(j)
                ==> entry.table_view(pre.root()).contains_key(j) && same_cap(caller@.kernel().table_view(pre.root())[j], entry.table_view(pre.root())[j]));
            lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), pre.root());
        }
        if pre.pages_wf() {
            lemma_entry_agrees(pre, caller@);
            CapKernel::lemma_own_step_keeps_space(entry, mid, pre.root(), frame, out);
            lemma_space_kept_agrees(entry, mid, pre.root(), pre.pages());
            lemma_returned_agrees(caller@, mid, c);
        }
    }
    out
}

/// Maps the page at offset `page` of the frame capability at index `from` of the caller's table into
/// the level 1 entry the address `va` names in the caller's own space, through the space capability at
/// index `slot`, against the token for that page, which says no frame is mapped there. As map does,
/// with level 1: on OK the token, and the authority with it, names the frame's page; refused, the token
/// is as it was. The page tokens stay in agreement with the space either way. The contract reads the
/// authority through the caller's pages and pages_id alone, so it is stated over that part of the
/// caller by itself.
pub fn map_own(caller: &mut Tracked<Caller>, token: &mut Tracked<PageToken>, slot: u64, va: u64, from: u64, page: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
        old(caller)@.pages_wf(),
        old(token)@.id() == old(caller)@.pages_id(),
        old(token)@.path() == address_path(va),
        old(token)@.frame() is None,
        slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), slot as usize),
        frame_slot_writes(old(caller)@.kernel(), old(caller)@.root(), from as usize),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        final(caller)@.start() == old(caller)@.start(),
        final(caller)@.pages_id() == old(caller)@.pages_id(),
        final(caller)@.pages() == old(caller)@.pages().insert(final(token)@.path(), final(token)@.frame()),
        final(caller)@.pages_wf(),
        final(token)@.id() == old(token)@.id(),
        final(token)@.path() == old(token)@.path(),
        out.status == STATUS_OK ==> final(token)@.frame()
            == Some(view_frame(old(caller)@.kernel().table_view(old(caller)@.root())[from as usize], page as usize)),
        out.status != STATUS_OK ==> final(token)@ == old(token)@,
        CapKernel::map_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, 1, from as usize, page as usize, out),
        returned_on(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root()),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    proof {
        token.borrow().agree(caller.borrow());
    }
    let out = step(caller, OPERATION_MAP, slot, va, 1, from, page, 0);
    proof {
        let entry = caller@.entry();
        let root = pre.root();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_MAP, slot, va, 1, from, page, 0)
                && #[trigger] entered(entry, caller@.kernel(), root, frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), root, frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Map);
        CapKernel::lemma_map_contract(entry, mid, root, frame, out);
        lemma_returned_map_fields(entry, mid, caller@.kernel(), c, root, slot as usize, va, 1, from as usize, page as usize);
        CapKernel::lemma_own_step_keeps_record(entry, mid, root, frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, root, frame, out);
        lemma_entry_agrees(pre, caller@);
        assert(forall|j: usize| #[trigger] caller@.kernel().table_view(root).contains_key(j)
            ==> entry.table_view(root).contains_key(j) && same_cap(caller@.kernel().table_view(root)[j], entry.table_view(root)[j]));
        lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), root);
        let p = address_path(va);
        let a = space_mapping(tree_of(&entry.table_pages, &entry.spaces), root);
        let b = space_mapping(tree_of(&mid.table_pages, &mid.spaces), root);
        if out.status == STATUS_OK {
            let v = entry.table_view(root);
            let u = pre.kernel().table_view(root);
            assert(out == status_only(STATUS_OK));
            assert(v.contains_key(slot as usize) && v.contains_key(from as usize));
            assert(same_cap(v[slot as usize], u[slot as usize]));
            assert(same_cap(v[from as usize], u[from as usize]));
            let f = view_frame(v[from as usize], page as usize);
            let e = frame_map_entry(f, v[from as usize].rights, false);
            assert(caller@.kernel().frames@.contains_key(f));
            assert(caller@.kernel().frames_wf());
            assert(b == a.insert(p, e));
            let pages = pre.pages().insert(p, Some(f));
            assert forall|q: SpacePath| #[trigger] pages.contains_key(q) implies page_agrees(b, q, pages[q]) by {
                if q != p {
                    assert(pre.pages().contains_key(q));
                    assert(page_agrees(a, q, pre.pages()[q]));
                    if large_path(q) == p {
                        assert(b[large_path(q)] == e);
                    }
                } else {
                    assert(page_agrees(a, p, None));
                    if large_path(p) == p {
                        assert(b[p] == e);
                    }
                }
            }
            set_page(caller.borrow_mut(), token.borrow_mut(), Some(f));
        } else {
            assert(b == a);
            assert(pre.pages().insert(p, None) =~= pre.pages());
        }
        lemma_returned_agrees(caller@, mid, c);
    }
    out
}

/// Unmaps the level 1 entry the address `va` names in the caller's own space, through the space
/// capability at index `slot`, against the token for that page, which names a frame. As unmap does: on
/// OK the token, and the authority with it, says no frame is mapped there; refused, the token is as it
/// was. The page tokens stay in agreement with the space either way. The contract reads the authority
/// through the caller's pages and pages_id alone.
pub fn unmap_own(caller: &mut Tracked<Caller>, token: &mut Tracked<PageToken>, slot: u64, va: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
        old(caller)@.pages_wf(),
        old(token)@.id() == old(caller)@.pages_id(),
        old(token)@.path() == address_path(va),
        old(token)@.frame() is Some,
        slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), slot as usize),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        final(caller)@.start() == old(caller)@.start(),
        final(caller)@.pages_id() == old(caller)@.pages_id(),
        final(caller)@.pages() == old(caller)@.pages().insert(final(token)@.path(), final(token)@.frame()),
        final(caller)@.pages_wf(),
        final(token)@.id() == old(token)@.id(),
        final(token)@.path() == old(token)@.path(),
        out.status == STATUS_OK ==> final(token)@.frame() is None,
        out.status != STATUS_OK ==> final(token)@ == old(token)@,
        CapKernel::unmap_contract(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), slot as usize, va, 1, out),
        forall|s: usize|
            old(caller)@.kernel().sealed(old(caller)@.root())
                && #[trigger] slot_names_own_space(old(caller)@.kernel(), old(caller)@.root(), s)
                ==> slot_names_own_space(final(caller)@.kernel(), final(caller)@.root(), s),
    no_unwind
{
    let ghost pre = caller@;
    proof {
        token.borrow().agree(caller.borrow());
    }
    let out = step(caller, OPERATION_UNMAP, slot, va, 1, 0, 0, 0);
    proof {
        let entry = caller@.entry();
        let root = pre.root();
        let (frame, c, mid) = choose|frame: Registers, c: int, mid: CapKernel|
            carries(frame, OPERATION_UNMAP, slot, va, 1, 0, 0, 0)
                && #[trigger] entered(entry, caller@.kernel(), root, frame, out, c, mid);
        lemma_entered(entry, caller@.kernel(), root, frame, out, c, mid);
        lemma_number_names_one_operation(Operation::Unmap);
        CapKernel::lemma_unmap_contract(entry, mid, root, frame, out);
        lemma_returned_unmap_fields(entry, mid, caller@.kernel(), c, root, slot as usize, va);
        CapKernel::lemma_own_step_keeps_record(entry, mid, root, frame, out);
        CapKernel::lemma_own_step_keeps_sealed(entry, mid, root, frame, out);
        lemma_entry_agrees(pre, caller@);
        assert(forall|j: usize| #[trigger] caller@.kernel().table_view(root).contains_key(j)
            ==> entry.table_view(root).contains_key(j) && same_cap(caller@.kernel().table_view(root)[j], entry.table_view(root)[j]));
        lemma_shrunk_view_keeps_slot_names_own_space(pre.kernel(), entry, caller@.kernel(), root);
        let p = address_path(va);
        let a = space_mapping(tree_of(&entry.table_pages, &entry.spaces), root);
        let b = space_mapping(tree_of(&mid.table_pages, &mid.spaces), root);
        if out.status == STATUS_OK {
            let v = entry.table_view(root);
            let u = pre.kernel().table_view(root);
            assert(v.contains_key(slot as usize));
            assert(same_cap(v[slot as usize], u[slot as usize]));
            assert(b == a.remove(p));
            lemma_shrunk_keeps_agree(a, b, pre.pages());
            let pages = pre.pages().insert(p, None);
            assert forall|q: SpacePath| #[trigger] pages.contains_key(q) implies page_agrees(b, q, pages[q]) by {
                if q != p {
                    assert(pre.pages().contains_key(q));
                } else {
                    assert(page_agrees(b, p, pre.pages()[p]));
                }
            }
            set_page(caller.borrow_mut(), token.borrow_mut(), None);
        } else {
            assert(b == a);
            assert(pre.pages().insert(p, pre.pages()[p]) =~= pre.pages());
        }
        lemma_returned_agrees(caller@, mid, c);
    }
    out
}

/// A word no wider than an index names the slot at that index of the caller's own table.
pub proof fn lemma_own_position(word: u64)
    requires
        word <= POSITION_INDEX_MASK,
    ensures
        spec_position(word) == Some(Position { through: None, index: word as usize }),
{
    assert(word >> 32u64 == 0) by (bit_vector)
        requires
            word <= 0xffffu64;
    assert((word >> 16u64) & 0xffffu64 == 0) by (bit_vector)
        requires
            word <= 0xffffu64;
    assert(word & 0xffffu64 == word) by (bit_vector)
        requires
            word <= 0xffffu64;
}

} // verus!
