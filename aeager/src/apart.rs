// SPDX-License-Identifier: MIT

//! Two eager sources of one process over disjoint windows, untyped runs and frame slots: what the
//! steps of one leave of the other. A step one source's back makes, accepted, keeps what a fresh other
//! source asks of the kernel (`own_kernel_ready`), so with the process facts the stepping source's own
//! readiness carries, the other is `source_ready` still when no other caller stepped between. And any
//! step it makes, accepted or refused, with other callers' steps between, adds no entry to the
//! process's space outside its own window's level-4 entry, so the other window stays unmapped.
use vstd::prelude::*;

use acall::step::*;
use aheap::arch::*;
use aheap::source::run_pages;
use verified::capability::block::order_pages;
use verified::capability::caller::{frame_view, view_writes_space};
use verified::capability::kernel::CapKernel;
use verified::capability::link::tree_of;
use verified::capability::list::MAX_DEPTH;
use verified::capability::map::{address_path, LOWER_HALF_END};
use verified::capability::mapping::{space_mapping, step, SpacePath};
use verified::capability::operation::*;
use verified::capability::reach::Right;
use verified::capability::space::SpaceKind;
use verified::capability::table::{block_bytes, TABLE_INDICES};
use verified::capability::view::right_bit;
use verified::define::{ENTRIES, PAGE_SZ, SIZE_512G};

use crate::eager::{
    acall_call_in_window, acall_setup_call, frame_slot, lemma_frame_slot, untyped_page, window_page, LEAF_INDICES,
    MAX_PAGES, TABLE_PAGES, WINDOW_BYTES,
};
use crate::glue::{
    acall_alone, acall_ok, acall_steps, kernel_source_ready, lemma_acall_steps_alone,
    lemma_distinct_slots_distinct_nodes, lemma_refs_changed_covered, lemma_retype_table_kept, lemma_retype_table_tree,
    lemma_window_level4, own_process, source_ready, window_unclaimed, AcallCall, AcallStep,
};

verus! {

/// The configuration constants `kernel_source_ready` asks of a source: its page count, its frame
/// slots, its untyped run's alignment and end, and its window's place in the lower half.
pub open spec fn source_config(memory: u64, pages: usize, slots: u64, window: usize) -> bool {
    &&& pages <= MAX_PAGES
    &&& slots < TABLE_INDICES as u64
    &&& slots as int % LEAF_INDICES as int != 0
    &&& pages > 0 ==> frame_slot(slots as int, pages - 1) < TABLE_INDICES
    &&& memory as int % (TABLE_PAGES * PAGE_BYTES) as int == 0
    &&& memory + pages * PAGE_BYTES <= u64::MAX
    &&& window != 0
    &&& window as int % SIZE_512G as int == 0
    &&& window + WINDOW_BYTES <= LOWER_HALF_END as usize
}

/// Two sources' untyped runs share no page, their frame slots no slot, and their windows no level-4
/// entry.
pub open spec fn sources_apart(
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    o_memory: u64,
    o_pages: usize,
    o_slots: u64,
    o_window: usize,
) -> bool {
    &&& (memory as int / PAGE_SZ as int + pages as int <= o_memory as int / PAGE_SZ as int
        || o_memory as int / PAGE_SZ as int + o_pages as int <= memory as int / PAGE_SZ as int)
    &&& forall|i: int, j: int| #![trigger frame_slot(slots as int, i), frame_slot(o_slots as int, j)]
        0 <= i < pages && 0 <= j < o_pages ==> frame_slot(slots as int, i) != frame_slot(o_slots as int, j)
    &&& window != o_window
}

/// The process facts of `kernel_source_ready`: the kernel is well formed, and the process at `root` is
/// sealed, recorded and live, with its table page live and a process space.
pub open spec fn process_ready(k: CapKernel, root: usize) -> bool {
    &&& k.wf()
    &&& k.sealed(root)
    &&& k.processes.records@.contains_key(root)
    &&& !k.processes.records@[root].value().dead
    &&& !k.blocks.pages@[(root / PAGE_SZ) as int].dead
    &&& k.spaces.roots@.contains_key(root)
    &&& k.spaces.records@[root].value().kind == SpaceKind::Process
}

/// What `kernel_source_ready` asks of the kernel for one source beyond the process facts and the
/// flush epoch's room: the space and untyped capabilities, the empty frame slots, the free pages of
/// the untyped run and the empty level-4 entry of the window.
pub open spec fn own_kernel_ready(
    k: CapKernel,
    root: usize,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
) -> bool {
    let v = k.table_view(root);
    let tree = tree_of(&k.table_pages, &k.spaces);
    &&& k.spaces.roots@.contains_key(root)
    &&& v.contains_key(space as usize)
    &&& v[space as usize].live
    &&& view_writes_space(v[space as usize])
    &&& v[space as usize].base == root
    &&& v.contains_key(untyped as usize)
    &&& v[untyped as usize].live
    &&& v[untyped as usize].kind is Untyped
    &&& v[untyped as usize].rights & right_bit(Right::Retype) != 0
    &&& v[untyped as usize].base <= memory as usize
    &&& memory as int + pages as int * PAGE_SZ as int
        <= v[untyped as usize].base as int + block_bytes(v[untyped as usize].order)
    &&& k.list.nodes@[k.tables.node_of(root, untyped as usize) as int].depth + 1 < MAX_DEPTH
    &&& forall|i: int| 0 <= i < pages ==> k.empty_slot(root, (#[trigger] frame_slot(slots as int, i)) as usize)
    &&& forall|i: int| 0 <= i < pages ==> {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k.blocks.tracks(p)
        &&& (#[trigger] k.blocks.pages@[memory as int / PAGE_SZ as int + i]).kind is Free
        &&& !k.blocks.covered(p)
    }
    &&& tree.entry(root, address_path(window as u64).l4).is_empty()
}

/// `kernel_source_ready` is its process facts, the flush epoch's room, the configuration and
/// `own_kernel_ready`.
pub proof fn lemma_kernel_source_ready_parts(
    k: CapKernel,
    root: usize,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
)
    ensures
        kernel_source_ready(k, root, space, untyped, memory, pages, slots, window) <==> {
            &&& process_ready(k, root)
            &&& k.flush_epoch as int + MAX_PAGES as int <= usize::MAX as int
            &&& source_config(memory, pages, slots, window)
            &&& own_kernel_ready(k, root, space, untyped, memory, pages, slots, window)
        },
{
}

/// The page `i` pages into an untyped run is page `i` past the run's first page.
proof fn lemma_untyped_page_index(memory: u64, i: int)
    requires
        0 <= i,
    ensures
        untyped_page(memory, i) / PAGE_SZ as int == memory as int / PAGE_SZ as int + i,
{
    use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
    let p = PAGE_SZ as int;
    assert(PAGE_BYTES as int == p);
    lemma_fundamental_div_mod(memory as int, p);
    let q = memory as int / p;
    let r = memory as int % p;
    assert(untyped_page(memory, i) == (q + i) * p + r) by (nonlinear_arith)
        requires
            memory as int == p * q + r,
            untyped_page(memory, i) == memory as int + i * p,
    ;
    lemma_fundamental_div_mod_converse(untyped_page(memory, i), p, q + i, r);
}

/// Two windows at distinct level-4-aligned addresses below the lower half's end have distinct level-4
/// entries, each the window's address over the level-4 span.
pub(crate) proof fn lemma_windows_apart(window: usize, o_window: usize)
    requires
        window as int % SIZE_512G as int == 0,
        o_window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        o_window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        window != o_window,
    ensures
        address_path(window as u64).l4 != address_path(o_window as u64).l4,
        (address_path(o_window as u64).l4 as int) < ENTRIES as int,
{
    use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
    lemma_window_level4(window, window as int);
    lemma_window_level4(o_window, o_window as int);
    lemma_fundamental_div_mod(window as int, SIZE_512G as int);
    lemma_fundamental_div_mod(o_window as int, SIZE_512G as int);
}

/// A frame slot of a source with a configuration `source_config` allows is a slot index of the table.
proof fn lemma_frame_slot_index(slots: u64, pages: usize, i: int)
    requires
        slots < TABLE_INDICES as u64,
        slots as int % LEAF_INDICES as int != 0,
        pages > 0 ==> frame_slot(slots as int, pages - 1) < TABLE_INDICES,
        0 <= i < pages,
    ensures
        0 <= frame_slot(slots as int, i) < TABLE_INDICES,
        (frame_slot(slots as int, i) as usize) as int == frame_slot(slots as int, i),
{
    lemma_frame_slot(slots as int, i, pages - 1);
}

/// An accepted step of one source's back, in its window, keeps what a fresh other source asks of the
/// kernel, when the two are apart: the step retypes from its own untyped run into its own frame
/// slots, links in its own window's level-4 entry or below it, and maps and unmaps in leaf tables.
#[verifier::spinoff_prover]
pub proof fn lemma_step_keeps_other(
    s: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
    o_untyped: u64,
    o_memory: u64,
    o_pages: usize,
    o_slots: u64,
    o_window: usize,
)
    requires
        s.valid(),
        s.out.status == STATUS_OK,
        acall_call_in_window(s, space, untyped, memory, pages, slots, window, start, count),
        source_config(memory, pages, slots, window),
        source_config(o_memory, o_pages, o_slots, o_window),
        sources_apart(memory, pages, slots, window, o_memory, o_pages, o_slots, o_window),
        own_kernel_ready(s.pre, s.root, space, o_untyped, o_memory, o_pages, o_slots, o_window),
    ensures
        own_kernel_ready(s.post, s.root, space, o_untyped, o_memory, o_pages, o_slots, o_window),
{
    reveal(AcallStep::valid);
    reveal(acall_call_in_window);
    reveal(acall_setup_call);
    let pre = s.pre;
    let post = s.post;
    let root = s.root;
    let a = tree_of(&pre.table_pages, &pre.spaces);
    let b = tree_of(&post.table_pages, &post.spaces);
    let ol4 = address_path(o_window as u64).l4;
    let l4 = address_path(window as u64).l4;
    let v = pre.table_view(root);
    let ob = o_memory as int / PAGE_SZ as int;
    lemma_windows_apart(window, o_window);
    assert(a.is_root(root));
    pre.lemma_table_base(root);
    assert(!a.is_page(root));
    pre.lemma_table_view(root, space as usize);
    pre.lemma_table_view(root, o_untyped as usize);
    let nu = pre.tables.node_of(root, o_untyped as usize);
    assert(pre.tables.is_cap(&pre.list, nu));
    match s.call {
        AcallCall::Retype { untyped: u, kind, base, word, level } => {
            if kind == RETYPE_FRAME {
                let i = choose|i: int|
                    0 <= i < pages && base as int == untyped_page(memory, i)
                        && word as int == #[trigger] frame_slot(slots as int, i);
                let to = word as usize;
                let at = (base as usize / PAGE_SZ) as int;
                reveal(CapKernel::retype_frame_contract_fields);
                assert(pre.empty_slot(root, to));
                pre.lemma_table_view(root, to);
                assert(!v.contains_key(to));
                assert(pre.tables.has_slot(&pre.list, root, o_untyped as usize));
                assert(post.table_view(root)[space as usize] == v[space as usize]);
                assert(post.table_view(root)[o_untyped as usize] == v[o_untyped as usize]);
                assert(post.tables.node_of(root, o_untyped as usize) == nu);
                assert(post.list.nodes@[nu as int].depth == pre.list.nodes@[nu as int].depth);
                lemma_untyped_page_index(memory, i);
                assert(at == memory as int / PAGE_SZ as int + i);
                lemma_frame_slot_index(slots, pages, i);
                assert forall|j: int| 0 <= j < o_pages implies post.empty_slot(
                    root,
                    (#[trigger] frame_slot(o_slots as int, j)) as usize,
                ) by {
                    let sj = frame_slot(o_slots as int, j) as usize;
                    lemma_frame_slot_index(o_slots, o_pages, j);
                    assert(frame_slot(slots as int, i) != frame_slot(o_slots as int, j));
                    assert(sj != to);
                    assert(pre.empty_slot(root, sj));
                    lemma_distinct_slots_distinct_nodes(pre, root, sj, to);
                }
                assert(order_pages(0) == 1);
                assert forall|j: int| 0 <= j < o_pages implies {
                    let p = ob + j;
                    &&& post.blocks.tracks(p)
                    &&& (#[trigger] post.blocks.pages@[o_memory as int / PAGE_SZ as int + j]).kind is Free
                    &&& !post.blocks.covered(p)
                } by {
                    assert(pre.blocks.pages@[ob + j].kind is Free);
                    assert(pre.blocks.tracks(ob + j));
                    assert(ob + j != at);
                    assert(post.blocks.pages@[ob + j] == pre.blocks.pages@[ob + j]);
                }
                assert(b == a);
            } else {
                assert(kind == RETYPE_TABLE_PAGE);
                let g = choose|g: int|
                    0 <= g && g + TABLE_PAGES <= pages && g % TABLE_PAGES as int == 0
                        && base as int == #[trigger] untyped_page(memory, g);
                let child = base as usize;
                let at = (child / PAGE_SZ) as int;
                reveal(CapKernel::retype_table_contract_fields);
                lemma_retype_table_kept(pre, post, child);
                lemma_untyped_page_index(memory, g);
                assert(at == memory as int / PAGE_SZ as int + g);
                assert(pre.small_block_free(child, 3));
                assert(order_pages(3) == 8);
                assert(pre.blocks.pages@[at + 0].kind is Free);
                if a.is_table(child) {
                    pre.lemma_table_base(child);
                    assert(false);
                }
                lemma_retype_table_tree(pre, post, child);
                assert(b.entry(root, ol4) == a.entry(root, ol4));
                assert(post.table_view(root) == v);
                assert forall|j: int| 0 <= j < o_pages implies post.empty_slot(
                    root,
                    (#[trigger] frame_slot(o_slots as int, j)) as usize,
                ) by {
                    assert(pre.empty_slot(root, frame_slot(o_slots as int, j) as usize));
                }
                assert forall|j: int| 0 <= j < o_pages implies {
                    let p = ob + j;
                    &&& post.blocks.tracks(p)
                    &&& (#[trigger] post.blocks.pages@[o_memory as int / PAGE_SZ as int + j]).kind is Free
                    &&& !post.blocks.covered(p)
                } by {
                    assert(pre.blocks.pages@[ob + j].kind is Free);
                    assert(pre.blocks.tracks(ob + j));
                    assert(!(at <= ob + j < at + TABLE_PAGES as int));
                    assert(post.blocks.pages@[ob + j] == pre.blocks.pages@[ob + j]);
                }
            }
        },
        AcallCall::Link { slot, va, level, from, child } => {
            reveal(CapKernel::link_contract_fields);
            let sp = v[slot as usize].base;
            assert(sp == root);
            let place = pre.link_parent(sp, va, level)->0;
            assert(pre.link_fits(sp, va, level, child as usize));
            assert(pre.link_parent(sp, va, level) is Some);
            if level == 4 {
                assert(va == window as u64);
                assert(place.entry == l4);
            } else {
                let p = address_path(va);
                assert(step(a, sp, p.l4) is Some);
                assert(a.names_child(sp, p.l4));
                pre.lemma_child_facts(sp, p.l4);
                let t3 = step(a, sp, p.l4)->0;
                if level == 3 {
                    assert(place.table == t3);
                    assert(a.is_page(place.table));
                } else {
                    assert(step(a, t3, p.l3) is Some);
                    assert(a.names_child(t3, p.l3));
                    pre.lemma_child_facts(t3, p.l3);
                    assert(place.table == step(a, t3, p.l3)->0);
                    assert(a.is_page(place.table));
                }
                assert(place.table != root);
            }
            assert(b.entry(root, ol4) == a.entry(root, ol4));
            assert(b.roots.dom() == a.roots.dom());
            assert forall|j: int| 0 <= j < o_pages implies post.empty_slot(
                root,
                (#[trigger] frame_slot(o_slots as int, j)) as usize,
            ) by {
                assert(pre.empty_slot(root, frame_slot(o_slots as int, j) as usize));
            }
        },
        AcallCall::Map { slot, va, level, from, page } => {
            reveal(CapKernel::map_contract_fields);
            assert(level == 1);
            let br = block_ref_of_map(pre, root, from as usize, page as usize);
            pre.lemma_page_span();
            assert forall|j: int| 0 <= j < o_pages implies post.empty_slot(
                root,
                (#[trigger] frame_slot(o_slots as int, j)) as usize,
            ) by {
                let sj = frame_slot(o_slots as int, j) as usize;
                assert(pre.empty_slot(root, sj));
                assert(pre.tables.has_slot(&pre.list, root, sj));
            }
            assert forall|j: int| 0 <= j < o_pages implies {
                let p = ob + j;
                &&& post.blocks.tracks(p)
                &&& (#[trigger] post.blocks.pages@[o_memory as int / PAGE_SZ as int + j]).kind is Free
                &&& !post.blocks.covered(p)
            } by {
                assert(pre.blocks.pages@[ob + j].kind is Free);
                assert(pre.blocks.tracks(ob + j));
                lemma_refs_changed_covered(
                    &pre.blocks,
                    &post.blocks,
                    br,
                    (verified::capability::refs::block_refs(&pre.blocks, br) + 1) as usize,
                    verified::capability::refs::block_dead(&pre.blocks, br),
                    ob + j,
                );
            }
            assert(post.spaces == pre.spaces);
            assert(b.maps.dom() == a.maps.dom());
            assert(!b.is_page(root));
            assert(b.entry(root, ol4) == a.entry(root, ol4));
        },
        AcallCall::Unmap { slot, va, level } => {
            reveal(CapKernel::unmap_contract_fields);
            let sp = v[slot as usize].base;
            let mp = space_mapping(a, sp)[address_path(va)];
            let br = verified::capability::refs::block_ref(&pre.blocks, mp.addr / PAGE_SZ);
            let refs = verified::capability::refs::block_refs(&pre.blocks, br);
            pre.lemma_page_span();
            assert forall|j: int| 0 <= j < o_pages implies post.empty_slot(
                root,
                (#[trigger] frame_slot(o_slots as int, j)) as usize,
            ) by {
                let sj = frame_slot(o_slots as int, j) as usize;
                assert(pre.empty_slot(root, sj));
                assert(pre.tables.has_slot(&pre.list, root, sj));
            }
            assert forall|j: int| 0 <= j < o_pages implies {
                let p = ob + j;
                &&& post.blocks.tracks(p)
                &&& (#[trigger] post.blocks.pages@[o_memory as int / PAGE_SZ as int + j]).kind is Free
                &&& !post.blocks.covered(p)
            } by {
                assert(pre.blocks.pages@[ob + j].kind is Free);
                assert(pre.blocks.tracks(ob + j));
                lemma_refs_changed_covered(
                    &pre.blocks,
                    &post.blocks,
                    br,
                    (refs - 1) as usize,
                    verified::capability::refs::block_dead(&pre.blocks, br) || refs == 1,
                    ob + j,
                );
            }
            assert(post.spaces == pre.spaces);
            assert(b.maps.dom() == a.maps.dom());
            assert(!b.is_page(root));
            assert(b.entry(root, ol4) == a.entry(root, ol4));
        },
        AcallCall::Inspect { at } => {
            reveal(CapKernel::inspect_contract_fields);
            assert(b == a);
        },
    }
}

/// The block whose count an accepted map of page `page` of the frame capability at index `from` of
/// the table at `root` raises.
pub open spec fn block_ref_of_map(k: CapKernel, root: usize, from: usize, page: usize) -> verified::capability::refs::BlockRef {
    verified::capability::refs::block_ref(
        &k.blocks,
        verified::capability::caller::view_frame(k.table_view(root)[from], page),
    )
}

/// The accepted steps of one source's back, in its window, with no other caller's step between, keep
/// what a fresh other source asks of the kernel, when the two are apart.
pub proof fn lemma_steps_keep_other(
    init: CapKernel,
    root: usize,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
    o_untyped: u64,
    o_memory: u64,
    o_pages: usize,
    o_slots: u64,
    o_window: usize,
)
    requires
        acall_alone(init, steps),
        acall_ok(steps),
        forall|k: int| 0 <= k < steps.len() ==> (#[trigger] steps[k]).root == root && steps[k].valid(),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
        source_config(memory, pages, slots, window),
        source_config(o_memory, o_pages, o_slots, o_window),
        sources_apart(memory, pages, slots, window, o_memory, o_pages, o_slots, o_window),
        own_kernel_ready(init, root, space, o_untyped, o_memory, o_pages, o_slots, o_window),
    ensures
        own_kernel_ready(
            if steps.len() == 0 { init } else { steps.last().post },
            root,
            space,
            o_untyped,
            o_memory,
            o_pages,
            o_slots,
            o_window,
        ),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let n = steps.len() - 1;
        let front = steps.drop_last();
        assert forall|k: int| 0 <= k < front.len() implies (#[trigger] front[k]).pre
            == (if k == 0 { init } else { front[k - 1].post }) by {
            assert(front[k] == steps[k]);
            assert(steps[k].pre == (if k == 0 { init } else { steps[k - 1].post }));
            if k > 0 {
                assert(front[k - 1] == steps[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < front.len() implies (#[trigger] front[k]).out.status == STATUS_OK by {
            assert(front[k] == steps[k]);
        }
        assert forall|k: int| 0 <= k < front.len() implies (#[trigger] front[k]).root == root && front[k].valid() by {
            assert(front[k] == steps[k]);
        }
        assert forall|k: int| 0 <= k < front.len() implies acall_call_in_window(
            #[trigger] front[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ) by {
            assert(front[k] == steps[k]);
        }
        lemma_steps_keep_other(
            init, root, front, space, untyped, memory, pages, slots, window, start, count,
            o_untyped, o_memory, o_pages, o_slots, o_window,
        );
        let last = steps[n];
        assert(last.pre == (if n == 0 { init } else { steps[n - 1].post }));
        if n > 0 {
            assert(front.last() == steps[n - 1]);
        }
        assert(last.out.status == STATUS_OK);
        assert(last.root == root && last.valid());
        assert(acall_call_in_window(last, space, untyped, memory, pages, slots, window, start, count));
        lemma_step_keeps_other(
            last, space, untyped, memory, pages, slots, window, start, count,
            o_untyped, o_memory, o_pages, o_slots, o_window,
        );
        assert(steps.last() == last);
    }
}

/// From `pre` to `post`, every entry of the space at `root` off the level-4 entry `l4` was there in
/// `pre`, as it is: the space gained nothing outside `l4`.
pub open spec fn mapping_kept_off(pre: CapKernel, post: CapKernel, root: usize, l4: usize) -> bool {
    let a = space_mapping(tree_of(&pre.table_pages, &pre.spaces), root);
    let b = space_mapping(tree_of(&post.table_pages, &post.spaces), root);
    forall|p: SpacePath| #[trigger] b.contains_key(p) && p.l4 != l4 ==> a.contains_key(p) && b[p] == a[p]
}

/// One step of a back in its window, accepted or refused, adds to the caller's space only in its
/// window's level-4 entry: a map in the window's run, the one step that adds, adds at a path of that
/// entry.
proof fn lemma_step_mapping_off(
    s: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
)
    requires
        s.valid(),
        acall_call_in_window(s, space, untyped, memory, pages, slots, window, start, count),
        window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        window <= start,
        start + count * PAGE_BYTES <= window + WINDOW_BYTES,
    ensures
        mapping_kept_off(s.pre, s.post, s.root, address_path(window as u64).l4),
{
    reveal(AcallStep::valid);
    reveal(acall_call_in_window);
    reveal(acall_setup_call);
    let pre = s.pre;
    let post = s.post;
    let root = s.root;
    let a = tree_of(&pre.table_pages, &pre.spaces);
    let b = tree_of(&post.table_pages, &post.spaces);
    let l4 = address_path(window as u64).l4;
    match s.call {
        AcallCall::Map { slot, va, level, from, page } => {
            if s.out.status == STATUS_OK {
                let sp = pre.table_view(root)[slot as usize].base;
                assert(run_pages(start, count).contains(va as int));
                lemma_window_level4(window, window as int);
                lemma_window_level4(window, va as int);
                assert(address_path(va).l4 == l4);
                if sp != root {
                    assert(space_mapping(b, root) == space_mapping(a, root));
                }
            } else {
                assert(b == a);
            }
        },
        AcallCall::Unmap { slot, va, level } => {
            if s.out.status == STATUS_OK {
                let sp = pre.table_view(root)[slot as usize].base;
                if sp != root {
                    assert(space_mapping(b, root) == space_mapping(a, root));
                }
            } else {
                assert(b == a);
            }
        },
        _ => {
            assert(space_mapping(b, root) == space_mapping(a, root));
        },
    }
}

/// The steps of a back in its window, with other callers' steps between, add to the caller's space
/// only in its window's level-4 entry, from `init` up to the end of step `n - 1`: the rely keeps the
/// sealed, recorded process's space from gaining entries between steps.
proof fn lemma_steps_mapping_off_upto(
    init: CapKernel,
    root: usize,
    steps: Seq<AcallStep>,
    n: int,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
)
    requires
        0 < n <= steps.len(),
        init.sealed(root),
        init.processes.records@.contains_key(root),
        CapKernel::rely(init, steps[0].pre, root),
        forall|k: int| 0 <= k < steps.len() ==> (#[trigger] steps[k]).root == root && steps[k].valid(),
        forall|j: int, k: int| 0 <= j && k == j + 1 && k < steps.len() ==> CapKernel::rely(
            (#[trigger] steps[j]).post,
            (#[trigger] steps[k]).pre,
            root,
        ),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
        window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        window <= start,
        start + count * PAGE_BYTES <= window + WINDOW_BYTES,
    ensures
        mapping_kept_off(init, steps[n - 1].post, root, address_path(window as u64).l4),
    decreases n,
{
    reveal(AcallStep::valid);
    let l4 = address_path(window as u64).l4;
    let last = steps[n - 1];
    lemma_step_mapping_off(last, space, untyped, memory, pages, slots, window, start, count);
    let entered = if n == 1 { init } else { steps[n - 2].post };
    if n == 1 {
        assert(CapKernel::space_kept(init, last.pre, root));
    } else {
        lemma_steps_mapping_off_upto(init, root, steps, n - 1, space, untyped, memory, pages, slots, window, start, count);
        let prev = steps[n - 2];
        assert(prev.valid());
        assert(prev.post.sealed(root));
        assert(prev.post.processes.records@.contains_key(root));
        assert(CapKernel::rely(prev.post, last.pre, root));
        assert(CapKernel::space_kept(prev.post, last.pre, root));
    }
    let m0 = space_mapping(tree_of(&init.table_pages, &init.spaces), root);
    let me = space_mapping(tree_of(&entered.table_pages, &entered.spaces), root);
    let mp = space_mapping(tree_of(&last.pre.table_pages, &last.pre.spaces), root);
    let mq = space_mapping(tree_of(&last.post.table_pages, &last.post.spaces), root);
    assert forall|p: SpacePath| #[trigger] mq.contains_key(p) && p.l4 != l4 implies m0.contains_key(p) && mq[p] == m0[p] by {
        assert(mp.contains_key(p) && mq[p] == mp[p]);
        assert(me.contains_key(p) && mp[p] == me[p]);
        if n > 1 {
            assert(mapping_kept_off(init, steps[n - 2].post, root, l4));
        }
    }
}

/// A back's steps in its window, whoever else stepped between them, add to the caller's space only in
/// its window's level-4 entry.
pub proof fn lemma_steps_mapping_off(
    pre: Caller,
    post: Caller,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
)
    requires
        acall_steps(pre, post, steps),
        pre.kernel().sealed(pre.root()),
        pre.kernel().processes.records@.contains_key(pre.root()),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
        window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        window <= start,
        start + count * PAGE_BYTES <= window + WINDOW_BYTES,
    ensures
        mapping_kept_off(pre.kernel(), post.kernel(), pre.root(), address_path(window as u64).l4),
{
    reveal(acall_steps);
    if steps.len() > 0 {
        lemma_steps_mapping_off_upto(
            pre.kernel(), pre.root(), steps, steps.len() as int, space, untyped, memory, pages, slots, window, start, count,
        );
        assert(steps.last() == steps[steps.len() - 1]);
    }
}

/// A page path off the level-4 entry a space gained entries in, where nothing large nor nothing at all
/// was mapped, is still so.
pub proof fn lemma_page_agrees_kept_off(pre: CapKernel, post: CapKernel, root: usize, l4: usize, p: SpacePath)
    requires
        mapping_kept_off(pre, post, root, l4),
        p.l4 != l4,
        page_agrees(space_mapping(tree_of(&pre.table_pages, &pre.spaces), root), p, None),
    ensures
        page_agrees(space_mapping(tree_of(&post.table_pages, &post.spaces), root), p, None),
{
    assert(large_path(p).l4 == p.l4);
}

/// A window's pages are at its level-4 entry, which is not that of another window.
pub proof fn lemma_window_page_off(window: usize, o_window: usize, a: int)
    requires
        window_page(o_window, a),
        window as int % SIZE_512G as int == 0,
        o_window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        o_window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        window != o_window,
    ensures
        address_path(a as u64).l4 != address_path(window as u64).l4,
{
    lemma_windows_apart(window, o_window);
    lemma_window_level4(o_window, a);
    lemma_window_level4(o_window, o_window as int);
}

/// After one source's accepted steps in its window with no other caller's step between, the other
/// source, apart from it, is ready still: its own part of the kernel is kept, the process is as the
/// stepping source's readiness says, and the flush epoch did not move.
pub proof fn lemma_other_source_ready(
    pre: Caller,
    post: Caller,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
    o_untyped: u64,
    o_memory: u64,
    o_pages: usize,
    o_slots: u64,
    o_window: usize,
)
    requires
        source_ready(pre, space, untyped, memory, pages, slots, window),
        source_ready(pre, space, o_untyped, o_memory, o_pages, o_slots, o_window),
        sources_apart(memory, pages, slots, window, o_memory, o_pages, o_slots, o_window),
        acall_steps(pre, post, steps),
        caller_alone(pre, post),
        acall_ok(steps),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
        process_ready(post.kernel(), pre.root()),
        post.kernel().flush_epoch == pre.kernel().flush_epoch,
    ensures
        source_ready(post, space, o_untyped, o_memory, o_pages, o_slots, o_window),
{
    let root = pre.root();
    lemma_acall_steps_alone(pre, post, steps);
    reveal(acall_steps);
    lemma_kernel_source_ready_parts(pre.kernel(), root, space, untyped, memory, pages, slots, window);
    lemma_kernel_source_ready_parts(pre.kernel(), root, space, o_untyped, o_memory, o_pages, o_slots, o_window);
    lemma_kernel_source_ready_parts(post.kernel(), root, space, o_untyped, o_memory, o_pages, o_slots, o_window);
    lemma_steps_keep_other(
        pre.kernel(), root, steps, space, untyped, memory, pages, slots, window, start, count,
        o_untyped, o_memory, o_pages, o_slots, o_window,
    );
    if steps.len() > 0 {
        assert(steps.last() == steps[steps.len() - 1]);
    }
}

/// After one source's steps in a run of its window, whoever else stepped between them, another window
/// of the process that was unclaimed is unclaimed still, when the caller's page tokens and the start of
/// its history are as they were.
pub proof fn lemma_other_window_unclaimed(
    pre: Caller,
    post: Caller,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
    o_window: usize,
)
    requires
        window_unclaimed(pre, o_window),
        own_process(pre),
        acall_steps(pre, post, steps),
        post.start() == pre.start(),
        post.pages().dom() == pre.pages().dom(),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
        window as int % SIZE_512G as int == 0,
        o_window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        o_window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        window != o_window,
        window <= start,
        start + count * PAGE_BYTES <= window + WINDOW_BYTES,
    ensures
        window_unclaimed(post, o_window),
{
    reveal(acall_steps);
    let root = pre.root();
    let l4 = address_path(window as u64).l4;
    lemma_steps_mapping_off(pre, post, steps, space, untyped, memory, pages, slots, window, start, count);
    assert forall|a: int| #[trigger] window_page(o_window, a) implies {
        &&& !post.pages().contains_key(address_path(a as u64))
        &&& page_agrees(
            space_mapping(tree_of(&post.start().table_pages, &post.start().spaces), post.root()),
            address_path(a as u64),
            None,
        )
        &&& page_agrees(
            space_mapping(tree_of(&post.kernel().table_pages, &post.kernel().spaces), post.root()),
            address_path(a as u64),
            None,
        )
    } by {
        let p = address_path(a as u64);
        assert(!pre.pages().dom().contains(p));
        lemma_window_page_off(window, o_window, a);
        lemma_page_agrees_kept_off(pre.kernel(), post.kernel(), root, l4, p);
    }
}

/// One step of a back in its window, accepted or refused, keeps every slot of `root`'s table
/// naming the caller's own space: it either leaves the table unchanged or inserts a `Frame`
/// capability, which writes no space.
pub(crate) proof fn lemma_step_keeps_slot_names_own_space(
    s: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
)
    requires
        s.valid(),
        acall_call_in_window(s, space, untyped, memory, pages, slots, window, start, count),
    ensures
        forall|slot: usize|
            #[trigger] slot_names_own_space(s.pre, s.root, slot)
                ==> slot_names_own_space(s.post, s.root, slot),
{
    reveal(AcallStep::valid);
    reveal(acall_call_in_window);
    reveal(acall_setup_call);
    let pre = s.pre;
    let post = s.post;
    let root = s.root;
    match s.call {
        AcallCall::Retype { untyped: u, kind, base, word, level } => {
            if kind == RETYPE_FRAME && s.out == status_only(STATUS_OK)
                && pre.retype_allowed(root, kind, u as usize, base as usize, word, level as usize)
            {
                let parent = pre.tables.node_of(root, u as usize);
                let fv = frame_view(base as usize, 0u8, parent);
                assert(post.table_view(root) == pre.table_view(root).insert(word as usize, fv));
                assert(!view_writes_space(fv));
            } else {
                assert(post.table_view(root) == pre.table_view(root));
            }
        },
        _ => {
            assert(post.table_view(root) == pre.table_view(root));
        },
    }
}

proof fn lemma_steps_keep_slot_names_own_space_upto(
    init: CapKernel,
    root: usize,
    steps: Seq<AcallStep>,
    n: int,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
)
    requires
        0 < n <= steps.len(),
        init.sealed(root),
        CapKernel::rely(init, steps[0].pre, root),
        forall|k: int| 0 <= k < steps.len() ==> (#[trigger] steps[k]).root == root && steps[k].valid(),
        forall|j: int, k: int| 0 <= j && k == j + 1 && k < steps.len() ==> CapKernel::rely(
            (#[trigger] steps[j]).post,
            (#[trigger] steps[k]).pre,
            root,
        ),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
    ensures
        forall|slot: usize|
            #[trigger] slot_names_own_space(init, root, slot)
                ==> slot_names_own_space(steps[n - 1].post, root, slot),
    decreases n,
{
    reveal(AcallStep::valid);
    let last = steps[n - 1];
    lemma_step_keeps_slot_names_own_space(last, space, untyped, memory, pages, slots, window, start, count);
    if n > 1 {
        lemma_steps_keep_slot_names_own_space_upto(
            init, root, steps, n - 1, space, untyped, memory, pages, slots, window, start, count,
        );
    }
    assert forall|slot: usize| #[trigger] slot_names_own_space(init, root, slot)
        implies slot_names_own_space(last.post, root, slot) by {
        if n == 1 {
            lemma_rely_keeps_slot_names_own_space(init, last.pre, root, slot);
        } else {
            let prev = steps[n - 2];
            assert(prev.valid());
            lemma_rely_keeps_slot_names_own_space(prev.post, last.pre, root, slot);
        }
    }
}

/// The steps of a back in its window, whoever else stepped between them, keep every slot of
/// `pre`'s table naming the caller's own space.
pub proof fn lemma_steps_keep_slot_names_own_space(
    pre: Caller,
    post: Caller,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
)
    requires
        acall_steps(pre, post, steps),
        pre.kernel().sealed(pre.root()),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
    ensures
        forall|slot: usize|
            #[trigger] slot_names_own_space(pre.kernel(), pre.root(), slot)
                ==> slot_names_own_space(post.kernel(), post.root(), slot),
{
    reveal(acall_steps);
    if steps.len() > 0 {
        lemma_steps_keep_slot_names_own_space_upto(
            pre.kernel(), pre.root(), steps, steps.len() as int, space, untyped, memory, pages, slots, window, start, count,
        );
        assert(steps.last() == steps[steps.len() - 1]);
    }
}

/// One accepted step of a back in its window keeps `retype_allowed` for a frame retype from
/// `other_untyped` at `frame_base` into `slot` when `slot` is none of the source's frame slots and
/// `frame_base`'s page lies outside the source's untyped run.
#[verifier::spinoff_prover]
proof fn lemma_step_keeps_retype_frame_allowed(
    s: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
    other_untyped: u64,
    frame_base: u64,
    slot: u64,
)
    requires
        s.valid(),
        s.out.status == STATUS_OK,
        acall_call_in_window(s, space, untyped, memory, pages, slots, window, start, count),
        source_config(memory, pages, slots, window),
        other_untyped < TABLE_INDICES,
        slot < TABLE_INDICES,
        forall|i: int| 0 <= i < pages ==> #[trigger] frame_slot(slots as int, i) != slot as int,
        (frame_base as int / PAGE_SZ as int) < memory as int / PAGE_SZ as int
            || (frame_base as int / PAGE_SZ as int) >= memory as int / PAGE_SZ as int + pages as int,
        s.pre.retype_allowed(s.root, RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0),
    ensures
        s.post.retype_allowed(s.root, RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0),
{
    reveal(AcallStep::valid);
    reveal(acall_call_in_window);
    reveal(acall_setup_call);
    let pre = s.pre;
    let post = s.post;
    let root = s.root;
    let at_frame = (frame_base as usize / PAGE_SZ) as int;
    pre.lemma_table_view(root, other_untyped as usize);
    let nu = pre.tables.node_of(root, other_untyped as usize);
    assert(pre.tables.has_slot(&pre.list, root, other_untyped as usize));
    assert(pre.tables.is_cap(&pre.list, nu));
    match s.call {
        AcallCall::Retype { untyped: u, kind, base, word, level } => {
            if kind == RETYPE_FRAME {
                let i = choose|i: int|
                    0 <= i < pages && base as int == untyped_page(memory, i)
                        && word as int == #[trigger] frame_slot(slots as int, i);
                let to = word as usize;
                let at = (base as usize / PAGE_SZ) as int;
                reveal(CapKernel::retype_frame_contract_fields);
                assert(pre.empty_slot(root, to));
                pre.lemma_table_view(root, to);
                assert(other_untyped as usize != to);
                assert(post.table_view(root)[other_untyped as usize] == pre.table_view(root)[other_untyped as usize]);
                assert(post.tables.node_of(root, other_untyped as usize) == nu);
                assert(post.list.nodes@[nu as int].depth == pre.list.nodes@[nu as int].depth);
                lemma_frame_slot_index(slots, pages, i);
                assert(to != slot as usize);
                lemma_distinct_slots_distinct_nodes(pre, root, slot as usize, to);
                assert(post.empty_slot(root, slot as usize));
                lemma_untyped_page_index(memory, i);
                assert(at == memory as int / PAGE_SZ as int + i);
                assert(at_frame != at);
                assert(post.blocks.tracks(at_frame));
                assert(post.blocks.pages@[at_frame] == pre.blocks.pages@[at_frame]);
                assert(!post.blocks.covered(at_frame));
            } else {
                assert(kind == RETYPE_TABLE_PAGE);
                let g = choose|g: int|
                    0 <= g && g + TABLE_PAGES <= pages && g % TABLE_PAGES as int == 0
                        && base as int == #[trigger] untyped_page(memory, g);
                let child = base as usize;
                let at = (child / PAGE_SZ) as int;
                reveal(CapKernel::retype_table_contract_fields);
                lemma_retype_table_kept(pre, post, child);
                lemma_untyped_page_index(memory, g);
                assert(at == memory as int / PAGE_SZ as int + g);
                assert(!(at <= at_frame < at + TABLE_PAGES as int));
                assert(post.blocks.tracks(at_frame));
                assert(post.blocks.pages@[at_frame] == pre.blocks.pages@[at_frame]);
                assert(!post.blocks.covered(at_frame));
                assert(post.table_view(root) == pre.table_view(root));
                assert(post.tables == pre.tables);
                assert(post.empty_slot(root, slot as usize));
            }
        },
        AcallCall::Link { .. } => {
            reveal(CapKernel::link_contract_fields);
        },
        AcallCall::Map { slot: m_slot, va: _, level: _, from: m_from, page: m_page } => {
            reveal(CapKernel::map_contract_fields);
            let br = block_ref_of_map(pre, root, m_from as usize, m_page as usize);
            pre.lemma_page_span();
            lemma_refs_changed_covered(
                &pre.blocks,
                &post.blocks,
                br,
                (verified::capability::refs::block_refs(&pre.blocks, br) + 1) as usize,
                verified::capability::refs::block_dead(&pre.blocks, br),
                at_frame,
            );
        },
        AcallCall::Unmap { slot: u_slot, va: u_va, level: _ } => {
            reveal(CapKernel::unmap_contract_fields);
            let sp = pre.table_view(root)[u_slot as usize].base;
            let mp = space_mapping(tree_of(&pre.table_pages, &pre.spaces), sp)[address_path(u_va)];
            let br = verified::capability::refs::block_ref(&pre.blocks, mp.addr / PAGE_SZ);
            let refs = verified::capability::refs::block_refs(&pre.blocks, br);
            pre.lemma_page_span();
            lemma_refs_changed_covered(
                &pre.blocks,
                &post.blocks,
                br,
                (refs - 1) as usize,
                verified::capability::refs::block_dead(&pre.blocks, br) || refs == 1,
                at_frame,
            );
        },
        AcallCall::Inspect { .. } => {
            reveal(CapKernel::inspect_contract_fields);
        },
    }
}

/// The accepted steps of a back in its window, with no other caller stepping between, keep
/// `retype_allowed` for a frame retype outside the source's frame slots and untyped run.
pub proof fn lemma_steps_keep_retype_frame_allowed(
    pre: Caller,
    post: Caller,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
    other_untyped: u64,
    frame_base: u64,
    slot: u64,
)
    requires
        acall_steps(pre, post, steps),
        caller_alone(pre, post),
        acall_ok(steps),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
        source_config(memory, pages, slots, window),
        other_untyped < TABLE_INDICES,
        slot < TABLE_INDICES,
        forall|i: int| 0 <= i < pages ==> #[trigger] frame_slot(slots as int, i) != slot as int,
        (frame_base as int / PAGE_SZ as int) < memory as int / PAGE_SZ as int
            || (frame_base as int / PAGE_SZ as int) >= memory as int / PAGE_SZ as int + pages as int,
        pre.kernel().retype_allowed(pre.root(), RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0),
    ensures
        post.kernel().retype_allowed(post.root(), RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0),
    decreases steps.len(),
{
    lemma_acall_steps_alone(pre, post, steps);
    reveal(acall_steps);
    let n = steps.len();
    if n > 0 {
        let front = steps.drop_last();
        let last = steps[n - 1];
        lemma_steps_keep_retype_frame_allowed_seq(
            pre.kernel(), pre.root(), steps, space, untyped, memory, pages, slots, window, start, count,
            other_untyped, frame_base, slot,
        );
        assert(steps.last() == last);
    }
}

proof fn lemma_steps_keep_retype_frame_allowed_seq(
    init: CapKernel,
    root: usize,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
    other_untyped: u64,
    frame_base: u64,
    slot: u64,
)
    requires
        acall_alone(init, steps),
        acall_ok(steps),
        forall|k: int| 0 <= k < steps.len() ==> (#[trigger] steps[k]).root == root && steps[k].valid(),
        forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
            #[trigger] steps[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ),
        source_config(memory, pages, slots, window),
        other_untyped < TABLE_INDICES,
        slot < TABLE_INDICES,
        forall|i: int| 0 <= i < pages ==> #[trigger] frame_slot(slots as int, i) != slot as int,
        (frame_base as int / PAGE_SZ as int) < memory as int / PAGE_SZ as int
            || (frame_base as int / PAGE_SZ as int) >= memory as int / PAGE_SZ as int + pages as int,
        init.retype_allowed(root, RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0),
    ensures
        (if steps.len() == 0 { init } else { steps.last().post }).retype_allowed(
            root, RETYPE_FRAME, other_untyped as usize, frame_base as usize, slot, 0,
        ),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let n = steps.len() - 1;
        let front = steps.drop_last();
        assert forall|k: int| 0 <= k < front.len() implies (#[trigger] front[k]).pre
            == (if k == 0 { init } else { front[k - 1].post }) by {
            assert(front[k] == steps[k]);
            assert(steps[k].pre == (if k == 0 { init } else { steps[k - 1].post }));
            if k > 0 {
                assert(front[k - 1] == steps[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < front.len() implies (#[trigger] front[k]).out.status == STATUS_OK by {
            assert(front[k] == steps[k]);
        }
        assert forall|k: int| 0 <= k < front.len() implies (#[trigger] front[k]).root == root && front[k].valid() by {
            assert(front[k] == steps[k]);
        }
        assert forall|k: int| 0 <= k < front.len() implies acall_call_in_window(
            #[trigger] front[k],
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            start,
            count,
        ) by {
            assert(front[k] == steps[k]);
        }
        lemma_steps_keep_retype_frame_allowed_seq(
            init, root, front, space, untyped, memory, pages, slots, window, start, count,
            other_untyped, frame_base, slot,
        );
        let last = steps[n];
        assert(last.pre == (if n == 0 { init } else { steps[n - 1].post }));
        if n > 0 {
            assert(front.last() == steps[n - 1]);
        }
        assert(last.out.status == STATUS_OK);
        assert(last.root == root && last.valid());
        assert(acall_call_in_window(last, space, untyped, memory, pages, slots, window, start, count));
        lemma_step_keeps_retype_frame_allowed(
            last, space, untyped, memory, pages, slots, window, start, count,
            other_untyped, frame_base, slot,
        );
        assert(steps.last() == last);
    }
}

} // verus!
