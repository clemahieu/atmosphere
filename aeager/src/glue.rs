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
use verified::capability::block::order_pages;
#[cfg(verus_keep_ghost)]
use verified::capability::reach::Right;
#[cfg(verus_keep_ghost)]
use verified::capability::caller::{frame_view, view_frame, view_retypes, view_writes_space};
#[cfg(verus_keep_ghost)]
use verified::capability::view::right_bit;
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::refs::{
    block_dead, block_ref, block_refs, block_typed, blocks_refs_changed, BlockRef,
};
#[cfg(verus_keep_ghost)]
use verified::capability::link::{
    child_entry, lemma_table_addr_valid, lemma_table_bound, linked, table_links_wf, tree_of, TableTree,
};
#[cfg(verus_keep_ghost)]
use verified::capability::map::{
    address_path, entry_written, frame_map_entry, names_entry, walk_table, LOWER_HALF_END,
};
#[cfg(verus_keep_ghost)]
use verified::capability::mapping::{entries_cleared, space_mapping, step, SpacePath};
#[cfg(verus_keep_ghost)]
use verified::capability::rely::same_cap;
#[cfg(verus_keep_ghost)]
use verified::capability::retype::FRAME_RIGHTS;
#[cfg(verus_keep_ghost)]
use verified::define::NUM_CPUS;
#[cfg(verus_keep_ghost)]
use verified::capability::list::{MAX_DEPTH, NODE_SPACE};
#[cfg(verus_keep_ghost)]
use verified::capability::space::{
    fresh_table, holds_kernel, SpaceKind, TableParent, TABLE_NODE_PAGES, TABLE_PAGE_BYTES,
};
#[cfg(verus_keep_ghost)]
use verified::capability::table::{block_bytes, index_entry, index_slot, NO_LEAF, TABLE_INDICES};
#[cfg(verus_keep_ghost)]
use verified::define::{ENTRIES, KERNEL_MEM_END_L4INDEX, PAGE_SZ, SIZE_1G, SIZE_2M, SIZE_512G};
#[cfg(verus_keep_ghost)]
use verified::capability::position::spec_position;
use verified::capability::operation::*;
#[cfg(verus_keep_ghost)]
use verified::capability::position::POSITION_INDEX_MASK;

#[cfg(verus_keep_ghost)]
use crate::eager::{
    frame_slot, lemma_frame_slot, occupied, untyped_page, window_block, FREE, HELD, LEAF_INDICES,
    MAPPED, MAX_PAGES, PARKED, REGION_BYTES, TABLE_PAGES, TAKEN, WINDOW_BLOCKS, WINDOW_BYTES,
};

verus! {

/// One memory system call the eager source makes through `acall::memory`.
pub ghost enum AcallCall {
    Retype { untyped: u64, kind: u64, base: u64, word: u64, level: u64 },
    Inspect { at: u64 },
    Link { slot: u64, va: u64, level: u64, from: u64, child: u64 },
    Map { slot: u64, va: u64, level: u64, from: u64, page: u64 },
    Unmap { slot: u64, va: u64, level: u64 },
}

/// One step `acall::memory` took for the process at `root`, entering from `pre` and leaving `post`,
/// returning `out`.
pub ghost struct AcallStep {
    pub pre: CapKernel,
    pub post: CapKernel,
    pub root: usize,
    pub call: AcallCall,
    pub out: Outcome,
}

impl AcallStep {
    /// `self` satisfies the `acall::memory` contract of `self.call` from `self.pre` to `self.post`
    /// for `self.root` with outcome `self.out`.
    #[verifier::opaque]
    pub open spec fn valid(self) -> bool {
        &&& self.pre.wf()
        &&& self.post.wf()
        &&& match self.call {
            AcallCall::Retype { untyped, kind, base, word, level } =>
                CapKernel::retype_contract(
                    self.pre, self.post, self.root, kind, untyped as usize, base as usize, word, level as usize, self.out,
                ),
            AcallCall::Inspect { at } =>
                CapKernel::inspect_contract(self.pre, self.post, self.root, spec_position(at), self.out),
            AcallCall::Link { slot, va, level, from, child } =>
                CapKernel::link_contract(
                    self.pre, self.post, self.root, slot as usize, va, level, from as usize, child as usize, self.out,
                ),
            AcallCall::Map { slot, va, level, from, page } =>
                CapKernel::map_contract(
                    self.pre, self.post, self.root, slot as usize, va, level, from as usize, page as usize, self.out,
                ),
            AcallCall::Unmap { slot, va, level } =>
                CapKernel::unmap_contract(self.pre, self.post, self.root, slot as usize, va, level, self.out),
        }
    }
}

/// `steps` is a sequence of valid `acall::memory` steps taking `pre` to `post`: `post`'s history extends
/// `pre`'s with each step's `(pre, post)` pair, and each enters from a state the rely relates to the one
/// before it, `pre`'s kernel for the first and the last step's `post` for the others, since other
/// callers' steps may come between.
#[verifier::opaque]
pub open spec fn acall_steps(pre: Caller, post: Caller, steps: Seq<AcallStep>) -> bool {
    let n = pre.history().len() as int;
    &&& post.root() == pre.root()
    &&& post.history().len() == n + steps.len()
    &&& post.history().take(n) == pre.history()
    &&& forall|k: int| 0 <= k < steps.len() ==>
        post.history().skip(n)[k] == ((#[trigger] steps[k]).pre, steps[k].post)
    &&& if steps.len() == 0 {
        post.kernel() == pre.kernel()
    } else {
        &&& CapKernel::rely(pre.kernel(), steps[0].pre, pre.root())
        &&& steps.last().post == post.kernel()
        &&& forall|k: int| 0 <= k < steps.len() ==> {
            &&& (#[trigger] steps[k]).root == pre.root()
            &&& steps[k].valid()
        }
        &&& forall|j: int, k: int|
            0 <= j && k == j + 1 && k < steps.len() ==> CapKernel::rely(
                (#[trigger] steps[j]).post,
                (#[trigger] steps[k]).pre,
                pre.root(),
            )
    }
}

/// Every step in `steps` was accepted by the kernel (`STATUS_OK`).
pub open spec fn acall_ok(steps: Seq<AcallStep>) -> bool {
    forall|k: int| 0 <= k < steps.len() ==> (#[trigger] steps[k]).out.status == STATUS_OK
}

/// No other caller stepped between the steps of `steps` starting from `init`: the first step entered
/// directly from `init`, and each later step entered directly from the post-state of the step before it.
pub open spec fn acall_alone(init: CapKernel, steps: Seq<AcallStep>) -> bool {
    forall|k: int| 0 <= k < steps.len() ==>
        (#[trigger] steps[k]).pre == (if k == 0 { init } else { steps[k - 1].post })
}

/// No step takes a caller to itself.
pub proof fn lemma_acall_steps_none(c: Caller)
    ensures
        acall_steps(c, c, Seq::<AcallStep>::empty()),
{
    reveal(acall_steps);
    assert(c.history().take(c.history().len() as int) =~= c.history());
}

/// One valid step of `pre`'s process, entering from a state the rely relates to `pre`'s kernel and
/// leaving `post`'s, takes `pre` to `post`.
pub proof fn lemma_acall_steps_one(pre: Caller, post: Caller, step: AcallStep)
    requires
        post.root() == pre.root(),
        post.history() == pre.history().push((step.pre, step.post)),
        CapKernel::rely(pre.kernel(), step.pre, pre.root()),
        step.post == post.kernel(),
        step.root == pre.root(),
        step.valid(),
    ensures
        acall_steps(pre, post, seq![step]),
{
    reveal(acall_steps);
    let n = pre.history().len() as int;
    let s = seq![step];
    assert(post.history().take(n) =~= pre.history());
    assert(post.history().skip(n) =~= seq![(step.pre, step.post)]);
    assert(s[0] == step && s.last() == step);
}

/// Concatenating two `acall::memory` step sequences, the second starting where the first ends, produces
/// one from the first's start to the second's end.
pub proof fn lemma_acall_steps_append(a: Caller, b: Caller, c: Caller, s1: Seq<AcallStep>, s2: Seq<AcallStep>)
    requires
        acall_steps(a, b, s1),
        acall_steps(b, c, s2),
    ensures
        acall_steps(a, c, s1 + s2),
{
    reveal(acall_steps);
    let na = a.history().len() as int;
    let nb = b.history().len() as int;
    let s = s1 + s2;
    assert(nb == na + s1.len());
    assert(c.history().take(na) =~= a.history()) by {
        assert(c.history().take(nb) == b.history());
        assert(b.history().take(na) == a.history());
        assert forall|i: int| 0 <= i < na implies #[trigger] c.history().take(na)[i] == a.history()[i] by {
            assert(c.history()[i] == c.history().take(nb)[i]);
            assert(b.history()[i] == b.history().take(na)[i]);
        }
    }
    assert forall|k: int| 0 <= k < s.len() implies
        c.history().skip(na)[k] == ((#[trigger] s[k]).pre, s[k].post) by {
        if k < s1.len() {
            assert(s[k] == s1[k]);
            assert(b.history().skip(na)[k] == (s1[k].pre, s1[k].post));
            assert(c.history().skip(na)[k] == c.history()[na + k]);
            assert(c.history()[na + k] == c.history().take(nb)[na + k]);
            assert(b.history()[na + k] == b.history().skip(na)[k]);
        } else {
            let m = k - s1.len();
            assert(s[k] == s2[m]);
            assert(c.history().skip(nb)[m] == (s2[m].pre, s2[m].post));
            assert(c.history().skip(na)[k] == c.history()[na + k]);
            assert(c.history().skip(nb)[m] == c.history()[nb + m]);
        }
    }
    if s1.len() == 0 {
        assert(s =~= s2);
    } else if s2.len() == 0 {
        assert(s =~= s1);
    } else {
        assert(s[0] == s1[0]);
        assert(s.last() == s2.last());
        assert forall|k: int| 0 <= k < s.len() implies {
            &&& (#[trigger] s[k]).root == a.root()
            &&& s[k].valid()
        } by {
            if k < s1.len() {
                assert(s[k] == s1[k]);
            } else {
                assert(s[k] == s2[k - s1.len()]);
            }
        }
        assert forall|j: int, k: int| 0 <= j && k == j + 1 && k < s.len() implies CapKernel::rely(
            (#[trigger] s[j]).post,
            (#[trigger] s[k]).pre,
            a.root(),
        ) by {
            if k < s1.len() {
                assert(s[j] == s1[j]);
                assert(s[k] == s1[k]);
            } else if j == s1.len() - 1 {
                assert(s[j] == s1.last());
                assert(s[k] == s2[0]);
            } else {
                assert(s[j] == s2[j - s1.len()]);
                assert(s[k] == s2[k - s1.len()]);
            }
        }
    }
}

/// Over a valid `acall_steps` sequence, `caller_alone` on the caller token is `acall_alone` on `steps`.
pub proof fn lemma_caller_alone_iff(pre: Caller, post: Caller, steps: Seq<AcallStep>)
    requires
        acall_steps(pre, post, steps),
    ensures
        caller_alone(pre, post) <==> acall_alone(pre.kernel(), steps),
{
    reveal(acall_steps);
    let n = pre.history().len() as int;
    let added = post.history().skip(n);
    assert(added.len() == steps.len());
    if steps.len() > 0 {
        assert(added.last() == added[steps.len() - 1]);
        assert(steps.last() == steps[steps.len() - 1]);
        assert(added[steps.len() - 1] == (steps[steps.len() - 1].pre, steps[steps.len() - 1].post));
    }
    if caller_alone(pre, post) {
        assert forall|k: int| 0 <= k < steps.len() implies
            (#[trigger] steps[k]).pre == (if k == 0 { pre.kernel() } else { steps[k - 1].post }) by {
            assert(added[k] == (steps[k].pre, steps[k].post));
            assert(added[k].0 == (if k == 0 { pre.kernel() } else { added[k - 1].1 }));
            if k > 0 {
                assert(added[k - 1] == (steps[k - 1].pre, steps[k - 1].post));
            }
        }
    }
    if acall_alone(pre.kernel(), steps) {
        assert forall|k: int| 0 <= k < added.len() implies
            (#[trigger] added[k]).0 == (if k == 0 { pre.kernel() } else { added[k - 1].1 }) by {
            assert(added[k] == (steps[k].pre, steps[k].post));
            assert(steps[k].pre == (if k == 0 { pre.kernel() } else { steps[k - 1].post }));
            if k > 0 {
                assert(added[k - 1] == (steps[k - 1].pre, steps[k - 1].post));
            }
        }
    }
}

/// What a valid `acall_steps` sequence that no other caller stepped between says of its steps: each is
/// a valid step of `pre`'s process, the first entered directly from `pre`'s kernel state and each later
/// one from the state the step before it left, and the last left `post`'s.
pub proof fn lemma_acall_steps_alone(pre: Caller, post: Caller, steps: Seq<AcallStep>)
    requires
        acall_steps(pre, post, steps),
        caller_alone(pre, post),
    ensures
        acall_alone(pre.kernel(), steps),
        forall|k: int| 0 <= k < steps.len() ==> {
            &&& (#[trigger] steps[k]).root == pre.root()
            &&& steps[k].valid()
            &&& steps[k].pre == (if k == 0 { pre.kernel() } else { steps[k - 1].post })
        },
        steps.len() > 0 ==> steps[steps.len() - 1].post == post.kernel(),
        steps.len() == 0 ==> post.kernel() == pre.kernel(),
{
    lemma_caller_alone_iff(pre, post, steps);
    reveal(acall_steps);
    if steps.len() > 0 {
        assert(steps.last() == steps[steps.len() - 1]);
    }
}

/// `caller_alone` across two concatenated `acall_steps` sequences implies `caller_alone` on each half.
pub proof fn lemma_caller_alone_split(a: Caller, b: Caller, c: Caller, s1: Seq<AcallStep>, s2: Seq<AcallStep>)
    requires
        acall_steps(a, b, s1),
        acall_steps(b, c, s2),
        caller_alone(a, c),
    ensures
        caller_alone(a, b),
        caller_alone(b, c),
{
    lemma_acall_steps_append(a, b, c, s1, s2);
    lemma_caller_alone_iff(a, c, s1 + s2);
    reveal(acall_steps);
    let s = s1 + s2;
    assert forall|k: int| 0 <= k < s1.len() implies
        (#[trigger] s1[k]).pre == (if k == 0 { a.kernel() } else { s1[k - 1].post }) by {
        assert(s1[k] == s[k]);
        assert(s[k].pre == (if k == 0 { a.kernel() } else { s[k - 1].post }));
        if k > 0 {
            assert(s1[k - 1] == s[k - 1]);
        }
    }
    assert forall|m: int| 0 <= m < s2.len() implies
        (#[trigger] s2[m]).pre == (if m == 0 { b.kernel() } else { s2[m - 1].post }) by {
        let k = s1.len() + m;
        assert(s2[m] == s[k]);
        assert(s[k].pre == (if k == 0 { a.kernel() } else { s[k - 1].post }));
        if m == 0 {
            if s1.len() > 0 {
                assert(s1.last() == s1[s1.len() - 1]);
                assert(s[k - 1] == s1[s1.len() - 1]);
            }
        } else {
            assert(s[k - 1] == s2[m - 1]);
        }
    }
    lemma_caller_alone_iff(a, b, s1);
    lemma_caller_alone_iff(b, c, s2);
}

/// What a fresh `Eager::new(space, untyped, memory, pages, slots, window)` asks of the kernel state `k`
/// for the caller whose table is at `root`, so that every system call its `back` makes is accepted when
/// no other caller steps between: the caller's process is live, sealed and recorded, with a process
/// space; `space` names a writable capability to that space; `untyped` names an untyped capability with
/// the retype right, at least two levels above `MAX_DEPTH`, covering `pages` free tracked pages from
/// `TABLE_PAGES`-aligned `memory`; each frame slot `frame_slot(slots, i)` lies in a present leaf of
/// `root` and is empty; `window` starts a non-kernel lower-half level-4 entry whose entry in `root`'s
/// space is empty; and `flush_epoch` has room for `MAX_PAGES` unmaps.
pub open spec fn kernel_source_ready(
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
    &&& k.wf()
    &&& k.sealed(root)
    &&& k.processes.records@.contains_key(root)
    &&& !k.processes.records@[root].value().dead
    &&& !k.blocks.pages@[(root / PAGE_SZ) as int].dead
    &&& k.spaces.roots@.contains_key(root)
    &&& k.spaces.records@[root].value().kind == SpaceKind::Process
    &&& k.flush_epoch as int + MAX_PAGES as int <= usize::MAX as int
    &&& pages <= MAX_PAGES
    &&& slots < TABLE_INDICES as u64
    &&& slots as int % LEAF_INDICES as int != 0
    &&& pages > 0 ==> frame_slot(slots as int, pages - 1) < TABLE_INDICES
    &&& memory as int % (TABLE_PAGES * PAGE_BYTES) as int == 0
    &&& memory + pages * PAGE_BYTES <= u64::MAX
    &&& window != 0
    &&& window as int % SIZE_512G as int == 0
    &&& window + WINDOW_BYTES <= LOWER_HALF_END as usize
    &&& v.contains_key(space as usize)
    &&& view_writes_space(v[space as usize])
    &&& v[space as usize].base == root
    &&& v.contains_key(untyped as usize)
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

/// `token`'s kernel state satisfies `kernel_source_ready` for `(space, untyped, memory, pages, slots, window)`.
pub open spec fn source_ready(
    token: Caller,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
) -> bool {
    kernel_source_ready(token.kernel(), token.root(), space, untyped, memory, pages, slots, window)
}

/// `source_ready` implies `Eager::new`'s bounds and `own_process` / `names_own_space` on `token`.
pub proof fn lemma_source_ready_premises(
    token: Caller,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
)
    requires
        source_ready(token, space, untyped, memory, pages, slots, window),
    ensures
        token.wf(),
        own_process(token),
        names_own_space(token, space),
        flush_room(token, MAX_PAGES as nat),
        window != 0,
        window as int % REGION_BYTES as int == 0,
        window + WINDOW_BYTES <= usize::MAX,
{
    use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
    assert(SIZE_512G as int == (ENTRIES as int) * (REGION_BYTES as int)) by {
        assert(SIZE_512G == ENTRIES * SIZE_1G);
        assert(REGION_BYTES == SIZE_1G);
    }
    let q = window as int / SIZE_512G as int;
    lemma_fundamental_div_mod(window as int, SIZE_512G as int);
    assert(window as int == (q * ENTRIES as int) * (REGION_BYTES as int)) by (nonlinear_arith)
        requires
            window as int == SIZE_512G as int * q,
            SIZE_512G as int == (ENTRIES as int) * (REGION_BYTES as int),
    ;
    lemma_mod_multiples_basic(q * ENTRIES as int, REGION_BYTES as int);
    assert(LOWER_HALF_END <= usize::MAX as u64);
}

/// Concatenating two accepted step sequences is accepted, and vice versa.
pub proof fn lemma_acall_ok_append(s1: Seq<AcallStep>, s2: Seq<AcallStep>)
    ensures
        acall_ok(s1 + s2) <==> (acall_ok(s1) && acall_ok(s2)),
{
    let s = s1 + s2;
    if acall_ok(s1) && acall_ok(s2) {
        assert forall|k: int| 0 <= k < s.len() implies (#[trigger] s[k]).out.status == STATUS_OK by {
            if k < s1.len() {
                assert(s[k] == s1[k]);
            } else {
                assert(s[k] == s2[k - s1.len()]);
            }
        }
    }
    if acall_ok(s) {
        assert forall|k: int| 0 <= k < s1.len() implies (#[trigger] s1[k]).out.status == STATUS_OK by {
            assert(s1[k] == s[k]);
        }
        assert forall|k: int| 0 <= k < s2.len() implies (#[trigger] s2[k]).out.status == STATUS_OK by {
            assert(s2[k] == s[s1.len() + k]);
        }
    }
}

/// Appending a sequence ending in a refused step after an accepted prefix ends in that same refused
/// step, with every earlier step accepted.
pub proof fn lemma_acall_refused_after_ok(s1: Seq<AcallStep>, s2: Seq<AcallStep>)
    requires
        acall_ok(s1),
        s2.len() > 0,
        acall_ok(s2.drop_last()),
        s2.last().out.status == STATUS_REFUSED,
    ensures
        (s1 + s2).len() > 0,
        acall_ok((s1 + s2).drop_last()),
        (s1 + s2).last() == s2.last(),
        !acall_ok(s1 + s2),
{
    let s = s1 + s2;
    assert(s.last() == s2.last());
    assert(s.drop_last() =~= s1 + s2.drop_last());
    lemma_acall_ok_append(s1, s2.drop_last());
    assert(s[s.len() - 1] == s2.last());
    assert(STATUS_REFUSED != STATUS_OK);
}

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
/// `slot` of the table at `root` holds a capability, it is a writable one-page frame whose block no other table
/// holds a capability of, counted at most by that capability and the entry at `at`, or by the capability
/// alone when there is no `at`, and the entry at `at`, while there is one, maps that frame's page.
pub open spec fn frame_held(k: CapKernel, root: usize, f: (usize, Option<usize>)) -> bool {
    let v = k.table_view(root);
    let m = space_mapping(tree_of(&k.table_pages, &k.spaces), root);
    &&& f.1 is Some ==> names_entry(f.1->0 as u64, 1)
    &&& v.contains_key(f.0) ==> {
        &&& v[f.0].kind is Frame
        &&& v[f.0].order == 0
        &&& v[f.0].rights & right_bit(Right::Write) != 0
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
/// process is its own: the process stays sealed and recorded, and every frame it holds stays held. The
/// rely is the only premise relating the two states.
pub proof fn lemma_frames_rely(k1: CapKernel, k2: CapKernel, root: usize, frames: Map<int, (usize, Option<usize>)>)
    requires
        k2.wf(),
        CapKernel::rely(k1, k2, root),
        k1.sealed(root),
        k1.processes.records@.contains_key(root),
        frames_held(k1, root, frames),
    ensures
        k2.sealed(root),
        k2.processes.records@.contains_key(root),
        frames_held(k2, root, frames),
{
    let a = space_mapping(tree_of(&k1.table_pages, &k1.spaces), root);
    let b = space_mapping(tree_of(&k2.table_pages, &k2.spaces), root);
    assert forall|p: SpacePath| #[trigger] b.contains_key(p) implies a.contains_key(p) && b[p] == a[p] by {}
    lemma_frames_shrunk(k1, k2, root, frames);
}

/// The slot that names a sealed process's own space still does across a step another caller takes, as
/// `CapKernel::rely` allows it: it is gone or holds what it held.
pub proof fn lemma_space_rely(k1: CapKernel, k2: CapKernel, root: usize, space: u64)
    requires
        CapKernel::rely(k1, k2, root),
        k1.sealed(root),
        names_space(k1, root, space),
    ensures
        names_space(k2, root, space),
{
    if k2.table_view(root).contains_key(space as usize) {
        assert(same_cap(k2.table_view(root)[space as usize], k1.table_view(root)[space as usize]));
    }
}

/// What a source knows of its process and its frames at the state its last call returned holds at the
/// state the next call entered from, which the step says the rely relates to it: the call's contract
/// starts from there.
pub proof fn lemma_entry_held(pre: Caller, post: Caller, frames: Map<int, (usize, Option<usize>)>)
    requires
        own_process(pre),
        frames_held(pre.kernel(), pre.root(), frames),
        post.root() == pre.root(),
        post.entry().wf(),
        CapKernel::rely(pre.kernel(), post.entry(), pre.root()),
    ensures
        post.entry().sealed(pre.root()),
        post.entry().processes.records@.contains_key(pre.root()),
        frames_held(post.entry(), pre.root(), frames),
        forall|space: u64| #[trigger] names_own_space(pre, space) ==> names_space(post.entry(), pre.root(), space),
{
    lemma_frames_rely(pre.kernel(), post.entry(), pre.root(), frames);
    assert forall|space: u64| #[trigger] names_own_space(pre, space) implies names_space(post.entry(), pre.root(), space) by {
        lemma_space_rely(pre.kernel(), post.entry(), pre.root(), space);
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
    assert(7u32 & 2u32 != 0) by (bit_vector);
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
pub const PAGE_LEVEL: u64 = 1;

/// The write right's bit, as inspect returns rights.
const RIGHT_WRITE: u64 = 2;

/// Retypes the free page at physical `base`, inside the untyped at `untyped`, as a frame whose
/// capability goes in the slot `destination`. Whether the kernel accepted, and the step it took. No
/// frame of `frames` names `destination`; each is kept, and the new frame, mapped nowhere, is held under
/// `key` once the kernel accepted.
pub(crate) fn retype_frame(
    caller: &mut Tracked<Caller>,
    untyped: u64,
    base: u64,
    destination: u64,
    frames: Ghost<Map<int, (usize, Option<usize>)>>,
    key: Ghost<int>,
) -> (r: (bool, Ghost<AcallStep>))
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
        r.0 ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.insert(key@, (destination as usize, None))),
        !r.0 ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@),
        acall_steps(old(caller)@, final(caller)@, seq![r.1@]),
        r.1@.call == (AcallCall::Retype { untyped, kind: RETYPE_FRAME, base, word: destination, level: 0 }),
        r.0 <==> r.1@.out.status == STATUS_OK,
        !r.0 ==> r.1@.out.status == STATUS_REFUSED,
    no_unwind
{
    let ghost pre = caller@;
    let out = memory::retype(caller, untyped, RETYPE_FRAME, base, destination, 0);
    let ghost step = AcallStep {
        pre: caller@.entry(),
        post: caller@.kernel(),
        root: pre.root(),
        call: AcallCall::Retype { untyped, kind: RETYPE_FRAME, base, word: destination, level: 0 },
        out,
    };
    proof {
        let root = pre.root();
        let e = caller@.entry();
        lemma_entry_held(pre, caller@, frames@);
        // The destination comes to hold a frame, which writes no space.
        assert forall|space: u64| #[trigger] names_own_space(pre, space) implies names_own_space(caller@, space) by {
            assert(names_space(e, root, space));
        }
        if out.status == STATUS_OK {
            let parent = e.tables.node_of(root, untyped as usize);
            lemma_frames_retyped(e, caller@.kernel(), root, frames@, key@, destination as usize, base as usize, parent);
        } else {
            lemma_frames_same(e, caller@.kernel(), root, frames@);
        }
        assert(step.valid()) by {
            reveal(AcallStep::valid);
        }
        lemma_acall_steps_one(pre, caller@, step);
    }
    (out.status == STATUS_OK, Ghost(step))
}

/// Retypes the free order-3 block at physical `base`, inside the untyped at `untyped`, as an unlinked
/// table page of `level`. Whether the kernel accepted, and the step it took.
/// Every frame of `frames` is kept.
pub(crate) fn retype_table_page(
    caller: &mut Tracked<Caller>,
    untyped: u64,
    base: u64,
    level: u64,
    frames: Ghost<Map<int, (usize, Option<usize>)>>,
) -> (r: (bool, Ghost<AcallStep>))
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
        acall_steps(old(caller)@, final(caller)@, seq![r.1@]),
        r.1@.call == (AcallCall::Retype { untyped, kind: RETYPE_TABLE_PAGE, base, word: 0, level }),
        r.0 <==> r.1@.out.status == STATUS_OK,
        !r.0 ==> r.1@.out.status == STATUS_REFUSED,
    no_unwind
{
    let ghost pre = caller@;
    let out = memory::retype(caller, untyped, RETYPE_TABLE_PAGE, base, 0, level);
    let ghost step = AcallStep {
        pre: caller@.entry(),
        post: caller@.kernel(),
        root: pre.root(),
        call: AcallCall::Retype { untyped, kind: RETYPE_TABLE_PAGE, base, word: 0, level },
        out,
    };
    proof {
        let root = pre.root();
        let e = caller@.entry();
        lemma_entry_held(pre, caller@, frames@);
        assert forall|space: u64| #[trigger] names_own_space(pre, space) implies names_own_space(caller@, space) by {
            assert(names_space(e, root, space));
        }
        if out.status == STATUS_OK {
            lemma_frames_kept(e, caller@.kernel(), root, frames@);
        } else {
            lemma_frames_same(e, caller@.kernel(), root, frames@);
        }
        assert(step.valid()) by {
            reveal(AcallStep::valid);
        }
        lemma_acall_steps_one(pre, caller@, step);
    }
    (out.status == STATUS_OK, Ghost(step))
}

/// Links the unlinked table page at physical `table`, inside the untyped at `untyped`, into the entry
/// at `level` that `address` names in the space at `space`. Whether the kernel accepted, and the step
/// it took. Every frame of `frames` is kept.
pub(crate) fn link(
    caller: &mut Tracked<Caller>,
    space: u64,
    address: usize,
    level: u64,
    untyped: u64,
    table: u64,
    frames: Ghost<Map<int, (usize, Option<usize>)>>,
) -> (r: (bool, Ghost<AcallStep>))
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
        acall_steps(old(caller)@, final(caller)@, seq![r.1@]),
        r.1@.call == (AcallCall::Link { slot: space, va: address as u64, level, from: untyped, child: table }),
        r.0 <==> r.1@.out.status == STATUS_OK,
        !r.0 ==> r.1@.out.status == STATUS_REFUSED,
    no_unwind
{
    let ghost pre = caller@;
    let out = memory::link(caller, space, address as u64, level, untyped, table);
    let ghost step = AcallStep {
        pre: caller@.entry(),
        post: caller@.kernel(),
        root: pre.root(),
        call: AcallCall::Link { slot: space, va: address as u64, level, from: untyped, child: table },
        out,
    };
    proof {
        let root = pre.root();
        let e = caller@.entry();
        lemma_entry_held(pre, caller@, frames@);
        assert forall|s: u64| #[trigger] names_own_space(pre, s) implies names_own_space(caller@, s) by {
            assert(names_space(e, root, s));
        }
        assert(space_mapping(tree_of(&caller@.kernel().table_pages, &caller@.kernel().spaces), root)
            == space_mapping(tree_of(&e.table_pages, &e.spaces), root));
        lemma_frames_same(e, caller@.kernel(), root, frames@);
        assert(step.valid()) by {
            reveal(AcallStep::valid);
        }
        lemma_acall_steps_one(pre, caller@, step);
    }
    (out.status == STATUS_OK, Ghost(step))
}

/// Maps the frame whose capability is at `frame`, which the source holds under `key` of `frames`,
/// mapped nowhere, at the page `address` in the space at `space`: on success the permission to the
/// page's bytes, with `provenance`, and the frame held mapped there; otherwise every frame kept. The frame is
/// inspected first and mapped only with the write right, so the page is one the hardware lets the
/// caller write; a slot no inspect of the caller's own table names is refused here, and a frame the
/// source holds has the write right. Also returns the steps it took: the inspect, and the map when the
/// inspect was accepted. The slot at `space` names the caller's own space, the one its thread runs in,
/// and no other frame of `frames` is at `address`. `live` holds every address of the window whose
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
) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        old(caller)@.wf(),
        own_process(old(caller)@),
        names_own_space(old(caller)@, space),
        !live@.contains(address),
        frame <= POSITION_INDEX_MASK,
        frames_held(old(caller)@.kernel(), old(caller)@.root(), frames@),
        frames@.contains_key(key@),
        frames@[key@] == (frame as usize, None::<usize>),
        forall|i: int| #[trigger] frames@.contains_key(i) && frames@[i].1 is Some ==> frames@[i].1->0 != address,
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        own_process(final(caller)@),
        keeps_own_space(old(caller)@, final(caller)@),
        match r.0 {
            Some(perm) => {
                &&& perm@.is_range(address as int, PAGE_BYTES as int)
                &&& perm@.provenance() == provenance@
                &&& frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.insert(key@, (frame as usize, Some(address))))
                &&& acall_ok(r.1@)
            },
            None => {
                &&& frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@)
                &&& r.1@.len() > 0
                &&& acall_ok(r.1@.drop_last())
                &&& r.1@.last().out.status == STATUS_REFUSED
            },
        },
        acall_steps(old(caller)@, final(caller)@, r.1@),
        1 <= r.1@.len() <= 2,
        r.0 is Some ==> r.1@.len() == 2,
        r.1@[0].out.status == STATUS_OK ==> r.1@.len() == 2,
        r.1@[0].call == (AcallCall::Inspect { at: frame }),
        r.1@.len() == 2 ==> r.1@[1].call == (AcallCall::Map { slot: space, va: address as u64, level: PAGE_LEVEL, from: frame, page: 0 }),
    no_unwind
{
    // The body relates three states; their invariants stay folded, and the lemmas open them.
    hide(CapKernel::wf);
    proof {
        lemma_own_position(frame);
    }
    let ghost first = caller@;
    let ghost root = first.root();
    let seen = memory::inspect(caller, frame);
    let ghost mid = caller@;
    let ghost entered = mid.entry();
    let ghost step1 = AcallStep {
        pre: entered,
        post: mid.kernel(),
        root,
        call: AcallCall::Inspect { at: frame },
        out: seen,
    };
    proof {
        lemma_entry_held(first, mid, frames@);
        assert(space_mapping(tree_of(&mid.kernel().table_pages, &mid.kernel().spaces), root)
            == space_mapping(tree_of(&entered.table_pages, &entered.spaces), root));
        lemma_frames_same(entered, mid.kernel(), root, frames@);
        assert forall|s: u64| #[trigger] names_own_space(first, s) implies names_own_space(mid, s) by {
            assert(names_space(entered, root, s));
        }
        assert(step1.valid()) by {
            reveal(AcallStep::valid);
        }
        lemma_acall_steps_one(first, mid, step1);
        if seen.status == STATUS_OK {
            // An accepted inspect names a slot of the caller's own table, and a frame the source holds
            // there has the write right.
            assert(entered.view_table_at(root, None) == Some(root));
            assert(entered.table_view(root).contains_key(frame as usize));
            assert(frame_held(entered, root, frames@[key@]));
            let rights = entered.table_view(root)[frame as usize].rights;
            assert(rights & right_bit(Right::Write) != 0);
            assert(seen.result_4 == rights as u64);
            assert((rights as u64) & 2u64 != 0) by (bit_vector)
                requires
                    rights & 2u32 != 0;
            assert(seen.result_4 & RIGHT_WRITE != 0);
        } else {
            assert(seen.status == STATUS_REFUSED);
            assert(seq![step1].drop_last() =~= Seq::<AcallStep>::empty());
        }
    }
    let ghost inspected = seq![step1];
    if seen.status != STATUS_OK || seen.result_4 & RIGHT_WRITE == 0 {
        return (None, Ghost(inspected));
    }
    let out = memory::map(caller, space, address as u64, PAGE_LEVEL, frame, 0);
    let ghost before = caller@.entry();
    let ghost step2 = AcallStep {
        pre: before,
        post: caller@.kernel(),
        root,
        call: AcallCall::Map { slot: space, va: address as u64, level: PAGE_LEVEL, from: frame, page: 0 },
        out,
    };
    let ghost steps = seq![step1, step2];
    proof {
        lemma_entry_held(mid, caller@, frames@);
        assert forall|s: u64| #[trigger] names_own_space(first, s) implies names_space(before, root, s) by {
            assert(names_own_space(mid, s));
        }
        if out.status == STATUS_OK {
            // The map was accepted, so the frame's slot was there at its entry, with the capability
            // the inspect read, the write right among its rights.
            assert(before.table_view(root).contains_key(frame as usize));
            assert(same_cap(before.table_view(root)[frame as usize], entered.table_view(root)[frame as usize]));
            let rights = before.table_view(root)[frame as usize].rights;
            assert(rights as u64 == seen.result_4);
            assert(rights & 2u32 != 0) by (bit_vector)
                requires
                    (rights as u64) & 2u64 != 0;
            lemma_frames_mapped(before, caller@.kernel(), root, space, address, frames@, key@, out);
        } else {
            lemma_frames_same(before, caller@.kernel(), root, frames@);
        }
        assert forall|s: u64| #[trigger] names_own_space(first, s) implies names_own_space(caller@, s) by {
            assert(names_space(before, root, s));
        }
        assert(step2.valid()) by {
            reveal(AcallStep::valid);
        }
        lemma_acall_steps_one(mid, caller@, step2);
        lemma_acall_steps_append(first, mid, caller@, seq![step1], seq![step2]);
        assert(seq![step1] + seq![step2] =~= steps);
        assert(steps[0] == step1 && steps[1] == step2 && steps.last() == step2);
        if out.status != STATUS_OK {
            assert(steps.drop_last() =~= seq![step1]);
        }
    }
    if out.status == STATUS_OK {
        (
            Some(mapped_permission(Ghost(before), Ghost(caller@.kernel()), Ghost(root), space, address, frame, Ghost(out), provenance, live)),
            Ghost(steps),
        )
    } else {
        (None, Ghost(steps))
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
/// bytes. Whether the kernel accepted, and the step it took. The frame the source holds under `key` of
/// `frames` is the one mapped there: once the kernel accepted it is held mapped nowhere, and otherwise
/// it is dropped.
pub(crate) fn unmap_page(
    caller: &mut Tracked<Caller>,
    space: u64,
    address: usize,
    perm: Tracked<PointsToRaw>,
    frames: Ghost<Map<int, (usize, Option<usize>)>>,
    key: Ghost<int>,
) -> (r: (bool, Ghost<AcallStep>))
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
        r.0 ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.insert(key@, (frames@[key@].0, None))),
        !r.0 ==> frames_held(final(caller)@.kernel(), final(caller)@.root(), frames@.remove(key@)),
        acall_steps(old(caller)@, final(caller)@, seq![r.1@]),
        r.1@.call == (AcallCall::Unmap { slot: space, va: address as u64, level: PAGE_LEVEL }),
        r.0 <==> r.1@.out.status == STATUS_OK,
        !r.0 ==> r.1@.out.status == STATUS_REFUSED,
    no_unwind
{
    let ghost pre = caller@;
    // The caller gave up the permission to every byte of the page, so nothing it uses is there.
    let out = memory::unmap(caller, space, address as u64, PAGE_LEVEL);
    let ghost step = AcallStep {
        pre: caller@.entry(),
        post: caller@.kernel(),
        root: pre.root(),
        call: AcallCall::Unmap { slot: space, va: address as u64, level: PAGE_LEVEL },
        out,
    };
    proof {
        let root = pre.root();
        let e = caller@.entry();
        lemma_entry_held(pre, caller@, frames@);
        assert forall|s: u64| #[trigger] names_own_space(pre, s) implies names_own_space(caller@, s) by {
            assert(names_space(e, root, s));
            assert(caller@.kernel().table_view(root) == e.table_view(root));
        }
        if out.status == STATUS_OK {
            lemma_frames_unmapped(e, caller@.kernel(), root, space, address, frames@, key@, out);
        } else {
            lemma_frames_same(e, caller@.kernel(), root, frames@);
            lemma_frames_drop(caller@.kernel(), root, frames@, key@);
        }
        assert(step.valid()) by {
            reveal(AcallStep::valid);
        }
        lemma_acall_steps_one(pre, caller@, step);
    }
    (out.status == STATUS_OK, Ghost(step))
}

/// Whether `token`'s kernel state has room for at least `n` flush-epoch increments without reaching
/// `usize::MAX`.
pub open spec fn flush_room(token: Caller, n: nat) -> bool {
    token.kernel().flush_epoch as int + n as int <= usize::MAX as int
}

/// Whether some page `0 <= i < pages` in `(state, owner)` is mapped or parked at `va`.
pub(crate) open spec fn window_entry_occupied(
    pages: usize,
    state: Seq<u8>,
    owner: Seq<usize>,
    va: usize,
) -> bool {
    exists|i: int| 0 <= i < pages && occupied(#[trigger] state[i]) && owner[i] == va
}

/// Inductive kernel-state readiness for an eager source whose configuration is
/// `(space, untyped, memory, pages, slots, window)` and whose record holds `(top, middle, tabled, state, owner)`.
#[verifier::opaque]
pub(crate) open spec fn source_state_ready(
    k: CapKernel,
    root: usize,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
) -> bool {
    let v = k.table_view(root);
    let tree = tree_of(&k.table_pages, &k.spaces);
    let l4 = address_path(window as u64).l4;
    &&& k.wf()
    &&& k.processes.records@.contains_key(root)
    &&& !k.processes.records@[root].value().dead
    &&& !k.blocks.pages@[(root / PAGE_SZ) as int].dead
    &&& k.spaces.roots@.contains_key(root)
    &&& k.spaces.records@[root].value().kind == SpaceKind::Process
    &&& pages <= MAX_PAGES
    &&& state.len() == MAX_PAGES
    &&& owner.len() == MAX_PAGES
    &&& tabled.len() == WINDOW_BLOCKS
    &&& slots < TABLE_INDICES as u64
    &&& slots as int % LEAF_INDICES as int != 0
    &&& pages > 0 ==> frame_slot(slots as int, pages - 1) < TABLE_INDICES
    &&& memory as int % (TABLE_PAGES * PAGE_BYTES) as int == 0
    &&& memory + pages * PAGE_BYTES <= u64::MAX
    &&& window != 0
    &&& window as int % SIZE_512G as int == 0
    &&& window + WINDOW_BYTES <= LOWER_HALF_END as usize
    &&& v.contains_key(space as usize)
    &&& view_writes_space(v[space as usize])
    &&& v[space as usize].base == root
    &&& v.contains_key(untyped as usize)
    &&& v[untyped as usize].kind is Untyped
    &&& v[untyped as usize].rights & right_bit(Right::Retype) != 0
    &&& v[untyped as usize].base <= memory as usize
    &&& memory as int + pages as int * PAGE_SZ as int
        <= v[untyped as usize].base as int + block_bytes(v[untyped as usize].order)
    &&& k.list.nodes@[k.tables.node_of(root, untyped as usize) as int].depth + 1 < MAX_DEPTH
    &&& forall|i: int| 0 <= i < pages && #[trigger] state[i] == FREE ==> {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k.blocks.tracks(p)
        &&& k.blocks.pages@[p].kind is Free
        &&& !k.blocks.covered(p)
    }
    &&& forall|i: int| 0 <= i < pages && (#[trigger] state[i] == HELD || occupied(state[i])) ==> {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& v.contains_key(s)
        &&& v[s] == frame_view(untyped_page(memory, i) as usize, 0, k.tables.node_of(root, untyped as usize))
        &&& k.list.nodes@[k.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& k.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&k.blocks, p) == BlockRef::Small(p)
        &&& k.blocks.pages@[p as int].kind is Base
        &&& k.blocks.pages@[p as int].object is Frame
        &&& frame_refs(k, p) == if occupied(state[i]) { 2usize } else { 1usize }
        &&& !k.blocks.pages@[p as int].dead
    }
    &&& forall|i: int| 0 <= i < pages && occupied(#[trigger] state[i]) ==> {
        &&& window <= owner[i]
        &&& owner[i] < window + WINDOW_BYTES
        &&& owner[i] as int % PAGE_BYTES as int == 0
        &&& top
        &&& middle
        &&& tabled[((owner[i] - window) as int / BLOCK_BYTES as int)]
    }
    &&& forall|i: int, j: int|
        0 <= i < pages && 0 <= j < pages && i != j
            && occupied(#[trigger] state[i]) && occupied(#[trigger] state[j])
            ==> owner[i] != owner[j]
    &&& (!top ==> !middle && forall|b: int| 0 <= b < WINDOW_BLOCKS ==> !#[trigger] tabled[b])
    &&& (!middle ==> forall|b: int| 0 <= b < WINDOW_BLOCKS ==> !#[trigger] tabled[b])
    &&& (!top ==> tree.entry(root, l4).is_empty())
    &&& (top ==> {
        let t3 = step(tree, root, l4)->0;
        &&& step(tree, root, l4) is Some
        &&& (!middle ==> tree.entry(t3, 0).is_empty())
        &&& (middle ==> {
            let t2 = step(tree, t3, 0)->0;
            &&& step(tree, t3, 0) is Some
            &&& forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] tabled[b] ==> {
                &&& step(tree, t2, b as usize) is Some
                &&& forall|e: usize| #![trigger tree.entry(step(tree, t2, b as usize)->0, e)] e < ENTRIES ==> {
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    &&& window_entry_occupied(pages, state, owner, va)
                        ==> tree.entry(step(tree, t2, b as usize)->0, e).perm.present
                    &&& !window_entry_occupied(pages, state, owner, va)
                        ==> tree.entry(step(tree, t2, b as usize)->0, e).is_empty()
                }
            }
            &&& forall|b: int| 0 <= b < WINDOW_BLOCKS && !#[trigger] tabled[b]
                ==> tree.entry(t2, b as usize).is_empty()
        })
    })
}

/// Path indices and `names_entry` facts for a 512G-aligned non-zero lower-half window and its blocks.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_window_path(window: usize)
    requires
        window != 0,
        window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
    ensures
        names_entry(window as u64, 4),
        names_entry(window as u64, 3),
        KERNEL_MEM_END_L4INDEX <= address_path(window as u64).l4 < ENTRIES,
        !holds_kernel(SpaceKind::Process, address_path(window as u64).l4),
        address_path(window as u64).l3 == 0,
        forall|b: int| 0 <= b < WINDOW_BLOCKS ==> {
            let vb = (#[trigger] window_block(window, b)) as u64;
            &&& window_block(window, b) >= 0
            &&& window_block(window, b) < LOWER_HALF_END as int
            &&& names_entry(vb, 2)
            &&& address_path(vb).l4 == address_path(window as u64).l4
            &&& address_path(vb).l3 == 0
            &&& address_path(vb).l2 == b as usize
        },
{
    use vstd::arithmetic::div_mod::*;
    let e = ENTRIES as int;
    assert(PAGE_BYTES == PAGE_SZ);
    assert(BLOCK_BYTES == SIZE_2M);
    assert(SIZE_2M == PAGE_SZ * ENTRIES);
    assert(SIZE_1G == SIZE_2M * ENTRIES);
    assert(SIZE_512G == SIZE_1G * ENTRIES);
    assert(LOWER_HALF_END as int == SIZE_512G as int * (e / 2));
    assert(WINDOW_BLOCKS == 4);
    assert(WINDOW_BYTES == 4 * BLOCK_BYTES);
    assert(KERNEL_MEM_END_L4INDEX == 1);

    let q = window as int / SIZE_512G as int;
    lemma_fundamental_div_mod(window as int, SIZE_512G as int);
    assert(window as int == SIZE_512G as int * q);
    assert(q >= 1) by (nonlinear_arith)
        requires
            window > 0,
            window as int == SIZE_512G as int * q,
            SIZE_512G > 0,
    ;
    assert(q < e / 2) by (nonlinear_arith)
        requires
            window + WINDOW_BYTES <= LOWER_HALF_END as usize,
            LOWER_HALF_END as int == SIZE_512G as int * (e / 2),
            window as int == SIZE_512G as int * q,
            WINDOW_BYTES > 0,
            SIZE_512G > 0,
    ;
    lemma_small_mod(q as nat, e as nat);
    assert((window as u64 / SIZE_512G as u64) as int == q);
    assert(address_path(window as u64).l4 == q as usize);

    assert(window as int == SIZE_1G as int * (e * q)) by (nonlinear_arith)
        requires
            window as int == SIZE_512G as int * q,
            SIZE_512G == SIZE_1G * ENTRIES,
            e == ENTRIES as int,
    ;
    lemma_mod_multiples_basic(e * q, SIZE_1G as int);
    lemma_div_by_multiple(e * q, SIZE_1G as int);
    lemma_mod_multiples_basic(q, e);
    assert((e * q) == q * e) by (nonlinear_arith);
    assert(address_path(window as u64).l3 == 0);
    assert((window as u64) % (SIZE_512G as u64) == 0);
    assert((window as u64) % (SIZE_1G as u64) == 0);

    assert forall|b: int| 0 <= b < WINDOW_BLOCKS implies {
        let vb = (#[trigger] window_block(window, b)) as u64;
        &&& window_block(window, b) >= 0
        &&& window_block(window, b) < LOWER_HALF_END as int
        &&& names_entry(vb, 2)
        &&& address_path(vb).l4 == address_path(window as u64).l4
        &&& address_path(vb).l3 == 0
        &&& address_path(vb).l2 == b as usize
    } by {
        let wbi = window_block(window, b);
        assert(0 <= b * (SIZE_2M as int) < 4 * (SIZE_2M as int)) by (nonlinear_arith)
            requires
                0 <= b < 4,
                SIZE_2M > 0,
        ;
        assert(4 * (SIZE_2M as int) < SIZE_1G as int);
        assert((SIZE_1G as int) < (SIZE_512G as int));
        assert(wbi < window as int + WINDOW_BYTES as int) by (nonlinear_arith)
            requires
                wbi == window as int + b * (BLOCK_BYTES as int),
                BLOCK_BYTES == SIZE_2M,
                WINDOW_BYTES == 4 * BLOCK_BYTES,
                b < 4,
                SIZE_2M > 0,
        ;
        let vb = wbi as u64;
        assert(vb as int == wbi);
        assert(wbi == (SIZE_512G as int) * q + b * (SIZE_2M as int)) by (nonlinear_arith)
            requires
                wbi == window as int + b * (BLOCK_BYTES as int),
                BLOCK_BYTES == SIZE_2M,
                window as int == (SIZE_512G as int) * q,
        ;
        assert((SIZE_512G as int) * q == q * (SIZE_512G as int)) by (nonlinear_arith);
        lemma_div_multiples_vanish_fancy(q, b * (SIZE_2M as int), SIZE_512G as int);
        assert((vb / SIZE_512G as u64) as int == q);
        assert(address_path(vb).l4 == q as usize);

        assert(wbi == (e * q) * (SIZE_1G as int) + b * (SIZE_2M as int)) by (nonlinear_arith)
            requires
                wbi == window as int + b * (BLOCK_BYTES as int),
                BLOCK_BYTES == SIZE_2M,
                window as int == SIZE_1G as int * (e * q),
        ;
        lemma_div_multiples_vanish_fancy(e * q, b * (SIZE_2M as int), SIZE_1G as int);
        assert((vb / SIZE_1G as u64) as int == e * q);
        assert(e * q == q * e) by (nonlinear_arith);
        lemma_mod_multiples_basic(q, e);
        assert(address_path(vb).l3 == 0);

        let k2 = e * (e * q) + b;
        assert(wbi == k2 * (SIZE_2M as int)) by (nonlinear_arith)
            requires
                wbi == (e * q) * (SIZE_1G as int) + b * (SIZE_2M as int),
                SIZE_1G == SIZE_2M * ENTRIES,
                e == ENTRIES as int,
                k2 == e * (e * q) + b,
        ;
        lemma_mod_multiples_basic(k2, SIZE_2M as int);
        lemma_div_by_multiple(k2, SIZE_2M as int);
        assert((vb % SIZE_2M as u64) == 0);
        assert((vb / SIZE_2M as u64) as int == k2);
        assert(k2 == (e * q) * e + b) by (nonlinear_arith)
            requires k2 == e * (e * q) + b;
        lemma_mod_multiples_vanish(e * q, b, e);
        lemma_small_mod(b as nat, e as nat);
        assert(address_path(vb).l2 == b as usize);
    }
}

/// Path indices and block/entry decomposition for a page-aligned address `va` inside `window`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_window_va_path(window: usize, va: usize)
    requires
        window != 0,
        window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        window <= va < window + WINDOW_BYTES,
        va as int % PAGE_BYTES as int == 0,
    ensures
        ({
            let b = (va - window) as int / BLOCK_BYTES as int;
            let e = (va as int - window_block(window, b)) / PAGE_BYTES as int;
            &&& 0 <= b < WINDOW_BLOCKS
            &&& 0 <= e < ENTRIES
            &&& names_entry(va as u64, 1)
            &&& va as int == window_block(window, b) + e * (PAGE_BYTES as int)
            &&& address_path(va as u64) == (SpacePath {
                l4: address_path(window as u64).l4,
                l3: 0,
                l2: b as usize,
                l1: e as usize,
            })
        }),
{
    use vstd::arithmetic::div_mod::*;
    lemma_window_path(window);
    let en = ENTRIES as int;
    assert(PAGE_BYTES == PAGE_SZ);
    assert(BLOCK_BYTES == SIZE_2M);
    assert(SIZE_2M == PAGE_SZ * ENTRIES);
    assert(SIZE_1G == SIZE_2M * ENTRIES);
    assert(SIZE_512G == SIZE_1G * ENTRIES);
    assert(WINDOW_BLOCKS == 4);
    assert(WINDOW_BYTES == 4 * BLOCK_BYTES);

    let off = (va - window) as int;
    lemma_div_pos_is_pos(off, SIZE_2M as int);
    lemma_multiply_divide_lt(off, SIZE_2M as int, 4);
    lemma_fundamental_div_mod(off, SIZE_2M as int);
    lemma_mod_bound(off, SIZE_2M as int);
    let b = off / (SIZE_2M as int);
    let rem = off % (SIZE_2M as int);
    assert(0 <= b < 4);
    assert(va as int == window_block(window, b) + rem) by (nonlinear_arith)
        requires
            off == va as int - window as int,
            off == (SIZE_2M as int) * b + rem,
            window_block(window, b) == window as int + b * (BLOCK_BYTES as int),
            BLOCK_BYTES == SIZE_2M,
    ;

    let q = window as int / SIZE_512G as int;
    lemma_fundamental_div_mod(window as int, SIZE_512G as int);
    let qw = va as int / PAGE_SZ as int;
    lemma_fundamental_div_mod(va as int, PAGE_SZ as int);
    assert(va as int == (PAGE_SZ as int) * qw);

    let wb_pages = en * (en * (en * q)) + en * b;
    assert(window_block(window, b) == (PAGE_SZ as int) * wb_pages) by (nonlinear_arith)
        requires
            window as int == (SIZE_512G as int) * q,
            window_block(window, b) == window as int + b * (BLOCK_BYTES as int),
            BLOCK_BYTES == SIZE_2M,
            SIZE_2M == PAGE_SZ * ENTRIES,
            SIZE_1G == SIZE_2M * ENTRIES,
            SIZE_512G == SIZE_1G * ENTRIES,
            en == ENTRIES as int,
            wb_pages == en * (en * (en * q)) + en * b,
    ;
    let e = qw - wb_pages;
    assert(rem == (PAGE_SZ as int) * e) by (nonlinear_arith)
        requires
            va as int == window_block(window, b) + rem,
            va as int == (PAGE_SZ as int) * qw,
            window_block(window, b) == (PAGE_SZ as int) * wb_pages,
            e == qw - wb_pages,
    ;
    assert(0 <= e < en) by (nonlinear_arith)
        requires
            0 <= rem < SIZE_2M as int,
            rem == (PAGE_SZ as int) * e,
            SIZE_2M == PAGE_SZ * ENTRIES,
            en == ENTRIES as int,
            PAGE_SZ > 0,
    ;
    assert(rem == e * (PAGE_SZ as int)) by (nonlinear_arith)
        requires rem == (PAGE_SZ as int) * e;
    lemma_div_by_multiple(e, PAGE_SZ as int);
    assert((va as int - window_block(window, b)) / (PAGE_BYTES as int) == e);
    assert((va as u64) % (PAGE_SZ as u64) == 0);
    assert(names_entry(va as u64, 1));

    lemma_path_page(va as u64);
    let p = address_path(va as u64);
    assert(p.l1 < ENTRIES && p.l2 < ENTRIES && p.l3 < ENTRIES && p.l4 < ENTRIES) by {
        lemma_mod_bound((va as u64 / PAGE_SZ as u64) as int, en);
        lemma_mod_bound((va as u64 / SIZE_2M as u64) as int, en);
        lemma_mod_bound((va as u64 / SIZE_1G as u64) as int, en);
        lemma_mod_bound((va as u64 / SIZE_512G as u64) as int, en);
    }
    let l4w = address_path(window as u64).l4 as int;
    assert(l4w == q);
    assert(qw == en * (en * (en * l4w + 0) + b) + e) by (nonlinear_arith)
        requires
            e == qw - wb_pages,
            wb_pages == en * (en * (en * q)) + en * b,
            l4w == q,
    ;
    assert(qw == en * (en * (en * (p.l4 as int) + (p.l3 as int)) + (p.l2 as int)) + (p.l1 as int)) by (nonlinear_arith)
        requires
            va as int == (PAGE_SZ as int) * qw,
            va as int == (PAGE_SZ as int) * (en * (en * (en * (p.l4 as int) + (p.l3 as int)) + (p.l2 as int)) + (p.l1 as int)),
            PAGE_SZ > 0,
    ;
    assert(p.l1 as int == e && p.l2 as int == b && p.l3 == 0 && p.l4 as int == l4w) by (nonlinear_arith)
        requires
            en == ENTRIES as int,
            0 <= e < en,
            0 <= b < 4,
            0 <= l4w < en,
            0 <= p.l1 < en,
            0 <= p.l2 < en,
            0 <= p.l3 < en,
            0 <= p.l4 < en,
            en * (en * (en * l4w + 0) + b) + e
                == en * (en * (en * (p.l4 as int) + (p.l3 as int)) + (p.l2 as int)) + (p.l1 as int),
    ;
}

/// Inverse of `lemma_window_va_path`: entry `e` of block `b` of `window` is a page-aligned address in `window`
/// with block `b`, entry `e`, and path `(l4, 0, b, e)`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_window_block_entry_va(window: usize, b: int, e: usize)
    requires
        window != 0,
        window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        0 <= b < WINDOW_BLOCKS,
        e < ENTRIES,
    ensures
        ({
            let va_int = window_block(window, b) + (e as int) * (PAGE_BYTES as int);
            let va = va_int as usize;
            &&& window <= va_int < window + WINDOW_BYTES
            &&& va as int == va_int
            &&& va as int % PAGE_BYTES as int == 0
            &&& (va - window) as int / BLOCK_BYTES as int == b
            &&& (va as int - window_block(window, b)) / PAGE_BYTES as int == e as int
            &&& address_path(va as u64) == (SpacePath {
                l4: address_path(window as u64).l4,
                l3: 0,
                l2: b as usize,
                l1: e,
            })
        }),
{
    use vstd::arithmetic::div_mod::*;
    lemma_window_path(window);
    assert(PAGE_BYTES == PAGE_SZ);
    assert(BLOCK_BYTES == SIZE_2M);
    assert(SIZE_2M == PAGE_SZ * ENTRIES);
    assert(WINDOW_BLOCKS == 4);
    assert(WINDOW_BYTES == 4 * BLOCK_BYTES);

    let va_int = window_block(window, b) + (e as int) * (PAGE_BYTES as int);
    assert(0 <= (e as int) * (PAGE_SZ as int) < SIZE_2M as int) by (nonlinear_arith)
        requires
            0 <= e < ENTRIES,
            SIZE_2M == PAGE_SZ * ENTRIES,
            PAGE_SZ > 0,
    ;
    assert(window as int <= va_int < window as int + WINDOW_BYTES as int) by (nonlinear_arith)
        requires
            va_int == window as int + b * (SIZE_2M as int) + (e as int) * (PAGE_SZ as int),
            0 <= b < 4,
            0 <= (e as int) * (PAGE_SZ as int) < SIZE_2M as int,
            WINDOW_BYTES == 4 * SIZE_2M,
            SIZE_2M > 0,
    ;
    let va = va_int as usize;
    assert(va as int == va_int);

    let wb = window_block(window, b) as u64;
    assert(names_entry(wb, 2));
    assert((wb as int) % (SIZE_2M as int) == 0);
    lemma_fundamental_div_mod(wb as int, SIZE_2M as int);
    let qb = (wb as int) / (SIZE_2M as int);
    assert(va_int == ((ENTRIES as int) * qb + (e as int)) * (PAGE_SZ as int)) by (nonlinear_arith)
        requires
            va_int == (wb as int) + (e as int) * (PAGE_SZ as int),
            wb as int == (SIZE_2M as int) * qb,
            SIZE_2M == PAGE_SZ * ENTRIES,
    ;
    lemma_mod_multiples_basic((ENTRIES as int) * qb + (e as int), PAGE_SZ as int);
    assert(va as int % PAGE_BYTES as int == 0);

    let off = (va - window) as int;
    assert(off == b * (SIZE_2M as int) + (e as int) * (PAGE_SZ as int));
    lemma_div_multiples_vanish_fancy(b, (e as int) * (PAGE_SZ as int), SIZE_2M as int);
    assert(off / (BLOCK_BYTES as int) == b);

    lemma_window_va_path(window, va);
}

/// `kernel_source_ready` on a fresh record `(top = false, middle = false, tabled = [false; 4], state = [FREE; ..])`
/// establishes `source_state_ready` and `flush_room(token, MAX_PAGES as nat)`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_fresh_source_state_ready(
    token: Caller,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
)
    requires
        source_ready(token, space, untyped, memory, pages, slots, window),
        state.len() == MAX_PAGES,
        owner.len() == MAX_PAGES,
        tabled.len() == WINDOW_BLOCKS,
        forall|b: int| 0 <= b < WINDOW_BLOCKS ==> !#[trigger] tabled[b],
        forall|i: int| 0 <= i < pages ==> #[trigger] state[i] == FREE,
    ensures
        source_state_ready(
            token.kernel(),
            token.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            false,
            false,
            tabled,
            state,
            owner,
        ),
        flush_room(token, MAX_PAGES as nat),
{
    reveal(source_state_ready);
    let k = token.kernel();
    let root = token.root();
    assert forall|i: int| 0 <= i < pages && #[trigger] state[i] == FREE implies {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k.blocks.tracks(p)
        &&& k.blocks.pages@[p].kind is Free
        &&& !k.blocks.covered(p)
    } by {
        let _ = frame_slot(slots as int, i);
        let _ = k.blocks.pages@[memory as int / PAGE_SZ as int + i];
    }
    assert forall|i: int| 0 <= i < pages implies {
        &&& !(#[trigger] state[i] == HELD || occupied(state[i]))
        &&& !occupied(state[i])
    } by {
        assert(state[i] == FREE);
    }
}

/// The capability at `space` naming the live caller's own space is not dead.
proof fn lemma_own_space_cap_live(k: CapKernel, root: usize, space: u64)
    requires
        k.wf(),
        k.processes.records@.contains_key(root),
        !k.processes.records@[root].value().dead,
        k.table_view(root).contains_key(space as usize),
        view_writes_space(k.table_view(root)[space as usize]),
        k.table_view(root)[space as usize].base == root,
    ensures
        !k.cap_dead(k.tables.node_of(root, space as usize)),
{
    k.lemma_table_view(root, space as usize);
}

/// Two distinct slot indices in `root` that both hold slots in `k` name distinct capability-list nodes.
proof fn lemma_distinct_slots_distinct_nodes(k: CapKernel, root: usize, i: usize, j: usize)
    requires
        k.wf(),
        k.tables.has_slot(&k.list, root, i),
        k.tables.has_slot(&k.list, root, j),
        i != j,
    ensures
        k.tables.node_of(root, i) != k.tables.node_of(root, j),
{
    k.lemma_slot(root, i);
    k.lemma_slot(root, j);
    if k.tables.node_of(root, i) == k.tables.node_of(root, j) {
        k.tables.lemma_entry(root, index_entry(i));
        k.tables.lemma_entry(root, index_entry(j));
        assert(index_entry(i) == index_entry(j));
        assert(index_slot(i) == index_slot(j));
        assert(i == 128 * (i / 128) + i % 128) by (nonlinear_arith);
        assert(j == 128 * (j / 128) + j % 128) by (nonlinear_arith);
    }
}

/// Physical address and page-alignment facts for page `idx` of a `TABLE_PAGES`-page-aligned untyped.
proof fn lemma_untyped_page_facts(k: CapKernel, memory: u64, pages: usize, idx: int)
    requires
        memory as int % (TABLE_PAGES * PAGE_BYTES) as int == 0,
        memory + pages * PAGE_BYTES <= u64::MAX,
        0 <= idx < pages,
        k.blocks.tracks(memory as int / PAGE_SZ as int + idx),
    ensures
        untyped_page(memory, idx) >= 0,
        untyped_page(memory, idx) < NODE_SPACE as int,
        (untyped_page(memory, idx) as usize) as int == untyped_page(memory, idx),
        ((untyped_page(memory, idx) as usize) as u64) as int == untyped_page(memory, idx),
        (untyped_page(memory, idx) as usize) % PAGE_SZ == 0,
        ((untyped_page(memory, idx) as usize) / PAGE_SZ) as int == memory as int / PAGE_SZ as int + idx,
        untyped_page(memory, idx) / PAGE_SZ as int == memory as int / PAGE_SZ as int + idx,
{
    use vstd::arithmetic::div_mod::*;
    assert(PAGE_BYTES == PAGE_SZ);
    assert(TABLE_PAGES == 8);
    let q8 = memory as int / (8 * PAGE_SZ as int);
    lemma_fundamental_div_mod(memory as int, 8 * PAGE_SZ as int);
    assert(memory as int == (8 * q8) * (PAGE_SZ as int)) by (nonlinear_arith)
        requires memory as int == (8 * PAGE_SZ as int) * q8;
    lemma_div_by_multiple(8 * q8, PAGE_SZ as int);
    let p = memory as int / PAGE_SZ as int + idx;
    assert(untyped_page(memory, idx) == p * (PAGE_SZ as int)) by (nonlinear_arith)
        requires
            untyped_page(memory, idx) == memory as int + idx * (PAGE_BYTES as int),
            PAGE_BYTES == PAGE_SZ,
            memory as int == (8 * q8) * (PAGE_SZ as int),
            memory as int / (PAGE_SZ as int) == 8 * q8,
            p == memory as int / (PAGE_SZ as int) + idx,
    ;
    assert((verified::define::NUM_PAGES as int) * (PAGE_SZ as int) <= NODE_SPACE as int);
    vstd::arithmetic::mul::lemma_mul_strict_inequality(p, verified::define::NUM_PAGES as int, PAGE_SZ as int);
    vstd::arithmetic::mul::lemma_mul_nonnegative(p, PAGE_SZ as int);
    assert(0 <= p * (PAGE_SZ as int) < NODE_SPACE as int);
    lemma_mod_multiples_basic(p, PAGE_SZ as int);
    lemma_div_by_multiple(p, PAGE_SZ as int);
}

/// Under `caller_alone` and `source_state_ready` with `state[idx] == FREE`, `retype_frame` succeeds and
/// preserves `source_state_ready` with `state.update(idx, HELD)`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ready_retype_frame(
    pre: Caller,
    post: Caller,
    step_out: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
    idx: usize,
)
    requires
        pre.wf(),
        post.wf(),
        post.root() == pre.root(),
        acall_steps(pre, post, seq![step_out]),
        caller_alone(pre, post),
        idx < pages,
        state[idx as int] == FREE,
        step_out.call == (AcallCall::Retype {
            untyped,
            kind: RETYPE_FRAME,
            base: untyped_page(memory, idx as int) as u64,
            word: frame_slot(slots as int, idx as int) as u64,
            level: 0,
        }),
        source_state_ready(
            pre.kernel(),
            pre.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state,
            owner,
        ),
    ensures
        step_out.out.status == STATUS_OK,
        post.kernel().flush_epoch == pre.kernel().flush_epoch,
        source_state_ready(
            post.kernel(),
            post.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state.update(idx as int, HELD),
            owner,
        ),
{
    reveal(source_state_ready);
    reveal(CapKernel::retype_frame_contract_fields);
    vstd::arithmetic::power2::lemma2_to64();
    lemma_acall_steps_alone(pre, post, seq![step_out]);
    assert(seq![step_out][0] == step_out);
    reveal(AcallStep::valid);
    assert(step_out.valid());
    let k0 = pre.kernel();
    let k1 = post.kernel();
    let root = pre.root();
    assert(step_out.pre == k0 && step_out.post == k1 && step_out.root == root);

    lemma_untyped_page_facts(k0, memory, pages, idx as int);
    let base = untyped_page(memory, idx as int) as usize;
    let p_idx = (base / PAGE_SZ) as int;
    lemma_frame_slot(slots as int, idx as int, (pages - 1) as int);
    let to_int = frame_slot(slots as int, idx as int);
    let to = to_int as usize;
    assert((to_int as u64) as usize == to);

    let v0 = k0.table_view(root);
    assert(block_bytes(0) == PAGE_SZ as int);
    assert(order_pages(0) == 1);
    assert(v0[untyped as usize].base <= base) by {
        assert(idx as int * (PAGE_BYTES as int) >= 0) by (nonlinear_arith)
            requires idx >= 0, PAGE_BYTES > 0;
    }
    assert(base as int + block_bytes(0) <= v0[untyped as usize].base as int + block_bytes(v0[untyped as usize].order)) by {
        assert((idx as int + 1) * (PAGE_SZ as int) <= (pages as int) * (PAGE_SZ as int)) by (nonlinear_arith)
            requires (idx as int) + 1 <= pages as int, PAGE_SZ > 0;
    }
    assert(view_retypes(v0[untyped as usize], base, 0));
    assert(k0.retype_under_allowed(root, untyped as usize, base, 0));
    assert(k0.empty_slot(root, to));
    assert(k0.blocks.tracks_addr_run(base, 1));
    assert forall|m: int| 0 <= m < order_pages(0) implies #[trigger] k0.blocks.pages@[p_idx + m].kind is Free by {
        assert(m == 0);
        assert(state[idx as int] == FREE);
    }
    assert(k0.small_block_free(base, 0));
    assert(k0.retype_allowed(root, RETYPE_FRAME, untyped as usize, base, to as u64, 0));
    assert(step_out.out.status == STATUS_OK);

    let parent = k0.tables.node_of(root, untyped as usize);
    let state1 = state.update(idx as int, HELD);
    let v1 = k1.table_view(root);
    assert(v1 == v0.insert(to, frame_view(base, 0, parent)));

    // `space` and `untyped` slots are unchanged because `to` was empty in `v0`.
    assert(!v0.contains_key(to)) by {
        k0.lemma_table_view(root, to);
    }
    assert(space as usize != to && untyped as usize != to);
    assert(k1.tables.node_of(root, untyped as usize) == parent);
    k0.lemma_table_view(root, untyped as usize);
    assert(k0.tables.is_cap(&k0.list, parent));
    assert(k1.list.nodes@[parent as int].depth == k0.list.nodes@[parent as int].depth);

    // `root`'s block was `Base`, not `Free`, so `kept_but_run` leaves it live.
    k0.lemma_table_base(root);
    assert((root / PAGE_SZ) as int != p_idx);
    assert(k1.blocks.pages@[(root / PAGE_SZ) as int] == k0.blocks.pages@[(root / PAGE_SZ) as int]);

    assert forall|i: int| 0 <= i < pages && #[trigger] state1[i] == FREE implies {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k1.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k1.blocks.tracks(p)
        &&& k1.blocks.pages@[p].kind is Free
        &&& !k1.blocks.covered(p)
    } by {
        assert(i != idx as int);
        assert(state[i] == FREE);
        let p = memory as int / PAGE_SZ as int + i;
        assert(p != p_idx);
        assert(k1.blocks.pages@[p] == k0.blocks.pages@[p]);
        if i < idx as int {
            lemma_frame_slot(slots as int, i, idx as int);
        } else {
            lemma_frame_slot(slots as int, idx as int, i);
        }
        lemma_frame_slot(slots as int, i, (pages - 1) as int);
        let si = frame_slot(slots as int, i) as usize;
        assert(si != to);
        assert(k0.tables.has_slot(&k0.list, root, si));
        lemma_distinct_slots_distinct_nodes(k0, root, si, to);
        assert(k1.empty_slot(root, si));
    }

    assert forall|i: int| 0 <= i < pages && (#[trigger] state1[i] == HELD || occupied(state1[i])) implies {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& v1.contains_key(s)
        &&& v1[s] == frame_view(untyped_page(memory, i) as usize, 0, k1.tables.node_of(root, untyped as usize))
        &&& k1.list.nodes@[k1.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& k1.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&k1.blocks, p) == BlockRef::Small(p)
        &&& k1.blocks.pages@[p as int].kind is Base
        &&& k1.blocks.pages@[p as int].object is Frame
        &&& frame_refs(k1, p) == if occupied(state1[i]) { 2usize } else { 1usize }
        &&& !k1.blocks.pages@[p as int].dead
    } by {
        lemma_frame_slot(slots as int, i, (pages - 1) as int);
        let s = frame_slot(slots as int, i) as usize;
        if i == idx as int {
            assert(s == to);
            assert(!occupied(state1[i]));
            assert(v1[to] == frame_view(base, 0, parent));
            let br = block_ref(&k1.blocks, base / PAGE_SZ);
            assert(br == BlockRef::Small(base / PAGE_SZ));
            assert(block_typed(&k1.blocks, br));
            assert(!block_dead(&k1.blocks, br));
            assert(block_refs(&k1.blocks, br) == 1);
            assert(k1.blocks.pages@[(base / PAGE_SZ) as int].kind is Base);
            assert(k1.blocks.pages@[(base / PAGE_SZ) as int].object is Frame);
            assert(k1.tables.node_of(root, to) == k0.tables.node_of(root, to));
        } else {
            assert(state[i] == state1[i]);
            assert(state[i] == HELD || occupied(state[i]));
            if i < idx as int {
                lemma_frame_slot(slots as int, i, idx as int);
            } else {
                lemma_frame_slot(slots as int, idx as int, i);
            }
            assert(s != to);
            assert(v0.contains_key(s));
            assert(v1[s] == v0[s]);
            k0.lemma_table_view(root, s);
            let ns = k0.tables.node_of(root, s);
            assert(k0.tables.is_cap(&k0.list, ns));
            assert(k1.tables.node_of(root, s) == ns);
            assert(k1.list.nodes@[ns as int].depth == k0.list.nodes@[ns as int].depth);
            lemma_slot_page(k0, root, s);
            lemma_untyped_page_facts(k0, memory, pages, i);
            let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
            assert((untyped_page(memory, i) as usize) / PAGE_SZ == p);
            assert(p as int == memory as int / PAGE_SZ as int + i);
            assert(slot_page(k0, root, s) == p);
            assert(p as int != p_idx);
            assert(k1.blocks.pages@[p as int] == k0.blocks.pages@[p as int]);
            assert((0usize as int) * PAGE_SZ < block_bytes(v0[s].order));
            assert(view_frame(v0[s], 0) == p);
            assert(block_ref(&k1.blocks, view_frame(v0[s], 0)) == block_ref(&k0.blocks, view_frame(v0[s], 0)));
            assert(frame_refs(k1, p) == frame_refs(k0, p));
        }
    }

    assert forall|i: int| 0 <= i < pages && occupied(#[trigger] state1[i]) implies {
        &&& window <= owner[i]
        &&& owner[i] < window + WINDOW_BYTES
        &&& owner[i] as int % PAGE_BYTES as int == 0
        &&& top
        &&& middle
        &&& tabled[((owner[i] - window) as int / BLOCK_BYTES as int)]
    } by {
        assert(i != idx as int);
        assert(occupied(state[i]));
    }

    assert forall|i: int, j: int|
        0 <= i < pages && 0 <= j < pages && i != j
            && occupied(#[trigger] state1[i]) && occupied(#[trigger] state1[j])
            implies owner[i] != owner[j] by {
        assert(i != idx as int && j != idx as int);
        assert(occupied(state[i]) && occupied(state[j]));
    }

    if top && middle {
        let tree0 = tree_of(&k0.table_pages, &k0.spaces);
        let tree1 = tree_of(&k1.table_pages, &k1.spaces);
        assert(tree1 == tree0);
        let t3 = step(tree0, root, address_path(window as u64).l4)->0;
        let t2 = step(tree0, t3, 0)->0;
        assert forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] tabled[b] implies {
            &&& step(tree1, t2, b as usize) is Some
            &&& forall|e: usize| #![trigger tree1.entry(step(tree1, t2, b as usize)->0, e)] e < ENTRIES ==> {
                let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                &&& window_entry_occupied(pages, state1, owner, va)
                    ==> tree1.entry(step(tree1, t2, b as usize)->0, e).perm.present
                &&& !window_entry_occupied(pages, state1, owner, va)
                    ==> tree1.entry(step(tree1, t2, b as usize)->0, e).is_empty()
            }
        } by {
            let t1 = step(tree0, t2, b as usize)->0;
            assert forall|e: usize| #![trigger tree1.entry(t1, e)] e < ENTRIES implies {
                let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                &&& window_entry_occupied(pages, state1, owner, va) ==> tree1.entry(t1, e).perm.present
                &&& !window_entry_occupied(pages, state1, owner, va) ==> tree1.entry(t1, e).is_empty()
            } by {
                let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                let _ = tree0.entry(t1, e);
                if window_entry_occupied(pages, state1, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state1[j]) && owner[j] == va;
                    assert(j != idx as int);
                    assert(occupied(state[j]));
                    assert(window_entry_occupied(pages, state, owner, va));
                }
                if window_entry_occupied(pages, state, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state[j]) && owner[j] == va;
                    assert(j != idx as int);
                    assert(occupied(state1[j]));
                    assert(window_entry_occupied(pages, state1, owner, va));
                }
            }
        }
    }
}

/// Under `caller_alone` and `source_state_ready` with a free order-3 group `group`, `retype_table_page`
/// at `1 <= level - 1 <= 3` is accepted.
pub(crate) proof fn lemma_ready_retype_table_ok(
    pre: Caller,
    mid: Caller,
    s1: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state_before: Seq<u8>,
    owner: Seq<usize>,
    group: usize,
    level: u64,
)
    requires
        pre.wf(),
        mid.wf(),
        mid.root() == pre.root(),
        acall_steps(pre, mid, seq![s1]),
        caller_alone(pre, mid),
        2 <= level <= 4,
        group + TABLE_PAGES <= pages,
        group as int % TABLE_PAGES as int == 0,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_before[group as int + k] == FREE,
        s1.call == (AcallCall::Retype {
            untyped,
            kind: RETYPE_TABLE_PAGE,
            base: untyped_page(memory, group as int) as u64,
            word: 0,
            level: (level - 1) as u64,
        }),
        source_state_ready(
            pre.kernel(),
            pre.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state_before,
            owner,
        ),
    ensures
        s1.out.status == STATUS_OK,
        mid.kernel().flush_epoch == pre.kernel().flush_epoch,
{
    lemma_ready_retype_table_contract(
        pre, mid, s1, space, untyped, memory, pages, slots, window, top, middle, tabled,
        state_before, owner, group, level,
    );
}

/// Under `caller_alone` and `source_state_ready` with a free order-3 group `group`, `retype_table_page`
/// at `1 <= level - 1 <= 3` is accepted, and its contract relates the two kernel states: the caller's
/// view is as it was, the untyped covers the group's block, and the block is a fresh table page of the
/// level.
#[verifier::spinoff_prover]
proof fn lemma_ready_retype_table_contract(
    pre: Caller,
    mid: Caller,
    s1: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state_before: Seq<u8>,
    owner: Seq<usize>,
    group: usize,
    level: u64,
)
    requires
        pre.wf(),
        mid.wf(),
        mid.root() == pre.root(),
        acall_steps(pre, mid, seq![s1]),
        caller_alone(pre, mid),
        2 <= level <= 4,
        group + TABLE_PAGES <= pages,
        group as int % TABLE_PAGES as int == 0,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_before[group as int + k] == FREE,
        s1.call == (AcallCall::Retype {
            untyped,
            kind: RETYPE_TABLE_PAGE,
            base: untyped_page(memory, group as int) as u64,
            word: 0,
            level: (level - 1) as u64,
        }),
        source_state_ready(
            pre.kernel(),
            pre.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state_before,
            owner,
        ),
    ensures
        s1.out.status == STATUS_OK,
        mid.kernel().flush_epoch == pre.kernel().flush_epoch,
        ({
            let child = untyped_page(memory, group as int) as usize;
            let k0 = pre.kernel();
            let km = mid.kernel();
            &&& child as u64 == untyped_page(memory, group as int) as u64
            &&& km.wf()
            &&& view_retypes(k0.table_view(pre.root())[untyped as usize], child, 3)
            &&& km.table_view(pre.root()) == k0.table_view(pre.root())
            &&& CapKernel::retype_table_contract_fields(k0, km, child)
            &&& km.table_pages.maps@.contains_key(child)
            &&& km.table_pages.records@[child].value() == fresh_table((level - 1) as usize)
        }),
{
    reveal(source_state_ready);
    reveal(CapKernel::retype_table_contract_fields);
    use vstd::arithmetic::div_mod::*;
    vstd::arithmetic::power2::lemma2_to64();
    lemma_acall_steps_alone(pre, mid, seq![s1]);
    assert(seq![s1][0] == s1);
    reveal(AcallStep::valid);
    assert(s1.valid());

    let k0 = pre.kernel();
    let root = pre.root();
    assert(s1.pre == k0 && s1.post == mid.kernel() && s1.root == root);

    assert(state_before[group as int + 0] == FREE);
    assert(state_before[group as int + 7] == FREE);
    lemma_untyped_page_facts(k0, memory, pages, group as int);
    lemma_untyped_page_facts(k0, memory, pages, group as int + 7);
    let base = untyped_page(memory, group as int) as usize;
    let p_grp = (base / PAGE_SZ) as int;

    assert(PAGE_BYTES == PAGE_SZ);
    assert(TABLE_PAGES == 8);
    assert(block_bytes(3) == 8 * PAGE_SZ as int);
    assert(order_pages(3) == 8);

    let qm = memory as int / (8 * PAGE_SZ as int);
    let qg = group as int / 8;
    lemma_fundamental_div_mod(memory as int, 8 * PAGE_SZ as int);
    lemma_fundamental_div_mod(group as int, 8);
    assert(base as int == (qm + qg) * (8 * PAGE_SZ as int)) by (nonlinear_arith)
        requires
            base as int == memory as int + (group as int) * (PAGE_SZ as int),
            memory as int == (8 * PAGE_SZ as int) * qm,
            group as int == 8 * qg,
    ;
    lemma_mod_multiples_basic(qm + qg, 8 * PAGE_SZ as int);
    assert(base as int % block_bytes(3) == 0);

    let v0 = k0.table_view(root);
    assert(v0[untyped as usize].base <= base) by {
        assert((group as int) * (PAGE_SZ as int) >= 0) by (nonlinear_arith)
            requires group >= 0, PAGE_SZ > 0;
    }
    assert(base as int + block_bytes(3) <= v0[untyped as usize].base as int + block_bytes(v0[untyped as usize].order)) by {
        assert((group as int + 8) * (PAGE_SZ as int) <= (pages as int) * (PAGE_SZ as int)) by (nonlinear_arith)
            requires group + 8 <= pages, PAGE_SZ > 0;
    }
    assert(8 * PAGE_SZ as int <= block_bytes(v0[untyped as usize].order)) by {
        assert(8 * (PAGE_SZ as int) <= (pages as int) * (PAGE_SZ as int)) by (nonlinear_arith)
            requires 8 <= pages, PAGE_SZ > 0;
    }
    if v0[untyped as usize].order < 3 {
        assert(v0[untyped as usize].order == 0 || v0[untyped as usize].order == 1 || v0[untyped as usize].order == 2);
        assert(block_bytes(v0[untyped as usize].order) <= 4 * PAGE_SZ as int);
        assert(false);
    }
    assert(view_retypes(v0[untyped as usize], base, 3));
    assert(k0.retype_under_allowed(root, untyped as usize, base, 3));

    assert(k0.blocks.tracks(p_grp + 7));
    assert(k0.blocks.tracks_addr_run(base, 8));
    assert(!k0.blocks.covered(p_grp));
    assert forall|m: int| 0 <= m < order_pages(3) implies #[trigger] k0.blocks.pages@[p_grp + m].kind is Free by {
        assert(p_grp + m == memory as int / PAGE_SZ as int + (group as int + m));
        assert(state_before[group as int + m] == FREE);
    }
    assert(k0.small_block_free(base, 3));
    assert(k0.retype_allowed(root, RETYPE_TABLE_PAGE, untyped as usize, base, 0, (level - 1) as usize));
    assert(s1.out.status == STATUS_OK);
    assert((untyped_page(memory, group as int) as u64) as usize == base);
    assert(((level - 1) as u64) as usize == (level - 1) as usize);
    assert(mid.kernel().table_view(root) == k0.table_view(root));
}

/// Distinct block entries `b1 != b2` of a level-2 table `t2` name distinct level-1 child tables.
proof fn lemma_distinct_children(k: CapKernel, t: usize, i: usize, j: usize)
    requires
        k.wf(),
        step(tree_of(&k.table_pages, &k.spaces), t, i) is Some,
        step(tree_of(&k.table_pages, &k.spaces), t, j) is Some,
        i != j,
    ensures
        step(tree_of(&k.table_pages, &k.spaces), t, i)->0 != step(tree_of(&k.table_pages, &k.spaces), t, j)->0,
{
    let tree = tree_of(&k.table_pages, &k.spaces);
    reveal(table_links_wf);
    let _ = tree.entry(t, i);
    let _ = tree.entry(t, j);
    let ci = step(tree, t, i)->0;
    let cj = step(tree, t, j)->0;
    assert(tree.record(ci).parent == Some(TableParent { table: t, entry: i }));
    assert(tree.record(cj).parent == Some(TableParent { table: t, entry: j }));
}

/// Equal `maps` and `roots` domains preserve `is_page`, `is_root`, and `is_table`.
proof fn lemma_same_tree_domains(a: TableTree, b: TableTree)
    requires
        b.maps.dom() == a.maps.dom(),
        b.roots.dom() == a.roots.dom(),
    ensures
        forall|t: usize| #[trigger] b.is_page(t) == a.is_page(t),
        forall|t: usize| #[trigger] b.is_root(t) == a.is_root(t),
        forall|t: usize| #[trigger] b.is_table(t) == a.is_table(t),
{
    assert forall|t: usize| #[trigger] b.is_page(t) == a.is_page(t) by {
        assert(b.maps.dom().contains(t) == a.maps.dom().contains(t));
    }
    assert forall|t: usize| #[trigger] b.is_root(t) == a.is_root(t) by {
        assert(b.roots.dom().contains(t) == a.roots.dom().contains(t));
    }
    assert forall|t: usize| #[trigger] b.is_table(t) == a.is_table(t) by {
        assert(b.is_page(t) == a.is_page(t));
        assert(b.is_root(t) == a.is_root(t));
    }
}

/// The table page a source has retyped at `child` and not linked yet, in `k`: a live table page of
/// `level` with a fresh record and every entry empty.
pub(crate) open spec fn table_page_unlinked(k: CapKernel, child: usize, level: usize) -> bool {
    let tree = tree_of(&k.table_pages, &k.spaces);
    &&& tree.is_page(child)
    &&& tree.record(child) == fresh_table(level)
    &&& !k.blocks.pages@[(child / PAGE_SZ) as int].dead
    &&& forall|i: usize| i < ENTRIES ==> #[trigger] k.table_pages.maps@[child].value()[i].is_empty()
}

/// Under `caller_alone` and `source_state_ready` with a free order-3 group `group`, `retype_table_page`
/// at `level - 1` is accepted and leaves `source_state_ready` with `group .. group + 8` marked `TAKEN`
/// and the window's tables as they were, the group's block an unlinked table page that the untyped still
/// covers.
pub(crate) proof fn lemma_ready_table_retyped(
    pre: Caller,
    mid: Caller,
    s1: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state_before: Seq<u8>,
    state_after: Seq<u8>,
    owner: Seq<usize>,
    group: usize,
    level: u64,
)
    requires
        pre.wf(),
        mid.wf(),
        mid.root() == pre.root(),
        acall_steps(pre, mid, seq![s1]),
        caller_alone(pre, mid),
        2 <= level <= 4,
        group + TABLE_PAGES <= pages,
        group as int % TABLE_PAGES as int == 0,
        state_after.len() == MAX_PAGES,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_before[group as int + k] == FREE,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_after[group as int + k] == TAKEN,
        forall|u: int|
            0 <= u < MAX_PAGES && !(group as int <= u < group as int + TABLE_PAGES as int)
                ==> #[trigger] state_after[u] == state_before[u],
        s1.call == (AcallCall::Retype {
            untyped,
            kind: RETYPE_TABLE_PAGE,
            base: untyped_page(memory, group as int) as u64,
            word: 0,
            level: (level - 1) as u64,
        }),
        source_state_ready(
            pre.kernel(),
            pre.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state_before,
            owner,
        ),
    ensures
        s1.out.status == STATUS_OK,
        mid.kernel().flush_epoch == pre.kernel().flush_epoch,
        source_state_ready(
            mid.kernel(),
            mid.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state_after,
            owner,
        ),
        table_page_unlinked(mid.kernel(), untyped_page(memory, group as int) as usize, (level - 1) as usize),
        view_retypes(
            mid.kernel().table_view(mid.root())[untyped as usize],
            untyped_page(memory, group as int) as usize,
            3,
        ),
        (untyped_page(memory, group as int) as usize) as u64 == untyped_page(memory, group as int) as u64,
{
    lemma_ready_retype_table_contract(
        pre, mid, s1, space, untyped, memory, pages, slots, window, top, middle, tabled,
        state_before, owner, group, level,
    );
    lemma_table_retyped_ready(
        pre.kernel(), mid.kernel(), pre.root(), space, untyped, memory, pages, slots, window, top, middle,
        tabled, state_before, state_after, owner, group, (level - 1) as usize,
    );
}

/// What a `retype_table_page` at `child` leaves as it was, as `retype_table_contract_fields` says it:
/// the tables, the spaces, the processes, the large regions, every tracked page outside the eight of
/// the block, every empty slot and every capability's depth.
proof fn lemma_retype_table_kept(k0: CapKernel, km: CapKernel, child: usize)
    requires
        CapKernel::retype_table_contract_fields(k0, km, child),
    ensures
        km.tables == k0.tables,
        km.spaces == k0.spaces,
        km.processes == k0.processes,
        km.blocks.regions_2m@ == k0.blocks.regions_2m@,
        km.blocks.regions_1g@ == k0.blocks.regions_1g@,
        !km.blocks.pages@[(child / PAGE_SZ) as int].dead,
        forall|p: int|
            k0.blocks.tracks(p) && !((child / PAGE_SZ) as int <= p < (child / PAGE_SZ) as int + TABLE_PAGES as int)
                ==> #[trigger] km.blocks.pages@[p] == k0.blocks.pages@[p],
        forall|t: usize, j: usize| #[trigger] k0.empty_slot(t, j) ==> km.empty_slot(t, j),
        forall|x: usize| #[trigger] k0.tables.is_cap(&k0.list, x)
            ==> km.list.nodes@[x as int].depth == k0.list.nodes@[x as int].depth,
{
    reveal(CapKernel::retype_table_contract_fields);
    assert(order_pages(3) == TABLE_PAGES as int);
}

/// A `retype_table_page` at `child`, which was no table, leaves every table's entries as they were and
/// naming the children they named, and the new table page's entries empty.
proof fn lemma_retype_table_tree(k0: CapKernel, km: CapKernel, child: usize)
    requires
        CapKernel::retype_table_contract_fields(k0, km, child),
        !tree_of(&k0.table_pages, &k0.spaces).is_table(child),
    ensures
        forall|t: usize, i: usize| tree_of(&k0.table_pages, &k0.spaces).is_table(t)
            ==> #[trigger] tree_of(&km.table_pages, &km.spaces).entry(t, i)
                == tree_of(&k0.table_pages, &k0.spaces).entry(t, i),
        forall|t: usize, i: usize| tree_of(&k0.table_pages, &k0.spaces).is_table(t)
            ==> #[trigger] tree_of(&km.table_pages, &km.spaces).names_child(t, i)
                == tree_of(&k0.table_pages, &k0.spaces).names_child(t, i),
        forall|i: usize| i < ENTRIES ==> #[trigger] km.table_pages.maps@[child].value()[i].is_empty(),
{
    reveal(CapKernel::retype_table_contract_fields);
    let tree0 = tree_of(&k0.table_pages, &k0.spaces);
    let treem = tree_of(&km.table_pages, &km.spaces);
    assert forall|t: usize| #[trigger] tree0.is_table(t) implies {
        &&& treem.is_page(t) == tree0.is_page(t)
        &&& treem.is_root(t) == tree0.is_root(t)
        &&& treem.record(t) == tree0.record(t)
        &&& forall|i: usize| #[trigger] treem.entry(t, i) == tree0.entry(t, i)
    } by {
        assert(t != child);
    }
    assert forall|t: usize, i: usize| tree0.is_table(t)
        implies #[trigger] treem.names_child(t, i) == tree0.names_child(t, i) by {
        assert(treem.entry(t, i) == tree0.entry(t, i));
        assert(treem.child_slot(t, i) == tree0.child_slot(t, i));
    }
}

/// The frame slots and pages of a source, as `source_state_ready` holds them in `k`.
pub(crate) open spec fn frames_ready(
    k: CapKernel,
    root: usize,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    state: Seq<u8>,
) -> bool {
    let v = k.table_view(root);
    &&& forall|i: int| 0 <= i < pages && #[trigger] state[i] == FREE ==> {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k.blocks.tracks(p)
        &&& k.blocks.pages@[p].kind is Free
        &&& !k.blocks.covered(p)
    }
    &&& forall|i: int| 0 <= i < pages && (#[trigger] state[i] == HELD || occupied(state[i])) ==> {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& v.contains_key(s)
        &&& v[s] == frame_view(untyped_page(memory, i) as usize, 0, k.tables.node_of(root, untyped as usize))
        &&& k.list.nodes@[k.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& k.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&k.blocks, p) == BlockRef::Small(p)
        &&& k.blocks.pages@[p as int].kind is Base
        &&& k.blocks.pages@[p as int].object is Frame
        &&& frame_refs(k, p) == if occupied(state[i]) { 2usize } else { 1usize }
        &&& !k.blocks.pages@[p as int].dead
    }
}

/// A `retype_table_page` of the free group `group .. group + 8` of a source leaves every other frame
/// slot and page of the source as `frames_ready` held it.
#[verifier::spinoff_prover]
proof fn lemma_retyped_frames_kept(
    k0: CapKernel,
    km: CapKernel,
    root: usize,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    state_before: Seq<u8>,
    state_after: Seq<u8>,
    group: usize,
)
    requires
        CapKernel::retype_table_contract_fields(k0, km, untyped_page(memory, group as int) as usize),
        km.table_view(root) == k0.table_view(root),
        pages <= MAX_PAGES,
        memory as int % (TABLE_PAGES * PAGE_BYTES) as int == 0,
        memory + pages * PAGE_BYTES <= u64::MAX,
        group + TABLE_PAGES <= pages,
        frames_ready(k0, root, untyped, memory, pages, slots, state_before),
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_before[group as int + k] == FREE,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_after[group as int + k] == TAKEN,
        forall|u: int|
            0 <= u < MAX_PAGES && !(group as int <= u < group as int + TABLE_PAGES as int)
                ==> #[trigger] state_after[u] == state_before[u],
    ensures
        frames_ready(km, root, untyped, memory, pages, slots, state_after),
{
    assert(state_before[group as int + 0] == FREE);
    lemma_untyped_page_facts(k0, memory, pages, group as int);
    let child = untyped_page(memory, group as int) as usize;
    let p_grp = (child / PAGE_SZ) as int;
    assert(p_grp == memory as int / PAGE_SZ as int + group as int);
    lemma_retype_table_kept(k0, km, child);
    let vm = km.table_view(root);

    assert forall|i: int| 0 <= i < pages && #[trigger] state_after[i] == FREE implies {
        let p = memory as int / PAGE_SZ as int + i;
        &&& km.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& km.blocks.tracks(p)
        &&& km.blocks.pages@[p].kind is Free
        &&& !km.blocks.covered(p)
    } by {
        if group as int <= i < group as int + TABLE_PAGES as int {
            assert(state_after[group as int + (i - group as int)] == TAKEN);
            assert(false);
        }
        assert(state_before[i] == FREE);
        let p = memory as int / PAGE_SZ as int + i;
        assert(km.blocks.pages@[p] == k0.blocks.pages@[p]);
    }

    assert forall|i: int| 0 <= i < pages && (#[trigger] state_after[i] == HELD || occupied(state_after[i])) implies {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& vm.contains_key(s)
        &&& vm[s] == frame_view(untyped_page(memory, i) as usize, 0, km.tables.node_of(root, untyped as usize))
        &&& km.list.nodes@[km.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& km.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&km.blocks, p) == BlockRef::Small(p)
        &&& km.blocks.pages@[p as int].kind is Base
        &&& km.blocks.pages@[p as int].object is Frame
        &&& frame_refs(km, p) == if occupied(state_after[i]) { 2usize } else { 1usize }
        &&& !km.blocks.pages@[p as int].dead
    } by {
        if group as int <= i < group as int + TABLE_PAGES as int {
            assert(state_after[group as int + (i - group as int)] == TAKEN);
            assert(false);
        }
        assert(state_before[i] == state_after[i]);
        let s = frame_slot(slots as int, i) as usize;
        lemma_untyped_page_facts(k0, memory, pages, i);
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        assert(p as int == memory as int / PAGE_SZ as int + i);
        k0.lemma_table_view(root, s);
        let ns = k0.tables.node_of(root, s);
        assert(k0.tables.is_cap(&k0.list, ns));
        assert(km.list.nodes@[ns as int].depth == k0.list.nodes@[ns as int].depth);
        assert(km.blocks.pages@[p as int] == k0.blocks.pages@[p as int]);
        assert(block_ref(&km.blocks, p) == block_ref(&k0.blocks, p));
        assert(frame_refs(km, p) == frame_refs(k0, p));
    }
}

/// A `retype_table_page` of the free group `group .. group + 8` of a ready source, as its contract
/// relates `k0` to `km`, leaves the source ready with the group marked `TAKEN` and the window's tables
/// as they were, the group's block an unlinked table page of `level`.
#[verifier::spinoff_prover]
proof fn lemma_table_retyped_ready(
    k0: CapKernel,
    km: CapKernel,
    root: usize,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state_before: Seq<u8>,
    state_after: Seq<u8>,
    owner: Seq<usize>,
    group: usize,
    level: usize,
)
    requires
        source_state_ready(k0, root, space, untyped, memory, pages, slots, window, top, middle, tabled, state_before, owner),
        km.wf(),
        km.table_view(root) == k0.table_view(root),
        CapKernel::retype_table_contract_fields(k0, km, untyped_page(memory, group as int) as usize),
        km.table_pages.maps@.contains_key(untyped_page(memory, group as int) as usize),
        km.table_pages.records@[untyped_page(memory, group as int) as usize].value() == fresh_table(level),
        group + TABLE_PAGES <= pages,
        state_after.len() == MAX_PAGES,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_before[group as int + k] == FREE,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_after[group as int + k] == TAKEN,
        forall|u: int|
            0 <= u < MAX_PAGES && !(group as int <= u < group as int + TABLE_PAGES as int)
                ==> #[trigger] state_after[u] == state_before[u],
    ensures
        source_state_ready(km, root, space, untyped, memory, pages, slots, window, top, middle, tabled, state_after, owner),
        table_page_unlinked(km, untyped_page(memory, group as int) as usize, level),
{
    reveal(source_state_ready);
    assert(state_before[group as int + 0] == FREE);
    lemma_untyped_page_facts(k0, memory, pages, group as int);
    let child = untyped_page(memory, group as int) as usize;
    let p_grp = (child / PAGE_SZ) as int;
    assert(p_grp == memory as int / PAGE_SZ as int + group as int);
    lemma_retype_table_kept(k0, km, child);

    let tree0 = tree_of(&k0.table_pages, &k0.spaces);
    let treem = tree_of(&km.table_pages, &km.spaces);

    // Every table of `tree0` had a `Base` page, whereas the group's pages were `Free` in `k0`, so
    // `child` was no table and `root`'s page is outside the group.
    assert(tree0.is_table(root));
    k0.lemma_table_base(root);
    let p_root = (root / PAGE_SZ) as int;
    if p_grp <= p_root < p_grp + TABLE_PAGES as int {
        assert(state_before[group as int + (p_root - p_grp)] == FREE);
        assert(k0.blocks.pages@[memory as int / PAGE_SZ as int + (group as int + (p_root - p_grp))].kind is Free);
        assert(false);
    }
    assert(km.blocks.pages@[p_root] == k0.blocks.pages@[p_root]);
    if tree0.is_table(child) {
        k0.lemma_table_base(child);
        assert(k0.blocks.pages@[memory as int / PAGE_SZ as int + group as int].kind is Free);
        assert(false);
    }
    lemma_retype_table_tree(k0, km, child);

    // The untyped's capability is where it was, at the depth it had.
    k0.lemma_table_view(root, untyped as usize);
    let nu = k0.tables.node_of(root, untyped as usize);
    assert(k0.tables.is_cap(&k0.list, nu));
    assert(km.list.nodes@[nu as int].depth == k0.list.nodes@[nu as int].depth);

    assert(frames_ready(k0, root, untyped, memory, pages, slots, state_before));
    lemma_retyped_frames_kept(k0, km, root, untyped, memory, pages, slots, state_before, state_after, group);

    assert forall|i: int| 0 <= i < pages && occupied(#[trigger] state_after[i]) implies {
        &&& window <= owner[i]
        &&& owner[i] < window + WINDOW_BYTES
        &&& owner[i] as int % PAGE_BYTES as int == 0
        &&& top
        &&& middle
        &&& tabled[((owner[i] - window) as int / BLOCK_BYTES as int)]
    } by {
        if group as int <= i < group as int + TABLE_PAGES as int {
            assert(state_after[group as int + (i - group as int)] == TAKEN);
            assert(false);
        }
        assert(occupied(state_before[i]));
    }

    assert forall|i: int, j: int|
        0 <= i < pages && 0 <= j < pages && i != j
            && occupied(#[trigger] state_after[i]) && occupied(#[trigger] state_after[j])
            implies owner[i] != owner[j] by {
        if group as int <= i < group as int + TABLE_PAGES as int {
            assert(state_after[group as int + (i - group as int)] == TAKEN);
            assert(false);
        }
        if group as int <= j < group as int + TABLE_PAGES as int {
            assert(state_after[group as int + (j - group as int)] == TAKEN);
            assert(false);
        }
        assert(occupied(state_before[i]) && occupied(state_before[j]));
    }

    // The window's tables are tables of `tree0`, so `treem` holds them as they were.
    assert(window_tables_ready(tree0, root, window, pages, top, middle, tabled, state_before, owner));
    lemma_retyped_window_tables(k0, treem, root, window, pages, top, middle, tabled, state_before, state_after, owner, group);
    assert(window_tables_ready(treem, root, window, pages, top, middle, tabled, state_after, owner));
    assert(frames_ready(km, root, untyped, memory, pages, slots, state_after));
}

/// The window's tables of a source, as `source_state_ready` holds them in `tree`.
pub(crate) open spec fn window_tables_ready(
    tree: TableTree,
    root: usize,
    window: usize,
    pages: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
) -> bool {
    let l4 = address_path(window as u64).l4;
    &&& (!top ==> tree.entry(root, l4).is_empty())
    &&& (top ==> {
        let t3 = step(tree, root, l4)->0;
        &&& step(tree, root, l4) is Some
        &&& (!middle ==> tree.entry(t3, 0).is_empty())
        &&& (middle ==> {
            let t2 = step(tree, t3, 0)->0;
            &&& step(tree, t3, 0) is Some
            &&& forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] tabled[b] ==> {
                &&& step(tree, t2, b as usize) is Some
                &&& forall|e: usize| #![trigger tree.entry(step(tree, t2, b as usize)->0, e)] e < ENTRIES ==> {
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    &&& window_entry_occupied(pages, state, owner, va)
                        ==> tree.entry(step(tree, t2, b as usize)->0, e).perm.present
                    &&& !window_entry_occupied(pages, state, owner, va)
                        ==> tree.entry(step(tree, t2, b as usize)->0, e).is_empty()
                }
            }
            &&& forall|b: int| 0 <= b < WINDOW_BLOCKS && !#[trigger] tabled[b]
                ==> tree.entry(t2, b as usize).is_empty()
        })
    })
}

/// A retype that leaves every table of `k0`'s tree as it was in `treem`, and takes the free group
/// `group .. group + 8` that no page of the window maps, leaves the window's tables ready.
#[verifier::spinoff_prover]
proof fn lemma_retyped_window_tables(
    k0: CapKernel,
    treem: TableTree,
    root: usize,
    window: usize,
    pages: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state_before: Seq<u8>,
    state_after: Seq<u8>,
    owner: Seq<usize>,
    group: usize,
)
    requires
        k0.wf(),
        tree_of(&k0.table_pages, &k0.spaces).is_table(root),
        forall|t: usize, i: usize| tree_of(&k0.table_pages, &k0.spaces).is_table(t)
            ==> #[trigger] treem.entry(t, i) == tree_of(&k0.table_pages, &k0.spaces).entry(t, i),
        forall|t: usize, i: usize| tree_of(&k0.table_pages, &k0.spaces).is_table(t)
            ==> #[trigger] treem.names_child(t, i) == tree_of(&k0.table_pages, &k0.spaces).names_child(t, i),
        window != 0,
        window as int % SIZE_512G as int == 0,
        window + WINDOW_BYTES <= LOWER_HALF_END as usize,
        pages <= MAX_PAGES,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_before[group as int + k] == FREE,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_after[group as int + k] == TAKEN,
        forall|u: int|
            0 <= u < MAX_PAGES && !(group as int <= u < group as int + TABLE_PAGES as int)
                ==> #[trigger] state_after[u] == state_before[u],
        window_tables_ready(tree_of(&k0.table_pages, &k0.spaces), root, window, pages, top, middle, tabled, state_before, owner),
    ensures
        window_tables_ready(treem, root, window, pages, top, middle, tabled, state_after, owner),
{
    let tree0 = tree_of(&k0.table_pages, &k0.spaces);
    lemma_window_path(window);
    let l4 = address_path(window as u64).l4;
    assert(treem.entry(root, l4) == tree0.entry(root, l4));
    if top {
        k0.lemma_child_facts(root, l4);
        let t3 = step(tree0, root, l4)->0;
        assert(tree0.is_table(t3));
        assert(treem.names_child(root, l4) == tree0.names_child(root, l4));
        assert(step(treem, root, l4) == Some(t3));
        assert(treem.entry(t3, 0) == tree0.entry(t3, 0));
        if middle {
            k0.lemma_child_facts(t3, 0);
            let t2 = step(tree0, t3, 0)->0;
            assert(tree0.is_table(t2));
            assert(treem.names_child(t3, 0) == tree0.names_child(t3, 0));
            assert(step(treem, t3, 0) == Some(t2));
            assert forall|b: int| 0 <= b < WINDOW_BLOCKS && !#[trigger] tabled[b]
                implies treem.entry(t2, b as usize).is_empty() by {
                assert(treem.entry(t2, b as usize) == tree0.entry(t2, b as usize));
            }
            assert forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] tabled[b] implies {
                &&& step(treem, t2, b as usize) is Some
                &&& forall|e: usize| #![trigger treem.entry(step(treem, t2, b as usize)->0, e)] e < ENTRIES ==> {
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    &&& window_entry_occupied(pages, state_after, owner, va)
                        ==> treem.entry(step(treem, t2, b as usize)->0, e).perm.present
                    &&& !window_entry_occupied(pages, state_after, owner, va)
                        ==> treem.entry(step(treem, t2, b as usize)->0, e).is_empty()
                }
            } by {
                k0.lemma_child_facts(t2, b as usize);
                let t1 = step(tree0, t2, b as usize)->0;
                assert(tree0.is_table(t1));
                assert(treem.names_child(t2, b as usize) == tree0.names_child(t2, b as usize));
                assert(treem.entry(t2, b as usize) == tree0.entry(t2, b as usize));
                assert(step(treem, t2, b as usize) == Some(t1));
                assert forall|e: usize| #![trigger treem.entry(t1, e)] e < ENTRIES implies {
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    &&& window_entry_occupied(pages, state_after, owner, va) ==> treem.entry(t1, e).perm.present
                    &&& !window_entry_occupied(pages, state_after, owner, va) ==> treem.entry(t1, e).is_empty()
                } by {
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    let _ = tree0.entry(t1, e);
                    assert(treem.entry(t1, e) == tree0.entry(t1, e));
                    if window_entry_occupied(pages, state_after, owner, va) {
                        let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state_after[j]) && owner[j] == va;
                        if group as int <= j < group as int + TABLE_PAGES as int {
                            assert(state_after[group as int + (j - group as int)] == TAKEN);
                            assert(false);
                        }
                        assert(occupied(state_before[j]));
                        assert(window_entry_occupied(pages, state_before, owner, va));
                    }
                    if window_entry_occupied(pages, state_before, owner, va) {
                        let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state_before[j]) && owner[j] == va;
                        if group as int <= j < group as int + TABLE_PAGES as int {
                            assert(state_before[group as int + (j - group as int)] == FREE);
                            assert(false);
                        }
                        assert(occupied(state_after[j]));
                        assert(window_entry_occupied(pages, state_after, owner, va));
                    }
                }
            }
        }
    }
}

/// Under `caller_alone` and `source_state_ready`, the `link` of an unlinked table page at `child`, one
/// level below `level` and covered by the untyped, at an unlinked path entry `(address, level)` is
/// accepted and establishes `source_state_ready` with that path entry marked linked.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ready_table_linked(
    mid: Caller,
    post: Caller,
    s2: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
    child: usize,
    address: usize,
    level: u64,
)
    requires
        mid.wf(),
        post.wf(),
        post.root() == mid.root(),
        acall_steps(mid, post, seq![s2]),
        caller_alone(mid, post),
        2 <= level <= 4,
        (level == 4 && !top && address == window)
            || (level == 3 && top && !middle && address == window)
            || (level == 2 && top && middle && exists|b: int|
                0 <= b < WINDOW_BLOCKS && !tabled[b] && address as int == #[trigger] window_block(window, b)),
        s2.call == (AcallCall::Link {
            slot: space,
            va: address as u64,
            level,
            from: untyped,
            child: child as u64,
        }),
        source_state_ready(
            mid.kernel(),
            mid.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state,
            owner,
        ),
        table_page_unlinked(mid.kernel(), child, (level - 1) as usize),
        view_retypes(mid.kernel().table_view(mid.root())[untyped as usize], child, 3),
    ensures
        s2.out.status == STATUS_OK,
        post.kernel().flush_epoch == mid.kernel().flush_epoch,
        ({
            let next_top = if level == 4 { true } else { top };
            let next_middle = if level == 3 { true } else { middle };
            let next_tabled = if level == 2 {
                tabled.update((address - window) as int / BLOCK_BYTES as int, true)
            } else {
                tabled
            };
            source_state_ready(
                post.kernel(),
                post.root(),
                space,
                untyped,
                memory,
                pages,
                slots,
                window,
                next_top,
                next_middle,
                next_tabled,
                state,
                owner,
            )
        }),
{
    reveal(source_state_ready);
    reveal(CapKernel::link_contract_fields);
    use vstd::arithmetic::div_mod::*;
    lemma_acall_steps_alone(mid, post, seq![s2]);
    assert(seq![s2][0] == s2);
    reveal(AcallStep::valid);
    assert(s2.valid());

    let km = mid.kernel();
    let k2 = post.kernel();
    let root = mid.root();
    assert(s2.pre == km && s2.post == k2 && s2.root == root);
    assert((child as u64) as usize == child);

    lemma_window_path(window);
    let l4 = address_path(window as u64).l4;
    let treem = tree_of(&km.table_pages, &km.spaces);
    let tree2 = tree_of(&k2.table_pages, &k2.spaces);

    // `root` is its space's root and `child` a table page with no space yet, so no table the walk from
    // `root` reaches is `child`.
    assert(treem.is_root(root));
    km.lemma_table_base(root);
    assert(!treem.is_page(root));
    assert(treem.is_page(child));
    km.lemma_table_base(child);
    assert(child != root);
    assert(treem.record(child).space is None);
    lemma_table_bound(&km.blocks, child);
    lemma_table_addr_valid(child);
    assert(((child + TABLE_NODE_PAGES * PAGE_SZ) as usize - TABLE_NODE_PAGES * PAGE_SZ) as usize == child);

    let vm = km.table_view(root);
    lemma_own_space_cap_live(km, root, space);

    if level == 4 {
        assert(km.link_parent(root, address as u64, 4) == Some(TableParent { table: root, entry: l4 }));
        assert(treem.child_slot(root, l4));
        assert(km.link_fits(root, address as u64, 4, child));
    } else if level == 3 {
        km.lemma_child_facts(root, l4);
        let t3 = step(treem, root, l4)->0;
        km.lemma_table_base(t3);
        assert(km.link_parent(root, address as u64, 3) == Some(TableParent { table: t3, entry: 0 }));
        assert(treem.child_slot(t3, 0));
        assert(km.link_fits(root, address as u64, 3, child));
    } else {
        let b_blk = choose|b: int| 0 <= b < WINDOW_BLOCKS && !tabled[b] && address as int == #[trigger] window_block(window, b);
        let _ = window_block(window, b_blk);
        assert((address - window) as int / BLOCK_BYTES as int == b_blk) by {
            assert(address - window == b_blk * (BLOCK_BYTES as int));
            lemma_div_by_multiple(b_blk, BLOCK_BYTES as int);
        }
        km.lemma_child_facts(root, l4);
        let t3 = step(treem, root, l4)->0;
        km.lemma_table_base(t3);
        km.lemma_child_facts(t3, 0);
        let t2 = step(treem, t3, 0)->0;
        km.lemma_table_base(t2);
        assert(km.link_parent(root, address as u64, 2) == Some(TableParent { table: t2, entry: b_blk as usize }));
        assert(treem.child_slot(t2, b_blk as usize));
        assert(km.link_fits(root, address as u64, 2, child));
    }

    assert(km.link_allowed(root, space as usize, address as u64, level, untyped as usize, child));
    assert(s2.out.status == STATUS_OK);

    // Post-link state `k2`: its blocks, list, tables, processes and views are `km`'s.
    let place = km.link_parent(root, address as u64, level)->0;
    assert(linked(treem, tree2, place.table, place.entry, child, root));
    lemma_same_tree_domains(treem, tree2);
    let v2 = k2.table_view(root);
    assert(v2 == vm);
    assert(k2.spaces.roots@.contains_key(root)) by {
        assert(tree2.is_root(root) == treem.is_root(root));
    }
    assert(k2.spaces.records@[root].value().kind == SpaceKind::Process) by {
        assert(treem.is_root(root));
        assert(tree2.space_records[root].value().kind == treem.space_records[root].value().kind);
    }

    let next_top = if level == 4 { true } else { top };
    let next_middle = if level == 3 { true } else { middle };
    let next_tabled = if level == 2 {
        tabled.update((address - window) as int / BLOCK_BYTES as int, true)
    } else {
        tabled
    };

    assert forall|i: int| 0 <= i < pages && #[trigger] state[i] == FREE implies {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k2.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k2.blocks.tracks(p)
        &&& k2.blocks.pages@[p].kind is Free
        &&& !k2.blocks.covered(p)
    } by {
        let si = frame_slot(slots as int, i) as usize;
        assert(km.empty_slot(root, si));
    }

    assert forall|i: int| 0 <= i < pages && (#[trigger] state[i] == HELD || occupied(state[i])) implies {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& v2.contains_key(s)
        &&& v2[s] == frame_view(untyped_page(memory, i) as usize, 0, k2.tables.node_of(root, untyped as usize))
        &&& k2.list.nodes@[k2.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& k2.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&k2.blocks, p) == BlockRef::Small(p)
        &&& k2.blocks.pages@[p as int].kind is Base
        &&& k2.blocks.pages@[p as int].object is Frame
        &&& frame_refs(k2, p) == if occupied(state[i]) { 2usize } else { 1usize }
        &&& !k2.blocks.pages@[p as int].dead
    } by {
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        assert(frame_refs(k2, p) == frame_refs(km, p));
    }

    assert forall|i: int| 0 <= i < pages && occupied(#[trigger] state[i]) implies {
        &&& window <= owner[i]
        &&& owner[i] < window + WINDOW_BYTES
        &&& owner[i] as int % PAGE_BYTES as int == 0
        &&& next_top
        &&& next_middle
        &&& next_tabled[((owner[i] - window) as int / BLOCK_BYTES as int)]
    } by {
        // An occupied page's block has its table, so the link is of another block's table.
        let x = (owner[i] - window) as int / BLOCK_BYTES as int;
        assert(top && middle && tabled[x]);
        assert(level == 2);
        assert(WINDOW_BYTES == WINDOW_BLOCKS * BLOCK_BYTES);
        assert(0 <= x < WINDOW_BLOCKS);
    }

    // Tree structure after `linked`:
    if level == 4 {
        assert(linked(treem, tree2, root, l4, child, root));
        assert(tree2.is_root(root) && !tree2.is_page(root));
        assert(tree2.record(root).level == treem.record(root).level);
        assert(tree2.child_slot(root, l4));
        assert(tree2.entry(root, l4) == child_entry(child));
        assert(tree2.names_child(root, l4));
        assert(step(tree2, root, l4) == Some(child));
        assert(tree2.entry(child, 0) == treem.entry(child, 0));
        assert(km.table_pages.maps@[child].value()[0].is_empty());
        assert(treem.entry(child, 0).is_empty());
    } else if level == 3 {
        km.lemma_child_facts(root, l4);
        let t3 = step(treem, root, l4)->0;
        km.lemma_table_base(t3);
        assert(treem.is_table(t3));
        assert(t3 != child && root != t3);
        assert(linked(treem, tree2, t3, 0, child, root));
        assert(tree2.record(root).level == treem.record(root).level);
        assert(tree2.record(t3).level == treem.record(t3).level);
        assert(tree2.entry(root, l4) == treem.entry(root, l4));
        assert(tree2.child_slot(root, l4));
        assert(tree2.names_child(root, l4));
        assert(step(tree2, root, l4) == Some(t3));
        assert(tree2.child_slot(t3, 0));
        assert(tree2.entry(t3, 0) == child_entry(child));
        assert(tree2.names_child(t3, 0));
        assert(step(tree2, t3, 0) == Some(child));
        assert forall|b: int| 0 <= b < WINDOW_BLOCKS && !#[trigger] next_tabled[b]
            implies tree2.entry(child, b as usize).is_empty() by {
            assert(tree2.entry(child, b as usize) == treem.entry(child, b as usize));
            assert(km.table_pages.maps@[child].value()[b as usize].is_empty());
        }
    } else {
        let b_blk = (address - window) as int / BLOCK_BYTES as int;
        let b_ch = choose|b: int| 0 <= b < WINDOW_BLOCKS && !tabled[b] && address as int == #[trigger] window_block(window, b);
        assert(b_blk == b_ch) by {
            assert(address - window == b_ch * (BLOCK_BYTES as int));
            lemma_div_by_multiple(b_ch, BLOCK_BYTES as int);
        }
        km.lemma_child_facts(root, l4);
        let t3 = step(treem, root, l4)->0;
        km.lemma_table_base(t3);
        km.lemma_child_facts(t3, 0);
        let t2 = step(treem, t3, 0)->0;
        km.lemma_table_base(t2);
        assert(treem.is_table(t3) && treem.is_table(t2));
        assert(t3 != child && t2 != child && root != t3 && root != t2 && t3 != t2);
        assert(linked(treem, tree2, t2, b_blk as usize, child, root));
        assert(tree2.record(root).level == treem.record(root).level);
        assert(tree2.record(t3).level == treem.record(t3).level);
        assert(tree2.record(t2).level == treem.record(t2).level);
        assert(tree2.entry(root, l4) == treem.entry(root, l4));
        assert(tree2.child_slot(root, l4) && tree2.names_child(root, l4));
        assert(step(tree2, root, l4) == Some(t3));
        assert(tree2.entry(t3, 0) == treem.entry(t3, 0));
        assert(tree2.child_slot(t3, 0) && tree2.names_child(t3, 0));
        assert(step(tree2, t3, 0) == Some(t2));

        assert forall|b: int| 0 <= b < WINDOW_BLOCKS && !#[trigger] next_tabled[b]
            implies tree2.entry(t2, b as usize).is_empty() by {
            assert(b != b_blk);
            assert(!tabled[b]);
            assert(tree2.entry(t2, b as usize) == treem.entry(t2, b as usize));
        }

        assert forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] next_tabled[b] implies {
            &&& step(tree2, t2, b as usize) is Some
            &&& forall|e: usize| #![trigger tree2.entry(step(tree2, t2, b as usize)->0, e)] e < ENTRIES ==> {
                let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                &&& window_entry_occupied(pages, state, owner, va)
                    ==> tree2.entry(step(tree2, t2, b as usize)->0, e).perm.present
                &&& !window_entry_occupied(pages, state, owner, va)
                    ==> tree2.entry(step(tree2, t2, b as usize)->0, e).is_empty()
            }
        } by {
            if b == b_blk {
                assert(tree2.child_slot(t2, b as usize));
                assert(tree2.entry(t2, b as usize) == child_entry(child));
                assert(tree2.names_child(t2, b as usize));
                assert(step(tree2, t2, b as usize) == Some(child));
                assert forall|e: usize| #![trigger tree2.entry(child, e)] e < ENTRIES implies {
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    &&& window_entry_occupied(pages, state, owner, va) ==> tree2.entry(child, e).perm.present
                    &&& !window_entry_occupied(pages, state, owner, va) ==> tree2.entry(child, e).is_empty()
                } by {
                    lemma_window_block_entry_va(window, b, e);
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    if window_entry_occupied(pages, state, owner, va) {
                        let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state[j]) && owner[j] == va;
                        assert(tabled[((owner[j] - window) as int / BLOCK_BYTES as int)]);
                        assert(false);
                    }
                    assert(tree2.entry(child, e) == treem.entry(child, e));
                    assert(km.table_pages.maps@[child].value()[e].is_empty());
                }
            } else {
                assert(tabled[b]);
                km.lemma_child_facts(t2, b as usize);
                let t1 = step(treem, t2, b as usize)->0;
                km.lemma_table_base(t1);
                assert(treem.is_table(t1));
                assert(t1 != child && t1 != t2);
                assert(tree2.entry(t2, b as usize) == treem.entry(t2, b as usize));
                assert(tree2.child_slot(t2, b as usize) && tree2.names_child(t2, b as usize));
                assert(step(tree2, t2, b as usize) == Some(t1));
                assert forall|e: usize| #![trigger tree2.entry(t1, e)] e < ENTRIES implies {
                    let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                    &&& window_entry_occupied(pages, state, owner, va) ==> tree2.entry(t1, e).perm.present
                    &&& !window_entry_occupied(pages, state, owner, va) ==> tree2.entry(t1, e).is_empty()
                } by {
                    let _ = treem.entry(t1, e);
                    assert(tree2.entry(t1, e) == treem.entry(t1, e));
                }
            }
        }
    }
}

/// Under `caller_alone` and `source_state_ready`, `retype_table_page` followed by `link` of a free order-3
/// group `group` at an unlinked path entry `(address, level)` succeeds and establishes `source_state_ready`
/// with that path entry marked linked and `group .. group + 8` marked `TAKEN`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ready_table_group(
    pre: Caller,
    mid: Caller,
    post: Caller,
    s1: AcallStep,
    s2: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state_before: Seq<u8>,
    state_after: Seq<u8>,
    owner: Seq<usize>,
    group: usize,
    address: usize,
    level: u64,
)
    requires
        pre.wf(),
        mid.wf(),
        post.wf(),
        mid.root() == pre.root(),
        post.root() == pre.root(),
        acall_steps(pre, mid, seq![s1]),
        acall_steps(mid, post, seq![s2]),
        caller_alone(pre, mid),
        caller_alone(mid, post),
        2 <= level <= 4,
        group + TABLE_PAGES <= pages,
        group as int % TABLE_PAGES as int == 0,
        state_after.len() == MAX_PAGES,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_before[group as int + k] == FREE,
        forall|k: int| 0 <= k < TABLE_PAGES as int ==> #[trigger] state_after[group as int + k] == TAKEN,
        forall|u: int|
            0 <= u < MAX_PAGES && !(group as int <= u < group as int + TABLE_PAGES as int)
                ==> #[trigger] state_after[u] == state_before[u],
        (level == 4 && !top && address == window)
            || (level == 3 && top && !middle && address == window)
            || (level == 2 && top && middle && exists|b: int|
                0 <= b < WINDOW_BLOCKS && !tabled[b] && address as int == #[trigger] window_block(window, b)),
        s1.call == (AcallCall::Retype {
            untyped,
            kind: RETYPE_TABLE_PAGE,
            base: untyped_page(memory, group as int) as u64,
            word: 0,
            level: (level - 1) as u64,
        }),
        s2.call == (AcallCall::Link {
            slot: space,
            va: address as u64,
            level,
            from: untyped,
            child: untyped_page(memory, group as int) as u64,
        }),
        source_state_ready(
            pre.kernel(),
            pre.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state_before,
            owner,
        ),
    ensures
        s1.out.status == STATUS_OK,
        s2.out.status == STATUS_OK,
        post.kernel().flush_epoch == pre.kernel().flush_epoch,
        ({
            let next_top = if level == 4 { true } else { top };
            let next_middle = if level == 3 { true } else { middle };
            let next_tabled = if level == 2 {
                tabled.update((address - window) as int / BLOCK_BYTES as int, true)
            } else {
                tabled
            };
            source_state_ready(
                post.kernel(),
                post.root(),
                space,
                untyped,
                memory,
                pages,
                slots,
                window,
                next_top,
                next_middle,
                next_tabled,
                state_after,
                owner,
            )
        }),
{
    lemma_ready_table_retyped(
        pre, mid, s1, space, untyped, memory, pages, slots, window, top, middle, tabled,
        state_before, state_after, owner, group, level,
    );
    lemma_ready_table_linked(
        mid, post, s2, space, untyped, memory, pages, slots, window, top, middle, tabled,
        state_after, owner, untyped_page(memory, group as int) as usize, address, level,
    );
}

/// `blocks_refs_changed` preserves `covered` on every tracked page.
proof fn lemma_refs_changed_covered(
    a: &verified::capability::block::BlockTable,
    b: &verified::capability::block::BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
    p: int,
)
    requires
        blocks_refs_changed(a, b, br, refs, dead),
        a.tracks(p),
    ensures
        b.covered(p) == a.covered(p),
{
    use verified::capability::block::{NUM_1G, NUM_2M};
    use verified::define::{NUM_PAGES, PAGES_PER_1G, PAGES_PER_2M};
    let r2 = verified::capability::block::region_2m(p);
    let r1 = verified::capability::block::region_1g(p);
    assert(NUM_PAGES as int == (PAGES_PER_2M as int) * (NUM_2M as int));
    assert(NUM_PAGES as int == (PAGES_PER_1G as int) * (NUM_1G as int));
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(p, PAGES_PER_2M as int, NUM_2M as int);
    vstd::arithmetic::div_mod::lemma_multiply_divide_lt(p, PAGES_PER_1G as int, NUM_1G as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(p, PAGES_PER_2M as int);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(p, PAGES_PER_1G as int);
    assert(0 <= r2 < NUM_2M as int);
    assert(0 <= r1 < NUM_1G as int);
    assert(b.regions_2m@[r2].typed == a.regions_2m@[r2].typed);
    assert(b.regions_1g@[r1].typed == a.regions_1g@[r1].typed);
}

/// Under `caller_alone` and `source_state_ready` with `state[idx] == HELD`, `top && middle && tabled[b]`,
/// and `!window_entry_occupied(pages, state, owner, addr)`, `map_page`'s steps are accepted and establish
/// `source_state_ready` with `state.update(idx, MAPPED)` and `owner.update(idx, addr)`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ready_map_page(
    pre: Caller,
    post: Caller,
    steps: Seq<AcallStep>,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
    idx: usize,
    addr: usize,
)
    requires
        pre.wf(),
        post.wf(),
        post.root() == pre.root(),
        acall_steps(pre, post, steps),
        caller_alone(pre, post),
        1 <= steps.len() <= 2,
        steps[0].out.status == STATUS_OK ==> steps.len() == 2,
        steps[0].call == (AcallCall::Inspect { at: frame_slot(slots as int, idx as int) as u64 }),
        steps.len() == 2 ==> steps[1].call == (AcallCall::Map {
            slot: space,
            va: addr as u64,
            level: PAGE_LEVEL,
            from: frame_slot(slots as int, idx as int) as u64,
            page: 0,
        }),
        idx < pages,
        state[idx as int] == HELD,
        window <= addr < window + WINDOW_BYTES,
        addr as int % PAGE_BYTES as int == 0,
        tabled[((addr - window) as int / BLOCK_BYTES as int)],
        !window_entry_occupied(pages, state, owner, addr),
        source_state_ready(
            pre.kernel(),
            pre.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            true,
            true,
            tabled,
            state,
            owner,
        ),
    ensures
        steps.len() == 2,
        acall_ok(steps),
        post.kernel().flush_epoch == pre.kernel().flush_epoch,
        source_state_ready(
            post.kernel(),
            post.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            true,
            true,
            tabled,
            state.update(idx as int, MAPPED),
            owner.update(idx as int, addr),
        ),
{
    reveal(source_state_ready);
    reveal(CapKernel::inspect_contract_fields);
    reveal(CapKernel::map_contract_fields);
    use vstd::arithmetic::div_mod::*;
    vstd::arithmetic::power2::lemma2_to64();
    lemma_acall_steps_alone(pre, post, steps);
    reveal(AcallStep::valid);

    let k0 = pre.kernel();
    let k2 = post.kernel();
    let root = pre.root();
    assert(steps[0].pre == k0 && steps[0].root == root);
    assert(steps[0].valid());

    lemma_frame_slot(slots as int, idx as int, (pages - 1) as int);
    let from_int = frame_slot(slots as int, idx as int);
    let from = from_int as usize;
    let from_u64 = from_int as u64;
    assert(from_u64 <= POSITION_INDEX_MASK);
    lemma_own_position(from_u64);
    assert(k0.view_table_at(root, None) == Some(root));
    assert(k0.table_view(root).contains_key(from));
    assert(k0.inspect_allowed(root, spec_position(from_u64)));
    assert(steps[0].out.status == STATUS_OK);
    assert(steps.len() == 2);

    let k1 = steps[0].post;
    assert(steps[1].pre == k1 && steps[1].post == k2 && steps[1].root == root);
    assert(steps[1].valid());

    // `k1` is identical to `k0` on all capability/space/block/process/epoch state.
    let v1 = k1.table_view(root);
    assert(v1 == k0.table_view(root));
    let tree0 = tree_of(&k0.table_pages, &k0.spaces);
    let tree1 = tree_of(&k1.table_pages, &k1.spaces);
    let tree2 = tree_of(&k2.table_pages, &k2.spaces);
    assert(tree1 == tree0);

    lemma_window_path(window);
    lemma_window_va_path(window, addr);
    let l4 = address_path(window as u64).l4;
    let b_blk = (addr - window) as int / BLOCK_BYTES as int;
    let e_idx = ((addr as int - window_block(window, b_blk)) / PAGE_BYTES as int) as usize;
    let path = address_path(addr as u64);
    assert(path == SpacePath { l4, l3: 0, l2: b_blk as usize, l1: e_idx });
    assert(((window_block(window, b_blk) + (e_idx as int) * (PAGE_BYTES as int)) as usize) == addr);

    let t3 = step(tree1, root, l4)->0;
    let t2 = step(tree1, t3, 0)->0;
    let t1 = step(tree1, t2, b_blk as usize)->0;
    k1.lemma_table_base(root);
    k1.lemma_child_facts(root, l4);
    k1.lemma_child_facts(t3, 0);
    k1.lemma_child_facts(t2, b_blk as usize);
    k1.lemma_table_base(t3);
    k1.lemma_table_base(t2);
    k1.lemma_table_base(t1);
    assert(walk_table(tree1, root, path) == Some(t1));
    assert(!k1.blocks.pages@[(t1 / PAGE_SZ) as int].dead);
    assert(tree1.entry(t1, e_idx).is_empty());
    assert(k1.map_fits(root, addr as u64, 1));

    lemma_own_space_cap_live(k1, root, space);
    assert(block_bytes(0) == PAGE_SZ as int);
    assert(v1[from] == frame_view(untyped_page(memory, idx as int) as usize, 0, k1.tables.node_of(root, untyped as usize)));
    assert(v1[from].rights == 7u32);
    assert(right_bit(Right::Read) == 1u32);
    assert(7u32 & 1u32 != 0) by (bit_vector);
    assert(v1[from].rights & right_bit(Right::Read) != 0);
    lemma_slot_page(k1, root, from);
    lemma_untyped_page_facts(k1, memory, pages, idx as int);
    let p_idx = (untyped_page(memory, idx as int) / PAGE_SZ as int) as usize;
    assert((untyped_page(memory, idx as int) as usize) / PAGE_SZ == p_idx);
    assert(view_frame(v1[from], 0) == p_idx);
    let br = block_ref(&k1.blocks, p_idx);
    assert(br == BlockRef::Small(p_idx));
    assert(!occupied(state[idx as int]));
    assert(frame_refs(k1, p_idx) == 1usize);
    assert(block_refs(&k1.blocks, br) == 1usize);
    assert(!block_dead(&k1.blocks, br));
    assert(k1.map_allowed(root, space as usize, addr as u64, PAGE_LEVEL, from, 0));
    assert(steps[1].out.status == STATUS_OK);
    assert forall|m: int| 0 <= m < steps.len() implies (#[trigger] steps[m]).out.status == STATUS_OK by {
        assert(m == 0 || m == 1);
    }

    let state2 = state.update(idx as int, MAPPED);
    let owner2 = owner.update(idx as int, addr);
    let v2 = k2.table_view(root);
    assert(v2 == v1);
    assert(blocks_refs_changed(&k1.blocks, &k2.blocks, br, 2usize, false));

    // `root`'s block is a `Space`/`Process` object, whereas `p_idx` is `Frame`, so `root / PAGE_SZ != p_idx`.
    assert(!k2.blocks.pages@[(root / PAGE_SZ) as int].dead) by {
        assert(verified::capability::space::space_wf(&k1.list, &k1.spaces, &k1.blocks, root));
        assert(k1.blocks.pages@[p_idx as int].object is Frame);
        assert(k1.blocks.pages@[(root / PAGE_SZ) as int].kind is Base);
        assert(!(k1.blocks.pages@[(root / PAGE_SZ) as int].object is Frame));
        let rbr = BlockRef::Small(root / PAGE_SZ);
        assert(block_typed(&k1.blocks, rbr));
        assert(rbr != br);
        assert(block_dead(&k2.blocks, rbr) == block_dead(&k1.blocks, rbr));
    }

    let nu = k1.tables.node_of(root, untyped as usize);
    k1.lemma_table_view(root, untyped as usize);
    assert(k1.tables.is_cap(&k1.list, nu));
    assert(k2.list.nodes@[nu as int].depth == k1.list.nodes@[nu as int].depth);

    assert forall|i: int| 0 <= i < pages && #[trigger] state2[i] == FREE implies {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k2.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k2.blocks.tracks(p)
        &&& k2.blocks.pages@[p].kind is Free
        &&& !k2.blocks.covered(p)
    } by {
        assert(i != idx as int);
        assert(state[i] == FREE);
        let si = frame_slot(slots as int, i) as usize;
        assert(k1.tables.has_slot(&k1.list, root, si));
        let p = memory as int / PAGE_SZ as int + i;
        assert(k2.blocks.pages@[p].kind == k1.blocks.pages@[p].kind);
        lemma_refs_changed_covered(&k1.blocks, &k2.blocks, br, 2usize, false, p);
    }

    assert forall|i: int| 0 <= i < pages && (#[trigger] state2[i] == HELD || occupied(state2[i])) implies {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& v2.contains_key(s)
        &&& v2[s] == frame_view(untyped_page(memory, i) as usize, 0, k2.tables.node_of(root, untyped as usize))
        &&& k2.list.nodes@[k2.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& k2.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&k2.blocks, p) == BlockRef::Small(p)
        &&& k2.blocks.pages@[p as int].kind is Base
        &&& k2.blocks.pages@[p as int].object is Frame
        &&& frame_refs(k2, p) == if occupied(state2[i]) { 2usize } else { 1usize }
        &&& !k2.blocks.pages@[p as int].dead
    } by {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        k1.lemma_table_view(root, s);
        let ns = k1.tables.node_of(root, s);
        assert(k1.tables.is_cap(&k1.list, ns));
        assert(k2.list.nodes@[ns as int].depth == k1.list.nodes@[ns as int].depth);
        if i == idx as int {
            assert(p == p_idx);
            assert(occupied(state2[i]));
            assert(block_ref(&k2.blocks, p_idx) == br);
            assert(frame_refs(k2, p_idx) == 2usize);
            assert(!block_dead(&k2.blocks, br));
            assert(k2.blocks.pages@[p_idx as int].kind == k1.blocks.pages@[p_idx as int].kind);
            assert(k2.blocks.pages@[p_idx as int].object == k1.blocks.pages@[p_idx as int].object);
        } else {
            assert(state[i] == state2[i]);
            lemma_slot_page(k1, root, s);
            lemma_untyped_page_facts(k1, memory, pages, i);
            assert((untyped_page(memory, i) as usize) / PAGE_SZ == p);
            assert(p as int == memory as int / PAGE_SZ as int + i);
            assert(p_idx as int == memory as int / PAGE_SZ as int + idx as int);
            assert(p != p_idx);
            assert(slot_page(k1, root, s) == p);
            let x = block_ref(&k1.blocks, p);
            assert(x == BlockRef::Small(p));
            assert(block_typed(&k1.blocks, x));
            assert(x != br);
            assert(block_ref(&k2.blocks, p) == x);
            assert(block_refs(&k2.blocks, x) == block_refs(&k1.blocks, x));
            assert(block_dead(&k2.blocks, x) == block_dead(&k1.blocks, x));
            assert(k2.blocks.pages@[p as int].kind == k1.blocks.pages@[p as int].kind);
            assert(k2.blocks.pages@[p as int].object == k1.blocks.pages@[p as int].object);
        }
    }

    assert forall|i: int| 0 <= i < pages && occupied(#[trigger] state2[i]) implies {
        &&& window <= owner2[i]
        &&& owner2[i] < window + WINDOW_BYTES
        &&& owner2[i] as int % PAGE_BYTES as int == 0
        &&& tabled[((owner2[i] - window) as int / BLOCK_BYTES as int)]
    } by {
        if i != idx as int {
            assert(occupied(state[i]) && owner2[i] == owner[i]);
        }
    }

    assert forall|i: int, j: int|
        0 <= i < pages && 0 <= j < pages && i != j
            && occupied(#[trigger] state2[i]) && occupied(#[trigger] state2[j])
            implies owner2[i] != owner2[j] by {
        if i == idx as int {
            assert(occupied(state[j]) && owner2[j] == owner[j]);
            if owner[j] == addr {
                assert(window_entry_occupied(pages, state, owner, addr));
                assert(false);
            }
        } else if j == idx as int {
            assert(occupied(state[i]) && owner2[i] == owner[i]);
            if owner[i] == addr {
                assert(window_entry_occupied(pages, state, owner, addr));
                assert(false);
            }
        } else {
            assert(occupied(state[i]) && occupied(state[j]));
        }
    }

    // Tree structure under `entry_written(tree1, tree2, t1, e_idx)`:
    assert(entry_written(tree1, tree2, t1, e_idx));
    lemma_same_tree_domains(tree1, tree2);
    assert forall|u: usize| #[trigger] tree2.record(u).level == tree1.record(u).level by {
        if u != t1 {
            assert(tree2.record(u) == tree1.record(u));
        }
    }
    assert(root != t1 && t3 != t1 && t2 != t1);
    assert(tree2.entry(root, l4) == tree1.entry(root, l4));
    assert(tree2.child_slot(root, l4) && tree2.names_child(root, l4));
    assert(step(tree2, root, l4) == Some(t3));
    assert(tree2.entry(t3, 0) == tree1.entry(t3, 0));
    assert(tree2.child_slot(t3, 0) && tree2.names_child(t3, 0));
    assert(step(tree2, t3, 0) == Some(t2));

    assert forall|b: int| 0 <= b < WINDOW_BLOCKS && !#[trigger] tabled[b]
        implies tree2.entry(t2, b as usize).is_empty() by {
        assert(tree2.entry(t2, b as usize) == tree1.entry(t2, b as usize));
    }

    assert forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] tabled[b] implies {
        &&& step(tree2, t2, b as usize) is Some
        &&& forall|e: usize| #![trigger tree2.entry(step(tree2, t2, b as usize)->0, e)] e < ENTRIES ==> {
            let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
            &&& window_entry_occupied(pages, state2, owner2, va)
                ==> tree2.entry(step(tree2, t2, b as usize)->0, e).perm.present
            &&& !window_entry_occupied(pages, state2, owner2, va)
                ==> tree2.entry(step(tree2, t2, b as usize)->0, e).is_empty()
        }
    } by {
        k1.lemma_child_facts(t2, b as usize);
        let tb = step(tree1, t2, b as usize)->0;
        k1.lemma_table_base(tb);
        assert(tb != t2);
        assert(tree2.entry(t2, b as usize) == tree1.entry(t2, b as usize));
        assert(tree2.child_slot(t2, b as usize) && tree2.names_child(t2, b as usize));
        assert(step(tree2, t2, b as usize) == Some(tb));
        if b != b_blk {
            lemma_distinct_children(k1, t2, b as usize, b_blk as usize);
            assert(tb != t1);
        }
        assert forall|e: usize| #![trigger tree2.entry(tb, e)] e < ENTRIES implies {
            let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
            &&& window_entry_occupied(pages, state2, owner2, va) ==> tree2.entry(tb, e).perm.present
            &&& !window_entry_occupied(pages, state2, owner2, va) ==> tree2.entry(tb, e).is_empty()
        } by {
            lemma_window_block_entry_va(window, b, e);
            let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
            if b == b_blk && e == e_idx {
                assert(tb == t1 && va == addr);
                assert(occupied(state2[idx as int]) && owner2[idx as int] == addr);
                assert(window_entry_occupied(pages, state2, owner2, va));
                assert(tree2.entry(t1, e_idx).perm.present);
            } else {
                assert(!(tb == t1 && e == e_idx));
                assert(va != addr) by {
                    if va == addr {
                        assert((va - window) as int / BLOCK_BYTES as int == b);
                        assert(b == b_blk);
                        assert((va as int - window_block(window, b)) / PAGE_BYTES as int == e as int);
                        assert(e == e_idx);
                    }
                }
                let _ = tree1.entry(tb, e);
                assert(tree2.entry(tb, e) == tree1.entry(tb, e));
                if window_entry_occupied(pages, state2, owner2, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state2[j]) && owner2[j] == va;
                    assert(j != idx as int);
                    assert(occupied(state[j]) && owner[j] == va);
                    assert(window_entry_occupied(pages, state, owner, va));
                }
                if window_entry_occupied(pages, state, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state[j]) && owner[j] == va;
                    assert(j != idx as int);
                    assert(occupied(state2[j]) && owner2[j] == va);
                    assert(window_entry_occupied(pages, state2, owner2, va));
                }
            }
        }
    }
}

/// Under `caller_alone`, `flush_room(pre, 1)`, `frames_held`, and `source_state_ready` with
/// `state[idx] == PARKED` and `owner[idx] == addr`, `unmap_page` succeeds, increments `flush_epoch` by 1,
/// and establishes `source_state_ready` with `state.update(idx, HELD)`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ready_unmap_page(
    pre: Caller,
    post: Caller,
    step_out: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
    frames: Map<int, (usize, Option<usize>)>,
    idx: usize,
    addr: usize,
)
    requires
        pre.wf(),
        post.wf(),
        post.root() == pre.root(),
        acall_steps(pre, post, seq![step_out]),
        caller_alone(pre, post),
        flush_room(pre, 1),
        frames_held(pre.kernel(), pre.root(), frames),
        frames.contains_key(idx as int),
        frames[idx as int] == (frame_slot(slots as int, idx as int) as usize, Some(addr)),
        idx < pages,
        state[idx as int] == PARKED,
        owner[idx as int] == addr,
        step_out.call == (AcallCall::Unmap { slot: space, va: addr as u64, level: PAGE_LEVEL }),
        source_state_ready(
            pre.kernel(),
            pre.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state,
            owner,
        ),
    ensures
        step_out.out.status == STATUS_OK,
        post.kernel().flush_epoch == pre.kernel().flush_epoch + 1,
        source_state_ready(
            post.kernel(),
            post.root(),
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state.update(idx as int, HELD),
            owner,
        ),
{
    reveal(source_state_ready);
    reveal(CapKernel::unmap_contract_fields);
    use vstd::arithmetic::div_mod::*;
    vstd::arithmetic::power2::lemma2_to64();
    lemma_acall_steps_alone(pre, post, seq![step_out]);
    assert(seq![step_out][0] == step_out);
    reveal(AcallStep::valid);
    assert(step_out.valid());

    let k0 = pre.kernel();
    let k1 = post.kernel();
    let root = pre.root();
    assert(step_out.pre == k0 && step_out.post == k1 && step_out.root == root);

    assert(occupied(state[idx as int]));
    assert(top && middle);
    lemma_window_path(window);
    lemma_window_va_path(window, addr);
    let l4 = address_path(window as u64).l4;
    let b_blk = (addr - window) as int / BLOCK_BYTES as int;
    let e_idx = ((addr as int - window_block(window, b_blk)) / PAGE_BYTES as int) as usize;
    let path = address_path(addr as u64);
    assert(path == SpacePath { l4, l3: 0, l2: b_blk as usize, l1: e_idx });
    assert(((window_block(window, b_blk) + (e_idx as int) * (PAGE_BYTES as int)) as usize) == addr);
    assert(tabled[b_blk]);

    let tree0 = tree_of(&k0.table_pages, &k0.spaces);
    let tree1 = tree_of(&k1.table_pages, &k1.spaces);
    let t3 = step(tree0, root, l4)->0;
    let t2 = step(tree0, t3, 0)->0;
    let t1 = step(tree0, t2, b_blk as usize)->0;
    k0.lemma_table_base(root);
    k0.lemma_child_facts(root, l4);
    k0.lemma_table_base(t3);
    k0.lemma_child_facts(t3, 0);
    k0.lemma_table_base(t2);
    k0.lemma_child_facts(t2, b_blk as usize);
    k0.lemma_table_base(t1);
    assert(walk_table(tree0, root, path) == Some(t1));
    assert(window_entry_occupied(pages, state, owner, addr));
    let _ = tree0.entry(t1, e_idx);
    assert(tree0.entry(t1, e_idx).perm.present);
    assert(k0.unmap_fits(root, addr as u64));
    lemma_own_space_cap_live(k0, root, space);
    assert(k0.unmap_allowed(root, space as usize, addr as u64, PAGE_LEVEL));
    assert(step_out.out.status == STATUS_OK);

    let from = frame_slot(slots as int, idx as int) as usize;
    let v0 = k0.table_view(root);
    let v1 = k1.table_view(root);
    assert(v1 == v0);
    assert(v0.contains_key(from));
    lemma_slot_page(k0, root, from);
    lemma_untyped_page_facts(k0, memory, pages, idx as int);
    let p_idx = (untyped_page(memory, idx as int) / PAGE_SZ as int) as usize;
    assert((untyped_page(memory, idx as int) as usize) / PAGE_SZ == p_idx);
    assert(slot_page(k0, root, from) == p_idx);
    assert(frame_held(k0, root, frames[idx as int]));
    assert(space_mapping(tree0, root)[path].addr / PAGE_SZ == p_idx);
    let br = block_ref(&k0.blocks, p_idx);
    assert(br == BlockRef::Small(p_idx));
    assert(frame_refs(k0, p_idx) == 2usize);
    assert(block_refs(&k0.blocks, br) == 2usize);
    assert(!block_dead(&k0.blocks, br));
    assert(blocks_refs_changed(&k0.blocks, &k1.blocks, br, 1usize, false));

    assert(!k1.blocks.pages@[(root / PAGE_SZ) as int].dead) by {
        assert(verified::capability::space::space_wf(&k0.list, &k0.spaces, &k0.blocks, root));
        assert(k0.blocks.pages@[p_idx as int].object is Frame);
        assert(k0.blocks.pages@[(root / PAGE_SZ) as int].kind is Base);
        assert(!(k0.blocks.pages@[(root / PAGE_SZ) as int].object is Frame));
        let rbr = BlockRef::Small(root / PAGE_SZ);
        assert(block_typed(&k0.blocks, rbr));
        assert(rbr != br);
        assert(block_dead(&k1.blocks, rbr) == block_dead(&k0.blocks, rbr));
    }

    k0.lemma_table_view(root, untyped as usize);
    k0.lemma_slot(root, untyped as usize);
    let nu = k0.tables.node_of(root, untyped as usize);
    k0.lemma_slot_bound(nu);
    assert(k1.list.nodes@[nu as int].depth == k0.list.nodes@[nu as int].depth);

    let state1 = state.update(idx as int, HELD);
    assert forall|i: int| 0 <= i < pages && #[trigger] state1[i] == FREE implies {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k1.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k1.blocks.tracks(p)
        &&& k1.blocks.pages@[p].kind is Free
        &&& !k1.blocks.covered(p)
    } by {
        assert(i != idx as int);
        assert(state[i] == FREE);
        let si = frame_slot(slots as int, i) as usize;
        assert(k0.tables.has_slot(&k0.list, root, si));
        let p = memory as int / PAGE_SZ as int + i;
        assert(k1.blocks.pages@[p].kind == k0.blocks.pages@[p].kind);
        lemma_refs_changed_covered(&k0.blocks, &k1.blocks, br, 1usize, false, p);
    }

    assert forall|i: int| 0 <= i < pages && (#[trigger] state1[i] == HELD || occupied(state1[i])) implies {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& v1.contains_key(s)
        &&& v1[s] == frame_view(untyped_page(memory, i) as usize, 0, k1.tables.node_of(root, untyped as usize))
        &&& k1.list.nodes@[k1.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& k1.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&k1.blocks, p) == BlockRef::Small(p)
        &&& k1.blocks.pages@[p as int].kind is Base
        &&& k1.blocks.pages@[p as int].object is Frame
        &&& frame_refs(k1, p) == if occupied(state1[i]) { 2usize } else { 1usize }
        &&& !k1.blocks.pages@[p as int].dead
    } by {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        k0.lemma_table_view(root, s);
        k0.lemma_slot(root, s);
        let ns = k0.tables.node_of(root, s);
        k0.lemma_slot_bound(ns);
        assert(k1.list.nodes@[ns as int].depth == k0.list.nodes@[ns as int].depth);
        if i == idx as int {
            assert(p == p_idx);
            assert(!occupied(state1[i]));
            assert(block_ref(&k1.blocks, p_idx) == br);
            assert(frame_refs(k1, p_idx) == 1usize);
            assert(!block_dead(&k1.blocks, br));
            assert(k1.blocks.pages@[p_idx as int].kind == k0.blocks.pages@[p_idx as int].kind);
            assert(k1.blocks.pages@[p_idx as int].object == k0.blocks.pages@[p_idx as int].object);
        } else {
            assert(state[i] == state1[i]);
            lemma_slot_page(k0, root, s);
            lemma_untyped_page_facts(k0, memory, pages, i);
            assert((untyped_page(memory, i) as usize) / PAGE_SZ == p);
            assert(p as int == memory as int / PAGE_SZ as int + i);
            assert(p_idx as int == memory as int / PAGE_SZ as int + idx as int);
            assert(p != p_idx);
            assert(slot_page(k0, root, s) == p);
            let x = block_ref(&k0.blocks, p);
            assert(x == BlockRef::Small(p));
            assert(block_typed(&k0.blocks, x));
            assert(x != br);
            assert(block_ref(&k1.blocks, p) == x);
            assert(block_refs(&k1.blocks, x) == block_refs(&k0.blocks, x));
            assert(block_dead(&k1.blocks, x) == block_dead(&k0.blocks, x));
            assert(k1.blocks.pages@[p as int].kind == k0.blocks.pages@[p as int].kind);
            assert(k1.blocks.pages@[p as int].object == k0.blocks.pages@[p as int].object);
        }
    }

    assert forall|i: int| 0 <= i < pages && occupied(#[trigger] state1[i]) implies {
        &&& window <= owner[i]
        &&& owner[i] < window + WINDOW_BYTES
        &&& owner[i] as int % PAGE_BYTES as int == 0
        &&& top
        &&& middle
        &&& tabled[((owner[i] - window) as int / BLOCK_BYTES as int)]
    } by {
        assert(i != idx as int);
        assert(occupied(state[i]));
    }

    assert forall|i: int, j: int|
        0 <= i < pages && 0 <= j < pages && i != j
            && occupied(#[trigger] state1[i]) && occupied(#[trigger] state1[j])
            implies owner[i] != owner[j] by {
        assert(i != idx as int && j != idx as int);
        assert(occupied(state[i]) && occupied(state[j]));
    }

    reveal(entries_cleared);
    lemma_same_tree_domains(tree0, tree1);
    assert forall|u: usize| #[trigger] tree1.record(u) == tree0.record(u) by {
        assert(tree1.is_page(u) == tree0.is_page(u));
    }
    assert(root != t1 && t3 != t1 && t2 != t1);
    assert(tree1.entry(root, l4) == tree0.entry(root, l4));
    assert(tree1.child_slot(root, l4) && tree1.names_child(root, l4));
    assert(step(tree1, root, l4) == Some(t3));
    assert(tree1.entry(t3, 0) == tree0.entry(t3, 0));
    assert(tree1.child_slot(t3, 0) && tree1.names_child(t3, 0));
    assert(step(tree1, t3, 0) == Some(t2));

    assert forall|b: int| 0 <= b < WINDOW_BLOCKS && !#[trigger] tabled[b]
        implies tree1.entry(t2, b as usize).is_empty() by {
        assert(tree1.entry(t2, b as usize) == tree0.entry(t2, b as usize));
    }

    assert forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] tabled[b] implies {
        &&& step(tree1, t2, b as usize) is Some
        &&& forall|e: usize| #![trigger tree1.entry(step(tree1, t2, b as usize)->0, e)] e < ENTRIES ==> {
            let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
            &&& window_entry_occupied(pages, state1, owner, va)
                ==> tree1.entry(step(tree1, t2, b as usize)->0, e).perm.present
            &&& !window_entry_occupied(pages, state1, owner, va)
                ==> tree1.entry(step(tree1, t2, b as usize)->0, e).is_empty()
        }
    } by {
        k0.lemma_child_facts(t2, b as usize);
        let tb = step(tree0, t2, b as usize)->0;
        k0.lemma_table_base(tb);
        assert(tb != t2);
        assert(tree1.entry(t2, b as usize) == tree0.entry(t2, b as usize));
        assert(tree1.child_slot(t2, b as usize) && tree1.names_child(t2, b as usize));
        assert(step(tree1, t2, b as usize) == Some(tb));
        if b != b_blk {
            lemma_distinct_children(k0, t2, b as usize, b_blk as usize);
            assert(tb != t1);
        }
        assert forall|e: usize| #![trigger tree1.entry(tb, e)] e < ENTRIES implies {
            let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
            &&& window_entry_occupied(pages, state1, owner, va) ==> tree1.entry(tb, e).perm.present
            &&& !window_entry_occupied(pages, state1, owner, va) ==> tree1.entry(tb, e).is_empty()
        } by {
            lemma_window_block_entry_va(window, b, e);
            let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
            if b == b_blk && e == e_idx {
                assert(tb == t1 && va == addr);
                assert(tree1.entry(t1, e_idx).is_empty());
                if window_entry_occupied(pages, state1, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state1[j]) && owner[j] == va;
                    assert(j != idx as int);
                    assert(occupied(state[j]) && occupied(state[idx as int]));
                    assert(owner[j] != owner[idx as int]);
                    assert(false);
                }
            } else {
                assert(!(tb == t1 && e == e_idx));
                assert(va != addr) by {
                    if va == addr {
                        assert((va - window) as int / BLOCK_BYTES as int == b);
                        assert(b == b_blk);
                        assert((va as int - window_block(window, b)) / PAGE_BYTES as int == e as int);
                        assert(e == e_idx);
                    }
                }
                let _ = tree0.entry(tb, e);
                assert(tree1.entry(tb, e) == tree0.entry(tb, e));
                if window_entry_occupied(pages, state1, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state1[j]) && owner[j] == va;
                    assert(j != idx as int);
                    assert(occupied(state[j]));
                    assert(window_entry_occupied(pages, state, owner, va));
                }
                if window_entry_occupied(pages, state, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state[j]) && owner[j] == va;
                    assert(j != idx as int);
                    assert(occupied(state1[j]));
                    assert(window_entry_occupied(pages, state1, owner, va));
                }
            }
        }
    }
}

/// Toggling a page between `MAPPED` and `PARKED` at the same owner address leaves `occupied` unchanged
/// on every page and therefore preserves `source_state_ready`.
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_ready_park_toggle(
    k: CapKernel,
    root: usize,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state: Seq<u8>,
    owner: Seq<usize>,
    idx: usize,
    new_st: u8,
)
    requires
        idx < pages,
        occupied(state[idx as int]),
        occupied(new_st),
        source_state_ready(k, root, space, untyped, memory, pages, slots, window, top, middle, tabled, state, owner),
    ensures
        source_state_ready(
            k,
            root,
            space,
            untyped,
            memory,
            pages,
            slots,
            window,
            top,
            middle,
            tabled,
            state.update(idx as int, new_st),
            owner,
        ),
{
    reveal(source_state_ready);
    let state1 = state.update(idx as int, new_st);
    assert forall|i: int| 0 <= i < pages && #[trigger] state1[i] == FREE implies {
        let p = memory as int / PAGE_SZ as int + i;
        &&& k.empty_slot(root, frame_slot(slots as int, i) as usize)
        &&& k.blocks.tracks(p)
        &&& k.blocks.pages@[p].kind is Free
        &&& !k.blocks.covered(p)
    } by {
        assert(i != idx as int);
        assert(state[i] == FREE);
    }
    assert forall|i: int| 0 <= i < pages && (#[trigger] state1[i] == HELD || occupied(state1[i])) implies {
        let s = frame_slot(slots as int, i) as usize;
        let p = (untyped_page(memory, i) / PAGE_SZ as int) as usize;
        &&& k.table_view(root).contains_key(s)
        &&& k.table_view(root)[s] == frame_view(untyped_page(memory, i) as usize, 0, k.tables.node_of(root, untyped as usize))
        &&& k.list.nodes@[k.tables.node_of(root, s) as int].depth < MAX_DEPTH
        &&& k.blocks.tracks(memory as int / PAGE_SZ as int + i)
        &&& block_ref(&k.blocks, p) == BlockRef::Small(p)
        &&& k.blocks.pages@[p as int].kind is Base
        &&& k.blocks.pages@[p as int].object is Frame
        &&& frame_refs(k, p) == if occupied(state1[i]) { 2usize } else { 1usize }
        &&& !k.blocks.pages@[p as int].dead
    } by {
        if i == idx as int {
            assert(occupied(state[idx as int]));
        } else {
            assert(state[i] == state1[i]);
        }
    }
    assert forall|i: int| 0 <= i < pages && occupied(#[trigger] state1[i]) implies {
        &&& window <= owner[i]
        &&& owner[i] < window + WINDOW_BYTES
        &&& owner[i] as int % PAGE_BYTES as int == 0
        &&& top
        &&& middle
        &&& tabled[((owner[i] - window) as int / BLOCK_BYTES as int)]
    } by {
        if i != idx as int {
            assert(occupied(state[i]));
        } else {
            assert(occupied(state[idx as int]));
        }
    }
    assert forall|i: int, j: int|
        0 <= i < pages && 0 <= j < pages && i != j
            && occupied(#[trigger] state1[i]) && occupied(#[trigger] state1[j])
            implies owner[i] != owner[j] by {
        assert(occupied(state[i]) && occupied(state[j]));
    }
    if top && middle {
        let tree = tree_of(&k.table_pages, &k.spaces);
        let t3 = step(tree, root, address_path(window as u64).l4)->0;
        let t2 = step(tree, t3, 0)->0;
        assert forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] tabled[b] implies {
            &&& step(tree, t2, b as usize) is Some
            &&& forall|e: usize| #![trigger tree.entry(step(tree, t2, b as usize)->0, e)] e < ENTRIES ==> {
                let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                &&& window_entry_occupied(pages, state1, owner, va)
                    ==> tree.entry(step(tree, t2, b as usize)->0, e).perm.present
                &&& !window_entry_occupied(pages, state1, owner, va)
                    ==> tree.entry(step(tree, t2, b as usize)->0, e).is_empty()
            }
        } by {
            let t1 = step(tree, t2, b as usize)->0;
            assert forall|e: usize| #![trigger tree.entry(t1, e)] e < ENTRIES implies {
                let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                &&& window_entry_occupied(pages, state1, owner, va) ==> tree.entry(t1, e).perm.present
                &&& !window_entry_occupied(pages, state1, owner, va) ==> tree.entry(t1, e).is_empty()
            } by {
                let va = (window_block(window, b) + (e as int) * (PAGE_BYTES as int)) as usize;
                let _ = tree.entry(t1, e);
                if window_entry_occupied(pages, state1, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state1[j]) && owner[j] == va;
                    assert(occupied(state[j]));
                    assert(window_entry_occupied(pages, state, owner, va));
                }
                if window_entry_occupied(pages, state, owner, va) {
                    let j = choose|j: int| 0 <= j < pages && occupied(#[trigger] state[j]) && owner[j] == va;
                    assert(occupied(state1[j]));
                    assert(window_entry_occupied(pages, state1, owner, va));
                }
            }
        }
    }
}

/// If `Caller` `b` equals `a` (same kernel and history), readiness on `a` is readiness on `b`.
pub(crate) proof fn lemma_same_kernel_ready(
    k: CapKernel,
    root: usize,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: Seq<bool>,
    state1: Seq<u8>,
    state2: Seq<u8>,
    owner1: Seq<usize>,
    owner2: Seq<usize>,
)
    requires
        state1 =~= state2,
        owner1 =~= owner2,
        source_state_ready(k, root, space, untyped, memory, pages, slots, window, top, middle, tabled, state1, owner1),
    ensures
        source_state_ready(k, root, space, untyped, memory, pages, slots, window, top, middle, tabled, state2, owner2),
{
    reveal(source_state_ready);
    assert(state1 == state2 && owner1 == owner2);
}

} // verus!
