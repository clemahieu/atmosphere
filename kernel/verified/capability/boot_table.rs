// SPDX-License-Identifier: MIT

//! The boot step that gives one path of the root's space its tables: for each of the level 3, 2 and 1
//! tables the walk of a path prefix does not reach yet, the next order-3 block of the root's untyped at
//! ROOT_UNTYPED_SLOT is retyped as a table page and linked through the root's process capability at
//! ROOT_PROCESS_SLOT, as every mapper pays for its tables; a table the walk reaches is reused. See
//! design/address-spaces-as-objects/, design/untyped-memory/ and design/process-holds-capabilities/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::derive::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::steps::Steps;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;

/// What a table step keeps of the capability list: its root, and every node live before, live with its
/// parent and depth. A frame capability the frame step made is such a node, so it stays the root's child.
pub open spec fn nodes_kept(a: Tree, b: Tree) -> bool {
    &&& b.seq@[0] == a.seq@[0]
    &&& forall|j: int| #![trigger b.nodes@[j]] 0 <= j < NODE_SPACE && a.nodes@[j].live ==> {
        &&& b.nodes@[j].live
        &&& b.nodes@[j].depth == a.nodes@[j].depth
        &&& b.parent@[j as usize] == a.parent@[j as usize]
    }
}

/// Two steps that each keep the list's nodes keep them together.
pub proof fn lemma_nodes_kept_trans(a: Tree, b: Tree, c: Tree)
    requires
        nodes_kept(a, b),
        nodes_kept(b, c),
    ensures
        nodes_kept(a, c),
{
    assert forall|j: int| #![trigger c.nodes@[j]] 0 <= j < NODE_SPACE && a.nodes@[j].live implies {
        &&& c.nodes@[j].live
        &&& c.nodes@[j].depth == a.nodes@[j].depth
        &&& c.parent@[j as usize] == a.parent@[j as usize]
    } by {
        assert(b.nodes@[j].live);
    }
}

/// The k-th order-3 block from the cursor.
pub open spec fn cursor_block(cursor: usize, k: int) -> usize {
    (cursor + k * TABLE_PAGE_BYTES as int) as usize
}

/// t is one of the blocks from cursor up to next, which a table step has made table pages.
pub open spec fn made_from(cursor: usize, next: usize, t: usize) -> bool {
    &&& t < next
    &&& t == cursor || t == cursor + TABLE_PAGE_BYTES || t == cursor + 2 * TABLE_PAGE_BYTES
}

/// Every table of a is a table of b, of the same kind and level, and every entry of a that names a child
/// names the same one in b, so every walk a finds, b finds.
pub open spec fn steps_kept(a: TableTree, b: TableTree) -> bool {
    &&& forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) ==> {
        &&& b.is_page(t) == a.is_page(t)
        &&& b.is_root(t) == a.is_root(t)
        &&& b.record(t).level == a.record(t).level
        &&& a.is_root(t) ==> b.space_records[t].value().kind == a.space_records[t].value().kind
    }
    &&& forall|t: usize, i: usize| #![trigger step(a, t, i)] step(a, t, i) is Some ==> b.entry(t, i) == a.entry(t, i)
}

/// So each step, and each walk to a table, that a finds is b's too.
pub proof fn lemma_steps_kept(a: TableTree, b: TableTree)
    requires
        steps_kept(a, b),
    ensures
        forall|t: usize, i: usize| #![trigger step(a, t, i)] step(a, t, i) is Some ==> step(b, t, i) == step(a, t, i),
        forall|r: usize, p: SpacePath| #![trigger walk_table(a, r, p)]
            walk_table(a, r, p) is Some ==> walk_table(b, r, p) == walk_table(a, r, p),
        forall|r: usize, p: SpacePath| #![trigger walk_large_table(a, r, p)]
            walk_large_table(a, r, p) is Some ==> walk_large_table(b, r, p) == walk_large_table(a, r, p),
{
    assert forall|t: usize, i: usize| #![trigger step(a, t, i)] step(a, t, i) is Some implies step(b, t, i) == step(a, t, i) by {
        assert(a.names_child(t, i));
        assert(a.is_table(t));
        assert(b.entry(t, i) == a.entry(t, i));
    }
    assert forall|r: usize, p: SpacePath| #![trigger walk_table(a, r, p)]
        walk_table(a, r, p) is Some implies walk_table(b, r, p) == walk_table(a, r, p) by {
        assert(a.is_table(r));
        let t3 = step(a, r, p.l4)->0;
        let t2 = step(a, t3, p.l3)->0;
        assert(step(b, r, p.l4) == step(a, r, p.l4));
        assert(step(b, t3, p.l3) == step(a, t3, p.l3));
        assert(step(b, t2, p.l2) == step(a, t2, p.l2));
    }
    assert forall|r: usize, p: SpacePath| #![trigger walk_large_table(a, r, p)]
        walk_large_table(a, r, p) is Some implies walk_large_table(b, r, p) == walk_large_table(a, r, p) by {
        assert(a.is_table(r));
        let t3 = step(a, r, p.l4)->0;
        assert(step(b, r, p.l4) == step(a, r, p.l4));
        assert(step(b, t3, p.l3) == step(a, t3, p.l3));
    }
}

/// Keeping the steps composes.
pub proof fn lemma_steps_kept_trans(a: TableTree, b: TableTree, c: TableTree)
    requires
        steps_kept(a, b),
        steps_kept(b, c),
    ensures
        steps_kept(a, c),
{
    lemma_steps_kept(a, b);
    assert forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) implies {
        &&& c.is_page(t) == a.is_page(t)
        &&& c.is_root(t) == a.is_root(t)
        &&& c.record(t).level == a.record(t).level
        &&& a.is_root(t) ==> c.space_records[t].value().kind == a.space_records[t].value().kind
    } by {
        assert(b.is_table(t));
    }
    assert forall|t: usize, i: usize| #![trigger step(a, t, i)] step(a, t, i) is Some implies c.entry(t, i) == a.entry(t, i) by {
        assert(step(b, t, i) == step(a, t, i));
    }
}

/// Two different order-3 blocks share no page.
pub proof fn lemma_blocks_apart(b: usize, c: usize)
    requires
        b % TABLE_PAGE_BYTES == 0,
        c % TABLE_PAGE_BYTES == 0,
        b != c,
    ensures
        b / PAGE_SZ + 8 <= c / PAGE_SZ || c / PAGE_SZ + 8 <= b / PAGE_SZ,
{
    assert(b / PAGE_SZ + 8 <= c / PAGE_SZ || c / PAGE_SZ + 8 <= b / PAGE_SZ) by (nonlinear_arith)
        requires
            b % TABLE_PAGE_BYTES == 0,
            c % TABLE_PAGE_BYTES == 0,
            b != c,
    {
    }
}

/// Pages under one level 4 entry: 512G.
pub const PAGES_PER_L4: usize = PAGES_PER_1G * ENTRIES;

/// The path of virtual page x of a space, level 4 first.
pub open spec fn page_path(x: int) -> SpacePath {
    SpacePath {
        l4: (x / PAGES_PER_L4 as int) as usize,
        l3: (x / PAGES_PER_1G as int % ENTRIES as int) as usize,
        l2: (x / PAGES_PER_2M as int % ENTRIES as int) as usize,
        l1: (x % ENTRIES as int) as usize,
    }
}

/// Some virtual page of the runs lies under entry l4 of a level 4 table.
pub open spec fn image_l4(runs: Seq<ImageRun>, l4: usize) -> bool {
    exists|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) && page_path(x).l4 == l4
}

/// Every virtual page of the runs lies under a level 4 entry past the kernel's: its l4 index is at least
/// KERNEL_MEM_END_L4INDEX and below 512.
pub open spec fn image_virt_wf(runs: Seq<ImageRun>) -> bool {
    forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x)
        ==> KERNEL_MEM_END_L4INDEX <= x / PAGES_PER_L4 as int && (x / PAGES_PER_L4 as int) < ENTRIES
}

/// A run's virtual pages start at or past KERNEL_MEM_END_L4INDEX's level 4 entry and end by the end of
/// the last.
pub open spec fn run_virt_wf(run: ImageRun) -> bool {
    &&& KERNEL_MEM_END_L4INDEX * PAGES_PER_L4 <= run.virt
    &&& run.virt + run.pages <= ENTRIES * PAGES_PER_L4
}

/// How many 2M regions a run's virtual pages touch.
pub open spec fn run_regions(run: ImageRun) -> int {
    (run.virt + run.pages - 1) / PAGES_PER_2M as int - run.virt as int / PAGES_PER_2M as int + 1
}

/// The tables the runs need at most: three for each 2M region a run touches, counted run by run.
pub open spec fn image_tables_bound(runs: Seq<ImageRun>) -> int
    decreases runs.len(),
{
    if runs.len() == 0 {
        0
    } else {
        image_tables_bound(runs.drop_last()) + 3 * run_regions(runs.last())
    }
}

/// How many order-3 blocks a block of memory holds.
pub open spec fn untyped_tables(p: Payload) -> int {
    block_bytes(p.order) / TABLE_PAGE_BYTES as int
}

/// The bound over the first r + 1 runs is the bound over the first r and run r's.
proof fn lemma_bound_step(runs: Seq<ImageRun>, r: int)
    requires
        0 <= r < runs.len(),
    ensures
        image_tables_bound(runs.take(r + 1)) == image_tables_bound(runs.take(r)) + 3 * run_regions(runs[r]),
{
    assert(runs.take(r + 1).drop_last() =~= runs.take(r));
    assert(runs.take(r + 1).last() == runs[r]);
}

/// A run with pages touches at least one region, so the bound over a prefix is at most the whole's.
proof fn lemma_bound_prefix(runs: Seq<ImageRun>, r: int)
    requires
        0 <= r <= runs.len(),
        forall|a: int| #![trigger runs[a]] 0 <= a < runs.len() ==> runs[a].pages > 0,
    ensures
        image_tables_bound(runs.take(r)) <= image_tables_bound(runs),
    decreases runs.len() - r,
{
    if r == runs.len() {
        assert(runs.take(r) =~= runs);
    } else {
        lemma_bound_step(runs, r);
        lemma_div_is_ordered(runs[r].virt as int, runs[r].virt + runs[r].pages - 1, PAGES_PER_2M as int);
        lemma_bound_prefix(runs, r + 1);
    }
}

/// A run whose pages start and end in range has each page's l4 index in range.
proof fn lemma_run_virt_in(runs: Seq<ImageRun>, a: int, x: int)
    requires
        0 <= a < runs.len(),
        run_virt_wf(runs[a]),
        in_virt_at(runs, a, x),
    ensures
        KERNEL_MEM_END_L4INDEX <= x / PAGES_PER_L4 as int && (x / PAGES_PER_L4 as int) < ENTRIES,
{
    lemma_div_is_ordered(PAGES_PER_L4 as int, x, PAGES_PER_L4 as int);
    lemma_div_is_ordered(x, ENTRIES * PAGES_PER_L4 - 1, PAGES_PER_L4 as int);
}

/// A run with pages whose pages do not start and end in range has a page whose l4 index is out of range.
proof fn lemma_run_virt_out(runs: Seq<ImageRun>, a: int)
    requires
        0 <= a < runs.len(),
        runs[a].pages > 0,
        !run_virt_wf(runs[a]),
    ensures
        !image_virt_wf(runs),
{
    let v = runs[a].virt as int;
    let x = if v < PAGES_PER_L4 { v } else { v + runs[a].pages - 1 };
    assert(in_virt_at(runs, a, x));
    if v >= PAGES_PER_L4 {
        lemma_div_is_ordered(ENTRIES * PAGES_PER_L4 as int, x, PAGES_PER_L4 as int);
    }
}

/// Virtual page x's path above level 1 is that of its 2M region x / PAGES_PER_2M.
proof fn lemma_page_region(x: int)
    requires
        0 <= x,
    ensures
        x / PAGES_PER_L4 as int == x / PAGES_PER_2M as int / PAGES_PER_1G as int,
        x / PAGES_PER_1G as int % ENTRIES as int == x / PAGES_PER_2M as int / ENTRIES as int % ENTRIES as int,
        x / PAGES_PER_2M as int % ENTRIES as int == x / PAGES_PER_2M as int % ENTRIES as int,
{
    lemma_div_denominator(x, PAGES_PER_2M as int, PAGES_PER_1G as int);
    lemma_div_denominator(x, PAGES_PER_2M as int, ENTRIES as int);
}

/// A 2M region q of a run whose pages lie in range lies under a level 4 entry past the kernel's.
proof fn lemma_region_l4(v: usize, n: usize, q: usize)
    requires
        n > 0,
        KERNEL_MEM_END_L4INDEX * PAGES_PER_L4 <= v,
        v + n <= ENTRIES * PAGES_PER_L4,
        v / PAGES_PER_2M <= q <= (v + n - 1) / PAGES_PER_2M as int,
    ensures
        KERNEL_MEM_END_L4INDEX <= q / PAGES_PER_1G < ENTRIES,
{
    lemma_div_is_ordered(KERNEL_MEM_END_L4INDEX * PAGES_PER_L4, v as int, PAGES_PER_2M as int);
    lemma_div_is_ordered(v as int / PAGES_PER_2M as int, q as int, PAGES_PER_1G as int);
    lemma_div_is_ordered(v + n - 1, ENTRIES * PAGES_PER_L4 - 1, PAGES_PER_2M as int);
    lemma_div_is_ordered(q as int, (ENTRIES * PAGES_PER_L4 - 1) / PAGES_PER_2M as int, PAGES_PER_1G as int);
}

/// A 2M region q that run r's virtual pages touch lies under a level 4 entry some page of the runs lies
/// under: the first page of the run's in that region.
proof fn lemma_region_image_l4(runs: Seq<ImageRun>, r: int, q: usize)
    requires
        0 <= r < runs.len(),
        runs[r].pages > 0,
        runs[r].virt as int / (PAGES_PER_2M as int) <= q <= (runs[r].virt + runs[r].pages - 1) / PAGES_PER_2M as int,
    ensures
        image_l4(runs, q / PAGES_PER_1G),
{
    let v = runs[r].virt as int;
    let e = runs[r].virt + runs[r].pages - 1;
    lemma_fundamental_div_mod(e, PAGES_PER_2M as int);
    lemma_fundamental_div_mod(v, PAGES_PER_2M as int);
    lemma_mod_bound(e, PAGES_PER_2M as int);
    lemma_mod_bound(v, PAGES_PER_2M as int);
    vstd::arithmetic::mul::lemma_mul_inequality(v / PAGES_PER_2M as int, q as int, PAGES_PER_2M as int);
    vstd::arithmetic::mul::lemma_mul_inequality(q as int, e / PAGES_PER_2M as int, PAGES_PER_2M as int);
    let x = if v <= q * PAGES_PER_2M { q * PAGES_PER_2M } else { v };
    assert(x / PAGES_PER_2M as int == q) by {
        if v <= q * PAGES_PER_2M {
            lemma_fundamental_div_mod_converse(x, PAGES_PER_2M as int, q as int, 0);
        } else {
            lemma_fundamental_div_mod_converse(v, PAGES_PER_2M as int, q as int, v - q * PAGES_PER_2M);
        }
    }
    assert(in_virt_at(runs, r, x));
    lemma_page_region(x);
    assert(page_path(x).l4 == q / PAGES_PER_1G);
}

/// The j-th order-3 block of a block of memory with at least j + 1 of them lies within it.
proof fn lemma_untyped_block(p: Payload, j: int)
    requires
        payload_wf(p),
        0 <= j < untyped_tables(p),
    ensures
        cursor_block(p.base, j) as int == p.base + j * TABLE_PAGE_BYTES as int,
        cursor_block(p.base, j) % TABLE_PAGE_BYTES == 0,
        p.base + (j + 1) * TABLE_PAGE_BYTES as int <= NODE_SPACE,
        block_within(cursor_block(p.base, j), 3, p),
{
    lemma2_to64();
    assert(block_bytes(3) == TABLE_PAGE_BYTES);
    if p.order < 3 {
        assert(block_bytes(p.order) <= PAGE_SZ * 4);
        assert(false);
    }
    let e = (p.order - 3) as nat;
    let m = pow2(e) as int;
    lemma_pow2_adds(e, 3);
    lemma_pow2_pos(e);
    assert(block_bytes(p.order) == TABLE_PAGE_BYTES as int * m) by (nonlinear_arith)
        requires
            block_bytes(p.order) == pow2(p.order as nat) as int * PAGE_SZ,
            pow2(p.order as nat) == m * 8,
    ;
    lemma_div_multiples_vanish(m, TABLE_PAGE_BYTES as int);
    assert(j < m);
    assert((j + 1) * TABLE_PAGE_BYTES as int <= TABLE_PAGE_BYTES as int * m) by (nonlinear_arith)
        requires
            j < m,
    ;
    lemma_mod_mod(p.base as int, TABLE_PAGE_BYTES as int, m);
    lemma_mod_multiples_vanish(j, p.base as int, TABLE_PAGE_BYTES as int);
}

/// Whether the runs' virtual pages all lie past the kernel's level 4 entries and the tables they need fit
/// in cap order-3 blocks: what boot_root_tables refuses for, checked without touching any state, so a
/// caller can check it before a step it must not take when the tables would be refused.
pub fn image_tables_fit(runs: &[ImageRun], cap: usize) -> (ret: bool)
    requires
        image_runs_wf(runs@),
    ensures
        ret == (image_virt_wf(runs@) && image_tables_bound(runs@) <= cap),
        ret ==> forall|a: int| #![trigger runs@[a]] 0 <= a < runs@.len() ==> run_virt_wf(runs@[a]),
{
    let mut need: usize = 0;
    let mut r: usize = 0;
    while r < runs.len()
        invariant
            r <= runs@.len(),
            image_runs_wf(runs@),
            need as int == image_tables_bound(runs@.take(r as int)),
            need <= cap,
            forall|a: int| #![trigger runs@[a]] 0 <= a < r ==> run_virt_wf(runs@[a]),
        decreases runs@.len() - r,
    {
        let v = runs[r].virt;
        let n = runs[r].pages;
        proof {
            assert(runs@[r as int].pages > 0);
        }
        if v < KERNEL_MEM_END_L4INDEX * PAGES_PER_L4 || v > ENTRIES * PAGES_PER_L4 || n > ENTRIES * PAGES_PER_L4 - v {
            proof {
                lemma_run_virt_out(runs@, r as int);
            }
            return false;
        }
        let more = 3 * ((v + n - 1) / PAGES_PER_2M - v / PAGES_PER_2M + 1);
        proof {
            lemma_bound_step(runs@, r as int);
            lemma_div_is_ordered(v as int, v + n - 1, PAGES_PER_2M as int);
        }
        if more > cap - need {
            proof {
                assert(more as int == 3 * run_regions(runs@[r as int]));
                assert(image_tables_bound(runs@.take(r as int + 1)) > cap);
                lemma_bound_prefix(runs@, r as int + 1);
            }
            return false;
        }
        need = need + more;
        r = r + 1;
    }
    proof {
        assert(runs@.take(runs@.len() as int) =~= runs@);
        assert forall|a: int, x: int| 0 <= a < runs@.len() && #[trigger] in_virt_at(runs@, a, x)
            implies KERNEL_MEM_END_L4INDEX <= x / PAGES_PER_L4 as int && (x / PAGES_PER_L4 as int) < ENTRIES by {
            assert(run_virt_wf(runs@[a]));
            lemma_run_virt_in(runs@, a, x);
        }
    }
    true
}

impl CapKernel {
    /// The space the root's process capability at ROOT_PROCESS_SLOT names.
    pub open spec fn root_space(&self, process: usize) -> usize {
        self.payload_of(self.tables.node_of(process, ROOT_PROCESS_SLOT)).base
    }

    /// The root's untyped capability at ROOT_UNTYPED_SLOT.
    pub open spec fn root_untyped(&self, process: usize) -> usize {
        self.tables.node_of(process, ROOT_UNTYPED_SLOT)
    }

    /// What a table step uses of the root's: its live table, the capability at ROOT_PROCESS_SLOT that may
    /// change its space, whose block is not dead, and the untyped at ROOT_UNTYPED_SLOT with the retype
    /// right.
    pub open spec fn root_tables_ready(&self, process: usize) -> bool {
        let n = self.tables.node_of(process, ROOT_PROCESS_SLOT);
        let u = self.root_untyped(process);
        &&& self.tables.roots@.contains_key(process)
        &&& self.root_live(process)
        &&& self.tables.has_slot(&self.list, process, ROOT_PROCESS_SLOT)
        &&& self.is_cap(n)
        &&& writes_space(self.payload_of(n))
        &&& !self.cap_dead(n)
        &&& !self.blocks.pages@[(self.root_space(process) / PAGE_SZ) as int].dead
        &&& self.tables.has_slot(&self.list, process, ROOT_UNTYPED_SLOT)
        &&& self.is_cap(u)
        &&& self.payload_of(u).kind is Untyped
        &&& self.payload_of(u).rights & right_bit(Right::Retype) != 0
        &&& self.list.nodes@[u as int].depth < MAX_DEPTH
    }

    /// The order-3 block at b lies in the root's untyped and is free, so retyping it as a table page
    /// succeeds.
    pub open spec fn root_table_block(&self, process: usize, b: usize) -> bool {
        &&& block_within(b, 3, self.payload_of(self.root_untyped(process)))
        &&& self.blocks.tracks_addr_run(b, 8)
        &&& !self.blocks.covered((b / PAGE_SZ) as int)
        &&& forall|k: int| 0 <= k < 8 ==> #[trigger] self.blocks.pages@[b / PAGE_SZ + k].kind is Free
    }

    /// A table lies in a typed block of its own; a table page is no root, and a root is its space's,
    /// at level 4.
    pub proof fn lemma_table_base(&self, t: usize)
        requires
            self.wf(),
            tree_of(&self.table_pages, &self.spaces).is_table(t),
        ensures
            self.blocks.pages@[(t / PAGE_SZ) as int].kind is Base,
            self.blocks.tracks_addr(t),
            t % TABLE_PAGE_BYTES == 0,
            tree_of(&self.table_pages, &self.spaces).is_page(t) ==> !tree_of(&self.table_pages, &self.spaces).is_root(t),
            tree_of(&self.table_pages, &self.spaces).is_root(t) ==> {
                &&& tree_of(&self.table_pages, &self.spaces).record(t).space == Some(t)
                &&& tree_of(&self.table_pages, &self.spaces).record(t).level == 4
            },
    {
        if self.table_pages.maps@.contains_key(t) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        }
        if self.spaces.roots@.contains_key(t) {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, t));
        }
    }

    /// An entry that can hold a child is present or empty, and only a level 2 table's is a large frame.
    pub proof fn lemma_entry_shape(&self, t: usize, i: usize)
        requires
            self.wf(),
            tree_of(&self.table_pages, &self.spaces).child_slot(t, i),
        ensures
            tree_of(&self.table_pages, &self.spaces).entry(t, i).perm.present
                || tree_of(&self.table_pages, &self.spaces).entry(t, i).is_empty(),
            tree_of(&self.table_pages, &self.spaces).entry(t, i).perm.present
                && tree_of(&self.table_pages, &self.spaces).entry(t, i).perm.ps
                ==> tree_of(&self.table_pages, &self.spaces).record(t).level == 2,
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        if self.table_pages.maps@.contains_key(t) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
            assert(table_record_wf(&self.table_pages, t));
            assert(self.table_pages.maps@[t].value()[i].perm.present || self.table_pages.maps@[t].value()[i].is_empty());
        } else {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, t));
            assert(root_record_wf(&self.spaces, t));
            assert(self.spaces.roots@[t].value()[i].perm.present || self.spaces.roots@[t].value()[i].is_empty());
        }
        assert(table_links_wf(tree));
        let _ = tree.entry(t, i);
    }

    /// The table an entry names is a live table page one level down, in the same space, at the address
    /// the entry holds.
    pub proof fn lemma_child_facts(&self, t: usize, i: usize)
        requires
            self.wf(),
            tree_of(&self.table_pages, &self.spaces).names_child(t, i),
        ensures
            ({
                let tree = tree_of(&self.table_pages, &self.spaces);
                let c = step(tree, t, i)->0;
                &&& step(tree, t, i) is Some
                &&& tree.is_page(c)
                &&& tree.entry(t, i).addr == c + TABLE_NODE_PAGES * PAGE_SZ
                &&& tree.record(c).level + 1 == tree.record(t).level
                &&& tree.record(c).space == tree.record(t).space
                &&& !self.blocks.pages@[(c / PAGE_SZ) as int].dead
            }),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let c = (tree.entry(t, i).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize;
        assert(table_links_wf(tree));
        let _ = tree.entry(t, i);
        assert(tree.is_page(c));
        assert(tree.record(c).parent == Some(TableParent { table: t, entry: i }));
        assert(tree.maps.contains_key(c));
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, c));
        assert(tree.entry(t, i).addr == table_addr(c));
    }

    /// A table page whose block holds a reference, or that has a parent, is live.
    pub proof fn lemma_page_alive(&self, c: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(c),
            self.blocks.pages@[(c / PAGE_SZ) as int].refs != 0 || self.table_pages.records@[c].value().parent is Some,
        ensures
            !self.blocks.pages@[(c / PAGE_SZ) as int].dead,
    {
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, c));
    }

    /// A page that is not free lies outside a free block.
    pub proof fn lemma_outside_block(&self, process: usize, b: usize, j: int)
        requires
            self.root_table_block(process, b),
            !(self.blocks.pages@[j].kind is Free),
        ensures
            !(b / PAGE_SZ <= j < b / PAGE_SZ + 8),
    {
        if b / PAGE_SZ <= j < b / PAGE_SZ + 8 {
            let k = j - b / PAGE_SZ;
            assert(self.blocks.pages@[b / PAGE_SZ + k].kind is Free);
        }
    }

    /// A step that kept the tables, the processes, the threads, the capabilities, every live node and
    /// the block of the root's space keeps what a table step uses of the root's.
    pub proof fn lemma_ready_kept(pre: Self, post: Self, process: usize)
        requires
            pre.wf(),
            pre.root_tables_ready(process),
            post.tables == pre.tables,
            post.processes == pre.processes,
            post.threads == pre.threads,
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && pre.list.nodes@[j].live
                ==> post.list.nodes@[j].live,
            post.list.nodes@[pre.root_untyped(process) as int].depth == pre.list.nodes@[pre.root_untyped(process) as int].depth,
            post.blocks.pages@[(pre.root_space(process) / PAGE_SZ) as int] == pre.blocks.pages@[(pre.root_space(process) / PAGE_SZ) as int],
        ensures
            post.root_tables_ready(process),
    {
        let n = pre.tables.node_of(process, ROOT_PROCESS_SLOT);
        let u = pre.root_untyped(process);
        pre.lemma_slot(process, ROOT_PROCESS_SLOT);
        pre.lemma_slot_bound(n);
        pre.lemma_slot(process, ROOT_UNTYPED_SLOT);
        pre.lemma_slot_bound(u);
        let ln = pre.tables.leaf(process, index_entry(ROOT_PROCESS_SLOT));
        let lu = pre.tables.leaf(process, index_entry(ROOT_UNTYPED_SLOT));
        assert(post.list.nodes@[ln as int].live);
        assert(post.list.nodes@[lu as int].live);
        assert(post.is_cap(n));
        assert(post.is_cap(u));
    }

    /// A free block outside the one a step used stays free and in the root's untyped.
    pub proof fn lemma_block_kept(pre: Self, post: Self, process: usize, b: usize, used: usize)
        requires
            pre.root_table_block(process, b),
            post.tables == pre.tables,
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            used % TABLE_PAGE_BYTES == 0,
            b != used,
            forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(used / PAGE_SZ <= j < used / PAGE_SZ + 8)
                ==> post.blocks.pages@[j] == pre.blocks.pages@[j],
        ensures
            post.root_table_block(process, b),
    {
        lemma2_to64();
        assert(block_bytes(3) == TABLE_PAGE_BYTES);
        lemma_blocks_apart(b, used);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] post.blocks.pages@[b / PAGE_SZ + k].kind is Free by {
            assert(pre.blocks.pages@[b / PAGE_SZ + k].kind is Free);
        }
    }

    /// A retype keeps the list's nodes: the node it adds was not live, so the root is still first, as
    /// the only node without a parent, and no live node's parent or depth changed.
    pub proof fn lemma_retype_nodes_kept(pre: Self, post: Self, base: usize, parent: usize)
        requires
            pre.wf(),
            post.wf(),
            !pre.list.nodes@[base as int].live,
            post.list.parent@ == pre.list.parent@.insert(base, parent),
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base
                ==> post.list.nodes@[i].live == pre.list.nodes@[i].live,
            forall|x: usize| #![trigger post.list.nodes@[x as int]] pre.list.valid(x) && x != base
                ==> post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth,
        ensures
            nodes_kept(pre.list, post.list),
    {
        let r = pre.list.seq@[0];
        pre.list.lemma_link(0);
        assert(r != base);
        assert(post.list.nodes@[r as int].live);
        assert(has(post.list.seq@, r));
        lemma_has(post.list.seq@, r);
        let k = choose|k: int| 0 <= k < post.list.seq@.len() && post.list.seq@[k] == r;
        if k > 0 {
            assert(post.list.parent@.contains_key(post.list.seq@[k]));
            assert(pre.list.parent@.contains_key(r));
        }
        assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && pre.list.nodes@[j].live implies {
            &&& post.list.nodes@[j].live
            &&& post.list.nodes@[j].depth == pre.list.nodes@[j].depth
            &&& post.list.parent@[j as usize] == pre.list.parent@[j as usize]
        } by {
            assert(j != base);
            pre.list.lemma_live_valid(j as usize);
            assert(post.list.nodes@[(j as usize) as int].depth == pre.list.nodes@[(j as usize) as int].depth);
        }
    }

    /// A frame capability the frame step made stays where it was across a step that kept the
    /// capability tables, the capabilities, their payloads and the list's nodes.
    pub proof fn lemma_frame_through_tables(pre: Self, post: Self, root: usize, process: usize, leaf2: usize, t: int, fb: (nat, nat), rights: u32)
        requires
            pre.wf(),
            post.wf(),
            pre.root_frame_at(root, process, leaf2, t, fb, rights),
            post.tables == pre.tables,
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #[trigger] post.payload_of(x) == pre.payload_of(x),
            nodes_kept(pre.list, post.list),
        ensures
            post.root_frame_at(root, process, leaf2, t, fb, rights),
    {
        let n = (leaf2 + 1 + t) as usize;
        let i = (ROOT_FRAME_SLOT + t) as usize;
        pre.lemma_slot(process, i);
        pre.lemma_slot_bound(n);
        let l = pre.tables.leaf(process, index_entry(i));
        assert(post.list.nodes@[l as int].live);
        assert(post.is_cap(n));
        let k = choose|k: int| 0 <= k < pre.list.seq@.len() && pre.list.seq@[k] == n;
        pre.list.lemma_link(k);
        assert(post.list.nodes@[n as int].live);
        assert(has(post.list.seq@, n));
        lemma_has(post.list.seq@, n);
        assert(post.list.is_child(root, n));
    }

    /// Gives entry i of the root's table t a child table at the given level: the one it names, changing
    /// nothing, or the block at the cursor, retyped as a table page under the root's untyped at
    /// ROOT_UNTYPED_SLOT and linked through the root's capability at ROOT_PROCESS_SLOT. Returns the child
    /// and whether it is the cursor's new table. The entry holds no large frame, and the cursor's block
    /// is free in the root's untyped, so it never refuses.
    #[verifier::spinoff_prover]
    pub(crate) fn boot_root_table(&mut self, process: usize, s: usize, t: usize, is_root: bool, i: usize, level: usize, cursor: usize)
        -> (ret: (usize, bool))
        requires
            old(self).wf(),
            old(self).root_tables_ready(process),
            s == old(self).root_space(process),
            old(self).root_table_block(process, cursor),
            1 <= level <= 3,
            is_root == tree_of(&old(self).table_pages, &old(self).spaces).is_root(t),
            tree_of(&old(self).table_pages, &old(self).spaces).child_slot(t, i),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).space == Some(s),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).level == level + 1,
            !old(self).blocks.pages@[(t / PAGE_SZ) as int].dead,
            !(tree_of(&old(self).table_pages, &old(self).spaces).entry(t, i).perm.present
                && tree_of(&old(self).table_pages, &old(self).spaces).entry(t, i).perm.ps),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            final(self).wf(),
            final(self).root_tables_ready(process),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).spaces.roots@.dom() == old(self).spaces.roots@.dom(),
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces.registers == old(self).spaces.registers,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(ret.1 && cursor / PAGE_SZ <= j < cursor / PAGE_SZ + 8)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && old(self).list.nodes@[j].live
                ==> final(self).list.nodes@[j].live,
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            nodes_kept(old(self).list, final(self).list),
            forall|r: ObjectId, o: ObjectId| #[trigger] final(self).view().reach(r, o) == old(self).view().reach(r, o),
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            forall|b: usize| #![trigger final(self).root_table_block(process, b)]
                old(self).root_table_block(process, b) && (!ret.1 || b != cursor) ==> final(self).root_table_block(process, b),
            steps_kept(tree_of(&old(self).table_pages, &old(self).spaces), tree_of(&final(self).table_pages, &final(self).spaces)),
            step(tree_of(&final(self).table_pages, &final(self).spaces), t, i) == Some(ret.0),
            tree_of(&final(self).table_pages, &final(self).spaces).is_page(ret.0),
            tree_of(&final(self).table_pages, &final(self).spaces).record(ret.0).level == level,
            tree_of(&final(self).table_pages, &final(self).spaces).record(ret.0).space == Some(s),
            !final(self).blocks.pages@[(ret.0 / PAGE_SZ) as int].dead,
            forall|x: usize, j: usize| #![trigger tree_of(&final(self).table_pages, &final(self).spaces).entry(x, j)]
                tree_of(&old(self).table_pages, &old(self).spaces).is_table(x) && j < ENTRIES && !(x == t && j == i)
                ==> tree_of(&final(self).table_pages, &final(self).spaces).entry(x, j)
                    == tree_of(&old(self).table_pages, &old(self).spaces).entry(x, j),
            !ret.1 ==> *final(self) == *old(self),
            ret.1 ==> {
                &&& ret.0 == cursor
                &&& final(self).table_pages.maps@.dom() == old(self).table_pages.maps@.dom().insert(cursor)
                &&& forall|j: usize| j < ENTRIES ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(cursor, j).is_empty()
            },
    {
        // The body relates three states; their invariants stay folded, and the lemmas open them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            pre.lemma_table_base(t);
            pre.lemma_entry_shape(t, i);
            assert(steps_kept(a, a));
            assert(nodes_kept(pre.list, pre.list));
        }
        let e = self.table_entry(t, is_root, i);
        if e.perm.present {
            proof {
                assert(a.names_child(t, i));
                pre.lemma_child_facts(t, i);
            }
            return ((e.addr - TABLE_NODE_PAGES * PAGE_SZ) as usize, false);
        }
        let ghost n = pre.tables.node_of(process, ROOT_PROCESS_SLOT);
        let ghost u = pre.root_untyped(process);
        proof {
            assert(a.entry(t, i).is_empty());
            lemma2_to64();
            assert(block_bytes(3) == TABLE_PAGE_BYTES);
            assert(pre.blocks.pages@[cursor / PAGE_SZ + 0].kind is Free);
            pre.lemma_free_not_table(cursor, cursor / PAGE_SZ);
            pre.lemma_slot(process, ROOT_UNTYPED_SLOT);
            pre.lemma_slot_bound(u);
            pre.lemma_slot(process, ROOT_PROCESS_SLOT);
            pre.lemma_slot_bound(n);
            assert(pre.can_retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level));
            pre.lemma_written_space(n);
            pre.lemma_table_base(s);
            pre.lemma_outside_block(process, cursor, (s / PAGE_SZ) as int);
            pre.lemma_outside_block(process, cursor, (t / PAGE_SZ) as int);
        }
        // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let retyped = self.retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level, Tracked(&mut steps));
        let ghost mid = *self;
        let ghost m = tree_of(&mid.table_pages, &mid.spaces);
        proof {
            assert(retyped);
            Self::lemma_ready_kept(pre, mid, process);
            Self::lemma_retype_nodes_kept(pre, mid, cursor, u);
            assert(m.is_table(t));
            assert(m.record(t) == a.record(t));
            assert(m.entry(t, i) == a.entry(t, i));
            assert(m.is_page(cursor));
            mid.lemma_page_alive(cursor);
            assert(mid.can_retype_under(process, ROOT_UNTYPED_SLOT, cursor, 3));
            assert(mid.can_link(process, ROOT_PROCESS_SLOT, t, i, ROOT_UNTYPED_SLOT, cursor));
        }
        let linked = self.link(process, ROOT_PROCESS_SLOT, t, i, ROOT_UNTYPED_SLOT, cursor);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            assert(linked);
            assert(Self::link_done(mid, post, t, i, cursor, s));
            assert(post.view() == mid.view());
            assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
                assert(mid.is_cap(x) == pre.is_cap(x));
            }
            assert(b.entry(t, i) == child_entry(cursor));
            assert(b.names_child(t, i));
            assert(step(b, t, i) == Some(cursor));
            assert forall|j: usize| j < ENTRIES implies #[trigger] b.entry(cursor, j).is_empty() by {
                assert(m.entry(cursor, j).is_empty());
            }
            assert(steps_kept(a, m)) by {
                assert forall|x: usize| #![trigger a.is_table(x)] a.is_table(x) implies x != cursor by {}
            }
            assert(steps_kept(m, b)) by {
                assert forall|x: usize, j: usize| #![trigger step(m, x, j)] step(m, x, j) is Some implies b.entry(x, j) == m.entry(x, j) by {
                    assert(m.names_child(x, j));
                }
            }
            lemma_steps_kept_trans(a, m, b);
            assert forall|r: usize| #[trigger] space_mapping(b, r) == space_mapping(a, r) by {
                if !pre.spaces.roots@.contains_key(r) {
                    assert(space_mapping(m, r) =~= space_mapping(a, r));
                }
            }
            assert forall|x: usize| #![trigger post.root_table_block(process, x)]
                pre.root_table_block(process, x) && x != cursor implies post.root_table_block(process, x) by {
                Self::lemma_block_kept(pre, post, process, x, cursor);
            }
            assert(post.table_pages.maps@.dom() =~= pre.table_pages.maps@.dom().insert(cursor));
            assert forall|x: usize, j: usize| #![trigger b.entry(x, j)] a.is_table(x) && j < ENTRIES && !(x == t && j == i)
                implies b.entry(x, j) == a.entry(x, j) by {
                assert(x != cursor);
                assert(m.is_table(x));
                assert(m.entry(x, j) == a.entry(x, j));
            }
        }
        (cursor, true)
    }

    /// Gives the path prefix l4, l3, l2 of the root's space its level 3, 2 and 1 tables: each one the walk
    /// already reaches is kept, and each one it does not is the next order-3 block from the cursor,
    /// retyped under the root's untyped at ROOT_UNTYPED_SLOT and linked through the root's capability at
    /// ROOT_PROCESS_SLOT. Returns the cursor past the blocks used, at most three. The prefix is past the
    /// kernel slots and maps no large frame, and the cursor's next three blocks are free in the root's
    /// untyped, so it never refuses; the caller checks that once for every path.
    #[verifier::spinoff_prover]
    pub(crate) fn boot_root_path(&mut self, process: usize, s: usize, l4: usize, l3: usize, l2: usize, cursor: usize) -> (ret: usize)
        requires
            old(self).wf(),
            old(self).root_tables_ready(process),
            s == old(self).root_space(process),
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES,
            l3 < ENTRIES,
            l2 < ENTRIES,
            cursor + 3 * TABLE_PAGE_BYTES <= old(self).blocks.page_count() * PAGE_SZ,
            forall|k: int| 0 <= k < 3 ==> #[trigger] old(self).root_table_block(process, cursor_block(cursor, k)),
            !space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), s).contains_key(SpacePath { l4, l3, l2, l1: 0 }),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            final(self).wf(),
            final(self).root_tables_ready(process),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).spaces.roots@.dom() == old(self).spaces.roots@.dom(),
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces.registers == old(self).spaces.registers,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            ret == cursor || ret == cursor + TABLE_PAGE_BYTES || ret == cursor + 2 * TABLE_PAGE_BYTES || ret == cursor + 3 * TABLE_PAGE_BYTES,
            nodes_kept(old(self).list, final(self).list),
            forall|t: usize| #[trigger] final(self).table_pages.maps@.contains_key(t)
                <==> (old(self).table_pages.maps@.contains_key(t) || made_from(cursor, ret, t)),
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(cursor / PAGE_SZ <= j < ret / PAGE_SZ)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && old(self).list.nodes@[j].live
                ==> final(self).list.nodes@[j].live,
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            forall|r: ObjectId, o: ObjectId| #[trigger] final(self).view().reach(r, o) == old(self).view().reach(r, o),
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            forall|r: usize, p: SpacePath| #![trigger walk_table(tree_of(&old(self).table_pages, &old(self).spaces), r, p)]
                walk_table(tree_of(&old(self).table_pages, &old(self).spaces), r, p) is Some
                ==> walk_table(tree_of(&final(self).table_pages, &final(self).spaces), r, p)
                    == walk_table(tree_of(&old(self).table_pages, &old(self).spaces), r, p),
            forall|r: usize, p: SpacePath| #![trigger walk_large_table(tree_of(&old(self).table_pages, &old(self).spaces), r, p)]
                walk_large_table(tree_of(&old(self).table_pages, &old(self).spaces), r, p) is Some
                ==> walk_large_table(tree_of(&final(self).table_pages, &final(self).spaces), r, p)
                    == walk_large_table(tree_of(&old(self).table_pages, &old(self).spaces), r, p),
            forall|p: SpacePath| #![trigger walk_table(tree_of(&final(self).table_pages, &final(self).spaces), s, p)]
                p.l4 == l4 && p.l3 == l3 && p.l2 == l2 ==> {
                let b = tree_of(&final(self).table_pages, &final(self).spaces);
                let t1 = walk_table(b, s, p)->0;
                &&& walk_table(b, s, p) is Some
                &&& b.is_page(t1)
                &&& b.record(t1).level == 1
                &&& b.record(t1).space == Some(s)
                &&& !final(self).blocks.pages@[(t1 / PAGE_SZ) as int].dead
            },
            forall|t: usize| #![trigger tree_of(&final(self).table_pages, &final(self).spaces).record(t)]
                final(self).table_pages.maps@.contains_key(t) && !old(self).table_pages.maps@.contains_key(t)
                && tree_of(&final(self).table_pages, &final(self).spaces).record(t).level == 1
                ==> forall|j: usize| j < ENTRIES ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(t, j).is_empty(),
            forall|j: usize| #![trigger tree_of(&final(self).table_pages, &final(self).spaces).entry(s, j)]
                j < ENTRIES && j != l4 ==> tree_of(&final(self).table_pages, &final(self).spaces).entry(s, j)
                    == tree_of(&old(self).table_pages, &old(self).spaces).entry(s, j),
    {
        // The body relates four states; their invariants stay folded, and the steps' contracts carry them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let ghost n = pre.tables.node_of(process, ROOT_PROCESS_SLOT);
        let ghost path = SpacePath { l4, l3, l2, l1: 0 };
        proof {
            pre.lemma_written_space(n);
            pre.lemma_table_base(s);
            assert(a.is_root(s));
            assert(!a.is_page(s));
            pre.lemma_entry_shape(s, l4);
            assert(pre.root_table_block(process, cursor_block(cursor, 0)));
            assert(cursor_block(cursor, 0) == cursor);
        }
        let (t3, m3) = self.boot_root_table(process, s, s, true, l4, 3, cursor);
        let ghost s1 = *self;
        let ghost b1 = tree_of(&s1.table_pages, &s1.spaces);
        let c1 = if m3 { cursor + TABLE_PAGE_BYTES } else { cursor };
        proof {
            lemma2_to64();
            assert(block_bytes(3) == TABLE_PAGE_BYTES);
            assert(pre.root_table_block(process, cursor_block(cursor, 1)));
            assert(pre.root_table_block(process, cursor_block(cursor, 2)));
            assert(s1.root_table_block(process, cursor_block(cursor, 1)));
            assert(s1.root_table_block(process, cursor_block(cursor, 2)));
            if !m3 {
                assert(s1.root_table_block(process, cursor_block(cursor, 0)));
            }
            assert(s1.root_table_block(process, c1));
            s1.lemma_table_base(t3);
            s1.lemma_entry_shape(t3, l3);
        }
        let (t2, m2) = self.boot_root_table(process, s, t3, false, l3, 2, c1);
        let ghost s2 = *self;
        let ghost b2 = tree_of(&s2.table_pages, &s2.spaces);
        let c2 = if m2 { c1 + TABLE_PAGE_BYTES } else { c1 };
        proof {
            assert(s2.root_table_block(process, cursor_block(cursor, 2)));
            if !m2 {
                assert(s2.root_table_block(process, c1));
            } else if !m3 {
                assert(s2.root_table_block(process, cursor_block(cursor, 1)));
            }
            assert(s2.root_table_block(process, c2));
            lemma_steps_kept(b1, b2);
            assert(step(b2, s, l4) == Some(t3));
            assert(space_mapping(b2, s) == space_mapping(a, s));
            assert(!space_mapping(b2, s).contains_key(path));
            s2.lemma_table_base(t2);
            assert(walk(b2, s, path) is None);
            assert(step(b2, t3, l3) == Some(t2));
            s2.lemma_entry_shape(t2, l2);
        }
        let (t1, m1) = self.boot_root_table(process, s, t2, false, l2, 1, c2);
        let c3 = if m1 { c2 + TABLE_PAGE_BYTES } else { c2 };
        proof {
            let post = *self;
            let b3 = tree_of(&post.table_pages, &post.spaces);
            lemma_nodes_kept_trans(pre.list, s1.list, s2.list);
            lemma_nodes_kept_trans(pre.list, s2.list, post.list);
            lemma_steps_kept_trans(a, b1, b2);
            lemma_steps_kept_trans(a, b2, b3);
            lemma_steps_kept(a, b3);
            lemma_steps_kept(b2, b3);
            lemma_steps_kept_trans(b1, b2, b3);
            lemma_steps_kept(b1, b3);
            assert(step(b3, s, l4) == Some(t3));
            assert(step(b3, t3, l3) == Some(t2));
            assert(step(b3, t2, l2) == Some(t1));
            assert(b3.is_root(s));
            assert forall|p: SpacePath| #![trigger walk_table(b3, s, p)] p.l4 == l4 && p.l3 == l3 && p.l2 == l2 implies {
                &&& walk_table(b3, s, p) is Some
                &&& b3.is_page(walk_table(b3, s, p)->0)
                &&& b3.record(walk_table(b3, s, p)->0).level == 1
                &&& b3.record(walk_table(b3, s, p)->0).space == Some(s)
                &&& !post.blocks.pages@[(walk_table(b3, s, p)->0 / PAGE_SZ) as int].dead
            } by {
                assert(walk_table(b3, s, p) == Some(t1));
            }
            assert forall|t: usize| #[trigger] post.table_pages.maps@.contains_key(t)
                <==> (pre.table_pages.maps@.contains_key(t) || made_from(cursor, c3, t)) by {
                if made_from(cursor, c3, t) && !pre.table_pages.maps@.contains_key(t) {
                    assert(t == cursor || t == c1 || t == c2);
                }
            }
            assert forall|t: usize| #![trigger b3.record(t)]
                post.table_pages.maps@.contains_key(t) && !pre.table_pages.maps@.contains_key(t) && b3.record(t).level == 1
                implies forall|j: usize| j < ENTRIES ==> #[trigger] b3.entry(t, j).is_empty() by {
                if m3 && t == cursor {
                    assert(b1.is_table(t3));
                    assert(b3.record(t3).level == 3);
                } else if m2 && t == c1 {
                    assert(b2.is_table(t2));
                    assert(b3.record(t2).level == 2);
                } else {
                    assert(m1 && t == c2);
                }
            }
            // Only the path's own entry of the level 4 table changes: the other two steps write below it.
            assert(b1.is_root(s));
            assert(b2.is_root(s));
            assert(s != t3);
            assert(s != t2);
            assert forall|j: usize| #![trigger b3.entry(s, j)] j < ENTRIES && j != l4 implies b3.entry(s, j) == a.entry(s, j) by {
                assert(b1.entry(s, j) == a.entry(s, j));
                assert(b2.entry(s, j) == b1.entry(s, j));
                assert(b3.entry(s, j) == b2.entry(s, j));
            }
        }
        c3
    }

    /// Every order-3 block of the root's untyped at ROOT_UNTYPED_SLOT is free, so the table step may take
    /// any of them.
    pub open spec fn root_untyped_free(&self, process: usize) -> bool {
        forall|b: usize| #[trigger] block_within(b, 3, self.payload_of(self.root_untyped(process)))
            ==> self.root_table_block(process, b)
    }

    /// The walk of a path of the root's space s to a table ends at a live level 1 table page of s.
    pub proof fn lemma_walk_table_facts(&self, s: usize, p: SpacePath)
        requires
            self.wf(),
            walk_table(tree_of(&self.table_pages, &self.spaces), s, p) is Some,
        ensures
            ({
                let b = tree_of(&self.table_pages, &self.spaces);
                let t1 = walk_table(b, s, p)->0;
                &&& b.is_page(t1)
                &&& b.record(t1).level == 1
                &&& b.record(t1).space == Some(s)
                &&& !self.blocks.pages@[(t1 / PAGE_SZ) as int].dead
            }),
    {
        let b = tree_of(&self.table_pages, &self.spaces);
        assert(b.is_root(s));
        self.lemma_table_base(s);
        let t3 = step(b, s, p.l4)->0;
        let t2 = step(b, t3, p.l3)->0;
        assert(b.names_child(s, p.l4));
        self.lemma_child_facts(s, p.l4);
        assert(b.names_child(t3, p.l3));
        self.lemma_child_facts(t3, p.l3);
        assert(b.names_child(t2, p.l2));
        self.lemma_child_facts(t2, p.l2);
    }

    /// A level 1 entry the walk reaches and finds no frame in is empty.
    pub proof fn lemma_level1_empty(&self, s: usize, p: SpacePath)
        requires
            self.wf(),
            p.l1 < ENTRIES,
            walk_table(tree_of(&self.table_pages, &self.spaces), s, p) is Some,
            tree_of(&self.table_pages, &self.spaces).is_page(walk_table(tree_of(&self.table_pages, &self.spaces), s, p)->0),
            tree_of(&self.table_pages, &self.spaces).record(walk_table(tree_of(&self.table_pages, &self.spaces), s, p)->0).level == 1,
            walk(tree_of(&self.table_pages, &self.spaces), s, p) is None,
        ensures
            tree_of(&self.table_pages, &self.spaces).entry(walk_table(tree_of(&self.table_pages, &self.spaces), s, p)->0, p.l1).is_empty(),
    {
        let b = tree_of(&self.table_pages, &self.spaces);
        let t1 = walk_table(b, s, p)->0;
        assert(frame_entry(b, t1, p.l1) is None);
        assert(!b.entry(t1, p.l1).perm.present);
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t1));
        assert(table_record_wf(&self.table_pages, t1));
        assert(self.table_pages.maps@[t1].value()[p.l1].perm.present || self.table_pages.maps@[t1].value()[p.l1].is_empty());
    }

    /// A free block at or past the blocks a step used stays free and in the root's untyped.
    pub proof fn lemma_block_past(pre: Self, post: Self, process: usize, b: usize, lo: usize, hi: usize)
        requires
            pre.root_table_block(process, b),
            post.tables == pre.tables,
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            hi <= b,
            forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(lo / PAGE_SZ <= j < hi / PAGE_SZ)
                ==> post.blocks.pages@[j] == pre.blocks.pages@[j],
        ensures
            post.root_table_block(process, b),
    {
        lemma_div_is_ordered(hi as int, b as int, PAGE_SZ as int);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] post.blocks.pages@[b / PAGE_SZ + k].kind is Free by {
            assert(pre.blocks.pages@[b / PAGE_SZ + k].kind is Free);
        }
    }

    /// The three blocks from the cursor, the k-th order-3 block of the root's untyped with at least two
    /// more after it, are free in the root's untyped and lie inside the page array.
    pub proof fn lemma_region_blocks(&self, process: usize, u: Payload, cap: int, k: int, cursor: usize)
        requires
            payload_wf(u),
            cap == untyped_tables(u),
            0 <= k,
            k + 3 <= cap,
            cursor as int == u.base + k * TABLE_PAGE_BYTES as int,
            forall|j: int| k <= j < cap ==> #[trigger] self.root_table_block(process, cursor_block(u.base, j)),
        ensures
            cursor + 3 * TABLE_PAGE_BYTES <= self.blocks.page_count() * PAGE_SZ,
            forall|i: int| 0 <= i < 3 ==> #[trigger] self.root_table_block(process, cursor_block(cursor, i)),
    {
        assert forall|i: int| 0 <= i < 3 implies #[trigger] self.root_table_block(process, cursor_block(cursor, i)) by {
            lemma_untyped_block(u, k + i);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(TABLE_PAGE_BYTES as int, k, i);
            assert(cursor_block(cursor, i) == cursor_block(u.base, k + i));
        }
        lemma_untyped_block(u, k + 2);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(TABLE_PAGE_BYTES as int, k, 2);
        let b2 = cursor_block(u.base, k + 2);
        assert(self.root_table_block(process, b2));
        lemma_mod_mod(b2 as int, PAGE_SZ as int, 8);
        lemma_fundamental_div_mod(b2 as int, PAGE_SZ as int);
    }

    /// After a path step took the blocks from the cursor, the k-th of the root's untyped, up to next,
    /// next is the k2-th, the blocks from it on stay free in the root's untyped, and the pages outside
    /// the untyped's first k2 blocks are as before the whole step.
    pub proof fn lemma_region_after(pre: Self, cur: Self, post: Self, process: usize, u: Payload, cap: int, k: int, cursor: usize, next: usize)
        -> (k2: int)
        requires
            payload_wf(u),
            cap == untyped_tables(u),
            0 <= k,
            k + 3 <= cap,
            cursor as int == u.base + k * TABLE_PAGE_BYTES as int,
            next == cursor || next == cursor + TABLE_PAGE_BYTES || next == cursor + 2 * TABLE_PAGE_BYTES || next == cursor + 3 * TABLE_PAGE_BYTES,
            forall|j: int| k <= j < cap ==> #[trigger] cur.root_table_block(process, cursor_block(u.base, j)),
            post.tables == cur.tables,
            post.blocks.regions_2m@ == cur.blocks.regions_2m@,
            post.blocks.regions_1g@ == cur.blocks.regions_1g@,
            forall|j: int| #![trigger post.blocks.pages@[j]] cur.blocks.tracks(j) && !(cursor / PAGE_SZ <= j < next / PAGE_SZ)
                ==> post.blocks.pages@[j] == cur.blocks.pages@[j],
            forall|j: int| #![trigger cur.blocks.pages@[j]] pre.blocks.tracks(j) && !(u.base / PAGE_SZ <= j < cursor / PAGE_SZ)
                ==> cur.blocks.pages@[j] == pre.blocks.pages@[j],
        ensures
            k <= k2 <= k + 3,
            next as int == u.base + k2 * TABLE_PAGE_BYTES as int,
            forall|j: int| k2 <= j < cap ==> #[trigger] post.root_table_block(process, cursor_block(u.base, j)),
            forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(u.base / PAGE_SZ <= j < next / PAGE_SZ)
                ==> post.blocks.pages@[j] == pre.blocks.pages@[j],
    {
        let k2 = if next == cursor { k } else if next == cursor + TABLE_PAGE_BYTES { k + 1 } else if next == cursor + 2 * TABLE_PAGE_BYTES { k + 2 } else { k + 3 };
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(TABLE_PAGE_BYTES as int, k, 1);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(TABLE_PAGE_BYTES as int, k, 2);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(TABLE_PAGE_BYTES as int, k, 3);
        assert forall|j: int| k2 <= j < cap implies #[trigger] post.root_table_block(process, cursor_block(u.base, j)) by {
            lemma_untyped_block(u, j);
            vstd::arithmetic::mul::lemma_mul_inequality(k2, j, TABLE_PAGE_BYTES as int);
            Self::lemma_block_past(cur, post, process, cursor_block(u.base, j), cursor, next);
        }
        assert forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(u.base / PAGE_SZ <= j < next / PAGE_SZ)
            implies post.blocks.pages@[j] == pre.blocks.pages@[j] by {
            lemma_div_is_ordered(u.base as int, cursor as int, PAGE_SZ as int);
            lemma_div_is_ordered(cursor as int, next as int, PAGE_SZ as int);
        }
        k2
    }

    /// The root's space and what its untyped at ROOT_UNTYPED_SLOT says.
    pub fn root_space_and_untyped(&self, process: usize) -> (ret: (usize, Payload))
        requires
            self.wf(),
            self.root_tables_ready(process),
        ensures
            ret.0 == self.root_space(process),
            ret.1 == self.payload_of(self.root_untyped(process)),
            payload_wf(ret.1),
    {
        proof {
            self.lemma_slot(process, ROOT_PROCESS_SLOT);
            self.lemma_slot(process, ROOT_UNTYPED_SLOT);
            assert(cap_wf(self.payload_of(self.root_untyped(process))));
        }
        let space = self.tables.lookup(&self.list, process, ROOT_PROCESS_SLOT).unwrap().1;
        let untyped = self.tables.lookup(&self.list, process, ROOT_UNTYPED_SLOT).unwrap().1;
        (space.base, untyped)
    }

    /// The step after boot_root_image that gives every 2M region dom0's runs touch in the root's space
    /// its level 3, 2 and 1 tables, by boot_root_path for each region, paid from the root's untyped at
    /// ROOT_UNTYPED_SLOT. Before any write it checks that every run's virtual pages lie under level 4
    /// entries past the kernel's, and that the untyped holds three order-3 blocks for each region a run
    /// touches, run by run; it refuses, changing nothing, when either fails. On success every page of
    /// every run walks to a level 1 table of the root's space whose entry for it is empty, and every
    /// order-3 block of the untyped past the ones the check counted is free as it was.
    #[verifier::spinoff_prover]
    pub(crate) fn boot_root_tables(&mut self, process: usize, runs: &[ImageRun]) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).root_tables_ready(process),
            old(self).root_untyped_free(process),
            image_runs_wf(runs@),
            forall|p: SpacePath| !#[trigger] space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), old(self).root_space(process)).contains_key(p),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces.registers == old(self).spaces.registers,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            !ret ==> *final(self) == *old(self),
            ret == (image_virt_wf(runs@)
                && image_tables_bound(runs@) <= untyped_tables(old(self).payload_of(old(self).root_untyped(process)))),
            ret ==> {
                let s = old(self).root_space(process);
                let u = old(self).payload_of(old(self).root_untyped(process));
                let b = tree_of(&final(self).table_pages, &final(self).spaces);
                &&& image_virt_wf(runs@)
                &&& image_tables_bound(runs@) <= untyped_tables(u)
                &&& final(self).wf()
                &&& final(self).root_tables_ready(process)
                &&& final(self).tables == old(self).tables
                &&& final(self).processes == old(self).processes
                &&& final(self).threads == old(self).threads
                &&& final(self).spaces.roots@.dom() == old(self).spaces.roots@.dom()
                &&& final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@
                &&& final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@
                &&& forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j)
                    && !(u.base / PAGE_SZ <= j < (u.base + block_bytes(u.order)) / PAGE_SZ as int)
                    ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j]
                &&& forall|j: int| image_tables_bound(runs@) <= j < untyped_tables(u)
                    ==> #[trigger] final(self).root_table_block(process, cursor_block(u.base, j))
                &&& forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && old(self).list.nodes@[j].live
                    ==> final(self).list.nodes@[j].live
                &&& forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x)
                &&& forall|x: usize| #[trigger] final(self).payload_of(x) == old(self).payload_of(x)
                &&& forall|r: ObjectId, o: ObjectId| #[trigger] final(self).view().reach(r, o) == old(self).view().reach(r, o)
                &&& forall|r: usize| #[trigger] space_mapping(b, r) == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r)
                &&& nodes_kept(old(self).list, final(self).list)
                &&& forall|root: usize, leaf2: usize, t: int, fb: (nat, nat), rights: u32|
                    #![trigger old(self).root_frame_at(root, process, leaf2, t, fb, rights)]
                    #![trigger final(self).root_frame_at(root, process, leaf2, t, fb, rights)]
                    old(self).root_frame_at(root, process, leaf2, t, fb, rights)
                    ==> final(self).root_frame_at(root, process, leaf2, t, fb, rights)
                &&& forall|a: int, x: int| 0 <= a < runs@.len() && #[trigger] in_virt_at(runs@, a, x) ==> {
                    let t1 = walk_table(b, s, page_path(x))->0;
                    &&& walk_table(b, s, page_path(x)) is Some
                    &&& b.is_page(t1)
                    &&& b.record(t1).level == 1
                    &&& b.record(t1).space == Some(s)
                    &&& !final(self).blocks.pages@[(t1 / PAGE_SZ) as int].dead
                    &&& b.entry(t1, page_path(x).l1).is_empty()
                }
                &&& forall|j: usize| j < ENTRIES && !image_l4(runs@, j)
                    ==> #[trigger] b.entry(s, j) == tree_of(&old(self).table_pages, &old(self).spaces).entry(s, j)
            },
    {
        // The invariants of the states stay folded, as do the two facts about the root's that every
        // path step carries through unopened.
        hide(CapKernel::wf);
        hide(CapKernel::root_tables_ready);
        hide(CapKernel::root_table_block);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let ghost u = pre.payload_of(pre.root_untyped(process));
        let (s, untyped) = self.root_space_and_untyped(process);
        let cap = order_bytes(untyped.order) / TABLE_PAGE_BYTES;
        // The up-front check, before any write.
        if !image_tables_fit(runs, cap) {
            return false;
        }
        proof {
            assert(cap as int == untyped_tables(u));
            assert forall|j: int| 0 <= j < cap implies #[trigger] pre.root_table_block(process, cursor_block(untyped.base, j)) by {
                lemma_untyped_block(u, j);
            }
        }
        proof {
            assert(nodes_kept(pre.list, self.list));
        }
        let mut cursor = untyped.base;
        let ghost mut k: int = 0;
        let mut r: usize = 0;
        while r < runs.len()
            invariant
                self.stale_epoch == pre.stale_epoch,
                self.flush_epoch == pre.flush_epoch,
                self.cores == pre.cores,
                self.devices == pre.devices,
                self.iommus.present == pre.iommus.present,
                r <= runs@.len(),
                image_runs_wf(runs@),
                image_virt_wf(runs@),
                forall|a: int| #![trigger runs@[a]] 0 <= a < runs@.len() ==> run_virt_wf(runs@[a]),
                s == pre.root_space(process),
                untyped == u,
                payload_wf(u),
                cap as int == untyped_tables(u),
                image_tables_bound(runs@) <= cap,
                cursor as int == u.base + k * TABLE_PAGE_BYTES as int,
                0 <= k <= image_tables_bound(runs@.take(r as int)),
                forall|j: int| k <= j < cap ==> #[trigger] self.root_table_block(process, cursor_block(u.base, j)),
                self.wf(),
                self.root_tables_ready(process),
                self.tables == pre.tables,
                self.processes == pre.processes,
                self.threads == pre.threads,
                self.spaces.roots@.dom() == pre.spaces.roots@.dom(),
                self.spaces.kernel_root == pre.spaces.kernel_root,
                self.spaces.registers == pre.spaces.registers,
                self.blocks.regions_2m@ == pre.blocks.regions_2m@,
                self.blocks.regions_1g@ == pre.blocks.regions_1g@,
                forall|j: int| #![trigger self.blocks.pages@[j]] pre.blocks.tracks(j) && !(u.base / PAGE_SZ <= j < cursor / PAGE_SZ)
                    ==> self.blocks.pages@[j] == pre.blocks.pages@[j],
                forall|j: int| #![trigger self.list.nodes@[j]] 0 <= j < NODE_SPACE && pre.list.nodes@[j].live
                    ==> self.list.nodes@[j].live,
                forall|x: usize| #[trigger] self.is_cap(x) == pre.is_cap(x),
                nodes_kept(pre.list, self.list),
                forall|r: ObjectId, o: ObjectId| #[trigger] self.view().reach(r, o) == pre.view().reach(r, o),
                forall|p: SpacePath| !#[trigger] space_mapping(a, s).contains_key(p),
                forall|r: usize| #[trigger] space_mapping(tree_of(&self.table_pages, &self.spaces), r) == space_mapping(a, r),
                forall|a: int, x: int| 0 <= a < r && #[trigger] in_virt_at(runs@, a, x)
                    ==> walk_table(tree_of(&self.table_pages, &self.spaces), s, page_path(x)) is Some,
                forall|j: usize| j < ENTRIES && !image_l4(runs@, j)
                    ==> #[trigger] tree_of(&self.table_pages, &self.spaces).entry(s, j) == a.entry(s, j),
            decreases runs@.len() - r,
        {
            let v = runs[r].virt;
            let n = runs[r].pages;
            let last = (v + n - 1) / PAGES_PER_2M;
            let mut q = v / PAGES_PER_2M;
            proof {
                assert(runs@[r as int].pages > 0);
                assert(run_virt_wf(runs@[r as int]));
                lemma_bound_step(runs@, r as int);
                lemma_bound_prefix(runs@, r as int + 1);
                lemma_div_is_ordered(v as int, v + n - 1, PAGES_PER_2M as int);
            }
            while q <= last
                invariant
                    self.stale_epoch == pre.stale_epoch,
                    self.flush_epoch == pre.flush_epoch,
                    self.cores == pre.cores,
                    self.devices == pre.devices,
                    self.iommus.present == pre.iommus.present,
                    r < runs@.len(),
                    image_runs_wf(runs@),
                    image_virt_wf(runs@),
                    forall|a: int| #![trigger runs@[a]] 0 <= a < runs@.len() ==> run_virt_wf(runs@[a]),
                    v == runs@[r as int].virt,
                    n == runs@[r as int].pages,
                    n > 0,
                    KERNEL_MEM_END_L4INDEX * PAGES_PER_L4 <= v,
                    v + n <= ENTRIES * PAGES_PER_L4,
                    last == (v + n - 1) / PAGES_PER_2M as int,
                    v as int / (PAGES_PER_2M as int) <= q <= last + 1,
                    s == pre.root_space(process),
                    untyped == u,
                    payload_wf(u),
                    cap as int == untyped_tables(u),
                    image_tables_bound(runs@.take(r as int + 1)) == image_tables_bound(runs@.take(r as int)) + 3 * run_regions(runs@[r as int]),
                    image_tables_bound(runs@.take(r as int + 1)) <= cap,
                    cursor as int == u.base + k * TABLE_PAGE_BYTES as int,
                    0 <= k <= image_tables_bound(runs@.take(r as int)) + 3 * (q - v as int / PAGES_PER_2M as int),
                    forall|j: int| k <= j < cap ==> #[trigger] self.root_table_block(process, cursor_block(u.base, j)),
                    self.wf(),
                    self.root_tables_ready(process),
                    self.tables == pre.tables,
                    self.processes == pre.processes,
                    self.threads == pre.threads,
                    self.spaces.roots@.dom() == pre.spaces.roots@.dom(),
                    self.spaces.kernel_root == pre.spaces.kernel_root,
                    self.spaces.registers == pre.spaces.registers,
                    self.blocks.regions_2m@ == pre.blocks.regions_2m@,
                    self.blocks.regions_1g@ == pre.blocks.regions_1g@,
                    forall|j: int| #![trigger self.blocks.pages@[j]] pre.blocks.tracks(j) && !(u.base / PAGE_SZ <= j < cursor / PAGE_SZ)
                        ==> self.blocks.pages@[j] == pre.blocks.pages@[j],
                    forall|j: int| #![trigger self.list.nodes@[j]] 0 <= j < NODE_SPACE && pre.list.nodes@[j].live
                        ==> self.list.nodes@[j].live,
                    forall|x: usize| #[trigger] self.is_cap(x) == pre.is_cap(x),
                    nodes_kept(pre.list, self.list),
                    forall|r: ObjectId, o: ObjectId| #[trigger] self.view().reach(r, o) == pre.view().reach(r, o),
                    forall|p: SpacePath| !#[trigger] space_mapping(a, s).contains_key(p),
                    forall|r: usize| #[trigger] space_mapping(tree_of(&self.table_pages, &self.spaces), r) == space_mapping(a, r),
                    forall|a: int, x: int| 0 <= a < r && #[trigger] in_virt_at(runs@, a, x)
                        ==> walk_table(tree_of(&self.table_pages, &self.spaces), s, page_path(x)) is Some,
                    forall|x: int| #[trigger] in_virt_at(runs@, r as int, x) && (x / PAGES_PER_2M as int) < q
                        ==> walk_table(tree_of(&self.table_pages, &self.spaces), s, page_path(x)) is Some,
                    forall|j: usize| j < ENTRIES && !image_l4(runs@, j)
                        ==> #[trigger] tree_of(&self.table_pages, &self.spaces).entry(s, j) == a.entry(s, j),
                decreases last + 1 - q,
            {
                let l4 = q / PAGES_PER_1G;
                let l3 = q / PAGES_PER_2M % ENTRIES;
                let l2 = q % ENTRIES;
                let ghost cur = *self;
                let ghost c = tree_of(&cur.table_pages, &cur.spaces);
                proof {
                    assert(k + 3 <= cap);
                    lemma_region_l4(v, n, q);
                    cur.lemma_region_blocks(process, u, cap as int, k, cursor);
                    assert(space_mapping(c, s) == space_mapping(a, s));
                    assert(!space_mapping(a, s).contains_key(SpacePath { l4, l3, l2, l1: 0 }));
                }
                let next = self.boot_root_path(process, s, l4, l3, l2, cursor);
                proof {
                    let post = *self;
                    let b = tree_of(&post.table_pages, &post.spaces);
                    let k2 = Self::lemma_region_after(pre, cur, post, process, u, cap as int, k, cursor, next);
                    lemma_nodes_kept_trans(pre.list, cur.list, post.list);
                    assert forall|aa: int, x: int| 0 <= aa < r && #[trigger] in_virt_at(runs@, aa, x)
                        implies walk_table(b, s, page_path(x)) is Some by {
                        assert(walk_table(c, s, page_path(x)) is Some);
                    }
                    assert forall|x: int| #[trigger] in_virt_at(runs@, r as int, x) && (x / PAGES_PER_2M as int) < q + 1
                        implies walk_table(b, s, page_path(x)) is Some by {
                        if (x / PAGES_PER_2M as int) < q {
                            assert(walk_table(c, s, page_path(x)) is Some);
                        } else {
                            lemma_page_region(x);
                            assert(page_path(x).l4 == l4 && page_path(x).l3 == l3 && page_path(x).l2 == l2);
                        }
                    }
                    // The region's level 4 entry is one the image reaches; every other entry stays.
                    lemma_region_image_l4(runs@, r as int, q);
                    assert forall|j: usize| j < ENTRIES && !image_l4(runs@, j) implies #[trigger] b.entry(s, j) == a.entry(s, j) by {
                        assert(j != l4);
                        assert(c.entry(s, j) == a.entry(s, j));
                    }
                    k = k2;
                }
                cursor = next;
                q = q + 1;
            }
            proof {
                assert forall|x: int| #[trigger] in_virt_at(runs@, r as int, x)
                    implies walk_table(tree_of(&self.table_pages, &self.spaces), s, page_path(x)) is Some by {
                    lemma_div_is_ordered(x, v + n - 1, PAGES_PER_2M as int);
                }
            }
            r = r + 1;
        }
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            assert(runs@.take(runs@.len() as int) =~= runs@);
            assert forall|aa: int, x: int| 0 <= aa < runs@.len() && #[trigger] in_virt_at(runs@, aa, x) implies {
                let t1 = walk_table(b, s, page_path(x))->0;
                &&& walk_table(b, s, page_path(x)) is Some
                &&& b.is_page(t1)
                &&& b.record(t1).level == 1
                &&& b.record(t1).space == Some(s)
                &&& !post.blocks.pages@[(t1 / PAGE_SZ) as int].dead
                &&& b.entry(t1, page_path(x).l1).is_empty()
            } by {
                post.lemma_walk_table_facts(s, page_path(x));
                assert(!space_mapping(a, s).contains_key(page_path(x)));
                assert(!space_mapping(b, s).contains_key(page_path(x)));
                post.lemma_level1_empty(s, page_path(x));
            }
            assert forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j)
                && !(u.base / PAGE_SZ <= j < (u.base + block_bytes(u.order)) / PAGE_SZ as int)
                implies post.blocks.pages@[j] == pre.blocks.pages@[j] by {
                lemma_div_is_ordered(cursor as int, u.base + block_bytes(u.order), PAGE_SZ as int);
            }
            assert forall|root: usize, leaf2: usize, t: int, fb: (nat, nat), rights: u32|
                #[trigger] pre.root_frame_at(root, process, leaf2, t, fb, rights)
                implies post.root_frame_at(root, process, leaf2, t, fb, rights) by {
                Self::lemma_frame_through_tables(pre, post, root, process, leaf2, t, fb, rights);
            }
        }
        true
    }
}

} // verus!
