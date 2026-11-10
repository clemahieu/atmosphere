//! The witnesses of four uses a process exists for. A creator can build a process that holds a
//! capability it chose and has a thread bound to it: from the state boot leaves, the root gives itself a
//! leaf, retypes a process and a thread bound to it, retypes a leaf into the new process's table and
//! derives an untyped into it. The root can share memory between processes it built: it retypes two
//! processes, gives each space the tables of one path, retypes a frame and maps it at that path in
//! both. It can take that memory back: one revoke of the frame capability unmaps it from both. And the
//! root can map memory into its own space: at a level 4 entry outside the kernel slots and the image's,
//! it gives its space the tables of one path, retypes a frame and maps it there. Every step is proven
//! to succeed. Only Verus compiles this module, so no image contains it.
//! See design/process-holds-capabilities/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_kernel::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::decompose::*;
use crate::capability::delete::*;
use crate::capability::derive::*;
use crate::capability::destroy::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::position::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::reclaim_process::*;
use crate::capability::reclaim_thread::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::revoke::*;
use crate::capability::space::*;
use crate::capability::steps::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;

/// The index of the root's table the new process's capability goes in: slot 1 of root entry 2, the
/// leaf the witness gives the root first.
pub const WITNESS_PROCESS_SLOT: usize = 257;

/// The index of the root's table the new thread's capability goes in: slot 2 of root entry 2.
pub const WITNESS_THREAD_SLOT: usize = 258;

/// The index of the root's table the second process's capability goes in, when the root maps one frame
/// into two processes: slot 2 of root entry 2.
pub const WITNESS_SECOND_PROCESS_SLOT: usize = 258;

/// The index of the root's table the shared frame's capability goes in: slot 3 of root entry 2.
pub const WITNESS_FRAME_SLOT: usize = 259;

/// The index of the new process's table the derived capability goes in: slot 1 of its root entry 0.
pub const WITNESS_CHILD_SLOT: usize = 1;

/// The tables the runs need are never fewer than none.
proof fn lemma_tables_bound_nonneg(runs: Seq<ImageRun>)
    ensures
        0 <= image_tables_bound(runs),
    decreases runs.len(),
{
    if runs.len() > 0 {
        lemma_tables_bound_nonneg(runs.drop_last());
        let run = runs.last();
        let v = run.virt as int;
        lemma_div_is_ordered(v - 1, v + run.pages - 1, PAGES_PER_2M as int);
        lemma_fundamental_div_mod(v, PAGES_PER_2M as int);
        lemma_fundamental_div_mod(v - 1, PAGES_PER_2M as int);
        lemma_mod_bound(v, PAGES_PER_2M as int);
        lemma_mod_bound(v - 1, PAGES_PER_2M as int);
        assert(run_regions(run) >= 0);
    }
}

/// Page k of the order-3 block at b is its k-th page, in the 2M and 1G regions its first page is in,
/// and at an even k starts an order-1 block; the next order-3 block starts 8 pages on.
proof fn lemma_block_page(b: usize, k: int)
    requires
        b % PROCESS_BYTES == 0,
        0 <= k < 8,
    ensures
        (b + k * PAGE_SZ) / PAGE_SZ as int == b / PAGE_SZ + k,
        (b + k * PAGE_SZ) % PAGE_SZ as int == 0,
        (b + PROCESS_BYTES) / PAGE_SZ as int == b / PAGE_SZ + 8,
        region_2m(b / PAGE_SZ + k) == region_2m((b / PAGE_SZ) as int),
        region_1g(b / PAGE_SZ + k) == region_1g((b / PAGE_SZ) as int),
        k % 2 == 0 ==> (b + k * PAGE_SZ) % (2 * PAGE_SZ) as int == 0,
{
    // The order-3 blocks in a 2M and in a 1G region.
    let in_2m = PAGES_PER_2M as int / 8;
    let in_1g = PAGES_PER_1G as int / 8;
    assert(PAGES_PER_2M as int == 8 * in_2m && PAGES_PER_1G as int == 8 * in_1g);
    let q = b as int / PROCESS_BYTES as int;
    lemma_fundamental_div_mod(b as int, PROCESS_BYTES as int);
    assert(b == PROCESS_BYTES as int * q);
    lemma_fundamental_div_mod_converse(b + k * PAGE_SZ, PAGE_SZ as int, 8 * q + k, 0);
    lemma_fundamental_div_mod_converse(b as int, PAGE_SZ as int, 8 * q, 0);
    lemma_fundamental_div_mod_converse(b + PROCESS_BYTES, PAGE_SZ as int, 8 * q + 8, 0);
    lemma_fundamental_div_mod(q, in_2m);
    lemma_mod_pos_bound(q, in_2m);
    let d2 = q / in_2m;
    let r2 = q % in_2m;
    assert(8 * q == d2 * PAGES_PER_2M as int + 8 * r2) by (nonlinear_arith)
        requires
            q == in_2m * d2 + r2,
            PAGES_PER_2M as int == 8 * in_2m,
    ;
    lemma_fundamental_div_mod_converse(8 * q + k, PAGES_PER_2M as int, q / in_2m, 8 * (q % in_2m) + k);
    lemma_fundamental_div_mod_converse(8 * q, PAGES_PER_2M as int, q / in_2m, 8 * (q % in_2m));
    lemma_fundamental_div_mod(q, in_1g);
    lemma_mod_pos_bound(q, in_1g);
    lemma_fundamental_div_mod_converse(8 * q + k, PAGES_PER_1G as int, q / in_1g, 8 * (q % in_1g) + k);
    lemma_fundamental_div_mod_converse(8 * q, PAGES_PER_1G as int, q / in_1g, 8 * (q % in_1g));
    if k % 2 == 0 {
        lemma_fundamental_div_mod(k, 2);
        lemma_fundamental_div_mod_converse(b + k * PAGE_SZ, (2 * PAGE_SZ) as int, 4 * q + k / 2, 0);
    }
}

/// An order-3 block aligned from b, and its first page, which an order-1 block starts at.
proof fn lemma_aligned(b: usize)
    requires
        b % PROCESS_BYTES == 0,
    ensures
        b % PAGE_SZ == 0,
        b % (2 * PAGE_SZ) as usize == 0,
{
    lemma_fundamental_div_mod(b as int, PROCESS_BYTES as int);
    lemma_fundamental_div_mod_converse(b as int, PAGE_SZ as int, 8 * (b as int / PROCESS_BYTES as int), 0);
    lemma_fundamental_div_mod_converse(b as int, (2 * PAGE_SZ) as int, 4 * (b as int / PROCESS_BYTES as int), 0);
}

/// The j-th order-3 block from b is j blocks on, aligned, and starts 8j pages on.
proof fn lemma_cursor_block(b: usize, j: int)
    requires
        b % PROCESS_BYTES == 0,
        0 <= j,
        b + j * PROCESS_BYTES <= NODE_SPACE,
    ensures
        cursor_block(b, j) == b + j * PROCESS_BYTES,
        cursor_block(b, j) % PROCESS_BYTES == 0,
        cursor_block(b, j) / PAGE_SZ == b / PAGE_SZ + 8 * j,
{
    let q = b as int / PROCESS_BYTES as int;
    lemma_fundamental_div_mod(b as int, PROCESS_BYTES as int);
    assert(b + j * PROCESS_BYTES == (q + j) * PROCESS_BYTES) by (nonlinear_arith)
        requires
            b == PROCESS_BYTES as int * q,
    ;
    lemma_fundamental_div_mod_converse(b + j * PROCESS_BYTES, PROCESS_BYTES as int, q + j, 0);
    lemma_fundamental_div_mod_converse(b + j * PROCESS_BYTES, PAGE_SZ as int, 8 * q + 8 * j, 0);
    lemma_fundamental_div_mod_converse(b as int, PAGE_SZ as int, 8 * q, 0);
}

/// Process p has a record, and it is live.
pub open spec fn witness_alive(k: CapKernel, p: usize) -> bool {
    &&& k.processes.records@.contains_key(p)
    &&& !k.processes.records@[p].value().dead
}

/// Index i of the table at root holds capability n, saying c, at depth d.
pub open spec fn witness_slot(k: CapKernel, root: usize, i: usize, n: usize, c: Payload, d: usize) -> bool {
    &&& k.slot_holds(root, i, n, c)
    &&& k.list.nodes@[n as int].depth == d
}

/// Index i of the table at root is a slot, of node n, and holds nothing.
pub open spec fn witness_empty(k: CapKernel, root: usize, i: usize, n: usize) -> bool {
    &&& k.tables.has_slot(&k.list, root, i)
    &&& k.tables.node_of(root, i) == n
    &&& !k.list.nodes@[n as int].live
}

/// The root at process: its table, its live record, and its first untyped, first, at ROOT_UNTYPED_SLOT,
/// node u, at depth 1, with the retype right.
pub open spec fn witness_root(k: CapKernel, process: usize, u: usize, first: Payload) -> bool {
    &&& k.tables.roots@.contains_key(process)
    &&& witness_alive(k, process)
    &&& witness_slot(k, process, ROOT_UNTYPED_SLOT, u, first, 1)
    &&& first.kind is Untyped
    &&& first.rights & right_bit(Right::Retype) != 0
}

/// Frame capability n's children are a and b, neither has a child, and every mapping record that names
/// page g is a child of n.
pub open spec fn frame_shared(k: CapKernel, n: usize, a: usize, b: usize, g: usize) -> bool {
    &&& forall|y: usize| #[trigger] k.list.is_child(n, y) ==> y == a || y == b
    &&& forall|z: usize| !#[trigger] k.list.is_child(a, z)
    &&& forall|z: usize| !#[trigger] k.list.is_child(b, z)
    &&& forall|m: usize| #[trigger] k.mappings@.contains_key(m) && record_pages(k.mappings@[m]).contains(g)
        ==> k.list.is_child(n, m)
}

/// The order-3 block at b lies in first and is free.
pub open spec fn witness_block(k: CapKernel, b: usize, first: Payload) -> bool {
    &&& block_within(b, 3, first)
    &&& k.blocks.tracks_addr_run(b, 8)
    &&& !k.blocks.covered((b / PAGE_SZ) as int)
    &&& forall|j: int| 0 <= j < 8 ==> #[trigger] k.blocks.pages@[b / PAGE_SZ + j].kind is Free
}

/// The order-3 blocks lo up to hi from b lie in first and are free.
pub open spec fn witness_run(k: CapKernel, b: usize, lo: int, hi: int, first: Payload) -> bool {
    forall|j: int| lo <= j < hi ==> #[trigger] witness_block(k, cursor_block(b, j), first)
}

/// A free block stays free across a step that kept the regions and every page's kind outside lo up to
/// hi, which the block lies outside.
proof fn lemma_witness_block_kept(pre: CapKernel, post: CapKernel, b: usize, first: Payload, lo: int, hi: int)
    requires
        witness_block(pre, b, first),
        post.blocks.regions_2m@ == pre.blocks.regions_2m@,
        post.blocks.regions_1g@ == pre.blocks.regions_1g@,
        forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(lo <= j < hi)
            ==> post.blocks.pages@[j].kind == pre.blocks.pages@[j].kind,
        b / PAGE_SZ + 8 <= lo || hi <= b / PAGE_SZ,
    ensures
        witness_block(post, b, first),
{
    assert forall|j: int| 0 <= j < 8 implies #[trigger] post.blocks.pages@[b / PAGE_SZ + j].kind is Free by {
        assert(pre.blocks.pages@[b / PAGE_SZ + j].kind is Free);
    }
}

/// So does a run of them, all on one side of lo up to hi.
proof fn lemma_run_kept(pre: CapKernel, post: CapKernel, b: usize, jlo: int, jhi: int, first: Payload, lo: int, hi: int)
    requires
        witness_run(pre, b, jlo, jhi, first),
        b % PROCESS_BYTES == 0,
        0 <= jlo,
        b + jhi * PROCESS_BYTES <= NODE_SPACE,
        post.blocks.regions_2m@ == pre.blocks.regions_2m@,
        post.blocks.regions_1g@ == pre.blocks.regions_1g@,
        forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(lo <= j < hi)
            ==> post.blocks.pages@[j].kind == pre.blocks.pages@[j].kind,
        hi <= b / PAGE_SZ + 8 * jlo || b / PAGE_SZ + 8 * jhi <= lo,
    ensures
        witness_run(post, b, jlo, jhi, first),
{
    assert forall|j: int| jlo <= j < jhi implies #[trigger] witness_block(post, cursor_block(b, j), first) by {
        assert(j * PROCESS_BYTES <= jhi * PROCESS_BYTES) by (nonlinear_arith)
            requires
                j <= jhi,
        ;
        lemma_cursor_block(b, j);
        lemma_witness_block_kept(pre, post, cursor_block(b, j), first, lo, hi);
    }
}

/// A slot's capability stays across a step that kept the capability tables, the capabilities and the
/// list's live nodes.
proof fn lemma_witness_slot_kept(pre: CapKernel, post: CapKernel, root: usize, i: usize, n: usize, c: Payload, d: usize)
    requires
        pre.wf(),
        post.tables == pre.tables,
        forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
        nodes_kept(pre.list, post.list),
        witness_slot(pre, root, i, n, c, d),
    ensures
        witness_slot(post, root, i, n, c, d),
{
    pre.lemma_slot(root, i);
    pre.lemma_slot_bound(n);
    assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] pre.list.nodes@[j].live implies post.list.nodes@[j].live by {}
    CapKernel::lemma_slot_stays(pre, post, root, i);
}

/// An empty slot stays empty across a step that kept the capability tables, the list's live nodes and
/// the liveness of every node that is not a page's first.
proof fn lemma_witness_empty_kept(pre: CapKernel, post: CapKernel, root: usize, i: usize, n: usize)
    requires
        pre.wf(),
        post.tables == pre.tables,
        nodes_kept(pre.list, post.list),
        forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
            ==> post.list.nodes@[j].live == pre.list.nodes@[j].live,
        witness_empty(pre, root, i, n),
    ensures
        witness_empty(post, root, i, n),
{
    pre.lemma_slot(root, i);
    pre.lemma_slot_bound(n);
    assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] pre.list.nodes@[j].live implies post.list.nodes@[j].live by {}
    CapKernel::lemma_slot_stays(pre, post, root, i);
    assert(post.list.nodes@[n as int].live == pre.list.nodes@[n as int].live);
}

/// A map adds one node, a mapping, and keeps every other: so it keeps the capabilities and the list's
/// live nodes.
proof fn lemma_map_kept(pre: CapKernel, post: CapKernel, node: usize, f: usize)
    requires
        pre.wf(),
        post.tables == pre.tables,
        !pre.list.nodes@[node as int].live,
        post.list.nodes@[node as int].kind is Mapping,
        post.list.parent@ == pre.list.parent@.insert(node, f),
        post.list.seq@[0] == pre.list.seq@[0],
        forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
            &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
            &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            &&& post.list.nodes@[i].depth == pre.list.nodes@[i].depth
        },
    ensures
        forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
        nodes_kept(pre.list, post.list),
{
    assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
        if pre.tables.owner@.contains_key(page_of(x)) && x % PAGE_SZ < NODES_PER_PAGE && x != node {
            pre.lemma_slot_bound(x);
            assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
        }
    }
    assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && pre.list.nodes@[j].live implies {
        &&& post.list.nodes@[j].live
        &&& post.list.nodes@[j].depth == pre.list.nodes@[j].depth
        &&& post.list.parent@[j as usize] == pre.list.parent@[j as usize]
    } by {
        assert(j != node);
    }
}

/// A new root, at an address no table had, keeps every step of the tables there were.
proof fn lemma_new_root_steps_kept(a: TableTree, b: TableTree, q: usize)
    requires
        b.maps == a.maps,
        b.records == a.records,
        b.roots == a.roots.insert(q, b.roots[q]),
        b.space_records == a.space_records.insert(q, b.space_records[q]),
        !a.is_table(q),
    ensures
        steps_kept(a, b),
{
    assert forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) implies {
        &&& b.is_page(t) == a.is_page(t)
        &&& b.is_root(t) == a.is_root(t)
        &&& b.record(t).level == a.record(t).level
        &&& a.is_root(t) ==> b.space_records[t].value().kind == a.space_records[t].value().kind
    } by {
        assert(t != q);
    }
    assert forall|t: usize, i: usize| #![trigger step(a, t, i)] step(a, t, i) is Some implies b.entry(t, i) == a.entry(t, i) by {
        assert(a.is_table(t));
        assert(t != q);
    }
}

/// A listed node is in the node space and live.
proof fn lemma_listed_live(t: Tree, x: usize)
    requires
        t.wf(),
        t.seq@.contains(x),
    ensures
        x < NODE_SPACE,
        t.nodes@[x as int].live,
{
    let k = choose|k: int| 0 <= k < t.seq@.len() && t.seq@[k] == x;
    t.lemma_link(k);
}

/// Across a step that keeps the first node, the liveness of every node but a and b, and the parent of
/// every other node that had one, a child of c after the step that is neither a nor b was one before:
/// it is live, so it was live and listed before, and not first, so it had its parent then.
proof fn lemma_children_kept(pre: Tree, post: Tree, a: usize, b: usize, c: usize)
    requires
        pre.wf(),
        post.wf(),
        post.seq@[0] == pre.seq@[0],
        forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != a && i != b
            ==> post.nodes@[i].live == pre.nodes@[i].live,
        forall|x: usize| x != a && x != b && #[trigger] pre.parent@.contains_key(x) ==> post.parent@[x] == pre.parent@[x],
    ensures
        forall|x: usize| #[trigger] post.is_child(c, x) && x != a && x != b ==> pre.is_child(c, x),
{
    assert forall|x: usize| #[trigger] post.is_child(c, x) && x != a && x != b implies pre.is_child(c, x) by {
        lemma_listed_live(post, x);
        assert(post.nodes@[x as int].live == pre.nodes@[x as int].live);
        assert(has(pre.seq@, x));
        lemma_has(pre.seq@, x);
        let k = choose|k: int| 0 <= k < pre.seq@.len() && pre.seq@[k] == x;
        assert(k != 0);
        assert(pre.parent@.contains_key(pre.seq@[k]));
    }
}

/// Across a step that adds n, dead before, under p and changes no other node's liveness or parent,
/// n has no child after it, and every other child after it was the same child before: a live node
/// past the first has a parent, so it was not the first before either.
proof fn lemma_added_children(pre: Tree, post: Tree, n: usize, p: usize)
    requires
        pre.wf(),
        post.wf(),
        n < NODE_SPACE,
        !pre.nodes@[n as int].live,
        p != n,
        post.parent@ == pre.parent@.insert(n, p),
        forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != n
            ==> post.nodes@[i].live == pre.nodes@[i].live,
    ensures
        forall|x: usize| !#[trigger] post.is_child(n, x),
        forall|c: usize, x: usize| #[trigger] post.is_child(c, x) && x != n ==> pre.is_child(c, x),
{
    assert forall|c: usize, x: usize| #[trigger] post.is_child(c, x) && x != n implies pre.is_child(c, x) by {
        lemma_listed_live(post, x);
        assert(post.nodes@[x as int].live == pre.nodes@[x as int].live);
        assert(has(pre.seq@, x));
        lemma_has(pre.seq@, x);
        let k = choose|k: int| 0 <= k < pre.seq@.len() && pre.seq@[k] == x;
        let j = choose|j: int| 0 <= j < post.seq@.len() && post.seq@[j] == x;
        assert(j != 0);
        assert(post.parent@.contains_key(post.seq@[j]));
        assert(pre.parent@.contains_key(x));
        if k == 0 {
            assert(!pre.parent@.contains_key(pre.seq@[0]));
        }
        assert(pre.parent@.contains_key(pre.seq@[k]));
    }
    assert forall|x: usize| !#[trigger] post.is_child(n, x) by {
        if post.is_child(n, x) {
            if x == n {
                assert(post.parent@[n] == p);
            } else {
                assert(pre.is_child(n, x));
                pre.lemma_dead_childless(n, x);
            }
        }
    }
}

/// A child stays its parent's child across a step that keeps its parent and keeps it live: it is listed,
/// since it is live, and not first, since it has a parent.
proof fn lemma_child_kept(pre: Tree, post: Tree, c: usize, x: usize)
    requires
        pre.wf(),
        post.wf(),
        pre.is_child(c, x),
        pre.parent@.contains_key(x) ==> post.parent@.contains_key(x) && post.parent@[x] == pre.parent@[x],
        x < NODE_SPACE,
        post.nodes@[x as int].live,
    ensures
        post.is_child(c, x),
{
    let k = choose|k: int| 0 <= k < pre.seq@.len() && pre.seq@[k] == x;
    assert(k != 0);
    assert(pre.parent@.contains_key(pre.seq@[k]));
    assert(has(post.seq@, x));
    lemma_has(post.seq@, x);
}

/// A live node in a leaf's page is listed and not first, since the first node lies outside every leaf:
/// so it is its parent's child, one deeper, and no deeper than the deepest.
proof fn lemma_owned_listed(k: CapKernel, x: usize)
    requires
        k.wf(),
        x < NODE_SPACE,
        k.list.nodes@[x as int].live,
        k.tables.owner@.contains_key(page_of(x)),
    ensures
        k.list.is_child(k.list.parent@[x], x),
        k.list.d(x) >= 1,
        k.list.d(x) == k.list.d(k.list.parent@[x]) + 1,
        k.list.d(x) <= MAX_DEPTH,
{
    let s = k.list.seq@;
    assert(has(s, x));
    lemma_has(s, x);
    let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
    assert(j != 0);
    assert(k.list.parent@.contains_key(s[j]));
}

/// A slot of a leaf that holds no capability is not live: a live node in a leaf's slot is a capability.
proof fn lemma_deleted_dead(k: CapKernel, n: usize)
    requires
        k.wf(),
        k.tables.owner@.contains_key(page_of(n)),
        n % PAGE_SZ != 0,
        n % PAGE_SZ < NODES_PER_PAGE,
        !k.is_cap(n),
    ensures
        !k.list.nodes@[n as int].live,
{
    if k.list.nodes@[n as int].live {
        assert(k.list.nodes@[n as int].kind is Capability);
    }
}

/// Across steps that only killed nodes and kept every parent, a child of c after them was one before.
proof fn lemma_children_back(pre: Tree, post: Tree, c: usize)
    requires
        pre.wf(),
        post.wf(),
        post.parent@ == pre.parent@,
        forall|i: int| 0 <= i < NODE_SPACE && #[trigger] post.nodes@[i].live ==> pre.nodes@[i].live,
    ensures
        forall|x: usize| #[trigger] post.is_child(c, x) ==> pre.is_child(c, x),
{
    assert forall|x: usize| #[trigger] post.is_child(c, x) implies pre.is_child(c, x) by {
        lemma_listed_live(post, x);
        assert(pre.nodes@[x as int].live);
        assert(has(pre.seq@, x));
        lemma_has(pre.seq@, x);
        let k = choose|k: int| 0 <= k < post.seq@.len() && post.seq@[k] == x;
        assert(k != 0);
        assert(post.parent@.contains_key(post.seq@[k]));
        assert(pre.parent@.contains_key(x));
    }
}

/// A leaf whose slots from 2 on are dead has no live slot from any j of at least 2 on.
proof fn lemma_live_slots_none(k: CapKernel, b: usize, j: int)
    requires
        2 <= j,
        forall|x: int| b + 2 <= x < b + NODES_PER_PAGE ==> !#[trigger] k.list.nodes@[x].live,
    ensures
        k.live_slots_from(b, j) == 0,
    decreases NODES_PER_PAGE - j,
{
    if j < NODES_PER_PAGE {
        lemma_live_slots_none(k, b, j + 1);
        assert(!k.list.nodes@[b + j].live);
    }
}

/// A slot stays a slot of the same node across a step that kept the tables and the liveness of every
/// node but n, when n cannot be the slot's leaf: n is not live, not a page's first node, or not a leaf
/// of that table.
proof fn lemma_slot_kept_but(pre: CapKernel, post: CapKernel, root: usize, i: usize, n: usize)
    requires
        pre.wf(),
        pre.tables.has_slot(&pre.list, root, i),
        post.tables == pre.tables,
        forall|j: int| 0 <= j < NODE_SPACE && j != n ==> #[trigger] post.list.nodes@[j].live == pre.list.nodes@[j].live,
        !pre.list.nodes@[n as int].live || n % PAGE_SZ != 0
            || !(pre.tables.owner@.contains_key(n) && pre.tables.owner@[n].0 == root),
    ensures
        post.tables.has_slot(&post.list, root, i),
        post.tables.node_of(root, i) == pre.tables.node_of(root, i),
{
    pre.lemma_slot(root, i);
    let node = pre.tables.node_of(root, i);
    pre.lemma_slot_bound(node);
    let leaf = pre.tables.leaf(root, index_entry(i));
    assert(leaf == page_of(node));
    assert(leaf <= node);
    if leaf == n {
        lemma_fundamental_div_mod(node as int, PAGE_SZ as int);
        lemma_mod_multiples_basic(node as int / PAGE_SZ as int, PAGE_SZ as int);
        assert(n % PAGE_SZ == 0);
    }
    assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
}

impl CapKernel {
    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of two free ones past those boot's tables took from the first untyped: retype a leaf into root
    /// entry 2 of the root's table at the second block's first two pages, a process at `base` into
    /// slot 1 of that leaf, a thread at the second block's next two pages into slot 2, bound to the
    /// process, a leaf at its next two into root entry 0 of the process's table, through the process
    /// capability, and derive an untyped over its last two pages from the root's first untyped into
    /// slot 1 of that leaf, through the process capability. Every step succeeds, and at the end the
    /// new process is not the root, holds the derived capability, the root's untyped's child, and has
    /// the thread bound to it. What a reclaim of it starts from holds too: the process block's first
    /// page and the new leaf's two are acknowledged, the thread's block holds one reference and the
    /// process's two, the capability and the binding, no core has the process's space loaded, its
    /// table has the one leaf, and the three slots hold what the steps put there. The thread
    /// capability and the derived untyped have no child, and the process capability's only child is
    /// the binding. The process is live, the thread inactive and bound to it, the flush epoch still 0,
    /// the process's space empty outside the kernel's entries, and the leaf live and hidden, owned by
    /// root entry 0 of the process's table, with no live node past its slot 1.
    pub fn witness_process_holds_capability(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
                let u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
                let child = (base + 12 * PAGE_SZ + 1) as usize;
                let thread = (base + 10 * PAGE_SZ) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& final(self).view().holds(base, child)
                &&& final(self).list.is_child(u, child)
                &&& final(self).payload_of(child) == child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1)
                &&& bound_threads(&final(self).list, &final(self).tables).contains_key(thread)
                &&& bound_threads(&final(self).list, &final(self).tables)[thread] == base
                &&& final(self).acknowledged(base / PAGE_SZ)
                &&& final(self).acknowledged(((base + 12 * PAGE_SZ) / PAGE_SZ as int) as usize)
                &&& final(self).acknowledged(((base + 12 * PAGE_SZ) / PAGE_SZ as int + 1) as usize)
                &&& block_refs(&final(self).blocks, BlockRef::Small(thread / PAGE_SZ)) == 1
                &&& block_refs(&final(self).blocks, BlockRef::Small(base / PAGE_SZ)) == 2
                &&& final(self).process_unloaded(base)
                &&& final(self).tables.leaf(base, 0) == (base + 12 * PAGE_SZ) as usize
                &&& forall|r: int| 1 <= r < ROOT_ENTRIES ==> #[trigger] final(self).tables.leaf(base, r) == NO_LEAF
                &&& final(self).slot_holds(process, WITNESS_PROCESS_SLOT, (base + 8 * PAGE_SZ + 1) as usize, process_of(base))
                &&& final(self).slot_holds(process, WITNESS_THREAD_SLOT, (base + 8 * PAGE_SZ + 2) as usize, thread_of(thread))
                &&& final(self).slot_holds(base, WITNESS_CHILD_SLOT, child, child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1))
                &&& final(self).flush_epoch == 0
                &&& witness_alive(*final(self), base)
                &&& final(self).threads.records@.contains_key(thread)
                &&& final(self).threads.records@[thread].value().state is Inactive
                &&& final(self).threads.records@[thread].value().process == Some(base)
                &&& final(self).spaces.roots@.contains_key(base)
                &&& forall|i: usize| i < ENTRIES && !holds_kernel(SpaceKind::Process, i)
                    ==> #[trigger] final(self).spaces.roots@[base].value()[i].is_empty()
                &&& final(self).list.nodes@[base + 12 * PAGE_SZ].live
                &&& final(self).list.nodes@[base + 12 * PAGE_SZ].kind is Hidden
                &&& forall|x: int| base + 12 * PAGE_SZ + 1 < x < base + 12 * PAGE_SZ + NODES_PER_PAGE ==> !#[trigger] final(self).list.nodes@[x].live
                &&& final(self).tables.owner@[(base + 12 * PAGE_SZ) as usize] == (base, 0int)
                &&& forall|c: usize| !#[trigger] final(self).list.is_child((base + 8 * PAGE_SZ + 2) as usize, c)
                &&& final(self).list.childless((base + 8 * PAGE_SZ + 2) as usize)
                &&& forall|c: usize| #[trigger] final(self).list.is_child((base + 8 * PAGE_SZ + 1) as usize, c) ==> c == thread
                &&& forall|c: usize| !#[trigger] final(self).list.is_child(child, c)
                &&& final(self).list.childless(child)
                &&& final(self).slot_holds(process, ROOT_UNTYPED_SLOT, u, first)
                &&& first.kind is Untyped
                &&& first.rights & right_bit(Right::Retype) != 0
                &&& final(self).tables.roots@.contains_key(process)
                &&& witness_alive(*final(self), process)
                &&& block_within(base, PROCESS_ORDER, first)
                &&& block_within(thread, THREAD_ORDER, first)
                &&& block_within((base + 12 * PAGE_SZ) as usize, 1, first)
                &&& final(self).blocks.tracks_addr_run(base, order_pages(PROCESS_ORDER as usize))
                &&& base + 2 * PROCESS_BYTES <= NODE_SPACE
                &&& final(self).tables.owner@.contains_key((base + 12 * PAGE_SZ) as usize)
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped, its process capability and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            let pn = (leaf@ + 1) as usize;
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            // The two free blocks, the second right after the first.
            assert(s0.root_untyped(process) == u);
            assert(s0.root_table_block(process, cursor_block(first.base, itb)));
            assert(s0.root_table_block(process, cursor_block(first.base, itb + 1)));
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 2) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(cursor_block(first.base, itb + 1) == base + PROCESS_BYTES);
            // The first untyped is the first boot block, whose pages boot left acknowledged.
            lemma_runs_blocks(free@, MAX_ORDER as nat);
            let b0 = bs[0];
            assert(b0.1 <= MAX_ORDER && b0.0 + pow2(b0.1) <= NUM_PAGES);
            assert(b0.0 * PAGE_SZ <= NUM_PAGES * PAGE_SZ) by (nonlinear_arith)
                requires
                    b0.0 <= NUM_PAGES,
            ;
            assert(first.base == b0.0 * PAGE_SZ);
            assert((b0.1 as u8) as nat == b0.1);
            assert(block_bytes(first.order) == pow2(b0.1) * PAGE_SZ);
            lemma_fundamental_div_mod_converse(base as int, PAGE_SZ as int, b0.0 + 8 * itb, 0);
            assert(base / PAGE_SZ == b0.0 + 8 * itb);
            assert(8 * itb + 16 <= pow2(b0.1)) by (nonlinear_arith)
                requires
                    PROCESS_BYTES == 8 * PAGE_SZ,
                    (itb + 2) * PROCESS_BYTES <= pow2(b0.1) * PAGE_SZ,
            ;
            assert(in_page_block(bs[0], (base / PAGE_SZ) as nat));
            assert(in_page_block(bs[0], (base / PAGE_SZ + 12) as nat));
            assert(in_page_block(bs[0], (base / PAGE_SZ + 13) as nat));
            assert(s0.acknowledged(base / PAGE_SZ));
            assert(s0.acknowledged((base / PAGE_SZ + 12) as usize));
            assert(s0.acknowledged((base / PAGE_SZ + 13) as usize));
        }
        let b2 = base + PROCESS_BYTES;
        let bt = b2 + 2 * PAGE_SZ;
        let bl = b2 + 4 * PAGE_SZ;
        let bd = b2 + 6 * PAGE_SZ;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(base % PROCESS_BYTES == 0);
            assert(b2 % PROCESS_BYTES == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            lemma_block_page(b2, 4);
            lemma_block_page(b2, 6);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == b2 / PAGE_SZ + 2);
            assert(bl / PAGE_SZ == b2 / PAGE_SZ + 4);
            assert(!s0.blocks.covered((base / PAGE_SZ) as int));
            assert(!s0.blocks.covered((b2 / PAGE_SZ) as int));
            assert(!s0.blocks.covered(b2 / PAGE_SZ + 2));
            assert(!s0.blocks.covered(b2 / PAGE_SZ + 4));
            assert forall|i: int| base / PAGE_SZ <= i < base / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[base / PAGE_SZ + (i - base / PAGE_SZ)].kind is Free);
            }
            assert forall|i: int| b2 / PAGE_SZ <= i < b2 / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[b2 / PAGE_SZ + (i - b2 / PAGE_SZ)].kind is Free);
            }
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b2, 1));
            assert(s0.blocks.small_free((b2 / PAGE_SZ) as int, 1));
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b2));
        }
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b2);
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at1, b2));
            assert(s1.tables.leaf(process, 2) == b2);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_THREAD_SLOT) && index_entry(WITNESS_THREAD_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_PROCESS_SLOT) as int].live);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_THREAD_SLOT) as int].live);
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == b2 + 1);
            assert(s1.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(s1.root_live(process));
            assert forall|i: int| base / PAGE_SZ <= i < base / PAGE_SZ + 8 || b2 / PAGE_SZ + 2 <= i < b2 / PAGE_SZ + 8
                implies #[trigger] s1.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.tracks(i));
                assert(s0.blocks.pages@[i].kind is Free);
            }
        }

        // A process, in slot 1 of that leaf.
        proof {
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(s1.blocks.pages@[(base / PAGE_SZ + k) as int].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base);
        let ghost s2 = *self;
        let ghost np = (b2 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None));
            assert(s2.tables.roots@.contains_key(base));
            assert(s2.processes.records@.contains_key(base));
            assert(!s2.processes.records@[base].value().dead);
            assert(s2.payload_of(np) == process_of(base));
            assert(s2.payload_of(np).rights & right_bit(Right::Control) != 0);
            assert(s2.list.nodes@[np as int].depth == 2);
            assert(s2.view().holds(process, np));
            assert(s2.is_cap(np));
            // The root's table keeps its new leaf, which the new process's table lacks, so the two differ.
            assert(s1.tables.roots@.contains_key(process));
            assert(s2.tables.leaf(process, 2) == b2);
            assert(s2.tables.leaf(base, 2) == NO_LEAF);
            assert(base != process);
            // The untyped, the thread's slot and the root's record stay.
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.is_cap(u));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s2.is_cap(u) && s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(!s2.list.nodes@[(b2 + 2) as int].live);
            assert(s1.processes.records@.contains_key(process));
            assert(s2.processes.records@.contains_key(process));
            assert(s2.root_live(process));
            assert(s2.tables.roots@.contains_key(process));
            assert forall|i: int| b2 / PAGE_SZ + 2 <= i < b2 / PAGE_SZ + 8 implies #[trigger] s2.blocks.pages@[i].kind is Free by {
                assert(s1.blocks.tracks(i));
                assert(s1.blocks.pages@[i].kind is Free);
            }
            // The process capability was not live before its retype, so it has no child after it.
            assert(s1.list.wf() && s2.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(!s1.list.nodes@[np as int].live);
            assert(s1.list.nodes@[u as int].live);
            assert(u != np);
            assert(s2.list.parent@ == s1.list.parent@.insert(np, u));
            assert forall|x: usize| x != np && x != np && #[trigger] s1.list.parent@.contains_key(x)
                implies s2.list.parent@[x] == s1.list.parent@[x] by {}
            lemma_children_kept(s1.list, s2.list, np, np, np);
            assert forall|x: usize| !#[trigger] s2.list.is_child(np, x) by {
                if s2.list.is_child(np, x) && x != np {
                    s1.list.lemma_dead_childless(np, x);
                }
            }
        }

        // A thread, in slot 2 of the root's leaf, bound to the process.
        proof {
            assert(block_refs(&s2.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(!s2.cap_dead(np));
            assert(s2.can_hold_thread(process, WITNESS_PROCESS_SLOT));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(s2.blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s2.blocks.pages@[bt / PAGE_SZ + k].kind is Free by {
                    assert(s2.blocks.pages@[(b2 / PAGE_SZ + 2 + k) as int].kind is Free);
                }
            }
            assert(s2.can_retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT));
        }
        let ok3 = self.retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT);
        let ghost s3 = *self;
        proof {
            assert(ok3);
            assert(s2.payload_of(s2.tables.node_of(process, WITNESS_PROCESS_SLOT)).base == base);
            // The thread holds one reference on its block and one on the process's, which the process
            // capability holds the other of; no core has the process's space loaded.
            assert(block_refs(&s3.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(block_refs(&s3.blocks, BlockRef::Small(bt / PAGE_SZ)) == 1);
            assert(s3.process_unloaded(base));
            assert(bound_threads(&s3.list, &s3.tables) == bound_threads(&s2.list, &s2.tables).insert(bt, base));
            assert(Self::retype_keeps(s2, s3, (b2 + 2) as usize, (bt / PAGE_SZ) as int, 1, None));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.is_cap(u));
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s3.is_cap(u) && s3.payload_of(u) == first && s3.list.nodes@[u as int].depth == 1);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s3.is_cap(np) && s3.payload_of(np) == process_of(base));
            assert(s2.processes.records@.contains_key(process));
            assert(s3.processes.records@.contains_key(process));
            assert(s3.root_live(process));
            assert(s3.tables.roots@.contains_key(process));
            assert(s3.processes.records@.contains_key(base));
            assert(!s3.processes.records@[base].value().dead);
            assert(s3.tables.leaf(base, 0) == NO_LEAF);
            assert forall|i: int| b2 / PAGE_SZ + 4 <= i < b2 / PAGE_SZ + 6 implies #[trigger] s3.blocks.pages@[i].kind is Free by {
                assert(s2.blocks.tracks(i));
                assert(s2.blocks.pages@[i].kind is Free);
            }
            // The retype adds the thread capability, under the untyped, and the binding, under the process
            // capability. So the process capability's only child is the binding, and the thread capability,
            // not live before, has none.
            assert(s3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let nt = (b2 + 2) as usize;
            assert(s2.list.nodes@[u as int].live);
            assert(u != nt);
            assert(Self::typed_nodes(s2.list, s3.list, nt, bt));
            assert(s3.list.parent@ == s2.list.parent@.insert(nt, u).insert(bt, np));
            assert forall|x: usize| x != nt && x != bt && #[trigger] s2.list.parent@.contains_key(x)
                implies s3.list.parent@[x] == s2.list.parent@[x] by {}
            lemma_children_kept(s2.list, s3.list, nt, bt, np);
            lemma_children_kept(s2.list, s3.list, nt, bt, nt);
            assert forall|x: usize| #[trigger] s3.list.is_child(np, x) implies x == bt by {
                if x != bt && x != nt {
                    assert(s2.list.is_child(np, x));
                }
            }
            assert forall|x: usize| !#[trigger] s3.list.is_child(nt, x) by {
                if s3.list.is_child(nt, x) && x != nt && x != bt {
                    s2.list.lemma_dead_childless(nt, x);
                }
            }
        }

        // A leaf in root entry 0 of the new process's table, through the process capability.
        let at2 = Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 };
        proof {
            assert(s3.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s3.blocks.small_free((bl / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s3.blocks.pages@[bl / PAGE_SZ + k].kind is Free by {
                    assert(s3.blocks.pages@[(b2 / PAGE_SZ + 4 + k) as int].kind is Free);
                }
            }
            assert(s3.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl));
        }
        let ok4 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl);
        let ghost s4 = *self;
        let ghost child = (bl + 1) as usize;
        proof {
            assert(ok4);
            assert(Self::leaf_retyped(s3, s4, process, ROOT_UNTYPED_SLOT, at2, bl));
            assert(s3.blocks.tracks((base / PAGE_SZ) as int));
            assert(s3.blocks.tracks((bt / PAGE_SZ) as int));
            assert(s4.blocks.pages@[(base / PAGE_SZ) as int] == s3.blocks.pages@[(base / PAGE_SZ) as int]);
            assert(s4.blocks.pages@[(bt / PAGE_SZ) as int] == s3.blocks.pages@[(bt / PAGE_SZ) as int]);
            assert(block_refs(&s4.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(block_refs(&s4.blocks, BlockRef::Small(bt / PAGE_SZ)) == 1);
            assert(s4.process_unloaded(base));
            assert(s4.tables.leaf(base, 0) == bl);
            assert(index_ok(WITNESS_CHILD_SLOT) && index_entry(WITNESS_CHILD_SLOT) == 0);
            assert(s4.tables.has_slot(&s4.list, base, WITNESS_CHILD_SLOT));
            assert(s4.tables.node_of(base, WITNESS_CHILD_SLOT) == child);
            assert(!s4.list.nodes@[child as int].live);
            assert(s4.processes == s3.processes);
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.is_cap(u));
            assert(s4.tables.has_slot(&s4.list, process, ROOT_UNTYPED_SLOT));
            assert(s4.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s4.is_cap(u) && s4.payload_of(u) == first && s4.list.nodes@[u as int].depth == 1);
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.is_cap(np));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_PROCESS_SLOT));
            assert(s4.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s4.is_cap(np) && s4.payload_of(np) == process_of(base));
            assert(s4.root_live(process));
            assert(s4.tables.roots@.contains_key(process));
            // The leaf's hidden node goes under the untyped, so the two capabilities keep their children.
            assert(s4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let nt = (b2 + 2) as usize;
            assert(s4.list.parent@ == s3.list.parent@.insert(bl, u));
            assert forall|x: usize| x != bl && x != bl && #[trigger] s3.list.parent@.contains_key(x)
                implies s4.list.parent@[x] == s3.list.parent@[x] by {}
            lemma_children_kept(s3.list, s4.list, bl, bl, np);
            lemma_children_kept(s3.list, s4.list, bl, bl, nt);
            assert forall|x: usize| #[trigger] s4.list.is_child(np, x) implies x == bt by {
                if x != bl {
                    assert(s3.list.is_child(np, x));
                }
            }
            assert forall|x: usize| !#[trigger] s4.list.is_child(nt, x) by {
                if s4.list.is_child(nt, x) && x != bl {
                    assert(s3.list.is_child(nt, x));
                }
            }
            // The leaf: live, hidden, its other nodes not live, owned by root entry 0 of the new table.
            lemma_listed_live(s4.list, bl);
            assert(s4.list.nodes@[bl as int].kind is Hidden);
            assert(s4.tables.owner@[bl] == (base, 0int));
            assert(s4.threads == s3.threads);
            assert(s4.spaces == s3.spaces);
            assert(s4.flush_epoch == s0.flush_epoch);
        }

        // An untyped over the second block's last two pages, derived from the root's untyped into slot 1
        // of the new process's leaf, through the process capability.
        let at3 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT };
        proof {
            assert(s4.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(!s4.cap_dead(u));
            assert(names_block(first.kind));
            assert(UNTYPED_RIGHTS & !UNTYPED_RIGHTS == 0) by (compute_only);
            assert(UNTYPED_RIGHTS & right_bit(Right::Control) == 0) by (compute_only);
            assert(block_within(bd, 1, first));
            assert(narrows(child_of(first, UNTYPED_RIGHTS, bd, 1), first));
            assert(s4.can_derive_between(process, ROOT_UNTYPED_SLOT, base, WITNESS_CHILD_SLOT, UNTYPED_RIGHTS, bd, 1));
            assert(s4.can_derive_at(process, ROOT_UNTYPED_SLOT, at3, UNTYPED_RIGHTS, bd, 1));
        }
        let ok5 = self.derive(process, ROOT_UNTYPED_SLOT, at3, UNTYPED_RIGHTS, bd, 1);
        proof {
            let s5 = *self;
            assert(ok5);
            assert(Self::cap_derived_between(s4, s5, process, ROOT_UNTYPED_SLOT, base, WITNESS_CHILD_SLOT, UNTYPED_RIGHTS, bd, 1));
            assert(s5.view().holds(base, child));
            assert(s5.list.is_child(u, child));
            assert(s5.payload_of(child) == child_of(first, UNTYPED_RIGHTS, bd, 1));
            assert(bound_threads(&s5.list, &s5.tables) == bound_threads(&s2.list, &s2.tables).insert(bt, base));
            assert(child == base + 12 * PAGE_SZ + 1);
            assert(bt == base + 10 * PAGE_SZ);
            assert(bd == base + 14 * PAGE_SZ);
            // An untyped's derive leaves the blocks, and no step changed an acknowledgement.
            assert(s4.payload_of(s4.tables.node_of(process, ROOT_UNTYPED_SLOT)).kind is Untyped);
            assert(s5.blocks == s4.blocks);
            assert(block_refs(&s5.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(block_refs(&s5.blocks, BlockRef::Small(bt / PAGE_SZ)) == 1);
            assert(s5.process_unloaded(base));
            assert(s5.stale_epoch == s0.stale_epoch);
            assert(s5.cores == s0.cores);
            assert(s5.iommus == s0.iommus);
            assert(bl / PAGE_SZ == base / PAGE_SZ + 12);
            assert((base + 12 * PAGE_SZ) / PAGE_SZ as int == bl / PAGE_SZ);
            // The new table's root entries and the three slots the reclaim starts from.
            assert(s5.tables.roots == s4.tables.roots);
            assert forall|r: int| 1 <= r < ROOT_ENTRIES implies #[trigger] s5.tables.leaf(base, r) == NO_LEAF by {
                assert(s3.tables.leaf(base, r) == s2.tables.leaf(base, r));
                assert(s4.tables.leaf(base, r) == s3.tables.leaf(base, r));
            }
            assert(Self::derive_step(s4, s5, child));
            Self::lemma_slot_stays(s4, s5, process, WITNESS_PROCESS_SLOT);
            Self::lemma_slot_stays(s4, s5, process, WITNESS_THREAD_SLOT);
            Self::lemma_caps_frame(s4, s5, child, child, np);
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_THREAD_SLOT));
            assert(s3.is_cap((b2 + 2) as usize) && s3.payload_of((b2 + 2) as usize) == thread_of(bt));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_THREAD_SLOT));
            assert(s4.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(s4.is_cap((b2 + 2) as usize) && s4.payload_of((b2 + 2) as usize) == thread_of(bt));
            Self::lemma_caps_frame(s4, s5, child, child, (b2 + 2) as usize);
            assert(s5.slot_holds(process, WITNESS_PROCESS_SLOT, np, process_of(base)));
            assert(s5.slot_holds(process, WITNESS_THREAD_SLOT, (b2 + 2) as usize, thread_of(bt)));
            assert(s5.slot_holds(base, WITNESS_CHILD_SLOT, child, child_of(first, UNTYPED_RIGHTS, bd, 1)));
            Self::lemma_acknowledged_kept(s0, s5, base / PAGE_SZ);
            Self::lemma_acknowledged_kept(s0, s5, (base / PAGE_SZ + 12) as usize);
            Self::lemma_acknowledged_kept(s0, s5, (base / PAGE_SZ + 13) as usize);
            // The derived untyped goes under the root's untyped: the two capabilities keep their children,
            // and it, not live before, has none.
            assert(s5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let nt = (b2 + 2) as usize;
            assert(s4.list.nodes@[u as int].live);
            assert(u != child);
            assert(s5.list.parent@ == s4.list.parent@.insert(child, u));
            assert(s5.list.seq@[0] == s4.list.seq@[0]);
            assert forall|x: usize| x != child && x != child && #[trigger] s4.list.parent@.contains_key(x)
                implies s5.list.parent@[x] == s4.list.parent@[x] by {}
            lemma_children_kept(s4.list, s5.list, child, child, np);
            lemma_children_kept(s4.list, s5.list, child, child, nt);
            lemma_children_kept(s4.list, s5.list, child, child, child);
            assert forall|x: usize| #[trigger] s5.list.is_child(np, x) implies x == bt by {
                if x != child {
                    assert(s4.list.is_child(np, x));
                }
            }
            assert forall|x: usize| !#[trigger] s5.list.is_child(nt, x) by {
                if s5.list.is_child(nt, x) && x != child {
                    assert(s4.list.is_child(nt, x));
                }
            }
            assert forall|x: usize| !#[trigger] s5.list.is_child(child, x) by {
                if s5.list.is_child(child, x) && x != child {
                    s4.list.lemma_dead_childless(child, x);
                }
            }
            assert(s5.list.nodes@[nt as int].live);
            if !s5.list.childless(nt) {
                s5.list.lemma_next_is_child(nt);
            }
            if !s5.list.childless(child) {
                s5.list.lemma_next_is_child(child);
            }
            // The rest of what the reclaim reads, kept by the leaf's retype and the derive.
            assert(s0.flush_epoch == 0);
            assert(s5.processes == s4.processes);
            assert(s5.threads == s4.threads);
            assert(s5.spaces.roots@ == s4.spaces.roots@);
            assert(s5.tables.owner == s4.tables.owner);
            assert(s5.list.nodes@[bl as int].live && s5.list.nodes@[bl as int].kind is Hidden);
            assert forall|x: int| bl + 1 < x < bl + NODES_PER_PAGE implies !#[trigger] s5.list.nodes@[x].live by {
                assert(!s4.list.nodes@[x].live);
            }
            // What a teardown of the process starts from: the root's untyped, table and record, the blocks
            // within the untyped, and the new leaf's owner.
            Self::lemma_slot_stays(s4, s5, process, ROOT_UNTYPED_SLOT);
            Self::lemma_caps_frame(s4, s5, child, child, u);
            assert(s5.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s3.processes.records@.contains_key(process));
            assert(s4.root_live(process));
            assert(witness_alive(s5, process));
            assert(s5.tables.roots@.contains_key(process));
            assert(block_within(base, PROCESS_ORDER, first));
            assert(block_within(bt, THREAD_ORDER, first));
            assert(block_within(bl, 1, first));
            assert(bl == base + 12 * PAGE_SZ);
            assert(base + 2 * PROCESS_BYTES <= NODE_SPACE) by (nonlinear_arith)
                requires
                    (itb + 2) * PROCESS_BYTES <= block_bytes(first.order),
                    first.base + block_bytes(first.order) <= NODE_SPACE,
                    base == first.base + itb * PROCESS_BYTES,
            ;
            assert(s4.tables.owner@.contains_key(bl));
            assert(s5.tables.owner@.contains_key(bl));
        }
        ok1 && ok2 && ok3 && ok4 && ok5
    }

    /// From the end of the spawn witness, as the root: destroy the process through its capability in
    /// slot 257, delete the thread's capability, retype the thread's block, which unbinds the thread,
    /// delete the process's capability, retype the leaf in the process's table three times, which
    /// unlinks it, slices its one capability and frees it, retype the process's block, which frees it,
    /// and retype a process at the same block into slot 257 again. Each step returns what a teardown
    /// driven by retype says, in this order, and at the end the root holds a capability to a live
    /// process at the same block. See design/teardown-driven-by-retype/.
    #[verifier::spinoff_prover]
    pub fn witness_process_block_retyped(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        base: usize,
    ) -> (ret: (bool, bool, ReclaimStep, bool, ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, bool))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret.0,
            ret.1,
            ret.2 is Slice,
            ret.3,
            ret.4 is Unlinked,
            ret.5 is Slice,
            ret.6 is Freed,
            ret.7 is Freed,
            ret.8,
            final(self).wf(),
            final(self).view().holds(process, (base + 8 * PAGE_SZ + 1) as usize),
            final(self).payload_of((base + 8 * PAGE_SZ + 1) as usize) == process_of(base),
            witness_alive(*final(self), base),
    {
        hide(CapKernel::wf);
        let ok0 = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, base);
        let ghost r0 = *self;
        let ghost first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let b2 = base + PROCESS_BYTES;
        let bt = b2 + 2 * PAGE_SZ;
        let bl = b2 + 4 * PAGE_SZ;
        let ghost np = (b2 + 1) as usize;
        let ghost nt = (b2 + 2) as usize;
        let ghost child = (bl + 1) as usize;
        proof {
            assert(ok0);
            lemma2_to64();
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(base % PROCESS_BYTES == 0);
            assert(b2 % PROCESS_BYTES == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            lemma_block_page(b2, 4);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == base / PAGE_SZ + 10);
            assert(bl / PAGE_SZ == base / PAGE_SZ + 12);
            assert(bt == base + 10 * PAGE_SZ);
            assert(bl == base + 12 * PAGE_SZ);
            assert(np == base + 8 * PAGE_SZ + 1);
            assert(nt == base + 8 * PAGE_SZ + 2);
            // Where the four slots' nodes lie, and whose leaves they are in.
            r0.lemma_slot(process, ROOT_UNTYPED_SLOT);
            r0.lemma_slot(process, WITNESS_PROCESS_SLOT);
            r0.lemma_slot(process, WITNESS_THREAD_SLOT);
            r0.lemma_slot(base, WITNESS_CHILD_SLOT);
            assert(index_slot(ROOT_UNTYPED_SLOT) == 5 && index_slot(WITNESS_PROCESS_SLOT) == 1);
            assert(index_slot(WITNESS_THREAD_SLOT) == 2 && index_slot(WITNESS_CHILD_SLOT) == 1);
            assert(index_entry(WITNESS_CHILD_SLOT) == 0);
            assert(u % PAGE_SZ == 5 && np % PAGE_SZ == 1 && nt % PAGE_SZ == 2 && child % PAGE_SZ == 1);
            r0.lemma_slot_bound(u);
            r0.lemma_slot_bound(np);
            r0.lemma_slot_bound(nt);
            r0.lemma_slot_bound(child);
            // The root's leaf holding its untyped is the root's, the process's leaf the process's.
            assert(r0.tables.owner@[page_of(u)].0 == process);
            assert(r0.tables.owner@[bl].0 == base);
            assert(page_of(u) != bl);
            r0.lemma_process_cap(np);
            assert(r0.blocks.tracks_addr(base));
            assert(block_typed(&r0.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(r0.processes.records@.contains_key(base));
            assert(r0.tables.roots@.contains_key(base)) by {
                reveal(CapKernel::wf);
            }
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(r0.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(r0.list.parent@[child] == u);
            assert(r0.payload_of(child).kind is Untyped);
            assert(r0.can_destroy(process, WITNESS_PROCESS_SLOT));
        }

        // Destroy the process, through its capability in slot 257 of the root's table.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.destroy(0, process, WITNESS_PROCESS_SLOT, Tracked(&mut steps));
        let ghost r1 = *self;
        let at_thread = Position { through: None, index: WITNESS_THREAD_SLOT };
        proof {
            assert(ok1);
            assert(r0.payload_of(np).base == base);
            assert(Self::process_destroyed(r0, r1, base));
            assert(r1.list == r0.list && r1.tables == r0.tables && r1.blocks == r0.blocks);
            assert(r1.processes.records@[process] == r0.processes.records@[process]);
            assert(r1.processes.records@.contains_key(base));
            assert(r1.root_live(process));
            // The thread's capability can go: it is in the root's slot 258, deeper than the first node,
            // and has no child.
            assert(r1.table_at(process, None) == Some(process));
            assert(r1.slot_holds(process, WITNESS_THREAD_SLOT, nt, thread_of(bt)));
            lemma_owned_listed(r1, nt);
            assert(r1.list.childless(nt));
            assert(r1.cap_at(process, at_thread) == Some(nt));
            assert(r1.can_delete_at(process, at_thread));
        }

        // Delete the thread's capability.
        let ok2 = self.delete(process, at_thread);
        let ghost r2 = *self;
        proof {
            assert(ok2 is Some);
            assert(Self::cap_deleted_at(r1, r2, process, at_thread));
            assert(Self::object_dropped(r1, r2, nt));
            assert(r1.payload_of(nt).kind is Thread);
            assert(blocks_refs_changed(&r1.blocks, &r2.blocks, BlockRef::Small(bt / PAGE_SZ), 0, block_dead(&r1.blocks, BlockRef::Small(bt / PAGE_SZ)) || true));
            assert(r2.blocks.pages@[(bt / PAGE_SZ) as int].refs == 0);
            assert(block_typed(&r2.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(block_refs(&r2.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            lemma_deleted_dead(r2, nt);
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r2.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != nt {
                    assert(r2.list.nodes@[i].live == r1.list.nodes@[i].live);
                }
            }
            assert(r2.list.parent@ == r0.list.parent@);
            assert(r2.tables == r0.tables);
            assert(r2.processes == r1.processes);
            assert(r2.spaces == r0.spaces);
            assert(r2.threads.records == r0.threads.records);
            assert(r2.root_live(process));
            assert(r2.tables.roots@.contains_key(process));
            // The root's untyped is still its slot 5, and can retype the thread's block.
            lemma_slot_kept_but(r1, r2, process, ROOT_UNTYPED_SLOT, nt);
            Self::lemma_caps_frame(r1, r2, nt, nt, u);
            assert(r2.list.nodes@[child as int].live == r1.list.nodes@[child as int].live);
            assert(r2.list.nodes@[child as int].live);
            assert(r2.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r2, child);
            assert(r2.list.d(u) < MAX_DEPTH);
            assert(r2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(r2.threads.records@[bt].value().process == Some(base));
            assert(r2.thread_is_dead(bt));
            assert(r2.can_unbind_thread(process, ROOT_UNTYPED_SLOT, bt));
        }

        // Retype the thread's block: the thread is dead, so the retype unbinds it from the process.
        let ok3 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bt, Tracked(&mut steps));
        let ghost r3 = *self;
        let at_process = Position { through: None, index: WITNESS_PROCESS_SLOT };
        proof {
            assert(ok3 is Slice);
            assert(r2.thread_unbound(r3, process, ROOT_UNTYPED_SLOT, bt));
            assert(Self::unbound(r2, r3, bt));
            assert(block_refs(&r3.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(block_typed(&r3.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r3.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != bt {
                    assert(r3.list.nodes@[i].live == r2.list.nodes@[i].live);
                    assert(r2.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r3.list.parent@ == r0.list.parent@);
            assert(r3.tables == r0.tables);
            assert(r3.processes.records == r0.processes.records || r3.processes.records == r1.processes.records);
            assert(r3.root_live(process));
            assert(r3.spaces == r0.spaces);
            // The slots of the root's leaves stay: the thread's block is no leaf of the root's, since an
            // owned leaf whose node is live holds one reference.
            assert(!r2.list.nodes@[bt as int].live || !r2.tables.owner@.contains_key(bt)) by {
                reveal(CapKernel::wf);
            }
            lemma_slot_kept_but(r1, r2, process, WITNESS_PROCESS_SLOT, nt);
            lemma_slot_kept_but(r2, r3, process, WITNESS_PROCESS_SLOT, bt);
            lemma_slot_kept_but(r2, r3, process, ROOT_UNTYPED_SLOT, bt);
            // The process's capability can go: its only child was the thread's binding.
            assert(r3.list.nodes@[np as int].live == r2.list.nodes@[np as int].live);
            assert(r3.list.nodes@[np as int].kind == r2.list.nodes@[np as int].kind);
            Self::lemma_caps_frame(r1, r2, nt, nt, np);
            assert(r3.is_cap(np));
            assert(r3.payload_of(np) == process_of(base));
            assert(r3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r3, np);
            lemma_children_back(r0.list, r2.list, np);
            assert forall|c: usize| #[trigger] r2.list.is_child(np, c) implies c == bt by {
                assert(r0.list.is_child(np, c));
            }
            assert(r3.list.childless(np));
            assert(r3.table_at(process, None) == Some(process));
            assert(r3.cap_at(process, at_process) == Some(np));
            assert(r3.can_delete_at(process, at_process));
        }

        // Delete the process's capability.
        let ok4 = self.delete(process, at_process);
        let ghost r4 = *self;
        proof {
            assert(ok4 is Some);
            assert(Self::cap_deleted_at(r3, r4, process, at_process));
            assert(Self::object_dropped(r3, r4, np));
            assert(block_refs(&r4.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r4.blocks, BlockRef::Small(base / PAGE_SZ)));
            lemma_deleted_dead(r4, np);
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r4.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != np {
                    assert(r4.list.nodes@[i].live == r3.list.nodes@[i].live);
                    assert(r3.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r4.list.parent@ == r0.list.parent@);
            assert(r4.tables == r0.tables);
            assert(r4.processes.records == r3.processes.records);
            assert(r4.root_live(process));
            assert(r4.spaces == r0.spaces);
            lemma_slot_kept_but(r3, r4, process, WITNESS_PROCESS_SLOT, np);
            lemma_slot_kept_but(r3, r4, process, ROOT_UNTYPED_SLOT, np);
            Self::lemma_caps_frame(r3, r4, np, np, u);
            assert(r3.list.nodes@[u as int].live == r2.list.nodes@[u as int].live);
            assert(r3.list.nodes@[u as int].kind == r2.list.nodes@[u as int].kind);
            assert(r3.is_cap(u));
            assert(r4.is_cap(u));
            // The leaf in the process's table is still live: only slots died.
            assert(r4.list.nodes@[bl as int].live == r3.list.nodes@[bl as int].live);
            assert(r3.list.nodes@[bl as int].live == r2.list.nodes@[bl as int].live);
            assert(r2.list.nodes@[bl as int].live == r1.list.nodes@[bl as int].live);
            assert(r4.list.nodes@[bl as int].live);
            assert(r4.list.nodes@[child as int].live == r3.list.nodes@[child as int].live);
            assert(r3.list.nodes@[child as int].live == r2.list.nodes@[child as int].live);
            assert(r4.list.nodes@[child as int].live);
            assert(r4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r4, child);
            assert(r4.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(r4.can_unlink_leaf(process, ROOT_UNTYPED_SLOT, bl));
        }

        // Retype the process's leaf: its hidden node is live, so the retype unlinks it.
        let ok5 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r5 = *self;
        proof {
            assert(ok5 is Unlinked);
            assert(r4.leaf_unlinked(r5, process, ROOT_UNTYPED_SLOT, bl));
            assert(block_refs(&r5.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r5.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r5.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != bl {
                    assert(r5.list.nodes@[i].live == r4.list.nodes@[i].live);
                    assert(r4.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r5.list.parent@ == r0.list.parent@);
            assert(r5.tables == r0.tables);
            assert(r5.root_live(process));
            assert(r5.spaces == r0.spaces);
            assert(r5.flush_epoch == 0);
            lemma_slot_kept_but(r4, r5, process, ROOT_UNTYPED_SLOT, bl);
            lemma_slot_kept_but(r4, r5, process, WITNESS_PROCESS_SLOT, bl);
            assert(r5.is_cap(u));
            assert(r5.list.nodes@[child as int].live == r4.list.nodes@[child as int].live);
            assert(r5.list.nodes@[child as int].live);
            assert(r5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r5, child);
            assert(r5.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            // The leaf's one live slot is the derived untyped, which has no child.
            assert(r5.list.nodes@[bl + 1].live);
            assert(!r5.leaf_is_empty(bl));
            assert(r5.can_slice_leaf(process, ROOT_UNTYPED_SLOT, bl));
            assert forall|x: int| bl + 2 <= x < bl + NODES_PER_PAGE implies !#[trigger] r5.list.nodes@[x].live by {
                assert(!r0.list.nodes@[x].live);
            }
            lemma_children_back(r0.list, r5.list, child);
            if !r5.list.childless(child) {
                r5.list.lemma_next_is_child(child);
                assert(r0.list.is_child(child, r5.list.nodes@[child as int].next));
            }
            assert forall|j: int| 1 <= j < NODES_PER_PAGE && (#[trigger] r5.list.nodes@[bl + j]).live
                implies r5.list.childless((bl + j) as usize) by {
                if j != 1 {
                    assert(!r5.list.nodes@[bl + j].live);
                }
            }
            assert(r5.leaf_slots_childless(bl));
            lemma_live_slots_none(r5, bl, 2);
            assert(r5.leaf_live_slots(bl) == 1);
            // No slot of the leaf names the process's block: its one capability is an untyped.
            assert(r5.payload_of(child).kind is Untyped);
            assert(!r5.leaf_slot_names(bl, BlockRef::Small(base / PAGE_SZ))) by {
                if r5.leaf_slot_names(bl, BlockRef::Small(base / PAGE_SZ)) {
                    let n = choose|n: usize| bl < n < bl + NODES_PER_PAGE && #[trigger] r5.cap_names_block(n, BlockRef::Small(base / PAGE_SZ));
                    if n != child {
                        assert(!r5.list.nodes@[n as int].live);
                    }
                }
            }
        }

        // Retype the leaf again: its hidden node is gone, so the retype slices its slots.
        let ok6 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r6 = *self;
        proof {
            assert(ok6 is Slice);
            assert(r5.leaf_slice_kept(r6, bl));
            assert(r6.leaf_is_empty(bl));
            assert(block_refs(&r6.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r6.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(r6.tables == r0.tables);
            assert(r6.root_live(process));
            assert(r6.spaces.roots == r0.spaces.roots);
            assert(r6.spaces.loaded == r0.spaces.loaded);
            assert(r6.processes.records == r1.processes.records);
            assert(r6.tables.has_slot(&r6.list, process, ROOT_UNTYPED_SLOT));
            assert(r6.tables.has_slot(&r6.list, process, WITNESS_PROCESS_SLOT));
            assert(r6.is_cap(u));
            assert(r6.list.nodes@[u as int].depth == r5.list.nodes@[u as int].depth);
            assert(r6.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(r6.list.nodes@[np as int].live == r5.list.nodes@[np as int].live);
            assert(!r6.list.nodes@[np as int].live);
            Self::lemma_acknowledged_kept(r0, r6, bl / PAGE_SZ);
            Self::lemma_acknowledged_kept(r0, r6, (bl / PAGE_SZ + 1) as usize);
        }

        // Retype the leaf a third time: it is empty, so the retype frees it.
        let ok7 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r7 = *self;
        proof {
            assert(ok7 is Freed);
            assert(r6.leaf_freed(r7, 0, process, ROOT_UNTYPED_SLOT, bl));
            assert(r6.tables.owner@[bl] == (base, 0int));
            assert(r7.tables.leaf(base, 0) == NO_LEAF);
            assert forall|r: int| 0 <= r < ROOT_ENTRIES implies #[trigger] r7.tables.leaf(base, r) == NO_LEAF by {
                if r != 0 {
                    assert(r7.tables.leaf(base, r) == r6.tables.leaf(base, r));
                }
            }
            assert(r7.tables.roots@.dom().contains(process));
            assert(r7.tables.leaf(process, 0) == r6.tables.leaf(process, 0));
            assert(r7.tables.leaf(process, 2) == r6.tables.leaf(process, 2));
            assert(r7.tables.has_slot(&r7.list, process, ROOT_UNTYPED_SLOT));
            assert(r7.tables.has_slot(&r7.list, process, WITNESS_PROCESS_SLOT));
            assert(r7.tables.is_cap(&r7.list, u));
            assert(r7.payload_of(u) == first);
            assert(r7.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(r6.blocks.tracks((base / PAGE_SZ) as int));
            assert(r7.blocks.pages@[(base / PAGE_SZ) as int] == r6.blocks.pages@[(base / PAGE_SZ) as int]);
            assert(r7.process_is_dead(base));
            assert(r7.process_unloaded(base));
            assert forall|i: usize| KERNEL_MEM_END_L4INDEX <= i < ENTRIES implies #[trigger] r7.spaces.roots@[base].value()[i].is_empty() by {
                assert(!holds_kernel(SpaceKind::Process, i));
                assert(r0.spaces.roots@[base].value()[i].is_empty());
            }
            assert(r7.process_is_spent(base));
            Self::lemma_acknowledged_kept(r0, r7, base / PAGE_SZ);
            assert(r7.processes.records@.contains_key(base));
            // The process's block is still typed, so no typed large block covers it.
            r7.lemma_process_block(base);
            assert(r7.blocks.wf()) by {
                reveal(CapKernel::wf);
            }
            r7.blocks.lemma_not_free_uncovered((base / PAGE_SZ) as int);
        }

        // Retype the process's block: the process is spent, so the retype frees it.
        let ok8 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        let ghost r8 = *self;
        proof {
            assert(ok8 is Freed);
            assert(r7.process_freed(r8, 0, process, ROOT_UNTYPED_SLOT, base));
            assert(r8.tables.roots@[process] == r7.tables.roots@[process]);
            assert(r8.tables.roots@.contains_key(process));
            assert(r8.processes.records@[process] == r7.processes.records@[process]);
            assert(r8.root_live(process));
            assert(r8.tables.leaf(process, 0) == r7.tables.leaf(process, 0));
            assert(r8.tables.leaf(process, 2) == r7.tables.leaf(process, 2));
            assert(r8.tables.has_slot(&r8.list, process, ROOT_UNTYPED_SLOT));
            assert(r8.tables.has_slot(&r8.list, process, WITNESS_PROCESS_SLOT));
            assert(r8.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(!r8.list.nodes@[np as int].live);
            assert(r8.is_cap(u));
            assert(r8.payload_of(u) == first);
            assert(r8.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(!r8.blocks.covered((base / PAGE_SZ) as int));
            assert(r8.blocks.small_free((base / PAGE_SZ) as int, PROCESS_ORDER as usize)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] r8.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(r8.blocks.pages@[(base / PAGE_SZ) + k].kind is Free);
                }
            }
            assert(r8.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }

        // Retype a process at the same block into slot 257 again.
        let ok9 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base);
        proof {
            assert(ok9);
            assert(np == base + 8 * PAGE_SZ + 1);
        }
        (ok1, ok2.is_some(), ok3, ok4.is_some(), ok5, ok6, ok7, ok8, ok9)
    }

    /// Gives entry e of table t of space s a child table at the given level: the order-3 block at the
    /// cursor, retyped as a table page under the root's untyped at ROOT_UNTYPED_SLOT and linked through
    /// the capability to s's process at index i of the root's table, at depth d. The entry is empty and
    /// the block free in the untyped, so it never refuses.
    #[verifier::spinoff_prover]
    fn witness_table(
        &mut self,
        process: usize,
        i: usize,
        t: usize,
        e: usize,
        level: usize,
        cursor: usize,
        s: Ghost<usize>,
        n: Ghost<usize>,
        d: Ghost<usize>,
        u: Ghost<usize>,
        first: Ghost<Payload>,
    ) -> (ret: bool)
        requires
            old(self).wf(),
            witness_root(*old(self), process, u@, first@),
            witness_slot(*old(self), process, i, n@, process_of(s@), d@),
            witness_alive(*old(self), s@),
            witness_block(*old(self), cursor, first@),
            1 <= level <= 3,
            tree_of(&old(self).table_pages, &old(self).spaces).is_table(t),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).space == Some(s@),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).level == level + 1,
            !old(self).blocks.pages@[(t / PAGE_SZ) as int].dead,
            tree_of(&old(self).table_pages, &old(self).spaces).child_slot(t, e),
            tree_of(&old(self).table_pages, &old(self).spaces).entry(t, e).is_empty(),
        ensures
            ret,
            final(self).wf(),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(cursor / PAGE_SZ <= j < cursor / PAGE_SZ + 8)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            nodes_kept(old(self).list, final(self).list),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            steps_kept(tree_of(&old(self).table_pages, &old(self).spaces), tree_of(&final(self).table_pages, &final(self).spaces)),
            witness_root(*final(self), process, u@, first@),
            witness_slot(*final(self), process, i, n@, process_of(s@), d@),
            step(tree_of(&final(self).table_pages, &final(self).spaces), t, e) == Some(cursor),
            tree_of(&final(self).table_pages, &final(self).spaces).is_page(cursor),
            tree_of(&final(self).table_pages, &final(self).spaces).record(cursor).level == level,
            tree_of(&final(self).table_pages, &final(self).spaces).record(cursor).space == Some(s@),
            !final(self).blocks.pages@[(cursor / PAGE_SZ) as int].dead,
            forall|j: usize| j < ENTRIES ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(cursor, j).is_empty(),
    {
        // The body relates three states; their invariants stay folded, and the lemmas open them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            lemma2_to64();
            assert(block_bytes(3) == PROCESS_BYTES);
            pre.lemma_table_base(t);
            assert(pre.blocks.pages@[cursor / PAGE_SZ + 0].kind is Free);
            pre.lemma_free_not_table(cursor, cursor / PAGE_SZ);
            pre.lemma_slot(process, ROOT_UNTYPED_SLOT);
            pre.lemma_slot_bound(u@);
            pre.lemma_slot(process, i);
            pre.lemma_slot_bound(n@);
            assert(pre.blocks.small_free((cursor / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] pre.blocks.pages@[cursor / PAGE_SZ + k].kind is Free by {
                    assert(pre.blocks.pages@[cursor / PAGE_SZ + k].kind is Free);
                }
            }
            assert(pre.can_retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level));
            // The parent is a typed table, so it lies outside the free block.
            if cursor / PAGE_SZ <= t / PAGE_SZ < cursor / PAGE_SZ + 8 {
                assert(pre.blocks.pages@[cursor / PAGE_SZ + (t / PAGE_SZ - cursor / PAGE_SZ)].kind is Free);
            }
            assert(t != cursor);
            lemma_aligned(cursor);
        }
        let retyped = self.retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level);
        let ghost mid = *self;
        let ghost m = tree_of(&mid.table_pages, &mid.spaces);
        proof {
            assert(retyped);
            Self::lemma_retype_nodes_kept(pre, mid, cursor, u@);
            assert(m.is_table(t));
            assert(m.record(t) == a.record(t));
            assert(m.entry(t, e) == a.entry(t, e));
            assert(m.child_slot(t, e));
            assert(m.is_page(cursor));
            mid.lemma_page_alive(cursor);
            assert(pre.blocks.tracks((t / PAGE_SZ) as int));
            assert(mid.blocks.pages@[(t / PAGE_SZ) as int] == pre.blocks.pages@[(t / PAGE_SZ) as int]);
            lemma_witness_slot_kept(pre, mid, process, ROOT_UNTYPED_SLOT, u@, first@, 1);
            lemma_witness_slot_kept(pre, mid, process, i, n@, process_of(s@), d@);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(mid.can_retype_under(process, ROOT_UNTYPED_SLOT, cursor, 3));
            assert(mid.can_link(process, i, t, e, ROOT_UNTYPED_SLOT, cursor));
        }
        let linked = self.link(process, i, t, e, ROOT_UNTYPED_SLOT, cursor);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            assert(linked);
            assert(mid.payload_of(mid.tables.node_of(process, i)).base == s@);
            assert(Self::link_done(mid, post, t, e, cursor, s@));
            assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
                assert(mid.is_cap(x) == pre.is_cap(x));
            }
            assert(b.entry(t, e) == child_entry(cursor));
            assert(b.names_child(t, e));
            assert(step(b, t, e) == Some(cursor));
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
            assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                implies post.list.nodes@[j].live == pre.list.nodes@[j].live by {
                assert(j != cursor);
            }
            assert(post.list == mid.list);
        }
        true
    }

    /// Gives space s the level 3, 2 and 1 tables of the path of the first page under entry l4 of its
    /// level 4 table, at the three order-3 blocks from the cursor, through the capability to s's process
    /// at index i of the root's table, at depth d. The entry is empty and the blocks free in the root's
    /// untyped, so it never refuses.
    #[verifier::spinoff_prover]
    fn witness_path(
        &mut self,
        process: usize,
        i: usize,
        s: usize,
        l4: usize,
        cursor: usize,
        n: Ghost<usize>,
        d: Ghost<usize>,
        u: Ghost<usize>,
        first: Ghost<Payload>,
    ) -> (ret: bool)
        requires
            old(self).wf(),
            witness_root(*old(self), process, u@, first@),
            witness_slot(*old(self), process, i, n@, process_of(s), d@),
            witness_alive(*old(self), s),
            tree_of(&old(self).table_pages, &old(self).spaces).is_root(s),
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES,
            tree_of(&old(self).table_pages, &old(self).spaces).entry(s, l4).is_empty(),
            !old(self).blocks.pages@[(s / PAGE_SZ) as int].dead,
            cursor + 3 * PROCESS_BYTES <= NODE_SPACE,
            witness_block(*old(self), cursor, first@),
            witness_block(*old(self), (cursor + PROCESS_BYTES) as usize, first@),
            witness_block(*old(self), (cursor + 2 * PROCESS_BYTES) as usize, first@),
        ensures
            ret,
            final(self).wf(),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(cursor / PAGE_SZ <= j < cursor / PAGE_SZ + 24)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            nodes_kept(old(self).list, final(self).list),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            steps_kept(tree_of(&old(self).table_pages, &old(self).spaces), tree_of(&final(self).table_pages, &final(self).spaces)),
            witness_root(*final(self), process, u@, first@),
            witness_slot(*final(self), process, i, n@, process_of(s), d@),
            walk_table(tree_of(&final(self).table_pages, &final(self).spaces), s, SpacePath { l4: l4, l3: 0, l2: 0, l1: 0 }) is Some,
    {
        // The body relates four states; their invariants stay folded, and the steps' contracts carry them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let ghost path = SpacePath { l4: l4, l3: 0, l2: 0, l1: 0 };
        let c1 = cursor + PROCESS_BYTES;
        let c2 = c1 + PROCESS_BYTES;
        proof {
            lemma2_to64();
            assert(block_bytes(3) == PROCESS_BYTES);
            pre.lemma_table_base(s);
            assert(cursor % PROCESS_BYTES == 0);
            assert(c1 % PROCESS_BYTES == 0);
            lemma_block_page(cursor, 0);
            lemma_block_page(c1, 0);
            assert(c1 / PAGE_SZ == cursor / PAGE_SZ + 8);
            assert(c2 / PAGE_SZ == cursor / PAGE_SZ + 16);
            assert(a.child_slot(s, l4));
        }
        let ok1 = self.witness_table(process, i, s, l4, 3, cursor, Ghost(s), n, d, u, first);
        let ghost s1 = *self;
        let ghost b1 = tree_of(&s1.table_pages, &s1.spaces);
        proof {
            lemma_witness_block_kept(pre, s1, c1, first@, (cursor / PAGE_SZ) as int, cursor / PAGE_SZ + 8);
            lemma_witness_block_kept(pre, s1, c2, first@, (cursor / PAGE_SZ) as int, cursor / PAGE_SZ + 8);
            s1.lemma_table_base(cursor);
            assert(b1.child_slot(cursor, 0));
        }
        let ok2 = self.witness_table(process, i, cursor, 0, 2, c1, Ghost(s), n, d, u, first);
        let ghost s2 = *self;
        let ghost b2 = tree_of(&s2.table_pages, &s2.spaces);
        proof {
            lemma_witness_block_kept(s1, s2, c2, first@, (c1 / PAGE_SZ) as int, c1 / PAGE_SZ + 8);
            s2.lemma_table_base(c1);
            assert(b2.child_slot(c1, 0));
        }
        let ok3 = self.witness_table(process, i, c1, 0, 1, c2, Ghost(s), n, d, u, first);
        proof {
            let post = *self;
            let b3 = tree_of(&post.table_pages, &post.spaces);
            lemma_nodes_kept_trans(pre.list, s1.list, s2.list);
            lemma_nodes_kept_trans(pre.list, s2.list, post.list);
            lemma_steps_kept_trans(a, b1, b2);
            lemma_steps_kept_trans(a, b2, b3);
            lemma_steps_kept_trans(b1, b2, b3);
            lemma_steps_kept(b1, b3);
            lemma_steps_kept(b2, b3);
            assert(a.is_table(s));
            assert(b3.is_root(s));
            assert(step(b3, s, l4) == Some(cursor));
            assert(step(b3, cursor, 0) == Some(c1));
            assert(step(b3, c1, 0) == Some(c2));
            assert(walk_table(b3, s, path) == Some(c2));
            assert forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(cursor / PAGE_SZ <= j < cursor / PAGE_SZ + 24)
                implies post.blocks.pages@[j] == pre.blocks.pages@[j] by {
                assert(s1.blocks.pages@[j] == pre.blocks.pages@[j]);
                assert(s2.blocks.pages@[j] == s1.blocks.pages@[j]);
            }
            assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                implies post.list.nodes@[j].live == pre.list.nodes@[j].live by {
                assert(s1.list.nodes@[j].live == pre.list.nodes@[j].live);
                assert(s2.list.nodes@[j].live == s1.list.nodes@[j].live);
            }
            assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
                assert(s1.is_cap(x) == pre.is_cap(x));
                assert(s2.is_cap(x) == s1.is_cap(x));
            }
            assert forall|r: usize| #[trigger] space_mapping(b3, r) == space_mapping(a, r) by {
                assert(space_mapping(b1, r) == space_mapping(a, r));
                assert(space_mapping(b2, r) == space_mapping(b1, r));
            }
        }
        ok1 && ok2 && ok3
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of nine free ones past those boot's tables took from the first untyped: retype a leaf into root
    /// entry 2 of the root's table at the second block's first two pages, a process P at `base` into
    /// slot 1 of that leaf, P's level 3, 2 and 1 tables for the path of the first page past the kernel's
    /// at the third to fifth blocks, a process Q at the sixth into slot 2, Q's tables for the same path
    /// at the seventh to ninth, and a frame at the second block's third page into slot 3; then map the
    /// frame at that path in P's space and in Q's. Every step succeeds, and at the end P and Q differ,
    /// neither is the root, and the path maps the one frame, with the frame capability's rights, in
    /// both spaces. What a revoke of the frame capability starts from holds too: the flush epoch is as
    /// boot left it, the root is live and slot 3 holds the capability, whose only children are the two
    /// mappings, which have none, and no other mapping names the frame's page.
    #[verifier::spinoff_prover]
    pub fn witness_root_maps_one_frame_into_two_processes(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@),
            image_tables_bound(image@) + 9 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let tree = tree_of(&final(self).table_pages, &final(self).spaces);
                let q = (base + 5 * PROCESS_BYTES) as usize;
                let path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
                let entry = frame_map_entry(((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
                let nf = (base + PROCESS_BYTES + 3) as usize;
                let fp = ((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& q != process
                &&& base != q
                &&& space_mapping(tree, base).contains_key(path)
                &&& space_mapping(tree, base)[path] == entry
                &&& space_mapping(tree, q).contains_key(path)
                &&& space_mapping(tree, q)[path] == entry
                &&& walk_finds(tree, base, path, fp)
                &&& walk_finds(tree, q, path, fp)
                &&& final(self).flush_epoch == old(self).flush_epoch
                &&& final(self).tables.roots@.contains_key(process)
                &&& witness_alive(*final(self), process)
                &&& final(self).tables.has_slot(&final(self).list, process, WITNESS_FRAME_SLOT)
                &&& final(self).tables.node_of(process, WITNESS_FRAME_SLOT) == nf
                &&& final(self).is_cap(nf)
                &&& exists|m1: usize, m2: usize| #[trigger] frame_shared(*final(self), nf, m1, m2, fp)
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            let pn = (leaf@ + 1) as usize;
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            assert(witness_root(s0, process, u, first));
            // The nine free blocks, one after another.
            assert(s0.root_untyped(process) == u);
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 9) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(base + 9 * PROCESS_BYTES <= NODE_SPACE);
            assert forall|j: int| 0 <= j < 9 implies #[trigger] witness_block(s0, cursor_block(base, j), first) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(s0.root_table_block(process, cursor_block(first.base, itb + j)));
            }
        }
        let b1 = base + PROCESS_BYTES;
        let bf = b1 + 2 * PAGE_SZ;
        let b2 = b1 + PROCESS_BYTES;
        let bq = b2 + 3 * PROCESS_BYTES;
        let b6 = bq + PROCESS_BYTES;
        let ghost fp = (bf / PAGE_SZ) as int;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(block_bytes(0) == PAGE_SZ);
            assert(cursor_block(base, 0) == base);
            assert(witness_block(s0, base, first));
            assert(base % PROCESS_BYTES == 0);
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            lemma_cursor_block(base, 5);
            lemma_cursor_block(base, 6);
            lemma_block_page(base, 0);
            lemma_block_page(b1, 0);
            lemma_block_page(b1, 2);
            assert(witness_block(s0, b1, first));
            assert(b1 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(fp == b1 / PAGE_SZ + 2);
            assert(s0.blocks.pages@[b1 / PAGE_SZ + 2].kind is Free);
            assert(!s0.blocks.covered(fp));
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b1, 1));
            assert(s0.blocks.small_free((b1 / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1));
        }
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1);
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at1, b1));
            assert(s1.tables.leaf(process, 2) == b1);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(witness_root(s1, process, u, first));
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_SECOND_PROCESS_SLOT) && index_entry(WITNESS_SECOND_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_FRAME_SLOT) && index_entry(WITNESS_FRAME_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == b1 + 1);
            assert(!s1.list.nodes@[(b1 + 1) as int].live);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s1.tables.node_of(process, WITNESS_SECOND_PROCESS_SLOT) == b1 + 2);
            assert(witness_empty(s1, process, WITNESS_SECOND_PROCESS_SLOT, (b1 + 2) as usize));
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_FRAME_SLOT));
            assert(s1.tables.node_of(process, WITNESS_FRAME_SLOT) == b1 + 3);
            assert(witness_empty(s1, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize));
            lemma_run_kept(s0, s1, base, 0, 1, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            lemma_run_kept(s0, s1, base, 2, 9, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            assert(s0.blocks.tracks(fp));
            assert(s1.blocks.pages@[fp].kind is Free);
            assert(s1.blocks.regions_2m@ == s0.blocks.regions_2m@);
            assert(s1.blocks.regions_1g@ == s0.blocks.regions_1g@);
        }

        // P, in slot 1 of that leaf.
        proof {
            assert(witness_block(s1, cursor_block(base, 0), first));
            assert(witness_block(s1, base, first));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(s1.blocks.pages@[base / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
            assert(s1.blocks.pages@[base / PAGE_SZ + 0].kind is Free);
            s1.lemma_free_not_table(base, base / PAGE_SZ);
        }
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base);
        let ghost s2 = *self;
        let ghost a2 = tree_of(&s2.table_pages, &s2.spaces);
        let ghost np = (b1 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None));
            assert(witness_alive(s2, base));
            assert(s2.payload_of(np) == process_of(base));
            assert(s2.list.nodes@[np as int].depth == 2);
            assert(s2.view().holds(process, np));
            assert(s2.is_cap(np));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(witness_slot(s2, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2));
            // The root's table keeps its new leaf, which P's table lacks, so the two differ.
            assert(s2.tables.leaf(process, 2) == b1);
            assert(s2.tables.leaf(base, 2) == NO_LEAF);
            assert(base != process);
            // The root's untyped, record and empty slots stay.
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s2.is_cap(u) && s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
            assert(s1.processes.records@.contains_key(process));
            assert(s2.tables.roots@.contains_key(process));
            assert(witness_root(s2, process, u, first));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(witness_empty(s2, process, WITNESS_SECOND_PROCESS_SLOT, (b1 + 2) as usize));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_FRAME_SLOT));
            assert(witness_empty(s2, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize));
            // P's space is a fresh root with nothing mapped.
            assert(!a2.is_page(base));
            assert(a2.is_root(base));
            assert(s2.spaces.roots@[base].value()[KERNEL_MEM_END_L4INDEX as usize].is_empty());
            assert(a2.entry(base, KERNEL_MEM_END_L4INDEX).is_empty());
            assert(s2.spaces.records@[base].value().kind is Process);
            assert(!s2.blocks.pages@[(base / PAGE_SZ) as int].dead);
            assert(space_mapping(a2, base) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty());
            // The blocks past P's and the frame's page stay free.
            lemma_run_kept(s1, s2, base, 2, 9, first, (base / PAGE_SZ) as int, base / PAGE_SZ + 8);
            assert(s1.blocks.tracks(fp));
            assert(s2.blocks.pages@[fp] == s1.blocks.pages@[fp]);
        }

        // P's tables for the path, through its capability.
        proof {
            lemma_cursor_block(base, 3);
            lemma_cursor_block(base, 4);
            assert(witness_block(s2, cursor_block(base, 2), first));
            assert(witness_block(s2, cursor_block(base, 3), first));
            assert(witness_block(s2, cursor_block(base, 4), first));
            assert(witness_block(s2, b2, first));
            assert(witness_block(s2, (b2 + PROCESS_BYTES) as usize, first));
            assert(witness_block(s2, (b2 + 2 * PROCESS_BYTES) as usize, first));
        }
        let ok3 = self.witness_path(process, WITNESS_PROCESS_SLOT, base, KERNEL_MEM_END_L4INDEX, b2, Ghost(np), Ghost(2), Ghost(u), Ghost(first));
        let ghost s3 = *self;
        let ghost a3 = tree_of(&s3.table_pages, &s3.spaces);
        proof {
            assert(ok3);
            assert(walk_table(a3, base, path) is Some);
            assert(space_mapping(a3, base) == space_mapping(a2, base));
            assert(witness_alive(s3, base));
            assert(a2.is_table(base));
            assert(s3.spaces.records@[base].value().kind is Process);
            lemma_witness_empty_kept(s2, s3, process, WITNESS_SECOND_PROCESS_SLOT, (b1 + 2) as usize);
            lemma_witness_empty_kept(s2, s3, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 16);
            lemma_run_kept(s2, s3, base, 5, 9, first, (b2 / PAGE_SZ) as int, b2 / PAGE_SZ + 24);
            assert(s2.blocks.tracks(fp));
            assert(s3.blocks.pages@[fp] == s2.blocks.pages@[fp]);
            assert(s3.tables.leaf(process, 2) == b1);
        }

        // Q, in slot 2 of the root's leaf.
        proof {
            assert(witness_block(s3, cursor_block(base, 5), first));
            assert(witness_block(s3, bq, first));
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bq, 3));
            assert(s3.blocks.small_free((bq / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s3.blocks.pages@[bq / PAGE_SZ + k].kind is Free by {
                    assert(s3.blocks.pages@[bq / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s3.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_SECOND_PROCESS_SLOT, bq, PROCESS_ORDER));
            assert(s3.blocks.pages@[bq / PAGE_SZ + 0].kind is Free);
            s3.lemma_free_not_table(bq, bq / PAGE_SZ);
            assert(!a3.is_table(bq));
        }
        let ok4 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_SECOND_PROCESS_SLOT, bq);
        let ghost s4 = *self;
        let ghost a4 = tree_of(&s4.table_pages, &s4.spaces);
        let ghost nq = (b1 + 2) as usize;
        proof {
            assert(ok4);
            assert(Self::retype_keeps(s3, s4, nq, (bq / PAGE_SZ) as int, 3, None));
            // Q's capability, record and fresh space.
            assert(s4.payload_of(nq) == process_of(bq));
            assert(s4.list.nodes@[nq as int].depth == 2);
            assert(s4.view().holds(process, nq));
            assert(s4.is_cap(nq));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s4.tables.node_of(process, WITNESS_SECOND_PROCESS_SLOT) == nq);
            assert(witness_slot(s4, process, WITNESS_SECOND_PROCESS_SLOT, nq, process_of(bq), 2));
            assert(witness_alive(s4, bq));
            assert(s3.tables.roots@.contains_key(process));
            assert(s4.tables.leaf(process, 2) == b1);
            assert(s4.tables.leaf(bq, 2) == NO_LEAF);
            assert(bq != process);
            assert(!a4.is_page(bq));
            assert(a4.is_root(bq));
            assert(s4.spaces.roots@[bq].value()[KERNEL_MEM_END_L4INDEX as usize].is_empty());
            assert(a4.entry(bq, KERNEL_MEM_END_L4INDEX).is_empty());
            assert(!s4.blocks.pages@[(bq / PAGE_SZ) as int].dead);
            assert(space_mapping(a4, bq) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty());
            // P's walk, mapping, record, kind and capability stay.
            lemma_new_root_steps_kept(a3, a4, bq);
            lemma_steps_kept(a3, a4);
            assert(walk_table(a4, base, path) == walk_table(a3, base, path));
            assert(s3.spaces.roots@.contains_key(base));
            assert(space_mapping(a4, base) == space_mapping(a3, base));
            assert(s3.processes.records@.contains_key(base));
            assert(witness_alive(s4, base));
            assert(a3.is_table(base));
            assert(s4.spaces.records@[base].value().kind is Process);
            assert(s3.is_cap(np));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_PROCESS_SLOT));
            assert(s4.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(witness_slot(s4, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2));
            // The root's untyped, record and frame slot stay.
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.is_cap(u));
            assert(s4.tables.has_slot(&s4.list, process, ROOT_UNTYPED_SLOT));
            assert(s4.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s4.is_cap(u) && s4.payload_of(u) == first && s4.list.nodes@[u as int].depth == 1);
            assert(s3.processes.records@.contains_key(process));
            assert(witness_root(s4, process, u, first));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_FRAME_SLOT));
            assert(witness_empty(s4, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize));
            // The blocks past Q's and the frame's page stay free.
            lemma_run_kept(s3, s4, base, 6, 9, first, (bq / PAGE_SZ) as int, bq / PAGE_SZ + 8);
            assert(s3.blocks.tracks(fp));
            assert(s4.blocks.pages@[fp] == s3.blocks.pages@[fp]);
        }

        // Q's tables for the path, through its capability.
        proof {
            lemma_cursor_block(base, 7);
            lemma_cursor_block(base, 8);
            assert(witness_block(s4, cursor_block(base, 6), first));
            assert(witness_block(s4, cursor_block(base, 7), first));
            assert(witness_block(s4, cursor_block(base, 8), first));
            assert(witness_block(s4, b6, first));
            assert(witness_block(s4, (b6 + PROCESS_BYTES) as usize, first));
            assert(witness_block(s4, (b6 + 2 * PROCESS_BYTES) as usize, first));
        }
        let ok5 = self.witness_path(process, WITNESS_SECOND_PROCESS_SLOT, bq, KERNEL_MEM_END_L4INDEX, b6, Ghost(nq), Ghost(2), Ghost(u), Ghost(first));
        let ghost s5 = *self;
        let ghost a5 = tree_of(&s5.table_pages, &s5.spaces);
        proof {
            assert(ok5);
            lemma_steps_kept(a4, a5);
            assert(walk_table(a5, base, path) == walk_table(a4, base, path));
            assert(walk_table(a5, bq, path) is Some);
            assert(space_mapping(a5, base) == space_mapping(a4, base));
            assert(space_mapping(a5, bq) == space_mapping(a4, bq));
            assert(a4.is_table(base));
            assert(a4.is_table(bq));
            assert(s5.spaces.records@[base].value().kind is Process);
            assert(s5.spaces.records@[bq].value().kind is Process);
            assert(witness_alive(s5, base));
            assert(witness_alive(s5, bq));
            lemma_witness_slot_kept(s4, s5, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2);
            lemma_witness_empty_kept(s4, s5, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize);
            assert(s4.blocks.tracks(fp));
            assert(s5.blocks.pages@[fp] == s4.blocks.pages@[fp]);
            assert(s5.blocks.regions_2m@ == s0.blocks.regions_2m@);
            assert(s5.blocks.regions_1g@ == s0.blocks.regions_1g@);
        }

        // The frame, at the second block's third page, in slot 3 of the root's leaf.
        proof {
            assert(block_within(bf, 0, first));
            assert(s5.can_retype_under(process, ROOT_UNTYPED_SLOT, bf, 0));
            assert(s5.blocks.small_free(fp, 0)) by {
                assert(!s5.blocks.covered(fp));
                assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] s5.blocks.pages@[fp + k].kind is Free by {
                    assert(k == 0);
                }
            }
            assert(s5.can_retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
        }
        let ok6 = self.retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf);
        let ghost s6 = *self;
        let ghost a6 = tree_of(&s6.table_pages, &s6.spaces);
        let ghost nf = (b1 + 3) as usize;
        let ghost cap = crate::capability::retype::frame_of(bf);
        proof {
            assert(ok6);
            assert(Self::frame_retyped(s5, s6, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
            assert(Self::retype_keeps(s5, s6, nf, fp, 0, None));
            assert(a6 == a5);
            assert(s6.payload_of(nf) == cap);
            assert(s6.list.nodes@[nf as int].depth == 2);
            assert(s6.view().holds(process, nf));
            assert(s6.is_cap(nf));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_FRAME_SLOT));
            assert(s6.tables.has_slot(&s6.list, process, WITNESS_FRAME_SLOT));
            assert(s6.tables.node_of(process, WITNESS_FRAME_SLOT) == nf);
            assert(witness_slot(s6, process, WITNESS_FRAME_SLOT, nf, cap, 2));
            assert(block_refs(&s6.blocks, block_ref(&s6.blocks, bf / PAGE_SZ)) == 1);
            // P's and Q's capabilities and records, and the root's, stay.
            assert(s5.is_cap(np));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_PROCESS_SLOT));
            assert(s5.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(witness_slot(s6, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2));
            assert(s5.is_cap(nq));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s5.tables.node_of(process, WITNESS_SECOND_PROCESS_SLOT) == nq);
            assert(witness_slot(s6, process, WITNESS_SECOND_PROCESS_SLOT, nq, process_of(bq), 2));
            assert(s5.processes.records@.contains_key(base));
            assert(s5.processes.records@.contains_key(bq));
            assert(witness_alive(s6, base));
            assert(witness_alive(s6, bq));
            assert(s5.tables.has_slot(&s5.list, process, ROOT_UNTYPED_SLOT));
            assert(s5.is_cap(u));
            assert(s6.tables.has_slot(&s6.list, process, ROOT_UNTYPED_SLOT));
            assert(s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s6.is_cap(u) && s6.payload_of(u) == first && s6.list.nodes@[u as int].depth == 1);
            assert(s5.processes.records@.contains_key(process));
            assert(s5.tables.roots@.contains_key(process));
            assert(witness_root(s6, process, u, first));
            assert(s6.spaces.records@[base].value().kind == SpaceKind::Process);
            assert(s6.spaces.records@[bq].value().kind == SpaceKind::Process);
        }

        // The frame at the path in P's space.
        let ghost entry = frame_map_entry(((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
        proof {
            s6.lemma_walk_table_facts(base, path);
            assert(!space_mapping(a6, base).contains_key(path));
            assert(walk(a6, base, path) is None);
            s6.lemma_level1_empty(base, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / PAGE_SZ);
            assert(s6.can_map(process, WITNESS_PROCESS_SLOT, SpaceKind::Process, path, WITNESS_FRAME_SLOT, 0));
        }
        let ok7 = self.map(process, WITNESS_PROCESS_SLOT, KERNEL_MEM_END_L4INDEX, 0, 0, 0, WITNESS_FRAME_SLOT, 0);
        let ghost s7 = *self;
        let ghost a7 = tree_of(&s7.table_pages, &s7.spaces);
        proof {
            assert(ok7);
            assert(Self::map_done(s6, s7, process, WITNESS_PROCESS_SLOT, path, WITNESS_FRAME_SLOT, 0));
            let t1 = walk_table(a6, base, path)->0;
            lemma_map_kept(s6, s7, mapping_node(t1, 0), nf);
            assert(space_mapping(a7, base) == space_mapping(a6, base).insert(path, entry));
            assert(space_mapping(a7, bq) == space_mapping(a6, bq));
            assert(walk_table(a7, bq, path) == walk_table(a6, bq, path));
            lemma_witness_slot_kept(s6, s7, process, ROOT_UNTYPED_SLOT, u, first, 1);
            lemma_witness_slot_kept(s6, s7, process, WITNESS_SECOND_PROCESS_SLOT, nq, process_of(bq), 2);
            lemma_witness_slot_kept(s6, s7, process, WITNESS_FRAME_SLOT, nf, cap, 2);
            assert(witness_root(s7, process, u, first));
            assert(witness_alive(s7, bq));
            assert(s7.spaces.records@[bq].value().kind == SpaceKind::Process);
            // The frame's block holds one more reference, the mapping's.
            assert(s6.blocks.tracks(fp));
            assert(block_ref(&s7.blocks, bf / PAGE_SZ) == block_ref(&s6.blocks, bf / PAGE_SZ));
            assert(block_refs(&s7.blocks, block_ref(&s7.blocks, bf / PAGE_SZ)) == 2);
        }

        // The frame at the path in Q's space.
        proof {
            s7.lemma_walk_table_facts(bq, path);
            assert(!space_mapping(a7, bq).contains_key(path));
            assert(walk(a7, bq, path) is None);
            s7.lemma_level1_empty(bq, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / PAGE_SZ);
            assert(s7.can_map(process, WITNESS_SECOND_PROCESS_SLOT, SpaceKind::Process, path, WITNESS_FRAME_SLOT, 0));
        }
        let ok8 = self.map(process, WITNESS_SECOND_PROCESS_SLOT, KERNEL_MEM_END_L4INDEX, 0, 0, 0, WITNESS_FRAME_SLOT, 0);
        proof {
            let s8 = *self;
            let a8 = tree_of(&s8.table_pages, &s8.spaces);
            assert(ok8);
            assert(Self::map_done(s7, s8, process, WITNESS_SECOND_PROCESS_SLOT, path, WITNESS_FRAME_SLOT, 0));
            assert(space_mapping(a8, bq) == space_mapping(a7, bq).insert(path, entry));
            assert(space_mapping(a8, base) == space_mapping(a7, base));
            assert(space_mapping(a8, base).contains_key(path));
            assert(space_mapping(a8, base)[path] == entry);
            assert(space_mapping(a8, bq).contains_key(path));
            assert(space_mapping(a8, bq)[path] == entry);
            assert(bq == base + 5 * PROCESS_BYTES);
            // Both walks end at the frame's page.
            let g = fp as usize;
            lemma_fundamental_div_mod(bf as int, PAGE_SZ as int);
            assert(fp * PAGE_SZ == bf);
            assert(entry.addr == bf);
            assert(entry.addr / PAGE_SZ == g);
            assert(walk_finds(a8, base, path, g));
            assert(walk_finds(a8, bq, path, g));
            // The root, its frame capability and the epoch stay.
            let t1 = walk_table(a6, base, path)->0;
            let t2 = walk_table(a7, bq, path)->0;
            let m1 = mapping_node(t1, 0);
            let m2 = mapping_node(t2, 0);
            lemma_map_kept(s7, s8, m2, nf);
            lemma_witness_slot_kept(s7, s8, process, WITNESS_FRAME_SLOT, nf, cap, 2);
            assert(witness_alive(s8, process));
            assert(s8.flush_epoch == s0.flush_epoch);
            assert(s5.list.wf() && s6.list.wf() && s7.list.wf() && s8.list.wf()) by {
                reveal(CapKernel::wf);
            }
            // No record named the frame's page before the frame was retyped: its page was free and no
            // typed region covered it.
            assert forall|m: usize| #[trigger] s5.mappings@.contains_key(m) implies !record_pages(s5.mappings@[m]).contains(g) by {
                if record_pages(s5.mappings@[m]).contains(g) {
                    assert(s5.mapped@.contains(g)) by {
                        reveal(CapKernel::wf);
                    }
                    let br = s5.lemma_mapped_block(g);
                    assert(s5.blocks.pages@[fp].kind is Free);
                    assert(!s5.blocks.covered(fp));
                    match br {
                        BlockRef::Small(b) => {
                            assert(b == g);
                        },
                        BlockRef::Two(r) => {
                            lemma_fundamental_div_mod_converse(fp, PAGES_PER_2M as int, r as int, fp - r * PAGES_PER_2M);
                            assert(region_2m(fp) == r);
                        },
                        BlockRef::One(r) => {
                            lemma_fundamental_div_mod_converse(fp, PAGES_PER_1G as int, r as int, fp - r * PAGES_PER_1G);
                            assert(region_1g(fp) == r);
                        },
                    }
                }
            }
            // The frame capability is new and childless; each map adds one childless child under it.
            assert(s6.mappings@ == s5.mappings@);
            assert(!s5.list.nodes@[nf as int].live);
            assert(s5.list.nodes@[u as int].live);
            assert(s6.list.is_child(u, nf));
            lemma_listed_live(s6.list, nf);
            lemma_added_children(s5.list, s6.list, nf, u);
            assert(s7.list.is_child(nf, m1));
            lemma_listed_live(s7.list, m1);
            lemma_added_children(s6.list, s7.list, m1, nf);
            assert(s8.list.is_child(nf, m2));
            lemma_listed_live(s8.list, m2);
            lemma_added_children(s7.list, s8.list, m2, nf);
            assert(s7.list.nodes@[m1 as int].live);
            assert(m1 != m2);
            assert(s8.list.is_child(nf, m1)) by {
                assert(s8.list.nodes@[m1 as int].live);
                lemma_child_kept(s7.list, s8.list, nf, m1);
            }
            assert(frame_shared(s8, nf, m1, m2, g)) by {
                assert forall|y: usize| #[trigger] s8.list.is_child(nf, y) implies y == m1 || y == m2 by {
                    if y != m1 && y != m2 {
                        assert(s7.list.is_child(nf, y));
                        assert(s6.list.is_child(nf, y));
                    }
                }
                assert forall|z: usize| !#[trigger] s8.list.is_child(m1, z) by {
                    if s8.list.is_child(m1, z) {
                        if z == m2 {
                            assert(s8.list.parent@[m2] == nf);
                        } else {
                            assert(s7.list.is_child(m1, z));
                        }
                    }
                }
                assert forall|m: usize| #[trigger] s8.mappings@.contains_key(m) && record_pages(s8.mappings@[m]).contains(g)
                    implies s8.list.is_child(nf, m) by {
                    if m != m1 && m != m2 {
                        assert(s5.mappings@.contains_key(m));
                        assert(s8.mappings@[m] == s5.mappings@[m]);
                    }
                }
            }
        }
        ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8
    }

    /// From the state boot leaves, as the root at `process`, with the nine free blocks of
    /// witness_root_maps_one_frame_into_two_processes: share a frame between P and Q as it does, then
    /// revoke the frame capability in slot 3 of the root's leaf. One revoke finishes, since the
    /// capability's run is the two mappings, within its budget and two epochs past boot's. At the end
    /// the capability stays, neither P's space nor Q's maps the path, the frame's page is not mapped,
    /// and no walk of any space finds it.
    #[verifier::spinoff_prover]
    pub fn witness_root_revokes_a_shared_frame(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@),
            image_tables_bound(image@) + 9 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let tree = tree_of(&final(self).table_pages, &final(self).spaces);
                let q = (base + 5 * PROCESS_BYTES) as usize;
                let path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
                let nf = (base + PROCESS_BYTES + 3) as usize;
                let fp = ((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize;
                &&& final(self).wf()
                &&& final(self).is_cap(nf)
                &&& forall|x: usize| !#[trigger] final(self).list.is_child(nf, x)
                &&& !space_mapping(tree, base).contains_key(path)
                &&& !space_mapping(tree, q).contains_key(path)
                &&& !final(self).mapped@.contains(fp)
                &&& forall|r: usize, p: SpacePath| !#[trigger] walk_finds(tree, r, p, fp)
            }),
    {
        hide(CapKernel::wf);
        let shared = self.witness_root_maps_one_frame_into_two_processes(root, process, leaf, frames, t, free, image, untyped, frame, base);
        let ghost s8 = *self;
        let ghost nf = (base + PROCESS_BYTES + 3) as usize;
        let ghost g = ((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize;
        let at = Position { through: None, index: WITNESS_FRAME_SLOT };
        proof {
            assert(s8.cap_at(process, at) == Some(nf));
            assert(s8.root_live(process));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let done = self.revoke(process, at, Tracked(&mut steps));
        proof {
            let s9 = *self;
            let a8 = tree_of(&s8.table_pages, &s8.spaces);
            let tree = tree_of(&s9.table_pages, &s9.spaces);
            let q = (base + 5 * PROCESS_BYTES) as usize;
            let path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
            assert(!(done is Refused));
            assert(s8.list.wf() && s9.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let (m1, m2) = choose|m1: usize, m2: usize| frame_shared(s8, nf, m1, m2, g);
            let gone = choose|gone: Seq<usize>| revoked_seq(s8.list, s9.list, nf, gone);
            // Every node the revoke took was below the capability, whose children have none, so it
            // was one of the two mappings, and it took at most two.
            assert forall|i: int| 0 <= i < gone.len() implies #[trigger] gone[i] == m1 || gone[i] == m2 by {
                let x = gone[i];
                assert forall|y: usize, z: usize| #[trigger] s8.list.is_child(nf, y) implies !#[trigger] s8.list.is_child(y, z) by {
                    assert(y == m1 || y == m2);
                }
                lemma_below_child(s8.list, nf, x);
            }
            if gone.len() > 2 {
                assert(gone[0] == m1 || gone[0] == m2);
                assert(gone[1] == m1 || gone[1] == m2);
                assert(gone[2] == m1 || gone[2] == m2);
                assert(gone[0] != gone[1] && gone[0] != gone[2] && gone[1] != gone[2]);
            }
            assert(s8.list.seq@.len() - s9.list.seq@.len() <= 2);
            // So the revoke stopped neither on its budget nor on the epoch: it finished.
            assert(s8.flush_epoch == 0);
            assert(s9.flush_epoch <= 2);
            assert(done is Done);
            assert(Self::cap_revoked_at(s8, s9, process, at));
            // A record after the revoke is one before, so it names the frame's page only as a child
            // of the capability, which has none left.
            assert(mapped_wf(s9.mapped@, s9.mappings@) && mappings_wf(&s9.list, &s9.tables, tree, &s9.blocks, s9.holders@, s9.mappings@)) by {
                reveal(CapKernel::wf);
            }
            if s9.mapped@.contains(g) {
                let m = choose|m: usize| #![trigger s9.mappings@[m]] s9.mappings@.contains_key(m) && record_pages(s9.mappings@[m]).contains(g);
                assert(s8.mappings@.contains_key(m) && s8.mappings@[m] == s9.mappings@[m]);
                assert(s8.list.is_child(nf, m));
                assert(mapping_wf(&s9.list, &s9.tables, tree, &s9.blocks, s9.holders@, s9.mappings@, m));
                lemma_child_kept(s8.list, s9.list, nf, m);
            }
            assert forall|r: usize, p: SpacePath| !#[trigger] walk_finds(tree, r, p, g) by {
                if walk_finds(tree, r, p, g) {
                    s9.lemma_walk_mapped(r, p, g);
                }
            }
            // A walk after it is the walk before, which found the frame's page.
            if space_mapping(tree, base).contains_key(path) {
                assert(walk(tree, base, path) == walk(a8, base, path));
                assert(walk_finds(tree, base, path, g));
            }
            if space_mapping(tree, q).contains_key(path) {
                assert(walk(tree, q, path) == walk(a8, q, path));
                assert(walk_finds(tree, q, path, g));
            }
        }
        match done {
            RevokeStep::Done => shared,
            _ => false,
        }
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of four free ones past those boot's tables took from the first untyped, and entry l4 of the
    /// root's level 4 table past the kernel's and under no page of the image: retype a leaf into root
    /// entry 2 of the root's table at the fourth block's first two pages, give the root's own space the
    /// level 3, 2 and 1 tables of the first page under entry l4 at the first three blocks, through its
    /// process capability, retype a frame at the fourth block's third page into slot 3 of the leaf, and
    /// map it there. Every step succeeds, and at the end the root's space maps what it did, the image,
    /// and the frame at that path, with the frame capability's rights.
    #[verifier::spinoff_prover]
    pub fn witness_root_maps_a_frame_into_its_own_space(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        base: usize,
        l4: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@),
            image_tables_bound(image@) + 4 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES,
            !image_l4(image@, l4),
        ensures
            ret,
            ({
                let tree = tree_of(&final(self).table_pages, &final(self).spaces);
                let path = SpacePath { l4, l3: 0, l2: 0, l1: 0 };
                let entry = frame_map_entry(((base + 26 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
                &&& final(self).wf()
                &&& space_mapping(tree, process) == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), process).insert(path, entry)
                &&& space_mapping(tree, process).contains_key(path)
                &&& space_mapping(tree, process)[path] == entry
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost a0 = tree_of(&s0.table_pages, &s0.spaces);
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost pn = (leaf@ + 1) as usize;
        let ghost d = s0.list.nodes@[pn as int].depth;
        let ghost path = SpacePath { l4, l3: 0, l2: 0, l1: 0 };
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            s0.lemma_process_space(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            assert(witness_root(s0, process, u, first));
            assert(witness_slot(s0, process, ROOT_PROCESS_SLOT, pn, process_of(process), d));
            // The four free blocks, one after another.
            assert(s0.root_untyped(process) == u);
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 4) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(base + 4 * PROCESS_BYTES <= NODE_SPACE);
            assert forall|j: int| 0 <= j < 4 implies #[trigger] witness_block(s0, cursor_block(base, j), first) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(s0.root_table_block(process, cursor_block(first.base, itb + j)));
            }
        }
        let lb = base + 3 * PROCESS_BYTES;
        let bf = lb + 2 * PAGE_SZ;
        let ghost fp = (bf / PAGE_SZ) as int;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(block_bytes(0) == PAGE_SZ);
            assert(cursor_block(base, 0) == base);
            assert(witness_block(s0, base, first));
            assert(base % PROCESS_BYTES == 0);
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            lemma_cursor_block(base, 3);
            assert(witness_block(s0, lb, first));
            lemma_block_page(lb, 0);
            lemma_block_page(lb, 2);
            assert(lb / PAGE_SZ == base / PAGE_SZ + 24);
            assert(fp == lb / PAGE_SZ + 2);
            assert(s0.blocks.pages@[lb / PAGE_SZ + 2].kind is Free);
            assert(!s0.blocks.covered(fp));
            // The root's process block is typed, so it lies outside the free fourth block.
            if lb / PAGE_SZ <= process / PAGE_SZ < lb / PAGE_SZ + 8 {
                assert(s0.blocks.pages@[lb / PAGE_SZ + (process / PAGE_SZ - lb / PAGE_SZ)].kind is Free);
            }
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, lb, 1));
            assert(s0.blocks.small_free((lb / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb));
        }
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb);
        let ghost s1 = *self;
        let ghost a1 = tree_of(&s1.table_pages, &s1.spaces);
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at, lb));
            assert(a1 == a0);
            assert(s1.tables.leaf(process, 2) == lb);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(witness_root(s1, process, u, first));
            assert(s0.tables.has_slot(&s0.list, process, ROOT_PROCESS_SLOT));
            assert(s0.is_cap(pn));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_PROCESS_SLOT));
            assert(s1.tables.node_of(process, ROOT_PROCESS_SLOT) == pn);
            assert(witness_slot(s1, process, ROOT_PROCESS_SLOT, pn, process_of(process), d));
            assert(witness_alive(s1, process));
            assert(index_ok(WITNESS_FRAME_SLOT) && index_entry(WITNESS_FRAME_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_FRAME_SLOT));
            assert(s1.tables.node_of(process, WITNESS_FRAME_SLOT) == lb + 3);
            assert(witness_empty(s1, process, WITNESS_FRAME_SLOT, (lb + 3) as usize));
            lemma_run_kept(s0, s1, base, 0, 3, first, (lb / PAGE_SZ) as int, lb / PAGE_SZ + 2);
            assert(s0.blocks.tracks(fp));
            assert(s1.blocks.pages@[fp].kind is Free);
            assert(s0.blocks.tracks((process / PAGE_SZ) as int));
            assert(s1.blocks.pages@[(process / PAGE_SZ) as int] == s0.blocks.pages@[(process / PAGE_SZ) as int]);
            assert(!s1.blocks.pages@[(process / PAGE_SZ) as int].dead);
            assert(a1.is_root(process));
            assert(a1.entry(process, l4).is_empty());
        }

        // The root's tables for the path, through its process capability.
        proof {
            assert(witness_block(s1, cursor_block(base, 0), first));
            assert(witness_block(s1, cursor_block(base, 1), first));
            assert(witness_block(s1, cursor_block(base, 2), first));
            assert(witness_block(s1, base, first));
            assert(witness_block(s1, (base + PROCESS_BYTES) as usize, first));
            assert(witness_block(s1, (base + 2 * PROCESS_BYTES) as usize, first));
        }
        let ok2 = self.witness_path(process, ROOT_PROCESS_SLOT, process, l4, base, Ghost(pn), Ghost(d), Ghost(u), Ghost(first));
        let ghost s2 = *self;
        let ghost a2 = tree_of(&s2.table_pages, &s2.spaces);
        proof {
            assert(ok2);
            assert(walk_table(a2, process, path) is Some);
            assert(space_mapping(a2, process) == space_mapping(a1, process));
            lemma_witness_empty_kept(s1, s2, process, WITNESS_FRAME_SLOT, (lb + 3) as usize);
            assert(s1.blocks.tracks(fp));
            assert(s2.blocks.pages@[fp] == s1.blocks.pages@[fp]);
            assert(s2.blocks.regions_2m@ == s0.blocks.regions_2m@);
            assert(s2.blocks.regions_1g@ == s0.blocks.regions_1g@);
        }

        // The frame, at the fourth block's third page, in slot 3 of the root's leaf.
        proof {
            assert(block_within(bf, 0, first));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bf, 0));
            assert(s2.blocks.small_free(fp, 0)) by {
                assert(!s2.blocks.covered(fp));
                assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] s2.blocks.pages@[fp + k].kind is Free by {
                    assert(k == 0);
                }
            }
            assert(s2.can_retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
        }
        let ok3 = self.retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf);
        let ghost s3 = *self;
        let ghost a3 = tree_of(&s3.table_pages, &s3.spaces);
        let ghost nf = (lb + 3) as usize;
        let ghost cap = crate::capability::retype::frame_of(bf);
        proof {
            assert(ok3);
            assert(Self::frame_retyped(s2, s3, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
            assert(Self::retype_keeps(s2, s3, nf, fp, 0, None));
            assert(a3 == a2);
            assert(s3.payload_of(nf) == cap);
            assert(s3.list.nodes@[nf as int].depth == 2);
            assert(s3.is_cap(nf));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_FRAME_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_FRAME_SLOT));
            assert(s3.tables.node_of(process, WITNESS_FRAME_SLOT) == nf);
            assert(block_refs(&s3.blocks, block_ref(&s3.blocks, bf / PAGE_SZ)) == 1);
            // The root's process capability and record stay.
            assert(s2.is_cap(pn));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_PROCESS_SLOT));
            assert(s2.tables.node_of(process, ROOT_PROCESS_SLOT) == pn);
            assert(s3.tables.has_slot(&s3.list, process, ROOT_PROCESS_SLOT));
            assert(s3.tables.node_of(process, ROOT_PROCESS_SLOT) == pn);
            assert(s3.is_cap(pn) && s3.payload_of(pn) == process_of(process));
            assert(s2.processes.records@.contains_key(process));
            assert(witness_alive(s3, process));
            assert(s3.wf());
            s3.lemma_process_space(pn);
            assert(s3.spaces.records@[process].value().kind == SpaceKind::Process);
        }

        // The frame at the path in the root's own space.
        let ghost entry = frame_map_entry(((base + 26 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
        proof {
            s3.lemma_walk_table_facts(process, path);
            assert(space_mapping(a3, process) == space_mapping(a0, process));
            // The path's l4 index is under no page of the image, and boot mapped only the image's.
            if space_mapping(a0, process).contains_key(path) {
                assert(crate::capability::boot_map::image_path(image@, path));
                let (ia, ix) = choose|ia: int, ix: int| 0 <= ia < image@.len() && #[trigger] in_virt_at(image@, ia, ix) && page_path(ix) == path;
                assert(in_virt_at(image@, ia, ix) && page_path(ix).l4 == l4);
                assert(image_l4(image@, l4));
            }
            assert(!space_mapping(a3, process).contains_key(path));
            assert(walk(a3, process, path) is None);
            s3.lemma_level1_empty(process, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / PAGE_SZ);
            assert(s3.can_map(process, ROOT_PROCESS_SLOT, SpaceKind::Process, path, WITNESS_FRAME_SLOT, 0));
        }
        let ok4 = self.map(process, ROOT_PROCESS_SLOT, l4, 0, 0, 0, WITNESS_FRAME_SLOT, 0);
        proof {
            let s4 = *self;
            let a4 = tree_of(&s4.table_pages, &s4.spaces);
            assert(ok4);
            assert(Self::map_done(s3, s4, process, ROOT_PROCESS_SLOT, path, WITNESS_FRAME_SLOT, 0));
            assert(space_mapping(a4, process) == space_mapping(a3, process).insert(path, entry));
            assert(space_mapping(a4, process) == space_mapping(a0, process).insert(path, entry));
            assert(space_mapping(a4, process).contains_key(path));
            assert(space_mapping(a4, process)[path] == entry);
        }
        ok1 && ok2 && ok3 && ok4
    }
}

} // verus!
