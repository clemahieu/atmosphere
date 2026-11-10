//! The witnesses of two uses a process exists for. A creator can build a process that holds a capability
//! it chose and has a thread bound to it: from the state boot leaves, the root gives itself a leaf,
//! retypes a process and a thread bound to it, retypes a leaf into the new process's table and derives
//! an untyped into it. And the root can share memory between processes it built: it retypes two
//! processes, gives each space the tables of one path, retypes a frame and maps it at that path in
//! both. Every step is proven to succeed. Only Verus compiles this module, so no image contains it.
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
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::space::*;
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
        lemma_fundamental_div_mod(v, 512);
        lemma_fundamental_div_mod(v - 1, 512);
        lemma_mod_bound(v, 512);
        lemma_mod_bound(v - 1, 512);
        assert(run_regions(run) >= 0);
    }
}

/// Page k of the order-3 block at b is its k-th page, in the 2M and 1G regions its first page is in,
/// and at an even k starts an order-1 block; the next order-3 block starts 8 pages on.
proof fn lemma_block_page(b: usize, k: int)
    requires
        b % 32768 == 0,
        0 <= k < 8,
    ensures
        (b + k * 4096) / 4096 == b / 4096 + k,
        (b + k * 4096) % 4096 == 0,
        (b + 32768) / 4096 == b / 4096 + 8,
        region_2m(b / 4096 + k) == region_2m((b / 4096) as int),
        region_1g(b / 4096 + k) == region_1g((b / 4096) as int),
        k % 2 == 0 ==> (b + k * 4096) % 8192 == 0,
{
    let q = b as int / 32768;
    lemma_fundamental_div_mod(b as int, 32768);
    assert(b == 32768 * q);
    lemma_fundamental_div_mod_converse(b + k * 4096, 4096, 8 * q + k, 0);
    lemma_fundamental_div_mod_converse(b as int, 4096, 8 * q, 0);
    lemma_fundamental_div_mod_converse(b + 32768, 4096, 8 * q + 8, 0);
    lemma_fundamental_div_mod(q, 64);
    lemma_mod_pos_bound(q, 64);
    lemma_fundamental_div_mod_converse(8 * q + k, 512, q / 64, 8 * (q % 64) + k);
    lemma_fundamental_div_mod_converse(8 * q, 512, q / 64, 8 * (q % 64));
    lemma_fundamental_div_mod(q, 32768);
    lemma_mod_pos_bound(q, 32768);
    lemma_fundamental_div_mod_converse(8 * q + k, 262144, q / 32768, 8 * (q % 32768) + k);
    lemma_fundamental_div_mod_converse(8 * q, 262144, q / 32768, 8 * (q % 32768));
    if k % 2 == 0 {
        lemma_fundamental_div_mod(k, 2);
        lemma_fundamental_div_mod_converse(b + k * 4096, 8192, 4 * q + k / 2, 0);
    }
}

/// An order-3 block 32768-aligned from b, and its first page, which an order-1 block starts at.
proof fn lemma_aligned(b: usize)
    requires
        b % 32768 == 0,
    ensures
        b % 4096 == 0,
        b % 8192 == 0,
{
    lemma_fundamental_div_mod(b as int, 32768);
    lemma_fundamental_div_mod_converse(b as int, 4096, 8 * (b as int / 32768), 0);
    lemma_fundamental_div_mod_converse(b as int, 8192, 4 * (b as int / 32768), 0);
}

/// The j-th order-3 block from b is j blocks on, aligned, and starts 8j pages on.
proof fn lemma_cursor_block(b: usize, j: int)
    requires
        b % 32768 == 0,
        0 <= j,
        b + j * 32768 <= NODE_SPACE,
    ensures
        cursor_block(b, j) == b + j * 32768,
        cursor_block(b, j) % 32768 == 0,
        cursor_block(b, j) / 4096 == b / 4096 + 8 * j,
{
    let q = b as int / 32768;
    lemma_fundamental_div_mod(b as int, 32768);
    lemma_fundamental_div_mod_converse(b + j * 32768, 32768, q + j, 0);
    lemma_fundamental_div_mod_converse(b + j * 32768, 4096, 8 * q + 8 * j, 0);
    lemma_fundamental_div_mod_converse(b as int, 4096, 8 * q, 0);
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

/// The order-3 block at b lies in first and is free.
pub open spec fn witness_block(k: CapKernel, b: usize, first: Payload) -> bool {
    &&& block_within(b, 3, first)
    &&& k.blocks.tracks_addr_run(b, 8)
    &&& !k.blocks.covered((b / 4096) as int)
    &&& forall|j: int| 0 <= j < 8 ==> #[trigger] k.blocks.pages@[b / 4096 + j].kind is Free
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
        b / 4096 + 8 <= lo || hi <= b / 4096,
    ensures
        witness_block(post, b, first),
{
    assert forall|j: int| 0 <= j < 8 implies #[trigger] post.blocks.pages@[b / 4096 + j].kind is Free by {
        assert(pre.blocks.pages@[b / 4096 + j].kind is Free);
    }
}

/// So does a run of them, all on one side of lo up to hi.
proof fn lemma_run_kept(pre: CapKernel, post: CapKernel, b: usize, jlo: int, jhi: int, first: Payload, lo: int, hi: int)
    requires
        witness_run(pre, b, jlo, jhi, first),
        b % 32768 == 0,
        0 <= jlo,
        b + jhi * 32768 <= NODE_SPACE,
        post.blocks.regions_2m@ == pre.blocks.regions_2m@,
        post.blocks.regions_1g@ == pre.blocks.regions_1g@,
        forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(lo <= j < hi)
            ==> post.blocks.pages@[j].kind == pre.blocks.pages@[j].kind,
        hi <= b / 4096 + 8 * jlo || b / 4096 + 8 * jhi <= lo,
    ensures
        witness_run(post, b, jlo, jhi, first),
{
    assert forall|j: int| jlo <= j < jhi implies #[trigger] witness_block(post, cursor_block(b, j), first) by {
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
        forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % 4096 != 0
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
        if pre.tables.owner@.contains_key(page_of(x)) && x % 4096 < NODES_PER_PAGE && x != node {
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
    /// table has the one leaf, and the three slots hold what the steps put there.
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
                let child = (base + 49153) as usize;
                let thread = (base + 40960) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& final(self).view().holds(base, child)
                &&& final(self).list.is_child(u, child)
                &&& final(self).payload_of(child) == child_of(first, UNTYPED_RIGHTS, (base + 57344) as usize, 1)
                &&& bound_threads(&final(self).list, &final(self).tables).contains_key(thread)
                &&& bound_threads(&final(self).list, &final(self).tables)[thread] == base
                &&& final(self).acknowledged(base / 4096)
                &&& final(self).acknowledged(((base + 49152) / 4096) as usize)
                &&& final(self).acknowledged(((base + 49152) / 4096 + 1) as usize)
                &&& block_refs(&final(self).blocks, BlockRef::Small(thread / 4096)) == 1
                &&& block_refs(&final(self).blocks, BlockRef::Small(base / 4096)) == 2
                &&& final(self).process_unloaded(base)
                &&& final(self).tables.leaf(base, 0) == (base + 49152) as usize
                &&& forall|r: int| 1 <= r < ROOT_ENTRIES ==> #[trigger] final(self).tables.leaf(base, r) == NO_LEAF
                &&& final(self).slot_holds(process, WITNESS_PROCESS_SLOT, (base + 32769) as usize, process_of(base))
                &&& final(self).slot_holds(process, WITNESS_THREAD_SLOT, (base + 32770) as usize, thread_of(thread))
                &&& final(self).slot_holds(base, WITNESS_CHILD_SLOT, child, child_of(first, UNTYPED_RIGHTS, (base + 57344) as usize, 1))
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
            lemma_fundamental_div_mod(block_bytes(first.order), 32768);
            lemma_mod_bound(block_bytes(first.order), 32768);
            assert((itb + 2) * 32768 <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * 32768);
            assert(cursor_block(first.base, itb + 1) == base + 32768);
            // The first untyped is the first boot block, whose pages boot left acknowledged.
            lemma_runs_blocks(free@, MAX_ORDER as nat);
            let b0 = bs[0];
            assert(b0.1 <= MAX_ORDER && b0.0 + pow2(b0.1) <= NUM_PAGES);
            assert(b0.0 * 4096 <= NUM_PAGES * 4096) by (nonlinear_arith)
                requires
                    b0.0 <= NUM_PAGES,
            ;
            assert(first.base == b0.0 * 4096);
            assert((b0.1 as u8) as nat == b0.1);
            assert(block_bytes(first.order) == pow2(b0.1) * 4096);
            lemma_fundamental_div_mod_converse(base as int, 4096, b0.0 + 8 * itb, 0);
            assert(base / 4096 == b0.0 + 8 * itb);
            assert(8 * itb + 16 <= pow2(b0.1)) by (nonlinear_arith)
                requires
                    (itb + 2) * 32768 <= pow2(b0.1) * 4096,
            ;
            assert(in_page_block(bs[0], (base / 4096) as nat));
            assert(in_page_block(bs[0], (base / 4096 + 12) as nat));
            assert(in_page_block(bs[0], (base / 4096 + 13) as nat));
            assert(s0.acknowledged(base / 4096));
            assert(s0.acknowledged((base / 4096 + 12) as usize));
            assert(s0.acknowledged((base / 4096 + 13) as usize));
        }
        let b2 = base + 32768;
        let bt = b2 + 8192;
        let bl = b2 + 16384;
        let bd = b2 + 24576;
        proof {
            assert(block_bytes(3) == 32768);
            assert(block_bytes(1) == 8192);
            assert(base % 32768 == 0);
            assert(b2 % 32768 == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            lemma_block_page(b2, 4);
            lemma_block_page(b2, 6);
            assert(b2 / 4096 == base / 4096 + 8);
            assert(bt / 4096 == b2 / 4096 + 2);
            assert(bl / 4096 == b2 / 4096 + 4);
            assert(!s0.blocks.covered((base / 4096) as int));
            assert(!s0.blocks.covered((b2 / 4096) as int));
            assert(!s0.blocks.covered(b2 / 4096 + 2));
            assert(!s0.blocks.covered(b2 / 4096 + 4));
            assert forall|i: int| base / 4096 <= i < base / 4096 + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[base / 4096 + (i - base / 4096)].kind is Free);
            }
            assert forall|i: int| b2 / 4096 <= i < b2 / 4096 + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[b2 / 4096 + (i - b2 / 4096)].kind is Free);
            }
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b2, 1));
            assert(s0.blocks.small_free((b2 / 4096) as int, 1));
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
            assert forall|i: int| base / 4096 <= i < base / 4096 + 8 || b2 / 4096 + 2 <= i < b2 / 4096 + 8
                implies #[trigger] s1.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.tracks(i));
                assert(s0.blocks.pages@[i].kind is Free);
            }
        }

        // A process, in slot 1 of that leaf.
        proof {
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / 4096) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / 4096 + k].kind is Free by {
                    assert(s1.blocks.pages@[(base / 4096 + k) as int].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base);
        let ghost s2 = *self;
        let ghost np = (b2 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / 4096) as int, 3, None));
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
            assert forall|i: int| b2 / 4096 + 2 <= i < b2 / 4096 + 8 implies #[trigger] s2.blocks.pages@[i].kind is Free by {
                assert(s1.blocks.tracks(i));
                assert(s1.blocks.pages@[i].kind is Free);
            }
        }

        // A thread, in slot 2 of the root's leaf, bound to the process.
        proof {
            assert(block_refs(&s2.blocks, BlockRef::Small(base / 4096)) == 1);
            assert(!s2.cap_dead(np));
            assert(s2.can_hold_thread(process, WITNESS_PROCESS_SLOT));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(s2.blocks.small_free((bt / 4096) as int, THREAD_ORDER as usize)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s2.blocks.pages@[bt / 4096 + k].kind is Free by {
                    assert(s2.blocks.pages@[(b2 / 4096 + 2 + k) as int].kind is Free);
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
            assert(block_refs(&s3.blocks, BlockRef::Small(base / 4096)) == 2);
            assert(block_refs(&s3.blocks, BlockRef::Small(bt / 4096)) == 1);
            assert(s3.process_unloaded(base));
            assert(bound_threads(&s3.list, &s3.tables) == bound_threads(&s2.list, &s2.tables).insert(bt, base));
            assert(Self::retype_keeps(s2, s3, (b2 + 2) as usize, (bt / 4096) as int, 1, None));
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
            assert forall|i: int| b2 / 4096 + 4 <= i < b2 / 4096 + 6 implies #[trigger] s3.blocks.pages@[i].kind is Free by {
                assert(s2.blocks.tracks(i));
                assert(s2.blocks.pages@[i].kind is Free);
            }
        }

        // A leaf in root entry 0 of the new process's table, through the process capability.
        let at2 = Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 };
        proof {
            assert(s3.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s3.blocks.small_free((bl / 4096) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s3.blocks.pages@[bl / 4096 + k].kind is Free by {
                    assert(s3.blocks.pages@[(b2 / 4096 + 4 + k) as int].kind is Free);
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
            assert(s3.blocks.tracks((base / 4096) as int));
            assert(s3.blocks.tracks((bt / 4096) as int));
            assert(s4.blocks.pages@[(base / 4096) as int] == s3.blocks.pages@[(base / 4096) as int]);
            assert(s4.blocks.pages@[(bt / 4096) as int] == s3.blocks.pages@[(bt / 4096) as int]);
            assert(block_refs(&s4.blocks, BlockRef::Small(base / 4096)) == 2);
            assert(block_refs(&s4.blocks, BlockRef::Small(bt / 4096)) == 1);
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
            assert(child == base + 49153);
            assert(bt == base + 40960);
            assert(bd == base + 57344);
            // An untyped's derive leaves the blocks, and no step changed an acknowledgement.
            assert(s4.payload_of(s4.tables.node_of(process, ROOT_UNTYPED_SLOT)).kind is Untyped);
            assert(s5.blocks == s4.blocks);
            assert(block_refs(&s5.blocks, BlockRef::Small(base / 4096)) == 2);
            assert(block_refs(&s5.blocks, BlockRef::Small(bt / 4096)) == 1);
            assert(s5.process_unloaded(base));
            assert(s5.stale_epoch == s0.stale_epoch);
            assert(s5.cores == s0.cores);
            assert(s5.iommus == s0.iommus);
            assert(bl / 4096 == base / 4096 + 12);
            assert((base + 49152) / 4096 == bl / 4096);
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
            Self::lemma_acknowledged_kept(s0, s5, base / 4096);
            Self::lemma_acknowledged_kept(s0, s5, (base / 4096 + 12) as usize);
            Self::lemma_acknowledged_kept(s0, s5, (base / 4096 + 13) as usize);
        }
        ok1 && ok2 && ok3 && ok4 && ok5
    }

    /// Gives entry e of table t of space s a child table at the given level: the order-3 block at the
    /// cursor, retyped as a table page under the root's untyped at ROOT_UNTYPED_SLOT and linked through
    /// the capability to s's process at index i of the root's table. The entry is empty and the block
    /// free in the untyped, so it never refuses.
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
        u: Ghost<usize>,
        first: Ghost<Payload>,
    ) -> (ret: bool)
        requires
            old(self).wf(),
            witness_root(*old(self), process, u@, first@),
            witness_slot(*old(self), process, i, n@, process_of(s@), 2),
            witness_alive(*old(self), s@),
            witness_block(*old(self), cursor, first@),
            1 <= level <= 3,
            tree_of(&old(self).table_pages, &old(self).spaces).is_table(t),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).space == Some(s@),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).level == level + 1,
            !old(self).blocks.pages@[(t / 4096) as int].dead,
            tree_of(&old(self).table_pages, &old(self).spaces).child_slot(t, e),
            tree_of(&old(self).table_pages, &old(self).spaces).entry(t, e).is_empty(),
        ensures
            ret,
            final(self).wf(),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(cursor / 4096 <= j < cursor / 4096 + 8)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            nodes_kept(old(self).list, final(self).list),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j % 4096 != 0
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            steps_kept(tree_of(&old(self).table_pages, &old(self).spaces), tree_of(&final(self).table_pages, &final(self).spaces)),
            witness_root(*final(self), process, u@, first@),
            witness_slot(*final(self), process, i, n@, process_of(s@), 2),
            step(tree_of(&final(self).table_pages, &final(self).spaces), t, e) == Some(cursor),
            tree_of(&final(self).table_pages, &final(self).spaces).is_page(cursor),
            tree_of(&final(self).table_pages, &final(self).spaces).record(cursor).level == level,
            tree_of(&final(self).table_pages, &final(self).spaces).record(cursor).space == Some(s@),
            !final(self).blocks.pages@[(cursor / 4096) as int].dead,
            forall|j: usize| j < 512 ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(cursor, j).is_empty(),
    {
        // The body relates three states; their invariants stay folded, and the lemmas open them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            lemma2_to64();
            assert(block_bytes(3) == 32768);
            pre.lemma_table_base(t);
            assert(pre.blocks.pages@[cursor / 4096 + 0].kind is Free);
            pre.lemma_free_not_table(cursor, cursor / 4096);
            pre.lemma_slot(process, ROOT_UNTYPED_SLOT);
            pre.lemma_slot_bound(u@);
            pre.lemma_slot(process, i);
            pre.lemma_slot_bound(n@);
            assert(pre.blocks.small_free((cursor / 4096) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] pre.blocks.pages@[cursor / 4096 + k].kind is Free by {
                    assert(pre.blocks.pages@[cursor / 4096 + k].kind is Free);
                }
            }
            assert(pre.can_retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level));
            // The parent is a typed table, so it lies outside the free block.
            if cursor / 4096 <= t / 4096 < cursor / 4096 + 8 {
                assert(pre.blocks.pages@[cursor / 4096 + (t / 4096 - cursor / 4096)].kind is Free);
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
            assert(pre.blocks.tracks((t / 4096) as int));
            assert(mid.blocks.pages@[(t / 4096) as int] == pre.blocks.pages@[(t / 4096) as int]);
            lemma_witness_slot_kept(pre, mid, process, ROOT_UNTYPED_SLOT, u@, first@, 1);
            lemma_witness_slot_kept(pre, mid, process, i, n@, process_of(s@), 2);
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
            assert forall|j: usize| j < 512 implies #[trigger] b.entry(cursor, j).is_empty() by {
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
            assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % 4096 != 0
                implies post.list.nodes@[j].live == pre.list.nodes@[j].live by {
                assert(j != cursor);
            }
            assert(post.list == mid.list);
        }
        true
    }

    /// Gives space s the level 3, 2 and 1 tables of the path of the first page past the kernel's, at the
    /// three order-3 blocks from the cursor, through the capability to s's process at index i of the
    /// root's table. The space is fresh and the blocks free in the root's untyped, so it never refuses.
    #[verifier::spinoff_prover]
    fn witness_path(
        &mut self,
        process: usize,
        i: usize,
        s: usize,
        cursor: usize,
        n: Ghost<usize>,
        u: Ghost<usize>,
        first: Ghost<Payload>,
    ) -> (ret: bool)
        requires
            old(self).wf(),
            witness_root(*old(self), process, u@, first@),
            witness_slot(*old(self), process, i, n@, process_of(s), 2),
            witness_alive(*old(self), s),
            tree_of(&old(self).table_pages, &old(self).spaces).is_root(s),
            tree_of(&old(self).table_pages, &old(self).spaces).entry(s, KERNEL_MEM_END_L4INDEX).is_empty(),
            !old(self).blocks.pages@[(s / 4096) as int].dead,
            cursor + 98304 <= NODE_SPACE,
            witness_block(*old(self), cursor, first@),
            witness_block(*old(self), (cursor + 32768) as usize, first@),
            witness_block(*old(self), (cursor + 65536) as usize, first@),
        ensures
            ret,
            final(self).wf(),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(cursor / 4096 <= j < cursor / 4096 + 24)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            nodes_kept(old(self).list, final(self).list),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j % 4096 != 0
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            steps_kept(tree_of(&old(self).table_pages, &old(self).spaces), tree_of(&final(self).table_pages, &final(self).spaces)),
            witness_root(*final(self), process, u@, first@),
            witness_slot(*final(self), process, i, n@, process_of(s), 2),
            walk_table(tree_of(&final(self).table_pages, &final(self).spaces), s, SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 }) is Some,
    {
        // The body relates four states; their invariants stay folded, and the steps' contracts carry them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let ghost path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
        let c1 = cursor + 32768;
        let c2 = c1 + 32768;
        proof {
            lemma2_to64();
            assert(block_bytes(3) == 32768);
            pre.lemma_table_base(s);
            assert(cursor % 32768 == 0);
            assert(c1 % 32768 == 0);
            lemma_block_page(cursor, 0);
            lemma_block_page(c1, 0);
            assert(c1 / 4096 == cursor / 4096 + 8);
            assert(c2 / 4096 == cursor / 4096 + 16);
            assert(a.child_slot(s, KERNEL_MEM_END_L4INDEX));
        }
        let ok1 = self.witness_table(process, i, s, KERNEL_MEM_END_L4INDEX, 3, cursor, Ghost(s), n, u, first);
        let ghost s1 = *self;
        let ghost b1 = tree_of(&s1.table_pages, &s1.spaces);
        proof {
            lemma_witness_block_kept(pre, s1, c1, first@, (cursor / 4096) as int, cursor / 4096 + 8);
            lemma_witness_block_kept(pre, s1, c2, first@, (cursor / 4096) as int, cursor / 4096 + 8);
            s1.lemma_table_base(cursor);
            assert(b1.child_slot(cursor, 0));
        }
        let ok2 = self.witness_table(process, i, cursor, 0, 2, c1, Ghost(s), n, u, first);
        let ghost s2 = *self;
        let ghost b2 = tree_of(&s2.table_pages, &s2.spaces);
        proof {
            lemma_witness_block_kept(s1, s2, c2, first@, (c1 / 4096) as int, c1 / 4096 + 8);
            s2.lemma_table_base(c1);
            assert(b2.child_slot(c1, 0));
        }
        let ok3 = self.witness_table(process, i, c1, 0, 1, c2, Ghost(s), n, u, first);
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
            assert(step(b3, s, KERNEL_MEM_END_L4INDEX) == Some(cursor));
            assert(step(b3, cursor, 0) == Some(c1));
            assert(step(b3, c1, 0) == Some(c2));
            assert(walk_table(b3, s, path) == Some(c2));
            assert forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(cursor / 4096 <= j < cursor / 4096 + 24)
                implies post.blocks.pages@[j] == pre.blocks.pages@[j] by {
                assert(s1.blocks.pages@[j] == pre.blocks.pages@[j]);
                assert(s2.blocks.pages@[j] == s1.blocks.pages@[j]);
            }
            assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % 4096 != 0
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
    /// both spaces.
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
                let q = (base + 163840) as usize;
                let path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
                let entry = frame_map_entry(((base + 40960) / 4096) as usize, FRAME_RIGHTS, false);
                &&& final(self).wf()
                &&& base != process
                &&& q != process
                &&& base != q
                &&& space_mapping(tree, base).contains_key(path)
                &&& space_mapping(tree, base)[path] == entry
                &&& space_mapping(tree, q).contains_key(path)
                &&& space_mapping(tree, q)[path] == entry
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
            lemma_fundamental_div_mod(block_bytes(first.order), 32768);
            lemma_mod_bound(block_bytes(first.order), 32768);
            assert((itb + 9) * 32768 <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * 32768);
            assert(base + 9 * 32768 <= NODE_SPACE);
            assert forall|j: int| 0 <= j < 9 implies #[trigger] witness_block(s0, cursor_block(base, j), first) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(s0.root_table_block(process, cursor_block(first.base, itb + j)));
            }
        }
        let b1 = base + 32768;
        let bf = b1 + 8192;
        let b2 = b1 + 32768;
        let bq = b2 + 98304;
        let b6 = bq + 32768;
        let ghost fp = (bf / 4096) as int;
        proof {
            assert(block_bytes(3) == 32768);
            assert(block_bytes(1) == 8192);
            assert(block_bytes(0) == 4096);
            assert(cursor_block(base, 0) == base);
            assert(witness_block(s0, base, first));
            assert(base % 32768 == 0);
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            lemma_cursor_block(base, 5);
            lemma_cursor_block(base, 6);
            lemma_block_page(base, 0);
            lemma_block_page(b1, 0);
            lemma_block_page(b1, 2);
            assert(witness_block(s0, b1, first));
            assert(b1 / 4096 == base / 4096 + 8);
            assert(fp == b1 / 4096 + 2);
            assert(s0.blocks.pages@[b1 / 4096 + 2].kind is Free);
            assert(!s0.blocks.covered(fp));
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b1, 1));
            assert(s0.blocks.small_free((b1 / 4096) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[b1 / 4096 + k].kind is Free by {
                    assert(s0.blocks.pages@[b1 / 4096 + k].kind is Free);
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
            lemma_run_kept(s0, s1, base, 0, 1, first, (b1 / 4096) as int, b1 / 4096 + 2);
            lemma_run_kept(s0, s1, base, 2, 9, first, (b1 / 4096) as int, b1 / 4096 + 2);
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
            assert(s1.blocks.small_free((base / 4096) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / 4096 + k].kind is Free by {
                    assert(s1.blocks.pages@[base / 4096 + k].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
            assert(s1.blocks.pages@[base / 4096 + 0].kind is Free);
            s1.lemma_free_not_table(base, base / 4096);
        }
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base);
        let ghost s2 = *self;
        let ghost a2 = tree_of(&s2.table_pages, &s2.spaces);
        let ghost np = (b1 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / 4096) as int, 3, None));
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
            assert(!s2.blocks.pages@[(base / 4096) as int].dead);
            assert(space_mapping(a2, base) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty());
            // The blocks past P's and the frame's page stay free.
            lemma_run_kept(s1, s2, base, 2, 9, first, (base / 4096) as int, base / 4096 + 8);
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
            assert(witness_block(s2, (b2 + 32768) as usize, first));
            assert(witness_block(s2, (b2 + 65536) as usize, first));
        }
        let ok3 = self.witness_path(process, WITNESS_PROCESS_SLOT, base, b2, Ghost(np), Ghost(u), Ghost(first));
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
            assert(b2 / 4096 == base / 4096 + 16);
            lemma_run_kept(s2, s3, base, 5, 9, first, (b2 / 4096) as int, b2 / 4096 + 24);
            assert(s2.blocks.tracks(fp));
            assert(s3.blocks.pages@[fp] == s2.blocks.pages@[fp]);
            assert(s3.tables.leaf(process, 2) == b1);
        }

        // Q, in slot 2 of the root's leaf.
        proof {
            assert(witness_block(s3, cursor_block(base, 5), first));
            assert(witness_block(s3, bq, first));
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bq, 3));
            assert(s3.blocks.small_free((bq / 4096) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s3.blocks.pages@[bq / 4096 + k].kind is Free by {
                    assert(s3.blocks.pages@[bq / 4096 + k].kind is Free);
                }
            }
            assert(s3.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_SECOND_PROCESS_SLOT, bq, PROCESS_ORDER));
            assert(s3.blocks.pages@[bq / 4096 + 0].kind is Free);
            s3.lemma_free_not_table(bq, bq / 4096);
            assert(!a3.is_table(bq));
        }
        let ok4 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_SECOND_PROCESS_SLOT, bq);
        let ghost s4 = *self;
        let ghost a4 = tree_of(&s4.table_pages, &s4.spaces);
        let ghost nq = (b1 + 2) as usize;
        proof {
            assert(ok4);
            assert(Self::retype_keeps(s3, s4, nq, (bq / 4096) as int, 3, None));
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
            assert(!s4.blocks.pages@[(bq / 4096) as int].dead);
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
            lemma_run_kept(s3, s4, base, 6, 9, first, (bq / 4096) as int, bq / 4096 + 8);
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
            assert(witness_block(s4, (b6 + 32768) as usize, first));
            assert(witness_block(s4, (b6 + 65536) as usize, first));
        }
        let ok5 = self.witness_path(process, WITNESS_SECOND_PROCESS_SLOT, bq, b6, Ghost(nq), Ghost(u), Ghost(first));
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
            assert(block_refs(&s6.blocks, block_ref(&s6.blocks, bf / 4096)) == 1);
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
        let ghost entry = frame_map_entry(((base + 40960) / 4096) as usize, FRAME_RIGHTS, false);
        proof {
            s6.lemma_walk_table_facts(base, path);
            assert(!space_mapping(a6, base).contains_key(path));
            assert(walk(a6, base, path) is None);
            s6.lemma_level1_empty(base, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / 4096);
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
            assert(block_ref(&s7.blocks, bf / 4096) == block_ref(&s6.blocks, bf / 4096));
            assert(block_refs(&s7.blocks, block_ref(&s7.blocks, bf / 4096)) == 2);
        }

        // The frame at the path in Q's space.
        proof {
            s7.lemma_walk_table_facts(bq, path);
            assert(!space_mapping(a7, bq).contains_key(path));
            assert(walk(a7, bq, path) is None);
            s7.lemma_level1_empty(bq, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / 4096);
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
            assert(bq == base + 163840);
        }
        ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8
    }
}

} // verus!
