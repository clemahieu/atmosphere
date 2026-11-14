// SPDX-License-Identifier: MIT

//! The boot step that maps dom0's image in the root's space: each virtual page of each run is mapped
//! through map in the space of the root's process capability at ROOT_PROCESS_SLOT, from the frame
//! capability whose block holds its physical page, at slot ROOT_FRAME_SLOT plus that block's index, at
//! the page's offset into the block. Each mapping is then a node under that capability and carries the
//! run's rights. See design/root-process-at-boot/ and design/address-spaces-as-objects/.
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
#[cfg(verus_keep_ghost)]
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::decompose::*;
#[cfg(verus_keep_ghost)]
use crate::capability::endpoint::*;
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
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::steps::Steps;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
#[cfg(verus_keep_ghost)]
use crate::pagetable::entry::PageEntry;
use crate::define::*;

/// The physical page virtual page x of run maps.
pub open spec fn image_frame(run: ImageRun, x: int) -> usize {
    (run.phys + (x - run.virt)) as usize
}

/// The entry virtual page x of run gets: its physical page, with the run's rights.
pub open spec fn image_entry(run: ImageRun, x: int) -> PageEntry {
    frame_map_entry(image_frame(run, x), image_rights(run), false)
}

/// p is the path of a virtual page of one of the runs.
pub open spec fn image_path(runs: Seq<ImageRun>, p: SpacePath) -> bool {
    exists|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) && page_path(x) == p
}

/// The virtual page of page j of block u of run.
pub open spec fn block_virt(run: ImageRun, u: int, j: int) -> int {
    run.virt + (run_image_blocks(run)[u].0 - run.phys) + j
}

/// The slot of the frame capability for block u of run a.
pub open spec fn frame_slot(runs: Seq<ImageRun>, a: int, u: int) -> usize {
    (ROOT_FRAME_SLOT + image_offset(runs, a) + u) as usize
}

/// The mapping node of virtual page x of space s: the node of its entry in the level 1 table its path
/// reaches.
pub open spec fn page_node(tree: TableTree, s: usize, x: int) -> usize {
    mapping_node(walk_table(tree, s, page_path(x))->0, page_path(x).l1)
}

/// Virtual page x of run a is mapped once the runs before r are, and run r's pages before v.
pub open spec fn page_done(r: int, v: int, a: int, x: int) -> bool {
    a < r || (a == r && x < v)
}

/// Page j of block u of run a is mapped once the runs before r are, run r's blocks before k, and block
/// k's pages before i.
pub open spec fn block_page_done(r: int, k: int, i: int, a: int, u: int, j: int) -> bool {
    a < r || (a == r && (u < k || (u == k && j < i)))
}

/// The first virtual page of run r, where its maps start.
pub open spec fn run_start(runs: Seq<ImageRun>, r: int) -> int {
    if r < runs.len() { runs[r].virt as int } else { 0 }
}

/// The virtual page a path names, the inverse of page_path below 512 level 4 entries.
pub open spec fn path_page(p: SpacePath) -> int {
    p.l4 * PAGES_PER_L4 + p.l3 * PAGES_PER_1G + p.l2 * PAGES_PER_2M + p.l1
}

/// Every node live in a stays live in b, of the same kind and depth.
pub open spec fn nodes_kept(a: Tree, b: Tree) -> bool {
    forall|n: int| #![trigger b.nodes@[n]] 0 <= n < NODE_SPACE && a.nodes@[n].live ==> {
        &&& b.nodes@[n].live
        &&& b.nodes@[n].kind == a.nodes@[n].kind
        &&& b.nodes@[n].depth == a.nodes@[n].depth
    }
}

/// Block table b has typed what a had and no more: every tracked page has the kind it had and every
/// large region is typed or not as it was, so a block free in a is free in b.
pub open spec fn kinds_kept(a: &BlockTable, b: &BlockTable) -> bool {
    &&& forall|i: int| a.tracks(i) ==> (#[trigger] b.pages@[i]).kind == a.pages@[i].kind
    &&& forall|x: int| 0 <= x < NUM_2M ==> (#[trigger] b.regions_2m@[x]).typed == a.regions_2m@[x].typed
    &&& forall|x: int| 0 <= x < NUM_1G ==> (#[trigger] b.regions_1g@[x]).typed == a.regions_1g@[x].typed
}

/// A virtual page below 512 level 4 entries is the page its path names, and its level 1 index is in
/// range.
proof fn lemma_path_page(x: int)
    requires
        0 <= x < ENTRIES * PAGES_PER_L4,
    ensures
        path_page(page_path(x)) == x,
        page_path(x).l1 < ENTRIES,
{
    let q1 = x / ENTRIES as int;
    let q2 = x / PAGES_PER_1G as int;
    let q3 = x / PAGES_PER_L4 as int;
    lemma_fundamental_div_mod(x, ENTRIES as int);
    lemma_div_denominator(x, ENTRIES as int, ENTRIES as int);
    lemma_fundamental_div_mod(q1, ENTRIES as int);
    lemma_div_denominator(x, PAGES_PER_1G as int, ENTRIES as int);
    lemma_fundamental_div_mod(q2, ENTRIES as int);
    lemma_div_pos_is_pos(x, PAGES_PER_L4 as int);
    lemma_div_is_ordered(x, ENTRIES * PAGES_PER_L4 - 1, PAGES_PER_L4 as int);
    assert((ENTRIES * PAGES_PER_L4 - 1) / PAGES_PER_L4 as int == INDEX_MASK) by (compute_only);
    lemma_mod_bound(x, ENTRIES as int);
    lemma_mod_bound(q1, ENTRIES as int);
    lemma_mod_bound(q2, ENTRIES as int);
    assert(q1 / ENTRIES as int == q2);
    assert(q2 / ENTRIES as int == q3);
    assert(x == q3 * PAGES_PER_L4 + (q2 % ENTRIES as int) * PAGES_PER_1G + (q1 % ENTRIES as int) * PAGES_PER_2M + x % ENTRIES as int) by (nonlinear_arith)
        requires
            x == ENTRIES * q1 + x % ENTRIES as int,
            q1 == ENTRIES * q2 + q1 % ENTRIES as int,
            q2 == ENTRIES * q3 + q2 % ENTRIES as int,
    ;
}

/// A virtual page of a run lies below 512 level 4 entries.
proof fn lemma_virt_range(runs: Seq<ImageRun>, a: int, x: int)
    requires
        image_virt_wf(runs),
        0 <= a < runs.len(),
        in_virt_at(runs, a, x),
    ensures
        0 <= x < ENTRIES * PAGES_PER_L4,
{
    assert((x / PAGES_PER_L4 as int) < ENTRIES);
    if x >= ENTRIES * PAGES_PER_L4 {
        lemma_div_is_ordered(ENTRIES * PAGES_PER_L4 as int, x, PAGES_PER_L4 as int);
        assert((ENTRIES * PAGES_PER_L4 as int) / PAGES_PER_L4 as int == ENTRIES) by (compute_only);
    }
}

/// A run's frame capabilities carry the read right.
proof fn lemma_image_rights_read(run: ImageRun)
    ensures
        image_rights(run) & right_bit(Right::Read) != 0,
{
    let r = image_rights(run);
    assert(r == 1 || r == 3 || r == 5 || r == 7);
    assert(1u32 & 1 == 1 && 3u32 & 1 == 1 && 5u32 & 1 == 1 && 7u32 & 1 == 1) by (bit_vector);
}

/// A map after the page's: the map adds one node, mapping x0 of run r, to what was mapped once the
/// runs before r and run r's pages before x0 were; afterwards those before x0 + 1 are.
proof fn lemma_added_step(runs: Seq<ImageRun>, r: int, x0: int, added: IMap<SpacePath, PageEntry>)
    requires
        image_runs_apart(runs),
        image_virt_wf(runs),
        0 <= r < runs.len(),
        in_virt_at(runs, r, x0),
        forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) ==> {
            &&& added.contains_key(page_path(x)) == page_done(r, x0, a, x)
            &&& page_done(r, x0, a, x) ==> added[page_path(x)] == image_entry(runs[a], x)
        },
        forall|p: SpacePath| #[trigger] added.contains_key(p) ==> image_path(runs, p),
    ensures
        ({
            let next = added.insert(page_path(x0), image_entry(runs[r], x0));
            &&& !added.contains_key(page_path(x0))
            &&& forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) ==> {
                &&& next.contains_key(page_path(x)) == page_done(r, x0 + 1, a, x)
                &&& page_done(r, x0 + 1, a, x) ==> next[page_path(x)] == image_entry(runs[a], x)
            }
            &&& forall|p: SpacePath| #[trigger] next.contains_key(p) ==> image_path(runs, p)
        }),
{
    let next = added.insert(page_path(x0), image_entry(runs[r], x0));
    lemma_virt_range(runs, r, x0);
    lemma_path_page(x0);
    assert forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) implies {
        &&& next.contains_key(page_path(x)) == page_done(r, x0 + 1, a, x)
        &&& page_done(r, x0 + 1, a, x) ==> next[page_path(x)] == image_entry(runs[a], x)
    } by {
        lemma_virt_range(runs, a, x);
        lemma_path_page(x);
        if x == x0 && a != r {
            assert(!(in_virt_at(runs, a, x) && in_virt_at(runs, r, x)));
        }
    }
    assert forall|p: SpacePath| #[trigger] next.contains_key(p) implies image_path(runs, p) by {
        if p == page_path(x0) {
            assert(in_virt_at(runs, r, x0));
        }
    }
}

impl CapKernel {
    /// What the map step starts from, as the frame and table steps leave it: the root's process
    /// capability that may change its space, a space of kind Process; every page of every run walking to
    /// a level 1 table of that space whose entry for it is empty; each block of the runs a frame
    /// capability at its fixed slot with its run's rights; each physical page of the runs in a typed 2M
    /// region with at most ROOT_FRAME_SLOTS references.
    pub open spec fn maps_ready(&self, root: usize, process: usize, leaf2: usize, runs: Seq<ImageRun>) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let s = self.root_space(process);
        &&& self.wf()
        &&& self.root_tables_ready(process)
        &&& self.spaces.records@[s].value().kind == SpaceKind::Process
        &&& image_runs_wf(runs, self.blocks.page_count())
        &&& image_virt_wf(runs)
        &&& forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) ==> {
            &&& walk_table(tree, s, page_path(x)) is Some
            &&& tree.entry(walk_table(tree, s, page_path(x))->0, page_path(x).l1).is_empty()
        }
        &&& forall|a: int, u: int| #![trigger run_image_blocks(runs[a])[u]]
            0 <= a < runs.len() && 0 <= u < run_image_blocks(runs[a]).len() ==> self.root_frame_at(
                root,
                process,
                leaf2,
                image_offset(runs, a) + u,
                run_image_blocks(runs[a])[u],
                image_rights(runs[a]),
            )
        &&& forall|a: int, g: int| 0 <= a < runs.len() && #[trigger] in_run_at(image_phys(runs), a, g) ==> {
            &&& self.blocks.regions_2m@[g / PAGES_PER_2M as int].typed
            &&& self.blocks.regions_2m@[g / PAGES_PER_2M as int].refs <= ROOT_FRAME_SLOTS
        }
    }

    /// What the map step leaves: the capability tables, processes, threads and spaces as they were, and
    /// every block of memory typed or free as it was; the root's space maps each virtual page of each
    /// run to its physical page with its run's rights, and every other path as it did; every other
    /// space as it was; each mapping a child of the frame capability of its block; every table walk,
    /// and everyone's reach, as they were.
    pub open spec fn maps_done(pre: Self, post: Self, process: usize, runs: Seq<ImageRun>) -> bool {
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let b0 = tree_of(&post.table_pages, &post.spaces);
        let s = pre.root_space(process);
        &&& post.wf()
        &&& post.tables == pre.tables
        &&& post.processes == pre.processes
        &&& post.endpoints == pre.endpoints
        &&& post.threads == pre.threads
        &&& post.spaces == pre.spaces
        &&& post.list.seq@[0] == pre.list.seq@[0]
        &&& nodes_kept(pre.list, post.list)
        &&& kinds_kept(&pre.blocks, &post.blocks)
        &&& post.blocks.pages@[(s / PAGE_SZ) as int].dead == pre.blocks.pages@[(s / PAGE_SZ) as int].dead
        &&& forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) ==> {
            &&& space_mapping(b0, s).contains_key(page_path(x))
            &&& space_mapping(b0, s)[page_path(x)] == image_entry(runs[a], x)
        }
        &&& forall|p: SpacePath| #![trigger space_mapping(b0, s).contains_key(p)] !image_path(runs, p) ==> {
            &&& space_mapping(b0, s).contains_key(p) == space_mapping(a0, s).contains_key(p)
            &&& space_mapping(a0, s).contains_key(p) ==> space_mapping(b0, s)[p] == space_mapping(a0, s)[p]
        }
        &&& forall|t: usize| t != s ==> #[trigger] space_mapping(b0, t) == space_mapping(a0, t)
        &&& forall|a: int, u: int, j: int| #![trigger frame_slot(runs, a, u), block_virt(runs[a], u, j)]
            0 <= a < runs.len() && 0 <= u < run_image_blocks(runs[a]).len()
            && 0 <= j < pow2(run_image_blocks(runs[a])[u].1) ==> post.list.is_child(
            pre.tables.node_of(process, frame_slot(runs, a, u)),
            page_node(a0, s, block_virt(runs[a], u, j)),
        )
        &&& forall|t: usize, q: SpacePath| #[trigger] walk_table(b0, t, q) == walk_table(a0, t, q)
        &&& forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o)
    }

    /// What holds once the runs before r, run r's blocks before k and block k's pages before i are
    /// mapped, which is run r's virtual pages before v: the state is pre's but for the paths added to
    /// the root's space and their nodes, done maps, each a child of its block's frame capability.
    #[verifier::opaque]
    pub open spec fn maps_progress(
        cur: Self,
        pre: Self,
        process: usize,
        runs: Seq<ImageRun>,
        r: int,
        k: int,
        i: int,
        v: int,
        added: IMap<SpacePath, PageEntry>,
        done: int,
    ) -> bool {
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let b0 = tree_of(&cur.table_pages, &cur.spaces);
        let s = pre.root_space(process);
        &&& cur.wf()
        &&& cur.tables == pre.tables
        &&& cur.processes == pre.processes
        &&& cur.endpoints == pre.endpoints
        &&& cur.threads == pre.threads
        &&& cur.spaces == pre.spaces
        &&& cur.list.seq@[0] == pre.list.seq@[0]
        &&& nodes_kept(pre.list, cur.list)
        &&& kinds_kept(&pre.blocks, &cur.blocks)
        &&& cur.blocks.pages@[(s / PAGE_SZ) as int].dead == pre.blocks.pages@[(s / PAGE_SZ) as int].dead
        &&& forall|t: usize, q: SpacePath| #[trigger] walk_table(b0, t, q) == walk_table(a0, t, q)
        &&& forall|o1: ObjectId, o2: ObjectId| #[trigger] cur.view().reach(o1, o2) == pre.view().reach(o1, o2)
        &&& forall|t: usize| t != s ==> #[trigger] space_mapping(b0, t) == space_mapping(a0, t)
        &&& space_mapping(b0, s) == space_mapping(a0, s).union_prefer_right(added)
        &&& forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) ==> {
            &&& added.contains_key(page_path(x)) == page_done(r, v, a, x)
            &&& page_done(r, v, a, x) ==> added[page_path(x)] == image_entry(runs[a], x)
        }
        &&& forall|p: SpacePath| #[trigger] added.contains_key(p) ==> image_path(runs, p)
        &&& forall|a: int, g: int| 0 <= a < runs.len() && #[trigger] in_run_at(image_phys(runs), a, g) ==> {
            &&& cur.blocks.regions_2m@[g / PAGES_PER_2M as int].typed
            &&& cur.blocks.regions_2m@[g / PAGES_PER_2M as int].refs <= ROOT_FRAME_SLOTS + done
        }
        &&& forall|a: int, u: int, j: int| #![trigger frame_slot(runs, a, u), block_virt(runs[a], u, j)]
            0 <= a < runs.len() && 0 <= u < run_image_blocks(runs[a]).len()
            && 0 <= j < pow2(run_image_blocks(runs[a])[u].1) && block_page_done(r, k, i, a, u, j)
            ==> cur.list.is_child(
            pre.tables.node_of(process, frame_slot(runs, a, u)),
            page_node(a0, s, block_virt(runs[a], u, j)),
        )
    }

    /// A slot of the root's stays a slot while its nodes stay live, and a capability in it stays one, at
    /// its depth.
    proof fn lemma_slot_kept(pre: Self, cur: Self, process: usize, i: usize)
        requires
            pre.wf(),
            cur.tables == pre.tables,
            nodes_kept(pre.list, cur.list),
            pre.tables.has_slot(&pre.list, process, i),
        ensures
            cur.tables.has_slot(&cur.list, process, i),
            pre.is_cap(pre.tables.node_of(process, i)) ==> cur.is_cap(pre.tables.node_of(process, i)),
            cur.list.nodes@[pre.tables.node_of(process, i) as int].depth == pre.list.nodes@[pre.tables.node_of(process, i) as int].depth
                || !pre.is_cap(pre.tables.node_of(process, i)),
    {
        pre.lemma_slot(process, i);
        let leaf = pre.tables.leaf(process, index_entry(i));
        pre.tables.lemma_leaf(&pre.list, leaf);
        reveal(Tree::store_wf);
        assert(pre.list.store_wf());
        assert(pre.list.pages@.dom().contains(leaf));
        assert(cur.list.nodes@[leaf as int].live);
        let n = pre.tables.node_of(process, i);
        assert(n < NODE_SPACE);
        if pre.is_cap(n) {
            assert(cur.list.nodes@[n as int].live);
        }
    }

    /// A child stays a child across a map: the map's node was not live, so the child is not it, and
    /// only the map's node gains a parent.
    proof fn lemma_child_kept(a: Self, b: Self, c: usize, i: usize, node: usize, f: usize)
        requires
            a.wf(),
            b.wf(),
            a.list.is_child(c, i),
            !a.list.nodes@[node as int].live,
            b.list.parent@ == a.list.parent@.insert(node, f),
            b.list.seq@[0] == a.list.seq@[0],
            forall|n: int| #![trigger b.list.nodes@[n]] 0 <= n < NODE_SPACE && n != node
                ==> b.list.nodes@[n].live == a.list.nodes@[n].live,
        ensures
            b.list.is_child(c, i),
    {
        let k = choose|k: int| 0 <= k < a.list.seq@.len() && a.list.seq@[k] == i;
        a.list.lemma_link(k);
        assert(i != node);
        assert(b.list.nodes@[i as int].live);
        lemma_has(b.list.seq@, i);
    }

    /// The step's map is not refused: the capabilities it uses are as the frame step left them, the
    /// page's level 1 table is live and its entry empty, and the block's references are bounded by the
    /// maps so far.
    proof fn lemma_step_ready(
        pre: Self,
        cur: Self,
        root: usize,
        process: usize,
        leaf2: usize,
        runs: Seq<ImageRun>,
        r: int,
        k: int,
        i: int,
        v: int,
        added: IMap<SpacePath, PageEntry>,
        done: int,
    )
        requires
            pre.maps_ready(root, process, leaf2, runs),
            Self::maps_progress(cur, pre, process, runs, r, k, i, v, added, done),
            0 <= r < runs.len(),
            0 <= k < run_image_blocks(runs[r]).len(),
            0 <= i < pow2(run_image_blocks(runs[r])[k].1),
            run_image_blocks(runs[r])[k].1 <= IMAGE_ORDER,
            v == block_virt(runs[r], k, i),
            in_virt_at(runs, r, v),
            0 <= done <= PAGES_PER_2M * (image_offset(runs, r) + k) + i,
        ensures
            cur.wf(),
            cur.tables.roots@.contains_key(process),
            cur.root_live(process),
            cur.can_map(process, ROOT_PROCESS_SLOT, SpaceKind::Process, page_path(v), frame_slot(runs, r, k), i as usize),
            frame_of(cur.payload_of(cur.tables.node_of(process, frame_slot(runs, r, k))), i as usize) == image_frame(runs[r], v),
            cur.payload_of(cur.tables.node_of(process, frame_slot(runs, r, k))).rights == image_rights(runs[r]),
            cur.payload_of(cur.tables.node_of(process, ROOT_PROCESS_SLOT)).base == pre.root_space(process),
            0 <= image_offset(runs, r) + k < ROOT_FRAME_SLOTS,
    {
        hide(CapKernel::wf);
        reveal(CapKernel::maps_progress);
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let b0 = tree_of(&cur.table_pages, &cur.spaces);
        let s = pre.root_space(process);
        let p = page_path(v);
        let b = run_image_blocks(runs[r])[k];
        let t = image_offset(runs, r) + k;
        let slot = frame_slot(runs, r, k);
        let f = pre.tables.node_of(process, slot);
        let n = pre.tables.node_of(process, ROOT_PROCESS_SLOT);
        // The root's process capability.
        Self::lemma_slot_kept(pre, cur, process, ROOT_PROCESS_SLOT);
        // The page's table and entry.
        lemma_virt_range(runs, r, v);
        lemma_path_page(v);
        assert(walk_table(b0, s, p) == walk_table(a0, s, p));
        assert(!added.contains_key(p));
        assert(walk(a0, s, p) is None);
        assert(!space_mapping(a0, s).contains_key(p));
        assert(!space_mapping(b0, s).contains_key(p));
        assert(walk(b0, s, p) is None);
        cur.lemma_walk_table_facts(s, p);
        cur.lemma_level1_empty(s, p);
        // The frame capability.
        assert(pre.root_frame_at(root, process, leaf2, t, b, image_rights(runs[r])));
        assert(slot == (ROOT_FRAME_SLOT + t) as usize);
        Self::lemma_slot_kept(pre, cur, process, slot);
        lemma_image_rights_read(runs[r]);
        lemma2_to64();
        if b.1 < 9 {
            lemma_pow2_strictly_increases(b.1, 9);
        }
        let phys = image_phys(runs);
        assert(phys[r] == (runs[r].phys, runs[r].pages));
        assert(cur.blocks.tracks_run(runs[r].phys as int, runs[r].pages as int));
        let g = image_frame(runs[r], v);
        assert(g == b.0 + i);
        assert(in_run_at(phys, r, g as int));
        lemma_div_by_multiple(b.0 as int, PAGE_SZ as int);
        assert(frame_of(cur.payload_of(f), i as usize) == g);
        assert(block_ref(&cur.blocks, g) == BlockRef::Two(g / PAGES_PER_2M));
        // The maps done so far are at most a 2M region's pages a frame slot, which keeps the region's
        // references below usize::MAX.
        vstd::arithmetic::mul::lemma_mul_inequality(t, ROOT_FRAME_SLOTS as int, PAGES_PER_2M as int);
        vstd::arithmetic::mul::lemma_mul_is_commutative(t, PAGES_PER_2M as int);
        assert(ROOT_FRAME_SLOTS * PAGES_PER_2M <= u32::MAX) by (compute_only);
    }

    /// One map more keeps the progress, with the page added to the root's space and its node a child of
    /// its block's frame capability.
    proof fn lemma_step(
        pre: Self,
        cur: Self,
        post: Self,
        root: usize,
        process: usize,
        leaf2: usize,
        runs: Seq<ImageRun>,
        r: int,
        k: int,
        i: int,
        v: int,
        added: IMap<SpacePath, PageEntry>,
        done: int,
    )
        requires
            pre.maps_ready(root, process, leaf2, runs),
            Self::maps_progress(cur, pre, process, runs, r, k, i, v, added, done),
            0 <= r < runs.len(),
            0 <= k < run_image_blocks(runs[r]).len(),
            0 <= i < pow2(run_image_blocks(runs[r])[k].1),
            run_image_blocks(runs[r])[k].1 <= IMAGE_ORDER,
            v == block_virt(runs[r], k, i),
            in_virt_at(runs, r, v),
            0 <= done <= PAGES_PER_2M * (image_offset(runs, r) + k) + i,
            post.wf(),
            Self::map_done(cur, post, process, ROOT_PROCESS_SLOT, page_path(v), frame_slot(runs, r, k), i as usize),
        ensures
            Self::maps_progress(
                post,
                pre,
                process,
                runs,
                r,
                k,
                i + 1,
                v + 1,
                added.insert(page_path(v), image_entry(runs[r], v)),
                done + 1,
            ),
    {
        hide(CapKernel::wf);
        Self::lemma_step_ready(pre, cur, root, process, leaf2, runs, r, k, i, v, added, done);
        reveal(CapKernel::maps_progress);
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let c0 = tree_of(&cur.table_pages, &cur.spaces);
        let b0 = tree_of(&post.table_pages, &post.spaces);
        let s = pre.root_space(process);
        let p = page_path(v);
        let slot = frame_slot(runs, r, k);
        let f = cur.tables.node_of(process, slot);
        let node = mapping_node(walk_table(c0, s, p)->0, p.l1);
        let e = image_entry(runs[r], v);
        let next = added.insert(p, e);
        assert(walk_table(c0, s, p) == walk_table(a0, s, p));
        assert(node == page_node(a0, s, v));
        // The root's space gains the page.
        assert(space_mapping(b0, s) == space_mapping(c0, s).insert(p, e));
        assert(space_mapping(b0, s) =~= space_mapping(a0, s).union_prefer_right(next));
        lemma_added_step(runs, r, v, added);
        // Every other space, walk and reach.
        assert forall|t: usize| t != s implies #[trigger] space_mapping(b0, t) == space_mapping(a0, t) by {
            assert(space_mapping(b0, t) == space_mapping(c0, t));
        }
        assert forall|t: usize, q: SpacePath| #[trigger] walk_table(b0, t, q) == walk_table(a0, t, q) by {
            assert(walk_table(b0, t, q) == walk_table(c0, t, q));
        }
        assert(cur.spaces.records@[s].value().kind is Process);
        assert forall|o1: ObjectId, o2: ObjectId| #[trigger] post.view().reach(o1, o2) == pre.view().reach(o1, o2) by {
            assert(post.view().reach(o1, o2) == cur.view().reach(o1, o2));
        }
        // The nodes live before.
        assert(nodes_kept(pre.list, post.list)) by {
            assert forall|m: int| #![trigger post.list.nodes@[m]] 0 <= m < NODE_SPACE && pre.list.nodes@[m].live implies {
                &&& post.list.nodes@[m].live
                &&& post.list.nodes@[m].kind == pre.list.nodes@[m].kind
                &&& post.list.nodes@[m].depth == pre.list.nodes@[m].depth
            } by {
                assert(cur.list.nodes@[m].live);
                assert(m != node);
            }
        }
        // The references: the page's region gains one.
        let g0 = image_frame(runs[r], v);
        let br = block_ref(&cur.blocks, g0);
        assert(in_run_at(image_phys(runs), r, g0 as int));
        assert(br == BlockRef::Two(g0 / PAGES_PER_2M));
        // The root's space's own page is a small block, so its dead flag is not the region's.
        assert(c0.is_root(s));
        cur.lemma_table_base(s);
        assert(block_typed(&cur.blocks, BlockRef::Small(s / PAGE_SZ)));
        assert(block_dead(&post.blocks, BlockRef::Small(s / PAGE_SZ)) == block_dead(&cur.blocks, BlockRef::Small(s / PAGE_SZ)));
        assert forall|a: int, g: int| 0 <= a < runs.len() && #[trigger] in_run_at(image_phys(runs), a, g) implies {
            &&& post.blocks.regions_2m@[g / PAGES_PER_2M as int].typed
            &&& post.blocks.regions_2m@[g / PAGES_PER_2M as int].refs <= ROOT_FRAME_SLOTS + done + 1
        } by {
            assert(image_phys(runs)[a] == (runs[a].phys, runs[a].pages));
            assert(cur.blocks.tracks_run(runs[a].phys as int, runs[a].pages as int));
            let q = g / PAGES_PER_2M as int;
            lemma_div_pos_is_pos(g, PAGES_PER_2M as int);
            lemma_div_is_ordered(g, cur.blocks.page_count() as int - 1, PAGES_PER_2M as int);
            assert(0 <= q < NUM_2M);
            assert(post.blocks.regions_2m@[q].typed == cur.blocks.regions_2m@[q].typed);
            if q != g0 / PAGES_PER_2M {
                assert(block_typed(&cur.blocks, BlockRef::Two(q as usize)));
                assert(block_refs(&post.blocks, BlockRef::Two(q as usize)) == block_refs(&cur.blocks, BlockRef::Two(q as usize)));
            }
        }
        // The children: the ones before stay, and the page's node is one.
        assert forall|a: int, u: int, j: int| #![trigger frame_slot(runs, a, u), block_virt(runs[a], u, j)]
            0 <= a < runs.len() && 0 <= u < run_image_blocks(runs[a]).len()
            && 0 <= j < pow2(run_image_blocks(runs[a])[u].1) && block_page_done(r, k, i + 1, a, u, j)
            implies post.list.is_child(
            pre.tables.node_of(process, frame_slot(runs, a, u)),
            page_node(a0, s, block_virt(runs[a], u, j)),
        ) by {
            if block_page_done(r, k, i, a, u, j) {
                Self::lemma_child_kept(
                    cur,
                    post,
                    pre.tables.node_of(process, frame_slot(runs, a, u)),
                    page_node(a0, s, block_virt(runs[a], u, j)),
                    node,
                    f,
                );
            } else {
                assert(a == r && u == k && j == i);
            }
        }
    }

    /// The maps start with nothing added.
    proof fn lemma_maps_start(pre: Self, root: usize, process: usize, leaf2: usize, runs: Seq<ImageRun>)
        requires
            pre.maps_ready(root, process, leaf2, runs),
        ensures
            Self::maps_progress(pre, pre, process, runs, 0, 0, 0, run_start(runs, 0), IMap::empty(), 0),
    {
        reveal(CapKernel::maps_progress);
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let s = pre.root_space(process);
        assert(space_mapping(a0, s) =~= space_mapping(a0, s).union_prefer_right(IMap::<SpacePath, PageEntry>::empty()));
    }

    /// A block's pages all mapped, the next block starts.
    proof fn lemma_block_next(
        cur: Self,
        pre: Self,
        process: usize,
        runs: Seq<ImageRun>,
        r: int,
        k: int,
        i: int,
        v: int,
        added: IMap<SpacePath, PageEntry>,
        done: int,
    )
        requires
            Self::maps_progress(cur, pre, process, runs, r, k, i, v, added, done),
            0 <= r < runs.len(),
            0 <= k < run_image_blocks(runs[r]).len(),
            i == pow2(run_image_blocks(runs[r])[k].1),
        ensures
            Self::maps_progress(cur, pre, process, runs, r, k + 1, 0, v, added, done),
    {
        reveal(CapKernel::maps_progress);
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let s = pre.root_space(process);
        assert forall|a: int, u: int, j: int| #![trigger frame_slot(runs, a, u), block_virt(runs[a], u, j)]
            0 <= a < runs.len() && 0 <= u < run_image_blocks(runs[a]).len()
            && 0 <= j < pow2(run_image_blocks(runs[a])[u].1) && block_page_done(r, k + 1, 0, a, u, j)
            implies cur.list.is_child(
            pre.tables.node_of(process, frame_slot(runs, a, u)),
            page_node(a0, s, block_virt(runs[a], u, j)),
        ) by {
            assert(block_page_done(r, k, i, a, u, j));
        }
    }

    /// A run's blocks all mapped, the next run starts.
    proof fn lemma_run_next(
        cur: Self,
        pre: Self,
        process: usize,
        runs: Seq<ImageRun>,
        r: int,
        k: int,
        v: int,
        added: IMap<SpacePath, PageEntry>,
        done: int,
    )
        requires
            Self::maps_progress(cur, pre, process, runs, r, k, 0, v, added, done),
            0 <= r < runs.len(),
            k == run_image_blocks(runs[r]).len(),
            v == runs[r].virt + runs[r].pages,
        ensures
            Self::maps_progress(cur, pre, process, runs, r + 1, 0, 0, run_start(runs, r + 1), added, done),
    {
        reveal(CapKernel::maps_progress);
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let s = pre.root_space(process);
        assert forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) implies {
            &&& added.contains_key(page_path(x)) == page_done(r + 1, run_start(runs, r + 1), a, x)
            &&& page_done(r + 1, run_start(runs, r + 1), a, x) ==> added[page_path(x)] == image_entry(runs[a], x)
        } by {
            assert(page_done(r, v, a, x) == page_done(r + 1, run_start(runs, r + 1), a, x));
        }
        assert forall|a: int, u: int, j: int| #![trigger frame_slot(runs, a, u), block_virt(runs[a], u, j)]
            0 <= a < runs.len() && 0 <= u < run_image_blocks(runs[a]).len()
            && 0 <= j < pow2(run_image_blocks(runs[a])[u].1) && block_page_done(r + 1, 0, 0, a, u, j)
            implies cur.list.is_child(
            pre.tables.node_of(process, frame_slot(runs, a, u)),
            page_node(a0, s, block_virt(runs[a], u, j)),
        ) by {
            assert(block_page_done(r, k, 0, a, u, j));
        }
    }

    /// Every run mapped, the step's ensures hold.
    proof fn lemma_maps_end(pre: Self, cur: Self, process: usize, runs: Seq<ImageRun>, added: IMap<SpacePath, PageEntry>, done: int)
        requires
            Self::maps_progress(cur, pre, process, runs, runs.len() as int, 0, 0, 0, added, done),
        ensures
            Self::maps_done(pre, cur, process, runs),
    {
        reveal(CapKernel::maps_progress);
        let a0 = tree_of(&pre.table_pages, &pre.spaces);
        let b0 = tree_of(&cur.table_pages, &cur.spaces);
        let s = pre.root_space(process);
        assert forall|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_virt_at(runs, a, x) implies {
            &&& space_mapping(b0, s).contains_key(page_path(x))
            &&& space_mapping(b0, s)[page_path(x)] == image_entry(runs[a], x)
        } by {
            assert(page_done(runs.len() as int, 0, a, x));
            assert(added.contains_key(page_path(x)));
        }
        assert forall|p: SpacePath| #![trigger space_mapping(b0, s).contains_key(p)] !image_path(runs, p) implies {
            &&& space_mapping(b0, s).contains_key(p) == space_mapping(a0, s).contains_key(p)
            &&& space_mapping(a0, s).contains_key(p) ==> space_mapping(b0, s)[p] == space_mapping(a0, s)[p]
        } by {
            assert(!added.contains_key(p));
        }
        assert forall|a: int, u: int, j: int| #![trigger frame_slot(runs, a, u), block_virt(runs[a], u, j)]
            0 <= a < runs.len() && 0 <= u < run_image_blocks(runs[a]).len()
            && 0 <= j < pow2(run_image_blocks(runs[a])[u].1) implies cur.list.is_child(
            pre.tables.node_of(process, frame_slot(runs, a, u)),
            page_node(a0, s, block_virt(runs[a], u, j)),
        ) by {
            assert(block_page_done(runs.len() as int, 0, 0, a, u, j));
        }
    }

    /// Maps every virtual page of every run in the root's space, from the frame capability of the block
    /// that holds its physical page, at its offset into that block. Every map succeeds, which the requires
    /// prove, so nothing is refused. The root's space gains exactly the runs' pages, each with its run's
    /// rights; each mapping is a child of its block's frame capability; nothing else changes in any
    /// space, and nobody's reach.
    pub(crate) fn boot_root_maps(&mut self, Ghost(root): Ghost<usize>, process: usize, Ghost(leaf2): Ghost<usize>, runs: &[ImageRun])
        requires
            old(self).maps_ready(root, process, leaf2, runs@),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            Self::maps_done(*old(self), *final(self), process, runs@),
    {
        hide(CapKernel::wf);
        hide(CapKernel::maps_ready);
        let ghost pre = *self;
        let ghost mut added: IMap<SpacePath, PageEntry> = IMap::empty();
        let ghost mut done: int = 0;
        proof {
            Self::lemma_maps_start(pre, root, process, leaf2, runs@);
        }
        let mut idx: usize = 0;
        let mut r: usize = 0;
        while r < runs.len()
            invariant
                self.stale_epoch == pre.stale_epoch,
                self.flush_epoch == pre.flush_epoch,
                self.cores == pre.cores,
                self.devices == pre.devices,
                self.iommus.present == pre.iommus.present,
                pre.maps_ready(root, process, leaf2, runs@),
                r <= runs@.len(),
                idx as int == image_offset(runs@, r as int),
                0 <= done <= PAGES_PER_2M * idx,
                Self::maps_progress(*self, pre, process, runs@, r as int, 0, 0, run_start(runs@, r as int), added, done),
            decreases runs@.len() - r,
        {
            let phys = runs[r].phys;
            let virt = runs[r].virt;
            let pages = runs[r].pages;
            proof {
                reveal(CapKernel::maps_ready);
                assert(image_phys(runs@)[r as int] == (phys, pages));
                assert(pre.blocks.tracks_run(phys as int, pages as int));
                assert(pages > 0);
                assert(in_virt_at(runs@, r as int, virt + pages - 1));
                lemma_virt_range(runs@, r as int, virt + pages - 1);
                assert(run_image_blocks(runs@[r as int]).skip(0) =~= run_image_blocks(runs@[r as int]));
            }
            let mut ps = phys;
            let mut w = virt;
            let mut m = pages;
            let ghost mut k: int = 0;
            while m > 0
                invariant
                    self.stale_epoch == pre.stale_epoch,
                    self.flush_epoch == pre.flush_epoch,
                    self.cores == pre.cores,
                    self.devices == pre.devices,
                    self.iommus.present == pre.iommus.present,
                    pre.maps_ready(root, process, leaf2, runs@),
                    r < runs@.len(),
                    phys == runs@[r as int].phys,
                    virt == runs@[r as int].virt,
                    pages == runs@[r as int].pages,
                    pre.blocks.tracks_run(phys as int, pages as int),
                    virt + pages <= ENTRIES * PAGES_PER_L4,
                    virt <= w,
                    ps == phys + (w - virt),
                    ps + m == phys + pages,
                    0 <= k <= run_image_blocks(runs@[r as int]).len(),
                    run_image_blocks(runs@[r as int]).skip(k) == run_blocks(ps as nat, m as nat, IMAGE_ORDER as nat),
                    idx as int == image_offset(runs@, r as int) + k,
                    0 <= done <= PAGES_PER_2M * idx,
                    Self::maps_progress(*self, pre, process, runs@, r as int, k, 0, w as int, added, done),
                decreases m,
            {
                // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
                let tracked mut steps = Steps::fresh();
                let (o, size) = first_block(ps, m, IMAGE_ORDER, Tracked(&mut steps));
                proof {
                    lemma_order_below(ps as nat, m as nat, IMAGE_ORDER as nat);
                    let rest = run_blocks((ps + size) as nat, (m - size) as nat, IMAGE_ORDER as nat);
                    assert(run_blocks(ps as nat, m as nat, IMAGE_ORDER as nat) == seq![(ps as nat, o as nat)] + rest);
                    assert(run_image_blocks(runs@[r as int]).skip(k)[0] == (ps as nat, o as nat));
                    let blocks = run_image_blocks(runs@[r as int]);
                    assert(blocks.skip(k).skip(1) =~= rest);
                    assert(blocks.skip(k + 1) =~= blocks.skip(k).skip(1));
                    lemma2_to64();
                    if o < 9 {
                        lemma_pow2_strictly_increases(o as nat, 9);
                    }
                    reveal(CapKernel::maps_ready);
                    assert(pre.root_frame_at(
                        root,
                        process,
                        leaf2,
                        image_offset(runs@, r as int) + k,
                        run_image_blocks(runs@[r as int])[k],
                        image_rights(runs@[r as int]),
                    ));
                }
                let from = ROOT_FRAME_SLOT + idx;
                let mut j: usize = 0;
                while j < size
                    invariant
                        self.stale_epoch == pre.stale_epoch,
                        self.flush_epoch == pre.flush_epoch,
                        self.cores == pre.cores,
                        self.devices == pre.devices,
                        self.iommus.present == pre.iommus.present,
                        pre.maps_ready(root, process, leaf2, runs@),
                        r < runs@.len(),
                        phys == runs@[r as int].phys,
                        virt == runs@[r as int].virt,
                        pages == runs@[r as int].pages,
                        pre.blocks.tracks_run(phys as int, pages as int),
                        virt + pages <= ENTRIES * PAGES_PER_L4,
                        virt <= w,
                        ps == phys + (w - virt),
                        ps + m == phys + pages,
                        size <= m,
                        size as nat == pow2(o as nat),
                        o <= IMAGE_ORDER,
                        size <= PAGES_PER_2M,
                        0 <= k < run_image_blocks(runs@[r as int]).len(),
                        run_image_blocks(runs@[r as int])[k] == (ps as nat, o as nat),
                        run_image_blocks(runs@[r as int]).skip(k + 1) == run_blocks(
                            (ps + size) as nat,
                            (m - size) as nat,
                            IMAGE_ORDER as nat,
                        ),
                        idx as int == image_offset(runs@, r as int) + k,
                        idx < ROOT_FRAME_SLOTS,
                        from == ROOT_FRAME_SLOT + idx,
                        j <= size,
                        0 <= done <= PAGES_PER_2M * idx + j,
                        Self::maps_progress(*self, pre, process, runs@, r as int, k, j as int, w + j, added, done),
                    decreases size - j,
                {
                    let x = w + j;
                    let l4 = x / PAGES_PER_L4;
                    let l3 = x / PAGES_PER_1G % ENTRIES;
                    let l2 = x / PAGES_PER_2M % ENTRIES;
                    let l1 = x % ENTRIES;
                    let ghost cur = *self;
                    proof {
                        assert(SpacePath { l4, l3, l2, l1 } == page_path(x as int));
                        assert(block_virt(runs@[r as int], k, j as int) == x);
                        assert(in_virt_at(runs@, r as int, x as int));
                        assert(from == frame_slot(runs@, r as int, k));
                        Self::lemma_step_ready(pre, cur, root, process, leaf2, runs@, r as int, k, j as int, x as int, added, done);
                    }
                    let mapped = self.map(process, ROOT_PROCESS_SLOT, l4, l3, l2, l1, from, j);
                    proof {
                        assert(mapped);
                        Self::lemma_step(pre, cur, *self, root, process, leaf2, runs@, r as int, k, j as int, x as int, added, done);
                        added = added.insert(page_path(x as int), image_entry(runs@[r as int], x as int));
                        done = done + 1;
                    }
                    j = j + 1;
                }
                proof {
                    Self::lemma_block_next(*self, pre, process, runs@, r as int, k, size as int, (w + size) as int, added, done);
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(PAGES_PER_2M as int, idx as int, 1);
                }
                idx = idx + 1;
                ps = ps + size;
                w = w + size;
                m = m - size;
                proof {
                    k = k + 1;
                }
            }
            proof {
                assert(run_blocks(ps as nat, 0, IMAGE_ORDER as nat).len() == 0);
                assert(k == run_image_blocks(runs@[r as int]).len());
                lemma_runs_blocks_step(image_phys(runs@), r as int, IMAGE_ORDER as nat);
                assert(image_phys(runs@)[r as int] == (phys, pages));
                Self::lemma_run_next(*self, pre, process, runs@, r as int, k, w as int, added, done);
            }
            r = r + 1;
        }
        proof {
            Self::lemma_maps_end(pre, *self, process, runs@, added, done);
        }
    }
}

} // verus!
