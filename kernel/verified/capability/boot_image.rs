//! The boot step that hands the root dom0's image: each run the loader mapped for dom0, which kernel/src
//! checked at the trust boundary, decomposes into aligned blocks of at most 512 pages, and each block
//! becomes a frame capability with its run's rights at consecutive slots of the root's second leaf from
//! ROOT_FRAME_SLOT, by boot_root_frame. See design/root-process-at-boot/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::block::*;
use crate::capability::boot::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_frame::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_memory::*;
use crate::capability::decompose::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::steps::Steps;
use crate::define::*;

/// How many frame capabilities the root's second leaf holds, from ROOT_FRAME_SLOT to its last slot.
pub const ROOT_FRAME_SLOTS: usize = 127;

/// The largest order of a block of dom0's image: 512 pages, so that each block lies in the one 2M
/// region boot_root_frame types as a large frame for it.
pub const IMAGE_ORDER: u8 = 9;

/// One run the loader mapped for dom0, in pages, as kernel/src checked it at the trust boundary: its
/// first virtual page, its first physical page, how many pages it has, and its rights.
pub struct ImageRun {
    pub virt: usize,
    pub phys: usize,
    pub pages: usize,
    pub writable: bool,
    pub executable: bool,
}

/// The rights of the frame capabilities for a run: read, then write and execute as the run has them.
pub open spec fn image_rights(run: ImageRun) -> u32 {
    (1 + (if run.writable { 2int } else { 0int }) + (if run.executable { 4int } else { 0int })) as u32
}

/// The runs' physical pages, as the first page and the page count of each.
pub open spec fn image_phys(runs: Seq<ImageRun>) -> Seq<(usize, usize)> {
    Seq::new(runs.len(), |a: int| (runs[a].phys, runs[a].pages))
}

/// Virtual page x is in run a.
pub open spec fn in_virt_at(runs: Seq<ImageRun>, a: int, x: int) -> bool {
    runs[a].virt as int <= x < runs[a].virt + runs[a].pages
}

/// What kernel/src checked of the runs, short of where their virtual pages lie in a space, which
/// mapping them checks: none is empty, their physical pages lie inside NUM_PAGES, and no physical or
/// virtual page is in two of them.
pub open spec fn image_runs_wf(runs: Seq<ImageRun>) -> bool {
    &&& runs_wf(image_phys(runs))
    &&& forall|a: int| #![trigger runs[a]] 0 <= a < runs.len() ==> runs[a].pages > 0
    &&& forall|a: int, b: int, x: int|
        0 <= a < runs.len() && 0 <= b < runs.len() && a != b ==> !(#[trigger] in_virt_at(runs, a, x)
            && #[trigger] in_virt_at(runs, b, x))
}

/// The blocks of the image, run by run, each as its first page and its order.
pub open spec fn image_blocks(runs: Seq<ImageRun>) -> Seq<(nat, nat)> {
    runs_blocks(image_phys(runs), IMAGE_ORDER as nat)
}

/// The blocks of one run.
pub open spec fn run_image_blocks(run: ImageRun) -> Seq<(nat, nat)> {
    run_blocks(run.phys as nat, run.pages as nat, IMAGE_ORDER as nat)
}

/// How many blocks the runs before run a have: the first of run a's is at this index.
pub open spec fn image_offset(runs: Seq<ImageRun>, a: int) -> int {
    runs_blocks(image_phys(runs).take(a), IMAGE_ORDER as nat).len() as int
}

/// The 2M region q holds a physical page of one of the runs.
pub open spec fn image_region(runs: Seq<ImageRun>, q: int) -> bool {
    exists|a: int, x: int| 0 <= a < runs.len() && #[trigger] in_run_at(image_phys(runs), a, x) && region_2m(x) == q
}

/// The 2M region block b lies in.
pub open spec fn block_region(b: (nat, nat)) -> int {
    b.0 as int / PAGES_PER_2M as int
}

/// One of the first k blocks lies in 2M region q.
pub open spec fn in_regions(bs: Seq<(nat, nat)>, k: int, q: int) -> bool {
    exists|t: int| 0 <= t < k && #[trigger] block_region(bs[t]) == q
}

/// The pages of 2M region q that m holds.
pub open spec fn region_keys(m: Map<usize, PagePerm4k>, q: int) -> Set<usize> {
    m.dom().filter(|j: usize| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M)
}

/// The blocks among the first k + 1 in region q are those among the first k, and block k's.
proof fn lemma_in_regions_step(bs: Seq<(nat, nat)>, k: int, q: int)
    requires
        0 <= k < bs.len(),
    ensures
        in_regions(bs, k + 1, q) <==> (in_regions(bs, k, q) || block_region(bs[k]) == q),
{
    if in_regions(bs, k + 1, q) {
        let t = choose|t: int| 0 <= t < k + 1 && #[trigger] block_region(bs[t]) == q;
        if t < k {
            assert(in_regions(bs, k, q));
        }
    }
    if in_regions(bs, k, q) {
        let t = choose|t: int| 0 <= t < k && #[trigger] block_region(bs[t]) == q;
        assert(in_regions(bs, k + 1, q));
    }
    if block_region(bs[k]) == q {
        assert(in_regions(bs, k + 1, q));
    }
}

/// A block at page s aligned to its order o of at most 9 is, by address, one boot_root_frame takes, in
/// the 2M region s is in.
proof fn lemma_image_base(s: usize, o: u8)
    requires
        s < NUM_PAGES,
        o <= IMAGE_ORDER,
        (s as nat) % pow2(o as nat) == 0,
    ensures
        (s * PAGE_SZ) as int % block_bytes(o) == 0,
        (s * PAGE_SZ) / PAGE_SZ as int == s,
        frame_region((s * PAGE_SZ) as usize) == s / PAGES_PER_2M,
{
    let p = pow2(o as nat) as int;
    lemma_pow2_pos(o as nat);
    lemma_fundamental_div_mod(s as int, p);
    let q = s as int / p;
    assert(s * PAGE_SZ == q * (p * PAGE_SZ)) by (nonlinear_arith)
        requires
            s == p * q + 0,
    ;
    lemma_mod_multiples_basic(q, p * PAGE_SZ);
    lemma_div_multiples_vanish(s as int, PAGE_SZ as int);
    assert((s * PAGE_SZ) as int == PAGE_SZ * (s as int));
}

/// A page of an aligned block of at most 512 pages lies in the 2M region the block does.
proof fn lemma_page_block_region(b: (nat, nat), x: nat)
    requires
        b.1 <= IMAGE_ORDER,
        b.0 % pow2(b.1) == 0,
        b.0 < NUM_PAGES,
        in_page_block(b, x),
    ensures
        region_2m(x as int) == block_region(b),
{
    let s = b.0 as usize;
    let o = b.1 as u8;
    lemma_image_base(s, o);
    lemma_block_in_2m((s * PAGE_SZ) as usize, o);
    let r = s as int / PAGES_PER_2M as int;
    assert(r * PAGES_PER_2M <= s && s + pow2(b.1) <= (r + 1) * PAGES_PER_2M);
    lemma_fundamental_div_mod_converse(x as int, PAGES_PER_2M as int, r, x - r * PAGES_PER_2M);
}

/// Counts the blocks the runs decompose into, or refuses when there are more than the root's second
/// leaf has slots for.
fn count_frames(runs: &[ImageRun]) -> (ret: Option<usize>)
    requires
        image_runs_wf(runs@),
    ensures
        ret matches Some(count) ==> count == image_blocks(runs@).len() && count <= ROOT_FRAME_SLOTS,
        ret is None ==> image_blocks(runs@).len() > ROOT_FRAME_SLOTS,
{
    let ghost phys = image_phys(runs@);
    let mut count: usize = 0;
    let mut r: usize = 0;
    while r < runs.len()
        invariant
            r <= runs@.len(),
            image_runs_wf(runs@),
            phys == image_phys(runs@),
            count == runs_blocks(phys.take(r as int), IMAGE_ORDER as nat).len(),
            count <= ROOT_FRAME_SLOTS,
        decreases runs@.len() - r,
    {
        let start = runs[r].phys;
        let n = runs[r].pages;
        proof {
            lemma_runs_blocks_step(phys, r as int, IMAGE_ORDER as nat);
            assert(phys[r as int] == (start, n));
            assert(start + n <= NUM_PAGES);
        }
        let mut s = start;
        let mut m = n;
        while m > 0
            invariant
                r < runs@.len(),
                image_runs_wf(runs@),
                phys == image_phys(runs@),
                s + m <= NUM_PAGES,
                count + run_blocks(s as nat, m as nat, IMAGE_ORDER as nat).len() == runs_blocks(
                    phys.take(r as int + 1),
                    IMAGE_ORDER as nat,
                ).len(),
                count <= ROOT_FRAME_SLOTS,
            decreases m,
        {
            // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
            let tracked mut steps = Steps::fresh();
            let (o, size) = first_block(s, m, IMAGE_ORDER, Tracked(&mut steps));
            proof {
                assert(run_blocks(s as nat, m as nat, IMAGE_ORDER as nat) == seq![(s as nat, o as nat)] + run_blocks(
                    (s + size) as nat,
                    (m - size) as nat,
                    IMAGE_ORDER as nat,
                ));
            }
            if count == ROOT_FRAME_SLOTS {
                proof {
                    lemma_runs_blocks_prefix(phys, r as int + 1, IMAGE_ORDER as nat);
                    assert(phys.take(phys.len() as int) =~= phys);
                }
                return None;
            }
            count = count + 1;
            s = s + size;
            m = m - size;
        }
        r = r + 1;
    }
    proof {
        assert(phys.take(phys.len() as int) =~= phys);
    }
    Some(count)
}

/// What holds once boot_root_image has put the first k blocks of the image: the second leaf's slots
/// from ROOT_FRAME_SLOT + k are as boot left them, the 2M regions of the first k blocks are typed
/// with a holder and at most k references and every other region and page is as it was, every node
/// outside those slots keeps its liveness and depth and every capability there its payload, the
/// permissions left are those of the image regions not yet typed, and the root's reach has grown by
/// exactly the first k blocks.
#[verifier::opaque]
pub open spec fn image_progress(
    cur: CapKernel,
    pre: CapKernel,
    root: usize,
    process: usize,
    leaf2: usize,
    runs: Seq<ImageRun>,
    bs: Seq<(nat, nat)>,
    k: int,
    perms: Map<usize, PagePerm4k>,
) -> bool {
    &&& cur.wf()
    &&& cur.list.seq@[0] == root
    &&& cur.tables.roots == pre.tables.roots
    &&& cur.tables.owner == pre.tables.owner
    &&& cur.threads == pre.threads
    &&& cur.processes == pre.processes
    &&& cur.spaces == pre.spaces
    &&& cur.table_pages == pre.table_pages
    &&& cur.list.pages@.dom() == pre.list.pages@.dom()
    &&& cur.blocks.free_perms == pre.blocks.free_perms
    &&& cur.blocks.regions_1g@ == pre.blocks.regions_1g@
    &&& forall|j: int| #![trigger cur.list.nodes@[j]] 0 <= j < NODE_SPACE && !(leaf2 + 1 <= j < leaf2 + 1 + k)
        ==> cur.list.nodes@[j].live == pre.list.nodes@[j].live && cur.list.nodes@[j].depth == pre.list.nodes@[j].depth
    &&& forall|x: usize| #![trigger cur.is_cap(x)] #![trigger pre.is_cap(x)]
        !(leaf2 + 1 <= x < leaf2 + 1 + k) ==> cur.is_cap(x) == pre.is_cap(x)
    &&& forall|x: usize| #![trigger pre.is_cap(x)] #![trigger cur.payload_of(x)]
        !(leaf2 + 1 <= x < leaf2 + 1 + k) && pre.is_cap(x) ==> cur.payload_of(x) == pre.payload_of(x)
    &&& forall|j: int| leaf2 + 1 + k <= j < leaf2 + NODES_PER_PAGE ==> !#[trigger] cur.list.nodes@[j].live
    &&& forall|q: int| 0 <= q < NUM_2M && #[trigger] in_regions(bs, k, q) ==> {
        &&& cur.blocks.regions_2m@[q].typed
        &&& !cur.blocks.regions_2m@[q].dead
        &&& cur.blocks.regions_2m@[q].refs <= k
        &&& cur.holders@.contains_key(BlockRef::Two(q as usize))
    }
    &&& forall|q: int| 0 <= q < NUM_2M && !in_regions(bs, k, q)
        ==> #[trigger] cur.blocks.regions_2m@[q] == pre.blocks.regions_2m@[q]
    &&& forall|j: int| pre.blocks.tracks(j) && !in_regions(bs, k, region_2m(j))
        ==> #[trigger] cur.blocks.pages@[j] == pre.blocks.pages@[j]
    &&& forall|q: int, j: usize| #![trigger image_region(runs, q), perms.contains_key(j)]
        image_region(runs, q) && !in_regions(bs, k, q) && q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> perms.contains_key(j)
    &&& forall|j: usize| #[trigger] perms.contains_key(j) ==> perms[j].addr() == j * PAGE_SZ
    &&& forall|o: usize| #[trigger] cur.view().reach(process, o) <==> (pre.view().reach(process, o) || in_blocks(bs, k, o))
    &&& forall|q: usize, o: usize| #[trigger] cur.view().reach(q, o) && !pre.view().reach(q, o) ==> in_blocks(bs, k, o)
}

impl CapKernel {
    /// Slot ROOT_FRAME_SLOT + t of the root's second leaf holds the frame capability for block b with
    /// rights, below the list's synthetic root.
    pub open spec fn root_frame_at(&self, root: usize, process: usize, leaf2: usize, t: int, b: (nat, nat), rights: u32) -> bool {
        let n = (leaf2 + 1 + t) as usize;
        &&& 0 <= t < ROOT_FRAME_SLOTS
        &&& self.tables.has_slot(&self.list, process, (ROOT_FRAME_SLOT + t) as usize)
        &&& self.tables.node_of(process, (ROOT_FRAME_SLOT + t) as usize) == n
        &&& self.is_cap(n)
        &&& self.payload_of(n) == boot_frame_payload((b.0 * PAGE_SZ) as usize, b.1 as u8, rights)
        &&& self.list.is_child(root, n)
        &&& self.list.nodes@[n as int].depth == 1
    }

    /// One frame capability more, for block k at page s of order o in 2M region s / 512, as
    /// boot_root_frame puts it at slot ROOT_FRAME_SLOT + k, keeps image_progress and says it of the
    /// first k + 1 blocks, with that region's permissions taken out.
    proof fn lemma_image_step(
        pre: Self,
        cur: Self,
        post: Self,
        root: usize,
        process: usize,
        leaf2: usize,
        runs: Seq<ImageRun>,
        bs: Seq<(nat, nat)>,
        k: int,
        s: usize,
        o: u8,
        perms: Map<usize, PagePerm4k>,
        left: Map<usize, PagePerm4k>,
    )
        requires
            image_progress(cur, pre, root, process, leaf2, runs, bs, k, perms),
            0 <= k < bs.len(),
            bs.len() <= ROOT_FRAME_SLOTS,
            leaf2 + NODES_PER_PAGE <= NODE_SPACE,
            bs[k] == (s as nat, o as nat),
            cur.blocks.tracks(s as int),
            forall|q: int| #[trigger] image_region(runs, q) ==> !pre.blocks.regions_2m@[q].typed,
            image_region(runs, (s / PAGES_PER_2M) as int),
            left == perms.remove_keys(region_keys(perms, (s / PAGES_PER_2M) as int)),
            forall|x: usize| #[trigger] block_in(bs[k], x) == in_block((s * PAGE_SZ) as usize, o, x),
            ({
                let child = (leaf2 + 1 + k) as usize;
                let r = s / PAGES_PER_2M;
                let held = if cur.holders@.contains_key(BlockRef::Two(r)) {
                    cur.holders@[BlockRef::Two(r)]
                } else {
                    Set::<usize>::empty()
                };
                let refs = if cur.blocks.regions_2m@[r as int].typed { cur.blocks.regions_2m@[r as int].refs as int } else { 0 };
                &&& post.wf()
                &&& post.list.seq@[0] == root
                &&& post.tables.roots == cur.tables.roots
                &&& post.tables.owner == cur.tables.owner
                &&& Self::adds_cap(cur, post, child)
                &&& forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j != child
                    ==> post.list.nodes@[j].live == cur.list.nodes@[j].live
                    && post.list.nodes@[j].depth == cur.list.nodes@[j].depth
                &&& post.blocks.regions_2m@[r as int].typed
                &&& !post.blocks.regions_2m@[r as int].dead
                &&& post.blocks.regions_2m@[r as int].refs == refs + 1
                &&& post.blocks.regions_2m@ == cur.blocks.regions_2m@.update(r as int, post.blocks.regions_2m@[r as int])
                &&& post.blocks.regions_1g@ == cur.blocks.regions_1g@
                &&& post.holders@ == cur.holders@.insert(BlockRef::Two(r), held.insert(child))
                &&& forall|j: int| cur.blocks.tracks(j) && region_2m(j) != r ==> #[trigger] post.blocks.pages@[j] == cur.blocks.pages@[j]
                &&& post.blocks.free_perms == cur.blocks.free_perms
                &&& post.threads == cur.threads
                &&& post.processes == cur.processes
                &&& post.spaces == cur.spaces
                &&& post.table_pages == cur.table_pages
                &&& post.list.pages@.dom() == cur.list.pages@.dom()
                &&& forall|x: usize| #[trigger] post.view().reach(process, x)
                    <==> (cur.view().reach(process, x) || in_block((s * PAGE_SZ) as usize, o, x))
                &&& forall|q: usize, x: usize| #[trigger] post.view().reach(q, x) && !cur.view().reach(q, x)
                    ==> in_block((s * PAGE_SZ) as usize, o, x)
            }),
        ensures
            image_progress(post, pre, root, process, leaf2, runs, bs, k + 1, left),
    {
        reveal(image_progress);
        let child = (leaf2 + 1 + k) as usize;
        let r = s / PAGES_PER_2M;
        assert(child as int == leaf2 + 1 + k);
        assert(block_region(bs[k]) == r as int);
        assert forall|q: int| #[trigger] in_regions(bs, k + 1, q) <==> (in_regions(bs, k, q) || q == r as int) by {
            lemma_in_regions_step(bs, k, q);
        }
        // The region was typed before only by an earlier block of the image.
        if cur.blocks.regions_2m@[r as int].typed {
            if !in_regions(bs, k, r as int) {
                assert(cur.blocks.regions_2m@[r as int] == pre.blocks.regions_2m@[r as int]);
            }
            assert(in_regions(bs, k, r as int));
        }
        assert forall|q: int| 0 <= q < NUM_2M && #[trigger] in_regions(bs, k + 1, q) implies {
            &&& post.blocks.regions_2m@[q].typed
            &&& !post.blocks.regions_2m@[q].dead
            &&& post.blocks.regions_2m@[q].refs <= k + 1
            &&& post.holders@.contains_key(BlockRef::Two(q as usize))
        } by {
            if q != r as int {
                assert(in_regions(bs, k, q));
                assert(post.blocks.regions_2m@[q] == cur.blocks.regions_2m@[q]);
                assert(BlockRef::Two(q as usize) != BlockRef::Two(r));
            }
        }
        assert forall|q: int| 0 <= q < NUM_2M && !in_regions(bs, k + 1, q)
            implies #[trigger] post.blocks.regions_2m@[q] == pre.blocks.regions_2m@[q] by {
            assert(q != r as int);
            assert(post.blocks.regions_2m@[q] == cur.blocks.regions_2m@[q]);
        }
        assert forall|j: int| pre.blocks.tracks(j) && !in_regions(bs, k + 1, region_2m(j))
            implies #[trigger] post.blocks.pages@[j] == pre.blocks.pages@[j] by {
            assert(region_2m(j) != r as int);
        }
        assert forall|q: int, j: usize| #![trigger image_region(runs, q), left.contains_key(j)]
            image_region(runs, q) && !in_regions(bs, k + 1, q) && q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M implies left.contains_key(j) by {
            assert(q != r as int);
            assert(perms.contains_key(j));
            assert(!region_keys(perms, r as int).contains(j));
        }
        assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && !(leaf2 + 1 <= j < leaf2 + 1 + (k + 1))
            implies post.list.nodes@[j].live == pre.list.nodes@[j].live && post.list.nodes@[j].depth == pre.list.nodes@[j].depth by {
            assert(cur.list.nodes@[j].live == pre.list.nodes@[j].live);
            assert(cur.list.nodes@[j].depth == pre.list.nodes@[j].depth);
        }
        assert forall|x: usize| !(leaf2 + 1 <= x < leaf2 + 1 + (k + 1)) implies #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            assert(x != child);
            assert(post.is_cap(x) == cur.is_cap(x));
            assert(cur.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: usize| !(leaf2 + 1 <= x < leaf2 + 1 + (k + 1)) && #[trigger] pre.is_cap(x)
            implies post.payload_of(x) == pre.payload_of(x) by {
            assert(x != child);
            assert(cur.is_cap(x));
            assert(post.payload_of(x) == cur.payload_of(x));
            assert(cur.payload_of(x) == pre.payload_of(x));
        }
        assert forall|j: int| leaf2 + 1 + (k + 1) <= j < leaf2 + NODES_PER_PAGE implies !#[trigger] post.list.nodes@[j].live by {
            assert(!cur.list.nodes@[j].live);
        }
        assert forall|x: usize| #[trigger] post.view().reach(process, x)
            <==> (pre.view().reach(process, x) || in_blocks(bs, k + 1, x)) by {
            if in_blocks(bs, k, x) {
                let t = choose|t: int| 0 <= t < k && #[trigger] block_in(bs[t], x);
                assert(in_blocks(bs, k + 1, x));
            }
            if block_in(bs[k], x) {
                assert(in_blocks(bs, k + 1, x));
            }
            if in_blocks(bs, k + 1, x) {
                let t = choose|t: int| 0 <= t < k + 1 && #[trigger] block_in(bs[t], x);
                if t < k {
                    assert(in_blocks(bs, k, x));
                }
            }
            assert(cur.view().reach(process, x) <==> (pre.view().reach(process, x) || in_blocks(bs, k, x)));
        }
        assert forall|q: usize, x: usize| #[trigger] post.view().reach(q, x) && !pre.view().reach(q, x)
            implies in_blocks(bs, k + 1, x) by {
            if cur.view().reach(q, x) {
                let t = choose|t: int| 0 <= t < k && #[trigger] block_in(bs[t], x);
                assert(in_blocks(bs, k + 1, x));
            } else {
                assert(block_in(bs[k], x));
                assert(in_blocks(bs, k + 1, x));
            }
        }
    }

    /// A frame capability boot put earlier stays where it is, as it was, through a later step that
    /// adds one capability elsewhere in the second leaf.
    proof fn lemma_frame_kept(
        cur: Self,
        post: Self,
        root: usize,
        process: usize,
        leaf2: usize,
        child: usize,
        t: int,
        b: (nat, nat),
        rights: u32,
    )
        requires
            cur.root_frame_at(root, process, leaf2, t, b, rights),
            cur.list.seq@[0] == root,
            cur.tables.leaf(process, 1) == leaf2,
            leaf2 + NODES_PER_PAGE <= NODE_SPACE,
            child != leaf2,
            post.wf(),
            post.list.seq@[0] == root,
            post.tables.roots == cur.tables.roots,
            Self::adds_cap(cur, post, child),
            forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j != child
                ==> post.list.nodes@[j].live == cur.list.nodes@[j].live
                && post.list.nodes@[j].depth == cur.list.nodes@[j].depth,
            post.list.parent@ == cur.list.parent@.insert(child, root),
        ensures
            post.root_frame_at(root, process, leaf2, t, b, rights),
    {
        let x = (leaf2 + 1 + t) as usize;
        let i = (ROOT_FRAME_SLOT + t) as usize;
        assert(cur.list.nodes@[x as int].live);
        assert(x != child);
        assert(index_entry(i) == 1);
        assert(post.list.nodes@[leaf2 as int].live == cur.list.nodes@[leaf2 as int].live);
        assert(post.tables.has_slot(&post.list, process, i));
        assert(post.is_cap(x));
        assert(post.payload_of(x) == cur.payload_of(x));
        assert(post.list.nodes@[x as int].live);
        assert(has(post.list.seq@, x));
        lemma_has(post.list.seq@, x);
        assert(cur.list.is_child(root, x));
        assert(post.list.parent@[x] == root);
        assert(post.list.is_child(root, x));
    }

    /// Before block k at page s goes in: the slot boot_root_frame fills is the second leaf's next empty
    /// one, and the block's 2M region is typed exactly when an earlier block of the image lies in it,
    /// so it is either typed with a holder and room for one more reference, or as boot found it,
    /// reserved, with its pages' permissions at hand and no list page in it.
    proof fn lemma_image_ready(
        pre: Self,
        cur: Self,
        root: usize,
        process: usize,
        leaf2: usize,
        runs: Seq<ImageRun>,
        bs: Seq<(nat, nat)>,
        k: int,
        s: usize,
        perms: Map<usize, PagePerm4k>,
    )
        requires
            image_progress(cur, pre, root, process, leaf2, runs, bs, k, perms),
            0 <= k < bs.len(),
            bs.len() <= ROOT_FRAME_SLOTS,
            leaf2 + NODES_PER_PAGE <= NODE_SPACE,
            bs[k].0 == s as nat,
            cur.blocks.tracks(s as int),
            image_region(runs, (s / PAGES_PER_2M) as int),
            pre.tables.leaf(process, 1) == leaf2,
            pre.list.nodes@[leaf2 as int].live,
            forall|i: usize| ROOT_FRAME_SLOT <= i < 2 * NODES_PER_PAGE ==> #[trigger] pre.tables.has_slot(&pre.list, process, i),
            forall|q: int| #[trigger] image_region(runs, q) ==> {
                &&& !pre.blocks.regions_2m@[q].typed
                &&& forall|j: int| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> #[trigger] pre.blocks.pages@[j].kind is Reserved
            },
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                ==> !image_region(runs, region_2m((p / PAGE_SZ) as int)),
        ensures
            ({
                let r = s / PAGES_PER_2M;
                let i = (ROOT_FRAME_SLOT + k) as usize;
                &&& cur.wf()
                &&& cur.list.seq@[0] == root
                &&& cur.tables.leaf(process, 1) == leaf2
                &&& cur.tables.has_slot(&cur.list, process, i)
                &&& !cur.list.nodes@[leaf2 + 1 + k].live
                &&& forall|j: usize| #[trigger] perms.contains_key(j) ==> perms[j].addr() == j * PAGE_SZ
                &&& cur.blocks.regions_2m@[r as int].typed ==> {
                    &&& cur.holders@.contains_key(BlockRef::Two(r))
                    &&& !cur.blocks.regions_2m@[r as int].dead
                    &&& cur.blocks.regions_2m@[r as int].refs < usize::MAX
                }
                &&& !cur.blocks.regions_2m@[r as int].typed ==> {
                    &&& forall|j: int| r * PAGES_PER_2M <= j < (r + 1) * PAGES_PER_2M ==> #[trigger] cur.blocks.pages@[j].kind is Reserved
                    &&& forall|j: usize| r * PAGES_PER_2M <= j < (r + 1) * PAGES_PER_2M ==> #[trigger] perms.contains_key(j)
                    &&& forall|p: usize| #[trigger] cur.list.pages@.dom().contains(p) && cur.blocks.tracks_addr(p)
                        ==> region_2m((p / PAGE_SZ) as int) != r
                }
            }),
    {
        reveal(image_progress);
        let r = s / PAGES_PER_2M;
        let q = r as int;
        let i = (ROOT_FRAME_SLOT + k) as usize;
        assert(block_region(bs[k]) == q);
        assert(in_regions(bs, k + 1, q));
        assert(index_entry(i) == 1);
        assert(pre.tables.has_slot(&pre.list, process, i));
        assert(cur.list.nodes@[leaf2 as int].live == pre.list.nodes@[leaf2 as int].live);
        assert(cur.tables.has_slot(&cur.list, process, i));
        assert(!cur.list.nodes@[leaf2 + 1 + k].live);
        if !in_regions(bs, k, q) {
            assert(cur.blocks.regions_2m@[q] == pre.blocks.regions_2m@[q]);
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(PAGES_PER_2M as int, q, 1);
            assert forall|j: int| r * PAGES_PER_2M <= j < (r + 1) * PAGES_PER_2M implies #[trigger] cur.blocks.pages@[j].kind is Reserved by {
                lemma_fundamental_div_mod_converse(j, PAGES_PER_2M as int, q, j - q * PAGES_PER_2M);
                assert(region_2m(j) == q);
                assert(cur.blocks.pages@[j] == pre.blocks.pages@[j]);
            }
            assert forall|j: usize| r * PAGES_PER_2M <= j < (r + 1) * PAGES_PER_2M implies #[trigger] perms.contains_key(j) by {
                assert(image_region(runs, q));
            }
        } else {
            lemma_div_is_ordered(s as int, NUM_PAGES - 1, PAGES_PER_2M as int);
            assert((NUM_PAGES - 1) / (PAGES_PER_2M as int) < NUM_2M) by (compute_only);
            assert(cur.blocks.regions_2m@[q].refs <= k);
        }
        assert forall|p: usize| #[trigger] cur.list.pages@.dom().contains(p) && cur.blocks.tracks_addr(p)
            implies region_2m((p / PAGE_SZ) as int) != r by {
            assert(pre.list.pages@.dom().contains(p));
        }
    }

    /// The frame capabilities of the runs before run r, and the first k - off of run r's, stay through
    /// boot_root_frame putting block k, the next of run r's, at slot ROOT_FRAME_SLOT + k.
    proof fn lemma_frames_kept(
        cur: Self,
        post: Self,
        root: usize,
        process: usize,
        leaf2: usize,
        runs: Seq<ImageRun>,
        r: int,
        off: int,
        k: int,
        rights: u32,
        b: (nat, nat),
    )
        requires
            0 <= r < runs.len(),
            0 <= off <= k < ROOT_FRAME_SLOTS,
            k - off < run_image_blocks(runs[r]).len(),
            run_image_blocks(runs[r])[k - off] == b,
            off == image_offset(runs, r),
            cur.list.seq@[0] == root,
            cur.tables.leaf(process, 1) == leaf2,
            leaf2 + NODES_PER_PAGE <= NODE_SPACE,
            forall|a: int, u: int| #![trigger run_image_blocks(runs[a])[u]]
                0 <= a < r && 0 <= u < run_image_blocks(runs[a]).len() ==> cur.root_frame_at(
                root,
                process,
                leaf2,
                image_offset(runs, a) + u,
                run_image_blocks(runs[a])[u],
                image_rights(runs[a]),
            ),
            forall|u: int| #![trigger run_image_blocks(runs[r])[u]] 0 <= u < k - off ==> cur.root_frame_at(
                root,
                process,
                leaf2,
                off + u,
                run_image_blocks(runs[r])[u],
                rights,
            ),
            ({
                let child = (leaf2 + 1 + k) as usize;
                let i = (ROOT_FRAME_SLOT + k) as usize;
                &&& post.wf()
                &&& post.list.seq@[0] == root
                &&& post.tables.roots == cur.tables.roots
                &&& Self::adds_cap(cur, post, child)
                &&& forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j != child
                    ==> post.list.nodes@[j].live == cur.list.nodes@[j].live
                    && post.list.nodes@[j].depth == cur.list.nodes@[j].depth
                &&& post.list.parent@ == cur.list.parent@.insert(child, root)
                &&& post.tables.has_slot(&post.list, process, i)
                &&& post.tables.node_of(process, i) == child
                &&& post.is_cap(child)
                &&& post.payload_of(child) == boot_frame_payload((b.0 * PAGE_SZ) as usize, b.1 as u8, rights)
                &&& post.list.is_child(root, child)
                &&& post.list.nodes@[child as int].depth == 1
            }),
        ensures
            forall|a: int, u: int| #![trigger run_image_blocks(runs[a])[u]]
                0 <= a < r && 0 <= u < run_image_blocks(runs[a]).len() ==> post.root_frame_at(
                root,
                process,
                leaf2,
                image_offset(runs, a) + u,
                run_image_blocks(runs[a])[u],
                image_rights(runs[a]),
            ),
            forall|u: int| #![trigger run_image_blocks(runs[r])[u]] 0 <= u < k + 1 - off ==> post.root_frame_at(
                root,
                process,
                leaf2,
                off + u,
                run_image_blocks(runs[r])[u],
                rights,
            ),
    {
        let child = (leaf2 + 1 + k) as usize;
        assert(child != leaf2);
        assert forall|a: int, u: int| #![trigger run_image_blocks(runs[a])[u]]
            0 <= a < r && 0 <= u < run_image_blocks(runs[a]).len() implies post.root_frame_at(
            root,
            process,
            leaf2,
            image_offset(runs, a) + u,
            run_image_blocks(runs[a])[u],
            image_rights(runs[a]),
        ) by {
            Self::lemma_frame_kept(
                cur,
                post,
                root,
                process,
                leaf2,
                child,
                image_offset(runs, a) + u,
                run_image_blocks(runs[a])[u],
                image_rights(runs[a]),
            );
        }
        assert forall|u: int| #![trigger run_image_blocks(runs[r])[u]] 0 <= u < k + 1 - off implies post.root_frame_at(
            root,
            process,
            leaf2,
            off + u,
            run_image_blocks(runs[r])[u],
            rights,
        ) by {
            if u < k - off {
                Self::lemma_frame_kept(cur, post, root, process, leaf2, child, off + u, run_image_blocks(runs[r])[u], rights);
            }
        }
    }

    /// The step after boot_root_memory: each run the loader mapped for dom0, which kernel/src checked
    /// at the trust boundary, decomposes into aligned blocks of at most 512 pages, and each block
    /// becomes a frame capability with its run's rights at consecutive slots of the root's second leaf
    /// from ROOT_FRAME_SLOT, below the list's synthetic root, by boot_root_frame. Every 2M region a run
    /// touches is reserved, untyped, holds no list page, and comes with its pages' permissions, so each
    /// is typed as a large frame by the first block in it. The root's reach grows by exactly the runs'
    /// physical pages, and nobody else's by anything outside them. It returns how many blocks there
    /// are, and refuses, leaving the state as it was, when they do not fit in the second leaf.
    #[verifier::spinoff_prover]
    pub fn boot_root_image(
        &mut self,
        root: usize,
        process: usize,
        leaf2: usize,
        runs: &[ImageRun],
        Tracked(perms): Tracked<Map<usize, PagePerm4k>>,
    ) -> (ret: Option<usize>)
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.leaf(process, 1) == leaf2,
            forall|i: usize| ROOT_FRAME_SLOT <= i < 2 * NODES_PER_PAGE ==> #[trigger] old(self).tables.has_slot(
                &old(self).list,
                process,
                i,
            ),
            forall|j: int| leaf2 + 1 <= j < leaf2 + NODES_PER_PAGE ==> !#[trigger] old(self).list.nodes@[j].live,
            image_runs_wf(runs@),
            forall|q: int| #[trigger] image_region(runs@, q) ==> {
                &&& !old(self).blocks.regions_2m@[q].typed
                &&& forall|j: int| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> #[trigger] old(self).blocks.pages@[j].kind is Reserved
                &&& forall|j: usize| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> #[trigger] perms.contains_key(j)
            },
            forall|j: usize| #[trigger] perms.contains_key(j) ==> perms[j].addr() == j * PAGE_SZ,
            forall|p: usize| #[trigger] old(self).list.pages@.dom().contains(p) && old(self).blocks.tracks_addr(p)
                ==> !image_region(runs@, region_2m((p / PAGE_SZ) as int)),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            ret is None ==> image_blocks(runs@).len() > ROOT_FRAME_SLOTS && *final(self) == *old(self),
            ret matches Some(count) ==> {
                let bs = image_blocks(runs@);
                let phys = image_phys(runs@);
                &&& count == bs.len()
                &&& count <= ROOT_FRAME_SLOTS
                &&& final(self).wf()
                &&& final(self).list.seq@[0] == root
                &&& final(self).tables.roots == old(self).tables.roots
                &&& final(self).tables.owner == old(self).tables.owner
                &&& forall|a: int, u: int| #![trigger run_image_blocks(runs@[a])[u]]
                    0 <= a < runs@.len() && 0 <= u < run_image_blocks(runs@[a]).len() ==> {
                    &&& bs[image_offset(runs@, a) + u] == run_image_blocks(runs@[a])[u]
                    &&& final(self).root_frame_at(
                        root,
                        process,
                        leaf2,
                        image_offset(runs@, a) + u,
                        run_image_blocks(runs@[a])[u],
                        image_rights(runs@[a]),
                    )
                }
                &&& forall|t: int| #![trigger bs[t]] 0 <= t < count ==> bs[t].1 <= IMAGE_ORDER && bs[t].0 % pow2(bs[t].1) == 0
                &&& forall|t: int, u: int, x: nat| 0 <= t < count && 0 <= u < count && t != u
                    ==> !(#[trigger] in_page_block(bs[t], x) && #[trigger] in_page_block(bs[u], x))
                &&& forall|x: nat| #[trigger] in_runs(phys, runs@.len() as int, x as int)
                    <==> exists|t: int| 0 <= t < count && #[trigger] in_page_block(bs[t], x)
                &&& forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE
                    && !(leaf2 + 1 <= j < leaf2 + 1 + count)
                    ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live
                    && final(self).list.nodes@[j].depth == old(self).list.nodes@[j].depth
                &&& forall|x: usize| #![trigger final(self).is_cap(x)] #![trigger old(self).is_cap(x)]
                    !(leaf2 + 1 <= x < leaf2 + 1 + count) ==> final(self).is_cap(x) == old(self).is_cap(x)
                &&& forall|x: usize| #![trigger old(self).is_cap(x)] #![trigger final(self).payload_of(x)]
                    !(leaf2 + 1 <= x < leaf2 + 1 + count) && old(self).is_cap(x)
                    ==> final(self).payload_of(x) == old(self).payload_of(x)
                &&& final(self).blocks.free_perms == old(self).blocks.free_perms
                &&& final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@
                &&& final(self).threads == old(self).threads
                &&& final(self).processes == old(self).processes
                &&& final(self).spaces == old(self).spaces
                &&& final(self).list.pages@.dom() == old(self).list.pages@.dom()
                &&& forall|o: usize| #[trigger] final(self).view().reach(process, o)
                    <==> (old(self).view().reach(process, o) || (o % PAGE_SZ == 0
                        && in_runs(phys, runs@.len() as int, (o / PAGE_SZ) as int)))
                &&& forall|q: usize, o: usize| #[trigger] final(self).view().reach(q, o) && !old(self).view().reach(q, o)
                    ==> o % PAGE_SZ == 0 && in_runs(phys, runs@.len() as int, (o / PAGE_SZ) as int)
                &&& final(self).table_pages == old(self).table_pages
                &&& forall|q: int| 0 <= q < NUM_2M && !image_region(runs@, q)
                    ==> #[trigger] final(self).blocks.regions_2m@[q] == old(self).blocks.regions_2m@[q]
                &&& forall|j: int| old(self).blocks.tracks(j) && !image_region(runs@, region_2m(j))
                    ==> #[trigger] final(self).blocks.pages@[j] == old(self).blocks.pages@[j]
                &&& forall|q: int| #[trigger] image_region(runs@, q) ==> {
                    &&& 0 <= q < NUM_2M
                    &&& final(self).blocks.regions_2m@[q].typed
                    &&& !final(self).blocks.regions_2m@[q].dead
                    &&& final(self).blocks.regions_2m@[q].refs <= count
                    &&& final(self).holders@.contains_key(BlockRef::Two(q as usize))
                }
                &&& forall|a: int, g: int| 0 <= a < runs@.len() && #[trigger] in_run_at(phys, a, g)
                    ==> block_ref(&final(self).blocks, g as usize) == BlockRef::Two((g / PAGES_PER_2M as int) as usize)
            },
    {
        let count = match count_frames(runs) {
            Some(count) => count,
            None => return None,
        };
        let ghost pre = *self;
        let ghost phys = image_phys(runs@);
        let ghost bs = image_blocks(runs@);
        let tracked mut perms = perms;
        proof {
            lemma_runs_blocks(phys, IMAGE_ORDER as nat);
            assert(index_entry(255usize) == 1) by (compute_only);
            assert(index_slot(255usize) == 127) by (compute_only);
            assert(pre.tables.has_slot(&pre.list, process, 255usize));
            pre.lemma_slot(process, 255usize);
            assert(pre.tables.node_of(process, 255usize) == leaf2 + 127);
            pre.lemma_slot_bound((leaf2 + 127) as usize);
            assert(pre.tables.has_slot(&pre.list, process, ROOT_FRAME_SLOT));
            assert(index_entry(ROOT_FRAME_SLOT) == 1) by (compute_only);
            assert(pre.list.nodes@[leaf2 as int].live);
            reveal(image_progress);
            assert(forall|q: int| 0 <= q < NUM_2M ==> !#[trigger] in_regions(bs, 0, q));
            assert forall|q: int, j: usize| #![trigger image_region(runs@, q), perms.contains_key(j)]
                image_region(runs@, q) && !in_regions(bs, 0, q) && q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M implies perms.contains_key(j) by {}
            assert forall|o: usize| #[trigger] pre.view().reach(process, o) <==> (pre.view().reach(process, o) || in_blocks(bs, 0, o)) by {}
            assert(image_progress(*self, pre, root, process, leaf2, runs@, bs, 0, perms));
        }
        let mut k: usize = 0;
        let mut r: usize = 0;
        while r < runs.len()
            invariant
                self.stale_epoch == pre.stale_epoch,
                self.flush_epoch == pre.flush_epoch,
                r <= runs@.len(),
                image_runs_wf(runs@),
                phys == image_phys(runs@),
                bs == image_blocks(runs@),
                bs == runs_blocks(phys, IMAGE_ORDER as nat),
                count == bs.len(),
                bs.len() <= ROOT_FRAME_SLOTS,
                leaf2 + NODES_PER_PAGE <= NODE_SPACE,
                pre.tables.leaf(process, 1) == leaf2,
                pre.list.nodes@[leaf2 as int].live,
                forall|i: usize| ROOT_FRAME_SLOT <= i < 2 * NODES_PER_PAGE ==> #[trigger] pre.tables.has_slot(&pre.list, process, i),
                forall|q: int| #[trigger] image_region(runs@, q) ==> {
                    &&& !pre.blocks.regions_2m@[q].typed
                    &&& forall|j: int| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> #[trigger] pre.blocks.pages@[j].kind is Reserved
                },
                forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                    ==> !image_region(runs@, region_2m((p / PAGE_SZ) as int)),
                k == runs_blocks(phys.take(r as int), IMAGE_ORDER as nat).len(),
                image_progress(*self, pre, root, process, leaf2, runs@, bs, k as int, perms),
                forall|a: int, u: int| #![trigger run_image_blocks(runs@[a])[u]]
                    0 <= a < r && 0 <= u < run_image_blocks(runs@[a]).len() ==> self.root_frame_at(
                    root,
                    process,
                    leaf2,
                    image_offset(runs@, a) + u,
                    run_image_blocks(runs@[a])[u],
                    image_rights(runs@[a]),
                ),
            decreases runs@.len() - r,
        {
            let start = runs[r].phys;
            let n = runs[r].pages;
            let w: u32 = if runs[r].writable { 2 } else { 0 };
            let x: u32 = if runs[r].executable { 4 } else { 0 };
            let rights = 1 + w + x;
            let ghost off = k as int;
            let ghost full = run_image_blocks(runs@[r as int]);
            proof {
                assert(phys[r as int] == (start, n));
                assert(pre.blocks.tracks_run(start as int, n as int));
                assert(n > 0);
                assert(rights == image_rights(runs@[r as int]));
                assert(rights & 128u32 == 0) by (bit_vector)
                    requires
                        rights < 8u32,
                ;
                assert(image_offset(runs@, r as int) == off);
                assert(full == run_blocks(start as nat, n as nat, IMAGE_ORDER as nat));
                lemma_runs_blocks_step(phys, r as int, IMAGE_ORDER as nat);
                lemma_runs_blocks_prefix(phys, r as int + 1, IMAGE_ORDER as nat);
                let c = runs_blocks(phys.take(r as int + 1), IMAGE_ORDER as nat);
                assert forall|u: int| 0 <= u < full.len() implies bs[k + u] == #[trigger] full[u] by {
                    assert(c[k + u] == full[u]);
                }
            }
            let mut s = start;
            let mut m = n;
            while m > 0
                invariant
                    self.stale_epoch == pre.stale_epoch,
                    self.flush_epoch == pre.flush_epoch,
                    r < runs@.len(),
                    image_runs_wf(runs@),
                    phys == image_phys(runs@),
                    bs == image_blocks(runs@),
                    bs == runs_blocks(phys, IMAGE_ORDER as nat),
                    count == bs.len(),
                    bs.len() <= ROOT_FRAME_SLOTS,
                    leaf2 + NODES_PER_PAGE <= NODE_SPACE,
                    pre.tables.leaf(process, 1) == leaf2,
                    pre.list.nodes@[leaf2 as int].live,
                    forall|i: usize| ROOT_FRAME_SLOT <= i < 2 * NODES_PER_PAGE ==> #[trigger] pre.tables.has_slot(&pre.list, process, i),
                    forall|q: int| #[trigger] image_region(runs@, q) ==> {
                        &&& !pre.blocks.regions_2m@[q].typed
                        &&& forall|j: int| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> #[trigger] pre.blocks.pages@[j].kind is Reserved
                    },
                    forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                        ==> !image_region(runs@, region_2m((p / PAGE_SZ) as int)),
                    phys[r as int] == (start, n),
                    start <= s,
                    s + m == start + n,
                    pre.blocks.tracks_run(start as int, n as int),
                    rights == image_rights(runs@[r as int]),
                    rights & CONTROL_RIGHT == 0,
                    off == image_offset(runs@, r as int),
                    full == run_image_blocks(runs@[r as int]),
                    off <= k,
                    off + full.len() == runs_blocks(phys.take(r as int + 1), IMAGE_ORDER as nat).len(),
                    runs_blocks(phys.take(r as int + 1), IMAGE_ORDER as nat).len() <= bs.len(),
                    k + run_blocks(s as nat, m as nat, IMAGE_ORDER as nat).len() == off + full.len(),
                    forall|u: int| 0 <= u < run_blocks(s as nat, m as nat, IMAGE_ORDER as nat).len()
                        ==> bs[k + u] == #[trigger] run_blocks(s as nat, m as nat, IMAGE_ORDER as nat)[u],
                    forall|u: int| 0 <= u < run_blocks(s as nat, m as nat, IMAGE_ORDER as nat).len()
                        ==> full[k - off + u] == #[trigger] run_blocks(s as nat, m as nat, IMAGE_ORDER as nat)[u],
                    image_progress(*self, pre, root, process, leaf2, runs@, bs, k as int, perms),
                    forall|a: int, u: int| #![trigger run_image_blocks(runs@[a])[u]]
                        0 <= a < r && 0 <= u < run_image_blocks(runs@[a]).len() ==> self.root_frame_at(
                        root,
                        process,
                        leaf2,
                        image_offset(runs@, a) + u,
                        run_image_blocks(runs@[a])[u],
                        image_rights(runs@[a]),
                    ),
                    forall|u: int| #![trigger full[u]] 0 <= u < k - off ==> self.root_frame_at(
                        root,
                        process,
                        leaf2,
                        off + u,
                        full[u],
                        rights,
                    ),
                decreases m,
            {
                // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
                let tracked mut steps = Steps::fresh();
                let (o, size) = first_block(s, m, IMAGE_ORDER, Tracked(&mut steps));
                let ghost cur = *self;
                let ghost rest = run_blocks(s as nat, m as nat, IMAGE_ORDER as nat);
                let ghost rest2 = run_blocks((s + size) as nat, (m - size) as nat, IMAGE_ORDER as nat);
                let ghost q = (s / PAGES_PER_2M) as int;
                proof {
                    lemma_order_below(s as nat, m as nat, IMAGE_ORDER as nat);
                    assert(rest == seq![(s as nat, o as nat)] + rest2);
                    assert(rest[0] == (s as nat, o as nat));
                    assert(bs[k as int] == rest[0]);
                    assert(full[k - off] == rest[0]);
                    assert(k < bs.len());
                    lemma_image_base(s, o);
                    assert(in_run_at(phys, r as int, s as int));
                    assert(region_2m(s as int) == q);
                    assert(image_region(runs@, q));
                    Self::lemma_image_ready(pre, cur, root, process, leaf2, runs@, bs, k as int, s, perms);
                    assert(region_keys(perms, q).subset_of(perms.dom()));
                }
                let ghost held = perms;
                let tracked region = perms.tracked_remove_keys(region_keys(held, q));
                proof {
                    assert(region == held.restrict(region_keys(held, q)));
                    assert forall|j: usize| #[trigger] region.contains_key(j) implies region[j].addr() == j * PAGE_SZ by {
                        assert(held.contains_key(j));
                    }
                    if !cur.blocks.regions_2m@[q].typed {
                        assert forall|j: usize| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M implies #[trigger] region.contains_key(j) by {
                            assert(held.contains_key(j));
                            assert(region_keys(held, q).contains(j));
                        }
                    }
                }
                self.boot_root_frame(root, process, leaf2, ROOT_FRAME_SLOT + k, s * PAGE_SZ, o, rights, Tracked(region));
                proof {
                    let post = *self;
                    assert forall|y: usize| #[trigger] block_in(bs[k as int], y) == in_block((s * PAGE_SZ) as usize, o, y) by {}
                    Self::lemma_image_step(pre, cur, post, root, process, leaf2, runs@, bs, k as int, s, o, held, perms);
                    assert(full[k - off] == (s as nat, o as nat));
                    assert(((s as nat) * PAGE_SZ) as usize == s * PAGE_SZ);
                    Self::lemma_frames_kept(cur, post, root, process, leaf2, runs@, r as int, off, k as int, rights, (s as nat, o as nat));
                    assert forall|u: int| 0 <= u < rest2.len() implies bs[k + 1 + u] == #[trigger] rest2[u] by {
                        assert(rest[u + 1] == rest2[u]);
                        assert(bs[k + (u + 1)] == rest[u + 1]);
                    }
                    assert forall|u: int| 0 <= u < rest2.len() implies full[k + 1 - off + u] == #[trigger] rest2[u] by {
                        assert(rest[u + 1] == rest2[u]);
                        assert(full[k - off + (u + 1)] == rest[u + 1]);
                    }
                }
                k = k + 1;
                s = s + size;
                m = m - size;
            }
            proof {
                assert(k - off == full.len());
                assert forall|a: int, u: int| #![trigger run_image_blocks(runs@[a])[u]]
                    0 <= a < r + 1 && 0 <= u < run_image_blocks(runs@[a]).len() implies self.root_frame_at(
                    root,
                    process,
                    leaf2,
                    image_offset(runs@, a) + u,
                    run_image_blocks(runs@[a])[u],
                    image_rights(runs@[a]),
                ) by {
                    if a == r {
                        assert(full[u] == run_image_blocks(runs@[a])[u]);
                    }
                }
            }
            r = r + 1;
        }
        proof {
            reveal(image_progress);
            let post = *self;
            let len = runs@.len() as int;
            assert(phys.take(len) =~= phys);
            assert(k == bs.len());
            let len_bs = bs.len() as int;
            assert forall|a: int, u: int| #![trigger run_image_blocks(runs@[a])[u]]
                0 <= a < runs@.len() && 0 <= u < run_image_blocks(runs@[a]).len()
                implies bs[image_offset(runs@, a) + u] == run_image_blocks(runs@[a])[u] by {
                lemma_runs_blocks_step(phys, a, IMAGE_ORDER as nat);
                lemma_runs_blocks_prefix(phys, a + 1, IMAGE_ORDER as nat);
                assert(phys[a] == (runs@[a].phys, runs@[a].pages));
                let c = runs_blocks(phys.take(a + 1), IMAGE_ORDER as nat);
                assert(c[image_offset(runs@, a) + u] == run_image_blocks(runs@[a])[u]);
            }
            assert forall|o: usize| #[trigger] in_blocks(bs, bs.len() as int, o)
                <==> (o % PAGE_SZ == 0 && in_runs(phys, len, (o / PAGE_SZ) as int)) by {
                if in_blocks(bs, bs.len() as int, o) {
                    let t = choose|t: int| 0 <= t < bs.len() && #[trigger] block_in(bs[t], o);
                    lemma_block_in(bs[t], o);
                    assert(in_page_block(bs[t], (o / PAGE_SZ) as nat));
                    assert(in_runs(phys, len, ((o / PAGE_SZ) as nat) as int));
                }
                if o % PAGE_SZ == 0 && in_runs(phys, len, (o / PAGE_SZ) as int) {
                    let y = (o / PAGE_SZ) as nat;
                    assert(in_runs(phys, len, y as int));
                    let t = choose|t: int| 0 <= t < bs.len() && #[trigger] in_page_block(bs[t], y);
                    lemma_block_in(bs[t], o);
                    assert(block_in(bs[t], o));
                    assert(in_blocks(bs, bs.len() as int, o));
                }
            }
            assert forall|o: usize| #[trigger] post.view().reach(process, o)
                <==> (pre.view().reach(process, o) || (o % PAGE_SZ == 0 && in_runs(phys, len, (o / PAGE_SZ) as int))) by {
                assert(post.view().reach(process, o) <==> (pre.view().reach(process, o) || in_blocks(bs, bs.len() as int, o)));
            }
            assert forall|q: usize, o: usize| #[trigger] post.view().reach(q, o) && !pre.view().reach(q, o)
                implies o % PAGE_SZ == 0 && in_runs(phys, len, (o / PAGE_SZ) as int) by {
                assert(in_blocks(bs, bs.len() as int, o));
            }
            // The image's regions are exactly those its blocks lie in.
            assert forall|q: int| #[trigger] in_regions(bs, len_bs, q) implies image_region(runs@, q) by {
                let t = choose|t: int| 0 <= t < len_bs && #[trigger] block_region(bs[t]) == q;
                let b = bs[t];
                lemma_pow2_pos(b.1);
                assert(in_page_block(b, b.0));
                assert(in_runs(phys, len, b.0 as int));
                let a = choose|a: int| 0 <= a < len && #[trigger] in_run_at(phys, a, b.0 as int);
                lemma_page_block_region(b, b.0);
            }
            assert forall|q: int| #[trigger] image_region(runs@, q) implies 0 <= q < NUM_2M && in_regions(bs, len_bs, q) by {
                let (a, x) = choose|a: int, x: int| 0 <= a < runs@.len() && #[trigger] in_run_at(phys, a, x) && region_2m(x) == q;
                assert(pre.blocks.tracks_run(phys[a].0 as int, phys[a].1 as int));
                let y = x as nat;
                assert(in_runs(phys, len, y as int));
                let t = choose|t: int| 0 <= t < len_bs && #[trigger] in_page_block(bs[t], y);
                lemma_page_block_region(bs[t], y);
                assert(block_region(bs[t]) == q);
            }
            assert forall|q: int| 0 <= q < NUM_2M && !image_region(runs@, q)
                implies #[trigger] post.blocks.regions_2m@[q] == pre.blocks.regions_2m@[q] by {
                assert(!in_regions(bs, len_bs, q));
            }
            assert forall|j: int| pre.blocks.tracks(j) && !image_region(runs@, region_2m(j))
                implies #[trigger] post.blocks.pages@[j] == pre.blocks.pages@[j] by {
                assert(!in_regions(bs, len_bs, region_2m(j)));
            }
            assert forall|a: int, g: int| 0 <= a < runs@.len() && #[trigger] in_run_at(phys, a, g)
                implies block_ref(&post.blocks, g as usize) == BlockRef::Two((g / PAGES_PER_2M as int) as usize) by {
                assert(pre.blocks.tracks_run(phys[a].0 as int, phys[a].1 as int));
                assert(image_region(runs@, region_2m(g)));
                assert(post.blocks.regions_2m@[region_2m(g)].typed);
            }
        }
        Some(count)
    }
}

} // verus!
