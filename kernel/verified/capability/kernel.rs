//! The capability kernel's state, which each later module extends. `wf` holds at every step boundary:
//! a long operation returns to the caller between steps, so other cores interleave only where it
//! holds. One lock covers all of this. Per-CPU state outside the lock (stacks, the GDT and TSS and the
//! switch decision) lives in kernel/src's Cpu. See design/one-lock-bounded-steps/ and
//! design/flush-without-waiting/.
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::block::*;
use crate::capability::link::*;
use crate::capability::mapping::*;
use crate::capability::list::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::Tables;
use crate::capability::zero::*;
use crate::define::*;
use crate::pptr::PointsTo;

/// One core's view under the lock.
#[derive(Clone, Copy)]
pub struct CoreState {
    /// Only this core writes it. A stop from elsewhere is a request this core acts on.
    pub current_thread: Option<usize>,
    /// The flush epoch this core has acknowledged.
    pub acked_epoch: usize,
    /// A space's id on this core is valid only at this generation. It is never zero.
    pub generation: usize,
    /// The next PCID to hand out at this generation.
    pub next_pcid: usize,
    /// The PCIDs this core may hold entries under. Only a flush empties it.
    pub pcids_used: Ghost<Set<usize>>,
}

/// The largest generation a space's word can hold above its 12 bits of PCID.
pub const ID_GENERATION_MAX: usize = 0xF_FFFF_FFFF_FFFF;

pub open spec fn id_generation(word: usize) -> usize {
    (word / 4096) as usize
}

pub open spec fn id_pcid(word: usize) -> usize {
    (word % 4096) as usize
}

/// Space s holds a valid id on core c.
pub open spec fn holds_id(cores: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, c: int, s: usize) -> bool {
    &&& lists.contains_key(s)
    &&& id_generation(lists[s].value().ids@[c]) == cores[c].generation
}

/// No word is ahead of its core's generation, so a new generation leaves no id valid. A valid id is one
/// already handed out, and no two spaces hold one. Nothing is under a PCID not yet handed out.
#[verifier::opaque]
pub open spec fn ids_wf(cores: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>) -> bool {
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> {
        &&& 1 <= (#[trigger] cores[c]).generation <= ID_GENERATION_MAX
        &&& 1 <= cores[c].next_pcid <= PCID_MAX
    }
    &&& forall|c: int, p: usize| 0 <= c < NUM_CPUS && #[trigger] cores[c].pcids_used@.contains(p) ==> p < cores[c].next_pcid
    &&& forall|c: int, s: usize| 0 <= c < NUM_CPUS && lists.contains_key(s) ==> #[trigger] id_generation(lists[s].value().ids@[c]) <= cores[c].generation
    &&& forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, lists, c, s) ==> {
        &&& 1 <= id_pcid(lists[s].value().ids@[c])
        &&& id_pcid(lists[s].value().ids@[c]) < cores[c].next_pcid
    }
    &&& forall|c: int, s: usize, r: usize| 0 <= c < NUM_CPUS && s != r && #[trigger] holds_id(cores, lists, c, s) && #[trigger] holds_id(cores, lists, c, r)
        ==> id_pcid(lists[s].value().ids@[c]) != id_pcid(lists[r].value().ids@[c])
}

/// A word holds its generation and PCID.
pub proof fn lemma_id_word(g: usize, p: usize)
    requires
        g <= ID_GENERATION_MAX,
        p < 4096,
    ensures
        g * 4096 + p <= usize::MAX,
        id_generation((g * 4096 + p) as usize) == g,
        id_pcid((g * 4096 + p) as usize) == p,
{
    assert(g * 4096 + p <= usize::MAX) by (nonlinear_arith)
        requires g <= ID_GENERATION_MAX, p < 4096;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g * 4096 + p, 4096, g as int, p as int);
}

/// The ids after space s's word on core c becomes w: its generation current, its PCID handed out and
/// held by no other space.
pub proof fn lemma_id_loaded(cores: Seq<CoreState>, pre: Map<usize, PointsTo<SpaceCores>>, post: Map<usize, PointsTo<SpaceCores>>, c: int, s: usize, w: usize)
    requires
        ids_wf(cores, pre),
        0 <= c < NUM_CPUS,
        pre.contains_key(s),
        post == pre.insert(s, post[s]),
        post[s].value().ids@ == pre[s].value().ids@.update(c, w),
        id_generation(w) == cores[c].generation,
        1 <= id_pcid(w) < cores[c].next_pcid,
        forall|r: usize| r != s && #[trigger] holds_id(cores, pre, c, r) ==> id_pcid(pre[r].value().ids@[c]) != id_pcid(w),
    ensures
        ids_wf(cores, post),
{
    reveal(ids_wf);
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && post.contains_key(r) implies #[trigger] id_generation(post[r].value().ids@[d]) <= cores[d].generation by {
        assert(pre.contains_key(r));
        if !(d == c && r == s) {
            assert(post[r].value().ids@[d] == pre[r].value().ids@[d]);
        }
    }
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(cores, post, d, r) implies {
        &&& 1 <= id_pcid(post[r].value().ids@[d])
        &&& id_pcid(post[r].value().ids@[d]) < cores[d].next_pcid
    } by {
        if !(d == c && r == s) {
            assert(post[r].value().ids@[d] == pre[r].value().ids@[d]);
            assert(holds_id(cores, pre, d, r));
        }
    }
    assert forall|d: int, r: usize, q: usize| 0 <= d < NUM_CPUS && r != q && #[trigger] holds_id(cores, post, d, r) && #[trigger] holds_id(cores, post, d, q)
        implies id_pcid(post[r].value().ids@[d]) != id_pcid(post[q].value().ids@[d]) by {
        if !(d == c && r == s) {
            assert(post[r].value().ids@[d] == pre[r].value().ids@[d]);
        }
        if !(d == c && q == s) {
            assert(post[q].value().ids@[d] == pre[q].value().ids@[d]);
        }
        if d == c && r == s {
            assert(holds_id(cores, pre, c, q));
        } else if d == c && q == s {
            assert(holds_id(cores, pre, c, r));
        } else {
            assert(holds_id(cores, pre, d, r));
            assert(holds_id(cores, pre, d, q));
        }
    }
}

/// The ids after core c's state changes with its generation kept: more PCIDs handed out leaves every id
/// valid, and any set of PCIDs handed out may be the ones used.
pub proof fn lemma_ids_core_step(pre: Seq<CoreState>, post: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, c: int)
    requires
        ids_wf(pre, lists),
        0 <= c < NUM_CPUS,
        post.len() == pre.len(),
        forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post[d] == pre[d],
        post[c].generation == pre[c].generation,
        pre[c].next_pcid <= post[c].next_pcid <= PCID_MAX,
        forall|p: usize| #[trigger] post[c].pcids_used@.contains(p) ==> p < post[c].next_pcid,
    ensures
        ids_wf(post, lists),
        forall|s: usize| #[trigger] holds_id(post, lists, c, s) == holds_id(pre, lists, c, s),
{
    reveal(ids_wf);
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS implies #[trigger] holds_id(post, lists, d, s) == holds_id(pre, lists, d, s) by {
        assert(post[d].generation == pre[d].generation);
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies {
        &&& 1 <= (#[trigger] post[d]).generation <= ID_GENERATION_MAX
        &&& 1 <= post[d].next_pcid <= PCID_MAX
    } by {
        assert(1 <= pre[d].generation <= ID_GENERATION_MAX);
        assert(1 <= pre[d].next_pcid <= PCID_MAX);
    }
    assert forall|d: int, p: usize| 0 <= d < NUM_CPUS && #[trigger] post[d].pcids_used@.contains(p) implies p < post[d].next_pcid by {
        if d != c {
            assert(pre[d].pcids_used@.contains(p));
        }
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) implies #[trigger] id_generation(lists[s].value().ids@[d]) <= post[d].generation by {
        assert(id_generation(lists[s].value().ids@[d]) <= pre[d].generation);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(post, lists, d, s) implies {
        &&& 1 <= id_pcid(lists[s].value().ids@[d])
        &&& id_pcid(lists[s].value().ids@[d]) < post[d].next_pcid
    } by {
        assert(holds_id(pre, lists, d, s));
    }
    assert forall|d: int, s: usize, r: usize| 0 <= d < NUM_CPUS && s != r && #[trigger] holds_id(post, lists, d, s) && #[trigger] holds_id(post, lists, d, r)
        implies id_pcid(lists[s].value().ids@[d]) != id_pcid(lists[r].value().ids@[d]) by {
        assert(holds_id(pre, lists, d, s));
        assert(holds_id(pre, lists, d, r));
    }
}

/// The ids after core c starts a new generation with nothing used: no space's id is valid there.
pub proof fn lemma_ids_new_generation(pre: Seq<CoreState>, post: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, c: int)
    requires
        ids_wf(pre, lists),
        0 <= c < NUM_CPUS,
        post.len() == pre.len(),
        forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post[d] == pre[d],
        post[c].generation == pre[c].generation + 1,
        post[c].generation <= ID_GENERATION_MAX,
        1 <= post[c].next_pcid <= PCID_MAX,
        post[c].pcids_used@ == Set::<usize>::empty(),
    ensures
        ids_wf(post, lists),
        forall|s: usize| !#[trigger] holds_id(post, lists, c, s),
{
    reveal(ids_wf);
    assert forall|s: usize| !#[trigger] holds_id(post, lists, c, s) by {
        if lists.contains_key(s) {
            assert(id_generation(lists[s].value().ids@[c]) <= pre[c].generation);
        }
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies {
        &&& 1 <= (#[trigger] post[d]).generation <= ID_GENERATION_MAX
        &&& 1 <= post[d].next_pcid <= PCID_MAX
    } by {
        assert(1 <= pre[d].generation <= ID_GENERATION_MAX);
        assert(1 <= pre[d].next_pcid <= PCID_MAX);
    }
    assert forall|d: int, p: usize| 0 <= d < NUM_CPUS && #[trigger] post[d].pcids_used@.contains(p) implies p < post[d].next_pcid by {
        if d != c {
            assert(pre[d].pcids_used@.contains(p));
        }
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) implies #[trigger] id_generation(lists[s].value().ids@[d]) <= post[d].generation by {
        assert(id_generation(lists[s].value().ids@[d]) <= pre[d].generation);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(post, lists, d, s) implies {
        &&& 1 <= id_pcid(lists[s].value().ids@[d])
        &&& id_pcid(lists[s].value().ids@[d]) < post[d].next_pcid
    } by {
        assert(d != c);
        assert(holds_id(pre, lists, d, s));
    }
    assert forall|d: int, s: usize, r: usize| 0 <= d < NUM_CPUS && s != r && #[trigger] holds_id(post, lists, d, s) && #[trigger] holds_id(post, lists, d, r)
        implies id_pcid(lists[s].value().ids@[d]) != id_pcid(lists[r].value().ids@[d]) by {
        assert(d != c);
        assert(holds_id(pre, lists, d, s));
        assert(holds_id(pre, lists, d, r));
    }
}

/// A new space's zero words hold no id, whatever the others hold.
pub proof fn lemma_ids_space_added(cores: Seq<CoreState>, pre: Map<usize, PointsTo<SpaceCores>>, post: Map<usize, PointsTo<SpaceCores>>, base: usize)
    requires
        ids_wf(cores, pre),
        !pre.contains_key(base),
        post == pre.insert(base, post[base]),
        forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] post[base].value().ids@[c] == 0usize,
    ensures
        ids_wf(cores, post),
{
    reveal(ids_wf);
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies s != base && holds_id(cores, pre, c, s) by {
        if s == base {
            assert(post[base].value().ids@[c] == 0usize);
            assert(cores[c].generation >= 1);
            assert(id_generation(0usize) == 0);
        } else {
            assert(post[s] == pre[s]);
        }
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && post.contains_key(s) implies #[trigger] id_generation(post[s].value().ids@[c]) <= cores[c].generation by {
        if s == base {
            assert(post[base].value().ids@[c] == 0usize);
            assert(id_generation(0usize) == 0);
            assert(cores[c].generation >= 1);
        } else {
            assert(pre.contains_key(s));
            assert(post[s] == pre[s]);
        }
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies {
        &&& 1 <= id_pcid(post[s].value().ids@[c])
        &&& id_pcid(post[s].value().ids@[c]) < cores[c].next_pcid
    } by {
        assert(holds_id(cores, pre, c, s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize, r: usize| 0 <= c < NUM_CPUS && s != r && #[trigger] holds_id(cores, post, c, s) && #[trigger] holds_id(cores, post, c, r)
        implies id_pcid(post[s].value().ids@[c]) != id_pcid(post[r].value().ids@[c]) by {
        assert(holds_id(cores, pre, c, s));
        assert(holds_id(cores, pre, c, r));
        assert(post[s] == pre[s]);
        assert(post[r] == pre[r]);
    }
}

pub proof fn lemma_ids_space_removed(cores: Seq<CoreState>, pre: Map<usize, PointsTo<SpaceCores>>, post: Map<usize, PointsTo<SpaceCores>>, base: usize)
    requires
        ids_wf(cores, pre),
        post == pre.remove(base),
    ensures
        ids_wf(cores, post),
{
    reveal(ids_wf);
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies s != base && holds_id(cores, pre, c, s) by {
        assert(post.contains_key(s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && post.contains_key(s) implies #[trigger] id_generation(post[s].value().ids@[c]) <= cores[c].generation by {
        assert(pre.contains_key(s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies {
        &&& 1 <= id_pcid(post[s].value().ids@[c])
        &&& id_pcid(post[s].value().ids@[c]) < cores[c].next_pcid
    } by {
        assert(holds_id(cores, pre, c, s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize, r: usize| 0 <= c < NUM_CPUS && s != r && #[trigger] holds_id(cores, post, c, s) && #[trigger] holds_id(cores, post, c, r)
        implies id_pcid(post[s].value().ids@[c]) != id_pcid(post[r].value().ids@[c]) by {
        assert(holds_id(cores, pre, c, s));
        assert(holds_id(cores, pre, c, r));
        assert(post[s] == pre[s]);
        assert(post[r] == pre[r]);
    }
}

/// What a flush cleared: every context on a core, or all of an IOMMU's IOTLB.
pub ghost enum FlushTarget {
    Core(int),
    Iommu(int),
}

/// What a flush of `target`, started when the epoch was `epoch`, proves. Only flush glue can make one,
/// so only it can clear a model of what the target holds. A core's glue came with the IPIs,
/// atmo-6x9.5.13; an IOMMU's comes with device capabilities, atmo-6x9.16.14.
pub tracked struct Flushed {
    pub ghost target: FlushTarget,
    pub ghost epoch: int,
}

/// Something a core may hold in its TLB or paging-structure caches: an entry of this space's tables
/// leading to this page, which is a frame's page or the base page of a table's block.
pub ghost struct TlbEntry {
    pub space: usize,
    pub page: usize,
}

/// For each IOMMU, the epoch its last finished invalidate started at, and what it may still hold that
/// its IO spaces' tables no longer say. A device keeps translating while the kernel runs, so an IOMMU
/// may refill from an entry between an invalidate and that entry's unmap.
pub struct IommuState {
    pub acked: Array<usize, NUM_IOMMUS>,
    pub tlb: Ghost<Seq<Set<TlbEntry>>>,
}

impl IommuState {
    /// No IOMMU has acknowledged anything or holds anything stale.
    pub fn zero(&mut self)
        requires
            old(self).acked.wf(),
        ensures
            final(self).acked.wf(),
            final(self).tlb@.len() == NUM_IOMMUS,
            forall|i: int| 0 <= i < NUM_IOMMUS ==> #[trigger] final(self).acked@[i] == 0,
            forall|i: int| 0 <= i < NUM_IOMMUS ==> #[trigger] final(self).tlb@[i] == Set::<TlbEntry>::empty(),
    {
        let mut i = 0;
        while i != NUM_IOMMUS
            invariant
                0 <= i <= NUM_IOMMUS,
                self.acked.wf(),
                forall|j: int| 0 <= j < i ==> #[trigger] self.acked@[j] == 0,
            decreases NUM_IOMMUS - i,
        {
            self.acked.set(i, 0);
            i = i + 1;
        }
        self.tlb = Ghost(Seq::new(NUM_IOMMUS as nat, |i: int| Set::<TlbEntry>::empty()));
    }
}

/// When each page's, 2M region's and 1G region's last unmap was, zero if it has none: unmap bumps the
/// epoch first, so a real one is never zero. A block's stale epoch is the word at its level. An unmap
/// writes all three for its page, so a free reads one word however large its block. These outlive a
/// block's typing, so retype cannot lose them.
pub struct StaleEpochs {
    pub pages: Array<usize, NUM_PAGES>,
    pub two: Array<usize, NUM_2M>,
    pub one: Array<usize, NUM_1G>,
}

impl StaleEpochs {
    pub open spec fn wf(&self) -> bool {
        &&& self.pages.wf()
        &&& self.two.wf()
        &&& self.one.wf()
    }

    /// A core at epoch `acked` has not acknowledged this page's last unmap, read at any level.
    pub open spec fn above(&self, acked: int, page: usize) -> bool {
        &&& acked < self.pages@[page as int]
        &&& acked < self.two@[(page / PAGES_PER_2M) as int]
        &&& acked < self.one@[(page / PAGES_PER_1G) as int]
    }

    /// This page's unmap happened at this epoch, read at any level.
    pub open spec fn written(&self, epoch: usize, page: usize) -> bool {
        &&& self.pages@[page as int] == epoch
        &&& self.two@[(page / PAGES_PER_2M) as int] == epoch
        &&& self.one@[(page / PAGES_PER_1G) as int] == epoch
    }

    /// The stale word of region r.
    pub open spec fn region(&self, level: Large, r: usize) -> usize {
        match level {
            Large::Two => self.two@[r as int],
            Large::One => self.one@[r as int],
        }
    }

    /// Every word zero: no unmap yet.
    pub fn zero(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
    {
        let mut i = 0;
        while i != NUM_PAGES
            invariant
                0 <= i <= NUM_PAGES,
                self.wf(),
            decreases NUM_PAGES - i,
        {
            self.pages.set(i, 0);
            i = i + 1;
        }
        let mut i = 0;
        while i != NUM_2M
            invariant
                0 <= i <= NUM_2M,
                self.wf(),
            decreases NUM_2M - i,
        {
            self.two.set(i, 0);
            i = i + 1;
        }
        let mut i = 0;
        while i != NUM_1G
            invariant
                0 <= i <= NUM_1G,
                self.wf(),
            decreases NUM_1G - i,
        {
            self.one.set(i, 0);
            i = i + 1;
        }
    }

    /// This run of pages was unmapped at this epoch. A page above an acknowledgement older than the epoch
    /// stays above it.
    pub fn record_run(&mut self, first: usize, count: usize, epoch: usize)
        requires
            old(self).wf(),
            first + count <= NUM_PAGES,
        ensures
            final(self).wf(),
            forall|g: usize| first <= g < first + count ==> #[trigger] final(self).written(epoch, g),
            forall|a: int, g: usize| a < epoch && g < NUM_PAGES && old(self).above(a, g) ==> #[trigger] final(self).above(a, g),
    {
        let mut k = 0;
        while k != count
            invariant
                self.wf(),
                0 <= k <= count,
                first + count <= NUM_PAGES,
                forall|g: usize| first <= g < first + k ==> #[trigger] self.written(epoch, g),
                forall|a: int, g: usize| a < epoch && g < NUM_PAGES && old(self).above(a, g) ==> #[trigger] self.above(a, g),
            decreases count - k,
        {
            let ghost mid = *self;
            self.record(first + k, epoch);
            proof {
                let page = (first + k) as usize;
                assert forall|g: usize| first <= g < first + k + 1 implies #[trigger] self.written(epoch, g) by {
                    if g != page {
                        assert(mid.written(epoch, g));
                    }
                }
                assert forall|a: int, g: usize| a < epoch && g < NUM_PAGES && old(self).above(a, g) implies #[trigger] self.above(a, g) by {
                    assert(mid.above(a, g));
                }
            }
            k = k + 1;
        }
    }

    /// This page's unmap happened at this epoch.
    pub fn record(&mut self, page: usize, epoch: usize)
        requires
            old(self).wf(),
            page < NUM_PAGES,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(page as int, epoch),
            final(self).two@ == old(self).two@.update((page / PAGES_PER_2M) as int, epoch),
            final(self).one@ == old(self).one@.update((page / PAGES_PER_1G) as int, epoch),
    {
        self.pages.set(page, epoch);
        self.two.set(page / PAGES_PER_2M, epoch);
        self.one.set(page / PAGES_PER_1G, epoch);
    }
}

pub struct CapKernel {
    pub list: Tree,
    pub cores: Array<CoreState, NUM_CPUS>,
    pub flush_epoch: usize,
    /// For each core, what it may still hold that its space's tables no longer say. What they do say,
    /// a core that loaded the space may hold too: see core_may_hold.
    pub tlb: Ghost<Seq<Set<TlbEntry>>>,
    pub iommus: IommuState,
    /// Frames some address space maps.
    pub mapped: Ghost<Set<usize>>,
    pub blocks: BlockTable,
    pub tables: Tables,
    pub stale_epoch: StaleEpochs,
    /// The permission of each page of a frame, by page number.
    pub frames: Tracked<Map<usize, PagePerm4k>>,
    /// The table pages' tables and spare pages.
    pub table_pages: TablePages,
    /// The spaces, each a root table named by capabilities.
    pub spaces: Spaces,
    /// What each live mapping node stands for.
    pub mappings: Ghost<IMap<usize, MappingRecord>>,
    /// The large blocks being zeroed. Each is typed with no capability yet.
    pub zeroing: Zeroing,
    /// The frame capabilities holding each block's references.
    pub holders: Ghost<IMap<BlockRef, Set<usize>>>,
}

/// Flushes every context on this core, all PCIDs and paging-structure caches: changing CR4.PGE does
/// that where a flush of the current PCID would leave entries under the others.
#[verifier(external_body)]
// external_body(glue): only the hardware can attest a flush, so only this makes the token
pub fn flush_every_context(core: usize, epoch: usize) -> (ret: Tracked<Flushed>)
    ensures
        ret@.target == FlushTarget::Core(core as int),
        ret@.epoch == epoch as int,
{
    unsafe {
        core::arch::asm!(
            "mov {cr4}, cr4",
            "xor {cr4}, {pge}",
            "mov cr4, {cr4}",
            "xor {cr4}, {pge}",
            "mov cr4, {cr4}",
            cr4 = out(reg) _,
            pge = const 1 << 7,
        );
    }
    Tracked::assume_new()
}

/// A live hidden node is node 0 of a table leaf or a table page, so unlinking it can find what to detach.
/// And a leaf in a root entry has its hidden node, so revoking the untyped it came from always reaches it.
pub open spec fn hidden_nodes_are_leaves(list: &Tree, tables: &Tables, pages: &TablePages) -> bool {
    &&& forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Hidden
        ==> tables.owner@.contains_key(n) || pages.maps@.contains_key(n)
    &&& forall|l: usize| #[trigger] tables.owner@.contains_key(l) && tables.attached(l) ==> {
        &&& l < NODE_SPACE
        &&& list.nodes@[l as int].live
        &&& list.nodes@[l as int].kind is Hidden
    }
}

/// Node i of node page k of table page t.
pub open spec fn table_node(t: usize, k: usize, i: usize) -> usize {
    (table_node_page(t, k) + i) as usize
}

/// A live node in a table page's node pages, other than its hidden node, is a mapping node, so an empty
/// entry's node is free for a map.
pub open spec fn table_nodes_are_mappings(list: &Tree, pages: &TablePages) -> bool {
    forall|t: usize, k: usize, i: usize| #![trigger table_node(t, k, i)]
        pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE && (k != 0 || i != 0)
            && list.nodes@[table_node(t, k, i) as int].live
            ==> list.nodes@[table_node(t, k, i) as int].kind is Mapping
}

/// Only a capability has children, and the list's first node is one, so a hidden node is below
/// something and has nothing below it, and a retype naming its block can unlink it.
pub open spec fn parents_are_capabilities(list: &Tree) -> bool {
    &&& list.nodes@[list.seq@[0] as int].kind is Capability
    &&& forall|x: usize| #[trigger] list.seq@.contains(x) && x != list.seq@[0]
        ==> list.nodes@[list.parent@[x] as int].kind is Capability
}

/// The parents stay capabilities while the list, the parent map and every node in a page the list
/// held are as they were: a live node is in such a page.
pub proof fn lemma_parents_same_live(pre: Tree, post: Tree)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        post.seq == pre.seq,
        post.parent == pre.parent,
        forall|i: usize| #[trigger] pre.valid(i) ==> post.nodes@[i as int] == pre.nodes@[i as int],
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    pre.lemma_link(0);
    pre.lemma_live_valid(s[0]);
    assert forall|x: usize| #[trigger] post.seq@.contains(x) && x != post.seq@[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
        pre.lemma_link(k);
        pre.lemma_parent_live(x);
        pre.lemma_live_valid(pre.parent@[x]);
    }
}

/// The parents after a child joins under a capability: the child's parent is one, and no other
/// node's kind or parent changed.
pub proof fn lemma_parents_derived(pre: Tree, post: Tree, c: usize, slot: usize)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        c < NODE_SPACE,
        pre.nodes@[c as int].live,
        pre.nodes@[c as int].kind is Capability,
        slot < NODE_SPACE,
        !pre.nodes@[slot as int].live,
        post.parent@ == pre.parent@.insert(slot, c),
        post.seq@[0] == pre.seq@[0],
        forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != slot ==> {
            &&& post.nodes@[i].live == pre.nodes@[i].live
            &&& post.nodes@[i].kind == pre.nodes@[i].kind
        },
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    pre.lemma_link(0);
    assert(s[0] != slot);
    assert forall|x: usize| #[trigger] post.seq@.contains(x) && x != post.seq@[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < post.seq@.len() && post.seq@[k] == x;
        post.lemma_link(k);
        if x != slot {
            assert(pre.nodes@[x as int].live);
            lemma_has(s, x);
            let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
            assert(j != 0);
            assert(pre.parent@.contains_key(s[j]));
            pre.lemma_parent_live(x);
            assert(pre.parent@[x] != slot);
            assert(post.parent@[x] == pre.parent@[x]);
        }
    }
}

/// The parents after a node goes: no parent changed, and a node still listed has a live parent, so
/// not the one that went.
pub proof fn lemma_parents_removed(pre: Tree, post: Tree, i: usize)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        i < NODE_SPACE,
        !post.nodes@[i as int].live,
        post.parent@ == pre.parent@,
        post.seq@[0] == pre.seq@[0],
        forall|x: int| 0 <= x < NODE_SPACE && x != i ==> #[trigger] post.nodes@[x].live == pre.nodes@[x].live,
        forall|x: int| 0 <= x < NODE_SPACE && x != i ==> #[trigger] post.nodes@[x].kind == pre.nodes@[x].kind,
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    pre.lemma_link(0);
    post.lemma_link(0);
    assert(post.seq@[0] != i);
    assert forall|x: usize| #[trigger] post.seq@.contains(x) && x != post.seq@[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < post.seq@.len() && post.seq@[k] == x;
        post.lemma_link(k);
        assert(x != i);
        assert(pre.nodes@[x as int].live);
        lemma_has(s, x);
        assert(k != 0);
        assert(post.parent@.contains_key(post.seq@[k]));
        post.lemma_parent_live(x);
        assert(post.parent@[x] != i);
        assert(pre.nodes@[pre.parent@[x] as int].kind is Capability);
    }
}

/// The parents after capability i is renamed slot: slot's parent is i's, a child of i has slot, and
/// every other parent is as it was.
pub proof fn lemma_parents_moved(pre: Tree, post: Tree, i: usize, slot: usize)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        i < NODE_SPACE,
        slot < NODE_SPACE,
        i != slot,
        pre.nodes@[i as int].live,
        pre.nodes@[i as int].kind is Capability,
        !pre.nodes@[slot as int].live,
        !post.nodes@[i as int].live,
        post.nodes@[slot as int].kind is Capability,
        exists|p: int| 0 <= p < pre.seq@.len() && #[trigger] pre.seq@[p] == i
            && post.seq@ == pre.seq@.update(p, slot),
        i != pre.seq@[0] ==> post.parent@[slot] == pre.parent@[i],
        forall|x: usize| x != i && x != slot && #[trigger] pre.parent@.contains_key(x) ==>
            post.parent@.contains_key(x) && post.parent@[x] == rename(pre.parent@[x], i, slot),
        forall|x: int| #![trigger post.nodes@[x]] 0 <= x < NODE_SPACE && x != i && x != slot ==> {
            &&& post.nodes@[x].live == pre.nodes@[x].live
            &&& post.nodes@[x].kind == pre.nodes@[x].kind
        },
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    let t = post.seq@;
    let p = choose|p: int| 0 <= p < s.len() && #[trigger] s[p] == i && t == s.update(p, slot);
    pre.lemma_link(0);
    if p == 0 {
        assert(t[0] == slot);
    } else {
        lemma_nodup(s, 0, p);
        assert(t[0] == s[0]);
        assert(s[0] != i && s[0] != slot);
    }
    assert forall|x: usize| #[trigger] t.contains(x) && x != t[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < t.len() && t[k] == x;
        post.lemma_link(k);
        assert(x != i);
        if x == slot {
            if k != p {
                pre.lemma_link(k);
                assert(t[k] == s[k]);
                assert(false);
            }
            assert(p != 0);
            lemma_nodup(s, 0, p);
            assert(i != s[0]);
            assert(pre.parent@.contains_key(s[p]));
            assert(s.contains(i));
            pre.lemma_parent_live(i);
            assert(pre.d(s[p]) == pre.d(pre.parent@[s[p]]) + 1);
            assert(pre.parent@[i] != i);
            assert(pre.parent@[i] != slot);
            assert(post.parent@[slot] == pre.parent@[i]);
        } else {
            assert(pre.nodes@[x as int].live);
            lemma_has(s, x);
            let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
            assert(j != p);
            assert(t[j] == x);
            if j == 0 {
                assert(p != 0);
                assert(t[0] == x);
                assert(false);
            }
            assert(pre.parent@.contains_key(s[j]));
            assert(post.parent@[x] == rename(pre.parent@[x], i, slot));
            if pre.parent@[x] != i {
                pre.lemma_parent_live(x);
                assert(pre.parent@[x] != slot);
            }
        }
    }
}

/// A live node in a leaf's slot is a capability, since mappings and bindings live in other pages, so
/// tearing down a leaf only ever finds capabilities in it.
pub open spec fn leaf_slots_are_capabilities(list: &Tree, tables: &Tables) -> bool {
    forall|n: usize| #[trigger] list.nodes@[n as int].live && tables.owner@.contains_key(page_of(n))
        && n % 4096 != 0 && n % 4096 < NODES_PER_PAGE ==> list.nodes@[n as int].kind is Capability
}

/// The list's first node lives outside every leaf, so whatever a leaf holds can be unlinked.
pub open spec fn first_node_outside_leaves(list: &Tree, tables: &Tables) -> bool {
    !tables.owner@.contains_key(page_of(list.seq@[0]))
}

/// Every capability node but the list's first is in a table's slot, so unlinking it can read what it
/// says.
pub open spec fn capability_nodes_are_slots(list: &Tree, tables: &Tables) -> bool {
    forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Capability
        && n != list.seq@[0] ==> tables.is_cap(list, n)
}

/// A page the list holds nodes in is not free, so a newly typed block's first page is not already one,
/// and is no block's member, so a leaf's second page is not one and its block can free whole.
pub open spec fn list_pages_used(list: &Tree, blocks: &BlockTable) -> bool {
    forall|p: usize| #[trigger] list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES ==> {
        &&& !(blocks.pages@[(p / 4096) as int].kind is Free)
        &&& blocks.pages@[(p / 4096) as int].kind is Member
            ==> blocks.pages@[blocks.pages@[(p / 4096) as int].base as int].object is TablePage
                || blocks.pages@[blocks.pages@[(p / 4096) as int].base as int].object is Space
        &&& !(blocks.pages@[(p / 4096) as int].object is Frame)
    }
}

/// The list's pages stay used while no page changes kind or object and every page keeps its block: a
/// member page is in no typed region, so its block names its base.
pub proof fn lemma_list_pages_used_same_kinds(list: &Tree, a: &BlockTable, b: &BlockTable)
    requires
        list_pages_used(list, a),
        a.wf(),
        forall|i: int| 0 <= i < NUM_PAGES ==> {
            &&& (#[trigger] b.pages@[i]).kind == a.pages@[i].kind
            &&& b.pages@[i].object == a.pages@[i].object
        },
        forall|i: usize| i < NUM_PAGES ==> #[trigger] block_ref(b, i) == block_ref(a, i),
        forall|x: int| 0 <= x < NUM_2M ==> (#[trigger] b.regions_2m@[x]).typed == a.regions_2m@[x].typed,
        forall|x: int| 0 <= x < NUM_1G ==> (#[trigger] b.regions_1g@[x]).typed == a.regions_1g@[x].typed,
    ensures
        list_pages_used(list, b),
{
    assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
        &&& !(b.pages@[(p / 4096) as int].kind is Free)
        &&& b.pages@[(p / 4096) as int].kind is Member
            ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
                || b.pages@[b.pages@[(p / 4096) as int].base as int].object is Space
        &&& !(b.pages@[(p / 4096) as int].object is Frame)
    } by {
        let x = p / 4096;
        assert(b.pages@[x as int].kind == a.pages@[x as int].kind);
        if a.pages@[x as int].kind is Member {
            a.lemma_not_free_uncovered(x as int);
            a.lemma_member(x as int);
            assert(block_ref(a, x) == BlockRef::Small(a.pages@[x as int].base));
            assert(block_ref(b, x) == BlockRef::Small(b.pages@[x as int].base));
            assert(b.pages@[x as int].base == a.pages@[x as int].base);
        }
    }
}

/// Each block being zeroed is a live typed region of the block table. It is what keeps a newly typed
/// region, whose pages were not covered, apart from every block being zeroed.
pub open spec fn zeroing_typed(z: &Zeroing, blocks: &BlockTable) -> bool {
    forall|b: usize| #[trigger] z.blocks@.contains_key(b) ==> {
        &&& z.blocks@[b] == PAGES_PER_2M ==> {
            &&& blocks.regions_2m@[(b / PAGES_PER_2M) as int].typed
            &&& !blocks.regions_2m@[(b / PAGES_PER_2M) as int].dead
        }
        &&& z.blocks@[b] == PAGES_PER_1G ==> {
            &&& blocks.regions_1g@[(b / PAGES_PER_1G) as int].typed
            &&& !blocks.regions_1g@[(b / PAGES_PER_1G) as int].dead
        }
    }
}

impl CapKernel {
    pub open spec fn acked(&self, c: int) -> int {
        self.cores@[c].acked_epoch as int
    }

    /// The epoch IOMMU i's last finished invalidate started at.
    pub open spec fn iommu_acked(&self, i: int) -> int {
        self.iommus.acked@[i] as int
    }

    /// Core c has loaded space s.
    pub open spec fn loaded(&self, c: int, s: usize) -> bool {
        &&& self.spaces.loaded@.contains_key(s)
        &&& core_listed(self.spaces.loaded@[s].value().list, c)
    }

    /// A core holds an entry of a space only if it loaded the space. A translation to an unmapped page
    /// can survive on a core only if that core has not yet acknowledged the page's unmap. The strict
    /// comparison needs unmap to bump the epoch first. The same holds of each IOMMU.
    pub open spec fn tlb_wf(&self) -> bool {
        &&& self.tlb@.len() == NUM_CPUS
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] self.acked(c) <= self.flush_epoch
        &&& forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) ==> self.loaded(c, e.space)
        &&& forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) && !self.mapped@.contains(e.page)
            ==> e.page < NUM_PAGES && self.stale_epoch.above(self.acked(c), e.page)
        &&& self.iommus_wf()
    }

    /// A translation to an unmapped page can survive in an IOMMU only if it has not yet acknowledged the
    /// page's unmap.
    pub open spec fn iommus_wf(&self) -> bool {
        &&& self.iommus.acked.wf()
        &&& self.iommus.tlb@.len() == NUM_IOMMUS
        &&& forall|i: int| 0 <= i < NUM_IOMMUS ==> #[trigger] self.iommu_acked(i) <= self.flush_epoch
        &&& forall|i: int, e: TlbEntry|
            0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) && !self.mapped@.contains(e.page)
            ==> e.page < NUM_PAGES && self.stale_epoch.above(self.iommu_acked(i), e.page)
    }

    /// The IOMMU model reads nothing but itself, the epoch and the staleness record.
    pub proof fn lemma_iommus_same(pre: Self, post: Self)
        requires
            pre.iommus_wf(),
            post.iommus == pre.iommus,
            post.flush_epoch == pre.flush_epoch,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
        ensures
            post.iommus_wf(),
    {
        assert forall|i: int| 0 <= i < NUM_IOMMUS implies #[trigger] post.iommu_acked(i) <= post.flush_epoch by {
            assert(pre.iommu_acked(i) <= pre.flush_epoch);
        }
        assert forall|i: int, e: TlbEntry|
            0 <= i < NUM_IOMMUS && #[trigger] post.iommus.tlb@[i].contains(e) && !post.mapped@.contains(e.page)
            implies e.page < NUM_PAGES && post.stale_epoch.above(post.iommu_acked(i), e.page) by {
            assert(pre.iommus.tlb@[i].contains(e));
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.list.wf()
        &&& self.cores.wf()
        &&& self.blocks.wf()
        &&& self.tables.wf(&self.list)
        &&& self.tables.caps_wf(&self.list)
        &&& self.stale_epoch.wf()
        &&& self.tlb_wf()
        &&& ids_wf(self.cores@, self.spaces.loaded@)
        &&& self.frames_wf()
        &&& self.zeroing.wf()
        &&& zeroing_typed(&self.zeroing, &self.blocks)
        &&& list_pages_used(&self.list, &self.blocks)
        &&& hidden_nodes_are_leaves(&self.list, &self.tables, &self.table_pages)
        &&& table_nodes_are_mappings(&self.list, &self.table_pages)
        &&& table_pages_wf(&self.list, &self.table_pages, &self.blocks)
        &&& spaces_wf(&self.list, &self.tables, &self.spaces, &self.blocks)
        &&& table_links_wf(tree_of(&self.table_pages, &self.spaces))
        &&& mapped_wf(self.mapped@, self.mappings@)
        &&& mappings_wf(&self.list, &self.tables, tree_of(&self.table_pages, &self.spaces), &self.blocks, self.holders@, self.mappings@)
        &&& capability_nodes_are_slots(&self.list, &self.tables)
        &&& parents_are_capabilities(&self.list)
        &&& first_node_outside_leaves(&self.list, &self.tables)
        &&& leaf_slots_are_capabilities(&self.list, &self.tables)
        &&& holders_wf(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@)
        &&& objects_wf(&self.tables, &self.blocks, self.holders@)
        &&& frames_held(self.frames@, self.holders@)
        &&& leaf_blocks_wf(&self.list, &self.tables, &self.blocks)
    }

    /// A frame's permission is for its own page.
    pub open spec fn frames_wf(&self) -> bool {
        forall|i: usize| #[trigger] self.frames@.contains_key(i) ==> self.frames@[i].addr() == i * 4096
    }

    /// No core or IOMMU can reach page f, a frame's or a table's, through something stale, under any
    /// space. What retype needs, as a fact it can check: see lemma_acknowledged_is_clean.
    pub open spec fn no_stale_translation(&self, f: usize) -> bool {
        &&& forall|c: int, s: usize| 0 <= c < NUM_CPUS ==> !#[trigger] self.tlb@[c].contains(TlbEntry { space: s, page: f })
        &&& forall|i: int, s: usize| 0 <= i < NUM_IOMMUS ==> !#[trigger] self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f })
    }

    /// Every core and every IOMMU has acknowledged this epoch. Either kind of space may have mapped a
    /// page, and the word records only when.
    pub open spec fn all_acknowledged(&self, epoch: int) -> bool {
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> epoch <= #[trigger] self.acked(c)
        &&& forall|i: int| 0 <= i < NUM_IOMMUS ==> epoch <= #[trigger] self.iommu_acked(i)
    }

    /// Every core and IOMMU has acknowledged f's last unmap.
    pub open spec fn acknowledged(&self, f: usize) -> bool {
        &&& f < NUM_PAGES
        &&& self.all_acknowledged(self.stale_epoch.pages@[f as int] as int)
    }

    /// Every core and IOMMU has acknowledged the last unmap of any page of region r.
    pub open spec fn region_acknowledged(&self, level: Large, r: usize) -> bool {
        self.all_acknowledged(self.stale_epoch.region(level, r) as int)
    }

    /// No page of region r is mapped.
    pub open spec fn region_unmapped(&self, level: Large, r: usize) -> bool {
        forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> !self.mapped@.contains(i)
    }

    /// No core or IOMMU can reach any page of region r through something stale.
    pub open spec fn region_clean(&self, level: Large, r: usize) -> bool {
        forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> self.no_stale_translation(i)
    }

    /// The rule the cross-CPU proofs rest on: a step by core c leaves every other core's current
    /// thread alone.
    pub open spec fn writes_only_own_current(pre: Self, post: Self, c: int) -> bool {
        forall|d: int| 0 <= d < NUM_CPUS && d != c
            ==> #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread
    }

    /// What every step by core c must establish.
    pub open spec fn step_ok(pre: Self, post: Self, c: int) -> bool {
        &&& post.wf()
        &&& Self::writes_only_own_current(pre, post, c)
    }

    /// No two spaces hold one id at one generation on one core.
    pub proof fn lemma_ids_unique(&self, c: int, s: usize, r: usize)
        requires
            self.wf(),
            0 <= c < NUM_CPUS,
            s != r,
            holds_id(self.cores@, self.spaces.loaded@, c, s),
            holds_id(self.cores@, self.spaces.loaded@, c, r),
        ensures
            id_pcid(self.spaces.loaded@[s].value().ids@[c]) != id_pcid(self.spaces.loaded@[r].value().ids@[c]),
    {
        reveal(ids_wf);
    }

    /// A valid id is one this core has handed out, and nothing is under a PCID it has not.
    pub proof fn lemma_id_handed_out(&self, c: int, s: usize, p: usize)
        requires
            self.wf(),
            0 <= c < NUM_CPUS,
        ensures
            holds_id(self.cores@, self.spaces.loaded@, c, s) ==> {
                &&& 1 <= id_pcid(self.spaces.loaded@[s].value().ids@[c])
                &&& id_pcid(self.spaces.loaded@[s].value().ids@[c]) < self.cores@[c].next_pcid
            },
            self.cores@[c].next_pcid <= p ==> !self.cores@[c].pcids_used@.contains(p),
            1 <= self.cores@[c].generation <= ID_GENERATION_MAX,
            1 <= self.cores@[c].next_pcid <= PCID_MAX,
    {
        reveal(ids_wf);
        assert(1 <= self.cores@[c].generation <= ID_GENERATION_MAX);
    }

    /// Only core c's state and its model of the TLB changed, and it stays on what it was running.
    pub open spec fn only_core_changed(pre: Self, post: Self, c: int) -> bool {
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.table_pages == pre.table_pages
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.spaces == pre.spaces
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.iommus == pre.iommus
        &&& post.cores@[c].current_thread == pre.cores@[c].current_thread
        &&& pre.acked(c) <= post.acked(c)
        &&& forall|e: TlbEntry| #[trigger] post.tlb@[c].contains(e) ==> pre.tlb@[c].contains(e)
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d]
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.tlb@[d] == pre.tlb@[d]
    }

    /// An unmapped page every core and IOMMU has acknowledged is free of stale translations.
    pub proof fn lemma_acknowledged_is_clean(&self, f: usize)
        requires
            self.wf(),
            !self.mapped@.contains(f),
            self.acknowledged(f),
        ensures
            self.no_stale_translation(f),
    {
        assert forall|c: int, s: usize| 0 <= c < NUM_CPUS implies !#[trigger] self.tlb@[c].contains(TlbEntry { space: s, page: f }) by {
            if self.tlb@[c].contains(TlbEntry { space: s, page: f }) {
                assert(self.stale_epoch.above(self.acked(c), f));
                assert(self.stale_epoch.pages@[f as int] <= self.acked(c));
            }
        }
        assert forall|i: int, s: usize| 0 <= i < NUM_IOMMUS implies !#[trigger] self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f }) by {
            if self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f }) {
                assert(self.stale_epoch.above(self.iommu_acked(i), f));
                assert(self.stale_epoch.pages@[f as int] <= self.iommu_acked(i));
            }
        }
    }

    /// A region with no page mapped, every core and IOMMU having acknowledged its word, is free of stale
    /// translations on every page: each page's unmap wrote that word too.
    pub proof fn lemma_region_acknowledged_is_clean(&self, level: Large, r: usize)
        requires
            self.wf(),
            self.region_unmapped(level, r),
            self.region_acknowledged(level, r),
        ensures
            self.region_clean(level, r),
    {
        assert forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) implies self.no_stale_translation(i) by {
            assert(i / level_pages(level) == r);
            assert forall|c: int, s: usize| 0 <= c < NUM_CPUS implies !#[trigger] self.tlb@[c].contains(TlbEntry { space: s, page: i }) by {
                if self.tlb@[c].contains(TlbEntry { space: s, page: i }) {
                    assert(!self.mapped@.contains(i));
                    assert(self.stale_epoch.above(self.acked(c), i));
                    assert(self.stale_epoch.region(level, r) <= self.acked(c));
                }
            }
            assert forall|j: int, s: usize| 0 <= j < NUM_IOMMUS implies !#[trigger] self.iommus.tlb@[j].contains(TlbEntry { space: s, page: i }) by {
                if self.iommus.tlb@[j].contains(TlbEntry { space: s, page: i }) {
                    assert(!self.mapped@.contains(i));
                    assert(self.stale_epoch.above(self.iommu_acked(j), i));
                    assert(self.stale_epoch.region(level, r) <= self.iommu_acked(j));
                }
            }
        }
    }

    /// Makes this a kernel with one root capability, no mappings, no core running anything and every
    /// page Reserved. In place, since the block table is too large to move by value.
    pub fn init(&mut self, root: usize, Tracked(perm): Tracked<PointsTo<NodePage>>, kernel_entries: Array<usize, KERNEL_MEM_END_L4INDEX>)
        requires
            old(self).cores.wf(),
            old(self).iommus.acked.wf(),
            old(self).stale_epoch.wf(),
            old(self).zeroing.cursor.wf(),
            old(self).zeroing.active_2m.wf(),
            old(self).zeroing.active_1g.wf(),
            old(self).blocks.pages.wf(),
            old(self).blocks.regions_2m.wf(),
            old(self).blocks.regions_1g.wf(),
            old(self).blocks.count_2m.wf(),
            old(self).blocks.count_1g.wf(),
            root % 4096 == 0,
            root + 4096 <= NODE_SPACE,
            perm.addr() == root,
            perm.is_init(),
            perm.value().nodes.wf(),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] perm.value().nodes@[k]).live,
            kernel_entries.wf(),
        ensures
            final(self).wf(),
            final(self).spaces.kernel_entries == kernel_entries,
            final(self).flush_epoch == 0,
            final(self).mapped@ == Set::<usize>::empty(),
            forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] final(self).cores@[c]).current_thread.is_None(),
    {
        self.list = Tree::new(root, Tracked(perm));
        self.tables = Tables::new();
        self.table_pages = TablePages::new();
        self.spaces = Spaces::new(kernel_entries);
        self.mappings = Ghost(IMap::empty());
        self.frames = Tracked(Map::tracked_empty());
        self.zeroing.init();
        self.holders = Ghost(IMap::empty());
        self.blocks.init();
        let mut i = 0;
        while i != NUM_CPUS
            invariant
                0 <= i <= NUM_CPUS,
                self.cores.wf(),
                self.list.wf(),
                self.tables.wf(&self.list),
                self.blocks.wf(),
                self.stale_epoch.wf(),
                self.zeroing.wf(),
                self.zeroing.blocks@ == Map::<usize, usize>::empty(),
                forall|i: int| 0 <= i < NODE_SPACE && i != root ==> !(#[trigger] self.list.nodes@[i]).live,
                self.list.nodes@[root as int].kind == NodeKind::Capability,
                forall|q: int| 0 <= q < NUM_2M ==> !(#[trigger] self.blocks.regions_2m@[q]).typed,
                forall|q: int| 0 <= q < NUM_1G ==> !(#[trigger] self.blocks.regions_1g@[q]).typed,
                forall|c: int| 0 <= c < i ==> {
                    &&& (#[trigger] self.cores@[c]).current_thread.is_None()
                    &&& self.cores@[c].acked_epoch == 0
                    &&& self.cores@[c].generation == 1
                    &&& self.cores@[c].next_pcid == 1
                    &&& self.cores@[c].pcids_used@ == Set::<usize>::empty()
                },
            decreases NUM_CPUS - i,
        {
            self.cores.set(i, CoreState { current_thread: None, acked_epoch: 0, generation: 1, next_pcid: 1, pcids_used: Ghost(Set::empty()) });
            i = i + 1;
        }
        self.stale_epoch.zero();
        self.iommus.zero();
        proof {
            assert forall|n: usize| n < NODE_SPACE && (#[trigger] self.list.nodes@[n as int]).live
                && self.list.nodes@[n as int].kind is Hidden implies self.tables.owner@.contains_key(n) by {
                assert(n == root);
            }
        }
        self.flush_epoch = 0;
        self.tlb = Ghost(Seq::new(NUM_CPUS as nat, |c: int| Set::<TlbEntry>::empty()));
        self.mapped = Ghost(Set::empty());
        proof {
            reveal(ids_wf);
        }
    }

    /// A step that does nothing keeps the invariant, the shape every later step is stated in.
    pub fn no_op(&self, c: usize)
        requires
            self.wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*self, *self, c as int),
    {
    }

    /// An entry of space s leading to this page has left its tables, so every core that loaded s may
    /// still hold it, and only a flush removes it. The page is mapped still, or its unmap is recorded and
    /// no core has acknowledged it.
    pub fn note_stale(&mut self, c: usize, s: usize, Ghost(page): Ghost<usize>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).spaces.roots@.contains_key(s),
            page < NUM_PAGES,
            old(self).mapped@.contains(page)
                || forall|d: int| 0 <= d < NUM_CPUS ==> old(self).stale_epoch.above(#[trigger] old(self).acked(d), page),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            forall|d: int| 0 <= d < NUM_CPUS ==> #[trigger] final(self).tlb@[d] == (
                if old(self).loaded(d, s) { old(self).tlb@[d].insert(TlbEntry { space: s, page }) } else { old(self).tlb@[d] }),
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).spaces.loaded == old(self).spaces.loaded,
    {
        let ghost pre = *old(self);
        let ghost e = TlbEntry { space: s, page };
        self.tlb = Ghost(Seq::new(NUM_CPUS as nat, |d: int| if pre.loaded(d, s) { pre.tlb@[d].insert(e) } else { pre.tlb@[d] }));
        proof {
            Self::lemma_iommus_same(pre, *self);
            assert(self.tlb@.len() == NUM_CPUS);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.tlb@[d] == (
                if pre.loaded(d, s) { pre.tlb@[d].insert(e) } else { pre.tlb@[d] }) by {}
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|d: int, g: TlbEntry|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(g) implies self.loaded(d, g.space) by {
                if pre.loaded(d, s) && g == e {
                    assert(pre.loaded(d, s));
                } else {
                    assert(pre.tlb@[d].contains(g));
                    assert(pre.loaded(d, g.space));
                }
            }
            assert forall|d: int, g: TlbEntry|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(g) && !self.mapped@.contains(g.page)
                implies g.page < NUM_PAGES && self.stale_epoch.above(self.acked(d), g.page) by {
                assert(pre.acked(d) == self.acked(d));
                if g == e {
                    assert(!pre.mapped@.contains(page));
                    assert(pre.stale_epoch.above(pre.acked(d), page));
                } else {
                    assert(pre.tlb@[d].contains(g));
                }
            }
        }
    }

    /// Whether every core and IOMMU has acknowledged f's last unmap, which is a bounded number of loads.
    pub fn is_acknowledged(&self, f: usize) -> (ret: bool)
        requires
            self.wf(),
            f < NUM_PAGES,
        ensures
            ret == self.acknowledged(f),
    {
        self.has_acknowledged(*self.stale_epoch.pages.get(f))
    }

    /// Whether every core and IOMMU has acknowledged the last unmap of any page of region r.
    pub fn is_region_acknowledged(&self, level: Large, r: usize) -> (ret: bool)
        requires
            self.wf(),
            r < level_regions(level),
        ensures
            ret == self.region_acknowledged(level, r),
    {
        let epoch = match level {
            Large::Two => *self.stale_epoch.two.get(r),
            Large::One => *self.stale_epoch.one.get(r),
        };
        self.has_acknowledged(epoch)
    }

    /// Whether every core and IOMMU has reached this epoch, which is a bounded number of loads.
    fn has_acknowledged(&self, epoch: usize) -> (ret: bool)
        requires
            self.wf(),
        ensures
            ret == self.all_acknowledged(epoch as int),
    {
        let mut c = 0;
        while c != NUM_CPUS
            invariant
                self.wf(),
                0 <= c <= NUM_CPUS,
                forall|d: int| 0 <= d < c ==> epoch <= #[trigger] self.acked(d),
            decreases NUM_CPUS - c,
        {
            if self.cores.get(c).acked_epoch < epoch {
                assert(self.acked(c as int) < epoch);
                return false;
            }
            c = c + 1;
        }
        let mut i = 0;
        while i != NUM_IOMMUS
            invariant
                self.wf(),
                0 <= i <= NUM_IOMMUS,
                forall|d: int| 0 <= d < NUM_CPUS ==> epoch <= #[trigger] self.acked(d),
                forall|j: int| 0 <= j < i ==> epoch <= #[trigger] self.iommu_acked(j),
            decreases NUM_IOMMUS - i,
        {
            if *self.iommus.acked.get(i) < epoch {
                assert(self.iommu_acked(i as int) < epoch);
                return false;
            }
            i = i + 1;
        }
        true
    }

    /// The TLB model reads nothing but the cores, the epoch, the staleness record and the core lists it
    /// has entries for.
    pub proof fn lemma_tlb_same(pre: Self, post: Self)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            forall|s: usize| #[trigger] pre.spaces.loaded@.contains_key(s) ==> {
                &&& post.spaces.loaded@.contains_key(s)
                &&& post.spaces.loaded@[s].value() == pre.spaces.loaded@[s].value()
            },
        ensures
            post.tlb_wf(),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.acked(c) <= post.flush_epoch by {
            assert(pre.acked(c) <= pre.flush_epoch);
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) implies post.loaded(c, e.space) by {
            assert(pre.tlb@[c].contains(e));
            assert(pre.spaces.loaded@.contains_key(e.space));
        }
        assert forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) && !post.mapped@.contains(e.page)
            implies e.page < NUM_PAGES && post.stale_epoch.above(post.acked(c), e.page) by {
            assert(pre.tlb@[c].contains(e));
            assert(pre.acked(c) == post.acked(c));
        }
        Self::lemma_iommus_same(pre, post);
    }

    /// The TLB model after a space no core loaded goes: no core held an entry of it.
    pub proof fn lemma_tlb_space_removed(pre: Self, post: Self, base: usize)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.spaces.loaded@ == pre.spaces.loaded@.remove(base),
            forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && e.space == base ==> !#[trigger] pre.tlb@[c].contains(e),
        ensures
            post.tlb_wf(),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.acked(c) <= post.flush_epoch by {
            assert(pre.acked(c) <= pre.flush_epoch);
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) implies post.loaded(c, e.space) by {
            assert(pre.tlb@[c].contains(e));
            assert(e.space != base);
            assert(pre.spaces.loaded@.contains_key(e.space));
            assert(post.spaces.loaded@[e.space] == pre.spaces.loaded@[e.space]);
        }
        assert forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) && !post.mapped@.contains(e.page)
            implies e.page < NUM_PAGES && post.stale_epoch.above(post.acked(c), e.page) by {
            assert(pre.tlb@[c].contains(e));
            assert(pre.acked(c) == post.acked(c));
        }
        Self::lemma_iommus_same(pre, post);
    }

    /// More pages being mapped keeps the TLB model: it says least about a mapped page.
    pub proof fn lemma_tlb_more_mapped(pre: Self, post: Self)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            forall|g: usize| #[trigger] pre.mapped@.contains(g) ==> post.mapped@.contains(g),
            post.stale_epoch == pre.stale_epoch,
            post.spaces.loaded == pre.spaces.loaded,
        ensures
            post.tlb_wf(),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.acked(c) <= post.flush_epoch by {
            assert(pre.acked(c) <= pre.flush_epoch);
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) implies post.loaded(c, e.space) by {
            assert(pre.tlb@[c].contains(e));
        }
        assert forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) && !post.mapped@.contains(e.page)
            implies e.page < NUM_PAGES && post.stale_epoch.above(post.acked(c), e.page) by {
            assert(pre.tlb@[c].contains(e));
            assert(!pre.mapped@.contains(e.page));
            assert(pre.acked(c) == post.acked(c));
        }
        assert forall|i: int| 0 <= i < NUM_IOMMUS implies #[trigger] post.iommu_acked(i) <= post.flush_epoch by {
            assert(pre.iommu_acked(i) <= pre.flush_epoch);
        }
        assert forall|i: int, e: TlbEntry|
            0 <= i < NUM_IOMMUS && #[trigger] post.iommus.tlb@[i].contains(e) && !post.mapped@.contains(e.page)
            implies e.page < NUM_PAGES && post.stale_epoch.above(post.iommu_acked(i), e.page) by {
            assert(pre.iommus.tlb@[i].contains(e));
            assert(!pre.mapped@.contains(e.page));
        }
    }

    /// The mappings after a step that changed only the blocks and the holders, keeping every typed
    /// block's pages in it and every holder in place, adding none.
    pub proof fn lemma_mappings_blocks_changed(pre: Self, post: Self)
        requires
            pre.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            forall|i: usize| i < NUM_PAGES && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
                && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
                ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
                ==> post.holders@.contains_key(br) && post.holders@[br].contains(n),
            forall|br: BlockRef, n: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(n)
                ==> pre.holders@.contains_key(br) && pre.holders@[br].contains(n),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
        ) by {
            pre.lemma_mapping_node(n);
        }
        Self::lemma_mappings_same_tree(pre, post);
    }

    /// Changing only the block table, the frames and the zeroing table keeps the invariant if each of
    /// them keeps its own, every typed block keeps its pages and every holder stays in place.
    pub proof fn lemma_zeroing_changed(pre: Self, post: Self)
        requires
            pre.wf(),
            post.blocks.wf(),
            post.frames_wf(),
            post.zeroing.wf(),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            frames_held(post.frames@, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            forall|i: usize| i < NUM_PAGES && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
                && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
                ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
                ==> post.holders@.contains_key(br) && post.holders@[br].contains(n),
            forall|br: BlockRef, n: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(n)
                ==> pre.holders@.contains_key(br) && pre.holders@[br].contains(n),
        ensures
            post.wf(),
    {
        Self::lemma_tlb_same(pre, post);
        Self::lemma_mappings_blocks_changed(pre, post);
    }

    /// Changing only the block table keeps the invariant.
    proof fn lemma_blocks_changed(pre: Self, post: Self)
        requires
            pre.wf(),
            post.blocks.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.frames_wf(),
            post.zeroing == pre.zeroing,
            zeroing_typed(&pre.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            frames_held(post.frames@, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            forall|i: usize| i < NUM_PAGES && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
                && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
                ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
                ==> post.holders@.contains_key(br) && post.holders@[br].contains(n),
            forall|br: BlockRef, n: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(n)
                ==> pre.holders@.contains_key(br) && pre.holders@[br].contains(n),
        ensures
            post.wf(),
    {
        Self::lemma_tlb_same(pre, post);
        Self::lemma_mappings_blocks_changed(pre, post);
    }

    /// A live node in a slot of an owned leaf is a capability.
    pub proof fn lemma_live_slot_is_cap(&self, n: usize)
        requires
            self.wf(),
            self.list.nodes@[n as int].live,
            self.tables.owner@.contains_key(page_of(n)),
            n % 4096 != 0,
            n % 4096 < NODES_PER_PAGE,
        ensures
            self.is_cap(n),
    {
    }

    /// A node in a leaf's page is not the list's first.
    pub proof fn lemma_leaf_node_not_first(&self, n: usize)
        requires
            self.wf(),
            self.tables.owner@.contains_key(page_of(n)),
        ensures
            n != self.list.seq@[0],
    {
    }

    /// A live hidden node has a parent and nothing below it.
    pub proof fn lemma_hidden_is_leaf(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Hidden,
        ensures
            n != self.list.seq@[0],
            self.list.childless(n),
    {
        if !self.list.childless(n) {
            self.list.lemma_next_is_child(n);
        }
    }

    /// A live hidden node is an owned leaf's or a table page's, which its block's object tells apart.
    /// That block holds its one reference and is no holder's key.
    pub proof fn lemma_hidden_block(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Hidden,
        ensures
            self.tables.owner@.contains_key(n) || self.table_pages.maps@.contains_key(n),
            n / 4096 < NUM_PAGES,
            self.tables.owner@.contains_key(n) == (self.blocks.pages@[(n / 4096) as int].object is TableLeaf),
            self.table_pages.maps@.contains_key(n) == (self.blocks.pages@[(n / 4096) as int].object is TablePage),
            block_typed(&self.blocks, BlockRef::Small(n / 4096)),
            block_refs(&self.blocks, BlockRef::Small(n / 4096)) == 1,
            !block_dead(&self.blocks, BlockRef::Small(n / 4096)),
            !self.holders@.contains_key(BlockRef::Small(n / 4096)),
    {
        if self.tables.owner@.contains_key(n) {
            lemma_leaf_block_unkeyed(&self.tables, &self.blocks, self.holders@, n);
        } else {
            assert(self.table_pages.maps@.contains_key(n));
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, n));
            lemma_table_page_unkeyed(&self.list, &self.table_pages, &self.tables, &self.blocks, self.holders@, n);
        }
    }

    /// A slot's node is no leaf, since a leaf is page aligned.
    pub proof fn lemma_slot_not_owned(&self, n: usize)
        requires
            self.wf(),
            n % 4096 != 0,
        ensures
            !self.tables.owner@.contains_key(n),
    {
        if self.tables.owner@.contains_key(n) {
            self.tables.lemma_leaf(&self.list, n);
        }
    }

    /// A live node that is not hidden is no leaf, since a leaf's live node is its hidden one.
    pub proof fn lemma_unhidden_not_owned(&self, n: usize)
        requires
            self.wf(),
            self.list.nodes@[n as int].live,
            !(self.list.nodes@[n as int].kind is Hidden),
        ensures
            !self.tables.owner@.contains_key(n),
    {
        if self.tables.owner@.contains_key(n) {
            assert(self.list.nodes@[n as int].kind is Hidden);
        }
    }

    /// A step that changes no node but n and m, neither a leaf, leaves every leaf's node as it was.
    pub proof fn lemma_same_leaf_nodes(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            !pre.tables.owner@.contains_key(n),
            !pre.tables.owner@.contains_key(m),
        ensures
            same_leaf_nodes(&pre.list, &post.list, &pre.tables),
            same_leaf_nodes(&pre.list, &post.list, &post.tables),
    {
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            pre.lemma_slot_bound(l);
            assert(l != n && l != m);
        }
    }

    /// A dead small block at zero references, whose teardown has finished and which no core can reach
    /// through a stale translation, returns to free with its permissions.
    pub fn free_block(&mut self, c: usize, base: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            base < NUM_PAGES,
            forall|i: usize| base <= i < base + order_pages(old(self).blocks.pages@[base as int].order)
                ==> #[trigger] old(self).no_stale_translation(i),
            old(self).blocks.pages@[base as int].kind is Base,
            old(self).blocks.pages@[base as int].dead,
            old(self).blocks.pages@[base as int].torn_down,
            old(self).blocks.pages@[base as int].refs == 0,
            forall|p: usize| #[trigger] old(self).list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
                ==> !old(self).blocks.in_block(base as int, (p / 4096) as int),
            forall|k: usize| k < order_pages(old(self).blocks.pages@[base as int].order) ==> {
                &&& perms.contains_key((base + k) as usize)
                &&& #[trigger] perms[(base + k) as usize].addr() == (base + k) * 4096
                &&& perms[(base + k) as usize].is_uninit()
            },
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
    {
        let ghost pre = *old(self);
        proof {
            // The callee's clause splits, so its conjuncts need triggers of their own.
            assert forall|k: usize| k < order_pages(pre.blocks.pages@[base as int].order) implies
                #[trigger] perms.contains_key((base + k) as usize) by {
                assert(perms[(base + k) as usize].addr() == (base + k) * 4096);
            }
            assert forall|k: usize| k < order_pages(pre.blocks.pages@[base as int].order) implies
                #[trigger] perms[(base + k) as usize].is_uninit() by {
                assert(perms[(base + k) as usize].addr() == (base + k) * 4096);
            }
        }
        self.blocks.free_block(base, Tracked(perms));
        self.holders = Ghost(pre.holders@.remove(BlockRef::Small(base)));
        proof {
            assert forall|br: BlockRef, i: usize| #[trigger] self.holders@.contains_key(br) && #[trigger] block_has_page(br, i)
                implies self.frames@.contains_key(i) by {
                assert(pre.holders@.contains_key(br));
            }
            Self::lemma_small_freed(pre, *self, base);
        }
    }

    /// The kernel after a small block frees, its holder entry going with it. What it still holds of the
    /// frames is the caller's to say, since a frame hands its pages back from there.
    pub proof fn lemma_small_freed(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            base < NUM_PAGES,
            pre.blocks.pages@[base as int].kind is Base,
            pre.blocks.pages@[base as int].refs == 0,
            post.blocks.wf(),
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(base as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
                ==> !pre.blocks.in_block(base as int, (p / 4096) as int),
            post.holders@ == pre.holders@.remove(BlockRef::Small(base)),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.zeroing == pre.zeroing,
            post.frames_wf(),
            frames_held(post.frames@, post.holders@),
        ensures
            post.wf(),
    {
        lemma_holders_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, base);
        lemma_list_pages_used_small_freed(&pre.list, &pre.blocks, &post.blocks, base);
        assert forall|t: usize, k: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
        }
        lemma_table_pages_small_freed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, base);
        assert forall|s: usize, k: usize| #[trigger] pre.spaces.roots@.contains_key(s) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
        }
        lemma_spaces_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, base);
        assert forall|x: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(x))
            implies post.blocks.pages@[x as int].object is Frame by {
            assert(x != base);
            assert(pre.holders@.contains_key(BlockRef::Small(x)));
            assert(block_typed(&pre.blocks, BlockRef::Small(x)));
            if pre.blocks.in_block(base as int, x as int) {
                pre.blocks.lemma_base(base as int);
                pre.blocks.lemma_base(x as int);
                if x != base {
                    pre.blocks.lemma_member_of(base as int, x as int);
                }
            }
            assert(post.blocks.pages@[x as int] == pre.blocks.pages@[x as int]);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& l / 4096 < NUM_PAGES
            &&& post.blocks.pages@[(l / 4096) as int].kind is Base
            &&& post.blocks.pages@[(l / 4096) as int].object is TableLeaf
            &&& post.blocks.pages@[(l / 4096) as int].order == 1
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(pre.list.pages@.dom().contains(l));
            assert(!pre.blocks.in_block(base as int, (l / 4096) as int));
            assert(post.blocks.pages@[(l / 4096) as int] == pre.blocks.pages@[(l / 4096) as int]);
        }
        assert forall|x: usize| x < NUM_PAGES && #[trigger] leaf_block(&post.blocks, x)
            implies post.tables.owner@.contains_key((x * 4096) as usize) by {
            assert(!pre.blocks.in_block(base as int, x as int));
            assert(post.blocks.pages@[x as int] == pre.blocks.pages@[x as int]);
            assert(leaf_block(&pre.blocks, x));
        }
        lemma_leaf_blocks_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, pre.holders@, base);
        assert forall|i: usize| i < NUM_PAGES && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
            && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
            implies #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i) by {
            assert(block_ref(&pre.blocks, i) != BlockRef::Small(base));
            lemma_block_ref_small_freed(&pre.blocks, &post.blocks, base, i);
        }
        assert forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
            implies post.holders@.contains_key(br) && post.holders@[br].contains(n) by {
            if br == BlockRef::Small(base) {
                assert(pre.holders@[br].len() == 0);
                pre.holders@[br].lemma_len0_is_empty();
            }
        }
        Self::lemma_blocks_changed(pre, post);
    }

    /// As free_block, for a 2M block.
    pub fn free_2m(&mut self, c: usize, r: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            r < NUM_2M,
            old(self).region_unmapped(Large::Two, r),
            old(self).region_clean(Large::Two, r),
            old(self).blocks.regions_2m@[r as int].typed,
            old(self).blocks.regions_2m@[r as int].dead,
            old(self).blocks.regions_2m@[r as int].torn_down,
            old(self).blocks.regions_2m@[r as int].refs == 0,
            forall|i: usize| BlockTable::large_pages(Large::Two, r as int).contains(i) ==> #[trigger] holds(perms, i),
            perms.dom() == BlockTable::large_pages(Large::Two, r as int),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
    {
        let ghost pre = *old(self);
        self.blocks.free_2m(r, Tracked(perms));
        self.holders = Ghost(pre.holders@.remove(BlockRef::Two(r)));
        proof {
            Self::lemma_large_freed(pre, *self, Large::Two, r);
        }
    }

    /// As free_block, for a 1G block.
    pub fn free_1g(&mut self, c: usize, r: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            r < NUM_1G,
            old(self).region_unmapped(Large::One, r),
            old(self).region_clean(Large::One, r),
            old(self).blocks.regions_1g@[r as int].typed,
            old(self).blocks.regions_1g@[r as int].dead,
            old(self).blocks.regions_1g@[r as int].torn_down,
            old(self).blocks.regions_1g@[r as int].refs == 0,
            forall|i: usize| BlockTable::large_pages(Large::One, r as int).contains(i) ==> #[trigger] holds(perms, i),
            perms.dom() == BlockTable::large_pages(Large::One, r as int),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
    {
        let ghost pre = *old(self);
        self.blocks.free_1g(r, Tracked(perms));
        self.holders = Ghost(pre.holders@.remove(BlockRef::One(r)));
        proof {
            Self::lemma_large_freed(pre, *self, Large::One, r);
        }
    }

    /// The kernel after a dead large block frees, its holder entry going with it. A block being zeroed is
    /// not dead, so it is not this one.
    pub proof fn lemma_large_freed(pre: Self, post: Self, level: Large, r: usize)
        requires
            pre.wf(),
            r < level_regions(level),
            post.blocks.wf(),
            post.blocks.pages@ == pre.blocks.pages@,
            match level {
                Large::Two => {
                    &&& pre.blocks.regions_2m@[r as int].typed
                    &&& pre.blocks.regions_2m@[r as int].dead
                    &&& pre.blocks.regions_2m@[r as int].refs == 0
                    &&& !post.blocks.regions_2m@[r as int].typed
                    &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@.update(r as int, post.blocks.regions_2m@[r as int])
                    &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@
                },
                Large::One => {
                    &&& pre.blocks.regions_1g@[r as int].typed
                    &&& pre.blocks.regions_1g@[r as int].dead
                    &&& pre.blocks.regions_1g@[r as int].refs == 0
                    &&& !post.blocks.regions_1g@[r as int].typed
                    &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@.update(r as int, post.blocks.regions_1g@[r as int])
                    &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@
                },
            },
            post.holders@ == pre.holders@.remove(level_ref(level, r)),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.zeroing == pre.zeroing,
            post.frames_wf(),
            frames_held(post.frames@, post.holders@),
        ensures
            post.wf(),
    {
        match level {
            Large::Two => lemma_holders_2m_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, r),
            Large::One => lemma_holders_1g_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, r),
        }
        assert forall|b: usize| #[trigger] pre.zeroing.blocks@.contains_key(b) implies {
            &&& pre.zeroing.blocks@[b] == PAGES_PER_2M ==> {
                &&& post.blocks.regions_2m@[(b / PAGES_PER_2M) as int].typed
                &&& !post.blocks.regions_2m@[(b / PAGES_PER_2M) as int].dead
            }
            &&& pre.zeroing.blocks@[b] == PAGES_PER_1G ==> {
                &&& post.blocks.regions_1g@[(b / PAGES_PER_1G) as int].typed
                &&& !post.blocks.regions_1g@[(b / PAGES_PER_1G) as int].dead
            }
        } by {
            assert(pre.zeroing.block_level(b));
            if pre.zeroing.blocks@[b] == PAGES_PER_2M && level is Two {
                assert((b / PAGES_PER_2M) as int != r as int);
            }
            if pre.zeroing.blocks@[b] == PAGES_PER_1G && level is One {
                assert((b / PAGES_PER_1G) as int != r as int);
            }
        }
        lemma_leaf_blocks_same_pages(&pre.list, &pre.tables, &pre.blocks, &post.blocks);
        lemma_leaf_blocks_owned_same_types(&pre.tables, &pre.blocks, &post.blocks);
        lemma_table_pages_same_pages(&pre.list, &pre.table_pages, &pre.blocks, &post.blocks);
        lemma_spaces_same_pages(&pre.list, &pre.tables, &pre.spaces, &pre.blocks, &post.blocks);
        let br = level_ref(level, r);
        assert forall|i: usize| i < NUM_PAGES && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
            && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
            implies #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i) by {
            assert(block_ref(&pre.blocks, i) != br);
            match level {
                Large::Two => lemma_block_ref_2m_freed(&pre.blocks, &post.blocks, r, i),
                Large::One => lemma_block_ref_1g_freed(&pre.blocks, &post.blocks, r, i),
            }
        }
        assert forall|k: BlockRef, n: usize| pre.holders@.contains_key(k) && #[trigger] pre.holders@[k].contains(n)
            implies post.holders@.contains_key(k) && post.holders@[k].contains(n) by {
            if k == br {
                assert(pre.holders@[k].len() == 0);
                pre.holders@[k].lemma_len0_is_empty();
            }
        }
        Self::lemma_blocks_changed(pre, post);
    }

    /// IOMMU i acknowledges an invalidate of all it holds, which started at this epoch. A device kept
    /// translating since, so i may hold what was unmapped after that epoch, and only what was unmapped
    /// by then leaves its model.
    pub fn acknowledge_iommu(&mut self, i: usize, epoch: usize, Tracked(flushed): Tracked<Flushed>)
        requires
            old(self).wf(),
            i < NUM_IOMMUS,
            flushed.target == FlushTarget::Iommu(i as int),
            flushed.epoch == epoch,
            old(self).iommu_acked(i as int) <= epoch <= old(self).flush_epoch,
        ensures
            final(self).wf(),
            final(self).iommu_acked(i as int) == epoch,
            old(self).iommu_acked(i as int) <= final(self).iommu_acked(i as int),
            forall|j: int| 0 <= j < NUM_IOMMUS && j != i ==> #[trigger] final(self).iommu_acked(j) == old(self).iommu_acked(j),
            final(self).iommus.tlb@[i as int] == old(self).iommus.tlb@[i as int].filter(|e: TlbEntry| old(self).stale_epoch.above(epoch as int, e.page)),
            forall|j: int| 0 <= j < NUM_IOMMUS && j != i ==> #[trigger] final(self).iommus.tlb@[j] == old(self).iommus.tlb@[j],
            final(self).tlb == old(self).tlb,
            final(self).cores == old(self).cores,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
    {
        let ghost pre = *old(self);
        self.iommus.acked.set(i, epoch);
        self.iommus.tlb = Ghost(pre.iommus.tlb@.update(i as int, pre.iommus.tlb@[i as int].filter(|e: TlbEntry| pre.stale_epoch.above(epoch as int, e.page))));
        proof {
            broadcast use vstd::set::lemma_set_filter;
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] self.acked(c) <= self.flush_epoch by {
                assert(pre.acked(c) <= pre.flush_epoch);
            }
            assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) implies self.loaded(c, e.space) by {
                assert(pre.tlb@[c].contains(e));
            }
            assert forall|c: int, e: TlbEntry|
                0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) && !self.mapped@.contains(e.page)
                implies e.page < NUM_PAGES && self.stale_epoch.above(self.acked(c), e.page) by {
                assert(pre.tlb@[c].contains(e));
                assert(pre.acked(c) == self.acked(c));
            }
            assert forall|j: int| 0 <= j < NUM_IOMMUS implies #[trigger] self.iommu_acked(j) <= self.flush_epoch by {
                if j != i as int {
                    assert(pre.iommu_acked(j) <= pre.flush_epoch);
                }
            }
            assert forall|j: int, e: TlbEntry|
                0 <= j < NUM_IOMMUS && #[trigger] self.iommus.tlb@[j].contains(e) && !self.mapped@.contains(e.page)
                implies e.page < NUM_PAGES && self.stale_epoch.above(self.iommu_acked(j), e.page) by {
                if j != i as int {
                    assert(pre.iommus.tlb@[j].contains(e));
                    assert(pre.iommu_acked(j) == self.iommu_acked(j));
                } else {
                    assert(pre.iommus.tlb@[j].contains(e));
                }
            }
        }
    }

    /// Core c acknowledges a flush of every context it did. Between that flush and this call c runs
    /// no user code, since IF stays clear in the kernel, so its TLB model is empty.
    pub fn acknowledge(&mut self, c: usize, epoch: usize, Tracked(flushed): Tracked<Flushed>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            flushed.target == FlushTarget::Core(c as int),
            flushed.epoch == epoch,
            old(self).acked(c as int) <= epoch <= old(self).flush_epoch,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).acked(c as int) == epoch,
            final(self).tlb@[c as int] == Set::<TlbEntry>::empty(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).tlb@[d] == old(self).tlb@[d],
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            Self::only_core_changed(*old(self), *final(self), c as int),
            final(self).cores@[c as int].generation == old(self).cores@[c as int].generation,
            final(self).cores@[c as int].next_pcid == old(self).cores@[c as int].next_pcid,
            final(self).cores@[c as int].pcids_used@ == Set::<usize>::empty(),
    {
        let ghost pre = *old(self);
        let state = *self.cores.get(c);
        self.cores.set(c, CoreState {
            current_thread: state.current_thread,
            acked_epoch: epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            pcids_used: Ghost(Set::empty()),
        });
        self.tlb = Ghost(self.tlb@.update(c as int, Set::empty()));
        proof {
            Self::lemma_iommus_same(pre, *self);
            reveal(ids_wf);
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies #[trigger] self.cores@[d] == pre.cores@[d] by {}
            lemma_ids_core_step(pre.cores@, self.cores@, self.spaces.loaded@, c as int);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                if d != c as int {
                    assert(self.cores@[d] == pre.cores@[d]);
                    assert(pre.acked(d) <= pre.flush_epoch);
                }
            }
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies
                #[trigger] self.cores@[d].current_thread == pre.cores@[d].current_thread by {
                assert(self.cores@[d] == pre.cores@[d]);
            }
            assert forall|d: int, f: TlbEntry|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(f) && !self.mapped@.contains(f.page)
                implies f.page < NUM_PAGES && self.stale_epoch.above(self.acked(d), f.page) by {
                if d == c as int {
                    assert(self.tlb@[d] == Set::<TlbEntry>::empty());
                    assert(!self.tlb@[d].contains(f));
                }
                assert(d != c as int);
                assert(self.cores@[d] == pre.cores@[d]);
                assert(self.tlb@[d] == pre.tlb@[d]);
                assert(pre.acked(d) == self.acked(d));
                assert(pre.tlb@[d].contains(f));
            }
        }
    }
}

} // verus!
