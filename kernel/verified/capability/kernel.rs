//! The capability kernel's state, which each later module extends. `wf` holds at every step boundary:
//! a long operation returns to the caller between steps, so other cores interleave only where it
//! holds. One lock covers all of this. Per-CPU state outside the lock (stacks, the GDT and TSS and the
//! switch decision) lives in kernel/src's Cpu. See the design on atmo-6x9.6.7, sections 7, 9 and 10.
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::block::*;
use crate::capability::list::*;
use crate::capability::refs::*;
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
}

/// What a flush of every context on `core`, started when the epoch was `epoch`, proves. Only flush
/// glue can make one, so only it can clear the TLB model. That glue comes with the IPIs,
/// atmo-6x9.5.13.
pub tracked struct Flushed {
    pub ghost core: int,
    pub ghost epoch: int,
}

pub struct CapKernel {
    pub list: Tree,
    pub cores: Array<CoreState, NUM_CPUS>,
    pub flush_epoch: usize,
    /// For each core, the frames it may still hold a translation to, cached or in use.
    pub tlb: Ghost<Seq<Set<usize>>>,
    /// Frames some address space maps.
    pub mapped: Ghost<Set<usize>>,
    pub blocks: BlockTable,
    pub tables: Tables,
    /// The epoch of the last unmap of the frame whose block is based at this page. Zero if it has
    /// none: unmap bumps the epoch first, so a real one is never zero. A frame is its base page's
    /// number. This outlives the block's typing, so retype cannot lose it.
    pub stale_epoch: Array<usize, NUM_PAGES>,
    /// The permission of each page of a frame, by page number.
    pub frames: Tracked<Map<usize, PagePerm4k>>,
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
        ret@.core == core as int,
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

/// A live hidden node is node 0 of a table leaf, the only block with one so far, so unlinking it can
/// find what to detach. And a leaf in a root entry has its hidden node, so revoking the untyped it came
/// from always reaches it.
pub open spec fn hidden_nodes_are_leaves(list: &Tree, tables: &Tables) -> bool {
    &&& forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Hidden
        ==> tables.owner@.contains_key(n)
    &&& forall|l: usize| #[trigger] tables.owner@.contains_key(l) && tables.attached(l) ==> {
        &&& l < NODE_SPACE
        &&& list.nodes@[l as int].live
        &&& list.nodes@[l as int].kind is Hidden
    }
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
        &&& !(blocks.pages@[(p / 4096) as int].kind is Member)
        &&& !(blocks.pages@[(p / 4096) as int].object is Frame)
    }
}

/// The list's pages stay used while no page changes kind.
pub proof fn lemma_list_pages_used_same_kinds(list: &Tree, a: &BlockTable, b: &BlockTable)
    requires
        list_pages_used(list, a),
        forall|i: int| 0 <= i < NUM_PAGES ==> {
            &&& (#[trigger] b.pages@[i]).kind == a.pages@[i].kind
            &&& b.pages@[i].object == a.pages@[i].object
        },
    ensures
        list_pages_used(list, b),
{
    assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
        &&& !(b.pages@[(p / 4096) as int].kind is Free)
        &&& !(b.pages@[(p / 4096) as int].kind is Member)
        &&& !(b.pages@[(p / 4096) as int].object is Frame)
    } by {
        assert(b.pages@[(p / 4096) as int].kind == a.pages@[(p / 4096) as int].kind);
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

    /// A translation to an unmapped frame can survive on a core only if that core has not yet
    /// acknowledged the frame's unmap. The strict comparison needs unmap to bump the epoch first.
    pub open spec fn tlb_wf(&self) -> bool {
        &&& self.tlb@.len() == NUM_CPUS
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] self.acked(c) <= self.flush_epoch
        &&& forall|c: int, f: usize|
            0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(f) && !self.mapped@.contains(f)
            ==> f < NUM_PAGES && self.acked(c) < self.stale_epoch@[f as int]
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.list.wf()
        &&& self.cores.wf()
        &&& self.blocks.wf()
        &&& self.tables.wf(&self.list)
        &&& self.tables.caps_wf(&self.list)
        &&& self.stale_epoch.wf()
        &&& self.tlb_wf()
        &&& self.frames_wf()
        &&& self.zeroing.wf()
        &&& zeroing_typed(&self.zeroing, &self.blocks)
        &&& list_pages_used(&self.list, &self.blocks)
        &&& hidden_nodes_are_leaves(&self.list, &self.tables)
        &&& capability_nodes_are_slots(&self.list, &self.tables)
        &&& parents_are_capabilities(&self.list)
        &&& first_node_outside_leaves(&self.list, &self.tables)
        &&& holders_wf(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@)
        &&& objects_wf(&self.tables, &self.blocks, self.holders@)
        &&& frames_held(self.frames@, self.holders@)
        &&& leaf_blocks_wf(&self.list, &self.tables, &self.blocks)
    }

    /// A frame's permission is for its own page.
    pub open spec fn frames_wf(&self) -> bool {
        forall|i: usize| #[trigger] self.frames@.contains_key(i) ==> self.frames@[i].addr() == i * 4096
    }

    /// No core can reach f through a stale translation. What retype needs, as a fact it can check:
    /// see lemma_acknowledged_is_clean.
    pub open spec fn no_stale_translation(&self, f: usize) -> bool {
        forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] self.tlb@[c].contains(f)
    }

    /// Every core has acknowledged f's last unmap.
    pub open spec fn acknowledged(&self, f: usize) -> bool {
        &&& f < NUM_PAGES
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> self.stale_epoch@[f as int] <= #[trigger] self.acked(c)
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

    /// An unmapped frame every core has acknowledged is free of stale translations.
    pub proof fn lemma_acknowledged_is_clean(&self, f: usize)
        requires
            self.wf(),
            !self.mapped@.contains(f),
            self.acknowledged(f),
        ensures
            self.no_stale_translation(f),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies !#[trigger] self.tlb@[c].contains(f) by {
            if self.tlb@[c].contains(f) {
                assert(self.acked(c) < self.stale_epoch@[f as int]);
                assert(self.stale_epoch@[f as int] <= self.acked(c));
            }
        }
    }

    /// Makes this a kernel with one root capability, no mappings, no core running anything and every
    /// page Reserved. In place, since the block table is too large to move by value.
    pub fn init(&mut self, root: usize, Tracked(perm): Tracked<PointsTo<NodePage>>)
        requires
            old(self).cores.wf(),
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
        ensures
            final(self).wf(),
            final(self).flush_epoch == 0,
            final(self).mapped@ == Set::<usize>::empty(),
            forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] final(self).cores@[c]).current_thread.is_None(),
    {
        self.list = Tree::new(root, Tracked(perm));
        self.tables = Tables::new();
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
                },
            decreases NUM_CPUS - i,
        {
            self.cores.set(i, CoreState { current_thread: None, acked_epoch: 0 });
            i = i + 1;
        }
        let mut i = 0;
        while i != NUM_PAGES
            invariant
                0 <= i <= NUM_PAGES,
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
                forall|c: int| 0 <= c < NUM_CPUS ==> {
                    &&& (#[trigger] self.cores@[c]).current_thread.is_None()
                    &&& self.cores@[c].acked_epoch == 0
                },
            decreases NUM_PAGES - i,
        {
            self.stale_epoch.set(i, 0);
            i = i + 1;
        }
        proof {
            assert forall|n: usize| n < NODE_SPACE && (#[trigger] self.list.nodes@[n as int]).live
                && self.list.nodes@[n as int].kind is Hidden implies self.tables.owner@.contains_key(n) by {
                assert(n == root);
            }
        }
        self.flush_epoch = 0;
        self.tlb = Ghost(Seq::new(NUM_CPUS as nat, |c: int| Set::<usize>::empty()));
        self.mapped = Ghost(Set::empty());
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

    /// Core c loaded a space that maps f, so it may now hold a translation to it.
    pub fn note_loaded(&mut self, c: usize, f: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).mapped@.contains(f),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).tlb@[c as int].contains(f),
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch@ == old(self).stale_epoch@,
            final(self).flush_epoch == old(self).flush_epoch,
    {
        let ghost pre = *old(self);
        self.tlb = Ghost(self.tlb@.update(c as int, self.tlb@[c as int].insert(f)));
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|d: int, g: usize|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(g) && !self.mapped@.contains(g)
                implies g < NUM_PAGES && self.acked(d) < self.stale_epoch@[g as int] by {
                if d == c as int {
                    assert(g != f);
                    assert(pre.tlb@[d].contains(g));
                } else {
                    assert(self.tlb@[d] == pre.tlb@[d]);
                }
                assert(pre.acked(d) == self.acked(d));
            }
        }
    }

    /// A new mapping of f exists.
    pub fn note_mapped(&mut self, c: usize, f: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).mapped@ == old(self).mapped@.insert(f),
            final(self).tlb == old(self).tlb,
            final(self).stale_epoch@ == old(self).stale_epoch@,
            final(self).flush_epoch == old(self).flush_epoch,
    {
        let ghost pre = *old(self);
        self.mapped = Ghost(self.mapped@.insert(f));
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|d: int, g: usize|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(g) && !self.mapped@.contains(g)
                implies g < NUM_PAGES && self.acked(d) < self.stale_epoch@[g as int] by {
                assert(g != f);
                assert(!pre.mapped@.contains(g));
                assert(pre.tlb@[d].contains(g));
            }
        }
    }

    /// f's last mapping went. The epoch is bumped first, so no core has acknowledged this unmap yet,
    /// however recently it last flushed.
    pub fn note_unmapped(&mut self, c: usize, f: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            f < NUM_PAGES,
            old(self).flush_epoch < usize::MAX,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).flush_epoch == old(self).flush_epoch + 1,
            final(self).mapped@ == old(self).mapped@.remove(f),
            final(self).stale_epoch@[f as int] == final(self).flush_epoch,
            final(self).tlb == old(self).tlb,
    {
        let ghost pre = *old(self);
        self.flush_epoch = self.flush_epoch + 1;
        let e = self.flush_epoch;
        self.mapped = Ghost(self.mapped@.remove(f));
        self.stale_epoch.set(f, e);
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|c2: int, g: usize|
                0 <= c2 < NUM_CPUS && #[trigger] self.tlb@[c2].contains(g) && !self.mapped@.contains(g)
                implies g < NUM_PAGES && self.acked(c2) < self.stale_epoch@[g as int] by {
                assert(pre.acked(c2) <= pre.flush_epoch);
                assert(self.acked(c2) == pre.acked(c2));
                assert(pre.tlb@[c2].contains(g));
                if g != f {
                    assert(!pre.mapped@.contains(g));
                    assert(pre.tlb@[c2].contains(g) && !pre.mapped@.contains(g));
                    assert(self.stale_epoch@[g as int] == pre.stale_epoch@[g as int]);
                } else {
                    assert(self.stale_epoch@[g as int] == e);
                }
            }
        }
    }

    /// Whether every core has acknowledged f's last unmap, which is a bounded number of loads.
    pub fn is_acknowledged(&self, f: usize) -> (ret: bool)
        requires
            self.wf(),
            f < NUM_PAGES,
        ensures
            ret == self.acknowledged(f),
    {
        let epoch = *self.stale_epoch.get(f);
        let mut c = 0;
        while c != NUM_CPUS
            invariant
                self.wf(),
                f < NUM_PAGES,
                epoch == self.stale_epoch@[f as int],
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
        true
    }

    /// The TLB model reads nothing but the cores, the epoch and the staleness record.
    pub proof fn lemma_tlb_same(pre: Self, post: Self)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
        ensures
            post.tlb_wf(),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.acked(c) <= post.flush_epoch by {
            assert(pre.acked(c) <= pre.flush_epoch);
        }
        assert forall|c: int, f: usize|
            0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(f) && !post.mapped@.contains(f)
            implies f < NUM_PAGES && post.acked(c) < post.stale_epoch@[f as int] by {
            assert(pre.tlb@[c].contains(f));
            assert(pre.acked(c) == post.acked(c));
        }
    }

    /// Changing only the block table, the frames and the zeroing table keeps the invariant if each of
    /// them keeps its own.
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
            post.list == pre.list,
            post.tables == pre.tables,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
        ensures
            post.wf(),
    {
        Self::lemma_tlb_same(pre, post);
    }

    /// Changing only the block table keeps the invariant.
    proof fn lemma_blocks_changed(pre: Self, post: Self)
        requires
            pre.wf(),
            post.blocks.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
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
        ensures
            post.wf(),
    {
        Self::lemma_tlb_same(pre, post);
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

    /// A live hidden node is an owned leaf's, whose block holds its one reference and is no holder's key.
    pub proof fn lemma_hidden_block(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Hidden,
        ensures
            self.tables.owner@.contains_key(n),
            n / 4096 < NUM_PAGES,
            block_typed(&self.blocks, BlockRef::Small(n / 4096)),
            block_refs(&self.blocks, BlockRef::Small(n / 4096)) == 1,
            !block_dead(&self.blocks, BlockRef::Small(n / 4096)),
            !self.holders@.contains_key(BlockRef::Small(n / 4096)),
    {
        assert(self.tables.owner@.contains_key(n));
        lemma_leaf_block_unkeyed(&self.tables, &self.blocks, self.holders@, n);
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
            !old(self).mapped@.contains(base),
            old(self).no_stale_translation(base),
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
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.zeroing == pre.zeroing,
            post.frames_wf(),
            frames_held(post.frames@, post.holders@),
        ensures
            post.wf(),
    {
        lemma_holders_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, base);
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
            implies !(post.blocks.pages@[(p / 4096) as int].kind is Free)
                && !(post.blocks.pages@[(p / 4096) as int].kind is Member) by {
            assert(!pre.blocks.in_block(base as int, (p / 4096) as int));
            assert(!(pre.blocks.pages@[(p / 4096) as int].kind is Free));
            assert(post.blocks.pages@[(p / 4096) as int] == pre.blocks.pages@[(p / 4096) as int]);
        }
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
        Self::lemma_blocks_changed(pre, post);
    }

    /// As free_block, for a 2M block.
    pub fn free_2m(&mut self, c: usize, r: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            r < NUM_2M,
            !old(self).mapped@.contains((r * PAGES_PER_2M) as usize),
            old(self).no_stale_translation((r * PAGES_PER_2M) as usize),
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
            !old(self).mapped@.contains((r * PAGES_PER_1G) as usize),
            old(self).no_stale_translation((r * PAGES_PER_1G) as usize),
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
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
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
        Self::lemma_blocks_changed(pre, post);
    }

    /// Core c acknowledges a flush of every context it did. Between that flush and this call c runs
    /// no user code, since IF stays clear in the kernel, so its TLB model is empty.
    pub fn acknowledge(&mut self, c: usize, epoch: usize, Tracked(flushed): Tracked<Flushed>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            flushed.core == c,
            flushed.epoch == epoch,
            old(self).acked(c as int) <= epoch <= old(self).flush_epoch,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).acked(c as int) == epoch,
            final(self).tlb@[c as int] == Set::<usize>::empty(),
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch@ == old(self).stale_epoch@,
    {
        let ghost pre = *old(self);
        let current_thread = self.cores.get(c).current_thread;
        self.cores.set(c, CoreState { current_thread, acked_epoch: epoch });
        self.tlb = Ghost(self.tlb@.update(c as int, Set::empty()));
        proof {
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
            assert forall|d: int, f: usize|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(f) && !self.mapped@.contains(f)
                implies f < NUM_PAGES && self.acked(d) < self.stale_epoch@[f as int] by {
                if d == c as int {
                    assert(self.tlb@[d] == Set::<usize>::empty());
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
