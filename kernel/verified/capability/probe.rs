// SPDX-License-Identifier: MIT

//! Probing the accessed and dirty bits the processor sets in up to 64 consecutive entries of one level 1
//! table of a space: each present entry's bits are read and cleared, and returned as two masks. Only those
//! bits change, so no mapping does and nothing needs a flush. A translation a TLB still holds may hide a
//! use until the next walk, which the caller treats as sampling error and confirms with an unmap when it
//! matters. At most 64 entries are read and written under the lock: see design/one-lock-bounded-steps/
//! and design/arch-module/.
use vstd::prelude::*;

verus! {

use crate::arch::*;
#[cfg(verus_keep_ghost)]
use crate::capability::block::BlockTable;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
use crate::capability::map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

/// The most entries one probe reads.
pub const PROBE_MAX: u64 = 64;

/// What a probe returns: bit i of each mask is entry i's bit as read, and whether this target's walker
/// maintains each bit, without which its mask says nothing. The words read are ghost.
#[derive(Clone, Copy)]
pub struct Probed {
    pub accessed: u64,
    pub dirty: u64,
    pub accessed_maintained: bool,
    pub dirty_maintained: bool,
    pub read: Ghost<Seq<usize>>,
}

/// Bit i of mask m is set.
pub open spec fn mask_bit(m: u64, i: int) -> bool {
    (m >> (i as u64)) & 1u64 == 1u64
}

/// Setting bit i of a mask sets it and keeps the others.
pub proof fn lemma_mask_bit_set(m: u64, i: u64)
    requires
        i < 64,
    ensures
        forall|j: int| 0 <= j < 64 ==> #[trigger] mask_bit(m | (1u64 << i), j) == (j == i || mask_bit(m, j)),
{
    assert forall|j: int| 0 <= j < 64 implies #[trigger] mask_bit(m | (1u64 << i), j) == (j == i || mask_bit(m, j)) by {
        let k = j as u64;
        assert(((m | (1u64 << i)) >> k) & 1u64 == 1u64 <==> k == i || (m >> k) & 1u64 == 1u64) by (bit_vector)
            requires
                i < 64,
                k < 64,
        ;
    }
}

/// The empty mask has no bit set.
pub proof fn lemma_mask_empty()
    ensures
        forall|j: int| 0 <= j < 64 ==> !#[trigger] mask_bit(0u64, j),
{
    assert forall|j: int| 0 <= j < 64 implies !#[trigger] mask_bit(0u64, j) by {
        let k = j as u64;
        assert((0u64 >> k) & 1u64 != 1u64) by (bit_vector);
    }
}

/// Entry e of table t of the tree as the probe found it has been probed, leaving the table's words as
/// `after`: when it is present, `word` is the word read and decodes to the entry, a and d are the word's
/// accessed and dirty bits, and the entry's bits are clear; when it is not, a and d are false.
pub open spec fn probed_entry(tree: TableTree, after: PageMap, t: usize, e: usize, word: usize, a: bool, d: bool) -> bool {
    let present = tree.entry(t, e).perm.present;
    &&& present ==> spec_usize2page_entry(word, after.level@) == tree.entry(t, e)
    &&& a == (present && spec_usize2page_entry_status(word, after.level@).accessed)
    &&& d == (present && spec_usize2page_entry_status(word, after.level@).dirty)
    &&& present ==> after.status(e as int).is_clear()
}

/// The first n entries from l1 of table t have been probed, with word j and bit j of each mask for entry
/// l1 + j.
pub open spec fn probed_prefix(tree: TableTree, after: PageMap, t: usize, l1: usize, read: Seq<usize>, accessed: u64, dirty: u64, n: int) -> bool {
    &&& read.len() == n
    &&& forall|j: int| #![trigger read[j]] 0 <= j < n
        ==> probed_entry(tree, after, t, (l1 + j) as usize, read[j], mask_bit(accessed, j), mask_bit(dirty, j))
}

/// b is a with table page t's words changed in their accessed and dirty bits alone: t keeps its view.
pub open spec fn tree_status_only(a: TableTree, b: TableTree, t: usize) -> bool {
    &&& a.maps.contains_key(t)
    &&& b.maps == a.maps.insert(t, b.maps[t])
    &&& b.maps[t].value()@ == a.maps[t].value()@
    &&& b.records == a.records
    &&& b.roots == a.roots
    &&& b.space_records == a.space_records
}

/// Such a tree has every entry, record, step and walk of the one it came from.
pub proof fn lemma_tree_status_only(a: TableTree, b: TableTree, t: usize)
    requires
        tree_status_only(a, b, t),
    ensures
        forall|u: usize| #[trigger] b.maps.contains_key(u) == a.maps.contains_key(u),
        forall|u: usize| #[trigger] b.record(u) == a.record(u),
        forall|u: usize, i: usize| #[trigger] b.entry(u, i) == a.entry(u, i),
        forall|u: usize, i: usize| #[trigger] b.child_slot(u, i) == a.child_slot(u, i),
        forall|u: usize, i: usize| #[trigger] b.names_child(u, i) == a.names_child(u, i),
        forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i),
        forall|u: usize, i: usize| #[trigger] frame_slot(b, u, i) == frame_slot(a, u, i),
        forall|s: usize, q: SpacePath| #[trigger] walk_table(b, s, q) == walk_table(a, s, q),
        forall|s: usize, q: SpacePath| #[trigger] walk(b, s, q) == walk(a, s, q),
{
    assert forall|u: usize| #[trigger] b.maps.contains_key(u) == a.maps.contains_key(u) by {}
    assert forall|u: usize| #[trigger] b.record(u) == a.record(u) by {}
    assert forall|u: usize, i: usize| #[trigger] b.entry(u, i) == a.entry(u, i) by {
        if u == t {
            assert(b.maps[t].value()[i] == b.maps[t].value()@[i as int]);
            assert(a.maps[t].value()[i] == a.maps[t].value()@[i as int]);
        }
    }
    assert forall|u: usize, i: usize| #[trigger] b.child_slot(u, i) == a.child_slot(u, i) by {
        assert(b.record(u) == a.record(u));
    }
    assert forall|u: usize, i: usize| #[trigger] b.names_child(u, i) == a.names_child(u, i) by {
        assert(b.child_slot(u, i) == a.child_slot(u, i));
        assert(b.entry(u, i) == a.entry(u, i));
    }
    assert forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i) by {
        assert(b.names_child(u, i) == a.names_child(u, i));
        assert(b.entry(u, i) == a.entry(u, i));
    }
    assert forall|u: usize, i: usize| #[trigger] frame_slot(b, u, i) == frame_slot(a, u, i) by {
        assert(b.record(u) == a.record(u));
        assert(b.entry(u, i) == a.entry(u, i));
    }
    assert forall|s: usize, q: SpacePath| #[trigger] walk_table(b, s, q) == walk_table(a, s, q) by {
        assert(step(b, s, q.l4) == step(a, s, q.l4));
        if let Some(t3) = step(a, s, q.l4) {
            assert(step(b, t3, q.l3) == step(a, t3, q.l3));
            if let Some(t2) = step(a, t3, q.l3) {
                assert(step(b, t2, q.l2) == step(a, t2, q.l2));
            }
        }
    }
    assert forall|s: usize, q: SpacePath| #[trigger] walk(b, s, q) == walk(a, s, q) by {
        assert(step(b, s, q.l4) == step(a, s, q.l4));
        if let Some(t3) = step(a, s, q.l4) {
            assert(step(b, t3, q.l3) == step(a, t3, q.l3));
            if let Some(t2) = step(a, t3, q.l3) {
                assert(step(b, t2, q.l2) == step(a, t2, q.l2));
                assert(b.record(t2) == a.record(t2));
                assert(b.entry(t2, q.l2) == a.entry(t2, q.l2));
                if let Some(t1) = step(a, t2, q.l2) {
                    assert(b.record(t1) == a.record(t1));
                    assert(b.entry(t1, q.l1) == a.entry(t1, q.l1));
                }
            }
        }
    }
}

/// Such a tree is linked as the one it came from.
pub proof fn lemma_links_status_only(a: TableTree, b: TableTree, t: usize)
    requires
        tree_status_only(a, b, t),
        table_links_wf(a),
    ensures
        table_links_wf(b),
{
    lemma_tree_status_only(a, b, t);
}

/// Such a tree keeps every mapping.
pub proof fn lemma_mappings_status_only(
    list: &Tree,
    tables: &Tables,
    a: TableTree,
    b: TableTree,
    blocks: &BlockTable,
    holders: IMap<BlockRef, Set<usize>>,
    mappings: IMap<usize, MappingRecord>,
    t: usize,
)
    requires
        tree_status_only(a, b, t),
        mappings_wf(list, tables, a, blocks, holders, mappings),
    ensures
        mappings_wf(list, tables, b, blocks, holders, mappings),
{
    lemma_tree_status_only(a, b, t);
    assert forall|n: usize| #[trigger] mappings.contains_key(n)
        implies mapping_wf(list, tables, b, blocks, holders, mappings, n) by {
        let m = mappings[n];
        assert(mapping_wf(list, tables, a, blocks, holders, mappings, n));
        assert(b.entry(m.table, m.entry) == a.entry(m.table, m.entry));
        assert(b.record(m.table) == a.record(m.table));
        assert(b.maps.contains_key(m.table) == a.maps.contains_key(m.table));
    }
    assert forall|u: usize, e: usize| #[trigger] frame_slot(b, u, e) implies {
        &&& mappings.contains_key(mapping_node(u, e))
        &&& mappings[mapping_node(u, e)].table == u
        &&& mappings[mapping_node(u, e)].entry == e
    } by {
        assert(frame_slot(a, u, e));
    }
}

/// Table pages whose page t changed in its words' accessed and dirty bits alone are as well formed.
pub proof fn lemma_table_pages_status_only(list: &Tree, pa: &TablePages, pb: &TablePages, blocks: &BlockTable, t: usize)
    requires
        table_pages_wf(list, pa, blocks),
        pa.maps@.contains_key(t),
        pb.maps@ == pa.maps@.insert(t, pb.maps@[t]),
        pb.maps@[t].addr() == pa.maps@[t].addr(),
        pb.maps@[t].is_init(),
        pb.maps@[t].value().wf(),
        pb.maps@[t].value().level == pa.maps@[t].value().level,
        pb.maps@[t].value()@ == pa.maps@[t].value()@,
        pb.records == pa.records,
        pb.spare == pa.spare,
    ensures
        table_pages_wf(list, pb, blocks),
{
    assert forall|u: usize| #[trigger] pb.maps@.contains_key(u) implies table_page_wf(list, pb, blocks, u) by {
        assert(table_page_wf(list, pa, blocks, u));
        if u == t {
            assert forall|i: usize| i < ENTRIES implies #[trigger] pb.maps@[u].value()[i] == pa.maps@[u].value()[i] by {
                assert(pb.maps@[u].value()[i] == pb.maps@[u].value()@[i as int]);
                assert(pa.maps@[u].value()[i] == pa.maps@[u].value()@[i as int]);
            }
        }
    }
    assert forall|b: usize| blocks.tracks(b as int) && #[trigger] table_block(blocks, b) implies pb.maps@.contains_key((b * PAGE_SZ) as usize) by {
        assert(pa.maps@.contains_key((b * PAGE_SZ) as usize));
    }
}

impl CapKernel {
    /// The refusals: an address that names no level 1 entry, a count of 0 or over 64, or a range that
    /// leaves its level 1 table; an index that names no capability to a process's space, or none that may
    /// change it, or one naming a dead process; a path that reaches no live level 1 table.
    pub open spec fn can_probe(&self, root: usize, slot: usize, va: u64, count: u64) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let n = self.tables.node_of(root, slot);
        let p = address_path(va);
        &&& names_entry(va, 1)
        &&& 1 <= count <= PROBE_MAX
        &&& p.l1 + count <= ENTRIES
        &&& self.tables.has_slot(&self.list, root, slot)
        &&& self.is_cap(n)
        &&& writes_space(self.payload_of(n))
        &&& !self.cap_dead(n)
        &&& self.spaces.records@[self.payload_of(n).base].value().kind == SpaceKind::Process
        &&& walk_table(tree, self.payload_of(n).base, p) is Some
    }

    /// post is pre with only table page t's words changed, each in its accessed and dirty bits alone:
    /// its view, and so every entry, is as it was.
    pub open spec fn status_only(pre: Self, post: Self, t: usize) -> bool {
        &&& pre.table_pages.maps@.contains_key(t)
        &&& post.table_pages.maps@ == pre.table_pages.maps@.insert(t, post.table_pages.maps@[t])
        &&& post.table_pages.maps@[t].addr() == pre.table_pages.maps@[t].addr()
        &&& post.table_pages.maps@[t].is_init()
        &&& post.table_pages.maps@[t].value().wf()
        &&& post.table_pages.maps@[t].value().level == pre.table_pages.maps@[t].value().level
        &&& post.table_pages.maps@[t].value()@ == pre.table_pages.maps@[t].value()@
        &&& post.table_pages.records == pre.table_pages.records
        &&& post.table_pages.spare == pre.table_pages.spare
        &&& post.list == pre.list
        &&& post.cores == pre.cores
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.iommus == pre.iommus
        &&& post.mapped == pre.mapped
        &&& post.blocks == pre.blocks
        &&& post.tables == pre.tables
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.frames == pre.frames
        &&& post.spaces == pre.spaces
        &&& post.mappings == pre.mappings
        &&& post.zeroing == pre.zeroing
        &&& post.holders == pre.holders
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.processes == pre.processes
        &&& post.stop_ipis == pre.stop_ipis
    }

    /// What a probe of count entries from the address va, in the space of the capability at index slot of
    /// the table at root, left: only the accessed and dirty bits of the level 1 table's words changed, so
    /// every entry, every table walk and the view are as they were; each entry in the range was probed
    /// (probed_entry: its word as read is its entry's, bit i of each mask is its bit as read when it is
    /// present, and its bits are clear); the masks have no bit past the range; and the two facts are the
    /// target's.
    pub open spec fn probe_done(pre: Self, post: Self, root: usize, slot: usize, va: u64, count: u64, r: Probed) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let p = address_path(va);
        let t = walk_table(a, pre.payload_of(pre.tables.node_of(root, slot)).base, p)->0;
        &&& Self::status_only(pre, post, t)
        &&& forall|u: usize, i: usize| #[trigger] b.entry(u, i) == a.entry(u, i)
        &&& forall|s: usize, q: SpacePath| #[trigger] walk_table(b, s, q) == walk_table(a, s, q)
        &&& forall|s: usize, q: SpacePath| #[trigger] walk(b, s, q) == walk(a, s, q)
        &&& post.view() == pre.view()
        &&& probed_prefix(a, post.table_pages.maps@[t].value(), t, p.l1, r.read@, r.accessed, r.dirty, count as int)
        &&& forall|i: int| count <= i < 64 ==> !#[trigger] mask_bit(r.accessed, i)
        &&& forall|i: int| count <= i < 64 ==> !#[trigger] mask_bit(r.dirty, i)
        &&& r.accessed_maintained == maintains_accessed()
        &&& r.dirty_maintained == maintains_dirty()
    }

    /// A step that changed only the accessed and dirty bits of one table page's words keeps the kernel
    /// well formed, every entry and table walk, and the view.
    pub proof fn lemma_status_only(pre: Self, post: Self, t: usize)
        requires
            pre.wf(),
            Self::status_only(pre, post, t),
        ensures
            post.wf(),
            forall|u: usize, i: usize| #[trigger] tree_of(&post.table_pages, &post.spaces).entry(u, i)
                == tree_of(&pre.table_pages, &pre.spaces).entry(u, i),
            forall|s: usize, q: SpacePath| #[trigger] walk_table(tree_of(&post.table_pages, &post.spaces), s, q)
                == walk_table(tree_of(&pre.table_pages, &pre.spaces), s, q),
            forall|s: usize, q: SpacePath| #[trigger] walk(tree_of(&post.table_pages, &post.spaces), s, q)
                == walk(tree_of(&pre.table_pages, &pre.spaces), s, q),
            post.view() == pre.view(),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(tree_status_only(a, b, t));
        lemma_tree_status_only(a, b, t);
        lemma_links_status_only(a, b, t);
        lemma_mappings_status_only(&pre.list, &pre.tables, a, b, &pre.blocks, pre.holders@, pre.mappings@, t);
        lemma_table_pages_status_only(&pre.list, &pre.table_pages, &post.table_pages, &pre.blocks, t);
        assert forall|u: usize| #[trigger] post.table_pages.maps@.contains_key(u) == pre.table_pages.maps@.contains_key(u) by {}
        assert(hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages));
        assert(table_nodes_are_mappings(&post.list, &post.table_pages));
        Self::lemma_tlb_same(pre, post);
        assert forall|s: usize, q: SpacePath| #[trigger] walk(b, s, q) == walk(a, s, q) by {}
        lemma_same_walks_same_shares(a, b);
    }

    /// A probe that changed only the status bits of the level 1 table t its path reaches, and read the
    /// first count entries from the path's level 1 index into r, is done.
    pub proof fn lemma_probe_done(pre: Self, post: Self, root: usize, slot: usize, va: u64, count: u64, t: usize, r: Probed)
        requires
            pre.wf(),
            pre.can_probe(root, slot, va, count),
            tree_of(&pre.table_pages, &pre.spaces).is_page(t),
            t == walk_table(tree_of(&pre.table_pages, &pre.spaces), pre.payload_of(pre.tables.node_of(root, slot)).base, address_path(va))->0,
            Self::status_only(pre, post, t),
            probed_prefix(
                tree_of(&pre.table_pages, &pre.spaces),
                post.table_pages.maps@[t].value(),
                t,
                address_path(va).l1,
                r.read@,
                r.accessed,
                r.dirty,
                count as int,
            ),
            forall|j: int| count <= j < 64 ==> !#[trigger] mask_bit(r.accessed, j),
            forall|j: int| count <= j < 64 ==> !#[trigger] mask_bit(r.dirty, j),
            r.accessed_maintained == maintains_accessed(),
            r.dirty_maintained == maintains_dirty(),
        ensures
            post.wf(),
            Self::probe_done(pre, post, root, slot, va, count, r),
    {
        Self::lemma_status_only(pre, post, t);
    }

    /// Reads and clears the accessed and dirty bits of `count` entries, from the one the address `va`
    /// names, of the level 1 table it reaches in the space of the capability at index `slot` of the table
    /// at `root`. All of these come from user space, and a refusal changes nothing. See
    /// design/syscall-abi-in-registers/. Each entry is one unit, and a count over PROBE_MAX is refused.
    pub fn probe_at(&mut self, root: usize, slot: usize, va: u64, count: u64, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Probed>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(steps).count <= old(steps).count + PROBE_MAX,
            final(self).wf(),
            ret is Some == old(self).can_probe(root, slot, va, count),
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> Self::probe_done(*old(self), *final(self), root, slot, va, count, ret->0),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        let ghost p = address_path(va);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        if !entry_named(va, 1) || count == 0 || count > PROBE_MAX {
            return None;
        }
        let (l4, l3, l2, l1) = address_indices(va);
        if l1 + count as usize > ENTRIES {
            return None;
        }
        let (n, space) = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found,
            None => { return None; },
        };
        proof {
            pre.lemma_slot(root, slot);
            assert(space == pre.payload_of(n));
        }
        let n_node = self.list.get(n);
        let n_kind = match n_node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !n_node.live || !n_kind || !may_write_space(&space) {
            return None;
        }
        proof {
            assert(pre.is_cap(n));
            pre.lemma_written_space(n);
            pre.lemma_root_table(space.base);
        }
        if self.is_cap_dead(n, space) {
            return None;
        }
        let s = space.base;
        if !same_kind(self.space_kind(s), SpaceKind::Process) {
            return None;
        }
        let t3 = match self.table_step(s, true, l4) {
            Some(t) => t,
            None => { return None; },
        };
        let t2 = match self.table_step(t3, false, l3) {
            Some(t) => t,
            None => { return None; },
        };
        let t = match self.table_step(t2, false, l2) {
            Some(t) => t,
            None => { return None; },
        };
        proof {
            assert(walk_table(tree, s, p) == Some(t));
            assert(tree.is_page(t));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
            assert(tree.record(t).level == 1);
            assert(pre.table_pages.maps@[t].value().level@ == 1);
            lemma_table_bound(t);
            assert(pre.can_probe(root, slot, va, count));
        }
        let ghost m0 = pre.table_pages.maps@[t];
        let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(t);
        let ptr = t + TABLE_NODE_PAGES * PAGE_SZ;
        let mut accessed: u64 = 0;
        let mut dirty: u64 = 0;
        let ghost mut read: Seq<usize> = Seq::empty();
        let mut i: u64 = 0;
        proof {
            lemma_mask_empty();
        }
        let ghost start = steps.count;
        while i < count
            invariant
                0 <= i <= count <= PROBE_MAX,
                steps.count == start + i,
                l1 + count <= ENTRIES,
                l1 == p.l1,
                m0 == pre.table_pages.maps@[t],
                tree.is_page(t),
                tree.maps[t] == m0,
                map.addr() == ptr,
                ptr == m0.addr(),
                map.is_init(),
                map.value().wf(),
                map.value().level == m0.value().level,
                m0.value().level@ == 1,
                map.value()@ == m0.value()@,
                probed_prefix(tree, map.value(), t, l1, read, accessed, dirty, i as int),
                forall|j: int| i <= j < 64 ==> !#[trigger] mask_bit(accessed, j),
                forall|j: int| i <= j < 64 ==> !#[trigger] mask_bit(dirty, j),
            decreases count - i,
        {
            let e = l1 + i as usize;
            let entry = PPtr::<PageMap>::from_usize(ptr).borrow(Tracked(&map)).get(e, 1);
            let ghost before = map.value();
            let ghost read0 = read;
            let ghost accessed0 = accessed;
            let ghost dirty0 = dirty;
            let ghost mut word0: usize = 0;
            let ghost mut a0 = false;
            let ghost mut d0 = false;
            assert(entry == m0.value()[e]);
            assert(tree.entry(t, e) == m0.value()[e]);
            if entry.perm.present {
                let word = page_map_clear_status(ptr, Tracked(&mut map), e);
                let status = usize2page_entry_status(word, 1);
                let a_bit = status.accessed;
                let d_bit = status.dirty;
                proof {
                    lemma_mask_bit_set(accessed, i);
                    lemma_mask_bit_set(dirty, i);
                    word0 = word;
                    a0 = a_bit;
                    d0 = d_bit;
                    assert(a_bit == spec_usize2page_entry_status(word, map.value().level@).accessed);
                    assert(d_bit == spec_usize2page_entry_status(word, map.value().level@).dirty);
                }
                if a_bit {
                    accessed = accessed | (1u64 << i);
                }
                if d_bit {
                    dirty = dirty | (1u64 << i);
                }
            }
            proof {
                read = read0.push(word0);
                assert(forall|j: int| 0 <= j < 64 && j != i ==> mask_bit(accessed, j) == #[trigger] mask_bit(accessed0, j));
                assert(forall|j: int| 0 <= j < 64 && j != i ==> mask_bit(dirty, j) == #[trigger] mask_bit(dirty0, j));
                assert(mask_bit(accessed, i as int) == a0);
                assert(mask_bit(dirty, i as int) == d0);
                assert forall|j: int| #![trigger read[j]] 0 <= j < i + 1
                    implies probed_entry(tree, map.value(), t, (l1 + j) as usize, read[j], mask_bit(accessed, j), mask_bit(dirty, j)) by {
                    let f = (l1 + j) as usize;
                    if j < i {
                        assert(read[j] == read0[j]);
                        assert(probed_entry(tree, before, t, f, read0[j], mask_bit(accessed0, j), mask_bit(dirty0, j)));
                        assert(mask_bit(accessed, j) == mask_bit(accessed0, j));
                        assert(mask_bit(dirty, j) == mask_bit(dirty0, j));
                        assert(f != e);
                        assert(map.value().ar@[f as int] == before.ar@[f as int]);
                    } else {
                        assert(j == i);
                        assert(f == e);
                        assert(read[j] == word0);
                    }
                }
                assert(probed_prefix(tree, map.value(), t, l1, read, accessed, dirty, i + 1));
                assert forall|j: int| i + 1 <= j < 64 implies !#[trigger] mask_bit(accessed, j) by {
                    assert(mask_bit(accessed, j) == mask_bit(accessed0, j));
                }
                assert forall|j: int| i + 1 <= j < 64 implies !#[trigger] mask_bit(dirty, j) by {
                    assert(mask_bit(dirty, j) == mask_bit(dirty0, j));
                }
            }
            i = i + 1;
            proof {
                steps.step();
            }
        }
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(t, map);
            assert(self.table_pages.maps@ =~= pre.table_pages.maps@.insert(t, map));
        }
        let r = Probed {
            accessed,
            dirty,
            accessed_maintained: maintains_accessed(),
            dirty_maintained: maintains_dirty(),
            read: Ghost(read),
        };
        proof {
            assert(Self::status_only(pre, *self, t));
            assert(self.table_pages.maps@[t] == map);
            Self::lemma_probe_done(pre, *self, root, slot, va, count, t, r);
        }
        Some(r)
    }
}

} // verus!
