//! The boot step that gives one path of the root's space its tables: for each of the level 3, 2 and 1
//! tables the walk of a path prefix does not reach yet, the next order-3 block of the root's untyped at
//! ROOT_UNTYPED_SLOT is retyped as a table page and linked through the root's process capability at
//! ROOT_PROCESS_SLOT, as every mapper pays for its tables; a table the walk reaches is reused. See
//! design/address-spaces-as-objects/, design/untyped-memory/ and design/process-holds-capabilities/.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::derive::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::reach::*;
use crate::capability::retype::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::define::*;

/// The k-th order-3 block from the cursor.
pub open spec fn cursor_block(cursor: usize, k: int) -> usize {
    (cursor + k * 32768) as usize
}

/// t is one of the blocks from cursor up to next, which a table step has made table pages.
pub open spec fn made_from(cursor: usize, next: usize, t: usize) -> bool {
    &&& t < next
    &&& t == cursor || t == cursor + 32768 || t == cursor + 65536
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
        b % 32768 == 0,
        c % 32768 == 0,
        b != c,
    ensures
        b / 4096 + 8 <= c / 4096 || c / 4096 + 8 <= b / 4096,
{
    assert(b / 4096 + 8 <= c / 4096 || c / 4096 + 8 <= b / 4096) by (nonlinear_arith)
        requires
            b % 32768 == 0,
            c % 32768 == 0,
            b != c,
    {
    }
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
        &&& !self.blocks.pages@[(self.root_space(process) / 4096) as int].dead
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
        &&& b / 4096 + 8 <= NUM_PAGES
        &&& !self.blocks.covered((b / 4096) as int)
        &&& forall|k: int| 0 <= k < 8 ==> #[trigger] self.blocks.pages@[b / 4096 + k].kind is Free
    }

    /// A table lies in a typed block of its own; a table page is no root, and a root is its space's,
    /// at level 4.
    pub proof fn lemma_table_base(&self, t: usize)
        requires
            self.wf(),
            tree_of(&self.table_pages, &self.spaces).is_table(t),
        ensures
            self.blocks.pages@[(t / 4096) as int].kind is Base,
            t / 4096 < NUM_PAGES,
            t % 32768 == 0,
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
                &&& tree.entry(t, i).addr == c + TABLE_NODE_PAGES * 4096
                &&& tree.record(c).level + 1 == tree.record(t).level
                &&& tree.record(c).space == tree.record(t).space
                &&& !self.blocks.pages@[(c / 4096) as int].dead
            }),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let c = (tree.entry(t, i).addr - TABLE_NODE_PAGES * 4096) as usize;
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
            self.blocks.pages@[(c / 4096) as int].refs != 0 || self.table_pages.records@[c].value().parent is Some,
        ensures
            !self.blocks.pages@[(c / 4096) as int].dead,
    {
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, c));
    }

    /// A page that is not free lies outside a free block.
    pub proof fn lemma_outside_block(&self, process: usize, b: usize, j: int)
        requires
            self.root_table_block(process, b),
            !(self.blocks.pages@[j].kind is Free),
        ensures
            !(b / 4096 <= j < b / 4096 + 8),
    {
        if b / 4096 <= j < b / 4096 + 8 {
            let k = j - b / 4096;
            assert(self.blocks.pages@[b / 4096 + k].kind is Free);
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
            post.blocks.pages@[(pre.root_space(process) / 4096) as int] == pre.blocks.pages@[(pre.root_space(process) / 4096) as int],
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
            used % 32768 == 0,
            b != used,
            forall|j: int| #![trigger post.blocks.pages@[j]] 0 <= j < NUM_PAGES && !(used / 4096 <= j < used / 4096 + 8)
                ==> post.blocks.pages@[j] == pre.blocks.pages@[j],
        ensures
            post.root_table_block(process, b),
    {
        lemma2_to64();
        assert(block_bytes(3) == 32768);
        lemma_blocks_apart(b, used);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] post.blocks.pages@[b / 4096 + k].kind is Free by {
            assert(pre.blocks.pages@[b / 4096 + k].kind is Free);
        }
    }

    /// Gives entry i of the root's table t a child table at the given level: the one it names, changing
    /// nothing, or the block at the cursor, retyped as a table page under the root's untyped at
    /// ROOT_UNTYPED_SLOT and linked through the root's capability at ROOT_PROCESS_SLOT. Returns the child
    /// and whether it is the cursor's new table. The entry holds no large frame, and the cursor's block
    /// is free in the root's untyped, so it never refuses.
    #[verifier::spinoff_prover]
    pub fn boot_root_table(&mut self, process: usize, s: usize, t: usize, is_root: bool, i: usize, level: usize, cursor: usize)
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
            !old(self).blocks.pages@[(t / 4096) as int].dead,
            !(tree_of(&old(self).table_pages, &old(self).spaces).entry(t, i).perm.present
                && tree_of(&old(self).table_pages, &old(self).spaces).entry(t, i).perm.ps),
        ensures
            final(self).wf(),
            final(self).root_tables_ready(process),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).spaces.roots@.dom() == old(self).spaces.roots@.dom(),
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] 0 <= j < NUM_PAGES && !(ret.1 && cursor / 4096 <= j < cursor / 4096 + 8)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && old(self).list.nodes@[j].live
                ==> final(self).list.nodes@[j].live,
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
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
            !final(self).blocks.pages@[(ret.0 / 4096) as int].dead,
            !ret.1 ==> *final(self) == *old(self),
            ret.1 ==> {
                &&& ret.0 == cursor
                &&& final(self).table_pages.maps@.dom() == old(self).table_pages.maps@.dom().insert(cursor)
                &&& forall|j: usize| j < 512 ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(cursor, j).is_empty()
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
        }
        let e = self.table_entry(t, is_root, i);
        if e.perm.present {
            proof {
                assert(a.names_child(t, i));
                pre.lemma_child_facts(t, i);
            }
            return ((e.addr - TABLE_NODE_PAGES * 4096) as usize, false);
        }
        let ghost n = pre.tables.node_of(process, ROOT_PROCESS_SLOT);
        let ghost u = pre.root_untyped(process);
        proof {
            assert(a.entry(t, i).is_empty());
            lemma2_to64();
            assert(block_bytes(3) == 32768);
            assert(pre.blocks.pages@[cursor / 4096 + 0].kind is Free);
            pre.lemma_free_not_table(cursor, cursor / 4096);
            pre.lemma_slot(process, ROOT_UNTYPED_SLOT);
            pre.lemma_slot_bound(u);
            pre.lemma_slot(process, ROOT_PROCESS_SLOT);
            pre.lemma_slot_bound(n);
            assert(pre.can_retype_under(process, ROOT_UNTYPED_SLOT, cursor, 3));
            pre.lemma_written_space(n);
            pre.lemma_table_base(s);
            pre.lemma_outside_block(process, cursor, (s / 4096) as int);
            pre.lemma_outside_block(process, cursor, (t / 4096) as int);
        }
        let retyped = self.retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level);
        let ghost mid = *self;
        let ghost m = tree_of(&mid.table_pages, &mid.spaces);
        proof {
            assert(retyped);
            Self::lemma_ready_kept(pre, mid, process);
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
            assert forall|x: usize| #![trigger post.root_table_block(process, x)]
                pre.root_table_block(process, x) && x != cursor implies post.root_table_block(process, x) by {
                Self::lemma_block_kept(pre, post, process, x, cursor);
            }
            assert(post.table_pages.maps@.dom() =~= pre.table_pages.maps@.dom().insert(cursor));
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
    pub fn boot_root_path(&mut self, process: usize, s: usize, l4: usize, l3: usize, l2: usize, cursor: usize) -> (ret: usize)
        requires
            old(self).wf(),
            old(self).root_tables_ready(process),
            s == old(self).root_space(process),
            KERNEL_MEM_END_L4INDEX <= l4 < 512,
            l3 < 512,
            l2 < 512,
            cursor + 3 * 32768 <= NUM_PAGES * 4096,
            forall|k: int| 0 <= k < 3 ==> #[trigger] old(self).root_table_block(process, cursor_block(cursor, k)),
            !space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), s).contains_key(SpacePath { l4, l3, l2, l1: 0 }),
        ensures
            final(self).wf(),
            final(self).root_tables_ready(process),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).spaces.roots@.dom() == old(self).spaces.roots@.dom(),
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            ret == cursor || ret == cursor + 32768 || ret == cursor + 65536 || ret == cursor + 98304,
            forall|t: usize| #[trigger] final(self).table_pages.maps@.contains_key(t)
                <==> (old(self).table_pages.maps@.contains_key(t) || made_from(cursor, ret, t)),
            forall|j: int| #![trigger final(self).blocks.pages@[j]] 0 <= j < NUM_PAGES && !(cursor / 4096 <= j < ret / 4096)
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
                &&& !final(self).blocks.pages@[(t1 / 4096) as int].dead
            },
            forall|t: usize| #![trigger tree_of(&final(self).table_pages, &final(self).spaces).record(t)]
                final(self).table_pages.maps@.contains_key(t) && !old(self).table_pages.maps@.contains_key(t)
                && tree_of(&final(self).table_pages, &final(self).spaces).record(t).level == 1
                ==> forall|j: usize| j < 512 ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(t, j).is_empty(),
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
        let c1 = if m3 { cursor + 32768 } else { cursor };
        proof {
            lemma2_to64();
            assert(block_bytes(3) == 32768);
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
        let c2 = if m2 { c1 + 32768 } else { c1 };
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
        let c3 = if m1 { c2 + 32768 } else { c2 };
        proof {
            let post = *self;
            let b3 = tree_of(&post.table_pages, &post.spaces);
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
                &&& !post.blocks.pages@[(walk_table(b3, s, p)->0 / 4096) as int].dead
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
                implies forall|j: usize| j < 512 ==> #[trigger] b3.entry(t, j).is_empty() by {
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
        }
        c3
    }
}

} // verus!
