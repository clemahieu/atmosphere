//! Linking a table page into an entry of a table in a space. A table's entry and its child's record say
//! the same thing, and a link writes both in one step, so a detach can always clear both. See the design
//! on atmo-6x9.6.7, sections 6 and 8.
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::{ObjectType, PageKind};
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::mapping::*;
use crate::capability::refs::*;
use crate::capability::reach::*;
use crate::capability::retype::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::define::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;
use crate::util::page_ptr_util_u::*;

/// Every table the kernel holds, whether a table page or a space's root, by its block's address.
pub ghost struct TableTree {
    pub maps: Map<usize, PointsTo<PageMap>>,
    pub records: Map<usize, PointsTo<TableRecord>>,
    pub roots: Map<usize, PointsTo<PageMap>>,
    pub space_records: Map<usize, PointsTo<SpaceRecord>>,
}

pub open spec fn tree_of(pages: &TablePages, spaces: &Spaces) -> TableTree {
    TableTree { maps: pages.maps@, records: pages.records@, roots: spaces.roots@, space_records: spaces.records@ }
}

impl TableTree {
    pub open spec fn is_page(self, t: usize) -> bool {
        self.maps.contains_key(t)
    }

    pub open spec fn is_root(self, t: usize) -> bool {
        self.roots.contains_key(t)
    }

    pub open spec fn is_table(self, t: usize) -> bool {
        self.is_page(t) || self.is_root(t)
    }

    pub open spec fn entry(self, t: usize, i: usize) -> PageEntry {
        if self.is_page(t) { self.maps[t].value()[i] } else { self.roots[t].value()[i] }
    }

    pub open spec fn record(self, t: usize) -> TableRecord {
        if self.is_page(t) { self.records[t].value() } else { self.space_records[t].value().table }
    }

    /// Entry i of table t can point at a child table: it is above level 1 and no kernel slot. Only a
    /// process's root has kernel slots.
    pub open spec fn child_slot(self, t: usize, i: usize) -> bool {
        &&& self.is_table(t)
        &&& i < 512
        &&& self.record(t).level >= 2
        &&& self.is_root(t) ==> !holds_kernel(self.space_records[t].value().kind, i)
    }

    /// Entry i of table t names a child table: present in a slot that can hold one, without ps. The ps
    /// bit is what tells it from a large frame's entry.
    pub open spec fn names_child(self, t: usize, i: usize) -> bool {
        &&& self.child_slot(t, i)
        &&& self.entry(t, i).perm.present
        &&& !self.entry(t, i).perm.ps
    }
}

/// The address a table page's entry holds for it: its table's.
pub open spec fn table_addr(t: usize) -> usize {
    (t + TABLE_NODE_PAGES * 4096) as usize
}

/// A present entry above level 1, outside the kernel slots, names a child table whose record names that
/// entry, and a child's record names a present entry that names it, one level up and in the same space.
/// A table page with a parent has a space, and a space is a space the kernel holds. A table page with a
/// space and no parent has been cut off with what is below it, which still names that space.
pub open spec fn table_links_wf(tree: TableTree) -> bool {
    &&& forall|t: usize, i: usize| #![trigger tree.entry(t, i)]
        tree.names_child(t, i) ==> {
        let c = (tree.entry(t, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        &&& tree.is_page(c)
        &&& tree.record(c).parent == Some(TableParent { table: t, entry: i })
    }
    &&& forall|t: usize, i: usize| #![trigger tree.entry(t, i)]
        tree.child_slot(t, i) && tree.entry(t, i).perm.present && tree.entry(t, i).perm.ps ==> tree.record(t).level == 2
    &&& forall|c: usize| #![trigger tree.maps.contains_key(c)] tree.is_page(c) ==> {
        let r = tree.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& tree.names_child(p.table, p.entry)
            &&& tree.entry(p.table, p.entry).addr == table_addr(c)
            &&& tree.record(p.table).level == r.level + 1
            &&& tree.record(p.table).space == r.space
        }
        &&& r.space is Some ==> tree.is_root(r.space->0)
    }
}

/// b is a without table page t, which is no space's root, has no parent and has no entry.
pub open spec fn table_removed(a: TableTree, b: TableTree, t: usize) -> bool {
    &&& a.is_page(t)
    &&& !a.is_root(t)
    &&& b.maps == a.maps.remove(t)
    &&& b.records == a.records.remove(t)
    &&& b.roots == a.roots
    &&& b.space_records == a.space_records
    &&& a.record(t).parent is None
    &&& forall|i: usize| i < 512 ==> #[trigger] a.entry(t, i).is_empty()
}

/// Every table but t reads as it did.
pub proof fn lemma_table_removed_others(a: TableTree, b: TableTree, t: usize, u: usize)
    requires
        table_removed(a, b, t),
        u != t,
    ensures
        b.is_page(u) == a.is_page(u),
        b.is_root(u) == a.is_root(u),
        b.is_table(u) == a.is_table(u),
        b.record(u) == a.record(u),
        forall|i: usize| #[trigger] b.entry(u, i) == a.entry(u, i),
        forall|i: usize| #[trigger] b.child_slot(u, i) == a.child_slot(u, i),
        forall|i: usize| #[trigger] b.names_child(u, i) == a.names_child(u, i),
{
    assert forall|i: usize| #[trigger] b.entry(u, i) == a.entry(u, i) by {}
    assert forall|i: usize| #[trigger] b.child_slot(u, i) == a.child_slot(u, i) by {}
    assert forall|i: usize| #[trigger] b.names_child(u, i) == a.names_child(u, i) by {
        assert(b.entry(u, i) == a.entry(u, i));
        assert(b.child_slot(u, i) == a.child_slot(u, i));
    }
}

/// A table page with no parent and no entry goes and the links stay: no entry named it, it named nothing,
/// and every other table is as it was.
pub proof fn lemma_links_table_removed(a: TableTree, b: TableTree, t: usize)
    requires
        table_links_wf(a),
        table_removed(a, b, t),
    ensures
        table_links_wf(b),
{
    assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        b.names_child(u, i) implies {
        let c = (b.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        &&& b.is_page(c)
        &&& b.record(c).parent == Some(TableParent { table: u, entry: i })
    } by {
        assert(u != t);
        lemma_table_removed_others(a, b, t, u);
        assert(a.names_child(u, i));
        assert(a.entry(u, i) == b.entry(u, i));
        let c = (a.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        assert(a.is_page(c));
        assert(a.record(c).parent == Some(TableParent { table: u, entry: i }));
        assert(c != t);
        lemma_table_removed_others(a, b, t, c);
    }
    assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        b.child_slot(u, i) && b.entry(u, i).perm.present && b.entry(u, i).perm.ps implies b.record(u).level == 2 by {
        assert(u != t);
        lemma_table_removed_others(a, b, t, u);
        assert(a.entry(u, i) == b.entry(u, i));
        assert(a.child_slot(u, i));
    }
    assert forall|c: usize| #![trigger b.maps.contains_key(c)] b.is_page(c) implies {
        let r = b.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& b.names_child(p.table, p.entry)
            &&& b.entry(p.table, p.entry).addr == table_addr(c)
            &&& b.record(p.table).level == r.level + 1
            &&& b.record(p.table).space == r.space
        }
        &&& r.space is Some ==> b.is_root(r.space->0)
    } by {
        assert(c != t);
        lemma_table_removed_others(a, b, t, c);
        assert(a.is_page(c));
        assert(a.maps.contains_key(c));
        let r = a.record(c);
        if r.parent is Some {
            let p = r.parent->0;
            assert(a.names_child(p.table, p.entry));
            if p.table == t {
                assert(a.entry(t, p.entry).is_empty());
            }
            lemma_table_removed_others(a, b, t, p.table);
            assert(b.entry(p.table, p.entry) == a.entry(p.table, p.entry));
            assert(b.names_child(p.table, p.entry) == a.names_child(p.table, p.entry));
        }
    }
}

/// Every walk reads as it did: t was on none, since nothing named it, and it found nothing itself.
pub proof fn lemma_walk_table_removed(a: TableTree, b: TableTree, t: usize, r: usize, p: SpacePath)
    requires
        table_removed(a, b, t),
    ensures
        walk(b, r, p) == walk(a, r, p),
{
    assert forall|u: usize, i: usize| {
        &&& #[trigger] step(b, u, i) == step(a, u, i)
        &&& frame_entry(b, u, i) == frame_entry(a, u, i)
        &&& large_entry(b, u, i) == large_entry(a, u, i)
    } by {
        if u == t {
            assert(!b.is_table(t));
            if i < 512 {
                assert(a.entry(t, i).is_empty());
            }
        } else {
            lemma_table_removed_others(a, b, t, u);
            assert(b.entry(u, i) == a.entry(u, i));
            assert(b.names_child(u, i) == a.names_child(u, i));
        }
    }
    assert(a.is_root(r) == b.is_root(r));
    if a.is_root(r) {
        assert(step(b, r, p.l4) == step(a, r, p.l4));
        if let Some(t3) = step(a, r, p.l4) {
            assert(step(b, t3, p.l3) == step(a, t3, p.l3));
            if let Some(t2) = step(a, t3, p.l3) {
                assert(step(b, t2, p.l2) == step(a, t2, p.l2));
                assert(large_entry(b, t2, p.l2) == large_entry(a, t2, p.l2));
                if let Some(t1) = step(a, t2, p.l2) {
                    assert(step(b, t1, p.l1) == step(a, t1, p.l1));
                    assert(frame_entry(b, t1, p.l1) == frame_entry(a, t1, p.l1));
                }
            }
        }
    }
}

/// A table page typed afresh keeps the links: it has no parent and no space, every entry of it is empty,
/// no record names it, since a parent is a table the kernel already held, and every other table is as
/// it was.
pub proof fn lemma_links_table_added(pre: TableTree, post: TableTree, t: usize)
    requires
        table_links_wf(pre),
        !pre.is_table(t),
        post.maps == pre.maps.insert(t, post.maps[t]),
        post.records == pre.records.insert(t, post.records[t]),
        post.roots == pre.roots,
        post.space_records == pre.space_records,
        post.record(t).parent is None,
        post.record(t).space is None,
        forall|i: usize| i < 512 ==> #[trigger] post.entry(t, i).is_empty(),
    ensures
        table_links_wf(post),
{
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.names_child(u, i) implies {
        let c = (post.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        &&& post.is_page(c)
        &&& post.record(c).parent == Some(TableParent { table: u, entry: i })
    } by {
        if u == t {
            assert(post.entry(t, i).is_empty());
        }
        assert(pre.is_table(u));
        assert(post.record(u) == pre.record(u));
        assert(post.entry(u, i) == pre.entry(u, i));
        assert(pre.names_child(u, i));
        let c = (pre.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        assert(pre.is_page(c));
        assert(c != t);
        assert(post.record(c) == pre.record(c));
    }
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.child_slot(u, i) && post.entry(u, i).perm.present && post.entry(u, i).perm.ps implies post.record(u).level == 2 by {
        if u == t {
            assert(post.entry(t, i).is_empty());
        }
        assert(pre.is_table(u));
        assert(post.record(u) == pre.record(u));
        assert(post.entry(u, i) == pre.entry(u, i));
        assert(pre.child_slot(u, i));
    }
    assert forall|c: usize| #![trigger post.maps.contains_key(c)] post.is_page(c) implies {
        let r = post.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& post.names_child(p.table, p.entry)
            &&& post.entry(p.table, p.entry).addr == table_addr(c)
            &&& post.record(p.table).level == r.level + 1
            &&& post.record(p.table).space == r.space
        }
        &&& r.space is Some ==> post.is_root(r.space->0)
    } by {
        if c != t {
            assert(pre.is_page(c));
            assert(post.record(c) == pre.record(c));
            let r = pre.record(c);
            if r.parent is Some {
                let p = r.parent->0;
                assert(pre.names_child(p.table, p.entry));
                assert(p.table != t);
                assert(post.record(p.table) == pre.record(p.table));
                assert(post.entry(p.table, p.entry) == pre.entry(p.table, p.entry));
            }
        }
    }
}

/// A root typed afresh keeps the links, as a table page does: its record names its own space, it has
/// no parent, and every entry of it outside the kernel slots is empty.
pub proof fn lemma_links_root_added(pre: TableTree, post: TableTree, s: usize)
    requires
        table_links_wf(pre),
        !pre.is_table(s),
        post.maps == pre.maps,
        post.records == pre.records,
        post.roots == pre.roots.insert(s, post.roots[s]),
        post.space_records == pre.space_records.insert(s, post.space_records[s]),
        post.record(s).parent is None,
        forall|i: usize| i < 512 && !holds_kernel(post.space_records[s].value().kind, i) ==> #[trigger] post.entry(s, i).is_empty(),
    ensures
        table_links_wf(post),
{
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.names_child(u, i) implies {
        let c = (post.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        &&& post.is_page(c)
        &&& post.record(c).parent == Some(TableParent { table: u, entry: i })
    } by {
        if u == s {
            assert(post.entry(s, i).is_empty());
        }
        assert(pre.is_table(u));
        assert(post.record(u) == pre.record(u));
        assert(post.entry(u, i) == pre.entry(u, i));
        assert(pre.names_child(u, i));
        let c = (pre.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        assert(pre.is_page(c));
        assert(post.record(c) == pre.record(c));
    }
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.child_slot(u, i) && post.entry(u, i).perm.present && post.entry(u, i).perm.ps implies post.record(u).level == 2 by {
        if u == s {
            assert(post.entry(s, i).is_empty());
        }
        assert(pre.is_table(u));
        assert(post.record(u) == pre.record(u));
        assert(post.entry(u, i) == pre.entry(u, i));
        assert(pre.child_slot(u, i));
    }
    assert forall|c: usize| #![trigger post.maps.contains_key(c)] post.is_page(c) implies {
        let r = post.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& post.names_child(p.table, p.entry)
            &&& post.entry(p.table, p.entry).addr == table_addr(c)
            &&& post.record(p.table).level == r.level + 1
            &&& post.record(p.table).space == r.space
        }
        &&& r.space is Some ==> post.is_root(r.space->0)
    } by {
        assert(pre.is_page(c));
        assert(post.record(c) == pre.record(c));
        let r = pre.record(c);
        if r.parent is Some {
            let p = r.parent->0;
            assert(pre.names_child(p.table, p.entry));
            assert(p.table != s);
            assert(post.record(p.table) == pre.record(p.table));
            assert(post.entry(p.table, p.entry) == pre.entry(p.table, p.entry));
        }
    }
}

/// An entry that names a child table.
pub open spec fn child_entry(child: usize) -> PageEntry {
    PageEntry {
        addr: table_addr(child),
        perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true },
    }
}

/// What a link changes between two trees of the same tables: the parent's entry, the child's record,
/// and the written flag of the parent's, whose level, space and parent stay.
pub open spec fn linked(pre: TableTree, post: TableTree, parent: usize, entry: usize, child: usize, s: usize) -> bool {
    &&& post.maps.dom() == pre.maps.dom()
    &&& post.roots.dom() == pre.roots.dom()
    &&& post.entry(parent, entry) == child_entry(child)
    &&& forall|t: usize, i: usize| #![trigger post.entry(t, i)]
        pre.is_table(t) && i < 512 && !(t == parent && i == entry) ==> post.entry(t, i) == pre.entry(t, i)
    &&& forall|t: usize| #![trigger post.record(t)] pre.is_table(t) ==> post.record(t).level == pre.record(t).level
    &&& forall|t: usize| #![trigger post.record(t)] pre.is_table(t) && t != child ==> {
        &&& post.record(t).space == pre.record(t).space
        &&& post.record(t).parent == pre.record(t).parent
    }
    &&& post.record(child).space == Some(s)
    &&& post.record(child).parent == Some(TableParent { table: parent, entry })
    &&& forall|t: usize| #![trigger post.space_records[t]]
        pre.is_root(t) ==> post.space_records[t].value().kind == pre.space_records[t].value().kind
}

/// A link into an empty entry of a table in space s, of a table page one level below it that had no
/// parent, keeps the links: the new entry and the child's record name each other, and every other entry
/// and record are as they were, and none of those named the child or the entry.
pub proof fn lemma_links_linked(pre: TableTree, post: TableTree, parent: usize, entry: usize, child: usize, s: usize)
    requires
        table_links_wf(pre),
        linked(pre, post, parent, entry, child, s),
        pre.child_slot(parent, entry),
        pre.entry(parent, entry).is_empty(),
        pre.is_page(child),
        pre.record(child).parent is None,
        pre.record(child).space is None,
        pre.record(child).level + 1 == pre.record(parent).level,
        pre.record(parent).space == Some(s),
        pre.is_root(s),
        child + TABLE_NODE_PAGES * 4096 <= usize::MAX,
    ensures
        table_links_wf(post),
{
    assert forall|t: usize| #[trigger] post.is_table(t) == pre.is_table(t) by {
        assert(post.maps.contains_key(t) == pre.maps.contains_key(t));
        assert(post.roots.contains_key(t) == pre.roots.contains_key(t));
    }
    assert forall|t: usize| #[trigger] post.is_page(t) == pre.is_page(t) by {
        assert(post.maps.contains_key(t) == pre.maps.contains_key(t));
    }
    assert forall|t: usize| #[trigger] post.is_root(t) == pre.is_root(t) by {
        assert(post.roots.contains_key(t) == pre.roots.contains_key(t));
    }
    assert forall|t: usize, i: usize| #[trigger] post.child_slot(t, i) == pre.child_slot(t, i) by {
        if pre.is_table(t) {
            assert(post.record(t).level == pre.record(t).level);
        }
    }
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.names_child(u, i) implies {
        let c = (post.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        &&& post.is_page(c)
        &&& post.record(c).parent == Some(TableParent { table: u, entry: i })
    } by {
        if u == parent && i == entry {
            assert(post.entry(parent, entry) == child_entry(child));
            assert((child_entry(child).addr - TABLE_NODE_PAGES * 4096) as usize == child);
        } else {
            assert(post.entry(u, i) == pre.entry(u, i));
            assert(pre.names_child(u, i));
            let c = (pre.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
            assert(pre.is_page(c));
            assert(pre.record(c).parent == Some(TableParent { table: u, entry: i }));
            assert(c != child);
            assert(post.record(c).parent == pre.record(c).parent);
        }
    }
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.child_slot(u, i) && post.entry(u, i).perm.present && post.entry(u, i).perm.ps implies post.record(u).level == 2 by {
        if !(u == parent && i == entry) {
            assert(post.entry(u, i) == pre.entry(u, i));
            assert(pre.child_slot(u, i));
            assert(pre.record(u).level == 2);
            assert(post.record(u).level == pre.record(u).level);
        }
    }
    assert forall|c: usize| #![trigger post.maps.contains_key(c)] post.is_page(c) implies {
        let r = post.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& post.names_child(p.table, p.entry)
            &&& post.entry(p.table, p.entry).addr == table_addr(c)
            &&& post.record(p.table).level == r.level + 1
            &&& post.record(p.table).space == r.space
        }
        &&& r.space is Some ==> post.is_root(r.space->0)
    } by {
        assert(pre.is_page(c));
        if c == child {
            assert(post.record(child).level == pre.record(child).level);
            assert(post.record(parent).level == pre.record(parent).level);
            assert(post.record(parent).space == pre.record(parent).space);
            assert(post.entry(parent, entry) == child_entry(child));
        } else {
            let r = pre.record(c);
            assert(post.record(c).space == r.space);
            assert(post.record(c).parent == r.parent);
            assert(post.record(c).level == r.level);
            if r.parent is Some {
                let p = r.parent->0;
                assert(pre.names_child(p.table, p.entry));
                if p.table == parent && p.entry == entry {
                    assert(pre.entry(parent, entry).is_empty());
                }
                assert(post.entry(p.table, p.entry) == pre.entry(p.table, p.entry));
                assert(post.record(p.table).level == pre.record(p.table).level);
                assert(p.table != child);
                assert(post.record(p.table).space == pre.record(p.table).space);
            }
        }
    }
}

/// What a detach changes between two trees of the same tables: the parent's entry goes empty and the
/// child's record forgets its parent. Every level and space stays, and so does every other entry.
pub open spec fn detached(pre: TableTree, post: TableTree, parent: usize, entry: usize, child: usize) -> bool {
    &&& post.maps.dom() == pre.maps.dom()
    &&& post.roots.dom() == pre.roots.dom()
    &&& post.entry(parent, entry).is_empty()
    &&& forall|t: usize, i: usize| #![trigger post.entry(t, i)]
        pre.is_table(t) && i < 512 && !(t == parent && i == entry) ==> post.entry(t, i) == pre.entry(t, i)
    &&& forall|t: usize| #![trigger post.record(t)] pre.is_table(t) ==> {
        &&& post.record(t).level == pre.record(t).level
        &&& post.record(t).space == pre.record(t).space
    }
    &&& forall|t: usize| #![trigger post.record(t)] pre.is_table(t) && t != child ==> post.record(t).parent == pre.record(t).parent
    &&& post.record(child).parent is None
    &&& forall|t: usize| #![trigger post.space_records[t]]
        pre.is_root(t) ==> post.space_records[t].value().kind == pre.space_records[t].value().kind
}

/// A detach of a table page from the entry that names it keeps the links: the entry and the record that
/// named each other both go, and no other record named that entry, since an entry has one address.
pub proof fn lemma_links_detached(pre: TableTree, post: TableTree, parent: usize, entry: usize, child: usize)
    requires
        table_links_wf(pre),
        detached(pre, post, parent, entry, child),
        pre.is_page(child),
        pre.record(child).parent == Some(TableParent { table: parent, entry }),
        forall|c: usize| #[trigger] pre.maps.contains_key(c) ==> c + TABLE_NODE_PAGES * 4096 <= usize::MAX,
    ensures
        table_links_wf(post),
{
    assert forall|t: usize| #[trigger] post.is_table(t) == pre.is_table(t) by {
        assert(post.maps.contains_key(t) == pre.maps.contains_key(t));
        assert(post.roots.contains_key(t) == pre.roots.contains_key(t));
    }
    assert forall|t: usize| #[trigger] post.is_page(t) == pre.is_page(t) by {
        assert(post.maps.contains_key(t) == pre.maps.contains_key(t));
    }
    assert forall|t: usize| #[trigger] post.is_root(t) == pre.is_root(t) by {
        assert(post.roots.contains_key(t) == pre.roots.contains_key(t));
    }
    assert forall|t: usize, i: usize| #[trigger] post.child_slot(t, i) == pre.child_slot(t, i) by {
        if pre.is_table(t) {
            assert(post.record(t).level == pre.record(t).level);
        }
    }
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.names_child(u, i) implies {
        let c = (post.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        &&& post.is_page(c)
        &&& post.record(c).parent == Some(TableParent { table: u, entry: i })
    } by {
        assert(!(u == parent && i == entry));
        assert(post.entry(u, i) == pre.entry(u, i));
        assert(pre.names_child(u, i));
        let c = (pre.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        assert(pre.is_page(c));
        assert(pre.record(c).parent == Some(TableParent { table: u, entry: i }));
        assert(c != child);
        assert(post.record(c).parent == pre.record(c).parent);
    }
    assert forall|u: usize, i: usize| #![trigger post.entry(u, i)]
        post.child_slot(u, i) && post.entry(u, i).perm.present && post.entry(u, i).perm.ps implies post.record(u).level == 2 by {
        assert(!(u == parent && i == entry));
        assert(post.entry(u, i) == pre.entry(u, i));
        assert(pre.child_slot(u, i));
        assert(pre.record(u).level == 2);
        assert(post.record(u).level == pre.record(u).level);
    }
    assert(pre.maps.contains_key(child));
    assert(pre.entry(parent, entry).addr == table_addr(child));
    assert forall|c: usize| #![trigger post.maps.contains_key(c)] post.is_page(c) implies {
        let r = post.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& post.names_child(p.table, p.entry)
            &&& post.entry(p.table, p.entry).addr == table_addr(c)
            &&& post.record(p.table).level == r.level + 1
            &&& post.record(p.table).space == r.space
        }
        &&& r.space is Some ==> post.is_root(r.space->0)
    } by {
        assert(pre.is_page(c));
        assert(pre.maps.contains_key(c));
        let r = pre.record(c);
        assert(post.record(c).space == r.space);
        assert(post.record(c).level == r.level);
        if c != child {
            assert(post.record(c).parent == r.parent);
            if r.parent is Some {
                let p = r.parent->0;
                assert(pre.names_child(p.table, p.entry));
                assert(pre.entry(p.table, p.entry).addr == table_addr(c));
                assert(!(p.table == parent && p.entry == entry));
                assert(post.entry(p.table, p.entry) == pre.entry(p.table, p.entry));
                assert(post.record(p.table).level == pre.record(p.table).level);
                assert(post.record(p.table).space == pre.record(p.table).space);
                assert(post.child_slot(p.table, p.entry));
            }
        }
    }
}

/// A detach keeps the frame mappings: the entry it empties named a child, so was none, and an empty entry
/// is none.
pub proof fn lemma_frame_entries_detached(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize)
    requires
        detached(a, b, parent, entry, child),
        a.names_child(parent, entry),
    ensures
        same_frame_entries(a, b),
{
    assert forall|t: usize, e: usize| #[trigger] frame_slot(a, t, e) implies {
        &&& frame_slot(b, t, e)
        &&& b.record(t).level == a.record(t).level
        &&& b.entry(t, e) == a.entry(t, e)
    } by {
        assert(b.maps.dom() == a.maps.dom());
        assert(b.is_page(t));
        assert(a.is_table(t));
        assert(b.record(t).level == a.record(t).level);
        assert(!(t == parent && e == entry));
        assert(b.entry(t, e) == a.entry(t, e));
    }
    assert forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) implies frame_slot(a, t, e) by {
        assert(b.maps.dom() == a.maps.dom());
        assert(a.is_page(t));
        assert(a.is_table(t));
        assert(b.record(t).level == a.record(t).level);
        assert(!(t == parent && e == entry));
        assert(b.entry(t, e) == a.entry(t, e));
    }
}

/// Path p of space r passes through entry `entry` of table `parent`: its walk reads that entry to find
/// the next table.
pub open spec fn passes_through(tree: TableTree, r: usize, p: SpacePath, parent: usize, entry: usize) -> bool {
    &&& tree.is_root(r)
    &&& {
        ||| r == parent && p.l4 == entry
        ||| match step(tree, r, p.l4) {
            None => false,
            Some(t3) => {
                ||| t3 == parent && p.l3 == entry
                ||| match step(tree, t3, p.l3) {
                    None => false,
                    Some(t2) => t2 == parent && p.l2 == entry,
                }
            },
        }
    }
}

/// The walks through entry `entry` of `parent` find nothing, and every other walk finds what it did. Kept
/// opaque because it relates every walk of b to a's.
#[verifier::opaque]
pub open spec fn walks_detached(a: TableTree, b: TableTree, parent: usize, entry: usize) -> bool {
    forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p)
        == if passes_through(a, r, p, parent, entry) { None } else { walk(a, r, p) }
}

/// A detach ends the walks that read its entry and no other: a step reads only entries that name a child,
/// and the frame entries a walk ends at are not that entry.
pub proof fn lemma_walk_detached(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, r: usize, p: SpacePath)
    requires
        detached(a, b, parent, entry, child),
        a.names_child(parent, entry),
    ensures
        walk(b, r, p) == (if passes_through(a, r, p, parent, entry) { None } else { walk(a, r, p) }),
{
    assert forall|t: usize| #[trigger] b.is_table(t) == a.is_table(t) by {
        assert(b.maps.contains_key(t) == a.maps.contains_key(t));
        assert(b.roots.contains_key(t) == a.roots.contains_key(t));
    }
    assert forall|t: usize| #[trigger] b.is_root(t) == a.is_root(t) by {
        assert(b.roots.contains_key(t) == a.roots.contains_key(t));
    }
    assert forall|t: usize, i: usize| !(t == parent && i == entry) implies #[trigger] step(b, t, i) == step(a, t, i) by {
        if a.is_table(t) && i < 512 {
            assert(b.entry(t, i) == a.entry(t, i));
            assert(b.record(t).level == a.record(t).level);
        }
    }
    assert(step(b, parent, entry) is None);
    assert forall|t: usize, i: usize| true implies #[trigger] frame_entry(b, t, i) == frame_entry(a, t, i) by {
        if a.is_table(t) && i < 512 {
            assert(b.record(t).level == a.record(t).level);
            if !(t == parent && i == entry) {
                assert(b.entry(t, i) == a.entry(t, i));
            }
        }
    }
    assert forall|t: usize, i: usize| true implies #[trigger] large_entry(b, t, i) == large_entry(a, t, i) by {
        if a.is_table(t) && i < 512 {
            assert(b.record(t).level == a.record(t).level);
            if !(t == parent && i == entry) {
                assert(b.entry(t, i) == a.entry(t, i));
            }
        }
    }
    assert(large_entry(b, parent, entry) is None);
}

/// A walk through the entry naming table page t finds page g.
pub open spec fn cut_walk_finds(tree: TableTree, t: usize, g: usize) -> bool {
    let s = tree.record(t).space->0;
    let q = tree.record(t).parent->0;
    &&& tree.record(t).parent is Some
    &&& exists|p: SpacePath| #![trigger walk_finds(tree, s, p, g)]
        passes_through(tree, s, p, q.table, q.entry) && walk_finds(tree, s, p, g)
}

/// The entries of table t that name a child.
pub open spec fn child_entries(tree: TableTree, t: usize) -> Set<usize> {
    Set::<usize>::range(0, 512).filter(|e: usize| tree.names_child(t, e))
}

pub proof fn lemma_child_entries(tree: TableTree, t: usize, e: usize)
    ensures
        child_entries(tree, t).contains(e) <==> tree.names_child(t, e),
{
    broadcast use vstd::set::lemma_set_filter;
    vstd::set_lib::range_set_properties::<usize>(0, 512);
}

/// The child table entry e of table t names.
pub open spec fn child_at(tree: TableTree, t: usize, e: usize) -> usize {
    (tree.entry(t, e).addr - TABLE_NODE_PAGES * 4096) as usize
}

/// What t's cut leaves a core or an IOMMU holding that nothing will read again: t's own page, from a
/// paging-structure cache, and the pages the walks through the entry naming it find, from a TLB. The tables
/// below t keep their space, so their pages stay said until they are cut in turn.
pub open spec fn cut_pages(tree: TableTree, t: usize) -> Set<usize> {
    Set::<usize>::range(0, NUM_PAGES).filter(|g: usize| g == t / 4096 || cut_walk_finds(tree, t, g))
}

pub proof fn lemma_cut_pages(tree: TableTree, t: usize, g: usize)
    ensures
        cut_pages(tree, t).contains(g) <==> g < NUM_PAGES && (g == t / 4096 || cut_walk_finds(tree, t, g)),
{
    broadcast use vstd::set::lemma_set_filter;
    vstd::set_lib::range_set_properties::<usize>(0, NUM_PAGES);
}

/// An address whose page is below NUM_PAGES is below 2^33.
pub proof fn lemma_table_bound(t: usize)
    requires
        t / 4096 < NUM_PAGES,
    ensures
        t < 0x2_0000_0000,
{
    lemma_fundamental_div_mod(t as int, 4096);
}

/// A table page's table lies within memory: its address, page aligned and below 2^33 plus five pages,
/// has no bit outside MEM_MASK.
pub proof fn lemma_table_addr_valid(t: usize)
    requires
        t % 4096 == 0,
        t < 0x2_0000_0000,
    ensures
        t + TABLE_NODE_PAGES * 4096 < 0x1_0000_0000_0000,
        MEM_valid((t + TABLE_NODE_PAGES * 4096) as usize),
{
    assert(t % 4096 == 0 && t < 0x2_0000_0000 ==> ((t + 0x5000) as usize) & 0xffff_0000_0000_0fffusize == 0) by (bit_vector);
    assert((!MEM_MASK) as usize == 0xffff_0000_0000_0fffusize) by (compute_only);
}

/// An entry is empty, in constant time.
pub fn entry_is_empty(e: &PageEntry) -> (ret: bool)
    ensures
        ret == e.is_empty(),
{
    e.addr == 0 && !e.perm.present && !e.perm.ps && !e.perm.write && !e.perm.execute_disable && !e.perm.user
}

impl CapKernel {
    /// The refusals: an index that names no capability to a space, or none that may change it; a parent
    /// that is no live table of that space, or an entry of it that is taken or cannot hold a child; an
    /// untyped that does not cover the child; a child that is no live table page, is not one level below
    /// the parent, or has been linked or written.
    pub open spec fn can_link(&self, root: usize, slot: usize, parent: usize, entry: usize, from: usize, child: usize) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let n = self.tables.node_of(root, slot);
        &&& self.tables.has_slot(root, slot)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Space
        &&& self.payload_of(n).rights & right_bit(Right::Write) != 0
        &&& tree.is_table(parent)
        &&& tree.record(parent).space == Some(self.payload_of(n).base)
        &&& !self.blocks.pages@[(parent / 4096) as int].dead
        &&& tree.child_slot(parent, entry)
        &&& tree.entry(parent, entry).is_empty()
        &&& self.can_retype_under(root, from, child, 3)
        &&& tree.is_page(child)
        &&& !self.blocks.pages@[(child / 4096) as int].dead
        &&& tree.record(child).level + 1 == tree.record(parent).level
        &&& tree.record(child).space is None
        &&& tree.record(child).parent is None
        &&& !tree.record(child).written
    }

    /// What a link leaves: the capabilities, the list and the blocks as they were, and the tables linked.
    pub open spec fn link_done(pre: Self, post: Self, parent: usize, entry: usize, child: usize, s: usize) -> bool {
        let tree = tree_of(&post.table_pages, &post.spaces);
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& tree.entry(parent, entry) == child_entry(child)
        &&& tree.record(child).parent == Some(TableParent { table: parent, entry })
        &&& tree.record(child).space == Some(s)
        &&& tree.record(child).level == tree_of(&pre.table_pages, &pre.spaces).record(child).level
        &&& tree.record(parent).written
        &&& linked(tree_of(&pre.table_pages, &pre.spaces), tree, parent, entry, child, s)
    }

    /// The invariant after a link, given what the tables' own invariants say. The entry written was
    /// empty, so no mapping's entry changed.
    proof fn lemma_link_wf(pre: Self, post: Self, parent: usize, entry: usize, child: usize, s: usize)
        requires
            pre.wf(),
            linked(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), parent, entry, child, s),
            tree_of(&pre.table_pages, &pre.spaces).is_table(parent),
            tree_of(&pre.table_pages, &pre.spaces).record(parent).level >= 2,
            tree_of(&pre.table_pages, &pre.spaces).entry(parent, entry).is_empty(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.spaces.loaded == pre.spaces.loaded,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
        ensures
            post.wf(),
    {
        lemma_frame_entries_linked(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), parent, entry, child, s);
        Self::lemma_tables_changed_wf(pre, post);
    }

    /// The invariant after a step that changed only the tables, none of their frame mappings, given what
    /// the tables' own invariants say.
    proof fn lemma_tables_changed_wf(pre: Self, post: Self)
        requires
            pre.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.spaces.loaded == pre.spaces.loaded,
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
        ensures
            post.wf(),
    {
        Self::lemma_tlb_same(pre, post);
        assert forall|n: usize| n < NODE_SPACE && (#[trigger] post.list.nodes@[n as int]).live && post.list.nodes@[n as int].kind is Hidden
            implies post.tables.owner@.contains_key(n) || post.table_pages.maps@.contains_key(n) by {
            assert(pre.tables.owner@.contains_key(n) || pre.table_pages.maps@.contains_key(n));
            assert(post.table_pages.maps@.contains_key(n) == pre.table_pages.maps@.contains_key(n));
        }
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
        ) by {
            pre.lemma_mapping_node(n);
        }
        lemma_mappings_kept(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, &post.list, &post.tables, b, &post.blocks, post.holders@, pre.mappings@);
    }

    /// The table pages after a link: the child's record changed, a page parent's entry and record changed,
    /// and every page keeps its table's address, its level and, while not written, its empty entries.
    proof fn lemma_link_pages(pre: Self, post: Self, parent: usize, entry: usize, child: usize)
        requires
            pre.wf(),
            post.list == pre.list,
            post.blocks == pre.blocks,
            post.table_pages.spare == pre.table_pages.spare,
            pre.table_pages.maps@.contains_key(child),
            child != parent,
            !pre.table_pages.records@[child].value().written,
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            post.table_pages.records@.dom() == pre.table_pages.records@.dom(),
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent ==> post.table_pages.maps@[t] == pre.table_pages.maps@[t],
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent && t != child
                ==> post.table_pages.records@[t] == pre.table_pages.records@[t],
            pre.table_pages.maps@.contains_key(parent) ==> {
                &&& post.table_pages.maps@[parent].addr() == pre.table_pages.maps@[parent].addr()
                &&& post.table_pages.maps@[parent].is_init()
                &&& post.table_pages.maps@[parent].value().wf()
                &&& post.table_pages.records@[parent].addr() == pre.table_pages.records@[parent].addr()
                &&& post.table_pages.records@[parent].is_init()
                &&& post.table_pages.records@[parent].value().level == pre.table_pages.records@[parent].value().level
                &&& post.table_pages.records@[parent].value().parent == pre.table_pages.records@[parent].value().parent
                &&& post.table_pages.records@[parent].value().written
            },
            post.table_pages.records@[child].addr() == pre.table_pages.records@[child].addr(),
            post.table_pages.records@[child].is_init(),
            post.table_pages.records@[child].value().level == pre.table_pages.records@[child].value().level,
            !pre.blocks.pages@[(child / 4096) as int].dead,
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        let pa = &pre.table_pages;
        let pb = &post.table_pages;
        assert forall|t: usize| #[trigger] pb.maps@.contains_key(t) implies table_page_wf(&post.list, pb, &post.blocks, t) by {
            assert(pa.maps@.contains_key(t));
            assert(table_page_wf(&pre.list, pa, &pre.blocks, t));
            assert(pb.records@.contains_key(t));
            if t == parent {
                assert(table_record_wf(pb, t));
            } else if t == child {
                assert(pb.maps@[t] == pa.maps@[t]);
                assert forall|i: usize| i < 512 implies #[trigger] pb.maps@[t].value()[i].is_empty() by {
                    assert(pa.maps@[t].value()[i].is_empty());
                }
                assert(table_record_wf(pb, t));
            } else {
                assert(pb.maps@[t] == pa.maps@[t]);
                assert(pb.records@[t] == pa.records@[t]);
                assert forall|i: usize| i < 512 && !pb.records@[t].value().written implies #[trigger] pb.maps@[t].value()[i].is_empty() by {
                    assert(pa.maps@[t].value()[i].is_empty());
                }
                assert(table_record_wf(pb, t));
            }
        }
        assert forall|b: usize| b < NUM_PAGES && #[trigger] table_block(&post.blocks, b) implies pb.maps@.contains_key((b * 4096) as usize) by {
            assert(pa.maps@.contains_key((b * 4096) as usize));
        }
    }

    /// The spaces after a link into a root or a detach from one: an entry outside its kernel slots, now naming a
    /// table or empty, and its record's written flag changed, and the root keeps its address, its kind, its
    /// record and its kernel slots.
    proof fn lemma_link_spaces(pre: Self, post: Self, parent: usize, entry: usize)
        requires
            pre.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.spaces.loaded == pre.spaces.loaded,
            post.spaces.holders == pre.spaces.holders,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            post.spaces.bound == pre.spaces.bound,
            pre.spaces.roots@.contains_key(parent),
            !holds_kernel(pre.spaces.records@[parent].value().kind, entry),
            post.spaces.roots@[parent].value()[entry].is_empty()
                || (post.spaces.roots@[parent].value()[entry].perm.present && !post.spaces.roots@[parent].value()[entry].perm.ps),
            post.spaces.roots@ == pre.spaces.roots@.insert(parent, post.spaces.roots@[parent]),
            post.spaces.records@ == pre.spaces.records@.insert(parent, post.spaces.records@[parent]),
            post.spaces.roots@[parent].addr() == pre.spaces.roots@[parent].addr(),
            post.spaces.roots@[parent].is_init(),
            post.spaces.roots@[parent].value().wf(),
            forall|i: usize| i < 512 && i != entry ==> #[trigger] post.spaces.roots@[parent].value()[i] == pre.spaces.roots@[parent].value()[i],
            post.spaces.records@[parent].addr() == pre.spaces.records@[parent].addr(),
            post.spaces.records@[parent].is_init(),
            post.spaces.records@[parent].value().kind == pre.spaces.records@[parent].value().kind,
            post.spaces.records@[parent].value().root == pre.spaces.records@[parent].value().root,
            post.spaces.records@[parent].value().table.level == pre.spaces.records@[parent].value().table.level,
            post.spaces.records@[parent].value().table.space == pre.spaces.records@[parent].value().table.space,
            post.spaces.records@[parent].value().table.parent == pre.spaces.records@[parent].value().table.parent,
            post.spaces.records@[parent].value().table.written,
        ensures
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
    {
        let sa = &pre.spaces;
        let sb = &post.spaces;
        assert forall|s: usize| #[trigger] sb.roots@.contains_key(s) implies space_wf(&post.list, sb, &post.blocks, s) by {
            assert(sa.roots@.contains_key(s));
            assert(space_wf(&pre.list, sa, &pre.blocks, s));
            if s == parent {
                assert forall|i: usize| i < KERNEL_MEM_END_L4INDEX && i != entry implies #[trigger] sb.roots@[s].value()[i] == sa.roots@[s].value()[i] by {}
                assert(kernel_slots_wf(sb, s));
                assert(root_record_wf(sb, s));
            } else {
                assert(sb.roots@[s] == sa.roots@[s]);
                assert(sb.records@[s] == sa.records@[s]);
                assert(kernel_slots_wf(sb, s));
                assert(root_record_wf(sb, s));
            }
        }
        assert forall|b: usize| b < NUM_PAGES && #[trigger] space_block(&post.blocks, b) implies sb.roots@.contains_key((b * 4096) as usize) by {
            assert(sa.roots@.contains_key((b * 4096) as usize));
        }
    }

    /// Reads the entry of a table, which the caller has found to be a root or a table page.
    pub fn table_entry(&self, t: usize, is_root: bool, i: usize) -> (ret: PageEntry)
        requires
            self.wf(),
            i < 512,
            is_root ==> self.spaces.roots@.contains_key(t),
            !is_root ==> self.table_pages.maps@.contains_key(t),
            is_root ==> !self.table_pages.maps@.contains_key(t),
        ensures
            ret =~= tree_of(&self.table_pages, &self.spaces).entry(t, i),
    {
        if is_root {
            let tracked map = self.spaces.roots.borrow().tracked_borrow(t);
            let record = PPtr::<SpaceRecord>::from_usize(t + SPACE_RECORD_PAGE * 4096).borrow(Tracked(self.spaces.records.borrow().tracked_borrow(t)));
            PPtr::<PageMap>::from_usize(record.root).borrow(Tracked(map)).get(i)
        } else {
            let tracked map = self.table_pages.maps.borrow().tracked_borrow(t);
            PPtr::<PageMap>::from_usize(t + TABLE_NODE_PAGES * 4096).borrow(Tracked(map)).get(i)
        }
    }

    /// Reads a table's record.
    /// Whether entry i of the table at t is a kernel slot.
    pub fn is_kernel_slot(&self, t: usize, is_root: bool, i: usize) -> (ret: bool)
        requires
            self.wf(),
            is_root ==> self.spaces.roots@.contains_key(t),
            !is_root ==> !self.spaces.roots@.contains_key(t),
        ensures
            ret == (is_root && holds_kernel(self.spaces.records@[t].value().kind, i)),
    {
        if !is_root || i >= KERNEL_MEM_END_L4INDEX {
            return false;
        }
        match self.space_kind(t) {
            SpaceKind::Process => true,
            SpaceKind::Io => false,
        }
    }

    /// Reads the kind of the space at s.
    pub fn space_kind(&self, s: usize) -> (ret: SpaceKind)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
        ensures
            ret == self.spaces.records@[s].value().kind,
    {
        proof {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        }
        PPtr::<SpaceRecord>::from_usize(s + SPACE_RECORD_PAGE * 4096).borrow(Tracked(self.spaces.records.borrow().tracked_borrow(s))).kind
    }

    /// Reads a table's record, which the caller has found to be a root's or a table page's.
    pub fn table_record(&self, t: usize, is_root: bool) -> (ret: TableRecord)
        requires
            self.wf(),
            is_root ==> self.spaces.roots@.contains_key(t),
            !is_root ==> self.table_pages.maps@.contains_key(t),
            is_root ==> !self.table_pages.maps@.contains_key(t),
        ensures
            ret == tree_of(&self.table_pages, &self.spaces).record(t),
    {
        if is_root {
            PPtr::<SpaceRecord>::from_usize(t + SPACE_RECORD_PAGE * 4096).borrow(Tracked(self.spaces.records.borrow().tracked_borrow(t))).table
        } else {
            *PPtr::<TableRecord>::from_usize(t + TABLE_RECORD_PAGE * 4096).borrow(Tracked(self.table_pages.records.borrow().tracked_borrow(t)))
        }
    }

    /// Writes the child's record: it is linked into `entry` of `parent` in space `s`.
    fn link_child(&mut self, parent: usize, entry: usize, child: usize, s: usize)
        requires
            old(self).table_pages.maps@.contains_key(child),
            old(self).table_pages.records@.contains_key(child),
            old(self).table_pages.records@[child].addr() == child + TABLE_RECORD_PAGE * 4096,
            old(self).table_pages.records@[child].is_init(),
            child / 4096 < NUM_PAGES,
        ensures
            final(self).table_pages.maps == old(self).table_pages.maps,
            final(self).table_pages.spare == old(self).table_pages.spare,
            final(self).spaces == old(self).spaces,
            final(self).mappings == old(self).mappings,
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).cores == old(self).cores,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).tlb == old(self).tlb,
            final(self).iommus == old(self).iommus,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).table_pages.records@ == old(self).table_pages.records@.insert(child, final(self).table_pages.records@[child]),
            final(self).table_pages.records@[child].addr() == old(self).table_pages.records@[child].addr(),
            final(self).table_pages.records@[child].is_init(),
            final(self).table_pages.records@[child].value() == (TableRecord {
                level: old(self).table_pages.records@[child].value().level,
                space: Some(s),
                parent: Some(TableParent { table: parent, entry }),
                written: false,
            }),
    {
        proof {
            lemma_table_bound(child);
        }
        let ptr = PPtr::<TableRecord>::from_usize(child + TABLE_RECORD_PAGE * 4096);
        let tracked mut record = self.table_pages.records.borrow_mut().tracked_remove(child);
        let level = ptr.borrow(Tracked(&record)).level;
        ptr.write(Tracked(&mut record), TableRecord { level, space: Some(s), parent: Some(TableParent { table: parent, entry }), written: false });
        proof {
            self.table_pages.records.borrow_mut().tracked_insert(child, record);
            assert(self.table_pages.records@ =~= old(self).table_pages.records@.insert(child, self.table_pages.records@[child]));
        }
    }

    /// Links `child` into `entry` of the root of space `parent`, which the caller has checked can take it.
    fn link_root(&mut self, parent: usize, entry: usize, child: usize)
        requires
            old(self).wf(),
            old(self).spaces.roots@.contains_key(parent),
            !old(self).table_pages.maps@.contains_key(parent),
            old(self).table_pages.maps@.contains_key(child),
            !old(self).blocks.pages@[(child / 4096) as int].dead,
            tree_of(&old(self).table_pages, &old(self).spaces).child_slot(parent, entry),
            tree_of(&old(self).table_pages, &old(self).spaces).entry(parent, entry).is_empty(),
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).parent is None,
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).space is None,
            !tree_of(&old(self).table_pages, &old(self).spaces).record(child).written,
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).level + 1
                == tree_of(&old(self).table_pages, &old(self).spaces).record(parent).level,
        ensures
            final(self).wf(),
            final(self).spaces.loaded == old(self).spaces.loaded,
            Self::link_done(*old(self), *final(self), parent, entry, child, parent),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, parent));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
            lemma_table_bound(parent);
            lemma_table_bound(child);
            lemma_table_page_aligned(child);
            lemma_table_addr_valid(child);
        }
        let value = PageEntry {
            addr: child + TABLE_NODE_PAGES * 4096,
            perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true },
        };
        let tracked mut map = self.spaces.roots.borrow_mut().tracked_remove(parent);
        let tracked mut record = self.spaces.records.borrow_mut().tracked_remove(parent);
        let ptr = PPtr::<SpaceRecord>::from_usize(parent + SPACE_RECORD_PAGE * 4096);
        let space_record = *ptr.borrow(Tracked(&record));
        page_map_set(space_record.root, Tracked(&mut map), entry, value);
        ptr.write(
            Tracked(&mut record),
            SpaceRecord {
                kind: space_record.kind,
                root: space_record.root,
                table: TableRecord {
                    level: space_record.table.level,
                    space: space_record.table.space,
                    parent: space_record.table.parent,
                    written: true,
                },
            },
        );
        proof {
            self.spaces.roots.borrow_mut().tracked_insert(parent, map);
            self.spaces.records.borrow_mut().tracked_insert(parent, record);
            assert(self.spaces.roots@ =~= pre.spaces.roots@.insert(parent, self.spaces.roots@[parent]));
            assert(self.spaces.records@ =~= pre.spaces.records@.insert(parent, self.spaces.records@[parent]));
        }
        let ghost mid = *self;
        self.link_child(parent, entry, child, parent);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            assert(post.spaces.roots@ == pre.spaces.roots@.insert(parent, post.spaces.roots@[parent]));
            assert(post.spaces.records@ == pre.spaces.records@.insert(parent, post.spaces.records@[parent]));
            assert(post.spaces.roots@[parent].value()[entry] == value);
            assert forall|i: usize| i < 512 && i != entry implies #[trigger] post.spaces.roots@[parent].value()[i] == pre.spaces.roots@[parent].value()[i] by {}
            Self::lemma_link_spaces(pre, post, parent, entry);
            assert(post.table_pages.maps@.dom() == pre.table_pages.maps@.dom());
            assert(post.table_pages.records@.dom() == pre.table_pages.records@.dom());
            assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent && t != child
                implies post.table_pages.records@[t] == pre.table_pages.records@[t] by {}
            Self::lemma_link_pages(pre, post, parent, entry, child);
            Self::lemma_link_tree(pre, post, parent, entry, child, parent);
            lemma_links_linked(a, b, parent, entry, child, parent);
            Self::lemma_link_wf(pre, post, parent, entry, child, parent);
        }
    }

    /// Links `child` into `entry` of the table page `parent` in space `s`, which the caller has checked can
    /// take it.
    fn link_page(&mut self, parent: usize, entry: usize, child: usize, s: usize)
        requires
            old(self).wf(),
            old(self).table_pages.maps@.contains_key(parent),
            old(self).table_pages.maps@.contains_key(child),
            old(self).spaces.roots@.contains_key(s),
            !old(self).blocks.pages@[(child / 4096) as int].dead,
            tree_of(&old(self).table_pages, &old(self).spaces).child_slot(parent, entry),
            tree_of(&old(self).table_pages, &old(self).spaces).entry(parent, entry).is_empty(),
            tree_of(&old(self).table_pages, &old(self).spaces).record(parent).space == Some(s),
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).parent is None,
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).space is None,
            !tree_of(&old(self).table_pages, &old(self).spaces).record(child).written,
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).level + 1
                == tree_of(&old(self).table_pages, &old(self).spaces).record(parent).level,
        ensures
            final(self).wf(),
            final(self).spaces.loaded == old(self).spaces.loaded,
            Self::link_done(*old(self), *final(self), parent, entry, child, s),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, parent));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
            lemma_table_bound(parent);
            lemma_table_bound(child);
            lemma_table_page_aligned(child);
            lemma_table_addr_valid(child);
        }
        let value = PageEntry {
            addr: child + TABLE_NODE_PAGES * 4096,
            perm: PageEntryPerm { present: true, ps: false, write: true, execute_disable: false, user: true },
        };
        let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(parent);
        let tracked mut record = self.table_pages.records.borrow_mut().tracked_remove(parent);
        let ptr = PPtr::<TableRecord>::from_usize(parent + TABLE_RECORD_PAGE * 4096);
        let parent_record = *ptr.borrow(Tracked(&record));
        page_map_set(parent + TABLE_NODE_PAGES * 4096, Tracked(&mut map), entry, value);
        ptr.write(
            Tracked(&mut record),
            TableRecord { level: parent_record.level, space: parent_record.space, parent: parent_record.parent, written: true },
        );
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(parent, map);
            self.table_pages.records.borrow_mut().tracked_insert(parent, record);
            assert(self.table_pages.maps@ =~= pre.table_pages.maps@.insert(parent, self.table_pages.maps@[parent]));
            assert(self.table_pages.records@ =~= pre.table_pages.records@.insert(parent, self.table_pages.records@[parent]));
        }
        self.link_child(parent, entry, child, s);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            assert(post.table_pages.maps@ == pre.table_pages.maps@.insert(parent, post.table_pages.maps@[parent]));
            assert(post.table_pages.maps@[parent].value()[entry] == value);
            assert forall|i: usize| i < 512 && i != entry implies #[trigger] post.table_pages.maps@[parent].value()[i] == pre.table_pages.maps@[parent].value()[i] by {}
            assert(post.table_pages.maps@.dom() == pre.table_pages.maps@.dom());
            assert(post.table_pages.records@.dom() == pre.table_pages.records@.dom());
            assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent
                implies post.table_pages.maps@[t] == pre.table_pages.maps@[t] by {}
            assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent && t != child
                implies post.table_pages.records@[t] == pre.table_pages.records@[t] by {}
            Self::lemma_link_pages(pre, post, parent, entry, child);
            Self::lemma_link_tree(pre, post, parent, entry, child, s);
            lemma_links_linked(a, b, parent, entry, child, s);
            Self::lemma_link_wf(pre, post, parent, entry, child, s);
        }
    }

    /// The trees before and after a link are linked, given what the writes did to the permissions.
    proof fn lemma_link_tree(pre: Self, post: Self, parent: usize, entry: usize, child: usize, s: usize)
        requires
            pre.wf(),
            pre.table_pages.maps@.contains_key(child),
            child != parent,
            tree_of(&pre.table_pages, &pre.spaces).is_table(parent),
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            post.spaces.roots@.dom() == pre.spaces.roots@.dom(),
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent ==> post.table_pages.maps@[t] == pre.table_pages.maps@[t],
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent && t != child
                ==> post.table_pages.records@[t] == pre.table_pages.records@[t],
            forall|t: usize| #[trigger] pre.spaces.roots@.contains_key(t) && t != parent ==> {
                &&& post.spaces.roots@[t] == pre.spaces.roots@[t]
                &&& post.spaces.records@[t] == pre.spaces.records@[t]
            },
            pre.table_pages.maps@.contains_key(parent) ==> {
                &&& post.table_pages.maps@[parent].value()[entry] == child_entry(child)
                &&& forall|i: usize| i < 512 && i != entry ==> #[trigger] post.table_pages.maps@[parent].value()[i] == pre.table_pages.maps@[parent].value()[i]
                &&& post.table_pages.records@[parent].value().level == pre.table_pages.records@[parent].value().level
                &&& post.table_pages.records@[parent].value().space == pre.table_pages.records@[parent].value().space
                &&& post.table_pages.records@[parent].value().parent == pre.table_pages.records@[parent].value().parent
                &&& post.spaces == pre.spaces
            },
            !pre.table_pages.maps@.contains_key(parent) ==> {
                &&& post.spaces.records@[parent].value().kind == pre.spaces.records@[parent].value().kind
                &&& post.spaces.roots@[parent].value()[entry] == child_entry(child)
                &&& forall|i: usize| i < 512 && i != entry ==> #[trigger] post.spaces.roots@[parent].value()[i] == pre.spaces.roots@[parent].value()[i]
                &&& post.spaces.records@[parent].value().table.level == pre.spaces.records@[parent].value().table.level
                &&& post.spaces.records@[parent].value().table.space == pre.spaces.records@[parent].value().table.space
                &&& post.spaces.records@[parent].value().table.parent == pre.spaces.records@[parent].value().table.parent
            },
            post.table_pages.records@[child].value().level == pre.table_pages.records@[child].value().level,
            post.table_pages.records@[child].value().space == Some(s),
            post.table_pages.records@[child].value().parent == Some(TableParent { table: parent, entry }),
        ensures
            linked(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), parent, entry, child, s),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert forall|t: usize| #[trigger] b.is_page(t) == a.is_page(t) by {
            assert(post.table_pages.maps@.contains_key(t) == pre.table_pages.maps@.contains_key(t));
        }
        assert forall|t: usize| #[trigger] b.is_root(t) == a.is_root(t) by {
            assert(post.spaces.roots@.contains_key(t) == pre.spaces.roots@.contains_key(t));
        }
        assert(b.entry(parent, entry) == child_entry(child));
        assert forall|t: usize, i: usize| #![trigger b.entry(t, i)]
            a.is_table(t) && i < 512 && !(t == parent && i == entry) implies b.entry(t, i) == a.entry(t, i) by {
            if a.is_page(t) {
                if t == parent {
                    assert(post.table_pages.maps@[parent].value()[i] == pre.table_pages.maps@[parent].value()[i]);
                } else {
                    assert(post.table_pages.maps@[t] == pre.table_pages.maps@[t]);
                }
            } else {
                if t == parent {
                    assert(post.spaces.roots@[parent].value()[i] == pre.spaces.roots@[parent].value()[i]);
                } else {
                    assert(post.spaces.roots@[t] == pre.spaces.roots@[t]);
                }
            }
        }
        assert forall|t: usize| #![trigger b.record(t)] a.is_table(t) implies b.record(t).level == a.record(t).level by {
            if a.is_page(t) {
                if t != parent && t != child {
                    assert(post.table_pages.records@[t] == pre.table_pages.records@[t]);
                }
            } else {
                if t != parent {
                    assert(post.spaces.records@[t] == pre.spaces.records@[t]);
                }
            }
        }
        assert forall|t: usize| #![trigger b.record(t)] a.is_table(t) && t != child implies {
            &&& b.record(t).space == a.record(t).space
            &&& b.record(t).parent == a.record(t).parent
        } by {
            if a.is_page(t) {
                if t != parent {
                    assert(post.table_pages.records@[t] == pre.table_pages.records@[t]);
                }
            } else {
                if t != parent {
                    assert(post.spaces.records@[t] == pre.spaces.records@[t]);
                }
            }
        }
    }

    /// A link leaves every space's mapping as it was: a child not written has no entry.
    proof fn lemma_link_mappings(pre: Self, post: Self, root: usize, slot: usize, parent: usize, entry: usize, from: usize, child: usize, s: usize)
        requires
            pre.wf(),
            pre.can_link(root, slot, parent, entry, from, child),
            Self::link_done(pre, post, parent, entry, child, s),
        ensures
            forall|r: usize| #[trigger] space_mapping(tree_of(&post.table_pages, &post.spaces), r)
                == space_mapping(tree_of(&pre.table_pages, &pre.spaces), r),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(a.is_page(child));
        assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
        assert(table_record_wf(&pre.table_pages, child));
        assert forall|i: usize| i < 512 implies #[trigger] a.entry(child, i).is_empty() by {
            assert(pre.table_pages.maps@[child].value()[i].is_empty());
        }
        assert(child != parent);
        lemma_table_bound(child);
        assert forall|r: usize| #[trigger] space_mapping(b, r) == space_mapping(a, r) by {
            lemma_mapping_linked(a, b, parent, entry, child, s, r);
        }
    }

    /// Links the unlinked table page `child` into `entry` of the table `parent`, in the space named by
    /// the capability at index `slot` of the table at `root`, on the authority of the untyped at index
    /// `from` over the child's block. All of these come from user space, and a refusal changes nothing.
    /// The entry and both records change in one step.
    pub fn link(&mut self, root: usize, slot: usize, parent: usize, entry: usize, from: usize, child: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret == old(self).can_link(root, slot, parent, entry, from, child),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            ret ==> {
                let tree = tree_of(&final(self).table_pages, &final(self).spaces);
                let s = old(self).payload_of(old(self).tables.node_of(root, slot)).base;
                &&& tree.entry(parent, entry) == child_entry(child)
                &&& tree.record(child).parent == Some(TableParent { table: parent, entry })
                &&& tree.record(child).space == Some(s)
                &&& tree.record(child).level == tree_of(&old(self).table_pages, &old(self).spaces).record(child).level
                &&& tree.record(parent).written
                &&& forall|r: usize| #[trigger] space_mapping(tree, r) == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r)
            },
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (n, payload) = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found,
            None => { return false; },
        };
        proof {
            pre.lemma_slot(root, slot);
            assert(payload == pre.payload_of(n));
            assert(right_bit(Right::Write) == 2);
        }
        let node = self.list.get(n);
        let is_space = match payload.kind {
            CapKind::Space => true,
            _ => false,
        };
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !node.live || !kind_ok || !is_space || payload.rights & 2 == 0 {
            return false;
        }
        proof {
            assert(pre.is_cap(n));
            pre.lemma_space_cap(n);
        }
        if parent % 32768 != 0 || parent / 4096 >= NUM_PAGES || child % 32768 != 0 || child / 4096 >= NUM_PAGES || entry >= 512 {
            proof {
                if tree.is_page(parent) {
                    assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, parent));
                }
                if tree.is_root(parent) {
                    assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, parent));
                }
                if tree.is_page(child) {
                    assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
                }
            }
            return false;
        }
        let is_root = parent == payload.base;
        if !is_root {
            let block = *self.blocks.pages.get(parent / 4096);
            let is_page = match (block.kind, block.object) {
                (PageKind::Base, ObjectType::TablePage) => true,
                _ => false,
            };
            if !is_page {
                proof {
                    if tree.is_page(parent) {
                        assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, parent));
                    }
                    if tree.is_root(parent) {
                        assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, parent));
                    }
                }
                return false;
            }
            proof {
                lemma_table_page_base(parent, parent / 4096);
                assert(table_block(&pre.blocks, parent / 4096));
                assert(tree.is_page(parent));
                if tree.is_root(parent) {
                    assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, parent));
                }
            }
        } else {
            proof {
                assert(tree.is_root(parent));
                assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, parent));
                if tree.is_page(parent) {
                    assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, parent));
                }
            }
        }
        if self.blocks.pages.get(parent / 4096).dead {
            return false;
        }
        let child_block = *self.blocks.pages.get(child / 4096);
        let child_ok = match (child_block.kind, child_block.object) {
            (PageKind::Base, ObjectType::TablePage) => true,
            _ => false,
        };
        if !child_ok || child_block.dead {
            proof {
                if tree.is_page(child) {
                    assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
                }
            }
            return false;
        }
        proof {
            lemma_table_page_base(child, child / 4096);
            assert(table_block(&pre.blocks, child / 4096));
            assert(tree.is_page(child));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
        }
        match self.retype_parent(root, from, child, 3) {
            Some(_) => {},
            None => { return false; },
        }
        let parent_record = self.table_record(parent, is_root);
        let child_record = self.table_record(child, false);
        let parent_space_ok = match parent_record.space {
            Some(s) => s == payload.base,
            None => false,
        };
        let child_free = match (child_record.space, child_record.parent) {
            (None, None) => !child_record.written,
            _ => false,
        };
        if !parent_space_ok || !child_free || parent_record.level < 2 || child_record.level + 1 != parent_record.level {
            return false;
        }
        if self.is_kernel_slot(parent, is_root, entry) {
            return false;
        }
        proof {
            assert(tree.child_slot(parent, entry));
        }
        let current = self.table_entry(parent, is_root, entry);
        if !entry_is_empty(&current) {
            return false;
        }
        proof {
            assert(pre.can_link(root, slot, parent, entry, from, child));
        }
        proof {
            assert(pre.can_link(root, slot, parent, entry, from, child));
        }
        if is_root {
            self.link_root(parent, entry, child);
        } else {
            self.link_page(parent, entry, child, payload.base);
        }
        proof {
            assert(self.view() == pre.view());
            Self::lemma_link_mappings(pre, *self, root, slot, parent, entry, from, child, payload.base);
        }
        true
    }

    /// What cutting table page t does to the tables: with no parent, nothing changed; with one, that entry
    /// empty and t's record with no parent, and the walks through the entry gone, so what is left of the
    /// abstract mapping is what the subtree below it did not map.
    pub open spec fn tree_cut(pre: Self, post: Self, t: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let p = a.record(t).parent;
        &&& p is None ==> post.table_pages == pre.table_pages && post.spaces == pre.spaces
        &&& p is Some ==> detached(a, b, p->0.table, p->0.entry, t)
        &&& p is Some ==> walks_detached(a, b, p->0.table, p->0.entry)
    }

    /// A cut, and nothing but the tables changed by it.
    pub open spec fn tables_cut(pre: Self, post: Self, t: usize) -> bool {
        &&& Self::tree_cut(pre, post, t)
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.cores == pre.cores
        &&& post.table_pages.spare == pre.table_pages.spare
        &&& post.spaces.loaded == pre.spaces.loaded
        &&& post.spaces.holders == pre.spaces.holders
        &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
        &&& post.spaces.bound == pre.spaces.bound
    }

    /// A detach alone: only the tables changed.
    pub open spec fn detach_done(pre: Self, post: Self, t: usize) -> bool {
        &&& Self::tables_cut(pre, post, t)
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.iommus == pre.iommus
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& tree_of(&pre.table_pages, &pre.spaces).record(t).parent is None ==> post == pre
    }

    /// Table page t's cut is recorded: the epoch rose past every acknowledgement and is written for t's
    /// page, so that page does not count as acknowledged, and what the cut leaves is in the TLB of every
    /// core that loaded the space and, for an IO space, of every IOMMU, where only a flush takes it out.
    /// What the walks lost keeps its mapping nodes, so it stays mapped, and its words are written when
    /// those unlink.
    pub open spec fn cut_stale_noted(pre: Self, post: Self, t: usize) -> bool {
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let pages = cut_pages(tree, t);
        let space = tree.record(t).space;
        &&& post.flush_epoch == pre.flush_epoch + 1
        &&& post.stale_epoch.written(post.flush_epoch, t / 4096)
        &&& !post.acknowledged(t / 4096)
        &&& forall|d: int, g: usize| #![trigger post.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g })]
            0 <= d < NUM_CPUS && space is Some && pre.loaded(d, space->Some_0) && pages.contains(g)
            ==> post.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g })
        &&& forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] pre.tlb@[d].contains(e) ==> post.tlb@[d].contains(e)
        &&& forall|i: int, g: usize| #![trigger post.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g })]
            0 <= i < NUM_IOMMUS && space is Some && pre.spaces.records@[space->Some_0].value().kind is Io && pages.contains(g)
            ==> post.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g })
        &&& forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] pre.iommus.tlb@[i].contains(e) ==> post.iommus.tlb@[i].contains(e)
        &&& post.iommus.acked == pre.iommus.acked
        &&& post.mapped == pre.mapped
        &&& forall|a: int, g: usize| a < post.flush_epoch && g < NUM_PAGES && pre.stale_epoch.above(a, g)
            ==> #[trigger] post.stale_epoch.above(a, g)
    }

    /// A detach with its record, and nothing else changed by it.
    pub open spec fn detach_recorded(pre: Self, post: Self, t: usize) -> bool {
        &&& Self::tables_cut(pre, post, t)
        &&& Self::cut_recorded(pre, post, t)
    }

    /// The tables as tree_cut says and the record as cut_stale_noted says. A page the walks lost is mapped
    /// still, and what a core could hold before it can hold after.
    pub open spec fn cut_recorded(pre: Self, post: Self, t: usize) -> bool {
        &&& Self::tree_cut(pre, post, t)
        &&& Self::cut_stale_noted(pre, post, t)
        &&& forall|g: usize| #[trigger] cut_walk_finds(tree_of(&pre.table_pages, &pre.spaces), t, g)
            ==> post.mapped@.contains(g) && g < NUM_PAGES
        &&& forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] pre.core_may_hold(c, e) ==> post.core_may_hold(c, e)
    }

    /// A page a frame mapping maps is mapped.
    proof fn lemma_slot_mapped(&self, t: usize, e: usize, g: usize)
        requires
            self.wf(),
            frame_slot(tree_of(&self.table_pages, &self.spaces), t, e),
            tree_of(&self.table_pages, &self.spaces).entry(t, e).addr / 4096 <= g,
            g < tree_of(&self.table_pages, &self.spaces).entry(t, e).addr / 4096
                + entry_pages(if tree_of(&self.table_pages, &self.spaces).entry(t, e).perm.ps { 2usize } else { 1usize }),
        ensures
            self.mapped@.contains(g),
            g < NUM_PAGES,
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let n = mapping_node(t, e);
        assert(frame_slot(tree, t, e));
        assert(self.mappings@.contains_key(n));
        let m = self.mappings@[n];
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(m.frame + entry_pages(tree.record(t).level) <= NUM_PAGES);
        lemma_div_by_multiple(m.frame as int, 4096);
        lemma_map_pages(m.frame, m.large);
        assert(record_pages(m).contains(g));
        assert(page_named(self.mappings@, g));
    }

    /// A page a walk finds is mapped: the walk ended at a frame mapping of a table page.
    pub proof fn lemma_walk_mapped(&self, r: usize, p: SpacePath, g: usize)
        requires
            self.wf(),
            walk_finds(tree_of(&self.table_pages, &self.spaces), r, p, g),
        ensures
            self.mapped@.contains(g),
            g < NUM_PAGES,
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let t3 = step(tree, r, p.l4)->0;
        let t2 = step(tree, t3, p.l3)->0;
        assert(tree.names_child(t3, p.l3));
        assert(tree.is_page(t2));
        if step(tree, t2, p.l2) is None {
            assert(frame_slot(tree, t2, p.l2));
            self.lemma_slot_mapped(t2, p.l2, g);
        } else {
            let t1 = step(tree, t2, p.l2)->0;
            assert(tree.names_child(t2, p.l2));
            assert(tree.is_page(t1));
            assert(frame_slot(tree, t1, p.l1));
            self.lemma_slot_mapped(t1, p.l1, g);
        }
    }

    /// A walk reads only tables of its own space, so a table entry it passes through is one of r's.
    proof fn lemma_passes_in_space(&self, r: usize, p: SpacePath, parent: usize, entry: usize)
        requires
            self.wf(),
            passes_through(tree_of(&self.table_pages, &self.spaces), r, p, parent, entry),
        ensures
            tree_of(&self.table_pages, &self.spaces).record(parent).space == Some(r),
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(self.spaces.roots@.contains_key(r));
        assert(space_wf(&self.list, &self.spaces, &self.blocks, r));
        if self.table_pages.maps@.contains_key(r) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, r));
        }
        assert(tree.record(r).space == Some(r));
        if !(r == parent && p.l4 == entry) {
            let t3 = step(tree, r, p.l4)->0;
            assert(tree.names_child(r, p.l4));
            assert(tree.maps.contains_key(t3));
            assert(tree.record(t3).space == Some(r));
            if !(t3 == parent && p.l3 == entry) {
                let t2 = step(tree, t3, p.l3)->0;
                assert(tree.names_child(t3, p.l3));
                assert(tree.maps.contains_key(t2));
            }
        }
    }

    /// What a cut's walks lost is mapped still.
    proof fn lemma_cut_walks_mapped(&self, t: usize, g: usize)
        requires
            self.wf(),
            cut_walk_finds(tree_of(&self.table_pages, &self.spaces), t, g),
        ensures
            self.mapped@.contains(g),
            g < NUM_PAGES,
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let s = tree.record(t).space->0;
        let q = tree.record(t).parent->0;
        let p = choose|p: SpacePath| #![trigger walk_finds(tree, s, p, g)]
            passes_through(tree, s, p, q.table, q.entry) && walk_finds(tree, s, p, g);
        self.lemma_walk_mapped(s, p, g);
    }

    /// Records table page t's cut, while its entry still stands: the epoch is bumped first, so no core or
    /// IOMMU has acknowledged it however recently it flushed.
    fn note_cut_stale(&mut self, t: usize)
        requires
            old(self).wf(),
            old(self).table_pages.maps@.contains_key(t),
            old(self).flush_epoch < usize::MAX,
        ensures
            final(self).wf(),
            Self::cut_stale_noted(*old(self), *final(self), t),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).mappings == old(self).mappings,
            final(self).table_pages == old(self).table_pages,
            final(self).spaces == old(self).spaces,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).cores == old(self).cores,
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        let ghost pages = cut_pages(tree, t);
        let ghost space = tree.record(t).space;
        proof {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
        }
        self.flush_epoch = self.flush_epoch + 1;
        let epoch = self.flush_epoch;
        self.stale_epoch.record_run(t / 4096, 1, epoch);
        self.tlb = Ghost(Seq::new(NUM_CPUS as nat, |d: int|
            if space is Some && pre.loaded(d, space->Some_0) {
                pre.tlb@[d].union(stale_entries(space->Some_0, pages))
            } else {
                pre.tlb@[d]
            }));
        self.iommus.tlb = Ghost(Seq::new(NUM_IOMMUS as nat, |i: int|
            if space is Some && pre.spaces.records@[space->Some_0].value().kind is Io {
                pre.iommus.tlb@[i].union(stale_entries(space->Some_0, pages))
            } else {
                pre.iommus.tlb@[i]
            }));
        proof {
            if space is Some {
                lemma_stale_entries(space->Some_0, pages);
            }
            assert(self.stale_epoch.written(epoch, t / 4096));
            assert(self.tlb@.len() == NUM_CPUS);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert(pre.acked(0) <= pre.flush_epoch);
            assert(self.acked(0) == pre.acked(0));
            assert(!self.acknowledged(t / 4096));
            assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(e) implies self.loaded(d, e.space) by {
                assert(pre.loaded(d, e.space));
            }
            assert forall|d: int, e: TlbEntry|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(e) && !self.mapped@.contains(e.page)
                implies e.page < NUM_PAGES && self.stale_epoch.above(self.acked(d), e.page) by {
                assert(pre.acked(d) <= pre.flush_epoch);
                assert(self.acked(d) == pre.acked(d));
                if pre.tlb@[d].contains(e) {
                    assert(!pre.mapped@.contains(e.page));
                    assert(pre.stale_epoch.above(pre.acked(d), e.page));
                    assert(pre.acked(d) < epoch);
                } else {
                    lemma_cut_pages(tree, t, e.page);
                    if e.page != t / 4096 {
                        pre.lemma_cut_walks_mapped(t, e.page);
                    }
                }
            }
            assert(self.iommus.tlb@.len() == NUM_IOMMUS);
            assert forall|i: int| 0 <= i < NUM_IOMMUS implies #[trigger] self.iommu_acked(i) <= self.flush_epoch by {
                assert(pre.iommu_acked(i) <= pre.flush_epoch);
            }
            assert forall|i: int, e: TlbEntry|
                0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) && !self.mapped@.contains(e.page)
                implies e.page < NUM_PAGES && self.stale_epoch.above(self.iommu_acked(i), e.page) by {
                assert(pre.iommu_acked(i) <= pre.flush_epoch);
                assert(self.iommu_acked(i) == pre.iommu_acked(i));
                if pre.iommus.tlb@[i].contains(e) {
                    assert(!pre.mapped@.contains(e.page));
                    assert(pre.stale_epoch.above(pre.iommu_acked(i), e.page));
                    assert(pre.iommu_acked(i) < epoch);
                } else {
                    lemma_cut_pages(tree, t, e.page);
                    if e.page != t / 4096 {
                        pre.lemma_cut_walks_mapped(t, e.page);
                    }
                }
            }
            assert(self.tlb_wf());
            assert forall|d: int, g: usize| #![trigger self.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g })]
                0 <= d < NUM_CPUS && space is Some && pre.loaded(d, space->Some_0) && pages.contains(g)
                implies self.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g }) by {
            }
            assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] pre.tlb@[d].contains(e) implies self.tlb@[d].contains(e) by {
            }
            assert forall|i: int, g: usize| #![trigger self.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g })]
                0 <= i < NUM_IOMMUS && space is Some && pre.spaces.records@[space->Some_0].value().kind is Io && pages.contains(g)
                implies self.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g }) by {
            }
            assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] pre.iommus.tlb@[i].contains(e) implies self.iommus.tlb@[i].contains(e) by {
            }
        }
    }

    /// What a core could hold before a recorded cut it can hold after: the tables still say it, or the
    /// walk that found it passed through the cut entry, in t's space, and the record put it in the TLB.
    proof fn lemma_cut_keeps_hold(pre: Self, post: Self, t: usize, c: int, e: TlbEntry)
        requires
            pre.wf(),
            pre.table_pages.maps@.contains_key(t),
            0 <= c < NUM_CPUS,
            Self::tables_cut(pre, post, t),
            Self::cut_stale_noted(pre, post, t),
            pre.core_may_hold(c, e),
        ensures
            post.core_may_hold(c, e),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        if pre.tlb@[c].contains(e) {
            return;
        }
        assert(post.loaded(c, e.space));
        let q = a.record(t).parent;
        if q is None {
            assert(a == b);
            return;
        }
        let parent = q->0.table;
        let entry = q->0.entry;
        assert(detached(a, b, parent, entry, t));
        if exists|u: usize| #![trigger a.record(u)] a.is_table(u) && a.record(u).space == Some(e.space) && u / 4096 == e.page {
            let u = choose|u: usize| #![trigger a.record(u)] a.is_table(u) && a.record(u).space == Some(e.space) && u / 4096 == e.page;
            assert(b.maps.contains_key(u) == a.maps.contains_key(u));
            assert(b.roots.contains_key(u) == a.roots.contains_key(u));
            assert(b.record(u).space == a.record(u).space);
            assert(b.is_table(u) && b.record(u).space == Some(e.space) && u / 4096 == e.page);
            return;
        }
        let p = choose|p: SpacePath| #[trigger] walk_finds(a, e.space, p, e.page);
        reveal(walks_detached);
        assert(walk(b, e.space, p) == (if passes_through(a, e.space, p, parent, entry) { None } else { walk(a, e.space, p) }));
        if passes_through(a, e.space, p, parent, entry) {
            pre.lemma_passes_in_space(e.space, p, parent, entry);
            assert(a.maps.contains_key(t));
            assert(a.record(t).space == Some(e.space));
            assert(cut_walk_finds(a, t, e.page));
            pre.lemma_walk_mapped(e.space, p, e.page);
            lemma_cut_pages(a, t, e.page);
            assert(pre.loaded(c, e.space));
            assert(post.tlb@[c].contains(TlbEntry { space: e.space, page: e.page }));
            assert(TlbEntry { space: e.space, page: e.page } == e);
        } else {
            assert(walk_finds(b, e.space, p, e.page));
        }
    }

    /// Node n is a table page's hidden node.
    pub open spec fn hidden_table(&self, n: usize) -> bool {
        &&& self.list.nodes@[n as int].kind is Hidden
        &&& self.table_pages.maps@.contains_key(n)
    }

    /// Table page t's hidden node went: its cut is recorded, the node is gone and its block is dead at
    /// zero.
    pub open spec fn table_unlinked(pre: Self, post: Self, t: usize) -> bool {
        &&& Self::cut_recorded(pre, post, t)
        &&& !post.list.nodes@[t as int].live
        &&& post.blocks.pages@[(t / 4096) as int].refs == 0
        &&& post.blocks.pages@[(t / 4096) as int].dead
    }

    /// What a recorded cut says stays true while nothing it names changes.
    pub proof fn lemma_cut_recorded_same(pre: Self, mid: Self, post: Self, t: usize)
        requires
            pre.wf(),
            pre.table_pages.maps@.contains_key(t),
            Self::cut_recorded(pre, mid, t),
            mid.cores == pre.cores,
            post.table_pages == mid.table_pages,
            post.spaces == mid.spaces,
            post.cores == mid.cores,
            post.flush_epoch == mid.flush_epoch,
            post.tlb == mid.tlb,
            post.iommus == mid.iommus,
            post.mapped == mid.mapped,
            post.stale_epoch == mid.stale_epoch,
        ensures
            Self::cut_recorded(pre, post, t),
    {
        assert(pre.acked(0) <= pre.flush_epoch);
        assert(post.acked(0) == pre.acked(0));
        assert(!post.acknowledged(t / 4096));
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] pre.core_may_hold(c, e) implies post.core_may_hold(c, e) by {
            assert(mid.core_may_hold(c, e));
        }
    }

    /// A cut takes walks away and puts none in.
    pub proof fn lemma_cut_shrunk(pre: Self, post: Self, t: usize)
        requires
            Self::tree_cut(pre, post, t),
        ensures
            Self::mappings_shrunk(pre, post),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let q = a.record(t).parent;
        if q is None {
            assert(a == b);
        } else {
            reveal(walks_detached);
            assert forall|r: usize, p: SpacePath| #![trigger walk(b, r, p)] walk(b, r, p) is Some implies walk(b, r, p) == walk(a, r, p) by {
                assert(walk(b, r, p) == (if passes_through(a, r, p, q->0.table, q->0.entry) { None } else { walk(a, r, p) }));
            }
        }
    }

    /// Two steps that each only take walks away take only walks away.
    pub proof fn lemma_shrunk_compose(a: Self, b: Self, c: Self)
        requires
            Self::mappings_shrunk(a, b),
            Self::mappings_shrunk(b, c),
        ensures
            Self::mappings_shrunk(a, c),
    {
        let (ta, tb, tc) = (tree_of(&a.table_pages, &a.spaces), tree_of(&b.table_pages, &b.spaces), tree_of(&c.table_pages, &c.spaces));
        assert forall|r: usize, p: SpacePath| #![trigger walk(tc, r, p)] walk(tc, r, p) is Some implies walk(tc, r, p) == walk(ta, r, p) by {
            assert(walk(tc, r, p) == walk(tb, r, p));
            assert(walk(tb, r, p) == walk(ta, r, p));
        }
    }

    /// Cuts node n's table page, if n is a table page's hidden node, so that node can go.
    pub fn cut_hidden_table(&mut self, n: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(self).wf(),
            old(self).hidden_table(n) ==> Self::detach_recorded(*old(self), *final(self), n),
            old(self).hidden_table(n) ==> final(self).table_pages.records@[n].value().parent is None,
            !old(self).hidden_table(n) ==> *final(self) == *old(self),
    {
        let ghost pre = *old(self);
        proof {
            self.list.lemma_live_valid(n);
        }
        let node = self.list.get(n);
        match node.kind {
            NodeKind::Hidden => {
                proof {
                    pre.lemma_hidden_block(n);
                }
                let object = self.blocks.pages.get(n / 4096).object;
                match object {
                    ObjectType::TablePage => {
                        self.detach_stale(n);
                        proof {
                            let a = tree_of(&pre.table_pages, &pre.spaces);
                            let b = tree_of(&self.table_pages, &self.spaces);
                            assert(a.is_page(n) && b.is_page(n));
                        }
                    },
                    _ => {},
                }
            },
            _ => {},
        }
    }

    /// Cuts table page t from the entry that names it and records what that leaves stale, so the walks
    /// through it end and whatever a core or an IOMMU got from them is one a flush must take out.
    pub fn detach_stale(&mut self, t: usize)
        requires
            old(self).wf(),
            old(self).table_pages.maps@.contains_key(t),
            old(self).flush_epoch < usize::MAX,
        ensures
            final(self).wf(),
            Self::detach_recorded(*old(self), *final(self), t),
    {
        let ghost pre = *old(self);
        self.note_cut_stale(t);
        self.detach_table(t);
        proof {
            let a = tree_of(&pre.table_pages, &pre.spaces);
            assert(Self::tables_cut(pre, *self, t));
            assert(self.cores == pre.cores);
            assert(self.acked(0) == pre.acked(0));
            assert(pre.acked(0) <= pre.flush_epoch);
            assert(!self.acknowledged(t / 4096));
            assert(Self::cut_stale_noted(pre, *self, t));
            assert forall|g: usize| #[trigger] cut_walk_finds(a, t, g) implies self.mapped@.contains(g) && g < NUM_PAGES by {
                pre.lemma_cut_walks_mapped(t, g);
            }
            assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] pre.core_may_hold(c, e) implies self.core_may_hold(c, e) by {
                Self::lemma_cut_keeps_hold(pre, *self, t, c, e);
            }
        }
    }

    /// Cuts table page t from the entry that names it, the entry and t's parent in one step, so the walks
    /// through it end. t keeps its space, as what is below it does, and a table with no parent writes
    /// nothing. detach_stale records what the cut leaves stale.
    pub fn detach_table(&mut self, t: usize)
        requires
            old(self).wf(),
            old(self).table_pages.maps@.contains_key(t),
        ensures
            final(self).wf(),
            Self::detach_done(*old(self), *final(self), t),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let record = self.table_record(t, false);
        let p = match record.parent {
            None => { return; },
            Some(p) => p,
        };
        proof {
            assert(a.maps.contains_key(t));
            assert(a.names_child(p.table, p.entry));
            assert(a.record(p.table).level == a.record(t).level + 1);
            if a.is_page(p.table) {
                assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, p.table));
            } else {
                assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, p.table));
            }
        }
        let object = self.blocks.pages.get(p.table / 4096).object;
        match object {
            ObjectType::TablePage => {
                proof {
                    if !a.is_page(p.table) {
                        assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, p.table));
                    }
                }
                self.detach_from_page(p.table, p.entry, t);
            },
            _ => {
                proof {
                    if a.is_page(p.table) {
                        assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, p.table));
                    }
                }
                self.detach_from_root(p.table, p.entry, t);
            },
        }
    }

    /// Forgets table page child's parent.
    fn clear_parent(&mut self, child: usize)
        requires
            old(self).table_pages.records@.contains_key(child),
            old(self).table_pages.records@[child].addr() == child + TABLE_RECORD_PAGE * 4096,
            old(self).table_pages.records@[child].is_init(),
            child / 4096 < NUM_PAGES,
        ensures
            final(self).table_pages.maps == old(self).table_pages.maps,
            final(self).table_pages.spare == old(self).table_pages.spare,
            final(self).spaces == old(self).spaces,
            final(self).mappings == old(self).mappings,
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).cores == old(self).cores,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).tlb == old(self).tlb,
            final(self).iommus == old(self).iommus,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).table_pages.records@ == old(self).table_pages.records@.insert(child, final(self).table_pages.records@[child]),
            final(self).table_pages.records@[child].addr() == old(self).table_pages.records@[child].addr(),
            final(self).table_pages.records@[child].is_init(),
            final(self).table_pages.records@[child].value() == (TableRecord {
                level: old(self).table_pages.records@[child].value().level,
                space: old(self).table_pages.records@[child].value().space,
                parent: None,
                written: old(self).table_pages.records@[child].value().written,
            }),
    {
        proof {
            lemma_table_bound(child);
        }
        let ptr = PPtr::<TableRecord>::from_usize(child + TABLE_RECORD_PAGE * 4096);
        let tracked mut perm = self.table_pages.records.borrow_mut().tracked_remove(child);
        let record = *ptr.borrow(Tracked(&perm));
        ptr.write(Tracked(&mut perm), TableRecord { level: record.level, space: record.space, parent: None, written: record.written });
        proof {
            self.table_pages.records.borrow_mut().tracked_insert(child, perm);
            assert(self.table_pages.records@ =~= old(self).table_pages.records@.insert(child, self.table_pages.records@[child]));
        }
    }

    /// The table pages after a detach: the child's record lost its parent, a page parent's entry went
    /// empty, and every page keeps its table's address, its level and, while not written, its empty entries.
    proof fn lemma_detach_pages(pre: Self, post: Self, parent: usize, entry: usize, child: usize)
        requires
            pre.wf(),
            post.list == pre.list,
            post.blocks == pre.blocks,
            post.table_pages.spare == pre.table_pages.spare,
            pre.table_pages.maps@.contains_key(child),
            child != parent,
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            post.table_pages.records@.dom() == pre.table_pages.records@.dom(),
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent ==> post.table_pages.maps@[t] == pre.table_pages.maps@[t],
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != child
                ==> post.table_pages.records@[t] == pre.table_pages.records@[t],
            pre.table_pages.maps@.contains_key(parent) ==> {
                &&& post.table_pages.maps@[parent].addr() == pre.table_pages.maps@[parent].addr()
                &&& post.table_pages.maps@[parent].is_init()
                &&& post.table_pages.maps@[parent].value().wf()
                &&& entry < 512
                &&& post.table_pages.maps@[parent].value()[entry].is_empty()
                &&& forall|i: usize| i < 512 && i != entry ==> #[trigger] post.table_pages.maps@[parent].value()[i] == pre.table_pages.maps@[parent].value()[i]
            },
            post.table_pages.records@[child].addr() == pre.table_pages.records@[child].addr(),
            post.table_pages.records@[child].is_init(),
            post.table_pages.records@[child].value().level == pre.table_pages.records@[child].value().level,
            post.table_pages.records@[child].value().written == pre.table_pages.records@[child].value().written,
            post.table_pages.records@[child].value().parent is None,
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        let pa = &pre.table_pages;
        let pb = &post.table_pages;
        assert forall|t: usize| #[trigger] pb.maps@.contains_key(t) implies table_page_wf(&post.list, pb, &post.blocks, t) by {
            assert(pa.maps@.contains_key(t));
            assert(table_page_wf(&pre.list, pa, &pre.blocks, t));
            assert(pb.records@.contains_key(t));
            assert(table_record_wf(pb, t)) by {
                if !pb.records@[t].value().written {
                    assert(!pa.records@[t].value().written);
                    assert forall|i: usize| #![trigger pb.maps@[t].value()[i]] i < 512 implies pb.maps@[t].value()[i].is_empty() by {
                        if !(t == parent && i == entry) {
                            assert(pa.maps@[t].value()[i].is_empty());
                        }
                    }
                }
            }
        }
        assert forall|b: usize| b < NUM_PAGES && #[trigger] table_block(&post.blocks, b) implies pb.maps@.contains_key((b * 4096) as usize) by {
            assert(pa.maps@.contains_key((b * 4096) as usize));
        }
    }

    /// What a detach's writes say of the two trees, and the invariant after them, given the tables' own.
    proof fn lemma_detach_post(pre: Self, post: Self, parent: usize, entry: usize, child: usize)
        requires
            pre.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.spaces.loaded == pre.spaces.loaded,
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            pre.table_pages.maps@.contains_key(child),
            tree_of(&pre.table_pages, &pre.spaces).names_child(parent, entry),
            tree_of(&pre.table_pages, &pre.spaces).record(child).parent == Some(TableParent { table: parent, entry }),
            detached(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), parent, entry, child),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
        ensures
            post.wf(),
            walks_detached(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), parent, entry),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert forall|c: usize| #[trigger] a.maps.contains_key(c) implies c + TABLE_NODE_PAGES * 4096 <= usize::MAX by {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, c));
            lemma_table_bound(c);
        }
        lemma_links_detached(a, b, parent, entry, child);
        lemma_frame_entries_detached(a, b, parent, entry, child);
        Self::lemma_tables_changed_wf(pre, post);
        assert forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p)
            == (if passes_through(a, r, p, parent, entry) { None } else { walk(a, r, p) }) by {
            lemma_walk_detached(a, b, parent, entry, child, r, p);
        }
        assert(walks_detached(a, b, parent, entry)) by {
            reveal(walks_detached);
        }
    }

    /// Cuts `child` from `entry` of the table page `parent`, whose entry names it.
    fn detach_from_page(&mut self, parent: usize, entry: usize, child: usize)
        requires
            old(self).wf(),
            old(self).table_pages.maps@.contains_key(parent),
            old(self).table_pages.maps@.contains_key(child),
            tree_of(&old(self).table_pages, &old(self).spaces).names_child(parent, entry),
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).parent == Some(TableParent { table: parent, entry }),
            child != parent,
        ensures
            final(self).wf(),
            Self::detach_done(*old(self), *final(self), child),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, parent));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
            lemma_table_bound(parent);
            lemma_table_bound(child);
        }
        let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(parent);
        page_map_set(parent + TABLE_NODE_PAGES * 4096, Tracked(&mut map), entry, PageEntry::empty());
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(parent, map);
            assert(self.table_pages.maps@ =~= pre.table_pages.maps@.insert(parent, self.table_pages.maps@[parent]));
        }
        self.clear_parent(child);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            assert(post.table_pages.maps@ == pre.table_pages.maps@.insert(parent, post.table_pages.maps@[parent]));
            assert(post.table_pages.maps@.dom() == pre.table_pages.maps@.dom());
            assert(post.table_pages.records@.dom() == pre.table_pages.records@.dom());
            assert forall|i: usize| i < 512 && i != entry implies #[trigger] post.table_pages.maps@[parent].value()[i] == pre.table_pages.maps@[parent].value()[i] by {}
            assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent
                implies post.table_pages.maps@[t] == pre.table_pages.maps@[t] by {}
            assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != child
                implies post.table_pages.records@[t] == pre.table_pages.records@[t] by {}
            Self::lemma_detach_pages(pre, post, parent, entry, child);
            Self::lemma_detach_tree(pre, post, parent, entry, child);
            Self::lemma_detach_post(pre, post, parent, entry, child);
        }
    }

    /// Cuts `child` from `entry` of the root of space `parent`, whose entry names it.
    fn detach_from_root(&mut self, parent: usize, entry: usize, child: usize)
        requires
            old(self).wf(),
            old(self).spaces.roots@.contains_key(parent),
            !old(self).table_pages.maps@.contains_key(parent),
            old(self).table_pages.maps@.contains_key(child),
            tree_of(&old(self).table_pages, &old(self).spaces).names_child(parent, entry),
            tree_of(&old(self).table_pages, &old(self).spaces).record(child).parent == Some(TableParent { table: parent, entry }),
            child != parent,
        ensures
            final(self).wf(),
            Self::detach_done(*old(self), *final(self), child),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, parent));
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, child));
            lemma_table_bound(parent);
            lemma_table_bound(child);
        }
        let root = PPtr::<SpaceRecord>::from_usize(parent + SPACE_RECORD_PAGE * 4096)
            .borrow(Tracked(self.spaces.records.borrow().tracked_borrow(parent)))
            .root;
        let tracked mut map = self.spaces.roots.borrow_mut().tracked_remove(parent);
        page_map_set(root, Tracked(&mut map), entry, PageEntry::empty());
        proof {
            self.spaces.roots.borrow_mut().tracked_insert(parent, map);
            assert(self.spaces.roots@ =~= pre.spaces.roots@.insert(parent, self.spaces.roots@[parent]));
        }
        self.clear_parent(child);
        proof {
            let post = *self;
            assert(pre.spaces.roots@[parent].value()[entry].perm.present);
            assert(pre.spaces.records@[parent].value().table.written) by {
                assert(root_record_wf(&pre.spaces, parent));
                assert(!pre.spaces.roots@[parent].value()[entry].is_empty());
            }
            assert(post.spaces.roots@ == pre.spaces.roots@.insert(parent, post.spaces.roots@[parent]));
            assert(post.spaces.records@ =~= pre.spaces.records@.insert(parent, post.spaces.records@[parent]));
            assert forall|i: usize| i < 512 && i != entry implies #[trigger] post.spaces.roots@[parent].value()[i] == pre.spaces.roots@[parent].value()[i] by {}
            Self::lemma_link_spaces(pre, post, parent, entry);
            assert(post.table_pages.maps@ == pre.table_pages.maps@);
            assert(post.table_pages.records@.dom() == pre.table_pages.records@.dom());
            assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != child
                implies post.table_pages.records@[t] == pre.table_pages.records@[t] by {}
            Self::lemma_detach_pages(pre, post, parent, entry, child);
            Self::lemma_detach_tree(pre, post, parent, entry, child);
            Self::lemma_detach_post(pre, post, parent, entry, child);
        }
    }

    /// A detach's writes as a statement of the two trees: one entry and one parent.
    proof fn lemma_detach_tree(pre: Self, post: Self, parent: usize, entry: usize, child: usize)
        requires
            pre.wf(),
            pre.table_pages.maps@.contains_key(child),
            child != parent,
            tree_of(&pre.table_pages, &pre.spaces).is_table(parent),
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            post.spaces.roots@.dom() == pre.spaces.roots@.dom(),
            post.spaces.records == pre.spaces.records,
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != parent ==> post.table_pages.maps@[t] == pre.table_pages.maps@[t],
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != child
                ==> post.table_pages.records@[t] == pre.table_pages.records@[t],
            forall|t: usize| #[trigger] pre.spaces.roots@.contains_key(t) && t != parent ==> post.spaces.roots@[t] == pre.spaces.roots@[t],
            pre.table_pages.maps@.contains_key(parent) ==> {
                &&& post.table_pages.maps@[parent].value()[entry].is_empty()
                &&& forall|i: usize| i < 512 && i != entry ==> #[trigger] post.table_pages.maps@[parent].value()[i] == pre.table_pages.maps@[parent].value()[i]
            },
            !pre.table_pages.maps@.contains_key(parent) ==> {
                &&& post.spaces.roots@[parent].value()[entry].is_empty()
                &&& forall|i: usize| i < 512 && i != entry ==> #[trigger] post.spaces.roots@[parent].value()[i] == pre.spaces.roots@[parent].value()[i]
            },
            post.table_pages.records@[child].value().level == pre.table_pages.records@[child].value().level,
            post.table_pages.records@[child].value().space == pre.table_pages.records@[child].value().space,
            post.table_pages.records@[child].value().parent is None,
        ensures
            detached(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), parent, entry, child),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert forall|t: usize| #[trigger] b.is_page(t) == a.is_page(t) by {
            assert(post.table_pages.maps@.contains_key(t) == pre.table_pages.maps@.contains_key(t));
        }
        assert(b.entry(parent, entry).is_empty());
        assert forall|t: usize, i: usize| #![trigger b.entry(t, i)]
            a.is_table(t) && i < 512 && !(t == parent && i == entry) implies b.entry(t, i) == a.entry(t, i) by {
            if a.is_page(t) {
                if t == parent {
                    assert(post.table_pages.maps@[parent].value()[i] == pre.table_pages.maps@[parent].value()[i]);
                } else {
                    assert(post.table_pages.maps@[t] == pre.table_pages.maps@[t]);
                }
            } else {
                if t == parent {
                    assert(post.spaces.roots@[parent].value()[i] == pre.spaces.roots@[parent].value()[i]);
                } else {
                    assert(post.spaces.roots@[t] == pre.spaces.roots@[t]);
                }
            }
        }
        assert forall|t: usize| #![trigger b.record(t)] a.is_table(t) implies {
            &&& b.record(t).level == a.record(t).level
            &&& b.record(t).space == a.record(t).space
        } by {
            if a.is_page(t) && t != child {
                assert(post.table_pages.records@[t] == pre.table_pages.records@[t]);
            }
        }
        assert forall|t: usize| #![trigger b.record(t)] a.is_table(t) && t != child implies b.record(t).parent == a.record(t).parent by {
            if a.is_page(t) {
                assert(post.table_pages.records@[t] == pre.table_pages.records@[t]);
            }
        }
    }
}

} // verus!
