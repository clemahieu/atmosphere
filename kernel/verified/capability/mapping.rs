//! What a space maps, read by walking its tables from the root, as pagetable_spec's walk does. A kernel
//! slot leads nowhere, since child_slot excludes it. Map, unmap and detach state what they do in these
//! terms. See the design on atmo-6x9.6.7, section 8.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::space::*;
use crate::define::*;
use crate::pagetable::entry::*;

/// The indices of one page of a space's virtual address, level 4 first.
pub ghost struct SpacePath {
    pub l4: usize,
    pub l3: usize,
    pub l2: usize,
    pub l1: usize,
}

/// The table entry i of table t leads to, if it can hold a child and is present.
pub open spec fn step(tree: TableTree, t: usize, i: usize) -> Option<usize> {
    if tree.child_slot(t, i) && tree.entry(t, i).perm.present {
        Some((tree.entry(t, i).addr - TABLE_NODE_PAGES * 4096) as usize)
    } else {
        None
    }
}

/// The frame entry i of table t maps, if t is at level 1 and the entry is present.
pub open spec fn frame_entry(tree: TableTree, t: usize, i: usize) -> Option<PageEntry> {
    if tree.is_table(t) && i < 512 && tree.record(t).level == 1 && tree.entry(t, i).perm.present {
        Some(tree.entry(t, i))
    } else {
        None
    }
}

/// What path p of space s maps.
pub open spec fn walk(tree: TableTree, s: usize, p: SpacePath) -> Option<PageEntry> {
    if !tree.is_root(s) {
        None
    } else {
        match step(tree, s, p.l4) {
            None => None,
            Some(t3) => match step(tree, t3, p.l3) {
                None => None,
                Some(t2) => match step(tree, t2, p.l2) {
                    None => None,
                    Some(t1) => frame_entry(tree, t1, p.l1),
                },
            },
        }
    }
}

/// The abstract mapping of space s: every path the walk finds a frame entry at.
pub open spec fn space_mapping(tree: TableTree, s: usize) -> IMap<SpacePath, PageEntry> {
    IMap::new(|p: SpacePath| walk(tree, s, p) is Some, |p: SpacePath| walk(tree, s, p)->0)
}

impl CapKernel {
    /// The step touched no table, so no space's mapping changed.
    pub open spec fn same_tree(pre: Self, post: Self) -> bool {
        tree_of(&post.table_pages, &post.spaces) == tree_of(&pre.table_pages, &pre.spaces)
    }
}

/// A root with no entry past the kernel slots maps nothing.
pub proof fn lemma_mapping_fresh(tree: TableTree, s: usize)
    requires
        forall|i: usize| KERNEL_MEM_END_L4INDEX <= i < 512 ==> #[trigger] tree.entry(s, i).is_empty(),
        tree.is_root(s),
    ensures
        space_mapping(tree, s) =~= IMap::<SpacePath, PageEntry>::empty(),
{
    assert forall|p: SpacePath| !(#[trigger] walk(tree, s, p) is Some) by {
        if tree.child_slot(s, p.l4) {
            assert(tree.entry(s, p.l4).is_empty());
        }
    }
}

/// A link leaves every walk as it was. The new entry was not present, and the child it leads to has no
/// entry, so no walk went through it before or finds anything through it now. It is above level 1, so
/// no walk ends at it.
pub proof fn lemma_walk_linked(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, s: usize, r: usize, p: SpacePath)
    requires
        linked(a, b, parent, entry, child, s),
        a.child_slot(parent, entry),
        a.entry(parent, entry).is_empty(),
        a.is_page(child),
        child != parent,
        child + TABLE_NODE_PAGES * 4096 <= usize::MAX,
        forall|i: usize| i < 512 ==> #[trigger] a.entry(child, i).is_empty(),
    ensures
        walk(b, r, p) == walk(a, r, p),
{
    assert forall|t: usize, i: usize| !(t == parent && i == entry) implies #[trigger] step(b, t, i) == step(a, t, i) by {
        if a.is_table(t) && i < 512 {
            assert(b.entry(t, i) == a.entry(t, i));
            assert(b.record(t).level == a.record(t).level);
        }
    }
    assert forall|t: usize, i: usize| true implies #[trigger] frame_entry(b, t, i) == frame_entry(a, t, i) by {
        if a.is_table(t) && i < 512 {
            assert(b.record(t).level == a.record(t).level);
            if !(t == parent && i == entry) {
                assert(b.entry(t, i) == a.entry(t, i));
            }
        }
    }
    assert(step(a, parent, entry) is None);
    assert forall|i: usize| i < 512 implies step(b, child, i) is None && frame_entry(b, child, i) is None by {
        assert(b.entry(child, i) == a.entry(child, i));
        assert(a.entry(child, i).is_empty());
    }
    assert forall|i: usize| i >= 512 implies step(b, child, i) is None && frame_entry(b, child, i) is None by {}
    assert(b.entry(parent, entry).addr == table_addr(child));
    assert(step(b, parent, entry) == Some(child));
}

/// So a link leaves every space's mapping as it was.
pub proof fn lemma_mapping_linked(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, s: usize, r: usize)
    requires
        linked(a, b, parent, entry, child, s),
        a.child_slot(parent, entry),
        a.entry(parent, entry).is_empty(),
        a.is_page(child),
        child != parent,
        child + TABLE_NODE_PAGES * 4096 <= usize::MAX,
        forall|i: usize| i < 512 ==> #[trigger] a.entry(child, i).is_empty(),
    ensures
        space_mapping(b, r) =~= space_mapping(a, r),
{
    assert forall|p: SpacePath| #[trigger] walk(b, r, p) == walk(a, r, p) by {
        lemma_walk_linked(a, b, parent, entry, child, s, r, p);
    }
}

/// Every table of a is in b as it was, and b has others.
pub open spec fn tree_extended(a: TableTree, b: TableTree) -> bool {
    forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) ==> {
        &&& b.is_page(t) == a.is_page(t)
        &&& b.is_root(t) == a.is_root(t)
        &&& b.record(t) == a.record(t)
        &&& forall|i: usize| i < 512 ==> #[trigger] b.entry(t, i) == a.entry(t, i)
    }
}

/// A new table is on no walk: an existing table's present entry names a table that already exists.
pub proof fn lemma_mapping_extended(a: TableTree, b: TableTree, s: usize)
    requires
        table_links_wf(a),
        tree_extended(a, b),
        a.is_root(s),
    ensures
        space_mapping(b, s) =~= space_mapping(a, s),
{
    assert forall|t: usize, i: usize| #![trigger step(a, t, i)] a.is_table(t) && i < 512 implies step(b, t, i) == step(a, t, i)
        && frame_entry(b, t, i) == frame_entry(a, t, i) && (step(a, t, i) is Some ==> a.is_table(step(a, t, i)->0)) by {
        assert(b.entry(t, i) == a.entry(t, i));
        if a.child_slot(t, i) && a.entry(t, i).perm.present {
            assert(table_links_wf(a));
            let _ = a.entry(t, i);
        }
    }
    assert forall|p: SpacePath| #[trigger] walk(b, s, p) == walk(a, s, p) by {
        assert(a.is_table(s));
        if p.l4 < 512 {
            if let Some(t3) = step(a, s, p.l4) {
                assert(a.is_table(t3));
                if p.l3 < 512 {
                    if let Some(t2) = step(a, t3, p.l3) {
                        assert(a.is_table(t2));
                        if p.l2 < 512 {
                            if let Some(t1) = step(a, t2, p.l2) {
                                assert(a.is_table(t1));
                                if p.l1 >= 512 {
                                    assert(frame_entry(b, t1, p.l1) is None);
                                    assert(frame_entry(a, t1, p.l1) is None);
                                }
                            }
                        } else {
                            assert(step(b, t2, p.l2) is None);
                            assert(step(a, t2, p.l2) is None);
                        }
                    }
                } else {
                    assert(step(b, t3, p.l3) is None);
                    assert(step(a, t3, p.l3) is None);
                }
            }
        } else {
            assert(step(b, s, p.l4) is None);
            assert(step(a, s, p.l4) is None);
        }
    }
}

} // verus!
