//! What a space maps, read by walking its tables from the root, as pagetable_spec's walk does. A kernel
//! slot leads nowhere, since child_slot excludes it. Map, unmap and detach state what they do in these
//! terms. See the design on atmo-6x9.6.7, section 8.
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::define::*;
use crate::pagetable::entry::PageEntry;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

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

    /// The step took entries away and put none in: whatever a walk finds now, it found before.
    pub open spec fn mappings_shrunk(pre: Self, post: Self) -> bool {
        forall|r: usize, p: SpacePath| #![trigger walk(tree_of(&post.table_pages, &post.spaces), r, p)]
            walk(tree_of(&post.table_pages, &post.spaces), r, p) is Some
                ==> walk(tree_of(&post.table_pages, &post.spaces), r, p) == walk(tree_of(&pre.table_pages, &pre.spaces), r, p)
    }

    /// Node n's mapping is gone: its entry is empty, its record and its reference with it, every other
    /// entry is as it was, its table's page is the only one written, and the only walks changed are
    /// those that ended at that entry.
    pub open spec fn mapping_unlinked(pre: Self, post: Self, n: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let m = pre.mappings@[n];
        let br = block_ref(&pre.blocks, m.frame);
        &&& post.table_pages.maps@ == pre.table_pages.maps@.insert(m.table, post.table_pages.maps@[m.table])
        &&& post.table_pages.maps@[m.table].addr() == pre.table_pages.maps@[m.table].addr()
        &&& post.table_pages.maps@[m.table].is_init()
        &&& post.table_pages.maps@[m.table].value().wf()
        &&& b.entry(m.table, m.entry).is_empty()
        &&& entries_cleared(a, b, m.table, m.entry)
        &&& walks_cut(a, b, m.table, m.entry)
        &&& post.mappings@ == pre.mappings@.remove(n)
        &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) - 1) as usize, block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1)
        &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].remove(n))
    }

    /// Unlinking a mapping takes a walk's entry away and puts none in.
    pub proof fn lemma_unlinked_shrunk(pre: Self, post: Self, n: usize)
        requires
            Self::mapping_unlinked(pre, post, n),
        ensures
            Self::mappings_shrunk(pre, post),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let m = pre.mappings@[n];
        reveal(walks_cut);
        assert forall|r: usize, p: SpacePath| #![trigger walk(b, r, p)]
            walk(b, r, p) is Some implies walk(b, r, p) == walk(a, r, p) by {
            assert(walk(b, r, p) == (if ends_at(a, r, p, m.table, m.entry) { None } else { walk(a, r, p) }));
        }
    }

    /// A step that keeps the tree keeps every walk.
    pub proof fn lemma_same_tree_shrunk(pre: Self, post: Self)
        requires
            Self::same_tree(pre, post),
        ensures
            Self::mappings_shrunk(pre, post),
    {
    }
}

/// Every entry but e of t, and every entry of every other table, is as it was. Kept opaque: the rule
/// relates every entry of b to a's and would otherwise feed every quantifier over entries.
#[verifier::opaque]
pub open spec fn entries_cleared(a: TableTree, b: TableTree, t: usize, e: usize) -> bool {
    forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        i < 512 && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i)
}

/// The walks that ended at entry e of t find nothing, and every other walk finds what it did. Kept
/// opaque for the same reason as entries_cleared.
#[verifier::opaque]
pub open spec fn walks_cut(a: TableTree, b: TableTree, t: usize, e: usize) -> bool {
    forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p)
        == if ends_at(a, r, p, t, e) { None } else { walk(a, r, p) }
}

/// Path p of space r reaches entry e of table t at level 1.
pub open spec fn ends_at(tree: TableTree, r: usize, p: SpacePath, t: usize, e: usize) -> bool {
    &&& tree.is_root(r)
    &&& p.l1 == e
    &&& match step(tree, r, p.l4) {
        None => false,
        Some(t3) => match step(tree, t3, p.l3) {
            None => false,
            Some(t2) => step(tree, t2, p.l2) == Some(t),
        },
    }
}

/// What a mapping node holds, by its node: the table and entry that map a frame, and the frame's page.
pub ghost struct MappingRecord {
    pub table: usize,
    pub entry: usize,
    pub frame: usize,
}

/// Entry e of the table page at t has its node at node e + 1 of the block's node pages, so an entry finds
/// its mapping in constant time. Node 0 is the hidden node.
pub open spec fn mapping_node(t: usize, e: usize) -> usize {
    (t + ((e + 1) / NODES_PER_PAGE as int) * 4096 + (e + 1) % NODES_PER_PAGE as int) as usize
}

/// Mapping node n stands for a present entry of a level 1 table, naming its frame. It is a child of a
/// frame capability covering the frame, and it holds a reference on the frame's block and on no other.
pub open spec fn mapping_wf(list: &Tree, tables: &Tables, tree: TableTree, blocks: &BlockTable, holders: IMap<BlockRef, Set<usize>>, mappings: IMap<usize, MappingRecord>, n: usize) -> bool {
    let m = mappings[n];
    let c = list.parent@[n];
    &&& n == mapping_node(m.table, m.entry)
    &&& n < NODE_SPACE
    &&& list.valid(n)
    &&& list.nodes@[n as int].live
    &&& list.nodes@[n as int].kind is Mapping
    &&& tree.is_page(m.table)
    &&& tree.record(m.table).level == 1
    &&& m.entry < 512
    &&& tree.entry(m.table, m.entry).perm.present
    &&& tree.entry(m.table, m.entry).addr == m.frame * 4096
    &&& m.frame < NUM_PAGES
    &&& holders.contains_key(block_ref(blocks, m.frame))
    &&& holders[block_ref(blocks, m.frame)].contains(n)
    &&& forall|br: BlockRef| holders.contains_key(br) && #[trigger] holders[br].contains(n) ==> br == block_ref(blocks, m.frame)
    &&& list.parent@.contains_key(n)
    &&& tables.is_cap(list, c)
    &&& tables.payload_of(c).kind is Frame
    &&& tables.payload_of(c).base <= m.frame * 4096
    &&& m.frame * 4096 + 4096 <= tables.payload_of(c).base as int + block_bytes(tables.payload_of(c).order)
}

/// Entry e of t is a present entry of a level 1 table page: a frame mapping.
pub open spec fn frame_slot(tree: TableTree, t: usize, e: usize) -> bool {
    &&& tree.is_page(t)
    &&& tree.record(t).level == 1
    &&& e < 512
    &&& tree.entry(t, e).perm.present
}

/// A live mapping node has a record, and a present entry of a level 1 table has the node that says so.
pub open spec fn mappings_wf(list: &Tree, tables: &Tables, tree: TableTree, blocks: &BlockTable, holders: IMap<BlockRef, Set<usize>>, mappings: IMap<usize, MappingRecord>) -> bool {
    &&& forall|n: usize| #[trigger] mappings.contains_key(n) ==> mapping_wf(list, tables, tree, blocks, holders, mappings, n)
    &&& forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Mapping
        ==> mappings.contains_key(n)
    &&& forall|t: usize, e: usize| #[trigger] frame_slot(tree, t, e) ==> {
        &&& mappings.contains_key(mapping_node(t, e))
        &&& mappings[mapping_node(t, e)].table == t
        &&& mappings[mapping_node(t, e)].entry == e
    }
}

/// Every level 1 table of a is one of b with its entries, and a level 1 table new in b has no present
/// entry.
pub open spec fn same_frame_entries(a: TableTree, b: TableTree) -> bool {
    &&& forall|t: usize| #![trigger a.record(t)] a.is_page(t) && a.record(t).level == 1 ==> {
        &&& b.is_page(t)
        &&& b.record(t).level == 1
        &&& forall|i: usize| i < 512 ==> #[trigger] b.entry(t, i) == a.entry(t, i)
    }
    &&& forall|t: usize| #![trigger b.record(t)] b.is_page(t) && b.record(t).level == 1 && !(a.is_page(t) && a.record(t).level == 1)
        ==> forall|i: usize| i < 512 ==> !(#[trigger] b.entry(t, i)).perm.present
}

/// What mappings_wf reads of mapping node n besides the tree and the records: its node, its parent's
/// capability, its frame's block and its place among the holders. Each is as it was, under whatever
/// name the parent now has.
pub open spec fn mapping_node_kept(
    list_a: &Tree,
    tables_a: &Tables,
    blocks_a: &BlockTable,
    holders_a: IMap<BlockRef, Set<usize>>,
    list_b: &Tree,
    tables_b: &Tables,
    blocks_b: &BlockTable,
    holders_b: IMap<BlockRef, Set<usize>>,
    frame: usize,
    n: usize,
) -> bool {
    &&& list_b.valid(n)
    &&& list_b.parent@.contains_key(n)
    &&& tables_b.is_cap(list_b, list_b.parent@[n])
    &&& tables_b.payload_of(list_b.parent@[n]) == tables_a.payload_of(list_a.parent@[n])
    &&& block_ref(blocks_b, frame) == block_ref(blocks_a, frame)
    &&& holders_b.contains_key(block_ref(blocks_a, frame))
    &&& holders_b[block_ref(blocks_a, frame)].contains(n)
    &&& forall|br: BlockRef| holders_b.contains_key(br) && #[trigger] holders_b[br].contains(n)
        ==> holders_a.contains_key(br) && holders_a[br].contains(n)
}

/// The mappings after a step that kept every level 1 entry, every mapping node and what each reads.
pub proof fn lemma_mappings_kept(
    list_a: &Tree,
    tables_a: &Tables,
    tree_a: TableTree,
    blocks_a: &BlockTable,
    holders_a: IMap<BlockRef, Set<usize>>,
    list_b: &Tree,
    tables_b: &Tables,
    tree_b: TableTree,
    blocks_b: &BlockTable,
    holders_b: IMap<BlockRef, Set<usize>>,
    mappings: IMap<usize, MappingRecord>,
)
    requires
        mappings_wf(list_a, tables_a, tree_a, blocks_a, holders_a, mappings),
        same_mapping_nodes(list_a, list_b),
        same_frame_entries(tree_a, tree_b),
        forall|n: usize| #[trigger] mappings.contains_key(n)
            ==> mapping_node_kept(list_a, tables_a, blocks_a, holders_a, list_b, tables_b, blocks_b, holders_b, mappings[n].frame, n),
    ensures
        mappings_wf(list_b, tables_b, tree_b, blocks_b, holders_b, mappings),
{
    assert forall|n: usize| #[trigger] mappings.contains_key(n)
        implies mapping_wf(list_b, tables_b, tree_b, blocks_b, holders_b, mappings, n) by {
        let m = mappings[n];
        assert(mapping_wf(list_a, tables_a, tree_a, blocks_a, holders_a, mappings, n));
        assert(mapping_node_kept(list_a, tables_a, blocks_a, holders_a, list_b, tables_b, blocks_b, holders_b, m.frame, n));
        assert(tree_a.record(m.table).level == 1);
        assert(tree_b.entry(m.table, m.entry) == tree_a.entry(m.table, m.entry));
        assert(list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Mapping);
        assert(list_b.nodes@[n as int].live && list_b.nodes@[n as int].kind is Mapping);
    }
    assert forall|n: usize| n < NODE_SPACE && (#[trigger] list_b.nodes@[n as int]).live && list_b.nodes@[n as int].kind is Mapping
        implies mappings.contains_key(n) by {
        assert(list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Mapping);
    }
    assert forall|t: usize, e: usize| #[trigger] frame_slot(tree_b, t, e) implies {
        &&& mappings.contains_key(mapping_node(t, e))
        &&& mappings[mapping_node(t, e)].table == t
        &&& mappings[mapping_node(t, e)].entry == e
    } by {
        if tree_a.is_page(t) && tree_a.record(t).level == 1 {
            assert(tree_b.entry(t, e) == tree_a.entry(t, e));
            assert(frame_slot(tree_a, t, e));
        } else {
            assert(!tree_b.entry(t, e).perm.present);
        }
    }
}

impl CapKernel {
    /// Mapping node n is listed below its parent, a frame capability, and its frame's block has
    /// references, since it holds n.
    pub proof fn lemma_mapping_node(&self, n: usize)
        requires
            self.wf(),
            self.mappings@.contains_key(n),
        ensures
            n < NODE_SPACE,
            self.list.valid(n),
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Mapping,
            self.list.parent@.contains_key(n),
            self.is_cap(self.list.parent@[n]),
            self.payload_of(self.list.parent@[n]).kind is Frame,
            self.list.is_child(self.list.parent@[n], n),
            self.mappings@[n].frame < NUM_PAGES,
            self.holders@.contains_key(block_ref(&self.blocks, self.mappings@[n].frame)),
            self.holders@[block_ref(&self.blocks, self.mappings@[n].frame)].contains(n),
            block_typed(&self.blocks, block_ref(&self.blocks, self.mappings@[n].frame)),
            block_refs(&self.blocks, block_ref(&self.blocks, self.mappings@[n].frame)) > 0,
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(has(self.list.seq@, n));
        lemma_has(self.list.seq@, n);
        assert(n != self.list.seq@[0]);
        let br = block_ref(&self.blocks, self.mappings@[n].frame);
        if self.holders@[br].len() == 0 {
            self.holders@[br].lemma_len0_is_empty();
        }
    }

    /// A childless live node is no mapping's parent.
    pub proof fn lemma_childless_no_mapping(&self, x: usize)
        requires
            self.wf(),
            x < NODE_SPACE,
            self.list.nodes@[x as int].live,
            self.list.childless(x),
        ensures
            forall|n: usize| #[trigger] self.mappings@.contains_key(n) ==> self.list.parent@[n] != x,
    {
        let s = self.list.seq@;
        assert(has(s, x));
        lemma_has(s, x);
        let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
        self.list.lemma_link(j);
        if j + 1 < s.len() {
            self.list.lemma_link(j + 1);
            assert(s[j + 1] != NONE);
        }
        self.list.lemma_no_child(x, j);
        assert forall|n: usize| #[trigger] self.mappings@.contains_key(n) implies self.list.parent@[n] != x by {
            self.lemma_mapping_node(n);
            assert(!self.list.is_child(x, n));
        }
    }

    /// Each mapping's parent is still a capability saying the same after a step that changed only nodes
    /// x and y, neither any mapping's parent, and no parent link.
    pub proof fn lemma_mapping_parents_kept(pre: Self, post: Self, x: usize, y: usize)
        requires
            Self::caps_frame(pre, post, x, y),
            post.list.parent@ == pre.list.parent@,
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n) ==> pre.list.parent@[n] != x && pre.list.parent@[n] != y,
        ensures
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n) ==> {
                &&& post.list.parent@.contains_key(n)
                &&& post.is_cap(post.list.parent@[n])
                &&& post.payload_of(post.list.parent@[n]) == pre.payload_of(pre.list.parent@[n])
            },
    {
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies {
            &&& post.list.parent@.contains_key(n)
            &&& post.is_cap(post.list.parent@[n])
            &&& post.payload_of(post.list.parent@[n]) == pre.payload_of(pre.list.parent@[n])
        } by {
            pre.lemma_mapping_node(n);
            Self::lemma_caps_frame(pre, post, x, y, pre.list.parent@[n]);
        }
    }

    /// The mappings after a step that touched no table and no mapping node, given what it did to each
    /// mapping node's parent, frame block and holders.
    pub proof fn lemma_mappings_same_tree(pre: Self, post: Self)
        requires
            pre.wf(),
            Self::same_tree(pre, post),
            post.mappings == pre.mappings,
            same_mapping_nodes(&pre.list, &post.list),
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n) ==> mapping_node_kept(
                &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
            ),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(same_frame_entries(a, b));
        lemma_mappings_kept(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, &post.list, &post.tables, b, &post.blocks, post.holders@, pre.mappings@);
    }

    /// The mappings after a step that added list pages and nodes, none a mapping, kept every mapping
    /// node's parent link, every capability and the holders, typed a free small block, and added no
    /// present entry at level 1.
    pub proof fn lemma_mappings_grown(pre: Self, post: Self, page: usize, order: usize)
        requires
            pre.wf(),
            post.mappings == pre.mappings,
            post.holders == pre.holders,
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
            same_mapping_nodes(&pre.list, &post.list),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
                ==> post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n],
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.is_cap(x) && post.payload_of(x) == pre.payload_of(x),
            small_order(order),
            page % (order_pages(order) as usize) == 0,
            page + order_pages(order) <= NUM_PAGES,
            forall|k: int| 0 <= k < order_pages(order) ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            !pre.blocks.covered(page as int),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| 0 <= i < NUM_PAGES && !(page <= i < page + order_pages(order))
                ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
        ) by {
            pre.lemma_mapping_node(n);
            lemma_block_ref_small_typed(&pre.blocks, &post.blocks, page, order, pre.mappings@[n].frame);
        }
        lemma_mappings_kept(
            &pre.list, &pre.tables, tree_of(&pre.table_pages, &pre.spaces), &pre.blocks, pre.holders@,
            &post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, pre.mappings@,
        );
    }

    /// Mapping node n lies in a node page of its table's block: the block's base page or a member of it,
    /// so in no leaf's block.
    pub proof fn lemma_mapping_node_page(&self, n: usize)
        requires
            self.wf(),
            self.mappings@.contains_key(n),
        ensures
            page_of(n) / 4096 < NUM_PAGES,
            !leaf_block(&self.blocks, page_of(n) / 4096),
    {
        let m = self.mappings@[n];
        let t = m.table;
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        let q = t / 4096;
        self.blocks.lemma_base(q as int);
        assert(order_pages(3) == 8);
        lemma_mapping_node_place(t, m.entry);
        let k = ((m.entry + 1) / (NODES_PER_PAGE as int)) as usize;
        assert(page_of(n) / 4096 == q + k);
        if k > 0 {
            self.blocks.lemma_member_of(q as int, q + k);
        }
    }
}

/// Where a mapping node lies: in node page (e + 1) / 128 of its table's block, at slot (e + 1) % 128.
pub proof fn lemma_mapping_node_place(t: usize, e: usize)
    requires
        t % 32768 == 0,
        t / 4096 + TABLE_NODE_PAGES <= NUM_PAGES,
        e < 512,
    ensures
        (e + 1) / (NODES_PER_PAGE as int) < TABLE_NODE_PAGES,
        mapping_node(t, e) == t + ((e + 1) / (NODES_PER_PAGE as int)) * 4096 + (e + 1) % (NODES_PER_PAGE as int),
        mapping_node(t, e) / 4096 == t / 4096 + (e + 1) / (NODES_PER_PAGE as int),
        mapping_node(t, e) % 4096 == (e + 1) % (NODES_PER_PAGE as int),
        page_of(mapping_node(t, e)) == table_node_page(t, ((e + 1) / (NODES_PER_PAGE as int)) as usize),
{
    let k = ((e + 1) / (NODES_PER_PAGE as int)) as usize;
    let s = (e + 1) % (NODES_PER_PAGE as int);
    lemma_table_page_aligned(t);
    let q = t / 4096;
    assert(k < TABLE_NODE_PAGES);
    assert(s < NODES_PER_PAGE);
    let n = mapping_node(t, e);
    assert(n == 4096 * (q + k) + s);
    lemma_fundamental_div_mod_converse(n as int, 4096, q + k, s as int);
    assert(page_of(n) == n - s);
    lemma_table_node_page(t, k);
}

/// A table added with no present entry keeps the level 1 entries: every table of a is as it was.
pub proof fn lemma_frame_entries_extended(a: TableTree, b: TableTree)
    requires
        tree_extended(a, b),
        forall|u: usize| #[trigger] b.is_page(u) && !a.is_page(u)
            ==> forall|i: usize| i < 512 ==> !(#[trigger] b.entry(u, i)).perm.present,
    ensures
        same_frame_entries(a, b),
{
    assert forall|t: usize| #![trigger a.record(t)] a.is_page(t) && a.record(t).level == 1 implies {
        &&& b.is_page(t)
        &&& b.record(t).level == 1
        &&& forall|i: usize| i < 512 ==> #[trigger] b.entry(t, i) == a.entry(t, i)
    } by {
        assert(a.is_table(t));
    }
    assert forall|t: usize| #![trigger b.record(t)] b.is_page(t) && b.record(t).level == 1 && !(a.is_page(t) && a.record(t).level == 1)
        implies forall|i: usize| i < 512 ==> !(#[trigger] b.entry(t, i)).perm.present by {
        if a.is_page(t) {
            assert(a.is_table(t));
            assert(b.record(t) == a.record(t));
        }
    }
}

/// A link keeps the level 1 entries: it writes an entry of a table above level 1.
pub proof fn lemma_frame_entries_linked(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, s: usize)
    requires
        linked(a, b, parent, entry, child, s),
        a.is_table(parent),
        a.record(parent).level >= 2,
    ensures
        same_frame_entries(a, b),
{
    assert forall|t: usize| #![trigger a.record(t)] a.is_page(t) && a.record(t).level == 1 implies {
        &&& b.is_page(t)
        &&& b.record(t).level == 1
        &&& forall|i: usize| i < 512 ==> #[trigger] b.entry(t, i) == a.entry(t, i)
    } by {
        assert(b.maps.dom() == a.maps.dom());
        assert(b.is_page(t));
        assert(a.is_table(t));
        assert(b.record(t).level == a.record(t).level);
        assert(t != parent);
    }
    assert forall|t: usize| #![trigger b.record(t)] b.is_page(t) && b.record(t).level == 1 && !(a.is_page(t) && a.record(t).level == 1)
        implies forall|i: usize| i < 512 ==> !(#[trigger] b.entry(t, i)).perm.present by {
        assert(b.maps.dom() == a.maps.dom());
        assert(a.is_page(t));
        assert(a.is_table(t));
        assert(b.record(t).level == a.record(t).level);
    }
}

/// The mapping nodes after pages are added and nodes x and y, neither a mapping, are made: every other
/// node is as it was.
pub proof fn lemma_mapping_nodes_grown(a: Tree, mid: Tree, b: Tree, x: usize, y: usize)
    requires
        a.wf(),
        list_grown(a, mid),
        forall|i: int| #![trigger b.nodes@[i]] 0 <= i < NODE_SPACE && i != x && i != y ==> {
            &&& b.nodes@[i].live == mid.nodes@[i].live
            &&& b.nodes@[i].kind == mid.nodes@[i].kind
        },
        x < NODE_SPACE,
        y < NODE_SPACE,
        !a.nodes@[x as int].live,
        !a.nodes@[y as int].live,
        !(b.nodes@[x as int].kind is Mapping),
        !(b.nodes@[y as int].kind is Mapping),
    ensures
        same_mapping_nodes(&a, &b),
{
    assert forall|i: usize| i < NODE_SPACE implies
        (b.nodes@[i as int].live && b.nodes@[i as int].kind is Mapping) == (a.nodes@[i as int].live && a.nodes@[i as int].kind is Mapping) by {
        if i != x && i != y {
            assert(mid.nodes@[i as int].live == a.nodes@[i as int].live);
            if a.nodes@[i as int].live {
                a.lemma_live_valid(i);
                assert(mid.nodes@[i as int] == a.nodes@[i as int]);
            }
        }
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

impl CapKernel {
    /// Undoes mapping node n: its entry and its reference go in one step, and nothing else. The node's
    /// own page says where its entry is.
    pub fn clear_mapping(&mut self, n: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            old(self).list.nodes@[n as int].kind is Mapping,
        ensures
            Self::mapping_unlinked(*old(self), *final(self), n),
            final(self).tables == old(self).tables,
            final(self).blocks.wf(),
            final(self).list == old(self).list,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).tlb == old(self).tlb,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).spaces == old(self).spaces,
            final(self).table_pages.records == old(self).table_pages.records,
            final(self).table_pages.spare == old(self).table_pages.spare,
    {
        let ghost pre = *old(self);
        let ghost m = pre.mappings@[n];
        proof {
            pre.lemma_mapping_node_located(n);
            pre.lemma_mapping_node(n);
        }
        let page = n / 4096;
        let block = *self.blocks.pages.get(page);
        let base = match block.kind {
            crate::capability::block::PageKind::Member => block.base,
            _ => page,
        };
        let t = base * 4096;
        let e = (page - base) * NODES_PER_PAGE + n % 4096 - 1;
        proof {
            assert(t == m.table);
            assert(e == m.entry);
        }
        let entry = PPtr::<PageMap>::from_usize(t + TABLE_NODE_PAGES * 4096)
            .borrow(Tracked(self.table_pages.maps.borrow().tracked_borrow(t)))
            .get(e);
        proof {
            assert(entry =~= tree_of(&pre.table_pages, &pre.spaces).entry(m.table, m.entry));
        }
        let br = locate(&self.blocks, entry.addr / 4096);
        let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(t);
        page_map_set(t + TABLE_NODE_PAGES * 4096, Tracked(&mut map), e, PageEntry::empty());
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(t, map);
        }
        drop_block_ref(&mut self.blocks, br);
        self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].remove(n)));
        self.mappings = Ghost(pre.mappings@.remove(n));
        proof {
            assert(self.table_pages.maps@ =~= pre.table_pages.maps@.insert(m.table, map));
            assert forall|i: usize| #![trigger self.table_pages.maps@[m.table].value()[i]] i < 512 && i != m.entry
                implies self.table_pages.maps@[m.table].value()[i] == pre.table_pages.maps@[m.table].value()[i] by {
                assert(map.value()[i] =~= pre.table_pages.maps@[m.table].value()[i]);
            }
            Self::lemma_clear_mapping_post(pre, *self, n);
        }
    }

    /// Where mapping node n's entry is, read from n alone: its table t is the block based at page t / 4096,
    /// n lies in node page (e + 1) / 128 of that block at slot (e + 1) % 128, and the entry it stands for
    /// names its frame.
    pub proof fn lemma_mapping_node_located(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Mapping,
        ensures
            self.mappings@.contains_key(n),
            ({
                let m = self.mappings@[n];
                let q = m.table / 4096;
                let k = ((m.entry + 1) / (NODES_PER_PAGE as int)) as usize;
                let tree = tree_of(&self.table_pages, &self.spaces);
                &&& n / 4096 == q + k
                &&& n / 4096 < NUM_PAGES
                &&& k == 0 ==> self.blocks.pages@[(n / 4096) as int].kind is Base
                &&& k > 0 ==> self.blocks.pages@[(n / 4096) as int].kind is Member && self.blocks.pages@[(n / 4096) as int].base == q
                &&& q * 4096 == m.table
                &&& m.table + TABLE_NODE_PAGES * 4096 <= usize::MAX
                &&& (n / 4096 - q) * NODES_PER_PAGE + n % 4096 - 1 == m.entry
                &&& m.entry < 512
                &&& self.table_pages.maps@.contains_key(m.table)
                &&& self.table_pages.maps@[m.table].addr() == m.table + TABLE_NODE_PAGES * 4096
                &&& self.table_pages.maps@[m.table].is_init()
                &&& self.table_pages.maps@[m.table].value().wf()
                &&& tree.entry(m.table, m.entry).addr == m.frame * 4096
                &&& tree.entry(m.table, m.entry).addr / 4096 == m.frame
                &&& m.frame < NUM_PAGES
            }),
    {
        let m = self.mappings@[n];
        let t = m.table;
        let q = t / 4096;
        let k = ((m.entry + 1) / (NODES_PER_PAGE as int)) as usize;
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        self.blocks.lemma_base(q as int);
        assert(order_pages(3) == 8);
        lemma_mapping_node_place(t, m.entry);
        lemma_table_page_base(t, q);
        assert(n / 4096 == q + k);
        if k > 0 {
            self.blocks.lemma_member_of(q as int, q + k);
        }
        lemma_fundamental_div_mod((m.entry + 1) as int, NODES_PER_PAGE as int);
        assert((n / 4096 - q) * NODES_PER_PAGE + n % 4096 - 1 == m.entry);
        lemma_div_multiples_vanish(m.frame as int, 4096);
    }

    /// Emptying mapping node n's entry, with its reference dropped and its record and holding removed,
    /// is the unlinking of n.
    proof fn lemma_clear_mapping_post(pre: Self, post: Self, n: usize)
        requires
            pre.wf(),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Mapping,
            post.spaces == pre.spaces,
            post.table_pages.records == pre.table_pages.records,
            ({
                let m = pre.mappings@[n];
                let br = block_ref(&pre.blocks, m.frame);
                &&& post.table_pages.maps@ == pre.table_pages.maps@.insert(m.table, post.table_pages.maps@[m.table])
                &&& post.table_pages.maps@[m.table].addr() == pre.table_pages.maps@[m.table].addr()
                &&& post.table_pages.maps@[m.table].is_init()
                &&& post.table_pages.maps@[m.table].value().wf()
                &&& forall|i: usize| #![trigger post.table_pages.maps@[m.table].value()[i]] i < 512 && i != m.entry
                    ==> post.table_pages.maps@[m.table].value()[i] == pre.table_pages.maps@[m.table].value()[i]
                &&& post.table_pages.maps@[m.table].value()[m.entry].is_empty()
                &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) - 1) as usize, block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1)
                &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].remove(n))
                &&& post.mappings@ == pre.mappings@.remove(n)
            }),
        ensures
            Self::mapping_unlinked(pre, post, n),
    {
        let m = pre.mappings@[n];
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(pre.mappings@.contains_key(n));
        pre.lemma_mapping_node(n);
        assert(mapping_wf(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, pre.mappings@, n));
        assert(b.is_page(m.table));
        assert(b.maps.dom() =~= a.maps.dom());
        assert(b.entry(m.table, m.entry).is_empty());
        assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
            i < 512 && !(u == m.table && i == m.entry) implies b.entry(u, i) == a.entry(u, i) by {
            assert(b.is_page(u) == a.is_page(u));
            if u != m.table && a.is_page(u) {
                assert(post.table_pages.maps@[u] == pre.table_pages.maps@[u]);
            }
        }
        assert(entries_cleared(a, b, m.table, m.entry)) by {
            reveal(entries_cleared);
        }
        assert forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p)
            == (if ends_at(a, r, p, m.table, m.entry) { None } else { walk(a, r, p) }) by {
            lemma_walk_entry_cleared(a, b, m.table, m.entry, r, p);
        }
        assert(walks_cut(a, b, m.table, m.entry)) by {
            reveal(walks_cut);
        }
    }
}

/// Clearing entry e of level 1 table t ends the walks that reached it and no other: a step reads only
/// entries of tables above level 1, and a frame entry is read only by the walk that ends at it.
pub proof fn lemma_walk_entry_cleared(a: TableTree, b: TableTree, t: usize, e: usize, r: usize, p: SpacePath)
    requires
        b.maps.dom() == a.maps.dom(),
        b.roots == a.roots,
        b.records == a.records,
        b.space_records == a.space_records,
        a.is_page(t),
        a.record(t).level == 1,
        e < 512,
        !b.entry(t, e).perm.present,
        forall|u: usize, i: usize| #![trigger b.entry(u, i)] i < 512 && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i),
    ensures
        walk(b, r, p) == (if ends_at(a, r, p, t, e) { None } else { walk(a, r, p) }),
{
    assert forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i) by {
        assert(b.child_slot(u, i) == a.child_slot(u, i));
        if a.child_slot(u, i) {
            assert(u != t);
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert forall|u: usize, i: usize| !(u == t && i == e) implies #[trigger] frame_entry(b, u, i) == frame_entry(a, u, i) by {
        if a.is_table(u) && i < 512 {
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert(frame_entry(b, t, e) is None);
    if a.is_root(r) {
        if let Some(t3) = step(a, r, p.l4) {
            if let Some(t2) = step(a, t3, p.l3) {
                if let Some(t1) = step(a, t2, p.l2) {
                    if t1 == t && p.l1 == e {
                        assert(ends_at(a, r, p, t, e));
                    } else {
                        assert(!ends_at(a, r, p, t, e));
                        assert(frame_entry(b, t1, p.l1) == frame_entry(a, t1, p.l1));
                    }
                }
            }
        }
    }
}

/// The table pages after entry e of table page t is emptied: the page keeps its address, its record
/// and its other entries, and a record not written had no entry to lose.
pub proof fn lemma_table_pages_entry_cleared(list: &Tree, pa: &TablePages, pb: &TablePages, blocks: &BlockTable, t: usize, e: usize)
    requires
        table_pages_wf(list, pa, blocks),
        pa.maps@.contains_key(t),
        e < 512,
        pb.records == pa.records,
        pb.spare == pa.spare,
        pb.maps@ == pa.maps@.insert(t, pb.maps@[t]),
        pb.maps@[t].addr() == pa.maps@[t].addr(),
        pb.maps@[t].is_init(),
        pb.maps@[t].value().wf(),
        forall|i: usize| #![trigger pb.maps@[t].value()[i]] i < 512 && i != e ==> pb.maps@[t].value()[i] == pa.maps@[t].value()[i],
        pb.maps@[t].value()[e].is_empty(),
    ensures
        table_pages_wf(list, pb, blocks),
{
    assert forall|u: usize| #[trigger] pb.maps@.contains_key(u) implies table_page_wf(list, pb, blocks, u) by {
        assert(pa.maps@.contains_key(u));
        assert(table_page_wf(list, pa, blocks, u));
        if u == t {
            assert(table_record_wf(pb, t)) by {
                let record = pb.records@[t].value();
                if !record.written {
                    assert forall|i: usize| #![trigger pb.maps@[t].value()[i]] i < 512 implies pb.maps@[t].value()[i].is_empty() by {
                        if i != e {
                            assert(pa.maps@[t].value()[i].is_empty());
                        }
                    }
                }
            }
        } else {
            assert(pb.maps@[u] == pa.maps@[u]);
        }
    }
}

/// The links after entry e of level 1 table t is emptied: no link is at level 1.
pub proof fn lemma_links_entry_cleared(a: TableTree, b: TableTree, t: usize, e: usize)
    requires
        table_links_wf(a),
        b.maps.dom() == a.maps.dom(),
        b.roots == a.roots,
        b.records == a.records,
        b.space_records == a.space_records,
        a.is_page(t),
        a.record(t).level == 1,
        forall|u: usize, i: usize| #![trigger b.entry(u, i)] i < 512 && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i),
    ensures
        table_links_wf(b),
{
    assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        b.child_slot(u, i) && b.entry(u, i).perm.present implies {
        let c = (b.entry(u, i).addr - TABLE_NODE_PAGES * 4096) as usize;
        &&& b.is_page(c)
        &&& b.record(c).parent == Some(TableParent { table: u, entry: i })
    } by {
        assert(a.child_slot(u, i));
        assert(u != t);
        assert(b.entry(u, i) == a.entry(u, i));
        let _ = a.entry(u, i);
    }
    assert forall|c: usize| #![trigger b.maps.contains_key(c)] b.is_page(c) implies {
        let r = b.record(c);
        &&& (r.parent is Some) == (r.space is Some)
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& b.child_slot(p.table, p.entry)
            &&& b.entry(p.table, p.entry).perm.present
            &&& b.entry(p.table, p.entry).addr == table_addr(c)
            &&& b.record(p.table).level == r.level + 1
            &&& b.record(p.table).space == r.space
        }
        &&& r.space is Some ==> b.is_root(r.space->0)
    } by {
        assert(a.is_page(c));
        assert(a.maps.contains_key(c));
        let r = a.record(c);
        if r.parent is Some {
            let p = r.parent->0;
            assert(a.child_slot(p.table, p.entry));
            assert(p.table != t);
            assert(b.entry(p.table, p.entry) == a.entry(p.table, p.entry));
        }
    }
}

} // verus!
