//! Address spaces as retyped objects. A table page is an order-3 block: 5 node pages, whose node 0 is
//! the block's hidden node, then the table, then 2 spare pages. So an entry finds its mapping's node
//! in constant time, and whoever maps pays for the table. See the design on atmo-6x9.6.7, sections 1
//! and 8.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::define::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

/// The node pages of a table page's block, first in it, so its hidden node is at its address.
pub const TABLE_NODE_PAGES: usize = 5;

/// The permissions of each table page's table and spare pages, by the block's address.
pub struct TablePages {
    pub maps: Tracked<Map<usize, PointsTo<PageMap>>>,
    pub spare: Tracked<Map<usize, PagePerm4k>>,
}

impl TablePages {
    pub fn new() -> (ret: Self)
        ensures
            ret.maps@ == Map::<usize, PointsTo<PageMap>>::empty(),
            ret.spare@ == Map::<usize, PagePerm4k>::empty(),
    {
        TablePages { maps: Tracked(Map::tracked_empty()), spare: Tracked(Map::tracked_empty()) }
    }
}

/// The kth node page of the table page at t.
pub open spec fn table_node_page(t: usize, k: usize) -> usize {
    (t + k * 4096) as usize
}

/// The block at page b holds a table page.
pub open spec fn table_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& blocks.pages@[b as int].object is TablePage
}

/// The table page at t has its table, its spare pages and its node pages. Its block holds one
/// reference, its hidden node's, and is dead at once when that goes.
pub open spec fn table_page_wf(list: &Tree, pages: &TablePages, blocks: &BlockTable, t: usize) -> bool {
    &&& t % 32768 == 0
    &&& t / 4096 < NUM_PAGES
    &&& pages.maps@[t].addr() == t + TABLE_NODE_PAGES * 4096
    &&& pages.maps@[t].is_init()
    &&& pages.maps@[t].value().wf()
    &&& pages.spare@.contains_key((t + 6 * 4096) as usize)
    &&& pages.spare@.contains_key((t + 7 * 4096) as usize)
    &&& pages.spare@[(t + 6 * 4096) as usize].addr() == t + 6 * 4096
    &&& pages.spare@[(t + 7 * 4096) as usize].addr() == t + 7 * 4096
    &&& pages.spare@[(t + 6 * 4096) as usize].is_uninit()
    &&& pages.spare@[(t + 7 * 4096) as usize].is_uninit()
    &&& blocks.pages@[(t / 4096) as int].kind is Base
    &&& blocks.pages@[(t / 4096) as int].object is TablePage
    &&& blocks.pages@[(t / 4096) as int].order == 3
    &&& forall|k: usize| k < TABLE_NODE_PAGES ==> list.pages@.dom().contains(#[trigger] table_node_page(t, k))
    &&& list.nodes@[t as int].live ==> {
        &&& list.nodes@[t as int].kind is Hidden
        &&& blocks.pages@[(t / 4096) as int].refs == 1
        &&& !blocks.pages@[(t / 4096) as int].dead
    }
    &&& !list.nodes@[t as int].live ==> {
        &&& blocks.pages@[(t / 4096) as int].refs == 0
        &&& blocks.pages@[(t / 4096) as int].dead
    }
}

/// Each table page is well formed, and a table page block is one of these, so a retype naming one
/// finds its node.
pub open spec fn table_pages_wf(list: &Tree, pages: &TablePages, blocks: &BlockTable) -> bool {
    &&& forall|t: usize| #[trigger] pages.maps@.contains_key(t) ==> table_page_wf(list, pages, blocks, t)
    &&& forall|b: usize| b < NUM_PAGES && #[trigger] table_block(blocks, b)
        ==> pages.maps@.contains_key((b * 4096) as usize)
}

/// Every table page's node is as it was.
pub open spec fn same_table_nodes(list_a: &Tree, list_b: &Tree, pages: &TablePages) -> bool {
    forall|t: usize| #[trigger] pages.maps@.contains_key(t) ==> {
        &&& list_b.nodes@[t as int].live == list_a.nodes@[t as int].live
        &&& list_b.nodes@[t as int].kind == list_a.nodes@[t as int].kind
    }
}

/// A table page's base, eight pages aligned, is page aligned and is its page's base.
pub proof fn lemma_table_page_aligned(t: usize)
    requires
        t % 32768 == 0,
    ensures
        t % 4096 == 0,
        t as int == 4096 * (t as int / 4096),
        (t / 4096) % 8 == 0,
{
    lemma_fundamental_div_mod(t as int, 32768);
    let q = t as int / 32768;
    assert(t as int == 4096 * (8 * q));
    lemma_mod_multiples_basic(8 * q, 4096);
    lemma_div_multiples_vanish(8 * q, 4096);
    assert(t as int / 4096 == 8 * q);
    lemma_mod_multiples_basic(q, 8);
}

/// Two distinct table pages lie on distinct pages.
pub proof fn lemma_table_pages_distinct(t: usize, u: usize)
    requires
        t % 32768 == 0,
        u % 32768 == 0,
        t != u,
    ensures
        t / 4096 != u / 4096,
{
    lemma_table_page_aligned(t);
    lemma_table_page_aligned(u);
}

/// Two distinct table pages are eight pages apart, so their spare pages are distinct.
pub proof fn lemma_table_pages_apart(t: usize, u: usize)
    requires
        t % 32768 == 0,
        u % 32768 == 0,
        t != u,
    ensures
        t + 6 * 4096 != u + 7 * 4096,
{
    lemma_fundamental_div_mod(t as int, 32768);
    lemma_fundamental_div_mod(u as int, 32768);
}

/// The kth node page of a table page is the kth page of its block, page aligned.
pub proof fn lemma_table_node_page(t: usize, k: usize)
    requires
        t % 32768 == 0,
        t / 4096 + k < NUM_PAGES,
    ensures
        table_node_page(t, k) == t + k * 4096,
        table_node_page(t, k) % 4096 == 0,
        table_node_page(t, k) / 4096 == t / 4096 + k,
{
    lemma_table_page_aligned(t);
    let p = t as int / 4096;
    assert((t + k * 4096) as int == 4096 * (p + k));
    lemma_mod_multiples_basic(p + k, 4096);
    lemma_div_multiples_vanish(p + k, 4096);
}

/// The block at `base`, eight pages aligned, starts at `page`.
pub proof fn lemma_table_page_base(base: usize, page: usize)
    requires
        base % 32768 == 0,
        page == base / 4096,
    ensures
        page % 8 == 0,
        page * 4096 == base,
        base % 4096 == 0,
{
    lemma_table_page_aligned(base);
}

/// The table pages read nothing of the list but their node pages and nodes.
pub proof fn lemma_table_pages_same_nodes(list_a: &Tree, list_b: &Tree, pages: &TablePages, blocks: &BlockTable)
    requires
        table_pages_wf(list_a, pages, blocks),
        same_table_nodes(list_a, list_b, pages),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        table_pages_wf(list_b, pages, blocks),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list_b, pages, blocks, t) by {
        assert(table_page_wf(list_a, pages, blocks, t));
        assert forall|k: usize| k < TABLE_NODE_PAGES implies list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
            assert(list_a.pages@.dom().contains(table_node_page(t, k)));
        }
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_table_pages_same_pages(list: &Tree, pages: &TablePages, a: &BlockTable, b: &BlockTable)
    requires
        table_pages_wf(list, pages, a),
        b.pages@ == a.pages@,
    ensures
        table_pages_wf(list, pages, b),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list, pages, b, t) by {
        assert(table_page_wf(list, pages, a, t));
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(table_block(a, x));
    }
}

/// A table page's block is no holder's key: a holder's small block is a frame.
pub proof fn lemma_table_page_unkeyed(
    list: &Tree,
    pages: &TablePages,
    tables: &Tables,
    blocks: &BlockTable,
    holders: IMap<BlockRef, Set<usize>>,
    t: usize,
)
    requires
        table_pages_wf(list, pages, blocks),
        objects_wf(tables, blocks, holders),
        pages.maps@.contains_key(t),
    ensures
        t / 4096 < NUM_PAGES,
        block_typed(blocks, BlockRef::Small(t / 4096)),
        !holders.contains_key(BlockRef::Small(t / 4096)),
{
    assert(table_page_wf(list, pages, blocks, t));
    if holders.contains_key(BlockRef::Small(t / 4096)) {
        assert(blocks.pages@[(t / 4096) as int].object is Frame);
    }
}

/// A step that changes the count of a block that is no table page's leaves every table page's block
/// as it was.
pub proof fn lemma_table_pages_refs_changed(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        table_pages_wf(list_a, pages, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !(a.pages@[x as int].object is TablePage),
            _ => true,
        },
        same_table_nodes(list_a, list_b, pages),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        table_pages_wf(list_b, pages, b),
{
    lemma_table_pages_same_nodes(list_a, list_b, pages, a);
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list_b, pages, b, t) by {
        assert(table_page_wf(list_b, pages, a, t));
        let x = BlockRef::Small(t / 4096);
        assert(block_typed(a, x));
        assert(x != br);
        assert(block_refs(b, x) == block_refs(a, x));
        assert(block_dead(b, x) == block_dead(a, x));
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(table_block(a, x));
    }
}

/// The table pages after hidden node t goes and its block's one reference with it: that block is dead
/// at zero, and every other table page's block is as it was, since no two lie on one page.
pub proof fn lemma_table_page_dropped(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    t: usize,
)
    requires
        table_pages_wf(list_a, pages, a),
        pages.maps@.contains_key(t),
        blocks_refs_changed(a, b, BlockRef::Small(t / 4096), 0, true),
        !list_b.nodes@[t as int].live,
        forall|u: usize| #[trigger] pages.maps@.contains_key(u) && u != t ==> {
            &&& list_b.nodes@[u as int].live == list_a.nodes@[u as int].live
            &&& list_b.nodes@[u as int].kind == list_a.nodes@[u as int].kind
        },
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        table_pages_wf(list_b, pages, b),
{
    let br = BlockRef::Small(t / 4096);
    assert forall|u: usize| #[trigger] pages.maps@.contains_key(u) implies table_page_wf(list_b, pages, b, u) by {
        assert(table_page_wf(list_a, pages, a, u));
        assert forall|k: usize| k < TABLE_NODE_PAGES implies list_b.pages@.dom().contains(#[trigger] table_node_page(u, k)) by {
            assert(list_a.pages@.dom().contains(table_node_page(u, k)));
        }
        if u != t {
            lemma_table_pages_distinct(u, t);
            let x = BlockRef::Small(u / 4096);
            assert(block_typed(a, x));
            assert(x != br);
            assert(block_refs(b, x) == block_refs(a, x));
            assert(block_dead(b, x) == block_dead(a, x));
        }
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(table_block(a, x));
    }
}

/// The table pages after a free small block is typed: no table page lay in it, and a table block
/// outside it was one before.
pub proof fn lemma_table_pages_small_typed(
    list: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        table_pages_wf(list, pages, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
    ensures
        forall|t: usize| #[trigger] pages.maps@.contains_key(t) ==> table_page_wf(list, pages, b, t),
        forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x) && !(base <= x < base + size)
            ==> pages.maps@.contains_key((x * 4096) as usize),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list, pages, b, t) by {
        assert(table_page_wf(list, pages, a, t));
        let x = (t / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x) && !(base <= x < base + size)
        implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(table_block(a, x));
    }
}

/// The table pages after a small block frees: a table page's first page is the list's, so it was not
/// in it, and a freed page is no table block.
pub proof fn lemma_table_pages_small_freed(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        table_pages_wf(list_a, pages, a),
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
            ==> !a.in_block(base as int, (p / 4096) as int),
        forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_table_nodes(list_a, list_b, pages),
        forall|t: usize, k: usize| #[trigger] pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            ==> list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)),
    ensures
        table_pages_wf(list_b, pages, b),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list_b, pages, b, t) by {
        assert(table_page_wf(list_a, pages, a, t));
        assert(list_b.pages@.dom().contains(table_node_page(t, 0)));
        assert(table_node_page(t, 0) == t);
        assert(!a.in_block(base as int, (t / 4096) as int));
        assert(b.pages@[(t / 4096) as int] == a.pages@[(t / 4096) as int]);
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(table_block(a, x));
    }
}

/// A table page's node pages stay the list's when a page of another kind of block leaves it: each is
/// its block's base or member.
pub proof fn lemma_table_node_pages_kept(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    blocks: &BlockTable,
    base: usize,
)
    requires
        table_pages_wf(list_a, pages, blocks),
        blocks.wf(),
        base / 4096 < NUM_PAGES,
        !(blocks.pages@[(base / 4096) as int].kind is Member),
        !(blocks.pages@[(base / 4096) as int].object is TablePage),
        list_b.pages@.dom() == list_a.pages@.dom().remove(base),
    ensures
        forall|t: usize, k: usize| #[trigger] pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            ==> list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)),
{
    assert forall|t: usize, k: usize| #[trigger] pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
        implies list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
        assert(table_page_wf(list_a, pages, blocks, t));
        let p = table_node_page(t, k);
        assert(list_a.pages@.dom().contains(p));
        let page = (t / 4096) as int;
        blocks.lemma_base(page);
        lemma_table_node_page(t, k);
        if k == 0 {
            assert(p / 4096 == t / 4096);
        } else {
            blocks.lemma_member_of(page, page + k);
        }
        assert(p / 4096 != base / 4096);
    }
}

/// The list's pages stay used after a free small block is typed: none lay in it, and a member page's
/// base is a base, so not in it either.
pub proof fn lemma_list_pages_used_small_typed(list: &Tree, a: &BlockTable, b: &BlockTable, base: usize, size: int)
    requires
        list_pages_used(list, a),
        a.member_bases_wf(),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
    ensures
        list_pages_used(list, b),
{
    assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
        &&& !(b.pages@[(p / 4096) as int].kind is Free)
        &&& b.pages@[(p / 4096) as int].kind is Member
            ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
        &&& !(b.pages@[(p / 4096) as int].object is Frame)
    } by {
        let x = (p / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
        if a.pages@[x].kind is Member {
            a.lemma_member(x);
            let bb = a.pages@[x].base as int;
            if base <= bb < base + size {
                assert(a.pages@[base + (bb - base)].kind is Free);
            }
            assert(b.pages@[bb] == a.pages@[bb]);
        }
    }
}

/// The list's pages stay used after a small block frees: none lay in it, and a member page's base is
/// a base in the same block, so not in it either.
pub proof fn lemma_list_pages_used_small_freed(list: &Tree, a: &BlockTable, b: &BlockTable, base: usize)
    requires
        list_pages_used(list, a),
        a.wf(),
        base < NUM_PAGES,
        a.pages@[base as int].kind is Base,
        forall|p: usize| #[trigger] list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
            ==> !a.in_block(base as int, (p / 4096) as int),
        forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
    ensures
        list_pages_used(list, b),
{
    assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
        &&& !(b.pages@[(p / 4096) as int].kind is Free)
        &&& b.pages@[(p / 4096) as int].kind is Member
            ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
        &&& !(b.pages@[(p / 4096) as int].object is Frame)
    } by {
        let x = (p / 4096) as int;
        assert(!a.in_block(base as int, x));
        assert(b.pages@[x] == a.pages@[x]);
        if a.pages@[x].kind is Member {
            a.lemma_member(x);
            let bb = a.pages@[x].base as int;
            if a.in_block(base as int, bb) {
                if bb != base as int {
                    a.lemma_member_of(base as int, bb);
                }
                assert(bb == base as int);
                assert(a.in_block(base as int, x));
            }
            assert(b.pages@[bb] == a.pages@[bb]);
        }
    }
}

/// The list's pages stay used when it gains a page of a typed block that is no frame.
pub proof fn lemma_list_pages_used_page_added(list_a: &Tree, list_b: &Tree, blocks: &BlockTable, p: usize)
    requires
        list_pages_used(list_a, blocks),
        list_b.pages@.dom() == list_a.pages@.dom().insert(p),
        p / 4096 < NUM_PAGES ==> {
            &&& blocks.pages@[(p / 4096) as int].kind is Base
            &&& !(blocks.pages@[(p / 4096) as int].object is Frame)
        },
    ensures
        list_pages_used(list_b, blocks),
{
    assert forall|q: usize| #[trigger] list_b.pages@.dom().contains(q) && q / 4096 < NUM_PAGES implies {
        &&& !(blocks.pages@[(q / 4096) as int].kind is Free)
        &&& blocks.pages@[(q / 4096) as int].kind is Member
            ==> blocks.pages@[blocks.pages@[(q / 4096) as int].base as int].object is TablePage
        &&& !(blocks.pages@[(q / 4096) as int].object is Frame)
    } by {
        if q != p {
            assert(list_a.pages@.dom().contains(q));
        }
    }
}

/// And when it loses pages.
pub proof fn lemma_list_pages_used_subset(list_a: &Tree, list_b: &Tree, blocks: &BlockTable)
    requires
        list_pages_used(list_a, blocks),
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) ==> list_a.pages@.dom().contains(p),
    ensures
        list_pages_used(list_b, blocks),
{
    assert forall|q: usize| #[trigger] list_b.pages@.dom().contains(q) && q / 4096 < NUM_PAGES implies {
        &&& !(blocks.pages@[(q / 4096) as int].kind is Free)
        &&& blocks.pages@[(q / 4096) as int].kind is Member
            ==> blocks.pages@[blocks.pages@[(q / 4096) as int].base as int].object is TablePage
        &&& !(blocks.pages@[(q / 4096) as int].object is Frame)
    } by {
        assert(list_a.pages@.dom().contains(q));
    }
}

/// A list that gained pages: nothing it held changed, and no node became live.
pub open spec fn list_grown(a: Tree, b: Tree) -> bool {
    &&& b.seq == a.seq
    &&& b.parent == a.parent
    &&& forall|p: usize| #[trigger] a.pages@.dom().contains(p) ==> b.pages@.dom().contains(p)
    &&& forall|i: usize| #[trigger] a.valid(i) ==> b.valid(i) && b.nodes@[i as int] == a.nodes@[i as int]
    &&& forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] b.nodes@[i].live == a.nodes@[i].live
}

pub proof fn lemma_list_grown_trans(a: Tree, b: Tree, c: Tree)
    requires
        list_grown(a, b),
        list_grown(b, c),
    ensures
        list_grown(a, c),
{
    assert forall|i: usize| #[trigger] a.valid(i) implies c.valid(i) && c.nodes@[i as int] == a.nodes@[i as int] by {
        assert(b.valid(i));
    }
}

impl CapKernel {
    /// A table page's first node page is the list's, so its node 0 is a node the list holds, and it is
    /// no leaf.
    pub proof fn lemma_table_page_valid(&self, t: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
        ensures
            t % 4096 == 0,
            t < NODE_SPACE,
            self.list.pages@.dom().contains(t),
            self.list.valid(t),
            !self.tables.owner@.contains_key(t),
    {
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        lemma_table_page_aligned(t);
        assert(self.list.pages@.dom().contains(table_node_page(t, 0)));
        assert(table_node_page(t, 0) == t);
        assert(page_of(t) == t);
    }

    /// A slot's node is no table page, since a table page is page aligned.
    pub proof fn lemma_slot_not_table_page(&self, n: usize)
        requires
            self.wf(),
            n % 4096 != 0,
        ensures
            !self.table_pages.maps@.contains_key(n),
    {
        if self.table_pages.maps@.contains_key(n) {
            self.lemma_table_page_valid(n);
        }
    }

    /// A live node that is not hidden is no table page, since a table page's live node is its hidden one.
    pub proof fn lemma_unhidden_not_table_page(&self, n: usize)
        requires
            self.wf(),
            self.list.nodes@[n as int].live,
            !(self.list.nodes@[n as int].kind is Hidden),
        ensures
            !self.table_pages.maps@.contains_key(n),
    {
        if self.table_pages.maps@.contains_key(n) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, n));
        }
    }

    /// A step that changes no node but n and m, neither a table page, leaves every table page's node as
    /// it was.
    pub proof fn lemma_same_table_nodes(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            !pre.table_pages.maps@.contains_key(n),
            !pre.table_pages.maps@.contains_key(m),
        ensures
            same_table_nodes(&pre.list, &post.list, &pre.table_pages),
    {
        assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) implies {
            &&& post.list.nodes@[t as int].live == pre.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind == pre.list.nodes@[t as int].kind
        } by {
            pre.lemma_table_page_valid(t);
            assert(t != n && t != m);
        }
    }

    /// The view after a hidden node joins under a capability: every capability is as it was, and the
    /// only new parent entry is the hidden node's, which no capability descends from.
    pub proof fn lemma_hidden_added_discharges(pre: Self, post: Self, root: usize, parent: usize, n: usize)
        requires
            pre.wf(),
            n < NODE_SPACE,
            !pre.list.nodes@[n as int].live,
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> {
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.tables.owner@[page_of(x)] == pre.tables.owner@[page_of(x)]
            },
            post.list.parent@ == pre.list.parent@.insert(n, parent),
            pre.view().holds_right(root, parent, Right::Retype),
        ensures
            discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: n }),
    {
        let (a, b) = (post.view(), pre.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        let f = |x: NodeId| x;
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, f(h.1))) by {
            assert(post.is_cap(h.1) == pre.is_cap(h.1));
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(f(x))
            &&& b.names[f(x)] == a.names[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(f(x))
            &&& b.pages[f(x)] == a.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((f(x), r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            assert(x != n);
            pre.list.lemma_parent_live(x);
        }
        assert(simulates(a, b, live, f));
        assert forall|x: NodeId| #[trigger] b.names.contains_key(x) implies a.names.contains_key(x) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|o: ObjectId| #[trigger] (a.contents)(o) == (b.contents)(o) by {}
        lemma_simulated_discharges_retype(b, a, root, parent, n, live, f);
    }

    /// What a table page's retype does to the fields the view reads: the tables are as they were, and so
    /// is every node the list held.
    pub open spec fn table_page_step(pre: Self, post: Self) -> bool {
        &&& pre.wf()
        &&& post.tables == pre.tables
        &&& forall|x: usize| #[trigger] pre.list.valid(x) ==> {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        }
    }

    /// So the capabilities, and what they say, are as they were.
    pub proof fn lemma_table_page_cap(pre: Self, post: Self, x: usize)
        requires
            Self::table_page_step(pre, post),
        ensures
            post.is_cap(x) == pre.is_cap(x),
            pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
    {
        if pre.tables.owner@.contains_key(page_of(x)) && x % 4096 < NODES_PER_PAGE {
            pre.lemma_slot_bound(x);
        }
    }

    proof fn lemma_table_page_caps_wf(pre: Self, post: Self)
        requires
            Self::table_page_step(pre, post),
        ensures
            post.tables.caps_wf(&post.list),
            same_frames(&pre.list, &pre.tables, &post.list, &post.tables),
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
    {
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.payload_of(x) == pre.payload_of(x) by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) implies payload_wf(post.tables.payload_of(n)) by {
            assert(post.is_cap(n));
            assert(pre.tables.is_cap(&pre.list, n));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Frame implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Frame implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
    }

    /// A node the list held before the table page's retype has its kind after, and a leaf's node is one.
    proof fn lemma_table_page_old_node(pre: Self, post: Self, mid: Tree, base: usize, x: usize)
        requires
            Self::table_page_step(pre, post),
            list_grown(pre.list, mid),
            !pre.list.pages@.dom().contains(base),
            x < NODE_SPACE,
            post.list.nodes@[x as int].live,
            x != base ==> post.list.nodes@[x as int].live == mid.nodes@[x as int].live,
        ensures
            x != base ==> pre.list.nodes@[x as int].live && pre.list.valid(x)
                && pre.list.nodes@[x as int].kind == post.list.nodes@[x as int].kind,
    {
        if x != base {
            assert(pre.list.nodes@[x as int].live);
            pre.list.lemma_live_valid(x);
        }
    }

    /// The hidden nodes, the parents, the slots and the leaves after a table page's retype: the new node
    /// is the table page's, hidden under the untyped's capability, and every other node's kind and
    /// parent are as they were.
    proof fn lemma_table_page_nodes(pre: Self, post: Self, mid: Tree, parent: usize, base: usize)
        requires
            Self::table_page_step(pre, post),
            list_grown(pre.list, mid),
            mid.wf(),
            post.list.wf(),
            !pre.list.pages@.dom().contains(base),
            base < NODE_SPACE,
            mid.valid(base),
            !mid.nodes@[base as int].live,
            parent < NODE_SPACE,
            pre.is_cap(parent),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.list.parent@ == mid.parent@.insert(base, parent),
            post.list.seq@[0] == mid.seq@[0],
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
            },
            post.table_pages.maps@.contains_key(base),
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) ==> post.table_pages.maps@.contains_key(t),
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
            capability_nodes_are_slots(&post.list, &post.tables),
            first_node_outside_leaves(&post.list, &post.tables),
            leaf_slots_are_capabilities(&post.list, &post.tables),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            Self::lemma_table_page_old_node(pre, post, mid, base, x);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) && post.tables.attached(l) implies {
            &&& l < NODE_SPACE
            &&& post.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind is Hidden
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            lemma_leaf_page(l);
            assert(page_of(l) == l);
            assert(pre.list.valid(l));
            pre.list.lemma_valid_bound(l);
            assert(l != base);
        }
        pre.lemma_slot_bound(parent);
        lemma_parents_same_live(pre.list, mid);
        lemma_parents_derived(mid, post.list, parent, base);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Capability && x != post.list.seq@[0]
            implies post.tables.is_cap(&post.list, x) by {
            Self::lemma_table_page_old_node(pre, post, mid, base, x);
            assert(pre.tables.is_cap(&pre.list, x));
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|n: usize| #[trigger] post.list.nodes@[n as int].live && post.tables.owner@.contains_key(page_of(n))
            && n % 4096 != 0 && n % 4096 < NODES_PER_PAGE implies post.list.nodes@[n as int].kind is Capability by {
            pre.lemma_slot_bound(n);
        }
    }

    /// The block table's invariants after the free order-3 block at `page` is typed as the table page at
    /// `base`: no leaf, frame or list page lay in it, and the list's new pages are its first five.
    proof fn lemma_table_page_blocks(pre: Self, post: Self, base: usize, page: usize)
        requires
            Self::table_page_step(pre, post),
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.blocks.wf(),
            base % 32768 == 0,
            base / 4096 == page,
            page * 4096 == base,
            page % 8 == 0,
            page + 8 <= NUM_PAGES,
            !pre.blocks.covered(page as int),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| 0 <= i < NUM_PAGES && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TablePage,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|k: usize| k < TABLE_NODE_PAGES ==> post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) ==> pre.list.pages@.dom().contains(p)
                || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]),
            post.table_pages.maps@[base].addr() == base + TABLE_NODE_PAGES * 4096,
            post.table_pages.maps@[base].is_init(),
            post.table_pages.maps@[base].value().wf(),
            post.table_pages.spare@ == pre.table_pages.spare@
                .insert((base + 6 * 4096) as usize, post.table_pages.spare@[(base + 6 * 4096) as usize])
                .insert((base + 7 * 4096) as usize, post.table_pages.spare@[(base + 7 * 4096) as usize]),
            post.table_pages.spare@[(base + 6 * 4096) as usize].addr() == base + 6 * 4096,
            post.table_pages.spare@[(base + 7 * 4096) as usize].addr() == base + 7 * 4096,
            post.table_pages.spare@[(base + 6 * 4096) as usize].is_uninit(),
            post.table_pages.spare@[(base + 7 * 4096) as usize].is_uninit(),
        ensures
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            zeroing_typed(&post.zeroing, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        assert forall|k: int| 0 < k < 8 implies {
            &&& (#[trigger] b.pages@[page + k]).kind is Member
            &&& b.pages@[page + k].base == page
        } by {
            b.lemma_member_of(page as int, page + k);
        }
        assert(!pre.list.pages@.dom().contains(base)) by {
            assert(table_node_page(base, 0) == base);
            assert(pre.blocks.pages@[page + 0int].kind is Free);
        }
        Self::lemma_table_page_caps_wf(pre, post);
        Self::lemma_table_page_list_pages_used(pre, post, base, page);
        lemma_holders_small_typed(&pre.list, &pre.tables, a, b, &pre.zeroing, pre.holders@, page, 3);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, b, &pre.zeroing, pre.holders@);
        assert forall|br: BlockRef| #[trigger] pre.holders@.contains_key(br) implies block_typed(a, br) by {}
        lemma_objects_small_typed(&pre.tables, &post.tables, a, b, pre.holders@, page, 8);
        lemma_leaf_blocks_small_typed(&pre.list, &pre.tables, a, b, pre.holders@, page, 8);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            lemma_leaf_page(l);
            assert(page_of(l) == l);
            assert(pre.list.valid(l));
        }
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &pre.tables, b);
        Self::lemma_table_page_pages(pre, post, base, page);
    }

    /// The list's pages after a table page's retype: those it held lie outside the new block, and the
    /// new block's first five are its base and members.
    proof fn lemma_table_page_list_pages_used(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            post.blocks.wf(),
            base % 32768 == 0,
            base / 4096 == page,
            page + 8 <= NUM_PAGES,
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| 0 <= i < NUM_PAGES && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TablePage,
            post.blocks.pages@[page as int].order == 3,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) ==> pre.list.pages@.dom().contains(p)
                || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k),
        ensures
            list_pages_used(&post.list, &post.blocks),
    {
        let b = &post.blocks;
        lemma_list_pages_used_small_typed(&pre.list, &pre.blocks, b, page, 8);
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
            &&& !(b.pages@[(p / 4096) as int].kind is Free)
            &&& b.pages@[(p / 4096) as int].kind is Member
                ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
            &&& !(b.pages@[(p / 4096) as int].object is Frame)
        } by {
            if !pre.list.pages@.dom().contains(p) {
                let k = choose|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k);
                lemma_table_node_page(base, k);
                assert(p / 4096 == page + k);
                if k != 0 {
                    b.lemma_member_of(page as int, page + k);
                }
            }
        }
    }

    /// The table pages after a table page's retype: the new one has what its block gave, and every other
    /// lay outside the block, keeps its node and keeps its permissions, since no spare page is shared.
    proof fn lemma_table_page_pages(pre: Self, post: Self, base: usize, page: usize)
        requires
            Self::table_page_step(pre, post),
            base % 32768 == 0,
            base / 4096 == page,
            page * 4096 == base,
            page + 8 <= NUM_PAGES,
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| 0 <= i < NUM_PAGES && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TablePage,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).kind is Member,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|k: usize| k < TABLE_NODE_PAGES ==> post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            !pre.list.pages@.dom().contains(base),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]),
            post.table_pages.maps@[base].addr() == base + TABLE_NODE_PAGES * 4096,
            post.table_pages.maps@[base].is_init(),
            post.table_pages.maps@[base].value().wf(),
            post.table_pages.spare@ == pre.table_pages.spare@
                .insert((base + 6 * 4096) as usize, post.table_pages.spare@[(base + 6 * 4096) as usize])
                .insert((base + 7 * 4096) as usize, post.table_pages.spare@[(base + 7 * 4096) as usize]),
            post.table_pages.spare@[(base + 6 * 4096) as usize].addr() == base + 6 * 4096,
            post.table_pages.spare@[(base + 7 * 4096) as usize].addr() == base + 7 * 4096,
            post.table_pages.spare@[(base + 6 * 4096) as usize].is_uninit(),
            post.table_pages.spare@[(base + 7 * 4096) as usize].is_uninit(),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let pa = &pre.table_pages;
        let pb = &post.table_pages;
        lemma_table_pages_small_typed(&pre.list, pa, a, b, page, 8);
        assert forall|t: usize| #[trigger] pb.maps@.contains_key(t) implies table_page_wf(&post.list, pb, b, t) by {
            if t == base {
                assert(table_page_wf(&post.list, pb, b, base));
            } else {
                assert(pa.maps@.contains_key(t));
                assert(table_page_wf(&pre.list, pa, b, t));
                pre.lemma_table_page_valid(t);
                assert(t != base);
                lemma_table_pages_apart(t, base);
                lemma_table_pages_apart(base, t);
                assert(pb.maps@[t] == pa.maps@[t]);
                assert(pb.spare@[(t + 6 * 4096) as usize] == pa.spare@[(t + 6 * 4096) as usize]);
                assert(pb.spare@[(t + 7 * 4096) as usize] == pa.spare@[(t + 7 * 4096) as usize]);
                assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
                    assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
                }
            }
        }
        assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x) implies pb.maps@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert((x * 4096) as usize == base);
            } else if page < x < page + 8 {
                assert(b.pages@[page + (x - page)].kind is Member);
            } else {
                assert(pa.maps@.contains_key((x * 4096) as usize));
            }
        }
    }

    /// The kth node page of the block at `page` is free and so not the list's.
    proof fn lemma_table_page_free_list(&self, base: usize, page: usize, k: usize)
        requires
            self.wf(),
            base % 32768 == 0,
            base / 4096 == page,
            page + 8 <= NUM_PAGES,
            k < 8,
            self.blocks.pages@[page + k].kind is Free,
        ensures
            !self.list.pages@.dom().contains(table_node_page(base, k)),
            table_node_page(base, k) % 4096 == 0,
            table_node_page(base, k) == base + k * 4096,
    {
        lemma_table_node_page(base, k);
    }

    /// Retypes the free order-3 block at `base` as a table page, under the untyped at index `from` of the
    /// table at `root`. All of these come from user space, and a refusal changes nothing.
    pub fn retype_table_page(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).can_retype_under(root, from, base, 3),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& old(self).blocks.pages@[(base / 4096) as int].kind is Free
                &&& final(self).table_pages.maps@.contains_key(base)
                &&& forall|i: usize| i < 512 ==> #[trigger] final(self).table_pages.maps@[base].value()[i].is_empty()
                &&& final(self).blocks.pages@[(base / 4096) as int].refs == 1
                &&& forall|k: usize| k < TABLE_NODE_PAGES ==> final(self).list.pages@.dom().contains(#[trigger] table_node_page(base, k))
                &&& final(self).list.is_child(parent, base)
                &&& final(self).list.nodes@[base as int].kind is Hidden
                &&& forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base })
            },
    {
        let ghost pre = *old(self);
        let parent = match self.retype_parent(root, from, base, 3) {
            Some(found) => found,
            None => { return false; },
        };
        if base / 4096 >= NUM_PAGES - 7 {
            return false;
        }
        let page = base / 4096;
        proof {
            lemma2_to64();
            assert(block_bytes(3) == 32768);
            assert(base % 32768 == 0);
            lemma_table_page_base(base, page);
        }
        let Tracked(perms) = match self.blocks.try_type(page, 3, ObjectType::TablePage) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let ghost all = perms;
        let tracked first;
        let tracked second;
        let tracked third;
        let tracked fourth;
        let tracked fifth;
        let tracked table;
        let tracked sixth;
        let tracked seventh;
        proof {
            assert forall|k: usize| k < 8 implies #[trigger] holds(all, (page + k) as usize) by {
                assert(all[(page + k) as usize].addr() == (page + k) * 4096);
            }
            assert(holds(all, (page + 0) as usize));
            assert(holds(all, (page + 1) as usize));
            assert(holds(all, (page + 2) as usize));
            assert(holds(all, (page + 3) as usize));
            assert(holds(all, (page + 4) as usize));
            assert(holds(all, (page + 5) as usize));
            assert(holds(all, (page + 6) as usize));
            assert(holds(all, (page + 7) as usize));
            first = perms.tracked_remove(page);
            second = perms.tracked_remove((page + 1) as usize);
            third = perms.tracked_remove((page + 2) as usize);
            fourth = perms.tracked_remove((page + 3) as usize);
            fifth = perms.tracked_remove((page + 4) as usize);
            table = perms.tracked_remove((page + 5) as usize);
            sixth = perms.tracked_remove((page + 6) as usize);
            seventh = perms.tracked_remove((page + 7) as usize);
            assert forall|k: usize| k < 8 implies !pre.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
                && table_node_page(base, k) % 4096 == 0 && table_node_page(base, k) == base + k * 4096 by {
                assert(pre.blocks.pages@[page + k].kind is Free);
                pre.lemma_table_page_free_list(base, page, k);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot_bound(parent);
        }
        let ghost l0 = self.list;
        let nodes = init_node_page(base, Tracked(first));
        proof {
            assert(table_node_page(base, 0) == base);
        }
        self.list.add_page(base, nodes);
        let ghost l1 = self.list;
        let nodes = init_node_page(base + 4096, Tracked(second));
        proof {
            assert(table_node_page(base, 1) == base + 4096);
            assert(list_grown(l0, l1));
            assert(l1.valid(base));
            assert(!l1.nodes@[base as int].live);
        }
        self.list.add_page(base + 4096, nodes);
        let ghost l2 = self.list;
        let nodes = init_node_page(base + 2 * 4096, Tracked(third));
        proof {
            assert(table_node_page(base, 2) == base + 2 * 4096);
            assert(list_grown(l1, l2));
            lemma_list_grown_trans(l0, l1, l2);
        }
        self.list.add_page(base + 2 * 4096, nodes);
        let ghost l3 = self.list;
        let nodes = init_node_page(base + 3 * 4096, Tracked(fourth));
        proof {
            assert(table_node_page(base, 3) == base + 3 * 4096);
            assert(list_grown(l2, l3));
            lemma_list_grown_trans(l0, l2, l3);
        }
        self.list.add_page(base + 3 * 4096, nodes);
        let ghost l4 = self.list;
        let nodes = init_node_page(base + 4 * 4096, Tracked(fifth));
        proof {
            assert(table_node_page(base, 4) == base + 4 * 4096);
            assert(list_grown(l3, l4));
            lemma_list_grown_trans(l0, l3, l4);
        }
        self.list.add_page(base + 4 * 4096, nodes);
        let ghost mid = self.list;
        proof {
            assert(list_grown(l4, mid));
            lemma_list_grown_trans(l0, l4, mid);
            assert(l1.valid(base) && !l1.nodes@[base as int].live);
            assert(mid.valid(base) && !mid.nodes@[base as int].live);
            mid.lemma_seq_fits();
            assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]);
        }
        self.list.derive(parent, base, NodeKind::Hidden);
        let (_, Tracked(map)) = page_perm_to_page_map(base + TABLE_NODE_PAGES * 4096, Tracked(table));
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(base, map);
            self.table_pages.spare.borrow_mut().tracked_insert((base + 6 * 4096) as usize, sixth);
            self.table_pages.spare.borrow_mut().tracked_insert((base + 7 * 4096) as usize, seventh);
        }
        proof {
            let post = *self;
            pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
            assert forall|x: usize| #[trigger] pre.list.valid(x) implies {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            } by {
                assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
                pre.list.lemma_valid_bound(x);
                assert(x != base);
            }
            assert(Self::table_page_step(pre, post));
            Self::lemma_table_page_caps_wf(pre, post);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_table_page_nodes(pre, post, mid, parent, base);
            assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) implies pre.list.pages@.dom().contains(p)
                || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k) by {
                if !pre.list.pages@.dom().contains(p) {
                    if p == base {
                        assert(p == table_node_page(base, 0));
                    } else if p == base + 4096 {
                        assert(p == table_node_page(base, 1));
                    } else if p == base + 2 * 4096 {
                        assert(p == table_node_page(base, 2));
                    } else if p == base + 3 * 4096 {
                        assert(p == table_node_page(base, 3));
                    } else {
                        assert(p == table_node_page(base, 4));
                    }
                }
            }
            assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)) by {
                if k == 0 {
                    assert(post.list.pages@.dom().contains(base));
                } else if k == 1 {
                    assert(post.list.pages@.dom().contains((base + 4096) as usize));
                } else if k == 2 {
                    assert(post.list.pages@.dom().contains((base + 2 * 4096) as usize));
                } else if k == 3 {
                    assert(post.list.pages@.dom().contains((base + 3 * 4096) as usize));
                } else {
                    assert(post.list.pages@.dom().contains((base + 4 * 4096) as usize));
                }
            }
            assert(post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]));
            Self::lemma_table_page_blocks(pre, post, base, page);
            assert(post.wf());
            Self::lemma_hidden_added_discharges(pre, post, root, parent, base);
        }
        true
    }
}

} // verus!
