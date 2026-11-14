// SPDX-License-Identifier: MIT

//! Replies as retyped objects. A reply is an order-0 block whose page holds its record: whether it
//! is dead, and the caller bound to it, none when it is made. A capability names a reply by its
//! block's base and carries no right, since holding it is what names the reply, and the capabilities
//! naming it hold its block's references. See design/ipc-with-reply-object/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
#[cfg(verus_keep_ghost)]
use crate::capability::derive::*;
#[cfg(verus_keep_ghost)]
use crate::capability::endpoint::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::retype::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::steps::Steps;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::layouts::*;
use crate::pptr::*;

/// retype_reply's bound in the step counter: typing the block. See design/one-lock-bounded-steps/.
pub const RETYPE_REPLY_STEPS: usize = 2 * SMALL_PAGES_MAX;

/// A reply capability carries no right: holding it names the reply.
pub const REPLY_RIGHTS: u32 = 0;

/// What a reply keeps in its page.
#[derive(Clone, Copy)]
pub struct ReplyRecord {
    /// Destroyed; its block waits for its references to go.
    pub dead: bool,
    /// The caller bound to it, waiting for the reply, 0 when none is.
    pub caller: usize,
}

/// A new reply's record: live, with no caller bound.
pub open spec fn fresh_reply() -> ReplyRecord {
    ReplyRecord { dead: false, caller: 0 }
}

/// A reply capability's payload.
pub open spec fn reply_of(base: usize) -> Payload {
    Payload { kind: CapKind::Reply, order: 0, rights: REPLY_RIGHTS, base, badge: 0, priority: 0 }
}

/// Each reply's record by its block's address, and the capabilities holding its block.
pub struct Replies {
    pub records: Tracked<Map<usize, PointsTo<ReplyRecord>>>,
    pub holders: Ghost<IMap<usize, Set<usize>>>,
}

impl Replies {
    pub fn new() -> (ret: Self)
        ensures
            ret.records@ == Map::<usize, PointsTo<ReplyRecord>>::empty(),
            ret.holders@ == IMap::<usize, Set<usize>>::empty(),
    {
        Replies { records: Tracked(Map::tracked_empty()), holders: Ghost(IMap::empty()) }
    }
}

/// The block at page b holds a reply.
pub open spec fn reply_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& blocks.pages@[b as int].object is Reply
}

/// Two distinct replies lie on distinct pages.
pub proof fn lemma_reply_pages_distinct(e: usize, u: usize)
    requires
        e % PAGE_SZ == 0,
        u % PAGE_SZ == 0,
        e != u,
    ensures
        e / PAGE_SZ != u / PAGE_SZ,
{
    lemma_fundamental_div_mod(e as int, PAGE_SZ as int);
    lemma_fundamental_div_mod(u as int, PAGE_SZ as int);
}

/// The reply at e has its record in its block's page. Its block's references are exactly its
/// holders, and it is dead at once when they go.
pub open spec fn reply_wf(replies: &Replies, blocks: &BlockTable, e: usize) -> bool {
    &&& e % PAGE_SZ == 0
    &&& blocks.tracks_addr(e)
    &&& replies.records@[e].addr() == e
    &&& replies.records@[e].is_init()
    &&& blocks.pages@[(e / PAGE_SZ) as int].kind is Base
    &&& blocks.pages@[(e / PAGE_SZ) as int].object is Reply
    &&& blocks.pages@[(e / PAGE_SZ) as int].order == 0
    &&& replies.holders@.contains_key(e)
    &&& replies.holders@[e].len() == blocks.pages@[(e / PAGE_SZ) as int].refs
    &&& blocks.pages@[(e / PAGE_SZ) as int].refs == 0 ==> blocks.pages@[(e / PAGE_SZ) as int].dead
}

/// Each reply is well formed, a reply's block is one of these, and the capabilities of kind
/// Reply are exactly the holders.
pub open spec fn replies_wf(list: &Tree, tables: &Tables, replies: &Replies, blocks: &BlockTable) -> bool {
    &&& forall|e: usize| #[trigger] replies.records@.contains_key(e) ==> reply_wf(replies, blocks, e)
    &&& forall|b: usize| blocks.tracks(b as int) && #[trigger] reply_block(blocks, b)
        ==> replies.records@.contains_key((b * PAGE_SZ) as usize)
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Reply ==> {
        &&& replies.records@.contains_key(tables.payload_of(n).base)
        &&& replies.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == 0
    }
    &&& forall|e: usize, n: usize| replies.records@.contains_key(e) && #[trigger] replies.holders@[e].contains(n) ==> {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Reply
        &&& tables.payload_of(n).base == e
    }
}

/// Each reply's holders after node i is renamed n.
pub open spec fn moved_reply_holders(holders: IMap<usize, Set<usize>>, i: usize, n: usize) -> IMap<usize, Set<usize>> {
    IMap::new(
        |e: usize| holders.contains_key(e),
        |e: usize| if holders[e].contains(i) { holders[e].remove(i).insert(n) } else { holders[e] },
    )
}

/// The reply capabilities of a and b are the same, saying the same.
pub open spec fn same_replies(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    &&& forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Reply ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
    &&& forall|x: usize| #[trigger] tables_a.is_cap(list_a, x) && tables_a.payload_of(x).kind is Reply ==> {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x) == tables_a.payload_of(x)
    }
}

/// The replies read nothing of the capabilities but the replies'.
pub proof fn lemma_replies_same_caps(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    replies: &Replies,
    blocks: &BlockTable,
)
    requires
        replies_wf(list_a, tables_a, replies, blocks),
        same_replies(list_a, tables_a, list_b, tables_b),
    ensures
        replies_wf(list_b, tables_b, replies, blocks),
{
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Reply implies {
        &&& replies.records@.contains_key(tables_b.payload_of(n).base)
        &&& replies.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == 0
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|e: usize, n: usize| replies.records@.contains_key(e) && #[trigger] replies.holders@[e].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Reply
        &&& tables_b.payload_of(n).base == e
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_replies_same_pages(list: &Tree, tables: &Tables, replies: &Replies, a: &BlockTable, b: &BlockTable)
    requires
        replies_wf(list, tables, replies, a),
        b.pages@ == a.pages@,
    ensures
        replies_wf(list, tables, replies, b),
{
    assert forall|e: usize| #[trigger] replies.records@.contains_key(e) implies reply_wf(replies, b, e) by {
        assert(reply_wf(replies, a, e));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] reply_block(b, x) implies replies.records@.contains_key((x * PAGE_SZ) as usize) by {
        assert(reply_block(a, x));
    }
}

/// A step that changes the count of a block that is no reply's leaves every reply's block as it
/// was.
pub proof fn lemma_replies_refs_changed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    replies: &Replies,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        replies_wf(list_a, tables_a, replies, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !(a.pages@[x as int].object is Reply),
            _ => true,
        },
        same_replies(list_a, tables_a, list_b, tables_b),
    ensures
        replies_wf(list_b, tables_b, replies, b),
{
    lemma_replies_same_caps(list_a, tables_a, list_b, tables_b, replies, a);
    assert forall|e: usize| #[trigger] replies.records@.contains_key(e) implies reply_wf(replies, b, e) by {
        assert(reply_wf(replies, a, e));
        let x = BlockRef::Small(e / PAGE_SZ);
        assert(block_typed(a, x));
        assert(x != br);
        assert(block_refs(b, x) == block_refs(a, x));
        assert(block_dead(b, x) == block_dead(a, x));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] reply_block(b, x) implies replies.records@.contains_key((x * PAGE_SZ) as usize) by {
        assert(reply_block(a, x));
    }
}

/// The replies after a free small block is typed as something that is no reply: no reply lay
/// in it, and a reply block outside it was one before.
pub proof fn lemma_replies_small_typed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    replies: &Replies,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        replies_wf(list_a, tables_a, replies, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| a.tracks(i) && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
        forall|k: int| 0 <= k < size ==> !((#[trigger] b.pages@[base + k]).object is Reply),
        same_replies(list_a, tables_a, list_b, tables_b),
    ensures
        replies_wf(list_b, tables_b, replies, b),
{
    lemma_replies_same_caps(list_a, tables_a, list_b, tables_b, replies, a);
    assert forall|e: usize| #[trigger] replies.records@.contains_key(e) implies reply_wf(replies, b, e) by {
        assert(reply_wf(replies, a, e));
        let x = (e / PAGE_SZ) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] reply_block(b, x) implies replies.records@.contains_key((x * PAGE_SZ) as usize) by {
        if base <= x < base + size {
            assert(!(b.pages@[base + (x - base)].object is Reply));
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(reply_block(a, x));
    }
}

/// No reply lies in a block of another kind: a reply's page is its own block's base.
pub proof fn lemma_replies_outside_block(list: &Tree, tables: &Tables, replies: &Replies, blocks: &BlockTable, base: usize)
    requires
        replies_wf(list, tables, replies, blocks),
        blocks.wf(),
        blocks.tracks(base as int),
        blocks.pages@[base as int].kind is Base,
        !(blocks.pages@[base as int].object is Reply),
    ensures
        forall|e: usize| #[trigger] replies.records@.contains_key(e) ==> !blocks.in_block(base as int, (e / PAGE_SZ) as int),
{
    assert forall|e: usize| #[trigger] replies.records@.contains_key(e) implies !blocks.in_block(base as int, (e / PAGE_SZ) as int) by {
        assert(reply_wf(replies, blocks, e));
        let x = (e / PAGE_SZ) as int;
        if blocks.in_block(base as int, x) && x != base {
            blocks.lemma_member_of(base as int, x);
        }
    }
}

/// The replies after a small block that is no reply's frees.
pub proof fn lemma_replies_small_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    replies: &Replies,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        replies_wf(list_a, tables_a, replies, a),
        a.wf(),
        a.tracks(base as int),
        a.pages@[base as int].kind is Base,
        !(a.pages@[base as int].object is Reply),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_replies(list_a, tables_a, list_b, tables_b),
    ensures
        replies_wf(list_b, tables_b, replies, b),
{
    lemma_replies_outside_block(list_a, tables_a, replies, a, base);
    lemma_replies_same_caps(list_a, tables_a, list_b, tables_b, replies, a);
    assert forall|e: usize| #[trigger] replies.records@.contains_key(e) implies reply_wf(replies, b, e) by {
        assert(reply_wf(replies, a, e));
        assert(!a.in_block(base as int, (e / PAGE_SZ) as int));
        assert(b.pages@[(e / PAGE_SZ) as int] == a.pages@[(e / PAGE_SZ) as int]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] reply_block(b, x) implies replies.records@.contains_key((x * PAGE_SZ) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(reply_block(a, x));
    }
}

impl CapKernel {
    /// A reply capability names a reply, whose block holds its reference, lies in no typed
    /// region and so is read as the small block at its base.
    pub proof fn lemma_reply_cap(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            self.payload_of(n).kind is Reply,
        ensures
            self.replies.records@.contains_key(self.payload_of(n).base),
            self.replies.holders@[self.payload_of(n).base].contains(n),
            self.payload_of(n).base % PAGE_SZ == 0,
            self.blocks.tracks_addr(self.payload_of(n).base),
            self.payload_of(n).order == 0,
            self.blocks.pages@[(self.payload_of(n).base / PAGE_SZ) as int].object is Reply,
            block_typed(&self.blocks, BlockRef::Small(self.payload_of(n).base / PAGE_SZ)),
            block_refs(&self.blocks, BlockRef::Small(self.payload_of(n).base / PAGE_SZ)) > 0,
            block_ref(&self.blocks, self.payload_of(n).base / PAGE_SZ) == BlockRef::Small(self.payload_of(n).base / PAGE_SZ),
    {
        let e = self.payload_of(n).base;
        assert(self.tables.is_cap(&self.list, n));
        assert(reply_wf(&self.replies, &self.blocks, e));
        if self.replies.holders@[e].len() == 0 {
            self.replies.holders@[e].lemma_len0_is_empty();
        }
        self.blocks.lemma_not_free_uncovered((e / PAGE_SZ) as int);
    }

    /// The replies after reply capability n, the only capability that changed, leaves reply e,
    /// taking its reference on the block with it.
    pub proof fn lemma_replies_holder_dropped(pre: Self, post: Self, n: usize, e: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            pre.is_cap(n),
            pre.payload_of(n).kind is Reply,
            pre.payload_of(n).base == e,
            !post.is_cap(n),
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(e / PAGE_SZ),
                (block_refs(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) - 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) || block_refs(&pre.blocks, BlockRef::Small(e / PAGE_SZ)) == 1,
            ),
            post.replies.records == pre.replies.records,
            post.replies.holders@ == pre.replies.holders@.insert(e, pre.replies.holders@[e].remove(n)),
        ensures
            replies_wf(&post.list, &post.tables, &post.replies, &post.blocks),
    {
        let ha = pre.replies.holders@;
        let hb = post.replies.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(e / PAGE_SZ);
        pre.lemma_reply_cap(n);
        assert(reply_wf(&pre.replies, a, e));
        assert(ha[e].contains(n));
        vstd::set::lemma_set_remove_len(ha[e], n);
        assert forall|u: usize| #[trigger] post.replies.records@.contains_key(u)
            implies reply_wf(&post.replies, b, u) by {
            assert(reply_wf(&pre.replies, a, u));
            if u != e {
                lemma_reply_pages_distinct(u, e);
                let x = BlockRef::Small(u / PAGE_SZ);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] reply_block(b, x)
            implies post.replies.records@.contains_key((x * PAGE_SZ) as usize) by {
            assert(reply_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Reply implies {
            &&& post.replies.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == 0
        } by {
            assert(x != n);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|u: usize, x: usize| post.replies.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Reply
            &&& post.tables.payload_of(x).base == u
        } by {
            assert(ha[u].contains(x));
            assert(pre.tables.is_cap(&pre.list, x));
            assert(x != n);
        }
    }

    /// What a reply's retype does to the block table: the free page at `page` is typed as the
    /// reply at `base`, the list gains no page, and no frame's holder changed.
    proof fn lemma_reply_blocks(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            same_mapping_nodes(&pre.list, &post.list),
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.blocks.wf(),
            base / PAGE_SZ == page,
            page * PAGE_SZ == base,
            pre.blocks.tracks(page as int),
            !pre.blocks.covered(page as int),
            pre.blocks.pages@[page as int].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && i != page ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Reply,
            post.blocks.pages@[page as int].order == 0,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child).kind is Reply,
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
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!pre.is_cap(child));
        assert(a.member_bases_wf());
        assert forall|k: int| 0 <= k < 1 implies #[trigger] a.pages@[page + k].kind is Free by {
            assert(page + k == page);
        }
        assert forall|i: int| a.tracks(i) && !(page <= i < page + 1) implies #[trigger] b.pages@[i] == a.pages@[i] by {}
        assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] a.pages@[page + k].kind is Free by {
            assert(page + k == page);
        }
        assert forall|i: int| a.tracks(i) && !(page <= i < page + order_pages(0)) implies #[trigger] b.pages@[i] == a.pages@[i] by {}
        lemma_list_pages_used_small_typed(&pre.list, a, b, page, 1);
        lemma_list_pages_used_subset(&pre.list, &post.list, b);
        lemma_holders_small_typed(&pre.list, &pre.tables, a, b, &pre.zeroing, pre.holders@, page, 0);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, b, &pre.zeroing, pre.holders@);
        assert forall|br: BlockRef| #[trigger] pre.holders@.contains_key(br) implies block_typed(a, br) by {}
        lemma_objects_small_typed(&pre.tables, &post.tables, a, b, pre.holders@, page, 1);
        lemma_leaf_blocks_small_typed(&pre.list, &pre.tables, a, b, pre.holders@, page, 1);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            lemma_leaf_page(l);
            assert(page_of(l) == l);
            assert(pre.list.valid(l));
            assert(l != child);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, b));
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, b);
        lemma_table_pages_small_typed(&pre.list, &pre.table_pages, a, b, page, 1);
        assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x)
            implies pre.table_pages.maps@.contains_key((x * PAGE_SZ) as usize) by {
            if x == page {
                assert(b.pages@[page as int].object is Reply);
            }
        }
        assert(table_pages_wf(&pre.list, &pre.table_pages, b));
        assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) implies {
            &&& post.list.nodes@[t as int].live == pre.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind == pre.list.nodes@[t as int].kind
        } by {
            pre.lemma_table_page_valid(t);
            assert(t != child);
        }
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, b);
    }

    /// The replies after a reply's retype at base: the new one has its record and holds its one
    /// capability, and every other lay outside the page and keeps its holders.
    proof fn lemma_replies_reply_added(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            base % PAGE_SZ == 0,
            base / PAGE_SZ == page,
            page * PAGE_SZ == base,
            pre.blocks.tracks(page as int),
            pre.blocks.pages@[page as int].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && i != page ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Reply,
            post.blocks.pages@[page as int].order == 0,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            post.replies.records@ == pre.replies.records@.insert(base, post.replies.records@[base]),
            post.replies.records@[base].addr() == base,
            post.replies.records@[base].is_init(),
            post.replies.holders@ == pre.replies.holders@.insert(base, set![child]),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child) == reply_of(base),
        ensures
            replies_wf(&post.list, &post.tables, &post.replies, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let ea = &pre.replies;
        let eb = &post.replies;
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!ea.records@.contains_key(base)) by {
            if ea.records@.contains_key(base) {
                assert(reply_wf(ea, a, base));
            }
        }
        assert(!pre.is_cap(child));
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), child);
        assert(set![child].len() == 1);
        assert forall|e: usize| #[trigger] eb.records@.contains_key(e) implies reply_wf(eb, b, e) by {
            if e == base {
                assert(eb.holders@[base] == set![child]);
            } else {
                assert(ea.records@.contains_key(e));
                assert(reply_wf(ea, a, e));
                lemma_reply_pages_distinct(e, base);
                assert(b.pages@[(e / PAGE_SZ) as int] == a.pages@[(e / PAGE_SZ) as int]);
                assert(eb.records@[e] == ea.records@[e]);
                assert(eb.holders@[e] == ea.holders@[e]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] reply_block(b, x) implies eb.records@.contains_key((x * PAGE_SZ) as usize) by {
            if x == page {
                assert((x * PAGE_SZ) as usize == base);
            } else {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(reply_block(a, x));
            }
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && post.tables.payload_of(n).kind is Reply implies {
            &&& eb.records@.contains_key(post.tables.payload_of(n).base)
            &&& eb.holders@[post.tables.payload_of(n).base].contains(n)
            &&& post.tables.payload_of(n).order == 0
        } by {
            if n == child {
                assert(eb.holders@[base].contains(child));
            } else {
                assert(pre.tables.is_cap(&pre.list, n));
                let e = pre.tables.payload_of(n).base;
                assert(ea.records@.contains_key(e));
                assert(e != base);
                assert(eb.holders@[e] == ea.holders@[e]);
            }
        }
        assert forall|e: usize, n: usize| eb.records@.contains_key(e) && #[trigger] eb.holders@[e].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& post.tables.payload_of(n).kind is Reply
            &&& post.tables.payload_of(n).base == e
        } by {
            if e == base {
                assert(n == child);
            } else {
                assert(ea.records@.contains_key(e));
                assert(ea.holders@[e].contains(n));
                assert(pre.tables.is_cap(&pre.list, n));
                assert(n != child);
            }
        }
    }

    /// The view of a reply's retype: one child under the untyped, naming the new reply, which no
    /// table root is, so it holds nothing.
    proof fn lemma_reply_view(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize)
        requires
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            blocked_on(&post.threads) == blocked_on(&pre.threads),
            post.frames@ == pre.frames@,
            Self::adds_cap(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(&pre.list, root, from),
            post.devices == pre.devices,
            pre.tables.has_slot(&pre.list, root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            post.payload_of(pre.tables.node_of(root, to)) == reply_of(base),
            block_within(base, 0, pre.payload_of(pre.tables.node_of(root, from))),
            !pre.tables.roots@.contains_key(base),
            Self::same_tree(pre, post),
        ensures
            post.view().holds(root, pre.tables.node_of(root, to)),
            adds_object(
                pre.view(),
                post.view(),
                root,
                pre.tables.node_of(root, from),
                pre.tables.node_of(root, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
                base,
            ),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let (a, b) = (pre.view(), post.view());
        Self::lemma_places_node_view(pre, post, root, from, root, to);
        let pp = pre.payload_of(parent);
        lemma2_to64();
        assert(block_bytes(0) == PAGE_SZ);
        assert(block_bytes(pp.order) == a.pages[parent] * PAGE_SZ);
        assert(a.covers(parent, base)) by {
            assert(a.names.contains_key(parent));
            assert(a.pages.contains_key(parent));
            assert(a.names[parent] == pp.base);
            assert(block_within(base, 0, pp));
            assert(base % PAGE_SZ == 0);
            assert(base + PAGE_SZ <= pp.base + a.pages[parent] * PAGE_SZ);
            assert(a.names[parent] <= base < a.names[parent] + a.pages[parent] * PAGE_SZ);
        }
        assert forall|x: NodeId| !#[trigger] b.held.contains((base, x)) by {
            if b.held.contains((base, x)) {
                assert(post.tables.owner@.contains_key(page_of(x)));
                pre.tables.lemma_leaf(&pre.list, page_of(x));
                assert(pre.tables.owner@[page_of(x)].0 == base);
            }
        }
        assert(b.names[child] == base);
    }

    /// Retypes the free page at `base` as a reply, under the untyped at index `from` of the table at
    /// `root`, with its capability at the empty index `to`: a record that says it is live, with no
    /// caller bound. All of these come from user space, and a refusal changes nothing.
    pub fn retype_reply(&mut self, root: usize, from: usize, to: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + RETYPE_REPLY_STEPS,
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            Self::same_tree(*old(self), *final(self)),
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).mappings == old(self).mappings,
            ret == old(self).can_retype_block(root, from, to, base, 0),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                let page = (base / PAGE_SZ) as int;
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& final(self).blocks.pages@[page].kind is Base
                &&& final(self).blocks.pages@[page].object is Reply
                &&& final(self).blocks.pages@[page].order == 0
                &&& final(self).blocks.pages@[page].refs == 1
                &&& !final(self).blocks.pages@[page].dead
                &&& forall|i: int| old(self).blocks.tracks(i) && i != page
                    ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i]
                &&& final(self).replies.records@.contains_key(base)
                &&& final(self).replies.records@[base].value() == fresh_reply()
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == reply_of(base)
                &&& final(self).list.is_child(parent, child)
                &&& final(self).list.parent@ == old(self).list.parent@.insert(child, parent)
                &&& final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1
                &&& Self::retype_keeps(*old(self), *final(self), child, page, 0, None)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base, pages: pow2(0), into: None })
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, 0) {
            Some(found) => found,
            None => { return false; },
        };
        if !self.blocks.page_tracked(base / PAGE_SZ) {
            return false;
        }
        let page = base / PAGE_SZ;
        proof {
            lemma2_to64();
            assert(base % PAGE_SZ == 0);
            assert(page * PAGE_SZ == base);
        }
        let Tracked(perms) = match self.blocks.try_type(page, 0, ObjectType::Reply, Tracked(&mut *steps)) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked mut first;
        proof {
            assert(0usize < order_pages(0));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * PAGE_SZ);
            assert((page + 0usize) as usize == page);
            first = perms.tracked_remove(page);
            // The page's permission is ours, so no table root lies there.
            if pre.tables.roots@.contains_key(base) {
                lemma_thread_block_layouts();
                first.is_distinct(self.tables.roots.borrow().tracked_borrow(base));
                pre.tables.lemma_root(base);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(parent);
            pre.lemma_slot_bound(child);
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
            pre.list.lemma_seq_fits();
        }
        let tracked mut record = page_into_reply_record(first);
        PPtr::<ReplyRecord>::from_usize(base).put(Tracked(&mut record), ReplyRecord { dead: false, caller: 0 });
        proof {
            self.replies.records.borrow_mut().tracked_insert(base, record);
        }
        let ghost mid = self.list;
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            self.tables.lemma_wf_same_pages(&mid, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: CapKind::Reply, order: 0, rights: REPLY_RIGHTS, base, badge: 0, priority: 0 },
        );
        self.replies.holders = Ghost(pre.replies.holders@.insert(base, set![child]));
        proof {
            let post = *self;
            assert(mid == pre.list);
            assert forall|x: usize| #[trigger] pre.list.valid(x) && x != child implies {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            } by {
                pre.list.lemma_valid_bound(x);
            }
            assert(Self::space_step(pre, post, child));
            assert(post.payload_of(child) == reply_of(base));
            assert(payload_wf(post.payload_of(child)));
            assert(post.is_cap(child));
            assert(REPLY_RIGHTS & 128 == 0) by (compute_only);
            Self::lemma_space_caps_wf(pre, post, child);
            Self::lemma_tlb_same(pre, post);
            assert(list_grown(pre.list, mid));
            Self::lemma_space_nodes(pre, post, mid, parent, child);
            Self::lemma_table_nodes_frame(pre, post, child, child);
            Self::lemma_space_nodes_frame(pre, post, child, child);
            lemma_mapping_nodes_grown(pre.list, mid, post.list, child, child);
            Self::lemma_reply_blocks(pre, post, base, page, child);
            assert forall|k: int| 0 <= k < 1 implies #[trigger] pre.blocks.pages@[page + k].kind is Free by {
                assert(page + k == page);
            }
            assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 1)
                implies #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i] by {}
            assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Space implies {
                &&& pre.is_cap(x)
                &&& pre.payload_of(x) == post.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] post.blocks.pages@[page + k]).object is Space) by {
                assert(page + k == page);
            }
            lemma_spaces_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] post.blocks.pages@[page + k]).object is Thread) by {
                assert(page + k == page);
            }
            lemma_threads_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] post.blocks.pages@[page + k]).object is Process) by {
                assert(page + k == page);
            }
            assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Process implies {
                &&& pre.tables.is_cap(&pre.list, x)
                &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Process implies {
                &&& post.tables.is_cap(&post.list, x)
                &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            lemma_processes_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !queue_object((#[trigger] post.blocks.pages@[page + k]).object) by {
                assert(page + k == page);
            }
            lemma_endpoints_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks, &post.blocks, page, 1);
            assert(post.replies.records@ == pre.replies.records@.insert(base, post.replies.records@[base]));
            Self::lemma_replies_reply_added(pre, post, base, page, child);
            assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
                implies post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n] by {
                pre.lemma_mapping_node(n);
            }
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
                &&& post.is_cap(x)
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
                pre.lemma_slot_bound(x);
            }
            Self::lemma_mappings_grown(pre, post, page, 0);
            assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
                implies pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x) by {
                assert(x != child);
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            Self::lemma_devices_same_caps(pre, post);
            lemma_binding_nodes_grown(pre.list, mid, post.list, child, child);
            lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
            assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
            Self::lemma_binding_parents_same_caps(pre, post);
            assert(post.wf());
            Self::lemma_bound_threads_same(pre, post);
            assert(right_bit(Right::Retype) == 8);
            Self::lemma_reply_view(pre, post, root, from, to, base);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            pre.lemma_retype_covers(root, from, base, 0);
            lemma_adds_object_discharges_retype(pre.view(), post.view(), root, parent, child, live, base, pow2(0));
            assert forall|r: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, r, i) implies {
                &&& post.tables.has_slot(&post.list, r, i)
                &&& post.tables.node_of(r, i) == pre.tables.node_of(r, i)
                &&& pre.tables.node_of(r, i) != child && !pre.list.nodes@[pre.tables.node_of(r, i) as int].live
                    ==> !post.list.nodes@[pre.tables.node_of(r, i) as int].live
            } by {
                pre.lemma_slot(r, i);
                let n = pre.tables.node_of(r, i);
                pre.lemma_slot_bound(n);
                let leaf = pre.tables.leaf(r, index_entry(i));
                assert(leaf == page_of(n));
                assert(leaf != child);
                assert(post.tables.leaf(r, index_entry(i)) == leaf);
                assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
            }
            assert forall|r: usize, e: int| pre.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES
                implies #[trigger] post.tables.leaf(r, e) == pre.tables.leaf(r, e) by {
                assert(post.tables.roots@[r] == pre.tables.roots@[r]);
            }
            assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(0))
                implies #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind by {
                assert(post.blocks.pages@[i] == pre.blocks.pages@[i]);
            }
            assert(Self::retype_keeps(pre, post, child, page as int, 0, None));
        }
        true
    }
}

} // verus!
