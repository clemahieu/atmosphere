//! The block table: what each physical page is, for the kernel that allocates nothing after boot. A
//! block is a power-of-two run of pages, aligned to its size, that goes free, typed, dead, free. The
//! entry at its base holds its order, its reference count and whether its teardown has finished. Each
//! 2M and 1G region counts the pages inside it that are not free, so that zero means every page is
//! free and a large block's freedom can be checked without walking. See the design on atmo-6x9.6.7,
//! section 6.
//!
//! Untyped authorisation is a precondition its caller proves, since capabilities live a level above.
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

use crate::array::Array;
use crate::define::*;

pub const PAGES_PER_2M: usize = 512;
pub const PAGES_PER_1G: usize = 262144;
pub const NUM_2M: usize = 4096;
pub const NUM_1G: usize = 8;

#[derive(Clone, Copy)]
pub enum PageKind {
    /// Boot kept it, or has not handed it over.
    Reserved,
    Free,
    /// The first page of a typed or dead block.
    Base,
    /// Any other page of one.
    Member,
}

#[derive(Clone, Copy)]
pub struct PageEntry {
    pub kind: PageKind,
    /// A member's block.
    pub base: usize,
    /// These four mean something only at a base.
    pub order: usize,
    pub dead: bool,
    pub torn_down: bool,
    pub refs: usize,
}

pub open spec fn small_order(order: usize) -> bool {
    order == 0 || order == 1 || order == 3
}

/// Pages in a small block.
pub open spec fn order_pages(order: usize) -> int {
    if order == 0 { 1 } else if order == 1 { 2 } else { 8 }
}

pub open spec fn region_2m(i: int) -> int { i / PAGES_PER_2M as int }

pub open spec fn region_1g(i: int) -> int { i / PAGES_PER_1G as int }

pub open spec fn free_entry() -> PageEntry {
    PageEntry { kind: PageKind::Free, base: 0, order: 0, dead: false, torn_down: false, refs: 0 }
}

/// m holds page i's permission, uninitialised. Named so that a proof can ask for one page's
/// permission from a map it has just changed.
pub open spec fn holds(m: Map<usize, PagePerm4k>, i: usize) -> bool {
    &&& m.contains_key(i)
    &&& m[i].addr() == i * 4096
    &&& m[i].is_uninit()
}

pub struct BlockTable {
    pub pages: Array<PageEntry, NUM_PAGES>,
    pub count_2m: Array<usize, NUM_2M>,
    pub count_1g: Array<usize, NUM_1G>,
    /// The permission of every free page, as bytes.
    pub free_perms: Tracked<Map<usize, PagePerm4k>>,
    /// The non-free pages of each region, which is what its count counts.
    pub in_2m: Ghost<Seq<Set<int>>>,
    pub in_1g: Ghost<Seq<Set<int>>>,
}

impl BlockTable {
    /// Each count is the size of its set, and the sets are exactly the non-free pages.
    pub open spec fn counts_wf(&self) -> bool {
        &&& self.pages.wf()
        &&& self.count_2m.wf()
        &&& self.count_1g.wf()
        &&& self.in_2m@.len() == NUM_2M
        &&& self.in_1g@.len() == NUM_1G
        &&& forall|r: int| 0 <= r < NUM_2M ==> {
            &&& (#[trigger] self.in_2m@[r]).finite()
            &&& self.in_2m@[r].len() == self.count_2m@[r]
            &&& self.in_2m@[r].subset_of(set_int_range(r * 512, (r + 1) * 512))
        }
        &&& forall|r: int| 0 <= r < NUM_1G ==> {
            &&& (#[trigger] self.in_1g@[r]).finite()
            &&& self.in_1g@[r].len() == self.count_1g@[r]
            &&& self.in_1g@[r].subset_of(set_int_range(r * 262144, (r + 1) * 262144))
        }
        &&& forall|i: int| 0 <= i < NUM_PAGES ==> {
            &&& self.in_2m@[region_2m(i)].contains(i) == !(#[trigger] self.pages@[i].kind is Free)
            &&& self.in_1g@[region_1g(i)].contains(i) == !(self.pages@[i].kind is Free)
        }
    }

    /// The table holds a permission for exactly its free pages.
    pub open spec fn free_wf(&self) -> bool {
        &&& forall|i: usize| #[trigger] self.free_perms@.contains_key(i) ==> {
            &&& i < NUM_PAGES
            &&& self.free_perms@[i].addr() == i * 4096
            &&& self.free_perms@[i].is_uninit()
        }
        &&& forall|i: usize| i < NUM_PAGES ==>
            (#[trigger] self.free_perms@.contains_key(i) == (self.pages@[i as int].kind is Free))
    }

    /// Every base is a small block, aligned and in range.
    #[verifier::opaque]
    pub open spec fn bases_wf(&self) -> bool {
        forall|i: int| 0 <= i < NUM_PAGES && (#[trigger] self.pages@[i].kind is Base) ==> {
            &&& small_order(self.pages@[i].order)
            &&& i % order_pages(self.pages@[i].order) == 0
            &&& i + order_pages(self.pages@[i].order) <= NUM_PAGES
        }
    }

    /// Every page of a base's block after the base is its member.
    #[verifier::opaque]
    pub open spec fn members_wf(&self) -> bool {
        forall|i: int, k: int| 0 <= i < NUM_PAGES && (#[trigger] self.pages@[i].kind is Base)
            && 0 < k < order_pages(self.pages@[i].order) ==> {
            &&& (#[trigger] self.pages@[i + k]).kind is Member
            &&& self.pages@[i + k].base == i
        }
    }

    /// A member's base is a base whose block covers it.
    #[verifier::opaque]
    pub open spec fn member_bases_wf(&self) -> bool {
        forall|i: int| 0 <= i < NUM_PAGES && (#[trigger] self.pages@[i].kind is Member) ==> {
            let b = self.pages@[i].base as int;
            &&& 0 <= b < NUM_PAGES
            &&& self.pages@[b].kind is Base
            &&& b < i < b + order_pages(self.pages@[b].order)
        }
    }

    /// The block structure. Its three parts are opaque: spelled out, the member clause names a
    /// page for every base and every offset, so the prover walks every block it has seen. The
    /// lemmas below reach one position each.
    pub open spec fn blocks_wf(&self) -> bool {
        &&& self.bases_wf()
        &&& self.members_wf()
        &&& self.member_bases_wf()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.counts_wf()
        &&& self.free_wf()
        &&& self.blocks_wf()
    }

    /// The pages of the block at base.
    pub open spec fn in_block(&self, base: int, i: int) -> bool {
        base <= i < base + order_pages(self.pages@[base].order)
    }

    /// A base's block is a small block, aligned and in range.
    pub proof fn lemma_base(&self, i: int)
        requires
            self.bases_wf(),
            0 <= i < NUM_PAGES,
            self.pages@[i].kind is Base,
        ensures
            small_order(self.pages@[i].order),
            i % order_pages(self.pages@[i].order) == 0,
            i + order_pages(self.pages@[i].order) <= NUM_PAGES,
    {
        reveal(BlockTable::bases_wf);
    }

    /// Every page of a base's block after the base is its member.
    pub proof fn lemma_member_of(&self, i: int, j: int)
        requires
            self.members_wf(),
            0 <= i < NUM_PAGES,
            self.pages@[i].kind is Base,
            i < j < i + order_pages(self.pages@[i].order),
        ensures
            self.pages@[j].kind is Member,
            self.pages@[j].base == i,
    {
        reveal(BlockTable::members_wf);
        assert(self.pages@[i + (j - i)].kind is Member);
        assert(i + (j - i) == j);
    }

    /// A member's base is a base whose block covers it.
    pub proof fn lemma_member(&self, i: int)
        requires
            self.member_bases_wf(),
            0 <= i < NUM_PAGES,
            self.pages@[i].kind is Member,
        ensures
            0 <= self.pages@[i].base < NUM_PAGES,
            self.pages@[self.pages@[i].base as int].kind is Base,
            self.pages@[i].base < i,
            i < self.pages@[i].base + order_pages(self.pages@[self.pages@[i].base as int].order),
    {
        reveal(BlockTable::member_bases_wf);
    }

    /// The block structure reads only each page's kind, a base's order and a member's base.
    pub open spec fn same_block(a: PageEntry, b: PageEntry) -> bool {
        &&& (a.kind is Base) == (b.kind is Base)
        &&& (a.kind is Member) == (b.kind is Member)
        &&& a.kind is Base ==> a.order == b.order
        &&& a.kind is Member ==> a.base == b.base
    }

    /// A table whose every page has the block structure of a well formed one is well formed.
    pub proof fn lemma_blocks_wf_same(pre: Self, post: Self)
        requires
            pre.blocks_wf(),
            pre.pages@.len() == NUM_PAGES,
            post.pages@.len() == NUM_PAGES,
            forall|i: int| 0 <= i < NUM_PAGES ==> Self::same_block(#[trigger] pre.pages@[i], post.pages@[i]),
        ensures
            post.blocks_wf(),
    {
        assert(post.bases_wf()) by {
            reveal(BlockTable::bases_wf);
            assert forall|b: int| 0 <= b < NUM_PAGES && (#[trigger] post.pages@[b].kind is Base) implies {
                &&& small_order(post.pages@[b].order)
                &&& b % order_pages(post.pages@[b].order) == 0
                &&& b + order_pages(post.pages@[b].order) <= NUM_PAGES
            } by {
                assert(Self::same_block(pre.pages@[b], post.pages@[b]));
                pre.lemma_base(b);
            }
        }
        assert(post.members_wf()) by {
            reveal(BlockTable::members_wf);
            assert forall|b: int, k: int| 0 <= b < NUM_PAGES && (#[trigger] post.pages@[b].kind is Base)
                && 0 < k < order_pages(post.pages@[b].order) implies {
                &&& (#[trigger] post.pages@[b + k]).kind is Member
                &&& post.pages@[b + k].base == b
            } by {
                assert(Self::same_block(pre.pages@[b], post.pages@[b]));
                pre.lemma_base(b);
                pre.lemma_member_of(b, b + k);
                assert(Self::same_block(pre.pages@[b + k], post.pages@[b + k]));
            }
        }
        assert(post.member_bases_wf()) by {
            reveal(BlockTable::member_bases_wf);
            assert forall|j: int| 0 <= j < NUM_PAGES && (#[trigger] post.pages@[j].kind is Member) implies {
                let b = post.pages@[j].base as int;
                &&& 0 <= b < NUM_PAGES
                &&& post.pages@[b].kind is Base
                &&& b < j < b + order_pages(post.pages@[b].order)
            } by {
                assert(Self::same_block(pre.pages@[j], post.pages@[j]));
                pre.lemma_member(j);
                let b = pre.pages@[j].base as int;
                assert(Self::same_block(pre.pages@[b], post.pages@[b]));
            }
        }
    }

    /// Two blocks have no page in common.
    pub proof fn lemma_blocks_disjoint(&self, a: int, b: int, i: int)
        requires
            self.wf(),
            0 <= a < NUM_PAGES,
            0 <= b < NUM_PAGES,
            a != b,
            self.pages@[a].kind is Base,
            self.pages@[b].kind is Base,
            self.in_block(a, i),
        ensures
            !self.in_block(b, i),
    {
        if self.in_block(b, i) {
            if i != a {
                self.lemma_member_of(a, i);
            }
            if i != b {
                self.lemma_member_of(b, i);
            }
        }
    }

    /// A 2M region whose count is zero has only free pages.
    pub proof fn lemma_zero_2m_is_free(&self, r: int, i: int)
        requires
            self.counts_wf(),
            0 <= r < NUM_2M,
            self.count_2m@[r] == 0,
            0 <= i < NUM_PAGES,
            region_2m(i) == r,
        ensures
            self.pages@[i].kind is Free,
    {
        self.in_2m@[r].lemma_len0_is_empty();
        assert(self.in_2m@[region_2m(i)].contains(i) == !(self.pages@[i].kind is Free));
    }

    /// A 1G region whose count is zero has only free pages.
    pub proof fn lemma_zero_1g_is_free(&self, r: int, i: int)
        requires
            self.counts_wf(),
            0 <= r < NUM_1G,
            self.count_1g@[r] == 0,
            0 <= i < NUM_PAGES,
            region_1g(i) == r,
        ensures
            self.pages@[i].kind is Free,
    {
        self.in_1g@[r].lemma_len0_is_empty();
        assert(self.in_1g@[region_1g(i)].contains(i) == !(self.pages@[i].kind is Free));
    }

    /// Set every entry Reserved, in place, since a table this size cannot move by value.
    pub fn init(&mut self)
        requires
            old(self).pages.wf(),
            old(self).count_2m.wf(),
            old(self).count_1g.wf(),
        ensures
            final(self).wf(),
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] final(self).pages@[i].kind is Reserved,
    {
        let mut i = 0;
        while i != NUM_PAGES
            invariant
                0 <= i <= NUM_PAGES,
                self.pages.wf(),
                forall|j: int| 0 <= j < i ==> #[trigger] self.pages@[j].kind is Reserved,
            decreases NUM_PAGES - i,
        {
            self.pages.set(i, PageEntry {
                kind: PageKind::Reserved,
                base: 0,
                order: 0,
                dead: false,
                torn_down: false,
                refs: 0,
            });
            i = i + 1;
        }
        let mut r = 0;
        while r != NUM_2M
            invariant
                0 <= r <= NUM_2M,
                self.count_2m.wf(),
                forall|j: int| 0 <= j < r ==> #[trigger] self.count_2m@[j] == 512,
            decreases NUM_2M - r,
        {
            self.count_2m.set(r, PAGES_PER_2M);
            r = r + 1;
        }
        let mut r = 0;
        while r != NUM_1G
            invariant
                0 <= r <= NUM_1G,
                self.count_1g.wf(),
                forall|j: int| 0 <= j < r ==> #[trigger] self.count_1g@[j] == 262144,
            decreases NUM_1G - r,
        {
            self.count_1g.set(r, PAGES_PER_1G);
            r = r + 1;
        }
        self.in_2m = Ghost(Seq::new(NUM_2M as nat, |r: int| set_int_range(r * 512, (r + 1) * 512)));
        self.in_1g = Ghost(Seq::new(NUM_1G as nat, |r: int| set_int_range(r * 262144, (r + 1) * 262144)));
        self.free_perms = Tracked(Map::tracked_empty());
        proof {
            assert forall|r: int| 0 <= r < NUM_2M implies {
                &&& (#[trigger] self.in_2m@[r]).finite()
                &&& self.in_2m@[r].len() == self.count_2m@[r]
                &&& self.in_2m@[r].subset_of(set_int_range(r * 512, (r + 1) * 512))
            } by {
                lemma_int_range(r * 512, (r + 1) * 512);
            }
            assert forall|r: int| 0 <= r < NUM_1G implies {
                &&& (#[trigger] self.in_1g@[r]).finite()
                &&& self.in_1g@[r].len() == self.count_1g@[r]
                &&& self.in_1g@[r].subset_of(set_int_range(r * 262144, (r + 1) * 262144))
            } by {
                lemma_int_range(r * 262144, (r + 1) * 262144);
            }
            assert(self.bases_wf()) by { reveal(BlockTable::bases_wf); }
            assert(self.members_wf()) by { reveal(BlockTable::members_wf); }
            assert(self.member_bases_wf()) by { reveal(BlockTable::member_bases_wf); }
        }
    }

    /// Make a non-free page free, taking back its permission.
    fn give_page(&mut self, i: usize, Tracked(perm): Tracked<PagePerm4k>)
        requires
            old(self).counts_wf(),
            old(self).free_wf(),
            i < NUM_PAGES,
            !(old(self).pages@[i as int].kind is Free),
            perm.addr() == i * 4096,
            perm.is_uninit(),
        ensures
            final(self).counts_wf(),
            final(self).free_wf(),
            final(self).pages@ == old(self).pages@.update(i as int, free_entry()),
    {
        let ghost pre = *old(self);
        let (r2, r1) = (i / PAGES_PER_2M, i / PAGES_PER_1G);
        proof {
            assert(pre.in_2m@[region_2m(i as int)].contains(i as int) == !(pre.pages@[i as int].kind is Free));
            assert(pre.in_2m@[r2 as int].contains(i as int));
            assert(pre.in_1g@[r1 as int].contains(i as int));
            assert(pre.in_2m@[r2 as int].finite());
            assert(pre.in_1g@[r1 as int].finite());
            vstd::set::lemma_set_remove_len(pre.in_2m@[r2 as int], i as int);
            vstd::set::lemma_set_remove_len(pre.in_1g@[r1 as int], i as int);
        }
        let (c2, c1) = (*self.count_2m.get(r2), *self.count_1g.get(r1));
        self.count_2m.set(r2, c2 - 1);
        self.count_1g.set(r1, c1 - 1);
        self.pages.set(i, PageEntry {
            kind: PageKind::Free,
            base: 0,
            order: 0,
            dead: false,
            torn_down: false,
            refs: 0,
        });
        self.in_2m = Ghost(pre.in_2m@.update(r2 as int, pre.in_2m@[r2 as int].remove(i as int)));
        self.in_1g = Ghost(pre.in_1g@.update(r1 as int, pre.in_1g@[r1 as int].remove(i as int)));
        proof {
            self.free_perms.borrow_mut().tracked_insert(i, perm);
            let me = *self;
            assert(me.pages@ =~= pre.pages@.update(i as int, free_entry()));
            assert forall|r: int| 0 <= r < NUM_2M implies {
                &&& (#[trigger] me.in_2m@[r]).finite()
                &&& me.in_2m@[r].len() == me.count_2m@[r]
                &&& me.in_2m@[r].subset_of(set_int_range(r * 512, (r + 1) * 512))
            } by {
                assert(pre.in_2m@[r].finite());
            }
            assert forall|r: int| 0 <= r < NUM_1G implies {
                &&& (#[trigger] me.in_1g@[r]).finite()
                &&& me.in_1g@[r].len() == me.count_1g@[r]
                &&& me.in_1g@[r].subset_of(set_int_range(r * 262144, (r + 1) * 262144))
            } by {
                assert(pre.in_1g@[r].finite());
            }
            assert forall|j: int| 0 <= j < NUM_PAGES implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == !(me.pages@[j].kind is Free)
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
        }
    }

    /// Make a free page non-free, handing out its permission.
    fn take_page(&mut self, i: usize, entry: PageEntry) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).counts_wf(),
            old(self).free_wf(),
            i < NUM_PAGES,
            old(self).pages@[i as int].kind is Free,
            !(entry.kind is Free),
        ensures
            final(self).counts_wf(),
            final(self).free_wf(),
            final(self).pages@ == old(self).pages@.update(i as int, entry),
            ret@.addr() == i * 4096,
            ret@.is_uninit(),
    {
        let ghost pre = *old(self);
        let (r2, r1) = (i / PAGES_PER_2M, i / PAGES_PER_1G);
        proof {
            assert(pre.in_2m@[region_2m(i as int)].contains(i as int) == !(pre.pages@[i as int].kind is Free));
            assert(!pre.in_2m@[r2 as int].contains(i as int));
            assert(!pre.in_1g@[r1 as int].contains(i as int));
            assert(pre.in_2m@[r2 as int].finite());
            assert(pre.in_1g@[r1 as int].finite());
            lemma_int_range(r2 * 512, (r2 + 1) * 512);
            lemma_int_range(r1 * 262144, (r1 + 1) * 262144);
            lemma_len_subset(pre.in_2m@[r2 as int], set_int_range(r2 * 512, (r2 + 1) * 512));
            lemma_len_subset(pre.in_1g@[r1 as int], set_int_range(r1 * 262144, (r1 + 1) * 262144));
            vstd::set::lemma_set_insert_len(pre.in_2m@[r2 as int], i as int);
            vstd::set::lemma_set_insert_len(pre.in_1g@[r1 as int], i as int);
        }
        let (c2, c1) = (*self.count_2m.get(r2), *self.count_1g.get(r1));
        self.count_2m.set(r2, c2 + 1);
        self.count_1g.set(r1, c1 + 1);
        self.pages.set(i, entry);
        self.in_2m = Ghost(pre.in_2m@.update(r2 as int, pre.in_2m@[r2 as int].insert(i as int)));
        self.in_1g = Ghost(pre.in_1g@.update(r1 as int, pre.in_1g@[r1 as int].insert(i as int)));
        let tracked perm;
        proof {
            assert(pre.free_perms@.contains_key(i));
            perm = self.free_perms.borrow_mut().tracked_remove(i);
            let me = *self;
            assert(me.pages@ =~= pre.pages@.update(i as int, entry));
            assert forall|r: int| 0 <= r < NUM_2M implies {
                &&& (#[trigger] me.in_2m@[r]).finite()
                &&& me.in_2m@[r].len() == me.count_2m@[r]
                &&& me.in_2m@[r].subset_of(set_int_range(r * 512, (r + 1) * 512))
            } by {
                assert(pre.in_2m@[r].finite());
            }
            assert forall|r: int| 0 <= r < NUM_1G implies {
                &&& (#[trigger] me.in_1g@[r]).finite()
                &&& me.in_1g@[r].len() == me.count_1g@[r]
                &&& me.in_1g@[r].subset_of(set_int_range(r * 262144, (r + 1) * 262144))
            } by {
                assert(pre.in_1g@[r].finite());
            }
            assert forall|j: int| 0 <= j < NUM_PAGES implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == !(me.pages@[j].kind is Free)
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
        }
        Tracked(perm)
    }

    /// Boot hands a reserved page to the table.
    pub fn add_free(&mut self, i: usize, Tracked(perm): Tracked<PagePerm4k>)
        requires
            old(self).wf(),
            i < NUM_PAGES,
            old(self).pages@[i as int].kind is Reserved,
            perm.addr() == i * 4096,
            perm.is_uninit(),
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(i as int, free_entry()),
    {
        let ghost pre = *old(self);
        self.give_page(i, Tracked(perm));
        proof {
            let me = *self;
            assert forall|j: int| 0 <= j < NUM_PAGES
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// Type a free block. Checks every page, at most 8, and on success holds one reference for the
    /// caller and hands back the permission of each page.
    pub fn try_type(&mut self, base: usize, order: usize) -> (ret: Option<Tracked<Map<usize, PagePerm4k>>>)
        requires
            old(self).wf(),
            small_order(order),
            base % (order_pages(order) as usize) == 0,
            base + order_pages(order) <= NUM_PAGES,
        ensures
            final(self).wf(),
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> {
                &&& forall|k: int| 0 <= k < order_pages(order)
                    ==> #[trigger] old(self).pages@[base + k].kind is Free
                &&& final(self).pages@[base as int].kind is Base
                &&& final(self).pages@[base as int].order == order
                &&& final(self).pages@[base as int].refs == 1
                &&& !final(self).pages@[base as int].dead
                &&& !final(self).pages@[base as int].torn_down
                &&& forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + order_pages(order))
                    ==> #[trigger] final(self).pages@[i] == old(self).pages@[i]
                &&& forall|k: usize| k < order_pages(order) ==> {
                    &&& ret->0@.contains_key((base + k) as usize)
                    &&& #[trigger] ret->0@[(base + k) as usize].addr() == (base + k) * 4096
                    &&& ret->0@[(base + k) as usize].is_uninit()
                }
            },
    {
        let ghost pre = *old(self);
        let size: usize = if order == 0 { 1 } else if order == 1 { 2 } else { 8 };
        let mut k = 0;
        while k != size
            invariant
                self.wf(),
                *self == pre,
                size as int == order_pages(order),
                0 <= k <= size,
                base + size <= NUM_PAGES,
                forall|j: int| 0 <= j < k ==> #[trigger] pre.pages@[base + j].kind is Free,
            decreases size - k,
        {
            match self.pages.get(base + k).kind {
                PageKind::Free => {},
                _ => return None,
            }
            k = k + 1;
        }
        let tracked mut taken = Map::<usize, PagePerm4k>::tracked_empty();
        let mut k = 0;
        while k != size
            invariant
                self.counts_wf(),
                self.free_wf(),
                size as int == order_pages(order),
                small_order(order),
                0 <= k <= size,
                base + size <= NUM_PAGES,
                forall|j: int| k <= j < size ==> #[trigger] self.pages@[base + j].kind is Free,
                forall|j: int| 0 <= j < size ==> #[trigger] pre.pages@[base + j].kind is Free,
                forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + size)
                    ==> #[trigger] self.pages@[i] == pre.pages@[i],
                k > 0 ==> self.pages@[base as int] == (PageEntry {
                    kind: PageKind::Base, base, order, dead: false, torn_down: false, refs: 1,
                }),
                forall|j: int| 0 < j < k ==> {
                    &&& (#[trigger] self.pages@[base + j]).kind is Member
                    &&& self.pages@[base + j].base == base
                },
                forall|j: usize| j < k ==> #[trigger] holds(taken, (base + j) as usize),
            decreases size - k,
        {
            let entry = if k == 0 {
                PageEntry { kind: PageKind::Base, base, order, dead: false, torn_down: false, refs: 1 }
            } else {
                PageEntry { kind: PageKind::Member, base, order: 0, dead: false, torn_down: false, refs: 0 }
            };
            let Tracked(perm) = self.take_page(base + k, entry);
            let ghost t0 = taken;
            proof {
                taken.tracked_insert((base + k) as usize, perm);
                assert forall|j: usize| j < k + 1 implies #[trigger] holds(taken, (base + j) as usize) by {
                    if j < k {
                        assert(holds(t0, (base + j) as usize));
                    }
                }
            }
            k = k + 1;
        }
        proof {
            self.lemma_typed_blocks_wf(pre, base as int, order);
        }
        let ghost t = taken;
        let ret = Some(Tracked(taken));
        proof {
            assert(ret->0@ == t);
            assert forall|j: usize| j < order_pages(order)
                implies #[trigger] ret->0@.contains_key((base + j) as usize) by {
                assert(holds(t, (base + j) as usize));
            }
            assert forall|j: usize| j < order_pages(order) implies {
                &&& (#[trigger] ret->0@[(base + j) as usize]).addr() == (base + j) * 4096
                &&& ret->0@[(base + j) as usize].is_uninit()
            } by {
                assert(holds(t, (base + j) as usize));
            }
        }
        ret
    }

    /// Typing a free block keeps the block structure.
    proof fn lemma_typed_blocks_wf(&self, pre: Self, base: int, order: usize)
        requires
            pre.blocks_wf(),
            pre.pages@.len() == NUM_PAGES,
            self.pages@.len() == NUM_PAGES,
            small_order(order),
            base % order_pages(order) == 0,
            0 <= base,
            base + order_pages(order) <= NUM_PAGES,
            self.pages@[base].kind is Base,
            self.pages@[base].order == order,
            forall|j: int| 0 <= j < order_pages(order) ==> #[trigger] pre.pages@[base + j].kind is Free,
            forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + order_pages(order))
                ==> #[trigger] self.pages@[i] == pre.pages@[i],
            forall|j: int| 0 < j < order_pages(order) ==> {
                &&& (#[trigger] self.pages@[base + j]).kind is Member
                &&& self.pages@[base + j].base == base
            },
        ensures
            self.blocks_wf(),
    {
        let size = order_pages(order);
        assert(self.bases_wf()) by {
            reveal(BlockTable::bases_wf);
            assert forall|b: int| 0 <= b < NUM_PAGES && (#[trigger] self.pages@[b].kind is Base) implies {
                &&& small_order(self.pages@[b].order)
                &&& b % order_pages(self.pages@[b].order) == 0
                &&& b + order_pages(self.pages@[b].order) <= NUM_PAGES
            } by {
                if b == base {
                } else if base < b < base + size {
                    assert(self.pages@[base + (b - base)].kind is Member);
                    assert(base + (b - base) == b);
                } else {
                    pre.lemma_base(b);
                }
            }
        }
        assert(self.members_wf()) by {
            reveal(BlockTable::members_wf);
            assert forall|b: int, k: int| 0 <= b < NUM_PAGES && (#[trigger] self.pages@[b].kind is Base)
                && 0 < k < order_pages(self.pages@[b].order) implies {
                &&& (#[trigger] self.pages@[b + k]).kind is Member
                &&& self.pages@[b + k].base == b
            } by {
                if b == base {
                } else if base < b < base + size {
                    assert(self.pages@[base + (b - base)].kind is Member);
                    assert(base + (b - base) == b);
                } else {
                    pre.lemma_base(b);
                    pre.lemma_member_of(b, b + k);
                    if base <= b + k < base + size {
                        assert(pre.pages@[base + (b + k - base)].kind is Free);
                        assert(base + (b + k - base) == b + k);
                    }
                }
            }
        }
        assert(self.member_bases_wf()) by {
            reveal(BlockTable::member_bases_wf);
            assert forall|j: int| 0 <= j < NUM_PAGES && (#[trigger] self.pages@[j].kind is Member) implies {
                let b = self.pages@[j].base as int;
                &&& 0 <= b < NUM_PAGES
                &&& self.pages@[b].kind is Base
                &&& b < j < b + order_pages(self.pages@[b].order)
            } by {
                if base <= j < base + size {
                    if j == base {
                    } else {
                        assert(self.pages@[base + (j - base)].base == base);
                        assert(base + (j - base) == j);
                    }
                } else {
                    pre.lemma_member(j);
                    let b = pre.pages@[j].base as int;
                    if base <= b < base + size {
                        assert(pre.pages@[base + (b - base)].kind is Free);
                        assert(base + (b - base) == b);
                    }
                }
            }
        }
    }

    /// Set a block's reference count, dead flag or teardown flag.
    fn set_base(&mut self, base: usize, entry: PageEntry)
        requires
            old(self).wf(),
            base < NUM_PAGES,
            old(self).pages@[base as int].kind is Base,
            entry.kind is Base,
            entry.order == old(self).pages@[base as int].order,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int, entry),
    {
        let ghost pre = *old(self);
        self.pages.set(base, entry);
        proof {
            let me = *self;
            assert(me.pages@ =~= pre.pages@.update(base as int, entry));
            assert forall|j: int| 0 <= j < NUM_PAGES implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == !(me.pages@[j].kind is Free)
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|i: usize| i < NUM_PAGES implies
                (#[trigger] me.free_perms@.contains_key(i) == (me.pages@[i as int].kind is Free)) by {
                assert(pre.free_perms@.contains_key(i) == (pre.pages@[i as int].kind is Free));
            }
            assert forall|j: int| 0 <= j < NUM_PAGES
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// Mark a block dead.
    pub fn mark_dead(&mut self, base: usize)
        requires
            old(self).wf(),
            base < NUM_PAGES,
            old(self).pages@[base as int].kind is Base,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { dead: true, ..old(self).pages@[base as int] }),
    {
        let e = *self.pages.get(base);
        self.set_base(base, PageEntry { dead: true, ..e });
    }

    /// Record that a dead block's teardown has finished.
    pub fn mark_torn_down(&mut self, base: usize)
        requires
            old(self).wf(),
            base < NUM_PAGES,
            old(self).pages@[base as int].kind is Base,
            old(self).pages@[base as int].dead,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { torn_down: true, ..old(self).pages@[base as int] }),
    {
        let e = *self.pages.get(base);
        self.set_base(base, PageEntry { torn_down: true, ..e });
    }

    /// Add a reference, unless the count is full.
    pub fn add_ref(&mut self, base: usize) -> (added: bool)
        requires
            old(self).wf(),
            base < NUM_PAGES,
            old(self).pages@[base as int].kind is Base,
        ensures
            final(self).wf(),
            added ==> final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { refs: (old(self).pages@[base as int].refs + 1) as usize, ..old(self).pages@[base as int] }),
            !added ==> *final(self) == *old(self),
    {
        let e = *self.pages.get(base);
        if e.refs == usize::MAX {
            return false;
        }
        self.set_base(base, PageEntry { refs: e.refs + 1, ..e });
        true
    }

    /// Drop a reference. The caller marks the block dead when this reaches zero.
    pub fn drop_ref(&mut self, base: usize)
        requires
            old(self).wf(),
            base < NUM_PAGES,
            old(self).pages@[base as int].kind is Base,
            old(self).pages@[base as int].refs > 0,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { refs: (old(self).pages@[base as int].refs - 1) as usize, ..old(self).pages@[base as int] }),
    {
        let e = *self.pages.get(base);
        self.set_base(base, PageEntry { refs: e.refs - 1, ..e });
    }

    /// A dead block at zero references whose teardown has finished returns to free, with its
    /// permissions.
    pub fn free_block(&mut self, base: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            base < NUM_PAGES,
            old(self).pages@[base as int].kind is Base,
            old(self).pages@[base as int].dead,
            old(self).pages@[base as int].torn_down,
            old(self).pages@[base as int].refs == 0,
            forall|k: usize| k < order_pages(old(self).pages@[base as int].order) ==> {
                &&& perms.contains_key((base + k) as usize)
                &&& #[trigger] perms[(base + k) as usize].addr() == (base + k) * 4096
                &&& perms[(base + k) as usize].is_uninit()
            },
        ensures
            final(self).wf(),
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] final(self).pages@[i] == (
                if old(self).in_block(base as int, i) { free_entry() } else { old(self).pages@[i] }),
    {
        let ghost pre = *old(self);
        let order = self.pages.get(base).order;
        let size: usize = if order == 0 { 1 } else if order == 1 { 2 } else { 8 };
        let tracked mut perms = perms;
        proof {
            pre.lemma_base(base as int);
            assert forall|j: usize| j < size implies #[trigger] holds(perms, (base + j) as usize) by {
                assert(perms[(base + j) as usize].addr() == (base + j) * 4096);
            }
        }
        let mut k = 0;
        while k != size
            invariant
                self.counts_wf(),
                self.free_wf(),
                pre.wf(),
                size as int == order_pages(order),
                order == pre.pages@[base as int].order,
                pre.pages@[base as int].kind is Base,
                0 <= k <= size,
                base < NUM_PAGES,
                base + size <= NUM_PAGES,
                forall|j: int| 0 <= j < k ==> #[trigger] self.pages@[base + j] == free_entry(),
                forall|j: int| k <= j < size ==> #[trigger] self.pages@[base + j] == pre.pages@[base + j],
                forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + size)
                    ==> #[trigger] self.pages@[i] == pre.pages@[i],
                forall|j: usize| k <= j < size ==> #[trigger] holds(perms, (base + j) as usize),
            decreases size - k,
        {
            let tracked perm;
            let ghost p0 = perms;
            proof {
                assert(pre.pages@[base + k] == self.pages@[base + k]);
                if k > 0 {
                    pre.lemma_member_of(base as int, base + k);
                }
                assert(holds(perms, (base + k) as usize));
                perm = perms.tracked_remove((base + k) as usize);
            }
            self.give_page(base + k, Tracked(perm));
            proof {
                assert forall|j: usize| k + 1 <= j < size implies #[trigger] holds(perms, (base + j) as usize) by {
                    assert(holds(p0, (base + j) as usize));
                }
            }
            k = k + 1;
        }
        proof {
            let me = *self;
            assert forall|i: int| 0 <= i < NUM_PAGES implies #[trigger] me.pages@[i] == (
                if pre.in_block(base as int, i) { free_entry() } else { pre.pages@[i] }) by {
                if pre.in_block(base as int, i) {
                    assert(me.pages@[base + (i - base)] == free_entry());
                    assert(base + (i - base) == i);
                }
            }
            self.lemma_freed_blocks_wf(pre, base as int);
        }
    }

    /// Freeing a whole block keeps the block structure.
    proof fn lemma_freed_blocks_wf(&self, pre: Self, base: int)
        requires
            pre.blocks_wf(),
            pre.pages@.len() == NUM_PAGES,
            self.pages@.len() == NUM_PAGES,
            0 <= base < NUM_PAGES,
            pre.pages@[base].kind is Base,
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] self.pages@[i] == (
                if pre.in_block(base, i) { free_entry() } else { pre.pages@[i] }),
        ensures
            self.blocks_wf(),
    {
        assert(self.bases_wf()) by {
            reveal(BlockTable::bases_wf);
            assert forall|b: int| 0 <= b < NUM_PAGES && (#[trigger] self.pages@[b].kind is Base) implies {
                &&& small_order(self.pages@[b].order)
                &&& b % order_pages(self.pages@[b].order) == 0
                &&& b + order_pages(self.pages@[b].order) <= NUM_PAGES
            } by {
                pre.lemma_base(b);
            }
        }
        assert(self.members_wf()) by {
            reveal(BlockTable::members_wf);
            assert forall|b: int, k: int| 0 <= b < NUM_PAGES && (#[trigger] self.pages@[b].kind is Base)
                && 0 < k < order_pages(self.pages@[b].order) implies {
                &&& (#[trigger] self.pages@[b + k]).kind is Member
                &&& self.pages@[b + k].base == b
            } by {
                pre.lemma_base(b);
                pre.lemma_member_of(b, b + k);
                if pre.in_block(base, b + k) && b + k != base {
                    pre.lemma_member_of(base, b + k);
                }
            }
        }
        assert(self.member_bases_wf()) by {
            reveal(BlockTable::member_bases_wf);
            assert forall|j: int| 0 <= j < NUM_PAGES && (#[trigger] self.pages@[j].kind is Member) implies {
                let b = self.pages@[j].base as int;
                &&& 0 <= b < NUM_PAGES
                &&& self.pages@[b].kind is Base
                &&& b < j < b + order_pages(self.pages@[b].order)
            } by {
                pre.lemma_member(j);
                let b = pre.pages@[j].base as int;
                if pre.in_block(base, b) && b != base {
                    pre.lemma_member_of(base, b);
                }
            }
        }
    }
}

} // verus!
