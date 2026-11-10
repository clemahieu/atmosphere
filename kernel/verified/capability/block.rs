//! The block table: what each physical page is, for the kernel that allocates nothing after boot. A
//! block is a power-of-two run of pages, aligned to its size, that goes free, typed, dead, free. The
//! entry at its base holds its order, its reference count and whether its teardown has finished. Each
//! 2M and 1G region counts what is not free inside it, so that zero means all of it is free. A large
//! block cannot write its page entries in a bounded step, so its state is in its region's entry, its
//! pages' entries stay Free, and a page is free only if neither region above it is typed. See
//! design/teardown-driven-by-retype/.
//!
//! Untyped authorisation is a precondition its caller proves, since capabilities live a level above.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::set_lib::*;

verus! {

use crate::array::Array;
use crate::define::*;
use crate::capability::steps::Steps;

pub const PAGES_PER_2M: usize = 512;
pub const PAGES_PER_1G: usize = 262144;
pub const NUM_2M: usize = 2048;
pub const NUM_1G: usize = 4;

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

/// What a small block was typed as, so a retype naming it knows what it is. Only a base has one.
#[derive(Clone, Copy)]
pub enum ObjectType {
    None,
    Frame,
    TableLeaf,
    TablePage,
    Space,
    Thread,
    Process,
}

#[derive(Clone, Copy)]
pub struct PageEntry {
    pub kind: PageKind,
    pub object: ObjectType,
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

/// The most pages a small block has.
pub const SMALL_PAGES_MAX: usize = 8;

/// Pages in a small block.
pub open spec fn order_pages(order: usize) -> int {
    if order == 0 { 1 } else if order == 1 { 2 } else { 8 }
}

pub open spec fn region_2m(i: int) -> int { i / PAGES_PER_2M as int }

pub open spec fn region_1g(i: int) -> int { i / PAGES_PER_1G as int }

pub open spec fn free_entry() -> PageEntry {
    PageEntry { kind: PageKind::Free, object: ObjectType::None, base: 0, order: 0, dead: false, torn_down: false, refs: 0 }
}

/// m holds page i's permission, uninitialised. Named so that a proof can ask for one page's
/// permission from a map it has just changed.
pub open spec fn holds(m: Map<usize, PagePerm4k>, i: usize) -> bool {
    &&& m.contains_key(i)
    &&& m[i].addr() == i * 4096
    &&& m[i].is_uninit()
}

/// The state of a 2M or 1G block, held by the region that is that block.
#[derive(Clone, Copy)]
pub struct RegionEntry {
    pub typed: bool,
    pub dead: bool,
    pub torn_down: bool,
    pub refs: usize,
}

/// Which level of region a large block is.
#[derive(Clone, Copy)]
pub enum Large {
    Two,
    One,
}

pub struct BlockTable {
    pub pages: Array<PageEntry, NUM_PAGES>,
    pub regions_2m: Array<RegionEntry, NUM_2M>,
    pub regions_1g: Array<RegionEntry, NUM_1G>,
    pub count_2m: Array<usize, NUM_2M>,
    pub count_1g: Array<usize, NUM_1G>,
    /// The permission of every free page, as bytes.
    pub free_perms: Tracked<Map<usize, PagePerm4k>>,
    /// What each region's count counts: its non-free pages, and for a 1G region, the base page of
    /// each typed 2M block inside it.
    pub in_2m: Ghost<Seq<Set<int>>>,
    pub in_1g: Ghost<Seq<Set<int>>>,
}

impl BlockTable {
    /// How many pages the table tracks. Every bound on a page index or a page's address is stated
    /// through this and the predicates below, so that where the count comes from is decided here.
    pub open spec fn spec_page_count(&self) -> usize {
        NUM_PAGES
    }

    #[verifier::when_used_as_spec(spec_page_count)]
    pub fn page_count(&self) -> (n: usize)
        ensures
            n == self.page_count(),
    {
        NUM_PAGES
    }

    /// Page i is one the table tracks.
    pub open spec fn tracks(&self, i: int) -> bool {
        0 <= i < NUM_PAGES
    }

    /// The n pages from page s end within the tracked pages.
    pub open spec fn tracks_run(&self, s: int, n: int) -> bool {
        s + n <= NUM_PAGES
    }

    /// Address a is in a page the table tracks.
    pub open spec fn tracks_addr(&self, a: usize) -> bool {
        a / PAGE_SZ_4K < NUM_PAGES
    }

    /// The n pages from the one holding address a end within the tracked pages.
    pub open spec fn tracks_addr_run(&self, a: usize, n: int) -> bool {
        a / PAGE_SZ_4K + n <= NUM_PAGES
    }

    /// Whether page i is one the table tracks.
    pub fn page_tracked(&self, i: usize) -> (r: bool)
        ensures
            r == self.tracks(i as int),
    {
        i < NUM_PAGES
    }

    /// Whether the n pages from page s end within the tracked pages.
    pub fn run_tracked(&self, s: usize, n: usize) -> (r: bool)
        ensures
            r == self.tracks_run(s as int, n as int),
    {
        s <= NUM_PAGES && n <= NUM_PAGES - s
    }

    /// Page i is inside a typed large block.
    pub open spec fn covered(&self, i: int) -> bool {
        self.regions_2m@[region_2m(i)].typed || self.regions_1g@[region_1g(i)].typed
    }

    /// The small block of this order at page base is free: none of its pages is typed, and no typed
    /// large block holds it.
    pub open spec fn small_free(&self, base: int, order: usize) -> bool {
        &&& !self.covered(base)
        &&& forall|k: int| 0 <= k < order_pages(order) ==> #[trigger] self.pages@[base + k].kind is Free
    }

    /// The large block that is region r of this level is free: none of its pages is typed, and no
    /// typed large block holds any of them.
    pub open spec fn large_free(&self, level: Large, r: int) -> bool {
        match level {
            Large::Two => forall|i: int| r * 512 <= i < (r + 1) * 512 ==> {
                &&& #[trigger] self.pages@[i].kind is Free
                &&& !self.covered(i)
            },
            Large::One => forall|i: int| r * 262144 <= i < (r + 1) * 262144 ==> {
                &&& #[trigger] self.pages@[i].kind is Free
                &&& !self.covered(i)
            },
        }
    }

    /// Each count is the size of its set, and the sets are exactly what they count.
    pub open spec fn counts_wf(&self) -> bool {
        &&& self.pages.wf()
        &&& self.regions_2m.wf()
        &&& self.regions_1g.wf()
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
        &&& forall|i: int| self.tracks(i) ==> {
            &&& self.in_2m@[region_2m(i)].contains(i) == !(#[trigger] self.pages@[i].kind is Free)
            &&& self.in_1g@[region_1g(i)].contains(i) == (!(self.pages@[i].kind is Free)
                || (i % 512 == 0 && self.regions_2m@[i / 512].typed))
        }
    }

    /// A typed large block has nothing typed inside it or around it.
    pub open spec fn large_wf(&self) -> bool {
        &&& forall|r: int| 0 <= r < NUM_2M && (#[trigger] self.regions_2m@[r]).typed ==> {
            &&& self.count_2m@[r] == 0
            &&& !self.regions_1g@[r / 512].typed
        }
        &&& forall|r: int| 0 <= r < NUM_1G && (#[trigger] self.regions_1g@[r]).typed ==>
            self.count_1g@[r] == 0
    }

    /// The table holds a permission for exactly its free pages outside any typed large block.
    pub open spec fn free_wf(&self) -> bool {
        &&& forall|i: usize| #[trigger] self.free_perms@.contains_key(i) ==> {
            &&& self.tracks(i as int)
            &&& self.free_perms@[i].addr() == i * 4096
            &&& self.free_perms@[i].is_uninit()
        }
        &&& forall|i: usize| self.tracks(i as int) ==>
            (#[trigger] self.free_perms@.contains_key(i)
                == (self.pages@[i as int].kind is Free && !self.covered(i as int)))
    }

    /// Every base is a small block, aligned and in range.
    #[verifier::opaque]
    pub open spec fn bases_wf(&self) -> bool {
        forall|i: int| self.tracks(i) && (#[trigger] self.pages@[i].kind is Base) ==> {
            &&& small_order(self.pages@[i].order)
            &&& i % order_pages(self.pages@[i].order) == 0
            &&& self.tracks_run(i, order_pages(self.pages@[i].order))
        }
    }

    /// Every page of a base's block after the base is its member.
    #[verifier::opaque]
    pub open spec fn members_wf(&self) -> bool {
        forall|i: int, k: int| self.tracks(i) && (#[trigger] self.pages@[i].kind is Base)
            && 0 < k < order_pages(self.pages@[i].order) ==> {
            &&& (#[trigger] self.pages@[i + k]).kind is Member
            &&& self.pages@[i + k].base == i
        }
    }

    /// A member's base is a base whose block covers it.
    #[verifier::opaque]
    pub open spec fn member_bases_wf(&self) -> bool {
        forall|i: int| self.tracks(i) && (#[trigger] self.pages@[i].kind is Member) ==> {
            let b = self.pages@[i].base as int;
            &&& self.tracks(b)
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
        &&& self.large_wf()
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
            self.tracks(i),
            self.pages@[i].kind is Base,
        ensures
            small_order(self.pages@[i].order),
            i % order_pages(self.pages@[i].order) == 0,
            self.tracks_run(i, order_pages(self.pages@[i].order)),
    {
        reveal(BlockTable::bases_wf);
    }

    /// Every page of a base's block after the base is its member.
    pub proof fn lemma_member_of(&self, i: int, j: int)
        requires
            self.members_wf(),
            self.tracks(i),
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
            self.tracks(i),
            self.pages@[i].kind is Member,
        ensures
            self.tracks(self.pages@[i].base as int),
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
            pre.pages@.len() == pre.page_count(),
            post.pages@.len() == post.page_count(),
            forall|i: int| pre.tracks(i) ==> Self::same_block(#[trigger] pre.pages@[i], post.pages@[i]),
        ensures
            post.blocks_wf(),
    {
        assert(post.bases_wf()) by {
            reveal(BlockTable::bases_wf);
            assert forall|b: int| post.tracks(b) && (#[trigger] post.pages@[b].kind is Base) implies {
                &&& small_order(post.pages@[b].order)
                &&& b % order_pages(post.pages@[b].order) == 0
                &&& post.tracks_run(b, order_pages(post.pages@[b].order))
            } by {
                assert(Self::same_block(pre.pages@[b], post.pages@[b]));
                pre.lemma_base(b);
            }
        }
        assert(post.members_wf()) by {
            reveal(BlockTable::members_wf);
            assert forall|b: int, k: int| post.tracks(b) && (#[trigger] post.pages@[b].kind is Base)
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
            assert forall|j: int| post.tracks(j) && (#[trigger] post.pages@[j].kind is Member) implies {
                let b = post.pages@[j].base as int;
                &&& post.tracks(b)
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
            self.tracks(a),
            self.tracks(b),
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
            self.tracks(i),
            region_2m(i) == r,
        ensures
            self.pages@[i].kind is Free,
    {
        self.in_2m@[r].lemma_len0_is_empty();
        assert(self.in_2m@[region_2m(i)].contains(i) == !(self.pages@[i].kind is Free));
    }

    /// A 1G region whose count is zero has only free pages, in no typed 2M block.
    pub proof fn lemma_zero_1g_is_free(&self, r: int, i: int)
        requires
            self.counts_wf(),
            0 <= r < NUM_1G,
            self.count_1g@[r] == 0,
            self.tracks(i),
            region_1g(i) == r,
        ensures
            self.pages@[i].kind is Free,
            !self.regions_2m@[region_2m(i)].typed,
    {
        self.in_1g@[r].lemma_len0_is_empty();
        assert(!self.in_1g@[region_1g(i)].contains(i));
        let b = region_2m(i) * 512;
        assert(self.tracks(b));
        assert(region_1g(b) == r);
        assert(b % 512 == 0 && b / 512 == region_2m(i));
        assert(self.in_1g@[region_1g(b)].contains(b) == (!(self.pages@[b].kind is Free)
            || (b % 512 == 0 && self.regions_2m@[b / 512].typed)));
        assert(!self.in_1g@[region_1g(b)].contains(b));
    }

    /// A free 2M block's count is zero, and neither it nor the 1G block around it is typed.
    pub proof fn lemma_free_2m_is_zero(&self, r: int)
        requires
            self.counts_wf(),
            0 <= r < NUM_2M,
            self.large_free(Large::Two, r),
        ensures
            self.count_2m@[r] == 0,
            !self.regions_2m@[r].typed,
            !self.regions_1g@[r / 512].typed,
    {
        assert forall|i: int| !self.in_2m@[r].contains(i) by {
            if self.in_2m@[r].contains(i) {
                assert(set_int_range(r * 512, (r + 1) * 512).contains(i));
                assert(self.tracks(i));
                assert(region_2m(i) == r);
                assert(self.pages@[i].kind is Free);
                assert(self.in_2m@[region_2m(i)].contains(i) == !(self.pages@[i].kind is Free));
            }
        }
        assert(self.in_2m@[r] =~= Set::<int>::empty());
        assert(self.in_2m@[r].len() == 0);
        let b = r * 512;
        assert(self.pages@[b].kind is Free);
        assert(!self.covered(b));
        assert(region_2m(b) == r);
        assert(region_1g(b) == r / 512);
    }

    /// A free 1G block's count is zero, and it is not typed.
    pub proof fn lemma_free_1g_is_zero(&self, r: int)
        requires
            self.counts_wf(),
            0 <= r < NUM_1G,
            self.large_free(Large::One, r),
        ensures
            self.count_1g@[r] == 0,
            !self.regions_1g@[r].typed,
    {
        assert forall|i: int| !self.in_1g@[r].contains(i) by {
            if self.in_1g@[r].contains(i) {
                assert(set_int_range(r * 262144, (r + 1) * 262144).contains(i));
                assert(self.tracks(i));
                assert(region_1g(i) == r);
                assert(self.pages@[i].kind is Free);
                assert(!self.covered(i));
                assert(region_2m(i) == i / 512);
                assert(self.in_1g@[region_1g(i)].contains(i) == (!(self.pages@[i].kind is Free)
                    || (i % 512 == 0 && self.regions_2m@[i / 512].typed)));
            }
        }
        assert(self.in_1g@[r] =~= Set::<int>::empty());
        assert(self.in_1g@[r].len() == 0);
        let b = r * 262144;
        assert(self.pages@[b].kind is Free);
        assert(!self.covered(b));
        assert(region_1g(b) == r);
    }

    /// A non-free page is in no typed large block: its regions' counts are not zero.
    pub proof fn lemma_not_free_uncovered(&self, i: int)
        requires
            self.counts_wf(),
            self.large_wf(),
            self.tracks(i),
            !(self.pages@[i].kind is Free),
        ensures
            !self.covered(i),
    {
        let (r2, r1) = (region_2m(i), region_1g(i));
        assert(self.in_2m@[r2].contains(i));
        assert(self.in_1g@[r1].contains(i));
        if self.regions_2m@[r2].typed {
            self.in_2m@[r2].lemma_len0_is_empty();
        }
        if self.regions_1g@[r1].typed {
            self.in_1g@[r1].lemma_len0_is_empty();
        }
    }

    /// Page i is in the large block at r.
    pub open spec fn in_large(level: Large, r: int, i: int) -> bool {
        match level {
            Large::Two => region_2m(i) == r,
            Large::One => region_1g(i) == r,
        }
    }

    /// The pages of a large block.
    pub open spec fn large_pages(level: Large, r: int) -> Set<usize> {
        match level {
            Large::Two => Set::<usize>::range((r * 512) as usize, ((r + 1) * 512) as usize),
            Large::One => Set::<usize>::range((r * 262144) as usize, ((r + 1) * 262144) as usize),
        }
    }

    /// The pages of a large block are those whose region it is.
    pub proof fn lemma_large_pages(level: Large, r: int)
        requires
            match level {
                Large::Two => 0 <= r < NUM_2M,
                Large::One => 0 <= r < NUM_1G,
            },
        ensures
            forall|i: usize| #[trigger] Self::large_pages(level, r).contains(i) == Self::in_large(level, r, i as int),
    {
        match level {
            Large::Two => {
                range_set_properties::<usize>((r * 512) as usize, ((r + 1) * 512) as usize);
            },
            Large::One => {
                range_set_properties::<usize>((r * 262144) as usize, ((r + 1) * 262144) as usize);
            },
        }
    }

    /// Set every entry Reserved, in place, since a table this size cannot move by value.
    pub fn init(&mut self, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).pages.wf(),
            old(self).count_2m.wf(),
            old(self).count_1g.wf(),
            old(self).regions_2m.wf(),
            old(self).regions_1g.wf(),
        ensures
            final(steps).count <= old(steps).count + NUM_PAGES + NUM_2M + NUM_1G,
            final(self).wf(),
            forall|i: int| final(self).tracks(i) ==> #[trigger] final(self).pages@[i].kind is Reserved,
            forall|i: int| final(self).tracks(i) ==> #[trigger] final(self).pages@[i].object is None,
            forall|r: int| 0 <= r < NUM_2M ==> !(#[trigger] final(self).regions_2m@[r]).typed,
            forall|r: int| 0 <= r < NUM_1G ==> !(#[trigger] final(self).regions_1g@[r]).typed,
    {
        let n = self.page_count();
        let ghost steps0 = steps.count;
        let mut i = 0;
        while i != n
            invariant
                n == self.page_count(),
                i <= n,
                steps.count == steps0 + i,
                self.pages.wf(),
                forall|j: int| 0 <= j < i ==> #[trigger] self.pages@[j].kind is Reserved,
                forall|j: int| 0 <= j < i ==> #[trigger] self.pages@[j].object is None,
            decreases n - i,
        {
            self.pages.set(i, PageEntry {
                kind: PageKind::Reserved,
                object: ObjectType::None,
                base: 0,
                order: 0,
                dead: false,
                torn_down: false,
                refs: 0,
            });
            i = i + 1;
            proof {
                steps.step();
            }
        }
        let mut r = 0;
        while r != NUM_2M
            invariant
                0 <= r <= NUM_2M,
                steps.count == steps0 + NUM_PAGES + r,
                self.count_2m.wf(),
                self.regions_2m.wf(),
                forall|j: int| 0 <= j < r ==> #[trigger] self.count_2m@[j] == 512,
                forall|j: int| 0 <= j < r ==> !(#[trigger] self.regions_2m@[j]).typed,
            decreases NUM_2M - r,
        {
            self.count_2m.set(r, PAGES_PER_2M);
            self.regions_2m.set(r, RegionEntry { typed: false, dead: false, torn_down: false, refs: 0 });
            r = r + 1;
            proof {
                steps.step();
            }
        }
        let mut r = 0;
        while r != NUM_1G
            invariant
                0 <= r <= NUM_1G,
                steps.count == steps0 + NUM_PAGES + NUM_2M + r,
                self.count_1g.wf(),
                self.regions_1g.wf(),
                forall|j: int| 0 <= j < r ==> #[trigger] self.count_1g@[j] == 262144,
                forall|j: int| 0 <= j < r ==> !(#[trigger] self.regions_1g@[j]).typed,
            decreases NUM_1G - r,
        {
            self.count_1g.set(r, PAGES_PER_1G);
            self.regions_1g.set(r, RegionEntry { typed: false, dead: false, torn_down: false, refs: 0 });
            r = r + 1;
            proof {
                steps.step();
            }
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
            old(self).large_wf(),
            old(self).free_wf(),
            old(self).tracks(i as int),
            !(old(self).pages@[i as int].kind is Free),
            perm.addr() == i * 4096,
            perm.is_uninit(),
        ensures
            final(self).counts_wf(),
            final(self).large_wf(),
            final(self).free_wf(),
            final(self).pages@ == old(self).pages@.update(i as int, free_entry()),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let ghost pre = *old(self);
        let (r2, r1) = (i / PAGES_PER_2M, i / PAGES_PER_1G);
        proof {
            pre.lemma_not_free_uncovered(i as int);
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
            object: ObjectType::None,
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
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|r: int| 0 <= r < NUM_2M && (#[trigger] me.regions_2m@[r]).typed implies {
                &&& me.count_2m@[r] == 0
                &&& !me.regions_1g@[r / 512].typed
            } by {
                assert(pre.regions_2m@[r].typed);
            }
            assert forall|r: int| 0 <= r < NUM_1G && (#[trigger] me.regions_1g@[r]).typed implies
                me.count_1g@[r] == 0 by {
                assert(pre.regions_1g@[r].typed);
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
            }
        }
    }

    /// Make a free page non-free, handing out its permission.
    fn take_page(&mut self, i: usize, entry: PageEntry) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).counts_wf(),
            old(self).large_wf(),
            old(self).free_wf(),
            old(self).tracks(i as int),
            old(self).pages@[i as int].kind is Free,
            !old(self).covered(i as int),
            !(entry.kind is Free),
        ensures
            final(self).counts_wf(),
            final(self).large_wf(),
            final(self).free_wf(),
            final(self).pages@ == old(self).pages@.update(i as int, entry),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
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
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|r: int| 0 <= r < NUM_2M && (#[trigger] me.regions_2m@[r]).typed implies {
                &&& me.count_2m@[r] == 0
                &&& !me.regions_1g@[r / 512].typed
            } by {
                assert(pre.regions_2m@[r].typed);
            }
            assert forall|r: int| 0 <= r < NUM_1G && (#[trigger] me.regions_1g@[r]).typed implies
                me.count_1g@[r] == 0 by {
                assert(pre.regions_1g@[r].typed);
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
            }
        }
        Tracked(perm)
    }

    /// Set a large block's state, keeping whether it is typed.
    fn set_region(&mut self, level: Large, r: usize, entry: RegionEntry)
        requires
            old(self).wf(),
            match level {
                Large::Two => r < NUM_2M && entry.typed == old(self).regions_2m@[r as int].typed,
                Large::One => r < NUM_1G && entry.typed == old(self).regions_1g@[r as int].typed,
            },
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            final(self).free_perms == old(self).free_perms,
            match level {
                Large::Two => {
                    &&& final(self).regions_2m@ == old(self).regions_2m@.update(r as int, entry)
                    &&& final(self).regions_1g@ == old(self).regions_1g@
                },
                Large::One => {
                    &&& final(self).regions_1g@ == old(self).regions_1g@.update(r as int, entry)
                    &&& final(self).regions_2m@ == old(self).regions_2m@
                },
            },
    {
        let ghost pre = *old(self);
        match level {
            Large::Two => self.regions_2m.set(r, entry),
            Large::One => self.regions_1g.set(r, entry),
        }
        proof {
            let me = *self;
            assert forall|j: int| 0 <= j < NUM_2M implies
                (#[trigger] me.regions_2m@[j]).typed == pre.regions_2m@[j].typed by {}
            assert forall|j: int| 0 <= j < NUM_1G implies
                (#[trigger] me.regions_1g@[j]).typed == pre.regions_1g@[j].typed by {}
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|j: int| 0 <= j < NUM_2M && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / 512].typed
            } by {
                assert(pre.regions_2m@[j].typed);
            }
            assert forall|j: int| 0 <= j < NUM_1G && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// The state of a large block.
    pub fn region(&self, level: Large, r: usize) -> (ret: RegionEntry)
        requires
            self.wf(),
            match level {
                Large::Two => r < NUM_2M,
                Large::One => r < NUM_1G,
            },
        ensures
            ret == match level {
                Large::Two => self.regions_2m@[r as int],
                Large::One => self.regions_1g@[r as int],
            },
    {
        match level {
            Large::Two => *self.regions_2m.get(r),
            Large::One => *self.regions_1g.get(r),
        }
    }

    /// Reads what a small block was typed as.
    pub fn object_of(&self, base: usize) -> (ret: ObjectType)
        requires
            self.wf(),
            self.tracks(base as int),
        ensures
            ret == self.pages@[base as int].object,
    {
        self.pages.get(base).object
    }

    /// Mark a large block dead.
    pub fn mark_large_dead(&mut self, level: Large, r: usize)
        requires
            old(self).wf(),
            match level {
                Large::Two => r < NUM_2M,
                Large::One => r < NUM_1G,
            },
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            match level {
                Large::Two => final(self).regions_1g@ == old(self).regions_1g@
                    && final(self).regions_2m@ == old(self).regions_2m@.update(r as int,
                        RegionEntry { dead: true, ..old(self).regions_2m@[r as int] }),
                Large::One => final(self).regions_2m@ == old(self).regions_2m@
                    && final(self).regions_1g@ == old(self).regions_1g@.update(r as int,
                        RegionEntry { dead: true, ..old(self).regions_1g@[r as int] }),
            },
    {
        let e = self.region(level, r);
        self.set_region(level, r, RegionEntry { dead: true, ..e });
    }

    /// Record that a dead large block's teardown has finished.
    pub fn mark_large_torn_down(&mut self, level: Large, r: usize)
        requires
            old(self).wf(),
            match level {
                Large::Two => r < NUM_2M && old(self).regions_2m@[r as int].dead,
                Large::One => r < NUM_1G && old(self).regions_1g@[r as int].dead,
            },
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            match level {
                Large::Two => final(self).regions_1g@ == old(self).regions_1g@
                    && final(self).regions_2m@ == old(self).regions_2m@.update(r as int,
                        RegionEntry { torn_down: true, ..old(self).regions_2m@[r as int] }),
                Large::One => final(self).regions_2m@ == old(self).regions_2m@
                    && final(self).regions_1g@ == old(self).regions_1g@.update(r as int,
                        RegionEntry { torn_down: true, ..old(self).regions_1g@[r as int] }),
            },
    {
        let e = self.region(level, r);
        self.set_region(level, r, RegionEntry { torn_down: true, ..e });
    }

    /// Add a reference to a large block, unless the count is full.
    pub fn add_large_ref(&mut self, level: Large, r: usize) -> (added: bool)
        requires
            old(self).wf(),
            match level {
                Large::Two => r < NUM_2M,
                Large::One => r < NUM_1G,
            },
        ensures
            final(self).wf(),
            !added ==> *final(self) == *old(self),
            final(self).pages@ == old(self).pages@,
            final(self).free_perms == old(self).free_perms,
            added == (match level {
                Large::Two => old(self).regions_2m@[r as int].refs != usize::MAX,
                Large::One => old(self).regions_1g@[r as int].refs != usize::MAX,
            }),
            added ==> match level {
                Large::Two => final(self).regions_1g@ == old(self).regions_1g@
                    && final(self).regions_2m@ == old(self).regions_2m@.update(r as int,
                        RegionEntry { refs: (old(self).regions_2m@[r as int].refs + 1) as usize, ..old(self).regions_2m@[r as int] }),
                Large::One => final(self).regions_2m@ == old(self).regions_2m@
                    && final(self).regions_1g@ == old(self).regions_1g@.update(r as int,
                        RegionEntry { refs: (old(self).regions_1g@[r as int].refs + 1) as usize, ..old(self).regions_1g@[r as int] }),
            },
    {
        let e = self.region(level, r);
        if e.refs == usize::MAX {
            return false;
        }
        self.set_region(level, r, RegionEntry { refs: e.refs + 1, ..e });
        true
    }

    /// Drop a reference to a large block. The caller marks it dead when this reaches zero.
    pub fn drop_large_ref(&mut self, level: Large, r: usize)
        requires
            old(self).wf(),
            match level {
                Large::Two => r < NUM_2M && old(self).regions_2m@[r as int].refs > 0,
                Large::One => r < NUM_1G && old(self).regions_1g@[r as int].refs > 0,
            },
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            match level {
                Large::Two => final(self).regions_1g@ == old(self).regions_1g@
                    && final(self).regions_2m@ == old(self).regions_2m@.update(r as int,
                        RegionEntry { refs: (old(self).regions_2m@[r as int].refs - 1) as usize, ..old(self).regions_2m@[r as int] }),
                Large::One => final(self).regions_2m@ == old(self).regions_2m@
                    && final(self).regions_1g@ == old(self).regions_1g@.update(r as int,
                        RegionEntry { refs: (old(self).regions_1g@[r as int].refs - 1) as usize, ..old(self).regions_1g@[r as int] }),
            },
    {
        let e = self.region(level, r);
        self.set_region(level, r, RegionEntry { refs: e.refs - 1, ..e });
    }

    /// Type a free 2M block, in constant time: its count says nothing inside it is typed, and the 1G
    /// entry says nothing around it is. Holds one reference for the caller and hands back the
    /// permission of each page.
    pub fn try_type_2m(&mut self, r: usize) -> (ret: Option<Tracked<Map<usize, PagePerm4k>>>)
        requires
            old(self).wf(),
            r < NUM_2M,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            ret is None ==> *final(self) == *old(self),
            ret is Some == old(self).large_free(Large::Two, r as int),
            ret is Some ==> {
                &&& final(self).regions_2m@[r as int] == (RegionEntry {
                    typed: true, dead: false, torn_down: false, refs: 1,
                })
                &&& final(self).regions_2m@ == old(self).regions_2m@.update(r as int, final(self).regions_2m@[r as int])
                &&& final(self).regions_1g@ == old(self).regions_1g@
                &&& ret->0@.dom() == Self::large_pages(Large::Two, r as int)
                &&& forall|i: usize| Self::large_pages(Large::Two, r as int).contains(i) ==>
                    #[trigger] holds(ret->0@, i)
            },
    {
        let r1 = r / 512;
        if *self.count_2m.get(r) != 0 || self.regions_2m.get(r).typed || self.regions_1g.get(r1).typed {
            proof {
                if self.large_free(Large::Two, r as int) {
                    self.lemma_free_2m_is_zero(r as int);
                }
            }
            return None;
        }
        let ghost pre = *old(self);
        let base = r * PAGES_PER_2M;
        let ghost keys = Self::large_pages(Large::Two, r as int);
        proof {
            assert(region_2m(base as int) == r);
            assert(region_1g(base as int) == r1);
            pre.lemma_zero_2m_is_free(r as int, base as int);
            assert(!pre.in_1g@[r1 as int].contains(base as int));
            lemma_int_range(r1 * 262144, (r1 + 1) * 262144);
            lemma_len_subset(pre.in_1g@[r1 as int], set_int_range(r1 * 262144, (r1 + 1) * 262144));
            vstd::set::lemma_set_insert_len(pre.in_1g@[r1 as int], base as int);
            Self::lemma_large_pages(Large::Two, r as int);
            assert forall|i: usize| keys.contains(i) implies {
                &&& #[trigger] pre.free_perms@.contains_key(i)
                &&& pre.pages@[i as int].kind is Free
                &&& !pre.covered(i as int)
            } by {
                assert(region_2m(i as int) == r);
                assert(region_1g(i as int) == r1);
                pre.lemma_zero_2m_is_free(r as int, i as int);
            }
        }
        let c1 = *self.count_1g.get(r1);
        self.count_1g.set(r1, c1 + 1);
        self.in_1g = Ghost(pre.in_1g@.update(r1 as int, pre.in_1g@[r1 as int].insert(base as int)));
        self.regions_2m.set(r, RegionEntry { typed: true, dead: false, torn_down: false, refs: 1 });
        let tracked taken;
        proof {
            taken = self.free_perms.borrow_mut().tracked_remove_keys(keys);
            let me = *self;
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
                if j % 512 == 0 && j / 512 == r {
                    assert(j == base);
                }
            }
            assert forall|j: int| 0 <= j < NUM_1G implies {
                &&& (#[trigger] me.in_1g@[j]).finite()
                &&& me.in_1g@[j].len() == me.count_1g@[j]
                &&& me.in_1g@[j].subset_of(set_int_range(j * 262144, (j + 1) * 262144))
            } by {
                assert(pre.in_1g@[j].finite());
            }
            assert forall|j: int| 0 <= j < NUM_2M && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / 512].typed
            } by {
                if j != r {
                    assert(pre.regions_2m@[j].typed);
                }
            }
            assert forall|j: int| 0 <= j < NUM_1G && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * 4096
                &&& me.free_perms@[j].is_uninit()
            } by {
                assert(pre.free_perms@.contains_key(j));
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
                assert(keys.contains(j) == (region_2m(j as int) == r));
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
            assert forall|i: usize| keys.contains(i) implies #[trigger] holds(taken, i) by {
                assert(pre.free_perms@.contains_key(i));
            }
        }
        Some(Tracked(taken))
    }

    /// Type the 2M region r, every page of which boot reserved, as a large block holding one reference:
    /// boot's step for a region dom0's image lies in. Its pages go Reserved to Free under the typed
    /// region, as every large block's pages are, so none becomes free and free_perms is unchanged. A
    /// bounded loop of 512 page writes. See design/root-process-at-boot/.
    pub fn type_reserved_2m(&mut self, r: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            r < NUM_2M,
            forall|i: int| r * 512 <= i < (r + 1) * 512 ==> #[trigger] old(self).pages@[i].kind is Reserved,
        ensures
            final(steps).count <= old(steps).count + PAGES_PER_2M,
            final(self).wf(),
            final(self).free_perms == old(self).free_perms,
            final(self).regions_2m@ == old(self).regions_2m@.update(r as int,
                RegionEntry { typed: true, dead: false, torn_down: false, refs: 1 }),
            final(self).regions_1g@ == old(self).regions_1g@,
            !old(self).regions_2m@[r as int].typed,
            !old(self).regions_1g@[r as int / 512].typed,
            forall|i: int| final(self).tracks(i) ==> #[trigger] final(self).pages@[i]
                == if region_2m(i) == r { free_entry() } else { old(self).pages@[i] },
    {
        let ghost pre = *old(self);
        let first = r * PAGES_PER_2M;
        let r1 = r / 512;
        proof {
            assert(region_2m(first as int) == r);
            assert(region_1g(first as int) == r1);
            assert(pre.pages@[first as int].kind is Reserved);
            pre.lemma_not_free_uncovered(first as int);
        }
        let ghost steps0 = steps.count;
        let mut k: usize = 0;
        while k < PAGES_PER_2M
            invariant
                k <= PAGES_PER_2M,
                steps.count == steps0 + k,
                r < NUM_2M,
                first == r * 512,
                self.pages.wf(),
                forall|i: int| self.tracks(i) ==> #[trigger] self.pages@[i]
                    == if first <= i < first + k { free_entry() } else { pre.pages@[i] },
                self.regions_2m == pre.regions_2m,
                self.regions_1g == pre.regions_1g,
                self.count_2m == pre.count_2m,
                self.count_1g == pre.count_1g,
                self.free_perms == pre.free_perms,
                self.in_2m == pre.in_2m,
                self.in_1g == pre.in_1g,
            decreases PAGES_PER_2M - k,
        {
            self.pages.set(first + k, PageEntry {
                kind: PageKind::Free,
                object: ObjectType::None,
                base: 0,
                order: 0,
                dead: false,
                torn_down: false,
                refs: 0,
            });
            k = k + 1;
            proof {
                steps.step();
            }
        }
        let ghost gone = set_int_range(first + 1, first + 512);
        proof {
            lemma_int_range(first + 1, first + 512);
            assert(pre.in_1g@[r1 as int].finite());
            assert forall|j: int| gone.contains(j) implies #[trigger] pre.in_1g@[r1 as int].contains(j) by {
                assert(region_1g(j) == r1);
                assert(pre.pages@[j].kind is Reserved);
            }
            lemma_len_subset(gone, pre.in_1g@[r1 as int]);
            let kept = pre.in_1g@[r1 as int].difference(gone);
            assert(kept + gone =~= pre.in_1g@[r1 as int]);
            assert(kept.disjoint(gone));
            vstd::set_lib::lemma_set_disjoint_lens(kept, gone);
            assert(kept.finite());
        }
        let c1 = *self.count_1g.get(r1);
        self.count_1g.set(r1, c1 - 511);
        self.count_2m.set(r, 0);
        self.in_2m = Ghost(pre.in_2m@.update(r as int, Set::empty()));
        self.in_1g = Ghost(pre.in_1g@.update(r1 as int, pre.in_1g@[r1 as int].difference(gone)));
        self.regions_2m.set(r, RegionEntry { typed: true, dead: false, torn_down: false, refs: 1 });
        proof {
            let me = *self;
            assert forall|i: int| me.tracks(i) implies #[trigger] me.pages@[i]
                == if region_2m(i) == r { free_entry() } else { pre.pages@[i] } by {
                assert((first <= i < first + 512) == (region_2m(i) == r));
            }
            assert forall|j: int| 0 <= j < NUM_2M implies {
                &&& (#[trigger] me.in_2m@[j]).finite()
                &&& me.in_2m@[j].len() == me.count_2m@[j]
                &&& me.in_2m@[j].subset_of(set_int_range(j * 512, (j + 1) * 512))
            } by {
                assert(pre.in_2m@[j].finite());
            }
            assert forall|j: int| 0 <= j < NUM_1G implies {
                &&& (#[trigger] me.in_1g@[j]).finite()
                &&& me.in_1g@[j].len() == me.count_1g@[j]
                &&& me.in_1g@[j].subset_of(set_int_range(j * 262144, (j + 1) * 262144))
            } by {
                assert(pre.in_1g@[j].finite());
            }
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
                assert((first <= j < first + 512) == (region_2m(j) == r));
                if region_2m(j) == r {
                    assert(region_1g(j) == r1);
                    assert(j % 512 == 0 <==> j == first);
                    assert(j / 512 == r);
                    assert(pre.pages@[j].kind is Reserved);
                }
            }
            assert forall|j: int| 0 <= j < NUM_2M && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / 512].typed
            } by {
                if j != r {
                    assert(pre.regions_2m@[j].typed);
                }
            }
            assert forall|j: int| 0 <= j < NUM_1G && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
                assert((first <= j < first + 512) == (region_2m(j as int) == r));
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {
                assert((first <= j < first + 512) == (region_2m(j) == r));
            }
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// Type a free 1G block, in constant time: its count says nothing inside it is typed.
    pub fn try_type_1g(&mut self, r: usize) -> (ret: Option<Tracked<Map<usize, PagePerm4k>>>)
        requires
            old(self).wf(),
            r < NUM_1G,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            ret is None ==> *final(self) == *old(self),
            ret is Some == old(self).large_free(Large::One, r as int),
            ret is Some ==> {
                &&& final(self).regions_1g@[r as int] == (RegionEntry {
                    typed: true, dead: false, torn_down: false, refs: 1,
                })
                &&& final(self).regions_1g@ == old(self).regions_1g@.update(r as int, final(self).regions_1g@[r as int])
                &&& final(self).regions_2m@ == old(self).regions_2m@
                &&& ret->0@.dom() == Self::large_pages(Large::One, r as int)
                &&& forall|i: usize| Self::large_pages(Large::One, r as int).contains(i) ==>
                    #[trigger] holds(ret->0@, i)
            },
    {
        if *self.count_1g.get(r) != 0 || self.regions_1g.get(r).typed {
            proof {
                if self.large_free(Large::One, r as int) {
                    self.lemma_free_1g_is_zero(r as int);
                }
            }
            return None;
        }
        let ghost pre = *old(self);
        let ghost keys = Self::large_pages(Large::One, r as int);
        proof {
            Self::lemma_large_pages(Large::One, r as int);
            assert forall|i: usize| keys.contains(i) implies {
                &&& #[trigger] pre.free_perms@.contains_key(i)
                &&& pre.pages@[i as int].kind is Free
                &&& !pre.covered(i as int)
            } by {
                pre.lemma_zero_1g_is_free(r as int, i as int);
            }
            assert forall|i: int| r * 262144 <= i < (r + 1) * 262144 implies {
                &&& #[trigger] pre.pages@[i].kind is Free
                &&& !pre.covered(i)
            } by {
                pre.lemma_zero_1g_is_free(r as int, i);
            }
        }
        self.regions_1g.set(r, RegionEntry { typed: true, dead: false, torn_down: false, refs: 1 });
        let tracked taken;
        proof {
            taken = self.free_perms.borrow_mut().tracked_remove_keys(keys);
            let me = *self;
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|j: int| 0 <= j < NUM_2M && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / 512].typed
            } by {
                assert(pre.regions_2m@[j].typed);
                if j / 512 == r {
                    pre.lemma_zero_1g_is_free(r as int, j * 512);
                }
            }
            assert forall|j: int| 0 <= j < NUM_1G && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                if j != r {
                    assert(pre.regions_1g@[j].typed);
                }
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * 4096
                &&& me.free_perms@[j].is_uninit()
            } by {
                assert(pre.free_perms@.contains_key(j));
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
                assert(keys.contains(j) == (region_1g(j as int) == r));
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
            assert forall|i: usize| keys.contains(i) implies #[trigger] holds(taken, i) by {
                assert(pre.free_perms@.contains_key(i));
            }
        }
        Some(Tracked(taken))
    }

    /// A dead 2M block at zero references whose teardown has finished returns to free, with its
    /// permissions.
    pub fn free_2m(&mut self, r: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            r < NUM_2M,
            old(self).regions_2m@[r as int].typed,
            old(self).regions_2m@[r as int].dead,
            old(self).regions_2m@[r as int].torn_down,
            old(self).regions_2m@[r as int].refs == 0,
            forall|i: usize| Self::large_pages(Large::Two, r as int).contains(i) ==> #[trigger] holds(perms, i),
            perms.dom() == Self::large_pages(Large::Two, r as int),
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            !final(self).regions_2m@[r as int].typed,
            final(self).regions_2m@ == old(self).regions_2m@.update(r as int, final(self).regions_2m@[r as int]),
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let ghost pre = *old(self);
        let r1 = r / 512;
        let base = r * PAGES_PER_2M;
        let ghost keys = Self::large_pages(Large::Two, r as int);
        proof {
            assert(region_2m(base as int) == r);
            assert(region_1g(base as int) == r1);
            assert(pre.in_1g@[region_1g(base as int)].contains(base as int)
                == (!(pre.pages@[base as int].kind is Free)
                    || (base as int % 512 == 0 && pre.regions_2m@[base as int / 512].typed)));
            assert(pre.in_1g@[region_1g(base as int)].contains(base as int));
            if pre.count_1g@[r1 as int] == 0 {
                pre.in_1g@[r1 as int].lemma_len0_is_empty();
            }
            vstd::set::lemma_set_remove_len(pre.in_1g@[r1 as int], base as int);
            Self::lemma_large_pages(Large::Two, r as int);
        }
        let c1 = *self.count_1g.get(r1);
        self.count_1g.set(r1, c1 - 1);
        self.in_1g = Ghost(pre.in_1g@.update(r1 as int, pre.in_1g@[r1 as int].remove(base as int)));
        self.regions_2m.set(r, RegionEntry { typed: false, dead: false, torn_down: false, refs: 0 });
        proof {
            self.free_perms.borrow_mut().tracked_union_prefer_right(perms);
            let me = *self;
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
                if j == base {
                    pre.lemma_zero_2m_is_free(r as int, j);
                }
            }
            assert forall|j: int| 0 <= j < NUM_1G implies {
                &&& (#[trigger] me.in_1g@[j]).finite()
                &&& me.in_1g@[j].len() == me.count_1g@[j]
                &&& me.in_1g@[j].subset_of(set_int_range(j * 262144, (j + 1) * 262144))
            } by {
                assert(pre.in_1g@[j].finite());
            }
            assert forall|j: int| 0 <= j < NUM_2M && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / 512].typed
            } by {
                assert(pre.regions_2m@[j].typed);
            }
            assert forall|j: int| 0 <= j < NUM_1G && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * 4096
                &&& me.free_perms@[j].is_uninit()
            } by {
                if keys.contains(j) {
                    assert(holds(perms, j));
                } else {
                    assert(pre.free_perms@.contains_key(j));
                }
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
                assert(keys.contains(j) == (region_2m(j as int) == r));
                if region_2m(j as int) == r {
                    pre.lemma_zero_2m_is_free(r as int, j as int);
                }
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// A dead 1G block at zero references whose teardown has finished returns to free, with its
    /// permissions.
    pub fn free_1g(&mut self, r: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            r < NUM_1G,
            old(self).regions_1g@[r as int].typed,
            old(self).regions_1g@[r as int].dead,
            old(self).regions_1g@[r as int].torn_down,
            old(self).regions_1g@[r as int].refs == 0,
            forall|i: usize| Self::large_pages(Large::One, r as int).contains(i) ==> #[trigger] holds(perms, i),
            perms.dom() == Self::large_pages(Large::One, r as int),
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            !final(self).regions_1g@[r as int].typed,
            final(self).regions_1g@ == old(self).regions_1g@.update(r as int, final(self).regions_1g@[r as int]),
            final(self).regions_2m@ == old(self).regions_2m@,
    {
        let ghost pre = *old(self);
        let ghost keys = Self::large_pages(Large::One, r as int);
        proof {
            Self::lemma_large_pages(Large::One, r as int);
        }
        self.regions_1g.set(r, RegionEntry { typed: false, dead: false, torn_down: false, refs: 0 });
        proof {
            self.free_perms.borrow_mut().tracked_union_prefer_right(perms);
            let me = *self;
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|j: int| 0 <= j < NUM_2M && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / 512].typed
            } by {
                assert(pre.regions_2m@[j].typed);
            }
            assert forall|j: int| 0 <= j < NUM_1G && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * 4096
                &&& me.free_perms@[j].is_uninit()
            } by {
                if keys.contains(j) {
                    assert(holds(perms, j));
                } else {
                    assert(pre.free_perms@.contains_key(j));
                }
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
                assert(keys.contains(j) == (region_1g(j as int) == r));
                if region_1g(j as int) == r {
                    pre.lemma_zero_1g_is_free(r as int, j as int);
                }
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// Boot hands a reserved page to the table.
    pub fn add_free(&mut self, i: usize, Tracked(perm): Tracked<PagePerm4k>)
        requires
            old(self).wf(),
            old(self).tracks(i as int),
            old(self).pages@[i as int].kind is Reserved,
            perm.addr() == i * 4096,
            perm.is_uninit(),
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(i as int, free_entry()),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let ghost pre = *old(self);
        self.give_page(i, Tracked(perm));
        proof {
            let me = *self;
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// Type a free block. Checks every page, at most 8, and on success holds one reference for the
    /// caller and hands back the permission of each page.
    pub fn try_type(&mut self, base: usize, order: usize, object: ObjectType, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Tracked<Map<usize, PagePerm4k>>>)
        requires
            old(self).wf(),
            small_order(order),
            base % (order_pages(order) as usize) == 0,
            old(self).tracks_run(base as int, order_pages(order)),
        ensures
            final(steps).count <= old(steps).count + 2 * SMALL_PAGES_MAX,
            final(self).wf(),
            ret is None ==> *final(self) == *old(self),
            ret is Some == old(self).small_free(base as int, order),
            ret is Some ==> {
                &&& final(self).regions_2m@ == old(self).regions_2m@
                &&& final(self).regions_1g@ == old(self).regions_1g@
                &&& final(self).pages@[base as int].kind is Base
                &&& final(self).pages@[base as int].object == object
                &&& final(self).pages@[base as int].order == order
                &&& final(self).pages@[base as int].refs == 1
                &&& !final(self).pages@[base as int].dead
                &&& !final(self).pages@[base as int].torn_down
                &&& forall|i: int| final(self).tracks(i) && !(base <= i < base + order_pages(order))
                    ==> #[trigger] final(self).pages@[i] == old(self).pages@[i]
                &&& forall|k: int| 0 < k < order_pages(order) ==> (#[trigger] final(self).pages@[base + k]).object is None
                &&& forall|k: usize| k < order_pages(order) ==> {
                    &&& ret->0@.contains_key((base + k) as usize)
                    &&& #[trigger] ret->0@[(base + k) as usize].addr() == (base + k) * 4096
                    &&& ret->0@[(base + k) as usize].is_uninit()
                }
            },
    {
        let ghost pre = *old(self);
        if self.regions_2m.get(base / PAGES_PER_2M).typed || self.regions_1g.get(base / PAGES_PER_1G).typed {
            return None;
        }
        let size: usize = if order == 0 { 1 } else if order == 1 { 2 } else { 8 };
        let ghost steps0 = steps.count;
        let mut k = 0;
        while k != size
            invariant
                self.wf(),
                *self == pre,
                size as int == order_pages(order),
                0 <= k <= size,
                size <= SMALL_PAGES_MAX,
                steps0 == old(steps).count,
                steps.count == steps0 + k,
                self.tracks_run(base as int, size as int),
                forall|j: int| 0 <= j < k ==> #[trigger] pre.pages@[base + j].kind is Free,
            decreases size - k,
        {
            match self.pages.get(base + k).kind {
                PageKind::Free => {},
                _ => return None,
            }
            k = k + 1;
            proof {
                steps.step();
            }
        }
        let tracked mut taken = Map::<usize, PagePerm4k>::tracked_empty();
        let mut k = 0;
        while k != size
            invariant
                self.counts_wf(),
                self.large_wf(),
                self.free_wf(),
                self.regions_2m@ == pre.regions_2m@,
                self.regions_1g@ == pre.regions_1g@,
                !pre.covered(base as int),
                base % (order_pages(order) as usize) == 0,
                size as int == order_pages(order),
                small_order(order),
                0 <= k <= size,
                size <= SMALL_PAGES_MAX,
                steps.count == steps0 + size + k,
                self.tracks_run(base as int, size as int),
                forall|j: int| k <= j < size ==> #[trigger] self.pages@[base + j].kind is Free,
                forall|j: int| 0 <= j < size ==> #[trigger] pre.pages@[base + j].kind is Free,
                forall|i: int| self.tracks(i) && !(base <= i < base + size)
                    ==> #[trigger] self.pages@[i] == pre.pages@[i],
                k > 0 ==> self.pages@[base as int] == (PageEntry {
                    kind: PageKind::Base, object, base, order, dead: false, torn_down: false, refs: 1,
                }),
                forall|j: int| 0 < j < k ==> {
                    &&& (#[trigger] self.pages@[base + j]).kind is Member
                    &&& self.pages@[base + j].base == base
                    &&& self.pages@[base + j].object is None
                },
                forall|j: usize| j < k ==> #[trigger] holds(taken, (base + j) as usize),
            decreases size - k,
        {
            let entry = if k == 0 {
                PageEntry { kind: PageKind::Base, object, base, order, dead: false, torn_down: false, refs: 1 }
            } else {
                PageEntry { kind: PageKind::Member, object: ObjectType::None, base, order: 0, dead: false, torn_down: false, refs: 0 }
            };
            proof {
                if order == 0 {
                    assert(k == 0);
                } else if order == 1 {
                    assert(base % 2 == 0 && k < 2);
                } else {
                    assert(base % 8 == 0 && k < 8);
                }
                assert(region_2m(base + k) == region_2m(base as int));
                assert(region_1g(base + k) == region_1g(base as int));
                assert(!self.covered(base + k));
            }
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
            proof {
                steps.step();
            }
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
            pre.pages@.len() == pre.page_count(),
            self.pages@.len() == self.page_count(),
            small_order(order),
            base % order_pages(order) == 0,
            0 <= base,
            self.tracks_run(base, order_pages(order)),
            self.pages@[base].kind is Base,
            self.pages@[base].order == order,
            forall|j: int| 0 <= j < order_pages(order) ==> #[trigger] pre.pages@[base + j].kind is Free,
            forall|i: int| self.tracks(i) && !(base <= i < base + order_pages(order))
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
            assert forall|b: int| self.tracks(b) && (#[trigger] self.pages@[b].kind is Base) implies {
                &&& small_order(self.pages@[b].order)
                &&& b % order_pages(self.pages@[b].order) == 0
                &&& self.tracks_run(b, order_pages(self.pages@[b].order))
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
            assert forall|b: int, k: int| self.tracks(b) && (#[trigger] self.pages@[b].kind is Base)
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
            assert forall|j: int| self.tracks(j) && (#[trigger] self.pages@[j].kind is Member) implies {
                let b = self.pages@[j].base as int;
                &&& self.tracks(b)
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
            old(self).tracks(base as int),
            old(self).pages@[base as int].kind is Base,
            entry.kind is Base,
            entry.order == old(self).pages@[base as int].order,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int, entry),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let ghost pre = *old(self);
        self.pages.set(base, entry);
        proof {
            let me = *self;
            assert(me.pages@ =~= pre.pages@.update(base as int, entry));
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % 512 == 0 && me.regions_2m@[j / 512].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|i: usize| me.tracks(i as int) implies
                (#[trigger] me.free_perms@.contains_key(i)
                    == (me.pages@[i as int].kind is Free && !me.covered(i as int))) by {
                assert(pre.free_perms@.contains_key(i)
                    == (pre.pages@[i as int].kind is Free && !pre.covered(i as int)));
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {}
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// Mark a block dead.
    pub fn mark_dead(&mut self, base: usize)
        requires
            old(self).wf(),
            old(self).tracks(base as int),
            old(self).pages@[base as int].kind is Base,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { dead: true, ..old(self).pages@[base as int] }),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let e = *self.pages.get(base);
        self.set_base(base, PageEntry { dead: true, ..e });
    }

    /// Record that a dead block's teardown has finished.
    pub fn mark_torn_down(&mut self, base: usize)
        requires
            old(self).wf(),
            old(self).tracks(base as int),
            old(self).pages@[base as int].kind is Base,
            old(self).pages@[base as int].dead,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { torn_down: true, ..old(self).pages@[base as int] }),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let e = *self.pages.get(base);
        self.set_base(base, PageEntry { torn_down: true, ..e });
    }

    /// Add a reference, unless the count is full.
    pub fn add_ref(&mut self, base: usize) -> (added: bool)
        requires
            old(self).wf(),
            old(self).tracks(base as int),
            old(self).pages@[base as int].kind is Base,
        ensures
            final(self).wf(),
            added ==> final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { refs: (old(self).pages@[base as int].refs + 1) as usize, ..old(self).pages@[base as int] }),
            !added ==> *final(self) == *old(self),
            added == (old(self).pages@[base as int].refs != usize::MAX),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
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
            old(self).tracks(base as int),
            old(self).pages@[base as int].kind is Base,
            old(self).pages@[base as int].refs > 0,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(base as int,
                PageEntry { refs: (old(self).pages@[base as int].refs - 1) as usize, ..old(self).pages@[base as int] }),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let e = *self.pages.get(base);
        self.set_base(base, PageEntry { refs: e.refs - 1, ..e });
    }

    /// A dead block at zero references whose teardown has finished returns to free, with its
    /// permissions.
    pub fn free_block(&mut self, base: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).tracks(base as int),
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
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            final(self).wf(),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
            forall|i: int| final(self).tracks(i) ==> #[trigger] final(self).pages@[i] == (
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
        let ghost steps0 = steps.count;
        let mut k = 0;
        while k != size
            invariant
                self.counts_wf(),
                self.large_wf(),
                self.free_wf(),
                pre.wf(),
                size as int == order_pages(order),
                order == pre.pages@[base as int].order,
                pre.pages@[base as int].kind is Base,
                0 <= k <= size,
                size <= SMALL_PAGES_MAX,
                steps.count == steps0 + k,
                self.tracks(base as int),
                self.tracks_run(base as int, size as int),
                forall|j: int| 0 <= j < k ==> #[trigger] self.pages@[base + j] == free_entry(),
                forall|j: int| k <= j < size ==> #[trigger] self.pages@[base + j] == pre.pages@[base + j],
                forall|i: int| self.tracks(i) && !(base <= i < base + size)
                    ==> #[trigger] self.pages@[i] == pre.pages@[i],
                forall|j: usize| k <= j < size ==> #[trigger] holds(perms, (base + j) as usize),
                self.regions_2m@ == pre.regions_2m@,
                self.regions_1g@ == pre.regions_1g@,
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
            proof {
                steps.step();
            }
        }
        proof {
            let me = *self;
            assert forall|i: int| me.tracks(i) implies #[trigger] me.pages@[i] == (
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
            pre.pages@.len() == pre.page_count(),
            self.pages@.len() == self.page_count(),
            self.tracks(base),
            pre.pages@[base].kind is Base,
            forall|i: int| self.tracks(i) ==> #[trigger] self.pages@[i] == (
                if pre.in_block(base, i) { free_entry() } else { pre.pages@[i] }),
        ensures
            self.blocks_wf(),
    {
        assert(self.bases_wf()) by {
            reveal(BlockTable::bases_wf);
            assert forall|b: int| self.tracks(b) && (#[trigger] self.pages@[b].kind is Base) implies {
                &&& small_order(self.pages@[b].order)
                &&& b % order_pages(self.pages@[b].order) == 0
                &&& self.tracks_run(b, order_pages(self.pages@[b].order))
            } by {
                pre.lemma_base(b);
            }
        }
        assert(self.members_wf()) by {
            reveal(BlockTable::members_wf);
            assert forall|b: int, k: int| self.tracks(b) && (#[trigger] self.pages@[b].kind is Base)
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
            assert forall|j: int| self.tracks(j) && (#[trigger] self.pages@[j].kind is Member) implies {
                let b = self.pages@[j].base as int;
                &&& self.tracks(b)
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
