// SPDX-License-Identifier: MIT

//! The block table: what each physical page is, for the kernel that allocates nothing after boot. A
//! block is a power-of-two run of pages, aligned to its size, that goes free, typed, dead, free. The
//! entry at its base holds its order, its reference count and whether its teardown has finished. Each
//! 2M and 1G region counts what is not free inside it, so that zero means all of it is free. A large
//! block cannot write its page entries in a bounded step, so its state is in its region's entry, its
//! pages' entries stay Free, and a page is free only if neither region above it is typed. See
//! design/teardown-driven-by-retype/. How many pages this table covers is
//! design/page-metadata-sized-from-the-memory-map/.
//!
//! Untyped authorisation is a precondition its caller proves, since capabilities live a level above.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::set_lib::*;
#[cfg(verus_keep_ghost)]
use vstd::layout::{size_of, align_of};
use vstd::raw_ptr::{IsExposed, PointsToRaw};

verus! {

use crate::column::Column;
#[cfg(verus_keep_ghost)]
use crate::column::lemma_word_aligned;
use crate::define::*;
use crate::capability::steps::Steps;

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
    Endpoint,
    Notification,
    Reply,
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
    &&& m[i].addr() == i * PAGE_SZ
    &&& m[i].is_uninit()
}

/// n pages from address 0, with n at most a count whose pages fit the identity-mapped span, end within
/// it.
pub proof fn lemma_pages_in_span(n: int, count: int)
    requires
        0 <= n <= count,
        count * PAGE_SZ <= IDENTITY_SPAN,
    ensures
        0 <= n * PAGE_SZ <= IDENTITY_SPAN,
{
    assert(0 <= n * PAGE_SZ <= count * PAGE_SZ) by (nonlinear_arith)
        requires
            0 <= n <= count,
    ;
}

/// A count of pages that is a whole number of 1G regions is a whole number of 2M regions too.
pub proof fn lemma_whole_regions(n: int)
    requires
        0 <= n,
        n % PAGES_PER_1G as int == 0,
    ensures
        (n / PAGES_PER_2M as int) * PAGES_PER_2M as int == n,
        (n / PAGES_PER_1G as int) * PAGES_PER_1G as int == n,
{
    let g = n / PAGES_PER_1G as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, PAGES_PER_1G as int);
    assert(PAGES_PER_1G as int == ENTRIES as int * PAGES_PER_2M as int);
    assert(n == PAGES_PER_2M as int * (g * ENTRIES as int)) by (nonlinear_arith)
        requires
            n == PAGES_PER_1G as int * g,
            PAGES_PER_1G as int == ENTRIES as int * PAGES_PER_2M as int,
    ;
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(g * ENTRIES as int, PAGES_PER_2M as int);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(g, PAGES_PER_1G as int);
}

/// Where each column of the page metadata lies in the region boot carves, as byte offsets from the
/// region's base, and how many bytes the columns take, which is what boot carves. Each column starts
/// where the one before it ends. The columns whose elements are words, or a whole number of words,
/// come first and the byte columns after them, so each starts at a multiple of a word, which is a
/// multiple of its element's alignment. design/page-metadata-sized-from-the-memory-map/.
#[derive(Clone, Copy)]
pub struct MetadataLayout {
    /// The block table's page entries, one per tracked page.
    pub page_entries: usize,
    /// The block table's region entries: one per 2M region, then one per 1G region.
    pub regions_2m: usize,
    pub regions_1g: usize,
    /// The block table's counts: one per 2M region, then one per 1G region.
    pub count_2m: usize,
    pub count_1g: usize,
    /// The stale epochs: one per tracked page, then one per 2M region, then one per 1G region. They
    /// start where the block table's columns end.
    pub stale_pages: usize,
    pub stale_2m: usize,
    pub stale_1g: usize,
    /// Where the stale epochs end: the columns that follow them start here.
    pub stale_end: usize,
    /// The zeroing cursors, one word per tracked page, from where the stale epochs end.
    pub zero_cursor: usize,
    /// The active flags, one byte per 2M region, then one per 1G region.
    pub active_2m: usize,
    pub active_1g: usize,
    pub bytes: usize,
}

/// The layout of the page metadata for `pages` tracked pages.
pub open spec fn spec_metadata_layout(pages: usize) -> MetadataLayout {
    let e = size_of::<PageEntry>() as int;
    let g = size_of::<RegionEntry>() as int;
    let w = size_of::<usize>() as int;
    let two = (pages / PAGES_PER_2M) as int;
    let one = (pages / PAGES_PER_1G) as int;
    let regions_2m = pages * e;
    let regions_1g = regions_2m + two * g;
    let count_2m = regions_1g + one * g;
    let count_1g = count_2m + two * w;
    let stale_pages = count_1g + one * w;
    let stale_2m = stale_pages + pages * w;
    let stale_1g = stale_2m + two * w;
    let stale_end = stale_1g + one * w;
    let active_2m = stale_end + pages * w;
    let active_1g = active_2m + two;
    MetadataLayout {
        page_entries: 0,
        regions_2m: regions_2m as usize,
        regions_1g: regions_1g as usize,
        count_2m: count_2m as usize,
        count_1g: count_1g as usize,
        stale_pages: stale_pages as usize,
        stale_2m: stale_2m as usize,
        stale_1g: stale_1g as usize,
        stale_end: stale_end as usize,
        zero_cursor: stale_end as usize,
        active_2m: active_2m as usize,
        active_1g: active_1g as usize,
        bytes: (active_1g + one) as usize,
    }
}

/// The offsets a layout of the page metadata for `pages` tracked pages holds, as sums: what
/// metadata_layout ensures and what the column constructors read.
pub open spec fn layout_sums(l: MetadataLayout, pages: usize) -> bool {
    let two = pages / PAGES_PER_2M;
    let one = pages / PAGES_PER_1G;
    let w = size_of::<usize>();
    &&& l == spec_metadata_layout(pages)
    &&& l.page_entries == 0
    &&& l.regions_2m == pages * size_of::<PageEntry>()
    &&& l.regions_1g == l.regions_2m + two * size_of::<RegionEntry>()
    &&& l.count_2m == l.regions_1g + one * size_of::<RegionEntry>()
    &&& l.count_1g == l.count_2m + two * w
    &&& l.stale_pages == l.count_1g + one * w
    &&& l.stale_2m == l.stale_pages + pages * w
    &&& l.stale_1g == l.stale_2m + two * w
    &&& l.stale_end == l.stale_1g + one * w
    &&& l.zero_cursor == l.stale_end
    &&& l.active_2m == l.zero_cursor + pages * w
    &&& l.active_1g == l.active_2m + two
    &&& l.bytes == l.active_1g + one
    &&& l.bytes <= IDENTITY_SPAN
}

/// The layout of the page metadata for `pages` tracked pages, from the page count, `size_of` and
/// nothing else. Boot calls it to size the carve and the kernel's init to place the columns in it, so
/// there is one layout. It ends within the identity-mapped span, as the tracked pages do.
pub fn metadata_layout(pages: usize) -> (l: MetadataLayout)
    requires
        pages * PAGE_SZ <= IDENTITY_SPAN,
    ensures
        layout_sums(l, pages),
{
    let w = core::mem::size_of::<usize>();
    let e = core::mem::size_of::<PageEntry>();
    let g = core::mem::size_of::<RegionEntry>();
    proof {
        lemma_span_within_48_bits();
        crate::layouts::lemma_page_metadata_layouts();
        assert(pages / PAGES_PER_2M <= pages && pages / PAGES_PER_1G <= pages) by {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(pages as int, 1, PAGES_PER_2M as int);
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(pages as int, 1, PAGES_PER_1G as int);
            vstd::arithmetic::div_mod::lemma_div_basics(pages as int);
        }
        // A page entry, two region entries, eight words and two bytes a page are far less than a page.
        assert(PAGE_SZ >= 256) by (compute_only);
        assert((e + 2 * g + 8 * w + 2) * pages <= pages * PAGE_SZ) by (nonlinear_arith)
            requires
                e == 32,
                g == 16,
                w == 8,
                PAGE_SZ >= 256,
                0 <= pages;
    }
    let regions_2m = pages * e;
    let regions_1g = regions_2m + pages / PAGES_PER_2M * g;
    let count_2m = regions_1g + pages / PAGES_PER_1G * g;
    let count_1g = count_2m + pages / PAGES_PER_2M * w;
    let stale_pages = count_1g + pages / PAGES_PER_1G * w;
    let stale_2m = stale_pages + pages * w;
    let stale_1g = stale_2m + pages / PAGES_PER_2M * w;
    let stale_end = stale_1g + pages / PAGES_PER_1G * w;
    let active_2m = stale_end + pages * w;
    let active_1g = active_2m + pages / PAGES_PER_2M;
    let bytes = active_1g + pages / PAGES_PER_1G;
    MetadataLayout {
        page_entries: 0,
        regions_2m,
        regions_1g,
        count_2m,
        count_1g,
        stale_pages,
        stale_2m,
        stale_1g,
        stale_end,
        zero_cursor: stale_end,
        active_2m,
        active_1g,
        bytes,
    }
}

/// Every column of the page metadata starts at an address aligned for its element, in a carve that
/// starts on a page.
pub proof fn lemma_metadata_aligned(carve: int, l: MetadataLayout, pages: usize)
    requires
        0 <= carve,
        carve % PAGE_SZ as int == 0,
        layout_sums(l, pages),
    ensures
        (carve + l.page_entries) % align_of::<PageEntry>() as int == 0,
        (carve + l.regions_2m) % align_of::<RegionEntry>() as int == 0,
        (carve + l.regions_1g) % align_of::<RegionEntry>() as int == 0,
        (carve + l.count_2m) % align_of::<usize>() as int == 0,
        (carve + l.count_1g) % align_of::<usize>() as int == 0,
        (carve + l.stale_pages) % align_of::<usize>() as int == 0,
        (carve + l.stale_2m) % align_of::<usize>() as int == 0,
        (carve + l.stale_1g) % align_of::<usize>() as int == 0,
        (carve + l.zero_cursor) % align_of::<usize>() as int == 0,
{
    crate::layouts::lemma_page_metadata_layouts();
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(carve, PAGE_SZ as int);
    let m = carve / PAGE_SZ as int;
    let p = pages as int;
    let two = (pages / PAGES_PER_2M) as int;
    let one = (pages / PAGES_PER_1G) as int;
    assert(PAGE_SZ as int == ENTRIES as int * 8) by (compute_only);
    let c = m * ENTRIES as int;
    assert(carve == c * 8) by (nonlinear_arith)
        requires
            carve == m * PAGE_SZ as int,
            PAGE_SZ as int == ENTRIES as int * 8,
            c == m * ENTRIES as int;
    // Each offset is a whole number of words: the sums, with the element sizes, in words.
    lemma_whole_words(carve + l.page_entries, c);
    lemma_whole_words(carve + l.regions_2m, c + 4 * p);
    lemma_whole_words(carve + l.regions_1g, c + 4 * p + 2 * two);
    lemma_whole_words(carve + l.count_2m, c + 4 * p + 2 * two + 2 * one);
    lemma_whole_words(carve + l.count_1g, c + 4 * p + 3 * two + 2 * one);
    lemma_whole_words(carve + l.stale_pages, c + 4 * p + 3 * two + 3 * one);
    lemma_whole_words(carve + l.stale_2m, c + 5 * p + 3 * two + 3 * one);
    lemma_whole_words(carve + l.stale_1g, c + 5 * p + 4 * two + 3 * one);
    lemma_whole_words(carve + l.zero_cursor, c + 5 * p + 4 * two + 4 * one);
}

/// An address that is a whole number of words is aligned for a word, and for any element whose
/// alignment is a word.
proof fn lemma_whole_words(x: int, q: int)
    requires
        0 <= q,
        x == q * 8,
    ensures
        x % 8 == 0,
        x % align_of::<usize>() as int == 0,
{
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q, 8);
    lemma_word_aligned(x);
}

/// A page below n regions of p pages each is in one of them.
pub proof fn lemma_region_of_page(i: int, p: int, n: int)
    requires
        0 <= i < n * p,
        0 < p,
    ensures
        0 <= i / p < n,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, p);
    assert(i / p < n) by (nonlinear_arith)
        requires
            i == p * (i / p) + i % p,
            0 <= i % p,
            i < n * p,
            0 < p;
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i, p);
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

/// The page entries, the region entries and the counts are columns of the page metadata boot carves,
/// placed by metadata_layout. How many pages the table tracks is the length of its page entries, the
/// one length it holds; the region counts are divisions of it.
/// design/page-metadata-sized-from-the-memory-map/.
pub struct BlockTable {
    pub pages: Column<PageEntry>,
    pub regions_2m: Column<RegionEntry>,
    pub regions_1g: Column<RegionEntry>,
    pub count_2m: Column<usize>,
    pub count_1g: Column<usize>,
    /// The permission of every free page, as bytes.
    pub free_perms: Tracked<Map<usize, PagePerm4k>>,
    /// What each region's count counts: its non-free pages, and for a 1G region, the base page of
    /// each typed 2M block inside it.
    pub in_2m: Ghost<Seq<Set<int>>>,
    pub in_1g: Ghost<Seq<Set<int>>>,
}

impl BlockTable {
    /// How many pages the table tracks: the length of its page entries. Every bound on a page index
    /// or a page's address is stated through this and the predicates below.
    pub open spec fn spec_page_count(&self) -> usize {
        self.pages@.len() as usize
    }

    #[verifier::when_used_as_spec(spec_page_count)]
    pub fn page_count(&self) -> (n: usize)
        requires
            self.pages.wf(),
        ensures
            n == self.page_count(),
            n == self.pages@.len(),
    {
        self.pages.len()
    }

    /// The tracked pages are whole 1G regions from address 0 and end within the identity-mapped
    /// span. No proof bounds the count by anything smaller. design/page-metadata-sized-from-the-memory-map/.
    pub open spec fn span_wf(&self) -> bool {
        &&& 0 < self.pages@.len()
        &&& self.pages@.len() % PAGES_PER_1G as nat == 0
        &&& self.pages@.len() * PAGE_SZ <= IDENTITY_SPAN
    }

    /// The page count is the length of the page entries: a length within the span fits a usize.
    pub proof fn lemma_page_count(&self)
        requires
            self.span_wf(),
        ensures
            self.spec_page_count() == self.pages@.len(),
            0 < self.spec_page_count(),
            self.spec_page_count() % PAGES_PER_1G == 0,
            self.spec_page_count() * PAGE_SZ <= IDENTITY_SPAN,
    {
        let n = self.pages@.len() as int;
        assert(n <= n * PAGE_SZ) by (nonlinear_arith)
            requires
                0 <= n,
                PAGE_SZ >= 1;
    }

    /// A tracked page lies within the identity-mapped span, so its address and the end of its page
    /// are below 2^48 and index times PAGE_SZ does not overflow.
    pub proof fn lemma_tracked_in_span(&self, i: int)
        requires
            self.span_wf(),
            self.tracks(i),
        ensures
            0 <= i * PAGE_SZ,
            (i + 1) * PAGE_SZ <= IDENTITY_SPAN,
            IDENTITY_SPAN <= 1usize << 48,
    {
        lemma_span_within_48_bits();
        lemma_pages_in_span(i + 1, self.spec_page_count() as int);
    }

    /// An address in a tracked page is below the identity-mapped span, so the bounds of what lies on a
    /// tracked page come from the span and not from the page count.
    pub proof fn lemma_addr_in_span(&self, a: usize)
        requires
            self.span_wf(),
            self.tracks_addr(a),
        ensures
            a < IDENTITY_SPAN,
            IDENTITY_SPAN <= 1usize << 48,
    {
        let i = a as int / PAGE_SZ as int;
        self.lemma_tracked_in_span(i);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, PAGE_SZ as int);
        assert(a < (i + 1) * PAGE_SZ) by (nonlinear_arith)
            requires
                a == PAGE_SZ * i + a % PAGE_SZ,
                a % PAGE_SZ < PAGE_SZ;
    }

    /// An address in a tracked page is below 2^48, so adding a block's bytes or a node's index to it
    /// does not overflow.
    pub proof fn lemma_addr_fits(&self, a: usize)
        requires
            self.span_wf(),
            self.tracks_addr(a),
        ensures
            a < crate::capability::list::NODE_SPACE,
    {
        self.lemma_addr_in_span(a);
        assert(IDENTITY_SPAN <= crate::capability::list::NODE_SPACE) by (compute_only);
    }

    /// The tracked pages' bytes end within 2^48, so a page index plus a block's pages does not overflow.
    pub proof fn lemma_count_fits(&self)
        requires
            self.span_wf(),
        ensures
            self.pages@.len() * PAGE_SZ <= crate::capability::list::NODE_SPACE,
            self.spec_page_count() == self.pages@.len(),
    {
        assert(IDENTITY_SPAN <= crate::capability::list::NODE_SPACE) by (compute_only);
        self.lemma_page_count();
    }

    /// The 2M and the 1G regions each tile the tracked pages: the page count is a whole number of
    /// either.
    pub proof fn lemma_regions_tile(&self)
        requires
            self.span_wf(),
        ensures
            (self.spec_page_count() / PAGES_PER_2M) * PAGES_PER_2M == self.spec_page_count(),
            (self.spec_page_count() / PAGES_PER_1G) * PAGES_PER_1G == self.spec_page_count(),
    {
        lemma_whole_regions(self.spec_page_count() as int);
    }

    /// How many 2M regions the tracked pages make. Every bound on a 2M region index is stated
    /// through this, as every bound on a page index is through the page count.
    pub open spec fn spec_num_2m(&self) -> usize {
        (self.spec_page_count() / PAGES_PER_2M) as usize
    }

    #[verifier::when_used_as_spec(spec_num_2m)]
    pub fn num_2m(&self) -> (n: usize)
        requires
            self.pages.wf(),
        ensures
            n == self.num_2m(),
    {
        self.page_count() / PAGES_PER_2M
    }

    /// How many 1G regions the tracked pages make.
    pub open spec fn spec_num_1g(&self) -> usize {
        (self.spec_page_count() / PAGES_PER_1G) as usize
    }

    #[verifier::when_used_as_spec(spec_num_1g)]
    pub fn num_1g(&self) -> (n: usize)
        requires
            self.pages.wf(),
        ensures
            n == self.num_1g(),
    {
        self.page_count() / PAGES_PER_1G
    }

    /// How many regions of this level the tracked pages make.
    pub open spec fn spec_level_regions(&self, level: Large) -> usize {
        match level {
            Large::Two => self.spec_num_2m(),
            Large::One => self.spec_num_1g(),
        }
    }

    #[verifier::when_used_as_spec(spec_level_regions)]
    pub fn level_regions(&self, level: Large) -> (n: usize)
        requires
            self.pages.wf(),
        ensures
            n == self.level_regions(level),
    {
        match level {
            Large::Two => self.num_2m(),
            Large::One => self.num_1g(),
        }
    }

    /// The 2M and the 1G regions together are exactly the tracked pages.
    pub proof fn lemma_region_counts(&self)
        requires
            self.span_wf(),
        ensures
            self.num_2m() * PAGES_PER_2M == self.spec_page_count(),
            self.num_1g() * PAGES_PER_1G == self.spec_page_count(),
    {
        self.lemma_regions_tile();
    }

    /// A tracked page's 2M and 1G regions are regions of the table.
    pub proof fn lemma_tracked_regions(&self, i: int)
        requires
            self.span_wf(),
            self.tracks(i),
        ensures
            0 <= region_2m(i) < self.num_2m(),
            0 <= region_1g(i) < self.num_1g(),
    {
        self.lemma_region_counts();
        lemma_region_of_page(i, PAGES_PER_2M as int, self.num_2m() as int);
        lemma_region_of_page(i, PAGES_PER_1G as int, self.num_1g() as int);
    }

    /// Page i is one the table tracks.
    pub open spec fn tracks(&self, i: int) -> bool {
        0 <= i < self.pages@.len()
    }

    /// The n pages from page s end within the tracked pages.
    pub open spec fn tracks_run(&self, s: int, n: int) -> bool {
        s + n <= self.pages@.len()
    }

    /// Address a is in a page the table tracks.
    pub open spec fn tracks_addr(&self, a: usize) -> bool {
        a / PAGE_SZ < self.pages@.len()
    }

    /// The n pages from the one holding address a end within the tracked pages.
    pub open spec fn tracks_addr_run(&self, a: usize, n: int) -> bool {
        a / PAGE_SZ + n <= self.pages@.len()
    }

    /// Whether page i is one the table tracks.
    pub fn page_tracked(&self, i: usize) -> (r: bool)
        requires
            self.pages.wf(),
        ensures
            r == self.tracks(i as int),
    {
        i < self.pages.len()
    }

    /// Whether the n pages from page s end within the tracked pages.
    pub fn run_tracked(&self, s: usize, n: usize) -> (r: bool)
        requires
            self.pages.wf(),
        ensures
            r == self.tracks_run(s as int, n as int),
    {
        let count = self.pages.len();
        s <= count && n <= count - s
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
            Large::Two => forall|i: int| r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M ==> {
                &&& #[trigger] self.pages@[i].kind is Free
                &&& !self.covered(i)
            },
            Large::One => forall|i: int| r * PAGES_PER_1G <= i < (r + 1) * PAGES_PER_1G ==> {
                &&& #[trigger] self.pages@[i].kind is Free
                &&& !self.covered(i)
            },
        }
    }

    /// Each count is the size of its set, and the sets are exactly what they count.
    pub open spec fn counts_wf(&self) -> bool {
        &&& self.span_wf()
        &&& self.pages.wf()
        &&& self.regions_2m.wf()
        &&& self.regions_1g.wf()
        &&& self.count_2m.wf()
        &&& self.count_1g.wf()
        &&& self.regions_2m@.len() == self.num_2m()
        &&& self.regions_1g@.len() == self.num_1g()
        &&& self.count_2m@.len() == self.num_2m()
        &&& self.count_1g@.len() == self.num_1g()
        &&& self.in_2m@.len() == self.num_2m()
        &&& self.in_1g@.len() == self.num_1g()
        &&& forall|r: int| 0 <= r < self.num_2m() ==> {
            &&& (#[trigger] self.in_2m@[r]).len() == self.count_2m@[r]
            &&& self.in_2m@[r].subset_of(set_int_range(r * PAGES_PER_2M, (r + 1) * PAGES_PER_2M))
        }
        &&& forall|r: int| 0 <= r < self.num_1g() ==> {
            &&& (#[trigger] self.in_1g@[r]).len() == self.count_1g@[r]
            &&& self.in_1g@[r].subset_of(set_int_range(r * PAGES_PER_1G, (r + 1) * PAGES_PER_1G))
        }
        &&& forall|i: int| self.tracks(i) ==> {
            &&& self.in_2m@[region_2m(i)].contains(i) == !(#[trigger] self.pages@[i].kind is Free)
            &&& self.in_1g@[region_1g(i)].contains(i) == (!(self.pages@[i].kind is Free)
                || (i % PAGES_PER_2M as int == 0 && self.regions_2m@[i / PAGES_PER_2M as int].typed))
        }
    }

    /// A typed large block has nothing typed inside it or around it.
    pub open spec fn large_wf(&self) -> bool {
        &&& forall|r: int| 0 <= r < self.num_2m() && (#[trigger] self.regions_2m@[r]).typed ==> {
            &&& self.count_2m@[r] == 0
            &&& !self.regions_1g@[r / ENTRIES as int].typed
        }
        &&& forall|r: int| 0 <= r < self.num_1g() && (#[trigger] self.regions_1g@[r]).typed ==>
            self.count_1g@[r] == 0
    }

    /// The table holds a permission for exactly its free pages outside any typed large block.
    pub open spec fn free_wf(&self) -> bool {
        &&& forall|i: usize| #[trigger] self.free_perms@.contains_key(i) ==> {
            &&& self.tracks(i as int)
            &&& self.free_perms@[i].addr() == i * PAGE_SZ
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
        &&& self.span_wf()
        &&& self.pages.wf()
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
            post.pages@.len() == pre.pages@.len(),
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

    /// A 2M region whose count is zero has only free pages.
    pub proof fn lemma_zero_2m_is_free(&self, r: int, i: int)
        requires
            self.counts_wf(),
            0 <= r < self.num_2m(),
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
            0 <= r < self.num_1g(),
            self.count_1g@[r] == 0,
            self.tracks(i),
            region_1g(i) == r,
        ensures
            self.pages@[i].kind is Free,
            !self.regions_2m@[region_2m(i)].typed,
    {
        self.in_1g@[r].lemma_len0_is_empty();
        assert(!self.in_1g@[region_1g(i)].contains(i));
        let b = region_2m(i) * PAGES_PER_2M;
        assert(self.tracks(b));
        assert(region_1g(b) == r);
        assert(b % PAGES_PER_2M as int == 0 && b / PAGES_PER_2M as int == region_2m(i));
        assert(self.in_1g@[region_1g(b)].contains(b) == (!(self.pages@[b].kind is Free)
            || (b % PAGES_PER_2M as int == 0 && self.regions_2m@[b / PAGES_PER_2M as int].typed)));
        assert(!self.in_1g@[region_1g(b)].contains(b));
    }

    /// A free 2M block's count is zero, and neither it nor the 1G block around it is typed.
    pub proof fn lemma_free_2m_is_zero(&self, r: int)
        requires
            self.counts_wf(),
            0 <= r < self.num_2m(),
            self.large_free(Large::Two, r),
        ensures
            self.count_2m@[r] == 0,
            !self.regions_2m@[r].typed,
            !self.regions_1g@[r / ENTRIES as int].typed,
    {
        assert forall|i: int| !self.in_2m@[r].contains(i) by {
            if self.in_2m@[r].contains(i) {
                assert(set_int_range(r * PAGES_PER_2M, (r + 1) * PAGES_PER_2M).contains(i));
                assert(self.tracks(i));
                assert(region_2m(i) == r);
                assert(self.pages@[i].kind is Free);
                assert(self.in_2m@[region_2m(i)].contains(i) == !(self.pages@[i].kind is Free));
            }
        }
        assert(self.in_2m@[r] =~= Set::<int>::empty());
        assert(self.in_2m@[r].len() == 0);
        let b = r * PAGES_PER_2M;
        assert(self.pages@[b].kind is Free);
        assert(!self.covered(b));
        assert(region_2m(b) == r);
        assert(region_1g(b) == r / ENTRIES as int);
    }

    /// A free 1G block's count is zero, and it is not typed.
    pub proof fn lemma_free_1g_is_zero(&self, r: int)
        requires
            self.counts_wf(),
            0 <= r < self.num_1g(),
            self.large_free(Large::One, r),
        ensures
            self.count_1g@[r] == 0,
            !self.regions_1g@[r].typed,
    {
        assert forall|i: int| !self.in_1g@[r].contains(i) by {
            if self.in_1g@[r].contains(i) {
                assert(set_int_range(r * PAGES_PER_1G, (r + 1) * PAGES_PER_1G).contains(i));
                assert(self.tracks(i));
                assert(region_1g(i) == r);
                assert(self.pages@[i].kind is Free);
                assert(!self.covered(i));
                assert(region_2m(i) == i / PAGES_PER_2M as int);
                assert(self.in_1g@[region_1g(i)].contains(i) == (!(self.pages@[i].kind is Free)
                    || (i % PAGES_PER_2M as int == 0 && self.regions_2m@[i / PAGES_PER_2M as int].typed)));
            }
        }
        assert(self.in_1g@[r] =~= Set::<int>::empty());
        assert(self.in_1g@[r].len() == 0);
        let b = r * PAGES_PER_1G;
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
            Large::Two => Set::<usize>::range((r * PAGES_PER_2M) as usize, ((r + 1) * PAGES_PER_2M) as usize),
            Large::One => Set::<usize>::range((r * PAGES_PER_1G) as usize, ((r + 1) * PAGES_PER_1G) as usize),
        }
    }

    /// post is this table changed in the pages of the small run of this order at page alone: every
    /// region's entry, at either level, and every page outside the run is as it was.
    pub open spec fn kept_but_run(&self, post: BlockTable, page: int, order: usize) -> bool {
        &&& post.pages@.len() == self.pages@.len()
        &&& post.regions_2m@ == self.regions_2m@
        &&& post.regions_1g@ == self.regions_1g@
        &&& forall|i: int| self.tracks(i) && !(page <= i < page + order_pages(order)) ==> #[trigger] post.pages@[i] == self.pages@[i]
    }

    /// post is this table changed in the entry of the large block that is region r of this level
    /// alone: every page entry and every other region's entry, at either level, is as it was.
    pub open spec fn kept_but_region(&self, post: BlockTable, level: Large, r: int) -> bool {
        &&& post.pages@ == self.pages@
        &&& match level {
            Large::Two => {
                &&& post.regions_2m@ == self.regions_2m@.update(r, post.regions_2m@[r])
                &&& post.regions_1g@ == self.regions_1g@
            },
            Large::One => {
                &&& post.regions_1g@ == self.regions_1g@.update(r, post.regions_1g@[r])
                &&& post.regions_2m@ == self.regions_2m@
            },
        }
    }

    /// A table left as it was changed in no entry, so in none but region r's.
    pub proof fn lemma_kept_but_region_same(&self, level: Large, r: int)
        requires
            match level {
                Large::Two => 0 <= r < self.regions_2m@.len(),
                Large::One => 0 <= r < self.regions_1g@.len(),
            },
        ensures
            self.kept_but_region(*self, level, r),
    {
        match level {
            Large::Two => assert(self.regions_2m@.update(r, self.regions_2m@[r]) =~= self.regions_2m@),
            Large::One => assert(self.regions_1g@.update(r, self.regions_1g@[r]) =~= self.regions_1g@),
        }
    }

    /// The pages of a large block are those whose region it is.
    pub proof fn lemma_large_pages(level: Large, r: int)
        requires
            match level {
                Large::Two => 0 <= r && (r + 1) * PAGES_PER_2M <= usize::MAX,
                Large::One => 0 <= r && (r + 1) * PAGES_PER_1G <= usize::MAX,
            },
        ensures
            forall|i: usize| #[trigger] Self::large_pages(level, r).contains(i) == Self::in_large(level, r, i as int),
    {
        match level {
            Large::Two => {
                range_set_properties::<usize>((r * PAGES_PER_2M) as usize, ((r + 1) * PAGES_PER_2M) as usize);
            },
            Large::One => {
                range_set_properties::<usize>((r * PAGES_PER_1G) as usize, ((r + 1) * PAGES_PER_1G) as usize);
            },
        }
    }

    /// A table tracking `pages` pages, every page Reserved and every region untyped and counting all
    /// its pages, with no free page, its columns in the carve at `carve` as metadata_layout places
    /// them. `raw` grants the carve; each column's permission is split from it and each entry written,
    /// so what the carve held before is not what this relies on. What `raw` grants past the block
    /// table's columns comes back, for the columns that follow them.
    pub fn new(carve: usize, pages: usize, Tracked(raw): Tracked<PointsToRaw>, Tracked(exposed): Tracked<IsExposed>)
        -> (ret: (Self, Tracked<PointsToRaw>))
        requires
            carve % PAGE_SZ == 0,
            0 < pages,
            pages % PAGES_PER_1G == 0,
            pages * PAGE_SZ <= IDENTITY_SPAN,
            carve + spec_metadata_layout(pages).bytes <= usize::MAX,
            raw.is_range(carve as int, spec_metadata_layout(pages).bytes as int),
            raw.provenance() == exposed@,
        ensures
            ret.0.wf(),
            ret.0.page_count() == pages,
            ret.0.pages@.len() == pages,
            forall|i: int| ret.0.tracks(i) ==> #[trigger] ret.0.pages@[i].kind is Reserved,
            forall|i: int| ret.0.tracks(i) ==> #[trigger] ret.0.pages@[i].object is None,
            forall|r: int| 0 <= r < ret.0.num_2m() ==> !(#[trigger] ret.0.regions_2m@[r]).typed,
            forall|r: int| 0 <= r < ret.0.num_1g() ==> !(#[trigger] ret.0.regions_1g@[r]).typed,
            ret.1@.is_range(
                carve + spec_metadata_layout(pages).stale_pages,
                spec_metadata_layout(pages).bytes - spec_metadata_layout(pages).stale_pages,
            ),
            ret.1@.provenance() == exposed@,
    {
        let l = metadata_layout(pages);
        let ghost c = carve as int;
        let n2 = pages / PAGES_PER_2M;
        let n1 = pages / PAGES_PER_1G;
        proof {
            crate::layouts::lemma_page_metadata_layouts();
            lemma_metadata_aligned(c, l, pages);
        }
        let tracked (first, rest) = raw.split(Set::range(c + l.page_entries, c + l.regions_2m));
        proof {
            assert(rest.dom() =~= Set::range(c + l.regions_2m, c + l.bytes));
        }
        let tracked (second, rest) = rest.split(Set::range(c + l.regions_2m, c + l.regions_1g));
        proof {
            assert(rest.dom() =~= Set::range(c + l.regions_1g, c + l.bytes));
        }
        let tracked (third, rest) = rest.split(Set::range(c + l.regions_1g, c + l.count_2m));
        proof {
            assert(rest.dom() =~= Set::range(c + l.count_2m, c + l.bytes));
        }
        let tracked (fourth, rest) = rest.split(Set::range(c + l.count_2m, c + l.count_1g));
        proof {
            assert(rest.dom() =~= Set::range(c + l.count_1g, c + l.bytes));
        }
        let tracked (fifth, past) = rest.split(Set::range(c + l.count_1g, c + l.stale_pages));
        proof {
            assert(fifth.dom() =~= Set::range(c + l.count_1g, c + l.stale_pages));
            assert(past.dom() =~= Set::range(c + l.stale_pages, c + l.bytes));
        }
        let reserved = PageEntry {
            kind: PageKind::Reserved,
            object: ObjectType::None,
            base: 0,
            order: 0,
            dead: false,
            torn_down: false,
            refs: 0,
        };
        let untyped = RegionEntry { typed: false, dead: false, torn_down: false, refs: 0 };
        let mut table = BlockTable {
            pages: Column::new(carve + l.page_entries, pages, reserved, Tracked(first), Tracked(exposed)),
            regions_2m: Column::new(carve + l.regions_2m, n2, untyped, Tracked(second), Tracked(exposed)),
            regions_1g: Column::new(carve + l.regions_1g, n1, untyped, Tracked(third), Tracked(exposed)),
            count_2m: Column::new(carve + l.count_2m, n2, PAGES_PER_2M, Tracked(fourth), Tracked(exposed)),
            count_1g: Column::new(carve + l.count_1g, n1, PAGES_PER_1G, Tracked(fifth), Tracked(exposed)),
            free_perms: Tracked(Map::tracked_empty()),
            in_2m: Ghost(Seq::empty()),
            in_1g: Ghost(Seq::empty()),
        };
        table.in_2m = Ghost(Seq::new(n2 as nat, |r: int| set_int_range(r * PAGES_PER_2M, (r + 1) * PAGES_PER_2M)));
        table.in_1g = Ghost(Seq::new(n1 as nat, |r: int| set_int_range(r * PAGES_PER_1G, (r + 1) * PAGES_PER_1G)));
        proof {
            assert forall|r: int| 0 <= r < n2 implies {
                &&& (#[trigger] table.in_2m@[r]).len() == table.count_2m@[r]
                &&& table.in_2m@[r].subset_of(set_int_range(r * PAGES_PER_2M, (r + 1) * PAGES_PER_2M))
            } by {
                lemma_int_range(r * PAGES_PER_2M, (r + 1) * PAGES_PER_2M);
            }
            assert forall|r: int| 0 <= r < n1 implies {
                &&& (#[trigger] table.in_1g@[r]).len() == table.count_1g@[r]
                &&& table.in_1g@[r].subset_of(set_int_range(r * PAGES_PER_1G, (r + 1) * PAGES_PER_1G))
            } by {
                lemma_int_range(r * PAGES_PER_1G, (r + 1) * PAGES_PER_1G);
            }
            assert(table.bases_wf()) by { reveal(BlockTable::bases_wf); }
            assert(table.members_wf()) by { reveal(BlockTable::members_wf); }
            assert(table.member_bases_wf()) by { reveal(BlockTable::member_bases_wf); }
        }
        (table, Tracked(past))
    }

    /// Make a non-free page free, taking back its permission.
    fn give_page(&mut self, i: usize, Tracked(perm): Tracked<PagePerm4k>)
        requires
            old(self).counts_wf(),
            old(self).large_wf(),
            old(self).free_wf(),
            old(self).tracks(i as int),
            !(old(self).pages@[i as int].kind is Free),
            perm.addr() == i * PAGE_SZ,
            perm.is_uninit(),
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
            assert forall|r: int| 0 <= r < me.num_2m() implies {
                &&& (#[trigger] me.in_2m@[r]).len() == me.count_2m@[r]
                &&& me.in_2m@[r].subset_of(set_int_range(r * PAGES_PER_2M, (r + 1) * PAGES_PER_2M))
            } by {
            }
            assert forall|r: int| 0 <= r < me.num_1g() implies {
                &&& (#[trigger] me.in_1g@[r]).len() == me.count_1g@[r]
                &&& me.in_1g@[r].subset_of(set_int_range(r * PAGES_PER_1G, (r + 1) * PAGES_PER_1G))
            } by {
            }
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|r: int| 0 <= r < me.num_2m() && (#[trigger] me.regions_2m@[r]).typed implies {
                &&& me.count_2m@[r] == 0
                &&& !me.regions_1g@[r / ENTRIES as int].typed
            } by {
                assert(pre.regions_2m@[r].typed);
            }
            assert forall|r: int| 0 <= r < me.num_1g() && (#[trigger] me.regions_1g@[r]).typed implies
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
            final(self).pages@.len() == old(self).pages@.len(),
            final(self).counts_wf(),
            final(self).large_wf(),
            final(self).free_wf(),
            final(self).pages@ == old(self).pages@.update(i as int, entry),
            final(self).regions_2m@ == old(self).regions_2m@,
            final(self).regions_1g@ == old(self).regions_1g@,
            ret@.addr() == i * PAGE_SZ,
            ret@.is_uninit(),
    {
        let ghost pre = *old(self);
        let (r2, r1) = (i / PAGES_PER_2M, i / PAGES_PER_1G);
        proof {
            assert(pre.in_2m@[region_2m(i as int)].contains(i as int) == !(pre.pages@[i as int].kind is Free));
            assert(!pre.in_2m@[r2 as int].contains(i as int));
            assert(!pre.in_1g@[r1 as int].contains(i as int));
            lemma_int_range(r2 * PAGES_PER_2M, (r2 + 1) * PAGES_PER_2M);
            lemma_int_range(r1 * PAGES_PER_1G, (r1 + 1) * PAGES_PER_1G);
            lemma_len_subset(pre.in_2m@[r2 as int], set_int_range(r2 * PAGES_PER_2M, (r2 + 1) * PAGES_PER_2M));
            lemma_len_subset(pre.in_1g@[r1 as int], set_int_range(r1 * PAGES_PER_1G, (r1 + 1) * PAGES_PER_1G));
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
            assert forall|r: int| 0 <= r < me.num_2m() implies {
                &&& (#[trigger] me.in_2m@[r]).len() == me.count_2m@[r]
                &&& me.in_2m@[r].subset_of(set_int_range(r * PAGES_PER_2M, (r + 1) * PAGES_PER_2M))
            } by {
            }
            assert forall|r: int| 0 <= r < me.num_1g() implies {
                &&& (#[trigger] me.in_1g@[r]).len() == me.count_1g@[r]
                &&& me.in_1g@[r].subset_of(set_int_range(r * PAGES_PER_1G, (r + 1) * PAGES_PER_1G))
            } by {
            }
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|r: int| 0 <= r < me.num_2m() && (#[trigger] me.regions_2m@[r]).typed implies {
                &&& me.count_2m@[r] == 0
                &&& !me.regions_1g@[r / ENTRIES as int].typed
            } by {
                assert(pre.regions_2m@[r].typed);
            }
            assert forall|r: int| 0 <= r < me.num_1g() && (#[trigger] me.regions_1g@[r]).typed implies
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
                Large::Two => r < old(self).num_2m() && entry.typed == old(self).regions_2m@[r as int].typed,
                Large::One => r < old(self).num_1g() && entry.typed == old(self).regions_1g@[r as int].typed,
            },
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
            assert forall|j: int| 0 <= j < me.num_2m() implies
                (#[trigger] me.regions_2m@[j]).typed == pre.regions_2m@[j].typed by {}
            assert forall|j: int| 0 <= j < me.num_1g() implies
                (#[trigger] me.regions_1g@[j]).typed == pre.regions_1g@[j].typed by {}
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|j: int| 0 <= j < me.num_2m() && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / ENTRIES as int].typed
            } by {
                assert(pre.regions_2m@[j].typed);
            }
            assert forall|j: int| 0 <= j < me.num_1g() && (#[trigger] me.regions_1g@[j]).typed implies
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
                Large::Two => r < self.num_2m(),
                Large::One => r < self.num_1g(),
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

    /// Mark a large block dead.
    pub fn mark_large_dead(&mut self, level: Large, r: usize)
        requires
            old(self).wf(),
            match level {
                Large::Two => r < old(self).num_2m(),
                Large::One => r < old(self).num_1g(),
            },
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
                Large::Two => r < old(self).num_2m() && old(self).regions_2m@[r as int].dead,
                Large::One => r < old(self).num_1g() && old(self).regions_1g@[r as int].dead,
            },
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
                Large::Two => r < old(self).num_2m(),
                Large::One => r < old(self).num_1g(),
            },
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
                Large::Two => r < old(self).num_2m() && old(self).regions_2m@[r as int].refs > 0,
                Large::One => r < old(self).num_1g() && old(self).regions_1g@[r as int].refs > 0,
            },
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
            r < old(self).num_2m(),
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
        let r1 = r / ENTRIES;
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
            lemma_int_range(r1 * PAGES_PER_1G, (r1 + 1) * PAGES_PER_1G);
            lemma_len_subset(pre.in_1g@[r1 as int], set_int_range(r1 * PAGES_PER_1G, (r1 + 1) * PAGES_PER_1G));
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
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
                if j % PAGES_PER_2M as int == 0 && j / PAGES_PER_2M as int == r {
                    assert(j == base);
                }
            }
            assert forall|j: int| 0 <= j < me.num_1g() implies {
                &&& (#[trigger] me.in_1g@[j]).len() == me.count_1g@[j]
                &&& me.in_1g@[j].subset_of(set_int_range(j * PAGES_PER_1G, (j + 1) * PAGES_PER_1G))
            } by {
            }
            assert forall|j: int| 0 <= j < me.num_2m() && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / ENTRIES as int].typed
            } by {
                if j != r {
                    assert(pre.regions_2m@[j].typed);
                }
            }
            assert forall|j: int| 0 <= j < me.num_1g() && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * PAGE_SZ
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
            r < old(self).num_2m(),
            forall|i: int| r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M ==> #[trigger] old(self).pages@[i].kind is Reserved,
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
            final(steps).count <= old(steps).count + PAGES_PER_2M,
            final(self).wf(),
            final(self).free_perms == old(self).free_perms,
            final(self).regions_2m@ == old(self).regions_2m@.update(r as int,
                RegionEntry { typed: true, dead: false, torn_down: false, refs: 1 }),
            final(self).regions_1g@ == old(self).regions_1g@,
            !old(self).regions_2m@[r as int].typed,
            !old(self).regions_1g@[r as int / ENTRIES as int].typed,
            forall|i: int| final(self).tracks(i) ==> #[trigger] final(self).pages@[i]
                == if region_2m(i) == r { free_entry() } else { old(self).pages@[i] },
    {
        let ghost pre = *old(self);
        let first = r * PAGES_PER_2M;
        let r1 = r / ENTRIES;
        proof {
            assert(region_2m(first as int) == r);
            assert(region_1g(first as int) == r1);
            assert(pre.pages@[first as int].kind is Reserved);
            pre.lemma_not_free_uncovered(first as int);
            pre.lemma_region_counts();
            pre.lemma_page_count();
            assert(first + PAGES_PER_2M <= self.page_count()) by (nonlinear_arith)
                requires
                    first == r * PAGES_PER_2M,
                    r + 1 <= pre.num_2m(),
                    pre.num_2m() * PAGES_PER_2M == self.page_count(),
                    PAGES_PER_2M > 0;
        }
        let ghost steps0 = steps.count;
        let mut k: usize = 0;
        while k < PAGES_PER_2M
            invariant
                k <= PAGES_PER_2M,
                steps.count == steps0 + k,
                r < pre.num_2m(),
                first == r * PAGES_PER_2M,
                self.tracks_run(first as int, PAGES_PER_2M as int),
                first + PAGES_PER_2M <= usize::MAX,
                self.pages.wf(),
                self.pages@.len() == pre.pages@.len(),
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
        let ghost gone = set_int_range(first + 1, first + PAGES_PER_2M);
        proof {
            lemma_int_range(first + 1, first + PAGES_PER_2M);
            assert forall|j: int| gone.contains(j) implies #[trigger] pre.in_1g@[r1 as int].contains(j) by {
                assert(region_1g(j) == r1);
                assert(pre.pages@[j].kind is Reserved);
            }
            lemma_len_subset(gone, pre.in_1g@[r1 as int]);
            let kept = pre.in_1g@[r1 as int].difference(gone);
            assert(kept + gone =~= pre.in_1g@[r1 as int]);
            assert(kept.disjoint(gone));
            vstd::set_lib::lemma_set_disjoint_lens(kept, gone);
        }
        let c1 = *self.count_1g.get(r1);
        self.count_1g.set(r1, c1 - (PAGES_PER_2M - 1));
        self.count_2m.set(r, 0);
        self.in_2m = Ghost(pre.in_2m@.update(r as int, Set::empty()));
        self.in_1g = Ghost(pre.in_1g@.update(r1 as int, pre.in_1g@[r1 as int].difference(gone)));
        self.regions_2m.set(r, RegionEntry { typed: true, dead: false, torn_down: false, refs: 1 });
        proof {
            let me = *self;
            assert forall|i: int| me.tracks(i) implies #[trigger] me.pages@[i]
                == if region_2m(i) == r { free_entry() } else { pre.pages@[i] } by {
                assert((first <= i < first + PAGES_PER_2M) == (region_2m(i) == r));
            }
            assert forall|j: int| 0 <= j < me.num_2m() implies {
                &&& (#[trigger] me.in_2m@[j]).len() == me.count_2m@[j]
                &&& me.in_2m@[j].subset_of(set_int_range(j * PAGES_PER_2M, (j + 1) * PAGES_PER_2M))
            } by {
            }
            assert forall|j: int| 0 <= j < me.num_1g() implies {
                &&& (#[trigger] me.in_1g@[j]).len() == me.count_1g@[j]
                &&& me.in_1g@[j].subset_of(set_int_range(j * PAGES_PER_1G, (j + 1) * PAGES_PER_1G))
            } by {
            }
            assert forall|j: int| me.tracks(j) implies {
                &&& me.in_2m@[region_2m(j)].contains(j) == !(#[trigger] me.pages@[j].kind is Free)
                &&& me.in_1g@[region_1g(j)].contains(j) == (!(me.pages@[j].kind is Free)
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
                assert((first <= j < first + PAGES_PER_2M) == (region_2m(j) == r));
                if region_2m(j) == r {
                    assert(region_1g(j) == r1);
                    assert(j % PAGES_PER_2M as int == 0 <==> j == first);
                    assert(j / PAGES_PER_2M as int == r);
                    assert(pre.pages@[j].kind is Reserved);
                }
            }
            assert forall|j: int| 0 <= j < me.num_2m() && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / ENTRIES as int].typed
            } by {
                if j != r {
                    assert(pre.regions_2m@[j].typed);
                }
            }
            assert forall|j: int| 0 <= j < me.num_1g() && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| me.tracks(j as int) implies
                (#[trigger] me.free_perms@.contains_key(j)
                    == (me.pages@[j as int].kind is Free && !me.covered(j as int))) by {
                assert(pre.free_perms@.contains_key(j)
                    == (pre.pages@[j as int].kind is Free && !pre.covered(j as int)));
                assert((first <= j < first + PAGES_PER_2M) == (region_2m(j as int) == r));
            }
            assert forall|j: int| me.tracks(j)
                implies Self::same_block(#[trigger] pre.pages@[j], me.pages@[j]) by {
                assert((first <= j < first + PAGES_PER_2M) == (region_2m(j) == r));
            }
            Self::lemma_blocks_wf_same(pre, me);
        }
    }

    /// Type a free 1G block, in constant time: its count says nothing inside it is typed.
    pub fn try_type_1g(&mut self, r: usize) -> (ret: Option<Tracked<Map<usize, PagePerm4k>>>)
        requires
            old(self).wf(),
            r < old(self).num_1g(),
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
            assert forall|i: int| r * PAGES_PER_1G <= i < (r + 1) * PAGES_PER_1G implies {
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
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|j: int| 0 <= j < me.num_2m() && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / ENTRIES as int].typed
            } by {
                assert(pre.regions_2m@[j].typed);
                if j / ENTRIES as int == r {
                    pre.lemma_zero_1g_is_free(r as int, j * PAGES_PER_2M);
                }
            }
            assert forall|j: int| 0 <= j < me.num_1g() && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                if j != r {
                    assert(pre.regions_1g@[j].typed);
                }
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * PAGE_SZ
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
            r < old(self).num_2m(),
            old(self).regions_2m@[r as int].typed,
            old(self).regions_2m@[r as int].dead,
            old(self).regions_2m@[r as int].torn_down,
            old(self).regions_2m@[r as int].refs == 0,
            forall|i: usize| Self::large_pages(Large::Two, r as int).contains(i) ==> #[trigger] holds(perms, i),
            perms.dom() == Self::large_pages(Large::Two, r as int),
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            !final(self).regions_2m@[r as int].typed,
            final(self).large_free(Large::Two, r as int),
            final(self).regions_2m@ == old(self).regions_2m@.update(r as int, final(self).regions_2m@[r as int]),
            final(self).regions_1g@ == old(self).regions_1g@,
    {
        let ghost pre = *old(self);
        let r1 = r / ENTRIES;
        let base = r * PAGES_PER_2M;
        let ghost keys = Self::large_pages(Large::Two, r as int);
        proof {
            assert(region_2m(base as int) == r);
            assert(region_1g(base as int) == r1);
            assert(pre.in_1g@[region_1g(base as int)].contains(base as int)
                == (!(pre.pages@[base as int].kind is Free)
                    || (base as int % PAGES_PER_2M as int == 0 && pre.regions_2m@[base as int / PAGES_PER_2M as int].typed)));
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
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
                if j == base {
                    pre.lemma_zero_2m_is_free(r as int, j);
                }
            }
            assert forall|j: int| 0 <= j < me.num_1g() implies {
                &&& (#[trigger] me.in_1g@[j]).len() == me.count_1g@[j]
                &&& me.in_1g@[j].subset_of(set_int_range(j * PAGES_PER_1G, (j + 1) * PAGES_PER_1G))
            } by {
            }
            assert forall|j: int| 0 <= j < me.num_2m() && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / ENTRIES as int].typed
            } by {
                assert(pre.regions_2m@[j].typed);
            }
            assert forall|j: int| 0 <= j < me.num_1g() && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * PAGE_SZ
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
            assert forall|i: int| r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M implies {
                &&& #[trigger] me.pages@[i].kind is Free
                &&& !me.covered(i)
            } by {
                assert(region_2m(i) == r);
                assert(region_1g(i) == r1);
                pre.lemma_zero_2m_is_free(r as int, i);
            }
        }
    }

    /// A dead 1G block at zero references whose teardown has finished returns to free, with its
    /// permissions.
    pub fn free_1g(&mut self, r: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            r < old(self).num_1g(),
            old(self).regions_1g@[r as int].typed,
            old(self).regions_1g@[r as int].dead,
            old(self).regions_1g@[r as int].torn_down,
            old(self).regions_1g@[r as int].refs == 0,
            forall|i: usize| Self::large_pages(Large::One, r as int).contains(i) ==> #[trigger] holds(perms, i),
            perms.dom() == Self::large_pages(Large::One, r as int),
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
            final(self).wf(),
            final(self).pages@ == old(self).pages@,
            !final(self).regions_1g@[r as int].typed,
            final(self).large_free(Large::One, r as int),
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
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
            } by {
                assert(pre.in_2m@[region_2m(j)].contains(j) == !(pre.pages@[j].kind is Free));
            }
            assert forall|j: int| 0 <= j < me.num_2m() && (#[trigger] me.regions_2m@[j]).typed implies {
                &&& me.count_2m@[j] == 0
                &&& !me.regions_1g@[j / ENTRIES as int].typed
            } by {
                assert(pre.regions_2m@[j].typed);
            }
            assert forall|j: int| 0 <= j < me.num_1g() && (#[trigger] me.regions_1g@[j]).typed implies
                me.count_1g@[j] == 0 by {
                assert(pre.regions_1g@[j].typed);
            }
            assert forall|j: usize| #[trigger] me.free_perms@.contains_key(j) implies {
                &&& me.tracks(j as int)
                &&& me.free_perms@[j].addr() == j * PAGE_SZ
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
            assert forall|i: int| r * PAGES_PER_1G <= i < (r + 1) * PAGES_PER_1G implies {
                &&& #[trigger] me.pages@[i].kind is Free
                &&& !me.covered(i)
            } by {
                assert(region_1g(i) == r);
                pre.lemma_zero_1g_is_free(r as int, i);
            }
        }
    }

    /// Boot hands a reserved page to the table.
    pub fn add_free(&mut self, i: usize, Tracked(perm): Tracked<PagePerm4k>)
        requires
            old(self).wf(),
            old(self).tracks(i as int),
            old(self).pages@[i as int].kind is Reserved,
            perm.addr() == i * PAGE_SZ,
            perm.is_uninit(),
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
            final(self).pages@.len() == old(self).pages@.len(),
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
                    &&& #[trigger] ret->0@[(base + k) as usize].addr() == (base + k) * PAGE_SZ
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
                self.pages@.len() == pre.pages@.len(),
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
                &&& (#[trigger] ret->0@[(base + j) as usize]).addr() == (base + j) * PAGE_SZ
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
            self.pages@.len() == pre.pages@.len(),
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
            final(self).pages@.len() == old(self).pages@.len(),
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
                    || (j % PAGES_PER_2M as int == 0 && me.regions_2m@[j / PAGES_PER_2M as int].typed))
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
            final(self).pages@.len() == old(self).pages@.len(),
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
            final(self).pages@.len() == old(self).pages@.len(),
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
            final(self).pages@.len() == old(self).pages@.len(),
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
            final(self).pages@.len() == old(self).pages@.len(),
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
                &&& #[trigger] perms[(base + k) as usize].addr() == (base + k) * PAGE_SZ
                &&& perms[(base + k) as usize].is_uninit()
            },
        ensures
            final(self).pages@.len() == old(self).pages@.len(),
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
                assert(perms[(base + j) as usize].addr() == (base + j) * PAGE_SZ);
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
                self.pages@.len() == pre.pages@.len(),
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
            self.pages@.len() == pre.pages@.len(),
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
