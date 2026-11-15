// SPDX-License-Identifier: MIT

//! Zeroing a typed block before anything can name it, in bounded steps. A large block takes more than
//! one kernel entry, so its permissions and its cursor stay here between them, and a later call, by
//! whoever retypes the block next, resumes where the last one stopped. See
//! design/teardown-driven-by-retype/. The cursors and the active flags are columns of the page
//! metadata boot carves, design/page-metadata-sized-from-the-memory-map/.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::set_lib::*;
use vstd::raw_ptr::{IsExposed, PointsToRaw};

verus! {

use crate::capability::block::*;
use crate::column::Column;
#[cfg(verus_keep_ghost)]
use crate::column::lemma_byte_aligned;
use crate::define::*;
use crate::pptr::*;
use crate::capability::steps::Steps;

/// The most pages one step zeroes: 64 KiB.
pub const ZERO_CHUNK_PAGES: usize = 16;

/// m holds page i's permission, and the page is zero.
pub open spec fn holds_zero(m: Map<usize, PagePerm4k>, i: usize) -> bool {
    &&& m.contains_key(i)
    &&& m[i].addr() == i * PAGE_SZ
    &&& m[i].is_init()
    &&& page_is_zero(m[i].value())
}

pub struct Zeroing {
    /// How many pages of the block at this base are zero.
    pub cursor: Column<usize>,
    /// The permissions of the blocks being zeroed.
    pub perms: Tracked<Map<usize, PagePerm4k>>,
    /// The block being zeroed at each base, in pages.
    pub blocks: Ghost<Map<usize, usize>>,
    /// Which 2M and 1G regions are being zeroed, for a later retype to read.
    pub active_2m: Column<bool>,
    pub active_1g: Column<bool>,
}

/// A block of this level, in pages.
pub open spec fn level_pages(level: Large) -> usize {
    match level {
        Large::Two => PAGES_PER_2M,
        Large::One => PAGES_PER_1G,
    }
}

/// The level of a large block of this order: 2M for order 9, 1G otherwise. A function rather than
/// the conditional itself, so a trigger over the level is a term the solver can match on.
pub open spec fn large_level(order: u8) -> Large {
    if order == 9 { Large::Two } else { Large::One }
}

/// The first page of region r.
pub open spec fn level_base(level: Large, r: usize) -> usize {
    (r * level_pages(level)) as usize
}

/// A region's pages are the range from its base.
pub proof fn lemma_level_pages(level: Large, r: usize)
    requires
        (r + 1) * level_pages(level) <= usize::MAX,
    ensures
        forall|i: usize| #[trigger] BlockTable::large_pages(level, r as int).contains(i)
            == (level_base(level, r) <= i < level_base(level, r) + level_pages(level)),
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

pub fn pages_of_level(level: Large) -> (ret: usize)
    ensures
        ret == level_pages(level),
{
    match level {
        Large::Two => PAGES_PER_2M,
        Large::One => PAGES_PER_1G,
    }
}

impl Zeroing {
    /// How many regions of this level the active flags cover.
    pub open spec fn regions(&self, level: Large) -> int {
        match level {
            Large::Two => self.active_2m@.len() as int,
            Large::One => self.active_1g@.len() as int,
        }
    }

    pub open spec fn active(&self, level: Large, r: usize) -> bool {
        match level {
            Large::Two => self.active_2m@[r as int],
            Large::One => self.active_1g@[r as int],
        }
    }

    /// The block at b is a whole region, marked active.
    pub open spec fn block_level(&self, b: usize) -> bool {
        ||| {
            &&& self.blocks@[b] == PAGES_PER_2M
            &&& b % PAGES_PER_2M == 0
            &&& b / PAGES_PER_2M < self.active_2m@.len()
            &&& self.active_2m@[(b / PAGES_PER_2M) as int]
        }
        ||| {
            &&& self.blocks@[b] == PAGES_PER_1G
            &&& b % PAGES_PER_1G == 0
            &&& b / PAGES_PER_1G < self.active_1g@.len()
            &&& self.active_1g@[(b / PAGES_PER_1G) as int]
        }
    }

    /// The cursors are one per page of whole 1G regions within the identity-mapped span, and the
    /// active flags one per 2M and one per 1G region of those pages. How many pages that is, the block
    /// table says: zeroing_typed.
    pub open spec fn sizes_wf(&self) -> bool {
        &&& self.cursor@.len() % PAGES_PER_1G as nat == 0
        &&& self.cursor@.len() * PAGE_SZ <= IDENTITY_SPAN
        &&& self.active_2m@.len() == self.cursor@.len() / PAGES_PER_2M as nat
        &&& self.active_1g@.len() == self.cursor@.len() / PAGES_PER_1G as nat
    }

    /// A region the active flags cover is a run of the pages the cursors cover, and those pages end
    /// within the identity-mapped span.
    pub proof fn lemma_region_in_cursors(&self, level: Large, r: usize)
        requires
            self.sizes_wf(),
            r < self.regions(level),
        ensures
            (r + 1) * level_pages(level) <= self.cursor@.len(),
            r * level_pages(level) + level_pages(level) <= self.cursor@.len(),
            self.cursor@.len() * PAGE_SZ <= IDENTITY_SPAN,
            self.cursor@.len() <= IDENTITY_SPAN <= 1usize << 48,
    {
        lemma_span_within_48_bits();
        let n = self.cursor@.len() as int;
        lemma_whole_regions(n);
        let p = level_pages(level) as int;
        let q = n / p;
        assert(q * p == n);
        assert((r + 1) * p <= q * p && (r + 1) * p == r * p + p) by (nonlinear_arith)
            requires
                r + 1 <= q,
                p > 0;
        assert(n <= n * PAGE_SZ) by (nonlinear_arith)
            requires
                0 <= n,
                PAGE_SZ > 0;
    }

    /// An active region's block is being zeroed.
    pub open spec fn active_wf(&self) -> bool {
        &&& self.active_2m.wf()
        &&& self.active_1g.wf()
        &&& forall|r: usize| r < self.active_2m@.len() && #[trigger] self.active_2m@[r as int] ==> {
            &&& self.blocks@.contains_key((r * PAGES_PER_2M) as usize)
            &&& self.blocks@[(r * PAGES_PER_2M) as usize] == PAGES_PER_2M
        }
        &&& forall|r: usize| r < self.active_1g@.len() && #[trigger] self.active_1g@[r as int] ==> {
            &&& self.blocks@.contains_key((r * PAGES_PER_1G) as usize)
            &&& self.blocks@[(r * PAGES_PER_1G) as usize] == PAGES_PER_1G
        }
    }

    /// Reads whether region r is being zeroed.
    pub fn is_active(&self, level: Large, r: usize) -> (ret: bool)
        requires
            self.wf(),
            r < self.regions(level),
        ensures
            ret == self.active(level, r),
            ret ==> self.blocks@.contains_key(level_base(level, r)),
            ret ==> self.blocks@[level_base(level, r)] == level_pages(level),
    {
        match level {
            Large::Two => *self.active_2m.get(r),
            Large::One => *self.active_1g.get(r),
        }
    }

    /// Page k of the block at b is zero if it is below the cursor, and otherwise uninitialised.
    pub open spec fn page_wf(&self, b: usize, k: usize) -> bool {
        let i = (b + k) as usize;
        if k < self.cursor@[b as int] {
            holds_zero(self.perms@, i)
        } else {
            holds(self.perms@, i)
        }
    }

    /// Every page of every block is as its cursor says. Opaque: spelled out, it names a page for
    /// every block and every offset. `lemma_page` reaches one position.
    #[verifier::opaque]
    pub open spec fn pages_wf(&self) -> bool {
        forall|b: usize, k: usize| self.blocks@.contains_key(b) && k < self.blocks@[b]
            ==> #[trigger] self.page_wf(b, k)
    }

    /// Two blocks being zeroed share no page.
    pub open spec fn disjoint_wf(&self) -> bool {
        forall|b1: usize, b2: usize| #[trigger] self.blocks@.contains_key(b1)
            && #[trigger] self.blocks@.contains_key(b2) && b1 != b2
            ==> b1 + self.blocks@[b1] <= b2 || b2 + self.blocks@[b2] <= b1
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.cursor.wf()
        &&& self.sizes_wf()
        &&& forall|b: usize| #[trigger] self.blocks@.contains_key(b) ==> {
            &&& 0 < self.blocks@[b]
            &&& b + self.blocks@[b] <= self.cursor@.len()
            &&& self.cursor@[b as int] <= self.blocks@[b]
            &&& self.block_level(b)
        }
        &&& self.active_wf()
        &&& self.disjoint_wf()
        &&& self.pages_wf()
    }

    pub proof fn lemma_page(&self, b: usize, k: usize)
        requires
            self.wf(),
            self.blocks@.contains_key(b),
            k < self.blocks@[b],
        ensures
            self.page_wf(b, k),
    {
        reveal(Zeroing::pages_wf);
    }

    /// A page of one block is not a page of another.
    pub proof fn lemma_disjoint(&self, b1: usize, k1: usize, b2: usize, k2: usize)
        requires
            self.wf(),
            self.blocks@.contains_key(b1),
            self.blocks@.contains_key(b2),
            b1 != b2,
            k1 < self.blocks@[b1],
            k2 < self.blocks@[b2],
        ensures
            b1 + k1 != b2 + k2,
    {
    }

    /// Nothing being zeroed: every cursor zero and no region active, in the carve at `carve`, as
    /// metadata_layout places the cursors and the active flags in it for `pages` tracked pages. `raw`
    /// grants the carve from the cursors to its end; each column's permission is split from it and each
    /// element written, so what the carve held before is not what this relies on.
    pub fn new(carve: usize, pages: usize, Tracked(raw): Tracked<PointsToRaw>, Tracked(exposed): Tracked<IsExposed>)
        -> (ret: Self)
        requires
            carve % PAGE_SZ == 0,
            pages % PAGES_PER_1G == 0,
            pages * PAGE_SZ <= IDENTITY_SPAN,
            carve + spec_metadata_layout(pages).bytes <= usize::MAX,
            raw.is_range(
                carve + spec_metadata_layout(pages).zero_cursor,
                spec_metadata_layout(pages).bytes - spec_metadata_layout(pages).zero_cursor,
            ),
            raw.provenance() == exposed@,
        ensures
            ret.wf(),
            ret.blocks@ == Map::<usize, usize>::empty(),
            ret.cursor@.len() == pages,
            ret.active_2m@.len() == pages / PAGES_PER_2M,
            ret.active_1g@.len() == pages / PAGES_PER_1G,
    {
        let l = metadata_layout(pages);
        let ghost c = carve as int;
        proof {
            lemma_metadata_aligned(c, l, pages);
            lemma_byte_aligned::<bool>(c + l.active_2m);
            lemma_byte_aligned::<bool>(c + l.active_1g);
        }
        let tracked (first, rest) = raw.split(Set::range(c + l.zero_cursor, c + l.active_2m));
        proof {
            assert(rest.dom() =~= Set::range(c + l.active_2m, c + l.bytes));
        }
        let tracked (second, third) = rest.split(Set::range(c + l.active_2m, c + l.active_1g));
        proof {
            assert(third.dom() =~= Set::range(c + l.active_1g, c + l.bytes));
        }
        let z = Zeroing {
            cursor: Column::new(carve + l.zero_cursor, pages, 0, Tracked(first), Tracked(exposed)),
            perms: Tracked(Map::tracked_empty()),
            blocks: Ghost(Map::empty()),
            active_2m: Column::new(carve + l.active_2m, pages / PAGES_PER_2M, false, Tracked(second), Tracked(exposed)),
            active_1g: Column::new(carve + l.active_1g, pages / PAGES_PER_1G, false, Tracked(third), Tracked(exposed)),
        };
        proof {
            reveal(Zeroing::pages_wf);
            assert forall|x: usize| x < z.active_2m@.len() && #[trigger] z.active_2m@[x as int] implies false by {
                assert(!z.active_2m@[x as int]);
            }
            assert forall|x: usize| x < z.active_1g@.len() && #[trigger] z.active_1g@[x as int] implies false by {
                assert(!z.active_1g@[x as int]);
            }
        }
        z
    }

    /// Start zeroing a region its caller has just typed, taking its permissions. The caller says the
    /// region shares no page with any block already here.
    pub fn begin(&mut self, level: Large, r: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            r < old(self).regions(level),
            perms.dom() == BlockTable::large_pages(level, r as int),
            forall|i: usize| BlockTable::large_pages(level, r as int).contains(i) ==> #[trigger] holds(perms, i),
            forall|b: usize| #[trigger] old(self).blocks@.contains_key(b) ==>
                level_base(level, r) + level_pages(level) <= b || b + old(self).blocks@[b] <= level_base(level, r),
        ensures
            final(self).wf(),
            final(self).blocks@ == old(self).blocks@.insert(level_base(level, r), level_pages(level)),
            final(self).cursor@.len() == old(self).cursor@.len(),
            final(self).cursor@[level_base(level, r) as int] == 0,
            final(self).active(level, r),
            match level {
                Large::Two => final(self).active_2m@ == old(self).active_2m@.update(r as int, true)
                    && final(self).active_1g@ == old(self).active_1g@,
                Large::One => final(self).active_1g@ == old(self).active_1g@.update(r as int, true)
                    && final(self).active_2m@ == old(self).active_2m@,
            },
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_region_in_cursors(level, r);
        }
        let pages = pages_of_level(level);
        let base = r * pages;
        self.cursor.set(base, 0);
        match level {
            Large::Two => { self.active_2m.set(r, true); },
            Large::One => { self.active_1g.set(r, true); },
        }
        proof {
            lemma_level_pages(level, r);
            self.perms.borrow_mut().tracked_union_prefer_right(perms);
        }
        self.blocks = Ghost(pre.blocks@.insert(base, pages));
        proof {
            let me = *self;
            assert forall|k: usize| k < pages implies #[trigger] holds(me.perms@, (base + k) as usize) by {
                assert(BlockTable::large_pages(level, r as int).contains((base + k) as usize));
                assert(holds(perms, (base + k) as usize));
            }
            assert forall|b: usize| #[trigger] me.blocks@.contains_key(b) implies {
                &&& 0 < me.blocks@[b]
                &&& b + me.blocks@[b] <= me.cursor@.len()
                &&& me.cursor@[b as int] <= me.blocks@[b]
                &&& me.block_level(b)
            } by {
                if b != base {
                    assert(pre.block_level(b));
                    assert(me.cursor@[b as int] == pre.cursor@[b as int]);
                }
            }
            assert(me.active_wf()) by {
                assert forall|x: usize| x < me.active_2m@.len() && #[trigger] me.active_2m@[x as int] implies {
                    &&& me.blocks@.contains_key((x * PAGES_PER_2M) as usize)
                    &&& me.blocks@[(x * PAGES_PER_2M) as usize] == PAGES_PER_2M
                } by {
                    if !(level is Two && x == r) {
                        assert(pre.active_2m@[x as int]);
                        assert(pre.blocks@.contains_key((x * PAGES_PER_2M) as usize));
                    }
                }
                assert forall|x: usize| x < me.active_1g@.len() && #[trigger] me.active_1g@[x as int] implies {
                    &&& me.blocks@.contains_key((x * PAGES_PER_1G) as usize)
                    &&& me.blocks@[(x * PAGES_PER_1G) as usize] == PAGES_PER_1G
                } by {
                    if !(level is One && x == r) {
                        assert(pre.active_1g@[x as int]);
                        assert(pre.blocks@.contains_key((x * PAGES_PER_1G) as usize));
                    }
                }
            }
            assert(me.disjoint_wf());
            assert forall|b: usize, k: usize| me.blocks@.contains_key(b) && k < me.blocks@[b]
                implies #[trigger] me.page_wf(b, k) by {
                if b != base {
                    pre.lemma_page(b, k);
                    let i = (b + k) as usize;
                    assert(!perms.dom().contains(i));
                    assert(me.perms@[i] == pre.perms@[i]);
                    assert(me.cursor@[b as int] == pre.cursor@[b as int]);
                }
            }
            reveal(Zeroing::pages_wf);
        }
    }

    /// Zero the next pages of the block, at most 64 KiB. Returns whether it is now all zero.
    pub fn step(&mut self, base: usize, pages: usize, Tracked(steps): Tracked<&mut Steps>) -> (done: bool)
        requires
            old(self).wf(),
            old(self).blocks@.contains_key(base),
            old(self).blocks@[base] == pages,
        ensures
            final(steps).count <= old(steps).count + ZERO_CHUNK_PAGES,
            final(self).wf(),
            final(self).blocks == old(self).blocks,
            final(self).active_2m == old(self).active_2m,
            final(self).active_1g == old(self).active_1g,
            final(self).cursor@.len() == old(self).cursor@.len(),
            done == (final(self).cursor@[base as int] == pages),
            old(self).cursor@[base as int] <= final(self).cursor@[base as int],
            old(self).cursor@[base as int] < pages ==> old(self).cursor@[base as int] < final(self).cursor@[base as int],
            final(self).cursor@[base as int] <= old(self).cursor@[base as int] + ZERO_CHUNK_PAGES,
    {
        let start = *self.cursor.get(base);
        let end = if pages - start < ZERO_CHUNK_PAGES { pages } else { start + ZERO_CHUNK_PAGES };
        let ghost steps0 = steps.count;
        let mut k = start;
        while k != end
            invariant
                self.wf(),
                self.blocks@.contains_key(base),
                self.blocks@[base] == pages,
                self.cursor@[base as int] == k,
                self.cursor@.len() == old(self).cursor@.len(),
                start <= k <= end <= pages,
                end - start <= ZERO_CHUNK_PAGES,
                steps.count == steps0 + (k - start),
                self.active_2m == old(self).active_2m,
                self.active_1g == old(self).active_1g,
                self.blocks == old(self).blocks,
            decreases end - k,
        {
            let ghost pre = *self;
            let i = base + k;
            let tracked mut perm;
            proof {
                pre.lemma_page(base, k);
                perm = self.perms.borrow_mut().tracked_remove(i);
            }
            zero_page(i * PAGE_SZ, Tracked(&mut perm));
            proof {
                self.perms.borrow_mut().tracked_insert(i, perm);
            }
            self.cursor.set(base, k + 1);
            k = k + 1;
            proof {
                steps.step();
                let me = *self;
                assert(me.blocks == pre.blocks);
                assert(me.perms@.dom() =~= pre.perms@.dom());
                assert forall|b: usize, k2: usize| me.blocks@.contains_key(b) && k2 < me.blocks@[b]
                    implies #[trigger] me.page_wf(b, k2) by {
                    pre.lemma_page(b, k2);
                    if b != base {
                        pre.lemma_disjoint(b, k2, base, (k - 1) as usize);
                    } else if k2 != k - 1 {
                        assert(b + k2 != i);
                    }
                }
                reveal(Zeroing::pages_wf);
            }
        }
        end == pages
    }

    /// A region that is all zero leaves here, with its permissions.
    pub fn finish(&mut self, level: Large, r: usize) -> (ret: Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            r < old(self).regions(level),
            old(self).active(level, r),
            old(self).cursor@[level_base(level, r) as int] == level_pages(level),
        ensures
            final(self).wf(),
            final(self).blocks@ == old(self).blocks@.remove(level_base(level, r)),
            final(self).cursor == old(self).cursor,
            !final(self).active(level, r),
            match level {
                Large::Two => final(self).active_2m@ == old(self).active_2m@.update(r as int, false)
                    && final(self).active_1g@ == old(self).active_1g@,
                Large::One => final(self).active_1g@ == old(self).active_1g@.update(r as int, false)
                    && final(self).active_2m@ == old(self).active_2m@,
            },
            ret@.dom() == BlockTable::large_pages(level, r as int),
            forall|k: usize| k < level_pages(level) ==> #[trigger] holds_zero(ret@, (level_base(level, r) + k) as usize),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_region_in_cursors(level, r);
        }
        let pages = pages_of_level(level);
        let base = r * pages;
        let ghost keys = BlockTable::large_pages(level, r as int);
        let tracked taken;
        match level {
            Large::Two => { self.active_2m.set(r, false); },
            Large::One => { self.active_1g.set(r, false); },
        }
        proof {
            lemma_level_pages(level, r);
            assert forall|i: usize| #[trigger] keys.contains(i) implies pre.perms@.dom().contains(i) by {
                pre.lemma_page(base, (i - base) as usize);
            }
            taken = self.perms.borrow_mut().tracked_remove_keys(keys);
        }
        self.blocks = Ghost(pre.blocks@.remove(base));
        proof {
            let me = *self;
            assert forall|k: usize| k < pages implies #[trigger] holds_zero(taken, (base + k) as usize) by {
                pre.lemma_page(base, k);
                assert(keys.contains((base + k) as usize));
            }
            assert forall|b: usize| #[trigger] me.blocks@.contains_key(b) implies {
                &&& 0 < me.blocks@[b]
                &&& b + me.blocks@[b] <= me.cursor@.len()
                &&& me.cursor@[b as int] <= me.blocks@[b]
                &&& me.block_level(b)
            } by {
                assert(pre.block_level(b));
                assert(b != base);
            }
            assert(me.active_wf()) by {
                assert forall|x: usize| x < me.active_2m@.len() && #[trigger] me.active_2m@[x as int] implies {
                    &&& me.blocks@.contains_key((x * PAGES_PER_2M) as usize)
                    &&& me.blocks@[(x * PAGES_PER_2M) as usize] == PAGES_PER_2M
                } by {
                    assert(pre.active_2m@[x as int]);
                    assert(pre.blocks@.contains_key((x * PAGES_PER_2M) as usize));
                    assert(pre.blocks@[base] == pages);
                    match level {
                        Large::Two => {
                            assert(x != r);
                            assert(x * PAGES_PER_2M != r * PAGES_PER_2M) by (nonlinear_arith)
                                requires x != r;
                        },
                        Large::One => {},
                    }
                }
                assert forall|x: usize| x < me.active_1g@.len() && #[trigger] me.active_1g@[x as int] implies {
                    &&& me.blocks@.contains_key((x * PAGES_PER_1G) as usize)
                    &&& me.blocks@[(x * PAGES_PER_1G) as usize] == PAGES_PER_1G
                } by {
                    assert(pre.active_1g@[x as int]);
                    assert(pre.blocks@.contains_key((x * PAGES_PER_1G) as usize));
                    assert(pre.blocks@[base] == pages);
                }
            }
            assert forall|b: usize, k: usize| me.blocks@.contains_key(b) && k < me.blocks@[b]
                implies #[trigger] me.page_wf(b, k) by {
                pre.lemma_page(b, k);
                let i = (b + k) as usize;
                assert(!keys.contains(i)) by {
                    if keys.contains(i) {
                        pre.lemma_disjoint(b, k, base, (i - base) as usize);
                    }
                }
                assert(me.perms@[i] == pre.perms@[i]);
            }
            reveal(Zeroing::pages_wf);
        }
        Tracked(taken)
    }
}

} // verus!
