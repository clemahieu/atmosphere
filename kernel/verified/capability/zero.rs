//! Zeroing a typed block before anything can name it, in bounded steps. A large block takes more than
//! one kernel entry, so its permissions and its cursor stay here between them, and a later call, by
//! whoever retypes the block next, resumes where the last one stopped. See the design on atmo-6x9.6.7,
//! section 6.
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

use crate::array::Array;
use crate::capability::block::*;
use crate::define::*;
use crate::pptr::*;

/// The most pages one step zeroes: 64 KiB.
pub const ZERO_CHUNK_PAGES: usize = 16;

/// m holds page i's permission, and the page is zero.
pub open spec fn holds_zero(m: Map<usize, PagePerm4k>, i: usize) -> bool {
    &&& m.contains_key(i)
    &&& m[i].addr() == i * 4096
    &&& m[i].is_init()
    &&& page_is_zero(m[i].value())
}

pub struct Zeroing {
    /// How many pages of the block at this base are zero.
    pub cursor: Array<usize, NUM_PAGES>,
    /// The permissions of the blocks being zeroed.
    pub perms: Tracked<Map<usize, PagePerm4k>>,
    /// The block being zeroed at each base, in pages.
    pub blocks: Ghost<Map<usize, usize>>,
}

impl Zeroing {
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
        &&& forall|b: usize| #[trigger] self.blocks@.contains_key(b) ==> {
            &&& 0 < self.blocks@[b]
            &&& b + self.blocks@[b] <= NUM_PAGES
            &&& self.cursor@[b as int] <= self.blocks@[b]
        }
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

    /// Start with nothing being zeroed, in place, since the array cannot move by value. A stale
    /// cursor is harmless: `begin` resets it.
    pub fn init(&mut self)
        requires
            old(self).cursor.wf(),
        ensures
            final(self).wf(),
            final(self).blocks@ == Map::<usize, usize>::empty(),
    {
        self.perms = Tracked(Map::tracked_empty());
        self.blocks = Ghost(Map::empty());
        proof {
            reveal(Zeroing::pages_wf);
        }
    }

    /// Start zeroing a block its caller has just typed, taking its permissions. The dom clause says no
    /// page of it is already here, which is what keeps blocks being zeroed apart.
    pub fn begin(&mut self, base: usize, pages: usize, Tracked(perms): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            !old(self).blocks@.contains_key(base),
            pages > 0,
            base + pages <= NUM_PAGES,
            forall|k: usize| k < pages ==> #[trigger] holds(perms, (base + k) as usize),
            forall|k: usize| k < pages ==> !#[trigger] old(self).perms@.contains_key((base + k) as usize),
            perms.dom().disjoint(old(self).perms@.dom()),
        ensures
            final(self).wf(),
            final(self).blocks@ == old(self).blocks@.insert(base, pages),
            final(self).cursor@[base as int] == 0,
    {
        let ghost pre = *old(self);
        self.cursor.set(base, 0);
        proof {
            self.perms.borrow_mut().tracked_union_prefer_right(perms);
        }
        self.blocks = Ghost(pre.blocks@.insert(base, pages));
        proof {
            let me = *self;
            // The new block is apart from every other: its pages are not in the old map, and
            // theirs are.
            assert forall|b2: usize| #[trigger] pre.blocks@.contains_key(b2) && b2 != base
                implies base + pages <= b2 || b2 + pre.blocks@[b2] <= base by {
                if !(base + pages <= b2 || b2 + pre.blocks@[b2] <= base) {
                    let m = if base < b2 { b2 } else { base };
                    let k = (m - base) as usize;
                    let k2 = (m - b2) as usize;
                    assert(k < pages);
                    assert(k2 < pre.blocks@[b2]);
                    pre.lemma_page(b2, k2);
                    assert(pre.perms@.contains_key((b2 + k2) as usize));
                    assert(!pre.perms@.contains_key((base + k) as usize));
                    assert(false);
                }
            }
            assert(me.disjoint_wf());
            assert forall|b: usize, k: usize| me.blocks@.contains_key(b) && k < me.blocks@[b]
                implies #[trigger] me.page_wf(b, k) by {
                if b == base {
                    assert(holds(perms, (base + k) as usize));
                } else {
                    pre.lemma_page(b, k);
                    let i = (b + k) as usize;
                    assert(!perms.dom().contains(i));
                    assert(me.perms@[i] == pre.perms@[i]);
                }
            }
            reveal(Zeroing::pages_wf);
        }
    }

    /// Zero the next pages of the block, at most 64 KiB. Returns whether it is now all zero.
    pub fn step(&mut self, base: usize, pages: usize) -> (done: bool)
        requires
            old(self).wf(),
            old(self).blocks@.contains_key(base),
            old(self).blocks@[base] == pages,
        ensures
            final(self).wf(),
            final(self).blocks == old(self).blocks,
            done == (final(self).cursor@[base as int] == pages),
            old(self).cursor@[base as int] < pages ==> old(self).cursor@[base as int] < final(self).cursor@[base as int],
            final(self).cursor@[base as int] <= old(self).cursor@[base as int] + ZERO_CHUNK_PAGES,
    {
        let start = *self.cursor.get(base);
        let end = if pages - start < ZERO_CHUNK_PAGES { pages } else { start + ZERO_CHUNK_PAGES };
        let mut k = start;
        while k != end
            invariant
                self.wf(),
                self.blocks@.contains_key(base),
                self.blocks@[base] == pages,
                self.cursor@[base as int] == k,
                start <= k <= end <= pages,
            decreases end - k,
        {
            let ghost pre = *self;
            let i = base + k;
            let tracked mut perm;
            proof {
                pre.lemma_page(base, k);
                perm = self.perms.borrow_mut().tracked_remove(i);
            }
            zero_page(i * 4096, Tracked(&mut perm));
            proof {
                self.perms.borrow_mut().tracked_insert(i, perm);
            }
            self.cursor.set(base, k + 1);
            k = k + 1;
            proof {
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

    /// A block that is all zero leaves here, with its permissions.
    pub fn finish(&mut self, base: usize, pages: usize) -> (ret: Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            old(self).blocks@.contains_key(base),
            old(self).blocks@[base] == pages,
            old(self).cursor@[base as int] == pages,
        ensures
            final(self).wf(),
            final(self).blocks@ == old(self).blocks@.remove(base),
            forall|k: usize| k < pages ==> #[trigger] holds_zero(ret@, (base + k) as usize),
    {
        let ghost pre = *old(self);
        let ghost keys = Set::<usize>::range(base, (base + pages) as usize);
        let tracked taken;
        proof {
            range_set_properties::<usize>(base, (base + pages) as usize);
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
