// SPDX-License-Identifier: MIT

//! The eager source: spans of a window of a few blocks, and frames and table pages retyped from a
//! small untyped, with no fault delivery.
//!
//! `Spans` is the window's bookkeeping, which the contract's view rests on: which blocks of the window
//! a span holds, and the spans by base. `Record` is what the source knows of its untyped: each page
//! free, held as a frame for reuse, mapped, or taken by a table page or by a retype the kernel
//! refused, and which tables of the window's path are linked. The record decides nothing the view
//! states, so its proof is that every index and address it computes is in range; whether a frame is
//! there to back a page is the kernel's to say, and a refusal anywhere refuses the run.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

use aheap::arch::*;
use aheap::source::*;

use crate::glue::*;

verus! {

broadcast use group_raw_ptr_axioms;

/// The blocks of the window spans are handed out from.
pub const WINDOW_BLOCKS: usize = 4;

/// The window's bytes.
pub const WINDOW_BYTES: usize = WINDOW_BLOCKS * BLOCK_BYTES;

/// What one entry of the level above a block's table maps: the window lies inside one such region,
/// so its blocks share their tables above the leaf's.
pub const REGION_BYTES: usize = BLOCK_BYTES * BLOCK_PAGES;

/// The most pages of untyped the record tracks.
pub const MAX_PAGES: usize = 64;

/// The pages of a table page's block, order 3.
pub const TABLE_PAGES: usize = 8;

/// A page of the untyped nothing has retyped.
const FREE: u8 = 0;

/// A page retyped as a frame whose capability the source holds, mapped nowhere.
const HELD: u8 = 1;

/// A page retyped as a frame and mapped at the address the record names.
const MAPPED: u8 = 2;

/// A page the source does not use again: a table page's, or one whose retype or unmap was refused.
const TAKEN: u8 = 3;

/// Scaling by a whole number of units keeps order and distributes over a sum.
proof fn lemma_scale(a: int, b: int, c: int)
    requires
        0 <= c,
    ensures
        a <= b ==> a * c <= b * c,
        (a + b) * c == a * c + b * c,
{
    assert(a <= b ==> a * c <= b * c) by (nonlinear_arith)
        requires
            0 <= c,
    ;
    assert((a + b) * c == a * c + b * c) by (nonlinear_arith);
}

/// The window's bookkeeping: its base, which of its blocks a span holds, the length of the span
/// that starts at each block, and the spans by base with the block each starts at.
struct Spans {
    window: usize,
    used: [bool; WINDOW_BLOCKS],
    lengths: [usize; WINDOW_BLOCKS],
    map: Ghost<Map<int, Span>>,
    index: Ghost<Map<int, int>>,
}

impl Spans {
    /// The span at `base` starts at a block of the window, holds that many blocks of it, all marked
    /// used, and its length is recorded at its first block.
    spec fn holds(&self, base: int) -> bool {
        let j = self.index@[base];
        let blocks = self.map@[base].blocks;
        &&& self.index@.contains_key(base)
        &&& 0 <= j
        &&& blocks > 0
        &&& j + blocks <= WINDOW_BLOCKS
        &&& base == self.window + j * BLOCK_BYTES
        &&& self.lengths@[j] == blocks
        &&& forall|k: int| j <= k < j + blocks ==> #[trigger] self.used@[k]
    }

    spec fn inv(&self) -> bool {
        &&& self.window > 0
        &&& self.window as int % BLOCK_BYTES as int == 0
        &&& self.window + WINDOW_BYTES <= usize::MAX
        &&& forall|base: int| #[trigger] self.map@.contains_key(base) ==> self.holds(base)
    }

    /// The first run of `blocks` blocks no span holds, as a new span with nothing backed; or none.
    /// `view` is the source's view, whose spans these are.
    fn reserve(&mut self, blocks: usize, view: Ghost<SourceView>) -> (r: Option<usize>)
        requires
            old(self).inv(),
            blocks > 0,
            view@.spans == old(self).map@,
        ensures
            final(self).inv(),
            match r {
                None => final(self).map@ == old(self).map@,
                Some(base) => {
                    &&& view@.fits(base as int, blocks as nat)
                    &&& final(self).map@ == old(self).map@.insert(base as int, Span { blocks: blocks as nat, backed: Set::empty() })
                },
            },
        no_unwind
    {
        if blocks > WINDOW_BLOCKS {
            return None;
        }
        let mut first: usize = 0;
        while first + blocks <= WINDOW_BLOCKS
            invariant
                self == old(self),
                self.inv(),
                0 < blocks <= WINDOW_BLOCKS,
                view@.spans == old(self).map@,
                first <= WINDOW_BLOCKS,
            decreases WINDOW_BLOCKS - first,
        {
            let mut t: usize = 0;
            let mut free = true;
            while t < blocks
                invariant
                    self == old(self),
                    first + blocks <= WINDOW_BLOCKS,
                    t <= blocks,
                    free ==> forall|u: int| first <= u < first + t ==> !#[trigger] self.used@[u],
                decreases blocks - t,
            {
                if self.used[first + t] {
                    free = false;
                }
                t += 1;
            }
            if free {
                proof {
                    lemma_scale(first as int, WINDOW_BLOCKS as int, BLOCK_BYTES as int);
                    lemma_scale(first as int + blocks, WINDOW_BLOCKS as int, BLOCK_BYTES as int);
                    lemma_scale(first as int, blocks as int, BLOCK_BYTES as int);
                }
                let base = self.window + first * BLOCK_BYTES;
                let ghost view = view@;
                proof {
                    lemma_mod_multiples_vanish(first as int, self.window as int, BLOCK_BYTES as int);
                    assert forall|other: int| #[trigger] view.spans.contains_key(other) implies view.apart(
                        base as int,
                        blocks as nat,
                        other,
                    ) by {
                        assert(self.holds(other));
                        let j = self.index@[other];
                        let length = self.map@[other].blocks;
                        if !(first + blocks <= j || j + length <= first) {
                            let shared = if first >= j {
                                first as int
                            } else {
                                j
                            };
                            assert(self.used@[shared]);
                            assert(!self.used@[shared]);
                        }
                        lemma_scale(j, length as int, BLOCK_BYTES as int);
                        lemma_scale(first as int + blocks, j, BLOCK_BYTES as int);
                        lemma_scale(j + length, first as int, BLOCK_BYTES as int);
                    }
                }
                let ghost before = *self;
                t = 0;
                while t < blocks
                    invariant
                        first + blocks <= WINDOW_BLOCKS,
                        t <= blocks,
                        self.window == before.window,
                        self.lengths == before.lengths,
                        self.map == before.map,
                        self.index == before.index,
                        forall|u: int| 0 <= u < WINDOW_BLOCKS && !(first <= u < first + t) ==> #[trigger] self.used@[u] == before.used@[u],
                        forall|u: int| first <= u < first + t ==> #[trigger] self.used@[u],
                    decreases blocks - t,
                {
                    self.used[first + t] = true;
                    t += 1;
                }
                self.lengths[first] = blocks;
                self.map = Ghost(self.map@.insert(base as int, Span { blocks: blocks as nat, backed: Set::empty() }));
                self.index = Ghost(self.index@.insert(base as int, first as int));
                proof {
                    assert forall|b: int| #[trigger] self.map@.contains_key(b) implies self.holds(b) by {
                        if b != base as int {
                            assert(before.holds(b));
                            let j = before.index@[b];
                            if j == first as int {
                                assert(before.used@[j]);
                                assert(!before.used@[j]);
                            }
                            assert forall|k: int| j <= k < j + before.map@[b].blocks implies #[trigger] self.used@[k] by {
                                assert(before.used@[k]);
                            }
                        }
                    }
                }
                return Some(base);
            }
            first += 1;
        }
        None
    }

    /// Puts a view of the same spans, with the same lengths, in place of the one held.
    fn rewrite(&mut self, map: Ghost<Map<int, Span>>)
        requires
            old(self).inv(),
            forall|b: int| #[trigger] map@.contains_key(b) <==> old(self).map@.contains_key(b),
            forall|b: int| #[trigger] map@.contains_key(b) ==> map@[b].blocks == old(self).map@[b].blocks,
        ensures
            final(self).inv(),
            final(self).map@ == map@,
        no_unwind
    {
        let ghost before = *self;
        self.map = map;
        assert forall|b: int| #[trigger] self.map@.contains_key(b) implies self.holds(b) by {
            assert(before.holds(b));
        }
    }

    /// Gives up the span at `span`, freeing its blocks. `view` is the source's view, whose spans these
    /// are.
    fn release(&mut self, span: usize, view: Ghost<SourceView>)
        requires
            old(self).inv(),
            old(self).map@.contains_key(span as int),
            view@.spans == old(self).map@,
            view@.wf(),
        ensures
            final(self).inv(),
            final(self).map@ == old(self).map@.remove(span as int),
        no_unwind
    {
        let ghost view = view@;
        let ghost j = self.index@[span as int];
        proof {
            assert(self.holds(span as int));
            lemma_scale(0, j, BLOCK_BYTES as int);
            lemma_div_multiples_vanish(j, BLOCK_BYTES as int);
            assert(span - self.window == BLOCK_BYTES * j);
            assert((span - self.window) / BLOCK_BYTES as int == j);
        }
        let first = (span - self.window) / BLOCK_BYTES;
        assert(first == j);
        let length = self.lengths[first];
        let ghost before = *self;
        let mut t: usize = 0;
        while t < length
            invariant
                first + length <= WINDOW_BLOCKS,
                t <= length,
                self.window == before.window,
                self.lengths == before.lengths,
                self.map == before.map,
                self.index == before.index,
                forall|u: int| 0 <= u < WINDOW_BLOCKS && !(first <= u < first + t) ==> #[trigger] self.used@[u] == before.used@[u],
            decreases length - t,
        {
            self.used[first + t] = false;
            t += 1;
        }
        self.map = Ghost(self.map@.remove(span as int));
        self.index = Ghost(self.index@.remove(span as int));
        proof {
            assert forall|b: int| #[trigger] self.map@.contains_key(b) implies self.holds(b) by {
                assert(before.holds(b));
                assert(view.released_span(span as int).fits(span as int, view.spans[span as int].blocks));
                assert(view.released_span(span as int).spans.contains_key(b));
                let i = before.index@[b];
                let blocks = before.map@[b].blocks;
                if !(first + length <= i || i + blocks <= first) {
                    lemma_scale(first as int + length, i, BLOCK_BYTES as int);
                    lemma_scale(i + blocks, first as int, BLOCK_BYTES as int);
                    lemma_scale(i, blocks as int, BLOCK_BYTES as int);
                    lemma_scale(first as int, length as int, BLOCK_BYTES as int);
                    lemma_scale(first as int + length, i + 1, BLOCK_BYTES as int);
                    lemma_scale(i + blocks, first as int + 1, BLOCK_BYTES as int);
                    lemma_scale(i, 1, BLOCK_BYTES as int);
                    lemma_scale(first as int, 1, BLOCK_BYTES as int);
                }
                assert forall|k: int| i <= k < i + blocks implies #[trigger] self.used@[k] by {
                    assert(before.used@[k]);
                }
            }
        }
    }
}

/// What the source knows of its untyped and of the window's tables.
struct Record {
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: usize,
    top: bool,
    middle: bool,
    tabled: [bool; WINDOW_BLOCKS],
    state: [u8; MAX_PAGES],
    owner: [usize; MAX_PAGES],
}

impl Record {
    spec fn inv(&self) -> bool {
        &&& self.pages <= MAX_PAGES
        &&& self.memory + self.pages * PAGE_BYTES <= u64::MAX
        &&& self.slots + MAX_PAGES <= u64::MAX
        &&& self.window + WINDOW_BYTES <= usize::MAX
    }

    /// The physical base of page `i` of the untyped.
    fn page(&self, i: usize) -> u64
        requires
            self.inv(),
            i < self.pages,
        no_unwind
    {
        proof {
            lemma_scale(i as int, self.pages as int, PAGE_BYTES as int);
        }
        self.memory + i as u64 * PAGE_BYTES as u64
    }

    /// A frame the source holds, mapped nowhere: one released before, else a free page retyped as a
    /// frame into its slot. None when no page is free or the kernel refused the retype.
    fn frame(&mut self) -> (r: Option<usize>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            match r {
                Some(i) => i < final(self).pages,
                None => true,
            },
        no_unwind
    {
        let mut i: usize = 0;
        while i < self.pages
            invariant
                self.inv(),
                i <= self.pages,
            decreases self.pages - i,
        {
            if self.state[i] == HELD {
                return Some(i);
            }
            i += 1;
        }
        let mut i = self.pages;
        while i > 0
            invariant
                self.inv(),
                i <= self.pages,
            decreases i,
        {
            i -= 1;
            if self.state[i] == FREE {
                let base = self.page(i);
                if retype_frame(self.untyped, base, self.slots + i as u64) {
                    self.state[i] = HELD;
                    return Some(i);
                }
                self.state[i] = TAKEN;
                return None;
            }
        }
        None
    }

    /// Retypes the lowest free order-3 block of the untyped as a table page of the level below
    /// `level`, and links it at the entry of `level` that `address` names. Whether both were done.
    fn table(&mut self, address: usize, level: u64) -> bool
        requires
            old(self).inv(),
            2 <= level <= 4,
        ensures
            final(self).inv(),
        no_unwind
    {
        let mut group: usize = 0;
        while group + TABLE_PAGES <= self.pages
            invariant
                self.inv(),
                group <= self.pages,
                2 <= level <= 4,
            decreases self.pages - group,
        {
            let mut k: usize = 0;
            let mut free = true;
            while k < TABLE_PAGES
                invariant
                    self.inv(),
                    group + TABLE_PAGES <= self.pages,
                    k <= TABLE_PAGES,
                    2 <= level <= 4,
                decreases TABLE_PAGES - k,
            {
                if self.state[group + k] != FREE {
                    free = false;
                }
                k += 1;
            }
            if free {
                k = 0;
                while k < TABLE_PAGES
                    invariant
                        self.inv(),
                        group + TABLE_PAGES <= self.pages,
                        k <= TABLE_PAGES,
                        2 <= level <= 4,
                    decreases TABLE_PAGES - k,
                {
                    self.state[group + k] = TAKEN;
                    k += 1;
                }
                let base = self.page(group);
                return retype_table_page(self.untyped, base, level - 1) && link(self.space, address, level, self.untyped, base);
            }
            group += TABLE_PAGES;
        }
        false
    }

    /// Backs the page at `addr` of the window: links the tables its path lacks, takes a frame and
    /// maps it there. The permission to the page's bytes, or none when anything was refused.
    fn back_page(&mut self, addr: usize, provenance: Ghost<Provenance>) -> (r: Option<Tracked<PointsToRaw>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            match r {
                Some(perm) => perm@.is_range(addr as int, PAGE_BYTES as int) && perm@.provenance() == provenance@,
                None => true,
            },
        no_unwind
    {
        let window = self.window;
        if !self.top {
            if !self.table(window, 4) {
                return None;
            }
            self.top = true;
        }
        if !self.middle {
            if !self.table(window, 3) {
                return None;
            }
            self.middle = true;
        }
        let offset = if addr >= window {
            addr - window
        } else {
            0
        };
        let mut block = offset / BLOCK_BYTES;
        if block >= WINDOW_BLOCKS {
            block = WINDOW_BLOCKS - 1;
        }
        if !self.tabled[block] {
            proof {
                lemma_scale(block as int, WINDOW_BLOCKS as int, BLOCK_BYTES as int);
            }
            if !self.table(window + block * BLOCK_BYTES, 2) {
                return None;
            }
            self.tabled[block] = true;
        }
        let i = match self.frame() {
            Some(i) => i,
            None => return None,
        };
        match map_page(self.space, addr, self.slots + i as u64, provenance) {
            Some(perm) => {
                self.state[i] = MAPPED;
                self.owner[i] = addr;
                Some(perm)
            },
            None => None,
        }
    }

    /// Unmaps the page at `addr`, taking the permission to its bytes, and holds its frame for reuse.
    fn release_page(&mut self, addr: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).inv(),
            perm@.is_range(addr as int, PAGE_BYTES as int),
        ensures
            final(self).inv(),
        no_unwind
    {
        let mut i: usize = 0;
        while i < self.pages && !(self.state[i] == MAPPED && self.owner[i] == addr)
            invariant
                self.inv(),
                i <= self.pages,
            decreases self.pages - i,
        {
            i += 1;
        }
        let unmapped = unmap_page(self.space, addr, perm);
        if i < self.pages {
            self.state[i] = if unmapped {
                HELD
            } else {
                TAKEN
            };
        }
    }

    /// Unmaps the run of `pages` pages from `start`, taking the permission to its bytes.
    fn release_run(&mut self, start: usize, pages: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).inv(),
            start + pages * PAGE_BYTES <= usize::MAX + 1,
            perm@.is_range(start as int, pages * PAGE_BYTES),
        ensures
            final(self).inv(),
        no_unwind
    {
        let tracked mut rest = perm.get();
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                k <= pages,
                start + pages * PAGE_BYTES <= usize::MAX + 1,
                rest.dom() =~= Set::range(start + k * PAGE_BYTES, start + pages * PAGE_BYTES),
            decreases pages - k,
        {
            proof {
                lemma_scale(k as int + 1, pages as int, PAGE_BYTES as int);
                lemma_scale(k as int, 1, PAGE_BYTES as int);
            }
            let addr = start + k * PAGE_BYTES;
            let tracked (page, others) = rest.split(Set::range(addr as int, addr + PAGE_BYTES));
            proof {
                rest = others;
            }
            self.release_page(addr, Tracked(page));
            k += 1;
            assert(rest.dom() =~= Set::range(start + k * PAGE_BYTES, start + pages * PAGE_BYTES));
        }
    }

    /// Backs the run of `pages` pages from `start` a page at a time: the permission to its bytes, or
    /// none, with each page backed so far given back, when a page was refused.
    fn back_run(&mut self, start: usize, pages: usize, provenance: Ghost<Provenance>) -> (r: Option<Tracked<PointsToRaw>>)
        requires
            old(self).inv(),
            start + pages * PAGE_BYTES <= usize::MAX + 1,
        ensures
            final(self).inv(),
            match r {
                Some(perm) => perm@.is_range(start as int, pages * PAGE_BYTES) && perm@.provenance() == provenance@,
                None => true,
            },
        no_unwind
    {
        let tracked mut run = PointsToRaw::empty(provenance@);
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                k <= pages,
                start + pages * PAGE_BYTES <= usize::MAX + 1,
                run.dom() =~= Set::range(start as int, start + k * PAGE_BYTES),
                run.provenance() == provenance@,
            decreases pages - k,
        {
            proof {
                lemma_scale(k as int + 1, pages as int, PAGE_BYTES as int);
                lemma_scale(k as int, 1, PAGE_BYTES as int);
            }
            let addr = start + k * PAGE_BYTES;
            match self.back_page(addr, provenance) {
                Some(page) => {
                    proof {
                        run = run.join(page.get());
                    }
                    k += 1;
                    assert(run.dom() =~= Set::range(start as int, start + k * PAGE_BYTES));
                },
                None => {
                    self.release_run(start, k, Tracked(run));
                    return None;
                },
            }
        }
        Some(Tracked(run))
    }
}

/// The eager span source over an untyped of at most `MAX_PAGES` pages and a window of
/// `WINDOW_BLOCKS` blocks.
pub struct Eager {
    spans: Spans,
    record: Record,
    exposed: Tracked<IsExposed>,
    /// The requests `reserve` and `back` have refused, each with the spans held then: the view's
    /// record.
    refusals: Ghost<Seq<Refusal>>,
}

impl Eager {
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        self.spans.inv() && self.record.inv()
    }

    /// The source that backs runs in the space at `space` with frames and table pages retyped from the
    /// untyped at `untyped`, whose `pages` pages from physical `memory` it alone retypes, putting
    /// frame capabilities in the empty slots from `slots`; and hands out spans of the window at
    /// `window`, which nothing maps, aligned to a region and with room for the window after it. None
    /// when the window or the counts do not fit.
    pub fn new(space: u64, untyped: u64, memory: u64, pages: usize, slots: u64, window: *mut u8) -> (r: Option<Eager>)
        ensures
            match r {
                Some(source) => source@.wf() && source@.spans.is_empty() && source@.provenance == window@.provenance,
                None => true,
            },
    {
        let addr = window as usize;
        if pages > MAX_PAGES || slots > u64::MAX - MAX_PAGES as u64 {
            return None;
        }
        proof {
            lemma_scale(pages as int, MAX_PAGES as int, PAGE_BYTES as int);
        }
        if memory > u64::MAX - pages as u64 * PAGE_BYTES as u64 || addr == 0 || addr % BLOCK_BYTES != 0 || addr % REGION_BYTES != 0
            || addr > usize::MAX - WINDOW_BYTES {
            return None;
        }
        let exposed = expose_provenance(window);
        let source = Eager {
            spans: Spans {
                window: addr,
                used: [false; WINDOW_BLOCKS],
                lengths: [0; WINDOW_BLOCKS],
                map: Ghost(Map::empty()),
                index: Ghost(Map::empty()),
            },
            record: Record {
                space,
                untyped,
                memory,
                pages,
                slots,
                window: addr,
                top: false,
                middle: false,
                tabled: [false; WINDOW_BLOCKS],
                state: [FREE; MAX_PAGES],
                owner: [0; MAX_PAGES],
            },
            exposed,
            refusals: Ghost(Seq::empty()),
        };
        assert(source@.spans =~= Map::empty());
        Some(source)
    }
}

impl SpanSource for Eager {
    closed spec fn view(&self) -> SourceView {
        SourceView { provenance: self.exposed@@, spans: self.spans.map@, refusals: self.refusals@ }
    }

    fn reserve(&mut self, blocks: usize) -> (r: Option<*mut u8>) {
        proof {
            use_type_invariant(&*self);
        }
        let ghost before = self@;
        match self.spans.reserve(blocks, Ghost(before)) {
            None => {
                let ghost r = Refusal { request: Request::Reserve { blocks: blocks as nat }, spans: before.spans };
                proof {
                    lemma_recorded_wf(before, r);
                }
                self.refusals = Ghost(self.refusals@.push(r));
                None
            },
            Some(base) => {
                proof {
                    lemma_reserved_wf(before, base as int, blocks as nat);
                }
                Some(with_exposed_provenance(base, self.exposed))
            },
        }
    }

    fn back(&mut self, span: Ghost<int>, start: usize, pages: usize) -> (r: Option<Tracked<PointsToRaw>>) {
        proof {
            use_type_invariant(&*self);
        }
        let ghost before = self@;
        proof {
            assert(before.released_span(span@).fits(span@, before.spans[span@].blocks));
        }
        match self.record.back_run(start, pages, Ghost(self.exposed@@)) {
            None => {
                let ghost r = Refusal { request: Request::Back { span: span@, start: start as int, pages: pages as nat }, spans: before.spans };
                proof {
                    lemma_recorded_wf(before, r);
                }
                self.refusals = Ghost(self.refusals@.push(r));
                None
            },
            Some(perm) => {
                proof {
                    lemma_backed_run_wf(before, span@, start as int, pages as nat);
                }
                self.spans.rewrite(Ghost(before.backed_run(span@, start as int, pages as nat).spans));
                Some(perm)
            },
        }
    }

    fn release(&mut self, span: Ghost<int>, start: usize, pages: usize, perm: Tracked<PointsToRaw>) {
        proof {
            use_type_invariant(&*self);
        }
        let ghost before = self@;
        proof {
            assert(before.released_span(span@).fits(span@, before.spans[span@].blocks));
            lemma_released_run_wf(before, span@, start as int, pages as nat);
        }
        self.record.release_run(start, pages, perm);
        self.spans.rewrite(Ghost(before.released_run(span@, start as int, pages as nat).spans));
    }

    fn release_span(&mut self, span: usize) {
        proof {
            use_type_invariant(&*self);
            lemma_released_span_wf(self@, span as int);
        }
        self.spans.release(span, Ghost(self@));
    }
}

} // verus!
