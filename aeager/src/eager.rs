// SPDX-License-Identifier: MIT

//! The eager source: spans of a window of a few blocks, and frames and table pages retyped from a
//! small untyped, with no fault delivery.
//!
//! `Spans` is the window's bookkeeping, which the contract's view rests on: which blocks of the window
//! a span holds, and the spans by base. `Record` is what the source knows of its untyped: each page
//! free, held as a frame for reuse, mapped, parked, or taken by a table page or by a retype the kernel
//! refused, and which tables of the window's path are linked. The record decides nothing the view
//! states, so its proof is that every index and address it computes is in range, that every page a
//! span holds backed is one the record maps at its address, and that a released page is parked at its
//! address, its permission the one the record hands out when that address is backed again with no
//! system call, so that back is granted; whether a frame is there to back any other page is the
//! kernel's to say, and a refusal anywhere refuses the run.
//!
//! A released page stays mapped at its address, parked with the permission to its bytes, and backs
//! that address again without a system call. A frame for another address is a held one, else a free
//! page retyped, else a parked page unmapped: the kernel's unmap drops the calling core's translation of
//! the page before it returns (design/flush-without-waiting/), so the frame mapped at its new address,
//! or another frame mapped later at the old one, is what that core reads there.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::iset::ISet;
use vstd::raw_ptr::*;

use acall::step::Caller;
use aheap::arch::*;
use aheap::source::*;
use verified::capability::list::NODES_PER_PAGE;
#[cfg(verus_keep_ghost)]
use verified::capability::table::index_ok;
use verified::capability::table::TABLE_INDICES;

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

/// The most pages of untyped the record tracks: enough for an object of more than a block, which aheap
/// backs whole as a span of its own, beside the table pages of the window's path and the heap's other
/// spans.
pub const MAX_PAGES: usize = 2 * BLOCK_PAGES;

/// The indices a capability table leaf gives its root entry, the first of which is the leaf's hidden
/// node and no slot.
pub const LEAF_INDICES: usize = NODES_PER_PAGE;

/// The slots a leaf gives, past its hidden node.
pub const LEAF_SLOTS: usize = LEAF_INDICES - 1;

/// The slot of the capability of the frame for page `i` of the untyped, when frames go from the slot
/// `slots` on: the `i`-th slot after it, counting only slots, so a run of frames that reaches the end of
/// a leaf goes on past the next leaf's hidden node. The caller provides the leaves those slots lie in.
pub open spec fn frame_slot(slots: int, i: int) -> int {
    let n = slots % LEAF_INDICES as int - 1 + i;
    slots - slots % LEAF_INDICES as int + (n / LEAF_SLOTS as int) * LEAF_INDICES as int + 1 + n % LEAF_SLOTS as int
}

/// From a slot, which is no leaf's hidden node, frame slots rise with the page and none is a hidden node.
proof fn lemma_frame_slot(slots: int, i: int, j: int)
    requires
        slots >= 0,
        slots % LEAF_INDICES as int != 0,
        0 <= i <= j,
    ensures
        frame_slot(slots, i) % LEAF_INDICES as int != 0,
        frame_slot(slots, i) >= slots,
        i < j ==> frame_slot(slots, i) < frame_slot(slots, j),
{
    let l = LEAF_INDICES as int;
    let m = LEAF_SLOTS as int;
    let base = slots - slots % l;
    let ni = slots % l - 1 + i;
    let nj = slots % l - 1 + j;
    lemma_fundamental_div_mod(slots, l);
    lemma_mod_bound(slots, l);
    lemma_fundamental_div_mod(ni, m);
    lemma_mod_bound(ni, m);
    lemma_fundamental_div_mod(nj, m);
    lemma_mod_bound(nj, m);
    lemma_div_pos_is_pos(ni, m);
    let qi = ni / m;
    let qj = nj / m;
    let ri = ni % m;
    let rj = nj % m;
    assert(base == l * (slots / l));
    assert((base + qi * l + 1 + ri) % l == 1 + ri) by {
        lemma_mod_multiples_vanish(slots / l + qi, 1 + ri, l);
        lemma_small_mod((1 + ri) as nat, l as nat);
        assert(base + qi * l + 1 + ri == l * (slots / l + qi) + (1 + ri)) by (nonlinear_arith)
            requires
                base == l * (slots / l),
        ;
    }
    lemma_div_is_ordered(ni, nj, m);
    assert(qi >= 0);
    assert(qi * l >= qi * m + qi) by (nonlinear_arith)
        requires
            qi >= 0,
            l == m + 1,
    ;
    if i < j {
        if qi == qj {
            assert(ri < rj);
        } else {
            assert(qi + 1 <= qj);
            assert(qi * l + l <= qj * l) by (nonlinear_arith)
                requires
                    qi + 1 <= qj,
                    l > 0,
            ;
        }
    }
}

/// The slot of the capability of the frame for page `i`, when frames go from the slot `slots` on.
fn frame_slot_at(slots: u64, i: usize) -> (r: u64)
    requires
        slots < TABLE_INDICES,
        slots as int % LEAF_INDICES as int != 0,
        i <= MAX_PAGES,
    ensures
        r == frame_slot(slots as int, i as int),
    no_unwind
{
    let offset = (slots % LEAF_INDICES as u64) as usize;
    let n = offset - 1 + i;
    proof {
        let l = LEAF_INDICES as int;
        let m = LEAF_SLOTS as int;
        lemma_mod_bound(slots as int, l);
        lemma_fundamental_div_mod(slots as int, l);
        lemma_div_pos_is_pos(n as int, m);
        lemma_fundamental_div_mod(n as int, m);
        lemma_mod_bound(n as int, m);
        assert(n as int / m <= n as int) by (nonlinear_arith)
            requires
                n as int == m * (n as int / m) + n as int % m,
                n as int % m >= 0,
                n as int / m >= 0,
                m >= 1,
        ;
        assert((n as int / m) * l <= n as int * l) by (nonlinear_arith)
            requires
                n as int / m <= n as int,
                l > 0,
        ;
        assert(n as int * l <= (LEAF_INDICES + MAX_PAGES) * LEAF_INDICES) by (nonlinear_arith)
            requires
                n < LEAF_INDICES + MAX_PAGES,
                l == LEAF_INDICES,
        ;
    }
    slots - offset as u64 + (n / LEAF_SLOTS * LEAF_INDICES) as u64 + 1 + (n % LEAF_SLOTS) as u64
}

/// Past the slots one leaf gives, frame slots lie in another leaf.
proof fn lemma_frame_slots_cross_leaves(slots: int)
    requires
        slots >= 0,
        slots % LEAF_INDICES as int != 0,
    ensures
        frame_slot(slots, LEAF_SLOTS as int) / LEAF_INDICES as int != frame_slot(slots, 0) / LEAF_INDICES as int,
{
    let l = LEAF_INDICES as int;
    let m = LEAF_SLOTS as int;
    let n0 = slots % l - 1;
    lemma_mod_bound(slots, l);
    lemma_fundamental_div_mod(slots, l);
    assert(n0 / m == 0) by {
        lemma_basic_div(n0, m);
    }
    assert((m + n0) / m == 1) by {
        lemma_div_plus_one(n0, m);
    }
    assert(n0 % m == n0) by {
        lemma_small_mod(n0 as nat, m as nat);
    }
    assert((m + n0) % m == n0) by {
        lemma_mod_add_multiples_vanish(n0, m);
    }
    let q = slots / l;
    assert(frame_slot(slots, 0) == l * q + 1 + n0);
    assert(frame_slot(slots, m) == l * (q + 1) + 1 + n0) by (nonlinear_arith)
        requires
            frame_slot(slots, m) == slots - slots % l + l + 1 + n0,
            slots == l * q + slots % l,
    ;
    lemma_div_multiples_vanish_fancy(q, 1 + n0, l);
    lemma_div_multiples_vanish_fancy(q + 1, 1 + n0, l);
}

/// The pages of a table page's block, order 3.
pub const TABLE_PAGES: usize = 8;

/// A page of the untyped nothing has retyped.
const FREE: u8 = 0;

/// A page retyped as a frame whose capability the source holds, mapped nowhere: a map of it was refused,
/// or it was parked and unmapped.
const HELD: u8 = 1;

/// A page retyped as a frame and mapped at the address the record names.
const MAPPED: u8 = 2;

/// A page the source does not use again: a table page's, or one whose retype or unmap was refused.
const TAKEN: u8 = 3;

/// A page retyped as a frame and mapped at the address the record names, in no run: its run was
/// released, and the record holds the permission to its bytes until that address is backed again.
const PARKED: u8 = 4;

/// Whether a page in `state` is mapped at the address the record names, its permission handed out or
/// parked.
spec fn occupied(state: u8) -> bool {
    state == MAPPED || state == PARKED
}

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

/// A run of pages from an aligned start grows by the page after it, which no shorter run holds and
/// every longer one does.
proof fn lemma_run_step(start: int, k: int, n: int)
    requires
        start % PAGE_BYTES as int == 0,
        0 <= k < n,
    ensures
        run_pages(start, (k + 1) as nat) =~= run_pages(start, k as nat).insert(start + k * PAGE_BYTES),
        !run_pages(start, k as nat).contains(start + k * PAGE_BYTES),
        run_pages(start, n as nat).contains(start + k * PAGE_BYTES),
{
    let p = PAGE_BYTES as int;
    let b = start + k * p;
    assert(b == p * k + start) by (nonlinear_arith)
        requires
            b == start + k * p,
    ;
    lemma_mod_multiples_vanish(k, start, p);
    lemma_scale(k + 1, n, p);
    lemma_scale(k, 1, p);
    assert forall|a: int| #[trigger] run_pages(start, (k + 1) as nat).contains(a) && a >= b implies a == b by {
        lemma_fundamental_div_mod(a, p);
        lemma_fundamental_div_mod(b, p);
        let qa = a / p;
        let qb = b / p;
        assert(qa == qb) by (nonlinear_arith)
            requires
                a == p * qa,
                b == p * qb,
                b <= a < b + p,
                p > 0,
        ;
    }
}

/// A run of pages lies in every longer run from the same start.
proof fn lemma_run_within(start: int, k: int, n: int)
    requires
        0 <= k <= n,
    ensures
        forall|a: int| #[trigger] run_pages(start, k as nat).contains(a) ==> run_pages(start, n as nat).contains(a),
{
    lemma_scale(k, n, PAGE_BYTES as int);
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
    /// The permission to each parked page's bytes, by page.
    parked: Tracked<Map<int, PointsToRaw>>,
    /// The provenance of every permission the record hands out.
    provenance: Ghost<Provenance>,
}

impl Record {
    /// `caller` is a token of the process whose space the record's system calls change: the slot at
    /// `space` names its own.
    spec fn serves(&self, caller: Caller) -> bool {
        &&& caller.wf()
        &&& names_own_space(caller, self.space)
    }

    spec fn inv(&self) -> bool {
        &&& self.pages <= MAX_PAGES
        &&& self.memory + self.pages * PAGE_BYTES <= u64::MAX
        &&& self.slots < TABLE_INDICES
        &&& self.slots as int % LEAF_INDICES as int != 0
        &&& forall|i: int| 0 <= i < self.pages ==> index_ok(#[trigger] frame_slot(self.slots as int, i) as usize)
        &&& forall|i: int, j: int|
            0 <= i < j < self.pages ==> #[trigger] frame_slot(self.slots as int, i) < #[trigger] frame_slot(self.slots as int, j)
        &&& self.window + WINDOW_BYTES <= usize::MAX
        &&& forall|i: int| 0 <= i < self.pages && #[trigger] self.state@[i] == PARKED ==> {
            &&& self.parked@.contains_key(i)
            &&& self.parked@[i].is_range(self.owner@[i] as int, PAGE_BYTES as int)
            &&& self.parked@[i].provenance() == self.provenance@
        }
        &&& forall|i: int, j: int|
            0 <= i < self.pages && 0 <= j < self.pages && i != j && occupied(#[trigger] self.state@[i]) && occupied(
                #[trigger] self.state@[j],
            ) ==> self.owner@[i] != self.owner@[j]
    }

    /// The addresses of the window whose page's permission the record has handed out or holds parked.
    spec fn live(&self) -> ISet<usize> {
        ISet::new(|a: usize| exists|i: int| 0 <= i < self.pages && occupied(#[trigger] self.state@[i]) && self.owner@[i] == a)
    }

    /// A page is mapped at `addr`, its permission handed out.
    spec fn maps(&self, addr: int) -> bool {
        exists|i: int| 0 <= i < self.pages && #[trigger] self.state@[i] == MAPPED && self.owner@[i] == addr
    }

    /// A page is parked at `addr`, its permission held here.
    spec fn parks(&self, addr: int) -> bool {
        exists|i: int| 0 <= i < self.pages && #[trigger] self.state@[i] == PARKED && self.owner@[i] == addr
    }

    /// Every page mapped in `old`, its permission handed out, still is, at the same address.
    spec fn keeps_mapped(&self, old: &Record) -> bool {
        &&& self.pages == old.pages
        &&& forall|i: int|
            0 <= i < self.pages && #[trigger] old.state@[i] == MAPPED ==> self.state@[i] == MAPPED && self.owner@[i]
                == old.owner@[i]
    }

    /// Every page this record maps at an address was mapped there, with the same state, in `old`.
    spec fn keeps(&self, old: &Record) -> bool {
        &&& self.pages == old.pages
        &&& forall|i: int|
            0 <= i < self.pages && occupied(#[trigger] self.state@[i]) ==> self.state@[i] == old.state@[i] && self.owner@[i]
                == old.owner@[i]
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

    /// The slot of the capability of the frame for page `i` of the untyped.
    fn slot(&self, i: usize) -> (r: u64)
        requires
            self.inv(),
            i < self.pages,
        ensures
            r == frame_slot(self.slots as int, i as int),
            index_ok(r as usize),
        no_unwind
    {
        frame_slot_at(self.slots, i)
    }

    /// A frame the source holds, mapped nowhere: one held before, else a free page retyped as a frame
    /// into its slot, else a parked page unmapped. None when no page is free or parked, or the kernel
    /// refused the retype or the unmap.
    fn frame(&mut self, caller: &mut Tracked<Caller>) -> (r: Option<usize>)
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
        ensures
            final(self).provenance == old(self).provenance,
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps(old(self)),
            final(self).keeps_mapped(old(self)),
            match r {
                Some(i) => i < final(self).pages && final(self).state@[i as int] == HELD,
                None => true,
            },
        no_unwind
    {
        let mut i: usize = 0;
        while i < self.pages
            invariant
                self.inv(),
                self.serves(caller@),
                i <= self.pages,
                self.keeps(old(self)),
                self.keeps_mapped(old(self)),
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
                self.serves(caller@),
                i <= self.pages,
                self.keeps(old(self)),
                self.keeps_mapped(old(self)),
            decreases i,
        {
            i -= 1;
            if self.state[i] == FREE {
                let base = self.page(i);
                let slot = self.slot(i);
                if retype_frame(caller, self.untyped, base, slot) {
                    self.state[i] = HELD;
                    return Some(i);
                }
                self.state[i] = TAKEN;
                return None;
            }
        }
        let mut i: usize = 0;
        while i < self.pages
            invariant
                self.inv(),
                self.serves(caller@),
                i <= self.pages,
                self.provenance == old(self).provenance,
                self.keeps(old(self)),
                self.keeps_mapped(old(self)),
            decreases self.pages - i,
        {
            if self.state[i] == PARKED {
                assert(self.state@[i as int] == PARKED);
                let tracked perm = self.parked.borrow_mut().tracked_remove(i as int);
                if unmap_page(caller, self.space, self.owner[i], Tracked(perm)) {
                    self.state[i] = HELD;
                    return Some(i);
                }
                self.state[i] = TAKEN;
                return None;
            }
            i += 1;
        }
        None
    }

    /// Retypes the lowest free order-3 block of the untyped as a table page of the level below
    /// `level`, and links it at the entry of `level` that `address` names. Whether both were done.
    fn table(&mut self, caller: &mut Tracked<Caller>, address: usize, level: u64) -> bool
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            2 <= level <= 4,
        ensures
            final(self).provenance == old(self).provenance,
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps(old(self)),
            final(self).keeps_mapped(old(self)),
        no_unwind
    {
        let mut group: usize = 0;
        while group + TABLE_PAGES <= self.pages
            invariant
                self.inv(),
                self.serves(caller@),
                group <= self.pages,
                2 <= level <= 4,
                self.keeps(old(self)),
                self.keeps_mapped(old(self)),
            decreases self.pages - group,
        {
            let mut k: usize = 0;
            let mut free = true;
            while k < TABLE_PAGES
                invariant
                    self.inv(),
                    self.serves(caller@),
                    group + TABLE_PAGES <= self.pages,
                    k <= TABLE_PAGES,
                    2 <= level <= 4,
                    self.keeps(old(self)),
                    self.keeps_mapped(old(self)),
                    free ==> forall|u: int| group <= u < group + k ==> #[trigger] self.state@[u] == FREE,
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
                        self.serves(caller@),
                        group + TABLE_PAGES <= self.pages,
                        k <= TABLE_PAGES,
                        2 <= level <= 4,
                        self.keeps(old(self)),
                        self.keeps_mapped(old(self)),
                        forall|u: int| group + k <= u < group + TABLE_PAGES ==> #[trigger] self.state@[u] == FREE,
                    decreases TABLE_PAGES - k,
                {
                    assert(self.state@[group + k] == FREE);
                    self.state[group + k] = TAKEN;
                    k += 1;
                }
                let base = self.page(group);
                return retype_table_page(caller, self.untyped, base, level - 1) && link(caller, self.space, address, level, self.untyped, base);
            }
            group += TABLE_PAGES;
        }
        false
    }

    /// The page occupied at `addr`, mapped or parked there; or `pages` when there is none.
    fn find(&self, addr: usize) -> (r: usize)
        requires
            self.inv(),
        ensures
            r <= self.pages,
            r < self.pages ==> occupied(self.state@[r as int]) && self.owner@[r as int] == addr,
            r == self.pages ==> !self.maps(addr as int) && !self.parks(addr as int),
        no_unwind
    {
        let mut i: usize = 0;
        while i < self.pages
            invariant
                self.inv(),
                i <= self.pages,
                forall|j: int| 0 <= j < i ==> !(occupied(#[trigger] self.state@[j]) && self.owner@[j] == addr),
            decreases self.pages - i,
        {
            if (self.state[i] == MAPPED || self.state[i] == PARKED) && self.owner[i] == addr {
                return i;
            }
            i += 1;
        }
        proof {
            if self.parks(addr as int) {
                let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == addr;
                assert(occupied(self.state@[j]));
            }
            if self.maps(addr as int) {
                let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == MAPPED && self.owner@[j] == addr;
                assert(occupied(self.state@[j]));
            }
        }
        i
    }

    /// Backs the page at `addr` of the window: hands out the page parked there, or links the tables
    /// its path lacks, takes a frame and maps it there. The permission to the page's bytes, or none
    /// when a page is mapped there already or anything was refused. A page parked at `addr` backs it
    /// again with no system call, so that back is granted and leaves every other parked page parked.
    fn back_page(&mut self, caller: &mut Tracked<Caller>, addr: usize, provenance: Ghost<Provenance>) -> (r: Option<Tracked<PointsToRaw>>)
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            provenance@ == old(self).provenance@,
        ensures
            final(self).provenance == old(self).provenance,
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps_mapped(old(self)),
            match r {
                Some(perm) => {
                    &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                    &&& perm@.provenance() == provenance@
                    &&& final(self).maps(addr as int)
                    &&& !old(self).maps(addr as int)
                },
                None => true,
            },
            old(self).parks(addr as int) ==> {
                &&& r is Some
                &&& forall|b: int| b != addr && #[trigger] old(self).parks(b) ==> final(self).parks(b)
            },
        no_unwind
    {
        let i = self.find(addr);
        if i == self.pages {
            return self.map_new(caller, addr, provenance);
        }
        if self.state[i] == MAPPED {
            proof {
                if self.parks(addr as int) {
                    let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == addr;
                    assert(occupied(self.state@[j]));
                }
            }
            return None;
        }
        assert(self.state@[i as int] == PARKED && self.owner@[i as int] == addr);
        let ghost before = *self;
        let tracked perm = self.parked.borrow_mut().tracked_remove(i as int);
        self.state[i] = MAPPED;
        proof {
            assert(self.state@[i as int] == MAPPED);
            if before.maps(addr as int) {
                let j = choose|j: int| 0 <= j < before.pages && #[trigger] before.state@[j] == MAPPED && before.owner@[j] == addr;
                assert(occupied(before.state@[j]));
            }
            assert forall|b: int| b != addr && #[trigger] before.parks(b) implies self.parks(b) by {
                let j = choose|j: int| 0 <= j < before.pages && #[trigger] before.state@[j] == PARKED && before.owner@[j] == b;
                assert(self.state@[j] == PARKED);
            }
        }
        Some(Tracked(perm))
    }

    /// Links the tables the path to `addr` lacks, takes a frame and maps it at `addr`, where no page
    /// is mapped or parked. The permission to the page's bytes, or none when anything was refused.
    fn map_new(&mut self, caller: &mut Tracked<Caller>, addr: usize, provenance: Ghost<Provenance>) -> (r: Option<Tracked<PointsToRaw>>)
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            provenance@ == old(self).provenance@,
            !old(self).maps(addr as int),
            !old(self).parks(addr as int),
        ensures
            final(self).provenance == old(self).provenance,
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps_mapped(old(self)),
            match r {
                Some(perm) => {
                    &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                    &&& perm@.provenance() == provenance@
                    &&& final(self).maps(addr as int)
                },
                None => true,
            },
        no_unwind
    {
        let ghost start = *self;
        proof {
            assert forall|j: int| 0 <= j < self.pages implies !(occupied(#[trigger] self.state@[j]) && self.owner@[j] == addr) by {
                if self.state@[j] == MAPPED && self.owner@[j] == addr {
                    assert(self.maps(addr as int));
                }
                if self.state@[j] == PARKED && self.owner@[j] == addr {
                    assert(self.parks(addr as int));
                }
            }
        }
        let window = self.window;
        if !self.top {
            let ghost before = *self;
            let linked = self.table(caller, window, 4);
            proof {
                lemma_mapped_trans(*self, before, start);
            }
            if !linked {
                return None;
            }
            self.top = true;
        }
        if !self.middle {
            let ghost before = *self;
            let linked = self.table(caller, window, 3);
            proof {
                lemma_mapped_trans(*self, before, start);
            }
            if !linked {
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
            let ghost before = *self;
            let linked = self.table(caller, window + block * BLOCK_BYTES, 2);
            proof {
                lemma_mapped_trans(*self, before, start);
            }
            if !linked {
                return None;
            }
            self.tabled[block] = true;
        }
        let ghost before = *self;
        let found = self.frame(caller);
        proof {
            lemma_mapped_trans(*self, before, start);
        }
        let i = match found {
            Some(i) => i,
            None => return None,
        };
        let slot = self.slot(i);
        let ghost live = self.live();
        assert(!live.contains(addr));
        match map_page(caller, self.space, addr, slot, provenance, Ghost(live)) {
            Some(perm) => {
                self.state[i] = MAPPED;
                self.owner[i] = addr;
                assert(self.state@[i as int] == MAPPED);
                Some(perm)
            },
            None => None,
        }
    }

    /// Parks the page mapped at `addr`, taking the permission to its bytes, which it hands out again
    /// when that address is backed. Every other page stays as it is.
    fn release_page(&mut self, addr: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).inv(),
            old(self).maps(addr as int),
            perm@.is_range(addr as int, PAGE_BYTES as int),
            perm@.provenance() == old(self).provenance@,
        ensures
            final(self).provenance == old(self).provenance,
            final(self).inv(),
            final(self).space == old(self).space,
            final(self).parks(addr as int),
            forall|a: int| a != addr && #[trigger] old(self).maps(a) ==> final(self).maps(a),
            forall|a: int| #[trigger] old(self).parks(a) ==> final(self).parks(a),
        no_unwind
    {
        let mut i: usize = 0;
        while i < self.pages && !(self.state[i] == MAPPED && self.owner[i] == addr)
            invariant
                self == old(self),
                self.inv(),
                i <= self.pages,
                forall|j: int| 0 <= j < i ==> !(#[trigger] self.state@[j] == MAPPED && self.owner@[j] == addr),
            decreases self.pages - i,
        {
            i += 1;
        }
        assert(i < self.pages) by {
            let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == MAPPED && self.owner@[j] == addr;
            if i >= self.pages {
                assert(self.state@[j] == MAPPED);
            }
        }
        let ghost before = *self;
        self.state[i] = PARKED;
        proof {
            self.parked.borrow_mut().tracked_insert(i as int, perm.get());
            assert(self.state@[i as int] == PARKED);
            assert forall|a: int| a != addr && #[trigger] before.maps(a) implies self.maps(a) by {
                let j = choose|j: int| 0 <= j < before.pages && #[trigger] before.state@[j] == MAPPED && before.owner@[j] == a;
                assert(self.state@[j] == MAPPED);
            }
            assert forall|a: int| #[trigger] before.parks(a) implies self.parks(a) by {
                let j = choose|j: int| 0 <= j < before.pages && #[trigger] before.state@[j] == PARKED && before.owner@[j] == a;
                assert(self.state@[j] == PARKED);
            }
        }
    }

    /// Parks the run of `pages` pages from `start`, each mapped, taking the permission to its bytes.
    fn release_run(&mut self, start: usize, pages: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).inv(),
            start as int % PAGE_BYTES as int == 0,
            start + pages * PAGE_BYTES <= usize::MAX + 1,
            perm@.is_range(start as int, pages * PAGE_BYTES),
            perm@.provenance() == old(self).provenance@,
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).maps(a),
        ensures
            final(self).provenance == old(self).provenance,
            final(self).inv(),
            final(self).space == old(self).space,
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).parks(a),
            forall|a: int| !run_pages(start as int, pages as nat).contains(a) && #[trigger] old(self).maps(a) ==> final(self).maps(a),
            forall|a: int| #[trigger] old(self).parks(a) ==> final(self).parks(a),
        no_unwind
    {
        let tracked mut rest = perm.get();
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                self.space == old(self).space,
                k <= pages,
                start as int % PAGE_BYTES as int == 0,
                start + pages * PAGE_BYTES <= usize::MAX + 1,
                rest.dom() =~= Set::range(start + k * PAGE_BYTES, start + pages * PAGE_BYTES),
                rest.provenance() == self.provenance@,
                self.provenance == old(self).provenance,
                forall|a: int|
                    #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, k as nat).contains(a)
                        ==> self.maps(a),
                forall|a: int| #[trigger] run_pages(start as int, k as nat).contains(a) ==> self.parks(a),
                forall|a: int| !run_pages(start as int, pages as nat).contains(a) && #[trigger] old(self).maps(a) ==> self.maps(a),
                forall|a: int| #[trigger] old(self).parks(a) ==> self.parks(a),
            decreases pages - k,
        {
            proof {
                lemma_scale(k as int + 1, pages as int, PAGE_BYTES as int);
                lemma_scale(k as int, 1, PAGE_BYTES as int);
                lemma_run_step(start as int, k as int, pages as int);
            }
            let addr = start + k * PAGE_BYTES;
            let tracked (page, others) = rest.split(Set::range(addr as int, addr + PAGE_BYTES));
            proof {
                rest = others;
            }
            let ghost before = *self;
            self.release_page(addr, Tracked(page));
            proof {
                assert forall|a: int|
                    #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, (k + 1) as nat).contains(a)
                        implies self.maps(a) by {
                    assert(before.maps(a));
                }
                assert forall|a: int| #[trigger] run_pages(start as int, (k + 1) as nat).contains(a) implies self.parks(a) by {
                    if a != addr {
                        assert(before.parks(a));
                    }
                }
                assert forall|a: int| !run_pages(start as int, pages as nat).contains(a) && #[trigger] old(self).maps(a) implies self.maps(a) by {
                    assert(before.maps(a));
                }
                assert forall|a: int| #[trigger] old(self).parks(a) implies self.parks(a) by {
                    assert(before.parks(a));
                }
            }
            k += 1;
            assert(rest.dom() =~= Set::range(start + k * PAGE_BYTES, start + pages * PAGE_BYTES));
        }
    }

    /// Backs the run of `pages` pages from `start` a page at a time: the permission to its bytes, or
    /// none, with each page backed so far given back, when a page was refused. A run whose every page
    /// is parked is granted.
    fn back_run(&mut self, caller: &mut Tracked<Caller>, start: usize, pages: usize, provenance: Ghost<Provenance>) -> (r: Option<Tracked<PointsToRaw>>)
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            provenance@ == old(self).provenance@,
            start as int % PAGE_BYTES as int == 0,
            start + pages * PAGE_BYTES <= usize::MAX + 1,
        ensures
            final(self).provenance == old(self).provenance,
            final(self).inv(),
            final(self).serves(final(caller)@),
            forall|a: int| #[trigger] old(self).maps(a) ==> final(self).maps(a),
            match r {
                Some(perm) => {
                    &&& perm@.is_range(start as int, pages * PAGE_BYTES)
                    &&& perm@.provenance() == provenance@
                    &&& forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).maps(a)
                },
                None => true,
            },
            (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a)) ==> r is Some,
        no_unwind
    {
        let ghost parked = forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a);
        let tracked mut run = PointsToRaw::empty(provenance@);
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                self.serves(caller@),
                k <= pages,
                start as int % PAGE_BYTES as int == 0,
                start + pages * PAGE_BYTES <= usize::MAX + 1,
                run.dom() =~= Set::range(start as int, start + k * PAGE_BYTES),
                run.provenance() == provenance@,
                provenance@ == self.provenance@,
                self.provenance == old(self).provenance,
                parked == forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a),
                forall|a: int| #[trigger] old(self).maps(a) ==> self.maps(a),
                forall|a: int| #[trigger] run_pages(start as int, k as nat).contains(a) ==> self.maps(a) && !old(self).maps(a),
                parked ==> forall|a: int|
                    #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, k as nat).contains(a)
                        ==> self.parks(a),
            decreases pages - k,
        {
            proof {
                lemma_scale(k as int + 1, pages as int, PAGE_BYTES as int);
                lemma_scale(k as int, 1, PAGE_BYTES as int);
                lemma_run_step(start as int, k as int, pages as int);
            }
            let addr = start + k * PAGE_BYTES;
            let ghost before = *self;
            proof {
                if parked {
                    assert(before.parks(addr as int));
                }
            }
            match self.back_page(caller, addr, provenance) {
                Some(page) => {
                    proof {
                        run = run.join(page.get());
                        lemma_keeps_mapped(*self, before);
                        if old(self).maps(addr as int) {
                            assert(before.maps(addr as int));
                        }
                        if parked {
                            assert forall|a: int|
                                #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, (k + 1) as nat).contains(a)
                                    implies self.parks(a) by {
                                assert(before.parks(a));
                            }
                        }
                    }
                    k += 1;
                    assert(run.dom() =~= Set::range(start as int, start + k * PAGE_BYTES));
                },
                None => {
                    proof {
                        lemma_keeps_mapped(*self, before);
                        lemma_run_within(start as int, k as int, pages as int);
                    }
                    let ghost released = *self;
                    self.release_run(start, k, Tracked(run));
                    proof {
                        assert forall|a: int| #[trigger] old(self).maps(a) implies self.maps(a) by {
                            assert(released.maps(a));
                            if run_pages(start as int, k as nat).contains(a) {
                                assert(!old(self).maps(a));
                            }
                        }
                    }
                    return None;
                },
            }
        }
        Some(Tracked(run))
    }
}

/// Keeping every mapped page is transitive.
proof fn lemma_mapped_trans(c: Record, b: Record, a: Record)
    requires
        c.keeps_mapped(&b),
        b.keeps_mapped(&a),
    ensures
        c.keeps_mapped(&a),
{
    assert forall|i: int| 0 <= i < c.pages && #[trigger] a.state@[i] == MAPPED implies c.state@[i] == MAPPED && c.owner@[i]
        == a.owner@[i] by {
        assert(b.state@[i] == MAPPED);
    }
}

/// A record that keeps every mapped page of another maps every address that one maps.
proof fn lemma_keeps_mapped(new: Record, old: Record)
    requires
        new.keeps_mapped(&old),
    ensures
        forall|a: int| #[trigger] old.maps(a) ==> new.maps(a),
{
    assert forall|a: int| #[trigger] old.maps(a) implies new.maps(a) by {
        let j = choose|j: int| 0 <= j < old.pages && #[trigger] old.state@[j] == MAPPED && old.owner@[j] == a;
        assert(new.state@[j] == MAPPED);
    }
}

/// The eager span source over an untyped of at most `MAX_PAGES` pages and a window of
/// `WINDOW_BLOCKS` blocks.
pub struct Eager {
    spans: Spans,
    record: Record,
    exposed: Tracked<IsExposed>,
    /// The requests `reserve` and `back` have granted: the view's record.
    grants: Ghost<Seq<Request>>,
    /// The requests `reserve` and `back` have refused, each with the spans held then: the view's
    /// record.
    refusals: Ghost<Seq<Refusal>>,
}

impl Eager {
    /// Every page a span holds backed is a page the record maps at its address: the permission
    /// handed out for it is that page's.
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        &&& self.spans.inv()
        &&& self.record.inv()
        &&& self.record.provenance@ == self.exposed@@
        &&& forall|base: int, a: int|
            self.spans.map@.contains_key(base) && #[trigger] self.spans.map@[base].backed.contains(a) ==> self.record.maps(a)
    }

    /// The slot of the process's own table that names the space the source backs runs in.
    pub closed spec fn space(&self) -> u64 {
        self.record.space
    }

    /// A page is parked at `addr`: its run was released, and a back of it is granted with no system
    /// call.
    pub closed spec fn parks(&self, addr: int) -> bool {
        self.record.parks(addr)
    }

    /// The source that backs runs in the space at `space` with frames and table pages retyped from the
    /// untyped at `untyped`, whose `pages` pages from physical `memory` it alone retypes, putting the
    /// capability of the frame for page i in the empty slot `frame_slot(slots, i)`, which runs on past a
    /// leaf's end into the next leaf, so the caller provides as many consecutive leaves as `pages` frames
    /// need; and hands out spans of the window at
    /// `window`, which nothing maps, aligned to a region and with room for the window after it. None
    /// when the window or the counts do not fit, or `slots` is no slot. Each operation borrows the
    /// process's token of the kernel, which its system calls thread.
    pub fn new(space: u64, untyped: u64, memory: u64, pages: usize, slots: u64, window: *mut u8) -> (r: Option<Eager>)
        ensures
            match r {
                Some(source) => {
                    &&& source@.wf()
                    &&& source@.spans.is_empty()
                    &&& source@.provenance == window@.provenance
                    &&& source.space() == space
                },
                None => true,
            },
    {
        let addr = window as usize;
        if pages > MAX_PAGES || slots >= TABLE_INDICES as u64 || slots % LEAF_INDICES as u64 == 0 {
            return None;
        }
        if pages > 0 && frame_slot_at(slots, pages - 1) >= TABLE_INDICES as u64 {
            return None;
        }
        proof {
            assert(MAX_PAGES >= BLOCK_PAGES + 64);
            lemma_frame_slots_cross_leaves(slots as int);
            assert forall|i: int| 0 <= i < pages implies index_ok(#[trigger] frame_slot(slots as int, i) as usize) by {
                lemma_frame_slot(slots as int, i, pages - 1);
                lemma_frame_slot(slots as int, i, i);
            }
            assert forall|i: int, j: int| 0 <= i < j < pages implies #[trigger] frame_slot(slots as int, i) < #[trigger] frame_slot(
                slots as int,
                j,
            ) by {
                lemma_frame_slot(slots as int, i, j);
            }
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
                parked: Tracked(Map::tracked_empty()),
                provenance: Ghost(exposed@@),
            },
            exposed,
            grants: Ghost(Seq::empty()),
            refusals: Ghost(Seq::empty()),
        };
        assert(source@.spans =~= Map::empty());
        Some(source)
    }
}

impl SpanSource for Eager {
    /// The process's token of the kernel, which the source's system calls thread.
    type Token = Caller;

    closed spec fn view(&self) -> SourceView {
        SourceView { provenance: self.exposed@@, spans: self.spans.map@, grants: self.grants@, refusals: self.refusals@ }
    }

    open spec fn serves(&self, token: Caller) -> bool {
        &&& token.wf()
        &&& names_own_space(token, self.space())
    }

    fn reserve(&mut self, token: &mut Tracked<Caller>, blocks: usize) -> (r: Option<*mut u8>) {
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
                self.grants = Ghost(self.grants@.push(Request::Reserve { blocks: blocks as nat }));
                Some(with_exposed_provenance(base, self.exposed))
            },
        }
    }

    /// A run whose every page is parked is granted.
    fn back(&mut self, token: &mut Tracked<Caller>, span: Ghost<int>, start: usize, pages: usize) -> (r: Option<Tracked<PointsToRaw>>)
        ensures
            (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a)) ==> r is Some,
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost before = self@;
        let ghost record = self.record;
        proof {
            assert(before.released_span(span@).fits(span@, before.spans[span@].blocks));
        }
        match self.record.back_run(token, start, pages, Ghost(self.exposed@@)) {
            None => {
                assert forall|base: int, a: int|
                    self.spans.map@.contains_key(base) && #[trigger] self.spans.map@[base].backed.contains(a) implies self.record.maps(a) by {
                    assert(record.maps(a));
                }
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
                self.grants = Ghost(self.grants@.push(Request::Back { span: span@, start: start as int, pages: pages as nat }));
                assert forall|base: int, a: int|
                    self.spans.map@.contains_key(base) && #[trigger] self.spans.map@[base].backed.contains(a) implies self.record.maps(a) by {
                    if !run_pages(start as int, pages as nat).contains(a) || base != span@ {
                        assert(before.spans[base].backed.contains(a) || run_pages(start as int, pages as nat).contains(a));
                        if before.spans[base].backed.contains(a) {
                            assert(record.maps(a));
                        }
                    }
                }
                Some(perm)
            },
        }
    }

    /// Each page of the run is parked.
    fn release(&mut self, token: &mut Tracked<Caller>, span: Ghost<int>, start: usize, pages: usize, perm: Tracked<PointsToRaw>)
        ensures
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).parks(a),
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost before = self@;
        let ghost record = self.record;
        proof {
            assert(before.released_span(span@).fits(span@, before.spans[span@].blocks));
            lemma_released_run_wf(before, span@, start as int, pages as nat);
            assert forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) implies record.maps(a) by {
                assert(before.spans[span@].backed.contains(a));
            }
        }
        let ghost after = before.released_run(span@, start as int, pages as nat).spans;
        assert forall|base: int, a: int|
            after.contains_key(base) && #[trigger] after[base].backed.contains(a) implies record.maps(a) && !run_pages(
                start as int,
                pages as nat,
            ).contains(a) by {
            assert(before.spans[base].backed.contains(a));
            assert(record.maps(a));
            if base != span@ {
                assert(before.released_span(base).fits(base, before.spans[base].blocks));
                assert(before.released_span(base).spans.contains_key(span@));
                assert(before.released_span(base).apart(base, before.spans[base].blocks, span@));
                if run_pages(start as int, pages as nat).contains(a) {
                    assert(false);
                }
            }
        }
        self.spans.rewrite(Ghost(after));
        self.record.release_run(start, pages, perm);
    }

    fn release_span(&mut self, token: &mut Tracked<Caller>, span: usize) {
        proof {
            use_type_invariant(&*self);
            lemma_released_span_wf(self@, span as int);
        }
        let ghost before = self.spans.map@;
        self.spans.release(span, Ghost(self@));
        assert forall|base: int, a: int|
            self.spans.map@.contains_key(base) && #[trigger] self.spans.map@[base].backed.contains(a) implies self.record.maps(a) by {
            assert(before[base].backed.contains(a));
        }
    }
}

/// The witness that a released page backs its address again, built into no image: from any
/// well-formed eager source holding a span in which the page at `x` is unbacked, back that page,
/// release it and back it again. When the first back is granted the second is, and the source ends
/// with the spans it started with. Whether the first back was granted is the kernel's to say.
#[cfg(verus_keep_ghost)]
pub fn witness_back_again(src: &mut Eager, token: &mut Tracked<Caller>, span: Ghost<int>, x: usize) -> (granted: bool)
    requires
        old(src)@.wf(),
        old(src)@.runs_in(span@, x as int, 1),
        old(src)@.unbacked(span@, x as int, 1),
        old(src).serves(old(token)@),
    ensures
        final(src)@.wf(),
        final(src).serves(final(token)@),
        final(src)@.spans == old(src)@.spans,
{
    let ghost start = src@;
    let first = match src.back(token, span, x, 1) {
        None => return false,
        Some(perm) => perm,
    };
    src.release(token, span, x, 1, first);
    assert(src@.spans[span@].backed =~= start.spans[span@].backed);
    assert(src@.spans =~= start.spans);
    let second = src.back(token, span, x, 1);
    assert(second is Some);
    if let Some(perm) = second {
        src.release(token, span, x, 1, perm);
    }
    assert(src@.spans[span@].backed =~= start.spans[span@].backed);
    assert(src@.spans =~= start.spans);
    true
}

} // verus!
