// SPDX-License-Identifier: MIT

//! The eager source: spans of a window of a few blocks, and frames and table pages retyped from a
//! small untyped, with no fault delivery.
//!
//! `Spans` is the window's bookkeeping, which the contract's view rests on: which blocks of the window
//! a span holds, and the spans by base. `Record` is what the source knows of its untyped: each page
//! free, held as a frame for reuse, mapped, parked, or taken by a table page or by a retype the kernel
//! refused, the untyped's contiguous free middle `[low, high)`, and which tables of the window's path
//! are linked. Its proof is that every index and address it computes is in range, that the pages a span
//! holds backed are the pages the record maps at their addresses, that a released page is parked at its
//! address and backs that address again with no system call, and that while free capacity covers a run
//! every `acall` step stays within the source's window, slots and untyped and a back refuses only when
//! `acall` refuses a step.
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
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
use verified::capability::list::NODES_PER_PAGE;
#[cfg(verus_keep_ghost)]
use verified::capability::operation::{RETYPE_FRAME, RETYPE_TABLE_PAGE, STATUS_OK, STATUS_REFUSED};
#[cfg(verus_keep_ghost)]
use verified::capability::position::POSITION_INDEX_MASK;
#[cfg(verus_keep_ghost)]
use verified::capability::table::index_ok;
use verified::capability::table::TABLE_INDICES;

use crate::glue::*;

verus! {

broadcast use {group_raw_ptr_axioms, vstd::set::lemma_set_filter, vstd::set_lib::range_set_properties};

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

/// Physical address of page `i` of an untyped starting at `memory`.
pub open spec fn untyped_page(memory: u64, i: int) -> int {
    memory + i * PAGE_BYTES as int
}

/// Virtual address of block `b` of a window starting at `window`.
pub open spec fn window_block(window: usize, b: int) -> int {
    window + b * BLOCK_BYTES as int
}

/// Whether `call` is a table-page, link or inspect call of an unexhausted eager source configured with
/// `(space, untyped, memory, max_pages, slots, window)`.
#[verifier::opaque]
pub open spec fn acall_setup_call(
    call: AcallCall,
    space: u64,
    untyped: u64,
    memory: u64,
    max_pages: usize,
    slots: u64,
    window: usize,
) -> bool {
    match call {
        AcallCall::Retype { untyped: u, kind, base, word, level } => {
            &&& u == untyped
            &&& {
                ||| {
                    &&& kind == RETYPE_TABLE_PAGE
                    &&& word == 0
                    &&& 1 <= level <= 3
                    &&& exists|g: int|
                        0 <= g && g + TABLE_PAGES <= max_pages && g % TABLE_PAGES as int == 0
                            && base as int == #[trigger] untyped_page(memory, g)
                }
                ||| {
                    &&& kind == RETYPE_FRAME
                    &&& level == 0
                    &&& exists|i: int|
                        0 <= i < max_pages && base as int == untyped_page(memory, i)
                            && word as int == #[trigger] frame_slot(slots as int, i)
                }
            }
        },
        AcallCall::Link { slot, va, level, from, child } => {
            &&& slot == space
            &&& from == untyped
            &&& (
                (level == 4 && va as int == window as int)
                || (level == 3 && va as int == window as int)
                || (level == 2 && exists|b: int| 0 <= b < WINDOW_BLOCKS && va as int == #[trigger] window_block(window, b))
            )
            &&& exists|g: int|
                0 <= g && g + TABLE_PAGES <= max_pages && g % TABLE_PAGES as int == 0
                    && child as int == #[trigger] untyped_page(memory, g)
        },
        AcallCall::Inspect { at } =>
            exists|i: int| 0 <= i < max_pages && at as int == #[trigger] frame_slot(slots as int, i),
        _ => false,
    }
}

/// Whether `step` is an `acall::memory` call made while backing `count` pages from `start` on an
/// unexhausted eager source configured with `(space, untyped, memory, max_pages, slots, window)`.
#[verifier::opaque]
pub open spec fn acall_call_in_window(
    step: AcallStep,
    space: u64,
    untyped: u64,
    memory: u64,
    max_pages: usize,
    slots: u64,
    window: usize,
    start: int,
    count: nat,
) -> bool {
    ||| acall_setup_call(step.call, space, untyped, memory, max_pages, slots, window)
    ||| match step.call {
        AcallCall::Map { slot, va, level, from, page } => {
            &&& slot == space
            &&& level == 1
            &&& page == 0
            &&& run_pages(start, count).contains(va as int)
            &&& exists|i: int| 0 <= i < max_pages && from as int == #[trigger] frame_slot(slots as int, i)
        },
        _ => false,
    }
}

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

    /// Whether the span at `base` holds block `k` of the window.
    spec fn covers(&self, base: int, k: int) -> bool {
        &&& self.map@.contains_key(base)
        &&& self.index@[base] <= k < self.index@[base] + self.map@[base].blocks
    }

    /// Whether `blocks` blocks from block `first` of the window fit apart from every span in `view`.
    spec fn fits_at(&self, view: SourceView, first: int, blocks: nat) -> bool {
        &&& blocks > 0
        &&& 0 <= first
        &&& first + blocks <= WINDOW_BLOCKS
        &&& forall|other: int|
            #[trigger] view.spans.contains_key(other) ==> view.apart(
                self.window + first * BLOCK_BYTES,
                blocks,
                other,
            )
    }

    spec fn inv(&self) -> bool {
        &&& self.window > 0
        &&& self.window as int % BLOCK_BYTES as int == 0
        &&& self.window + WINDOW_BYTES <= usize::MAX
        &&& forall|base: int| #[trigger] self.map@.contains_key(base) ==> self.holds(base)
        &&& forall|k: int| 0 <= k < WINDOW_BLOCKS && #[trigger] self.used@[k] ==> exists|base: int| #[trigger] self.covers(base, k)
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
            final(self).window == old(self).window,
            match r {
                None => {
                    &&& final(self).map@ == old(self).map@
                    &&& forall|first: int| !#[trigger] old(self).fits_at(view@, first, blocks as nat)
                },
                Some(base) => {
                    let first = (base - old(self).window) / BLOCK_BYTES as int;
                    &&& base == old(self).window + first * BLOCK_BYTES
                    &&& old(self).fits_at(view@, first, blocks as nat)
                    &&& forall|earlier: int|
                        0 <= earlier < first ==> !#[trigger] old(self).fits_at(view@, earlier, blocks as nat)
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
                forall|earlier: int|
                    0 <= earlier < first ==> !#[trigger] old(self).fits_at(view@, earlier, blocks as nat),
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
                    !free ==> exists|u: int| first <= u < first + t && #[trigger] self.used@[u],
                decreases blocks - t,
            {
                let ghost prev_t = t as int;
                if self.used[first + t] {
                    assert(self.used@[(first + t) as int]);
                    free = false;
                } else if !free {
                    proof {
                        let u = choose|u: int| first <= u < first + prev_t && #[trigger] self.used@[u];
                        assert(self.used@[u]);
                    }
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
                    assert(base - before.window == BLOCK_BYTES * (first as int)) by (nonlinear_arith)
                        requires
                            base == before.window + first * BLOCK_BYTES,
                    ;
                    lemma_div_multiples_vanish(first as int, BLOCK_BYTES as int);
                    assert((base - before.window) / BLOCK_BYTES as int == first as int);
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
                    assert forall|k: int| 0 <= k < WINDOW_BLOCKS && #[trigger] self.used@[k] implies exists|b: int| #[trigger] self.covers(b, k) by {
                        if first <= k < first + blocks {
                            assert(self.covers(base as int, k));
                        } else {
                            assert(before.used@[k]);
                            let b = choose|b: int| #[trigger] before.covers(b, k);
                            assert(before.holds(b));
                            if b == base as int {
                                assert(view.apart(base as int, blocks as nat, b));
                                lemma_scale(1, blocks as int, BLOCK_BYTES as int);
                                lemma_scale(1, before.map@[b].blocks as int, BLOCK_BYTES as int);
                            }
                            assert(self.covers(b, k));
                        }
                    }
                }
                return Some(base);
            }
            proof {
                if self.fits_at(view@, first as int, blocks as nat) {
                    let u = choose|u: int| first <= u < first + blocks && #[trigger] self.used@[u];
                    assert(self.used@[u]);
                    let other = choose|other: int| #[trigger] self.covers(other, u);
                    assert(self.holds(other));
                    let j = self.index@[other];
                    let length = self.map@[other].blocks;
                    assert(view@.spans.contains_key(other));
                    assert(view@.apart(self.window + first * BLOCK_BYTES, blocks as nat, other));
                    lemma_scale(first as int + 1, j + length, BLOCK_BYTES as int);
                    lemma_scale(j, length as int, BLOCK_BYTES as int);
                    lemma_scale(first as int, 1, BLOCK_BYTES as int);
                    lemma_scale(j + 1, first as int + blocks, BLOCK_BYTES as int);
                    lemma_scale(first as int, blocks as int, BLOCK_BYTES as int);
                    lemma_scale(j, 1, BLOCK_BYTES as int);
                }
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
            final(self).window == old(self).window,
            final(self).map@ == map@,
        no_unwind
    {
        let ghost before = *self;
        self.map = map;
        assert forall|b: int| #[trigger] self.map@.contains_key(b) implies self.holds(b) by {
            assert(before.holds(b));
        }
        assert forall|k: int| 0 <= k < WINDOW_BLOCKS && #[trigger] self.used@[k] implies exists|b: int| #[trigger] self.covers(b, k) by {
            assert(before.used@[k]);
            let b = choose|b: int| #[trigger] before.covers(b, k);
            assert(self.covers(b, k));
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
            final(self).window == old(self).window,
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
                forall|u: int| first <= u < first + t ==> !#[trigger] self.used@[u],
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
            assert forall|k: int| 0 <= k < WINDOW_BLOCKS && #[trigger] self.used@[k] implies exists|b: int| #[trigger] self.covers(b, k) by {
                assert(before.used@[k]);
                let b = choose|b: int| #[trigger] before.covers(b, k);
                assert(before.holds(b));
                assert(b != span as int);
                assert(self.covers(b, k));
            }
        }
    }
}

/// From the slot `slots` on, the frame slots of `pages` pages are slots of the table, one a page, rising
/// with the page.
#[verifier::opaque]
spec fn slots_ok(slots: u64, pages: usize) -> bool {
    &&& forall|i: int| 0 <= i < pages ==> index_ok(#[trigger] frame_slot(slots as int, i) as usize)
    &&& forall|i: int| 0 <= i < pages ==> 0 <= #[trigger] frame_slot(slots as int, i) < TABLE_INDICES
    &&& forall|i: int, j: int|
        0 <= i < j < pages ==> #[trigger] frame_slot(slots as int, i) < #[trigger] frame_slot(slots as int, j)
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
    /// The permission to each parked page's bytes, by page. Only proofs read it, so only Verus
    /// compiles it.
    #[cfg(verus_keep_ghost)]
    parked: Tracked<Map<int, PointsToRaw>>,
    /// The provenance of every permission the record hands out. Only proofs read it, so only Verus
    /// compiles it.
    #[cfg(verus_keep_ghost)]
    provenance: Ghost<Provenance>,
    /// Lowest page of the untyped's contiguous free middle `[low, high)`, aligned to `TABLE_PAGES`.
    /// Only proofs read it, so only Verus compiles it.
    #[cfg(verus_keep_ghost)]
    low: Ghost<int>,
    /// Upper bound of the untyped's contiguous free middle `[low, high)`. Only proofs read it, so
    /// only Verus compiles it.
    #[cfg(verus_keep_ghost)]
    high: Ghost<int>,
}

impl Record {
    /// `caller` is a token of the process whose space the record's system calls change, a process that
    /// is its own: the slot at `space` names its own space.
    spec fn serves(&self, caller: Caller) -> bool {
        &&& caller.wf()
        &&& own_process(caller)
        &&& names_own_space(caller, self.space)
        &&& frames_held(caller.kernel(), caller.root(), self.frames())
    }

    /// The frames the source holds, by page: the slot of each page held, mapped or parked, and the
    /// address a mapped or parked one is at.
    spec fn frames(&self) -> Map<int, (usize, Option<usize>)> {
        Map::new(
            Set::<int>::range(0, self.pages as int).filter(|i: int| self.state@[i] == HELD || occupied(self.state@[i])),
            |i: int| (frame_slot(self.slots as int, i) as usize, if occupied(self.state@[i]) { Some(self.owner@[i]) } else { None }),
        )
    }

    spec fn inv(&self) -> bool {
        &&& self.pages <= MAX_PAGES
        &&& self.memory + self.pages * PAGE_BYTES <= u64::MAX
        &&& self.slots < TABLE_INDICES
        &&& self.slots as int % LEAF_INDICES as int != 0
        &&& slots_ok(self.slots, self.pages)
        &&& self.window as int % BLOCK_BYTES as int == 0
        &&& self.window + WINDOW_BYTES <= usize::MAX
        &&& 0 <= self.low@ <= self.high@ <= self.pages
        &&& self.low@ % TABLE_PAGES as int == 0
        &&& forall|i: int| self.low@ <= i < self.high@ ==> #[trigger] self.state@[i] == FREE
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

    spec fn blocks_untabled(&self) -> int {
        (if self.tabled@[0] { 0int } else { 1int })
            + (if self.tabled@[1] { 0int } else { 1int })
            + (if self.tabled@[2] { 0int } else { 1int })
            + (if self.tabled@[3] { 0int } else { 1int })
    }

    spec fn tables_unlinked(&self) -> int {
        (if self.top { 0int } else { 1int })
            + (if self.middle { 0int } else { 1int })
            + self.blocks_untabled()
    }

    spec fn free_capacity(&self) -> int {
        self.high@ - self.low@ - self.tables_unlinked() * TABLE_PAGES as int
    }

    spec fn same_config(&self, old: &Record) -> bool {
        &&& self.space == old.space
        &&& self.untyped == old.untyped
        &&& self.memory == old.memory
        &&& self.pages == old.pages
        &&& self.slots == old.slots
        &&& self.window == old.window
        &&& self.provenance == old.provenance
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
    fn page(&self, i: usize) -> (r: u64)
        requires
            self.inv(),
            i < self.pages,
        ensures
            r as int == untyped_page(self.memory, i as int),
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
        proof {
            reveal(slots_ok);
        }
        frame_slot_at(self.slots, i)
    }

    /// A frame the source holds, mapped nowhere: one held before, else a free page retyped as a frame
    /// into its slot, else a parked page unmapped. None when no page is free or parked, or the kernel
    /// refused the retype or the unmap.
    fn frame(&mut self, caller: &mut Tracked<Caller>) -> (r: (Option<usize>, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps(old(self)),
            final(self).keeps_mapped(old(self)),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            match r.0 {
                Some(i) => {
                    &&& i < final(self).pages
                    &&& final(self).state@[i as int] == HELD
                    &&& acall_ok(r.1@)
                },
                None => true,
            },
            old(self).free_capacity() >= 1 ==> {
                &&& forall|k: int| 0 <= k < r.1@.len() ==> acall_setup_call(
                    (#[trigger] r.1@[k]).call,
                    old(self).space,
                    old(self).untyped,
                    old(self).memory,
                    old(self).pages,
                    old(self).slots,
                    old(self).window,
                )
                &&& r.0 is Some ==> final(self).free_capacity() >= old(self).free_capacity() - 1
                &&& r.0 is None ==> {
                    &&& r.1@.len() > 0
                    &&& acall_ok(r.1@.drop_last())
                    &&& r.1@.last().out.status == STATUS_REFUSED
                }
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let mut i: usize = 0;
        while i < self.pages
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                i <= self.pages,
                forall|u: int| 0 <= u < i ==> #[trigger] self.state@[u] != HELD,
            decreases self.pages - i,
        {
            if self.state[i] == HELD {
                proof {
                    lemma_acall_steps_none(caller@);
                }
                return (Some(i), Ghost(Seq::empty()));
            }
            i += 1;
        }
        let mut i = self.pages;
        while i > 0
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                i <= self.pages,
                forall|u: int| 0 <= u < self.pages ==> #[trigger] self.state@[u] != HELD,
                old(self).high@ > old(self).low@ ==> i >= old(self).high@,
            decreases i,
        {
            i -= 1;
            if self.state[i] == FREE {
                let base = self.page(i);
                let slot = self.slot(i);
                proof {
                    if self.high@ > self.low@ && i as int == self.high@ - 1 {
                        self.high = Ghost(self.high@ - 1);
                    }
                }
                let ghost before = *self;
                proof {
                    assert(before.frames() =~= old(self).frames());
                    // Every frame held is another page's, whose slot frame slots keep apart.
                    assert forall|u: int| #[trigger] before.frames().contains_key(u) implies before.frames()[u].0 != slot as usize by {
                        reveal(slots_ok);
                        assert(u != i);
                        assert(0 <= frame_slot(self.slots as int, u) < TABLE_INDICES);
                        if u < i {
                            assert(frame_slot(self.slots as int, u) < frame_slot(self.slots as int, i as int));
                        } else {
                            assert(frame_slot(self.slots as int, i as int) < frame_slot(self.slots as int, u));
                        }
                    }
                }
                let (retyped, Ghost(s)) = retype_frame(caller, self.untyped, base, slot, Ghost(before.frames()), Ghost(i as int));
                let ghost steps = seq![s];
                proof {
                    assert(base as int == untyped_page(self.memory, i as int));
                    assert(slot as int == frame_slot(self.slots as int, i as int));
                    assert(acall_setup_call(s.call, self.space, self.untyped, self.memory, self.pages, self.slots, self.window)) by {
                        reveal(acall_setup_call);
                    }
                    assert(steps[0] == s && steps.last() == s);
                    if !retyped {
                        assert(steps.drop_last() =~= Seq::<AcallStep>::empty());
                    }
                }
                if retyped {
                    self.state[i] = HELD;
                    assert(self.frames() =~= before.frames().insert(i as int, (slot as usize, None)));
                    return (Some(i), Ghost(steps));
                }
                self.state[i] = TAKEN;
                assert(self.frames() =~= before.frames());
                return (None, Ghost(steps));
            }
            proof {
                if old(self).high@ > old(self).low@ && i as int == old(self).high@ - 1 {
                    assert(self.state@[i as int] == FREE);
                }
            }
        }
        proof {
            assert(old(self).high@ == old(self).low@);
            assert(old(self).tables_unlinked() >= 0);
            assert(old(self).free_capacity() <= 0);
        }
        let mut i: usize = 0;
        while i < self.pages
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                i <= self.pages,
                old(self).high@ == old(self).low@,
                old(self).free_capacity() <= 0,
            decreases self.pages - i,
        {
            if self.state[i] == PARKED {
                assert(self.state@[i as int] == PARKED);
                let ghost before = *self;
                let tracked perm = self.parked.borrow_mut().tracked_remove(i as int);
                assert(self.frames() =~= before.frames());
                let (unmapped, Ghost(s)) = unmap_page(caller, self.space, self.owner[i], Tracked(perm), Ghost(before.frames()), Ghost(i as int));
                let ghost steps = seq![s];
                if unmapped {
                    self.state[i] = HELD;
                    assert(self.frames() =~= before.frames().insert(i as int, (before.frames()[i as int].0, None)));
                    return (Some(i), Ghost(steps));
                }
                self.state[i] = TAKEN;
                assert(self.frames() =~= before.frames().remove(i as int));
                return (None, Ghost(steps));
            }
            i += 1;
        }
        proof {
            lemma_acall_steps_none(caller@);
        }
        (None, Ghost(Seq::empty()))
    }

    /// Retypes the lowest free order-3 block of the untyped as a table page of the level below
    /// `level`, and links it at the entry of `level` that `address` names. Whether both were done,
    /// and the steps taken.
    fn table(&mut self, caller: &mut Tracked<Caller>, address: usize, level: u64) -> (r: (bool, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            2 <= level <= 4,
            (level == 4 && address == old(self).window)
                || (level == 3 && address == old(self).window)
                || (level == 2 && exists|b: int| 0 <= b < WINDOW_BLOCKS && address as int == #[trigger] window_block(old(self).window, b)),
        ensures
            final(self).same_config(old(self)),
            final(self).top == old(self).top,
            final(self).middle == old(self).middle,
            final(self).tabled == old(self).tabled,
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps(old(self)),
            final(self).keeps_mapped(old(self)),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_setup_call(
                (#[trigger] r.1@[k]).call,
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
            ),
            r.0 ==> acall_ok(r.1@),
            old(self).high@ - old(self).low@ >= TABLE_PAGES ==> {
                &&& final(self).high@ - final(self).low@ >= old(self).high@ - old(self).low@ - TABLE_PAGES as int
                &&& !r.0 ==> {
                    &&& r.1@.len() > 0
                    &&& acall_ok(r.1@.drop_last())
                    &&& r.1@.last().out.status == STATUS_REFUSED
                }
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let mut group: usize = 0;
        while group + TABLE_PAGES <= self.pages
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                group <= self.pages,
                group as int % TABLE_PAGES as int == 0,
                2 <= level <= 4,
                (level == 4 && address == old(self).window)
                    || (level == 3 && address == old(self).window)
                    || (level == 2 && exists|b: int| 0 <= b < WINDOW_BLOCKS && address as int == #[trigger] window_block(old(self).window, b)),
                old(self).high@ - old(self).low@ >= TABLE_PAGES ==> group <= old(self).low@,
            decreases self.pages - group,
        {
            let mut k: usize = 0;
            let mut free = true;
            while k < TABLE_PAGES
                invariant
                    *self == *old(self),
                    caller@ == old(caller)@,
                    self.inv(),
                    group + TABLE_PAGES <= self.pages,
                    k <= TABLE_PAGES,
                    2 <= level <= 4,
                    free ==> forall|u: int| group <= u < group + k ==> #[trigger] self.state@[u] == FREE,
                    (group == old(self).low@ && old(self).high@ - old(self).low@ >= TABLE_PAGES) ==> free,
                decreases TABLE_PAGES - k,
            {
                if self.state[group + k] != FREE {
                    proof {
                        if group == old(self).low@ && old(self).high@ - old(self).low@ >= TABLE_PAGES {
                            assert(self.state@[group + k] == FREE);
                        }
                    }
                    free = false;
                }
                k += 1;
            }
            if free {
                proof {
                    let tp = TABLE_PAGES as int;
                    if group + tp <= self.low@ {
                    } else if self.high@ - self.low@ >= tp {
                        lemma_fundamental_div_mod(group as int, tp);
                        lemma_fundamental_div_mod(self.low@, tp);
                        let qg = group as int / tp;
                        let ql = self.low@ / tp;
                        assert(qg == ql) by (nonlinear_arith)
                            requires
                                group as int == tp * qg,
                                self.low@ == tp * ql,
                                group <= self.low@,
                                group + tp > self.low@,
                                tp == 8,
                        ;
                        assert(group == self.low@);
                        lemma_mod_add_multiples_vanish(self.low@, tp);
                        self.low = Ghost(self.low@ + tp);
                    } else {
                        self.high = self.low;
                    }
                    assert(self.frames() =~= old(self).frames());
                }
                k = 0;
                while k < TABLE_PAGES
                    invariant
                        self.same_config(old(self)),
                        self.top == old(self).top,
                        self.middle == old(self).middle,
                        self.tabled == old(self).tabled,
                        old(self).high@ - old(self).low@ >= TABLE_PAGES
                            ==> self.high@ - self.low@ >= old(self).high@ - old(self).low@ - TABLE_PAGES as int,
                        self.low@ == self.high@ || self.low@ >= group + TABLE_PAGES,
                        self.inv(),
                        self.serves(caller@),
                        caller@ == old(caller)@,
                        group + TABLE_PAGES <= self.pages,
                        group as int % TABLE_PAGES as int == 0,
                        k <= TABLE_PAGES,
                        2 <= level <= 4,
                        self.keeps(old(self)),
                        self.keeps_mapped(old(self)),
                        forall|u: int| group + k <= u < group + TABLE_PAGES ==> #[trigger] self.state@[u] == FREE,
                    decreases TABLE_PAGES - k,
                {
                    assert(self.state@[group + k] == FREE);
                    let ghost before = *self;
                    self.state[group + k] = TAKEN;
                    assert(self.frames() =~= before.frames());
                    k += 1;
                }
                let base = self.page(group);
                let (retyped, Ghost(s1)) = retype_table_page(caller, self.untyped, base, level - 1, Ghost(self.frames()));
                proof {
                    assert(base as int == untyped_page(self.memory, group as int));
                    assert(acall_setup_call(s1.call, self.space, self.untyped, self.memory, self.pages, self.slots, self.window)) by {
                        reveal(acall_setup_call);
                    }
                }
                if !retyped {
                    let ghost steps = seq![s1];
                    proof {
                        assert(steps[0] == s1 && steps.last() == s1);
                        assert(steps.drop_last() =~= Seq::<AcallStep>::empty());
                    }
                    return (false, Ghost(steps));
                }
                let ghost mid = caller@;
                let (linked, Ghost(s2)) = link(
                    caller,
                    self.space,
                    address,
                    level,
                    self.untyped,
                    base,
                    Ghost(self.frames()),
                );
                let ghost steps = seq![s1] + seq![s2];
                proof {
                    if level == 2 {
                        let b = choose|b: int| 0 <= b < WINDOW_BLOCKS && address as int == #[trigger] window_block(old(self).window, b);
                        assert((address as u64) as int == window_block(self.window, b));
                    }
                    assert(base as int == untyped_page(self.memory, group as int));
                    assert(acall_setup_call(s2.call, self.space, self.untyped, self.memory, self.pages, self.slots, self.window)) by {
                        reveal(acall_setup_call);
                    }
                    lemma_acall_steps_append(old(caller)@, mid, caller@, seq![s1], seq![s2]);
                    if linked {
                        lemma_acall_ok_append(seq![s1], seq![s2]);
                    } else {
                        lemma_acall_refused_after_ok(seq![s1], seq![s2]);
                    }
                    assert forall|j: int| 0 <= j < steps.len() implies acall_setup_call(
                        (#[trigger] steps[j]).call,
                        old(self).space,
                        old(self).untyped,
                        old(self).memory,
                        old(self).pages,
                        old(self).slots,
                        old(self).window,
                    ) by {
                        if j == 0 {
                            assert(steps[j] == s1);
                        } else {
                            assert(steps[j] == s2);
                        }
                    }
                }
                return (linked, Ghost(steps));
            }
            proof {
                let tp = TABLE_PAGES as int;
                lemma_fundamental_div_mod(group as int, tp);
                lemma_fundamental_div_mod(self.low@, tp);
                if self.high@ - self.low@ >= tp {
                    assert(group < self.low@);
                    let qg = group as int / tp;
                    let ql = self.low@ / tp;
                    assert(qg < ql) by (nonlinear_arith)
                        requires
                            group as int == tp * qg,
                            self.low@ == tp * ql,
                            group < self.low@,
                            tp == 8,
                    ;
                    assert(group + tp <= self.low@) by (nonlinear_arith)
                        requires
                            group as int == tp * qg,
                            self.low@ == tp * ql,
                            qg + 1 <= ql,
                            tp == 8,
                    ;
                }
                lemma_mod_add_multiples_vanish(group as int, tp);
            }
            group += TABLE_PAGES;
        }
        proof {
            lemma_acall_steps_none(caller@);
        }
        (false, Ghost(Seq::empty()))
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
    fn back_page(
        &mut self,
        caller: &mut Tracked<Caller>,
        addr: usize,
        provenance: Ghost<Provenance>,
    ) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            provenance@ == old(self).provenance@,
            addr as int % PAGE_BYTES as int == 0,
            !old(self).maps(addr as int),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps_mapped(old(self)),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            match r.0 {
                Some(perm) => {
                    &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                    &&& perm@.provenance() == provenance@
                    &&& final(self).maps(addr as int)
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> a == addr || old(self).maps(a)
                    &&& acall_ok(r.1@)
                },
                None => {
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a)
                },
            },
            old(self).parks(addr as int) ==> {
                &&& r.0 is Some
                &&& r.1@ == Seq::<AcallStep>::empty()
                &&& final(caller)@ == old(caller)@
                &&& final(self).free_capacity() == old(self).free_capacity()
                &&& forall|b: int| b != addr && #[trigger] old(self).parks(b) ==> final(self).parks(b)
            },
            old(self).free_capacity() >= 1 ==> {
                &&& forall|k: int| 0 <= k < r.1@.len() ==> acall_call_in_window(
                    #[trigger] r.1@[k],
                    old(self).space,
                    old(self).untyped,
                    old(self).memory,
                    old(self).pages,
                    old(self).slots,
                    old(self).window,
                    addr as int,
                    1,
                )
                &&& r.0 is Some ==> final(self).free_capacity() >= old(self).free_capacity() - 1
                &&& r.0 is None ==> {
                    &&& r.1@.len() > 0
                    &&& acall_ok(r.1@.drop_last())
                    &&& r.1@.last().out.status == STATUS_REFUSED
                }
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let i = self.find(addr);
        if i == self.pages {
            return self.map_new(caller, addr, provenance);
        }
        proof {
            lemma_acall_steps_none(caller@);
        }
        if self.state[i] == MAPPED {
            proof {
                assert(self.state@[i as int] == MAPPED && self.owner@[i as int] == addr);
                assert(old(self).maps(addr as int));
            }
            return (None, Ghost(Seq::empty()));
        }
        assert(self.state@[i as int] == PARKED && self.owner@[i as int] == addr);
        let ghost before = *self;
        let tracked perm = self.parked.borrow_mut().tracked_remove(i as int);
        self.state[i] = MAPPED;
        proof {
            assert(self.frames() =~= before.frames());
            assert(self.state@[i as int] == MAPPED);
            assert forall|a: int| #[trigger] self.maps(a) implies a == addr || before.maps(a) by {
                if a != addr {
                    let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == MAPPED && self.owner@[j] == a;
                    assert(j != i);
                    assert(before.state@[j] == MAPPED);
                }
            }
            assert forall|b: int| b != addr && #[trigger] before.parks(b) implies self.parks(b) by {
                let j = choose|j: int| 0 <= j < before.pages && #[trigger] before.state@[j] == PARKED && before.owner@[j] == b;
                assert(self.state@[j] == PARKED);
            }
        }
        (Some(Tracked(perm)), Ghost(Seq::empty()))
    }

    /// Links the tables the path to `addr` lacks, at each level the record has not linked yet; false
    /// when a link was refused. Every page keeps its state and address.
    fn path_tables(&mut self, caller: &mut Tracked<Caller>, addr: usize) -> (r: (bool, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps(old(self)),
            final(self).keeps_mapped(old(self)),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_setup_call(
                (#[trigger] r.1@[k]).call,
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
            ),
            r.0 ==> acall_ok(r.1@),
            old(self).free_capacity() >= 0 ==> {
                &&& r.0 ==> final(self).free_capacity() >= old(self).free_capacity()
                &&& !r.0 ==> {
                    &&& r.1@.len() > 0
                    &&& acall_ok(r.1@.drop_last())
                    &&& r.1@.last().out.status == STATUS_REFUSED
                }
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let ghost start = *self;
        let ghost c0 = caller@;
        let ghost mut steps = Seq::<AcallStep>::empty();
        proof {
            lemma_acall_steps_none(c0);
        }
        let window = self.window;
        if !self.top {
            let ghost before = *self;
            proof {
                assert(before.blocks_untabled() >= 0);
                assert(before.tables_unlinked() >= 1);
                if start.free_capacity() >= 0 {
                    lemma_capacity_covers_table(before);
                }
            }
            let (linked, Ghost(s)) = self.table(caller, window, 4);
            proof {
                lemma_mapped_trans(*self, before, start);
                lemma_keeps_trans(*self, before, start);
                steps = s;
            }
            if !linked {
                return (false, Ghost(steps));
            }
            let ghost after_table = *self;
            self.top = true;
            proof {
                assert(self.frames() =~= after_table.frames());
                assert(self.tables_unlinked() == before.tables_unlinked() - 1);
                if start.free_capacity() >= 0 {
                    assert(self.free_capacity() >= before.free_capacity());
                }
            }
        }
        if !self.middle {
            let ghost before = *self;
            let ghost cmid = caller@;
            let ghost prev = steps;
            proof {
                assert(before.blocks_untabled() >= 0);
                assert(before.tables_unlinked() >= 1);
                if start.free_capacity() >= 0 {
                    assert(before.free_capacity() >= 0);
                    lemma_capacity_covers_table(before);
                }
            }
            let (linked, Ghost(s)) = self.table(caller, window, 3);
            proof {
                lemma_mapped_trans(*self, before, start);
                lemma_keeps_trans(*self, before, start);
                lemma_acall_steps_append(c0, cmid, caller@, prev, s);
                steps = prev + s;
                assert forall|j: int| 0 <= j < steps.len() implies acall_setup_call(
                    (#[trigger] steps[j]).call,
                    start.space,
                    start.untyped,
                    start.memory,
                    start.pages,
                    start.slots,
                    start.window,
                ) by {
                    if j < prev.len() {
                        assert(steps[j] == prev[j]);
                    } else {
                        assert(steps[j] == s[j - prev.len()]);
                    }
                }
            }
            if !linked {
                proof {
                    if start.free_capacity() >= 0 {
                        lemma_acall_refused_after_ok(prev, s);
                    }
                }
                return (false, Ghost(steps));
            }
            let ghost after_table = *self;
            self.middle = true;
            proof {
                lemma_acall_ok_append(prev, s);
                assert(self.frames() =~= after_table.frames());
                assert(self.tables_unlinked() == before.tables_unlinked() - 1);
                if start.free_capacity() >= 0 {
                    assert(self.free_capacity() >= before.free_capacity());
                }
            }
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
            let ghost before = *self;
            let ghost cmid = caller@;
            let ghost prev = steps;
            proof {
                lemma_scale(block as int, WINDOW_BLOCKS as int, BLOCK_BYTES as int);
                assert((window + block * BLOCK_BYTES) as int == window_block(before.window, block as int));
                assert(before.blocks_untabled() >= 1);
                assert(before.tables_unlinked() >= 1);
                if start.free_capacity() >= 0 {
                    assert(before.free_capacity() >= 0);
                    lemma_capacity_covers_table(before);
                }
            }
            let (linked, Ghost(s)) = self.table(caller, window + block * BLOCK_BYTES, 2);
            proof {
                lemma_mapped_trans(*self, before, start);
                lemma_keeps_trans(*self, before, start);
                lemma_acall_steps_append(c0, cmid, caller@, prev, s);
                steps = prev + s;
                assert forall|j: int| 0 <= j < steps.len() implies acall_setup_call(
                    (#[trigger] steps[j]).call,
                    start.space,
                    start.untyped,
                    start.memory,
                    start.pages,
                    start.slots,
                    start.window,
                ) by {
                    if j < prev.len() {
                        assert(steps[j] == prev[j]);
                    } else {
                        assert(steps[j] == s[j - prev.len()]);
                    }
                }
            }
            if !linked {
                proof {
                    if start.free_capacity() >= 0 {
                        lemma_acall_refused_after_ok(prev, s);
                    }
                }
                return (false, Ghost(steps));
            }
            let ghost after_table = *self;
            self.tabled[block] = true;
            proof {
                lemma_acall_ok_append(prev, s);
                assert(self.frames() =~= after_table.frames());
                assert(self.blocks_untabled() == before.blocks_untabled() - 1);
                assert(self.tables_unlinked() == before.tables_unlinked() - 1);
                if start.free_capacity() >= 0 {
                    assert(self.free_capacity() >= before.free_capacity());
                }
            }
        }
        (true, Ghost(steps))
    }

    /// Links the tables the path to `addr` lacks, takes a frame and maps it at `addr`, where no page
    /// is mapped or parked. The permission to the page's bytes, or none when anything was refused.
    fn map_new(
        &mut self,
        caller: &mut Tracked<Caller>,
        addr: usize,
        provenance: Ghost<Provenance>,
    ) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            provenance@ == old(self).provenance@,
            addr as int % PAGE_BYTES as int == 0,
            !old(self).maps(addr as int),
            !old(self).parks(addr as int),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps_mapped(old(self)),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            match r.0 {
                Some(perm) => {
                    &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                    &&& perm@.provenance() == provenance@
                    &&& final(self).maps(addr as int)
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> a == addr || old(self).maps(a)
                    &&& acall_ok(r.1@)
                },
                None => {
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a)
                },
            },
            old(self).free_capacity() >= 1 ==> {
                &&& forall|k: int| 0 <= k < r.1@.len() ==> acall_call_in_window(
                    #[trigger] r.1@[k],
                    old(self).space,
                    old(self).untyped,
                    old(self).memory,
                    old(self).pages,
                    old(self).slots,
                    old(self).window,
                    addr as int,
                    1,
                )
                &&& r.0 is Some ==> final(self).free_capacity() >= old(self).free_capacity() - 1
                &&& r.0 is None ==> {
                    &&& r.1@.len() > 0
                    &&& acall_ok(r.1@.drop_last())
                    &&& r.1@.last().out.status == STATUS_REFUSED
                }
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let ghost start = *self;
        let ghost c0 = caller@;
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
        let (linked, Ghost(s1)) = self.path_tables(caller, addr);
        proof {
            assert forall|j: int| 0 <= j < self.pages implies !(occupied(#[trigger] self.state@[j]) && self.owner@[j] == addr) by {
                if occupied(self.state@[j]) {
                    assert(start.state@[j] == self.state@[j]);
                }
            }
        }
        if !linked {
            proof {
                lemma_keeps_no_new_mapped(*self, start);
                if start.free_capacity() >= 1 {
                    assert forall|k: int| 0 <= k < s1.len() implies acall_call_in_window(
                        #[trigger] s1[k],
                        start.space,
                        start.untyped,
                        start.memory,
                        start.pages,
                        start.slots,
                        start.window,
                        addr as int,
                        1,
                    ) by {
                        reveal(acall_call_in_window);
                        assert(acall_setup_call(s1[k].call, start.space, start.untyped, start.memory, start.pages, start.slots, start.window));
                    }
                }
            }
            return (None, Ghost(s1));
        }
        let ghost before = *self;
        let ghost c1 = caller@;
        let (found, Ghost(s2)) = self.frame(caller);
        let ghost s12 = s1 + s2;
        proof {
            lemma_mapped_trans(*self, before, start);
            lemma_keeps_trans(*self, before, start);
            lemma_acall_steps_append(c0, c1, caller@, s1, s2);
            if start.free_capacity() >= 1 {
                assert forall|k: int| 0 <= k < s12.len() implies acall_call_in_window(
                    #[trigger] s12[k],
                    start.space,
                    start.untyped,
                    start.memory,
                    start.pages,
                    start.slots,
                    start.window,
                    addr as int,
                    1,
                ) by {
                    reveal(acall_call_in_window);
                    if k < s1.len() {
                        assert(s12[k] == s1[k]);
                    } else {
                        assert(s12[k] == s2[k - s1.len()]);
                    }
                }
            }
        }
        let i = match found {
            Some(i) => i,
            None => {
                proof {
                    lemma_keeps_no_new_mapped(*self, start);
                    if start.free_capacity() >= 1 {
                        lemma_acall_refused_after_ok(s1, s2);
                    }
                }
                return (None, Ghost(s12));
            },
        };
        proof {
            lemma_acall_ok_append(s1, s2);
        }
        let slot = self.slot(i);
        let ghost live = self.live();
        assert(!live.contains(addr));
        let ghost held = *self;
        let ghost c2 = caller@;
        proof {
            assert(held.frames().contains_key(i as int));
            assert(0 <= frame_slot(self.slots as int, i as int) < TABLE_INDICES) by {
                reveal(slots_ok);
            }
            assert(slot <= POSITION_INDEX_MASK);
            // No page the source holds is at addr: every mapped or parked page's address is live.
            assert forall|j: int| #[trigger] held.frames().contains_key(j) && held.frames()[j].1 is Some implies held.frames()[j].1->0 != addr by {
                if held.owner@[j] == addr {
                    assert(occupied(held.state@[j]));
                    assert(live.contains(addr));
                }
            }
        }
        let (mapped, Ghost(s3)) = map_page(caller, self.space, addr, slot, provenance, Ghost(live), Ghost(held.frames()), Ghost(i as int));
        let ghost steps = s12 + s3;
        proof {
            lemma_acall_steps_append(c0, c2, caller@, s12, s3);
            if start.free_capacity() >= 1 {
                assert(slot as int == frame_slot(start.slots as int, i as int));
                assert(run_pages(addr as int, 1).contains((addr as u64) as int));
                assert(acall_call_in_window(s3[0], start.space, start.untyped, start.memory, start.pages, start.slots, start.window, addr as int, 1)) by {
                    reveal(acall_call_in_window);
                    reveal(acall_setup_call);
                }
                if s3.len() == 2 {
                    assert(acall_call_in_window(s3[1], start.space, start.untyped, start.memory, start.pages, start.slots, start.window, addr as int, 1)) by {
                        reveal(acall_call_in_window);
                    }
                }
                assert forall|k: int| 0 <= k < steps.len() implies acall_call_in_window(
                    #[trigger] steps[k],
                    start.space,
                    start.untyped,
                    start.memory,
                    start.pages,
                    start.slots,
                    start.window,
                    addr as int,
                    1,
                ) by {
                    if k < s12.len() {
                        assert(steps[k] == s12[k]);
                    } else if k == s12.len() {
                        assert(steps[k] == s3[0]);
                    } else {
                        assert(steps[k] == s3[1]);
                    }
                }
            }
        }
        match mapped {
            Some(perm) => {
                self.state[i] = MAPPED;
                self.owner[i] = addr;
                proof {
                    lemma_acall_ok_append(s12, s3);
                    assert(self.state@[i as int] == MAPPED);
                    assert(self.frames() =~= held.frames().insert(i as int, (slot as usize, Some(addr))));
                    lemma_keeps_no_new_mapped(held, start);
                    assert forall|a: int| #[trigger] self.maps(a) implies a == addr || start.maps(a) by {
                        if a != addr {
                            let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == MAPPED && self.owner@[j] == a;
                            assert(j != i);
                            assert(held.state@[j] == MAPPED && held.owner@[j] == a);
                            assert(held.maps(a));
                        }
                    }
                }
                (Some(perm), Ghost(steps))
            },
            None => {
                proof {
                    lemma_keeps_no_new_mapped(*self, start);
                    if start.free_capacity() >= 1 {
                        lemma_acall_refused_after_ok(s12, s3);
                    }
                }
                (None, Ghost(steps))
            },
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
            final(self).same_config(old(self)),
            final(self).free_capacity() == old(self).free_capacity(),
            final(self).inv(),
            final(self).frames() == old(self).frames(),
            final(self).parks(addr as int),
            forall|a: int| a != addr && #[trigger] old(self).maps(a) ==> final(self).maps(a),
            forall|a: int| #[trigger] final(self).maps(a) ==> a != addr && old(self).maps(a),
            forall|a: int| #[trigger] old(self).parks(a) ==> final(self).parks(a),
        no_unwind
    {
        let mut i: usize = 0;
        while i < self.pages && !(self.state[i] == MAPPED && self.owner[i] == addr)
            invariant
                *self == *old(self),
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
            assert(self.frames() =~= before.frames());
            assert forall|a: int| a != addr && #[trigger] before.maps(a) implies self.maps(a) by {
                let j = choose|j: int| 0 <= j < before.pages && #[trigger] before.state@[j] == MAPPED && before.owner@[j] == a;
                assert(self.state@[j] == MAPPED);
            }
            assert forall|a: int| #[trigger] self.maps(a) implies a != addr && before.maps(a) by {
                let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == MAPPED && self.owner@[j] == a;
                assert(j != i);
                assert(before.state@[j] == MAPPED);
                assert(occupied(before.state@[j]) && occupied(before.state@[i as int]));
                assert(before.owner@[j] != before.owner@[i as int]);
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
            final(self).same_config(old(self)),
            final(self).free_capacity() == old(self).free_capacity(),
            final(self).inv(),
            final(self).frames() == old(self).frames(),
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).parks(a),
            forall|a: int| !run_pages(start as int, pages as nat).contains(a) && #[trigger] old(self).maps(a) ==> final(self).maps(a),
            forall|a: int| #[trigger] final(self).maps(a) ==> !run_pages(start as int, pages as nat).contains(a) && old(self).maps(a),
            forall|a: int| #[trigger] old(self).parks(a) ==> final(self).parks(a),
        no_unwind
    {
        let tracked mut rest = perm.get();
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                self.same_config(old(self)),
                self.free_capacity() == old(self).free_capacity(),
                self.frames() == old(self).frames(),
                k <= pages,
                start as int % PAGE_BYTES as int == 0,
                start + pages * PAGE_BYTES <= usize::MAX + 1,
                rest.dom() =~= Set::range(start + k * PAGE_BYTES, start + pages * PAGE_BYTES),
                rest.provenance() == self.provenance@,
                forall|a: int|
                    #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, k as nat).contains(a)
                        ==> self.maps(a),
                forall|a: int| #[trigger] run_pages(start as int, k as nat).contains(a) ==> self.parks(a),
                forall|a: int| !run_pages(start as int, pages as nat).contains(a) && #[trigger] old(self).maps(a) ==> self.maps(a),
                forall|a: int| #[trigger] self.maps(a) ==> !run_pages(start as int, k as nat).contains(a) && old(self).maps(a),
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
                assert forall|a: int| #[trigger] self.maps(a) implies !run_pages(start as int, (k + 1) as nat).contains(a) && old(self).maps(a) by {
                    assert(a != addr && before.maps(a));
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
    fn back_run(
        &mut self,
        caller: &mut Tracked<Caller>,
        start: usize,
        pages: usize,
        provenance: Ghost<Provenance>,
    ) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            provenance@ == old(self).provenance@,
            start as int % PAGE_BYTES as int == 0,
            start + pages * PAGE_BYTES <= usize::MAX + 1,
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> !old(self).maps(a),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            forall|a: int| #[trigger] old(self).maps(a) ==> final(self).maps(a),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            match r.0 {
                Some(perm) => {
                    &&& perm@.is_range(start as int, pages * PAGE_BYTES)
                    &&& perm@.provenance() == provenance@
                    &&& forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).maps(a)
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a) || run_pages(start as int, pages as nat).contains(a)
                    &&& acall_ok(r.1@)
                },
                None => {
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a)
                },
            },
            (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a)) ==> {
                &&& r.0 is Some
                &&& r.1@ == Seq::<AcallStep>::empty()
                &&& final(caller)@ == old(caller)@
                &&& final(self).free_capacity() == old(self).free_capacity()
            },
            old(self).free_capacity() >= pages as int ==> {
                &&& forall|j: int| 0 <= j < r.1@.len() ==> acall_call_in_window(
                    #[trigger] r.1@[j],
                    old(self).space,
                    old(self).untyped,
                    old(self).memory,
                    old(self).pages,
                    old(self).slots,
                    old(self).window,
                    start as int,
                    pages as nat,
                )
                &&& r.0 is Some ==> final(self).free_capacity() >= old(self).free_capacity() - pages as int
                &&& r.0 is None ==> {
                    &&& r.1@.len() > 0
                    &&& acall_ok(r.1@.drop_last())
                    &&& r.1@.last().out.status == STATUS_REFUSED
                }
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let ghost parked = forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a);
        let ghost c0 = caller@;
        let ghost mut steps = Seq::<AcallStep>::empty();
        proof {
            lemma_acall_steps_none(c0);
        }
        let tracked mut run = PointsToRaw::empty(provenance@);
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                self.same_config(old(self)),
                self.serves(caller@),
                k <= pages,
                start as int % PAGE_BYTES as int == 0,
                start + pages * PAGE_BYTES <= usize::MAX + 1,
                run.dom() =~= Set::range(start as int, start + k * PAGE_BYTES),
                run.provenance() == provenance@,
                provenance@ == self.provenance@,
                c0 == old(caller)@,
                acall_steps(c0, caller@, steps),
                acall_ok(steps),
                parked == forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a),
                forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> !old(self).maps(a),
                forall|a: int| #[trigger] old(self).maps(a) ==> self.maps(a),
                forall|a: int| #[trigger] run_pages(start as int, k as nat).contains(a) ==> self.maps(a) && !old(self).maps(a),
                forall|a: int| #[trigger] self.maps(a) ==> old(self).maps(a) || run_pages(start as int, k as nat).contains(a),
                parked ==> {
                    &&& steps == Seq::<AcallStep>::empty()
                    &&& caller@ == c0
                    &&& self.free_capacity() == old(self).free_capacity()
                    &&& forall|a: int|
                        #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, k as nat).contains(a)
                            ==> self.parks(a)
                },
                old(self).free_capacity() >= pages as int ==> {
                    &&& self.free_capacity() >= old(self).free_capacity() - k as int
                    &&& forall|j: int| 0 <= j < steps.len() ==> acall_call_in_window(
                        #[trigger] steps[j],
                        old(self).space,
                        old(self).untyped,
                        old(self).memory,
                        old(self).pages,
                        old(self).slots,
                        old(self).window,
                        start as int,
                        pages as nat,
                    )
                },
            decreases pages - k,
        {
            proof {
                lemma_scale(k as int + 1, pages as int, PAGE_BYTES as int);
                lemma_scale(k as int, 1, PAGE_BYTES as int);
                lemma_run_step(start as int, k as int, pages as int);
            }
            let addr = start + k * PAGE_BYTES;
            let ghost before = *self;
            let ghost cmid = caller@;
            let ghost prev = steps;
            proof {
                assert(run_pages(start as int, pages as nat).contains(addr as int));
                assert((addr as int) % PAGE_BYTES as int == 0);
                assert(!old(self).maps(addr as int));
                assert(!run_pages(start as int, k as nat).contains(addr as int));
                assert(!before.maps(addr as int));
                if parked {
                    assert(before.parks(addr as int));
                }
            }
            let (backed, Ghost(sp)) = self.back_page(caller, addr, provenance);
            let ghost next_steps = prev + sp;
            proof {
                lemma_acall_steps_append(c0, cmid, caller@, prev, sp);
                if old(self).free_capacity() >= pages as int {
                    assert forall|j: int| 0 <= j < next_steps.len() implies acall_call_in_window(
                        #[trigger] next_steps[j],
                        old(self).space,
                        old(self).untyped,
                        old(self).memory,
                        old(self).pages,
                        old(self).slots,
                        old(self).window,
                        start as int,
                        pages as nat,
                    ) by {
                        reveal(acall_call_in_window);
                        if j < prev.len() {
                            assert(next_steps[j] == prev[j]);
                        } else {
                            let st = sp[j - prev.len()];
                            assert(next_steps[j] == st);
                            assert(acall_call_in_window(st, old(self).space, old(self).untyped, old(self).memory, old(self).pages, old(self).slots, old(self).window, addr as int, 1));
                            if let AcallCall::Map { va, .. } = st.call {
                                if !acall_setup_call(st.call, old(self).space, old(self).untyped, old(self).memory, old(self).pages, old(self).slots, old(self).window) {
                                    assert(run_pages(addr as int, 1).contains(va as int));
                                    assert(start as int <= addr as int);
                                    assert(addr + PAGE_BYTES <= start + pages * PAGE_BYTES);
                                    assert(run_pages(start as int, pages as nat).contains(va as int));
                                }
                            }
                        }
                    }
                }
            }
            match backed {
                Some(page) => {
                    proof {
                        run = run.join(page.get());
                        lemma_keeps_mapped(*self, before);
                        lemma_acall_ok_append(prev, sp);
                        steps = next_steps;
                        if parked {
                            assert(prev == Seq::<AcallStep>::empty() && sp == Seq::<AcallStep>::empty());
                            assert(steps =~= Seq::<AcallStep>::empty());
                            assert forall|a: int|
                                #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, (k + 1) as nat).contains(a)
                                    implies self.parks(a) by {
                                assert(before.parks(a));
                            }
                        }
                        assert forall|a: int| #[trigger] self.maps(a) implies old(self).maps(a) || run_pages(start as int, (k + 1) as nat).contains(a) by {
                            if a == addr {
                                assert(run_pages(start as int, (k + 1) as nat).contains(a));
                            } else {
                                assert(before.maps(a));
                                if run_pages(start as int, k as nat).contains(a) {
                                    assert(run_pages(start as int, (k + 1) as nat).contains(a));
                                }
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
                        if old(self).free_capacity() >= pages as int {
                            lemma_acall_refused_after_ok(prev, sp);
                        }
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
                        assert forall|a: int| #[trigger] self.maps(a) implies old(self).maps(a) by {
                            assert(!run_pages(start as int, k as nat).contains(a) && released.maps(a));
                            assert(before.maps(a));
                        }
                    }
                    return (None, Ghost(next_steps));
                },
            }
        }
        (Some(Tracked(run)), Ghost(steps))
    }
}

/// A record whose free capacity is not negative while a table of the window's path is unlinked has a
/// table page's block of free middle.
proof fn lemma_capacity_covers_table(r: Record)
    requires
        r.tables_unlinked() >= 1,
        r.free_capacity() >= 0,
    ensures
        r.high@ - r.low@ >= TABLE_PAGES,
{
    let n = r.tables_unlinked();
    let tp = TABLE_PAGES as int;
    assert(n * tp >= tp) by (nonlinear_arith)
        requires
            n >= 1,
            tp == 8,
    ;
}

/// Keeping every occupied page's state and address introduces no newly mapped address.
proof fn lemma_keeps_no_new_mapped(new: Record, old: Record)
    requires
        new.keeps(&old),
    ensures
        forall|a: int| #[trigger] new.maps(a) ==> old.maps(a),
{
    assert forall|a: int| #[trigger] new.maps(a) implies old.maps(a) by {
        let j = choose|j: int| 0 <= j < new.pages && #[trigger] new.state@[j] == MAPPED && new.owner@[j] == a;
        assert(occupied(new.state@[j]));
        assert(old.state@[j] == MAPPED);
    }
}

/// Keeping every occupied page's state and address is transitive.
proof fn lemma_keeps_trans(c: Record, b: Record, a: Record)
    requires
        c.keeps(&b),
        b.keeps(&a),
    ensures
        c.keeps(&a),
{
    assert forall|i: int| 0 <= i < c.pages && occupied(#[trigger] c.state@[i]) implies c.state@[i] == a.state@[i] && c.owner@[i]
        == a.owner@[i] by {
        assert(occupied(b.state@[i]));
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

/// Every page a span of `spans` holds backed is a page the record maps at its address, and every page
/// the record maps is one a span holds backed.
spec fn backed_is_mapped(spans: Map<int, Span>, record: Record) -> bool {
    &&& forall|base: int, a: int| spans.contains_key(base) && #[trigger] spans[base].backed.contains(a) ==> record.maps(a)
    &&& forall|a: int| #[trigger] record.maps(a) ==> exists|base: int| #[trigger] spans.contains_key(base) && spans[base].backed.contains(a)
}

/// A new span with no page backed keeps the pages the spans hold backed the pages the record maps: its
/// base is no span's, which would overlap it.
proof fn lemma_reserved_backed(v: SourceView, record: Record, base: int, blocks: nat)
    requires
        v.wf(),
        v.fits(base, blocks),
        backed_is_mapped(v.spans, record),
    ensures
        backed_is_mapped(v.spans.insert(base, Span { blocks, backed: Set::empty() }), record),
{
    let after = v.spans.insert(base, Span { blocks, backed: Set::empty() });
    if v.spans.contains_key(base) {
        assert(v.apart(base, blocks, base));
        assert(v.released_span(base).fits(base, v.spans[base].blocks));
        lemma_scale(1, blocks as int, BLOCK_BYTES as int);
        lemma_scale(1, v.spans[base].blocks as int, BLOCK_BYTES as int);
        assert(false);
    }
    assert forall|b: int, a: int| after.contains_key(b) && #[trigger] after[b].backed.contains(a) implies record.maps(a) by {
        assert(b != base);
        assert(v.spans[b].backed.contains(a));
    }
    assert forall|a: int| #[trigger] record.maps(a) implies exists|b: int|
        #[trigger] after.contains_key(b) && after[b].backed.contains(a) by {
        let b = choose|b: int| #[trigger] v.spans.contains_key(b) && v.spans[b].backed.contains(a);
        assert(after.contains_key(b) && after[b].backed.contains(a));
    }
}

/// Giving up a span with no page backed keeps the pages the spans hold backed the pages the record maps.
proof fn lemma_released_span_backed(spans: Map<int, Span>, record: Record, span: int)
    requires
        backed_is_mapped(spans, record),
        spans[span].backed.is_empty(),
    ensures
        backed_is_mapped(spans.remove(span), record),
{
    let after = spans.remove(span);
    assert forall|b: int, a: int| after.contains_key(b) && #[trigger] after[b].backed.contains(a) implies record.maps(a) by {
        assert(spans.contains_key(b) && spans[b].backed.contains(a));
    }
    assert forall|a: int| #[trigger] record.maps(a) implies exists|b: int|
        #[trigger] after.contains_key(b) && after[b].backed.contains(a) by {
        let b = choose|b: int| #[trigger] spans.contains_key(b) && spans[b].backed.contains(a);
        assert(b != span);
        assert(after.contains_key(b) && after[b].backed.contains(a));
    }
}

/// Backs the run of `pages` pages from `start` in the record and, when the back is granted, marks its
/// pages backed in the span at `span`, as one step, so that the pages the spans hold backed stay the
/// pages the record maps. `view` is the source's view, whose spans these are.
fn back_fields(
    spans: &mut Spans,
    record: &mut Record,
    caller: &mut Tracked<Caller>,
    span: Ghost<int>,
    start: usize,
    pages: usize,
    provenance: Ghost<Provenance>,
    view: Ghost<SourceView>,
) -> (r: (Option<Tracked<PointsToRaw>>, Ghost<Seq<AcallStep>>))
    requires
        old(spans).inv(),
        old(record).inv(),
        old(record).serves(old(caller)@),
        provenance@ == old(record).provenance@,
        backed_is_mapped(old(spans).map@, *old(record)),
        view@.spans == old(spans).map@,
        view@.wf(),
        view@.runs_in(span@, start as int, pages as nat),
        view@.unbacked(span@, start as int, pages as nat),
    ensures
        final(spans).inv(),
        final(spans).window == old(spans).window,
        final(record).same_config(old(record)),
        final(record).inv(),
        final(record).serves(final(caller)@),
        backed_is_mapped(final(spans).map@, *final(record)),
        acall_steps(old(caller)@, final(caller)@, r.1@),
        match r.0 {
            Some(perm) => {
                &&& perm@.is_range(start as int, pages * PAGE_BYTES)
                &&& perm@.provenance() == provenance@
                &&& final(spans).map@ == view@.backed_run(span@, start as int, pages as nat).spans
                &&& acall_ok(r.1@)
            },
            None => final(spans).map@ == old(spans).map@,
        },
        (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(record).parks(a)) ==> {
            &&& r.0 is Some
            &&& r.1@ == Seq::<AcallStep>::empty()
            &&& final(caller)@ == old(caller)@
            &&& final(record).free_capacity() == old(record).free_capacity()
        },
        old(record).free_capacity() >= pages as int ==> {
            &&& forall|j: int| 0 <= j < r.1@.len() ==> acall_call_in_window(
                #[trigger] r.1@[j],
                old(record).space,
                old(record).untyped,
                old(record).memory,
                old(record).pages,
                old(record).slots,
                old(record).window,
                start as int,
                pages as nat,
            )
            &&& r.0 is Some ==> final(record).free_capacity() >= old(record).free_capacity() - pages as int
            &&& r.0 is None ==> {
                &&& r.1@.len() > 0
                &&& acall_ok(r.1@.drop_last())
                &&& r.1@.last().out.status == STATUS_REFUSED
            }
        },
    no_unwind
{
    let ghost before = *record;
    let ghost view = view@;
    let ghost after = view.backed_run(span@, start as int, pages as nat).spans;
    proof {
        assert(view.released_span(span@).fits(span@, view.spans[span@].blocks));
        // No page of the run is mapped: a span holding it backed would be this one, where it is unbacked,
        // or another, which lies apart from this one.
        assert forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) implies !before.maps(a) by {
            if before.maps(a) {
                let b = choose|b: int| #[trigger] view.spans.contains_key(b) && view.spans[b].backed.contains(a);
                if b != span@ {
                    assert(view.released_span(b).fits(b, view.spans[b].blocks));
                    assert(view.released_span(b).spans.contains_key(span@));
                    assert(view.released_span(b).apart(b, view.spans[b].blocks, span@));
                }
            }
        }
    }
    let (got, steps) = record.back_run(caller, start, pages, provenance);
    match got {
        None => (None, steps),
        Some(perm) => {
            spans.rewrite(Ghost(after));
            proof {
                assert forall|base: int, a: int| after.contains_key(base) && #[trigger] after[base].backed.contains(a) implies record.maps(
                    a,
                ) by {
                    if !(base == span@ && run_pages(start as int, pages as nat).contains(a)) {
                        assert(view.spans[base].backed.contains(a));
                        assert(before.maps(a));
                    }
                }
                assert forall|a: int| #[trigger] record.maps(a) implies exists|base: int|
                    #[trigger] after.contains_key(base) && after[base].backed.contains(a) by {
                    if run_pages(start as int, pages as nat).contains(a) {
                        assert(after.contains_key(span@) && after[span@].backed.contains(a));
                    } else {
                        assert(before.maps(a));
                        let b = choose|b: int| #[trigger] view.spans.contains_key(b) && view.spans[b].backed.contains(a);
                        assert(after.contains_key(b) && after[b].backed.contains(a));
                    }
                }
            }
            (Some(perm), steps)
        },
    }
}

/// Marks the pages of the backed run of `pages` pages from `start` no longer backed in the span at
/// `span` and parks each in the record, as one step, so that the pages the spans hold backed stay the
/// pages the record maps. `view` is the source's view, whose spans these are.
fn release_fields(
    spans: &mut Spans,
    record: &mut Record,
    span: Ghost<int>,
    start: usize,
    pages: usize,
    perm: Tracked<PointsToRaw>,
    view: Ghost<SourceView>,
)
    requires
        old(spans).inv(),
        old(record).inv(),
        backed_is_mapped(old(spans).map@, *old(record)),
        view@.spans == old(spans).map@,
        view@.wf(),
        view@.runs_in(span@, start as int, pages as nat),
        view@.backed(span@, start as int, pages as nat),
        perm@.is_range(start as int, pages * PAGE_BYTES),
        perm@.provenance() == old(record).provenance@,
    ensures
        final(spans).inv(),
        final(spans).window == old(spans).window,
        final(spans).map@ == view@.released_run(span@, start as int, pages as nat).spans,
        final(record).same_config(old(record)),
        final(record).inv(),
        final(record).frames() == old(record).frames(),
        backed_is_mapped(final(spans).map@, *final(record)),
        forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(record).parks(a),
    no_unwind
{
    let ghost before = *record;
    let ghost view = view@;
    let ghost after = view.released_run(span@, start as int, pages as nat).spans;
    proof {
        assert(view.released_span(span@).fits(span@, view.spans[span@].blocks));
        assert forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) implies before.maps(a) by {
            assert(view.spans[span@].backed.contains(a));
        }
        assert forall|base: int, a: int| after.contains_key(base) && #[trigger] after[base].backed.contains(a) implies before.maps(a)
            && !run_pages(start as int, pages as nat).contains(a) by {
            assert(view.spans[base].backed.contains(a));
            assert(before.maps(a));
            if base != span@ {
                assert(view.released_span(base).fits(base, view.spans[base].blocks));
                assert(view.released_span(base).spans.contains_key(span@));
                assert(view.released_span(base).apart(base, view.spans[base].blocks, span@));
                if run_pages(start as int, pages as nat).contains(a) {
                    assert(false);
                }
            }
        }
    }
    spans.rewrite(Ghost(after));
    record.release_run(start, pages, perm);
    proof {
        assert forall|a: int| #[trigger] record.maps(a) implies exists|base: int|
            #[trigger] after.contains_key(base) && after[base].backed.contains(a) by {
            assert(!run_pages(start as int, pages as nat).contains(a) && before.maps(a));
            let b = choose|b: int| #[trigger] view.spans.contains_key(b) && view.spans[b].backed.contains(a);
            assert(after.contains_key(b) && after[b].backed.contains(a));
        }
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
    /// The `acall` steps `back` has made on the caller token.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    trace: Ghost<Seq<AcallStep>>,
}

impl Eager {
    /// Every page a span holds backed is a page the record maps at its address, and vice versa: the
    /// permission handed out for it is that page's.
    #[verifier::type_invariant]
    spec fn wf(self) -> bool {
        &&& self.spans.inv()
        &&& self.record.inv()
        &&& self.record.window == self.spans.window
        &&& self.record.provenance@ == self.exposed@@
        &&& backed_is_mapped(self.spans.map@, self.record)
    }

    /// The slot of the process's own table that names the space the source backs runs in.
    pub closed spec fn space(&self) -> u64 {
        self.record.space
    }

    /// The slot of the process's own table that names the untyped the source retypes from.
    pub closed spec fn untyped(&self) -> u64 {
        self.record.untyped
    }

    /// The physical base address of page 0 of the source's untyped.
    pub closed spec fn memory(&self) -> u64 {
        self.record.memory
    }

    /// The number of untyped pages the source tracks.
    pub closed spec fn pages(&self) -> usize {
        self.record.pages
    }

    /// The first frame capability slot in the caller's table.
    pub closed spec fn slots(&self) -> u64 {
        self.record.slots
    }

    /// The base address of the window the source hands out spans from.
    pub closed spec fn window(&self) -> usize {
        self.spans.window
    }

    /// Free untyped pages in the contiguous middle beyond `TABLE_PAGES` per unlinked window table.
    pub closed spec fn free_capacity(&self) -> int {
        self.record.free_capacity()
    }

    /// The `acall` system-call steps `back` has made on the caller token so far.
    pub closed spec fn acall_trace(&self) -> Seq<AcallStep> {
        self.trace@
    }

    /// Whether the `blocks` blocks of the window from block `first` fit apart from every reserved
    /// span.
    pub open spec fn window_fits(&self, first: int, blocks: nat) -> bool {
        &&& blocks > 0
        &&& 0 <= first
        &&& first + blocks <= WINDOW_BLOCKS
        &&& forall|other: int|
            #[trigger] self@.spans.contains_key(other) ==> self@.apart(
                self.window() + first * BLOCK_BYTES,
                blocks,
                other,
            )
    }

    /// Whether some run of `blocks` blocks in the window fits apart from every reserved span.
    pub open spec fn can_reserve(&self, blocks: nat) -> bool {
        exists|first: int| #[trigger] self.window_fits(first, blocks)
    }

    /// Every frame the source retyped and still uses is in the slot it put it in, its block counted by
    /// that capability and, for a page the source maps, the one entry that maps it, at the address the
    /// source maps it at, in the space of the token's process.
    pub closed spec fn holds(&self, token: Caller) -> bool {
        frames_held(token.kernel(), token.root(), self.record.frames())
    }

    /// A page is parked at `addr`: its run was released, and a back of it is granted with no system
    /// call.
    pub closed spec fn parks(&self, addr: int) -> bool {
        self.record.parks(addr)
    }

    /// Whether `new` accepts `memory`, `pages`, `slots` and `window`: at most `MAX_PAGES` pages fitting
    /// in physical addresses from `memory`, `slots` a slot with every frame slot of the `pages` pages in
    /// the table, and `window` a non-null region-aligned address with room for the window after it.
    pub open spec fn new_ok(memory: u64, pages: usize, slots: u64, window: *mut u8) -> bool {
        &&& pages <= MAX_PAGES
        &&& slots < TABLE_INDICES
        &&& slots as int % LEAF_INDICES as int != 0
        &&& pages > 0 ==> frame_slot(slots as int, pages - 1) < TABLE_INDICES
        &&& memory + pages * PAGE_BYTES <= u64::MAX
        &&& window@.addr != 0
        &&& window@.addr as int % REGION_BYTES as int == 0
        &&& window@.addr + WINDOW_BYTES <= usize::MAX
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
                    &&& Self::new_ok(memory, pages, slots, window)
                    &&& source@.wf()
                    &&& source@.spans.is_empty()
                    &&& source@.grants == Seq::<Request>::empty()
                    &&& source@.refusals == Seq::<Refusal>::empty()
                    &&& source@.provenance == window@.provenance
                    &&& source.space() == space
                    &&& source.untyped() == untyped
                    &&& source.memory() == memory
                    &&& source.pages() == pages
                    &&& source.slots() == slots
                    &&& source.window() == window@.addr
                    &&& source.free_capacity() == pages as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int
                    &&& source.acall_trace() == Seq::<AcallStep>::empty()
                    &&& forall|token: Caller| #[trigger] source.holds(token)
                },
                None => !Self::new_ok(memory, pages, slots, window),
            },
    {
        let addr = window.addr();
        if pages > MAX_PAGES || slots >= TABLE_INDICES as u64 || slots % LEAF_INDICES as u64 == 0 {
            return None;
        }
        if pages > 0 && frame_slot_at(slots, pages - 1) >= TABLE_INDICES as u64 {
            return None;
        }
        proof {
            assert(MAX_PAGES >= BLOCK_PAGES + 64);
            assert(0int % TABLE_PAGES as int == 0) by (compute);
            lemma_frame_slots_cross_leaves(slots as int);
            assert forall|i: int| 0 <= i < pages implies index_ok(#[trigger] frame_slot(slots as int, i) as usize)
                && 0 <= frame_slot(slots as int, i) < TABLE_INDICES by {
                lemma_frame_slot(slots as int, i, pages - 1);
                lemma_frame_slot(slots as int, i, i);
            }
            assert forall|i: int, j: int| 0 <= i < j < pages implies #[trigger] frame_slot(slots as int, i) < #[trigger] frame_slot(
                slots as int,
                j,
            ) by {
                lemma_frame_slot(slots as int, i, j);
            }
            assert(slots_ok(slots, pages)) by {
                reveal(slots_ok);
            }
            lemma_scale(pages as int, MAX_PAGES as int, PAGE_BYTES as int);
            if addr as int % REGION_BYTES as int == 0 {
                let q = addr as int / REGION_BYTES as int;
                lemma_fundamental_div_mod(addr as int, REGION_BYTES as int);
                assert(addr as int == (q * BLOCK_PAGES as int) * BLOCK_BYTES as int) by (nonlinear_arith)
                    requires
                        addr as int == REGION_BYTES as int * q,
                        REGION_BYTES == BLOCK_BYTES * BLOCK_PAGES,
                ;
                lemma_mod_multiples_basic(q * BLOCK_PAGES as int, BLOCK_BYTES as int);
            }
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
                #[cfg(verus_keep_ghost)]
                parked: Tracked(Map::tracked_empty()),
                #[cfg(verus_keep_ghost)]
                provenance: Ghost(exposed@@),
                #[cfg(verus_keep_ghost)]
                low: Ghost(0),
                #[cfg(verus_keep_ghost)]
                high: Ghost(pages as int),
            },
            exposed,
            grants: Ghost(Seq::empty()),
            refusals: Ghost(Seq::empty()),
            trace: Ghost(Seq::empty()),
        };
        assert(source@.spans =~= Map::empty());
        assert(source.record.frames() =~= Map::empty());
        assert(source.record.tables_unlinked() == 2 + WINDOW_BLOCKS as int);
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
        &&& own_process(token)
        &&& names_own_space(token, self.space())
        &&& self.holds(token)
    }

    /// Grants the lowest run of `blocks` blocks in the window that fits apart from every reserved
    /// span, and refuses only when none fits.
    fn reserve(&mut self, token: &mut Tracked<Caller>, blocks: usize) -> (r: Option<*mut u8>)
        ensures
            final(token)@ == old(token)@,
            final(self).space() == old(self).space(),
            final(self).untyped() == old(self).untyped(),
            final(self).memory() == old(self).memory(),
            final(self).pages() == old(self).pages(),
            final(self).slots() == old(self).slots(),
            final(self).window() == old(self).window(),
            final(self).free_capacity() == old(self).free_capacity(),
            final(self).acall_trace() == old(self).acall_trace(),
            match r {
                Some(base) => {
                    let first = (base@.addr - old(self).window()) / BLOCK_BYTES as int;
                    &&& old(self).can_reserve(blocks as nat)
                    &&& base@.addr == old(self).window() + first * BLOCK_BYTES
                    &&& old(self).window_fits(first, blocks as nat)
                    &&& forall|earlier: int|
                        0 <= earlier < first ==> !#[trigger] old(self).window_fits(earlier, blocks as nat)
                },
                None => !old(self).can_reserve(blocks as nat),
            },
            old(self).window_fits(0, blocks as nat) ==> r is Some,
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost before = self@;
        proof {
            // Whichever span the reserve grants, the pages the spans hold backed stay the pages the record maps.
            assert forall|base: int| before.fits(base, blocks as nat) implies backed_is_mapped(
                #[trigger] before.spans.insert(base, Span { blocks: blocks as nat, backed: Set::empty() }),
                self.record,
            ) by {
                lemma_reserved_backed(before, self.record, base, blocks as nat);
            }
        }
        match self.spans.reserve(blocks, Ghost(before)) {
            None => {
                let ghost r = Refusal { request: Request::Reserve { blocks: blocks as nat }, spans: before.spans };
                proof {
                    lemma_recorded_wf(before, r);
                    if old(self).can_reserve(blocks as nat) {
                        let first = choose|first: int| #[trigger] old(self).window_fits(first, blocks as nat);
                        assert(old(self).spans.fits_at(before, first, blocks as nat));
                    }
                }
                self.refusals = Ghost(self.refusals@.push(r));
                None
            },
            Some(base) => {
                proof {
                    lemma_reserved_wf(before, base as int, blocks as nat);
                }
                self.grants = Ghost(self.grants@.push(Request::Reserve { blocks: blocks as nat }));
                let ptr: *mut u8 = with_exposed_provenance(base, self.exposed);
                proof {
                    let first = (ptr@.addr - old(self).window()) / BLOCK_BYTES as int;
                    assert(old(self).spans.fits_at(before, first, blocks as nat));
                    assert(old(self).window_fits(first, blocks as nat));
                    assert forall|earlier: int| 0 <= earlier < first implies !#[trigger] old(self).window_fits(earlier, blocks as nat) by {
                        assert(!old(self).spans.fits_at(before, earlier, blocks as nat));
                    }
                }
                Some(ptr)
            },
        }
    }

    /// A run whose every page is parked is granted with no system call; while free capacity covers the
    /// run, every `acall` step stays within the source's window, slots and untyped, and the run is
    /// granted unless `acall` refuses a step.
    fn back(&mut self, token: &mut Tracked<Caller>, span: Ghost<int>, start: usize, pages: usize) -> (r: Option<Tracked<PointsToRaw>>)
        ensures
            final(self).space() == old(self).space(),
            final(self).untyped() == old(self).untyped(),
            final(self).memory() == old(self).memory(),
            final(self).pages() == old(self).pages(),
            final(self).slots() == old(self).slots(),
            final(self).window() == old(self).window(),
            (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a)) ==> r is Some,
            ({
                let n = old(self).acall_trace().len() as int;
                let steps = final(self).acall_trace().skip(n);
                &&& n <= final(self).acall_trace().len()
                &&& final(self).acall_trace().take(n) == old(self).acall_trace()
                &&& acall_steps(old(token)@, final(token)@, steps)
                &&& r is Some ==> acall_ok(steps)
                &&& (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a)) ==> {
                    &&& steps == Seq::<AcallStep>::empty()
                    &&& final(token)@ == old(token)@
                    &&& final(self).free_capacity() == old(self).free_capacity()
                }
                &&& old(self).free_capacity() >= pages as int ==> {
                    &&& forall|k: int| 0 <= k < steps.len() ==> acall_call_in_window(
                        #[trigger] steps[k],
                        old(self).space(),
                        old(self).untyped(),
                        old(self).memory(),
                        old(self).pages(),
                        old(self).slots(),
                        old(self).window(),
                        start as int,
                        pages as nat,
                    )
                    &&& r is Some ==> final(self).free_capacity() >= old(self).free_capacity() - pages as int
                    &&& r is None ==> {
                        &&& steps.len() > 0
                        &&& acall_ok(steps.drop_last())
                        &&& steps.last().out.status == STATUS_REFUSED
                    }
                    &&& acall_ok(steps) ==> r is Some
                }
            }),
    {
        proof {
            use_type_invariant(&*self);
        }
        let ghost before = self@;
        let ghost record = self.record;
        let ghost old_trace = self.trace@;
        let (got, Ghost(steps)) = back_fields(
            &mut self.spans,
            &mut self.record,
            token,
            span,
            start,
            pages,
            Ghost(self.exposed@@),
            Ghost(before),
        );
        self.trace = Ghost(old_trace + steps);
        proof {
            assert(self.trace@.take(old_trace.len() as int) =~= old_trace);
            assert(self.trace@.skip(old_trace.len() as int) =~= steps);
        }
        match got {
            None => {
                let ghost r = Refusal { request: Request::Back { span: span@, start: start as int, pages: pages as nat }, spans: before.spans };
                proof {
                    lemma_recorded_wf(before, r);
                    if record.free_capacity() >= pages as int && acall_ok(steps) {
                        assert(steps[steps.len() - 1].out.status == STATUS_OK);
                    }
                }
                self.refusals = Ghost(self.refusals@.push(r));
                None
            },
            Some(perm) => {
                proof {
                    lemma_backed_run_wf(before, span@, start as int, pages as nat);
                }
                self.grants = Ghost(self.grants@.push(Request::Back { span: span@, start: start as int, pages: pages as nat }));
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
            lemma_released_run_wf(self@, span@, start as int, pages as nat);
        }
        let ghost before = self@;
        release_fields(&mut self.spans, &mut self.record, span, start, pages, perm, Ghost(before));
    }

    fn release_span(&mut self, token: &mut Tracked<Caller>, span: usize)
        ensures
            final(self).window() == old(self).window(),
    {
        proof {
            use_type_invariant(&*self);
            lemma_released_span_wf(self@, span as int);
            lemma_released_span_backed(self.spans.map@, self.record, span as int);
        }
        self.spans.release(span, Ghost(self@));
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
