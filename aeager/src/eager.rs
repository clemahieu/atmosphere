// SPDX-License-Identifier: MIT

//! The eager source: spans of a window of a few blocks, and frames and table pages retyped from a
//! small untyped, with no fault delivery.
//!
//! `Spans` is the window's bookkeeping, which the contract's view rests on: which blocks of the window
//! a span holds, and the spans by base. `Record` is what the source knows of its untyped: each page
//! free, held as a frame for reuse, mapped, parked, or taken by a table page or by a retype or unmap
//! the kernel refused, and which tables of the window's path are linked. Its proof is that every index
//! and address it computes is in range, that the pages a span holds backed are the pages the record
//! maps at their addresses, that a released page is parked at its address and backs that address again
//! with no system call, that every `acall` step stays within the source's window, slots and untyped,
//! and that a back refuses only when the untyped lacks a table block or frame the run needs or `acall`
//! refuses a step.
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

/// Whether the non-empty run of `pages` pages from `start` overlaps block `b` of `window`.
pub open spec fn run_touches_block(window: usize, start: int, pages: nat, b: int) -> bool {
    let base = window_block(window, b);
    &&& pages > 0
    &&& start < base + BLOCK_BYTES as int
    &&& base < start + pages * PAGE_BYTES as int
}

/// Whether `call` is a table-page, frame-retype, link, unmap or inspect call of an eager source
/// configured with `(space, untyped, memory, max_pages, slots, window)`.
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
        AcallCall::Unmap { slot, va, level } => {
            &&& slot == space
            &&& level == 1
            &&& window as int <= va as int
            &&& (va as int) < window as int + WINDOW_BYTES as int
            &&& va as int % PAGE_BYTES as int == 0
        },
        AcallCall::Inspect { at } =>
            exists|i: int| 0 <= i < max_pages && at as int == #[trigger] frame_slot(slots as int, i),
        _ => false,
    }
}

/// Whether `step` is an `acall::memory` call made while backing `count` pages from `start` on an
/// eager source configured with `(space, untyped, memory, max_pages, slots, window)`.
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

/// A step sequence either has every step accepted, or is non-empty with every step before the last
/// accepted and the last step refused.
spec fn step_seq_well_ended(steps: Seq<AcallStep>) -> bool {
    !acall_ok(steps) <==> {
        &&& steps.len() > 0
        &&& acall_ok(steps.drop_last())
        &&& steps.last().out.status == STATUS_REFUSED
    }
}

/// Appending a well-ended step sequence after an accepted prefix yields a well-ended step sequence.
proof fn lemma_well_ended_append(s1: Seq<AcallStep>, s2: Seq<AcallStep>)
    requires
        acall_ok(s1),
        step_seq_well_ended(s2),
    ensures
        step_seq_well_ended(s1 + s2),
{
    lemma_acall_ok_append(s1, s2);
    let s = s1 + s2;
    if acall_ok(s2) {
        if s.len() > 0 && s.last().out.status == STATUS_REFUSED {
            assert(s[s.len() - 1].out.status == STATUS_OK);
            assert(STATUS_REFUSED != STATUS_OK);
        }
    } else {
        lemma_acall_refused_after_ok(s1, s2);
    }
}

/// A page-aligned address inside `window` lies in block `(addr - window) / BLOCK_BYTES`, and its
/// one-page run overlaps that block of `window` alone.
proof fn lemma_addr_block(window: usize, addr: usize)
    requires
        window as int % BLOCK_BYTES as int == 0,
        window + WINDOW_BYTES <= usize::MAX,
        window <= addr < window + WINDOW_BYTES,
        addr as int % PAGE_BYTES as int == 0,
    ensures
        0 <= ((addr - window) as int) / (BLOCK_BYTES as int),
        ((addr - window) as int) / (BLOCK_BYTES as int) < WINDOW_BLOCKS,
        run_touches_block(window, addr as int, 1, (addr - window) as int / BLOCK_BYTES as int),
        forall|c: int|
            0 <= c < WINDOW_BLOCKS && c != (addr - window) as int / BLOCK_BYTES as int
                ==> !#[trigger] run_touches_block(window, addr as int, 1, c),
{
    let off = (addr - window) as int;
    let bb = BLOCK_BYTES as int;
    let p = PAGE_BYTES as int;
    let bp = BLOCK_PAGES as int;
    let b = off / bb;
    lemma_div_pos_is_pos(off, bb);
    lemma_multiply_divide_lt(off, bb, WINDOW_BLOCKS as int);
    lemma_fundamental_div_mod(off, bb);
    lemma_mod_bound(off, bb);
    lemma_fundamental_div_mod(window as int, bb);
    lemma_fundamental_div_mod(addr as int, p);
    let qw = window as int / bb;
    let qa = addr as int / p;
    let next_base = window_block(window, b + 1);
    assert(window_block(window, b) <= addr as int) by (nonlinear_arith)
        requires
            off == addr as int - window as int,
            off == bb * b + off % bb,
            off % bb >= 0,
            window_block(window, b) == window as int + b * bb,
    ;
    assert((addr as int) < next_base) by (nonlinear_arith)
        requires
            off == addr as int - window as int,
            off == bb * b + off % bb,
            off % bb < bb,
            next_base == window as int + (b + 1) * bb,
    ;
    let qn = (qw + b + 1) * bp;
    assert(next_base == p * qn) by (nonlinear_arith)
        requires
            window as int == bb * qw,
            next_base == window as int + (b + 1) * bb,
            qn == (qw + b + 1) * bp,
            bb == p * bp,
    ;
    assert(qa < qn) by (nonlinear_arith)
        requires
            addr as int == p * qa,
            next_base == p * qn,
            (addr as int) < next_base,
            p > 0,
    ;
    assert(addr as int + p <= window_block(window, b) + bb) by (nonlinear_arith)
        requires
            addr as int == p * qa,
            next_base == p * qn,
            qa + 1 <= qn,
            next_base == window_block(window, b) + bb,
            p > 0,
    ;
    assert forall|c: int| 0 <= c < WINDOW_BLOCKS && c != b implies !#[trigger] run_touches_block(window, addr as int, 1, c) by {
        if c < b {
            assert(window_block(window, c) + bb <= window_block(window, b)) by (nonlinear_arith)
                requires
                    c + 1 <= b,
                    window_block(window, c) == window as int + c * bb,
                    window_block(window, b) == window as int + b * bb,
                    bb > 0,
            ;
        } else {
            assert(window_block(window, b) + bb <= window_block(window, c)) by (nonlinear_arith)
                requires
                    b + 1 <= c,
                    window_block(window, c) == window as int + c * bb,
                    window_block(window, b) == window as int + b * bb,
                    bb > 0,
            ;
        }
    }
}

/// A non-empty run touches block `b` iff its first page or its remaining tail does.
proof fn lemma_run_touches_step(window: usize, start: int, pages: nat, b: int)
    requires
        pages >= 1,
    ensures
        run_touches_block(window, start, pages, b)
            <==> (run_touches_block(window, start, 1, b)
                || run_touches_block(window, start + PAGE_BYTES as int, (pages - 1) as nat, b)),
{
    let p = PAGE_BYTES as int;
    assert((pages as int - 1) * p == pages as int * p - p) by (nonlinear_arith);
    if pages > 1 {
        assert(pages as int * p >= p) by (nonlinear_arith)
            requires
                pages > 1,
                p > 0,
        ;
    }
}

/// Extending a run of `k` pages by the page after it touches block `b` iff the prefix or the added
/// page does.
proof fn lemma_run_touches_snoc(window: usize, start: int, k: nat, b: int)
    ensures
        run_touches_block(window, start, k + 1, b)
            <==> (run_touches_block(window, start, k, b)
                || run_touches_block(window, start + k * PAGE_BYTES as int, 1, b)),
{
    let p = PAGE_BYTES as int;
    assert((k + 1) * p == k * p + p) by (nonlinear_arith);
    if k > 0 {
        assert(k * p > 0) by (nonlinear_arith)
            requires
                k > 0,
                p > 0,
        ;
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

/// Whether a page in `state` is available as a frame: free in the untyped, held unmapped, or parked.
spec fn page_avail(s: u8) -> bool {
    s == FREE || s == HELD || s == PARKED
}

/// Count of pages in `0..n` whose state in `state` is available as a frame.
spec fn avail_upto(state: Seq<u8>, n: int) -> nat
    decreases if n > 0 { n } else { 0 },
{
    if n <= 0 {
        0
    } else {
        avail_upto(state, n - 1) + if page_avail(state[n - 1]) { 1nat } else { 0nat }
    }
}

/// Whether all `TABLE_PAGES` pages of order-3 group `g` in `state` are `FREE`.
spec fn group_free_in(state: Seq<u8>, g: int) -> bool {
    let base = g * TABLE_PAGES as int;
    &&& state[base] == FREE
    &&& state[base + 1] == FREE
    &&& state[base + 2] == FREE
    &&& state[base + 3] == FREE
    &&& state[base + 4] == FREE
    &&& state[base + 5] == FREE
    &&& state[base + 6] == FREE
    &&& state[base + 7] == FREE
}

/// Count of free order-3 groups in `0..ng` of `state`.
spec fn free_groups_upto(state: Seq<u8>, ng: int) -> nat
    decreases if ng > 0 { ng } else { 0 },
{
    if ng <= 0 {
        0
    } else {
        free_groups_upto(state, ng - 1) + if group_free_in(state, ng - 1) { 1nat } else { 0nat }
    }
}

/// Whether page `u` of `state` lies in one of its first `ng` order-3 groups, and that group is free.
/// Opaque, so that a fact about every free page names no other page.
#[verifier::opaque]
spec fn in_free_group(state: Seq<u8>, ng: int, u: int) -> bool {
    (u / TABLE_PAGES as int) < ng && group_free_in(state, u / TABLE_PAGES as int)
}

proof fn lemma_in_free_group(state: Seq<u8>, ng: int, u: int)
    ensures
        in_free_group(state, ng, u) <==> ((u / TABLE_PAGES as int) < ng && group_free_in(state, u / TABLE_PAGES as int)),
{
    reveal(in_free_group);
}

proof fn lemma_avail_bound(state: Seq<u8>, n: int)
    requires
        0 <= n <= state.len(),
    ensures
        avail_upto(state, n) <= n as nat,
    decreases n,
{
    if n > 0 {
        lemma_avail_bound(state, n - 1);
    }
}

proof fn lemma_avail_all_free(state: Seq<u8>, n: int)
    requires
        0 <= n <= state.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] state[i] == FREE,
    ensures
        avail_upto(state, n) == n as nat,
    decreases n,
{
    if n > 0 {
        assert(state[n - 1] == FREE);
        lemma_avail_all_free(state, n - 1);
    }
}

proof fn lemma_avail_at_least_one(state: Seq<u8>, n: int, idx: int)
    requires
        0 <= idx < n <= state.len(),
        page_avail(state[idx]),
    ensures
        avail_upto(state, n) >= 1,
    decreases n,
{
    if idx < n - 1 {
        lemma_avail_at_least_one(state, n - 1, idx);
    }
}

proof fn lemma_avail_none(state: Seq<u8>, n: int)
    requires
        0 <= n <= state.len(),
        forall|i: int| 0 <= i < n ==> !page_avail(#[trigger] state[i]),
    ensures
        avail_upto(state, n) == 0,
    decreases n,
{
    if n > 0 {
        assert(!page_avail(state[n - 1]));
        lemma_avail_none(state, n - 1);
    }
}

proof fn lemma_avail_eq(s1: Seq<u8>, s2: Seq<u8>, m: int)
    requires
        0 <= m <= s1.len(),
        m <= s2.len(),
        forall|i: int| 0 <= i < m ==> #[trigger] s2[i] == s1[i],
    ensures
        avail_upto(s2, m) == avail_upto(s1, m),
    decreases m,
{
    if m > 0 {
        assert(s2[m - 1] == s1[m - 1]);
        lemma_avail_eq(s1, s2, m - 1);
    }
}

proof fn lemma_avail_update(s1: Seq<u8>, s2: Seq<u8>, n: int, idx: int)
    requires
        0 <= idx < n <= s1.len(),
        s2.len() == s1.len(),
        forall|i: int| 0 <= i < n && i != idx ==> #[trigger] s2[i] == s1[i],
    ensures
        avail_upto(s2, n) as int - (if page_avail(s2[idx]) { 1int } else { 0int })
            == avail_upto(s1, n) as int - (if page_avail(s1[idx]) { 1int } else { 0int }),
    decreases n,
{
    if idx == n - 1 {
        lemma_avail_eq(s1, s2, n - 1);
    } else {
        assert(s2[n - 1] == s1[n - 1]);
        lemma_avail_update(s1, s2, n - 1, idx);
    }
}

proof fn lemma_avail_tail_zero(state: Seq<u8>, m: int, n: int)
    requires
        0 <= m <= n <= state.len(),
        forall|u: int| m <= u < n ==> !page_avail(#[trigger] state[u]),
    ensures
        avail_upto(state, n) == avail_upto(state, m),
    decreases n - m,
{
    if m < n {
        assert(!page_avail(state[n - 1]));
        lemma_avail_tail_zero(state, m, n - 1);
    }
}

proof fn lemma_free_groups_all_free(state: Seq<u8>, ng: int)
    requires
        0 <= ng,
        ng * TABLE_PAGES <= state.len(),
        forall|i: int| 0 <= i < ng * TABLE_PAGES ==> #[trigger] state[i] == FREE,
    ensures
        free_groups_upto(state, ng) == ng as nat,
    decreases ng,
{
    if ng > 0 {
        let base = (ng - 1) * TABLE_PAGES as int;
        assert(base + 8 == ng * TABLE_PAGES as int) by (nonlinear_arith)
            requires
                base == (ng - 1) * (TABLE_PAGES as int),
                TABLE_PAGES == 8,
        ;
        assert(base >= 0) by (nonlinear_arith)
            requires
                ng >= 1,
                base == (ng - 1) * (TABLE_PAGES as int),
                TABLE_PAGES == 8,
        ;
        assert(state[base] == FREE);
        assert(state[base + 1] == FREE);
        assert(state[base + 2] == FREE);
        assert(state[base + 3] == FREE);
        assert(state[base + 4] == FREE);
        assert(state[base + 5] == FREE);
        assert(state[base + 6] == FREE);
        assert(state[base + 7] == FREE);
        lemma_free_groups_all_free(state, ng - 1);
    }
}

proof fn lemma_free_groups_at_least_one(state: Seq<u8>, ng: int, g0: int)
    requires
        0 <= g0 < ng,
        ng * TABLE_PAGES <= state.len(),
        group_free_in(state, g0),
    ensures
        free_groups_upto(state, ng) >= 1,
    decreases ng,
{
    if g0 < ng - 1 {
        assert((ng - 1) * TABLE_PAGES <= ng * TABLE_PAGES) by (nonlinear_arith)
            requires
                TABLE_PAGES == 8,
        ;
        lemma_free_groups_at_least_one(state, ng - 1, g0);
    }
}

proof fn lemma_free_groups_none(state: Seq<u8>, ng: int)
    requires
        0 <= ng,
        ng * TABLE_PAGES <= state.len(),
        forall|g: int| 0 <= g < ng ==> !#[trigger] group_free_in(state, g),
    ensures
        free_groups_upto(state, ng) == 0,
    decreases ng,
{
    if ng > 0 {
        assert(!group_free_in(state, ng - 1));
        assert((ng - 1) * TABLE_PAGES <= ng * TABLE_PAGES) by (nonlinear_arith)
            requires
                TABLE_PAGES == 8,
        ;
        lemma_free_groups_none(state, ng - 1);
    }
}

proof fn lemma_free_groups_has_witness(state: Seq<u8>, ng: int) -> (g0: int)
    requires
        0 <= ng,
        ng * TABLE_PAGES <= state.len(),
        free_groups_upto(state, ng) >= 1,
    ensures
        0 <= g0 < ng,
        group_free_in(state, g0),
    decreases ng,
{
    if group_free_in(state, ng - 1) {
        ng - 1
    } else {
        assert((ng - 1) * TABLE_PAGES <= ng * TABLE_PAGES) by (nonlinear_arith)
            requires
                TABLE_PAGES == 8,
        ;
        lemma_free_groups_has_witness(state, ng - 1)
    }
}

proof fn lemma_free_groups_eq(s1: Seq<u8>, s2: Seq<u8>, ng: int)
    requires
        0 <= ng,
        ng * TABLE_PAGES <= s1.len(),
        s2.len() == s1.len(),
        forall|g: int| 0 <= g < ng ==> #[trigger] group_free_in(s2, g) == group_free_in(s1, g),
    ensures
        free_groups_upto(s2, ng) == free_groups_upto(s1, ng),
    decreases ng,
{
    if ng > 0 {
        assert(group_free_in(s2, ng - 1) == group_free_in(s1, ng - 1));
        assert((ng - 1) * TABLE_PAGES <= ng * TABLE_PAGES) by (nonlinear_arith)
            requires
                TABLE_PAGES == 8,
        ;
        lemma_free_groups_eq(s1, s2, ng - 1);
    }
}

proof fn lemma_free_groups_nonfree_change(s1: Seq<u8>, s2: Seq<u8>, ng: int, idx: int)
    requires
        0 <= ng,
        ng * TABLE_PAGES <= s1.len(),
        s2.len() == s1.len(),
        0 <= idx < s1.len(),
        s1[idx] != FREE,
        s2[idx] != FREE,
        forall|j: int| 0 <= j < s1.len() && j != idx ==> #[trigger] s2[j] == s1[j],
    ensures
        free_groups_upto(s2, ng) == free_groups_upto(s1, ng),
{
    assert forall|g: int| 0 <= g < ng implies #[trigger] group_free_in(s2, g) == group_free_in(s1, g) by {
        let base = g * TABLE_PAGES as int;
        assert(0 <= base && base + 8 <= ng * TABLE_PAGES as int) by (nonlinear_arith)
            requires
                0 <= g < ng,
                base == g * (TABLE_PAGES as int),
                TABLE_PAGES == 8,
        ;
        assert forall|k: int| 0 <= k < 8 implies (#[trigger] s2[base + k] == FREE) == (s1[base + k] == FREE) by {
            if base + k != idx {
                assert(s2[base + k] == s1[base + k]);
            }
        }
        assert((s2[base + 0] == FREE) == (s1[base + 0] == FREE));
        assert((s2[base + 1] == FREE) == (s1[base + 1] == FREE));
        assert((s2[base + 2] == FREE) == (s1[base + 2] == FREE));
        assert((s2[base + 3] == FREE) == (s1[base + 3] == FREE));
        assert((s2[base + 4] == FREE) == (s1[base + 4] == FREE));
        assert((s2[base + 5] == FREE) == (s1[base + 5] == FREE));
        assert((s2[base + 6] == FREE) == (s1[base + 6] == FREE));
        assert((s2[base + 7] == FREE) == (s1[base + 7] == FREE));
    }
    lemma_free_groups_eq(s1, s2, ng);
}

proof fn lemma_free_groups_loose_change(s1: Seq<u8>, s2: Seq<u8>, ng: int, idx: int)
    requires
        0 <= ng,
        ng * TABLE_PAGES <= s1.len(),
        s2.len() == s1.len(),
        0 <= idx < s1.len(),
        s2[idx] != FREE,
        idx / TABLE_PAGES as int >= ng || !group_free_in(s1, idx / TABLE_PAGES as int),
        forall|j: int| 0 <= j < s1.len() && j != idx ==> #[trigger] s2[j] == s1[j],
    ensures
        free_groups_upto(s2, ng) == free_groups_upto(s1, ng),
{
    let tp = TABLE_PAGES as int;
    lemma_fundamental_div_mod(idx, tp);
    lemma_mod_bound(idx, tp);
    let q = idx / tp;
    let r = idx % tp;
    assert forall|g: int| 0 <= g < ng implies #[trigger] group_free_in(s2, g) == group_free_in(s1, g) by {
        let base = g * tp;
        assert(0 <= base && base + 8 <= ng * tp) by (nonlinear_arith)
            requires
                0 <= g < ng,
                base == g * tp,
                tp == 8,
        ;
        if g == q {
            assert(idx == base + r) by (nonlinear_arith)
                requires
                    idx == tp * q + r,
                    base == g * tp,
                    g == q,
            ;
            assert(!group_free_in(s1, g));
            if r == 0 {
                assert(s2[base] != FREE);
            } else if r == 1 {
                assert(s2[base + 1] != FREE);
            } else if r == 2 {
                assert(s2[base + 2] != FREE);
            } else if r == 3 {
                assert(s2[base + 3] != FREE);
            } else if r == 4 {
                assert(s2[base + 4] != FREE);
            } else if r == 5 {
                assert(s2[base + 5] != FREE);
            } else if r == 6 {
                assert(s2[base + 6] != FREE);
            } else {
                assert(r == 7);
                assert(s2[base + 7] != FREE);
            }
            assert(!group_free_in(s2, g));
        } else {
            assert forall|k: int| 0 <= k < 8 implies #[trigger] s2[base + k] == s1[base + k] by {
                assert(base + k != idx) by (nonlinear_arith)
                    requires
                        idx == tp * q + r,
                        0 <= r < 8,
                        0 <= k < 8,
                        base == g * tp,
                        g != q,
                        tp == 8,
                ;
            }
            assert(s2[base + 0] == s1[base + 0]);
            assert(s2[base + 1] == s1[base + 1]);
            assert(s2[base + 2] == s1[base + 2]);
            assert(s2[base + 3] == s1[base + 3]);
            assert(s2[base + 4] == s1[base + 4]);
            assert(s2[base + 5] == s1[base + 5]);
            assert(s2[base + 6] == s1[base + 6]);
            assert(s2[base + 7] == s1[base + 7]);
        }
    }
    lemma_free_groups_eq(s1, s2, ng);
}

proof fn lemma_free_groups_update_one(s1: Seq<u8>, s2: Seq<u8>, ng: int, g0: int)
    requires
        0 <= g0 < ng,
        ng * TABLE_PAGES <= s1.len(),
        s2.len() == s1.len(),
        forall|j: int|
            0 <= j < ng * TABLE_PAGES && !(g0 * TABLE_PAGES <= j < (g0 + 1) * TABLE_PAGES)
                ==> #[trigger] s2[j] == s1[j],
    ensures
        free_groups_upto(s2, ng) as int - (if group_free_in(s2, g0) { 1int } else { 0int })
            == free_groups_upto(s1, ng) as int - (if group_free_in(s1, g0) { 1int } else { 0int }),
    decreases ng,
{
    let tp = TABLE_PAGES as int;
    assert((ng - 1) * tp <= ng * tp) by (nonlinear_arith)
        requires
            tp == 8,
    ;
    if g0 == ng - 1 {
        assert forall|g: int| 0 <= g < ng - 1 implies #[trigger] group_free_in(s2, g) == group_free_in(s1, g) by {
            let base = g * tp;
            assert(0 <= base && base + 8 <= g0 * tp) by (nonlinear_arith)
                requires
                    0 <= g < g0,
                    base == g * tp,
                    tp == 8,
            ;
            assert(s2[base] == s1[base]);
            assert(s2[base + 1] == s1[base + 1]);
            assert(s2[base + 2] == s1[base + 2]);
            assert(s2[base + 3] == s1[base + 3]);
            assert(s2[base + 4] == s1[base + 4]);
            assert(s2[base + 5] == s1[base + 5]);
            assert(s2[base + 6] == s1[base + 6]);
            assert(s2[base + 7] == s1[base + 7]);
        }
        lemma_free_groups_eq(s1, s2, ng - 1);
    } else {
        let base = (ng - 1) * tp;
        assert((g0 + 1) * tp <= base && base + 8 == ng * tp) by (nonlinear_arith)
            requires
                0 <= g0 < ng - 1,
                base == (ng - 1) * tp,
                tp == 8,
        ;
        assert(s2[base] == s1[base]);
        assert(s2[base + 1] == s1[base + 1]);
        assert(s2[base + 2] == s1[base + 2]);
        assert(s2[base + 3] == s1[base + 3]);
        assert(s2[base + 4] == s1[base + 4]);
        assert(s2[base + 5] == s1[base + 5]);
        assert(s2[base + 6] == s1[base + 6]);
        assert(s2[base + 7] == s1[base + 7]);
        assert(group_free_in(s2, ng - 1) == group_free_in(s1, ng - 1));
        lemma_free_groups_update_one(s1, s2, ng - 1, g0);
    }
}

/// Changing one page of a free group among the first `ng` keeps the count of free groups or lowers
/// it by one.
proof fn lemma_free_groups_break_one(s1: Seq<u8>, s2: Seq<u8>, ng: int, idx: int)
    requires
        0 <= idx,
        ng * TABLE_PAGES <= s1.len(),
        s2.len() == s1.len(),
        (idx / TABLE_PAGES as int) < ng,
        group_free_in(s1, idx / TABLE_PAGES as int),
        forall|j: int| 0 <= j < s1.len() && j != idx ==> #[trigger] s2[j] == s1[j],
    ensures
        free_groups_upto(s2, ng) <= free_groups_upto(s1, ng) <= free_groups_upto(s2, ng) + 1,
{
    let tp = TABLE_PAGES as int;
    let g0 = idx / tp;
    lemma_div_pos_is_pos(idx, tp);
    lemma_fundamental_div_mod(idx, tp);
    lemma_mod_bound(idx, tp);
    assert forall|j: int| 0 <= j < ng * TABLE_PAGES && !(g0 * TABLE_PAGES <= j < (g0 + 1) * TABLE_PAGES)
        implies #[trigger] s2[j] == s1[j] by {
        assert(j != idx) by (nonlinear_arith)
            requires
                idx == tp * g0 + idx % tp,
                0 <= idx % tp < tp,
                !(g0 * tp <= j < (g0 + 1) * tp),
                tp == 8,
        ;
    }
    lemma_free_groups_update_one(s1, s2, ng, g0);
}

/// With no page held or parked and every free page in a free group among the first `ng`, the pages
/// available in the first `m` groups are the pages of the free ones.
proof fn lemma_avail_only_free_groups_aligned(state: Seq<u8>, ng: int, m: int)
    requires
        0 <= m <= ng,
        ng * TABLE_PAGES <= state.len(),
        forall|u: int| 0 <= u < ng * TABLE_PAGES ==> #[trigger] state[u] != HELD && state[u] != PARKED,
        forall|u: int| 0 <= u < ng * TABLE_PAGES && #[trigger] state[u] == FREE ==> in_free_group(state, ng, u),
    ensures
        avail_upto(state, m * TABLE_PAGES) == free_groups_upto(state, m) * TABLE_PAGES as nat,
    decreases m,
{
    if m > 0 {
        lemma_avail_only_free_groups_aligned(state, ng, m - 1);
        let b = (m - 1) * TABLE_PAGES as int;
        assert(b >= 0 && m * TABLE_PAGES as int == b + 8 && b + 8 <= ng * TABLE_PAGES as int) by (nonlinear_arith)
            requires
                1 <= m <= ng,
                b == (m - 1) * (TABLE_PAGES as int),
                TABLE_PAGES == 8,
        ;
        if group_free_in(state, m - 1) {
            assert(avail_upto(state, b + 1) == avail_upto(state, b) + 1);
            assert(avail_upto(state, b + 2) == avail_upto(state, b) + 2);
            assert(avail_upto(state, b + 3) == avail_upto(state, b) + 3);
            assert(avail_upto(state, b + 4) == avail_upto(state, b) + 4);
            assert(avail_upto(state, b + 5) == avail_upto(state, b) + 5);
            assert(avail_upto(state, b + 6) == avail_upto(state, b) + 6);
            assert(avail_upto(state, b + 7) == avail_upto(state, b) + 7);
            assert(avail_upto(state, b + 8) == avail_upto(state, b) + 8);
            assert((free_groups_upto(state, m - 1) + 1) * (TABLE_PAGES as nat)
                == free_groups_upto(state, m - 1) * (TABLE_PAGES as nat) + 8) by (nonlinear_arith)
                requires
                    TABLE_PAGES == 8,
            ;
        } else {
            assert forall|u: int| b <= u < b + 8 implies !page_avail(#[trigger] state[u]) by {
                let k = u - b;
                assert((TABLE_PAGES as int) * (m - 1) + k == u) by (nonlinear_arith)
                    requires
                        b == (m - 1) * (TABLE_PAGES as int),
                        k == u - b,
                ;
                lemma_div_multiples_vanish_fancy(m - 1, k, TABLE_PAGES as int);
                assert(u / TABLE_PAGES as int == m - 1);
                assert(state[u] != HELD && state[u] != PARKED);
                if state[u] == FREE {
                    lemma_in_free_group(state, ng, u);
                    assert(group_free_in(state, m - 1));
                }
            }
            lemma_avail_tail_zero(state, b, b + 8);
        }
    }
}

/// With no page held or parked and every free page in a free group, the pages available are the
/// pages of the free groups.
proof fn lemma_avail_only_free_groups(state: Seq<u8>, pages: int, ng: int)
    requires
        0 <= pages <= state.len(),
        ng == pages / TABLE_PAGES as int,
        forall|u: int| 0 <= u < pages ==> #[trigger] state[u] != HELD && state[u] != PARKED,
        forall|u: int| 0 <= u < pages && #[trigger] state[u] == FREE ==> in_free_group(state, ng, u),
    ensures
        avail_upto(state, pages) == free_groups_upto(state, ng) * TABLE_PAGES as nat,
{
    let tp = TABLE_PAGES as int;
    lemma_div_pos_is_pos(pages, tp);
    lemma_fundamental_div_mod(pages, tp);
    lemma_mod_bound(pages, tp);
    let b = ng * tp;
    assert(b == tp * ng) by (nonlinear_arith)
        requires
            b == ng * tp,
    ;
    assert(b <= pages);
    assert forall|u: int| b <= u < pages implies !page_avail(#[trigger] state[u]) by {
        let k = u - b;
        assert(tp * ng + k == u) by (nonlinear_arith)
            requires
                b == tp * ng,
                k == u - b,
        ;
        assert(k < tp) by (nonlinear_arith)
            requires
                pages == tp * ng + pages % tp,
                pages % tp < tp,
                b == tp * ng,
                u < pages,
                k == u - b,
        ;
        lemma_div_multiples_vanish_fancy(ng, k, tp);
        assert(u / tp == ng);
        assert(state[u] != HELD && state[u] != PARKED);
        if state[u] == FREE {
            lemma_in_free_group(state, ng, u);
        }
    }
    lemma_avail_tail_zero(state, b, pages);
    lemma_avail_only_free_groups_aligned(state, ng, ng);
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
}

/// How `Record::frame` changes `free_groups()` when it returns a held frame: either no free group is
/// broken, or there were more free groups than unlinked window tables, or every available page belonged
/// to a free group.
spec fn frame_group_step(before: Record, after: Record) -> bool {
    ||| after.free_groups() == before.free_groups()
    ||| (before.free_groups() as int > before.tables_unlinked() && after.free_groups() + 1 >= before.free_groups())
    ||| (before.avail_pages() == before.free_groups() * TABLE_PAGES as nat
        && after.free_groups() + 1 >= before.free_groups())
}

/// What a back of `pages` pages that was refused spent, from `before` to `after`: the tables it
/// linked, a `TABLE_PAGES` block each, and, when `acall` refused a step, at most one block more, which
/// a refused table call spends, or one frame, which a refused retype or unmap spends; a refused map
/// keeps its frame held, and the pages backed before the refusal are parked. Each page's frame breaks
/// at most one free block more.
spec fn refused_spent(before: Record, after: Record, steps: Seq<AcallStep>, pages: nat) -> bool {
    let linked = before.tables_unlinked() - after.tables_unlinked();
    &&& 0 <= linked
    &&& after.free_groups() as int + linked <= before.free_groups() as int
    &&& before.free_groups() as int <= after.free_groups() as int + linked + pages
    &&& acall_ok(steps) ==> after.avail_pages() as int + linked * TABLE_PAGES as int == before.avail_pages() as int
    &&& after.avail_pages() as int + linked * TABLE_PAGES as int <= before.avail_pages() as int
    &&& before.avail_pages() as int <= after.avail_pages() as int + (linked + 1) * TABLE_PAGES as int
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

    spec fn addr_block(&self, addr: usize) -> int {
        (addr - self.window) as int / BLOCK_BYTES as int
    }

    spec fn inv(&self) -> bool {
        &&& self.pages <= MAX_PAGES
        &&& self.memory + self.pages * PAGE_BYTES <= u64::MAX
        &&& self.slots < TABLE_INDICES
        &&& self.slots as int % LEAF_INDICES as int != 0
        &&& slots_ok(self.slots, self.pages)
        &&& self.window as int % BLOCK_BYTES as int == 0
        &&& self.window + WINDOW_BYTES <= usize::MAX
        &&& forall|i: int| 0 <= i < self.pages && occupied(#[trigger] self.state@[i]) ==> {
            &&& self.window <= self.owner@[i] < self.window + WINDOW_BYTES
            &&& self.owner@[i] as int % PAGE_BYTES as int == 0
            &&& 0 <= self.addr_block(self.owner@[i]) < WINDOW_BLOCKS
            &&& self.top
            &&& self.middle
            &&& self.tabled@[self.addr_block(self.owner@[i])]
        }
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

    spec fn avail_pages(&self) -> nat {
        avail_upto(self.state@, self.pages as int)
    }

    spec fn free_groups(&self) -> nat {
        free_groups_upto(self.state@, (self.pages / TABLE_PAGES) as int)
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

    spec fn missing_tables(&self) -> int {
        if self.free_groups() as int >= self.tables_unlinked() {
            0
        } else {
            self.tables_unlinked() - self.free_groups() as int
        }
    }

    spec fn free_capacity(&self) -> int {
        self.avail_pages() as int
            - self.tables_unlinked() * TABLE_PAGES as int
            - self.missing_tables() * MAX_PAGES as int
    }

    spec fn tables_for_addr(&self, addr: usize) -> nat {
        (if self.top { 0nat } else { 1nat })
            + (if self.middle { 0nat } else { 1nat })
            + (if self.tabled@[self.addr_block(addr)] { 0nat } else { 1nat })
    }

    spec fn blocks_for_run(&self, start: int, pages: nat) -> nat {
        (if !self.tabled@[0] && run_touches_block(self.window, start, pages, 0) { 1nat } else { 0nat })
            + (if !self.tabled@[1] && run_touches_block(self.window, start, pages, 1) { 1nat } else { 0nat })
            + (if !self.tabled@[2] && run_touches_block(self.window, start, pages, 2) { 1nat } else { 0nat })
            + (if !self.tabled@[3] && run_touches_block(self.window, start, pages, 3) { 1nat } else { 0nat })
    }

    spec fn tables_for_run(&self, start: int, pages: nat) -> nat {
        if pages == 0 {
            0
        } else {
            (if self.top { 0nat } else { 1nat })
                + (if self.middle { 0nat } else { 1nat })
                + self.blocks_for_run(start, pages)
        }
    }

    spec fn can_back_run(&self, start: int, pages: nat) -> bool {
        &&& self.free_groups() >= self.tables_for_run(start, pages)
        &&& self.avail_pages() as int - self.tables_for_run(start, pages) as int * TABLE_PAGES as int >= pages as int
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

    fn is_free_group(&self, g: usize) -> (r: bool)
        requires
            self.inv(),
            g < self.pages / TABLE_PAGES,
        ensures
            (g + 1) * TABLE_PAGES <= self.pages,
            r == group_free_in(self.state@, g as int),
        no_unwind
    {
        proof {
            let ng = (self.pages / TABLE_PAGES) as int;
            lemma_fundamental_div_mod(self.pages as int, TABLE_PAGES as int);
            lemma_mod_bound(self.pages as int, TABLE_PAGES as int);
            assert((g + 1) * TABLE_PAGES <= self.pages) by (nonlinear_arith)
                requires
                    (g as int) < ng,
                    self.pages as int == (TABLE_PAGES as int) * ng + self.pages as int % (TABLE_PAGES as int),
                    self.pages as int % (TABLE_PAGES as int) >= 0,
                    TABLE_PAGES == 8,
            ;
        }
        let base = g * TABLE_PAGES;
        self.state[base] == FREE
            && self.state[base + 1] == FREE
            && self.state[base + 2] == FREE
            && self.state[base + 3] == FREE
            && self.state[base + 4] == FREE
            && self.state[base + 5] == FREE
            && self.state[base + 6] == FREE
            && self.state[base + 7] == FREE
    }

    fn count_free_groups(&self) -> (r: usize)
        requires
            self.inv(),
        ensures
            r as nat == self.free_groups(),
        no_unwind
    {
        let ng = self.pages / TABLE_PAGES;
        let mut g: usize = 0;
        let mut count: usize = 0;
        while g < ng
            invariant
                self.inv(),
                ng == self.pages / TABLE_PAGES,
                g <= ng,
                count <= g,
                count as nat == free_groups_upto(self.state@, g as int),
            decreases ng - g,
        {
            if self.is_free_group(g) {
                count += 1;
            }
            g += 1;
        }
        count
    }

    fn count_tables_unlinked(&self) -> (r: usize)
        ensures
            r as int == self.tables_unlinked(),
        no_unwind
    {
        (if self.top { 0 } else { 1 })
            + (if self.middle { 0 } else { 1 })
            + (if self.tabled[0] { 0 } else { 1 })
            + (if self.tabled[1] { 0 } else { 1 })
            + (if self.tabled[2] { 0 } else { 1 })
            + (if self.tabled[3] { 0 } else { 1 })
    }

    /// Retypes free page `i` as a frame into its slot.
    fn retype_free(&mut self, caller: &mut Tracked<Caller>, i: usize) -> (r: (Option<usize>, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            i < old(self).pages,
            old(self).state@[i as int] == FREE,
        ensures
            final(self).same_config(old(self)),
            final(self).top == old(self).top,
            final(self).middle == old(self).middle,
            final(self).tabled == old(self).tabled,
            final(self).owner == old(self).owner,
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps(old(self)),
            final(self).keeps_mapped(old(self)),
            forall|u: int| 0 <= u < MAX_PAGES && u != i as int ==> #[trigger] final(self).state@[u] == old(self).state@[u],
            acall_steps(old(caller)@, final(caller)@, r.1@),
            step_seq_well_ended(r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_setup_call(
                (#[trigger] r.1@[k]).call,
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
            ),
            match r.0 {
                Some(idx) => {
                    &&& idx == i
                    &&& final(self).state@[i as int] == HELD
                    &&& final(self).avail_pages() == old(self).avail_pages()
                    &&& acall_ok(r.1@)
                },
                None => {
                    &&& final(self).state@[i as int] == TAKEN
                    &&& final(self).avail_pages() + 1 == old(self).avail_pages()
                    &&& !acall_ok(r.1@)
                },
            },
        no_unwind
    {
        hide(CapKernel::wf);
        let base = self.page(i);
        let slot = self.slot(i);
        let ghost before = *self;
        proof {
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
            if retyped {
                assert(STATUS_REFUSED != STATUS_OK);
            } else {
                assert(steps.drop_last() =~= Seq::<AcallStep>::empty());
            }
        }
        if retyped {
            self.state[i] = HELD;
            proof {
                assert(self.frames() =~= before.frames().insert(i as int, (slot as usize, None)));
                lemma_avail_update(before.state@, self.state@, self.pages as int, i as int);
            }
            return (Some(i), Ghost(steps));
        }
        self.state[i] = TAKEN;
        assert(self.frames() =~= before.frames());
        proof {
            lemma_avail_update(before.state@, self.state@, self.pages as int, i as int);
        }
        (None, Ghost(steps))
    }

    /// A frame the source holds, mapped nowhere: one held before, else a loose free page or one from a
    /// free group beyond the unlinked window tables retyped as a frame, else a parked page unmapped,
    /// else a free page from a remaining group retyped. None when no page is available or the kernel
    /// refused the retype or the unmap.
    fn frame(&mut self, caller: &mut Tracked<Caller>) -> (r: (Option<usize>, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
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
            step_seq_well_ended(r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_setup_call(
                (#[trigger] r.1@[k]).call,
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
            ),
            match r.0 {
                Some(i) => {
                    &&& i < final(self).pages
                    &&& final(self).state@[i as int] == HELD
                    &&& acall_ok(r.1@)
                    &&& old(self).avail_pages() >= 1
                    &&& final(self).avail_pages() == old(self).avail_pages()
                    &&& final(self).free_groups() <= old(self).free_groups()
                    &&& frame_group_step(*old(self), *final(self))
                },
                None => {
                    ||| {
                        &&& old(self).avail_pages() == 0
                        &&& *final(self) == *old(self)
                        &&& final(caller)@ == old(caller)@
                        &&& r.1@ == Seq::<AcallStep>::empty()
                    }
                    ||| {
                        &&& old(self).avail_pages() >= 1
                        &&& !acall_ok(r.1@)
                        &&& final(self).avail_pages() + 1 == old(self).avail_pages()
                        &&& final(self).free_groups() <= old(self).free_groups()
                        &&& old(self).free_groups() <= final(self).free_groups() + 1
                    }
                },
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
                    lemma_avail_at_least_one(self.state@, self.pages as int, i as int);
                }
                return (Some(i), Ghost(Seq::empty()));
            }
            i += 1;
        }
        let ng = self.pages / TABLE_PAGES;
        proof {
            lemma_fundamental_div_mod(self.pages as int, TABLE_PAGES as int);
            lemma_mod_bound(self.pages as int, TABLE_PAGES as int);
            assert((ng as int) * TABLE_PAGES <= self.pages) by (nonlinear_arith)
                requires
                    self.pages as int == (TABLE_PAGES as int) * (ng as int) + self.pages as int % (TABLE_PAGES as int),
                    self.pages as int % (TABLE_PAGES as int) >= 0,
                    TABLE_PAGES == 8,
            ;
        }
        let mut i = self.pages;
        while i > 0
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                ng == self.pages / TABLE_PAGES,
                (ng as int) * TABLE_PAGES <= self.pages,
                i <= self.pages,
                forall|u: int| 0 <= u < self.pages ==> #[trigger] self.state@[u] != HELD,
                forall|u: int|
                    i <= u < self.pages && #[trigger] self.state@[u] == FREE ==> in_free_group(self.state@, ng as int, u),
            decreases i,
        {
            i -= 1;
            let g = i / TABLE_PAGES;
            if self.state[i] == FREE && (g >= ng || !self.is_free_group(g)) {
                proof {
                    lemma_avail_at_least_one(self.state@, self.pages as int, i as int);
                }
                let res = self.retype_free(caller, i);
                proof {
                    lemma_free_groups_loose_change(old(self).state@, self.state@, ng as int, i as int);
                }
                return res;
            }
            proof {
                lemma_in_free_group(self.state@, ng as int, i as int);
            }
        }
        if self.count_free_groups() > self.count_tables_unlinked() {
            let mut i = self.pages;
            while i > 0
                invariant
                    *self == *old(self),
                    caller@ == old(caller)@,
                    self.inv(),
                    self.serves(caller@),
                    ng == self.pages / TABLE_PAGES,
                    (ng as int) * TABLE_PAGES <= self.pages,
                    i <= self.pages,
                    self.free_groups() as int > self.tables_unlinked(),
                    forall|u: int|
                        0 <= u < self.pages && #[trigger] self.state@[u] == FREE ==> in_free_group(self.state@, ng as int, u),
                    forall|u: int| i <= u < self.pages ==> #[trigger] self.state@[u] != FREE,
                decreases i,
            {
                i -= 1;
                if self.state[i] == FREE {
                    proof {
                        lemma_avail_at_least_one(self.state@, self.pages as int, i as int);
                        assert(self.state@[i as int] == FREE);
                        lemma_in_free_group(self.state@, ng as int, i as int);
                    }
                    let res = self.retype_free(caller, i);
                    proof {
                        lemma_free_groups_break_one(old(self).state@, self.state@, ng as int, i as int);
                    }
                    return res;
                }
            }
            proof {
                assert(self.tables_unlinked() >= 0);
                let g0 = lemma_free_groups_has_witness(self.state@, ng as int);
                let base = g0 * TABLE_PAGES as int;
                assert(0 <= base < self.pages as int) by (nonlinear_arith)
                    requires
                        0 <= g0 < ng as int,
                        (ng as int) * (TABLE_PAGES as int) <= self.pages as int,
                        base == g0 * (TABLE_PAGES as int),
                        TABLE_PAGES == 8,
                ;
                assert(self.state@[base] == FREE);
                assert(false);
            }
        }
        let mut i: usize = 0;
        while i < self.pages
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                ng == self.pages / TABLE_PAGES,
                (ng as int) * TABLE_PAGES <= self.pages,
                i <= self.pages,
                forall|u: int| 0 <= u < self.pages ==> #[trigger] self.state@[u] != HELD,
                forall|u: int|
                    0 <= u < self.pages && #[trigger] self.state@[u] == FREE ==> in_free_group(self.state@, ng as int, u),
                forall|u: int| 0 <= u < i ==> #[trigger] self.state@[u] != PARKED,
            decreases self.pages - i,
        {
            if self.state[i] == PARKED {
                assert(self.state@[i as int] == PARKED);
                proof {
                    lemma_avail_at_least_one(self.state@, self.pages as int, i as int);
                }
                let ghost before = *self;
                let tracked perm = self.parked.borrow_mut().tracked_remove(i as int);
                assert(self.frames() =~= before.frames());
                let (unmapped, Ghost(s)) = unmap_page(caller, self.space, self.owner[i], Tracked(perm), Ghost(before.frames()), Ghost(i as int));
                let ghost steps = seq![s];
                proof {
                    assert(occupied(before.state@[i as int]));
                    assert((self.owner@[i as int] as u64) as int == before.owner@[i as int] as int);
                    assert(acall_setup_call(s.call, self.space, self.untyped, self.memory, self.pages, self.slots, self.window)) by {
                        reveal(acall_setup_call);
                    }
                    assert(steps[0] == s && steps.last() == s);
                    if unmapped {
                        assert(STATUS_REFUSED != STATUS_OK);
                    } else {
                        assert(steps.drop_last() =~= Seq::<AcallStep>::empty());
                    }
                }
                if unmapped {
                    self.state[i] = HELD;
                    proof {
                        assert(self.frames() =~= before.frames().insert(i as int, (before.frames()[i as int].0, None)));
                        lemma_avail_update(before.state@, self.state@, self.pages as int, i as int);
                        lemma_free_groups_nonfree_change(before.state@, self.state@, ng as int, i as int);
                    }
                    return (Some(i), Ghost(steps));
                }
                self.state[i] = TAKEN;
                assert(self.frames() =~= before.frames().remove(i as int));
                proof {
                    lemma_avail_update(before.state@, self.state@, self.pages as int, i as int);
                    lemma_free_groups_nonfree_change(before.state@, self.state@, ng as int, i as int);
                }
                return (None, Ghost(steps));
            }
            i += 1;
        }
        proof {
            assert forall|u: int| 0 <= u < self.pages implies #[trigger] self.state@[u] != HELD && self.state@[u] != PARKED by {}
            lemma_avail_only_free_groups(self.state@, self.pages as int, ng as int);
        }
        let mut i = self.pages;
        while i > 0
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                ng == self.pages / TABLE_PAGES,
                (ng as int) * TABLE_PAGES <= self.pages,
                i <= self.pages,
                self.avail_pages() == self.free_groups() * TABLE_PAGES as nat,
                forall|u: int| 0 <= u < self.pages ==> #[trigger] self.state@[u] != HELD && self.state@[u] != PARKED,
                forall|u: int|
                    0 <= u < self.pages && #[trigger] self.state@[u] == FREE ==> in_free_group(self.state@, ng as int, u),
                forall|u: int| i <= u < self.pages ==> #[trigger] self.state@[u] != FREE,
            decreases i,
        {
            i -= 1;
            if self.state[i] == FREE {
                proof {
                    lemma_avail_at_least_one(self.state@, self.pages as int, i as int);
                    assert(self.state@[i as int] == FREE);
                    lemma_in_free_group(self.state@, ng as int, i as int);
                }
                let res = self.retype_free(caller, i);
                proof {
                    lemma_free_groups_break_one(old(self).state@, self.state@, ng as int, i as int);
                }
                return res;
            }
        }
        proof {
            lemma_acall_steps_none(caller@);
            assert forall|u: int| 0 <= u < self.pages implies !page_avail(#[trigger] self.state@[u]) by {
                assert(self.state@[u] != HELD && self.state@[u] != PARKED && self.state@[u] != FREE);
            }
            lemma_avail_none(self.state@, self.pages as int);
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
            step_seq_well_ended(r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_setup_call(
                (#[trigger] r.1@[k]).call,
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
            ),
            r.0 ==> {
                &&& acall_ok(r.1@)
                &&& old(self).free_groups() >= 1
                &&& final(self).free_groups() + 1 == old(self).free_groups()
                &&& final(self).avail_pages() + TABLE_PAGES as nat == old(self).avail_pages()
            },
            !r.0 ==> {
                ||| {
                    &&& old(self).free_groups() == 0
                    &&& *final(self) == *old(self)
                    &&& final(caller)@ == old(caller)@
                    &&& r.1@ == Seq::<AcallStep>::empty()
                }
                ||| {
                    &&& old(self).free_groups() >= 1
                    &&& !acall_ok(r.1@)
                    &&& final(self).free_groups() + 1 == old(self).free_groups()
                    &&& final(self).avail_pages() + TABLE_PAGES as nat == old(self).avail_pages()
                }
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let ng = self.pages / TABLE_PAGES;
        let mut g: usize = 0;
        while g < ng
            invariant
                *self == *old(self),
                caller@ == old(caller)@,
                self.inv(),
                self.serves(caller@),
                ng == self.pages / TABLE_PAGES,
                g <= ng,
                2 <= level <= 4,
                (level == 4 && address == old(self).window)
                    || (level == 3 && address == old(self).window)
                    || (level == 2 && exists|b: int| 0 <= b < WINDOW_BLOCKS && address as int == #[trigger] window_block(old(self).window, b)),
                forall|u: int| 0 <= u < g ==> !#[trigger] group_free_in(self.state@, u),
            decreases ng - g,
        {
            if self.is_free_group(g) {
                let group = g * TABLE_PAGES;
                proof {
                    lemma_fundamental_div_mod(self.pages as int, TABLE_PAGES as int);
                    lemma_mod_bound(self.pages as int, TABLE_PAGES as int);
                    assert((ng as int) * TABLE_PAGES <= self.pages) by (nonlinear_arith)
                        requires
                            self.pages as int == (TABLE_PAGES as int) * (ng as int) + self.pages as int % (TABLE_PAGES as int),
                            self.pages as int % (TABLE_PAGES as int) >= 0,
                            TABLE_PAGES == 8,
                    ;
                    lemma_free_groups_at_least_one(old(self).state@, ng as int, g as int);
                    lemma_mod_multiples_basic(g as int, TABLE_PAGES as int);
                }
                let mut k: usize = 0;
                while k < TABLE_PAGES
                    invariant
                        self.same_config(old(self)),
                        self.top == old(self).top,
                        self.middle == old(self).middle,
                        self.tabled == old(self).tabled,
                        self.owner == old(self).owner,
                        self.inv(),
                        self.serves(caller@),
                        caller@ == old(caller)@,
                        ng == self.pages / TABLE_PAGES,
                        g < ng,
                        group == g * TABLE_PAGES,
                        group + TABLE_PAGES <= self.pages,
                        group as int % TABLE_PAGES as int == 0,
                        (ng as int) * TABLE_PAGES <= self.pages,
                        k <= TABLE_PAGES,
                        2 <= level <= 4,
                        self.keeps(old(self)),
                        self.keeps_mapped(old(self)),
                        self.avail_pages() + k as nat == old(self).avail_pages(),
                        k > 0 ==> self.state@[group as int] == TAKEN,
                        forall|u: int|
                            0 <= u < MAX_PAGES && !(group <= u < group + k)
                                ==> #[trigger] self.state@[u] == old(self).state@[u],
                        group_free_in(old(self).state@, g as int),
                    decreases TABLE_PAGES - k,
                {
                    proof {
                        let base = g as int * TABLE_PAGES as int;
                        assert(group as int == base);
                        if k == 0 {
                            assert(old(self).state@[base] == FREE);
                        } else if k == 1 {
                            assert(old(self).state@[base + 1] == FREE);
                        } else if k == 2 {
                            assert(old(self).state@[base + 2] == FREE);
                        } else if k == 3 {
                            assert(old(self).state@[base + 3] == FREE);
                        } else if k == 4 {
                            assert(old(self).state@[base + 4] == FREE);
                        } else if k == 5 {
                            assert(old(self).state@[base + 5] == FREE);
                        } else if k == 6 {
                            assert(old(self).state@[base + 6] == FREE);
                        } else {
                            assert(old(self).state@[base + 7] == FREE);
                        }
                        assert(self.state@[(group + k) as int] == FREE);
                    }
                    let ghost before = *self;
                    self.state[group + k] = TAKEN;
                    proof {
                        assert(self.frames() =~= before.frames());
                        lemma_avail_update(before.state@, self.state@, self.pages as int, (group + k) as int);
                    }
                    k += 1;
                }
                proof {
                    assert(!group_free_in(self.state@, g as int));
                    assert forall|j: int|
                        0 <= j < (ng as int) * TABLE_PAGES && !(g * TABLE_PAGES <= j < (g + 1) * TABLE_PAGES)
                        implies #[trigger] self.state@[j] == old(self).state@[j] by {
                        assert((g + 1) * TABLE_PAGES == group + TABLE_PAGES) by (nonlinear_arith)
                            requires
                                group == g * TABLE_PAGES,
                        ;
                    }
                    lemma_free_groups_update_one(old(self).state@, self.state@, ng as int, g as int);
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
                    assert(seq![s1][0] == s1);
                    if linked {
                        lemma_acall_ok_append(seq![s1], seq![s2]);
                        if steps.len() > 0 && steps.last().out.status == STATUS_REFUSED {
                            assert(steps[steps.len() - 1].out.status == STATUS_OK);
                            assert(STATUS_REFUSED != STATUS_OK);
                        }
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
            g += 1;
        }
        proof {
            lemma_acall_steps_none(caller@);
            lemma_fundamental_div_mod(self.pages as int, TABLE_PAGES as int);
            lemma_mod_bound(self.pages as int, TABLE_PAGES as int);
            assert((ng as int) * TABLE_PAGES <= self.pages) by (nonlinear_arith)
                requires
                    self.pages as int == (TABLE_PAGES as int) * (ng as int) + self.pages as int % (TABLE_PAGES as int),
                    self.pages as int % (TABLE_PAGES as int) >= 0,
                    TABLE_PAGES == 8,
            ;
            lemma_free_groups_none(self.state@, ng as int);
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
            old(self).window <= addr < old(self).window + WINDOW_BYTES,
            addr as int % PAGE_BYTES as int == 0,
            !old(self).maps(addr as int),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps_mapped(old(self)),
            forall|a: int| #[trigger] final(self).parks(a) ==> old(self).parks(a),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            step_seq_well_ended(r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_call_in_window(
                #[trigger] r.1@[k],
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
                addr as int,
                1,
            ),
            match r.0 {
                Some(perm) => {
                    &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                    &&& perm@.provenance() == provenance@
                    &&& final(self).maps(addr as int)
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> a == addr || old(self).maps(a)
                    &&& !final(self).parks(addr as int)
                    &&& acall_ok(r.1@)
                    &&& old(self).can_back_run(addr as int, 1)
                    &&& final(self).top && final(self).middle && final(self).tabled@[old(self).addr_block(addr)]
                    &&& forall|c: int|
                        0 <= c < WINDOW_BLOCKS && c != old(self).addr_block(addr)
                            ==> #[trigger] final(self).tabled@[c] == old(self).tabled@[c]
                    &&& final(self).free_groups() + old(self).tables_for_addr(addr) <= old(self).free_groups()
                    &&& old(self).free_groups() <= final(self).free_groups() + old(self).tables_for_addr(addr) + 1
                    &&& final(self).tables_unlinked() + old(self).tables_for_addr(addr) as int == old(self).tables_unlinked()
                    &&& final(self).avail_pages() + old(self).tables_for_addr(addr) * TABLE_PAGES as nat + 1
                        == old(self).avail_pages()
                    &&& old(self).free_capacity() >= 1 ==> final(self).free_capacity() == old(self).free_capacity() - 1
                    &&& forall|rem: nat|
                        rem >= 1 && #[trigger] old(self).can_back_run(addr as int, rem)
                            ==> final(self).can_back_run(addr + PAGE_BYTES as int, (rem - 1) as nat)
                },
                None => {
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a)
                    &&& (!old(self).can_back_run(addr as int, 1) || !acall_ok(r.1@))
                    &&& refused_spent(*old(self), *final(self), r.1@, 1)
                },
            },
            old(self).top ==> final(self).top,
            old(self).middle ==> final(self).middle,
            forall|c: int| 0 <= c < WINDOW_BLOCKS ==> (old(self).tabled@[c] ==> #[trigger] final(self).tabled@[c]),
            forall|c: int|
                0 <= c < WINDOW_BLOCKS && c != old(self).addr_block(addr)
                    ==> #[trigger] final(self).tabled@[c] == old(self).tabled@[c],
            old(self).parks(addr as int) ==> {
                &&& r.0 is Some
                &&& r.1@ == Seq::<AcallStep>::empty()
                &&& final(caller)@ == old(caller)@
                &&& final(self).free_capacity() == old(self).free_capacity() - 1
                &&& forall|b: int| b != addr && #[trigger] old(self).parks(b) ==> final(self).parks(b)
            },
            (old(self).tables_for_addr(addr) == 0 && old(self).avail_pages() == 0) ==> {
                &&& r.0 is None
                &&& *final(self) == *old(self)
                &&& final(caller)@ == old(caller)@
                &&& r.1@ == Seq::<AcallStep>::empty()
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
                assert(false);
            }
            return (None, Ghost(Seq::empty()));
        }
        assert(self.state@[i as int] == PARKED && self.owner@[i as int] == addr);
        let ghost before = *self;
        let tracked perm = self.parked.borrow_mut().tracked_remove(i as int);
        self.state[i] = MAPPED;
        proof {
            assert(occupied(before.state@[i as int]));
            assert(before.top && before.middle && before.tabled@[before.addr_block(addr)]);
            assert(before.tables_for_addr(addr) == 0);
            assert(self.frames() =~= before.frames());
            assert(self.state@[i as int] == MAPPED);
            lemma_avail_at_least_one(before.state@, self.pages as int, i as int);
            lemma_avail_update(before.state@, self.state@, self.pages as int, i as int);
            let ng = (self.pages / TABLE_PAGES) as int;
            lemma_fundamental_div_mod(self.pages as int, TABLE_PAGES as int);
            lemma_mod_bound(self.pages as int, TABLE_PAGES as int);
            assert(ng * TABLE_PAGES <= self.pages) by (nonlinear_arith)
                requires
                    self.pages as int == (TABLE_PAGES as int) * ng + self.pages as int % (TABLE_PAGES as int),
                    self.pages as int % (TABLE_PAGES as int) >= 0,
                    TABLE_PAGES == 8,
            ;
            lemma_free_groups_nonfree_change(before.state@, self.state@, ng, i as int);
            assert forall|a: int| #[trigger] self.maps(a) implies a == addr || before.maps(a) by {
                if a != addr {
                    let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == MAPPED && self.owner@[j] == a;
                    assert(j != i);
                    assert(before.state@[j] == MAPPED);
                }
            }
            if self.parks(addr as int) {
                let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == addr;
                assert(j != i);
                assert(occupied(before.state@[j]));
                assert(before.owner@[j] != before.owner@[i as int]);
            }
            assert forall|a: int| #[trigger] self.parks(a) implies before.parks(a) by {
                let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == a;
                assert(j != i);
                assert(before.state@[j] == PARKED && before.owner@[j] == a);
            }
            assert forall|b: int| b != addr && #[trigger] before.parks(b) implies self.parks(b) by {
                let j = choose|j: int| 0 <= j < before.pages && #[trigger] before.state@[j] == PARKED && before.owner@[j] == b;
                assert(self.state@[j] == PARKED);
            }
            lemma_tables_for_run_step(before, *self, addr, 1);
            assert(self.tables_for_run(addr + PAGE_BYTES as int, 0) == 0);
            assert(before.tables_for_run(addr as int, 1) == 0);
            assert forall|rem: nat|
                rem >= 1 && #[trigger] before.can_back_run(addr as int, rem)
                implies self.can_back_run(addr + PAGE_BYTES as int, (rem - 1) as nat) by {
                lemma_tables_for_run_step(before, *self, addr, rem);
            }
        }
        (Some(Tracked(perm)), Ghost(Seq::empty()))
    }

    /// Links the tables the path to `addr` lacks, at each level the record has not linked yet; false
    /// when no free table block remains or a link was refused. Every occupied page keeps its state and
    /// address.
    fn path_tables(&mut self, caller: &mut Tracked<Caller>, addr: usize) -> (r: (bool, Ghost<Seq<AcallStep>>))
        requires
            old(self).inv(),
            old(self).serves(old(caller)@),
            old(self).window <= addr < old(self).window + WINDOW_BYTES,
            addr as int % PAGE_BYTES as int == 0,
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps(old(self)),
            final(self).keeps_mapped(old(self)),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            step_seq_well_ended(r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_setup_call(
                (#[trigger] r.1@[k]).call,
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
            ),
            r.0 ==> {
                &&& acall_ok(r.1@)
                &&& old(self).free_groups() >= old(self).tables_for_addr(addr)
                &&& final(self).free_groups() + old(self).tables_for_addr(addr) == old(self).free_groups()
                &&& final(self).avail_pages() + old(self).tables_for_addr(addr) * TABLE_PAGES as nat
                    == old(self).avail_pages()
                &&& final(self).tables_unlinked() + old(self).tables_for_addr(addr) as int
                    == old(self).tables_unlinked()
                &&& final(self).top && final(self).middle && final(self).tabled@[old(self).addr_block(addr)]
                &&& forall|c: int|
                    0 <= c < WINDOW_BLOCKS && c != old(self).addr_block(addr)
                        ==> #[trigger] final(self).tabled@[c] == old(self).tabled@[c]
            },
            !r.0 ==> (old(self).free_groups() < old(self).tables_for_addr(addr) || !acall_ok(r.1@)),
            old(self).top ==> final(self).top,
            old(self).middle ==> final(self).middle,
            forall|c: int| 0 <= c < WINDOW_BLOCKS ==> (old(self).tabled@[c] ==> #[trigger] final(self).tabled@[c]),
            forall|c: int|
                0 <= c < WINDOW_BLOCKS && c != old(self).addr_block(addr)
                    ==> #[trigger] final(self).tabled@[c] == old(self).tabled@[c],
            // A path stopped part way keeps the tables it linked; a refused table call spent its block too.
            !r.0 ==> ({
                let linked = old(self).tables_unlinked() - final(self).tables_unlinked();
                let spent = if acall_ok(r.1@) { linked } else { linked + 1 };
                &&& 0 <= linked
                &&& final(self).free_groups() as int + spent == old(self).free_groups() as int
                &&& final(self).avail_pages() as int + spent * TABLE_PAGES as int == old(self).avail_pages() as int
            }),
            old(self).tables_for_addr(addr) == 0 ==> {
                &&& r.0
                &&& *final(self) == *old(self)
                &&& final(caller)@ == old(caller)@
                &&& r.1@ == Seq::<AcallStep>::empty()
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let ghost start = *self;
        let ghost c0 = caller@;
        let ghost mut steps = Seq::<AcallStep>::empty();
        let window = self.window;
        proof {
            lemma_acall_steps_none(c0);
            lemma_addr_block(window, addr);
        }
        let block = (addr - window) / BLOCK_BYTES;
        let ghost n_top: nat = if start.top { 0 } else { 1 };
        let ghost n_mid: nat = if start.middle { 0 } else { 1 };
        let ghost n_blk: nat = if start.tabled@[block as int] { 0 } else { 1 };
        proof {
            assert(block as int == start.addr_block(addr));
            assert(start.tables_for_addr(addr) == n_top + n_mid + n_blk);
        }
        if !self.top {
            let ghost before = *self;
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
            }
        }
        proof {
            assert(self.top);
            assert(self.middle == start.middle && self.tabled == start.tabled);
            assert(start.free_groups() >= n_top);
            assert(self.free_groups() + n_top == start.free_groups());
            assert(self.avail_pages() + n_top * TABLE_PAGES as nat == start.avail_pages());
            assert(self.tables_unlinked() + n_top as int == start.tables_unlinked());
            assert(acall_ok(steps) && step_seq_well_ended(steps));
        }
        if !self.middle {
            let ghost before = *self;
            let ghost cmid = caller@;
            let ghost prev = steps;
            let (linked, Ghost(s)) = self.table(caller, window, 3);
            proof {
                lemma_mapped_trans(*self, before, start);
                lemma_keeps_trans(*self, before, start);
                lemma_acall_steps_append(c0, cmid, caller@, prev, s);
                lemma_well_ended_append(prev, s);
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
                    lemma_acall_ok_append(prev, s);
                }
                return (false, Ghost(steps));
            }
            let ghost after_table = *self;
            self.middle = true;
            proof {
                lemma_acall_ok_append(prev, s);
                assert(self.frames() =~= after_table.frames());
                assert(self.tables_unlinked() == before.tables_unlinked() - 1);
            }
        }
        proof {
            assert(self.top && self.middle);
            assert(self.tabled == start.tabled);
            assert(start.free_groups() >= n_top + n_mid);
            assert(self.free_groups() + n_top + n_mid == start.free_groups());
            lemma_scale(n_top as int, n_mid as int, TABLE_PAGES as int);
            assert(self.avail_pages() + (n_top + n_mid) * TABLE_PAGES as nat == start.avail_pages());
            assert(self.tables_unlinked() + (n_top + n_mid) as int == start.tables_unlinked());
            assert(acall_ok(steps) && step_seq_well_ended(steps));
        }
        if !self.tabled[block] {
            let ghost before = *self;
            let ghost cmid = caller@;
            let ghost prev = steps;
            proof {
                lemma_scale(block as int, WINDOW_BLOCKS as int, BLOCK_BYTES as int);
                assert((window + block * BLOCK_BYTES) as int == window_block(before.window, block as int));
            }
            let (linked, Ghost(s)) = self.table(caller, window + block * BLOCK_BYTES, 2);
            proof {
                lemma_mapped_trans(*self, before, start);
                lemma_keeps_trans(*self, before, start);
                lemma_acall_steps_append(c0, cmid, caller@, prev, s);
                lemma_well_ended_append(prev, s);
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
                    lemma_acall_ok_append(prev, s);
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
            }
        }
        proof {
            lemma_scale((n_top + n_mid) as int, n_blk as int, TABLE_PAGES as int);
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
            old(self).window <= addr < old(self).window + WINDOW_BYTES,
            addr as int % PAGE_BYTES as int == 0,
            !old(self).maps(addr as int),
            !old(self).parks(addr as int),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            final(self).keeps_mapped(old(self)),
            forall|a: int| #[trigger] final(self).parks(a) ==> old(self).parks(a),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            step_seq_well_ended(r.1@),
            forall|k: int| 0 <= k < r.1@.len() ==> acall_call_in_window(
                #[trigger] r.1@[k],
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
                addr as int,
                1,
            ),
            match r.0 {
                Some(perm) => {
                    &&& perm@.is_range(addr as int, PAGE_BYTES as int)
                    &&& perm@.provenance() == provenance@
                    &&& final(self).maps(addr as int)
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> a == addr || old(self).maps(a)
                    &&& !final(self).parks(addr as int)
                    &&& acall_ok(r.1@)
                    &&& old(self).can_back_run(addr as int, 1)
                    &&& final(self).top && final(self).middle && final(self).tabled@[old(self).addr_block(addr)]
                    &&& forall|c: int|
                        0 <= c < WINDOW_BLOCKS && c != old(self).addr_block(addr)
                            ==> #[trigger] final(self).tabled@[c] == old(self).tabled@[c]
                    &&& final(self).free_groups() + old(self).tables_for_addr(addr) <= old(self).free_groups()
                    &&& old(self).free_groups() <= final(self).free_groups() + old(self).tables_for_addr(addr) + 1
                    &&& final(self).tables_unlinked() + old(self).tables_for_addr(addr) as int == old(self).tables_unlinked()
                    &&& final(self).avail_pages() + old(self).tables_for_addr(addr) * TABLE_PAGES as nat + 1
                        == old(self).avail_pages()
                    &&& old(self).free_capacity() >= 1 ==> final(self).free_capacity() == old(self).free_capacity() - 1
                    &&& forall|rem: nat|
                        rem >= 1 && #[trigger] old(self).can_back_run(addr as int, rem)
                            ==> final(self).can_back_run(addr + PAGE_BYTES as int, (rem - 1) as nat)
                },
                None => {
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a)
                    &&& (!old(self).can_back_run(addr as int, 1) || !acall_ok(r.1@))
                    &&& refused_spent(*old(self), *final(self), r.1@, 1)
                },
            },
            old(self).top ==> final(self).top,
            old(self).middle ==> final(self).middle,
            forall|c: int| 0 <= c < WINDOW_BLOCKS ==> (old(self).tabled@[c] ==> #[trigger] final(self).tabled@[c]),
            forall|c: int|
                0 <= c < WINDOW_BLOCKS && c != old(self).addr_block(addr)
                    ==> #[trigger] final(self).tabled@[c] == old(self).tabled@[c],
            (old(self).tables_for_addr(addr) == 0 && old(self).avail_pages() == 0) ==> {
                &&& r.0 is None
                &&& *final(self) == *old(self)
                &&& final(caller)@ == old(caller)@
                &&& r.1@ == Seq::<AcallStep>::empty()
            },
        no_unwind
    {
        // The kernel's invariant stays folded: the body only hands it from one call to the next.
        hide(CapKernel::wf);
        let ghost start = *self;
        let ghost c0 = caller@;
        proof {
            lemma_addr_block(start.window, addr);
            let b0 = start.addr_block(addr);
            if b0 != 0 {
                assert(!run_touches_block(start.window, addr as int, 1, 0));
            }
            if b0 != 1 {
                assert(!run_touches_block(start.window, addr as int, 1, 1));
            }
            if b0 != 2 {
                assert(!run_touches_block(start.window, addr as int, 1, 2));
            }
            if b0 != 3 {
                assert(!run_touches_block(start.window, addr as int, 1, 3));
            }
            assert(start.tables_for_run(addr as int, 1) == start.tables_for_addr(addr));
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
                lemma_keeps_no_new_parked(*self, start);
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
            lemma_well_ended_append(s1, s2);
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
        let i = match found {
            Some(i) => i,
            None => {
                proof {
                    lemma_keeps_no_new_mapped(*self, start);
                    lemma_keeps_no_new_parked(*self, start);
                    lemma_acall_ok_append(s1, s2);
                    if start.tables_for_addr(addr) == 0 && start.avail_pages() == 0 {
                        assert(s12 =~= Seq::<AcallStep>::empty());
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
            if mapped is Some {
                if s3.len() > 0 && s3.last().out.status == STATUS_REFUSED {
                    assert(s3[s3.len() - 1].out.status == STATUS_OK);
                    assert(STATUS_REFUSED != STATUS_OK);
                }
            } else {
                assert(s3[s3.len() - 1].out.status == STATUS_REFUSED);
                assert(STATUS_REFUSED != STATUS_OK);
                assert(!acall_ok(s3));
            }
            assert(step_seq_well_ended(s3));
            lemma_well_ended_append(s12, s3);
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
        match mapped {
            Some(perm) => {
                self.state[i] = MAPPED;
                self.owner[i] = addr;
                proof {
                    lemma_acall_ok_append(s12, s3);
                    lemma_addr_block(self.window, addr);
                    assert(self.state@[i as int] == MAPPED);
                    assert(self.frames() =~= held.frames().insert(i as int, (slot as usize, Some(addr))));
                    lemma_avail_update(held.state@, self.state@, self.pages as int, i as int);
                    let ng = (self.pages / TABLE_PAGES) as int;
                    lemma_fundamental_div_mod(self.pages as int, TABLE_PAGES as int);
                    lemma_mod_bound(self.pages as int, TABLE_PAGES as int);
                    assert(ng * TABLE_PAGES <= self.pages) by (nonlinear_arith)
                        requires
                            self.pages as int == (TABLE_PAGES as int) * ng + self.pages as int % (TABLE_PAGES as int),
                            self.pages as int % (TABLE_PAGES as int) >= 0,
                            TABLE_PAGES == 8,
                    ;
                    lemma_free_groups_nonfree_change(held.state@, self.state@, ng, i as int);
                    lemma_keeps_no_new_mapped(held, start);
                    lemma_keeps_no_new_parked(held, start);
                    assert forall|a: int| #[trigger] self.maps(a) implies a == addr || start.maps(a) by {
                        if a != addr {
                            let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == MAPPED && self.owner@[j] == a;
                            assert(j != i);
                            assert(held.state@[j] == MAPPED && held.owner@[j] == a);
                            assert(held.maps(a));
                        }
                    }
                    if self.parks(addr as int) {
                        let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == addr;
                        assert(j != i);
                        assert(occupied(held.state@[j]));
                        assert(live.contains(addr));
                    }
                    assert forall|a: int| #[trigger] self.parks(a) implies start.parks(a) by {
                        let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == a;
                        assert(j != i);
                        assert(held.state@[j] == PARKED && held.owner@[j] == a);
                        assert(held.parks(a));
                    }
                    lemma_map_new_step(start, before, held, *self, addr);
                }
                (Some(perm), Ghost(steps))
            },
            None => {
                proof {
                    lemma_keeps_no_new_mapped(*self, start);
                    lemma_keeps_no_new_parked(*self, start);
                    lemma_acall_ok_append(s12, s3);
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
            final(self).top == old(self).top,
            final(self).middle == old(self).middle,
            final(self).tabled == old(self).tabled,
            final(self).free_groups() == old(self).free_groups(),
            final(self).avail_pages() == old(self).avail_pages() + 1,
            final(self).free_capacity() == old(self).free_capacity() + 1,
            final(self).inv(),
            final(self).frames() == old(self).frames(),
            final(self).parks(addr as int),
            forall|a: int| a != addr && #[trigger] old(self).maps(a) ==> final(self).maps(a),
            forall|a: int| #[trigger] final(self).maps(a) ==> a != addr && old(self).maps(a),
            forall|a: int| #[trigger] old(self).parks(a) ==> final(self).parks(a),
            forall|a: int| #[trigger] final(self).parks(a) ==> a == addr || old(self).parks(a),
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
            lemma_avail_update(before.state@, self.state@, self.pages as int, i as int);
            let ng = (self.pages / TABLE_PAGES) as int;
            lemma_fundamental_div_mod(self.pages as int, TABLE_PAGES as int);
            lemma_mod_bound(self.pages as int, TABLE_PAGES as int);
            assert(ng * TABLE_PAGES <= self.pages) by (nonlinear_arith)
                requires
                    self.pages as int == (TABLE_PAGES as int) * ng + self.pages as int % (TABLE_PAGES as int),
                    self.pages as int % (TABLE_PAGES as int) >= 0,
                    TABLE_PAGES == 8,
            ;
            lemma_free_groups_nonfree_change(before.state@, self.state@, ng, i as int);
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
            assert forall|a: int| #[trigger] self.parks(a) implies a == addr || before.parks(a) by {
                if a != addr {
                    let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == a;
                    assert(j != i);
                    assert(before.state@[j] == PARKED && before.owner@[j] == a);
                }
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
            final(self).top == old(self).top,
            final(self).middle == old(self).middle,
            final(self).tabled == old(self).tabled,
            final(self).free_groups() == old(self).free_groups(),
            final(self).avail_pages() == old(self).avail_pages() + pages as nat,
            final(self).free_capacity() == old(self).free_capacity() + pages as int,
            final(self).inv(),
            final(self).frames() == old(self).frames(),
            pages == 0 ==> *final(self) == *old(self),
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).parks(a),
            forall|a: int| !run_pages(start as int, pages as nat).contains(a) && #[trigger] old(self).maps(a) ==> final(self).maps(a),
            forall|a: int| #[trigger] final(self).maps(a) ==> !run_pages(start as int, pages as nat).contains(a) && old(self).maps(a),
            forall|a: int| #[trigger] old(self).parks(a) ==> final(self).parks(a),
            forall|a: int| #[trigger] final(self).parks(a) ==> old(self).parks(a) || run_pages(start as int, pages as nat).contains(a),
        no_unwind
    {
        let tracked mut rest = perm.get();
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                self.same_config(old(self)),
                self.top == old(self).top,
                self.middle == old(self).middle,
                self.tabled == old(self).tabled,
                self.free_groups() == old(self).free_groups(),
                self.avail_pages() == old(self).avail_pages() + k as nat,
                self.free_capacity() == old(self).free_capacity() + k as int,
                self.frames() == old(self).frames(),
                k == 0 ==> *self == *old(self),
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
                forall|a: int| #[trigger] self.parks(a) ==> old(self).parks(a) || run_pages(start as int, k as nat).contains(a),
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
                assert forall|a: int| #[trigger] self.parks(a) implies old(self).parks(a) || run_pages(start as int, (k + 1) as nat).contains(a) by {
                    if a == addr {
                        assert(run_pages(start as int, (k + 1) as nat).contains(a));
                    } else {
                        assert(before.parks(a));
                        if run_pages(start as int, k as nat).contains(a) {
                            assert(run_pages(start as int, (k + 1) as nat).contains(a));
                        }
                    }
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
            pages > 0,
            start as int % PAGE_BYTES as int == 0,
            old(self).window <= start as int,
            start + pages * PAGE_BYTES <= old(self).window + WINDOW_BYTES,
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> !old(self).maps(a),
        ensures
            final(self).same_config(old(self)),
            final(self).inv(),
            final(self).serves(final(caller)@),
            forall|a: int| #[trigger] old(self).maps(a) ==> final(self).maps(a),
            acall_steps(old(caller)@, final(caller)@, r.1@),
            step_seq_well_ended(r.1@),
            forall|j: int| 0 <= j < r.1@.len() ==> acall_call_in_window(
                #[trigger] r.1@[j],
                old(self).space,
                old(self).untyped,
                old(self).memory,
                old(self).pages,
                old(self).slots,
                old(self).window,
                start as int,
                pages as nat,
            ),
            r.0 is None <==> (!old(self).can_back_run(start as int, pages as nat) || !acall_ok(r.1@)),
            match r.0 {
                Some(perm) => {
                    &&& perm@.is_range(start as int, pages * PAGE_BYTES)
                    &&& perm@.provenance() == provenance@
                    &&& forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).maps(a)
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a) || run_pages(start as int, pages as nat).contains(a)
                    &&& forall|a: int| #[trigger] final(self).parks(a) ==> old(self).parks(a) && !run_pages(start as int, pages as nat).contains(a)
                    &&& final(self).top && final(self).middle
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (
                        #[trigger] final(self).tabled@[b]
                            <==> (old(self).tabled@[b] || run_touches_block(old(self).window, start as int, pages as nat, b))
                    )
                    &&& final(self).avail_pages()
                        + old(self).tables_for_run(start as int, pages as nat) * TABLE_PAGES as nat
                        + pages as nat
                        == old(self).avail_pages()
                    &&& final(self).free_groups() + old(self).tables_for_run(start as int, pages as nat) <= old(self).free_groups()
                    &&& old(self).free_groups() <= final(self).free_groups() + old(self).tables_for_run(start as int, pages as nat) + pages
                    &&& acall_ok(r.1@)
                },
                None => {
                    &&& forall|a: int| #[trigger] final(self).maps(a) ==> old(self).maps(a)
                    &&& old(self).top ==> final(self).top
                    &&& old(self).middle ==> final(self).middle
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (
                        #[trigger] final(self).tabled@[b]
                            ==> (old(self).tabled@[b] || run_touches_block(old(self).window, start as int, pages as nat, b))
                    )
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (old(self).tabled@[b] ==> #[trigger] final(self).tabled@[b])
                    &&& forall|a: int|
                        #[trigger] final(self).parks(a) ==> old(self).parks(a) || run_pages(start as int, pages as nat).contains(a)
                    &&& refused_spent(*old(self), *final(self), r.1@, pages as nat)
                },
            },
            (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a)) ==> {
                &&& r.0 is Some
                &&& r.1@ == Seq::<AcallStep>::empty()
                &&& final(caller)@ == old(caller)@
                &&& final(self).free_capacity() == old(self).free_capacity() - pages as int
            },
            (old(self).tables_for_run(start as int, pages as nat) == 0 && old(self).avail_pages() == 0) ==> {
                &&& r.0 is None
                &&& *final(self) == *old(self)
                &&& final(caller)@ == old(caller)@
                &&& r.1@ == Seq::<AcallStep>::empty()
            },
            old(self).free_capacity() >= pages as int ==> {
                &&& old(self).can_back_run(start as int, pages as nat)
                &&& r.0 is Some ==> final(self).free_capacity() == old(self).free_capacity() - pages as int
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
            if old(self).free_capacity() >= pages as int {
                lemma_capacity_implies_can_back(*old(self), start as int, pages as nat);
            }
        }
        let tracked mut run = PointsToRaw::empty(provenance@);
        let mut k: usize = 0;
        while k < pages
            invariant
                self.inv(),
                self.same_config(old(self)),
                self.serves(caller@),
                pages > 0,
                k <= pages,
                start as int % PAGE_BYTES as int == 0,
                old(self).window <= start as int,
                start + pages * PAGE_BYTES <= old(self).window + WINDOW_BYTES,
                run.dom() =~= Set::range(start as int, start + k * PAGE_BYTES),
                run.provenance() == provenance@,
                provenance@ == self.provenance@,
                c0 == old(caller)@,
                acall_steps(c0, caller@, steps),
                acall_ok(steps),
                step_seq_well_ended(steps),
                forall|j: int| 0 <= j < steps.len() ==> acall_call_in_window(
                    #[trigger] steps[j],
                    old(self).space,
                    old(self).untyped,
                    old(self).memory,
                    old(self).pages,
                    old(self).slots,
                    old(self).window,
                    start as int,
                    pages as nat,
                ),
                old(self).inv(),
                old(self).free_capacity() >= pages as int ==> old(self).can_back_run(start as int, pages as nat),
                parked == forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a),
                forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> !old(self).maps(a),
                forall|a: int| #[trigger] old(self).maps(a) ==> self.maps(a),
                forall|a: int| #[trigger] run_pages(start as int, k as nat).contains(a) ==> self.maps(a) && !old(self).maps(a),
                forall|a: int| #[trigger] self.maps(a) ==> old(self).maps(a) || run_pages(start as int, k as nat).contains(a),
                forall|a: int| #[trigger] self.parks(a) ==> old(self).parks(a),
                k == 0 ==> *self == *old(self) && caller@ == c0 && steps == Seq::<AcallStep>::empty(),
                k > 0 ==> self.top && self.middle && old(self).avail_pages() >= 1,
                forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (
                    #[trigger] self.tabled@[b]
                        <==> (old(self).tabled@[b] || run_touches_block(old(self).window, start as int, k as nat, b))
                ),
                self.free_groups() + old(self).tables_for_run(start as int, k as nat) <= old(self).free_groups(),
                old(self).free_groups() <= self.free_groups() + old(self).tables_for_run(start as int, k as nat) + k,
                self.tables_unlinked() + old(self).tables_for_run(start as int, k as nat) as int == old(self).tables_unlinked(),
                old(self).top ==> self.top,
                old(self).middle ==> self.middle,
                self.avail_pages()
                    + old(self).tables_for_run(start as int, k as nat) * TABLE_PAGES as nat
                    + k as nat
                    == old(self).avail_pages(),
                (k < pages && old(self).can_back_run(start as int, pages as nat))
                    ==> self.can_back_run(start + k * PAGE_BYTES as int, (pages - k) as nat),
                parked ==> {
                    &&& steps == Seq::<AcallStep>::empty()
                    &&& caller@ == c0
                    &&& self.free_capacity() == old(self).free_capacity() - k as int
                    &&& forall|a: int|
                        #[trigger] run_pages(start as int, pages as nat).contains(a) && !run_pages(start as int, k as nat).contains(a)
                            ==> self.parks(a)
                },
                old(self).free_capacity() >= pages as int ==> self.free_capacity() == old(self).free_capacity() - k as int,
            decreases pages - k,
        {
            proof {
                lemma_scale(k as int + 1, pages as int, PAGE_BYTES as int);
                lemma_scale(0, k as int, PAGE_BYTES as int);
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
                lemma_well_ended_append(prev, sp);
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
            match backed {
                Some(page) => {
                    proof {
                        run = run.join(page.get());
                        lemma_keeps_mapped(*self, before);
                        lemma_acall_ok_append(prev, sp);
                        steps = next_steps;
                        lemma_addr_block(old(self).window, addr);
                        lemma_tables_for_run_snoc(*old(self), before, start as int, k as nat, addr);
                        lemma_scale(
                            old(self).tables_for_run(start as int, k as nat) as int,
                            before.tables_for_addr(addr) as int,
                            TABLE_PAGES as int,
                        );
                        assert forall|b: int| 0 <= b < WINDOW_BLOCKS implies (
                            #[trigger] self.tabled@[b]
                                <==> (old(self).tabled@[b] || run_touches_block(old(self).window, start as int, (k + 1) as nat, b))
                        ) by {
                            lemma_run_touches_snoc(old(self).window, start as int, k as nat, b);
                            let b0 = before.addr_block(addr);
                            assert(b0 == old(self).addr_block(addr));
                            if b != b0 {
                                assert(self.tabled@[b] == before.tabled@[b]);
                            }
                        }
                        if k + 1 < pages && old(self).can_back_run(start as int, pages as nat) {
                            let rem = (pages - k) as nat;
                            assert(before.can_back_run(addr as int, rem));
                            assert(self.can_back_run(addr + PAGE_BYTES as int, (rem - 1) as nat));
                            assert(addr + PAGE_BYTES as int == start + (k + 1) * PAGE_BYTES as int);
                        }
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
                        assert forall|a: int| #[trigger] self.parks(a) implies old(self).parks(a) by {
                            assert(before.parks(a));
                        }
                    }
                    k += 1;
                    assert(run.dom() =~= Set::range(start as int, start + k * PAGE_BYTES));
                },
                None => {
                    proof {
                        lemma_keeps_mapped(*self, before);
                        lemma_run_within(start as int, k as int, pages as int);
                        lemma_acall_ok_append(prev, sp);
                        if old(self).can_back_run(start as int, pages as nat) {
                            let rem = (pages - k) as nat;
                            lemma_can_back_first_page(before, addr as int, rem);
                            assert(!acall_ok(sp));
                        }
                        if old(self).tables_for_run(start as int, pages as nat) == 0 && old(self).avail_pages() == 0 {
                            assert(k == 0);
                            lemma_run_touches_step(old(self).window, start as int, pages as nat, 0);
                            lemma_run_touches_step(old(self).window, start as int, pages as nat, 1);
                            lemma_run_touches_step(old(self).window, start as int, pages as nat, 2);
                            lemma_run_touches_step(old(self).window, start as int, pages as nat, 3);
                            lemma_addr_block(old(self).window, start);
                            let b0 = old(self).addr_block(start);
                            if b0 != 0 {
                                assert(!run_touches_block(old(self).window, start as int, 1, 0));
                            }
                            if b0 != 1 {
                                assert(!run_touches_block(old(self).window, start as int, 1, 1));
                            }
                            if b0 != 2 {
                                assert(!run_touches_block(old(self).window, start as int, 1, 2));
                            }
                            if b0 != 3 {
                                assert(!run_touches_block(old(self).window, start as int, 1, 3));
                            }
                            assert(before.tables_for_addr(start) == 0);
                            assert(next_steps =~= Seq::<AcallStep>::empty());
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
                        // The pages backed before the refusal are parked, and what the refused page
                        // spent adds to what the backed ones did.
                        lemma_run_within(start as int, k as int, pages as int);
                        assert forall|a: int| #[trigger] self.parks(a)
                            implies old(self).parks(a) || run_pages(start as int, pages as nat).contains(a) by {
                            if !run_pages(start as int, k as nat).contains(a) {
                                assert(released.parks(a));
                                assert(before.parks(a));
                            }
                        }
                        lemma_addr_block(old(self).window, addr);
                        lemma_scale(k as int + 1, pages as int, PAGE_BYTES as int);
                        assert forall|b: int| 0 <= b < WINDOW_BLOCKS && #[trigger] self.tabled@[b]
                            implies old(self).tabled@[b] || run_touches_block(old(self).window, start as int, pages as nat, b) by {
                            lemma_run_touches_snoc(old(self).window, start as int, k as nat, b);
                            let b0 = before.addr_block(addr);
                            assert(b0 == old(self).addr_block(addr));
                            if b != b0 {
                                assert(released.tabled@[b] == before.tabled@[b]);
                            }
                        }
                        let linked_k = before.tables_unlinked() - released.tables_unlinked();
                        let tk = old(self).tables_for_run(start as int, k as nat) as int;
                        lemma_scale(tk, linked_k, TABLE_PAGES as int);
                        lemma_scale(linked_k, 1, TABLE_PAGES as int);
                        lemma_scale(tk + linked_k, 1, TABLE_PAGES as int);
                        lemma_scale(tk, tk + linked_k, TABLE_PAGES as int);
                        assert(acall_ok(next_steps) == acall_ok(sp));
                        assert(refused_spent(*old(self), *self, next_steps, pages as nat));
                    }
                    return (None, Ghost(next_steps));
                },
            }
        }
        proof {
            assert forall|a: int| #[trigger] self.parks(a)
                implies old(self).parks(a) && !run_pages(start as int, pages as nat).contains(a) by {
                if run_pages(start as int, pages as nat).contains(a) {
                    assert(self.maps(a));
                    let i = choose|i: int| 0 <= i < self.pages && #[trigger] self.state@[i] == MAPPED && self.owner@[i] == a;
                    let j = choose|j: int| 0 <= j < self.pages && #[trigger] self.state@[j] == PARKED && self.owner@[j] == a;
                    assert(i != j);
                    assert(occupied(self.state@[i]) && occupied(self.state@[j]));
                }
            }
        }
        (Some(Tracked(run)), Ghost(steps))
    }
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

/// Keeping every occupied page's state and address introduces no newly parked address.
proof fn lemma_keeps_no_new_parked(new: Record, old: Record)
    requires
        new.keeps(&old),
    ensures
        forall|a: int| #[trigger] new.parks(a) ==> old.parks(a),
{
    assert forall|a: int| #[trigger] new.parks(a) implies old.parks(a) by {
        let j = choose|j: int| 0 <= j < new.pages && #[trigger] new.state@[j] == PARKED && new.owner@[j] == a;
        assert(occupied(new.state@[j]));
        assert(old.state@[j] == PARKED);
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

/// Non-negative `free_capacity` implies the untyped holds at least one free table block for every
/// unlinked window table.
proof fn lemma_capacity_nonneg(r: Record)
    requires
        r.inv(),
        r.free_capacity() >= 0,
    ensures
        r.free_groups() as int >= r.tables_unlinked(),
        r.missing_tables() == 0,
        r.free_capacity() == r.avail_pages() as int - r.tables_unlinked() * TABLE_PAGES as int,
{
    lemma_avail_bound(r.state@, r.pages as int);
    if (r.free_groups() as int) < r.tables_unlinked() {
        let mt = r.missing_tables();
        let tu = r.tables_unlinked();
        assert(mt >= 1);
        assert(tu >= 1);
        assert(tu * (TABLE_PAGES as int) >= 8) by (nonlinear_arith)
            requires
                tu >= 1,
                TABLE_PAGES == 8,
        ;
        assert(mt * (MAX_PAGES as int) >= MAX_PAGES as int) by (nonlinear_arith)
            requires
                mt >= 1,
                MAX_PAGES > 0,
        ;
        assert(false);
    }
}

/// Unlinked tables on a run's path are at most the unlinked tables of the whole window.
proof fn lemma_tables_for_run_le_unlinked(r: Record, start: int, pages: nat)
    ensures
        r.tables_for_run(start, pages) as int <= r.tables_unlinked(),
{
}

/// Free capacity covering `pages` implies `can_back_run` for any non-empty `pages`-page run.
proof fn lemma_capacity_implies_can_back(r: Record, start: int, pages: nat)
    requires
        r.inv(),
        pages > 0,
        r.free_capacity() >= pages as int,
    ensures
        r.can_back_run(start, pages),
{
    lemma_capacity_nonneg(r);
    lemma_tables_for_run_le_unlinked(r, start, pages);
    let t = r.tables_for_run(start, pages) as int;
    let u = r.tables_unlinked();
    lemma_scale(t, u, TABLE_PAGES as int);
}

/// Being able to back `rem >= 1` pages from `addr` implies being able to back the first page at `addr`.
proof fn lemma_can_back_first_page(r: Record, addr: int, rem: nat)
    requires
        rem >= 1,
        r.can_back_run(addr, rem),
    ensures
        r.can_back_run(addr, 1),
{
    lemma_run_touches_step(r.window, addr, rem, 0);
    lemma_run_touches_step(r.window, addr, rem, 1);
    lemma_run_touches_step(r.window, addr, rem, 2);
    lemma_run_touches_step(r.window, addr, rem, 3);
    let t1 = r.tables_for_run(addr, 1) as int;
    let tr = r.tables_for_run(addr, rem) as int;
    assert(t1 <= tr);
    lemma_scale(t1, tr, TABLE_PAGES as int);
}

/// Linking the path tables for `addr` splits the unlinked tables of a `rem`-page run from `addr` into
/// `tables_for_addr(addr)` and the unlinked tables of the remaining `rem - 1` pages.
proof fn lemma_tables_for_run_step(before: Record, after: Record, addr: usize, rem: nat)
    requires
        before.inv(),
        before.window <= addr < before.window + WINDOW_BYTES,
        addr as int % PAGE_BYTES as int == 0,
        after.window == before.window,
        after.top && after.middle && after.tabled@[before.addr_block(addr)],
        forall|c: int|
            0 <= c < WINDOW_BLOCKS && c != before.addr_block(addr)
                ==> #[trigger] after.tabled@[c] == before.tabled@[c],
        rem >= 1,
    ensures
        before.tables_for_addr(addr)
            + after.tables_for_run(addr + PAGE_BYTES as int, (rem - 1) as nat)
            == before.tables_for_run(addr as int, rem),
{
    lemma_addr_block(before.window, addr);
    let b0 = before.addr_block(addr);
    if b0 != 0 {
        assert(after.tabled@[0] == before.tabled@[0]);
        assert(!run_touches_block(before.window, addr as int, 1, 0));
    }
    if b0 != 1 {
        assert(after.tabled@[1] == before.tabled@[1]);
        assert(!run_touches_block(before.window, addr as int, 1, 1));
    }
    if b0 != 2 {
        assert(after.tabled@[2] == before.tabled@[2]);
        assert(!run_touches_block(before.window, addr as int, 1, 2));
    }
    if b0 != 3 {
        assert(after.tabled@[3] == before.tabled@[3]);
        assert(!run_touches_block(before.window, addr as int, 1, 3));
    }
    if rem > 1 {
        lemma_run_touches_step(before.window, addr as int, rem, 0);
        lemma_run_touches_step(before.window, addr as int, rem, 1);
        lemma_run_touches_step(before.window, addr as int, rem, 2);
        lemma_run_touches_step(before.window, addr as int, rem, 3);
    }
}

/// Across the `(k + 1)`-th page of `back_run`, the path tables linked up to `k` plus those linked for
/// `addr = start + k * PAGE_BYTES` equal the path tables of the `(k + 1)`-page prefix.
proof fn lemma_tables_for_run_snoc(start_rec: Record, before: Record, start: int, k: nat, addr: usize)
    requires
        start_rec.inv(),
        before.window == start_rec.window,
        addr as int == start + k * PAGE_BYTES as int,
        start_rec.window <= addr < start_rec.window + WINDOW_BYTES,
        addr as int % PAGE_BYTES as int == 0,
        k == 0 ==> before == start_rec,
        k > 0 ==> before.top && before.middle,
        forall|b: int|
            0 <= b < WINDOW_BLOCKS ==> (
                #[trigger] before.tabled@[b]
                    <==> (start_rec.tabled@[b] || run_touches_block(start_rec.window, start, k, b))
            ),
    ensures
        start_rec.tables_for_run(start, k) + before.tables_for_addr(addr)
            == start_rec.tables_for_run(start, k + 1),
{
    lemma_addr_block(start_rec.window, addr);
    let b0 = before.addr_block(addr);
    assert(b0 == start_rec.addr_block(addr));
    if b0 != 0 {
        assert(!run_touches_block(start_rec.window, addr as int, 1, 0));
    }
    if b0 != 1 {
        assert(!run_touches_block(start_rec.window, addr as int, 1, 1));
    }
    if b0 != 2 {
        assert(!run_touches_block(start_rec.window, addr as int, 1, 2));
    }
    if b0 != 3 {
        assert(!run_touches_block(start_rec.window, addr as int, 1, 3));
    }
    assert(before.tabled@[0] <==> (start_rec.tabled@[0] || run_touches_block(start_rec.window, start, k, 0)));
    assert(before.tabled@[1] <==> (start_rec.tabled@[1] || run_touches_block(start_rec.window, start, k, 1)));
    assert(before.tabled@[2] <==> (start_rec.tabled@[2] || run_touches_block(start_rec.window, start, k, 2)));
    assert(before.tabled@[3] <==> (start_rec.tabled@[3] || run_touches_block(start_rec.window, start, k, 3)));
    lemma_run_touches_snoc(start_rec.window, start, k, 0);
    lemma_run_touches_snoc(start_rec.window, start, k, 1);
    lemma_run_touches_snoc(start_rec.window, start, k, 2);
    lemma_run_touches_snoc(start_rec.window, start, k, 3);
}

/// Accounting across `map_new`'s `Some` arm: preserves `free_capacity() - 1` when `free_capacity() >= 1`
/// and `can_back_run` on the remaining `rem - 1` pages.
proof fn lemma_map_new_step(start: Record, after_path: Record, held: Record, after: Record, addr: usize)
    requires
        start.inv(),
        after.inv(),
        start.window <= addr < start.window + WINDOW_BYTES,
        addr as int % PAGE_BYTES as int == 0,
        after_path.window == start.window,
        after.window == start.window,
        start.free_groups() >= start.tables_for_addr(addr),
        after_path.free_groups() + start.tables_for_addr(addr) == start.free_groups(),
        after_path.avail_pages() + start.tables_for_addr(addr) * TABLE_PAGES as nat == start.avail_pages(),
        after_path.tables_unlinked() + start.tables_for_addr(addr) as int == start.tables_unlinked(),
        after_path.top && after_path.middle && after_path.tabled@[start.addr_block(addr)],
        forall|c: int|
            0 <= c < WINDOW_BLOCKS && c != start.addr_block(addr)
                ==> #[trigger] after_path.tabled@[c] == start.tabled@[c],
        after_path.avail_pages() >= 1,
        held.avail_pages() == after_path.avail_pages(),
        held.free_groups() <= after_path.free_groups(),
        frame_group_step(after_path, held),
        after.top == after_path.top,
        after.middle == after_path.middle,
        after.tabled == after_path.tabled,
        after.free_groups() == held.free_groups(),
        after.avail_pages() + 1 == held.avail_pages(),
    ensures
        start.can_back_run(addr as int, 1),
        after.free_groups() + start.tables_for_addr(addr) <= start.free_groups(),
        after.avail_pages() + start.tables_for_addr(addr) * TABLE_PAGES as nat + 1 == start.avail_pages(),
        start.free_capacity() >= 1 ==> after.free_capacity() == start.free_capacity() - 1,
        forall|rem: nat|
            rem >= 1 && #[trigger] start.can_back_run(addr as int, rem)
                ==> after.can_back_run(addr + PAGE_BYTES as int, (rem - 1) as nat),
{
    lemma_tables_for_run_step(start, after, addr, 1);
    assert(after.tables_for_run(addr + PAGE_BYTES as int, 0) == 0);
    assert(start.tables_for_addr(addr) == start.tables_for_run(addr as int, 1));

    if start.free_capacity() >= 1 {
        lemma_capacity_nonneg(start);
        let need = start.tables_for_addr(addr) as int;
        assert(need * (TABLE_PAGES as int) + after_path.tables_unlinked() * (TABLE_PAGES as int)
            == start.tables_unlinked() * (TABLE_PAGES as int)) by (nonlinear_arith)
            requires
                after_path.tables_unlinked() + need == start.tables_unlinked(),
        ;
        assert(after_path.avail_pages() as int - after_path.tables_unlinked() * TABLE_PAGES as int == start.free_capacity());
        assert(after_path.free_groups() as int >= after_path.tables_unlinked());
        if after_path.avail_pages() == after_path.free_groups() * TABLE_PAGES as nat {
            let fg = after_path.free_groups() as int;
            let tu = after_path.tables_unlinked();
            assert(after_path.avail_pages() as int == fg * 8);
            assert(fg > tu) by (nonlinear_arith)
                requires
                    fg * 8 - tu * 8 >= 1,
            ;
        }
        assert(after.free_groups() as int >= after.tables_unlinked());
        assert(after.missing_tables() == 0);
    }

    assert forall|rem: nat|
        rem >= 1 && #[trigger] start.can_back_run(addr as int, rem)
        implies after.can_back_run(addr + PAGE_BYTES as int, (rem - 1) as nat) by {
        lemma_tables_for_run_step(start, after, addr, rem);
        lemma_tables_for_run_le_unlinked(after_path, addr + PAGE_BYTES as int, (rem - 1) as nat);
        assert(after.tables_for_run(addr + PAGE_BYTES as int, (rem - 1) as nat)
            == after_path.tables_for_run(addr + PAGE_BYTES as int, (rem - 1) as nat));
        let need = start.tables_for_addr(addr) as int;
        let ta = after.tables_for_run(addr + PAGE_BYTES as int, (rem - 1) as nat) as int;
        let tb = start.tables_for_run(addr as int, rem) as int;
        assert(need * (TABLE_PAGES as int) + ta * (TABLE_PAGES as int) == tb * (TABLE_PAGES as int)) by (nonlinear_arith)
            requires
                need + ta == tb,
        ;
        assert(after_path.free_groups() as int >= ta);
        assert(after_path.avail_pages() as int - ta * TABLE_PAGES as int >= rem as int);
        if after_path.avail_pages() == after_path.free_groups() * TABLE_PAGES as nat {
            let fg = after_path.free_groups() as int;
            assert(after_path.avail_pages() as int == fg * 8);
            assert(fg > ta) by (nonlinear_arith)
                requires
                    fg * 8 - ta * 8 >= 1,
            ;
        }
        assert(after.free_groups() as int >= ta);
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
        old(record).window == old(spans).window,
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
        step_seq_well_ended(r.1@),
        forall|j: int| 0 <= j < r.1@.len() ==> acall_call_in_window(
            #[trigger] r.1@[j],
            old(record).space,
            old(record).untyped,
            old(record).memory,
            old(record).pages,
            old(record).slots,
            old(record).window,
            start as int,
            pages as nat,
        ),
        r.0 is None <==> (!old(record).can_back_run(start as int, pages as nat) || !acall_ok(r.1@)),
        match r.0 {
            Some(perm) => {
                &&& perm@.is_range(start as int, pages * PAGE_BYTES)
                &&& perm@.provenance() == provenance@
                &&& final(spans).map@ == view@.backed_run(span@, start as int, pages as nat).spans
                &&& forall|a: int| #[trigger] final(record).parks(a) ==> old(record).parks(a) && !run_pages(start as int, pages as nat).contains(a)
                &&& final(record).top && final(record).middle
                &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (
                    #[trigger] final(record).tabled@[b]
                        <==> (old(record).tabled@[b] || run_touches_block(old(record).window, start as int, pages as nat, b))
                )
                &&& final(record).avail_pages()
                    + old(record).tables_for_run(start as int, pages as nat) * TABLE_PAGES as nat
                    + pages as nat
                    == old(record).avail_pages()
                &&& final(record).free_groups() + old(record).tables_for_run(start as int, pages as nat) <= old(record).free_groups()
                &&& old(record).free_groups() <= final(record).free_groups() + old(record).tables_for_run(start as int, pages as nat) + pages
                &&& acall_ok(r.1@)
            },
            None => {
                &&& final(spans).map@ == old(spans).map@
                &&& old(record).top ==> final(record).top
                &&& old(record).middle ==> final(record).middle
                &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (
                    #[trigger] final(record).tabled@[b]
                        ==> (old(record).tabled@[b] || run_touches_block(old(record).window, start as int, pages as nat, b))
                )
                &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (old(record).tabled@[b] ==> #[trigger] final(record).tabled@[b])
                &&& forall|a: int|
                    #[trigger] final(record).parks(a) ==> old(record).parks(a) || run_pages(start as int, pages as nat).contains(a)
                &&& refused_spent(*old(record), *final(record), r.1@, pages as nat)
            },
        },
        (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(record).parks(a)) ==> {
            &&& r.0 is Some
            &&& r.1@ == Seq::<AcallStep>::empty()
            &&& final(caller)@ == old(caller)@
            &&& final(record).free_capacity() == old(record).free_capacity() - pages as int
        },
        (old(record).tables_for_run(start as int, pages as nat) == 0 && old(record).avail_pages() == 0) ==> {
            &&& r.0 is None
            &&& *final(record) == *old(record)
            &&& final(caller)@ == old(caller)@
            &&& r.1@ == Seq::<AcallStep>::empty()
        },
        old(record).free_capacity() >= pages as int ==> {
            &&& old(record).can_back_run(start as int, pages as nat)
            &&& r.0 is Some ==> final(record).free_capacity() == old(record).free_capacity() - pages as int
        },
    no_unwind
{
    let ghost before = *record;
    let ghost view = view@;
    let ghost after = view.backed_run(span@, start as int, pages as nat).spans;
    proof {
        assert(old(spans).holds(span@));
        let j = old(spans).index@[span@];
        let blocks = old(spans).map@[span@].blocks;
        lemma_scale(0, j, BLOCK_BYTES as int);
        lemma_scale(j + blocks as int, WINDOW_BLOCKS as int, BLOCK_BYTES as int);
        lemma_scale(j, blocks as int, BLOCK_BYTES as int);
        assert(before.window <= start as int);
        assert(start + pages * PAGE_BYTES <= before.window + WINDOW_BYTES);
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
        final(record).top == old(record).top,
        final(record).middle == old(record).middle,
        final(record).tabled == old(record).tabled,
        final(record).free_groups() == old(record).free_groups(),
        final(record).avail_pages() == old(record).avail_pages() + pages as nat,
        final(record).free_capacity() == old(record).free_capacity() + pages as int,
        final(record).inv(),
        final(record).frames() == old(record).frames(),
        backed_is_mapped(final(spans).map@, *final(record)),
        forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(record).parks(a),
        forall|a: int| #[trigger] old(record).parks(a) ==> final(record).parks(a),
        forall|a: int| #[trigger] final(record).parks(a) ==> old(record).parks(a) || run_pages(start as int, pages as nat).contains(a),
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

    /// Free frames (free untyped pages, held frames, and parked frames `release` returned) beyond
    /// `TABLE_PAGES` per unlinked window table, negative when the untyped lacks a table block for an
    /// unlinked window table.
    pub closed spec fn free_capacity(&self) -> int {
        self.record.free_capacity()
    }

    /// Free untyped pages, held frames, and parked frames `release` returned.
    pub closed spec fn free_frames(&self) -> nat {
        self.record.avail_pages()
    }

    /// Free order-3 (`TABLE_PAGES`-page) blocks in the untyped available for table pages.
    pub closed spec fn free_table_blocks(&self) -> nat {
        self.record.free_groups()
    }

    /// Whether the level-3 table of the window's path has been linked.
    pub closed spec fn top_linked(&self) -> bool {
        self.record.top
    }

    /// Whether the level-2 table of the window's path has been linked.
    pub closed spec fn middle_linked(&self) -> bool {
        self.record.middle
    }

    /// Whether block `b` of the window has its leaf table linked.
    pub closed spec fn block_tabled(&self, b: int) -> bool {
        self.record.tabled@[b]
    }

    /// Number of the window's tables not linked yet: the level-3 and level-2 tables of its path and
    /// the leaf table of each block.
    pub open spec fn unlinked_tables(&self) -> nat {
        (if self.top_linked() { 0nat } else { 1nat })
            + (if self.middle_linked() { 0nat } else { 1nat })
            + (if self.block_tabled(0) { 0nat } else { 1nat })
            + (if self.block_tabled(1) { 0nat } else { 1nat })
            + (if self.block_tabled(2) { 0nat } else { 1nat })
            + (if self.block_tabled(3) { 0nat } else { 1nat })
    }

    /// Number of unlinked tables along the path of the `pages`-page run from `start`.
    pub open spec fn unlinked_tables_on(&self, start: int, pages: nat) -> nat {
        if pages == 0 {
            0
        } else {
            (if self.top_linked() { 0nat } else { 1nat })
                + (if self.middle_linked() { 0nat } else { 1nat })
                + (if !self.block_tabled(0) && run_touches_block(self.window(), start, pages, 0) { 1nat } else { 0nat })
                + (if !self.block_tabled(1) && run_touches_block(self.window(), start, pages, 1) { 1nat } else { 0nat })
                + (if !self.block_tabled(2) && run_touches_block(self.window(), start, pages, 2) { 1nat } else { 0nat })
                + (if !self.block_tabled(3) && run_touches_block(self.window(), start, pages, 3) { 1nat } else { 0nat })
        }
    }

    /// Number of pages in the `pages`-page run from `start` that are parked at their addresses.
    pub open spec fn parked_pages(&self, start: int, pages: nat) -> nat
        decreases pages,
    {
        if pages == 0 {
            0
        } else {
            let tail = (pages - 1) as nat;
            self.parked_pages(start, tail)
                + if self.parks(start + tail * PAGE_BYTES as int) { 1nat } else { 0nat }
        }
    }

    /// Number of pages in the `pages`-page run from `start` that are not parked at their addresses.
    pub open spec fn unparked_pages(&self, start: int, pages: nat) -> nat
        decreases pages,
    {
        if pages == 0 {
            0
        } else {
            let tail = (pages - 1) as nat;
            self.unparked_pages(start, tail)
                + if self.parks(start + tail * PAGE_BYTES as int) { 0nat } else { 1nat }
        }
    }

    /// Whether the source has enough free `TABLE_PAGES` blocks for the unlinked tables on the run's
    /// path and enough free frames outside the run's parked pages, beyond `TABLE_PAGES` per unlinked
    /// path table, to cover the run's unparked pages.
    pub open spec fn can_back(&self, start: int, pages: nat) -> bool {
        &&& self.free_table_blocks() >= self.unlinked_tables_on(start, pages)
        &&& (self.free_frames() as int - self.parked_pages(start, pages) as int)
            - self.unlinked_tables_on(start, pages) as int * TABLE_PAGES as int
            >= self.unparked_pages(start, pages) as int
    }

    proof fn lemma_run_parked_split(&self, start: int, pages: nat)
        ensures
            self.parked_pages(start, pages) + self.unparked_pages(start, pages) == pages,
        decreases pages,
    {
        if pages > 0 {
            self.lemma_run_parked_split(start, (pages - 1) as nat);
        }
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
                    &&& source.free_frames() == pages as nat
                    &&& source.free_table_blocks() == (pages / TABLE_PAGES) as nat
                    &&& !source.top_linked()
                    &&& !source.middle_linked()
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> !#[trigger] source.block_tabled(b)
                    &&& forall|a: int| !#[trigger] source.parks(a)
                    &&& pages >= (2 + WINDOW_BLOCKS) * TABLE_PAGES
                        ==> source.free_capacity() == pages as int - (2 + WINDOW_BLOCKS as int) * TABLE_PAGES as int
                    &&& pages < (2 + WINDOW_BLOCKS) * TABLE_PAGES ==> source.free_capacity() < 0
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
            },
            exposed,
            grants: Ghost(Seq::empty()),
            refusals: Ghost(Seq::empty()),
            trace: Ghost(Seq::empty()),
        };
        proof {
            assert(source@.spans =~= Map::empty());
            assert(source.record.frames() =~= Map::empty());
            assert(source.record.tables_unlinked() == 2 + WINDOW_BLOCKS as int);
            lemma_avail_all_free(source.record.state@, pages as int);
            let ng = (pages / TABLE_PAGES) as int;
            lemma_div_pos_is_pos(pages as int, TABLE_PAGES as int);
            lemma_fundamental_div_mod(pages as int, TABLE_PAGES as int);
            lemma_mod_bound(pages as int, TABLE_PAGES as int);
            assert(ng * TABLE_PAGES <= pages) by (nonlinear_arith)
                requires
                    pages as int == (TABLE_PAGES as int) * ng + pages as int % (TABLE_PAGES as int),
                    pages as int % (TABLE_PAGES as int) >= 0,
                    TABLE_PAGES == 8,
            ;
            lemma_free_groups_all_free(source.record.state@, ng);
            if pages >= (2 + WINDOW_BLOCKS) * TABLE_PAGES {
                assert(ng >= (2 + WINDOW_BLOCKS) as int) by (nonlinear_arith)
                    requires
                        pages as int == (TABLE_PAGES as int) * ng + pages as int % (TABLE_PAGES as int),
                        pages as int % (TABLE_PAGES as int) < (TABLE_PAGES as int),
                        pages >= (2 + WINDOW_BLOCKS) * TABLE_PAGES,
                        WINDOW_BLOCKS == 4,
                        TABLE_PAGES == 8,
                ;
                assert(source.record.missing_tables() == 0);
            } else {
                let mt = source.record.missing_tables();
                assert(mt >= 0);
                assert(mt * (MAX_PAGES as int) >= 0) by (nonlinear_arith)
                    requires
                        mt >= 0,
                        MAX_PAGES > 0,
                ;
            }
        }
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
            final(self).free_frames() == old(self).free_frames(),
            final(self).free_table_blocks() == old(self).free_table_blocks(),
            final(self).top_linked() == old(self).top_linked(),
            final(self).middle_linked() == old(self).middle_linked(),
            forall|b: int| 0 <= b < WINDOW_BLOCKS ==> #[trigger] final(self).block_tabled(b) == old(self).block_tabled(b),
            forall|a: int| #[trigger] final(self).parks(a) == old(self).parks(a),
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

    /// Every `acall` step stays within the source's window, slots and untyped; `back` returns `None` iff
    /// `!can_back(start, pages)` or `acall` refuses the final step; a run whose every page is parked is
    /// granted with no system call. A grant spends a free `TABLE_PAGES` block per table it links, and
    /// each frame it takes breaks at most one more. A refusal keeps the tables it linked on the run's
    /// path and parks the pages it backed before it: it spends a block per table linked, and the step
    /// `acall` refused, if any, at most one block more, or a frame.
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
                &&& (!acall_ok(steps) <==> {
                    &&& steps.len() > 0
                    &&& acall_ok(steps.drop_last())
                    &&& steps.last().out.status == STATUS_REFUSED
                })
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
                &&& (r is None <==> (!old(self).can_back(start as int, pages as nat) || !acall_ok(steps)))
                &&& (r is Some <==> (old(self).can_back(start as int, pages as nat) && acall_ok(steps)))
                &&& r is Some ==> {
                    &&& final(self).top_linked()
                    &&& final(self).middle_linked()
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (
                        #[trigger] final(self).block_tabled(b)
                            <==> (old(self).block_tabled(b) || run_touches_block(old(self).window(), start as int, pages as nat, b))
                    )
                    &&& final(self).free_frames()
                        + old(self).unlinked_tables_on(start as int, pages as nat) * TABLE_PAGES as nat
                        + pages as nat
                        == old(self).free_frames()
                    &&& final(self).free_table_blocks() + old(self).unlinked_tables_on(start as int, pages as nat)
                        <= old(self).free_table_blocks()
                    &&& old(self).free_table_blocks()
                        <= final(self).free_table_blocks() + old(self).unlinked_tables_on(start as int, pages as nat) + pages as nat
                    &&& forall|a: int|
                        #[trigger] final(self).parks(a)
                            ==> old(self).parks(a) && !run_pages(start as int, pages as nat).contains(a)
                }
                &&& r is None ==> {
                    let linked = old(self).unlinked_tables() as int - final(self).unlinked_tables() as int;
                    &&& final(self).unlinked_tables() <= old(self).unlinked_tables()
                    &&& old(self).top_linked() ==> final(self).top_linked()
                    &&& old(self).middle_linked() ==> final(self).middle_linked()
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (old(self).block_tabled(b) ==> #[trigger] final(self).block_tabled(b))
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> (
                        #[trigger] final(self).block_tabled(b)
                            ==> (old(self).block_tabled(b) || run_touches_block(old(self).window(), start as int, pages as nat, b))
                    )
                    &&& forall|a: int|
                        #[trigger] final(self).parks(a) ==> old(self).parks(a) || run_pages(start as int, pages as nat).contains(a)
                    &&& final(self).free_table_blocks() as int + linked <= old(self).free_table_blocks() as int
                    &&& old(self).free_table_blocks() as int <= final(self).free_table_blocks() as int + linked + pages as int
                    &&& acall_ok(steps) ==> final(self).free_frames() as int + linked * TABLE_PAGES as int == old(self).free_frames() as int
                    &&& final(self).free_frames() as int + linked * TABLE_PAGES as int <= old(self).free_frames() as int
                    &&& old(self).free_frames() as int <= final(self).free_frames() as int + (linked + 1) * TABLE_PAGES as int
                }
                &&& (forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> old(self).parks(a)) ==> {
                    &&& steps == Seq::<AcallStep>::empty()
                    &&& final(token)@ == old(token)@
                    &&& final(self).free_capacity() == old(self).free_capacity() - pages as int
                }
                &&& (old(self).unlinked_tables_on(start as int, pages as nat) == 0 && old(self).free_frames() == 0) ==> {
                    &&& r is None
                    &&& steps == Seq::<AcallStep>::empty()
                    &&& final(token)@ == old(token)@
                    &&& final(self).free_frames() == 0
                    &&& final(self).free_table_blocks() == old(self).free_table_blocks()
                    &&& final(self).top_linked() == old(self).top_linked()
                    &&& final(self).middle_linked() == old(self).middle_linked()
                    &&& forall|b: int| 0 <= b < WINDOW_BLOCKS ==> #[trigger] final(self).block_tabled(b) == old(self).block_tabled(b)
                    &&& forall|a: int| #[trigger] final(self).parks(a) == old(self).parks(a)
                }
                &&& old(self).free_capacity() >= pages as int ==> {
                    &&& old(self).can_back(start as int, pages as nat)
                    &&& r is Some ==> final(self).free_capacity() == old(self).free_capacity() - pages as int
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
            old(self).lemma_run_parked_split(start as int, pages as nat);
            assert(old(self).unlinked_tables_on(start as int, pages as nat)
                == old(self).record.tables_for_run(start as int, pages as nat));
            assert(old(self).can_back(start as int, pages as nat)
                <==> old(self).record.can_back_run(start as int, pages as nat));
        }
        let ghost before = self@;
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

    /// Each page of the run is parked, with no system call: the token, the configuration and the
    /// `acall` steps made so far stay as they were, and `free_capacity` and `free_frames` rise by
    /// `pages`.
    fn release(&mut self, token: &mut Tracked<Caller>, span: Ghost<int>, start: usize, pages: usize, perm: Tracked<PointsToRaw>)
        ensures
            final(token)@ == old(token)@,
            final(self).space() == old(self).space(),
            final(self).untyped() == old(self).untyped(),
            final(self).memory() == old(self).memory(),
            final(self).pages() == old(self).pages(),
            final(self).slots() == old(self).slots(),
            final(self).window() == old(self).window(),
            final(self).acall_trace() == old(self).acall_trace(),
            final(self).free_capacity() == old(self).free_capacity() + pages as int,
            final(self).free_frames() == old(self).free_frames() + pages as nat,
            final(self).free_table_blocks() == old(self).free_table_blocks(),
            final(self).top_linked() == old(self).top_linked(),
            final(self).middle_linked() == old(self).middle_linked(),
            forall|b: int| 0 <= b < WINDOW_BLOCKS ==> #[trigger] final(self).block_tabled(b) == old(self).block_tabled(b),
            forall|a: int| #[trigger] run_pages(start as int, pages as nat).contains(a) ==> final(self).parks(a),
            forall|a: int|
                #[trigger] final(self).parks(a)
                    <==> (old(self).parks(a) || run_pages(start as int, pages as nat).contains(a)),
    {
        proof {
            use_type_invariant(&*self);
            lemma_released_run_wf(self@, span@, start as int, pages as nat);
        }
        let ghost before = self@;
        release_fields(&mut self.spans, &mut self.record, span, start, pages, perm, Ghost(before));
    }

    /// Gives up the span with no system call: the token, the configuration, the linked tables, the
    /// parked and free frames and the `acall` steps made so far stay as they were.
    fn release_span(&mut self, token: &mut Tracked<Caller>, span: usize)
        ensures
            final(token)@ == old(token)@,
            final(self).space() == old(self).space(),
            final(self).untyped() == old(self).untyped(),
            final(self).memory() == old(self).memory(),
            final(self).pages() == old(self).pages(),
            final(self).slots() == old(self).slots(),
            final(self).window() == old(self).window(),
            final(self).free_capacity() == old(self).free_capacity(),
            final(self).free_frames() == old(self).free_frames(),
            final(self).free_table_blocks() == old(self).free_table_blocks(),
            final(self).top_linked() == old(self).top_linked(),
            final(self).middle_linked() == old(self).middle_linked(),
            forall|b: int| 0 <= b < WINDOW_BLOCKS ==> #[trigger] final(self).block_tabled(b) == old(self).block_tabled(b),
            forall|a: int| #[trigger] final(self).parks(a) == old(self).parks(a),
            final(self).acall_trace() == old(self).acall_trace(),
    {
        proof {
            use_type_invariant(&*self);
            lemma_released_span_wf(self@, span as int);
            lemma_released_span_backed(self.spans.map@, self.record, span as int);
        }
        self.spans.release(span, Ghost(self@));
    }
}

} // verus!
