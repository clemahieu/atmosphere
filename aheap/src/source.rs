//! The span source's contract: what the heap asks of whatever gives it address space and memory.
//!
//! A source hands out spans, block-aligned ranges of virtual addresses a whole number of blocks long,
//! and backs page runs inside them. Its view is the spans it has reserved, keyed by base address,
//! with the pages of each it has backed, the provenance every permission it returns carries, and the
//! count of the refusals it has made, so a caller's specification can say whether a call refused.
//!
//! - `reserve` gives a new span, unbacked and disjoint from every reserved one, or refuses, counts the
//!   refusal and changes nothing else.
//! - `back` takes a page run inside a reserved span with no page backed, and returns the permission
//!   to every byte of the run, the run now backed; or refuses, counts the refusal, backs nothing and
//!   changes nothing else.
//! - `release` takes a backed run with its permission and gives the run's frames up. It never
//!   refuses.
//! - `release_span` takes a span with no page backed and gives the range up. It never refuses.
//!
//! The permission is vstd's `PointsToRaw`. What it says about the kernel's map, that the run is
//! mapped readable and writable for this process, is trusted in each implementation of `back`, as
//! glue counted there; this crate trusts nothing.
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::set::*;

use crate::arch::*;

verus! {

/// One reserved span: its length in blocks and the addresses of the pages of it that are backed.
pub ghost struct Span {
    pub blocks: nat,
    pub backed: Set<int>,
}

/// What a source has handed out.
pub ghost struct SourceView {
    /// The provenance of every pointer and permission the source gives.
    pub provenance: Provenance,
    /// The reserved spans, by base address.
    pub spans: Map<int, Span>,
    /// The refusals `reserve` and `back` have made.
    pub refusals: nat,
}

/// The bytes of `blocks` blocks.
pub open spec fn span_bytes(blocks: nat) -> int {
    blocks * BLOCK_BYTES as int
}

/// The addresses of the pages of the run of `pages` pages from `start`.
pub open spec fn run_pages(start: int, pages: nat) -> Set<int> {
    Set::range(start, start + pages * PAGE_BYTES as int).filter(|a: int| a % PAGE_BYTES as int == 0)
}

impl SourceView {
    /// The span at `base` covers no address the span at `other` covers.
    pub open spec fn apart(self, base: int, blocks: nat, other: int) -> bool {
        base + span_bytes(blocks) <= other || other + span_bytes(self.spans[other].blocks) <= base
    }

    /// A span of `blocks` blocks at `base` lies in the address space, aligned to a block, above
    /// address 0, and apart from every reserved span.
    pub open spec fn fits(self, base: int, blocks: nat) -> bool {
        &&& blocks > 0
        &&& base > 0
        &&& base % BLOCK_BYTES as int == 0
        &&& base + span_bytes(blocks) <= usize::MAX as int + 1
        &&& forall|other: int| #[trigger] self.spans.contains_key(other) ==> self.apart(base, blocks, other)
    }

    /// Every span fits beside the others, and its backed pages are pages inside it.
    pub open spec fn wf(self) -> bool {
        &&& forall|base: int| #[trigger] self.spans.contains_key(base) ==> {
            &&& self.released_span(base).fits(base, self.spans[base].blocks)
            &&& forall|a: int| #[trigger] self.spans[base].backed.contains(a) ==> {
                &&& a % PAGE_BYTES as int == 0
                &&& base <= a < base + span_bytes(self.spans[base].blocks)
            }
        }
    }

    /// The run of `pages` pages from `start` is page-aligned, not empty, and inside the span at
    /// `span`.
    pub open spec fn runs_in(self, span: int, start: int, pages: nat) -> bool {
        &&& self.spans.contains_key(span)
        &&& pages > 0
        &&& start % PAGE_BYTES as int == 0
        &&& span <= start
        &&& start + pages * PAGE_BYTES as int <= span + span_bytes(self.spans[span].blocks)
    }

    /// No page of the run is backed.
    pub open spec fn unbacked(self, span: int, start: int, pages: nat) -> bool {
        self.spans[span].backed.disjoint(run_pages(start, pages))
    }

    /// Every page of the run is backed.
    pub open spec fn backed(self, span: int, start: int, pages: nat) -> bool {
        run_pages(start, pages).subset_of(self.spans[span].backed)
    }

    /// The view with a new span of `blocks` blocks at `base`, no page backed.
    pub open spec fn reserved(self, base: int, blocks: nat) -> Self {
        SourceView {
            spans: self.spans.insert(base, Span { blocks, backed: Set::empty() }),
            ..self
        }
    }

    /// The view with the run's pages backed.
    pub open spec fn backed_run(self, span: int, start: int, pages: nat) -> Self {
        SourceView {
            spans: self.spans.insert(
                span,
                Span { backed: self.spans[span].backed.union(run_pages(start, pages)), ..self.spans[span] },
            ),
            ..self
        }
    }

    /// The view with the run's pages no longer backed.
    pub open spec fn released_run(self, span: int, start: int, pages: nat) -> Self {
        SourceView {
            spans: self.spans.insert(
                span,
                Span { backed: self.spans[span].backed.difference(run_pages(start, pages)), ..self.spans[span] },
            ),
            ..self
        }
    }

    /// The view without the span at `span`.
    pub open spec fn released_span(self, span: int) -> Self {
        SourceView { spans: self.spans.remove(span), ..self }
    }

    /// The view with one more refusal counted and nothing else changed.
    pub open spec fn refused(self) -> Self {
        SourceView { refusals: self.refusals + 1, ..self }
    }
}

/// Each change a source's success makes keeps the view well formed, so an implementation's
/// `final(self)@.wf()` follows from the change it states.
pub proof fn lemma_reserved_wf(v: SourceView, base: int, blocks: nat)
    requires
        v.wf(),
        v.fits(base, blocks),
    ensures
        v.reserved(base, blocks).wf(),
{
    let w = v.reserved(base, blocks);
    if v.spans.contains_key(base) {
        assert(v.apart(base, blocks, base));
        assert(v.released_span(base).fits(base, v.spans[base].blocks));
    }
    assert forall|b: int| #[trigger] w.spans.contains_key(b) implies w.released_span(b).fits(b, w.spans[b].blocks) by {
        if b != base {
            assert(v.released_span(b).fits(b, v.spans[b].blocks));
            assert(v.apart(base, blocks, b));
            assert forall|o: int| #[trigger] w.released_span(b).spans.contains_key(o) implies w.released_span(b).apart(b, w.spans[b].blocks, o) by {
                if o != base {
                    assert(v.released_span(b).spans.contains_key(o));
                }
            }
        } else {
            assert(w.released_span(b).spans =~= v.spans);
        }
    }
}

pub proof fn lemma_backed_run_wf(v: SourceView, span: int, start: int, pages: nat)
    requires
        v.wf(),
        v.runs_in(span, start, pages),
    ensures
        v.backed_run(span, start, pages).wf(),
{
    let w = v.backed_run(span, start, pages);
    assert forall|b: int| #[trigger] w.spans.contains_key(b) implies w.released_span(b).fits(b, w.spans[b].blocks) by {
        assert(v.released_span(b).fits(b, v.spans[b].blocks));
        assert forall|o: int| #[trigger] w.released_span(b).spans.contains_key(o) implies w.released_span(b).apart(b, w.spans[b].blocks, o) by {
            assert(v.released_span(b).spans.contains_key(o));
        }
    }
}

pub proof fn lemma_released_run_wf(v: SourceView, span: int, start: int, pages: nat)
    requires
        v.wf(),
        v.spans.contains_key(span),
    ensures
        v.released_run(span, start, pages).wf(),
{
    let w = v.released_run(span, start, pages);
    assert forall|b: int| #[trigger] w.spans.contains_key(b) implies w.released_span(b).fits(b, w.spans[b].blocks) by {
        assert(v.released_span(b).fits(b, v.spans[b].blocks));
        assert forall|o: int| #[trigger] w.released_span(b).spans.contains_key(o) implies w.released_span(b).apart(b, w.spans[b].blocks, o) by {
            assert(v.released_span(b).spans.contains_key(o));
        }
    }
}

pub proof fn lemma_released_span_wf(v: SourceView, span: int)
    requires
        v.wf(),
    ensures
        v.released_span(span).wf(),
{
    let w = v.released_span(span);
    assert forall|b: int| #[trigger] w.spans.contains_key(b) implies w.released_span(b).fits(b, w.spans[b].blocks) by {
        assert(v.released_span(b).fits(b, v.spans[b].blocks));
        assert forall|o: int| #[trigger] w.released_span(b).spans.contains_key(o) implies w.released_span(b).apart(b, w.spans[b].blocks, o) by {
            assert(v.released_span(b).spans.contains_key(o));
        }
    }
}

pub proof fn lemma_refused_wf(v: SourceView)
    requires
        v.wf(),
    ensures
        v.refused().wf(),
{
    let w = v.refused();
    assert forall|b: int| #[trigger] w.spans.contains_key(b) implies w.released_span(b).fits(b, w.spans[b].blocks) by {
        assert(v.released_span(b).fits(b, v.spans[b].blocks));
        assert forall|o: int| #[trigger] w.released_span(b).spans.contains_key(o) implies w.released_span(b).apart(b, w.spans[b].blocks, o) by {
            assert(v.released_span(b).spans.contains_key(o));
        }
    }
}

/// Gives the heap spans of address space and backs page runs in them.
pub trait SpanSource {
    spec fn view(&self) -> SourceView;

    /// Reserves a span of `blocks` blocks, none of it backed, at the base the returned pointer
    /// addresses; or refuses, counts the refusal and changes nothing else.
    fn reserve(&mut self, blocks: usize) -> (r: Option<*mut u8>)
        requires
            old(self)@.wf(),
            blocks > 0,
        ensures
            final(self)@.wf(),
            match r {
                None => final(self)@ == old(self)@.refused(),
                Some(base) => {
                    &&& base@.provenance == old(self)@.provenance
                    &&& old(self)@.fits(base@.addr as int, blocks as nat)
                    &&& final(self)@ == old(self)@.reserved(base@.addr as int, blocks as nat)
                },
            },
    ;

    /// Backs the run of `pages` pages from `start` inside the span at `span`, and returns the
    /// permission to exactly its bytes; or refuses, counts the refusal, backs nothing and changes
    /// nothing else.
    fn back(&mut self, span: Ghost<int>, start: usize, pages: usize) -> (r: Option<Tracked<PointsToRaw>>)
        requires
            old(self)@.wf(),
            old(self)@.runs_in(span@, start as int, pages as nat),
            old(self)@.unbacked(span@, start as int, pages as nat),
        ensures
            final(self)@.wf(),
            match r {
                None => final(self)@ == old(self)@.refused(),
                Some(perm) => {
                    &&& perm@.is_range(start as int, pages * PAGE_BYTES)
                    &&& perm@.provenance() == old(self)@.provenance
                    &&& final(self)@ == old(self)@.backed_run(span@, start as int, pages as nat)
                },
            },
    ;

    /// Gives up the frames of the backed run of `pages` pages from `start` in the span at `span`,
    /// taking the permission to its bytes.
    fn release(&mut self, span: Ghost<int>, start: usize, pages: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self)@.wf(),
            old(self)@.runs_in(span@, start as int, pages as nat),
            old(self)@.backed(span@, start as int, pages as nat),
            perm@.is_range(start as int, pages * PAGE_BYTES),
            perm@.provenance() == old(self)@.provenance,
        ensures
            final(self)@.wf(),
            final(self)@ == old(self)@.released_run(span@, start as int, pages as nat),
    ;

    /// Gives up the span at `span`, which has no page backed.
    fn release_span(&mut self, span: usize)
        requires
            old(self)@.wf(),
            old(self)@.spans.contains_key(span as int),
            old(self)@.spans[span as int].backed.is_empty(),
        ensures
            final(self)@.wf(),
            final(self)@ == old(self)@.released_span(span as int),
    ;
}

} // verus!
