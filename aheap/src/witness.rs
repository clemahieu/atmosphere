//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! span source and the block buddy exist for.
//!
//! The span source's witness, from any well-formed source, reserves a span of one block, backs
//! its first page, writes a byte through the permission back returned and reads it again, releases
//! the page and the span, and ends with the view it started with. A source that refuses leaves the
//! view as it was with the refusal counted, and the sequence stops there.
//!
//! The page buddy's witness, over any well-formed source and with no spares, cuts a run of order 0
//! and one of order BLOCK_ORDER, frees both, and ends holding no span, with the source's view the one
//! it started with. A refusal stops the sequence after freeing what it cut, and the page buddy refuses
//! only when the source did, so a source that refused nothing during the sequence gave both runs. Its
//! second witness, with
//! one spare, cuts a run, frees it so its span stays as the spare, and cuts again, which is shown to
//! succeed whatever the source does.
//!
//! The backed run's witness, over any well-formed source and with no spares, cuts a run of order 0,
//! backs it, writes a byte through the permission and reads it again, releases the run's page and
//! frees the run, ending as the page buddy's witness does: a source that refused nothing gave the
//! byte.
use vstd::prelude::*;
use vstd::layout::*;
use vstd::raw_ptr::*;
use vstd::set::*;

use crate::arch::*;
use crate::buddy::*;
use crate::page::*;
use crate::source::*;

verus! {

broadcast use group_raw_ptr_axioms;

/// Writes and reads one byte of a span `src` backs, and gives the span back. Returns whether the
/// byte was written: false when the source refused to reserve or to back, which it did once.
pub fn witness_one_page<S: SpanSource>(src: &mut S) -> (wrote: bool)
    requires
        old(src)@.wf(),
    ensures
        final(src)@ == if wrote {
            old(src)@
        } else {
            old(src)@.refused()
        },
{
    let ghost start = src@;
    let base = match src.reserve(1) {
        None => return false,
        Some(base) => base,
    };
    let addr = base.addr();
    let ghost reserved = src@;
    assert(!start.spans.contains_key(addr as int));
    let perm = match src.back(Ghost(addr as int), addr, 1) {
        None => {
            src.release_span(addr);
            assert(src@.spans =~= start.spans);
            assert(src@ == start.refused());
            return false;
        },
        Some(perm) => perm,
    };
    let tracked run = perm.get();
    let ghost page = Set::range(addr as int, addr as int + PAGE_BYTES as int);
    let ghost first = Set::range(addr as int, addr as int + 1);
    let tracked (one, rest) = run.split(first);
    assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
        broadcast use layout_of_primitives, align_of_u8;
    }
    assert(one.is_range(addr as int, size_of::<u8>() as int));
    let tracked mut byte = one.into_typed::<u8>(addr);
    ptr_mut_write(base, Tracked(&mut byte), 7u8);
    let v = ptr_mut_read(base, Tracked(&mut byte));
    assert(v == 7u8);
    let tracked raw = byte.into_raw();
    let tracked whole = raw.join(rest);
    assert(whole.dom() =~= page);
    src.release(Ghost(addr as int), addr, 1, Tracked(whole));
    assert(src@.spans[addr as int].backed =~= Set::empty());
    assert(src@.spans =~= reserved.spans);
    src.release_span(addr);
    assert(src@.spans =~= start.spans);
    true
}

} // verus!

verus! {

/// The block buddy's witness: from the initial value it cuts a run of order 0 and frees it, takes
/// the whole block, is refused a run of order 0 while the block is taken, frees the block, and ends
/// with the initial view.
pub fn witness_block_buddy() -> (b: BlockBuddy)
    ensures
        b.wf(),
        b.blocks() == initial(),
{
    let mut b = BlockBuddy::new();
    assert(b.blocks().contains_key(0) && b.blocks()[0].free);
    assert(b.used() =~= Map::<int, nat>::empty());
    let small = b.alloc(0);
    let p = small.unwrap();
    assert(b.used() =~= Map::<int, nat>::empty().insert(p as int, 0nat));
    b.free(p);
    assert(b.used().dom() =~= Set::<int>::empty());
    proof {
        b.lemma_idle();
        lemma_block_pages();
    }
    assert(b.blocks().contains_key(0) && b.blocks()[0].free);
    let whole = b.alloc(BLOCK_ORDER).unwrap();
    assert(whole == 0);
    assert(b.used().contains_key(0) && b.used()[0] == BLOCK_ORDER as nat);
    assert(b.blocks().contains_key(0) && !b.blocks()[0].free && b.blocks()[0].order
        == BLOCK_ORDER);
    proof {
        b.lemma_view();
    }
    assert(!b.fits(0)) by {
        if b.fits(0) {
            let h = choose|h: int|
                #[trigger] b.blocks().contains_key(h) && b.blocks()[h].free && b.blocks()[h].order
                    >= 0;
            lemma_pages(b.blocks()[h].order, BLOCK_ORDER as nat);
            assert(placed(h, b.blocks()[h]));
            assert(h != 0);
            assert(h + pages(b.blocks()[h].order) <= 0 || 0 + pages(b.blocks()[0].order) <= h);
        }
    }
    let refused = b.alloc(0);
    assert(refused is None);
    b.free(whole);
    assert(b.used().dom() =~= Set::<int>::empty());
    proof {
        b.lemma_idle();
    }
    let idle = b.is_idle();
    assert(idle);
    b
}

} // verus!

verus! {

/// Reserving a span and giving it back leaves the view as it was.
proof fn lemma_reserved_released(s: SourceView, b: int)
    requires
        !s.spans.contains_key(b),
    ensures
        s.reserved(b, 1).released_span(b) == s,
{
    assert(s.reserved(b, 1).released_span(b).spans =~= s.spans);
}

/// Taking the metadata span, backing its page and taking a run span, then giving them back in the
/// order free_run does, leaves the view as it was.
proof fn lemma_meta_round_trip(s: SourceView, m: int, b: int)
    requires
        !s.spans.contains_key(m),
        !s.spans.contains_key(b),
        m != b,
    ensures
        s.reserved(m, 1).backed_run(m, m, 1).reserved(b, 1).released_span(b).released_run(m, m, 1).released_span(m) == s,
{
    let t = s.reserved(m, 1).backed_run(m, m, 1);
    lemma_reserved_released(t, b);
    assert(t.released_run(m, m, 1).released_span(m).spans =~= s.spans);
}

/// Cuts a small run and a whole block from a page buddy over `src` keeping no spare, frees both, and
/// returns the page buddy, which then holds no span and has given every span back to the source, with
/// whether both runs were cut: they were exactly when the source refused nothing, and otherwise it
/// refused once.
pub fn witness_page_buddy<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, bool))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        r.0.meta() is None,
        r.0.source() == if r.1 {
            src@
        } else {
            src@.refused()
        },
        r.1 == (r.0.source().refusals == src@.refusals),
{
    let mut pb = PageBuddy::new(src, 0);
    let ghost s0 = pb.source();
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let small = match pb.alloc_run(0) {
        Err(_) => {
            proof {
                pb.lemma_view();
            }
            return (pb, false);
        },
        Ok(p) => p,
    };
    let ghost b1 = span_of(small as int);
    let ghost h1 = page_of(small as int);
    let ghost one = Map::<int, nat>::empty().insert(h1, 0nat);
    assert(pb.used() == Map::<int, Map<int, nat>>::empty().insert(b1, one));
    assert(one.remove(h1) =~= Map::<int, nat>::empty());
    let ghost u1 = pb.used();
    let ghost s1 = pb.source();
    let ghost m1 = pb.meta();
    let ghost spans1 = pb.spans();
    proof {
        pb.lemma_view();
        let ma = m1->Some_0;
        assert(s1 == s0.reserved(ma, 1).backed_run(ma, ma, 1).reserved(b1, 1));
        assert(spans1.dom() =~= set![b1]);
        assert(u1.remove(b1).dom() =~= Set::<int>::empty());
        lemma_meta_round_trip(s0, ma, b1);
        lemma_meta_round_trip(s0.refused(), ma, b1);
        assert(s1.refused() == s0.refused().reserved(ma, 1).backed_run(ma, ma, 1).reserved(b1, 1));
        assert(spans1.dom().len() == 1);
    }
    let whole = match pb.alloc_run(BLOCK_ORDER) {
        Err(_) => {
            pb.free_run(small);
            assert(pb.used().dom() =~= Set::<int>::empty());
            proof {
                pb.lemma_view();
            }
            return (pb, false);
        },
        Ok(p) => p,
    };
    let ghost b2 = span_of(whole as int);
    let ghost h2 = page_of(whole as int);
    proof {
        lemma_block_pages();
        if b2 == b1 {
            assert(u1[b2].contains_key(h1));
            assert(placed(h1, Block { order: 0, free: false }));
            assert(h2 + pages(BLOCK_ORDER as nat) <= h1 || h1 + pages(0) <= h2);
        }
    }
    let ghost u2 = pb.used();
    let ghost whole_run = Map::<int, nat>::empty().insert(h2, BLOCK_ORDER as nat);
    assert(u2 == Map::<int, Map<int, nat>>::empty().insert(b1, one).insert(b2, whole_run));
    assert(whole_run.remove(h2) =~= Map::<int, nat>::empty());
    proof {
        assert(b2 != b1);
        assert(!spans1.contains_key(b2));
        assert(pb.source() == s1.reserved(b2, 1));
        assert(pb.meta() == m1);
        lemma_reserved_released(s1, b2);
        assert(u2.remove(b2).contains_key(b1));
        assert(u2.remove(b2).dom() != Set::<int>::empty());
    }
    pb.free_run(whole);
    assert(pb.used() =~= Map::<int, Map<int, nat>>::empty().insert(b1, one));
    assert(pb.source() == s1);
    assert(pb.used().remove(b1).dom() =~= Set::<int>::empty());
    pb.free_run(small);
    assert(pb.used().dom() =~= Set::<int>::empty());
    proof {
        pb.lemma_view();
    }
    (pb, true)
}

/// Cuts a run from a page buddy over `src` keeping one spare, frees it, so its span stays as the
/// spare, and cuts a run again, which the idle spare provably gives without asking the source; then
/// frees that run and returns the page buddy, every held span of it idle.
pub fn witness_page_buddy_spare<S: SpanSource>(src: S) -> (pb: PageBuddy<S>)
    requires
        src@.wf(),
    ensures
        pb.wf(),
        pb.spares() == 1,
        forall|b: int| #[trigger] pb.used().contains_key(b) ==> pb.used()[b].dom() == Set::<int>::empty(),
{
    let mut pb = PageBuddy::new(src, 1);
    let first = match pb.alloc_run(0) {
        Err(_) => {
            assert(pb.used().dom() =~= Set::<int>::empty());
            return pb;
        },
        Ok(p) => p,
    };
    let ghost b1 = span_of(first as int);
    let ghost h1 = page_of(first as int);
    let ghost one = Map::<int, nat>::empty().insert(h1, 0nat);
    assert(pb.used() == Map::<int, Map<int, nat>>::empty().insert(b1, one));
    assert(one.remove(h1) =~= Map::<int, nat>::empty());
    assert(pb.idle_spans() =~= Set::<int>::empty()) by {
        assert(pb.used()[b1].contains_key(h1));
    }
    pb.free_run(first);
    let ghost spare = Map::<int, Map<int, nat>>::empty().insert(b1, Map::<int, nat>::empty());
    assert(pb.used() =~= spare);
    proof {
        pb.lemma_view();
        pb.lemma_idle_fits(b1, 0);
    }
    let again = pb.alloc_run(0);
    assert(again is Ok);
    let second = match again {
        Ok(p) => p,
        Err(_) => return pb,
    };
    assert(span_of(second as int) == b1);
    let ghost h2 = page_of(second as int);
    let ghost two = Map::<int, nat>::empty().insert(h2, 0nat);
    assert(pb.used() == spare.insert(b1, two));
    assert(two.remove(h2) =~= Map::<int, nat>::empty());
    assert(pb.idle_spans() =~= Set::<int>::empty()) by {
        assert(pb.used()[b1].contains_key(h2));
    }
    pb.free_run(second);
    assert(pb.used() =~= spare);
    pb
}

/// Cuts a run of order 0 from a page buddy over `src` keeping no spare, backs it, writes a byte
/// through the permission and reads it again, releases the run's page and frees the run, and returns
/// the page buddy, which then holds no span and has given every span back to the source, with
/// whether the byte was written: it was exactly when the source refused nothing, and otherwise it
/// refused once.
pub fn witness_backed_run<S: SpanSource>(src: S) -> (r: (PageBuddy<S>, bool))
    requires
        src@.wf(),
    ensures
        r.0.wf(),
        r.0.spans().dom() == Set::<int>::empty(),
        r.0.meta() is None,
        r.0.source() == if r.1 {
            src@
        } else {
            src@.refused()
        },
        r.1 == (r.0.source().refusals == src@.refusals),
{
    let mut pb = PageBuddy::new(src, 0);
    let ghost s0 = pb.source();
    assert(pb.spans().dom() =~= Set::<int>::empty());
    let p = match pb.alloc_run(0) {
        Err(_) => {
            proof {
                pb.lemma_view();
            }
            return (pb, false);
        },
        Ok(p) => p,
    };
    let ghost b = span_of(p as int);
    let ghost h = page_of(p as int);
    let ghost one = Map::<int, nat>::empty().insert(h, 0nat);
    assert(pb.used() == Map::<int, Map<int, nat>>::empty().insert(b, one));
    assert(one.remove(h) =~= Map::<int, nat>::empty());
    let ghost s1 = pb.source();
    proof {
        pb.lemma_view();
        let ma = pb.meta()->Some_0;
        assert(s1 == s0.reserved(ma, 1).backed_run(ma, ma, 1).reserved(b, 1));
        assert(pb.used().remove(b).dom() =~= Set::<int>::empty());
        lemma_meta_round_trip(s0, ma, b);
        lemma_meta_round_trip(s0.refused(), ma, b);
        assert(s1.refused() == s0.refused().reserved(ma, 1).backed_run(ma, ma, 1).reserved(b, 1));
        assert(pages(0) == 1);
    }
    let (ptr, perm) = match pb.back_run(p, 0) {
        None => {
            pb.free_run(p);
            assert(pb.used().dom() =~= Set::<int>::empty());
            proof {
                pb.lemma_view();
            }
            return (pb, false);
        },
        Some(backed) => backed,
    };
    let tracked run = perm.get();
    let ghost first = Set::range(p as int, p as int + 1);
    let tracked (one_byte, rest) = run.split(first);
    assert(size_of::<u8>() == 1 && align_of::<u8>() == 1) by {
        broadcast use layout_of_primitives, align_of_u8;
    }
    assert(one_byte.is_range(p as int, size_of::<u8>() as int));
    let tracked mut byte = one_byte.into_typed::<u8>(p);
    ptr_mut_write(ptr, Tracked(&mut byte), 7u8);
    let v = ptr_mut_read(ptr, Tracked(&mut byte));
    assert(v == 7u8);
    let tracked raw = byte.into_raw();
    let tracked whole = raw.join(rest);
    assert(whole.dom() =~= Set::range(p as int, p as int + PAGE_BYTES as int));
    pb.release_run(p, 0, Tracked(whole));
    assert(pb.source().spans[b].backed =~= Set::<int>::empty());
    assert(pb.source().spans =~= s1.spans);
    pb.free_run(p);
    assert(pb.used().dom() =~= Set::<int>::empty());
    proof {
        pb.lemma_view();
    }
    (pb, true)
}

} // verus!
