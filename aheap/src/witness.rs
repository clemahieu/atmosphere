//! The witnesses: verified sequences of operations, built into no image, that reach the uses the
//! span source and the block buddy exist for.
//!
//! The span source's witness, from any well-formed source, reserves a span of one block, backs
//! its first page, writes a byte through the permission back returned and reads it again, releases
//! the page and the span, and ends with the view it started with. A source that refuses leaves the
//! view as it was, and the sequence stops there.
//!
//! The page buddy's witness, over any well-formed source and with no spares, cuts a run of order 0
//! and one of order BLOCK_ORDER, frees both, and ends holding no span. A refusal stops the sequence
//! after freeing what it cut.
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
/// byte was written: false when the source refused to reserve or to back.
pub fn witness_one_page<S: SpanSource>(src: &mut S) -> (wrote: bool)
    requires
        old(src)@.wf(),
    ensures
        final(src)@ == old(src)@,
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

/// Cuts a small run and a whole block from a page buddy over `src` keeping no spare, frees both, and
/// returns the page buddy, which then holds no span.
pub fn witness_page_buddy<S: SpanSource>(src: S) -> (pb: PageBuddy<S>)
    requires
        src@.wf(),
    ensures
        pb.wf(),
        pb.spans().dom() == Set::<int>::empty(),
        pb.meta() is None,
{
    let mut pb = PageBuddy::new(src, 0);
    let small = match pb.alloc_run(0) {
        Err(_) => {
            proof {
                pb.lemma_view();
            }
            return pb;
        },
        Ok(p) => p,
    };
    let ghost b1 = span_of(small as int);
    let ghost h1 = page_of(small as int);
    let ghost one = Map::<int, nat>::empty().insert(h1, 0nat);
    assert(pb.used() == Map::<int, Map<int, nat>>::empty().insert(b1, one));
    assert(one.remove(h1) =~= Map::<int, nat>::empty());
    let ghost u1 = pb.used();
    let whole = match pb.alloc_run(BLOCK_ORDER) {
        Err(_) => {
            pb.free_run(small);
            assert(pb.used().dom() =~= Set::<int>::empty());
            proof {
                pb.lemma_view();
            }
            return pb;
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
    pb.free_run(whole);
    assert(pb.used() =~= Map::<int, Map<int, nat>>::empty().insert(b1, one));
    pb.free_run(small);
    assert(pb.used().dom() =~= Set::<int>::empty());
    proof {
        pb.lemma_view();
    }
    pb
}

} // verus!
