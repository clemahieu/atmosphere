//! The span source's witness: a verified sequence of its operations, built into no image, that reaches
//! the use the source exists for. From any well-formed source it reserves a span of one block, backs
//! its first page, writes a byte through the permission back returned and reads it again, releases
//! the page and the span, and ends with the view it started with. A source that refuses leaves the
//! view as it was, and the sequence stops there.
use vstd::prelude::*;
use vstd::layout::*;
use vstd::raw_ptr::*;
use vstd::set::*;

use crate::arch::*;
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
