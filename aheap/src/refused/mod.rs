// SPDX-License-Identifier: MIT

//! False claims for the heap allocator. A pure function is its ensures at an output that ensures
//! excludes. A query is the ensures at the other result from the state that gives one. A state
//! change is the operation's ensures at an unchanged component, with the result this way.
//! `Allocator::source` returns the source it holds, so a reference that is not that source fails
//! its ensures. The specification is the trait and the body is the module, so the refusal's body
//! span is the module's, which is the span the check joins to the clause. tools/check-refused.py
//! runs each module under cfg(refused), which nothing else sets, so the claims are in no image
//! and no verify count. design/refused-claim-per-way/.

pub mod alloc_some;
pub mod allocator_new;
pub mod free_returns;
pub mod give_back;
pub mod has_token_true;
pub mod heap_alloc_some;
pub mod heap_free;
pub mod heap_new;
pub mod layout_fits_true;
pub mod lend_some;
pub mod source_returns;

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use crate::allocator::Allocator;
use crate::arch::PAGE_BYTES;
use crate::class::class_size;
use crate::heap::{class_for, large_layout, run_layout, slot_alloc, small_layout, Heap};
use crate::large::pages_for;
use crate::source::SpanSource;

verus! {

/// `layout_fits` at a bool that is not the layout disjunction it ensures.
pub trait LayoutFitsTrue {
    proof fn wrong(size: usize, align: usize, r: bool)
        ensures
            r != (small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(size as nat, align as nat)),
    ;
}

/// `Heap::new` at a heap whose spares or live set the ensures excludes.
pub trait HeapNewReturns {
    proof fn wrong(spares: usize, r: Heap)
        ensures
            r.spares() != spares,
            r.live() != ISet::<int>::empty(),
    ;
}

/// `Allocator::new` at an allocator that does not hold the token it was given. The requires are the
/// operation's.
pub trait AllocatorNewReturns {
    proof fn wrong<S: SpanSource>(spares: usize, src: S, token: Tracked<S::Token>, r: Allocator<S>)
        requires
            src@.wf(),
            src.serves(token@),
        ensures
            !r.held(),
            r.token() != Some(token@),
    ;
}

/// `Allocator::has_token`'s true at an allocator that holds its token, claimed false.
pub trait HasTokenTrue {
    proof fn wrong<S: SpanSource>(alloc: &Allocator<S>, r: bool)
        requires
            alloc.held(),
            !r,
        ensures
            r == alloc.held(),
    ;
}

/// `Allocator::alloc`'s Some at an unchanged allocator that holds its token, for a small layout.
/// The ensures is that arm of the operation, `slot_alloc`.
pub trait AllocSome {
    proof fn unchanged<S: SpanSource>(
        old_self: Allocator<S>,
        final_self: Allocator<S>,
        size: usize,
        align: usize,
        r: Option<(*mut u8, Tracked<PointsToRaw>)>,
    )
        requires
            old_self.held(),
            small_layout(size as nat, align as nat),
            final_self == old_self,
            r is Some,
        ensures
            old_self.held() && small_layout(size as nat, align as nat) ==> slot_alloc(old_self.heap(), final_self.heap(), old_self.src_view(), final_self.src_view(), size as nat, align as nat, r),
    ;
}

/// `Allocator::free` at an unchanged allocator. The live set still contains the address the ensures
/// removes. The requires are the operation's.
pub trait FreeReturns {
    proof fn unchanged<S: SpanSource>(
        old_self: Allocator<S>,
        final_self: Allocator<S>,
        p: *mut u8,
        size: usize,
        align: usize,
        perm: Tracked<PointsToRaw>,
    )
        requires
            old_self.held(),
            small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(size as nat, align as nat),
            small_layout(size as nat, align as nat) ==> {
                &&& (class_for(size as nat, align as nat) as int) < old_self.heap().classes().len()
                &&& old_self.heap().classes()[class_for(size as nat, align as nat) as int].live().contains(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, class_size(class_for(size as nat, align as nat)) as int)
            },
            run_layout(size as nat, align as nat) ==> {
                &&& old_self.heap().parts().contains_key(p@.addr as int)
                &&& old_self.heap().parts()[p@.addr as int] == pages_for(size as nat)
                &&& perm@.is_range(p@.addr as int, pages_for(size as nat) * PAGE_BYTES)
            },
            large_layout(size as nat, align as nat) ==> {
                &&& old_self.heap().large().contains_key(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, old_self.heap().large()[p@.addr as int] * PAGE_BYTES)
            },
            perm@.provenance() == old_self.src_view().provenance,
            final_self == old_self,
        ensures
            final_self.live() == old_self.live().remove(p@.addr as int),
    ;
}

/// `Allocator::lend`'s Some at an unchanged allocator. The ensures gives the token up.
pub trait LendSome {
    proof fn unchanged<S: SpanSource>(old_self: Allocator<S>, final_self: Allocator<S>, r: Option<Tracked<S::Token>>)
        requires
            final_self == old_self,
            r is Some,
        ensures
            !final_self.held(),
            final_self.token() is None,
    ;
}

/// `Allocator::give_back` at an unchanged allocator. The ensures holds the token that was given.
pub trait GiveBackReturns {
    proof fn unchanged<S: SpanSource>(old_self: Allocator<S>, final_self: Allocator<S>, token: Tracked<S::Token>)
        requires
            old_self.src_serves(token@),
            final_self == old_self,
        ensures
            final_self.held(),
            final_self.token() == Some(token@),
    ;
}

/// `Heap::alloc`'s Some at an unchanged heap and source, for a small layout. The ensures is that
/// arm of the operation, `slot_alloc`.
pub trait HeapAllocSome {
    proof fn unchanged<S: SpanSource>(
        old_self: Heap,
        final_self: Heap,
        old_src: S,
        final_src: S,
        old_token: Tracked<S::Token>,
        final_token: Tracked<S::Token>,
        size: usize,
        align: usize,
        r: Option<(*mut u8, Tracked<PointsToRaw>)>,
    )
        requires
            old_src.serves(old_token@),
            old_self.wf(old_src@),
            small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(size as nat, align as nat),
            small_layout(size as nat, align as nat),
            final_self == old_self,
            final_src == old_src,
            final_token@ == old_token@,
            r is Some,
        ensures
            small_layout(size as nat, align as nat) ==> slot_alloc(old_self, final_self, old_src@, final_src@, size as nat, align as nat, r),
    ;
}

/// `Heap::free` at an unchanged heap and source. The live set still contains the address the
/// ensures removes. The requires are the operation's.
pub trait HeapFreeReturns {
    proof fn unchanged<S: SpanSource>(
        old_self: Heap,
        final_self: Heap,
        old_src: S,
        final_src: S,
        old_token: Tracked<S::Token>,
        final_token: Tracked<S::Token>,
        p: *mut u8,
        size: usize,
        align: usize,
        perm: Tracked<PointsToRaw>,
    )
        requires
            old_src.serves(old_token@),
            old_self.wf(old_src@),
            small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(size as nat, align as nat),
            small_layout(size as nat, align as nat) ==> {
                &&& old_self.classes()[class_for(size as nat, align as nat) as int].live().contains(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, class_size(class_for(size as nat, align as nat)) as int)
            },
            run_layout(size as nat, align as nat) ==> {
                &&& old_self.parts().contains_key(p@.addr as int)
                &&& old_self.parts()[p@.addr as int] == pages_for(size as nat)
                &&& perm@.is_range(p@.addr as int, pages_for(size as nat) * PAGE_BYTES)
            },
            large_layout(size as nat, align as nat) ==> {
                &&& old_self.large().contains_key(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, old_self.large()[p@.addr as int] * PAGE_BYTES)
            },
            perm@.provenance() == old_src@.provenance,
            final_self == old_self,
            final_src == old_src,
            final_token@ == old_token@,
        ensures
            final_self.live() == old_self.live().remove(p@.addr as int),
    ;
}

/// `Allocator::source` at a reference that is not the source it holds.
pub trait SourceReturns {
    proof fn wrong<S: SpanSource>(alloc: &Allocator<S>, r: &S)
        ensures
            *r != alloc.src(),
    ;
}

} // verus!
