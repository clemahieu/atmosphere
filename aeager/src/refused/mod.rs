// SPDX-License-Identifier: MIT

//! False claims for `aeager`. A pure function is its ensures at an output that ensures excludes.
//! A state change is the operation's ensures at an unchanged component, with the result this way.
//! `new_allocator`'s Ready ensures `Eager::new_ok`, so a Ready where `new_ok` is false fails it.
//! `new`, `reserve`, `back`, `release`, `release_span` and `exercise_eager` are the success way at
//! an unchanged component. `new`'s Some is an arbitrary source, not the empty span map and the
//! `pages` free frames `new` ensures. `reserve`'s Some meets neither `can_reserve` nor the reserved
//! view. `back`'s Some and `release` spend or return `pages` frames. `release_span`'s own ensures
//! keep the configuration, and the trait ensures the span leaves the view, which a caller of the
//! impl sees. `exercise_eager`'s Some fails the `new_ok` biconditional.
//! `invoke`'s `STATUS_OK` and `STATUS_AGAIN` are the same state-change claim: an unchanged
//! allocator does not extend the caller token's history or meet the call's contract. The
//! specification is the trait and the body is the module, so the refusal's body span is the
//! module's, which is the span the check joins to the clause. tools/check-refused.py runs each
//! module under cfg(refused), which nothing else sets, so the claims are in no image and no verify
//! count. design/refused-claim-per-way/.

pub mod back_some;
pub mod exercise_eager_some;
pub mod invoke_again;
pub mod invoke_ok;
pub mod new_allocator_ready;
pub mod new_some;
pub mod release_returns;
pub mod release_span_returns;
pub mod reserve_some;

use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

use acall::step::Caller;
use aheap::arch::PAGE_BYTES;
use aheap::source::SpanSource;

use crate::allocator::AllocatorInit;
use crate::eager::{Eager, TABLE_PAGES};
use crate::exercise::Exercised;
use crate::glue::{names_own_space, own_process, window_unclaimed};
use crate::invoke::{call_contract, call_keeps_source, GuardedCall};

use aheap::allocator::Allocator;
use verified::capability::operation::{status_only, Outcome, RETYPE_FRAME, RETYPE_LARGE_FRAME, STATUS_AGAIN, STATUS_OK};

verus! {

/// `new_allocator`'s Ready where `Eager::new_ok` is false. The requires are the operation's, and the
/// ensures is the Ready arm's `new_ok` clause.
pub trait NewAllocatorReady {
    proof fn wrong(
        caller: Tracked<Caller>,
        spares: usize,
        space: u64,
        untyped: u64,
        memory: u64,
        pages: usize,
        slots: u64,
        window: *mut u8,
        r: AllocatorInit,
    )
        requires
            caller@.wf(),
            caller@.pages_wf(),
            names_own_space(caller@, space),
            window_unclaimed(caller@, window@.addr),
            r is Ready,
            !Eager::new_ok(memory, pages, slots, window),
        ensures
            Eager::new_ok(memory, pages, slots, window),
    ;
}

/// `Eager::new`'s Some at an unchanged caller. The source `new` returns has an empty span map and
/// `pages` frames free; an arbitrary `Some` has neither.
pub trait NewSome {
    proof fn unchanged(
        old_caller: Tracked<Caller>,
        final_caller: Tracked<Caller>,
        space: u64,
        untyped: u64,
        memory: u64,
        pages: usize,
        slots: u64,
        window: *mut u8,
        r: Option<Eager>,
    )
        requires
            old_caller@.pages_wf(),
            window_unclaimed(old_caller@, window@.addr),
            final_caller@ == old_caller@,
            r is Some,
        ensures
            r->0@.spans.is_empty(),
            r->0.free_frames() == pages as nat,
    ;
}

/// `Eager::reserve`'s Some at an unchanged source and token. The requires are the trait's. The
/// ensures are the Some arm's `can_reserve` and the view the trait's Some arm establishes.
pub trait ReserveSome {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        blocks: usize,
        r: Option<*mut u8>,
    )
        requires
            old_self.serves(old_token@),
            old_self@.wf(),
            blocks > 0,
            final_self == old_self,
            final_token@ == old_token@,
            r is Some,
        ensures
            old_self.can_reserve(blocks as nat),
            final_self@ == old_self@.reserved(r->0@.addr as int, blocks as nat),
    ;
}

/// `Eager::back`'s Some at an unchanged source and token. The requires are the trait's. A grant
/// spends `pages` frames, so the free-frame equation fails when nothing changed.
pub trait BackSome {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        span: int,
        start: usize,
        pages: usize,
        r: Option<Tracked<PointsToRaw>>,
    )
        requires
            old_self.serves(old_token@),
            old_self@.wf(),
            old_self@.runs_in(span, start as int, pages as nat),
            old_self@.unbacked(span, start as int, pages as nat),
            pages > 0,
            final_self == old_self,
            final_token@ == old_token@,
            r is Some,
        ensures
            final_self.free_frames() + old_self.unlinked_tables_on(start as int, pages as nat) * TABLE_PAGES as nat + pages as nat == old_self.free_frames(),
    ;
}

/// `Eager::release` at an unchanged source and token. The requires are the trait's. Free capacity
/// and free frames rise by `pages`, so neither equality holds when nothing changed.
pub trait ReleaseReturns {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        span: int,
        start: usize,
        pages: usize,
        perm: Tracked<PointsToRaw>,
    )
        requires
            old_self.serves(old_token@),
            old_self@.wf(),
            old_self@.runs_in(span, start as int, pages as nat),
            old_self@.backed(span, start as int, pages as nat),
            perm@.is_range(start as int, pages * PAGE_BYTES),
            perm@.provenance() == old_self@.provenance,
            final_self == old_self,
            final_token@ == old_token@,
        ensures
            final_self.free_capacity() == old_self.free_capacity() + pages as int,
            final_self.free_frames() == old_self.free_frames() + pages as nat,
    ;
}

/// `Eager::release_span` at an unchanged source and token. The requires are the trait's. The
/// impl's ensures keep the configuration; the trait ensures the span leaves the view.
pub trait ReleaseSpanReturns {
    proof fn unchanged(
        old_self: Eager,
        final_self: Eager,
        old_token: Tracked<Caller>,
        final_token: Tracked<Caller>,
        span: usize,
    )
        requires
            old_self.serves(old_token@),
            old_self@.wf(),
            old_self@.spans.contains_key(span as int),
            old_self@.spans[span as int].backed.is_empty(),
            final_self == old_self,
            final_token@ == old_token@,
        ensures
            final_self@ == old_self@.released_span(span as int),
    ;
}

/// `exercise_eager`'s Some at an unchanged caller. The requires are the operation's. Some where
/// `new_ok` does not hold fails the biconditional.
pub trait ExerciseEagerSome {
    proof fn unchanged(
        old_caller: Tracked<Caller>,
        final_caller: Tracked<Caller>,
        space: u64,
        untyped: u64,
        memory: u64,
        pages: usize,
        slots: u64,
        window: *mut u8,
        seen: Option<Exercised>,
    )
        requires
            old_caller@.pages_wf(),
            window_unclaimed(old_caller@, window@.addr),
            old_caller@.wf(),
            own_process(old_caller@),
            names_own_space(old_caller@, space),
            final_caller@ == old_caller@,
            seen is Some,
        ensures
            seen is Some <==> Eager::new_ok(memory, pages, slots, window),
    ;
}

/// `invoke` returning `STATUS_OK` on an allowed `Retype` with an unchanged allocator.
pub trait InvokeOk {
    proof fn unchanged(old_alloc: Allocator<Eager>, final_alloc: Allocator<Eager>, untyped: u64, base: u64, word: u64, out: Outcome)
        requires
            old_alloc.held(),
            old_alloc.token() is Some,
            old_alloc.token()->0.wf(),
            old_alloc.token()->0.entry() == old_alloc.token()->0.kernel(),
            ({
                let call = GuardedCall::Retype { untyped, kind: RETYPE_FRAME, base, word, level: 0 };
                let pre = old_alloc.token()->0;
                &&& call_keeps_source(&old_alloc.src(), call)
                &&& pre.kernel().retype_allowed(pre.root(), RETYPE_FRAME, untyped as usize, base as usize, word, 0)
            }),
            final_alloc == old_alloc,
            out == status_only(STATUS_OK),
        ensures
            final_alloc.token()->0.history() == old_alloc.token()->0.history().push((final_alloc.token()->0.entry(), final_alloc.token()->0.kernel())),
            call_contract(final_alloc.token()->0.entry(), final_alloc.token()->0.kernel(), final_alloc.token()->0.root(), GuardedCall::Retype { untyped, kind: RETYPE_FRAME, base, word, level: 0 }, out),
    ;
}

/// `invoke` returning `STATUS_AGAIN` on an allowed `Retype` (`RETYPE_LARGE_FRAME`) with an unchanged allocator.
pub trait InvokeAgain {
    proof fn unchanged(old_alloc: Allocator<Eager>, final_alloc: Allocator<Eager>, untyped: u64, base: u64, word: u64, out: Outcome)
        requires
            old_alloc.held(),
            old_alloc.token() is Some,
            old_alloc.token()->0.wf(),
            old_alloc.token()->0.entry() == old_alloc.token()->0.kernel(),
            ({
                let call = GuardedCall::Retype { untyped, kind: RETYPE_LARGE_FRAME, base, word, level: 0 };
                let pre = old_alloc.token()->0;
                &&& call_keeps_source(&old_alloc.src(), call)
                &&& pre.kernel().retype_allowed(pre.root(), RETYPE_LARGE_FRAME, untyped as usize, base as usize, word, 0)
            }),
            final_alloc == old_alloc,
            out == status_only(STATUS_AGAIN),
        ensures
            final_alloc.token()->0.history() == old_alloc.token()->0.history().push((final_alloc.token()->0.entry(), final_alloc.token()->0.kernel())),
            call_contract(final_alloc.token()->0.entry(), final_alloc.token()->0.kernel(), final_alloc.token()->0.root(), GuardedCall::Retype { untyped, kind: RETYPE_LARGE_FRAME, base, word, level: 0 }, out),
    ;
}

} // verus!
