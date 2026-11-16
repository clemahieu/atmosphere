// SPDX-License-Identifier: MIT

//! Combined construction of an eager span source and a heap allocator over it.

use vstd::prelude::*;

use acall::step::Caller;
use aheap::allocator::Allocator;
#[cfg(verus_keep_ghost)]
use aheap::source::{Refusal, Request, SpanSource};

use crate::eager::Eager;
#[cfg(verus_keep_ghost)]
use crate::glue::{names_own_space, window_unclaimed};

verus! {

/// Outcome of creating an `Allocator<Eager>` while preserving ownership of the caller token if the
/// source's configuration is refused.
pub enum AllocatorInit {
    Ready(Allocator<Eager>),
    Refused(Tracked<Caller>),
}

/// Packs a validated `Eager` source and caller token into `AllocatorInit::Ready` in its own frame
/// so `new_allocator` does not reserve the allocator storage while `Eager::new` is running.
#[inline(never)]
fn finish_allocator(spares: usize, eager: Eager, caller: Tracked<Caller>) -> (r: AllocatorInit)
    requires
        eager@.wf(),
        caller@.wf(),
        caller@.kernel().sealed(caller@.root()),
        caller@.kernel().processes.records@.contains_key(caller@.root()),
        names_own_space(caller@, eager.space()),
        eager.holds(caller@),
        eager.serves(caller@),
    ensures
        match r {
            AllocatorInit::Ready(alloc) => {
                &&& alloc.held()
                &&& alloc.token() == Some(caller@)
                &&& alloc.spares() == spares as nat
                &&& alloc.live() == ISet::<int>::empty()
                &&& alloc.src() == eager
                &&& alloc.src_view() == eager@
            },
            AllocatorInit::Refused(_) => false,
        },
{
    AllocatorInit::Ready(Allocator::new(spares, eager, caller))
}

/// Constructs an `Eager` span source over `(space, untyped, memory, pages, slots, window)` and
/// bundles it with an empty `Heap` of `spares` spare blocks and `caller` into an `Allocator`, or
/// returns `caller` untouched if `Eager::new` refuses the parameters.
pub fn new_allocator(
    mut caller: Tracked<Caller>,
    spares: usize,
    space: u64,
    untyped: u64,
    memory: u64,
    pages: usize,
    slots: u64,
    window: *mut u8,
) -> (r: AllocatorInit)
    requires
        caller@.wf(),
        caller@.pages_wf(),
        names_own_space(caller@, space),
        window_unclaimed(caller@, window@.addr),
    ensures
        match r {
            AllocatorInit::Ready(alloc) => {
                &&& Eager::new_ok(memory, pages, slots, window)
                &&& alloc.held()
                &&& alloc.token() is Some
                &&& alloc.token()->0.kernel() == caller@.kernel()
                &&& alloc.token()->0.entry() == caller@.entry()
                &&& alloc.token()->0.root() == caller@.root()
                &&& alloc.token()->0.history() == caller@.history()
                &&& alloc.token()->0.start() == caller@.start()
                &&& alloc.token()->0.pages_id() == caller@.pages_id()
                &&& alloc.token()->0.pages_wf()
                &&& alloc.spares() == spares as nat
                &&& alloc.live() == ISet::<int>::empty()
                &&& alloc.src_view().wf()
                &&& alloc.src().space() == space
                &&& alloc.src().untyped() == untyped
                &&& alloc.src().memory() == memory
                &&& alloc.src().pages() == pages
                &&& alloc.src().slots() == slots
                &&& alloc.src().window() == window@.addr
                &&& alloc.src_view().spans.is_empty()
                &&& alloc.src_view().grants == Seq::<Request>::empty()
                &&& alloc.src_view().refusals == Seq::<Refusal>::empty()
                &&& alloc.src_view().provenance == window@.provenance
            },
            AllocatorInit::Refused(returned) => {
                &&& !Eager::new_ok(memory, pages, slots, window)
                &&& returned@ == caller@
            },
        },
{
    let ghost c0 = caller@;
    match Eager::new(&mut caller, space, untyped, memory, pages, slots, window) {
        Some(eager) => {
            proof {
                assert(caller@.wf());
                assert(caller@.kernel().sealed(caller@.root()));
                assert(caller@.kernel().processes.records@.contains_key(caller@.root()));
                assert(names_own_space(caller@, space));
                assert(eager.space() == space);
                assert(eager.holds(caller@));
                assert(eager.serves(caller@));
            }
            finish_allocator(spares, eager, caller)
        },
        None => {
            proof {
                assert(caller@ == c0);
            }
            AllocatorInit::Refused(caller)
        },
    }
}

} // verus!
