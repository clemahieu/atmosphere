// SPDX-License-Identifier: MIT

//! Heap bundled with its span source and caller token under a single invariant.

use vstd::pervasive::unreached;
use vstd::prelude::*;
use vstd::raw_ptr::PointsToRaw;

#[cfg(verus_keep_ghost)]
use crate::arch::{CLASSES, PAGE_BYTES};
#[cfg(verus_keep_ghost)]
use crate::class::class_size;
#[cfg(verus_keep_ghost)]
use crate::heap::{
    class_for, large_alloc, large_free, large_layout, part_alloc, part_free, run_layout,
    slot_alloc, slot_free, small_layout,
};
use crate::heap::{layout_fits, Heap};
#[cfg(verus_keep_ghost)]
use crate::large::pages_for;
#[cfg(verus_keep_ghost)]
use crate::source::SourceView;
use crate::source::SpanSource;

verus! {

/// A heap bundled with its span source and an optional token proving authority over the source's
/// frames. While the token is held, `alloc` and `free` keep both the heap well-formed over the
/// source's view and the source serving the token; `lend` temporarily releases the token and
/// `give_back` re-attaches a token the source still serves.
pub struct Allocator<S: SpanSource> {
    heap: Heap,
    src: S,
    token: Option<Tracked<S::Token>>,
}

impl<S: SpanSource> Allocator<S> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        &&& self.src@.wf()
        &&& self.heap.wf(self.src@)
        &&& match self.token {
            Some(token) => self.src.serves(token@),
            None => true,
        }
    }

    /// The underlying heap.
    pub closed spec fn heap(&self) -> Heap {
        self.heap
    }

    /// The underlying span source.
    pub closed spec fn src(&self) -> S {
        self.src
    }

    /// The ghost view of the span source.
    pub open spec fn src_view(&self) -> SourceView {
        self.src()@
    }

    /// Whether `token` currently meets the source's `serves` relation.
    pub open spec fn src_serves(&self, token: S::Token) -> bool {
        self.src().serves(token)
    }

    /// A reference to the underlying span source.
    pub fn source(&self) -> (r: &S)
        ensures
            *r == self.src(),
    {
        &self.src
    }

    /// Whether the allocator currently holds its token.
    pub closed spec fn held(&self) -> bool {
        self.token is Some
    }

    /// The authority token currently held by the allocator, if any.
    pub closed spec fn token(&self) -> Option<S::Token> {
        match self.token {
            Some(t) => Some(t@),
            None => None,
        }
    }

    /// The number of spare idle blocks kept before returning one to the source.
    pub open spec fn spares(&self) -> nat {
        self.heap().spares()
    }

    /// The addresses of every object currently allocated through this allocator.
    pub open spec fn live(&self) -> ISet<int> {
        self.heap().live()
    }

    /// The allocator's invariant implies that its source view is well-formed and its heap is
    /// well-formed over that source view.
    pub proof fn lemma_wf(tracked &self)
        ensures
            self.src_view().wf(),
            self.heap().wf(self.src_view()),
            self.heap().classes().len() == CLASSES,
            self.held() <==> self.token() is Some,
            self.token() matches Some(t) ==> self.src_serves(t),
    {
        use_type_invariant(self);
        self.heap.lemma_parts(self.src@);
    }

    /// Creates an empty allocator bundling a fresh heap of `spares` spare blocks with `src` and
    /// its authority `token`.
    pub fn new(spares: usize, src: S, token: Tracked<S::Token>) -> (r: Self)
        requires
            src@.wf(),
            src.serves(token@),
        ensures
            r.held(),
            r.token() == Some(token@),
            r.src() == src,
            r.src_view() == src@,
            r.spares() == spares as nat,
            r.live() == ISet::<int>::empty(),
            r.heap().wf(src@),
            r.heap().spares() == spares as nat,
            r.heap().live() == ISet::<int>::empty(),
    {
        let heap = Heap::new(spares);
        Allocator { heap, src, token: Some(token) }
    }

    /// Returns whether the allocator currently holds its token.
    pub fn has_token(&self) -> (r: bool)
        ensures
            r == self.held(),
    {
        match &self.token {
            Some(_) => true,
            None => false,
        }
    }

    /// Allocates a block for `(size, align)` if the layout fits and the token is currently held,
    /// returning `None` otherwise or if the span source refuses a request.
    pub fn alloc(&mut self, size: usize, align: usize) -> (r: Option<(*mut u8, Tracked<PointsToRaw>)>)
        ensures
            final(self).held() == old(self).held(),
            final(self).token() is Some <==> final(self).held(),
            final(self).spares() == old(self).spares(),
            (!old(self).held() || !(small_layout(size as nat, align as nat) || run_layout(
                size as nat,
                align as nat,
            ) || large_layout(size as nat, align as nat))) ==> {
                &&& r is None
                &&& final(self).heap() == old(self).heap()
                &&& final(self).src() == old(self).src()
                &&& final(self).src_view() == old(self).src_view()
                &&& final(self).live() == old(self).live()
                &&& final(self).token() == old(self).token()
            },
            old(self).held() && small_layout(size as nat, align as nat) ==> slot_alloc(
                old(self).heap(),
                final(self).heap(),
                old(self).src_view(),
                final(self).src_view(),
                size as nat,
                align as nat,
                r,
            ),
            old(self).held() && run_layout(size as nat, align as nat) ==> part_alloc(
                old(self).heap(),
                final(self).heap(),
                old(self).src_view(),
                final(self).src_view(),
                size as nat,
                align as nat,
                r,
            ),
            old(self).held() && large_layout(size as nat, align as nat) ==> large_alloc(
                old(self).heap(),
                final(self).heap(),
                old(self).src_view(),
                final(self).src_view(),
                size as nat,
                align as nat,
                r,
            ),
    {
        proof {
            use_type_invariant(&*self);
        }
        if !layout_fits(size, align) {
            return None;
        }
        let Some(mut token) = self.token.take() else {
            return None;
        };
        let r = self.heap.alloc(&mut self.src, &mut token, size, align);
        proof {
            self.heap.lemma_parts(self.src@);
            self.heap.pb().lemma_view(self.src@);
        }
        self.token = Some(token);
        r
    }

    /// Frees an object `p` previously allocated with layout `(size, align)` and permission `perm`
    /// while the token is held.
    pub fn free(&mut self, p: *mut u8, size: usize, align: usize, perm: Tracked<PointsToRaw>)
        requires
            old(self).held(),
            small_layout(size as nat, align as nat) || run_layout(size as nat, align as nat) || large_layout(
                size as nat,
                align as nat,
            ),
            small_layout(size as nat, align as nat) ==> {
                &&& (class_for(size as nat, align as nat) as int) < old(self).heap().classes().len()
                &&& old(self).heap().classes()[class_for(size as nat, align as nat) as int].live().contains(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, class_size(class_for(size as nat, align as nat)) as int)
            },
            run_layout(size as nat, align as nat) ==> {
                &&& old(self).heap().parts().contains_key(p@.addr as int)
                &&& old(self).heap().parts()[p@.addr as int] == pages_for(size as nat)
                &&& perm@.is_range(p@.addr as int, pages_for(size as nat) * PAGE_BYTES)
            },
            large_layout(size as nat, align as nat) ==> {
                &&& old(self).heap().large().contains_key(p@.addr as int)
                &&& perm@.is_range(p@.addr as int, old(self).heap().large()[p@.addr as int] * PAGE_BYTES)
            },
            perm@.provenance() == old(self).src_view().provenance,
        ensures
            final(self).held(),
            final(self).token() is Some,
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live().remove(p@.addr as int),
            small_layout(size as nat, align as nat) ==> slot_free(
                old(self).heap(),
                final(self).heap(),
                old(self).src_view(),
                final(self).src_view(),
                p@.addr as int,
                size as nat,
                align as nat,
            ),
            run_layout(size as nat, align as nat) ==> part_free(
                old(self).heap(),
                final(self).heap(),
                old(self).src_view(),
                final(self).src_view(),
                p@.addr as int,
            ),
            large_layout(size as nat, align as nat) ==> large_free(
                old(self).heap(),
                final(self).heap(),
                old(self).src_view(),
                final(self).src_view(),
                p@.addr as int,
            ),
    {
        proof {
            use_type_invariant(&*self);
            self.heap.lemma_parts(self.src@);
        }
        let Some(mut token) = self.token.take() else {
            unreached()
        };
        self.heap.free(&mut self.src, &mut token, p, size, align, perm);
        proof {
            self.heap.lemma_parts(self.src@);
            self.heap.pb().lemma_view(self.src@);
        }
        self.token = Some(token);
    }

    /// Temporarily takes the authority token out of the allocator, if held.
    pub fn lend(&mut self) -> (r: Option<Tracked<S::Token>>)
        ensures
            !final(self).held(),
            final(self).token() is None,
            final(self).heap() == old(self).heap(),
            final(self).src() == old(self).src(),
            final(self).src_view() == old(self).src_view(),
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live(),
            old(self).held() <==> r is Some,
            r matches Some(token) ==> Some(token@) == old(self).token() && old(self).src_serves(token@),
    {
        proof {
            use_type_invariant(&*self);
        }
        self.token.take()
    }

    /// Returns an authority token that the allocator's source serves.
    pub fn give_back(&mut self, token: Tracked<S::Token>)
        requires
            old(self).src_serves(token@),
        ensures
            final(self).held(),
            final(self).token() == Some(token@),
            final(self).heap() == old(self).heap(),
            final(self).src() == old(self).src(),
            final(self).src_view() == old(self).src_view(),
            final(self).spares() == old(self).spares(),
            final(self).live() == old(self).live(),
    {
        proof {
            use_type_invariant(&*self);
        }
        self.token = Some(token);
    }
}

} // verus!
