// SPDX-License-Identifier: MIT

// Permissioned pointers for the kernel. This is the simple_pptr of the vstd the workspace Cargo.toml
// pins, without its allocation API, which the kernel does not have, and with conversions between
// permission types, which simple_pptr's private fields rule out. tools/upstream-copies/pptr.rs.patch
// records the difference, and the gate holds this file to simple_pptr plus that record. Its license
// follows.
//
// MIT License
//
// Copyright (c) 2021 The Verus Contributors
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#[cfg(verus_keep_ghost)]
use vstd::layout::*;
use vstd::prelude::*;
use vstd::raw_ptr;
use vstd::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use vstd::set_lib::*;
use core::marker::PhantomData;

use crate::define::PAGE_SZ;

verus! {

/// `PPtr` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to a `V` in memory.
/// This is designed to be simpler to use that Verus's
/// [more general pointer support](`vstd::raw_ptr`),
/// but also to serve as a better introductory point.
/// Historically, `PPtr` was positioned as a "trusted primitive" of Verus,
/// but now, it is implemented and verified from the more general pointer support,
/// which operates on similar principles, but which is much precise to Rust's
/// pointer semantics.
///
/// A `PPtr` is equvialent to its `usize`-based address. The type paramter `V` technically
/// doesn't matter, and you can freely convert between `PPtr<V>` and `PPtr<W>` by casting
/// to and from the `usize` address. What _really_ matters is the type paramter of the
/// `PointsTo<V>`.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`PointsTo<V>`](PointsTo). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in compiled code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### PointsTo objects.
///
/// The [`PointsTo`] object represents the ability to access (read or write)
/// the data behind the pointer.
///
/// The `perm: PointsTo<V>` object tracks two pieces of data:
///  * [`perm.pptr()`](PointsTo::pptr) is the pointer that the permission is associated to.
///  * [`perm.mem_contents()`](PointsTo::mem_contents) is the memory contents, which is one of either:
///     * [`MemContents::Uninit`] if the memory pointed-to by
///       by the pointer is uninitialized.
///     * [`MemContents::Init(v)`](raw_ptr::MemContents::Init) if the memory points-to the
///       the value `v`.
///
/// Your access to the `PointsTo` object determines what operations you can safely perform
/// with the pointer:
///  * You can _read_ from the pointer as long as you have read access to the `PointsTo` object,
///     e.g., `&PointsTo<V>`.
///  * You can _write_ to the pointer as long as you have mutable access to the `PointsTo` object,
///     e.g., `&mut PointsTo<V>`
///
/// For those familiar with separation logic, the `PointsTo` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Example
///
/// ```rust,ignored
/// fn example(p: PPtr<u64>, Tracked(points_to): Tracked<&mut PointsTo<u64>>)
///     requires
///         old(points_to).pptr() == p,
///         old(points_to).mem_contents() == MemContents::<u64>::Uninit,
/// {
///     // unsafe { *p = 5; }
///     p.write(Tracked(&mut *points_to), 5);
///
///     assert(points_to.mem_contents() == MemContents::Init(5));
///     assert(points_to.pptr() == p);
///
///     // let x = unsafe { *p };
///     let x = p.read(Tracked(&*points_to));
///
///     assert(x == 5);
/// }
/// ```
///
/// ### Examples of incorrect usage
///
/// The following doesn't violate Rust's ownership-checking, but it "mixes up" the `PointsTo`
/// objects, attempting to use the wrong `PointsTo` for the given pointer.
/// This violates the precondition on [`p.read()`](PPtr::read).
///
/// ```rust,ignored
/// fn mixed_up(p: PPtr<u64>, Tracked(perm_q): Tracked<&PointsTo<u64>>)
///     requires
///         perm_q.pptr() != p,
///         perm_q.is_init(),
/// {
///     // read from p, try to use q's permission object
///     let x = p.read(Tracked(perm_q));
/// }
/// ```
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`](vstd::cell::PCell), but has a few key differences:
///  * In `PCell<V>`, the type `V` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `V` is placed at some location in memory.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `PointsTo` token is the permission to read and write the contents.
///
/// ### Simplifications relative to more general pointer API
///
///  * Pointers are only represented by addresses and don't have a general notion of provenance
///  * Pointers are untyped (only `PointsTo` is typed).
///  * `PointsTo` tokens are non-fungible. They can't be broken up or made variable-sized, except
///    that [`page_into_typed`] and [`typed_into_page`] convert between the permission for a 4K page
///    and one for the object at its start.
// We want PPtr's fields to be public so the solver knows that equality of addresses
// implies equality of PPtrs
pub struct PPtr<V>(pub usize, pub PhantomData<V>);

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.
// Proofs alone read the fields, and a cargo build erases proofs, so only Verus compiles them; a
// cargo build keeps the type, which exec signatures name, with a marker for `V`.
pub tracked struct PointsTo<V> {
    #[cfg(verus_keep_ghost)]
    points_to: raw_ptr::PointsTo<V>,
    #[cfg(verus_keep_ghost)]
    exposed: raw_ptr::IsExposed,
    /// The raw bytes after the value, up to the end of its 4K page, when it fits one.
    #[cfg(verus_keep_ghost)]
    rest: PointsToRaw,
    #[cfg(not(verus_keep_ghost))]
    v: PhantomData<V>,
}

#[verusfmt::skip]
broadcast use {
    vstd::raw_ptr::group_raw_ptr_axioms,
    vstd::set_lib::group_set_lib_default,
    vstd::set::group_set_lemmas};

impl<V> PPtr<V> {
    /// Use `addr()` instead
    #[verifier::inline]
    pub open spec fn spec_addr(p: PPtr<V>) -> usize {
        p.0
    }

    /// Cast a pointer to an integer.
    #[inline(always)]
    #[verifier::when_used_as_spec(spec_addr)]
    pub fn addr(self) -> (u: usize)
        ensures
            u == self.addr(),
    {
        self.0
    }

    #[doc(hidden)]
    #[inline(always)]
    pub fn from_usize(u: usize) -> (s: Self)
        ensures
            u == s.addr(),
    {
        PPtr(u, PhantomData)
    }
}

impl<V> PointsTo<V> {
    #[verifier::inline]
    pub open spec fn pptr(&self) -> PPtr<V> {
        PPtr(self.addr(), PhantomData)
    }

    pub closed spec fn addr(self) -> usize {
        self.points_to.ptr().addr()
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        &&& self.points_to.ptr()@.provenance == self.exposed.provenance()
        &&& self.points_to.ptr().addr() != 0
        &&& size_of::<V>() <= PAGE_SZ ==> self.rest.is_range(
            self.points_to.ptr().addr() + size_of::<V>(),
            PAGE_SZ - size_of::<V>(),
        )
        &&& self.rest.provenance() == self.exposed.provenance()
    }

    pub closed spec fn mem_contents(&self) -> MemContents<V> {
        self.points_to.opt_value()
    }

    #[doc(hidden)]
    #[verifier::inline]
    pub open spec fn opt_value(&self) -> MemContents<V> {
        self.mem_contents()
    }

    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.mem_contents().is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.mem_contents().is_uninit()
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> V
        recommends
            self.is_init(),
    {
        self.mem_contents().value()
    }

    /// "Forgets" about the value stored behind the pointer.
    /// Updates the `PointsTo` value to [`MemContents::Uninit`].
    /// Note that this is a `proof` function, i.e., it is operationally a no-op in executable code.
    pub proof fn leak_contents(tracked &mut self)
        ensures
            final(self).pptr() == old(self).pptr(),
            final(self).is_uninit(),
    {
        use_type_invariant(&*self);
        self.points_to.leak_contents();
    }

    /// Guarantees that two distinct, non-ZST `PointsTo<V>` objects point to disjoint ranges of memory.
    /// Since both S and V are non-zero-sized, this also implies the pointers
    /// have distinct addresses.
    ///
    /// Note: If either S or T is zero-sized, we get disjointness "for free" without having to call this proof,
    /// since the empty memory range corresponding to a ZST cannot possibly intersect with any other memory.
    /// However, note that if one type is a ZST and the other is a non-ZST,
    /// the disjointness definition as stated here here does not hold,
    /// since the ZST pointer could be in the middle of the non-ZST's range.
    pub proof fn is_disjoint<S>(tracked &mut self, tracked other: &PointsTo<S>)
        requires
            size_of::<V>() != 0,
            size_of::<S>() != 0,
        ensures
            *old(self) == *final(self),
            final(self).addr() + size_of::<V>() <= other.addr() || other.addr() + size_of::<S>()
                <= final(self).addr(),
    {
        use_type_invariant(&*self);
        self.points_to.is_disjoint(&other.points_to);
    }

    /// Guarantees that two distinct, non-ZST `PointsTo<V>` objects point to different
    /// addresses. This is a corollary of [`PointsTo::is_disjoint`].
    pub proof fn is_distinct<S>(tracked &mut self, tracked other: &PointsTo<S>)
        requires
            size_of::<V>() != 0,
            size_of::<S>() != 0,
        ensures
            *old(self) == *final(self),
            final(self).addr() != other.addr(),
    {
        use_type_invariant(&*self);
        self.points_to.is_disjoint(&other.points_to);
    }
}

impl<V> Clone for PPtr<V> {
    fn clone(&self) -> (res: Self)
        ensures
            res == *self,
    {
        PPtr(self.0, PhantomData)
    }
}

impl<V> Copy for PPtr<V> {

}

impl<V> PPtr<V> {

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.mem_contents()`
    /// from `MemContents::Uninit` to `MemContents::Init(v)`.
    #[inline(always)]
    pub fn put(self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            old(perm).pptr() == self,
            old(perm).mem_contents() == MemContents::Uninit::<V>,
        ensures
            final(perm).pptr() == old(perm).pptr(),
            final(perm).mem_contents() == MemContents::Init(v),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        ptr_mut_write(ptr, Tracked(&mut perm.points_to), v);
    }

    /// Moves `v` out of the location pointed to by the pointer `self`
    /// and returns it.
    /// Requires the memory to be initialized, and leaves it uninitialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `Some(v)` to `None`,
    /// while returning the `v` as an `exec` value.
    #[inline(always)]
    pub fn take(self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
        ensures
            final(perm).pptr() == old(perm).pptr(),
            final(perm).mem_contents() == MemContents::Uninit::<V>,
            v == old(perm).value(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        ptr_mut_read(ptr, Tracked(&mut perm.points_to))
    }

    /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.
    #[inline(always)]
    pub fn borrow<'a>(self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            perm.pptr() == self,
            perm.is_init(),
        ensures
            *v == perm.value(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        ptr_ref(ptr, Tracked(&perm.points_to))
    }

    /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.
    #[inline(always)]
    pub fn borrow_mut<'a>(self, Tracked(perm): Tracked<&'a mut PointsTo<V>>) -> (v: &'a mut V)
        requires
            perm.pptr() == self,
            perm.is_init(),
        ensures
            final(perm).pptr() == self,
            final(perm).is_init(),
            *v == old(perm).value(),
            final(perm).value() == *final(v),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        ptr_mut_ref(ptr, Tracked(&mut perm.points_to))
    }

    #[inline(always)]
    pub fn write(self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) where V: Copy
        requires
            old(perm).pptr() == self,
        ensures
            final(perm).pptr() == old(perm).pptr(),
            final(perm).mem_contents() == MemContents::Init(in_v),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
            perm.leak_contents();
        }
        self.put(Tracked(&mut *perm), in_v);
    }

    #[inline(always)]
    pub fn read(self, Tracked(perm): Tracked<&PointsTo<V>>) -> (out_v: V) where V: Copy
        requires
            perm.pptr() == self,
            perm.is_init(),
        ensures
            out_v == perm.value(),
        opens_invariants none
        no_unwind
    {
        *self.borrow(Tracked(&*perm))
    }
}

pub use raw_ptr::MemContents;

/// Turns the permission for an uninitialised 4K page into a typed permission for the object at its
/// start. The rest of the page travels inside the permission.
pub proof fn page_into_typed<W>(tracked page: PointsTo<[u8; PAGE_SZ]>) -> (tracked ret: PointsTo<W>)
    requires
        page.is_uninit(),
        size_of::<[u8; PAGE_SZ]>() == PAGE_SZ,
        size_of::<W>() <= PAGE_SZ,
        page.addr() as int % align_of::<W>() as int == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    use_type_invariant(&page);
    let addr = page.addr();
    let tracked PointsTo { points_to, exposed, rest: _ } = page;
    let tracked raw = points_to.into_raw();
    let tracked (first, rest) = raw.split(set_int_range(addr as int, addr + size_of::<W>()));
    PointsTo { points_to: first.into_typed::<W>(addr), exposed, rest }
}

/// Gives an uninitialised typed permission back as the permission for its whole 4K page.
pub proof fn typed_into_page<W>(tracked typed: PointsTo<W>) -> (tracked ret: PointsTo<[u8; PAGE_SZ]>)
    requires
        typed.is_uninit(),
        size_of::<[u8; PAGE_SZ]>() == PAGE_SZ,
        align_of::<[u8; PAGE_SZ]>() == 1,
        size_of::<W>() <= PAGE_SZ,
    ensures
        ret.addr() == typed.addr(),
        ret.is_uninit(),
{
    use_type_invariant(&typed);
    let addr = typed.addr();
    let tracked PointsTo { points_to, exposed, rest } = typed;
    let tracked raw = points_to.into_raw().join(rest);
    let tracked points_to = raw.into_typed::<[u8; PAGE_SZ]>(addr);
    let tracked empty = PointsToRaw::empty(exposed.provenance());
    PointsTo { points_to, exposed, rest: empty }
}

/// A page survives the round trip through a typed permission at the same address.
proof fn page_round_trip<W>(tracked page: PointsTo<[u8; PAGE_SZ]>) -> (tracked ret: PointsTo<[u8; PAGE_SZ]>)
    requires
        page.is_uninit(),
        size_of::<[u8; PAGE_SZ]>() == PAGE_SZ,
        align_of::<[u8; PAGE_SZ]>() == 1,
        size_of::<W>() <= PAGE_SZ,
        page.addr() as int % align_of::<W>() as int == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    typed_into_page(page_into_typed::<W>(page))
}

pub open spec fn page_is_zero(page: [u8; PAGE_SZ]) -> bool {
    forall|i: int| 0 <= i < PAGE_SZ ==> #[trigger] page@[i] == 0
}

/// Clears an uninitialised 4K page through its permission.
pub fn zero_page(addr: usize, Tracked(perm): Tracked<&mut PointsTo<[u8; PAGE_SZ]>>)
    requires
        old(perm).is_uninit(),
        old(perm).addr() == addr,
    ensures
        final(perm).is_init(),
        final(perm).addr() == addr,
        page_is_zero(final(perm).value()),
{
    PPtr::<[u8; PAGE_SZ]>::from_usize(addr).put(Tracked(perm), [0u8; PAGE_SZ]);
}

} // verus!
