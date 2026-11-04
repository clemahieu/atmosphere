// Permissioned pointers for the kernel. This is vstd's simple_pptr at Verus 3e8600ac, without its
// allocation API, which the kernel does not have, and with conversions between permission types,
// which simple_pptr's private fields rule out. Its license follows.
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

use vstd::layout::*;
use vstd::prelude::*;
use vstd::raw_ptr;
use vstd::raw_ptr::*;
use vstd::set_lib::*;
use core::marker::PhantomData;

verus! {

/// `PPtr` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to a heap-allocated `V`.
/// This is designed to be simpler to use that Verus's
/// [more general pointer support](`crate::raw_ptr`),
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
/// The [`PointsTo`] object represents both the ability to access (read or write)
/// the data behind the pointer _and_ the ability to free it
/// (return it to the memory allocator).
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
///     of the `PointsTo` object (i.e., the ability to move it).
///
/// For those familiar with separation logic, the `PointsTo` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Example
///
/// ```rust,ignored
/// fn main() {
///     unsafe {
///         // ALLOCATE
///         // p: PPtr<u64>, points_to: PointsTo<u64>
///         let (p, Tracked(mut points_to)) = PPtr::<u64>::empty();
///
///         assert(points_to.mem_contents() == MemContents::Uninit);
///         assert(points_to.pptr() == p);
///
///         // unsafe { *p = 5; }
///         p.write(Tracked(&mut points_to), 5);
///
///         assert(points_to.mem_contents() == MemContents::Init(5));
///         assert(points_to.pptr() == p);
///
///         // let x = unsafe { *p };
///         let x = p.read(Tracked(&points_to));
///
///         assert(x == 5);
///
///         // DEALLOCATE
///         let y = p.into_inner(Tracked(points_to));
///
///         assert(y == 5);
///     }
/// }
/// ```
///
/// ### Examples of incorrect usage
///
/// The following code has a use-after-free bug, and it is rejected by Verus because
/// it fails to satisfy Rust's ownership-checker.
///
/// ```rust,ignored
/// fn main() {
///     unsafe {
///         // ALLOCATE
///         // p: PPtr<u64>, points_to: PointsTo<u64>
///         let (p, Tracked(mut points_to)) = PPtr::<u64>::empty();
///
///         // unsafe { *p = 5; }
///         p.write(Tracked(&mut points_to), 5);
///
///         // let x = unsafe { *p };
///         let x = p.read(Tracked(&points_to));
///
///         // DEALLOCATE
///         p.free(Tracked(points_to));                 // `points_to` is moved here
///
///         // READ-AFTER-FREE
///         let x2 = p.read(Tracked(&mut points_to));   // so it can't be used here
///     }
/// }
/// ```
///
/// The following doesn't violate Rust's ownership-checking, but it "mixes up" the `PointsTo`
/// objects, attempting to use the wrong `PointsTo` for the given pointer.
/// This violates the precondition on [`p.read()`](PPtr::read).
///
/// ```rust,ignored
/// fn main() {
///     unsafe {
///         // ALLOCATE p
///         let (p, Tracked(mut perm_p)) = PPtr::<u64>::empty();
///
///         // ALLOCATE q
///         let (q, Tracked(mut perm_q)) = PPtr::<u64>::empty();
///
///         // DEALLOCATE p
///         p.free(Tracked(perm_p));
///
///         // READ-AFTER-FREE (read from p, try to use q's permission object)
///         let x = p.read(Tracked(&mut perm_q));
///     }
/// }
/// ```
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`](crate::cell::PCell), but has a few key differences:
///  * In `PCell<V>`, the type `V` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `V` is placed at some location on the heap.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `ptr::PointsTo` token represents not just the permission to read/write
///    the contents, but also to deallocate.
///
/// ### Simplifications relative to more general pointer API
///
///  * Pointers are only represented by addresses and don't have a general notion of provenance
///  * Pointers are untyped (only `PointsTo` is typed).
///  * The `PointsTo` also encapsulates the permission to free a pointer.
///  * `PointsTo` tokens are non-fungible. They can't be broken up or made variable-sized.
// We want PPtr's fields to be public so the solver knows that equality of addresses
// implies equality of PPtrs
pub struct PPtr<V>(pub usize, pub PhantomData<V>);

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.
pub tracked struct PointsTo<V> {
    points_to: raw_ptr::PointsTo<V>,
    exposed: raw_ptr::IsExposed,
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

    /// Cast an integer to a pointer.
    ///
    /// Note that this does _not_ require or ensure that the pointer is valid.
    /// Of course, if the user creates an invalid pointer, they would still not be able to
    /// create a valid [`PointsTo`] token for it, and thus they would never
    /// be able to access the data behind the pointer.
    ///
    /// This is analogous to normal Rust, where casting to a pointer is always possible,
    /// but dereferencing a pointer is an `unsafe` operation.
    /// With PPtr, casting to a pointer is likewise always possible,
    /// while dereferencing it is only allowed when the right preconditions are met.
    #[inline(always)]
    pub fn from_addr(u: usize) -> (s: Self)
        ensures
            u == s.addr(),
    {
        PPtr(u, PhantomData)
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

    /// Guarantee that the `PointsTo` points to a non-null address.
    pub proof fn is_nonnull(tracked &self)
        ensures
            self.addr() != 0,
    {
        use_type_invariant(self);
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

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.
    #[inline(always)]
    pub fn replace(self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
        ensures
            final(perm).pptr() == old(perm).pptr(),
            final(perm).mem_contents() == MemContents::Init(in_v),
            out_v == old(perm).value(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        let out_v = ptr_mut_read(ptr, Tracked(&mut perm.points_to));
        ptr_mut_write(ptr, Tracked(&mut perm.points_to), in_v);
        out_v
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

impl<V> PointsTo<V> {
    /// Gives up an uninitialised permission for the raw bytes it covers.
    pub proof fn into_raw(tracked self) -> (tracked ret: (PointsToRaw, IsExposed))
        requires
            self.is_uninit(),
        ensures
            ret.0.is_range(self.addr() as int, size_of::<V>() as int),
            ret.0.provenance() == ret.1.provenance(),
    {
        use_type_invariant(&self);
        let tracked PointsTo { points_to, exposed } = self;
        (points_to.into_raw(), exposed)
    }

    /// Turns the raw bytes at an aligned, non-null address into an uninitialised typed permission.
    pub proof fn from_raw(tracked raw: PointsToRaw, tracked exposed: IsExposed, addr: usize) -> (tracked ret: Self)
        requires
            addr != 0,
            addr as int % align_of::<V>() as int == 0,
            raw.is_range(addr as int, size_of::<V>() as int),
            raw.provenance() == exposed.provenance(),
        ensures
            ret.addr() == addr,
            ret.is_uninit(),
    {
        let tracked points_to = raw.into_typed::<V>(addr);
        PointsTo { points_to, exposed }
    }
}

/// Turns the permission for an uninitialised 4K page into a typed permission for the object at its
/// start, and the raw permission for the rest of the page.
pub proof fn page_into_typed<W>(tracked page: PointsTo<[u8; 4096]>) -> (tracked ret: (PointsTo<W>, PointsToRaw))
    requires
        page.is_uninit(),
        size_of::<[u8; 4096]>() == 4096,
        size_of::<W>() <= 4096,
        page.addr() as int % align_of::<W>() as int == 0,
    ensures
        ret.0.addr() == page.addr(),
        ret.0.is_uninit(),
        ret.1.is_range(page.addr() + size_of::<W>(), 4096 - size_of::<W>()),
{
    page.is_nonnull();
    let addr = page.addr();
    let tracked (raw, exposed) = page.into_raw();
    let tracked (first, rest) = raw.split(set_int_range(addr as int, addr + size_of::<W>()));
    (PointsTo::<W>::from_raw(first, exposed, addr), rest)
}

} // verus!
