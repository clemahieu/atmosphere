// SPDX-License-Identifier: MIT

//! A column of page metadata: a run of elements whose length is known only at boot, held in memory
//! boot carved, with one points-to permission per element. The open view is the sequence of the
//! elements, which is what the proofs read, as with `Array`; the permissions sit behind a closed
//! match that only `new`, `get` and `set` open, so a query that reads one entry does not carry a
//! permission for every page. design/page-metadata-sized-from-the-memory-map/.

use vstd::prelude::*;
use vstd::raw_ptr::{IsExposed, PointsToRaw, ptr_mut_write, ptr_ref, with_exposed_provenance};
#[cfg(verus_keep_ghost)]
use vstd::raw_ptr::{MemContents, PointsTo, ptr_mut_from_data, PtrData};
#[cfg(verus_keep_ghost)]
use vstd::layout::{size_of, align_of};

verus! {

broadcast use {vstd::raw_ptr::group_raw_ptr_axioms, vstd::set_lib::group_set_lib_default, vstd::set::group_set_lemmas};

// Proofs alone read the sequence and the permissions, and a cargo build erases proofs, so only
// Verus compiles those fields; a cargo build keeps a marker for `T`.
pub struct Column<T> {
    /// The elements, in order: what the proofs read.
    #[cfg(verus_keep_ghost)]
    seq: Ghost<Seq<T>>,
    base: usize,
    len: usize,
    #[cfg(verus_keep_ghost)]
    perms: Tracked<Map<int, PointsTo<T>>>,
    exposed: Tracked<IsExposed>,
    #[cfg(not(verus_keep_ghost))]
    element: core::marker::PhantomData<T>,
}

/// The address of element `i` of a column of `T` at `base`.
pub open spec fn element_addr<T>(base: int, i: int) -> int {
    base + i * size_of::<T>()
}

impl<T> Column<T> {
    pub closed spec fn view(&self) -> Seq<T> {
        self.seq@
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> T
        recommends
            0 <= i < self@.len(),
    {
        self@[i]
    }

    pub open spec fn wf(&self) -> bool {
        self.matches()
    }

    /// The pointer element `i`'s permission is for.
    closed spec fn element_ptr(&self, i: int) -> *mut T {
        ptr_mut_from_data::<T>(
            PtrData { addr: element_addr::<T>(self.base as int, i) as usize, provenance: self.exposed@@, metadata: () },
        )
    }

    /// The sequence the proofs read is what memory holds: one initialised permission per element,
    /// at the element's address, holding the sequence's value there.
    pub closed spec fn matches(&self) -> bool {
        &&& self.seq@.len() == self.len
        &&& size_of::<T>() > 0
        &&& self.base + self.len * size_of::<T>() <= usize::MAX
        &&& self.perms@.dom() =~= Set::range(0, self.len as int)
        &&& forall|i: int| 0 <= i < self.len ==> {
            &&& (#[trigger] self.perms@[i]).ptr() == self.element_ptr(i)
            &&& self.perms@[i].opt_value() == MemContents::Init(self.seq@[i])
        }
    }

    /// How many elements the column holds.
    pub fn len(&self) -> (n: usize)
        requires
            self.wf(),
        ensures
            n == self@.len(),
    {
        self.len
    }

    /// Element `i`.
    pub fn get(&self, i: usize) -> (out: &T)
        requires
            self.wf(),
            i < self@.len(),
        ensures
            *out == self@[i as int],
    {
        let addr = self.element(i);
        let ptr = with_exposed_provenance::<T>(addr, self.exposed);
        let tracked perm = self.perms.borrow().tracked_borrow(i as int);
        ptr_ref(ptr as *const T, Tracked(perm))
    }

    /// Overwrites element `i` with `v`.
    pub fn set(&mut self, i: usize, v: T)
        requires
            old(self).wf(),
            i < old(self)@.len(),
        ensures
            final(self).wf(),
            final(self)@ =~= old(self)@.update(i as int, v),
    {
        let addr = self.element(i);
        let ptr = with_exposed_provenance::<T>(addr, self.exposed);
        let tracked mut perm = self.perms.borrow_mut().tracked_remove(i as int);
        ptr_mut_write(ptr, Tracked(&mut perm), v);
        proof {
            self.perms.borrow_mut().tracked_insert(i as int, perm);
            self.seq = Ghost(self.seq@.update(i as int, v));
        }
    }

    /// The address of element `i`, which does not overflow.
    fn element(&self, i: usize) -> (addr: usize)
        requires
            self.wf(),
            i < self.len,
        ensures
            addr == element_addr::<T>(self.base as int, i as int),
    {
        proof {
            vstd::arithmetic::mul::lemma_mul_inequality(i as int, self.len as int, size_of::<T>() as int);
        }
        self.base + i * core::mem::size_of::<T>()
    }
}

impl<T: Copy> Column<T> {
    /// A column of `len` copies of `fill` in the memory `raw` grants, starting at `base`: the raw
    /// permission is split into one typed permission per element and each element is written, so
    /// what memory held before is not what the proof relies on.
    pub fn new(
        base: usize,
        len: usize,
        fill: T,
        Tracked(raw): Tracked<PointsToRaw>,
        Tracked(exposed): Tracked<IsExposed>,
    ) -> (ret: Self)
        requires
            size_of::<T>() > 0,
            base as int % align_of::<T>() as int == 0,
            base + len * size_of::<T>() <= usize::MAX,
            raw.is_range(base as int, len * size_of::<T>()),
            raw.provenance() == exposed@,
        ensures
            ret.wf(),
            ret@ =~= Seq::new(len as nat, |i: int| fill),
    {
        let size = core::mem::size_of::<T>();
        let ghost s = size as int;
        let tracked mut rest = raw;
        let tracked mut perms = Map::<int, PointsTo<T>>::tracked_empty();
        let mut i: usize = 0;
        while i < len
            invariant
                s == size,
                s == size_of::<T>(),
                s > 0,
                i <= len,
                base + len * s <= usize::MAX,
                base as int % align_of::<T>() as int == 0,
                rest.provenance() == exposed@,
                rest.dom() =~= Set::range(base + i * s, base + len * s),
                perms.dom() =~= Set::range(0, i as int),
                forall|j: int| 0 <= j < i ==> {
                    &&& (#[trigger] perms[j]).ptr() == ptr_mut_from_data::<T>(
                        PtrData { addr: element_addr::<T>(base as int, j) as usize, provenance: exposed@, metadata: () },
                    )
                    &&& perms[j].opt_value() == MemContents::Init(fill)
                },
            decreases len - i,
        {
            assert(0 <= i * s && i * s + s <= len * s && (i + 1) * s == i * s + s) by (nonlinear_arith)
                requires
                    i < len,
                    s > 0,
            ;
            let addr = base + i * size;
            proof {
                lemma_element_aligned::<T>(base as int, i as int);
            }
            let tracked (first, others) = rest.split(Set::range(addr as int, addr + s));
            proof {
                rest = others;
                assert(rest.dom() =~= Set::range(base + (i + 1) * s, base + len * s));
            }
            let tracked mut perm = first.into_typed::<T>(addr);
            let ptr = with_exposed_provenance::<T>(addr, Tracked(exposed));
            ptr_mut_write(ptr, Tracked(&mut perm), fill);
            proof {
                perms.tracked_insert(i as int, perm);
            }
            i = i + 1;
        }
        Column {
            #[cfg(verus_keep_ghost)]
            seq: Ghost(Seq::new(len as nat, |i: int| fill)),
            base,
            len,
            #[cfg(verus_keep_ghost)]
            perms: Tracked(perms),
            exposed: Tracked(exposed),
            #[cfg(not(verus_keep_ghost))]
            element: core::marker::PhantomData,
        }
    }
}

/// Every element of a column whose base is aligned to its element is aligned too: the size of a
/// type is a multiple of its alignment.
proof fn lemma_element_aligned<T>(base: int, i: int)
    requires
        0 <= i,
        base % align_of::<T>() as int == 0,
    ensures
        element_addr::<T>(base, i) % align_of::<T>() as int == 0,
{
    broadcast use vstd::layout::group_align_properties;
    let a = align_of::<T>() as int;
    let z = size_of::<T>() as int;
    assert(a > 0);
    assert(z % a == 0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(z, a);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base, a);
    let k = z / a;
    let m = base / a;
    assert(base + i * z == (m + i * k) * a) by (nonlinear_arith)
        requires
            base == a * m,
            z == a * k,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(m + i * k, a);
}

} // verus!
