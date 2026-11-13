// SPDX-License-Identifier: MIT
//! A class's list of slabs: slab records linked through their `prev` and `next`.
//!
//! The list holds the permission to each record on it, by address, and the ghost sequence of their
//! addresses from the first. Each record's `prev` and `next` name its neighbours in that sequence,
//! 0 at the ends, so a record goes on the front, or comes off from anywhere, in constant time
//! (StarMalloc, arXiv 2403.09435, section 2.2). A size class keeps two lists, its partial slabs and
//! its full ones. The list writes the links of its records and nothing else of them.
//!
//! - `first()` is the first record, or none on an empty list.
//! - `find(a)` walks the list from the first record to the one whose slab's run holds the address
//!   `a`, or returns none when no record's does; linear in the list's length.
//! - `push(p, perm)` puts the record at `p`, with the permission to it, on the front.
//! - `remove(p)` takes the record at `p` off the list and returns the permission to it.
//!
//! Each states the sequence after it exactly, and each record's slab (`slabs`) is the one it had.
use vstd::prelude::*;
use vstd::raw_ptr::*;

use crate::record::Record;
#[cfg(verus_keep_ghost)]
use crate::slab::Slab;

verus! {

broadcast use group_raw_ptr_axioms;

/// The pointer to the record at `a`, with the provenance `prov`.
pub open spec fn record_ptr(a: int, prov: Provenance) -> *mut Record {
    ptr_mut_from_data(PtrData { addr: a as usize, provenance: prov, metadata: () })
}

/// Slab records linked through their links, with the permission to each.
pub struct ClassList {
    /// The first record, while the list holds one; it carries the records' provenance.
    head: Option<*mut Record>,
    /// The records' addresses, from the first.
    order: Ghost<Seq<int>>,
    /// The permission to each record on the list, by address. Only proofs read it, and a cargo
    /// build erases them.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    perms: Tracked<Map<int, PointsTo<Record>>>,
}

impl ClassList {
    /// The record at `a`.
    spec fn value(&self, a: int) -> Record {
        self.perms@[a].value()
    }

    /// The addresses of the records on the list, from the first.
    pub closed spec fn seq(&self) -> Seq<int> {
        self.order@
    }

    /// The slab of each record on the list, by address.
    pub closed spec fn slabs(&self) -> Map<int, Slab> {
        Map::new(self.perms@.dom(), |a: int| self.perms@[a].value().slab)
    }

    /// The record at position `i` links its neighbours, 0 at the ends.
    spec fn linked(&self, i: int) -> bool {
        let r = self.value(self.order@[i]);
        &&& r.prev as int == if i == 0 {
            0
        } else {
            self.order@[i - 1]
        }
        &&& r.next as int == if i + 1 < self.order@.len() {
            self.order@[i + 1]
        } else {
            0
        }
    }

    /// The permissions are keyed by the sequence, which repeats no address, each record is
    /// initialized at its address with the provenance `prov` and linked, and `head` is the first.
    pub closed spec fn wf(&self, prov: Provenance) -> bool {
        &&& self.order@.no_duplicates()
        &&& forall|a: int|
            #![trigger self.perms@.contains_key(a)]
            #![trigger self.order@.contains(a)]
            self.perms@.contains_key(a) <==> self.order@.contains(a)
        &&& forall|a: int| #[trigger]
            self.perms@.contains_key(a) ==> {
                &&& self.perms@[a].ptr() == record_ptr(a, prov)
                &&& self.perms@[a].is_init()
                &&& 0 < a <= usize::MAX
            }
        &&& forall|i: int| 0 <= i < self.order@.len() ==> #[trigger] self.linked(i)
        &&& match self.head {
            None => self.order@.len() == 0,
            Some(h) => {
                &&& self.order@.len() > 0
                &&& h == record_ptr(self.order@[0], prov)
            },
        }
    }

    /// On a well-formed list the sequence repeats no address, the slabs are those of its records,
    /// and no record is at address 0.
    pub proof fn lemma_view(&self, prov: Provenance)
        requires
            self.wf(prov),
        ensures
            self.seq().no_duplicates(),
            forall|a: int| #[trigger] self.slabs().contains_key(a) <==> self.seq().contains(a),
            forall|a: int| #[trigger] self.seq().contains(a) ==> 0 < a <= usize::MAX,
    {
        assert forall|a: int| #[trigger] self.seq().contains(a) implies 0 < a <= usize::MAX by {
            assert(self.perms@.contains_key(a));
        }
    }

    /// The record at position `i` is held, initialized at its address and linked.
    proof fn lemma_at(&self, i: int, prov: Provenance)
        requires
            self.wf(prov),
            0 <= i < self.order@.len(),
        ensures
            self.perms@.contains_key(self.order@[i]),
            self.perms@[self.order@[i]].ptr() == record_ptr(self.order@[i], prov),
            self.perms@[self.order@[i]].is_init(),
            0 < self.order@[i] <= usize::MAX,
            self.linked(i),
    {
        assert(self.order@.contains(self.order@[i]));
    }

    /// No record is on both this list and `other`: each list holds its records' permissions, and two
    /// permissions to one record cannot be held at once. It changes nothing.
    #[cfg(verus_keep_ghost)]
    pub(crate) fn apart(&mut self, other: &ClassList, Ghost(prov): Ghost<Provenance>, Ghost(prov2): Ghost<Provenance>)
        requires
            old(self).wf(prov),
            other.wf(prov2),
        ensures
            *final(self) == *old(self),
            old(self).slabs().dom().disjoint(other.slabs().dom()),
    {
        proof {
            if exists|a: int| #[trigger] self.perms@.contains_key(a) && other.perms@.contains_key(a) {
                let a = choose|a: int| #[trigger] self.perms@.contains_key(a) && other.perms@.contains_key(a);
                assert(self.order@.contains(a));
                assert(other.order@.contains(a));
                crate::arch::lemma_record_layout();
                let tracked mut pa = self.perms.borrow_mut().tracked_remove(a);
                pa.is_disjoint(other.perms.borrow().tracked_borrow(a));
                assert(false);
            }
        }
    }

    /// An empty list, well formed with any provenance.
    pub(crate) fn new() -> (r: Self)
        ensures
            r.seq() == Seq::<int>::empty(),
            r.slabs() == Map::<int, Slab>::empty(),
            forall|prov: Provenance| #[trigger] r.wf(prov),
    {
        let r = ClassList { head: None, order: Ghost(Seq::empty()), perms: Tracked(Map::tracked_empty()) };
        proof {
            assert(r.slabs() =~= Map::<int, Slab>::empty());
        }
        r
    }

    /// The first record, or none when the list is empty.
    pub(crate) fn first(&self, Ghost(prov): Ghost<Provenance>) -> (r: Option<*mut Record>)
        requires
            self.wf(prov),
        ensures
            match r {
                None => self.seq().len() == 0,
                Some(p) => {
                    &&& self.seq().len() > 0
                    &&& p == record_ptr(self.seq()[0], prov)
                },
            },
    {
        self.head
    }

    /// The record whose slab's run holds the address `a`, or none when no record's does.
    pub(crate) fn find(&self, a: usize, Ghost(prov): Ghost<Provenance>) -> (r: Option<*mut Record>)
        requires
            self.wf(prov),
        ensures
            match r {
                None => forall|b: int| #[trigger] self.seq().contains(b) ==> !self.slabs()[b].within(a as int),
                Some(p) => {
                    &&& self.seq().contains(p@.addr as int)
                    &&& p == record_ptr(p@.addr as int, prov)
                    &&& self.slabs()[p@.addr as int].within(a as int)
                },
            },
    {
        let h = match self.head {
            None => return None,
            Some(h) => h,
        };
        proof {
            self.lemma_at(0, prov);
        }
        let mut cur: usize = h.addr();
        let ghost mut j: int = 0;
        while cur != 0
            invariant
                self.wf(prov),
                self.head == Some(h),
                0 <= j <= self.order@.len(),
                cur as int == if j < self.order@.len() { self.order@[j] } else { 0 },
                forall|i: int| 0 <= i < j ==> !(#[trigger] self.value(self.order@[i])).slab.within(a as int),
            decreases self.order@.len() - j,
        {
            proof {
                self.lemma_at(j, prov);
            }
            let p = h.with_addr(cur);
            let tracked perm = self.perms.borrow().tracked_borrow(cur as int);
            let r = ptr_ref(p, Tracked(perm));
            if r.slab.holds_address(a) {
                proof {
                    assert(self.order@.contains(cur as int));
                    assert(p == record_ptr(cur as int, prov));
                }
                return Some(p);
            }
            cur = r.next;
            proof {
                j = j + 1;
            }
        }
        proof {
            if j < self.order@.len() {
                self.lemma_at(j, prov);
            }
            assert forall|b: int| #[trigger] self.seq().contains(b) implies !self.slabs()[b].within(a as int) by {
                let i = self.order@.index_of(b);
                assert(self.order@[i] == b);
                assert(self.perms@.contains_key(b));
                assert(!self.value(self.order@[i]).slab.within(a as int));
                assert(self.slabs()[b] == self.value(b).slab);
            }
        }
        None
    }

    /// Puts the record at `p`, with the permission to it, on the front of the list.
    pub(crate) fn push(&mut self, p: *mut Record, perm: Tracked<PointsTo<Record>>, Ghost(prov): Ghost<Provenance>)
        requires
            old(self).wf(prov),
            perm@.ptr() == p,
            perm@.is_init(),
            p@.provenance == prov,
            p@.addr != 0,
            !old(self).seq().contains(p@.addr as int),
        ensures
            final(self).wf(prov),
            final(self).seq() == seq![p@.addr as int] + old(self).seq(),
            final(self).slabs() == old(self).slabs().insert(p@.addr as int, perm@.value().slab),
    {
        let ghost a = p@.addr as int;
        let ghost old_order = self.order@;
        let Tracked(mut perm) = perm;
        let ghost slab = perm.value().slab;
        let next: usize = match self.head {
            None => 0,
            Some(h) => {
                proof {
                    self.lemma_at(0, prov);
                }
                let ghost b = self.order@[0];
                let tracked mut hperm = self.perms.borrow_mut().tracked_remove(b);
                let mut hr = ptr_mut_read(h, Tracked(&mut hperm));
                hr.prev = p.addr();
                ptr_mut_write(h, Tracked(&mut hperm), hr);
                proof {
                    self.perms.borrow_mut().tracked_insert(b, hperm);
                }
                h.addr()
            },
        };
        let mut r = ptr_mut_read(p, Tracked(&mut perm));
        r.prev = 0;
        r.next = next;
        ptr_mut_write(p, Tracked(&mut perm), r);
        proof {
            self.perms.borrow_mut().tracked_insert(a, perm);
        }
        self.head = Some(p);
        self.order = Ghost(seq![a] + old_order);
        proof {
            let o = old(self);
            let n = self.order@;
            assert(p == record_ptr(a, prov));
            assert forall|i: int, j: int| 0 <= i < j < n.len() implies n[i] != n[j] by {
                if i == 0 {
                    assert(o.order@.contains(n[j]));
                }
            }
            assert(self.perms@.dom() =~= o.perms@.dom().insert(a));
            assert(n[0] == a);
            assert forall|x: int| #[trigger] self.perms@.contains_key(x) <==> n.contains(x) by {
                if n.contains(x) && x != a {
                    let k = choose|k: int| 0 <= k < n.len() && n[k] == x;
                    assert(o.order@[k - 1] == x);
                    assert(o.order@.contains(x));
                }
                if o.order@.contains(x) {
                    let k = choose|k: int| 0 <= k < o.order@.len() && o.order@[k] == x;
                    assert(n[k + 1] == x);
                }
            }
            assert forall|i: int| 0 <= i < n.len() implies #[trigger] self.linked(i) by {
                if i > 0 {
                    o.lemma_at(i - 1, prov);
                    assert(o.linked(i - 1));
                }
            }
            assert(self.slabs() =~= o.slabs().insert(a, slab));
        }
    }

    /// Takes the record at `p` off the list and returns the permission to it.
    pub(crate) fn remove(&mut self, p: *mut Record, Ghost(prov): Ghost<Provenance>) -> (perm: Tracked<PointsTo<Record>>)
        requires
            old(self).wf(prov),
            old(self).seq().contains(p@.addr as int),
            p@.provenance == prov,
        ensures
            final(self).wf(prov),
            final(self).seq() == old(self).seq().remove(old(self).seq().index_of(p@.addr as int)),
            final(self).slabs() == old(self).slabs().remove(p@.addr as int),
            perm@.ptr() == p,
            perm@.is_init(),
            perm@.value().slab == old(self).slabs()[p@.addr as int],
    {
        let ghost a = p@.addr as int;
        let ghost old_order = self.order@;
        let ghost k = old_order.index_of(a);
        proof {
            assert(old_order.contains(a));
            self.lemma_at(k, prov);
            if k > 0 {
                self.lemma_at(k - 1, prov);
            }
            if k + 1 < old_order.len() {
                self.lemma_at(k + 1, prov);
            }
            assert(p == record_ptr(a, prov));
        }
        let tracked perm = self.perms.borrow_mut().tracked_remove(a);
        let r = ptr_ref(p, Tracked(&perm));
        let prev = r.prev;
        let next = r.next;
        if prev == 0 {
            if next == 0 {
                self.head = None;
            } else {
                self.head = Some(p.with_addr(next));
            }
        } else {
            let pp = p.with_addr(prev);
            let tracked mut q = self.perms.borrow_mut().tracked_remove(prev as int);
            let mut pr = ptr_mut_read(pp, Tracked(&mut q));
            pr.next = next;
            ptr_mut_write(pp, Tracked(&mut q), pr);
            proof {
                self.perms.borrow_mut().tracked_insert(prev as int, q);
            }
        }
        if next != 0 {
            let np = p.with_addr(next);
            let tracked mut q = self.perms.borrow_mut().tracked_remove(next as int);
            let mut nr = ptr_mut_read(np, Tracked(&mut q));
            nr.prev = prev;
            ptr_mut_write(np, Tracked(&mut q), nr);
            proof {
                self.perms.borrow_mut().tracked_insert(next as int, q);
            }
        }
        self.order = Ghost(old_order.remove(k));
        proof {
            let o = old(self);
            let n = self.order@;
            assert(self.perms@.dom() =~= o.perms@.dom().remove(a));
            assert(prev == 0 <==> k == 0);
            assert(next == 0 <==> k + 1 == o.order@.len());
            assert forall|i: int, j: int| 0 <= i < j < n.len() implies n[i] != n[j] by {
                let ii = if i < k { i } else { i + 1 };
                let jj = if j < k { j } else { j + 1 };
                assert(o.order@[ii] == n[i] && o.order@[jj] == n[j]);
            }
            assert forall|x: int| #[trigger] self.perms@.contains_key(x) <==> n.contains(x) by {
                if n.contains(x) {
                    let m = choose|m: int| 0 <= m < n.len() && n[m] == x;
                    let mm = if m < k { m } else { m + 1 };
                    assert(o.order@[mm] == x);
                    assert(o.order@.contains(x));
                }
                if self.perms@.contains_key(x) {
                    assert(o.order@.contains(x));
                    let m = choose|m: int| 0 <= m < o.order@.len() && o.order@[m] == x;
                    assert(m != k);
                    if m < k {
                        assert(n[m] == x);
                    } else {
                        assert(n[m - 1] == x);
                    }
                }
            }
            assert forall|i: int| 0 <= i < n.len() implies #[trigger] self.linked(i) by {
                let ii = if i < k { i } else { i + 1 };
                o.lemma_at(ii, prov);
                if ii > 0 {
                    o.lemma_at(ii - 1, prov);
                }
                if ii + 1 < o.order@.len() {
                    o.lemma_at(ii + 1, prov);
                }
            }
            assert(self.slabs() =~= o.slabs().remove(a));
        }
        Tracked(perm)
    }
}

} // verus!
