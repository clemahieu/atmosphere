// SPDX-License-Identifier: MIT

//! The boot step that hands the root its free memory: the free runs kernel/src checked at the trust
//! boundary become free pages of the block table, and each maximal aligned block of them an untyped
//! capability at consecutive slots of the root's first leaf from ROOT_UNTYPED_SLOT. See
//! design/root-process-at-boot/ and design/untyped-memory/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::decompose::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::steps::Steps;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;

/// How many untyped capabilities the root's first leaf holds, from ROOT_UNTYPED_SLOT to its last slot.
pub const ROOT_UNTYPED_SLOTS: usize = 123;

/// The blocks of order at most cap the runs decompose into, run by run, each as its first page and its
/// order.
pub open spec fn runs_blocks(runs: Seq<(usize, usize)>, cap: nat) -> Seq<(nat, nat)>
    decreases runs.len(),
{
    if runs.len() == 0 {
        Seq::empty()
    } else {
        runs_blocks(runs.drop_last(), cap) + run_blocks(runs.last().0 as nat, runs.last().1 as nat, cap)
    }
}

/// Page x is in run a.
pub open spec fn in_run_at(runs: Seq<(usize, usize)>, a: int, x: int) -> bool {
    runs[a].0 as int <= x < runs[a].0 + runs[a].1
}

/// Page x is in one of the first r runs.
pub open spec fn in_runs(runs: Seq<(usize, usize)>, r: int, x: int) -> bool {
    exists|a: int| 0 <= a < r && #[trigger] in_run_at(runs, a, x)
}

/// The runs lie inside NUM_PAGES and no page is in two of them.
pub open spec fn runs_wf(runs: Seq<(usize, usize)>) -> bool {
    &&& forall|a: int| #![trigger runs[a]] 0 <= a < runs.len() ==> runs[a].0 + runs[a].1 <= NUM_PAGES
    &&& forall|a: int, b: int, x: int|
        0 <= a < runs.len() && 0 <= b < runs.len() && a != b ==> !(#[trigger] in_run_at(runs, a, x) && #[trigger] in_run_at(
            runs,
            b,
            x,
        ))
}

/// o is a page of block b, given as its first page and its order, as reach names pages.
pub open spec fn block_in(b: (nat, nat), o: usize) -> bool {
    in_block((b.0 * PAGE_SZ) as usize, b.1 as u8, o)
}

/// o is a page of one of the first k blocks.
pub open spec fn in_blocks(bs: Seq<(nat, nat)>, k: int, o: usize) -> bool {
    exists|t: int| 0 <= t < k && #[trigger] block_in(bs[t], o)
}

/// The blocks of the first r + 1 runs are those of the first r, then those of run r.
pub proof fn lemma_runs_blocks_step(runs: Seq<(usize, usize)>, r: int, cap: nat)
    requires
        0 <= r < runs.len(),
    ensures
        runs_blocks(runs.take(r + 1), cap) == runs_blocks(runs.take(r), cap) + run_blocks(runs[r].0 as nat, runs[r].1 as nat, cap),
{
    let s = runs.take(r + 1);
    assert(s.drop_last() =~= runs.take(r));
    assert(s.last() == runs[r]);
}

/// The blocks of the first r runs begin the blocks of all of them.
pub proof fn lemma_runs_blocks_prefix(runs: Seq<(usize, usize)>, r: int, cap: nat)
    requires
        0 <= r <= runs.len(),
    ensures
        runs_blocks(runs.take(r), cap).len() <= runs_blocks(runs, cap).len(),
        forall|t: int|
            0 <= t < runs_blocks(runs.take(r), cap).len() ==> #[trigger] runs_blocks(runs.take(r), cap)[t] == runs_blocks(runs, cap)[t],
    decreases runs.len() - r,
{
    if r == runs.len() {
        assert(runs.take(r) =~= runs);
    } else {
        lemma_runs_blocks_prefix(runs, r + 1, cap);
        lemma_runs_blocks_step(runs, r, cap);
        let a = runs_blocks(runs.take(r), cap);
        let b = runs_blocks(runs.take(r + 1), cap);
        assert forall|t: int| 0 <= t < a.len() implies #[trigger] a[t] == runs_blocks(runs, cap)[t] by {
            assert(b[t] == a[t]);
        }
    }
}

/// The blocks of the runs are each of order at most the cap, aligned to its size, inside NUM_PAGES and
/// named by an untyped capability that is payload_wf, pairwise disjoint, and together exactly the runs'
/// pages.
pub proof fn lemma_runs_blocks(runs: Seq<(usize, usize)>, cap: nat)
    requires
        runs_wf(runs),
        cap <= MAX_ORDER,
    ensures
        forall|t: int|
            0 <= t < runs_blocks(runs, cap).len() ==> {
                let b = #[trigger] runs_blocks(runs, cap)[t];
                &&& b.1 <= cap
                &&& b.0 % pow2(b.1) == 0
                &&& b.0 + pow2(b.1) <= NUM_PAGES
                &&& payload_wf(page_block_payload(b))
            },
        forall|t: int, u: int, x: nat|
            0 <= t < runs_blocks(runs, cap).len() && 0 <= u < runs_blocks(runs, cap).len() && t != u
                ==> !(#[trigger] in_page_block(runs_blocks(runs, cap)[t], x) && #[trigger] in_page_block(
                runs_blocks(runs, cap)[u],
                x,
            )),
        forall|x: nat|
            #[trigger] in_runs(runs, runs.len() as int, x as int) <==> exists|t: int|
                0 <= t < runs_blocks(runs, cap).len() && #[trigger] in_page_block(runs_blocks(runs, cap)[t], x),
    decreases runs.len(),
{
    if runs.len() == 0 {
        return;
    }
    let n = runs.len() - 1;
    let s = runs.drop_last();
    let last = runs[n];
    assert forall|a: int| 0 <= a < s.len() implies #[trigger] s[a] == runs[a] by {}
    assert(runs_wf(s)) by {
        assert forall|a: int| #![trigger s[a]] 0 <= a < s.len() implies s[a].0 + s[a].1 <= NUM_PAGES by {
            assert(s[a] == runs[a]);
        }
        assert forall|a: int, b: int, x: int| 0 <= a < s.len() && 0 <= b < s.len() && a != b implies !(#[trigger] in_run_at(
            s,
            a,
            x,
        ) && #[trigger] in_run_at(s, b, x)) by {
            assert(s[a] == runs[a]);
            assert(s[b] == runs[b]);
            assert(!(in_run_at(runs, a, x) && in_run_at(runs, b, x)));
        }
    }
    lemma_runs_blocks(s, cap);
    assert(last.0 + last.1 <= NUM_PAGES);
    lemma_run_blocks(last.0 as nat, last.1 as nat, cap);
    let p = runs_blocks(s, cap);
    let l = run_blocks(last.0 as nat, last.1 as nat, cap);
    let bs = runs_blocks(runs, cap);
    assert(bs == p + l);
    assert forall|t: int| 0 <= t < bs.len() implies {
        let b = #[trigger] bs[t];
        &&& b.1 <= cap
        &&& b.0 % pow2(b.1) == 0
        &&& b.0 + pow2(b.1) <= NUM_PAGES
        &&& payload_wf(page_block_payload(b))
    } by {
        if t < p.len() {
            assert(bs[t] == p[t]);
        } else {
            let u = t - p.len();
            let b = l[u];
            assert(bs[t] == b);
            lemma_pow2_pos(b.1);
            let x = (b.0 + pow2(b.1) - 1) as nat;
            assert(in_page_block(l[u], x));
            assert(in_run(last.0 as nat, last.1 as nat, x));
        }
    }
    assert forall|t: int, u: int, x: nat| 0 <= t < bs.len() && 0 <= u < bs.len() && t != u implies !(#[trigger] in_page_block(
        bs[t],
        x,
    ) && #[trigger] in_page_block(bs[u], x)) by {
        if in_page_block(bs[t], x) && in_page_block(bs[u], x) {
            if t < p.len() && u < p.len() {
                assert(bs[t] == p[t]);
                assert(bs[u] == p[u]);
                assert(!(in_page_block(p[t], x) && in_page_block(p[u], x)));
            } else if t >= p.len() && u >= p.len() {
                assert(bs[t] == l[t - p.len()]);
                assert(bs[u] == l[u - p.len()]);
                assert(!(in_page_block(l[t - p.len()], x) && in_page_block(l[u - p.len()], x)));
            } else {
                let tp = if t < p.len() { t } else { u };
                let ul = if t < p.len() { u } else { t };
                assert(bs[tp] == p[tp]);
                assert(bs[ul] == l[ul - p.len()]);
                assert(in_page_block(p[tp], x));
                assert(in_runs(s, s.len() as int, x as int));
                let a = choose|a: int| 0 <= a < s.len() && #[trigger] in_run_at(s, a, x as int);
                assert(s[a] == runs[a]);
                assert(in_page_block(l[ul - p.len()], x));
                assert(in_run(last.0 as nat, last.1 as nat, x));
                assert(in_run_at(runs, a, x as int));
                assert(in_run_at(runs, n, x as int));
                assert(!(in_run_at(runs, a, x as int) && in_run_at(runs, n, x as int)));
            }
        }
    }
    assert forall|x: nat| #[trigger] in_runs(runs, runs.len() as int, x as int) <==> exists|t: int|
        0 <= t < bs.len() && #[trigger] in_page_block(bs[t], x) by {
        if in_runs(runs, runs.len() as int, x as int) {
            let a = choose|a: int| 0 <= a < runs.len() && #[trigger] in_run_at(runs, a, x as int);
            if a < n {
                assert(s[a] == runs[a]);
                assert(in_run_at(s, a, x as int));
                assert(in_runs(s, s.len() as int, x as int));
                let t = choose|t: int| 0 <= t < p.len() && #[trigger] in_page_block(p[t], x);
                assert(bs[t] == p[t]);
                assert(in_page_block(bs[t], x));
            } else {
                assert(in_run(last.0 as nat, last.1 as nat, x));
                let u = choose|u: int| 0 <= u < l.len() && #[trigger] in_page_block(l[u], x);
                assert(bs[p.len() + u] == l[u]);
                assert(in_page_block(bs[p.len() + u], x));
            }
        }
        if exists|t: int| 0 <= t < bs.len() && #[trigger] in_page_block(bs[t], x) {
            let t = choose|t: int| 0 <= t < bs.len() && #[trigger] in_page_block(bs[t], x);
            if t < p.len() {
                assert(bs[t] == p[t]);
                assert(in_page_block(p[t], x));
                assert(in_runs(s, s.len() as int, x as int));
                let a = choose|a: int| 0 <= a < s.len() && #[trigger] in_run_at(s, a, x as int);
                assert(s[a] == runs[a]);
                assert(in_run_at(runs, a, x as int));
            } else {
                let u = t - p.len();
                assert(bs[t] == l[u]);
                assert(in_page_block(l[u], x));
                assert(in_run(last.0 as nat, last.1 as nat, x));
                assert(in_run_at(runs, n, x as int));
            }
            assert(in_runs(runs, runs.len() as int, x as int));
        }
    }
}

/// Reach names a block's pages by address: o is one of them exactly when it is a page address whose
/// page is in the block.
pub proof fn lemma_block_in(b: (nat, nat), o: usize)
    requires
        b.1 <= MAX_ORDER,
        b.0 + pow2(b.1) <= NUM_PAGES,
    ensures
        block_in(b, o) <==> (o % PAGE_SZ == 0 && in_page_block(b, (o / PAGE_SZ) as nat)),
{
    lemma_pow2_pos(b.1);
    let p = pow2(b.1);
    assert((b.1 as u8) as nat == b.1);
    assert(block_bytes(b.1 as u8) == p * PAGE_SZ);
    assert(b.0 * PAGE_SZ <= NUM_PAGES * PAGE_SZ) by (nonlinear_arith)
        requires
            b.0 <= NUM_PAGES,
    ;
    let base = (b.0 * PAGE_SZ) as usize;
    assert(base == b.0 * PAGE_SZ);
    lemma_fundamental_div_mod(o as int, PAGE_SZ as int);
    let q = o as int / PAGE_SZ as int;
    if o % PAGE_SZ == 0 {
        assert(o == q * PAGE_SZ);
        assert((base <= o && o < base + p * PAGE_SZ) <==> (b.0 <= q && q < b.0 + p)) by (nonlinear_arith)
            requires
                base == b.0 * PAGE_SZ,
                o == q * PAGE_SZ,
        ;
    }
}

/// Counts the blocks the runs decompose into, or refuses when there are more than the root's first leaf
/// has untyped slots for.
fn count_blocks(runs: &[(usize, usize)]) -> (ret: Option<usize>)
    requires
        runs_wf(runs@),
    ensures
        ret matches Some(count) ==> count == runs_blocks(runs@, MAX_ORDER as nat).len() && count <= ROOT_UNTYPED_SLOTS,
        ret is None ==> runs_blocks(runs@, MAX_ORDER as nat).len() > ROOT_UNTYPED_SLOTS,
{
    let mut count: usize = 0;
    let mut r: usize = 0;
    while r < runs.len()
        invariant
            r <= runs@.len(),
            runs_wf(runs@),
            count == runs_blocks(runs@.take(r as int), MAX_ORDER as nat).len(),
            count <= ROOT_UNTYPED_SLOTS,
        decreases runs@.len() - r,
    {
        let (start, n) = runs[r];
        proof {
            lemma_runs_blocks_step(runs@, r as int, MAX_ORDER as nat);
            assert(runs@[r as int] == (start, n));
            assert(start + n <= NUM_PAGES);
        }
        let mut s = start;
        let mut m = n;
        while m > 0
            invariant
                r < runs@.len(),
                runs_wf(runs@),
                s + m <= NUM_PAGES,
                count + run_blocks(s as nat, m as nat, MAX_ORDER as nat).len() == runs_blocks(runs@.take(r as int + 1), MAX_ORDER as nat).len(),
                count <= ROOT_UNTYPED_SLOTS,
            decreases m,
        {
            // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
            let tracked mut steps = Steps::fresh();
            let (o, size) = first_block(s, m, MAX_ORDER, Tracked(&mut steps));
            proof {
                assert(run_blocks(s as nat, m as nat, MAX_ORDER as nat) == seq![(s as nat, o as nat)] + run_blocks(
                    (s + size) as nat,
                    (m - size) as nat,
                MAX_ORDER as nat));
            }
            if count == ROOT_UNTYPED_SLOTS {
                proof {
                    lemma_runs_blocks_prefix(runs@, r as int + 1, MAX_ORDER as nat);
                }
                return None;
            }
            count = count + 1;
            s = s + size;
            m = m - size;
        }
        r = r + 1;
    }
    proof {
        assert(runs@.take(runs@.len() as int) =~= runs@);
    }
    Some(count)
}

impl CapKernel {
    /// Slot ROOT_UNTYPED_SLOT + t of the root's first leaf holds the untyped capability for block b,
    /// below the list's synthetic root.
    pub open spec fn root_untyped_at(&self, root: usize, process: usize, leaf: usize, t: int, b: (nat, nat)) -> bool {
        let n = (leaf + ROOT_UNTYPED_SLOT + t) as usize;
        &&& self.tables.has_slot(&self.list, process, (ROOT_UNTYPED_SLOT + t) as usize)
        &&& self.tables.node_of(process, (ROOT_UNTYPED_SLOT + t) as usize) == n
        &&& self.is_cap(n)
        &&& self.payload_of(n) == page_block_payload(b)
        &&& self.list.is_child(root, n)
        &&& self.list.nodes@[n as int].depth == 1
    }

    /// Hands every page of the runs to the block table, as free.
    #[verifier::spinoff_prover]
    fn free_runs(&mut self, runs: &[(usize, usize)], Tracked(pages): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            runs_wf(runs@),
            forall|i: int| old(self).blocks.tracks(i) && in_runs(runs@, runs@.len() as int, i)
                ==> (#[trigger] old(self).blocks.pages@[i]).kind is Reserved,
            forall|i: usize| in_runs(runs@, runs@.len() as int, i as int) ==> #[trigger] holds(pages, i),
            forall|p: usize| #[trigger] old(self).list.pages@.dom().contains(p) && old(self).blocks.tracks_addr(p)
                ==> !in_runs(runs@, runs@.len() as int, (p / PAGE_SZ) as int),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).wf(),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            final(self).table_pages == old(self).table_pages,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|i: int| old(self).blocks.tracks(i) ==> #[trigger] final(self).blocks.pages@[i]
                == if in_runs(runs@, runs@.len() as int, i) { free_entry() } else { old(self).blocks.pages@[i] },
    {
        let ghost pre = *old(self);
        let tracked mut pages = pages;
        proof {
            assert forall|a: int, i: usize| 0 <= a < runs@.len() && #[trigger] in_run_at(runs@, a, i as int)
                implies #[trigger] holds(pages, i) by {
                assert(in_runs(runs@, runs@.len() as int, i as int));
            }
        }
        let mut r: usize = 0;
        while r < runs.len()
            invariant
                r <= runs@.len(),
                runs_wf(runs@),
                self.wf(),
                self.list == pre.list,
                self.tables == pre.tables,
                self.table_pages == pre.table_pages,
                self.spaces == pre.spaces,
                self.mappings == pre.mappings,
                self.cores == pre.cores,
                self.flush_epoch == pre.flush_epoch,
                self.tlb == pre.tlb,
                self.iommus == pre.iommus,
                self.mapped == pre.mapped,
                self.stale_epoch == pre.stale_epoch,
                self.flush_epoch == pre.flush_epoch,
                self.devices == pre.devices,
                self.threads == pre.threads,
                self.processes == pre.processes,
                self.frames == pre.frames,
                self.zeroing == pre.zeroing,
                self.holders == pre.holders,
                self.stop_ipis == pre.stop_ipis,
                self.blocks.regions_2m@ == pre.blocks.regions_2m@,
                self.blocks.regions_1g@ == pre.blocks.regions_1g@,
                forall|i: int| pre.blocks.tracks(i) ==> #[trigger] self.blocks.pages@[i]
                    == if in_runs(runs@, r as int, i) { free_entry() } else { pre.blocks.pages@[i] },
                forall|i: int| pre.blocks.tracks(i) && in_runs(runs@, runs@.len() as int, i)
                    ==> (#[trigger] pre.blocks.pages@[i]).kind is Reserved,
                forall|a: int, i: usize| r <= a < runs@.len() && #[trigger] in_run_at(runs@, a, i as int)
                    ==> #[trigger] holds(pages, i),
                forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                    ==> !in_runs(runs@, runs@.len() as int, (p / PAGE_SZ) as int),
            decreases runs@.len() - r,
        {
            let (start, n) = runs[r];
            let ghost before = *self;
            let ghost given = pages;
            proof {
                assert(runs@[r as int] == (start, n));
                assert(before.blocks.tracks_run(start as int, n as int));
                assert forall|i: int| start <= i < start + n implies #[trigger] before.blocks.pages@[i].kind is Reserved by {
                    assert(in_run_at(runs@, r as int, i));
                    if in_runs(runs@, r as int, i) {
                        let a = choose|a: int| 0 <= a < r && #[trigger] in_run_at(runs@, a, i);
                        assert(!(in_run_at(runs@, a, i) && in_run_at(runs@, r as int, i)));
                    }
                    assert(in_runs(runs@, runs@.len() as int, i));
                    assert(before.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
                assert forall|i: usize| start <= i < start + n implies #[trigger] holds(pages, i) by {
                    assert(in_run_at(runs@, r as int, i as int));
                }
            }
            add_free_run(&mut self.blocks, start, n, Tracked(&mut pages));
            proof {
                let after = *self;
                assert forall|p: usize| #[trigger] before.list.pages@.dom().contains(p) && before.blocks.tracks_addr(p)
                    implies !(start <= p / PAGE_SZ < start + n) by {
                    if start <= p / PAGE_SZ < start + n {
                        assert(in_run_at(runs@, r as int, (p / PAGE_SZ) as int));
                        assert(in_runs(runs@, runs@.len() as int, (p / PAGE_SZ) as int));
                    }
                }
                Self::lemma_reserved_freed(before, after, start, n);
                assert forall|a: int, i: usize| r + 1 <= a < runs@.len() && #[trigger] in_run_at(runs@, a, i as int)
                    implies #[trigger] holds(pages, i) by {
                    assert(holds(given, i));
                    assert(!(in_run_at(runs@, a, i as int) && in_run_at(runs@, r as int, i as int)));
                }
                assert forall|i: int| pre.blocks.tracks(i) implies #[trigger] after.blocks.pages@[i]
                    == if in_runs(runs@, r + 1, i) { free_entry() } else { pre.blocks.pages@[i] } by {
                    if start <= i < start + n {
                        assert(in_run_at(runs@, r as int, i));
                        assert(in_runs(runs@, r + 1, i));
                    } else if in_runs(runs@, r + 1, i) {
                        let a = choose|a: int| 0 <= a < r + 1 && #[trigger] in_run_at(runs@, a, i);
                        assert(a != r);
                        assert(in_runs(runs@, r as int, i));
                    } else {
                        if in_runs(runs@, r as int, i) {
                            let a = choose|a: int| 0 <= a < r && #[trigger] in_run_at(runs@, a, i);
                            assert(in_runs(runs@, r + 1, i));
                        }
                    }
                }
            }
            r = r + 1;
        }
    }

    /// Puts the untyped capability for each block of the runs at consecutive slots of the root's first
    /// leaf from ROOT_UNTYPED_SLOT.
    #[verifier::spinoff_prover]
    fn untyped_runs(&mut self, root: usize, process: usize, leaf: usize, runs: &[(usize, usize)])
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.has_slot(&old(self).list, process, ROOT_PROCESS_SLOT),
            old(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
            forall|j: int| leaf + ROOT_UNTYPED_SLOT <= j < leaf + NODES_PER_PAGE ==> !#[trigger] old(self).list.nodes@[j].live,
            runs_wf(runs@),
            runs_blocks(runs@, MAX_ORDER as nat).len() <= ROOT_UNTYPED_SLOTS,
            no_device_space(&old(self).spaces),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).wf(),
            final(self).list.seq@[0] == root,
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.has_slot(&final(self).list, process, ROOT_PROCESS_SLOT),
            final(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
            forall|t: int| #![trigger runs_blocks(runs@, MAX_ORDER as nat)[t]] 0 <= t < runs_blocks(runs@, MAX_ORDER as nat).len()
                ==> final(self).root_untyped_at(root, process, leaf, t, runs_blocks(runs@, MAX_ORDER as nat)[t]),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE
                && !(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + runs_blocks(runs@, MAX_ORDER as nat).len())
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|x: usize| #![trigger old(self).is_cap(x)]
                !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + runs_blocks(runs@, MAX_ORDER as nat).len())
                && old(self).is_cap(x) ==> final(self).is_cap(x) && final(self).payload_of(x) == old(self).payload_of(x),
            final(self).table_pages == old(self).table_pages,
            final(self).blocks == old(self).blocks,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            final(self).list.pages@.dom() == old(self).list.pages@.dom(),
            forall|o: usize| #[trigger] final(self).view().reach(process, o)
                <==> (old(self).view().reach(process, o) || in_blocks(runs_blocks(runs@, MAX_ORDER as nat), runs_blocks(runs@, MAX_ORDER as nat).len() as int, o)),
            forall|q: usize, o: usize| #[trigger] final(self).view().reach(q, o) && !old(self).view().reach(q, o)
                ==> in_blocks(runs_blocks(runs@, MAX_ORDER as nat), runs_blocks(runs@, MAX_ORDER as nat).len() as int, o),
    {
        let ghost pre = *old(self);
        let ghost bs = runs_blocks(runs@, MAX_ORDER as nat);
        proof {
            lemma_runs_blocks(runs@, MAX_ORDER as nat);
            pre.lemma_slot(process, ROOT_PROCESS_SLOT);
            assert(index_ok(127usize)) by (compute_only);
            assert(index_entry(127usize) == 0) by (compute_only);
            assert(index_slot(127usize) == 127) by (compute_only);
            assert(index_entry(ROOT_PROCESS_SLOT) == 0) by (compute_only);
            assert(index_slot(ROOT_PROCESS_SLOT) == 1) by (compute_only);
            assert(pre.tables.leaf(process, 0) == leaf);
            assert(pre.tables.has_slot(&pre.list, process, 127usize));
            pre.lemma_slot(process, 127usize);
            assert(pre.tables.node_of(process, 127usize) == leaf + 127);
            pre.lemma_slot_bound((leaf + 127) as usize);
        }
        let mut k: usize = 0;
        let mut r: usize = 0;
        while r < runs.len()
            invariant
                self.stale_epoch == pre.stale_epoch,
                self.flush_epoch == pre.flush_epoch,
                self.devices == pre.devices,
                self.iommus.present == pre.iommus.present,
                r <= runs@.len(),
                runs_wf(runs@),
                bs == runs_blocks(runs@, MAX_ORDER as nat),
                bs.len() <= ROOT_UNTYPED_SLOTS,
                leaf + NODES_PER_PAGE <= NODE_SPACE,
                k == runs_blocks(runs@.take(r as int), MAX_ORDER as nat).len(),
                forall|t: int| 0 <= t < bs.len() ==> payload_wf(page_block_payload(#[trigger] bs[t])),
                self.wf(),
                self.list.seq@[0] == root,
                self.tables.has_slot(&self.list, process, ROOT_PROCESS_SLOT),
                self.tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
                self.tables.roots == pre.tables.roots,
                self.tables.owner == pre.tables.owner,
                self.blocks == pre.blocks,
                self.threads == pre.threads,
                self.processes == pre.processes,
                self.spaces == pre.spaces,
                no_device_space(&pre.spaces),
                self.list.pages@.dom() == pre.list.pages@.dom(),
                forall|j: int| #![trigger self.list.nodes@[j]] 0 <= j < NODE_SPACE
                    && !(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + k)
                    ==> self.list.nodes@[j].live == pre.list.nodes@[j].live,
                forall|x: usize| #![trigger pre.is_cap(x)] !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + k) && pre.is_cap(x)
                    ==> self.is_cap(x) && self.payload_of(x) == pre.payload_of(x),
                self.table_pages == pre.table_pages,
                forall|j: int| leaf + ROOT_UNTYPED_SLOT + k <= j < leaf + NODES_PER_PAGE ==> !#[trigger] self.list.nodes@[j].live,
                forall|t: int| #![trigger bs[t]] 0 <= t < k ==> self.root_untyped_at(root, process, leaf, t, bs[t]),
                forall|o: usize| #[trigger] self.view().reach(process, o) <==> (pre.view().reach(process, o) || in_blocks(bs, k as int, o)),
                forall|q: usize, o: usize| #[trigger] self.view().reach(q, o) && !pre.view().reach(q, o) ==> in_blocks(bs, k as int, o),
            decreases runs@.len() - r,
        {
            let (start, n) = runs[r];
            proof {
                assert(runs@[r as int] == (start, n));
                assert(pre.blocks.tracks_run(start as int, n as int));
                lemma_runs_blocks_step(runs@, r as int, MAX_ORDER as nat);
                lemma_runs_blocks_prefix(runs@, r as int + 1, MAX_ORDER as nat);
                let c = runs_blocks(runs@.take(r as int + 1), MAX_ORDER as nat);
                let rb = run_blocks(start as nat, n as nat, MAX_ORDER as nat);
                assert forall|u: int| 0 <= u < rb.len() implies bs[k + u] == #[trigger] rb[u] by {
                    assert(c[k + u] == rb[u]);
                }
            }
            let mut s = start;
            let mut m = n;
            while m > 0
                invariant
                    self.stale_epoch == pre.stale_epoch,
                    self.flush_epoch == pre.flush_epoch,
                    r < runs@.len(),
                    runs_wf(runs@),
                    bs == runs_blocks(runs@, MAX_ORDER as nat),
                    bs.len() <= ROOT_UNTYPED_SLOTS,
                    leaf + NODES_PER_PAGE <= NODE_SPACE,
                    pre.blocks.tracks_run(s as int, m as int),
                    k + run_blocks(s as nat, m as nat, MAX_ORDER as nat).len() == runs_blocks(runs@.take(r as int + 1), MAX_ORDER as nat).len(),
                    runs_blocks(runs@.take(r as int + 1), MAX_ORDER as nat).len() <= bs.len(),
                    forall|u: int| 0 <= u < run_blocks(s as nat, m as nat, MAX_ORDER as nat).len() ==> bs[k + u] == #[trigger] run_blocks(
                        s as nat,
                        m as nat,
                    MAX_ORDER as nat)[u],
                    forall|t: int| 0 <= t < bs.len() ==> payload_wf(page_block_payload(#[trigger] bs[t])),
                    self.wf(),
                    self.devices == pre.devices,
                    self.iommus.present == pre.iommus.present,
                    self.list.seq@[0] == root,
                    self.tables.has_slot(&self.list, process, ROOT_PROCESS_SLOT),
                    self.tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
                    self.tables.roots == pre.tables.roots,
                    self.tables.owner == pre.tables.owner,
                    self.blocks == pre.blocks,
                    self.threads == pre.threads,
                    self.processes == pre.processes,
                    self.spaces == pre.spaces,
                    no_device_space(&pre.spaces),
                    self.list.pages@.dom() == pre.list.pages@.dom(),
                    forall|j: int| #![trigger self.list.nodes@[j]] 0 <= j < NODE_SPACE
                        && !(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + k)
                        ==> self.list.nodes@[j].live == pre.list.nodes@[j].live,
                    forall|x: usize| #![trigger pre.is_cap(x)] !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + k) && pre.is_cap(x)
                        ==> self.is_cap(x) && self.payload_of(x) == pre.payload_of(x),
                    self.table_pages == pre.table_pages,
                    forall|j: int| leaf + ROOT_UNTYPED_SLOT + k <= j < leaf + NODES_PER_PAGE ==> !#[trigger] self.list.nodes@[j].live,
                    forall|t: int| #![trigger bs[t]] 0 <= t < k ==> self.root_untyped_at(root, process, leaf, t, bs[t]),
                    forall|o: usize| #[trigger] self.view().reach(process, o) <==> (pre.view().reach(process, o) || in_blocks(bs, k as int, o)),
                    forall|q: usize, o: usize| #[trigger] self.view().reach(q, o) && !pre.view().reach(q, o) ==> in_blocks(bs, k as int, o),
                decreases m,
            {
                // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
                let tracked mut steps = Steps::fresh();
                let (o, size) = first_block(s, m, MAX_ORDER, Tracked(&mut steps));
                let ghost cur = *self;
                let ghost rb = run_blocks(s as nat, m as nat, MAX_ORDER as nat);
                let ghost rest = run_blocks((s + size) as nat, (m - size) as nat, MAX_ORDER as nat);
                proof {
                    assert(rb == seq![(s as nat, o as nat)] + rest);
                    assert(rb[0] == (s as nat, o as nat));
                    assert(bs[k as int] == rb[0]);
                    assert(k < bs.len());
                    assert(payload_wf(page_block_payload(bs[k as int])));
                    assert((s as nat * PAGE_SZ) as usize == s * PAGE_SZ);
                    assert(page_block_payload(bs[k as int]) == untyped_payload((s * PAGE_SZ) as usize, o));
                    assert(!cur.list.nodes@[leaf + (ROOT_UNTYPED_SLOT + k)].live);
                }
                self.boot_root_untyped(root, process, leaf, ROOT_UNTYPED_SLOT + k, s * PAGE_SZ, o);
                proof {
                    let post = *self;
                    assert forall|x: usize| #[trigger] block_in(bs[k as int], x) == in_block((s * PAGE_SZ) as usize, o, x) by {}
                    assert forall|u: int| 0 <= u < rest.len() implies bs[k + 1 + u] == #[trigger] rest[u] by {
                        assert(rb[u + 1] == rest[u]);
                        assert(bs[k + (u + 1)] == rb[u + 1]);
                    }
                    Self::lemma_untyped_step(pre, cur, post, root, process, leaf, bs, k as int, (s * PAGE_SZ) as usize, o);
                }
                k = k + 1;
                s = s + size;
                m = m - size;
            }
            r = r + 1;
        }
        proof {
            assert(runs@.take(runs@.len() as int) =~= runs@);
        }
    }

    /// One untyped capability more, at slot ROOT_UNTYPED_SLOT + k as boot_root_untyped puts it, keeps
    /// what untyped_runs says of the first k blocks and says it of the first k + 1.
    proof fn lemma_untyped_step(
        pre: Self,
        cur: Self,
        post: Self,
        root: usize,
        process: usize,
        leaf: usize,
        bs: Seq<(nat, nat)>,
        k: int,
        base: usize,
        order: u8,
    )
        requires
            0 <= k < bs.len(),
            leaf + NODES_PER_PAGE <= NODE_SPACE,
            ROOT_UNTYPED_SLOT + k < NODES_PER_PAGE,
            page_block_payload(bs[k]) == untyped_payload(base, order),
            forall|x: usize| #[trigger] block_in(bs[k], x) == in_block(base, order, x),
            cur.list.seq@[0] == root,
            forall|j: int| #![trigger cur.list.nodes@[j]] 0 <= j < NODE_SPACE
                && !(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + k)
                ==> cur.list.nodes@[j].live == pre.list.nodes@[j].live,
            forall|x: usize| #![trigger pre.is_cap(x)] !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + k) && pre.is_cap(x)
                ==> cur.is_cap(x) && cur.payload_of(x) == pre.payload_of(x),
            forall|j: int| leaf + ROOT_UNTYPED_SLOT + k <= j < leaf + NODES_PER_PAGE ==> !#[trigger] cur.list.nodes@[j].live,
            forall|t: int| #![trigger bs[t]] 0 <= t < k ==> cur.root_untyped_at(root, process, leaf, t, bs[t]),
            forall|o: usize| #[trigger] cur.view().reach(process, o) <==> (pre.view().reach(process, o) || in_blocks(bs, k, o)),
            forall|q: usize, o: usize| #[trigger] cur.view().reach(q, o) && !pre.view().reach(q, o) ==> in_blocks(bs, k, o),
            post.wf(),
            post.list.seq@[0] == root,
            post.tables.roots == cur.tables.roots,
            post.tables.has_slot(&post.list, process, ROOT_PROCESS_SLOT),
            post.tables.has_slot(&post.list, process, (ROOT_UNTYPED_SLOT + k) as usize),
            post.tables.node_of(process, (ROOT_UNTYPED_SLOT + k) as usize) == leaf + ROOT_UNTYPED_SLOT + k,
            post.is_cap((leaf + ROOT_UNTYPED_SLOT + k) as usize),
            post.payload_of((leaf + ROOT_UNTYPED_SLOT + k) as usize) == untyped_payload(base, order),
            post.list.is_child(root, (leaf + ROOT_UNTYPED_SLOT + k) as usize),
            post.list.nodes@[leaf + ROOT_UNTYPED_SLOT + k].depth == 1,
            Self::adds_cap(cur, post, (leaf + ROOT_UNTYPED_SLOT + k) as usize),
            forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j != leaf + ROOT_UNTYPED_SLOT + k
                ==> post.list.nodes@[j].live == cur.list.nodes@[j].live
                && post.list.nodes@[j].depth == cur.list.nodes@[j].depth,
            post.list.parent@ == cur.list.parent@.insert((leaf + ROOT_UNTYPED_SLOT + k) as usize, root),
            forall|o: usize| #[trigger] post.view().reach(process, o)
                <==> (cur.view().reach(process, o) || in_block(base, order, o)),
            forall|q: usize, o: usize| #[trigger] post.view().reach(q, o) && !cur.view().reach(q, o)
                ==> in_block(base, order, o),
        ensures
            forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE
                && !(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + k + 1)
                ==> post.list.nodes@[j].live == pre.list.nodes@[j].live,
            forall|x: usize| #![trigger pre.is_cap(x)] !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + k + 1) && pre.is_cap(x)
                ==> post.is_cap(x) && post.payload_of(x) == pre.payload_of(x),
            forall|j: int| leaf + ROOT_UNTYPED_SLOT + k + 1 <= j < leaf + NODES_PER_PAGE ==> !#[trigger] post.list.nodes@[j].live,
            forall|t: int| #![trigger bs[t]] 0 <= t < k + 1 ==> post.root_untyped_at(root, process, leaf, t, bs[t]),
            forall|o: usize| #[trigger] post.view().reach(process, o) <==> (pre.view().reach(process, o) || in_blocks(bs, k + 1, o)),
            forall|q: usize, o: usize| #[trigger] post.view().reach(q, o) && !pre.view().reach(q, o) ==> in_blocks(bs, k + 1, o),
    {
        let c = (leaf + ROOT_UNTYPED_SLOT + k) as usize;
        assert(index_entry(ROOT_PROCESS_SLOT) == 0) by (compute_only);
        assert forall|x: usize| #![trigger pre.is_cap(x)] !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + k + 1) && pre.is_cap(x)
            implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            assert(cur.is_cap(x) && cur.payload_of(x) == pre.payload_of(x));
            assert(x != c);
            assert(post.is_cap(x) == cur.is_cap(x));
            assert(post.payload_of(x) == cur.payload_of(x));
        }
        assert forall|t: int| #![trigger bs[t]] 0 <= t < k + 1 implies post.root_untyped_at(root, process, leaf, t, bs[t]) by {
            if t < k {
                let x = (leaf + ROOT_UNTYPED_SLOT + t) as usize;
                assert(cur.root_untyped_at(root, process, leaf, t, bs[t]));
                assert(x != c);
                assert(cur.is_cap(x));
                assert(post.is_cap(x));
                assert(post.payload_of(x) == cur.payload_of(x));
                assert(index_entry((ROOT_UNTYPED_SLOT + t) as usize) == 0);
                assert(index_ok((ROOT_UNTYPED_SLOT + t) as usize));
                assert(post.tables.has_slot(&post.list, process, (ROOT_UNTYPED_SLOT + t) as usize));
                assert(post.list.nodes@[x as int].live);
                assert(has(post.list.seq@, x));
                lemma_has(post.list.seq@, x);
                assert(post.list.parent@[x] == root);
                assert(post.list.is_child(root, x));
                assert(post.list.nodes@[x as int].depth == 1);
            }
        }
        assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE
            && !(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + k + 1)
            implies post.list.nodes@[j].live == pre.list.nodes@[j].live by {
            assert(cur.list.nodes@[j].live == pre.list.nodes@[j].live);
        }
        assert forall|j: int| leaf + ROOT_UNTYPED_SLOT + k + 1 <= j < leaf + NODES_PER_PAGE
            implies !#[trigger] post.list.nodes@[j].live by {
            assert(!cur.list.nodes@[j].live);
        }
        assert forall|x: usize| #[trigger] post.view().reach(process, x)
            <==> (pre.view().reach(process, x) || in_blocks(bs, k + 1, x)) by {
            if in_blocks(bs, k, x) {
                let t = choose|t: int| 0 <= t < k && #[trigger] block_in(bs[t], x);
                assert(in_blocks(bs, k + 1, x));
            }
            if block_in(bs[k], x) {
                assert(in_blocks(bs, k + 1, x));
            }
            if in_blocks(bs, k + 1, x) {
                let t = choose|t: int| 0 <= t < k + 1 && #[trigger] block_in(bs[t], x);
                if t < k {
                    assert(in_blocks(bs, k, x));
                }
            }
            assert(cur.view().reach(process, x) <==> (pre.view().reach(process, x) || in_blocks(bs, k, x)));
        }
        assert forall|q: usize, x: usize| #[trigger] post.view().reach(q, x) && !pre.view().reach(q, x)
            implies in_blocks(bs, k + 1, x) by {
            if cur.view().reach(q, x) {
                let t = choose|t: int| 0 <= t < k && #[trigger] block_in(bs[t], x);
                assert(in_blocks(bs, k + 1, x));
            } else {
                assert(block_in(bs[k], x));
                assert(in_blocks(bs, k + 1, x));
            }
        }
    }

    /// The step after the root's console and power capabilities: the free runs, which kernel/src checked
    /// are inside NUM_PAGES, pairwise disjoint, every page reserved with its permission handed over and
    /// no list page among them, become free pages of the block table, and each block they decompose
    /// into an untyped capability at consecutive slots from ROOT_UNTYPED_SLOT, below the list's
    /// synthetic root. The root's reach grows by exactly the runs' pages, and nobody else's by anything
    /// outside them. It returns how many blocks there are, and refuses, leaving the state as it was,
    /// when they do not fit in the root's first leaf.
    #[verifier::spinoff_prover]
    pub fn boot_root_memory(
        &mut self,
        root: usize,
        process: usize,
        leaf: usize,
        runs: &[(usize, usize)],
        Tracked(pages): Tracked<Map<usize, PagePerm4k>>,
    ) -> (ret: Option<usize>)
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.has_slot(&old(self).list, process, ROOT_PROCESS_SLOT),
            old(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
            forall|j: int| leaf + ROOT_UNTYPED_SLOT <= j < leaf + NODES_PER_PAGE ==> !#[trigger] old(self).list.nodes@[j].live,
            runs_wf(runs@),
            forall|i: int| old(self).blocks.tracks(i) && in_runs(runs@, runs@.len() as int, i)
                ==> (#[trigger] old(self).blocks.pages@[i]).kind is Reserved,
            forall|i: usize| in_runs(runs@, runs@.len() as int, i as int) ==> #[trigger] holds(pages, i),
            forall|p: usize| #[trigger] old(self).list.pages@.dom().contains(p) && old(self).blocks.tracks_addr(p)
                ==> !in_runs(runs@, runs@.len() as int, (p / PAGE_SZ) as int),
            no_device_space(&old(self).spaces),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            ret is None ==> runs_blocks(runs@, MAX_ORDER as nat).len() > ROOT_UNTYPED_SLOTS && *final(self) == *old(self),
            ret matches Some(count) ==> {
                let bs = runs_blocks(runs@, MAX_ORDER as nat);
                &&& count == bs.len()
                &&& count <= ROOT_UNTYPED_SLOTS
                &&& final(self).wf()
                &&& final(self).list.seq@[0] == root
                &&& final(self).tables.roots == old(self).tables.roots
                &&& final(self).tables.owner == old(self).tables.owner
                &&& final(self).tables.has_slot(&final(self).list, process, ROOT_PROCESS_SLOT)
                &&& final(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1
                &&& forall|t: int| #![trigger bs[t]] 0 <= t < count ==> {
                    &&& final(self).root_untyped_at(root, process, leaf, t, bs[t])
                    &&& bs[t].1 <= MAX_ORDER
                    &&& bs[t].0 % pow2(bs[t].1) == 0
                }
                &&& forall|t: int, u: int, x: nat| 0 <= t < count && 0 <= u < count && t != u
                    ==> !(#[trigger] in_page_block(bs[t], x) && #[trigger] in_page_block(bs[u], x))
                &&& forall|x: nat| #[trigger] in_runs(runs@, runs@.len() as int, x as int)
                    <==> exists|t: int| 0 <= t < count && #[trigger] in_page_block(bs[t], x)
                &&& forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE
                    && !(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + count)
                    ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live
                &&& forall|x: usize| #![trigger old(self).is_cap(x)]
                    !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + count) && old(self).is_cap(x)
                    ==> final(self).is_cap(x) && final(self).payload_of(x) == old(self).payload_of(x)
                &&& final(self).table_pages == old(self).table_pages
                &&& forall|i: int| old(self).blocks.tracks(i) ==> #[trigger] final(self).blocks.pages@[i]
                    == if in_runs(runs@, runs@.len() as int, i) { free_entry() } else { old(self).blocks.pages@[i] }
                &&& final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@
                &&& final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@
                &&& final(self).threads == old(self).threads
                &&& final(self).processes == old(self).processes
                &&& final(self).spaces == old(self).spaces
                &&& final(self).list.pages@.dom() == old(self).list.pages@.dom()
                &&& forall|o: usize| #[trigger] final(self).view().reach(process, o)
                    <==> (old(self).view().reach(process, o) || (o % PAGE_SZ == 0
                        && in_runs(runs@, runs@.len() as int, (o / PAGE_SZ) as int)))
                &&& forall|q: usize, o: usize| #[trigger] final(self).view().reach(q, o) && !old(self).view().reach(q, o)
                    ==> o % PAGE_SZ == 0 && in_runs(runs@, runs@.len() as int, (o / PAGE_SZ) as int)
            },
    {
        let count = match count_blocks(runs) {
            Some(count) => count,
            None => return None,
        };
        let ghost pre = *self;
        self.free_runs(runs, Tracked(pages));
        let ghost mid = *self;
        proof {
            assert(mid.view() == pre.view());
        }
        self.untyped_runs(root, process, leaf, runs);
        proof {
            let post = *self;
            let bs = runs_blocks(runs@, MAX_ORDER as nat);
            let len = runs@.len() as int;
            lemma_runs_blocks(runs@, MAX_ORDER as nat);
            assert forall|x: usize| #![trigger pre.is_cap(x)]
                !(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + count) && pre.is_cap(x)
                implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
                assert(mid.is_cap(x) && mid.payload_of(x) == pre.payload_of(x));
            }
            assert forall|o: usize| #[trigger] in_blocks(bs, bs.len() as int, o)
                <==> (o % PAGE_SZ == 0 && in_runs(runs@, len, (o / PAGE_SZ) as int)) by {
                if in_blocks(bs, bs.len() as int, o) {
                    let t = choose|t: int| 0 <= t < bs.len() && #[trigger] block_in(bs[t], o);
                    lemma_block_in(bs[t], o);
                    assert(in_page_block(bs[t], (o / PAGE_SZ) as nat));
                    assert(in_runs(runs@, len, ((o / PAGE_SZ) as nat) as int));
                }
                if o % PAGE_SZ == 0 && in_runs(runs@, len, (o / PAGE_SZ) as int) {
                    let x = (o / PAGE_SZ) as nat;
                    assert(in_runs(runs@, len, x as int));
                    let t = choose|t: int| 0 <= t < bs.len() && #[trigger] in_page_block(bs[t], x);
                    lemma_block_in(bs[t], o);
                    assert(block_in(bs[t], o));
                    assert(in_blocks(bs, bs.len() as int, o));
                }
            }
            assert forall|o: usize| #[trigger] post.view().reach(process, o)
                <==> (pre.view().reach(process, o) || (o % PAGE_SZ == 0 && in_runs(runs@, len, (o / PAGE_SZ) as int))) by {
                assert(post.view().reach(process, o) <==> (mid.view().reach(process, o) || in_blocks(bs, bs.len() as int, o)));
            }
            assert forall|q: usize, o: usize| #[trigger] post.view().reach(q, o) && !pre.view().reach(q, o)
                implies o % PAGE_SZ == 0 && in_runs(runs@, len, (o / PAGE_SZ) as int) by {
                assert(in_blocks(bs, bs.len() as int, o));
            }
        }
        Some(count)
    }
}

} // verus!
