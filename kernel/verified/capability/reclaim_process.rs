// SPDX-License-Identifier: MIT

//! Retype reclaiming a dead process's block: a retype cuts its address space root's child tables, a
//! slice per step, each cut two-way so the child's parent record goes with the entry. Both roots are
//! inside the process's block, so they go only with the process, once no core depends on the space: a
//! retype first retires a space a core has loaded, and each such core stops depending on it when it
//! acknowledges the retire's flush. A root maps no frame, so it holds no mapping node to unlink. Its capability table's leaves are not
//! detached: each stays in its root entry, inert, until its own untyped's holder retypes it, and that
//! retype's free clears the entry. Once both roots are empty, a retype frees the block. See
//! design/teardown-driven-by-retype/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
#[cfg(verus_keep_ghost)]
use crate::capability::endpoint::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reply::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
use crate::capability::steps::Steps;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::reclaim::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
use crate::capability::unmap::SEND_FLUSH_STEPS;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// The units of a retire: two checks of each core, and a flush IPI to each core on the list.
pub const RETIRE_STEPS: usize = 2 * NUM_CPUS + SEND_FLUSH_STEPS;

impl CapKernel {
    /// The process at `base` is dead with zero references: no capability names it and no thread is
    /// bound to it.
    pub open spec fn process_is_dead(&self, base: usize) -> bool {
        &&& self.processes.records@.contains_key(base)
        &&& self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0
    }

    /// No core has the space of the process at `base` on its loaded list, so none holds a translation
    /// of it.
    pub open spec fn process_unloaded(&self, base: usize) -> bool {
        self.spaces.loaded@[base].value().list == 0u32
    }

    /// No core depends on the space of the process at `base`: each core that has it loaded is past its
    /// retire, so none holds a translation of it or can walk it.
    pub open spec fn process_released(&self, base: usize) -> bool {
        forall|d: int| 0 <= d < NUM_CPUS ==> !#[trigger] self.depends(d, base)
    }

    /// Some core's base register names the space of the process at `base`: that core may walk it, and
    /// a flush leaves it free to fill its TLB from it again.
    pub open spec fn process_space_named(&self, base: usize) -> bool {
        exists|d: int| 0 <= d < NUM_CPUS && #[trigger] self.cores@[d].space == Some(base)
    }

    /// A retype may retire the space of the dead process at `base`: an untyped covers its block, it is
    /// not yet retired, a core depends on it, no core's base register names it, and the flush epoch can
    /// rise.
    pub open spec fn can_retire_process(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, PROCESS_ORDER)
        &&& self.process_is_dead(base)
        &&& self.spaces.loaded@[base].value().retired == 0
        &&& !self.process_released(base)
        &&& !self.process_space_named(base)
        &&& self.flush_epoch < usize::MAX
    }

    /// What retiring the space of the dead process at `base` did to self: the flush epoch rose by one,
    /// the space's retire epoch is the new epoch, a flush IPI went to each core on its list, and nothing
    /// else changed, so every core depends on what it did before. The core that acknowledges the new
    /// epoch no longer depends on the space.
    pub open spec fn process_retired(&self, post: Self, base: usize) -> bool {
        &&& post == (CapKernel { flush_epoch: post.flush_epoch, flush_ipis: post.flush_ipis, spaces: post.spaces, ..*self })
        &&& post.flush_epoch == self.flush_epoch + 1
        &&& post.flush_ipis@ == self.flush_ipis@ + self.flush_targets(base)
        &&& post.spaces == (Spaces { loaded: post.spaces.loaded, ..self.spaces })
        &&& post.spaces.loaded@ == self.spaces.loaded@.insert(base, post.spaces.loaded@[base])
        &&& post.spaces.loaded@[base].addr() == self.spaces.loaded@[base].addr()
        &&& post.spaces.loaded@[base].value() == (SpaceCores { retired: post.flush_epoch, ..self.spaces.loaded@[base].value() })
        &&& forall|d: int, r: usize| 0 <= d < NUM_CPUS ==> #[trigger] post.depends(d, r) == self.depends(d, r)
        &&& post.view() == self.view()
        &&& post.process_is_dead(base)
    }

    /// A retype may cut a child table of the dead process at `base`'s space root: an untyped covers its
    /// block, no core depends on its space, an entry of the root still names a child and the flush epoch
    /// can rise.
    pub open spec fn can_cut_process_space(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, PROCESS_ORDER)
        &&& self.process_is_dead(base)
        &&& self.process_released(base)
        &&& exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
        &&& self.flush_epoch < usize::MAX
    }

    /// What cutting children of the dead process at `base`'s space root did to self: as for a table
    /// page; the kernel slots are as they were; every table page's parent record names a table or
    /// nothing; and the process is still dead and released.
    pub open spec fn process_space_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let a = tree_of(&self.table_pages, &self.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        &&& self.table_children_cut(post, root, from, base)
        &&& forall|i: usize| #![trigger b.entry(base, i)] i < KERNEL_MEM_END_L4INDEX ==> b.entry(base, i) == a.entry(base, i)
        &&& forall|c: usize| #![trigger b.record(c)]
            b.is_page(c) && b.record(c).parent is Some ==> b.is_table(b.record(c).parent->Some_0.table)
        &&& post.process_is_dead(base)
        &&& post.process_released(base)
    }

    /// A block at an order-3 base holds a process exactly when a process record is kept there, and a
    /// process's space is a root of kind Process with no parent at level 4, which no table page shares.
    pub proof fn lemma_process_block(&self, base: usize)
        requires
            self.wf(),
            base % PROCESS_BYTES == 0,
            self.blocks.tracks_addr(base),
        ensures
            process_block(&self.blocks, base / PAGE_SZ) == self.processes.records@.contains_key(base),
            self.processes.records@.contains_key(base) ==> {
                &&& self.spaces.roots@.contains_key(base)
                &&& self.spaces.records@[base].value().kind is Process
                &&& self.spaces.loaded@.contains_key(base)
                &&& self.spaces.loaded@[base].addr() == base + SPACE_CORES_PAGE * PAGE_SZ
                &&& self.spaces.loaded@[base].is_init()
                &&& !self.table_pages.maps@.contains_key(base)
                &&& tree_of(&self.table_pages, &self.spaces).record(base).parent is None
                &&& tree_of(&self.table_pages, &self.spaces).record(base).level == 4
            },
    {
        assert(base % PROCESS_BYTES == 0 ==> base % LEAF_BYTES == 0) by (bit_vector);
        lemma_leaf_page(base);
        if process_block(&self.blocks, base / PAGE_SZ) {
            assert(self.processes.records@.contains_key(((base / PAGE_SZ) * PAGE_SZ) as usize));
        }
        if self.processes.records@.contains_key(base) {
            assert(process_wf(&self.processes, &self.blocks, base));
            assert(self.spaces.roots@.contains_key(base));
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
            self.lemma_space_block(base);
        }
    }

    /// A process record is kept only at a block typed as a process.
    pub proof fn lemma_process_object(&self, base: usize)
        requires
            self.wf(),
        ensures
            self.processes.records@.contains_key(base) ==> {
                &&& base % PROCESS_BYTES == 0
                &&& self.blocks.tracks_addr(base)
                &&& self.blocks.pages@[(base / PAGE_SZ) as int].object is Process
            },
    {
        if self.processes.records@.contains_key(base) {
            assert(process_wf(&self.processes, &self.blocks, base));
        }
    }

    /// No core depends on a released process space, so no core holds a translation of it.
    pub proof fn lemma_process_released(&self, base: usize)
        requires
            self.wf(),
            self.process_released(base),
        ensures
            forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base ==> !#[trigger] self.tlb@[d].contains(e),
    {
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base implies !#[trigger] self.tlb@[d].contains(e) by {
            assert(!self.depends(d, base));
        }
    }

    /// A process a core's current thread is bound to has a reference, and one a core may hold a
    /// translation of is not released.
    pub proof fn lemma_process_refused(&self, base: usize)
        requires
            self.wf(),
            self.processes.records@.contains_key(base),
        ensures
            (exists|d: int, t: usize| #![trigger self.cores@[d], self.threads.records@[t]] 0 <= d < NUM_CPUS && self.cores@[d].current_thread == Some(t)
                && self.threads.records@[t].value().process == Some(base))
                ==> self.blocks.pages@[(base / PAGE_SZ) as int].refs != 0,
            (exists|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base && #[trigger] self.tlb@[d].contains(e))
                ==> !self.process_released(base),
    {
        assert(process_wf(&self.processes, &self.blocks, base));
        if exists|d: int, t: usize| #![trigger self.cores@[d], self.threads.records@[t]] 0 <= d < NUM_CPUS && self.cores@[d].current_thread == Some(t)
            && self.threads.records@[t].value().process == Some(base) {
            let (d, t) = choose|d: int, t: usize| #![trigger self.cores@[d], self.threads.records@[t]] 0 <= d < NUM_CPUS && self.cores@[d].current_thread == Some(t)
                && self.threads.records@[t].value().process == Some(base);
            reveal(current_wf);
            assert(runs(self.cores@, d, t));
            assert(self.threads.records@.contains_key(t));
            assert(self.processes.bound@[base].contains(t));
            if self.blocks.pages@[(base / PAGE_SZ) as int].refs == 0 {
                self.processes.bound@[base].lemma_len0_is_empty();
            }
        }
        if exists|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base && #[trigger] self.tlb@[d].contains(e) {
            let (d, e) = choose|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base && #[trigger] self.tlb@[d].contains(e);
            assert(self.depends(d, base));
        }
    }

    /// No core has an unloaded process space loaded, so it is released.
    pub proof fn lemma_unloaded_released(&self, base: usize)
        requires
            self.process_unloaded(base),
        ensures
            self.process_released(base),
    {
        assert forall|d: int| 0 <= d < NUM_CPUS implies !#[trigger] self.depends(d, base) by {
            lemma_no_core_listed(d as u32);
        }
    }

    /// Whether the space of the process at `base` is released: one load of its list and a bounded loop
    /// over the cores.
    fn process_space_released(&self, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(base),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS,
            ret == self.process_released(base),
    {
        proof {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
        }
        let cores = *PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * PAGE_SZ).borrow(
            Tracked(self.spaces.loaded.borrow().tracked_borrow(base)),
        );
        let ghost start = steps.count;
        let mut d: usize = 0;
        while d != NUM_CPUS
            invariant
                0 <= d <= NUM_CPUS,
                start == old(steps).count,
                steps.count == start + d,
                self.wf(),
                self.spaces.loaded@.contains_key(base),
                cores == self.spaces.loaded@[base].value(),
                forall|k: int| 0 <= k < d ==> !#[trigger] self.depends(k, base),
            decreases NUM_CPUS - d,
        {
            if (cores.list >> (d as u32)) & 1u32 == 1u32
                && (cores.retired == 0 || self.cores.get(d).acked_epoch < cores.retired) {
                proof {
                    assert(self.loaded(d as int, base));
                    assert(self.depends(d as int, base));
                }
                return false;
            }
            proof {
                assert(!self.depends(d as int, base));
                steps.step();
            }
            d = d + 1;
        }
        true
    }

    /// Whether some core's base register names the space of the process at `base`: a bounded loop over
    /// the cores.
    fn process_space_names(&self, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS,
            ret == self.process_space_named(base),
    {
        let ghost start = steps.count;
        let mut d: usize = 0;
        while d != NUM_CPUS
            invariant
                0 <= d <= NUM_CPUS,
                start == old(steps).count,
                steps.count == start + d,
                self.wf(),
                forall|k: int| 0 <= k < d ==> #[trigger] self.cores@[k].space != Some(base),
            decreases NUM_CPUS - d,
        {
            if let Some(named) = self.cores.get(d).space {
                if named == base {
                    proof {
                        assert(self.cores@[d as int].space == Some(base));
                    }
                    return true;
                }
            }
            proof {
                steps.step();
            }
            d = d + 1;
        }
        false
    }

    /// A retire changes only the space's retire epoch, to an epoch no core has acknowledged, and raises
    /// the epoch, so the invariant holds and every core depends on what it did before.
    proof fn lemma_process_retired(pre: Self, post: Self, s: usize)
        requires
            pre.wf(),
            pre.spaces.roots@.contains_key(s),
            pre.flush_epoch < usize::MAX,
            pre.spaces.loaded@[s].value().retired == 0,
            forall|d: int| 0 <= d < NUM_CPUS ==> #[trigger] pre.cores@[d].space != Some(s),
            post == (CapKernel { flush_epoch: post.flush_epoch, flush_ipis: post.flush_ipis, spaces: post.spaces, ..pre }),
            post.flush_epoch == pre.flush_epoch + 1,
            post.spaces == (Spaces { loaded: post.spaces.loaded, ..pre.spaces }),
            post.spaces.loaded@ == pre.spaces.loaded@.insert(s, post.spaces.loaded@[s]),
            post.spaces.loaded@[s].addr() == pre.spaces.loaded@[s].addr(),
            post.spaces.loaded@[s].is_init(),
            post.spaces.loaded@[s].value() == (SpaceCores { retired: post.flush_epoch, ..pre.spaces.loaded@[s].value() }),
        ensures
            post.wf(),
            forall|d: int, r: usize| 0 <= d < NUM_CPUS ==> #[trigger] post.depends(d, r) == pre.depends(d, r),
            post.view() == pre.view(),
    {
        let sa = &pre.spaces;
        let sb = &post.spaces;
        assert(space_wf(&pre.list, sa, &pre.blocks, s));
        assert(sa.loaded@.contains_key(s));
        assert(sb.loaded@.dom() =~= sa.loaded@.dom());
        assert forall|d: int, r: usize| 0 <= d < NUM_CPUS implies #[trigger] post.depends(d, r) == pre.depends(d, r) by {
            assert(pre.acked(d) <= pre.flush_epoch);
            assert(post.acked(d) == pre.acked(d));
            assert(sb.loaded@.contains_key(r) == sa.loaded@.contains_key(r));
            if r != s && sa.loaded@.contains_key(r) {
                assert(sb.loaded@[r] == sa.loaded@[r]);
            }
        }
        assert forall|r: usize| #[trigger] sb.roots@.contains_key(r) implies space_wf(&post.list, sb, &post.blocks, r) by {
            assert(space_wf(&pre.list, sa, &pre.blocks, r));
            if r != s {
                assert(sb.loaded@[r] == sa.loaded@[r]);
            }
            assert(kernel_slots_wf(sb, r));
            assert(root_record_wf(sb, r));
        }
        assert forall|r: usize| #[trigger] sb.loaded@.contains_key(r) implies sb.roots@.contains_key(r) by {
            assert(sa.loaded@.contains_key(r));
        }
        assert(spaces_wf(&post.list, &post.tables, sb, &post.blocks));
        assert(tree_of(&post.table_pages, &post.spaces) == tree_of(&pre.table_pages, &pre.spaces));
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] names_wf(pre.cores@[d].space, pre.cores@[d].generation, sb.loaded@, d) by {
            reveal(ids_wf);
            assert(names_wf(pre.cores@[d].space, pre.cores@[d].generation, sa.loaded@, d));
            if let Some(r) = pre.cores@[d].space {
                assert(r != s);
                assert(sb.loaded@[r] == sa.loaded@[r]);
            }
        }
        lemma_ids_same(pre.cores@, sa.loaded@, sb.loaded@);
        lemma_registers_lists(sa.registers@, pre.cores@, sa.loaded@, sb.loaded@, sa.kernel_root@);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) <= post.flush_epoch by {
            assert(pre.acked(d) <= pre.flush_epoch);
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) implies post.depends(d, e.space) by {
            assert(pre.depends(d, e.space));
            assert(post.depends(d, e.space) == pre.depends(d, e.space));
        }
        assert forall|d: int, e: TlbEntry|
            0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(d), e.page) by {
            assert(pre.tlb@[d].contains(e));
            assert(pre.acked(d) == post.acked(d));
        }
        Self::lemma_iommus_same(pre, post);
        assert(post.tlb_wf());
    }

    /// Retires the space of the dead process at `base`, under the untyped at index `from` of the table at
    /// `root`: raises the flush epoch, records it as the space's retire epoch and sends a flush IPI to
    /// each core on the space's list. Refused unless it is not yet retired, a core depends on it and no
    /// core's base register names it. Returns whether it ran, and if not nothing changed.
    pub(crate) fn retire_process(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + RETIRE_STEPS,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_retire_process(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).process_retired(*final(self), base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, PROCESS_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) || self.flush_epoch == usize::MAX {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_process = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Process) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_process_block(base);
        }
        if !dead_process {
            return false;
        }
        let ptr = PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * PAGE_SZ);
        let cores = *ptr.borrow(Tracked(self.spaces.loaded.borrow().tracked_borrow(base)));
        if cores.retired != 0 || self.process_space_released(base, Tracked(&mut *steps)) {
            return false;
        }
        if self.process_space_names(base, Tracked(&mut *steps)) {
            return false;
        }
        let ghost sent = self.flush_ipis@;
        self.send_flush(base, Ghost(sent), Tracked(&mut *steps));
        let ghost mid = *self;
        self.flush_epoch = self.flush_epoch + 1;
        let mut next = cores;
        next.retired = self.flush_epoch;
        let tracked mut perm = self.spaces.loaded.borrow_mut().tracked_remove(base);
        ptr.write(Tracked(&mut perm), next);
        proof {
            self.spaces.loaded.borrow_mut().tracked_insert(base, perm);
            let post = *self;
            assert(post.spaces.loaded@ =~= mid.spaces.loaded@.insert(base, post.spaces.loaded@[base]));
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] mid.cores@[d].space != Some(base) by {
                if mid.cores@[d].space == Some(base) {
                    assert(pre.cores@[d].space == Some(base));
                    assert(pre.process_space_named(base));
                }
            }
            Self::lemma_process_retired(mid, post, base);
            Self::lemma_same_tree_shrunk(pre, post);
            assert(post.processes == pre.processes);
            assert(post.blocks == pre.blocks);
        }
        true
    }

    /// Cuts up to a budget of the child tables of the dead process at `base`'s space root, under the
    /// untyped at index `from` of the table at `root`, each from the entry naming it, with what that
    /// leaves stale, and leaves the kernel slots. Refused while a core depends on the space. Returns
    /// whether it ran, and if not nothing changed.
    pub(crate) fn cut_process_space(&mut self, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS + CUT_SLICE_STEPS,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_cut_process_space(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).process_space_cut(*final(self), root, from, base),
    {
        reveal(table_links_wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, PROCESS_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) || self.flush_epoch == usize::MAX {
            return false;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_process = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Process) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_process_block(base);
        }
        if !dead_process {
            return false;
        }
        if !self.process_space_released(base, Tracked(&mut *steps)) {
            return false;
        }
        proof {
            assert(a.is_root(base));
            assert(a.space_records[base].value().kind is Process);
        }
        let cut = self.cut_children(base, true, Tracked(steps));
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            if cut != 0 {
                Self::lemma_cuts_shed(pre, post, base);
                Self::lemma_cuts_same_view(pre, post, base);
                pre.lemma_retype_covers(root, from, base, PROCESS_ORDER);
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base, 0, base);
                assert forall|i: usize| #![trigger b.entry(base, i)] i < KERNEL_MEM_END_L4INDEX implies b.entry(base, i) == a.entry(base, i) by {
                    assert(!a.child_slot(base, i));
                }
                assert forall|c: usize| #![trigger b.record(c)]
                    b.is_page(c) && b.record(c).parent is Some implies b.is_table(b.record(c).parent->Some_0.table) by {
                    assert(b.maps.contains_key(c));
                    let p = b.record(c).parent->Some_0;
                    assert(b.names_child(p.table, p.entry));
                }
                post.lemma_process_block(base);
                assert(post.processes.records@.contains_key(base));
                assert forall|d: int| 0 <= d < NUM_CPUS implies !#[trigger] post.depends(d, base) by {
                    assert(post.acked(d) == pre.acked(d));
                    assert(!pre.depends(d, base));
                }
            }
        }
        cut != 0
    }

    /// Nothing is left of the dead process at `base` but its block: no core depends on its space, no entry
    /// of its table root names a leaf, and no entry of its space root outside the kernel slots holds
    /// anything. A leaf still in its table root is one whose own untyped's holder has not yet retyped it.
    pub open spec fn process_is_spent(&self, base: usize) -> bool {
        &&& self.process_is_dead(base)
        &&& self.process_released(base)
        &&& forall|r: int| 0 <= r < ROOT_ENTRIES ==> #[trigger] self.tables.leaf(base, r) == NO_LEAF
        &&& forall|i: usize| #![trigger self.spaces.roots@[base].value()[i]]
            KERNEL_MEM_END_L4INDEX <= i < ENTRIES ==> self.spaces.roots@[base].value()[i].is_empty()
    }

    /// What freeing the spent dead process at `base` did to self: no core depended on its space or held a
    /// translation of it, its block is free, and it is gone from the processes, the tables and the
    /// spaces, with no leaf left naming it. It held no capability, so the view is as it was, and the
    /// list, every other process record, every other table root, every leaf and its payload, every
    /// tracked page outside its block, and the 2 MiB and 1 GiB regions are as they were.
    pub open spec fn process_freed(&self, post: Self, c: usize, root: usize, from: usize, base: usize) -> bool {
        let untyped = self.tables.node_of(root, from);
        let page = base / PAGE_SZ;
        &&& self.view().holds_right(root, untyped, Right::Retype)
        &&& self.process_is_spent(base)
        &&& self.no_stale_translation(page)
        &&& forall|d: int| 0 <= d < NUM_CPUS ==> !#[trigger] self.depends(d, base)
        &&& forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base ==> !#[trigger] self.tlb@[d].contains(e)
        &&& forall|k: int| 0 <= k < 8 ==> #[trigger] post.blocks.pages@[page + k].kind is Free
        &&& !post.processes.records@.contains_key(base)
        &&& !post.tables.roots@.contains_key(base)
        &&& !post.spaces.roots@.contains_key(base)
        &&& forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) ==> post.tables.owner@[l].0 != base
        &&& post.list == self.list
        &&& post.processes.records@ == self.processes.records@.remove(base)
        &&& post.tables.roots@ == self.tables.roots@.remove(base)
        &&& post.tables.owner == self.tables.owner
        &&& post.tables.payloads == self.tables.payloads
        &&& forall|i: int| self.blocks.tracks(i) && !(page as int <= i < page + 8)
            ==> #[trigger] post.blocks.pages@[i] == self.blocks.pages@[i]
        &&& post.blocks.regions_2m@ == self.blocks.regions_2m@
        &&& post.blocks.regions_1g@ == self.blocks.regions_1g@
        &&& Self::step_ok(*self, post, c as int)
        &&& post.view() == self.view()
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&self.list, &self.tables)
        &&& discharges(self.view(), post.view(), root, Effect::Teardown { untyped, block: base, pages: pow2(PROCESS_ORDER as nat), object: base })
    }

    /// One step of a spent dead process going: its block frees, and its table root, record, spare pages
    /// and space go with it. The list held none of its pages, and nothing else changes.
    pub open spec fn process_freed_step(pre: Self, post: Self, base: usize) -> bool {
        let page = base / PAGE_SZ;
        &&& pre.wf()
        &&& pre.process_is_spent(base)
        &&& post.blocks.wf()
        &&& forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
            if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] })
        &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@
        &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@
        &&& post.list == pre.list
        &&& forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> !(base <= p < base + 8 * PAGE_SZ)
        &&& post.tables.wf(&post.list)
        &&& post.tables.roots@ == pre.tables.roots@.remove(base)
        &&& post.tables.owner == pre.tables.owner
        &&& post.tables.payloads == pre.tables.payloads
        &&& post.table_pages == pre.table_pages
        &&& post.spaces.roots@ == pre.spaces.roots@.remove(base)
        &&& post.spaces.records@ == pre.spaces.records@.remove(base)
        &&& post.spaces.loaded@ == pre.spaces.loaded@.remove(base)
        &&& post.spaces.holders@ == pre.spaces.holders@.remove(base)
        &&& post.spaces.bound@ == pre.spaces.bound@.remove(base)
        &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
        &&& post.spaces.registers == pre.spaces.registers
        &&& post.spaces.kernel_root == pre.spaces.kernel_root
        &&& post.processes.records@ == pre.processes.records@.remove(base)
        &&& post.processes.spare@ == pre.processes.spare@.remove((base + 2 * PAGE_SZ) as usize)
            .remove((base + 3 * PAGE_SZ) as usize).remove((base + 4 * PAGE_SZ) as usize)
        &&& post.processes.holders@ == pre.processes.holders@.remove(base)
        &&& post.processes.bound@ == pre.processes.bound@.remove(base)
        &&& post.holders == pre.holders
        &&& post.cores == pre.cores
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.iommus == pre.iommus
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.mappings == pre.mappings
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.endpoints == pre.endpoints
        &&& post.replies == pre.replies
    }

    /// What the invariant says of a spent process before it frees: its block and its space.
    proof fn lemma_spent_process(&self, base: usize)
        requires
            self.wf(),
            self.process_is_spent(base),
        ensures
            base % PROCESS_BYTES == 0,
            base % PAGE_SZ == 0,
            base as int == PAGE_SZ * (base / PAGE_SZ) as int,
            self.blocks.tracks_addr_run(base, 8),
            process_wf(&self.processes, &self.blocks, base),
            self.blocks.pages@[(base / PAGE_SZ) as int].dead,
            self.processes.holders@[base] == Set::<usize>::empty(),
            self.processes.bound@[base] == Set::<usize>::empty(),
            self.tables.roots@.contains_key(base),
            self.spaces.roots@.contains_key(base),
            self.spaces.records@[base].value().kind is Process,
            space_wf(&self.list, &self.spaces, &self.blocks, base),
            self.spaces.holders@[base] == Set::<usize>::empty(),
            self.spaces.bound@[base] == Set::<usize>::empty(),
            !self.table_pages.maps@.contains_key(base),
            tree_of(&self.table_pages, &self.spaces).record(base).level == 4,
            forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base ==> !#[trigger] self.tlb@[d].contains(e),
    {
        self.lemma_process_object(base);
        self.lemma_process_block(base);
        assert(process_wf(&self.processes, &self.blocks, base));
        assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
        lemma_table_page_aligned(base);
        self.processes.holders@[base].lemma_len0_is_empty();
        self.processes.bound@[base].lemma_len0_is_empty();
        self.lemma_process_released(base);
    }

    /// No page of a process's block is mapped: the only blocks a mapping names are frames'.
    proof fn lemma_process_page_unmapped(&self, page: usize)
        requires
            self.wf(),
            self.blocks.tracks(page as int),
            self.blocks.pages@[page as int].kind is Base,
            self.blocks.pages@[page as int].object is Process,
        ensures
            !self.mapped@.contains(page),
    {
        if self.mapped@.contains(page) {
            let br = self.lemma_mapped_block(page);
            match br {
                BlockRef::Small(b) => {
                    assert(self.holders@.contains_key(BlockRef::Small(page)));
                },
                BlockRef::Two(r) => { lemma_large_block_alone(&self.blocks, Large::Two, r, BlockRef::Small(page), page); },
                BlockRef::One(r) => { lemma_large_block_alone(&self.blocks, Large::One, r, BlockRef::Small(page), page); },
            }
        }
    }

    /// No page the list holds is in the freed process's block.
    proof fn lemma_process_list_pages(pre: Self, base: usize)
        requires
            pre.wf(),
            pre.process_is_spent(base),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> !(base <= p < base + 8 * PAGE_SZ),
        ensures
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                ==> !pre.blocks.in_block((base / PAGE_SZ) as int, (p / PAGE_SZ) as int),
    {
        let page = base / PAGE_SZ;
        pre.lemma_spent_process(base);
        assert(order_pages(3) == 8);
        assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
            implies !pre.blocks.in_block(page as int, (p / PAGE_SZ) as int) by {
            lemma_list_page(&pre.list, p);
            lemma_fundamental_div_mod(p as int, PAGE_SZ as int);
            assert(!(base <= p < base + 8 * PAGE_SZ));
        }
    }

    /// The tree after the spent process at `base` goes: its root named no child, and its kernel slots
    /// name none.
    proof fn lemma_process_freed_tree(pre: Self, post: Self, base: usize)
        requires
            Self::process_freed_step(pre, post, base),
        ensures
            space_removed(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base),
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        pre.lemma_spent_process(base);
        assert forall|i: usize| !#[trigger] a.names_child(base, i) by {
            if KERNEL_MEM_END_L4INDEX <= i < ENTRIES {
                assert(pre.spaces.roots@[base].value()[i].is_empty());
            }
        }
        assert(space_removed(a, b, base));
        lemma_links_space_removed(a, b, base);
        assert forall|t: usize, e: usize| #[trigger] frame_slot(a, t, e) implies {
            &&& frame_slot(b, t, e)
            &&& b.record(t).level == a.record(t).level
            &&& b.entry(t, e) == a.entry(t, e)
        } by {
            assert(t != base);
            lemma_space_removed_others(a, b, base, t);
            assert(b.entry(t, e) == a.entry(t, e));
        }
        assert forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) implies frame_slot(a, t, e) by {
            assert(t != base);
            lemma_space_removed_others(a, b, base, t);
            assert(b.entry(t, e) == a.entry(t, e));
        }
    }

    /// The capabilities and the view after the spent process at `base` goes: the list and every leaf are
    /// as they were, and only the table root left.
    proof fn lemma_process_freed_caps(pre: Self, post: Self, base: usize)
        requires
            Self::process_freed_step(pre, post, base),
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| #[trigger] post.tables.payload_of(x) == pre.tables.payload_of(x),
            post.view() == pre.view(),
    {
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x) by {}
        assert forall|x: usize| #[trigger] post.tables.payload_of(x) == pre.tables.payload_of(x) by {}
        let (a, b) = (pre.view(), post.view());
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) == a.held.contains(h) by {}
        assert(b.held =~= a.held);
        assert forall|n: NodeId| #[trigger] b.names.contains_key(n) == a.names.contains_key(n)
            && (a.names.contains_key(n) ==> b.names[n] == a.names[n]) by {}
        assert(b.names =~= a.names);
        assert forall|n: NodeId| #[trigger] b.pages.contains_key(n) == a.pages.contains_key(n)
            && (a.pages.contains_key(n) ==> b.pages[n] == a.pages[n]) by {}
        assert(b.pages =~= a.pages);
        assert forall|h: (NodeId, Right)| #[trigger] b.rights.contains(h) == a.rights.contains(h) by {}
        assert(b.rights =~= a.rights);
        Self::lemma_process_freed_tree(pre, post, base);
        lemma_space_removed_same_shares(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base);
        assert(b.shares == a.shares);
        assert(b == a);
    }

    /// The table pages, the spaces, the threads and the processes after the spent process at `base`
    /// goes: every other one lies in its own block, and no capability changed.
    proof fn lemma_process_freed_pages(pre: Self, post: Self, base: usize)
        requires
            Self::process_freed_step(pre, post, base),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| #[trigger] post.tables.payload_of(x) == pre.tables.payload_of(x),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks),
            replies_wf(&post.list, &post.tables, &post.replies, &post.blocks),
            process_tables_wf(&post.tables, &post.processes),
            process_spaces_wf(&post.spaces, &post.processes),
            bindings_wf(&post.list, &post.threads, &post.processes),
            binding_parents(&post.list, &post.tables, &post.threads),
            placements_wf(&post.list, &post.tables, &post.threads),
            device_bindings_wf(&post.list, &post.tables, post.spaces.bound@, &post.devices),
            list_pages_used(&post.list, &post.blocks),
    {
        let page = base / PAGE_SZ;
        pre.lemma_spent_process(base);
        Self::lemma_process_list_pages(pre, base);
        assert(order_pages(3) == 8);
        assert forall|t: usize, k: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
        }
        assert(same_table_nodes(&pre.list, &post.list, &pre.table_pages));
        lemma_table_pages_small_freed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, page);
        assert forall|s: usize, k: usize| #[trigger] post.spaces.roots@.contains_key(s) && !(post.spaces.records@[s].value().kind is Process)
            && k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
            assert(pre.spaces.roots@.contains_key(s));
            assert(post.spaces.records@[s] == pre.spaces.records@[s]);
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
        }
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_spaces_space_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &post.spaces, &pre.blocks, &post.blocks, base);
        assert forall|t: usize| #[trigger] pre.threads.records@.contains_key(t) implies post.list.pages@.dom().contains(t) by {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        assert(same_threads(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_threads_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page);
        lemma_processes_process_freed(&pre.list, &pre.tables, &post.tables, &pre.processes, &post.processes, &pre.blocks, &post.blocks, base);
        lemma_endpoints_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks, &post.blocks, page);
        lemma_replies_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, page);
        assert forall|p: usize| #[trigger] post.processes.records@.contains_key(p) implies post.tables.roots@.contains_key(p) by {
            assert(pre.processes.records@.contains_key(p));
        }
        assert forall|p: usize| #[trigger] post.processes.records@.contains_key(p) implies {
            &&& post.spaces.roots@.contains_key(p)
            &&& post.spaces.records@[p].value().kind is Process
        } by {
            assert(pre.processes.records@.contains_key(p));
        }
        assert forall|t: usize| #[trigger] post.threads.records@.contains_key(t) && post.threads.records@[t].value().process is Some implies {
            let p = post.threads.records@[t].value().process->Some_0;
            &&& t < NODE_SPACE
            &&& post.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind is Binding
            &&& post.processes.records@.contains_key(p)
            &&& post.processes.bound@[p].contains(t)
        } by {
            let p = pre.threads.records@[t].value().process->Some_0;
            assert(pre.processes.bound@[p].contains(t));
            assert(p != base);
        }
        assert forall|p: usize, t: usize| post.processes.records@.contains_key(p) && #[trigger] post.processes.bound@[p].contains(t)
            implies post.threads.records@.contains_key(t) && post.threads.records@[t].value().process == Some(p) by {
            assert(pre.processes.bound@[p].contains(t));
        }
        lemma_binding_parents_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Core implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            assert(post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x));
            assert(post.tables.payload_of(x) == pre.tables.payload_of(x));
        }
        lemma_placements_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert(pre.processes.records@.contains_key(base));
        pre.lemma_bound_empty(base);
        lemma_bound_kept_empty(pre.spaces.bound@, base);
        assert forall|x: usize| #[trigger] pre.is_cap(x) && pre.payload_of(x).kind is Space
            implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            assert(post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x));
            assert(post.tables.payload_of(x) == pre.tables.payload_of(x));
        }
        Self::lemma_device_bindings_space_caps(pre, post);
        lemma_list_pages_used_small_freed(&post.list, &pre.blocks, &post.blocks, page);
    }

    /// The holders, the objects and the mappings after the spent process at `base` goes: no holder is on
    /// its block, no leaf is in it, and no mapping names it.
    proof fn lemma_process_freed_objects(pre: Self, post: Self, base: usize)
        requires
            Self::process_freed_step(pre, post, base),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| #[trigger] post.tables.payload_of(x) == pre.tables.payload_of(x),
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            zeroing_typed(&post.zeroing, &post.blocks),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let page = base / PAGE_SZ;
        pre.lemma_spent_process(base);
        assert(order_pages(3) == 8);
        assert(pre.blocks.in_block(page as int, page as int));
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies !pre.blocks.in_block(page as int, (l / PAGE_SZ) as int) by {
            let x = (l / PAGE_SZ) as int;
            assert(pre.blocks.pages@[x].object is TableLeaf);
            if pre.blocks.in_block(page as int, x) && x != page {
                pre.blocks.lemma_member_of(page as int, x);
            }
        }
        assert forall|b: usize| #[trigger] pre.holders@.contains_key(BlockRef::Small(b)) implies !pre.blocks.in_block(page as int, b as int) by {
            assert(block_typed(&pre.blocks, BlockRef::Small(b)));
            assert(pre.blocks.pages@[b as int].object is Frame);
            if pre.blocks.in_block(page as int, b as int) && b != page {
                pre.blocks.lemma_member_of(page as int, b as int);
            }
        }
        assert(!pre.holders@.contains_key(BlockRef::Small(page)));
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m
        ) by {
            pre.lemma_mapping_node(m);
            if let BlockRef::Small(b) = block_ref(&pre.blocks, pre.mappings@[m].frame) {
                assert(pre.holders@.contains_key(BlockRef::Small(b)));
            }
            assert(block_ref(&pre.blocks, pre.mappings@[m].frame) != BlockRef::Small(page));
            lemma_block_ref_small_freed(&pre.blocks, &post.blocks, page, pre.mappings@[m].frame);
        }
        lemma_mappings_kept(&pre.list, &pre.tables, tree_of(&pre.table_pages, &pre.spaces), &pre.blocks, pre.holders@,
            &post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@);
        lemma_holders_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, page);
        assert(pre.holders@.remove(BlockRef::Small(page)) =~= pre.holders@);
        assert(same_frames(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@);
        assert forall|b: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(b))
            implies post.blocks.pages@[b as int].object is Frame by {
            assert(block_typed(&pre.blocks, BlockRef::Small(b)));
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && (#[trigger] post.blocks.pages@[b as int]).kind is Base
            && post.blocks.pages@[b as int].object is Frame implies {
            &&& post.blocks.pages@[b as int].order == 0
            &&& post.blocks.pages@[b as int].refs == 0 ==> post.holders@.contains_key(BlockRef::Small(b))
        } by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& post.blocks.tracks_addr(l)
            &&& post.blocks.pages@[(l / PAGE_SZ) as int] == pre.blocks.pages@[(l / PAGE_SZ) as int]
        } by {
            assert(pre.tables.owner@.contains_key(l));
        }
        assert forall|b: usize| post.blocks.tracks(b as int) && #[trigger] leaf_block(&post.blocks, b)
            implies post.tables.owner@.contains_key((b * PAGE_SZ) as usize) by {
            assert(post.blocks.pages@[b as int] == pre.blocks.pages@[b as int]);
            assert(leaf_block(&pre.blocks, b));
            lemma_page_base(&post.blocks, b);
        }
    }

    /// The kernel after the spent process at `base` frees.
    proof fn lemma_process_freed(pre: Self, post: Self, base: usize)
        requires
            Self::process_freed_step(pre, post, base),
        ensures
            post.wf(),
            post.view() == pre.view(),
    {
        let page = base / PAGE_SZ;
        pre.blocks.lemma_not_free_uncovered(page as int);
        pre.lemma_untranslatable_clean(page);
        Self::lemma_small_freed_translatable(pre, &post.blocks, page);
        pre.lemma_spent_process(base);
        Self::lemma_kernel_root_freed(pre, post, (base / PAGE_SZ) as int);
        Self::lemma_process_freed_caps(pre, post, base);
        Self::lemma_badges_same_caps(pre, post);
        Self::lemma_process_freed_tree(pre, post, base);
        Self::lemma_process_freed_pages(pre, post, base);
        Self::lemma_process_freed_objects(pre, post, base);
        Self::lemma_devices_same_caps(pre, post);
        Self::lemma_tlb_space_removed(pre, post, base);
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] pre.cores@[c].space != Some(base) by {
            if pre.cores@[c].space == Some(base) {
                pre.lemma_named_depends(c, base);
            }
        }
        lemma_ids_space_removed(pre.cores@, pre.spaces.loaded@, post.spaces.loaded@, base);
        lemma_registers_lists(pre.spaces.registers@, pre.cores@, pre.spaces.loaded@, post.spaces.loaded@, pre.spaces.kernel_root@);
    }

    /// Whether nothing is left in the roots of the process at `base`: no entry of its table root names a
    /// leaf and no entry of its space root outside the kernel slots holds anything. A constant number of
    /// loads.
    fn process_roots_clear(&self, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            self.processes.records@.contains_key(base),
        ensures
            final(steps).count <= old(steps).count + ROOT_ENTRIES + (ENTRIES - KERNEL_MEM_END_L4INDEX),
            ret == ((forall|r: int| 0 <= r < ROOT_ENTRIES ==> #[trigger] self.tables.leaf(base, r) == NO_LEAF)
                && (forall|i: usize| #![trigger self.spaces.roots@[base].value()[i]]
                    KERNEL_MEM_END_L4INDEX <= i < ENTRIES ==> self.spaces.roots@[base].value()[i].is_empty())),
    {
        proof {
            self.lemma_process_object(base);
            self.lemma_process_block(base);
        }
        let ghost steps0 = steps.count;
        let mut r = 0;
        while r != ROOT_ENTRIES
            invariant
                0 <= r <= ROOT_ENTRIES,
                steps0 == old(steps).count,
                steps.count == steps0 + r,
                self.wf(),
                self.tables.roots@.contains_key(base),
                forall|j: int| 0 <= j < r ==> #[trigger] self.tables.leaf(base, j) == NO_LEAF,
            decreases ROOT_ENTRIES - r,
        {
            if self.tables.entry(base, r) != NO_LEAF {
                return false;
            }
            r = r + 1;
            proof {
                steps.step();
            }
        }
        let ghost tree = tree_of(&self.table_pages, &self.spaces);
        let mut e = KERNEL_MEM_END_L4INDEX;
        while e != ENTRIES
            invariant
                KERNEL_MEM_END_L4INDEX <= e <= ENTRIES,
                steps0 == old(steps).count,
                steps.count == steps0 + ROOT_ENTRIES + (e - KERNEL_MEM_END_L4INDEX),
                self.wf(),
                self.spaces.roots@.contains_key(base),
                !self.table_pages.maps@.contains_key(base),
                tree == tree_of(&self.table_pages, &self.spaces),
                forall|j: int| 0 <= j < ROOT_ENTRIES ==> #[trigger] self.tables.leaf(base, j) == NO_LEAF,
                forall|j: usize| #![trigger self.spaces.roots@[base].value()[j]]
                    KERNEL_MEM_END_L4INDEX <= j < e ==> self.spaces.roots@[base].value()[j].is_empty(),
            decreases ENTRIES - e,
        {
            let entry = self.table_entry(base, true, e);
            proof {
                assert(!tree.is_page(base));
                assert(tree.entry(base, e) == self.spaces.roots@[base].value()[e]);
            }
            if !entry_is_empty(&entry) {
                return false;
            }
            e = e + 1;
            proof {
                steps.step();
            }
        }
        true
    }

    /// The block of the spent dead process at `base` goes back to the block table: its table root, its
    /// record, its spare pages and its space's root, record and list of cores turned back into page
    /// permissions.
    pub(crate) fn free_spent_process(&mut self, base: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).process_is_spent(base),
        ensures
            final(steps).count <= old(steps).count + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            forall|k: int| 0 <= k < 8 ==> #[trigger] final(self).blocks.pages@[(base / PAGE_SZ) + k].kind is Free,
            !final(self).processes.records@.contains_key(base),
            final(self).processes.records@ == old(self).processes.records@.remove(base),
            !final(self).tables.roots@.contains_key(base),
            !final(self).spaces.roots@.contains_key(base),
            forall|l: usize| #[trigger] final(self).tables.owner@.contains_key(l) ==> final(self).tables.owner@[l].0 != base,
            final(self).list == old(self).list,
            final(self).tables.roots@ == old(self).tables.roots@.remove(base),
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.payloads == old(self).tables.payloads,
            forall|i: int| old(self).blocks.tracks(i) && !((base / PAGE_SZ) as int <= i < (base / PAGE_SZ) + 8)
                ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i],
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            final(self).cores == old(self).cores,
            final(self).view() == old(self).view(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let page = base / PAGE_SZ;
        proof {
            pre.lemma_spent_process(base);
            pre.tables.lemma_root(base);
            crate::layouts::lemma_process_block_layouts();
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies pre.list.pages@[p].addr() == p by {
                lemma_list_page(&pre.list, p);
            }
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.tables.roots.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.processes.records.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.processes.spare.borrow().tracked_borrow((base + 2 * PAGE_SZ) as usize));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.processes.spare.borrow().tracked_borrow((base + 3 * PAGE_SZ) as usize));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.processes.spare.borrow().tracked_borrow((base + 4 * PAGE_SZ) as usize));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.roots.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.records.borrow().tracked_borrow(base));
            lemma_list_page_apart(self.list.pages.borrow_mut(), self.spaces.loaded.borrow().tracked_borrow(base));
            assert forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) implies !(base <= p < base + 8 * PAGE_SZ) by {
                lemma_list_page(&pre.list, p);
            }
        }
        self.blocks.mark_torn_down(page);
        let ghost mid = *self;
        let Tracked(table_root) = self.tables.take_root(&self.list, base);
        let tracked mut perms: Map<usize, PagePerm4k>;
        proof {
            let tracked mut record = self.processes.records.borrow_mut().tracked_remove(base);
            let tracked mut spare2 = self.processes.spare.borrow_mut().tracked_remove((base + 2 * PAGE_SZ) as usize);
            let tracked mut spare3 = self.processes.spare.borrow_mut().tracked_remove((base + 3 * PAGE_SZ) as usize);
            let tracked mut spare4 = self.processes.spare.borrow_mut().tracked_remove((base + 4 * PAGE_SZ) as usize);
            let tracked mut root = self.spaces.roots.borrow_mut().tracked_remove(base);
            let tracked mut space_record = self.spaces.records.borrow_mut().tracked_remove(base);
            let tracked mut cores = self.spaces.loaded.borrow_mut().tracked_remove(base);
            record.leak_contents();
            spare2.leak_contents();
            spare3.leak_contents();
            spare4.leak_contents();
            root.leak_contents();
            space_record.leak_contents();
            cores.leak_contents();
            perms = Map::tracked_empty();
            perms.tracked_insert(page, table_root);
            perms.tracked_insert((page + 1) as usize, crate::layouts::process_record_into_page(record));
            perms.tracked_insert((page + 2) as usize, spare2);
            perms.tracked_insert((page + 3) as usize, spare3);
            perms.tracked_insert((page + 4) as usize, spare4);
            perms.tracked_insert((page + 5) as usize, crate::layouts::page_map_into_page(root));
            perms.tracked_insert((page + 6) as usize, crate::layouts::space_record_into_page(space_record));
            perms.tracked_insert((page + 7) as usize, crate::layouts::core_list_into_page(cores));
            self.processes.holders = Ghost(pre.processes.holders@.remove(base));
            self.processes.bound = Ghost(pre.processes.bound@.remove(base));
            self.spaces.holders = Ghost(pre.spaces.holders@.remove(base));
            self.spaces.bound = Ghost(pre.spaces.bound@.remove(base));
            assert(self.blocks.pages@[page as int].order == 3);
            assert(order_pages(3) == 8);
            assert forall|k: usize| #![trigger perms.contains_key((page + k) as usize)] #![trigger perms[(page + k) as usize]]
                k < order_pages(self.blocks.pages@[page as int].order) implies {
                &&& perms.contains_key((page + k) as usize)
                &&& perms[(page + k) as usize].addr() == (page + k) * PAGE_SZ
                &&& perms[(page + k) as usize].is_uninit()
            } by {
                assert(k < 8);
            }
        }
        self.blocks.free_block(page, Tracked(perms), Tracked(steps));
        proof {
            let post = *self;
            assert forall|i: int| pre.blocks.tracks(i) implies #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(page as int, i) { free_entry() } else { pre.blocks.pages@[i] }) by {
                assert(mid.blocks.in_block(page as int, i) == pre.blocks.in_block(page as int, i));
                if i != page {
                    assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
                }
            }
            assert(post.processes.spare@ == pre.processes.spare@.remove((base + 2 * PAGE_SZ) as usize)
                .remove((base + 3 * PAGE_SZ) as usize).remove((base + 4 * PAGE_SZ) as usize));
            assert(Self::process_freed_step(pre, post, base));
            Self::lemma_process_freed(pre, post, base);
            Self::lemma_bound_threads_same(pre, post);
            Self::lemma_process_freed_tree(pre, post, base);
            assert forall|r: usize, p: SpacePath| #[trigger] walk(tree_of(&post.table_pages, &post.spaces), r, p)
                == walk(tree_of(&pre.table_pages, &pre.spaces), r, p) by {
                lemma_walk_space_removed(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), base, r, p);
            }
            assert forall|k: int| 0 <= k < 8 implies #[trigger] post.blocks.pages@[page + k].kind is Free by {
                assert(pre.blocks.in_block(page as int, page + k));
            }
            assert forall|i: int| pre.blocks.tracks(i) && !(page as int <= i < page + 8)
                implies #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i] by {
                assert(!pre.blocks.in_block(page as int, i));
            }
        }
    }

    /// Frees the spent dead process at `base`, once every core and IOMMU has acknowledged the epoch of its
    /// block's last unmap. Refused while anything is left of it: a reference, a core that depends on its
    /// space, a leaf in its table root or an entry in its space root.
    // In a solver of its own, as free_space is.
    #[verifier::spinoff_prover]
    pub(crate) fn free_process(&mut self, c: usize, root: usize, from: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: ReclaimStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS + ROOT_ENTRIES + (ENTRIES - KERNEL_MEM_END_L4INDEX)
                + (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX,
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            !(ret is Unlinked),
            !(ret is Slice),
            !(ret is Freed) ==> *final(self) == *old(self),
            !(old(self).can_retype_under(root, from, base, PROCESS_ORDER) && old(self).process_is_spent(base)) ==> ret is Refused,
            old(self).can_retype_under(root, from, base, PROCESS_ORDER) && old(self).process_is_spent(base)
                ==> if old(self).acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            ret is Again ==> !old(self).acknowledged(base / PAGE_SZ),
            ret is Freed ==> old(self).process_freed(*final(self), c, root, from, base),
    {
        let ghost pre = *old(self);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, PROCESS_ORDER) {
            Some(found) => found,
            None => { return ReclaimStep::Refused; },
        };
        let page = base / PAGE_SZ;
        if !self.blocks.page_tracked(page) {
            return ReclaimStep::Refused;
        }
        let entry = *self.blocks.pages.get(page);
        let dead_process = match (entry.kind, entry.object) {
            (PageKind::Base, ObjectType::Process) => entry.refs == 0,
            _ => false,
        };
        proof {
            lemma2_to64();
            pre.lemma_process_block(base);
        }
        if !dead_process {
            return ReclaimStep::Refused;
        }
        if !self.process_space_released(base, Tracked(&mut *steps)) {
            return ReclaimStep::Refused;
        }
        if !self.process_roots_clear(base, Tracked(&mut *steps)) {
            return ReclaimStep::Refused;
        }
        if !self.is_acknowledged(page, Tracked(&mut *steps)) {
            return ReclaimStep::Again;
        }
        proof {
            pre.lemma_process_page_unmapped(page);
            pre.lemma_acknowledged_is_clean(page);
            pre.lemma_spent_process(base);
            pre.lemma_process_released(base);
        }
        self.free_spent_process(base, Tracked(steps));
        proof {
            pre.lemma_retype_covers(root, from, base, PROCESS_ORDER);
            lemma_no_change_discharges_teardown(pre.view(), root, untyped, base, pow2(PROCESS_ORDER as nat), base);
            let post = *self;
            assert(Self::step_ok(pre, post, c as int));
        }
        ReclaimStep::Freed
    }
}

} // verus!
