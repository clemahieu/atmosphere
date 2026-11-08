//! Retype reclaiming a dead process's block: a retype cuts its address space root's child tables, a
//! slice per step, each detached two-way so the child's parent record goes with the entry. The space
//! root is inside the process's block, so it goes only with the process, once no core has the space
//! loaded. A root maps no frame, so it holds no mapping node to unlink. See
//! design/teardown-driven-by-retype/.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::mapping::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::space::*;
use crate::define::*;
use crate::pptr::*;

impl CapKernel {
    /// The process at `base` is dead with zero references: no capability names it and no thread is
    /// bound to it.
    pub open spec fn process_is_dead(&self, base: usize) -> bool {
        &&& self.processes.records@.contains_key(base)
        &&& self.blocks.pages@[(base / 4096) as int].refs == 0
    }

    /// No core has the space of the process at `base` on its loaded list, so none holds a translation
    /// of it.
    pub open spec fn process_unloaded(&self, base: usize) -> bool {
        self.spaces.loaded@[base].value().list == 0u32
    }

    /// A retype may cut a child table of the dead process at `base`'s space root: an untyped covers its
    /// block, no core has its space loaded, an entry of the root still names a child and the flush
    /// epoch can rise.
    pub open spec fn can_cut_process_space(&self, root: usize, from: usize, base: usize) -> bool {
        &&& self.can_retype_under(root, from, base, PROCESS_ORDER)
        &&& self.process_is_dead(base)
        &&& self.process_unloaded(base)
        &&& exists|e: usize| #[trigger] tree_of(&self.table_pages, &self.spaces).names_child(base, e)
        &&& self.flush_epoch < usize::MAX
    }

    /// What cutting children of the dead process at `base`'s space root did to self: as for a table
    /// page; the kernel slots are as they were; every table page's parent record names a table or
    /// nothing; and the process is still dead and unloaded.
    pub open spec fn process_space_cut(&self, post: Self, root: usize, from: usize, base: usize) -> bool {
        let a = tree_of(&self.table_pages, &self.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        &&& self.table_children_cut(post, root, from, base)
        &&& forall|i: usize| #![trigger b.entry(base, i)] i < KERNEL_MEM_END_L4INDEX ==> b.entry(base, i) == a.entry(base, i)
        &&& forall|c: usize| #![trigger b.record(c)]
            b.is_page(c) && b.record(c).parent is Some ==> b.is_table(b.record(c).parent->Some_0.table)
        &&& post.process_is_dead(base)
        &&& post.process_unloaded(base)
    }

    /// A block at an order-3 base holds a process exactly when a process record is kept there, and a
    /// process's space is a root of kind Process with no parent at level 4, which no table page shares.
    pub proof fn lemma_process_block(&self, base: usize)
        requires
            self.wf(),
            base % 32768 == 0,
            base / 4096 < NUM_PAGES,
        ensures
            process_block(&self.blocks, base / 4096) == self.processes.records@.contains_key(base),
            self.processes.records@.contains_key(base) ==> {
                &&& self.spaces.roots@.contains_key(base)
                &&& self.spaces.records@[base].value().kind is Process
                &&& self.spaces.loaded@.contains_key(base)
                &&& self.spaces.loaded@[base].addr() == base + SPACE_CORES_PAGE * 4096
                &&& self.spaces.loaded@[base].is_init()
                &&& !self.table_pages.maps@.contains_key(base)
                &&& tree_of(&self.table_pages, &self.spaces).record(base).parent is None
                &&& tree_of(&self.table_pages, &self.spaces).record(base).level == 4
            },
    {
        assert(base % 32768 == 0 ==> base % 8192 == 0) by (bit_vector);
        lemma_leaf_page(base);
        if process_block(&self.blocks, base / 4096) {
            assert(self.processes.records@.contains_key(((base / 4096) * 4096) as usize));
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
                &&& base % 32768 == 0
                &&& base / 4096 < NUM_PAGES
                &&& self.blocks.pages@[(base / 4096) as int].object is Process
            },
    {
        if self.processes.records@.contains_key(base) {
            assert(process_wf(&self.processes, &self.blocks, base));
        }
    }

    /// No core has an unloaded process space loaded, so no core holds a translation of it.
    pub proof fn lemma_process_unloaded(&self, base: usize)
        requires
            self.wf(),
            self.spaces.loaded@.contains_key(base),
            self.process_unloaded(base),
        ensures
            forall|d: int| 0 <= d < NUM_CPUS ==> !#[trigger] self.loaded(d, base),
            forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base ==> !#[trigger] self.tlb@[d].contains(e),
    {
        assert forall|d: int| 0 <= d < NUM_CPUS implies !#[trigger] self.loaded(d, base) by {
            lemma_no_core_listed(d as u32);
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base implies !#[trigger] self.tlb@[d].contains(e) by {
            assert(!self.loaded(d, base));
        }
    }

    /// Cuts up to a budget of the child tables of the dead process at `base`'s space root, under the
    /// untyped at index `from` of the table at `root`, each from the entry naming it, with what that
    /// leaves stale, and leaves the kernel slots. Refused while a core has the space loaded. Returns
    /// whether it ran, and if not nothing changed.
    pub fn cut_process_space(&mut self, root: usize, from: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            Self::mappings_shrunk(*old(self), *final(self)),
            ret == old(self).can_cut_process_space(root, from, base),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).process_space_cut(*final(self), root, from, base),
    {
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            Self::lemma_same_tree_shrunk(pre, pre);
        }
        let untyped = match self.retype_parent(root, from, base, PROCESS_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        let page = base / 4096;
        if page >= NUM_PAGES || self.flush_epoch == usize::MAX {
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
        let list = PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * 4096).borrow(
            Tracked(self.spaces.loaded.borrow().tracked_borrow(base)),
        ).list;
        if list != 0u32 {
            return false;
        }
        proof {
            assert(a.is_root(base));
            assert(a.space_records[base].value().kind is Process);
        }
        let steps = self.cut_children(base, true);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            if steps != 0 {
                lemma_no_change_discharges_teardown(pre.view(), root, untyped, base);
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
            }
        }
        steps != 0
    }
}

} // verus!
