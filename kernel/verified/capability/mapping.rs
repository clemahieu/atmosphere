// SPDX-License-Identifier: MIT

//! What a space maps, read by walking its tables from the root. A kernel
//! slot, which only a process's root has, leads nowhere, since child_slot excludes it. Map, unmap and detach state what they do in these
//! terms. See design/address-spaces-as-objects/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

use crate::arch::load_translation_root;
#[cfg(verus_keep_ghost)]
use crate::capability::block::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
use crate::capability::refs::*;
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::pagetable::entry::PageEntry;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

/// The steps of noting a mapping's unmap stale: the pages its record_run writes, a 2M mapping's
/// PAGES_PER_2M at most. See design/one-lock-bounded-steps/.
pub const MAPPING_NOTE_STEPS: usize = PAGES_PER_2M;

/// fresh_pcid's bound in the step counter: the acknowledgement of a flush of every context, when the
/// core's PCIDs run out.
pub const FRESH_PCID_STEPS: usize = ACKNOWLEDGE_STEPS;

/// load_space's bound in the step counter: one fresh_pcid.
pub const LOAD_SPACE_STEPS: usize = FRESH_PCID_STEPS;

/// The indices of one page of a space's virtual address, level 4 first.
pub ghost struct SpacePath {
    pub l4: usize,
    pub l3: usize,
    pub l2: usize,
    pub l1: usize,
}

/// The table entry i of table t leads to, if it names a child.
pub open spec fn step(tree: TableTree, t: usize, i: usize) -> Option<usize> {
    if tree.names_child(t, i) {
        Some((tree.entry(t, i).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize)
    } else {
        None
    }
}

/// The frame entry i of table t maps, if t is at level 1 and the entry is present.
pub open spec fn frame_entry(tree: TableTree, t: usize, i: usize) -> Option<PageEntry> {
    if tree.is_table(t) && i < ENTRIES && tree.record(t).level == 1 && tree.entry(t, i).perm.present {
        Some(tree.entry(t, i))
    } else {
        None
    }
}

/// The large frame entry i of table t maps, if t is at level 2 and the entry is present with ps.
pub open spec fn large_entry(tree: TableTree, t: usize, i: usize) -> Option<PageEntry> {
    if tree.is_table(t) && i < ENTRIES && tree.record(t).level == 2 && tree.entry(t, i).perm.present && tree.entry(t, i).perm.ps {
        Some(tree.entry(t, i))
    } else {
        None
    }
}

/// What path p of space s maps. A large frame is found at the path of its first page, with ps set in
/// the entry.
pub open spec fn walk(tree: TableTree, s: usize, p: SpacePath) -> Option<PageEntry> {
    if !tree.is_root(s) {
        None
    } else {
        match step(tree, s, p.l4) {
            None => None,
            Some(t3) => match step(tree, t3, p.l3) {
                None => None,
                Some(t2) => match step(tree, t2, p.l2) {
                    None => if p.l1 == 0 { large_entry(tree, t2, p.l2) } else { None },
                    Some(t1) => frame_entry(tree, t1, p.l1),
                },
            },
        }
    }
}

/// The abstract mapping of space s: every path the walk finds a frame entry at.
pub open spec fn space_mapping(tree: TableTree, s: usize) -> IMap<SpacePath, PageEntry> {
    IMap::new(|p: SpacePath| walk(tree, s, p) is Some, |p: SpacePath| walk(tree, s, p)->0)
}

/// The walk of path p of space s finds page g, in the frame it ends at.
pub open spec fn walk_finds(tree: TableTree, s: usize, p: SpacePath, g: usize) -> bool {
    &&& walk(tree, s, p) is Some
    &&& walk(tree, s, p)->0.addr / PAGE_SZ <= g
    &&& g < walk(tree, s, p)->0.addr / PAGE_SZ + entry_pages(if walk(tree, s, p)->0.perm.ps { 2usize } else { 1usize })
}

/// The space's tables say page g: g is the base page of a table of the space, or a page a walk finds.
pub open spec fn space_says(tree: TableTree, s: usize, g: usize) -> bool {
    ||| exists|t: usize| #![trigger tree.record(t)] tree.is_table(t) && tree.record(t).space == Some(s) && t / PAGE_SZ == g
    ||| exists|p: SpacePath| #[trigger] walk_finds(tree, s, p, g)
}

impl CapKernel {
    /// What core c may hold: anything of a space it loaded that the space's tables say now, since it can
    /// walk them whenever it likes, and whatever has left them that it has not flushed. A map or a link
    /// after the load is covered with no write here.
    pub open spec fn core_may_hold(&self, c: int, e: TlbEntry) -> bool {
        ||| self.tlb@[c].contains(e)
        ||| self.depends(c, e.space) && space_says(tree_of(&self.table_pages, &self.spaces), e.space, e.page)
    }

    /// Only a core that loaded a space may hold anything of it.
    pub proof fn lemma_may_hold_loaded(&self, c: int, e: TlbEntry)
        requires
            self.wf(),
            0 <= c < NUM_CPUS,
            self.core_may_hold(c, e),
        ensures
            self.loaded(c, e.space),
    {
    }

    /// No core has loaded a device space, so no core holds anything of it.
    pub proof fn lemma_io_space_unloaded(&self, s: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
            self.spaces.records@[s].value().kind is Device,
        ensures
            forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] self.loaded(c, s),
            forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && e.space == s ==> !#[trigger] self.tlb@[c].contains(e),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies !#[trigger] self.loaded(c, s) by {
            lemma_no_core_listed(c as u32);
        }
    }

    /// Core c loads process space s: from here on it may hold what the space's tables say, and it is on
    /// the space's list of cores, for an unmap to find. Pointing the core's base register at it is
    /// switch_space's. The register names no space, or s already: a load that ran out of PCIDs starts a
    /// new generation, which leaves no space's id valid, and a space the register named would keep a
    /// tag a later load could hand to another space.
    pub fn load_space(&mut self, c: usize, s: usize, Tracked(steps): Tracked<&mut Steps>) -> (pcid: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).spaces.roots@.contains_key(s),
            old(self).spaces.records@[s].value().kind is Process,
            old(self).cores@[c as int].generation < ID_GENERATION_MAX,
            old(self).cores@[c as int].space is None || old(self).cores@[c as int].space == Some(s),
        ensures
            final(steps).count <= old(steps).count + LOAD_SPACE_STEPS,
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).loaded(c as int, s),
            final(self).spaces.loaded@[s].value().retired == 0,
            final(self).depends(c as int, s),
            1 <= pcid < PCID_MAX,
            holds_id(final(self).cores@, final(self).spaces.loaded@, c as int, s),
            id_pcid(final(self).spaces.loaded@[s].value().ids@[c as int]) == pcid,
            final(self).cores@[c as int].pcids_used@.contains(pcid),
            holds_id(old(self).cores@, old(self).spaces.loaded@, c as int, s) ==> {
                &&& pcid == id_pcid(old(self).spaces.loaded@[s].value().ids@[c as int])
                &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation
                &&& final(self).tlb == old(self).tlb
            },
            !holds_id(old(self).cores@, old(self).spaces.loaded@, c as int, s) ==> ({
                &&& !old(self).cores@[c as int].pcids_used@.contains(pcid)
                &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation
                &&& final(self).tlb == old(self).tlb
            } || {
                &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation + 1
                &&& final(self).cores@[c as int].pcids_used@ == Set::<usize>::empty().insert(pcid)
                &&& final(self).tlb@[c as int] == Set::<TlbEntry>::empty()
                &&& final(self).acked(c as int) == old(self).flush_epoch
            }),
            forall|r: usize| r != s && #[trigger] holds_id(final(self).cores@, final(self).spaces.loaded@, c as int, r) ==> {
                &&& holds_id(old(self).cores@, old(self).spaces.loaded@, c as int, r)
                &&& final(self).spaces.loaded@[r] == old(self).spaces.loaded@[r]
            },
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && d != c ==> #[trigger] holds_id(final(self).cores@, final(self).spaces.loaded@, d, r) == holds_id(old(self).cores@, old(self).spaces.loaded@, d, r),
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && d != c && final(self).spaces.loaded@.contains_key(r)
                ==> #[trigger] final(self).spaces.loaded@[r].value().ids@[d] == old(self).spaces.loaded@[r].value().ids@[d],
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).cores@[d] == old(self).cores@[d],
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).tlb@[d] == old(self).tlb@[d],
            forall|e: TlbEntry| #[trigger] final(self).tlb@[c as int].contains(e) ==> old(self).tlb@[c as int].contains(e),
            final(self).cores@[c as int].current_thread == old(self).cores@[c as int].current_thread,
            final(self).cores@[c as int].space == old(self).cores@[c as int].space,
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && !(d == c as int && r == s)
                ==> #[trigger] final(self).loaded(d, r) == old(self).loaded(d, r),
            forall|e: TlbEntry| e.space == s && space_says(tree_of(&old(self).table_pages, &old(self).spaces), s, e.page)
                ==> #[trigger] final(self).core_may_hold(c as int, e),
            final(self).spaces.loaded@ == old(self).spaces.loaded@.insert(s, final(self).spaces.loaded@[s]),
            final(self).spaces.loaded@.dom() == old(self).spaces.loaded@.dom(),
            final(self).spaces.roots == old(self).spaces.roots,
            final(self).spaces.records == old(self).spaces.records,
            final(self).spaces.holders == old(self).spaces.holders,
            final(self).spaces.kernel_entries == old(self).spaces.kernel_entries,
            final(self).spaces.registers == old(self).spaces.registers,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces.bound == old(self).spaces.bound,
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).mappings == old(self).mappings,
            final(self).table_pages == old(self).table_pages,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
    {
        let ghost pre = *old(self);
        proof {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
            reveal(ids_wf);
        }
        let ptr = PPtr::<SpaceCores>::from_usize(s + SPACE_CORES_PAGE * PAGE_SZ);
        let cores = *ptr.borrow(Tracked(self.spaces.loaded.borrow().tracked_borrow(s)));
        let word = cores.ids[c];
        let held = word / PAGE_SZ == self.cores.get(c).generation;
        let pcid = if held {
            proof {
                reveal(ids_wf);
                assert(holds_id(pre.cores@, pre.spaces.loaded@, c as int, s));
            }
            word % PAGE_SZ
        } else {
            proof {
                reveal(ids_wf);
                assert(names_wf(pre.cores@[c as int].space, pre.cores@[c as int].generation, pre.spaces.loaded@, c as int));
            }
            self.fresh_pcid(c, Tracked(steps))
        };
        let ghost after = *self;
        self.note_pcid_used(c, pcid);
        let generation = self.cores.get(c).generation;
        let ghost mid = *self;
        proof {
            reveal(ids_wf);
            lemma_id_word(generation, pcid);
            assert forall|r: usize| r != s && #[trigger] holds_id(mid.cores@, mid.spaces.loaded@, c as int, r)
                implies id_pcid(mid.spaces.loaded@[r].value().ids@[c as int]) != pcid by {
                assert(holds_id(after.cores@, after.spaces.loaded@, c as int, r));
                if held {
                    assert(holds_id(pre.cores@, pre.spaces.loaded@, c as int, r));
                }
            }
        }
        let mut next = cores;
        next.list = cores.list | (1u32 << (c as u32));
        next.retired = 0;
        next.ids[c] = generation * PAGE_SZ + pcid;
        let tracked mut perm = self.spaces.loaded.borrow_mut().tracked_remove(s);
        ptr.write(Tracked(&mut perm), next);
        proof {
            self.spaces.loaded.borrow_mut().tracked_insert(s, perm);
            let post = *self;
            assert(post.spaces.loaded@ =~= mid.spaces.loaded@.insert(s, post.spaces.loaded@[s]));
            assert(post.spaces.loaded@.dom() =~= mid.spaces.loaded@.dom());
            assert(mid.spaces.loaded@ == pre.spaces.loaded@);
            assert forall|d: int| 0 <= d < NUM_CPUS && core_listed(mid.spaces.loaded@[s].value().list, d)
                implies #[trigger] core_listed(post.spaces.loaded@[s].value().list, d) by {
                lemma_core_added(cores.list, c as u32, d as u32);
            }
            lemma_id_loaded(mid.cores@, mid.spaces.loaded@, post.spaces.loaded@, c as int, s, (generation * PAGE_SZ + pcid) as usize);
            assert forall|d: int| 0 <= d < NUM_CPUS && (#[trigger] post.cores@[d]).space is Some
                && mid.spaces.loaded@.contains_key(post.cores@[d].space->0) implies {
                &&& post.spaces.loaded@.contains_key(post.cores@[d].space->0)
                &&& id_pcid(post.spaces.loaded@[post.cores@[d].space->0].value().ids@[d]) == id_pcid(mid.spaces.loaded@[post.cores@[d].space->0].value().ids@[d])
            } by {
                if post.cores@[d].space == Some(s) && d == c as int {
                    assert(names_wf(mid.cores@[d].space, mid.cores@[d].generation, mid.spaces.loaded@, d));
                    assert(held);
                }
            }
            lemma_registers_kept(mid.spaces.registers@, mid.cores@, post.cores@, mid.spaces.loaded@, post.spaces.loaded@, mid.spaces.kernel_root@);
            Self::lemma_core_loaded(mid, post, c as int, s);
            assert forall|e: TlbEntry| e.space == s && space_says(tree_of(&pre.table_pages, &pre.spaces), s, e.page)
                implies #[trigger] post.core_may_hold(c as int, e) by {
                assert(post.depends(c as int, e.space));
            }
        }
        pcid
    }

    /// A root at any offset of a table block but a space's root page is no space's root, since every
    /// space starts a block of TABLE_PAGE_BYTES: the root switch_space takes for None.
    pub proof fn lemma_no_space_root(&self, root: usize)
        requires
            self.wf(),
            root % TABLE_PAGE_BYTES != SPACE_ROOT_PAGE * PAGE_SZ,
        ensures
            forall|s: usize| #[trigger] self.spaces.roots@.contains_key(s) ==> root != s + SPACE_ROOT_PAGE * PAGE_SZ,
    {
        assert forall|s: usize| #[trigger] self.spaces.roots@.contains_key(s) implies root != s + SPACE_ROOT_PAGE * PAGE_SZ by {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
            let q = s as int / TABLE_PAGE_BYTES as int;
            lemma_fundamental_div_mod(s as int, TABLE_PAGE_BYTES as int);
            lemma_mod_multiples_vanish(q, (SPACE_ROOT_PAGE * PAGE_SZ) as int, TABLE_PAGE_BYTES as int);
            lemma_small_mod((SPACE_ROOT_PAGE * PAGE_SZ) as nat, TABLE_PAGE_BYTES as nat);
        }
    }

    /// No space holds KERNEL_TAG on any core, so what a core caches under it is no space's.
    pub proof fn lemma_kernel_tag(&self)
        requires
            self.wf(),
        ensures
            forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(self.cores@, self.spaces.loaded@, c, s)
                ==> id_pcid(self.spaces.loaded@[s].value().ids@[c]) != KERNEL_TAG,
    {
        assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(self.cores@, self.spaces.loaded@, c, s)
            implies id_pcid(self.spaces.loaded@[s].value().ids@[c]) != KERNEL_TAG by {
            self.lemma_id_handed_out(c, s, 0);
        }
    }

    /// Points core c's base register at `root` under `tag`, through the register the kernel holds for c,
    /// and records the space it names in the same step, so the record is the register's latest write
    /// (registers_wf). `root` is the root of `space`, or for None a root that is no space's under
    /// KERNEL_TAG, which no space holds (lemma_kernel_tag): the root c booted on, or one at no space's
    /// root offset. Every space's root is at SPACE_ROOT_PAGE of a block of TABLE_PAGE_BYTES, so a root at
    /// another offset of such a block is none, now or after any retype (lemma_no_space_root), and the
    /// record never says no space while the register names one. That the boot root is the kernel's own,
    /// a page outside every untyped that maps no page a space maps, is the glue's to keep, not this
    /// model's. A space's root goes in under the PCID or ASID the space holds on c, so what the core then
    /// caches is under that space's tag. A register names only a loaded space that is not retired, and a
    /// retire refuses while one names it, so a core that has acknowledged a retire never walks the space
    /// again. See design/teardown-driven-by-retype/.
    pub fn switch_space(&mut self, c: usize, space: Option<usize>, root: usize, tag: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            root % PAGE_SZ == 0,
            match space {
                Some(s) => {
                    &&& root == s + SPACE_ROOT_PAGE * PAGE_SZ
                    &&& old(self).loaded(c as int, s)
                    &&& old(self).spaces.loaded@[s].value().retired == 0
                    &&& holds_id(old(self).cores@, old(self).spaces.loaded@, c as int, s)
                    &&& tag == id_pcid(old(self).spaces.loaded@[s].value().ids@[c as int])
                },
                None => {
                    &&& root == old(self).spaces.kernel_root@ || root % TABLE_PAGE_BYTES != SPACE_ROOT_PAGE * PAGE_SZ
                    &&& tag == KERNEL_TAG
                },
            },
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).cores@[c as int].space == space,
            final(self).spaces.registers@[c as int].root() == root,
            final(self).spaces.registers@[c as int].tag() == tag,
            final(self).cores@[c as int].current_thread == old(self).cores@[c as int].current_thread,
            final(self).cores@[c as int].acked_epoch == old(self).cores@[c as int].acked_epoch,
            final(self).cores@[c as int].generation == old(self).cores@[c as int].generation,
            final(self).cores@[c as int].next_pcid == old(self).cores@[c as int].next_pcid,
            final(self).cores@[c as int].pcids_used == old(self).cores@[c as int].pcids_used,
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).cores@[d] == old(self).cores@[d],
            forall|d: int, r: usize| 0 <= d < NUM_CPUS ==> #[trigger] holds_id(final(self).cores@, final(self).spaces.loaded@, d, r) == holds_id(old(self).cores@, old(self).spaces.loaded@, d, r),
            final(self).tlb == old(self).tlb,
            final(self).spaces.roots == old(self).spaces.roots,
            final(self).spaces.records == old(self).spaces.records,
            final(self).spaces.loaded == old(self).spaces.loaded,
            final(self).spaces.holders == old(self).spaces.holders,
            final(self).spaces.bound == old(self).spaces.bound,
            final(self).spaces.kernel_entries == old(self).spaces.kernel_entries,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces == (Spaces { registers: final(self).spaces.registers, ..old(self).spaces }),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).mappings == old(self).mappings,
            final(self).table_pages == old(self).table_pages,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
    {
        let ghost pre = *old(self);
        let state = *self.cores.get(c);
        self.cores.set(c, CoreState {
            current_thread: state.current_thread,
            acked_epoch: state.acked_epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            pcids_used: state.pcids_used,
            space,
        });
        proof {
            reveal(registers_wf);
            assert(pre.spaces.registers@.contains_key(c as int));
            assert(pre.spaces.registers@[c as int].core() == c as int);
        }
        let tracked mut register = self.spaces.registers.borrow_mut().tracked_remove(c as int);
        load_translation_root(Tracked(&mut register), root, tag);
        proof {
            self.spaces.registers.borrow_mut().tracked_insert(c as int, register);
            let post = *self;
            reveal(registers_wf);
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies #[trigger] post.cores@[d] == pre.cores@[d] by {}
            assert(post.spaces.registers@ =~= pre.spaces.registers@.insert(c as int, register));
            assert(post.spaces.loaded@ == pre.spaces.loaded@);
            assert forall|d: int| 0 <= d < NUM_CPUS implies {
                &&& #[trigger] post.spaces.registers@.contains_key(d)
                &&& register_names(post.spaces.registers@[d], post.cores@[d].space, post.spaces.loaded@, d, post.spaces.kernel_root@)
            } by {
                assert(pre.spaces.registers@.contains_key(d));
                if d != c as int {
                    assert(post.cores@[d] == pre.cores@[d]);
                    assert(post.spaces.registers@[d] == pre.spaces.registers@[d]);
                    assert(register_names(pre.spaces.registers@[d], pre.cores@[d].space, pre.spaces.loaded@, d, pre.spaces.kernel_root@));
                } else {
                    assert(post.spaces.registers@[d] == register);
                    if let Some(s) = space {
                        assert(holds_id(pre.cores@, pre.spaces.loaded@, c as int, s));
                    }
                }
            }
            assert(registers_wf(post.spaces.registers@, post.cores@, post.spaces.loaded@, post.spaces.kernel_root@));
            lemma_ids_named(pre.cores@, post.cores@, post.spaces.loaded@, c as int);
            Self::lemma_iommus_same(pre, post);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread by {
                if d != c {
                    assert(post.cores@[d] == pre.cores@[d]);
                }
            }
            lemma_current_same(pre.cores@, post.cores@, pre.threads.records@, post.threads.records@);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) <= post.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
                assert(post.acked(d) == pre.acked(d));
            }
            assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) implies post.depends(d, e.space) by {
                assert(pre.depends(d, e.space));
                assert(post.acked(d) == pre.acked(d));
            }
            assert forall|d: int, e: TlbEntry|
                0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) && !post.mapped@.contains(e.page)
                implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(d), e.page) by {
                assert(post.acked(d) == pre.acked(d));
            }
        }
    }

    /// Hands out core c's next PCID. Run out, it flushes every context on this core first and starts a
    /// new generation, which leaves no space's id valid here, so the core's base register names no space.
    fn fresh_pcid(&mut self, c: usize, Tracked(steps): Tracked<&mut Steps>) -> (p: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).cores@[c as int].generation < ID_GENERATION_MAX,
            old(self).cores@[c as int].space is None,
        ensures
            final(steps).count <= old(steps).count + FRESH_PCID_STEPS,
            Self::step_ok(*old(self), *final(self), c as int),
            Self::only_core_changed(*old(self), *final(self), c as int),
            1 <= p < PCID_MAX,
            p < final(self).cores@[c as int].next_pcid,
            !final(self).cores@[c as int].pcids_used@.contains(p),
            forall|s: usize| #[trigger] holds_id(final(self).cores@, final(self).spaces.loaded@, c as int, s)
                ==> id_pcid(final(self).spaces.loaded@[s].value().ids@[c as int]) != p,
            forall|s: usize| #[trigger] holds_id(final(self).cores@, final(self).spaces.loaded@, c as int, s)
                ==> holds_id(old(self).cores@, old(self).spaces.loaded@, c as int, s),
            old(self).cores@[c as int].next_pcid != PCID_MAX ==> {
                &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation
                &&& final(self).cores@[c as int].pcids_used@ == old(self).cores@[c as int].pcids_used@
                &&& final(self).tlb == old(self).tlb
                &&& !old(self).cores@[c as int].pcids_used@.contains(p)
            },
            old(self).cores@[c as int].next_pcid == PCID_MAX ==> {
                &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation + 1
                &&& final(self).cores@[c as int].pcids_used@ == Set::<usize>::empty()
                &&& final(self).tlb@[c as int] == Set::<TlbEntry>::empty()
                &&& final(self).acked(c as int) == old(self).flush_epoch
            },
    {
        let ghost pre = *old(self);
        proof {
            reveal(ids_wf);
        }
        let state = *self.cores.get(c);
        if state.next_pcid == PCID_MAX {
            self.acknowledge(c, Tracked(steps));
            let ghost mid = *self;
            let state = *self.cores.get(c);
            self.cores.set(c, CoreState {
                current_thread: state.current_thread,
                acked_epoch: state.acked_epoch,
                generation: state.generation + 1,
                next_pcid: 2,
                pcids_used: state.pcids_used,
                space: state.space,
            });
            proof {
                let post = *self;
                assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies #[trigger] post.cores@[d] == mid.cores@[d] by {}
                lemma_ids_new_generation(mid.cores@, post.cores@, post.spaces.loaded@, c as int);
                Self::lemma_core_ids(mid, post, c as int);
            }
            1
        } else {
            self.cores.set(c, CoreState {
                current_thread: state.current_thread,
                acked_epoch: state.acked_epoch,
                generation: state.generation,
                next_pcid: state.next_pcid + 1,
                pcids_used: state.pcids_used,
                space: state.space,
            });
            proof {
                let post = *self;
                assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies #[trigger] post.cores@[d] == pre.cores@[d] by {}
                assert forall|p: usize| #[trigger] post.cores@[c as int].pcids_used@.contains(p) implies p < post.cores@[c as int].next_pcid by {
                    assert(pre.cores@[c as int].pcids_used@.contains(p));
                }
                lemma_ids_core_step(pre.cores@, post.cores@, post.spaces.loaded@, c as int);
                Self::lemma_core_ids(pre, post, c as int);
            }
            state.next_pcid
        }
    }

    /// Core c is about to run under this PCID, so it may hold entries under it.
    fn note_pcid_used(&mut self, c: usize, p: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            p < old(self).cores@[c as int].next_pcid,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            Self::only_core_changed(*old(self), *final(self), c as int),
            final(self).tlb == old(self).tlb,
            final(self).cores@[c as int].generation == old(self).cores@[c as int].generation,
            final(self).cores@[c as int].next_pcid == old(self).cores@[c as int].next_pcid,
            final(self).cores@[c as int].pcids_used@ == old(self).cores@[c as int].pcids_used@.insert(p),
    {
        let ghost pre = *old(self);
        let state = *self.cores.get(c);
        self.cores.set(c, CoreState {
            current_thread: state.current_thread,
            acked_epoch: state.acked_epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            pcids_used: Ghost(state.pcids_used@.insert(p)),
            space: state.space,
        });
        proof {
            let post = *self;
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies #[trigger] post.cores@[d] == pre.cores@[d] by {}
            reveal(ids_wf);
            assert forall|q: usize| #[trigger] post.cores@[c as int].pcids_used@.contains(q) implies q < post.cores@[c as int].next_pcid by {
                if q != p {
                    assert(pre.cores@[c as int].pcids_used@.contains(q));
                }
            }
            lemma_ids_core_step(pre.cores@, post.cores@, post.spaces.loaded@, c as int);
            Self::lemma_core_ids(pre, post, c as int);
        }
    }

    /// The invariant after a step that changed only core c's ids, given that they still hold.
    proof fn lemma_core_ids(pre: Self, post: Self, c: int)
        requires
            pre.wf(),
            0 <= c < NUM_CPUS,
            post.cores.wf(),
            ids_wf(post.cores@, post.spaces.loaded@),
            Self::only_core_changed(pre, post, c),
            post.tlb == pre.tlb,
            post.acked(c) == pre.acked(c),
        ensures
            post.wf(),
            Self::step_ok(pre, post, c),
    {
        Self::lemma_registers_core(pre, post, c);
        Self::lemma_iommus_same(pre, post);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread by {
            if d != c {
                assert(post.cores@[d] == pre.cores@[d]);
            }
        }
        lemma_current_same(pre.cores@, post.cores@, pre.threads.records@, post.threads.records@);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) <= post.flush_epoch by {
            assert(pre.acked(d) <= pre.flush_epoch);
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) implies post.depends(d, e.space) by {
            assert(pre.tlb@[d].contains(e));
            assert(pre.depends(d, e.space));
        }
        assert forall|d: int, e: TlbEntry|
            0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(d), e.page) by {
            assert(pre.tlb@[d].contains(e));
        }
    }

    /// The invariant after core c joins space s's list of cores: the spaces keep theirs, since only the
    /// one list's value changed, and a core on a list stays on it.
    proof fn lemma_core_loaded(pre: Self, post: Self, c: int, s: usize)
        requires
            pre.wf(),
            0 <= c < NUM_CPUS,
            pre.spaces.roots@.contains_key(s),
            pre.spaces.records@[s].value().kind is Process,
            post.iommus == pre.iommus,
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.spaces.holders == pre.spaces.holders,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            post.spaces.registers == pre.spaces.registers,
            post.spaces.kernel_root == pre.spaces.kernel_root,
            post.spaces.bound == pre.spaces.bound,
            post.spaces.loaded@ == pre.spaces.loaded@.insert(s, post.spaces.loaded@[s]),
            post.spaces.loaded@[s].addr() == pre.spaces.loaded@[s].addr(),
            post.spaces.loaded@[s].is_init(),
            post.spaces.loaded@[s].value().list == pre.spaces.loaded@[s].value().list | (1u32 << (c as u32)),
            post.spaces.loaded@[s].value().retired == 0,
            ids_wf(post.cores@, post.spaces.loaded@),
            registers_wf(post.spaces.registers@, post.cores@, post.spaces.loaded@, post.spaces.kernel_root@),
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.table_pages == pre.table_pages,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.cores == pre.cores,
            post.tlb == pre.tlb,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.flush_epoch == pre.flush_epoch,
        ensures
            post.wf(),
            post.loaded(c, s),
            post.depends(c, s),
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && !(d == c && r == s)
                ==> #[trigger] post.loaded(d, r) == pre.loaded(d, r),
            tree_of(&post.table_pages, &post.spaces) == tree_of(&pre.table_pages, &pre.spaces),
    {
        let sa = &pre.spaces;
        let sb = &post.spaces;
        assert(space_wf(&pre.list, sa, &pre.blocks, s));
        lemma_core_added(sa.loaded@[s].value().list, c as u32, c as u32);
        assert(post.loaded(c, s));
        assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && !(d == c && r == s)
            implies #[trigger] post.loaded(d, r) == pre.loaded(d, r) by {
            if r == s {
                lemma_core_added(sa.loaded@[s].value().list, c as u32, d as u32);
            } else {
                assert(sb.loaded@.contains_key(r) == sa.loaded@.contains_key(r));
                if sa.loaded@.contains_key(r) {
                    assert(sb.loaded@[r] == sa.loaded@[r]);
                }
            }
        }
        assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && #[trigger] pre.loaded(d, r) implies post.loaded(d, r) by {
            if r == s {
                lemma_core_added(sa.loaded@[s].value().list, c as u32, d as u32);
            } else {
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
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) <= post.flush_epoch by {
            assert(pre.acked(d) <= pre.flush_epoch);
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) implies post.depends(d, e.space) by {
            assert(pre.tlb@[d].contains(e));
            assert(pre.depends(d, e.space));
            assert(post.loaded(d, e.space));
            if e.space != s {
                assert(sb.loaded@[e.space] == sa.loaded@[e.space]);
            }
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

    /// The step touched no table, so no space's mapping changed.
    pub open spec fn same_tree(pre: Self, post: Self) -> bool {
        tree_of(&post.table_pages, &post.spaces) == tree_of(&pre.table_pages, &pre.spaces)
    }

    /// The step took entries away and put none in: whatever a walk finds now, it found before.
    pub open spec fn mappings_shrunk(pre: Self, post: Self) -> bool {
        forall|r: usize, p: SpacePath| #![trigger walk(tree_of(&post.table_pages, &post.spaces), r, p)]
            walk(tree_of(&post.table_pages, &post.spaces), r, p) is Some
                ==> walk(tree_of(&post.table_pages, &post.spaces), r, p) == walk(tree_of(&pre.table_pages, &pre.spaces), r, p)
    }

    /// Node n's unmap is recorded: the epoch rose past every acknowledgement and is written for each page
    /// the node mapped, so no such page counts as acknowledged, each such page is in the TLB of every core
    /// that loaded the space and only a flush takes it out, and a page leaves mapped when no other mapping
    /// names it.
    pub open spec fn mapping_stale_noted(pre: Self, post: Self, n: usize) -> bool {
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let m = pre.mappings@[n];
        let pages = record_pages(m);
        let space = tree.record(m.table).space;
        &&& post.flush_epoch == pre.flush_epoch + 1
        &&& forall|g: usize| #[trigger] pages.contains(g) ==> post.stale_epoch.written(post.flush_epoch, g)
        &&& forall|g: usize| #[trigger] pages.contains(g) ==> !post.acknowledged(g)
        &&& forall|d: int, g: usize| #![trigger post.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g })]
            0 <= d < NUM_CPUS && space is Some && pre.depends(d, space->Some_0) && pages.contains(g)
            ==> post.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g })
        &&& forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] pre.tlb@[d].contains(e) ==> post.tlb@[d].contains(e)
        &&& forall|i: int, g: usize| #![trigger post.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g })]
            0 <= i < NUM_IOMMUS && pre.iommu_present(i) && space is Some && pre.spaces.records@[space->Some_0].value().kind is Device && pages.contains(g)
            ==> post.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g })
        &&& forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] pre.iommus.tlb@[i].contains(e) ==> post.iommus.tlb@[i].contains(e)
        &&& post.iommus.acked == pre.iommus.acked
        &&& post.iommus.present == pre.iommus.present
        &&& post.iommus.commands == pre.iommus.commands
        &&& forall|g: usize| #[trigger] post.mapped@.contains(g)
            == (pre.mapped@.contains(g) && (!pages.contains(g) || page_named(pre.mappings@.remove(n), g)))
    }

    /// Node n's mapping is gone: its entry is empty, its record and its reference with it, every other
    /// entry is as it was, its table's page is the only one written, and the only walks changed are
    /// those that ended at that entry.
    pub open spec fn mapping_unlinked(pre: Self, post: Self, n: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let m = pre.mappings@[n];
        let br = block_ref(&pre.blocks, m.frame);
        &&& post.table_pages.maps@ == pre.table_pages.maps@.insert(m.table, post.table_pages.maps@[m.table])
        &&& post.table_pages.maps@[m.table].addr() == pre.table_pages.maps@[m.table].addr()
        &&& post.table_pages.maps@[m.table].is_init()
        &&& post.table_pages.maps@[m.table].value().wf()
        &&& post.table_pages.maps@[m.table].value().level == pre.table_pages.maps@[m.table].value().level
        &&& b.entry(m.table, m.entry).is_empty()
        &&& entries_cleared(a, b, m.table, m.entry)
        &&& walks_cut(a, b, m.table, m.entry)
        &&& post.mappings@ == pre.mappings@.remove(n)
        &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) - 1) as usize, block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1)
        &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].remove(n))
    }

    /// Unlinking a mapping takes a walk's entry away and puts none in.
    pub proof fn lemma_unlinked_shrunk(pre: Self, post: Self, n: usize)
        requires
            Self::mapping_unlinked(pre, post, n),
        ensures
            Self::mappings_shrunk(pre, post),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let m = pre.mappings@[n];
        reveal(walks_cut);
        assert forall|r: usize, p: SpacePath| #![trigger walk(b, r, p)]
            walk(b, r, p) is Some implies walk(b, r, p) == walk(a, r, p) by {
            assert(walk(b, r, p) == (if ends_at(a, r, p, m.table, m.entry) { None } else { walk(a, r, p) }));
        }
    }

    /// A step that keeps the tree keeps every walk.
    pub proof fn lemma_same_tree_shrunk(pre: Self, post: Self)
        requires
            Self::same_tree(pre, post),
        ensures
            Self::mappings_shrunk(pre, post),
    {
    }
}

/// Every entry but e of t, and every entry of every other table, is as it was. Kept opaque: the rule
/// relates every entry of b to a's and would otherwise feed every quantifier over entries.
#[verifier::opaque]
pub open spec fn entries_cleared(a: TableTree, b: TableTree, t: usize, e: usize) -> bool {
    forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        i < ENTRIES && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i)
}

/// The walks that ended at entry e of t find nothing, and every other walk finds what it did. Kept
/// opaque for the same reason as entries_cleared.
#[verifier::opaque]
pub open spec fn walks_cut(a: TableTree, b: TableTree, t: usize, e: usize) -> bool {
    forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p)
        == if ends_at(a, r, p, t, e) { None } else { walk(a, r, p) }
}

/// Path p of space r reaches entry e of table t: an entry of a level 1 table, or a large frame's entry
/// of a level 2 table at its first page's path.
pub open spec fn ends_at(tree: TableTree, r: usize, p: SpacePath, t: usize, e: usize) -> bool {
    &&& tree.is_root(r)
    &&& match step(tree, r, p.l4) {
        None => false,
        Some(t3) => match step(tree, t3, p.l3) {
            None => false,
            Some(t2) => {
                ||| p.l1 == e && step(tree, t2, p.l2) == Some(t)
                ||| p.l1 == 0 && p.l2 == e && t2 == t && large_entry(tree, t, e) is Some
            },
        },
    }
}

/// The pages an entry of a table at this level maps: one at level 1, a large frame's 512 at level 2.
pub open spec fn entry_pages(level: usize) -> int {
    if level == 2 {
        (PAGES_PER_2M as int)
    } else {
        1
    }
}

/// The level of table a map writes: 2 for a large frame, 1 otherwise.
pub open spec fn map_level(large: bool) -> usize {
    if large {
        2
    } else {
        1
    }
}

/// The pages a map of this first page maps.
pub open spec fn map_pages(frame: usize, large: bool) -> Set<usize> {
    Set::<usize>::range(frame, (frame + entry_pages(map_level(large))) as usize)
}

/// What map_pages holds, when its range fits.
pub proof fn lemma_map_pages(frame: usize, large: bool)
    requires
        frame + entry_pages(map_level(large)) <= usize::MAX,
    ensures
        forall|g: usize| #[trigger] map_pages(frame, large).contains(g) <==> frame <= g < frame + entry_pages(map_level(large)),
{
    vstd::set_lib::range_set_properties::<usize>(frame, (frame + entry_pages(map_level(large))) as usize);
}

/// The pages mapping record m maps.
pub open spec fn record_pages(m: MappingRecord) -> Set<usize> {
    map_pages(m.frame, m.large)
}

/// Some mapping record maps page g.
pub open spec fn page_named(mappings: IMap<usize, MappingRecord>, g: usize) -> bool {
    exists|n: usize| #![trigger mappings[n]] mappings.contains_key(n) && record_pages(mappings[n]).contains(g)
}

/// A page is mapped exactly while a mapping record names it.
pub open spec fn mapped_wf(mapped: Set<usize>, mappings: IMap<usize, MappingRecord>) -> bool {
    forall|g: usize| #[trigger] mapped.contains(g) == page_named(mappings, g)
}

/// A run of pages inside a frame capability lies in the capability's block, which is also its first
/// page's block.
pub proof fn lemma_mapped_page_in_block(blocks: &BlockTable, i: usize, p: Payload, frame: usize, count: int, g: usize)
    requires
        blocks.wf(),
        i == p.base / PAGE_SZ,
        blocks.tracks(i as int),
        block_typed(blocks, block_ref(blocks, i)),
        frame_in_block(block_ref(blocks, i), p),
        p.base <= frame * PAGE_SZ,
        frame * PAGE_SZ + count * PAGE_SZ <= p.base as int + block_bytes(p.order),
        blocks.tracks(frame as int),
        count >= 1,
        frame <= g < frame + count,
    ensures
        block_ref(blocks, frame) == block_ref(blocks, i),
        block_has_page(block_ref(blocks, i), g),
{
    match block_ref(blocks, i) {
        BlockRef::Small(b) => {
            assert(block_bytes(0) == PAGE_SZ) by {
                vstd::arithmetic::power2::lemma2_to64();
            }
        },
        BlockRef::Two(r) => {},
        BlockRef::One(r) => {
            if blocks.regions_2m@[(frame / PAGES_PER_2M) as int].typed {
                lemma_large_block_alone(blocks, Large::Two, frame / PAGES_PER_2M, BlockRef::One(r), frame);
            }
        },
    }
}

/// A new mapping's pages join mapped.
pub proof fn lemma_mapped_inserted(mapped: Set<usize>, mappings: IMap<usize, MappingRecord>, n: usize, m: MappingRecord)
    requires
        mapped_wf(mapped, mappings),
        !mappings.contains_key(n),
    ensures
        mapped_wf(mapped.union(record_pages(m)), mappings.insert(n, m)),
{
    let post = mappings.insert(n, m);
    assert forall|g: usize| #[trigger] mapped.union(record_pages(m)).contains(g) == page_named(post, g) by {
        if mapped.contains(g) {
            let o = choose|o: usize| #![trigger mappings[o]] mappings.contains_key(o) && record_pages(mappings[o]).contains(g);
            assert(post[o] == mappings[o]);
        }
        if record_pages(m).contains(g) {
            assert(post[n] == m);
        }
        if page_named(post, g) {
            let o = choose|o: usize| #![trigger post[o]] post.contains_key(o) && record_pages(post[o]).contains(g);
            if o != n {
                assert(mappings[o] == post[o]);
                assert(mapped.contains(g));
            }
        }
    }
}

/// With mapping n gone, a page stays mapped only if another mapping names it.
pub proof fn lemma_mapped_removed(mapped: Set<usize>, post: Set<usize>, mappings: IMap<usize, MappingRecord>, n: usize)
    requires
        mapped_wf(mapped, mappings),
        mappings.contains_key(n),
        forall|g: usize| #[trigger] post.contains(g)
            == (mapped.contains(g) && (!record_pages(mappings[n]).contains(g) || page_named(mappings.remove(n), g))),
    ensures
        mapped_wf(post, mappings.remove(n)),
{
    let rest = mappings.remove(n);
    assert forall|g: usize| #[trigger] post.contains(g) == page_named(rest, g) by {
        if page_named(rest, g) {
            let o = choose|o: usize| #![trigger rest[o]] rest.contains_key(o) && record_pages(rest[o]).contains(g);
            assert(mappings[o] == rest[o]);
            assert(mapped.contains(g));
        }
        if mapped.contains(g) && !record_pages(mappings[n]).contains(g) {
            let o = choose|o: usize| #![trigger mappings[o]] mappings.contains_key(o) && record_pages(mappings[o]).contains(g);
            assert(o != n);
            assert(rest[o] == mappings[o]);
        }
    }
}

/// The entries a core that loaded space s may hold for these pages.
pub open spec fn stale_entries(s: usize, pages: Set<usize>) -> Set<TlbEntry> {
    pages.map(|g: usize| TlbEntry { space: s, page: g })
}

pub proof fn lemma_stale_entries(s: usize, pages: Set<usize>)
    ensures
        forall|e: TlbEntry| #[trigger] stale_entries(s, pages).contains(e) <==> e.space == s && pages.contains(e.page),
{
    broadcast use Set::lemma_map_contains;
    let f = |g: usize| TlbEntry { space: s, page: g };
    assert forall|e: TlbEntry| #[trigger] stale_entries(s, pages).contains(e) <==> e.space == s && pages.contains(e.page) by {
        if e.space == s && pages.contains(e.page) {
            assert(f(e.page) == e);
        }
    }
}

/// What a mapping node holds, by its node: the table and entry that map a frame, the frame's page, and
/// whether the entry is a large one.
pub ghost struct MappingRecord {
    pub table: usize,
    pub entry: usize,
    pub frame: usize,
    pub large: bool,
}

/// Entry e of the table page at t has its node at node e + 1 of the block's node pages, so an entry finds
/// its mapping in constant time. Node 0 is the hidden node.
pub open spec fn mapping_node(t: usize, e: usize) -> usize {
    (t + ((e + 1) / NODES_PER_PAGE as int) * PAGE_SZ + (e + 1) % NODES_PER_PAGE as int) as usize
}

/// Mapping node n stands for a present entry of a level 1 table, or a present ps entry of a level 2
/// table, naming its frame, whose first page it is. It is a child of a frame capability covering the
/// pages the entry maps, and it holds a reference on the frame's block and on no other.
pub open spec fn mapping_wf(list: &Tree, tables: &Tables, tree: TableTree, blocks: &BlockTable, holders: IMap<BlockRef, Set<usize>>, mappings: IMap<usize, MappingRecord>, n: usize) -> bool {
    let m = mappings[n];
    let c = list.parent@[n];
    &&& n == mapping_node(m.table, m.entry)
    &&& n < NODE_SPACE
    &&& list.valid(n)
    &&& list.nodes@[n as int].live
    &&& list.nodes@[n as int].kind is Mapping
    &&& tree.is_page(m.table)
    &&& tree.record(m.table).level == 1 || tree.record(m.table).level == 2
    &&& m.large == (tree.record(m.table).level == 2)
    &&& m.entry < ENTRIES
    &&& tree.entry(m.table, m.entry).perm.present
    &&& tree.entry(m.table, m.entry).perm.ps == (tree.record(m.table).level == 2)
    &&& tree.entry(m.table, m.entry).addr == m.frame * PAGE_SZ
    &&& blocks.tracks(m.frame as int)
    &&& tree.record(m.table).level == 2 ==> m.frame % PAGES_PER_2M == 0
    &&& holders.contains_key(block_ref(blocks, m.frame))
    &&& holders[block_ref(blocks, m.frame)].contains(n)
    &&& forall|br: BlockRef| holders.contains_key(br) && #[trigger] holders[br].contains(n) ==> br == block_ref(blocks, m.frame)
    &&& list.parent@.contains_key(n)
    &&& tables.is_cap(list, c)
    &&& tables.payload_of(c).kind is Frame
    &&& tables.payload_of(c).base <= m.frame * PAGE_SZ
    &&& m.frame * PAGE_SZ + entry_pages(tree.record(m.table).level) * PAGE_SZ <= tables.payload_of(c).base as int + block_bytes(tables.payload_of(c).order)
}

/// Entry e of t is a frame mapping: a present entry of a level 1 table page, or a present ps entry of a
/// level 2 one.
pub open spec fn frame_slot(tree: TableTree, t: usize, e: usize) -> bool {
    &&& tree.is_page(t)
    &&& tree.record(t).level == 1 || (tree.record(t).level == 2 && tree.entry(t, e).perm.ps)
    &&& e < ENTRIES
    &&& tree.entry(t, e).perm.present
}

/// A live mapping node has a record, and a present entry of a level 1 table has the node that says so.
pub open spec fn mappings_wf(list: &Tree, tables: &Tables, tree: TableTree, blocks: &BlockTable, holders: IMap<BlockRef, Set<usize>>, mappings: IMap<usize, MappingRecord>) -> bool {
    &&& forall|n: usize| #[trigger] mappings.contains_key(n) ==> mapping_wf(list, tables, tree, blocks, holders, mappings, n)
    &&& forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Mapping
        ==> mappings.contains_key(n)
    &&& forall|t: usize, e: usize| #[trigger] frame_slot(tree, t, e) ==> {
        &&& mappings.contains_key(mapping_node(t, e))
        &&& mappings[mapping_node(t, e)].table == t
        &&& mappings[mapping_node(t, e)].entry == e
    }
}

/// The frame mappings of a and of b are one set, each entry as it was.
pub open spec fn same_frame_entries(a: TableTree, b: TableTree) -> bool {
    &&& forall|t: usize, e: usize| #[trigger] frame_slot(a, t, e) ==> {
        &&& frame_slot(b, t, e)
        &&& b.record(t).level == a.record(t).level
        &&& b.entry(t, e) == a.entry(t, e)
    }
    &&& forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) ==> frame_slot(a, t, e)
}

/// What mappings_wf reads of mapping node n besides the tree and the records: its node, its parent's
/// capability, its frame's block and its place among the holders. Each is as it was, under whatever
/// name the parent now has.
pub open spec fn mapping_node_kept(
    list_a: &Tree,
    tables_a: &Tables,
    blocks_a: &BlockTable,
    holders_a: IMap<BlockRef, Set<usize>>,
    list_b: &Tree,
    tables_b: &Tables,
    blocks_b: &BlockTable,
    holders_b: IMap<BlockRef, Set<usize>>,
    frame: usize,
    n: usize,
) -> bool {
    &&& list_b.valid(n)
    &&& list_b.parent@.contains_key(n)
    &&& tables_b.is_cap(list_b, list_b.parent@[n])
    &&& tables_b.payload_of(list_b.parent@[n]) == tables_a.payload_of(list_a.parent@[n])
    &&& block_ref(blocks_b, frame) == block_ref(blocks_a, frame)
    &&& holders_b.contains_key(block_ref(blocks_a, frame))
    &&& holders_b[block_ref(blocks_a, frame)].contains(n)
    &&& forall|br: BlockRef| holders_b.contains_key(br) && #[trigger] holders_b[br].contains(n)
        ==> holders_a.contains_key(br) && holders_a[br].contains(n)
}

/// The mappings after a step that kept every frame mapping, every mapping node and what each reads.
pub proof fn lemma_mappings_kept(
    list_a: &Tree,
    tables_a: &Tables,
    tree_a: TableTree,
    blocks_a: &BlockTable,
    holders_a: IMap<BlockRef, Set<usize>>,
    list_b: &Tree,
    tables_b: &Tables,
    tree_b: TableTree,
    blocks_b: &BlockTable,
    holders_b: IMap<BlockRef, Set<usize>>,
    mappings: IMap<usize, MappingRecord>,
)
    requires
        mappings_wf(list_a, tables_a, tree_a, blocks_a, holders_a, mappings),
        same_mapping_nodes(list_a, list_b),
        same_frame_entries(tree_a, tree_b),
        forall|n: usize| #[trigger] mappings.contains_key(n)
            ==> mapping_node_kept(list_a, tables_a, blocks_a, holders_a, list_b, tables_b, blocks_b, holders_b, mappings[n].frame, n),
    ensures
        mappings_wf(list_b, tables_b, tree_b, blocks_b, holders_b, mappings),
{
    assert forall|n: usize| #[trigger] mappings.contains_key(n)
        implies mapping_wf(list_b, tables_b, tree_b, blocks_b, holders_b, mappings, n) by {
        let m = mappings[n];
        assert(mapping_wf(list_a, tables_a, tree_a, blocks_a, holders_a, mappings, n));
        assert(mapping_node_kept(list_a, tables_a, blocks_a, holders_a, list_b, tables_b, blocks_b, holders_b, m.frame, n));
        assert(frame_slot(tree_a, m.table, m.entry));
        assert(frame_slot(tree_b, m.table, m.entry));
        assert(tree_b.record(m.table).level == tree_a.record(m.table).level);
        assert(tree_b.entry(m.table, m.entry) == tree_a.entry(m.table, m.entry));
        assert(list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Mapping);
        assert(list_b.nodes@[n as int].live && list_b.nodes@[n as int].kind is Mapping);
    }
    assert forall|n: usize| n < NODE_SPACE && (#[trigger] list_b.nodes@[n as int]).live && list_b.nodes@[n as int].kind is Mapping
        implies mappings.contains_key(n) by {
        assert(list_a.nodes@[n as int].live && list_a.nodes@[n as int].kind is Mapping);
    }
    assert forall|t: usize, e: usize| #[trigger] frame_slot(tree_b, t, e) implies {
        &&& mappings.contains_key(mapping_node(t, e))
        &&& mappings[mapping_node(t, e)].table == t
        &&& mappings[mapping_node(t, e)].entry == e
    } by {
        assert(frame_slot(tree_a, t, e));
    }
}

impl CapKernel {
    /// Mapping node n is listed below its parent, a frame capability, and its frame's block has
    /// references, since it holds n.
    pub proof fn lemma_mapping_node(&self, n: usize)
        requires
            self.wf(),
            self.mappings@.contains_key(n),
        ensures
            n < NODE_SPACE,
            self.list.valid(n),
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Mapping,
            self.list.parent@.contains_key(n),
            self.is_cap(self.list.parent@[n]),
            self.payload_of(self.list.parent@[n]).kind is Frame,
            self.list.is_child(self.list.parent@[n], n),
            self.blocks.tracks(self.mappings@[n].frame as int),
            self.holders@.contains_key(block_ref(&self.blocks, self.mappings@[n].frame)),
            self.holders@[block_ref(&self.blocks, self.mappings@[n].frame)].contains(n),
            block_typed(&self.blocks, block_ref(&self.blocks, self.mappings@[n].frame)),
            block_refs(&self.blocks, block_ref(&self.blocks, self.mappings@[n].frame)) > 0,
    {
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(has(self.list.seq@, n));
        lemma_has(self.list.seq@, n);
        assert(n != self.list.seq@[0]);
        let br = block_ref(&self.blocks, self.mappings@[n].frame);
        if self.holders@[br].len() == 0 {
            self.holders@[br].lemma_len0_is_empty();
        }
    }

    /// A childless live node is no mapping's parent.
    pub proof fn lemma_childless_no_mapping(&self, x: usize)
        requires
            self.wf(),
            x < NODE_SPACE,
            self.list.nodes@[x as int].live,
            self.list.childless(x),
        ensures
            forall|n: usize| #[trigger] self.mappings@.contains_key(n) ==> self.list.parent@[n] != x,
    {
        let s = self.list.seq@;
        assert(has(s, x));
        lemma_has(s, x);
        let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
        self.list.lemma_link(j);
        if j + 1 < s.len() {
            self.list.lemma_link(j + 1);
            assert(s[j + 1] != NONE);
        }
        self.list.lemma_no_child(x, j);
        assert forall|n: usize| #[trigger] self.mappings@.contains_key(n) implies self.list.parent@[n] != x by {
            self.lemma_mapping_node(n);
            assert(!self.list.is_child(x, n));
        }
    }

    /// Each mapping's parent is still a capability saying the same after a step that changed only nodes
    /// x and y, neither any mapping's parent, and no parent link.
    pub proof fn lemma_mapping_parents_kept(pre: Self, post: Self, x: usize, y: usize)
        requires
            Self::caps_frame(pre, post, x, y),
            post.list.parent@ == pre.list.parent@,
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n) ==> pre.list.parent@[n] != x && pre.list.parent@[n] != y,
        ensures
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n) ==> {
                &&& post.list.parent@.contains_key(n)
                &&& post.is_cap(post.list.parent@[n])
                &&& post.payload_of(post.list.parent@[n]) == pre.payload_of(pre.list.parent@[n])
            },
    {
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies {
            &&& post.list.parent@.contains_key(n)
            &&& post.is_cap(post.list.parent@[n])
            &&& post.payload_of(post.list.parent@[n]) == pre.payload_of(pre.list.parent@[n])
        } by {
            pre.lemma_mapping_node(n);
            Self::lemma_caps_frame(pre, post, x, y, pre.list.parent@[n]);
        }
    }

    /// The mappings after a step that touched no table and no mapping node, given what it did to each
    /// mapping node's parent, frame block and holders.
    pub proof fn lemma_mappings_same_tree(pre: Self, post: Self)
        requires
            pre.wf(),
            Self::same_tree(pre, post),
            post.mappings == pre.mappings,
            same_mapping_nodes(&pre.list, &post.list),
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n) ==> mapping_node_kept(
                &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
            ),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(same_frame_entries(a, b));
        lemma_mappings_kept(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, &post.list, &post.tables, b, &post.blocks, post.holders@, pre.mappings@);
    }

    /// The mappings after a step that added list pages and nodes, none a mapping, kept every mapping
    /// node's parent link, every capability and the holders, typed a free small block, and added no
    /// present entry at level 1.
    pub proof fn lemma_mappings_grown(pre: Self, post: Self, page: usize, order: usize)
        requires
            pre.wf(),
            post.mappings == pre.mappings,
            post.holders == pre.holders,
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
            same_mapping_nodes(&pre.list, &post.list),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
                ==> post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n],
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.is_cap(x) && post.payload_of(x) == pre.payload_of(x),
            small_order(order),
            page % (order_pages(order) as usize) == 0,
            pre.blocks.tracks_run(page as int, order_pages(order)),
            forall|k: int| 0 <= k < order_pages(order) ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            !pre.blocks.covered(page as int),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(order))
                ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
        ) by {
            pre.lemma_mapping_node(n);
            lemma_block_ref_small_typed(&pre.blocks, &post.blocks, page, order, pre.mappings@[n].frame);
        }
        lemma_mappings_kept(
            &pre.list, &pre.tables, tree_of(&pre.table_pages, &pre.spaces), &pre.blocks, pre.holders@,
            &post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, pre.mappings@,
        );
    }

    /// Mapping node n lies in a node page of its table's block: the block's base page or a member of it,
    /// so in no leaf's block.
    pub proof fn lemma_mapping_node_page(&self, n: usize)
        requires
            self.wf(),
            self.mappings@.contains_key(n),
        ensures
            self.blocks.tracks_addr(page_of(n)),
            !leaf_block(&self.blocks, page_of(n) / PAGE_SZ),
    {
        let m = self.mappings@[n];
        let t = m.table;
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        let q = t / PAGE_SZ;
        self.blocks.lemma_base(q as int);
        assert(order_pages(3) == 8);
        lemma_mapping_node_place(t, m.entry);
        let k = ((m.entry + 1) / (NODES_PER_PAGE as int)) as usize;
        assert(page_of(n) / PAGE_SZ == q + k);
        if k > 0 {
            self.blocks.lemma_member_of(q as int, q + k);
        }
    }
}

/// Where a mapping node lies: in node page (e + 1) / 128 of its table's block, at slot (e + 1) % 128.
pub proof fn lemma_mapping_node_place(t: usize, e: usize)
    requires
        t % TABLE_PAGE_BYTES == 0,
        t / PAGE_SZ + TABLE_NODE_PAGES <= NUM_PAGES,
        e < ENTRIES,
    ensures
        (e + 1) / (NODES_PER_PAGE as int) < TABLE_NODE_PAGES,
        mapping_node(t, e) == t + ((e + 1) / (NODES_PER_PAGE as int)) * PAGE_SZ + (e + 1) % (NODES_PER_PAGE as int),
        mapping_node(t, e) / PAGE_SZ == t / PAGE_SZ + (e + 1) / (NODES_PER_PAGE as int),
        mapping_node(t, e) % PAGE_SZ == (e + 1) % (NODES_PER_PAGE as int),
        page_of(mapping_node(t, e)) == table_node_page(t, ((e + 1) / (NODES_PER_PAGE as int)) as usize),
{
    let k = ((e + 1) / (NODES_PER_PAGE as int)) as usize;
    let s = (e + 1) % (NODES_PER_PAGE as int);
    lemma_table_page_aligned(t);
    let q = t / PAGE_SZ;
    assert(k < TABLE_NODE_PAGES);
    assert(s < NODES_PER_PAGE);
    let n = mapping_node(t, e);
    assert(n == PAGE_SZ * (q + k) + s);
    lemma_fundamental_div_mod_converse(n as int, (PAGE_SZ as int), q + k, s as int);
    assert(page_of(n) == n - s);
    lemma_table_node_page(t, k);
}

/// A table added with no present entry keeps the frame mappings: every table of a is as it was.
pub proof fn lemma_frame_entries_extended(a: TableTree, b: TableTree)
    requires
        tree_extended(a, b),
        forall|u: usize| #[trigger] b.is_page(u) && !a.is_page(u)
            ==> forall|i: usize| i < ENTRIES ==> !(#[trigger] b.entry(u, i)).perm.present,
    ensures
        same_frame_entries(a, b),
{
    assert forall|t: usize, e: usize| #[trigger] frame_slot(a, t, e) implies {
        &&& frame_slot(b, t, e)
        &&& b.record(t).level == a.record(t).level
        &&& b.entry(t, e) == a.entry(t, e)
    } by {
        assert(a.is_table(t));
    }
    assert forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) implies frame_slot(a, t, e) by {
        if a.is_page(t) {
            assert(a.is_table(t));
        } else {
            assert(!b.entry(t, e).perm.present);
        }
    }
}

/// A link keeps the frame mappings: it writes an empty entry, which was no mapping, and what it writes
/// names a child, so is none.
pub proof fn lemma_frame_entries_linked(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, s: usize)
    requires
        linked(a, b, parent, entry, child, s),
        a.is_table(parent),
        a.record(parent).level >= 2,
        a.entry(parent, entry).is_empty(),
    ensures
        same_frame_entries(a, b),
{
    assert forall|t: usize, e: usize| #[trigger] frame_slot(a, t, e) implies {
        &&& frame_slot(b, t, e)
        &&& b.record(t).level == a.record(t).level
        &&& b.entry(t, e) == a.entry(t, e)
    } by {
        assert(b.maps.dom() == a.maps.dom());
        assert(b.is_page(t));
        assert(a.is_table(t));
        assert(b.record(t).level == a.record(t).level);
        assert(!(t == parent && e == entry));
        assert(b.entry(t, e) == a.entry(t, e));
    }
    assert forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) implies frame_slot(a, t, e) by {
        assert(b.maps.dom() == a.maps.dom());
        assert(a.is_page(t));
        assert(a.is_table(t));
        assert(b.record(t).level == a.record(t).level);
        if t == parent && e == entry {
            assert(b.entry(parent, entry) == child_entry(child));
            assert(!b.entry(t, e).perm.ps);
            assert(a.record(parent).level >= 2);
        } else {
            assert(b.entry(t, e) == a.entry(t, e));
        }
    }
}

/// The mapping nodes after pages are added and nodes x and y, neither a mapping, are made: every other
/// node is as it was.
pub proof fn lemma_mapping_nodes_grown(a: Tree, mid: Tree, b: Tree, x: usize, y: usize)
    requires
        a.wf(),
        list_grown(a, mid),
        forall|i: int| #![trigger b.nodes@[i]] 0 <= i < NODE_SPACE && i != x && i != y ==> {
            &&& b.nodes@[i].live == mid.nodes@[i].live
            &&& b.nodes@[i].kind == mid.nodes@[i].kind
        },
        x < NODE_SPACE,
        y < NODE_SPACE,
        !a.nodes@[x as int].live,
        !a.nodes@[y as int].live,
        !(b.nodes@[x as int].kind is Mapping),
        !(b.nodes@[y as int].kind is Mapping),
    ensures
        same_mapping_nodes(&a, &b),
{
    assert forall|i: usize| i < NODE_SPACE implies
        (b.nodes@[i as int].live && b.nodes@[i as int].kind is Mapping) == (a.nodes@[i as int].live && a.nodes@[i as int].kind is Mapping) by {
        if i != x && i != y {
            assert(mid.nodes@[i as int].live == a.nodes@[i as int].live);
            if a.nodes@[i as int].live {
                a.lemma_live_valid(i);
                assert(mid.nodes@[i as int] == a.nodes@[i as int]);
            }
        }
    }
}

/// A root with no entry but the kernel slots maps nothing.
pub proof fn lemma_mapping_fresh(tree: TableTree, s: usize)
    requires
        forall|i: usize| i < ENTRIES && !holds_kernel(tree.space_records[s].value().kind, i) ==> #[trigger] tree.entry(s, i).is_empty(),
        tree.is_root(s),
    ensures
        space_mapping(tree, s) =~= IMap::<SpacePath, PageEntry>::empty(),
{
    assert forall|p: SpacePath| !(#[trigger] walk(tree, s, p) is Some) by {
        if tree.child_slot(s, p.l4) {
            assert(tree.entry(s, p.l4).is_empty());
        }
    }
}

/// A link leaves every walk as it was. The new entry was not present, and the child it leads to has no
/// entry, so no walk went through it before or finds anything through it now. It is above level 1, so
/// no walk ends at it.
pub proof fn lemma_walk_linked(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, s: usize, r: usize, p: SpacePath)
    requires
        linked(a, b, parent, entry, child, s),
        a.child_slot(parent, entry),
        a.entry(parent, entry).is_empty(),
        a.is_page(child),
        child != parent,
        child + TABLE_NODE_PAGES * PAGE_SZ <= usize::MAX,
        forall|i: usize| i < ENTRIES ==> #[trigger] a.entry(child, i).is_empty(),
    ensures
        walk(b, r, p) == walk(a, r, p),
{
    assert forall|t: usize, i: usize| !(t == parent && i == entry) implies #[trigger] step(b, t, i) == step(a, t, i) by {
        if a.is_table(t) && i < ENTRIES {
            assert(b.entry(t, i) == a.entry(t, i));
            assert(b.record(t).level == a.record(t).level);
        }
    }
    assert forall|t: usize, i: usize| true implies #[trigger] frame_entry(b, t, i) == frame_entry(a, t, i) by {
        if a.is_table(t) && i < ENTRIES {
            assert(b.record(t).level == a.record(t).level);
            if !(t == parent && i == entry) {
                assert(b.entry(t, i) == a.entry(t, i));
            }
        }
    }
    assert forall|t: usize, i: usize| true implies #[trigger] large_entry(b, t, i) == large_entry(a, t, i) by {
        if a.is_table(t) && i < ENTRIES {
            assert(b.record(t).level == a.record(t).level);
            if t == parent && i == entry {
                assert(b.entry(parent, entry) == child_entry(child));
                assert(!b.entry(parent, entry).perm.ps);
                assert(!a.entry(parent, entry).perm.present);
            } else {
                assert(b.entry(t, i) == a.entry(t, i));
            }
        }
    }
    assert(step(a, parent, entry) is None);
    assert forall|i: usize| i < ENTRIES implies step(b, child, i) is None && frame_entry(b, child, i) is None && large_entry(b, child, i) is None by {
        assert(b.entry(child, i) == a.entry(child, i));
        assert(a.entry(child, i).is_empty());
    }
    assert forall|i: usize| i >= ENTRIES implies step(b, child, i) is None && frame_entry(b, child, i) is None && large_entry(b, child, i) is None by {}
    assert(b.entry(parent, entry).addr == table_addr(child));
    assert(step(b, parent, entry) == Some(child));
}

/// So a link leaves every space's mapping as it was.
pub proof fn lemma_mapping_linked(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, s: usize, r: usize)
    requires
        linked(a, b, parent, entry, child, s),
        a.child_slot(parent, entry),
        a.entry(parent, entry).is_empty(),
        a.is_page(child),
        child != parent,
        child + TABLE_NODE_PAGES * PAGE_SZ <= usize::MAX,
        forall|i: usize| i < ENTRIES ==> #[trigger] a.entry(child, i).is_empty(),
    ensures
        space_mapping(b, r) =~= space_mapping(a, r),
{
    assert forall|p: SpacePath| #[trigger] walk(b, r, p) == walk(a, r, p) by {
        lemma_walk_linked(a, b, parent, entry, child, s, r, p);
    }
}

/// Every table of a is in b as it was, and b has others.
pub open spec fn tree_extended(a: TableTree, b: TableTree) -> bool {
    forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) ==> {
        &&& b.is_page(t) == a.is_page(t)
        &&& b.is_root(t) == a.is_root(t)
        &&& b.record(t) == a.record(t)
        &&& a.is_root(t) ==> b.space_records[t].value().kind == a.space_records[t].value().kind
        &&& forall|i: usize| i < ENTRIES ==> #[trigger] b.entry(t, i) == a.entry(t, i)
    }
}

/// A new table is on no walk: an existing table's present entry names a table that already exists.
pub proof fn lemma_mapping_extended(a: TableTree, b: TableTree, s: usize)
    requires
        table_links_wf(a),
        tree_extended(a, b),
        a.is_root(s),
    ensures
        space_mapping(b, s) =~= space_mapping(a, s),
{
    assert forall|t: usize, i: usize| #![trigger step(a, t, i)] a.is_table(t) && i < ENTRIES implies step(b, t, i) == step(a, t, i)
        && frame_entry(b, t, i) == frame_entry(a, t, i) && (step(a, t, i) is Some ==> a.is_table(step(a, t, i)->0)) by {
        assert(b.entry(t, i) == a.entry(t, i));
        if a.child_slot(t, i) && a.entry(t, i).perm.present {
            assert(table_links_wf(a));
            let _ = a.entry(t, i);
        }
    }
    assert forall|p: SpacePath| #[trigger] walk(b, s, p) == walk(a, s, p) by {
        assert(a.is_table(s));
        if p.l4 < ENTRIES {
            if let Some(t3) = step(a, s, p.l4) {
                assert(a.is_table(t3));
                if p.l3 < ENTRIES {
                    if let Some(t2) = step(a, t3, p.l3) {
                        assert(a.is_table(t2));
                        if p.l2 < ENTRIES {
                            if let Some(t1) = step(a, t2, p.l2) {
                                assert(a.is_table(t1));
                                if p.l1 >= ENTRIES {
                                    assert(frame_entry(b, t1, p.l1) is None);
                                    assert(frame_entry(a, t1, p.l1) is None);
                                }
                            }
                        } else {
                            assert(step(b, t2, p.l2) is None);
                            assert(step(a, t2, p.l2) is None);
                        }
                    }
                } else {
                    assert(step(b, t3, p.l3) is None);
                    assert(step(a, t3, p.l3) is None);
                }
            }
        } else {
            assert(step(b, s, p.l4) is None);
            assert(step(a, s, p.l4) is None);
        }
    }
}

impl CapKernel {
    /// The word w, read from mapping node n's entry as it was cleared, decodes to the entry the node's
    /// mapping held; its accessed and dirty bits are the processor's as they stood then.
    pub open spec fn mapping_word(pre: Self, n: usize, w: usize) -> bool {
        let m = pre.mappings@[n];
        crate::arch::spec_usize2page_entry(w, pre.table_pages.maps@[m.table].value().level@) == tree_of(&pre.table_pages, &pre.spaces).entry(m.table, m.entry)
    }

    /// Undoes mapping node n: its entry and its reference go in one step, and nothing else. The node's
    /// own page says where its entry is. Returns the entry's word as read in the step that cleared it.
    pub fn clear_mapping(&mut self, n: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            old(self).list.nodes@[n as int].kind is Mapping,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(steps).count <= old(steps).count + MAPPING_NOTE_STEPS,
            Self::mapping_unlinked(*old(self), *final(self), n),
            Self::mapping_stale_noted(*old(self), *final(self), n),
            Self::mapping_word(*old(self), n, ret),
            final(self).stale_epoch.wf(),
            final(self).tlb_wf(),
            mapped_wf(final(self).mapped@, final(self).mappings@),
            final(self).tables == old(self).tables,
            final(self).blocks.wf(),
            final(self).list == old(self).list,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).spaces == old(self).spaces,
            final(self).devices == old(self).devices,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).table_pages.records == old(self).table_pages.records,
            final(self).table_pages.spare == old(self).table_pages.spare,
    {
        let ghost pre = *old(self);
        let ghost m = pre.mappings@[n];
        proof {
            pre.lemma_mapping_node_located(n);
            pre.lemma_mapping_node(n);
        }
        let page = n / PAGE_SZ;
        let block = *self.blocks.pages.get(page);
        let base = match block.kind {
            crate::capability::block::PageKind::Member => block.base,
            _ => page,
        };
        let t = base * PAGE_SZ;
        let e = (page - base) * NODES_PER_PAGE + n % PAGE_SZ - 1;
        proof {
            assert(t == m.table);
            assert(e == m.entry);
        }
        let level = PPtr::<TableRecord>::from_usize(t + TABLE_RECORD_PAGE * PAGE_SZ)
            .borrow(Tracked(self.table_pages.records.borrow().tracked_borrow(t)))
            .level;
        let entry = PPtr::<PageMap>::from_usize(t + TABLE_NODE_PAGES * PAGE_SZ)
            .borrow(Tracked(self.table_pages.maps.borrow().tracked_borrow(t)))
            .get(e, level);
        proof {
            assert(entry =~= tree_of(&pre.table_pages, &pre.spaces).entry(m.table, m.entry));
            assert(mapping_wf(&pre.list, &pre.tables, tree_of(&pre.table_pages, &pre.spaces), &pre.blocks, pre.holders@, pre.mappings@, n));
        }
        let frame = entry.addr / PAGE_SZ;
        let large = entry.perm.ps;
        self.note_mapping_stale(n, frame, large, Tracked(steps));
        let ghost noted = *self;
        let br = locate(&self.blocks, frame);
        let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(t);
        let word = page_map_clear_take(t + TABLE_NODE_PAGES * PAGE_SZ, Tracked(&mut map), e);
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(t, map);
        }
        drop_block_ref(&mut self.blocks, br);
        self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].remove(n)));
        self.mappings = Ghost(pre.mappings@.remove(n));
        proof {
            assert(self.table_pages.maps@ =~= pre.table_pages.maps@.insert(m.table, map));
            assert forall|i: usize| #![trigger self.table_pages.maps@[m.table].value()[i]] i < ENTRIES && i != m.entry
                implies self.table_pages.maps@[m.table].value()[i] == pre.table_pages.maps@[m.table].value()[i] by {
                assert(map.value()[i] =~= pre.table_pages.maps@[m.table].value()[i]);
            }
            Self::lemma_tlb_same(noted, *self);
            Self::lemma_stale_noted_same(pre, noted, *self, n);
            lemma_mapped_removed(pre.mapped@, self.mapped@, pre.mappings@, n);
            Self::lemma_clear_mapping_post(pre, *self, n);
            assert(pre.table_pages.maps@[t].value()@[e as int] == entry);
        }
        word
    }

    /// What recorded node n's unmap stays true while nothing the record names changes.
    pub proof fn lemma_stale_noted_same(pre: Self, mid: Self, post: Self, n: usize)
        requires
            pre.wf(),
            Self::mapping_stale_noted(pre, mid, n),
            post.cores == pre.cores,
            mid.cores == pre.cores,
            post.flush_epoch == mid.flush_epoch,
            post.tlb == mid.tlb,
            post.iommus == mid.iommus,
            post.mapped == mid.mapped,
            post.stale_epoch == mid.stale_epoch,
        ensures
            Self::mapping_stale_noted(pre, post, n),
    {
        let pages = record_pages(pre.mappings@[n]);
        assert forall|g: usize| #[trigger] pages.contains(g) implies !post.acknowledged(g) by {
            assert(pre.acked(0) <= pre.flush_epoch);
            assert(post.acked(0) == pre.acked(0));
        }
    }

    /// A mapped page lies in a block a mapping holds a reference on, the block of the frame it maps.
    pub proof fn lemma_mapped_block(&self, g: usize) -> (br: BlockRef)
        requires
            self.wf(),
            self.mapped@.contains(g),
        ensures
            self.holders@.contains_key(br),
            block_typed(&self.blocks, br),
            block_has_page(br, g),
            block_refs(&self.blocks, br) > 0,
    {
        let n = choose|n: usize| #![trigger self.mappings@[n]] self.mappings@.contains_key(n) && record_pages(self.mappings@[n]).contains(g);
        let m = self.mappings@[n];
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        let c = self.list.parent@[n];
        let p = self.tables.payload_of(c);
        lemma_holder_refs(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@, c);
        let i = p.base / PAGE_SZ;
        assert(frame_in_block(block_ref(&self.blocks, i), p));
        lemma_map_pages(m.frame, m.large);
        assert(m.frame <= g < m.frame + entry_pages(tree.record(m.table).level));
        lemma_mapped_page_in_block(&self.blocks, i, p, m.frame, entry_pages(tree.record(m.table).level), g);
        let br = block_ref(&self.blocks, m.frame);
        assert(self.holders@[br].contains(n));
        if self.holders@[br].len() == 0 {
            self.holders@[br].lemma_len0_is_empty();
        }
        br
    }

    /// Records node n's unmap, while its entry still stands: the epoch is bumped first, so no core has
    /// acknowledged this one however recently it flushed. A large mapping's 512 pages take one epoch.
    fn note_mapping_stale(&mut self, n: usize, frame: usize, large: bool, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).mappings@.contains_key(n),
            old(self).mappings@[n].frame == frame,
            old(self).mappings@[n].large == large,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(steps).count <= old(steps).count + MAPPING_NOTE_STEPS,
            final(self).stale_epoch.wf(),
            final(self).tlb_wf(),
            Self::mapping_stale_noted(*old(self), *final(self), n),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).mappings == old(self).mappings,
            final(self).table_pages == old(self).table_pages,
            final(self).spaces == old(self).spaces,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).cores == old(self).cores,
            final(self).devices == old(self).devices,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        let ghost m = pre.mappings@[n];
        let ghost pages = record_pages(m);
        let ghost space = tree.record(m.table).space;
        proof {
            assert(mapping_wf(&pre.list, &pre.tables, tree, &pre.blocks, pre.holders@, pre.mappings@, n));
            assert(pre.blocks.tracks_run(frame as int, entry_pages(tree.record(m.table).level)));
        }
        let count: usize = if large { PAGES_PER_2M } else { 1 };
        self.flush_epoch = self.flush_epoch + 1;
        let epoch = self.flush_epoch;
        self.stale_epoch.record_run(frame, count, epoch, Tracked(steps));
        proof {
            self.tlb.borrow_mut().grow(Seq::new(NUM_CPUS as nat, |d: int|
                if space is Some && pre.depends(d, space->Some_0) {
                    pre.tlb@[d].union(stale_entries(space->Some_0, pages))
                } else {
                    pre.tlb@[d]
                }));
        }
        proof {
            self.iommus.tlb.borrow_mut().grow(Seq::new(NUM_IOMMUS as nat, |i: int|
                if pre.iommu_present(i) && space is Some && pre.spaces.records@[space->Some_0].value().kind is Device {
                    pre.iommus.tlb@[i].union(stale_entries(space->Some_0, pages))
                } else {
                    pre.iommus.tlb@[i]
                }));
        }
        self.mapped = Ghost(pre.mapped@.filter(|g: usize| !pages.contains(g) || page_named(pre.mappings@.remove(n), g)));
        proof {
            broadcast use vstd::set::lemma_set_filter;
            lemma_map_pages(frame, large);
            if space is Some {
                lemma_stale_entries(space->Some_0, pages);
            }
            assert forall|g: usize| #[trigger] pages.contains(g) implies self.stale_epoch.written(self.flush_epoch, g) by {
                assert(frame <= g < frame + count);
            }
            assert(self.tlb@.len() == NUM_CPUS);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|g: usize| #[trigger] pages.contains(g) implies !self.acknowledged(g) by {
                assert(pre.acked(0) <= pre.flush_epoch);
                assert(self.acked(0) == pre.acked(0));
            }
            assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(e) implies self.depends(d, e.space) by {
                assert(pre.depends(d, e.space));
            }
            assert forall|d: int, e: TlbEntry|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(e) && !self.mapped@.contains(e.page)
                implies self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.acked(d), e.page) by {
                assert(pre.acked(d) <= pre.flush_epoch);
                assert(self.acked(d) == pre.acked(d));
                if pages.contains(e.page) {
                    assert(self.stale_epoch.written(self.flush_epoch, e.page));
                    assert(frame <= e.page < frame + count);
                } else {
                    assert(pre.tlb@[d].contains(e));
                    assert(!pre.mapped@.contains(e.page));
                    assert(pre.stale_epoch.above(pre.acked(d), e.page));
                    assert(pre.acked(d) < epoch);
                }
            }
            assert(self.iommus.tlb@.len() == NUM_IOMMUS);
            assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) implies self.iommu_present(i) by {
                if !pre.iommu_present(i) {
                    assert(self.iommus.tlb@[i] == pre.iommus.tlb@[i]);
                    assert(pre.iommus.tlb@[i].contains(e));
                }
            }
            assert forall|i: int| 0 <= i < NUM_IOMMUS implies #[trigger] self.iommu_acked(i) <= self.flush_epoch by {
                assert(pre.iommu_acked(i) <= pre.flush_epoch);
            }
            assert forall|i: int, e: TlbEntry|
                0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) && !self.mapped@.contains(e.page)
                implies self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.iommu_acked(i), e.page) by {
                assert(pre.iommu_acked(i) <= pre.flush_epoch);
                assert(self.iommu_acked(i) == pre.iommu_acked(i));
                if pages.contains(e.page) {
                    assert(self.stale_epoch.written(self.flush_epoch, e.page));
                    assert(frame <= e.page < frame + count);
                } else {
                    assert(pre.iommus.tlb@[i].contains(e));
                    assert(!pre.mapped@.contains(e.page));
                    assert(pre.stale_epoch.above(pre.iommu_acked(i), e.page));
                    assert(pre.iommu_acked(i) < epoch);
                }
            }
            assert(self.tlb_wf());
            assert forall|d: int, g: usize| #![trigger self.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g })]
                0 <= d < NUM_CPUS && space is Some && pre.depends(d, space->Some_0) && pages.contains(g)
                implies self.tlb@[d].contains(TlbEntry { space: space->Some_0, page: g }) by {
            }
            assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] pre.tlb@[d].contains(e) implies self.tlb@[d].contains(e) by {
            }
            assert forall|i: int, g: usize| #![trigger self.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g })]
                0 <= i < NUM_IOMMUS && pre.iommu_present(i) && space is Some && pre.spaces.records@[space->Some_0].value().kind is Device && pages.contains(g)
                implies self.iommus.tlb@[i].contains(TlbEntry { space: space->Some_0, page: g }) by {
            }
            assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] pre.iommus.tlb@[i].contains(e) implies self.iommus.tlb@[i].contains(e) by {
            }
        }
    }

    /// Where mapping node n's entry is, read from n alone: its table t is the block based at page t / 4096,
    /// n lies in node page (e + 1) / 128 of that block at slot (e + 1) % 128, and the entry it stands for
    /// names its frame.
    pub proof fn lemma_mapping_node_located(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Mapping,
        ensures
            self.mappings@.contains_key(n),
            ({
                let m = self.mappings@[n];
                let q = m.table / PAGE_SZ;
                let k = ((m.entry + 1) / (NODES_PER_PAGE as int)) as usize;
                let tree = tree_of(&self.table_pages, &self.spaces);
                &&& n / PAGE_SZ == q + k
                &&& self.blocks.tracks_addr(n)
                &&& k == 0 ==> self.blocks.pages@[(n / PAGE_SZ) as int].kind is Base
                &&& k > 0 ==> self.blocks.pages@[(n / PAGE_SZ) as int].kind is Member && self.blocks.pages@[(n / PAGE_SZ) as int].base == q
                &&& q * PAGE_SZ == m.table
                &&& m.table + TABLE_NODE_PAGES * PAGE_SZ <= usize::MAX
                &&& (n / PAGE_SZ - q) * NODES_PER_PAGE + n % PAGE_SZ - 1 == m.entry
                &&& m.entry < ENTRIES
                &&& self.table_pages.maps@.contains_key(m.table)
                &&& self.table_pages.maps@[m.table].addr() == m.table + TABLE_NODE_PAGES * PAGE_SZ
                &&& self.table_pages.maps@[m.table].is_init()
                &&& self.table_pages.maps@[m.table].value().wf()
                &&& tree.entry(m.table, m.entry).addr == m.frame * PAGE_SZ
                &&& tree.entry(m.table, m.entry).addr / PAGE_SZ == m.frame
                &&& self.blocks.tracks(m.frame as int)
            }),
    {
        let m = self.mappings@[n];
        let t = m.table;
        let q = t / PAGE_SZ;
        let k = ((m.entry + 1) / (NODES_PER_PAGE as int)) as usize;
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        self.blocks.lemma_base(q as int);
        assert(order_pages(3) == 8);
        lemma_mapping_node_place(t, m.entry);
        lemma_table_page_base(t, q);
        assert(n / PAGE_SZ == q + k);
        if k > 0 {
            self.blocks.lemma_member_of(q as int, q + k);
        }
        lemma_fundamental_div_mod((m.entry + 1) as int, NODES_PER_PAGE as int);
        assert((n / PAGE_SZ - q) * NODES_PER_PAGE + n % PAGE_SZ - 1 == m.entry);
        lemma_div_multiples_vanish(m.frame as int, (PAGE_SZ as int));
    }

    /// Emptying mapping node n's entry, with its reference dropped and its record and holding removed,
    /// is the unlinking of n.
    proof fn lemma_clear_mapping_post(pre: Self, post: Self, n: usize)
        requires
            pre.wf(),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Mapping,
            post.spaces == pre.spaces,
            post.table_pages.records == pre.table_pages.records,
            ({
                let m = pre.mappings@[n];
                let br = block_ref(&pre.blocks, m.frame);
                &&& post.table_pages.maps@ == pre.table_pages.maps@.insert(m.table, post.table_pages.maps@[m.table])
                &&& post.table_pages.maps@[m.table].addr() == pre.table_pages.maps@[m.table].addr()
                &&& post.table_pages.maps@[m.table].is_init()
                &&& post.table_pages.maps@[m.table].value().wf()
                &&& post.table_pages.maps@[m.table].value().level == pre.table_pages.maps@[m.table].value().level
                &&& forall|i: usize| #![trigger post.table_pages.maps@[m.table].value()[i]] i < ENTRIES && i != m.entry
                    ==> post.table_pages.maps@[m.table].value()[i] == pre.table_pages.maps@[m.table].value()[i]
                &&& post.table_pages.maps@[m.table].value()[m.entry].is_empty()
                &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) - 1) as usize, block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1)
                &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].remove(n))
                &&& post.mappings@ == pre.mappings@.remove(n)
            }),
        ensures
            Self::mapping_unlinked(pre, post, n),
    {
        let m = pre.mappings@[n];
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(pre.mappings@.contains_key(n));
        pre.lemma_mapping_node(n);
        assert(mapping_wf(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, pre.mappings@, n));
        assert(b.is_page(m.table));
        assert(b.maps.dom() =~= a.maps.dom());
        assert(b.entry(m.table, m.entry).is_empty());
        assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
            i < ENTRIES && !(u == m.table && i == m.entry) implies b.entry(u, i) == a.entry(u, i) by {
            assert(b.is_page(u) == a.is_page(u));
            if u != m.table && a.is_page(u) {
                assert(post.table_pages.maps@[u] == pre.table_pages.maps@[u]);
            }
        }
        assert(entries_cleared(a, b, m.table, m.entry)) by {
            reveal(entries_cleared);
        }
        assert forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p)
            == (if ends_at(a, r, p, m.table, m.entry) { None } else { walk(a, r, p) }) by {
            lemma_walk_entry_cleared(a, b, m.table, m.entry, r, p);
        }
        assert(walks_cut(a, b, m.table, m.entry)) by {
            reveal(walks_cut);
        }
    }
}

/// Clearing frame mapping e of table t ends the walks that reached it and no other: a step reads only
/// entries that name a child, and a frame entry is read only by the walk that ends at it.
pub proof fn lemma_walk_entry_cleared(a: TableTree, b: TableTree, t: usize, e: usize, r: usize, p: SpacePath)
    requires
        b.maps.dom() == a.maps.dom(),
        b.roots == a.roots,
        b.records == a.records,
        b.space_records == a.space_records,
        frame_slot(a, t, e),
        !b.entry(t, e).perm.present,
        forall|u: usize, i: usize| #![trigger b.entry(u, i)] i < ENTRIES && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i),
    ensures
        walk(b, r, p) == (if ends_at(a, r, p, t, e) { None } else { walk(a, r, p) }),
{
    assert(!a.names_child(t, e));
    assert(!b.names_child(t, e));
    assert forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i) by {
        assert(b.child_slot(u, i) == a.child_slot(u, i));
        if a.child_slot(u, i) && !(u == t && i == e) {
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert forall|u: usize, i: usize| !(u == t && i == e) implies #[trigger] frame_entry(b, u, i) == frame_entry(a, u, i)
        && large_entry(b, u, i) == large_entry(a, u, i) by {
        if a.is_table(u) && i < ENTRIES {
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert(frame_entry(b, t, e) is None);
    assert(large_entry(b, t, e) is None);
    if a.is_root(r) {
        if let Some(t3) = step(a, r, p.l4) {
            if let Some(t2) = step(a, t3, p.l3) {
                if let Some(t1) = step(a, t2, p.l2) {
                    if t1 == t && p.l1 == e {
                        assert(ends_at(a, r, p, t, e));
                    } else {
                        if t2 == t && p.l2 == e {
                            assert(step(a, t, e) is None);
                        }
                        assert(!ends_at(a, r, p, t, e));
                        assert(frame_entry(b, t1, p.l1) == frame_entry(a, t1, p.l1));
                    }
                } else {
                    if t2 == t && p.l2 == e {
                        if p.l1 == 0 && large_entry(a, t, e) is Some {
                            assert(ends_at(a, r, p, t, e));
                        } else {
                            assert(!ends_at(a, r, p, t, e));
                        }
                    } else {
                        assert(!ends_at(a, r, p, t, e));
                        assert(large_entry(b, t2, p.l2) == large_entry(a, t2, p.l2));
                    }
                }
            }
        }
    }
}

/// The table pages after entry e of table page t is emptied: the page keeps its address, its record
/// and its other entries, and a record not written had no entry to lose.
pub proof fn lemma_table_pages_entry_cleared(list: &Tree, pa: &TablePages, pb: &TablePages, blocks: &BlockTable, t: usize, e: usize)
    requires
        table_pages_wf(list, pa, blocks),
        pa.maps@.contains_key(t),
        e < ENTRIES,
        pb.records == pa.records,
        pb.spare == pa.spare,
        pb.maps@ == pa.maps@.insert(t, pb.maps@[t]),
        pb.maps@[t].addr() == pa.maps@[t].addr(),
        pb.maps@[t].is_init(),
        pb.maps@[t].value().wf(),
        pb.maps@[t].value().level == pa.maps@[t].value().level,
        forall|i: usize| #![trigger pb.maps@[t].value()[i]] i < ENTRIES && i != e ==> pb.maps@[t].value()[i] == pa.maps@[t].value()[i],
        pb.maps@[t].value()[e].is_empty(),
    ensures
        table_pages_wf(list, pb, blocks),
{
    assert forall|u: usize| #[trigger] pb.maps@.contains_key(u) implies table_page_wf(list, pb, blocks, u) by {
        assert(pa.maps@.contains_key(u));
        assert(table_page_wf(list, pa, blocks, u));
        if u == t {
            assert(table_record_wf(pb, t)) by {
                let record = pb.records@[t].value();
                if !record.written {
                    assert forall|i: usize| #![trigger pb.maps@[t].value()[i]] i < ENTRIES implies pb.maps@[t].value()[i].is_empty() by {
                        if i != e {
                            assert(pa.maps@[t].value()[i].is_empty());
                        }
                    }
                }
            }
        } else {
            assert(pb.maps@[u] == pa.maps@[u]);
        }
    }
}

/// The links after frame mapping e of table t is emptied: no link is through a frame mapping.
pub proof fn lemma_links_entry_cleared(a: TableTree, b: TableTree, t: usize, e: usize)
    requires
        table_links_wf(a),
        b.maps.dom() == a.maps.dom(),
        b.roots == a.roots,
        b.records == a.records,
        b.space_records == a.space_records,
        frame_slot(a, t, e),
        !b.entry(t, e).perm.present,
        forall|u: usize, i: usize| #![trigger b.entry(u, i)] i < ENTRIES && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i),
    ensures
        table_links_wf(b),
{
    assert(!a.names_child(t, e));
    assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        b.names_child(u, i) implies {
        let c = (b.entry(u, i).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize;
        &&& b.is_page(c)
        &&& b.record(c).parent == Some(TableParent { table: u, entry: i })
    } by {
        assert(!(u == t && i == e));
        assert(b.entry(u, i) == a.entry(u, i));
        assert(a.names_child(u, i));
        let _ = a.entry(u, i);
    }
    assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        b.child_slot(u, i) && b.entry(u, i).perm.present && b.entry(u, i).perm.ps implies b.record(u).level == 2 by {
        assert(!(u == t && i == e));
        assert(b.entry(u, i) == a.entry(u, i));
        assert(a.child_slot(u, i));
        let _ = a.entry(u, i);
    }
    assert forall|c: usize| #![trigger b.maps.contains_key(c)] b.is_page(c) implies {
        let r = b.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& b.names_child(p.table, p.entry)
            &&& b.entry(p.table, p.entry).addr == table_addr(c)
            &&& b.record(p.table).level == r.level + 1
            &&& b.record(p.table).space == r.space
        }
    } by {
        assert(a.is_page(c));
        assert(a.maps.contains_key(c));
        let r = a.record(c);
        if r.parent is Some {
            let p = r.parent->0;
            assert(a.names_child(p.table, p.entry));
            assert(!(p.table == t && p.entry == e));
            assert(b.entry(p.table, p.entry) == a.entry(p.table, p.entry));
        }
    }
}

impl CapKernel {
    /// A table page's block: eight aligned tracked pages, the first its base, the rest members.
    pub proof fn lemma_table_page_room(&self, t: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
        ensures
            table_page_wf(&self.list, &self.table_pages, &self.blocks, t),
            t % TABLE_PAGE_BYTES == 0,
            t % PAGE_SZ == 0,
            self.blocks.tracks_addr_run(t, 8),
            t < NUM_PAGES * PAGE_SZ,
            self.blocks.pages@[(t / PAGE_SZ) as int].kind is Base,
            self.blocks.pages@[(t / PAGE_SZ) as int].object is TablePage,
            forall|k: int| 0 < k < 8 ==> (#[trigger] self.blocks.pages@[t / PAGE_SZ + k]).kind is Member
                && self.blocks.pages@[t / PAGE_SZ + k].base == t / PAGE_SZ,
    {
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        lemma_table_page_aligned(t);
        let q = (t / PAGE_SZ) as int;
        self.blocks.lemma_base(q);
        assert(order_pages(3) == 8);
        lemma_table_bound(t);
        assert forall|k: int| 0 < k < 8 implies (#[trigger] self.blocks.pages@[t / PAGE_SZ + k]).kind is Member
            && self.blocks.pages@[t / PAGE_SZ + k].base == t / PAGE_SZ by {
            self.blocks.lemma_member_of(q, q + k);
        }
    }

    /// A live node at an entry's place in a table page's block is a mapping node.
    pub proof fn lemma_table_node_is_mapping(&self, t: usize, e: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
            e < ENTRIES,
            self.list.nodes@[mapping_node(t, e) as int].live,
        ensures
            self.list.nodes@[mapping_node(t, e) as int].kind is Mapping,
    {
        self.lemma_table_page_room(t);
        lemma_mapping_node_place(t, e);
        let k = ((e + 1) / (NODES_PER_PAGE as int)) as usize;
        let i = ((e + 1) % (NODES_PER_PAGE as int)) as usize;
        assert(table_node(t, k, i) == mapping_node(t, e));
        assert(k != 0 || i != 0);
    }

    /// Where node i of node page k of table page t lies: in a page the list holds, in the table page's
    /// block, so in no leaf's page and, unless it is node 0 of page 0, no table page.
    pub proof fn lemma_table_node_in_block(&self, t: usize, k: usize, i: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
            k < TABLE_NODE_PAGES,
            i < NODES_PER_PAGE,
        ensures
            table_node(t, k, i) < NODE_SPACE,
            table_node(t, k, i) / PAGE_SZ == t / PAGE_SZ + k,
            table_node(t, k, i) % PAGE_SZ == i,
            page_of(table_node(t, k, i)) == table_node_page(t, k),
            self.list.valid(table_node(t, k, i)),
            !self.tables.owner@.contains_key(page_of(table_node(t, k, i))),
            k != 0 || i != 0 ==> table_node(t, k, i) != t,
            k != 0 || i != 0 ==> !self.table_pages.maps@.contains_key(table_node(t, k, i)),
    {
        self.lemma_table_page_room(t);
        lemma_table_node_place(t, k, i);
        let q = t / PAGE_SZ;
        let n = table_node(t, k, i);
        assert(self.list.pages@.dom().contains(table_node_page(t, k)));
        assert(self.list.valid(n));
        if self.tables.owner@.contains_key(page_of(n)) {
            let l = page_of(n);
            assert(self.blocks.pages@[(l / PAGE_SZ) as int].kind is Base);
            assert(self.blocks.pages@[(l / PAGE_SZ) as int].object is TableLeaf);
            assert(l / PAGE_SZ == q + k);
            if k > 0 {
                assert(self.blocks.pages@[q + k].kind is Member);
            }
            assert(false);
        }
        if (k != 0 || i != 0) && self.table_pages.maps@.contains_key(n) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, n));
            lemma_table_page_aligned(n);
            assert(i == 0);
            assert(k > 0);
            assert(self.blocks.pages@[q + k].kind is Member);
            assert(false);
        }
    }

    /// The clause after a step that adds no table page and changes no node the list held but n and m,
    /// each in a leaf's page or in no page the list held: a table page's nodes are as they were.
    pub proof fn lemma_table_nodes_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            pre.wf(),
            forall|t: usize| #[trigger] post.table_pages.maps@.contains_key(t) ==> pre.table_pages.maps@.contains_key(t),
            forall|x: usize| #[trigger] pre.list.valid(x) && x != n && x != m ==> {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            },
            !pre.list.valid(n) || pre.tables.owner@.contains_key(page_of(n)),
            !pre.list.valid(m) || pre.tables.owner@.contains_key(page_of(m)),
        ensures
            table_nodes_are_mappings(&post.list, &post.table_pages),
    {
        assert forall|t: usize, k: usize, i: usize| #![trigger table_node(t, k, i)]
            post.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE && (k != 0 || i != 0)
                && post.list.nodes@[table_node(t, k, i) as int].live
            implies post.list.nodes@[table_node(t, k, i) as int].kind is Mapping by {
            let x = table_node(t, k, i);
            pre.lemma_table_node_in_block(t, k, i);
            assert(x != n);
            assert(x != m);
            assert(pre.list.nodes@[x as int].live);
        }
    }

    /// The clause after a step that changes no node but the slots n and m and keeps the table pages.
    pub proof fn lemma_table_nodes_caps_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            post.table_pages == pre.table_pages,
            pre.tables.owner@.contains_key(page_of(n)),
            pre.tables.owner@.contains_key(page_of(m)),
        ensures
            table_nodes_are_mappings(&post.list, &post.table_pages),
    {
        assert forall|x: usize| #[trigger] pre.list.valid(x) && x != n && x != m implies {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        } by {
            pre.list.lemma_valid_bound(x);
        }
        Self::lemma_table_nodes_frame(pre, post, n, m);
    }

    /// Where node i of node page k of the space at s lies: in a page the list holds, in the space's block,
    /// so in no leaf's page.
    pub proof fn lemma_space_node_in_block(&self, s: usize, k: usize, i: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
            self.spaces.records@[s].value().kind is Device,
            k < TABLE_NODE_PAGES,
            i < NODES_PER_PAGE,
        ensures
            table_node(s, k, i) < NODE_SPACE,
            page_of(table_node(s, k, i)) == table_node_page(s, k),
            self.list.valid(table_node(s, k, i)),
            !self.tables.owner@.contains_key(page_of(table_node(s, k, i))),
    {
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        let q = (s / PAGE_SZ) as int;
        self.blocks.lemma_base(q);
        assert(order_pages(3) == 8);
        lemma_table_node_place(s, k, i);
        let n = table_node(s, k, i);
        assert(self.list.pages@.dom().contains(table_node_page(s, k)));
        assert(self.list.valid(n));
        if self.tables.owner@.contains_key(page_of(n)) {
            let l = page_of(n);
            assert(self.blocks.pages@[(l / PAGE_SZ) as int].kind is Base);
            assert(self.blocks.pages@[(l / PAGE_SZ) as int].object is TableLeaf);
            assert(l / PAGE_SZ == q + k);
            if k > 0 {
                self.blocks.lemma_member_of(q, q + k);
                assert(self.blocks.pages@[q + k].kind is Member);
            }
            assert(false);
        }
    }

    /// The space clause after a step that adds no space and changes no node the list held but n and m,
    /// each in a leaf's page or in no page the list held: a space's nodes are as they were.
    pub proof fn lemma_space_nodes_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            pre.wf(),
            forall|s: usize| #[trigger] post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device
                ==> pre.spaces.roots@.contains_key(s) && post.spaces.records@[s] == pre.spaces.records@[s],
            forall|x: usize| #[trigger] pre.list.valid(x) && x != n && x != m ==> {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            },
            !pre.list.valid(n) || pre.tables.owner@.contains_key(page_of(n)),
            !pre.list.valid(m) || pre.tables.owner@.contains_key(page_of(m)),
        ensures
            space_nodes_dead(&post.list, &post.spaces),
    {
        assert forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
            post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device && k < TABLE_NODE_PAGES
                && i < NODES_PER_PAGE
            implies !post.list.nodes@[table_node(s, k, i) as int].live by {
            let x = table_node(s, k, i);
            pre.lemma_space_node_in_block(s, k, i);
            assert(x != n);
            assert(x != m);
            assert(!pre.list.nodes@[x as int].live);
        }
    }

    /// The space clause after a step that changes no node but the slots n and m and keeps the spaces.
    pub proof fn lemma_space_nodes_caps_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            post.spaces.roots@.dom() == pre.spaces.roots@.dom(),
            post.spaces.records == pre.spaces.records,
            pre.tables.owner@.contains_key(page_of(n)),
            pre.tables.owner@.contains_key(page_of(m)),
        ensures
            space_nodes_dead(&post.list, &post.spaces),
    {
        assert forall|x: usize| #[trigger] pre.list.valid(x) && x != n && x != m implies {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        } by {
            pre.list.lemma_valid_bound(x);
        }
        assert forall|s: usize| #[trigger] post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device
            implies pre.spaces.roots@.contains_key(s) && post.spaces.records@[s] == pre.spaces.records@[s] by {
            assert(post.spaces.roots@.dom().contains(s));
        }
        Self::lemma_space_nodes_frame(pre, post, n, m);
    }

    /// What a table page's retype at base leaves of the list: the new node pages were not the list's, and
    /// every node the list held but base keeps its liveness and kind.
    pub open spec fn page_added_step(pre: Self, post: Self, base: usize) -> bool {
        &&& pre.wf()
        &&& base % TABLE_PAGE_BYTES == 0
        &&& pre.blocks.tracks_addr_run(base, 8)
        &&& forall|t: usize| #[trigger] post.table_pages.maps@.contains_key(t)
            ==> t == base || pre.table_pages.maps@.contains_key(t)
        &&& forall|k: usize| k < TABLE_NODE_PAGES ==> !pre.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
        &&& forall|x: usize| #[trigger] pre.list.valid(x) ==> {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        }
        &&& forall|x: int| 0 <= x < NODE_SPACE && x != base ==> #[trigger] post.list.nodes@[x].live == pre.list.nodes@[x].live
    }

    /// A live node in the new table page's node pages after its retype is the hidden one: the pages held no
    /// live node before, and only base changed.
    proof fn lemma_table_node_fresh(pre: Self, post: Self, base: usize, k: usize, i: usize)
        requires
            Self::page_added_step(pre, post, base),
            k < TABLE_NODE_PAGES,
            i < NODES_PER_PAGE,
            k != 0 || i != 0,
        ensures
            !post.list.nodes@[table_node(base, k, i) as int].live,
    {
        let x = table_node(base, k, i);
        lemma_table_node_place(base, k, i);
        assert(!pre.list.valid(x));
        if pre.list.nodes@[x as int].live {
            pre.list.lemma_live_valid(x);
        }
    }

    /// A live node in an older table page's node pages after a table page's retype is as it was: it is not
    /// base, whose page the list did not hold.
    proof fn lemma_table_node_kept(pre: Self, post: Self, base: usize, t: usize, k: usize, i: usize)
        requires
            Self::page_added_step(pre, post, base),
            pre.table_pages.maps@.contains_key(t),
            k < TABLE_NODE_PAGES,
            i < NODES_PER_PAGE,
            k != 0 || i != 0,
            post.list.nodes@[table_node(t, k, i) as int].live,
        ensures
            post.list.nodes@[table_node(t, k, i) as int].kind is Mapping,
    {
        let x = table_node(t, k, i);
        pre.lemma_table_node_in_block(t, k, i);
        lemma_table_page_aligned(base);
        assert(table_node_page(base, 0) == base);
        assert(!pre.list.pages@.dom().contains(base));
        assert(page_of(base) == base);
        assert(x != base);
        assert(pre.list.nodes@[x as int].live);
    }

    /// The clause after a table page's retype at base: its node pages hold no live node but the hidden one,
    /// and every other table page's nodes are as they were.
    pub proof fn lemma_table_nodes_page_added(pre: Self, post: Self, base: usize)
        requires
            Self::page_added_step(pre, post, base),
        ensures
            table_nodes_are_mappings(&post.list, &post.table_pages),
    {
        assert forall|t: usize, k: usize, i: usize| #![trigger table_node(t, k, i)]
            post.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE && (k != 0 || i != 0)
                && post.list.nodes@[table_node(t, k, i) as int].live
            implies post.list.nodes@[table_node(t, k, i) as int].kind is Mapping by {
            if t == base {
                Self::lemma_table_node_fresh(pre, post, base, k, i);
            } else {
                Self::lemma_table_node_kept(pre, post, base, t, k, i);
            }
        }
    }
}

/// Where node i of node page k of the table page at t lies: in that node page, at slot i.
pub proof fn lemma_table_node_place(t: usize, k: usize, i: usize)
    requires
        t % TABLE_PAGE_BYTES == 0,
        t / PAGE_SZ + TABLE_NODE_PAGES <= NUM_PAGES,
        k < TABLE_NODE_PAGES,
        i < NODES_PER_PAGE,
    ensures
        table_node(t, k, i) == t + k * PAGE_SZ + i,
        table_node(t, k, i) < NODE_SPACE,
        table_node(t, k, i) / PAGE_SZ == t / PAGE_SZ + k,
        table_node(t, k, i) % PAGE_SZ == i,
        page_of(table_node(t, k, i)) == table_node_page(t, k),
        k != 0 || i != 0 ==> table_node(t, k, i) != t,
{
    lemma_table_page_aligned(t);
    lemma_table_node_page(t, k);
    let q = t / PAGE_SZ;
    lemma_table_bound(t);
    let n = table_node(t, k, i);
    assert(n == PAGE_SZ * (q + k) + i);
    lemma_fundamental_div_mod_converse(n as int, (PAGE_SZ as int), q + k, i as int);
    assert(page_of(n) == n - i);
}

} // verus!
