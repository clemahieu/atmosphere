//! The boot steps that make the root process from pages boot sets aside, not from an untyped, so the
//! blocks they type are never retyped: no untyped covers them. They run on the state init leaves. See
//! design/root-process-at-boot/.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::console::*;
use crate::capability::derive::*;
use crate::capability::device::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::mapping::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;
use crate::layouts::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

/// The index of the root's capability to its own process in its table: slot 1 of entry 0, the first
/// slot of the table's first leaf.
pub const ROOT_PROCESS_SLOT: usize = 1;

/// The index of the root's capability to its own thread: slot 2 of entry 0.
pub const ROOT_THREAD_SLOT: usize = 2;

/// The index of the root's console capability: slot 3 of entry 0.
pub const ROOT_CONSOLE_SLOT: usize = 3;

/// The rights of an untyped capability boot hands the root: retype alone. Control is no right over
/// memory, design/sharing-by-derive/.
pub const UNTYPED_RIGHTS: u32 = 8;

/// The untyped capability boot hands the root for the block of order pages at base.
pub open spec fn untyped_payload(base: usize, order: u8) -> Payload {
    Payload { kind: CapKind::Untyped, order, rights: UNTYPED_RIGHTS, base, badge: 0, reserved: 0 }
}

/// o is one of the pages of the block of order pages at base, as reach names pages.
pub open spec fn in_block(base: usize, order: u8, o: usize) -> bool {
    &&& o % 4096 == 0
    &&& base <= o < base + block_bytes(order)
}

impl CapKernel {
    /// What init leaves: the list's synthetic root alone, no table, object, mapping or frame, every page
    /// reserved and no large block typed.
    pub open spec fn boot_empty(&self) -> bool {
        let root = self.list.seq@[0];
        &&& root % 4096 == 0
        &&& self.list.seq@ == seq![root]
        &&& self.list.parent@ == Map::<usize, usize>::empty()
        &&& self.list.pages@.dom() == set![root]
        &&& self.tables.roots@ == Map::<usize, PointsTo<TableRoot>>::empty()
        &&& self.tables.owner@ == Map::<usize, (usize, int)>::empty()
        &&& self.table_pages.maps@ == Map::<usize, PointsTo<PageMap>>::empty()
        &&& self.table_pages.records@ == Map::<usize, PointsTo<TableRecord>>::empty()
        &&& self.spaces.roots@ == Map::<usize, PointsTo<PageMap>>::empty()
        &&& self.spaces.records@ == Map::<usize, PointsTo<SpaceRecord>>::empty()
        &&& self.spaces.loaded@ == Map::<usize, PointsTo<SpaceCores>>::empty()
        &&& self.spaces.holders@ == IMap::<usize, Set<usize>>::empty()
        &&& self.spaces.bound@ == IMap::<usize, Set<usize>>::empty()
        &&& self.processes.records@ == Map::<usize, PointsTo<ProcessRecord>>::empty()
        &&& self.processes.spare@ == Map::<usize, PagePerm4k>::empty()
        &&& self.processes.holders@ == IMap::<usize, Set<usize>>::empty()
        &&& self.processes.bound@ == IMap::<usize, Set<usize>>::empty()
        &&& self.threads.records@ == Map::<usize, PointsTo<ThreadRecord>>::empty()
        &&& self.threads.holders@ == IMap::<usize, Set<usize>>::empty()
        &&& self.mappings@ == IMap::<usize, MappingRecord>::empty()
        &&& self.holders@ == IMap::<BlockRef, Set<usize>>::empty()
        &&& self.zeroing.blocks@ == Map::<usize, usize>::empty()
        &&& forall|i: int| 0 <= i < NUM_PAGES ==> {
            &&& (#[trigger] self.blocks.pages@[i]).kind is Reserved
            &&& self.blocks.pages@[i].object is None
        }
        &&& forall|r: int| 0 <= r < NUM_2M ==> !(#[trigger] self.blocks.regions_2m@[r]).typed
        &&& forall|r: int| 0 <= r < NUM_1G ==> !(#[trigger] self.blocks.regions_1g@[r]).typed
    }

    /// The first boot step: the root process from the eight pages at `base`, and the first leaf of its
    /// table from the two at `leaf`, with the root's capability to its process, with control, at
    /// ROOT_PROCESS_SLOT. Both blocks are typed as a retype types them, so a retype naming them is
    /// refused, and both hang below the list's synthetic root: the capability, and the leaf's hidden
    /// node, which every live leaf has. Boot hands over every page's permission.
    #[verifier::spinoff_prover]
    pub fn boot_root_process(&mut self, root: usize, base: usize, leaf: usize, Tracked(pages): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            old(self).boot_empty(),
            root == old(self).list.seq@[0],
            base % 32768 == 0,
            base / 4096 + 8 <= NUM_PAGES,
            leaf % 8192 == 0,
            leaf != NO_LEAF,
            leaf / 4096 + 2 <= NUM_PAGES,
            base + 32768 <= leaf || leaf + 8192 <= base,
            !(base <= root < base + 32768),
            !(leaf <= root < leaf + 8192),
            forall|i: usize| base / 4096 <= i < base / 4096 + 8 || leaf / 4096 <= i < leaf / 4096 + 2
                ==> #[trigger] holds(pages, i),
        ensures
            final(self).wf(),
            final(self).list.seq@[0] == root,
            final(self).tables.roots@.contains_key(base),
            final(self).tables.leaf(base, 0) == leaf,
            final(self).tables.has_slot(&final(self).list, base, ROOT_PROCESS_SLOT),
            final(self).tables.node_of(base, ROOT_PROCESS_SLOT) == leaf + 1,
            final(self).is_cap((leaf + 1) as usize),
            final(self).payload_of((leaf + 1) as usize) == process_of(base),
            final(self).payload_of((leaf + 1) as usize).rights & CONTROL_RIGHT != 0,
            final(self).list.is_child(root, (leaf + 1) as usize),
            final(self).list.nodes@[leaf + 1].depth == 1,
            final(self).list.is_child(root, leaf),
            final(self).list.nodes@[leaf as int].live,
            final(self).list.nodes@[leaf as int].kind is Hidden,
            forall|x: int| 0 <= x < NODE_SPACE && #[trigger] final(self).list.nodes@[x].live
                && final(self).list.nodes@[x].kind is Hidden ==> x == leaf,
            forall|x: usize| #[trigger] final(self).is_cap(x) ==> x == leaf + 1,
            !final(self).list.nodes@[leaf + 2].live,
            !final(self).list.nodes@[leaf + 3].live,
            forall|k: int| 0 <= k < 8 ==> {
                ||| (#[trigger] final(self).blocks.pages@[base / 4096 + k]).kind is Base
                ||| final(self).blocks.pages@[base / 4096 + k].kind is Member
            },
            forall|k: int| 0 <= k < 2 ==> {
                ||| (#[trigger] final(self).blocks.pages@[leaf / 4096 + k]).kind is Base
                ||| final(self).blocks.pages@[leaf / 4096 + k].kind is Member
            },
            final(self).processes.records@.contains_key(base),
            !final(self).processes.records@[base].value().dead,
            final(self).spaces.roots@.contains_key(base),
            forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] final(self).loaded(c, base),
            final(self).blocks.pages@[(base / 4096) as int].refs == 1,
            final(self).list.pages@.dom() == set![root, leaf],
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|i: int| 0 <= i < NUM_PAGES && !(base / 4096 <= i < base / 4096 + 8) && !(leaf / 4096 <= i < leaf / 4096 + 2)
                ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i],
    {
        let ghost pre = *old(self);
        let pb = base / 4096;
        let lb = leaf / 4096;
        let cap = leaf + 1;
        proof {
            lemma2_to64();
            lemma_table_page_base(base, pb);
            assert(lb % 2 == 0 && lb * 4096 == leaf) by (nonlinear_arith)
                requires
                    leaf % 8192 == 0,
                    lb == leaf / 4096,
            ;
            lemma_slot_in_leaf(leaf, 0);
            lemma_slot_in_leaf(leaf, 1);
            assert(pb + 8 <= lb || lb + 2 <= pb);
        }
        let tracked mut pages = pages;
        let ghost given = pages;
        add_free_run(&mut self.blocks, pb, 8, Tracked(&mut pages));
        proof {
            assert forall|i: usize| lb <= i < lb + 2 implies #[trigger] holds(pages, i) by {
                assert(holds(given, i));
            }
        }
        add_free_run(&mut self.blocks, lb, 2, Tracked(&mut pages));
        let ghost freed = self.blocks;
        proof {
            assert forall|k: int| 0 <= k < 2 implies #[trigger] freed.pages@[lb + k].kind is Free by {}
            assert(!freed.covered(lb as int));
        }
        let typed_leaf = self.blocks.try_type(lb, 1, ObjectType::TableLeaf);
        let ghost leaf_typed = self.blocks;
        proof {
            assert forall|k: int| 0 <= k < 8 implies #[trigger] leaf_typed.pages@[pb + k].kind is Free by {
                assert(leaf_typed.pages@[pb + k] == freed.pages@[pb + k]);
            }
            assert(!leaf_typed.covered(pb as int));
        }
        let typed_process = self.blocks.try_type(pb, 3, ObjectType::Process);
        let Tracked(leaf_perms) = typed_leaf.unwrap();
        let Tracked(process_perms) = typed_process.unwrap();
        let tracked mut leaf_perms = leaf_perms;
        let tracked mut process_perms = process_perms;
        let tracked first;
        let tracked second;
        let tracked table_root;
        let tracked record;
        let tracked spare2;
        let tracked spare3;
        let tracked spare4;
        let tracked space_root;
        let tracked space_record;
        let tracked space_cores;
        proof {
            assert(0usize < order_pages(1));
            assert(1usize < order_pages(1));
            assert(leaf_perms[(lb + 0usize) as usize].addr() == (lb + 0usize) * 4096);
            assert(leaf_perms[(lb + 1usize) as usize].addr() == (lb + 1usize) * 4096);
            first = leaf_perms.tracked_remove(lb);
            second = leaf_perms.tracked_remove((lb + 1) as usize);
            let all = process_perms;
            assert forall|k: usize| k < 8 implies #[trigger] holds(all, (pb + k) as usize) by {
                assert(all[(pb + k) as usize].addr() == (pb + k) * 4096);
            }
            assert(holds(all, (pb + 0) as usize));
            assert(holds(all, (pb + 1) as usize));
            assert(holds(all, (pb + 2) as usize));
            assert(holds(all, (pb + 3) as usize));
            assert(holds(all, (pb + 4) as usize));
            assert(holds(all, (pb + 5) as usize));
            assert(holds(all, (pb + 6) as usize));
            assert(holds(all, (pb + 7) as usize));
            table_root = process_perms.tracked_remove(pb);
            record = process_perms.tracked_remove((pb + 1) as usize);
            spare2 = process_perms.tracked_remove((pb + 2) as usize);
            spare3 = process_perms.tracked_remove((pb + 3) as usize);
            spare4 = process_perms.tracked_remove((pb + 4) as usize);
            space_root = process_perms.tracked_remove((pb + 5) as usize);
            space_record = process_perms.tracked_remove((pb + 6) as usize);
            space_cores = process_perms.tracked_remove((pb + 7) as usize);
        }
        let ghost l0 = self.list;
        self.tables.put_root(&self.list, base, Tracked(table_root));
        let ghost rooted = self.tables;
        let tracked mut typed_record = page_into_process_record(record);
        PPtr::<ProcessRecord>::from_usize(base + PROCESS_RECORD_PAGE * 4096).put(Tracked(&mut typed_record), ProcessRecord { dead: false });
        proof {
            self.processes.records.borrow_mut().tracked_insert(base, typed_record);
            self.processes.spare.borrow_mut().tracked_insert((base + 2 * 4096) as usize, spare2);
            self.processes.spare.borrow_mut().tracked_insert((base + 3 * 4096) as usize, spare3);
            self.processes.spare.borrow_mut().tracked_insert((base + 4 * 4096) as usize, spare4);
        }
        let root_table = base + SPACE_ROOT_PAGE * 4096;
        let (_, Tracked(map)) = page_perm_to_page_map(root_table, Tracked(space_root));
        let ghost map0 = map.value();
        let tracked mut map = map;
        page_map_set_kernel_entry_range(&self.spaces.kernel_entries, root_table, Tracked(&mut map));
        let tracked mut typed;
        let tracked mut cores;
        proof {
            typed = page_into_space_record(space_record);
            cores = page_into_core_list(space_cores);
        }
        let ids = vstd::array::array_fill_for_copy_types::<usize, NUM_CPUS>(0usize);
        PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * 4096).put(Tracked(&mut cores), SpaceCores { list: 0u32, ids });
        PPtr::<SpaceRecord>::from_usize(base + SPACE_RECORD_PAGE * 4096).put(
            Tracked(&mut typed),
            SpaceRecord {
                kind: SpaceKind::Process,
                root: root_table,
                table: TableRecord { level: 4, space: Some(base), parent: None, written: false },
            },
        );
        proof {
            self.spaces.roots.borrow_mut().tracked_insert(base, map);
            self.spaces.records.borrow_mut().tracked_insert(base, typed);
            self.spaces.loaded.borrow_mut().tracked_insert(base, cores);
        }
        let nodes = init_node_page(leaf, Tracked(first));
        proof {
            assert(!l0.pages@.dom().contains(leaf));
            l0.lemma_link(0);
        }
        self.list.add_page(leaf, nodes);
        let ghost l1 = self.list;
        proof {
            assert(l1.valid(leaf));
            assert(l1.valid(cap));
            l1.lemma_seq_fits();
        }
        self.list.derive(root, leaf, NodeKind::Hidden);
        let ghost l2 = self.list;
        proof {
            rooted.lemma_wf_same_pages(&l0, &l2);
            assert(l2.valid(cap));
            assert(!l2.nodes@[cap as int].live);
            l2.lemma_seq_fits();
        }
        self.tables.add_leaf(&self.list, base, 0, leaf, Tracked(second));
        let ghost leafed = self.tables;
        self.list.derive(root, cap, NodeKind::Capability);
        let ghost l3 = self.list;
        proof {
            leafed.lemma_wf_same_pages(&l2, &l3);
            assert(l1.valid((leaf + 2) as usize));
            assert(!l2.nodes@[leaf + 2].live);
            assert(!l3.nodes@[leaf + 2].live);
            assert(l1.valid((leaf + 3) as usize));
            assert(!l2.nodes@[leaf + 3].live);
            assert(!l3.nodes@[leaf + 3].live);
            assert(index_entry(ROOT_PROCESS_SLOT) == 0);
            assert(index_slot(ROOT_PROCESS_SLOT) == 1);
            assert(index_ok(ROOT_PROCESS_SLOT));
            assert(leafed.leaf(base, 0) == leaf);
            assert(leafed.has_slot(&l3, base, ROOT_PROCESS_SLOT));
            assert(leafed.node_of(base, ROOT_PROCESS_SLOT) == cap);
        }
        self.tables.set_payload(
            &self.list,
            base,
            ROOT_PROCESS_SLOT,
            Payload { kind: CapKind::Process, order: PROCESS_ORDER, rights: PROCESS_RIGHTS, base, badge: 0, reserved: 0 },
        );
        self.processes.holders = Ghost(pre.processes.holders@.insert(base, set![cap]));
        self.processes.bound = Ghost(pre.processes.bound@.insert(base, Set::<usize>::empty()));
        self.spaces.holders = Ghost(pre.spaces.holders@.insert(base, Set::<usize>::empty()));
        self.spaces.bound = Ghost(pre.spaces.bound@.insert(base, Set::<usize>::empty()));
        proof {
            let post = *self;
            assert(post.tables.roots@.dom() =~= set![base]);
            assert(post.tables.payload_of(leaf) == leafed.payload_of(leaf));
            assert forall|i: usize| #![trigger post.spaces.roots@[base].value()[i]]
                KERNEL_MEM_END_L4INDEX <= i < 512 implies post.spaces.roots@[base].value()[i].is_empty() by {
                assert(post.spaces.roots@[base].value()[i] =~= map0[i]);
                assert(map0[i].is_empty());
            }
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.spaces.loaded@[base].value().ids@[c] == 0usize by {
                broadcast use vstd::array::axiom_spec_array_fill_for_copy_type;
                assert(vstd::array::spec_array_fill_for_copy_type::<usize, NUM_CPUS>(0usize).view()[c] == 0usize);
            }
            assert(PROCESS_RIGHTS & CONTROL_RIGHT != 0) by (compute_only);
            Self::lemma_boot_root_process(pre, post, root, base, leaf, l0, l1, l2, l3, freed, leaf_typed);
            assert(post.list.pages@.dom() =~= set![root, leaf]);
            assert forall|i: int| 0 <= i < NUM_PAGES && !(pb <= i < pb + 8) && !(lb <= i < lb + 2)
                implies #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i] by {
                assert(post.blocks.pages@[i] == leaf_typed.pages@[i]);
                assert(leaf_typed.pages@[i] == freed.pages@[i]);
            }
        }
    }

    /// The second boot step: the root thread from the two pages at `t`, bound to the root process whose
    /// capability is at ROOT_PROCESS_SLOT, with the root's capability to it, with control, at
    /// ROOT_THREAD_SLOT below the list's synthetic root. The block is typed as a retype types it, so a
    /// retype naming it is refused. Boot hands over both pages' permissions.
    #[verifier::spinoff_prover]
    pub fn boot_root_thread(&mut self, root: usize, process: usize, leaf: usize, t: usize, Tracked(pages): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.roots@.contains_key(process),
            old(self).tables.leaf(process, 0) == leaf,
            leaf % 8192 == 0,
            leaf != NO_LEAF,
            leaf / 4096 + 2 <= NUM_PAGES,
            old(self).list.nodes@[leaf as int].live,
            old(self).is_cap((leaf + 1) as usize),
            old(self).payload_of((leaf + 1) as usize) == process_of(process),
            old(self).list.nodes@[leaf + 1].depth == 1,
            !old(self).list.nodes@[leaf + 2].live,
            old(self).blocks.pages@[(process / 4096) as int].refs == 1,
            t % 8192 == 0,
            t / 4096 + 2 <= NUM_PAGES,
            forall|i: int| t / 4096 <= i < t / 4096 + 2 ==> #[trigger] old(self).blocks.pages@[i].kind is Reserved,
            !old(self).blocks.covered((t / 4096) as int),
            forall|p: usize| #[trigger] old(self).list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
                ==> !(t / 4096 <= p / 4096 < t / 4096 + 2),
            forall|i: usize| t / 4096 <= i < t / 4096 + 2 ==> #[trigger] holds(pages, i),
        ensures
            final(self).wf(),
            final(self).list.seq@[0] == root,
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.has_slot(&final(self).list, process, ROOT_THREAD_SLOT),
            final(self).tables.node_of(process, ROOT_THREAD_SLOT) == leaf + 2,
            final(self).is_cap((leaf + 2) as usize),
            forall|x: usize| #[trigger] final(self).is_cap(x) ==> x == leaf + 2 || old(self).is_cap(x),
            final(self).payload_of((leaf + 2) as usize) == thread_of(t),
            final(self).payload_of((leaf + 2) as usize).rights & CONTROL_RIGHT != 0,
            final(self).list.is_child(root, (leaf + 2) as usize),
            final(self).list.nodes@[leaf + 2].depth == 1,
            final(self).threads.records@.contains_key(t),
            final(self).threads.records@[t].value() == (ThreadRecord {
                state: crate::capability::thread::ThreadState::Inactive,
                frame: zero_registers(),
                pending_stop: false,
                dying: false,
                process: Some(process),
                placement: None,
            }),
            final(self).list.is_child((leaf + 1) as usize, t),
            final(self).list.nodes@[t as int].kind is Binding,
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables).insert(t, process),
            forall|k: int| 0 <= k < 2 ==> {
                ||| (#[trigger] final(self).blocks.pages@[t / 4096 + k]).kind is Base
                ||| final(self).blocks.pages@[t / 4096 + k].kind is Member
            },
            final(self).is_cap((leaf + 1) as usize),
            final(self).payload_of((leaf + 1) as usize) == old(self).payload_of((leaf + 1) as usize),
            final(self).list.nodes@[leaf + 1].depth == 1,
            final(self).list.parent@[(leaf + 1) as usize] == old(self).list.parent@[(leaf + 1) as usize],
            final(self).list.parent@[leaf] == old(self).list.parent@[leaf],
            forall|x: int| #![trigger final(self).list.nodes@[x]] 0 <= x < NODE_SPACE && x != t && x != leaf + 2 ==> {
                &&& final(self).list.nodes@[x].live == old(self).list.nodes@[x].live
                &&& old(self).list.nodes@[x].live ==> final(self).list.nodes@[x].kind == old(self).list.nodes@[x].kind
            },
            final(self).processes.records == old(self).processes.records,
            final(self).spaces == old(self).spaces,
            final(self).list.pages@.dom() == old(self).list.pages@.dom().insert(t),
            forall|i: int| 0 <= i < NUM_PAGES && !(t / 4096 <= i < t / 4096 + 2) ==> {
                &&& (#[trigger] final(self).blocks.pages@[i]).kind == old(self).blocks.pages@[i].kind
                &&& final(self).blocks.pages@[i].object == old(self).blocks.pages@[i].object
                &&& final(self).blocks.pages@[i].order == old(self).blocks.pages@[i].order
            },
    {
        let ghost pre = *old(self);
        let tb = t / 4096;
        let n = leaf + 1;
        let cap = leaf + 2;
        proof {
            lemma2_to64();
            assert(tb % 2 == 0 && tb * 4096 == t) by (nonlinear_arith)
                requires
                    t % 8192 == 0,
                    tb == t / 4096,
            ;
            lemma_slot_in_leaf(leaf, 1);
            lemma_slot_in_leaf(leaf, 2);
            lemma_slot_in_leaf(t, 0);
            assert(index_entry(ROOT_THREAD_SLOT) == 0);
            assert(index_slot(ROOT_THREAD_SLOT) == 2);
            assert(index_ok(ROOT_THREAD_SLOT));
            assert(pre.tables.has_slot(&pre.list, process, ROOT_THREAD_SLOT));
            assert(pre.tables.node_of(process, ROOT_THREAD_SLOT) == cap);
            assert(pre.tables.owner@.contains_key(leaf));
            pre.lemma_slot_bound(n);
            pre.lemma_slot_bound(cap);
            pre.list.lemma_link(0);
            pre.list.lemma_live_valid(root);
            assert(pre.list.nodes@[root as int].kind is Capability);
            assert(pre.list.nodes@[root as int].depth == 0);
            assert(root != cap) by {
                assert(!pre.tables.owner@.contains_key(page_of(root)));
            }
            // The process's block is a base, so outside the thread's reserved pages.
            assert(process_wf(&pre.processes, &pre.blocks, process)) by {
                pre.lemma_process_cap(n);
            }
            assert(!(tb <= process / 4096 < tb + 2)) by {
                if tb <= process / 4096 < tb + 2 {
                    assert(pre.blocks.pages@[(process / 4096) as int].kind is Reserved);
                }
            }
        }
        let tracked mut pages = pages;
        add_free_run(&mut self.blocks, tb, 2, Tracked(&mut pages));
        let ghost freed = *self;
        proof {
            Self::lemma_reserved_freed(pre, freed, tb, 2);
            assert forall|k: int| 0 <= k < 2 implies #[trigger] freed.blocks.pages@[tb + k].kind is Free by {}
            assert(!freed.blocks.covered(tb as int));
            assert(!freed.list.pages@.dom().contains(t)) by {
                if freed.list.pages@.dom().contains(t) {
                    assert(t / 4096 == tb);
                }
            }
        }
        let typed = self.blocks.try_type(tb, 1, ObjectType::Thread);
        let Tracked(perms) = typed.unwrap();
        let tracked mut perms = perms;
        let tracked first;
        let tracked second;
        proof {
            assert(0usize < order_pages(1));
            assert(1usize < order_pages(1));
            assert(perms[(tb + 0usize) as usize].addr() == (tb + 0usize) * 4096);
            assert(perms[(tb + 1usize) as usize].addr() == (tb + 1usize) * 4096);
            assert((tb + 0usize) as usize == tb);
            first = perms.tracked_remove(tb);
            second = perms.tracked_remove((tb + 1) as usize);
        }
        let nodes = init_node_page(t, Tracked(first));
        self.list.add_page(t, nodes);
        let ghost mid = self.list;
        proof {
            mid.lemma_seq_fits();
            assert(mid.nodes@[root as int] == freed.list.nodes@[root as int]);
            assert(mid.nodes@[cap as int] == freed.list.nodes@[cap as int]);
            assert(mid.valid(cap));
            assert(!freed.list.nodes@[t as int].live) by {
                if freed.list.nodes@[t as int].live {
                    freed.list.lemma_live_valid(t);
                }
            }
            assert(!mid.nodes@[t as int].live);
        }
        let tracked mut record = page_into_thread_record(second);
        PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096).put(Tracked(&mut record), new_thread_record());
        proof {
            self.threads.records.borrow_mut().tracked_insert(t, record);
        }
        self.list.derive(root, cap, NodeKind::Capability);
        proof {
            freed.tables.lemma_wf_same_pages(&freed.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            process,
            ROOT_THREAD_SLOT,
            Payload { kind: CapKind::Thread, order: THREAD_ORDER, rights: THREAD_RIGHTS, base: t, badge: 0, reserved: 0 },
        );
        self.threads.holders = Ghost(freed.threads.holders@.insert(t, set![cap]));
        proof {
            Self::lemma_boot_thread_typed(freed, *self, mid, root, process, leaf, t);
        }
        let ghost typed = *self;
        proof {
            assert(typed.is_cap(n));
            assert(typed.payload_of(n) == process_of(process));
            assert(typed.blocks.pages@[(process / 4096) as int] == pre.blocks.pages@[(process / 4096) as int]);
            assert(!typed.list.nodes@[t as int].live);
        }
        self.bind_thread(n, t);
        proof {
            let post = *self;
            assert(post.tables == typed.tables);
            assert(cap != t);
            assert(n != t);
            assert(post.list.nodes@[cap as int].live == typed.list.nodes@[cap as int].live);
            assert(post.list.nodes@[cap as int].depth == typed.list.nodes@[cap as int].depth);
            assert(post.list.nodes@[n as int].depth == typed.list.nodes@[n as int].depth);
            assert(post.list.parent@[cap] == root);
            assert(post.list.seq@[0] == root);
            lemma_has(post.list.seq@, cap);
            assert(post.list.is_child(root, cap));
            assert(THREAD_RIGHTS & CONTROL_RIGHT != 0) by (compute_only);
            assert(post.threads.records@[t].value() == (ThreadRecord {
                state: crate::capability::thread::ThreadState::Inactive,
                frame: zero_registers(),
                pending_stop: false,
                dying: false,
                process: Some(process),
                placement: None,
            }));
            assert(thread_process(&post.threads, t) == Some(process));
            assert forall|x: usize| x != t implies #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x) by {
                assert(freed.threads == pre.threads);
                if post.threads.records@.contains_key(x) {
                    assert(post.threads.records@[x] == typed.threads.records@[x]);
                }
            }
            Self::lemma_bound_threads_insert(pre, post, t, process);
            assert forall|k: int| 0 <= k < 2 implies {
                ||| (#[trigger] post.blocks.pages@[t / 4096 + k]).kind is Base
                ||| post.blocks.pages@[t / 4096 + k].kind is Member
            } by {
                assert(post.blocks.pages@[tb + k].kind == typed.blocks.pages@[tb + k].kind);
                if k == 1 {
                    typed.blocks.lemma_member_of(tb as int, tb + 1);
                }
            }
            assert forall|i: int| 0 <= i < NUM_PAGES && !(t / 4096 <= i < t / 4096 + 2) implies {
                &&& (#[trigger] post.blocks.pages@[i]).kind == pre.blocks.pages@[i].kind
                &&& post.blocks.pages@[i].object == pre.blocks.pages@[i].object
                &&& post.blocks.pages@[i].order == pre.blocks.pages@[i].order
            } by {
                assert(typed.blocks.pages@[i] == freed.blocks.pages@[i]);
                assert(freed.blocks.pages@[i] == pre.blocks.pages@[i]);
            }
            assert(post.list.pages@.dom() =~= pre.list.pages@.dom().insert(t));
            assert forall|x: usize| #[trigger] post.is_cap(x) implies x == cap || pre.is_cap(x) by {
                assert(typed.is_cap(x));
                assert(freed.is_cap(x) == pre.is_cap(x));
            }
            // Only the thread's binding node and its capability come alive; every other node keeps its
            // liveness, and a node live before keeps its kind, the leaf's hidden node among them.
            assert(freed.list == pre.list);
            assert forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != t && x != cap implies {
                &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
                &&& pre.list.nodes@[x].live ==> post.list.nodes@[x].kind == pre.list.nodes@[x].kind
            } by {
                assert(post.list.nodes@[x].live == typed.list.nodes@[x].live);
                assert(typed.list.nodes@[x].live == mid.nodes@[x].live);
                assert(mid.nodes@[x].live == pre.list.nodes@[x].live);
                if pre.list.nodes@[x].live {
                    pre.list.lemma_live_valid(x as usize);
                    assert(mid.nodes@[x] == pre.list.nodes@[x]);
                }
            }
            pre.list.lemma_live_valid(leaf);
            assert(page_of(leaf) == leaf);
            assert(leaf != t) by {
                assert(pre.list.pages@.dom().contains(leaf));
            }
            assert(post.list.parent@[leaf] == pre.list.parent@[leaf]);
        }
    }

    /// Boot's one entry for the root: the root process from the eight pages at `process` with its
    /// table's first leaf from the two at `leaf`, then the root thread from the two at `t`, bound to it.
    /// The root holds its process at ROOT_PROCESS_SLOT and its thread at ROOT_THREAD_SLOT, both with
    /// control, and nothing else, so what it reaches is exactly the pages of those two blocks. It holds
    /// no Space capability: it writes its own space through its process capability. See
    /// design/root-process-at-boot/ and design/process-holds-capabilities/.
    pub fn boot_root(&mut self, root: usize, process: usize, leaf: usize, t: usize, Tracked(pages): Tracked<Map<usize, PagePerm4k>>)
        requires
            old(self).wf(),
            old(self).boot_empty(),
            root == old(self).list.seq@[0],
            process % 32768 == 0,
            process / 4096 + 8 <= NUM_PAGES,
            leaf % 8192 == 0,
            leaf != NO_LEAF,
            leaf / 4096 + 2 <= NUM_PAGES,
            t % 8192 == 0,
            t / 4096 + 2 <= NUM_PAGES,
            process + 32768 <= leaf || leaf + 8192 <= process,
            process + 32768 <= t || t + 8192 <= process,
            leaf + 8192 <= t || t + 8192 <= leaf,
            !(process <= root < process + 32768),
            !(leaf <= root < leaf + 8192),
            !(t <= root < t + 8192),
            forall|i: usize| process / 4096 <= i < process / 4096 + 8 || leaf / 4096 <= i < leaf / 4096 + 2
                || t / 4096 <= i < t / 4096 + 2 ==> #[trigger] holds(pages, i),
        ensures
            final(self).wf(),
            final(self).list.seq@[0] == root,
            final(self).tables.has_slot(&final(self).list, process, ROOT_PROCESS_SLOT),
            final(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
            final(self).is_cap((leaf + 1) as usize),
            final(self).payload_of((leaf + 1) as usize) == process_of(process),
            final(self).payload_of((leaf + 1) as usize).rights & CONTROL_RIGHT != 0,
            final(self).list.is_child(root, (leaf + 1) as usize),
            final(self).list.nodes@[leaf + 1].depth == 1,
            final(self).tables.has_slot(&final(self).list, process, ROOT_THREAD_SLOT),
            final(self).tables.node_of(process, ROOT_THREAD_SLOT) == leaf + 2,
            final(self).is_cap((leaf + 2) as usize),
            final(self).payload_of((leaf + 2) as usize) == thread_of(t),
            final(self).payload_of((leaf + 2) as usize).rights & CONTROL_RIGHT != 0,
            final(self).list.is_child(root, (leaf + 2) as usize),
            final(self).list.nodes@[leaf + 2].depth == 1,
            !final(self).list.nodes@[leaf + 3].live,
            final(self).list.nodes@[leaf as int].live,
            final(self).list.nodes@[leaf as int].kind is Hidden,
            final(self).list.is_child(root, leaf),
            forall|x: int| 0 <= x < NODE_SPACE && #[trigger] final(self).list.nodes@[x].live
                && final(self).list.nodes@[x].kind is Hidden ==> x == leaf,
            final(self).threads.records@.contains_key(t),
            final(self).threads.records@[t].value() == (ThreadRecord {
                state: crate::capability::thread::ThreadState::Inactive,
                frame: zero_registers(),
                pending_stop: false,
                dying: false,
                process: Some(process),
                placement: None,
            }),
            forall|o: usize| #[trigger] final(self).view().reach(process, o)
                <==> (o % 4096 == 0 && ((process <= o < process + 32768) || (t <= o < t + 8192))),
            forall|k: int| 0 <= k < 8 ==> {
                ||| (#[trigger] final(self).blocks.pages@[process / 4096 + k]).kind is Base
                ||| final(self).blocks.pages@[process / 4096 + k].kind is Member
            },
            forall|k: int| 0 <= k < 2 ==> {
                ||| (#[trigger] final(self).blocks.pages@[leaf / 4096 + k]).kind is Base
                ||| final(self).blocks.pages@[leaf / 4096 + k].kind is Member
            },
            forall|k: int| 0 <= k < 2 ==> {
                ||| (#[trigger] final(self).blocks.pages@[t / 4096 + k]).kind is Base
                ||| final(self).blocks.pages@[t / 4096 + k].kind is Member
            },
    {
        let ghost pre = *old(self);
        let ghost pb = process / 4096;
        let ghost lb = leaf / 4096;
        let ghost tb = t / 4096;
        proof {
            lemma2_to64();
            assert(pb * 4096 == process && lb * 4096 == leaf && tb * 4096 == t) by (nonlinear_arith)
                requires
                    process % 32768 == 0,
                    leaf % 8192 == 0,
                    t % 8192 == 0,
                    pb == process / 4096,
                    lb == leaf / 4096,
                    tb == t / 4096,
            ;
            assert(tb + 2 <= pb || pb + 8 <= tb);
            assert(tb + 2 <= lb || lb + 2 <= tb);
        }
        let tracked mut pages = pages;
        let tracked thread_pages;
        proof {
            let given = pages;
            let keys = set![tb, (tb + 1) as usize];
            assert forall|i: usize| #[trigger] keys.contains(i) implies given.dom().contains(i) by {
                assert(holds(given, i));
            }
            thread_pages = pages.tracked_remove_keys(keys);
            assert forall|i: usize| pb <= i < pb + 8 || lb <= i < lb + 2 implies #[trigger] holds(pages, i) by {
                assert(holds(given, i));
                assert(!keys.contains(i));
            }
            assert forall|i: usize| tb <= i < tb + 2 implies #[trigger] holds(thread_pages, i) by {
                assert(holds(given, i));
                assert(keys.contains(i));
            }
        }
        self.boot_root_process(root, process, leaf, Tracked(pages));
        let ghost mid = *self;
        proof {
            assert forall|i: int| tb <= i < tb + 2 implies #[trigger] mid.blocks.pages@[i].kind is Reserved by {
                assert(mid.blocks.pages@[i] == pre.blocks.pages@[i]);
            }
            assert(!mid.blocks.covered(tb as int)) by {
                assert(!pre.blocks.regions_2m@[region_2m(tb as int)].typed);
                assert(!pre.blocks.regions_1g@[region_1g(tb as int)].typed);
            }
            assert(!(tb <= root / 4096 < tb + 2)) by (nonlinear_arith)
                requires
                    tb * 4096 == t,
                    !(t <= root < t + 8192),
            ;
            assert forall|p: usize| #[trigger] mid.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
                implies !(tb <= p / 4096 < tb + 2) by {
                assert(mid.list.pages@.dom() == set![root, leaf]);
                assert(p == root || p == leaf);
            }
        }
        self.boot_root_thread(root, process, leaf, t, Tracked(thread_pages));
        proof {
            let post = *self;
            let a = (leaf + 1) as usize;
            let b = (leaf + 2) as usize;
            assert(post.tables.has_slot(&post.list, process, ROOT_PROCESS_SLOT));
            assert(post.tables.node_of(process, ROOT_PROCESS_SLOT) == a);
            assert(post.list.nodes@[a as int].live);
            assert(has(post.list.seq@, a));
            lemma_has(post.list.seq@, a);
            assert(post.list.is_child(root, a));
            post.lemma_slot(process, ROOT_PROCESS_SLOT);
            lemma_slot_in_leaf(leaf, 1);
            lemma_slot_in_leaf(leaf, 2);
            lemma_slot_in_leaf(leaf, 3);
            mid.lemma_slot_bound((leaf + 3) as usize);
            assert(!post.list.nodes@[leaf + 3].live) by {
                assert(leaf + 3 != t);
                assert(!mid.list.nodes@[leaf + 3].live);
            }
            assert forall|x: usize| #[trigger] post.is_cap(x) implies x == a || x == b by {
                if x != b {
                    assert(mid.is_cap(x));
                }
            }
            Self::lemma_root_reach(post, process, leaf, t);
            assert(post.list.nodes@[leaf as int].live);
            assert(has(post.list.seq@, leaf));
            lemma_has(post.list.seq@, leaf);
            assert(post.list.is_child(root, leaf));
        }
    }

    /// The step after boot_root: the root's console capability at ROOT_CONSOLE_SLOT, below the list's
    /// synthetic root as its process and thread capabilities are. The console is no block and carries
    /// no control, so the root's reach grows by the console's object alone, and nobody else's by
    /// anything else. See design/root-process-at-boot/.
    pub fn boot_root_console(&mut self, root: usize, process: usize, leaf: usize)
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.has_slot(&old(self).list, process, ROOT_PROCESS_SLOT),
            old(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
            !old(self).list.nodes@[leaf + 3].live,
        ensures
            final(self).wf(),
            final(self).list.seq@[0] == root,
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.has_slot(&final(self).list, process, ROOT_CONSOLE_SLOT),
            final(self).tables.node_of(process, ROOT_CONSOLE_SLOT) == leaf + 3,
            final(self).is_cap((leaf + 3) as usize),
            final(self).payload_of((leaf + 3) as usize) == console_payload(),
            final(self).list.is_child(root, (leaf + 3) as usize),
            final(self).list.nodes@[leaf + 3].depth == 1,
            Self::adds_cap(*old(self), *final(self), (leaf + 3) as usize),
            final(self).blocks == old(self).blocks,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            final(self).list.pages@.dom() == old(self).list.pages@.dom(),
            forall|o: usize| #[trigger] final(self).view().reach(process, o)
                <==> (old(self).view().reach(process, o) || o == CONSOLE_OBJECT),
            forall|r: usize, o: usize| #[trigger] final(self).view().reach(r, o) && !old(self).view().reach(r, o)
                ==> o == CONSOLE_OBJECT,
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_slot(process, ROOT_PROCESS_SLOT);
            assert(index_entry(ROOT_PROCESS_SLOT) == 0) by (compute_only);
            assert(index_slot(ROOT_PROCESS_SLOT) == 1) by (compute_only);
            assert(index_entry(ROOT_CONSOLE_SLOT) == 0) by (compute_only);
            assert(index_slot(ROOT_CONSOLE_SLOT) == 3) by (compute_only);
            assert(index_ok(ROOT_CONSOLE_SLOT)) by (compute_only);
            assert(pre.tables.leaf(process, 0) == leaf);
            assert(pre.tables.has_slot(&pre.list, process, ROOT_CONSOLE_SLOT));
            pre.lemma_slot(process, ROOT_CONSOLE_SLOT);
            assert(pre.tables.node_of(process, ROOT_CONSOLE_SLOT) == leaf + 3);
            pre.lemma_slot_bound((leaf + 3) as usize);
            pre.list.lemma_link(0);
            pre.list.lemma_live_valid(root);
            pre.list.lemma_valid_bound(root);
            pre.list.lemma_seq_fits();
            assert(pre.list.nodes@[root as int].depth == 0);
        }
        let child = leaf + 3;
        self.list.derive(root, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            process,
            ROOT_CONSOLE_SLOT,
            Payload { kind: CapKind::Console, order: 0, rights: CONSOLE_RIGHTS, base: CONSOLE_OBJECT, badge: 0, reserved: 0 },
        );
        proof {
            let post = *self;
            assert(post.payload_of(child) == console_payload());
            assert(0u32 & 128u32 == 0) by (bit_vector);
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_hidden_frame(pre, post, child, child);
            Self::lemma_table_nodes_caps_frame(pre, post, child, child);
            Self::lemma_space_nodes_caps_frame(pre, post, child, child);
            Self::lemma_bindings_caps_frame(pre, post, child, child);
            Self::lemma_add_untracked_holders(pre, post, child);
            Self::lemma_devices_caps_frame(pre, post, child, child);
            lemma_parents_derived(pre.list, post.list, root, child);
            Self::lemma_tlb_same(pre, post);
            assert(post.wf());
            Self::lemma_derive_step_adds_cap(pre, post, child);
            lemma_has(post.list.seq@, child);
            assert(post.list.is_child(root, child));
            Self::lemma_boot_held_view(pre, post, root, process, ROOT_CONSOLE_SLOT, child);
            Self::lemma_console_covers(post, child);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            lemma_adds_held_reach(pre.view(), post.view(), process, root, child, live);
            assert forall|o: usize| #[trigger] post.view().reach(process, o)
                <==> (pre.view().reach(process, o) || o == CONSOLE_OBJECT) by {
                assert(post.view().covers(child, o) == (o == CONSOLE_OBJECT));
            }
            assert forall|r: usize, o: usize| #[trigger] post.view().reach(r, o) && !pre.view().reach(r, o)
                implies o == CONSOLE_OBJECT by {
                assert(post.view().covers(child, o) == (o == CONSOLE_OBJECT));
            }
        }
    }

    /// The view of a boot step that puts a capability in slot i of the root's table, without control,
    /// below the list's first node, which no table holds.
    proof fn lemma_boot_held_view(pre: Self, post: Self, root: usize, process: usize, i: usize, child: usize)
        requires
            Self::adds_cap(pre, post, child),
            root == pre.list.seq@[0],
            pre.tables.has_slot(&pre.list, process, i),
            pre.tables.node_of(process, i) == child,
            post.list.parent@ == pre.list.parent@.insert(child, root),
            post.is_cap(child),
            post.payload_of(child).rights & CONTROL_RIGHT == 0,
        ensures
            adds_held(pre.view(), post.view(), process, root, child, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live),
    {
        let (a, b) = (pre.view(), post.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        pre.lemma_slot(process, i);
        pre.lemma_slot_bound(child);
        pre.list.lemma_link(0);
        pre.list.lemma_live_valid(root);
        pre.list.lemma_valid_bound(root);
        assert(live(root));
        assert(!live(child));
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) by {
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies live(x) by {
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies live(a.parent[x]) by {
            pre.list.lemma_parent_live(x);
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) == (a.held.contains(h) || h == (process, child)) by {
            if h.1 != child {
                assert(post.is_cap(h.1) == pre.is_cap(h.1));
            }
        }
        assert forall|x: NodeId| x != child implies {
            &&& #[trigger] b.names.contains_key(x) == a.names.contains_key(x)
            &&& b.pages.contains_key(x) == a.pages.contains_key(x)
            &&& a.names.contains_key(x) ==> b.names[x] == a.names[x]
            &&& a.pages.contains_key(x) ==> b.pages[x] == a.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| x != child implies #[trigger] b.rights.contains((x, r)) == a.rights.contains((x, r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert(!b.rights.contains((child, Right::Control)));
        assert(b.parent == a.parent.insert(child, root));
        assert(adds_held(a, b, process, root, child, live));
    }

    /// The console's capability covers the console's object alone.
    proof fn lemma_console_covers(s: Self, child: usize)
        requires
            s.is_cap(child),
            s.payload_of(child) == console_payload(),
        ensures
            forall|o: ObjectId| #[trigger] s.view().covers(child, o) <==> o == CONSOLE_OBJECT,
    {
        let b = s.view();
        assert(pow2(0) == 1) by { lemma2_to64(); }
        assert(b.names[child] == CONSOLE_OBJECT && b.pages[child] == 1);
        assert(CONSOLE_OBJECT % 4096 == 0) by (compute_only);
        assert forall|o: ObjectId| #[trigger] b.covers(child, o) <==> o == CONSOLE_OBJECT by {
            if b.covers(child, o) {
                assert(CONSOLE_OBJECT <= o < CONSOLE_OBJECT + 4096);
                assert(o == CONSOLE_OBJECT) by (nonlinear_arith)
                    requires
                        CONSOLE_OBJECT <= o < CONSOLE_OBJECT + 4096,
                        o % 4096 == 0,
                        CONSOLE_OBJECT % 4096 == 0,
                ;
            }
        }
    }

    /// The step after boot_root_console, once per block of free memory: an untyped capability to the
    /// block at base, of order pages, in slot i of the root's first leaf, below the list's synthetic
    /// root as the root's other capabilities are. It carries the retype right and no control, so the
    /// root's reach grows by the block's pages and nobody else's by anything outside them. See
    /// design/root-process-at-boot/ and design/untyped-memory/.
    pub fn boot_root_untyped(&mut self, root: usize, process: usize, leaf: usize, i: usize, base: usize, order: u8)
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.has_slot(&old(self).list, process, ROOT_PROCESS_SLOT),
            old(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
            ROOT_CONSOLE_SLOT < i < NODES_PER_PAGE,
            !old(self).list.nodes@[leaf + i].live,
            payload_wf(untyped_payload(base, order)),
        ensures
            final(self).wf(),
            final(self).list.seq@[0] == root,
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.has_slot(&final(self).list, process, ROOT_PROCESS_SLOT),
            final(self).tables.node_of(process, ROOT_PROCESS_SLOT) == leaf + 1,
            final(self).tables.has_slot(&final(self).list, process, i),
            final(self).tables.node_of(process, i) == leaf + i,
            final(self).is_cap((leaf + i) as usize),
            final(self).payload_of((leaf + i) as usize) == untyped_payload(base, order),
            final(self).list.is_child(root, (leaf + i) as usize),
            final(self).list.nodes@[leaf + i].depth == 1,
            Self::adds_cap(*old(self), *final(self), (leaf + i) as usize),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j != leaf + i
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live
                && final(self).list.nodes@[j].depth == old(self).list.nodes@[j].depth,
            final(self).list.parent@ == old(self).list.parent@.insert((leaf + i) as usize, root),
            final(self).blocks == old(self).blocks,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            final(self).list.pages@.dom() == old(self).list.pages@.dom(),
            forall|o: usize| #[trigger] final(self).view().reach(process, o)
                <==> (old(self).view().reach(process, o) || in_block(base, order, o)),
            forall|r: usize, o: usize| #[trigger] final(self).view().reach(r, o) && !old(self).view().reach(r, o)
                ==> in_block(base, order, o),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_slot(process, ROOT_PROCESS_SLOT);
            assert(index_entry(ROOT_PROCESS_SLOT) == 0) by (compute_only);
            assert(index_slot(ROOT_PROCESS_SLOT) == 1) by (compute_only);
            assert(index_entry(i) == 0);
            assert(index_slot(i) == i);
            assert(index_ok(i));
            assert(pre.tables.leaf(process, 0) == leaf);
            assert(pre.tables.has_slot(&pre.list, process, i));
            pre.lemma_slot(process, i);
            assert(pre.tables.node_of(process, i) == leaf + i);
            pre.lemma_slot_bound((leaf + i) as usize);
            pre.list.lemma_link(0);
            pre.list.lemma_live_valid(root);
            pre.list.lemma_valid_bound(root);
            pre.list.lemma_seq_fits();
            assert(pre.list.nodes@[root as int].depth == 0);
        }
        let child = leaf + i;
        self.list.derive(root, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            process,
            i,
            Payload { kind: CapKind::Untyped, order, rights: UNTYPED_RIGHTS, base, badge: 0, reserved: 0 },
        );
        proof {
            let post = *self;
            assert(post.payload_of(child) == untyped_payload(base, order));
            assert(UNTYPED_RIGHTS & CONTROL_RIGHT == 0) by (compute_only);
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_hidden_frame(pre, post, child, child);
            Self::lemma_table_nodes_caps_frame(pre, post, child, child);
            Self::lemma_space_nodes_caps_frame(pre, post, child, child);
            Self::lemma_bindings_caps_frame(pre, post, child, child);
            Self::lemma_add_untracked_holders(pre, post, child);
            Self::lemma_devices_caps_frame(pre, post, child, child);
            lemma_parents_derived(pre.list, post.list, root, child);
            Self::lemma_tlb_same(pre, post);
            assert(post.wf());
            Self::lemma_derive_step_adds_cap(pre, post, child);
            lemma_has(post.list.seq@, child);
            assert(post.list.is_child(root, child));
            assert(post.tables.has_slot(&post.list, process, ROOT_PROCESS_SLOT));
            assert(post.tables.has_slot(&post.list, process, i));
            Self::lemma_boot_held_view(pre, post, root, process, i, child);
            Self::lemma_untyped_covers(post, child, base, order);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            lemma_adds_held_reach(pre.view(), post.view(), process, root, child, live);
            assert forall|o: usize| #[trigger] post.view().reach(process, o)
                <==> (pre.view().reach(process, o) || in_block(base, order, o)) by {
                assert(post.view().covers(child, o) == in_block(base, order, o));
            }
            assert forall|r: usize, o: usize| #[trigger] post.view().reach(r, o) && !pre.view().reach(r, o)
                implies in_block(base, order, o) by {
                assert(post.view().covers(child, o) == in_block(base, order, o));
            }
        }
    }

    /// An untyped capability covers exactly its block's pages.
    proof fn lemma_untyped_covers(s: Self, child: usize, base: usize, order: u8)
        requires
            s.is_cap(child),
            s.payload_of(child) == untyped_payload(base, order),
        ensures
            forall|o: ObjectId| #[trigger] s.view().covers(child, o) <==> in_block(base, order, o),
    {
        let b = s.view();
        assert(b.names[child] == base && b.pages[child] == pow2(order as nat));
    }

    /// The root's reach after boot: it holds exactly its process and thread capabilities, each naming
    /// its block, and nobody else holds anything, so it reaches exactly the pages of those blocks.
    proof fn lemma_root_reach(s: Self, process: usize, leaf: usize, t: usize)
        requires
            forall|x: usize| #[trigger] s.is_cap(x) ==> x == leaf + 1 || x == leaf + 2,
            s.is_cap((leaf + 1) as usize),
            s.is_cap((leaf + 2) as usize),
            s.payload_of((leaf + 1) as usize) == process_of(process),
            s.payload_of((leaf + 2) as usize) == thread_of(t),
            page_of((leaf + 1) as usize) == leaf,
            page_of((leaf + 2) as usize) == leaf,
            s.tables.owner@[leaf].0 == process,
            process % 4096 == 0,
            t % 4096 == 0,
        ensures
            forall|o: usize| #[trigger] s.view().reach(process, o)
                <==> (o % 4096 == 0 && ((process <= o < process + 32768) || (t <= o < t + 8192))),
    {
        let v = s.view();
        let a = (leaf + 1) as usize;
        let b = (leaf + 2) as usize;
        lemma2_to64();
        assert(v.names[a] == process && v.pages[a] == 8);
        assert(v.names[b] == t && v.pages[b] == 2);
        assert(v.holds(process, a));
        assert(v.holds(process, b));
        // Only the process and its thread are controlled: every control capability names one of them.
        assert forall|q: usize, k: nat| #[trigger] v.controlled(process, q, k) implies q == process || q == t by {
            if k > 0 {
                let m = choose|m: usize| #[trigger] v.controls(m, q) && v.controlled(process, m, (k - 1) as nat);
                let c = choose|c: usize| #[trigger] v.holds_right(m, c, Right::Control) && v.process_behind(v.names[c]) == q;
                assert(s.is_cap(c));
            }
        }
        assert forall|o: usize| #[trigger] v.reach(process, o)
            <==> (o % 4096 == 0 && ((process <= o < process + 32768) || (t <= o < t + 8192))) by {
            if v.reach(process, o) {
                let (q, k) = choose|q: usize, k: nat| #[trigger] v.controlled(process, q, k) && (o == q || v.direct(q, o));
                assert(q == process || q == t);
                if o != q {
                    assert(!v.maps.contains((q, o)));
                    let (c, n, j) = choose|c: usize, n: usize, j: nat| #[trigger] v.descends(c, n, j) && v.holds(q, c) && v.covers(n, o);
                    assert(s.is_cap(n));
                }
            }
            if o % 4096 == 0 && process <= o < process + 32768 {
                assert(v.descends(a, a, 0));
                assert(v.covers(a, o));
                assert(v.direct(process, o));
                assert(v.controlled(process, process, 0));
            }
            if o % 4096 == 0 && t <= o < t + 8192 {
                assert(v.descends(b, b, 0));
                assert(v.covers(b, o));
                assert(v.direct(process, o));
                assert(v.controlled(process, process, 0));
            }
        }
    }

    /// The thread's block typed and its capability written below the synthetic root, before the thread
    /// is bound: the state is well formed, as after type_thread, whose proof this follows with the
    /// synthetic root in place of an untyped.
    proof fn lemma_boot_thread_typed(pre: Self, post: Self, mid: Tree, root: usize, process: usize, leaf: usize, t: usize)
        requires
            pre.wf(),
            root == pre.list.seq@[0],
            root < NODE_SPACE,
            pre.list.valid(root),
            pre.list.nodes@[root as int].live,
            pre.list.nodes@[root as int].kind is Capability,
            pre.list.nodes@[root as int].depth == 0,
            leaf % 8192 == 0,
            pre.tables.has_slot(&pre.list, process, ROOT_THREAD_SLOT),
            pre.tables.node_of(process, ROOT_THREAD_SLOT) == leaf + 2,
            page_of((leaf + 2) as usize) == leaf,
            ((leaf + 2) as usize) % 4096 == 2,
            pre.tables.owner@.contains_key(leaf),
            (leaf + 2) < NODE_SPACE,
            pre.list.valid((leaf + 2) as usize),
            !pre.list.nodes@[leaf + 2].live,
            t % 8192 == 0,
            (t / 4096) * 4096 == t,
            (t / 4096) % 2 == 0,
            t / 4096 + 2 <= NUM_PAGES,
            forall|k: int| 0 <= k < 2 ==> #[trigger] pre.blocks.pages@[t / 4096 + k].kind is Free,
            !pre.blocks.covered((t / 4096) as int),
            !pre.list.pages@.dom().contains(t),
            // The list: t's node page added, then the capability derived below the root.
            list_grown(pre.list, mid),
            mid.wf(),
            mid.pages@.dom() == pre.list.pages@.dom().insert(t),
            !mid.nodes@[t as int].live,
            post.list.wf(),
            post.list.is_child(root, (leaf + 2) as usize),
            post.list.parent@ == mid.parent@.insert((leaf + 2) as usize, root),
            post.list.pages@.dom() == mid.pages@.dom(),
            post.list.nodes@[leaf + 2].live,
            post.list.nodes@[leaf + 2].kind == NodeKind::Capability,
            post.list.nodes@[leaf + 2].depth == 1,
            post.list.seq@[0] == mid.seq@[0],
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != leaf + 2 ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
                &&& post.list.nodes@[i].depth == mid.nodes@[i].depth
            },
            // The blocks: the two free pages typed as a thread.
            post.blocks.wf(),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[(t / 4096) as int].kind is Base,
            post.blocks.pages@[(t / 4096) as int].object is Thread,
            post.blocks.pages@[(t / 4096) as int].order == 1,
            post.blocks.pages@[(t / 4096) as int].refs == 1,
            !post.blocks.pages@[(t / 4096) as int].dead,
            forall|k: int| 0 < k < 2 ==> (#[trigger] post.blocks.pages@[t / 4096 + k]).object is None,
            forall|i: int| 0 <= i < NUM_PAGES && !(t / 4096 <= i < t / 4096 + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            // The tables: the capability in slot 2.
            post.tables.wf(&post.list),
            post.tables.roots == pre.tables.roots,
            post.tables.owner == pre.tables.owner,
            post.tables.payload_of((leaf + 2) as usize) == thread_of(t),
            forall|x: usize| #![trigger post.tables.payload_of(x)]
                x != leaf + 2 && x % 4096 < NODES_PER_PAGE && pre.tables.owner@.contains_key(page_of(x))
                ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            // The thread.
            post.threads.records@ == pre.threads.records@.insert(t, post.threads.records@[t]),
            post.threads.records@[t].addr() == t + THREAD_RECORD_PAGE * 4096,
            post.threads.records@[t].is_init(),
            post.threads.records@[t].value() == fresh_thread(),
            post.threads.holders@ == pre.threads.holders@.insert(t, set![(leaf + 2) as usize]),
            // Everything else is as it was.
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.zeroing == pre.zeroing,
            post.holders == pre.holders,
            post.devices == pre.devices,
            post.processes == pre.processes,
            post.stop_ipis == pre.stop_ipis,
        ensures
            post.wf(),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> {
                &&& post.is_cap(x)
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
                &&& post.list.parent@[x] == pre.list.parent@[x]
            },
            post.is_cap((leaf + 2) as usize),
            forall|x: usize| #[trigger] post.is_cap(x) ==> x == leaf + 2 || pre.is_cap(x),
            !post.list.nodes@[t as int].live,
    {
        let base = t;
        let page = t / 4096;
        let parent = root;
        let child = (leaf + 2) as usize;
        assert forall|x: usize| #[trigger] pre.list.valid(x) && x != child implies {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        } by {
            assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
            pre.list.lemma_valid_bound(x);
        }
        assert(Self::space_step(pre, post, child));
        assert(post.payload_of(child) == thread_of(base));
        lemma2_to64();
        assert(block_bytes(THREAD_ORDER) == 8192);
        assert(payload_wf(post.payload_of(child)));
        assert(post.is_cap(child));
        Self::lemma_space_caps_wf(pre, post, child);
        Self::lemma_tlb_same(pre, post);
        Self::lemma_space_nodes(pre, post, mid, parent, child);
        Self::lemma_table_nodes_frame(pre, post, child, child);
        Self::lemma_space_nodes_frame(pre, post, child, child);
        lemma_mapping_nodes_grown(pre.list, mid, post.list, child, child);
        assert(post.list.pages@.dom() == pre.list.pages@.dom().insert(base));
        assert forall|k: int| 0 < k < 2 implies (#[trigger] post.blocks.pages@[page + k]).kind is Member by {
            post.blocks.lemma_member_of(page as int, page + k);
        }
        Self::lemma_thread_blocks(pre, post, base, page, child);
        assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Space) by {
            if k == 0 {
                assert(post.blocks.pages@[page as int].object is Thread);
            }
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Space implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Space implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        lemma_spaces_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page, 2);
        assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Process) by {
            if k == 0 {
                assert(post.blocks.pages@[page as int].object is Thread);
            }
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Process implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Process implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        lemma_processes_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page, 2);
        Self::lemma_threads_thread_added(pre, post, base, page, child);
        assert(!pre.threads.records@.contains_key(base)) by {
            if pre.threads.records@.contains_key(base) {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, base));
                assert(pre.blocks.pages@[page + 0int].kind is Free);
            }
        }
        assert(current_wf(post.cores@, post.threads.records@)) by {
            reveal(current_wf);
            assert forall|c: int, x: usize| 0 <= c < NUM_CPUS && #[trigger] runs(post.cores@, c, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (crate::capability::thread::ThreadState::Running { core: c as usize })
            } by {
                assert(runs(pre.cores@, c, x));
                assert(x != base);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(x != base);
                assert(pre.threads.records@.contains_key(x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                if x == base {
                    assert(post.threads.records@[base].value() == fresh_thread());
                } else {
                    assert(pre.threads.records@.contains_key(x));
                }
            }
        }
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
            implies post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n] by {
            pre.lemma_mapping_node(n);
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
            &&& post.is_cap(x)
            &&& post.payload_of(x) == pre.payload_of(x)
            &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
            &&& post.list.parent@[x] == pre.list.parent@[x]
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
            pre.lemma_slot_bound(x);
            assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
        }
        Self::lemma_mappings_grown(pre, post, page, 1);
        assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
            implies pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x) by {
            assert(x != child);
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        Self::lemma_devices_same_caps(pre, post);
        lemma_binding_nodes_grown(pre.list, mid, post.list, child, child);
        lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
        Self::lemma_binding_parents_same_caps(pre, post);
        assert(post.wf());
        assert forall|x: usize| #[trigger] post.is_cap(x) implies x == child || pre.is_cap(x) by {
            if x != child {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
        }
        assert(post.list.nodes@[t as int].live == mid.nodes@[t as int].live) by {
            assert(t as int != leaf + 2);
        }
    }

    /// The kernel after boot hands reserved pages start to start + n to the block table. No object,
    /// frame or list page lies in a reserved page, so every clause reads what it read before.
    proof fn lemma_reserved_freed(pre: Self, post: Self, start: usize, n: usize)
        requires
            pre.wf(),
            post.blocks.wf(),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            start + n <= NUM_PAGES,
            forall|i: int| start <= i < start + n ==> #[trigger] pre.blocks.pages@[i].kind is Reserved,
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] post.blocks.pages@[i]
                == if start <= i < start + n { free_entry() } else { pre.blocks.pages@[i] },
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
                ==> !(start <= p / 4096 < start + n),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.frames == pre.frames,
            post.zeroing == pre.zeroing,
            post.holders == pre.holders,
            post.stop_ipis == pre.stop_ipis,
        ensures
            post.wf(),
    {
        let a = pre.blocks;
        let b = post.blocks;
        // A base or a member, before or after, is the same entry: the freed pages were neither.
        assert forall|i: int| 0 <= i < NUM_PAGES && ((#[trigger] b.pages@[i]).kind is Base || b.pages@[i].kind is Member
            || a.pages@[i].kind is Base || a.pages@[i].kind is Member) implies b.pages@[i] == a.pages@[i] by {
            if start <= i < start + n {
                assert(a.pages@[i].kind is Reserved);
            }
        }
        assert forall|i: usize| i < NUM_PAGES implies #[trigger] block_ref(&b, i) == block_ref(&a, i) by {
            if start <= i < start + n {
                assert(a.pages@[i as int].kind is Reserved);
            }
        }
        assert forall|br: BlockRef| #[trigger] block_typed(&b, br) == block_typed(&a, br) by {
            match br {
                BlockRef::Small(x) => {
                    if x < NUM_PAGES && start <= x < start + n {
                        assert(a.pages@[x as int].kind is Reserved);
                    }
                },
                _ => {},
            }
        }
        assert forall|br: BlockRef| #[trigger] block_typed(&a, br) implies {
            &&& block_refs(&b, br) == block_refs(&a, br)
            &&& block_dead(&b, br) == block_dead(&a, br)
        } by {
            match br {
                BlockRef::Small(x) => {
                    assert(b.pages@[x as int] == a.pages@[x as int]);
                },
                _ => {},
            }
        }
        assert(list_pages_used(&post.list, &b)) by {
            assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
                &&& !(b.pages@[(p / 4096) as int].kind is Free)
                &&& b.pages@[(p / 4096) as int].kind is Member
                    ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
                        || b.pages@[b.pages@[(p / 4096) as int].base as int].object is Space
                &&& !(b.pages@[(p / 4096) as int].object is Frame)
            } by {
                let x = (p / 4096) as int;
                assert(b.pages@[x] == a.pages@[x]);
                if a.pages@[x].kind is Member {
                    a.lemma_member(x);
                    let y = a.pages@[x].base as int;
                    assert(b.pages@[y] == a.pages@[y]);
                }
            }
        }
        assert(holders_wf(&post.list, &post.tables, &b, &post.zeroing, post.holders@)) by {
            assert forall|m: usize| #[trigger] post.tables.is_cap(&post.list, m) && post.tables.payload_of(m).kind is Frame implies {
                let i = post.tables.payload_of(m).base / 4096;
                &&& i < NUM_PAGES
                &&& frame_in_block(block_ref(&b, i), post.tables.payload_of(m))
                &&& post.holders@.contains_key(block_ref(&b, i))
                &&& post.holders@[block_ref(&b, i)].contains(m)
            } by {
                assert(pre.tables.is_cap(&pre.list, m));
            }
            assert forall|br: BlockRef| #[trigger] post.holders@.contains_key(br) implies {
                &&& post.holders@[br].finite()
                &&& post.holders@[br].len() == block_refs(&b, br)
                &&& block_typed(&b, br)
                &&& block_refs(&b, br) == 0 ==> block_dead(&b, br)
                &&& !block_active(&post.zeroing, br)
            } by {
                assert(pre.holders@.contains_key(br));
                assert(block_typed(&a, br));
            }
            assert forall|br: BlockRef, m: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(m) implies ({
                &&& post.tables.is_cap(&post.list, m)
                &&& post.tables.payload_of(m).kind is Frame
                &&& post.tables.payload_of(m).base / 4096 < NUM_PAGES
                &&& block_ref(&b, post.tables.payload_of(m).base / 4096) == br
            } || (m < NODE_SPACE && post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Mapping)) by {
                assert(pre.holders@[br].contains(m));
                if pre.tables.is_cap(&pre.list, m) && pre.tables.payload_of(m).kind is Frame && pre.tables.payload_of(m).base / 4096 < NUM_PAGES
                    && block_ref(&a, pre.tables.payload_of(m).base / 4096) == br {
                    assert(block_ref(&b, pre.tables.payload_of(m).base / 4096) == br);
                }
            }
        }
        assert(objects_wf(&post.tables, &b, post.holders@)) by {
            assert forall|x: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(x)) implies b.pages@[x as int].object is Frame by {
                assert(block_typed(&a, BlockRef::Small(x)));
                assert(b.pages@[x as int] == a.pages@[x as int]);
            }
            assert forall|x: usize| x < NUM_PAGES && (#[trigger] b.pages@[x as int]).kind is Base
                && b.pages@[x as int].object is Frame implies {
                &&& b.pages@[x as int].order == 0
                &&& b.pages@[x as int].refs == 0 ==> post.holders@.contains_key(BlockRef::Small(x))
            } by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
            }
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
                &&& l / 4096 < NUM_PAGES
                &&& b.pages@[(l / 4096) as int].kind is Base
                &&& b.pages@[(l / 4096) as int].object is TableLeaf
                &&& b.pages@[(l / 4096) as int].order == 1
            } by {
                assert(a.pages@[(l / 4096) as int].kind is Base);
            }
            assert forall|x: usize| x < NUM_PAGES && #[trigger] leaf_block(&b, x)
                implies post.tables.owner@.contains_key((x * 4096) as usize) by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(leaf_block(&a, x));
            }
        }
        assert(leaf_blocks_wf(&post.list, &post.tables, &b)) by {
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
                &&& post.list.nodes@[l as int].live ==> {
                    &&& post.list.nodes@[l as int].kind is Hidden
                    &&& b.pages@[(l / 4096) as int].refs == 1
                    &&& !b.pages@[(l / 4096) as int].dead
                }
                &&& !post.list.nodes@[l as int].live ==> {
                    &&& b.pages@[(l / 4096) as int].refs == 0
                    &&& b.pages@[(l / 4096) as int].dead
                }
            } by {
                assert(a.pages@[(l / 4096) as int].kind is Base);
            }
        }
        assert(table_pages_wf(&post.list, &post.table_pages, &b)) by {
            assert forall|u: usize| #[trigger] post.table_pages.maps@.contains_key(u) implies table_page_wf(&post.list, &post.table_pages, &b, u) by {
                assert(table_page_wf(&pre.list, &pre.table_pages, &a, u));
                assert(a.pages@[(u / 4096) as int].kind is Base);
            }
            assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(&b, x)
                implies post.table_pages.maps@.contains_key((x * 4096) as usize) by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(table_block(&a, x));
            }
        }
        assert(spaces_wf(&post.list, &post.tables, &post.spaces, &b)) by {
            assert forall|s: usize| #[trigger] post.spaces.roots@.contains_key(s) implies space_wf(&post.list, &post.spaces, &b, s) by {
                assert(space_wf(&pre.list, &pre.spaces, &a, s));
                assert(a.pages@[(s / 4096) as int].kind is Base);
            }
            assert forall|x: usize| x < NUM_PAGES && #[trigger] space_block(&b, x)
                implies post.spaces.roots@.contains_key((x * 4096) as usize) by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(space_block(&a, x));
            }
        }
        assert(threads_wf(&post.list, &post.tables, &post.threads, &b)) by {
            assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u) implies thread_wf(&post.list, &post.threads, &b, u) by {
                assert(thread_wf(&pre.list, &pre.threads, &a, u));
                assert(a.pages@[(u / 4096) as int].kind is Base);
            }
            assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(&b, x)
                implies post.threads.records@.contains_key((x * 4096) as usize) by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(thread_block(&a, x));
            }
        }
        assert(processes_wf(&post.list, &post.tables, &post.processes, &b)) by {
            assert forall|p: usize| #[trigger] post.processes.records@.contains_key(p) implies process_wf(&post.processes, &b, p) by {
                assert(process_wf(&pre.processes, &a, p));
                assert(a.pages@[(p / 4096) as int].kind is Base);
            }
            assert forall|x: usize| x < NUM_PAGES && #[trigger] process_block(&b, x)
                implies post.processes.records@.contains_key((x * 4096) as usize) by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(process_block(&a, x));
            }
        }
        assert forall|i: usize| i < NUM_PAGES && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
            && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
            implies #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i) by {}
        Self::lemma_blocks_changed(pre, post);
    }

    /// The state after the first boot step is well formed. Everything in it is new, so each part of the
    /// invariant reads one process, one space, one leaf and three nodes.
    proof fn lemma_boot_root_process(
        pre: Self,
        post: Self,
        root: usize,
        base: usize,
        leaf: usize,
        l0: Tree,
        l1: Tree,
        l2: Tree,
        l3: Tree,
        freed: BlockTable,
        leaf_typed: BlockTable,
    )
        requires
            pre.wf(),
            pre.boot_empty(),
            root == pre.list.seq@[0],
            base % 32768 == 0,
            base / 4096 + 8 <= NUM_PAGES,
            leaf % 8192 == 0,
            leaf != NO_LEAF,
            leaf / 4096 + 2 <= NUM_PAGES,
            base + 32768 <= leaf || leaf + 8192 <= base,
            !(base <= root < base + 32768),
            !(leaf <= root < leaf + 8192),
            (base / 4096) * 4096 == base,
            (leaf / 4096) * 4096 == leaf,
            (leaf / 4096) % 2 == 0,
            (base / 4096) % 8 == 0,
            page_of(leaf) == leaf,
            page_of((leaf + 1) as usize) == leaf,
            ((leaf + 1) as usize) % 4096 == 1,
            // The list: the synthetic root, then the leaf's page, its hidden node and the capability.
            l0 == pre.list,
            l1.wf(),
            l1.seq == l0.seq,
            l1.parent == l0.parent,
            l1.pages@.dom() == l0.pages@.dom().insert(leaf),
            forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] l1.nodes@[i].live == l0.nodes@[i].live,
            forall|i: usize| #[trigger] l0.valid(i) ==> l1.valid(i) && l1.nodes@[i as int] == l0.nodes@[i as int],
            l2.wf(),
            l2.parent@ == l1.parent@.insert(leaf, root),
            l2.pages@.dom() == l1.pages@.dom(),
            l2.nodes@[leaf as int].live,
            l2.nodes@[leaf as int].kind == NodeKind::Hidden,
            l2.seq@[0] == root,
            forall|i: int| #![trigger l2.nodes@[i]] 0 <= i < NODE_SPACE && i != leaf ==> {
                &&& l2.nodes@[i].live == l1.nodes@[i].live
                &&& l2.nodes@[i].kind == l1.nodes@[i].kind
                &&& l2.nodes@[i].depth == l1.nodes@[i].depth
            },
            l3.wf(),
            l3.is_child(root, (leaf + 1) as usize),
            l3.parent@ == l2.parent@.insert((leaf + 1) as usize, root),
            l3.pages@.dom() == l2.pages@.dom(),
            l3.nodes@[leaf + 1].live,
            l3.nodes@[leaf + 1].kind == NodeKind::Capability,
            l3.nodes@[leaf + 1].depth == l2.nodes@[root as int].depth + 1,
            l3.seq@[0] == root,
            forall|i: int| #![trigger l3.nodes@[i]] 0 <= i < NODE_SPACE && i != leaf + 1 ==> {
                &&& l3.nodes@[i].live == l2.nodes@[i].live
                &&& l3.nodes@[i].kind == l2.nodes@[i].kind
                &&& l3.nodes@[i].depth == l2.nodes@[i].depth
            },
            l2.is_child(root, leaf),
            post.list == l3,
            // The blocks: ten reserved pages freed, then typed as a leaf and a process.
            freed.wf(),
            freed.regions_2m@ == pre.blocks.regions_2m@,
            freed.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] freed.pages@[i] == if (base / 4096 <= i < base / 4096 + 8 || leaf / 4096 <= i < leaf / 4096 + 2) { free_entry() } else { pre.blocks.pages@[i] },
            leaf_typed.wf(),
            leaf_typed.regions_2m@ == freed.regions_2m@,
            leaf_typed.regions_1g@ == freed.regions_1g@,
            leaf_typed.pages@[(leaf / 4096) as int].kind is Base,
            leaf_typed.pages@[(leaf / 4096) as int].object is TableLeaf,
            leaf_typed.pages@[(leaf / 4096) as int].order == 1,
            leaf_typed.pages@[(leaf / 4096) as int].refs == 1,
            !leaf_typed.pages@[(leaf / 4096) as int].dead,
            leaf_typed.pages@[leaf / 4096 + 1].object is None,
            forall|i: int| 0 <= i < NUM_PAGES && !(leaf / 4096 <= i < leaf / 4096 + 2) ==> #[trigger] leaf_typed.pages@[i] == freed.pages@[i],
            post.blocks.wf(),
            post.blocks.regions_2m@ == leaf_typed.regions_2m@,
            post.blocks.regions_1g@ == leaf_typed.regions_1g@,
            post.blocks.pages@[(base / 4096) as int].kind is Base,
            post.blocks.pages@[(base / 4096) as int].object is Process,
            post.blocks.pages@[(base / 4096) as int].order == 3,
            post.blocks.pages@[(base / 4096) as int].refs == 1,
            !post.blocks.pages@[(base / 4096) as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[base / 4096 + k]).object is None,
            forall|i: int| 0 <= i < NUM_PAGES && !(base / 4096 <= i < base / 4096 + 8) ==> #[trigger] post.blocks.pages@[i] == leaf_typed.pages@[i],
            // The tables: the process's root, with the leaf at entry 0 and the capability in slot 1.
            post.tables.wf(&post.list),
            post.tables.roots@.dom() == set![base],
            post.tables.leaf(base, 0) == leaf,
            post.tables.owner@ == Map::<usize, (usize, int)>::empty().insert(leaf, (base, 0int)),
            post.tables.payload_of((leaf + 1) as usize) == process_of(base),
            // The process and its space.
            post.processes.records@ == pre.processes.records@.insert(base, post.processes.records@[base]),
            post.processes.records@[base].addr() == base + PROCESS_RECORD_PAGE * 4096,
            post.processes.records@[base].is_init(),
            !post.processes.records@[base].value().dead,
            spare_kept(&post.processes, base, 2),
            spare_kept(&post.processes, base, 3),
            spare_kept(&post.processes, base, 4),
            post.processes.holders@ == pre.processes.holders@.insert(base, set![(leaf + 1) as usize]),
            post.processes.bound@ == pre.processes.bound@.insert(base, Set::<usize>::empty()),
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]),
            post.spaces.roots@[base].addr() == base + SPACE_ROOT_PAGE * 4096,
            post.spaces.roots@[base].is_init(),
            post.spaces.roots@[base].value().wf(),
            forall|i: usize| #![trigger post.spaces.roots@[base].value()[i]]
                KERNEL_MEM_END_L4INDEX <= i < 512 ==> post.spaces.roots@[base].value()[i].is_empty(),
            forall|i: usize| #![trigger post.spaces.roots@[base].value()[i]]
                i < KERNEL_MEM_END_L4INDEX ==> post.spaces.roots@[base].value()[i] == usize2page_entry(post.spaces.kernel_entries@[i as int]),
            post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]),
            post.spaces.records@[base].addr() == base + SPACE_RECORD_PAGE * 4096,
            post.spaces.records@[base].is_init(),
            post.spaces.records@[base].value() == (SpaceRecord {
                kind: SpaceKind::Process,
                root: (base + SPACE_ROOT_PAGE * 4096) as usize,
                table: TableRecord { level: 4, space: Some(base), parent: None, written: false },
            }),
            post.spaces.loaded@ == pre.spaces.loaded@.insert(base, post.spaces.loaded@[base]),
            post.spaces.loaded@[base].addr() == base + SPACE_CORES_PAGE * 4096,
            post.spaces.loaded@[base].is_init(),
            post.spaces.loaded@[base].value().list == 0u32,
            forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] post.spaces.loaded@[base].value().ids@[c] == 0usize,
            post.spaces.holders@ == pre.spaces.holders@.insert(base, Set::<usize>::empty()),
            post.spaces.bound@ == pre.spaces.bound@.insert(base, Set::<usize>::empty()),
            // Everything else is as init left it.
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.mappings == pre.mappings,
            post.zeroing == pre.zeroing,
            post.holders == pre.holders,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.stop_ipis == pre.stop_ipis,
        ensures
            post.wf(),
            post.is_cap((leaf + 1) as usize),
            post.list.is_child(root, leaf),
            post.list.nodes@[leaf + 1].depth == 1,
            post.list.nodes@[leaf as int].live,
            post.list.nodes@[leaf as int].kind is Hidden,
            forall|x: usize| #[trigger] post.is_cap(x) ==> x == leaf + 1,
            forall|k: int| 0 <= k < 8 ==> {
                ||| (#[trigger] post.blocks.pages@[base / 4096 + k]).kind is Base
                ||| post.blocks.pages@[base / 4096 + k].kind is Member
            },
            forall|k: int| 0 <= k < 2 ==> {
                ||| (#[trigger] post.blocks.pages@[leaf / 4096 + k]).kind is Base
                ||| post.blocks.pages@[leaf / 4096 + k].kind is Member
            },
            forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] post.loaded(c, base),
    {
        let cap = (leaf + 1) as usize;
        let pb = base / 4096;
        let lb = leaf / 4096;
        let list = post.list;
        let blocks = post.blocks;
        lemma2_to64();
        assert(block_bytes(3) == 32768);
        // Init's list holds its root alone.
        pre.list.lemma_link(0);
        assert forall|i: int| 0 <= i < NODE_SPACE implies #[trigger] l0.nodes@[i].live == (i == root as int) by {
            if l0.nodes@[i].live {
                lemma_has(l0.seq@, i as usize);
                let k = choose|k: int| 0 <= k < l0.seq@.len() && l0.seq@[k] == i as usize;
                assert(k == 0);
            }
        }
        assert(l0.valid(root));
        assert(l1.nodes@[root as int] == l0.nodes@[root as int]);
        assert(l0.nodes@[root as int].depth == 0);
        assert(l2.nodes@[root as int].depth == 0);
        assert(l0.nodes@[root as int].kind is Capability) by {
            assert(parents_are_capabilities(&pre.list));
        }
        assert(page_of(root) == root);
        assert(root != leaf);
        assert(root != cap);
        // The nodes after the step: the root, the leaf's hidden node and the capability.
        assert forall|i: int| 0 <= i < NODE_SPACE implies #[trigger] list.nodes@[i].live
            == (i == root as int || i == leaf as int || i == cap as int) by {
            if i != cap as int {
                assert(l3.nodes@[i].live == l2.nodes@[i].live);
                if i != leaf as int {
                    assert(l2.nodes@[i].live == l1.nodes@[i].live);
                }
            }
        }
        assert(list.nodes@[root as int].kind is Capability) by {
            assert(l3.nodes@[root as int].kind == l2.nodes@[root as int].kind);
            assert(l2.nodes@[root as int].kind == l1.nodes@[root as int].kind);
        }
        assert(list.nodes@[leaf as int].kind is Hidden) by {
            assert(l3.nodes@[leaf as int].kind == l2.nodes@[leaf as int].kind);
        }
        assert(list.nodes@[cap as int].kind is Capability);
        assert(list.parent@ == Map::<usize, usize>::empty().insert(leaf, root).insert(cap, root));
        assert(list.pages@.dom() == set![root].insert(leaf));
        assert forall|x: usize| #[trigger] list.seq@.contains(x) implies x == root || x == leaf || x == cap by {
            let k = choose|k: int| 0 <= k < list.seq@.len() && list.seq@[k] == x;
            list.lemma_link(k);
        }
        // The capabilities: the one in slot 1.
        assert forall|x: usize| #[trigger] post.is_cap(x) implies x == cap by {
            assert(page_of(x) == leaf);
            assert(x < NODE_SPACE);
            assert(list.nodes@[x as int].live);
        }
        assert(post.is_cap(cap));
        assert(list.is_child(root, leaf)) by {
            lemma_has(list.seq@, leaf);
        }
        // The blocks.
        assert forall|i: int| 0 <= i < NUM_PAGES && !(pb <= i < pb + 8) && !(lb <= i < lb + 2) implies {
            &&& (#[trigger] blocks.pages@[i]).kind is Reserved
            &&& blocks.pages@[i].object is None
        } by {
            assert(blocks.pages@[i] == leaf_typed.pages@[i]);
            assert(leaf_typed.pages@[i] == freed.pages@[i]);
        }
        assert(blocks.pages@[lb as int] == leaf_typed.pages@[lb as int]);
        assert forall|k: int| 0 < k < 8 implies (#[trigger] blocks.pages@[pb + k]).kind is Member by {
            blocks.lemma_member_of(pb as int, pb + k);
        }
        assert(blocks.pages@[lb + 1int].kind is Member) by {
            blocks.lemma_member_of(lb as int, lb + 1int);
        }
        assert(blocks.pages@[lb + 1int].object is None) by {
            assert(blocks.pages@[lb + 1int] == leaf_typed.pages@[lb + 1int]);
        }
        assert forall|i: int| 0 <= i < NUM_PAGES && (#[trigger] blocks.pages@[i]).kind is Base implies i == pb || i == lb by {
            if pb < i < pb + 8 {
                assert(blocks.pages@[pb + (i - pb)].kind is Member);
            }
            if i == lb + 1 {
                assert(blocks.pages@[lb + 1int].kind is Member);
            }
        }
        assert forall|i: int| 0 <= i < NUM_PAGES && #[trigger] blocks.pages@[i].object is Frame implies false by {
            if pb < i < pb + 8 {
                assert(blocks.pages@[pb + (i - pb)].object is None);
            }
        }
        assert(blocks.regions_2m@ == pre.blocks.regions_2m@);
        assert(blocks.regions_1g@ == pre.blocks.regions_1g@);
        // list_pages_used.
        assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
            &&& !(blocks.pages@[(p / 4096) as int].kind is Free)
            &&& blocks.pages@[(p / 4096) as int].kind is Member
                ==> blocks.pages@[blocks.pages@[(p / 4096) as int].base as int].object is TablePage
                    || blocks.pages@[blocks.pages@[(p / 4096) as int].base as int].object is Space
            &&& !(blocks.pages@[(p / 4096) as int].object is Frame)
        } by {
            if p == root {
                let x = (root / 4096) as int;
                assert(!(pb <= x < pb + 8) && !(lb <= x < lb + 2)) by (nonlinear_arith)
                    requires
                        x == root / 4096,
                        root % 4096 == 0,
                        pb * 4096 == base,
                        lb * 4096 == leaf,
                        !(base <= root < base + 32768),
                        !(leaf <= root < leaf + 8192),
                ;
            } else {
                assert(p == leaf);
                assert(p / 4096 == lb);
            }
        }
        // The table's first leaf and its hidden node.
        assert(hidden_nodes_are_leaves(&list, &post.tables, &post.table_pages)) by {
            assert forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Hidden
                implies post.tables.owner@.contains_key(n) || post.table_pages.maps@.contains_key(n) by {
                assert(n == leaf);
            }
        }
        assert(leaf_slots_are_capabilities(&list, &post.tables)) by {
            assert forall|n: usize| #[trigger] list.nodes@[n as int].live && post.tables.owner@.contains_key(page_of(n))
                && n % 4096 != 0 && n % 4096 < NODES_PER_PAGE implies list.nodes@[n as int].kind is Capability by {
                assert(page_of(n) == leaf);
                assert(n < NODE_SPACE);
                assert(n == root || n == leaf || n == cap);
            }
        }
        assert(first_node_outside_leaves(&list, &post.tables));
        assert(capability_nodes_are_slots(&list, &post.tables)) by {
            assert forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Capability
                && n != list.seq@[0] implies post.tables.is_cap(&list, n) by {
                assert(n == cap);
            }
        }
        assert(parents_are_capabilities(&list)) by {
            assert forall|x: usize| #[trigger] list.seq@.contains(x) && x != list.seq@[0]
                implies list.nodes@[list.parent@[x] as int].kind is Capability by {
                assert(x == leaf || x == cap);
            }
        }
        // What the capability says.
        assert(post.tables.caps_wf(&list)) by {
            assert forall|n: usize| #[trigger] post.tables.is_cap(&list, n)
                implies cap_wf(post.tables.payload_of(n)) by {
                assert(post.is_cap(n));
                assert(n == cap);
            }
        }
        assert(post.tables.control_wf(&list)) by {
            assert forall|n: usize| #[trigger] post.tables.is_cap(&list, n) implies control_named(post.tables.payload_of(n)) by {
                assert(post.is_cap(n));
                assert(n == cap);
            }
        }
        // The objects.
        assert(table_pages_wf(&list, &post.table_pages, &blocks)) by {
            assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(&blocks, x)
                implies post.table_pages.maps@.contains_key((x * 4096) as usize) by {
                assert(x == pb || x == lb);
            }
        }
        assert(objects_wf(&post.tables, &blocks, post.holders@)) by {
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
                &&& l / 4096 < NUM_PAGES
                &&& blocks.pages@[(l / 4096) as int].kind is Base
                &&& blocks.pages@[(l / 4096) as int].object is TableLeaf
                &&& blocks.pages@[(l / 4096) as int].order == 1
            } by {
                assert(l == leaf);
            }
            assert forall|x: usize| x < NUM_PAGES && #[trigger] leaf_block(&blocks, x)
                implies post.tables.owner@.contains_key((x * 4096) as usize) by {
                assert(x == pb || x == lb);
            }
            assert forall|x: usize| x < NUM_PAGES && (#[trigger] blocks.pages@[x as int]).kind is Base
                && blocks.pages@[x as int].object is Frame implies false by {}
        }
        assert(leaf_blocks_wf(&list, &post.tables, &blocks)) by {
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
                &&& list.nodes@[l as int].live ==> {
                    &&& list.nodes@[l as int].kind is Hidden
                    &&& blocks.pages@[(l / 4096) as int].refs == 1
                    &&& !blocks.pages@[(l / 4096) as int].dead
                }
                &&& !list.nodes@[l as int].live ==> {
                    &&& blocks.pages@[(l / 4096) as int].refs == 0
                    &&& blocks.pages@[(l / 4096) as int].dead
                }
            } by {
                assert(l == leaf);
            }
        }
        assert(holders_wf(&list, &post.tables, &blocks, &post.zeroing, post.holders@)) by {
            assert(holders_wf(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@));
            assert forall|n: usize| #[trigger] post.tables.is_cap(&list, n) && post.tables.payload_of(n).kind is Frame implies false by {
                assert(post.is_cap(n));
                assert(n == cap);
            }
        }
        assert(zeroing_typed(&post.zeroing, &blocks));
        assert(mappings_wf(&list, &post.tables, tree_of(&post.table_pages, &post.spaces), &blocks, post.holders@, post.mappings@)) by {
            assert forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live
                implies !(list.nodes@[n as int].kind is Mapping) by {
                assert(n == root || n == leaf || n == cap);
            }
        }
        // The space.
        let sb = &post.spaces;
        assert(space_wf(&list, sb, &blocks, base)) by {
            assert(root_record_wf(sb, base)) by {
                assert forall|i: usize| #![trigger sb.roots@[base].value()[i]]
                    i < 512 && !holds_kernel(sb.records@[base].value().kind, i)
                    implies sb.roots@[base].value()[i].is_empty() by {
                    assert(KERNEL_MEM_END_L4INDEX <= i);
                }
            }
            assert(kernel_slots_wf(sb, base));
            assert(sb.holders@[base] == Set::<usize>::empty());
            assert(sb.bound@[base] == Set::<usize>::empty());
            assert((base / 4096) as int == pb as int);
        }
        assert(spaces_wf(&list, &post.tables, sb, &blocks)) by {
            assert(pre.spaces.kernel_entries.wf());
            assert forall|x: usize| x < NUM_PAGES && #[trigger] space_block(&blocks, x)
                implies sb.roots@.contains_key((x * 4096) as usize) by {
                assert(x == pb || x == lb);
            }
            assert forall|n: usize| #[trigger] post.tables.is_cap(&list, n) && post.tables.payload_of(n).kind is Space implies false by {
                assert(post.is_cap(n));
                assert(n == cap);
            }
        }
        assert(space_nodes_dead(&list, sb));
        assert(table_nodes_are_mappings(&list, &post.table_pages));
        // The process.
        let pp = &post.processes;
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), cap);
        assert(set![cap].len() == 1);
        assert(process_wf(pp, &blocks, base)) by {
            assert(pp.holders@[base] == set![cap]);
            assert(pp.bound@[base] == Set::<usize>::empty());
            assert(pp.bound@[base].len() == 0);
        }
        assert(processes_wf(&list, &post.tables, pp, &blocks)) by {
            assert forall|x: usize| x < NUM_PAGES && #[trigger] process_block(&blocks, x)
                implies pp.records@.contains_key((x * 4096) as usize) by {
                assert(x == pb || x == lb);
            }
            assert forall|n: usize| #[trigger] post.tables.is_cap(&list, n) && post.tables.payload_of(n).kind is Process implies {
                &&& pp.records@.contains_key(post.tables.payload_of(n).base)
                &&& pp.holders@[post.tables.payload_of(n).base].contains(n)
                &&& post.tables.payload_of(n).order == PROCESS_ORDER
            } by {
                assert(post.is_cap(n));
                assert(n == cap);
            }
            assert forall|p: usize, n: usize| pp.records@.contains_key(p) && #[trigger] pp.holders@[p].contains(n) implies {
                &&& post.tables.is_cap(&list, n)
                &&& post.tables.payload_of(n).kind is Process
                &&& post.tables.payload_of(n).base == p
            } by {
                assert(p == base);
                assert(n == cap);
            }
        }
        assert(threads_wf(&list, &post.tables, &post.threads, &blocks)) by {
            assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(&blocks, x)
                implies post.threads.records@.contains_key((x * 4096) as usize) by {
                assert(x == pb || x == lb);
            }
            assert forall|n: usize| #[trigger] post.tables.is_cap(&list, n) && post.tables.payload_of(n).kind is Thread implies false by {
                assert(post.is_cap(n));
                assert(n == cap);
            }
        }
        assert(bindings_wf(&list, &post.threads, pp)) by {
            assert forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live
                implies !(list.nodes@[n as int].kind is Binding) by {
                assert(n == root || n == leaf || n == cap);
            }
            assert forall|p: usize, t: usize| pp.records@.contains_key(p) && #[trigger] pp.bound@[p].contains(t) implies false by {
                assert(p == base);
            }
        }
        assert(binding_parents(&list, &post.tables, &post.threads)) by {
            reveal(binding_parents);
            assert forall|t: usize| t < NODE_SPACE && (#[trigger] list.nodes@[t as int]).live
                implies !(list.nodes@[t as int].kind is Binding) by {
                assert(t == root || t == leaf || t == cap);
            }
        }
        // The space's tables, its mapping and the cores.
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(!a.is_table(base));
        assert forall|i: usize| i < 512 && !holds_kernel(b.space_records[base].value().kind, i) implies #[trigger] b.entry(base, i).is_empty() by {
            assert(KERNEL_MEM_END_L4INDEX <= i);
            assert(!b.is_page(base));
        }
        lemma_links_root_added(a, b, base);
        Self::lemma_tlb_same(pre, post);
        lemma_ids_space_added(pre.cores@, pre.spaces.loaded@, post.spaces.loaded@, base);
        assert forall|c: int| 0 <= c < NUM_CPUS implies !#[trigger] post.loaded(c, base) by {
            lemma_no_core_listed(c as u32);
        }
        Self::lemma_devices_same_caps(pre, post);
        assert(post.wf());
        assert forall|k: int| 0 <= k < 8 implies {
            ||| (#[trigger] post.blocks.pages@[base / 4096 + k]).kind is Base
            ||| post.blocks.pages@[base / 4096 + k].kind is Member
        } by {
            if k > 0 {
                assert(blocks.pages@[pb + k].kind is Member);
            }
        }
        assert forall|k: int| 0 <= k < 2 implies {
            ||| (#[trigger] post.blocks.pages@[leaf / 4096 + k]).kind is Base
            ||| post.blocks.pages@[leaf / 4096 + k].kind is Member
        } by {
            if k == 0 {
                assert(blocks.pages@[lb as int].kind is Base);
            }
        }
    }
}

/// Hands boot's reserved pages start to start + n to the block table.
fn add_free_run(blocks: &mut BlockTable, start: usize, n: usize, Tracked(pages): Tracked<&mut Map<usize, PagePerm4k>>)
    requires
        old(blocks).wf(),
        start + n <= NUM_PAGES,
        forall|i: int| start <= i < start + n ==> #[trigger] old(blocks).pages@[i].kind is Reserved,
        forall|i: usize| start <= i < start + n ==> #[trigger] holds(*old(pages), i),
    ensures
        final(blocks).wf(),
        final(blocks).regions_2m@ == old(blocks).regions_2m@,
        final(blocks).regions_1g@ == old(blocks).regions_1g@,
        forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] final(blocks).pages@[i]
            == if start <= i < start + n { free_entry() } else { old(blocks).pages@[i] },
        forall|i: usize| !(start <= i < start + n) && #[trigger] old(pages).contains_key(i)
            ==> final(pages).contains_key(i) && final(pages)[i] == old(pages)[i],
{
    let ghost pre = *old(blocks);
    let ghost given = *old(pages);
    let mut k = 0;
    while k != n
        invariant
            0 <= k <= n,
            start + n <= NUM_PAGES,
            blocks.wf(),
            blocks.regions_2m@ == pre.regions_2m@,
            blocks.regions_1g@ == pre.regions_1g@,
            forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] blocks.pages@[i]
                == if start <= i < start + k { free_entry() } else { pre.pages@[i] },
            forall|i: int| start <= i < start + n ==> #[trigger] pre.pages@[i].kind is Reserved,
            forall|i: usize| start + k <= i < start + n ==> #[trigger] holds(*pages, i),
            forall|i: usize| !(start <= i < start + k) && #[trigger] given.contains_key(i)
                ==> pages.contains_key(i) && pages[i] == given[i],
        decreases n - k,
    {
        let ghost before = *pages;
        let tracked perm;
        proof {
            assert(holds(before, (start + k) as usize));
            perm = pages.tracked_remove((start + k) as usize);
        }
        let ghost mid = *blocks;
        blocks.add_free(start + k, Tracked(perm));
        proof {
            assert forall|i: usize| start + k + 1 <= i < start + n implies #[trigger] holds(*pages, i) by {
                assert(holds(before, i));
            }
            assert forall|i: int| 0 <= i < NUM_PAGES implies #[trigger] blocks.pages@[i]
                == if start <= i < start + k + 1 { free_entry() } else { pre.pages@[i] } by {
                assert(mid.pages@[i] == if start <= i < start + k { free_entry() } else { pre.pages@[i] });
            }
        }
        k = k + 1;
    }
}

} // verus!
