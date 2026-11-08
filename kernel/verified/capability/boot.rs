//! The boot steps that make the root process from pages boot sets aside, not from an untyped, so the
//! blocks they type are never retyped: no untyped covers them. They run on the state init leaves. See
//! design/root-process-at-boot/.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::device::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::mapping::*;
use crate::capability::process::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::define::*;
use crate::layouts::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

/// The index of the root's capability to its own process in its table: slot 1 of entry 0, the first
/// slot of the table's first leaf.
pub const ROOT_PROCESS_SLOT: usize = 1;

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
    /// node, which every attached leaf has. Boot hands over every page's permission.
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
            final(self).tables.has_slot(base, ROOT_PROCESS_SLOT),
            final(self).tables.node_of(base, ROOT_PROCESS_SLOT) == leaf + 1,
            final(self).is_cap((leaf + 1) as usize),
            final(self).payload_of((leaf + 1) as usize) == process_of(base),
            final(self).payload_of((leaf + 1) as usize).rights & CONTROL_RIGHT != 0,
            final(self).list.is_child(root, (leaf + 1) as usize),
            final(self).list.nodes@[leaf + 1].depth == 1,
            final(self).list.is_child(root, leaf),
            final(self).list.nodes@[leaf as int].live,
            final(self).list.nodes@[leaf as int].kind is Hidden,
            forall|x: usize| #[trigger] final(self).is_cap(x) ==> x == leaf + 1,
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
            assert(index_entry(ROOT_PROCESS_SLOT) == 0);
            assert(index_slot(ROOT_PROCESS_SLOT) == 1);
            assert(index_ok(ROOT_PROCESS_SLOT));
            assert(leafed.leaf(base, 0) == leaf);
            assert(leafed.has_slot(base, ROOT_PROCESS_SLOT));
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
            assert(post.tables.attached(leaf));
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
        }
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
            post.tables.attached(leaf),
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
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) && post.tables.attached(l) implies {
                &&& l < NODE_SPACE
                &&& list.nodes@[l as int].live
                &&& list.nodes@[l as int].kind is Hidden
            } by {
                assert(l == leaf);
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
            assert forall|n: usize| #[trigger] post.tables.is_cap(&list, n) && !(post.tables.payload_of(n).kind is Device)
                implies payload_wf(post.tables.payload_of(n)) by {
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
