// SPDX-License-Identifier: MIT

//! Boot's one verified step for the capability kernel: init on the list's synthetic root, then the root
//! process with its table and thread, its console and power capabilities, its free memory as untyped
//! capabilities and dom0's image mapped in its space, each step's requires discharged by the previous
//! steps' ensures and by what kernel/src checked at the trust boundary of the pages and runs it passes.
//! See design/root-process-at-boot/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::arch::{BaseRegister, IotlbModel, TlbModel};
use crate::array::Array;
#[cfg(verus_keep_ghost)]
use crate::capability::block::*;
use crate::capability::boot::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_frame::*;
use crate::capability::boot_image::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_memory::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_table::*;
use crate::capability::console::*;
#[cfg(verus_keep_ghost)]
use crate::capability::cpu::*;
#[cfg(verus_keep_ghost)]
use crate::capability::decompose::*;
#[cfg(verus_keep_ghost)]
use crate::capability::derive::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
use crate::capability::power::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::pagetable::pagemap::*;
use crate::pptr::PointsTo;
#[cfg(verus_keep_ghost)]
use crate::util::page_ptr_util_u::mem_valid;

/// Page i is a page of one of the four blocks boot_root takes: the root's process at `process`, its
/// table's two leaves at `leaf` and `frames`, and its thread at `t`.
pub open spec fn in_root_blocks(process: usize, leaf: usize, frames: usize, t: usize, i: int) -> bool {
    ||| process / PAGE_SZ <= i < process / PAGE_SZ + 8
    ||| leaf / PAGE_SZ <= i < leaf / PAGE_SZ + 2
    ||| frames / PAGE_SZ <= i < frames / PAGE_SZ + 2
    ||| t / PAGE_SZ <= i < t / PAGE_SZ + 2
}

/// Page i is one the root reaches after boot: a page of its process's or its thread's block, of a free
/// run handed to it as untyped, or of one of dom0's image runs handed to it as frames.
pub open spec fn root_reach_page(process: usize, t: usize, free: Seq<(usize, usize)>, image: Seq<ImageRun>, i: int) -> bool {
    ||| process / PAGE_SZ <= i < process / PAGE_SZ + 8
    ||| t / PAGE_SZ <= i < t / PAGE_SZ + 2
    ||| in_runs(free, free.len() as int, i)
    ||| in_runs(image_phys(image), image.len() as int, i)
}

/// The pages of the four blocks boot_root takes that m holds.
pub open spec fn root_block_pages(m: Map<usize, PagePerm4k>, process: usize, leaf: usize, frames: usize, t: usize) -> Set<usize> {
    m.dom().filter(|i: usize| in_root_blocks(process, leaf, frames, t, i as int))
}

/// The pages of the free runs that m holds.
pub open spec fn free_run_pages(m: Map<usize, PagePerm4k>, runs: Seq<(usize, usize)>) -> Set<usize> {
    m.dom().filter(|i: usize| in_runs(runs, runs.len() as int, i as int))
}

impl CapKernel {
    /// A table without table pages maps nothing in any space: a walk's first step would name a table
    /// page.
    proof fn lemma_no_table_pages(&self, s: usize)
        requires
            self.wf(),
            self.table_pages.maps@ == Map::<usize, PointsTo<PageMap>>::empty(),
        ensures
            forall|p: SpacePath| !#[trigger] space_mapping(tree_of(&self.table_pages, &self.spaces), s).contains_key(p),
    {
        reveal(table_links_wf);
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert forall|p: SpacePath| !#[trigger] space_mapping(tree, s).contains_key(p) by {
            if tree.names_child(s, p.l4) {
                let c = (tree.entry(s, p.l4).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize;
                assert(tree.is_page(c));
                assert(tree.maps.contains_key(c));
            }
            assert(step(tree, s, p.l4) is None);
            assert(walk(tree, s, p) is None);
        }
    }

    /// Without table pages, a process's space has no entry outside the kernel slots: a present one
    /// would name a table page, or be a large frame's, which only a level 2 table holds.
    proof fn lemma_no_root_entries(&self, s: usize)
        requires
            self.wf(),
            self.table_pages.maps@ == Map::<usize, PointsTo<PageMap>>::empty(),
            self.spaces.roots@.contains_key(s),
            self.spaces.records@[s].value().kind == SpaceKind::Process,
        ensures
            forall|j: usize| KERNEL_MEM_END_L4INDEX <= j < ENTRIES
                ==> #[trigger] tree_of(&self.table_pages, &self.spaces).entry(s, j).is_empty(),
    {
        reveal(table_links_wf);
        let tree = tree_of(&self.table_pages, &self.spaces);
        self.lemma_table_base(s);
        assert forall|j: usize| KERNEL_MEM_END_L4INDEX <= j < ENTRIES implies #[trigger] tree.entry(s, j).is_empty() by {
            assert(!holds_kernel(tree.space_records[s].value().kind, j));
            assert(tree.child_slot(s, j));
            self.lemma_entry_shape(s, j);
            if tree.names_child(s, j) {
                let c = (tree.entry(s, j).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize;
                assert(tree.is_page(c));
                assert(tree.maps.contains_key(c));
            }
        }
    }

    /// Every order-3 block of an untyped capability for block b0 is free and outside any typed large
    /// block when every page of b0 is free and no large block is typed.
    proof fn lemma_untyped_block_free(&self, process: usize, b0: (nat, nat))
        requires
            self.payload_of(self.root_untyped(process)) == page_block_payload(b0),
            b0.1 <= MAX_ORDER,
            self.blocks.tracks_run(b0.0 as int, pow2(b0.1) as int),
            forall|j: int| b0.0 <= j < b0.0 + pow2(b0.1) ==> (#[trigger] self.blocks.pages@[j]).kind is Free,
            forall|r: int| 0 <= r < NUM_2M ==> !(#[trigger] self.blocks.regions_2m@[r]).typed,
            forall|r: int| 0 <= r < NUM_1G ==> !(#[trigger] self.blocks.regions_1g@[r]).typed,
        ensures
            self.root_untyped_free(process),
    {
        let pw = pow2(b0.1) as int;
        lemma2_to64();
        lemma_pow2_pos(b0.1);
        assert(block_bytes(3) == PROCESS_BYTES);
        assert forall|b: usize| #[trigger] block_within(b, 3, self.payload_of(self.root_untyped(process)))
            implies self.root_table_block(process, b) by {
            let base = b0.0 * PAGE_SZ;
            assert(base <= self.blocks.page_count() * PAGE_SZ);
            assert(self.payload_of(self.root_untyped(process)).base == base);
            assert(self.payload_of(self.root_untyped(process)).order as nat == b0.1);
            assert(block_bytes(b0.1 as u8) == pw * PAGE_SZ);
            let bp = b as int / PAGE_SZ as int;
            assert(bp * PAGE_SZ == b) by (nonlinear_arith)
                requires
                    b % PROCESS_BYTES == 0,
                    bp == b as int / PAGE_SZ as int,
            ;
            assert(b0.0 <= bp);
            assert(bp + 8 <= b0.0 + pw);
            assert(self.blocks.tracks_run(bp, 8));
            assert(bp / (PAGES_PER_2M as int) < NUM_2M) by (nonlinear_arith)
                requires
                    self.blocks.tracks(bp),
            ;
            assert(bp / (PAGES_PER_1G as int) < NUM_1G) by (nonlinear_arith)
                requires
                    self.blocks.tracks(bp),
            ;
            assert(!self.blocks.covered(bp));
            assert forall|k: int| 0 <= k < 8 implies #[trigger] self.blocks.pages@[b / PAGE_SZ + k].kind is Free by {
                assert(b0.0 <= bp + k < b0.0 + pw);
            }
        }
    }

    /// The state boot's composed step leaves when it succeeds, having returned `untyped` and `frame`:
    /// what kernel_init ensures, and so what a proof about the root's first operations starts from.
    /// The free runs are well formed, so each untyped block lies in the tracked pages. The root's
    /// first leaf is at entry 0 of its table and inside the node address space, each fixed slot of the
    /// root's table holds its kind, and each untyped is at depth 1, so a
    /// capability retyped under it is below the deepest depth; every page of the untyped blocks is
    /// acknowledged, since boot unmaps nothing, so a free of a block typed there is not refused as
    /// stale, and so is every 2M and 1G region; the root's thread is its process's and inactive, so a
    /// core may enter it; the root's process is live, as is the page of its space, and its table is the only one, so it is sealed; no flush has run, so the flush
    /// epoch is 0; no core runs a thread, and each is at generation 1 and names no space, so a load may start on any; every root entry of its table past the two boot filled is empty; the root's space
    /// maps exactly the image, and its level 4 entries outside the kernel slots that no image run
    /// reaches are empty, so a table built there is the root's own to fill; of
    /// the first untyped's order-3 blocks, every one past those the image's tables can take is free;
    /// the IOMMUs present are the `present` boot was given, which a bind needs of its device's IOMMU;
    /// the root holds each core's capability at its top priority, at depth 1; the root reaches exactly
    /// the console, power, the cores and the pages of its process, its thread, the free runs and the
    /// image, and nothing else reaches anything the root does not, besides itself; the
    /// root every core booted on is a page the base register can name, so a core may be pointed back
    /// at it.
    pub open spec fn booted(
        &self,
        root: usize,
        process: usize,
        leaf: usize,
        frames: usize,
        t: usize,
        free: Seq<(usize, usize)>,
        image: Seq<ImageRun>,
        untyped: usize,
        frame: usize,
        present: Seq<bool>,
        kernel_root: usize,
    ) -> bool {
        let bs = runs_blocks(free, MAX_ORDER as nat);
        let b = tree_of(&self.table_pages, &self.spaces);
        let first = page_block_payload(bs[0]);
        &&& runs_wf(free)
        &&& untyped == bs.len()
        &&& 0 < untyped <= ROOT_UNTYPED_SLOTS
        &&& frame == image_blocks(image).len()
        &&& frame <= ROOT_FRAME_SLOTS
        &&& self.wf()
        &&& self.list.seq@[0] == root
        &&& self.tables.roots@.dom() == set![process]
        &&& leaf + LEAF_BYTES <= NODE_SPACE
        &&& self.tables.leaf(process, 0) == leaf
        &&& self.slot_holds(process, ROOT_PROCESS_SLOT, (leaf + 1) as usize, process_of(process))
        &&& self.slot_holds(process, ROOT_THREAD_SLOT, (leaf + 2) as usize, thread_of(t))
        &&& self.slot_holds(process, ROOT_CONSOLE_SLOT, (leaf + 3) as usize, console_payload())
        &&& self.slot_holds(process, ROOT_POWER_SLOT, (leaf + 4) as usize, power_payload())
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> {
            &&& self.slot_holds(
                process,
                (ROOT_CORE_SLOT + c) as usize,
                (leaf + ROOT_CORE_SLOT + c) as usize,
                #[trigger] core_payload(c, MAX_PRIORITY),
            )
            &&& self.list.nodes@[leaf + ROOT_CORE_SLOT + c].depth == 1
        }
        &&& forall|k: int| 0 <= k < untyped ==> {
            &&& self.slot_holds(
                process,
                (ROOT_UNTYPED_SLOT + k) as usize,
                (leaf + ROOT_UNTYPED_SLOT + k) as usize,
                page_block_payload(#[trigger] bs[k]),
            )
            &&& self.list.nodes@[leaf + ROOT_UNTYPED_SLOT + k].depth == 1
        }
        &&& forall|k: int, j: nat| 0 <= k < untyped && #[trigger] in_page_block(bs[k], j) ==> self.acknowledged(j as usize)
        &&& forall|r: usize| r < NUM_2M ==> #[trigger] self.region_acknowledged(Large::Two, r)
        &&& forall|r: usize| r < NUM_1G ==> #[trigger] self.region_acknowledged(Large::One, r)
        &&& forall|a: int, u: int| #![trigger crate::capability::boot_map::frame_slot(image, a, u)]
            0 <= a < image.len() && 0 <= u < run_image_blocks(image[a]).len() ==> {
            let fb = run_image_blocks(image[a])[u];
            self.slot_holds(
                process,
                crate::capability::boot_map::frame_slot(image, a, u),
                (frames + 1 + image_offset(image, a) + u) as usize,
                boot_frame_payload((fb.0 * PAGE_SZ) as usize, fb.1 as u8, image_rights(image[a])),
            )
        }
        &&& self.threads.boot_thread@ == Some(t)
        &&& self.threads.queues.all_empty()
        &&& self.threads.records@.contains_key(t)
        &&& self.threads.records@[t].value().process == Some(process)
        &&& self.threads.records@[t].value().state is Inactive
        &&& !self.threads.records@[t].value().dying
        &&& self.threads.records@[t].value().placement is None
        &&& forall|a: int, x: int| 0 <= a < image.len() && #[trigger] in_virt_at(image, a, x) ==> {
            &&& space_mapping(b, process).contains_key(page_path(x))
            &&& space_mapping(b, process)[page_path(x)] == image_entry(image[a], x)
        }
        &&& forall|p: SpacePath| #[trigger] space_mapping(b, process).contains_key(p) ==> image_path(image, p)
        &&& forall|o: usize| #[trigger] self.view().reach(process, o) <==> (o == CONSOLE_OBJECT
            || o == POWER_OBJECT
            || is_core_object(o)
            || (o % PAGE_SZ == 0 && root_reach_page(process, t, free, image, (o / PAGE_SZ) as int)))
        &&& forall|q: usize, o: usize| #[trigger] self.view().reach(q, o)
            ==> o == q || self.view().reach(process, o)
        &&& forall|l4: usize| KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES && !image_l4(image, l4)
            ==> #[trigger] b.entry(process, l4).is_empty()
        &&& self.root_live(process)
        &&& !self.blocks.pages@[(process / PAGE_SZ) as int].dead
        &&& self.flush_epoch == 0
        &&& boot_registers(self.spaces.registers@, self.spaces.kernel_root@)
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> {
            &&& (#[trigger] self.cores@[c]).current_thread is None
            &&& self.cores@[c].generation == 1
            &&& self.cores@[c].next_pcid == 1
            &&& self.cores@[c].space is None
        }
        &&& self.devices.count == 0
        &&& self.iommus.present@ == present
        &&& forall|r: int| 2 <= r < ROOT_ENTRIES ==> #[trigger] self.tables.leaf(process, r) == NO_LEAF
        &&& forall|j: int| image_tables_bound(image) <= j < untyped_tables(first)
            ==> #[trigger] self.root_table_block(process, cursor_block(first.base, j))
        &&& self.spaces.kernel_root@ == kernel_root
        &&& self.spaces.kernel_root@ % PAGE_SZ == 0
        &&& mem_valid(self.spaces.kernel_root@)
    }

    /// Boot of the capability kernel, from the memory boot set aside for it: init with the list's
    /// synthetic root at `root`, then boot_root with the root's process at `process`, its table's
    /// leaves at `leaf` and `frames` and its thread at `t`, boot_root_object for the console and for
    /// power, boot_root_cores, boot_root_memory over the free runs and boot_root_space over dom0's image runs.
    /// kernel/src checks at the trust boundary that the four blocks, the root page, the free runs and
    /// every 2M region of the image are pairwise disjoint and that none holds the page of
    /// `kernel_root`, which boot hands to no block, and hands over every page's permission in `pages`,
    /// which is split here between the steps. It returns how many untyped and frame
    /// capabilities the root holds, and refuses exactly when the free runs make no block or more than
    /// the first leaf holds, or the image does not fit the second leaf or the first untyped block's
    /// tables. On success the state is the one `booted` describes, with `kernel_root`, a page the base
    /// register can name, which kernel/src checks with its alignment, as the root a core naming no
    /// space may be pointed back at. See design/root-process-at-boot/.
    #[verifier::spinoff_prover]
    pub fn kernel_init(
        &mut self,
        root: usize,
        Tracked(root_perm): Tracked<PointsTo<NodePage>>,
        kernel_entries: Array<usize, KERNEL_MEM_END_L4INDEX>,
        iommus_present: Array<bool, NUM_IOMMUS>,
        iommu_commands: CommandBuffers,
        process: usize,
        leaf: usize,
        frames: usize,
        t: usize,
        free: &[(usize, usize)],
        image: &[ImageRun],
        Tracked(pages): Tracked<Map<usize, PagePerm4k>>,
        kernel_root: usize,
        Tracked(registers): Tracked<Map<int, BaseRegister>>,
        Tracked(tlb): Tracked<TlbModel>,
        Tracked(iotlb): Tracked<IotlbModel>,
    ) -> (ret: Option<(usize, usize)>)
        requires
            boot_registers(registers, kernel_root),
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
            boot_tlb(tlb),
            boot_iotlb(iotlb),
            root % PAGE_SZ == 0,
            root + PAGE_SZ <= NODE_SPACE,
            root_perm.addr() == root,
            root_perm.is_init(),
            root_perm.value().nodes.wf(),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] root_perm.value().nodes@[k]).live,
            kernel_entries.wf(),
            iommus_present.wf(),
            iommu_commands.wf(iommus_present@),
            process % PROCESS_BYTES == 0,
            process / PAGE_SZ + 8 <= NUM_PAGES,
            leaf % LEAF_BYTES == 0,
            leaf != NO_LEAF,
            leaf / PAGE_SZ + 2 <= NUM_PAGES,
            frames % LEAF_BYTES == 0,
            frames != NO_LEAF,
            frames / PAGE_SZ + 2 <= NUM_PAGES,
            t % THREAD_BYTES == 0,
            t / PAGE_SZ + 2 <= NUM_PAGES,
            process + PROCESS_BYTES <= leaf || leaf + LEAF_BYTES <= process,
            process + PROCESS_BYTES <= frames || frames + LEAF_BYTES <= process,
            process + PROCESS_BYTES <= t || t + THREAD_BYTES <= process,
            leaf + LEAF_BYTES <= frames || frames + LEAF_BYTES <= leaf,
            leaf + LEAF_BYTES <= t || t + THREAD_BYTES <= leaf,
            frames + LEAF_BYTES <= t || t + THREAD_BYTES <= frames,
            !(process <= root < process + PROCESS_BYTES),
            !(leaf <= root < leaf + LEAF_BYTES),
            !(frames <= root < frames + LEAF_BYTES),
            !(t <= root < t + THREAD_BYTES),
            runs_wf(free@),
            forall|j: int| #[trigger] in_runs(free@, free@.len() as int, j)
                ==> !in_root_blocks(process, leaf, frames, t, j) && j != root / PAGE_SZ,
            image_runs_wf(image@),
            forall|j: int| #[trigger] image_region(image@, region_2m(j)) ==> {
                &&& 0 <= j < NUM_PAGES
                &&& !in_root_blocks(process, leaf, frames, t, j)
                &&& !in_runs(free@, free@.len() as int, j)
                &&& j != root / PAGE_SZ
            },
            forall|i: usize| in_root_blocks(process, leaf, frames, t, i as int) || in_runs(free@, free@.len() as int, i as int)
                ==> #[trigger] holds(pages, i),
            forall|j: usize| image_region(image@, region_2m(j as int)) ==> #[trigger] pages.contains_key(j),
            forall|j: usize| #[trigger] pages.contains_key(j) ==> pages[j].addr() == j * PAGE_SZ,
            !in_root_blocks(process, leaf, frames, t, (kernel_root / PAGE_SZ) as int),
            !in_runs(free@, free@.len() as int, (kernel_root / PAGE_SZ) as int),
            !image_region(image@, region_2m((kernel_root / PAGE_SZ) as int)),
        ensures
            ret is None <==> ({
                let bs = runs_blocks(free@, MAX_ORDER as nat);
                ||| bs.len() > ROOT_UNTYPED_SLOTS
                ||| bs.len() == 0
                ||| image_blocks(image@).len() > ROOT_FRAME_SLOTS
                ||| !image_virt_wf(image@)
                ||| image_tables_bound(image@) > untyped_tables(page_block_payload(bs[0]))
            }),
            ret matches Some((untyped, frame)) ==> final(self).booted(root, process, leaf, frames, t, free@, image@, untyped, frame, iommus_present@, kernel_root),
    {
        hide(CapKernel::wf);
        self.init(root, Tracked(root_perm), kernel_entries, iommus_present, iommu_commands, kernel_root, Tracked(registers), Tracked(tlb), Tracked(iotlb));
        let ghost s0 = *self;
        let ghost len = free@.len() as int;
        let tracked mut pages = pages;
        let ghost given = pages;
        let ghost k1 = root_block_pages(given, process, leaf, frames, t);
        let ghost k2 = free_run_pages(given, free@);
        let tracked root_pages;
        let tracked run_pages;
        proof {
            assert forall|i: usize| #[trigger] k1.contains(i) implies pages.dom().contains(i) by {
                assert(holds(given, i));
            }
            root_pages = pages.tracked_remove_keys(k1);
            assert forall|i: usize| #[trigger] k2.contains(i) implies pages.dom().contains(i) by {
                assert(holds(given, i));
                assert(!in_root_blocks(process, leaf, frames, t, i as int));
                assert(!k1.contains(i));
            }
            run_pages = pages.tracked_remove_keys(k2);
            assert forall|i: usize| in_root_blocks(process, leaf, frames, t, i as int)
                implies #[trigger] holds(root_pages, i) by {
                assert(holds(given, i));
                assert(k1.contains(i));
            }
            assert forall|i: usize| in_runs(free@, len, i as int) implies #[trigger] holds(run_pages, i) by {
                assert(holds(given, i));
                assert(k2.contains(i));
            }
        }
        self.boot_root(root, process, leaf, frames, t, Tracked(root_pages));
        let ghost s1 = *self;
        self.boot_root_object(
            root,
            process,
            leaf,
            ROOT_CONSOLE_SLOT,
            Payload { kind: CapKind::Console, order: 0, rights: CONSOLE_RIGHTS, base: CONSOLE_OBJECT, badge: 0, priority: 0 },
        );
        let ghost sc = *self;
        proof {
            assert(!s1.list.nodes@[leaf + 4].live);
            assert(!sc.list.nodes@[leaf + 4].live);
        }
        self.boot_root_object(
            root,
            process,
            leaf,
            ROOT_POWER_SLOT,
            Payload { kind: CapKind::Power, order: 0, rights: POWER_RIGHTS, base: POWER_OBJECT, badge: 0, priority: 0 },
        );
        let ghost s2 = *self;
        proof {
            assert(index_entry(ROOT_PROCESS_SLOT) == 0) by (compute_only);
            assert(index_slot(ROOT_PROCESS_SLOT) == 1) by (compute_only);
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] sc.list.nodes@[j].live implies s2.list.nodes@[j].live by {
                assert(j != leaf + 4);
            }
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s1.list.nodes@[j].live implies s2.list.nodes@[j].live by {
                assert(j != leaf + 3);
                assert(sc.list.nodes@[j].live);
            }
            assert forall|j: int| leaf + ROOT_CORE_SLOT <= j < leaf + NODES_PER_PAGE implies !#[trigger] s2.list.nodes@[j].live by {
                assert(!s1.list.nodes@[j].live);
                assert(!sc.list.nodes@[j].live);
            }
            assert forall|i: int| s2.blocks.tracks(i) && in_runs(free@, len, i) implies (#[trigger] s2.blocks.pages@[i]).kind is Reserved by {
                assert(!in_root_blocks(process, leaf, frames, t, i));
                assert(s1.blocks.pages@[i].kind == s0.blocks.pages@[i].kind);
                assert(s0.blocks.pages@[i].kind is Reserved);
            }
            assert forall|p: usize| #[trigger] s2.list.pages@.dom().contains(p) && s2.blocks.tracks_addr(p)
                implies !in_runs(free@, len, (p / PAGE_SZ) as int) by {
                assert(s1.list.pages@.dom().contains(p));
                if in_runs(free@, len, (p / PAGE_SZ) as int) {
                    assert(!in_root_blocks(process, leaf, frames, t, (p / PAGE_SZ) as int));
                    assert(p / PAGE_SZ != root / PAGE_SZ);
                    assert(p == root || p == leaf || p == frames || p == t);
                }
            }
        }
        self.boot_root_cores(root, process, leaf);
        let ghost sk = *self;
        proof {
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s2.list.nodes@[j].live implies sk.list.nodes@[j].live by {
                if !(leaf + ROOT_CORE_SLOT <= j < leaf + ROOT_CORE_SLOT + NUM_CPUS) {
                    assert(sk.list.nodes@[j].live == s2.list.nodes@[j].live);
                }
            }
            assert forall|j: int| leaf + ROOT_UNTYPED_SLOT <= j < leaf + NODES_PER_PAGE implies !#[trigger] sk.list.nodes@[j].live by {
                assert(!s2.list.nodes@[j].live);
            }
            assert forall|i: int| sk.blocks.tracks(i) && in_runs(free@, len, i) implies (#[trigger] sk.blocks.pages@[i]).kind is Reserved by {
                assert(s2.blocks.pages@[i].kind is Reserved);
            }
            assert forall|p: usize| #[trigger] sk.list.pages@.dom().contains(p) && sk.blocks.tracks_addr(p)
                implies !in_runs(free@, len, (p / PAGE_SZ) as int) by {
                assert(s2.list.pages@.dom().contains(p));
            }
        }
        let untyped = match self.boot_root_memory(root, process, leaf, free, Tracked(run_pages)) {
            Some(count) => count,
            None => return None,
        };
        let ghost s3 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        if untyped == 0 {
            return None;
        }
        proof {
            lemma_runs_blocks(free@, MAX_ORDER as nat);
            assert(index_entry(ROOT_UNTYPED_SLOT) == 0) by (compute_only);
            assert(index_ok(ROOT_UNTYPED_SLOT)) by (compute_only);
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            // No live node dies from s1 to s3, and the root's table's roots stay.
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] sk.list.nodes@[j].live implies s3.list.nodes@[j].live by {
                assert(!(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + untyped));
            }
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s2.list.nodes@[j].live implies s3.list.nodes@[j].live by {
                assert(sk.list.nodes@[j].live);
            }
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s1.list.nodes@[j].live implies s3.list.nodes@[j].live by {
                assert(s2.list.nodes@[j].live);
            }
            assert(s3.tables.roots == s1.tables.roots);
            // The root's process capability, and the untyped at ROOT_UNTYPED_SLOT.
            let n = (leaf + 1) as usize;
            assert(sc.is_cap(n) && sc.payload_of(n) == process_of(process));
            assert(s2.is_cap(n) && s2.payload_of(n) == process_of(process));
            assert(sk.is_cap(n) && sk.payload_of(n) == process_of(process));
            assert(s3.is_cap(n) && s3.payload_of(n) == process_of(process));
            assert(s3.tables.node_of(process, ROOT_PROCESS_SLOT) == n);
            assert(s3.root_untyped_at(root, process, leaf, 0, bs[0]));
            assert(s3.root_untyped(process) == leaf + ROOT_UNTYPED_SLOT);
            assert(!in_runs(free@, len, (process / PAGE_SZ) as int)) by {
                if in_runs(free@, len, (process / PAGE_SZ) as int) {
                    assert(!in_root_blocks(process, leaf, frames, t, (process / PAGE_SZ) as int));
                }
            }
            assert(s3.blocks.pages@[(process / PAGE_SZ) as int] == s1.blocks.pages@[(process / PAGE_SZ) as int]);
            assert(s3.root_tables_ready(process));
            // Every page of the first block is free, and no large block is typed.
            assert forall|j: int| bs[0].0 <= j < bs[0].0 + pow2(bs[0].1) implies (#[trigger] s3.blocks.pages@[j]).kind is Free by {
                assert(in_page_block(bs[0], j as nat));
                assert(in_runs(free@, len, (j as nat) as int));
            }
            assert forall|r: int| 0 <= r < NUM_2M implies !(#[trigger] s3.blocks.regions_2m@[r]).typed by {
                assert(s3.blocks.regions_2m@[r] == s0.blocks.regions_2m@[r]);
            }
            assert forall|r: int| 0 <= r < NUM_1G implies !(#[trigger] s3.blocks.regions_1g@[r]).typed by {
                assert(s3.blocks.regions_1g@[r] == s0.blocks.regions_1g@[r]);
            }
            s3.lemma_untyped_block_free(process, bs[0]);
            // No table page, so the root's space maps nothing.
            assert(s3.table_pages == s0.table_pages);
            s3.lemma_no_table_pages(s3.root_space(process));
            s3.lemma_written_space(n);
            s3.lemma_no_root_entries(process);
            // The second leaf's frame slots are slots, and free.
            assert(s3.tables.leaf(process, 1) == frames);
            assert forall|i: usize| ROOT_FRAME_SLOT <= i < 2 * NODES_PER_PAGE implies #[trigger] s3.tables.has_slot(&s3.list, process, i) by {
                assert(s1.tables.has_slot(&s1.list, process, i));
                Self::lemma_slot_stays(s1, s3, process, i);
            }
            assert forall|j: int| frames + 1 <= j < frames + NODES_PER_PAGE implies !#[trigger] s3.list.nodes@[j].live by {
                let i = (j - frames + NODES_PER_PAGE) as usize;
                lemma_fundamental_div_mod_converse(i as int, NODES_PER_PAGE as int, 1, j - frames);
                assert(index_entry(i) == 1);
                assert(index_slot(i) == j - frames);
                assert(s1.tables.has_slot(&s1.list, process, i));
                assert(s1.tables.node_of(process, i) == j);
                assert(!s1.list.nodes@[j].live);
                assert(j != leaf + 3);
                assert(!sc.list.nodes@[j].live);
                assert(j != leaf + 4);
                assert(!s2.list.nodes@[j].live);
                assert(!(leaf + ROOT_CORE_SLOT <= j < leaf + ROOT_CORE_SLOT + NUM_CPUS));
                assert(!sk.list.nodes@[j].live);
                assert(!(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + untyped));
            }
            // dom0's image lies in reserved 2M regions no large block is typed in, whose permissions
            // are what is left of pages.
            assert forall|q: int| #[trigger] image_region(image@, q) implies {
                &&& !s3.blocks.regions_2m@[q].typed
                &&& forall|j: int| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> #[trigger] s3.blocks.pages@[j].kind is Reserved
                &&& forall|j: usize| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M ==> #[trigger] pages.contains_key(j)
            } by {
                lemma_fundamental_div_mod_converse(q * PAGES_PER_2M, PAGES_PER_2M as int, q, 0);
                assert(region_2m(q * PAGES_PER_2M) == q);
                assert(s3.blocks.tracks(q * PAGES_PER_2M));
                assert(0 <= q < NUM_2M);
                assert(s3.blocks.regions_2m@[q] == s0.blocks.regions_2m@[q]);
                assert forall|j: int| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M implies #[trigger] s3.blocks.pages@[j].kind is Reserved by {
                    lemma_fundamental_div_mod_converse(j, PAGES_PER_2M as int, q, j - q * PAGES_PER_2M);
                    assert(region_2m(j) == q);
                    assert(image_region(image@, region_2m(j)));
                    assert(s3.blocks.pages@[j] == sk.blocks.pages@[j]);
                    assert(sk.blocks.pages@[j] == s2.blocks.pages@[j]);
                    assert(s1.blocks.pages@[j].kind == s0.blocks.pages@[j].kind);
                }
                assert forall|j: usize| q * PAGES_PER_2M <= j < (q + 1) * PAGES_PER_2M implies #[trigger] pages.contains_key(j) by {
                    lemma_fundamental_div_mod_converse(j as int, PAGES_PER_2M as int, q, j - q * PAGES_PER_2M);
                    assert(region_2m(j as int) == q);
                    assert(image_region(image@, region_2m(j as int)));
                    assert(given.contains_key(j));
                    assert(!k1.contains(j));
                    assert(!k2.contains(j));
                }
            }
            assert forall|j: usize| #[trigger] pages.contains_key(j) implies pages[j].addr() == j * PAGE_SZ by {
                assert(given.contains_key(j));
            }
            assert forall|p: usize| #[trigger] s3.list.pages@.dom().contains(p) && s3.blocks.tracks_addr(p)
                implies !image_region(image@, region_2m((p / PAGE_SZ) as int)) by {
                assert(s1.list.pages@.dom().contains(p));
                if image_region(image@, region_2m((p / PAGE_SZ) as int)) {
                    assert(!in_root_blocks(process, leaf, frames, t, (p / PAGE_SZ) as int));
                    assert(p == root || p == leaf || p == frames || p == t);
                }
            }
        }
        let frame = match self.boot_root_space(root, process, frames, image, Tracked(pages)) {
            Some(count) => count,
            None => return None,
        };
        proof {
            let s4 = *self;
            assert(s3.root_space(process) == process);
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s1.list.nodes@[j].live implies s4.list.nodes@[j].live by {
                assert(s3.list.nodes@[j].live);
            }
            assert(s4.tables.roots == s1.tables.roots);
            // The process, thread, console and power slots.
            assert(index_entry(ROOT_THREAD_SLOT) == 0) by (compute_only);
            assert(index_entry(ROOT_CONSOLE_SLOT) == 0) by (compute_only);
            assert(index_entry(ROOT_POWER_SLOT) == 0) by (compute_only);
            assert(index_ok(ROOT_THREAD_SLOT)) by (compute_only);
            assert(index_ok(ROOT_CONSOLE_SLOT)) by (compute_only);
            assert(index_ok(ROOT_POWER_SLOT)) by (compute_only);
            Self::lemma_slot_stays(s1, s4, process, ROOT_PROCESS_SLOT);
            Self::lemma_slot_stays(s1, s4, process, ROOT_THREAD_SLOT);
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] sc.list.nodes@[j].live implies s4.list.nodes@[j].live by {
                assert(s2.list.nodes@[j].live);
                assert(s3.list.nodes@[j].live);
            }
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s2.list.nodes@[j].live implies s4.list.nodes@[j].live by {
                assert(s3.list.nodes@[j].live);
            }
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] sk.list.nodes@[j].live implies s4.list.nodes@[j].live by {
                assert(s3.list.nodes@[j].live);
            }
            assert(s4.tables.roots == sc.tables.roots);
            Self::lemma_slot_stays(sc, s4, process, ROOT_CONSOLE_SLOT);
            Self::lemma_slot_stays(s2, s4, process, ROOT_POWER_SLOT);
            assert(!(frames + 1 <= leaf + 1 < frames + 1 + frame));
            assert(!(frames + 1 <= leaf + 2 < frames + 1 + frame));
            assert(!(frames + 1 <= leaf + 3 < frames + 1 + frame));
            assert(!(frames + 1 <= leaf + 4 < frames + 1 + frame));
            assert(sc.is_cap((leaf + 2) as usize) && sc.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(sc.is_cap((leaf + 3) as usize) && sc.payload_of((leaf + 3) as usize) == console_payload());
            assert(s2.is_cap((leaf + 2) as usize) && s2.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(s2.is_cap((leaf + 3) as usize) && s2.payload_of((leaf + 3) as usize) == console_payload());
            assert(s2.is_cap((leaf + 4) as usize) && s2.payload_of((leaf + 4) as usize) == power_payload());
            assert(sk.is_cap((leaf + 2) as usize) && sk.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(sk.is_cap((leaf + 3) as usize) && sk.payload_of((leaf + 3) as usize) == console_payload());
            assert(sk.is_cap((leaf + 4) as usize) && sk.payload_of((leaf + 4) as usize) == power_payload());
            assert(s3.is_cap((leaf + 1) as usize) && s3.payload_of((leaf + 1) as usize) == process_of(process));
            assert(s3.is_cap((leaf + 2) as usize) && s3.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(s3.is_cap((leaf + 3) as usize) && s3.payload_of((leaf + 3) as usize) == console_payload());
            assert(s3.is_cap((leaf + 4) as usize) && s3.payload_of((leaf + 4) as usize) == power_payload());
            assert(s4.is_cap((leaf + 1) as usize) && s4.payload_of((leaf + 1) as usize) == process_of(process));
            assert(s4.is_cap((leaf + 2) as usize) && s4.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(s4.is_cap((leaf + 3) as usize) && s4.payload_of((leaf + 3) as usize) == console_payload());
            assert(s4.is_cap((leaf + 4) as usize) && s4.payload_of((leaf + 4) as usize) == power_payload());
            let lb = leaf / PAGE_SZ;
            assert(lb * PAGE_SZ == leaf) by (nonlinear_arith)
                requires
                    leaf % LEAF_BYTES == 0,
                    lb == leaf / PAGE_SZ,
            ;
            assert(leaf + LEAF_BYTES <= NODE_SPACE);
            assert(s4.tables.leaf(process, 0) == leaf);
            // The core slots.
            assert forall|c: int| 0 <= c < NUM_CPUS implies {
                &&& s4.slot_holds(
                    process,
                    (ROOT_CORE_SLOT + c) as usize,
                    (leaf + ROOT_CORE_SLOT + c) as usize,
                    #[trigger] core_payload(c, MAX_PRIORITY),
                )
                &&& s4.list.nodes@[leaf + ROOT_CORE_SLOT + c].depth == 1
            } by {
                let x = (leaf + ROOT_CORE_SLOT + c) as usize;
                assert(sk.slot_holds(process, (ROOT_CORE_SLOT + c) as usize, x, core_payload(c, MAX_PRIORITY)));
                Self::lemma_slot_stays(sk, s4, process, (ROOT_CORE_SLOT + c) as usize);
                assert(!(leaf + ROOT_UNTYPED_SLOT <= x < leaf + ROOT_UNTYPED_SLOT + untyped));
                assert(!(frames + 1 <= x < frames + 1 + frame));
                assert(s3.is_cap(x) && s3.payload_of(x) == sk.payload_of(x));
                assert(s4.is_cap(x) && s4.payload_of(x) == s3.payload_of(x));
                assert(sk.list.nodes@[x as int].live);
                assert(s3.list.nodes@[x as int].depth == sk.list.nodes@[x as int].depth);
                assert(s4.list.nodes@[x as int].depth == s3.list.nodes@[x as int].depth);
            }
            // The untyped slots.
            assert forall|k: int| 0 <= k < untyped implies {
                &&& s4.slot_holds(
                    process,
                    (ROOT_UNTYPED_SLOT + k) as usize,
                    (leaf + ROOT_UNTYPED_SLOT + k) as usize,
                    page_block_payload(#[trigger] bs[k]),
                )
                &&& s4.list.nodes@[leaf + ROOT_UNTYPED_SLOT + k].depth == 1
            } by {
                let x = (leaf + ROOT_UNTYPED_SLOT + k) as usize;
                assert(s3.root_untyped_at(root, process, leaf, k, bs[k]));
                Self::lemma_slot_stays(s3, s4, process, (ROOT_UNTYPED_SLOT + k) as usize);
                assert(!(frames + 1 <= x < frames + 1 + frame));
                assert(s4.is_cap(x) && s4.payload_of(x) == s3.payload_of(x));
                assert(s3.list.nodes@[x as int].live);
                assert(s4.list.nodes@[x as int].depth == s3.list.nodes@[x as int].depth);
            }
            // The root is live, its table has no leaf past the two boot gave it, and the first
            // untyped's blocks the tables left are free.
            assert(s4.root_live(process)) by {
                assert(s3.root_live(process));
            }
            // The root's level 4 entries outside the kernel slots that no image run reaches are as
            // boot_root_memory left them, empty.
            assert forall|l4: usize| KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES && !image_l4(image@, l4)
                implies #[trigger] tree_of(&s4.table_pages, &s4.spaces).entry(process, l4).is_empty() by {
                assert(tree_of(&s4.table_pages, &s4.spaces).entry(process, l4) == tree_of(&s3.table_pages, &s3.spaces).entry(process, l4));
            }
            assert(!s4.blocks.pages@[(process / PAGE_SZ) as int].dead);
            assert forall|r: int| 2 <= r < ROOT_ENTRIES implies #[trigger] s4.tables.leaf(process, r) == NO_LEAF by {
                assert(s1.tables.leaf(process, r) == NO_LEAF);
            }
            let first = page_block_payload(bs[0]);
            assert(s3.payload_of(s3.root_untyped(process)) == first);
            assert forall|j: int| image_tables_bound(image@) <= j < untyped_tables(first)
                implies #[trigger] s4.root_table_block(process, cursor_block(first.base, j)) by {
            }
            assert(s4.threads == s1.threads);
            // The root's reach is the five steps' growths in turn, and anyone else's grew only by
            // what the root's did.
            let phys = image_phys(image@);
            assert forall|o: usize| #[trigger] s4.view().reach(process, o) <==> (o == CONSOLE_OBJECT
                || o == POWER_OBJECT
                || is_core_object(o)
                || (o % PAGE_SZ == 0 && root_reach_page(process, t, free@, image@, (o / PAGE_SZ) as int))) by {
                assert(s4.view().reach(process, o) <==> (s3.view().reach(process, o)
                    || (o % PAGE_SZ == 0 && in_runs(phys, image@.len() as int, (o / PAGE_SZ) as int))));
                assert(s3.view().reach(process, o) <==> (sk.view().reach(process, o)
                    || (o % PAGE_SZ == 0 && in_runs(free@, len, (o / PAGE_SZ) as int))));
                assert(sk.view().reach(process, o) <==> (s2.view().reach(process, o) || is_core_object(o)));
                assert(s2.view().reach(process, o) <==> (sc.view().reach(process, o) || o == POWER_OBJECT));
                assert(sc.view().reach(process, o) <==> (s1.view().reach(process, o) || o == CONSOLE_OBJECT));
                assert(s1.view().reach(process, o)
                    <==> (o % PAGE_SZ == 0 && ((process <= o < process + PROCESS_BYTES) || (t <= o < t + THREAD_BYTES))));
                if o % PAGE_SZ == 0 {
                    assert((process <= o < process + PROCESS_BYTES) <==> (process / PAGE_SZ <= o / PAGE_SZ < process / PAGE_SZ + 8))
                        by (nonlinear_arith)
                        requires
                            process % PROCESS_BYTES == 0,
                            o % PAGE_SZ == 0,
                    ;
                    assert((t <= o < t + THREAD_BYTES) <==> (t / PAGE_SZ <= o / PAGE_SZ < t / PAGE_SZ + 2)) by (nonlinear_arith)
                        requires
                            t % THREAD_BYTES == 0,
                            o % PAGE_SZ == 0,
                    ;
                }
            }
            assert forall|q: usize, o: usize| #[trigger] s4.view().reach(q, o) implies o == q || s4.view().reach(process, o) by {
                if !s3.view().reach(q, o) {
                    assert(o % PAGE_SZ == 0 && in_runs(phys, image@.len() as int, (o / PAGE_SZ) as int));
                    assert(s4.view().reach(process, o));
                } else if !sk.view().reach(q, o) {
                    assert(o % PAGE_SZ == 0 && in_runs(free@, len, (o / PAGE_SZ) as int));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                } else if !s2.view().reach(q, o) {
                    assert(is_core_object(o));
                    assert(sk.view().reach(process, o));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                } else if !sc.view().reach(q, o) {
                    assert(o == POWER_OBJECT);
                    assert(s2.view().reach(process, o));
                    assert(sk.view().reach(process, o));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                } else if !s1.view().reach(q, o) {
                    assert(o == CONSOLE_OBJECT);
                    assert(sc.view().reach(process, o));
                    assert(s2.view().reach(process, o));
                    assert(sk.view().reach(process, o));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                } else if o != q {
                    assert(s1.view().reach(process, o));
                    assert(sc.view().reach(process, o));
                    assert(s2.view().reach(process, o));
                    assert(sk.view().reach(process, o));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                }
            }
            // No step unmapped anything, so every word init zeroed is still zero, and every core and
            // IOMMU is at or past epoch zero.
            assert forall|k: int, j: nat| 0 <= k < untyped && #[trigger] in_page_block(bs[k], j)
                implies s4.acknowledged(j as usize) by {
                assert(bs[k].0 + pow2(bs[k].1) <= NUM_PAGES);
                assert(s4.stale_epoch == s0.stale_epoch);
                assert(s0.stale_epoch.pages@[j as usize as int] == 0);
            }
            assert forall|r: usize| r < NUM_2M implies #[trigger] s4.region_acknowledged(Large::Two, r) by {
                assert(s4.stale_epoch == s0.stale_epoch);
                assert(s0.stale_epoch.two@[r as int] == 0);
            }
            assert forall|r: usize| r < NUM_1G implies #[trigger] s4.region_acknowledged(Large::One, r) by {
                assert(s4.stale_epoch == s0.stale_epoch);
                assert(s0.stale_epoch.one@[r as int] == 0);
            }
        }
        Some((untyped, frame))
    }

    /// Boot leaves the root's process sealed: its table is the only one, so no other table holds a
    /// slot naming it, and the rely serves it from its first step. See
    /// design/region-map-owns-the-address-space/.
    pub proof fn lemma_booted_sealed(
        &self,
        root: usize,
        process: usize,
        leaf: usize,
        frames: usize,
        t: usize,
        free: Seq<(usize, usize)>,
        image: Seq<ImageRun>,
        untyped: usize,
        frame: usize,
        present: Seq<bool>,
        kernel_root: usize,
    )
        requires
            self.booted(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root),
        ensures
            self.sealed(process),
    {
        assert forall|q: usize, j: usize| q != process && #[trigger] self.table_view(q).contains_key(j)
            implies !self.names_process(self.table_view(q)[j], process) by {
            assert(self.tables.roots@.dom().contains(q));
        }
    }
}

} // verus!
