//! Boot's one verified step for the capability kernel: init on the list's synthetic root, then the root
//! process with its table and thread, its console, its free memory as untyped capabilities and dom0's
//! image mapped in its space, each step's requires discharged by the previous steps' ensures and by what
//! kernel/src checked at the trust boundary of the pages and runs it passes. See
//! design/root-process-at-boot/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_frame::*;
use crate::capability::boot_image::*;
use crate::capability::boot_map::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::console::*;
use crate::capability::decompose::*;
use crate::capability::derive::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::mapping::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;
use crate::pagetable::pagemap::*;
use crate::pptr::PointsTo;

/// Page i is a page of one of the four blocks boot_root takes: the root's process at `process`, its
/// table's two leaves at `leaf` and `frames`, and its thread at `t`.
pub open spec fn in_root_blocks(process: usize, leaf: usize, frames: usize, t: usize, i: int) -> bool {
    ||| process / 4096 <= i < process / 4096 + 8
    ||| leaf / 4096 <= i < leaf / 4096 + 2
    ||| frames / 4096 <= i < frames / 4096 + 2
    ||| t / 4096 <= i < t / 4096 + 2
}

/// Page i is one the root reaches after boot: a page of its process's or its thread's block, of a free
/// run handed to it as untyped, or of one of dom0's image runs handed to it as frames.
pub open spec fn root_reach_page(process: usize, t: usize, free: Seq<(usize, usize)>, image: Seq<ImageRun>, i: int) -> bool {
    ||| process / 4096 <= i < process / 4096 + 8
    ||| t / 4096 <= i < t / 4096 + 2
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
        let tree = tree_of(&self.table_pages, &self.spaces);
        assert forall|p: SpacePath| !#[trigger] space_mapping(tree, s).contains_key(p) by {
            if tree.names_child(s, p.l4) {
                let c = (tree.entry(s, p.l4).addr - TABLE_NODE_PAGES * 4096) as usize;
                assert(tree.is_page(c));
                assert(tree.maps.contains_key(c));
            }
            assert(step(tree, s, p.l4) is None);
            assert(walk(tree, s, p) is None);
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
        assert(block_bytes(3) == 32768);
        assert forall|b: usize| #[trigger] block_within(b, 3, self.payload_of(self.root_untyped(process)))
            implies self.root_table_block(process, b) by {
            let base = b0.0 * 4096;
            assert(base <= self.blocks.page_count() * 4096);
            assert(self.payload_of(self.root_untyped(process)).base == base);
            assert(self.payload_of(self.root_untyped(process)).order as nat == b0.1);
            assert(block_bytes(b0.1 as u8) == pw * 4096);
            let bp = b as int / 4096;
            assert(bp * 4096 == b) by (nonlinear_arith)
                requires
                    b % 32768 == 0,
                    bp == b as int / 4096,
            ;
            assert(b0.0 <= bp);
            assert(bp + 8 <= b0.0 + pw);
            assert(self.blocks.tracks_run(bp, 8));
            assert(bp / 512 < NUM_2M) by (nonlinear_arith)
                requires
                    self.blocks.tracks(bp),
            ;
            assert(bp / 262144 < NUM_1G) by (nonlinear_arith)
                requires
                    self.blocks.tracks(bp),
            ;
            assert(!self.blocks.covered(bp));
            assert forall|k: int| 0 <= k < 8 implies #[trigger] self.blocks.pages@[b / 4096 + k].kind is Free by {
                assert(b0.0 <= bp + k < b0.0 + pw);
            }
        }
    }

    /// Boot of the capability kernel, from the memory boot set aside for it: init with the list's
    /// synthetic root at `root`, then boot_root with the root's process at `process`, its table's leaves
    /// at `leaf` and `frames` and its thread at `t`, boot_root_console, boot_root_memory over the free
    /// runs and boot_root_space over dom0's image runs. kernel/src checks at the trust boundary that the
    /// four blocks, the root page, the free runs and every 2M region of the image are pairwise disjoint,
    /// and hands over every page's permission in `pages`, which is split here between the steps. It
    /// returns how many untyped and frame capabilities the root holds, and refuses exactly when the free
    /// runs make no block or more than the first leaf holds, or the image does not fit the second leaf
    /// or the first untyped block's tables. On success each fixed slot of the root's table holds its
    /// kind, the root's space maps exactly the image, the root reaches exactly the console and the pages
    /// of its process, its thread, the free runs and the image, and nothing else reaches anything the
    /// root does not, besides itself. See design/root-process-at-boot/.
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
    ) -> (ret: Option<(usize, usize)>)
        requires
            old(self).cores.wf(),
            old(self).iommus.acked.wf(),
            old(self).stale_epoch.wf(),
            old(self).zeroing.cursor.wf(),
            old(self).zeroing.active_2m.wf(),
            old(self).zeroing.active_1g.wf(),
            old(self).blocks.pages.wf(),
            old(self).blocks.regions_2m.wf(),
            old(self).blocks.regions_1g.wf(),
            old(self).blocks.count_2m.wf(),
            old(self).blocks.count_1g.wf(),
            root % 4096 == 0,
            root + 4096 <= NODE_SPACE,
            root_perm.addr() == root,
            root_perm.is_init(),
            root_perm.value().nodes.wf(),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] root_perm.value().nodes@[k]).live,
            kernel_entries.wf(),
            iommus_present.wf(),
            iommu_commands.wf(iommus_present@),
            process % 32768 == 0,
            old(self).blocks.tracks_addr_run(process, 8),
            leaf % 8192 == 0,
            leaf != NO_LEAF,
            old(self).blocks.tracks_addr_run(leaf, 2),
            frames % 8192 == 0,
            frames != NO_LEAF,
            old(self).blocks.tracks_addr_run(frames, 2),
            t % 8192 == 0,
            old(self).blocks.tracks_addr_run(t, 2),
            process + 32768 <= leaf || leaf + 8192 <= process,
            process + 32768 <= frames || frames + 8192 <= process,
            process + 32768 <= t || t + 8192 <= process,
            leaf + 8192 <= frames || frames + 8192 <= leaf,
            leaf + 8192 <= t || t + 8192 <= leaf,
            frames + 8192 <= t || t + 8192 <= frames,
            !(process <= root < process + 32768),
            !(leaf <= root < leaf + 8192),
            !(frames <= root < frames + 8192),
            !(t <= root < t + 8192),
            runs_wf(free@),
            forall|j: int| #[trigger] in_runs(free@, free@.len() as int, j)
                ==> !in_root_blocks(process, leaf, frames, t, j) && j != root / 4096,
            image_runs_wf(image@),
            forall|j: int| #[trigger] image_region(image@, region_2m(j)) ==> {
                &&& old(self).blocks.tracks(j)
                &&& !in_root_blocks(process, leaf, frames, t, j)
                &&& !in_runs(free@, free@.len() as int, j)
                &&& j != root / 4096
            },
            forall|i: usize| in_root_blocks(process, leaf, frames, t, i as int) || in_runs(free@, free@.len() as int, i as int)
                ==> #[trigger] holds(pages, i),
            forall|j: usize| image_region(image@, region_2m(j as int)) ==> #[trigger] pages.contains_key(j),
            forall|j: usize| #[trigger] pages.contains_key(j) ==> pages[j].addr() == j * 4096,
        ensures
            ret is None <==> ({
                let bs = runs_blocks(free@, MAX_ORDER as nat);
                ||| bs.len() > ROOT_UNTYPED_SLOTS
                ||| bs.len() == 0
                ||| image_blocks(image@).len() > ROOT_FRAME_SLOTS
                ||| !image_virt_wf(image@)
                ||| image_tables_bound(image@) > untyped_tables(page_block_payload(bs[0]))
            }),
            ret matches Some((untyped, frame)) ==> {
                let bs = runs_blocks(free@, MAX_ORDER as nat);
                let b = tree_of(&final(self).table_pages, &final(self).spaces);
                &&& untyped == bs.len()
                &&& 0 < untyped <= ROOT_UNTYPED_SLOTS
                &&& frame == image_blocks(image@).len()
                &&& frame <= ROOT_FRAME_SLOTS
                &&& final(self).wf()
                &&& final(self).list.seq@[0] == root
                &&& final(self).slot_holds(process, ROOT_PROCESS_SLOT, (leaf + 1) as usize, process_of(process))
                &&& final(self).slot_holds(process, ROOT_THREAD_SLOT, (leaf + 2) as usize, thread_of(t))
                &&& final(self).slot_holds(process, ROOT_CONSOLE_SLOT, (leaf + 3) as usize, console_payload())
                &&& forall|k: int| 0 <= k < untyped ==> final(self).slot_holds(
                    process,
                    (ROOT_UNTYPED_SLOT + k) as usize,
                    (leaf + ROOT_UNTYPED_SLOT + k) as usize,
                    page_block_payload(#[trigger] bs[k]),
                )
                &&& forall|a: int, u: int| #![trigger crate::capability::boot_map::frame_slot(image@, a, u)]
                    0 <= a < image@.len() && 0 <= u < run_image_blocks(image@[a]).len() ==> {
                    let fb = run_image_blocks(image@[a])[u];
                    final(self).slot_holds(
                        process,
                        crate::capability::boot_map::frame_slot(image@, a, u),
                        (frames + 1 + image_offset(image@, a) + u) as usize,
                        boot_frame_payload((fb.0 * 4096) as usize, fb.1 as u8, image_rights(image@[a])),
                    )
                }
                &&& final(self).threads.records@.contains_key(t)
                &&& final(self).threads.records@[t].value().process == Some(process)
                &&& forall|a: int, x: int| 0 <= a < image@.len() && #[trigger] in_virt_at(image@, a, x) ==> {
                    &&& space_mapping(b, process).contains_key(page_path(x))
                    &&& space_mapping(b, process)[page_path(x)] == image_entry(image@[a], x)
                }
                &&& forall|p: SpacePath| #[trigger] space_mapping(b, process).contains_key(p) ==> image_path(image@, p)
                &&& forall|o: usize| #[trigger] final(self).view().reach(process, o) <==> (o == CONSOLE_OBJECT
                    || (o % 4096 == 0 && root_reach_page(process, t, free@, image@, (o / 4096) as int)))
                &&& forall|q: usize, o: usize| #[trigger] final(self).view().reach(q, o)
                    ==> o == q || final(self).view().reach(process, o)
            },
    {
        hide(CapKernel::wf);
        self.init(root, Tracked(root_perm), kernel_entries, iommus_present, iommu_commands);
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
        self.boot_root_console(root, process, leaf);
        let ghost s2 = *self;
        proof {
            assert(index_entry(ROOT_PROCESS_SLOT) == 0) by (compute_only);
            assert(index_slot(ROOT_PROCESS_SLOT) == 1) by (compute_only);
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s1.list.nodes@[j].live implies s2.list.nodes@[j].live by {
                assert(j != leaf + 3);
            }
            Self::lemma_slot_stays(s1, s2, process, ROOT_PROCESS_SLOT);
            assert forall|j: int| leaf + ROOT_UNTYPED_SLOT <= j < leaf + NODES_PER_PAGE implies !#[trigger] s2.list.nodes@[j].live by {
                assert(!s1.list.nodes@[j].live);
            }
            assert forall|i: int| s2.blocks.tracks(i) && in_runs(free@, len, i) implies (#[trigger] s2.blocks.pages@[i]).kind is Reserved by {
                assert(!in_root_blocks(process, leaf, frames, t, i));
                assert(s1.blocks.pages@[i].kind == s0.blocks.pages@[i].kind);
                assert(s0.blocks.pages@[i].kind is Reserved);
            }
            assert forall|p: usize| #[trigger] s2.list.pages@.dom().contains(p) && s2.blocks.tracks_addr(p)
                implies !in_runs(free@, len, (p / 4096) as int) by {
                assert(s1.list.pages@.dom().contains(p));
                if in_runs(free@, len, (p / 4096) as int) {
                    assert(!in_root_blocks(process, leaf, frames, t, (p / 4096) as int));
                    assert(p / 4096 != root / 4096);
                    assert(p == root || p == leaf || p == frames || p == t);
                }
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
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s2.list.nodes@[j].live implies s3.list.nodes@[j].live by {
                assert(!(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + untyped));
            }
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s1.list.nodes@[j].live implies s3.list.nodes@[j].live by {
                assert(s2.list.nodes@[j].live);
            }
            assert(s3.tables.roots == s1.tables.roots);
            // The root's process capability, and the untyped at ROOT_UNTYPED_SLOT.
            let n = (leaf + 1) as usize;
            assert(s2.is_cap(n) && s2.payload_of(n) == process_of(process));
            assert(s3.is_cap(n) && s3.payload_of(n) == process_of(process));
            assert(s3.tables.node_of(process, ROOT_PROCESS_SLOT) == n);
            assert(s3.root_untyped_at(root, process, leaf, 0, bs[0]));
            assert(s3.root_untyped(process) == leaf + ROOT_UNTYPED_SLOT);
            assert(!in_runs(free@, len, (process / 4096) as int)) by {
                if in_runs(free@, len, (process / 4096) as int) {
                    assert(!in_root_blocks(process, leaf, frames, t, (process / 4096) as int));
                }
            }
            assert(s3.blocks.pages@[(process / 4096) as int] == s1.blocks.pages@[(process / 4096) as int]);
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
                assert(!s2.list.nodes@[j].live);
                assert(!(leaf + ROOT_UNTYPED_SLOT <= j < leaf + ROOT_UNTYPED_SLOT + untyped));
            }
            // dom0's image lies in reserved 2M regions no large block is typed in, whose permissions
            // are what is left of pages.
            assert forall|q: int| #[trigger] image_region(image@, q) implies {
                &&& !s3.blocks.regions_2m@[q].typed
                &&& forall|j: int| q * 512 <= j < (q + 1) * 512 ==> #[trigger] s3.blocks.pages@[j].kind is Reserved
                &&& forall|j: usize| q * 512 <= j < (q + 1) * 512 ==> #[trigger] pages.contains_key(j)
            } by {
                lemma_fundamental_div_mod_converse(q * 512, 512, q, 0);
                assert(region_2m(q * 512) == q);
                assert(s3.blocks.tracks(q * 512));
                assert(0 <= q < NUM_2M);
                assert(s3.blocks.regions_2m@[q] == s0.blocks.regions_2m@[q]);
                assert forall|j: int| q * 512 <= j < (q + 1) * 512 implies #[trigger] s3.blocks.pages@[j].kind is Reserved by {
                    lemma_fundamental_div_mod_converse(j, 512, q, j - q * 512);
                    assert(region_2m(j) == q);
                    assert(image_region(image@, region_2m(j)));
                    assert(s3.blocks.pages@[j] == s2.blocks.pages@[j]);
                    assert(s1.blocks.pages@[j].kind == s0.blocks.pages@[j].kind);
                }
                assert forall|j: usize| q * 512 <= j < (q + 1) * 512 implies #[trigger] pages.contains_key(j) by {
                    lemma_fundamental_div_mod_converse(j as int, 512, q, j - q * 512);
                    assert(region_2m(j as int) == q);
                    assert(image_region(image@, region_2m(j as int)));
                    assert(given.contains_key(j));
                    assert(!k1.contains(j));
                    assert(!k2.contains(j));
                }
            }
            assert forall|j: usize| #[trigger] pages.contains_key(j) implies pages[j].addr() == j * 4096 by {
                assert(given.contains_key(j));
            }
            assert forall|p: usize| #[trigger] s3.list.pages@.dom().contains(p) && s3.blocks.tracks_addr(p)
                implies !image_region(image@, region_2m((p / 4096) as int)) by {
                assert(s1.list.pages@.dom().contains(p));
                if image_region(image@, region_2m((p / 4096) as int)) {
                    assert(!in_root_blocks(process, leaf, frames, t, (p / 4096) as int));
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
            // The process, thread and console slots.
            assert(index_entry(ROOT_THREAD_SLOT) == 0) by (compute_only);
            assert(index_entry(ROOT_CONSOLE_SLOT) == 0) by (compute_only);
            assert(index_ok(ROOT_THREAD_SLOT)) by (compute_only);
            assert(index_ok(ROOT_CONSOLE_SLOT)) by (compute_only);
            Self::lemma_slot_stays(s1, s4, process, ROOT_PROCESS_SLOT);
            Self::lemma_slot_stays(s1, s4, process, ROOT_THREAD_SLOT);
            assert(s2.tables.has_slot(&s2.list, process, ROOT_CONSOLE_SLOT));
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] s2.list.nodes@[j].live implies s4.list.nodes@[j].live by {
                assert(s3.list.nodes@[j].live);
            }
            Self::lemma_slot_stays(s2, s4, process, ROOT_CONSOLE_SLOT);
            assert(!(frames + 1 <= leaf + 1 < frames + 1 + frame));
            assert(!(frames + 1 <= leaf + 2 < frames + 1 + frame));
            assert(!(frames + 1 <= leaf + 3 < frames + 1 + frame));
            assert(s2.is_cap((leaf + 2) as usize) && s2.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(s3.is_cap((leaf + 1) as usize) && s3.payload_of((leaf + 1) as usize) == process_of(process));
            assert(s3.is_cap((leaf + 2) as usize) && s3.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(s3.is_cap((leaf + 3) as usize) && s3.payload_of((leaf + 3) as usize) == console_payload());
            assert(s4.is_cap((leaf + 1) as usize) && s4.payload_of((leaf + 1) as usize) == process_of(process));
            assert(s4.is_cap((leaf + 2) as usize) && s4.payload_of((leaf + 2) as usize) == thread_of(t));
            assert(s4.is_cap((leaf + 3) as usize) && s4.payload_of((leaf + 3) as usize) == console_payload());
            // The untyped slots.
            assert forall|k: int| 0 <= k < untyped implies s4.slot_holds(
                process,
                (ROOT_UNTYPED_SLOT + k) as usize,
                (leaf + ROOT_UNTYPED_SLOT + k) as usize,
                page_block_payload(#[trigger] bs[k]),
            ) by {
                let x = (leaf + ROOT_UNTYPED_SLOT + k) as usize;
                assert(s3.root_untyped_at(root, process, leaf, k, bs[k]));
                Self::lemma_slot_stays(s3, s4, process, (ROOT_UNTYPED_SLOT + k) as usize);
                assert(!(frames + 1 <= x < frames + 1 + frame));
                assert(s4.is_cap(x) && s4.payload_of(x) == s3.payload_of(x));
            }
            assert(s4.threads == s1.threads);
            // The root's reach is the four steps' growths in turn, and anyone else's grew only by
            // what the root's did.
            let phys = image_phys(image@);
            assert forall|o: usize| #[trigger] s4.view().reach(process, o) <==> (o == CONSOLE_OBJECT
                || (o % 4096 == 0 && root_reach_page(process, t, free@, image@, (o / 4096) as int))) by {
                assert(s4.view().reach(process, o) <==> (s3.view().reach(process, o)
                    || (o % 4096 == 0 && in_runs(phys, image@.len() as int, (o / 4096) as int))));
                assert(s3.view().reach(process, o) <==> (s2.view().reach(process, o)
                    || (o % 4096 == 0 && in_runs(free@, len, (o / 4096) as int))));
                assert(s2.view().reach(process, o) <==> (s1.view().reach(process, o) || o == CONSOLE_OBJECT));
                assert(s1.view().reach(process, o)
                    <==> (o % 4096 == 0 && ((process <= o < process + 32768) || (t <= o < t + 8192))));
                if o % 4096 == 0 {
                    assert((process <= o < process + 32768) <==> (process / 4096 <= o / 4096 < process / 4096 + 8))
                        by (nonlinear_arith)
                        requires
                            process % 32768 == 0,
                            o % 4096 == 0,
                    ;
                    assert((t <= o < t + 8192) <==> (t / 4096 <= o / 4096 < t / 4096 + 2)) by (nonlinear_arith)
                        requires
                            t % 8192 == 0,
                            o % 4096 == 0,
                    ;
                }
            }
            assert forall|q: usize, o: usize| #[trigger] s4.view().reach(q, o) implies o == q || s4.view().reach(process, o) by {
                if !s3.view().reach(q, o) {
                    assert(o % 4096 == 0 && in_runs(phys, image@.len() as int, (o / 4096) as int));
                    assert(s4.view().reach(process, o));
                } else if !s2.view().reach(q, o) {
                    assert(o % 4096 == 0 && in_runs(free@, len, (o / 4096) as int));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                } else if !s1.view().reach(q, o) {
                    assert(o == CONSOLE_OBJECT);
                    assert(s2.view().reach(process, o));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                } else if o != q {
                    assert(s1.view().reach(process, o));
                    assert(s2.view().reach(process, o));
                    assert(s3.view().reach(process, o));
                    assert(s4.view().reach(process, o));
                }
            }
        }
        Some((untyped, frame))
    }
}

} // verus!
