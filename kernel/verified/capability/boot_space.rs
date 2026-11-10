//! The boot step that hands the root dom0's image and maps it in the root's space: it checks up front
//! that the root's untyped at ROOT_UNTYPED_SLOT pays for the tables the runs need, then boot_root_image
//! makes each block of the image a frame capability at its fixed slot, boot_root_tables builds the
//! tables from that untyped, and boot_root_maps maps each page from its frame capability. A refusal
//! comes before any write. See design/root-process-at-boot/ and design/address-spaces-as-objects/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::block::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_frame::*;
use crate::capability::boot_image::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::derive::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
use crate::define::*;

impl CapKernel {
    /// What boot_root_tables reads of the root's survives the frame step. The frame step writes only
    /// the second leaf's slots from ROOT_FRAME_SLOT and the 2M regions of the image, whose pages are all
    /// reserved; the root's process and untyped capabilities lie in its first leaf, its space's page is
    /// a typed block's base, and its untyped's pages are free, so none of them is the frame step's.
    proof fn lemma_tables_ready_after_image(pre: Self, post: Self, process: usize, leaf2: usize, count: usize, runs: Seq<ImageRun>)
        requires
            pre.wf(),
            post.wf(),
            pre.root_tables_ready(process),
            pre.root_untyped_free(process),
            pre.payload_of(pre.tables.node_of(process, ROOT_PROCESS_SLOT)).kind is Process,
            pre.tables.leaf(process, 1) == leaf2,
            pre.tables.has_slot(&pre.list, process, ROOT_FRAME_SLOT),
            count <= ROOT_FRAME_SLOTS,
            forall|q: int| #[trigger] image_region(runs, q)
                ==> forall|j: int| q * 512 <= j < (q + 1) * 512 ==> #[trigger] pre.blocks.pages@[j].kind is Reserved,
            post.tables.roots == pre.tables.roots,
            post.tables.owner == pre.tables.owner,
            post.processes == pre.processes,
            post.threads == pre.threads,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && !(leaf2 + 1 <= j < leaf2 + 1 + count)
                ==> post.list.nodes@[j].live == pre.list.nodes@[j].live
                && post.list.nodes@[j].depth == pre.list.nodes@[j].depth,
            forall|x: usize| #![trigger post.is_cap(x)] #![trigger pre.is_cap(x)]
                !(leaf2 + 1 <= x < leaf2 + 1 + count) ==> post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #![trigger pre.is_cap(x)] #![trigger post.payload_of(x)]
                !(leaf2 + 1 <= x < leaf2 + 1 + count) && pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
            forall|q: int| 0 <= q < NUM_2M && !image_region(runs, q)
                ==> #[trigger] post.blocks.regions_2m@[q] == pre.blocks.regions_2m@[q],
            forall|j: int| pre.blocks.tracks(j) && !image_region(runs, region_2m(j))
                ==> #[trigger] post.blocks.pages@[j] == pre.blocks.pages@[j],
        ensures
            post.root_tables_ready(process),
            post.root_untyped_free(process),
            post.tables.node_of(process, ROOT_PROCESS_SLOT) == pre.tables.node_of(process, ROOT_PROCESS_SLOT),
            post.payload_of(pre.tables.node_of(process, ROOT_PROCESS_SLOT))
                == pre.payload_of(pre.tables.node_of(process, ROOT_PROCESS_SLOT)),
            post.root_space(process) == pre.root_space(process),
            post.root_untyped(process) == pre.root_untyped(process),
            post.payload_of(post.root_untyped(process)) == pre.payload_of(pre.root_untyped(process)),
    {
        let n = pre.tables.node_of(process, ROOT_PROCESS_SLOT);
        let u = pre.root_untyped(process);
        let l0 = pre.tables.leaf(process, 0);
        assert(index_entry(1usize) == 0 && index_slot(1usize) == 1) by (compute_only);
        assert(index_entry(5usize) == 0 && index_slot(5usize) == 5) by (compute_only);
        assert(index_entry(129usize) == 1) by (compute_only);
        pre.lemma_slot(process, ROOT_PROCESS_SLOT);
        pre.lemma_slot_bound(n);
        pre.lemma_slot(process, ROOT_UNTYPED_SLOT);
        pre.lemma_slot_bound(u);
        pre.tables.lemma_root(process);
        pre.tables.lemma_entry(process, 0);
        pre.tables.lemma_entry(process, 1);
        pre.tables.lemma_leaf(&pre.list, l0);
        pre.tables.lemma_leaf(&pre.list, leaf2);
        assert(l0 != leaf2);
        assert(n == l0 + 1);
        assert(u == l0 + 5);
        assert(!(leaf2 + 1 <= l0 < leaf2 + 1 + count));
        assert(!(leaf2 + 1 <= n < leaf2 + 1 + count));
        assert(!(leaf2 + 1 <= u < leaf2 + 1 + count));
        assert(post.list.nodes@[l0 as int].live);
        assert(post.is_cap(n));
        assert(post.is_cap(u));
        assert(post.payload_of(n) == pre.payload_of(n));
        assert(post.payload_of(u) == pre.payload_of(u));
        // The space's page is a typed block's base, so no image region holds it.
        pre.lemma_process_cap(n);
        let sp = (pre.root_space(process) / 4096) as int;
        if image_region(runs, region_2m(sp)) {
            assert(pre.blocks.pages@[sp].kind is Reserved);
        }
        assert(post.blocks.pages@[sp] == pre.blocks.pages@[sp]);
        assert(post.root_tables_ready(process));
        // Each order-3 block of the untyped is free, so no image region holds any of its pages.
        assert forall|b: usize| #[trigger] block_within(b, 3, post.payload_of(post.root_untyped(process)))
            implies post.root_table_block(process, b) by {
            assert(pre.root_table_block(process, b));
            assert forall|k: int| 0 <= k < 8 implies #[trigger] post.blocks.pages@[b / 4096 + k].kind is Free by {
                let j = b / 4096 + k;
                assert(pre.blocks.pages@[j].kind is Free);
                if image_region(runs, region_2m(j)) {
                    assert(pre.blocks.pages@[j].kind is Reserved);
                }
            }
            let j0 = (b / 4096) as int;
            assert(pre.blocks.pages@[j0 + 0].kind is Free);
            if image_region(runs, region_2m(j0)) {
                assert(pre.blocks.pages@[j0].kind is Reserved);
            }
            assert(post.blocks.regions_2m@[region_2m(j0)] == pre.blocks.regions_2m@[region_2m(j0)]);
        }
    }

    /// A free order-3 block of the root's untyped stays one while the capability tables stay and the
    /// block table types nothing more.
    proof fn lemma_table_block_kept(pre: Self, post: Self, process: usize, b: usize)
        requires
            pre.root_table_block(process, b),
            post.tables == pre.tables,
            kinds_kept(&pre.blocks, &post.blocks),
        ensures
            post.root_table_block(process, b),
    {
        let i = (b / 4096) as int;
        assert(pre.blocks.tracks(i));
        assert(0 <= region_2m(i) < NUM_2M);
        assert(0 <= region_1g(i) < NUM_1G);
        assert forall|k: int| 0 <= k < 8 implies #[trigger] post.blocks.pages@[b / 4096 + k].kind is Free by {
            assert(pre.blocks.tracks(b / 4096 + k));
            assert(pre.blocks.pages@[b / 4096 + k].kind is Free);
        }
    }

    /// The step after boot_root_memory that hands the root dom0's image and maps it in the root's space.
    /// It checks up front that the runs' virtual pages lie past the kernel's level 4 entries and that the
    /// root's untyped at ROOT_UNTYPED_SLOT holds the tables they need, then boot_root_image makes each
    /// block of the image a frame capability at its fixed slot, boot_root_tables builds the tables from
    /// that untyped, and boot_root_maps maps each virtual page of each run from the frame capability of
    /// its block. It refuses, changing nothing, exactly when the check fails or the blocks do not fit in
    /// the second leaf. On success the root's space maps exactly the runs' pages, each to its physical
    /// page with its run's rights and as a child of its block's frame capability; every other space is
    /// as it was; and the root's reach has grown by exactly the runs' physical pages, since the tables
    /// come from its own untyped, of whose order-3 blocks every one past those the tables can take is
    /// free as it was.
    #[verifier::spinoff_prover]
    pub fn boot_root_space(
        &mut self,
        root: usize,
        process: usize,
        leaf2: usize,
        runs: &[ImageRun],
        Tracked(perms): Tracked<Map<usize, PagePerm4k>>,
    ) -> (ret: Option<usize>)
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.leaf(process, 1) == leaf2,
            forall|i: usize| ROOT_FRAME_SLOT <= i < 2 * NODES_PER_PAGE ==> #[trigger] old(self).tables.has_slot(
                &old(self).list,
                process,
                i,
            ),
            forall|j: int| leaf2 + 1 <= j < leaf2 + NODES_PER_PAGE ==> !#[trigger] old(self).list.nodes@[j].live,
            image_runs_wf(runs@),
            forall|q: int| #[trigger] image_region(runs@, q) ==> {
                &&& !old(self).blocks.regions_2m@[q].typed
                &&& forall|j: int| q * 512 <= j < (q + 1) * 512 ==> #[trigger] old(self).blocks.pages@[j].kind is Reserved
                &&& forall|j: usize| q * 512 <= j < (q + 1) * 512 ==> #[trigger] perms.contains_key(j)
            },
            forall|j: usize| #[trigger] perms.contains_key(j) ==> perms[j].addr() == j * 4096,
            forall|p: usize| #[trigger] old(self).list.pages@.dom().contains(p) && old(self).blocks.tracks_addr(p)
                ==> !image_region(runs@, region_2m((p / 4096) as int)),
            old(self).root_tables_ready(process),
            old(self).root_untyped_free(process),
            old(self).payload_of(old(self).tables.node_of(process, ROOT_PROCESS_SLOT)).kind is Process,
            forall|p: SpacePath| !#[trigger] space_mapping(
                tree_of(&old(self).table_pages, &old(self).spaces),
                old(self).root_space(process),
            ).contains_key(p),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            ret is None <==> (image_blocks(runs@).len() > ROOT_FRAME_SLOTS || !image_virt_wf(runs@)
                || image_tables_bound(runs@) > untyped_tables(old(self).payload_of(old(self).root_untyped(process)))),
            ret is None ==> *final(self) == *old(self),
            ret matches Some(count) ==> {
                let s = old(self).root_space(process);
                let a0 = tree_of(&old(self).table_pages, &old(self).spaces);
                let b0 = tree_of(&final(self).table_pages, &final(self).spaces);
                let phys = image_phys(runs@);
                &&& count == image_blocks(runs@).len()
                &&& final(self).wf()
                &&& final(self).root_space(process) == s
                &&& final(self).processes == old(self).processes
                &&& final(self).threads == old(self).threads
                &&& final(self).list.seq@[0] == root
                &&& final(self).tables.roots == old(self).tables.roots
                &&& forall|j: int| 0 <= j < NODE_SPACE && #[trigger] old(self).list.nodes@[j].live ==> {
                    &&& final(self).list.nodes@[j].live
                    &&& final(self).list.nodes@[j].depth == old(self).list.nodes@[j].depth
                }
                &&& forall|j: int| image_tables_bound(runs@) <= j < untyped_tables(old(self).payload_of(old(self).root_untyped(process)))
                    ==> #[trigger] final(self).root_table_block(
                        process,
                        cursor_block(old(self).payload_of(old(self).root_untyped(process)).base, j),
                    )
                &&& forall|a: int, u: int| #![trigger crate::capability::boot_map::frame_slot(runs@, a, u)]
                    0 <= a < runs@.len() && 0 <= u < run_image_blocks(runs@[a]).len() ==> {
                    let fb = run_image_blocks(runs@[a])[u];
                    final(self).slot_holds(
                        process,
                        crate::capability::boot_map::frame_slot(runs@, a, u),
                        (leaf2 + 1 + image_offset(runs@, a) + u) as usize,
                        boot_frame_payload((fb.0 * 4096) as usize, fb.1 as u8, image_rights(runs@[a])),
                    )
                }
                &&& forall|a: int, x: int| 0 <= a < runs@.len() && #[trigger] in_virt_at(runs@, a, x) ==> {
                    &&& space_mapping(b0, s).contains_key(page_path(x))
                    &&& space_mapping(b0, s)[page_path(x)] == image_entry(runs@[a], x)
                }
                &&& forall|p: SpacePath| #[trigger] space_mapping(b0, s).contains_key(p) ==> image_path(runs@, p)
                &&& forall|t: usize| t != s ==> #[trigger] space_mapping(b0, t) == space_mapping(a0, t)
                &&& forall|j: usize| j < 512 && !image_l4(runs@, j) ==> #[trigger] b0.entry(s, j) == a0.entry(s, j)
                &&& !final(self).blocks.pages@[(s / 4096) as int].dead
                &&& forall|a: int, u: int, j: int| #![trigger crate::capability::boot_map::frame_slot(runs@, a, u), block_virt(runs@[a], u, j)]
                    0 <= a < runs@.len() && 0 <= u < run_image_blocks(runs@[a]).len()
                    && 0 <= j < pow2(run_image_blocks(runs@[a])[u].1) ==> {
                    let n = final(self).tables.node_of(process, crate::capability::boot_map::frame_slot(runs@, a, u));
                    let fb = run_image_blocks(runs@[a])[u];
                    &&& n == leaf2 + 1 + image_offset(runs@, a) + u
                    &&& final(self).payload_of(n) == boot_frame_payload((fb.0 * 4096) as usize, fb.1 as u8, image_rights(runs@[a]))
                    &&& final(self).list.is_child(n, page_node(b0, s, block_virt(runs@[a], u, j)))
                }
                &&& forall|x: usize| #![trigger old(self).is_cap(x)]
                    !(leaf2 + 1 <= x < leaf2 + 1 + count) && old(self).is_cap(x)
                    ==> final(self).is_cap(x) && final(self).payload_of(x) == old(self).payload_of(x)
                &&& forall|o: usize| #[trigger] final(self).view().reach(process, o)
                    <==> (old(self).view().reach(process, o) || (o % 4096 == 0
                        && in_runs(phys, runs@.len() as int, (o / 4096) as int)))
                &&& forall|q: usize, o: usize| #[trigger] final(self).view().reach(q, o) && !old(self).view().reach(q, o)
                    ==> o % 4096 == 0 && in_runs(phys, runs@.len() as int, (o / 4096) as int)
            },
    {
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a0 = tree_of(&pre.table_pages, &pre.spaces);
        let ghost n = pre.tables.node_of(process, ROOT_PROCESS_SLOT);
        let (s, untyped) = self.root_space_and_untyped(process);
        let cap = order_bytes(untyped.order) / 32768;
        proof {
            assert(cap as int == untyped_tables(untyped));
        }
        // The tables check, before any write.
        if !image_tables_fit(runs, cap) {
            return None;
        }
        let count = match self.boot_root_image(root, process, leaf2, runs, Tracked(perms)) {
            Some(count) => count,
            None => return None,
        };
        let ghost mid = *self;
        proof {
            assert(pre.tables.has_slot(&pre.list, process, ROOT_FRAME_SLOT));
            Self::lemma_tables_ready_after_image(pre, mid, process, leaf2, count, runs@);
            assert(tree_of(&mid.table_pages, &mid.spaces) == a0);
        }
        let ok = self.boot_root_tables(process, runs);
        let ghost tab = *self;
        proof {
            assert(ok);
            let t0 = tree_of(&tab.table_pages, &tab.spaces);
            assert(tab.payload_of(n) == pre.payload_of(n));
            assert(tab.root_space(process) == s);
            assert(tab.is_cap(n)) by {
                reveal(CapKernel::root_tables_ready);
            }
            tab.lemma_written_space(n);
            assert forall|a: int, u: int| #![trigger run_image_blocks(runs@[a])[u]]
                0 <= a < runs@.len() && 0 <= u < run_image_blocks(runs@[a]).len() implies tab.root_frame_at(
                    root,
                    process,
                    leaf2,
                    image_offset(runs@, a) + u,
                    run_image_blocks(runs@[a])[u],
                    image_rights(runs@[a]),
                ) by {
                assert(mid.root_frame_at(
                    root,
                    process,
                    leaf2,
                    image_offset(runs@, a) + u,
                    run_image_blocks(runs@[a])[u],
                    image_rights(runs@[a]),
                ));
            }
            assert forall|a: int, g: int| 0 <= a < runs@.len() && #[trigger] in_run_at(image_phys(runs@), a, g) implies {
                &&& tab.blocks.regions_2m@[g / PAGES_PER_2M as int].typed
                &&& tab.blocks.regions_2m@[g / PAGES_PER_2M as int].refs <= ROOT_FRAME_SLOTS
            } by {
                assert(region_2m(g) == g / PAGES_PER_2M as int);
                assert(image_region(runs@, g / PAGES_PER_2M as int));
            }
            assert forall|a: int, x: int| 0 <= a < runs@.len() && #[trigger] in_virt_at(runs@, a, x) implies {
                &&& walk_table(t0, s, page_path(x)) is Some
                &&& t0.entry(walk_table(t0, s, page_path(x))->0, page_path(x).l1).is_empty()
            } by {
            }
            assert(tab.maps_ready(root, process, leaf2, runs@));
        }
        self.boot_root_maps(Ghost(root), process, Ghost(leaf2), runs);
        proof {
            let post = *self;
            let t0 = tree_of(&tab.table_pages, &tab.spaces);
            let b0 = tree_of(&post.table_pages, &post.spaces);
            assert(Self::maps_done(tab, post, process, runs@));
            assert(post.root_space(process) == s);
            pre.lemma_slot(process, ROOT_FRAME_SLOT);
            pre.lemma_slot_bound(pre.tables.node_of(process, ROOT_FRAME_SLOT));
            assert(leaf2 < NODE_SPACE);
            assert forall|p: SpacePath| #[trigger] space_mapping(b0, s).contains_key(p) implies image_path(runs@, p) by {
                if !image_path(runs@, p) {
                    assert(space_mapping(t0, s) == space_mapping(a0, s));
                    assert(!space_mapping(a0, s).contains_key(p));
                }
            }
            assert forall|t: usize| t != s implies #[trigger] space_mapping(b0, t) == space_mapping(a0, t) by {
                assert(space_mapping(t0, t) == space_mapping(a0, t));
            }
            assert forall|a: int, u: int, j: int| #![trigger crate::capability::boot_map::frame_slot(runs@, a, u), block_virt(runs@[a], u, j)]
                0 <= a < runs@.len() && 0 <= u < run_image_blocks(runs@[a]).len()
                && 0 <= j < pow2(run_image_blocks(runs@[a])[u].1) implies {
                let nf = post.tables.node_of(process, crate::capability::boot_map::frame_slot(runs@, a, u));
                let fb = run_image_blocks(runs@[a])[u];
                &&& nf == leaf2 + 1 + image_offset(runs@, a) + u
                &&& post.payload_of(nf) == boot_frame_payload((fb.0 * 4096) as usize, fb.1 as u8, image_rights(runs@[a]))
                &&& post.list.is_child(nf, page_node(b0, s, block_virt(runs@[a], u, j)))
            } by {
                let fb = run_image_blocks(runs@[a])[u];
                assert(tab.root_frame_at(root, process, leaf2, image_offset(runs@, a) + u, fb, image_rights(runs@[a])));
                let x = block_virt(runs@[a], u, j);
                let nf = post.tables.node_of(process, crate::capability::boot_map::frame_slot(runs@, a, u));
                assert(walk_table(b0, s, page_path(x)) == walk_table(t0, s, page_path(x)));
                assert(page_node(b0, s, x) == page_node(t0, s, x));
                assert(post.tables == tab.tables);
                assert(crate::capability::boot_map::frame_slot(runs@, a, u) == (ROOT_FRAME_SLOT + (image_offset(runs@, a) + u)) as usize);
                assert(nf == leaf2 + 1 + image_offset(runs@, a) + u);
                assert(post.payload_of(nf) == tab.payload_of(nf));
                assert(post.payload_of(nf) == boot_frame_payload((fb.0 * 4096) as usize, fb.1 as u8, image_rights(runs@[a])));
                assert(post.list.is_child(tab.tables.node_of(process, crate::capability::boot_map::frame_slot(runs@, a, u)), page_node(t0, s, x)));
            }
            assert forall|x: usize| #![trigger pre.is_cap(x)]
                !(leaf2 + 1 <= x < leaf2 + 1 + count) && pre.is_cap(x)
                implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
                assert(mid.is_cap(x) && mid.payload_of(x) == pre.payload_of(x));
                assert(tab.is_cap(x) && tab.payload_of(x) == mid.payload_of(x));
                tab.lemma_slot_bound(x);
                assert(post.list.nodes@[x as int].live && post.list.nodes@[x as int].kind == tab.list.nodes@[x as int].kind);
            }
            // What the composed boot reads of the root's table afterwards: its roots, every live node,
            // and each frame slot.
            assert(post.list.seq@[0] == root);
            assert(post.tables.roots == pre.tables.roots);
            assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] pre.list.nodes@[j].live implies {
                &&& post.list.nodes@[j].live
                &&& post.list.nodes@[j].depth == pre.list.nodes@[j].depth
            } by {
                assert(!(leaf2 + 1 <= j < leaf2 + 1 + count));
                assert(mid.list.nodes@[j].live);
                assert(mid.list.nodes@[j].depth == pre.list.nodes@[j].depth);
                assert(tab.list.nodes@[j].live);
                assert(tab.list.nodes@[j].depth == mid.list.nodes@[j].depth);
                assert(post.list.nodes@[j].depth == tab.list.nodes@[j].depth);
            }
            // The untyped's blocks the tables left: the maps type nothing.
            let u = pre.payload_of(pre.root_untyped(process));
            assert forall|j: int| image_tables_bound(runs@) <= j < untyped_tables(u)
                implies #[trigger] post.root_table_block(process, cursor_block(u.base, j)) by {
                assert(tab.root_table_block(process, cursor_block(u.base, j)));
                Self::lemma_table_block_kept(tab, post, process, cursor_block(u.base, j));
            }
            assert forall|a: int, u: int| #![trigger crate::capability::boot_map::frame_slot(runs@, a, u)]
                0 <= a < runs@.len() && 0 <= u < run_image_blocks(runs@[a]).len() implies {
                let fb = run_image_blocks(runs@[a])[u];
                post.slot_holds(
                    process,
                    crate::capability::boot_map::frame_slot(runs@, a, u),
                    (leaf2 + 1 + image_offset(runs@, a) + u) as usize,
                    boot_frame_payload((fb.0 * 4096) as usize, fb.1 as u8, image_rights(runs@[a])),
                )
            } by {
                let fb = run_image_blocks(runs@[a])[u];
                let i = crate::capability::boot_map::frame_slot(runs@, a, u);
                let nf = (leaf2 + 1 + image_offset(runs@, a) + u) as usize;
                assert(tab.root_frame_at(root, process, leaf2, image_offset(runs@, a) + u, fb, image_rights(runs@[a])));
                assert(i == (ROOT_FRAME_SLOT + (image_offset(runs@, a) + u)) as usize);
                Self::lemma_slot_stays(tab, post, process, i);
                tab.lemma_slot_bound(nf);
                assert(post.list.nodes@[nf as int].live && post.list.nodes@[nf as int].kind == tab.list.nodes@[nf as int].kind);
                assert(post.is_cap(nf));
                assert(post.payload_of(nf) == tab.payload_of(nf));
            }
            // The root's level 4 entries that no run reaches: the tables step left them, and the maps
            // write only level 1 tables.
            assert(t0.is_root(s));
            assert(b0.is_root(s));
            post.lemma_table_base(s);
            tab.lemma_table_base(s);
            assert forall|j: usize| j < 512 && !image_l4(runs@, j) implies #[trigger] b0.entry(s, j) == a0.entry(s, j) by {
                assert(b0.entry(s, j) == t0.entry(s, j));
            }
            assert(!post.blocks.pages@[(s / 4096) as int].dead) by {
                reveal(CapKernel::root_tables_ready);
            }
            assert(post.wf());
            assert(count == image_blocks(runs@).len());
            assert(post.processes == pre.processes);
            assert(post.threads == pre.threads);
            assert forall|a: int, x: int| 0 <= a < runs@.len() && #[trigger] in_virt_at(runs@, a, x) implies {
                &&& space_mapping(b0, s).contains_key(page_path(x))
                &&& space_mapping(b0, s)[page_path(x)] == image_entry(runs@[a], x)
            } by {
            }
            assert forall|o: usize| #[trigger] post.view().reach(process, o)
                <==> (pre.view().reach(process, o) || (o % 4096 == 0
                    && in_runs(image_phys(runs@), runs@.len() as int, (o / 4096) as int))) by {
                assert(post.view().reach(process, o) == tab.view().reach(process, o));
                assert(tab.view().reach(process, o) == mid.view().reach(process, o));
            }
            assert forall|q: usize, o: usize| #[trigger] post.view().reach(q, o) && !pre.view().reach(q, o)
                implies o % 4096 == 0 && in_runs(image_phys(runs@), runs@.len() as int, (o / 4096) as int) by {
                assert(post.view().reach(q, o) == tab.view().reach(q, o));
                assert(tab.view().reach(q, o) == mid.view().reach(q, o));
            }
        }
        Some(count)
    }
}

} // verus!
