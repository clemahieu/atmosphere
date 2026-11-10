//! The boot step that hands the root a frame capability for a block of dom0's image. dom0's pages are
//! reserved, not free, so no untyped covers them: boot types the 2M region a block lies in as a large
//! frame, as retype types one, and the block's capability is a narrowed piece of it, as derive narrows
//! one. The region is never retyped, since no untyped covers it. See design/root-process-at-boot/ and
//! design/capability-names-a-block/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
#[cfg(verus_keep_ghost)]
use crate::capability::boot::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::steps::Steps;
use crate::define::*;

/// The frame capability boot hands the root for the block of order pages at base.
pub open spec fn boot_frame_payload(base: usize, order: u8, rights: u32) -> Payload {
    Payload { kind: CapKind::Frame, order, rights, base, badge: 0, reserved: 0 }
}

/// The 2M region the block at base lies in.
pub open spec fn frame_region(base: usize) -> usize {
    base / 4096 / PAGES_PER_2M
}

/// An aligned block of at most 512 pages lies in one 2M region, the one its first page is in.
pub proof fn lemma_block_in_2m(base: usize, order: u8)
    requires
        order <= 9,
        base as int % block_bytes(order) == 0,
    ensures
        base % 4096 == 0,
        frame_region(base) * 0x200000 <= base,
        base as int + block_bytes(order) <= (frame_region(base) + 1) * 0x200000,
{
    crate::capability::map::lemma_block_base_aligned(base, order);
    let p = pow2(order as nat) as int;
    lemma_pow2_pos(order as nat);
    lemma_pow2_adds(order as nat, (9 - order) as nat);
    lemma_pow2_pos((9 - order) as nat);
    lemma2_to64();
    let k = pow2((9 - order) as nat) as int;
    assert(p * k == 512);
    let s = block_bytes(order);
    assert(s == p * 4096);
    assert(s * k == 0x200000) by (nonlinear_arith)
        requires
            s == p * 4096,
            p * k == 512,
    ;
    lemma_div_denominator(base as int, 4096, 512);
    assert(frame_region(base) == base as int / 0x200000);
    lemma_fundamental_div_mod(base as int, 0x200000);
    let m = base as int % 0x200000;
    lemma_mod_mod(base as int, s, k);
    assert(m % s == 0);
    lemma_fundamental_div_mod(m, s);
    let t = m / s;
    assert(m == s * t);
    if t >= k {
        lemma_mul_inequality(k, t, s);
        assert(false);
    }
    lemma_mul_inequality(t + 1, k, s);
    assert(m + s <= 0x200000) by (nonlinear_arith)
        requires
            m == s * t,
            (t + 1) * s <= k * s,
            s * k == 0x200000,
    ;
}

impl CapKernel {
    /// The kernel after boot types the 2M region r, every page of which it reserved, as a large block
    /// with one reference and no holder yet, and takes its pages' permissions as a frame's. No object,
    /// frame or list page lies in a reserved page and no holder names the region, so every clause reads
    /// what it read before but the region's own, which reads as a block retype has typed and zeroed.
    pub proof fn lemma_reserved_typed_2m(pre: Self, post: Self, r: usize)
        requires
            pre.wf(),
            post.blocks.wf(),
            r < NUM_2M,
            !pre.blocks.regions_2m@[r as int].typed,
            !pre.blocks.regions_1g@[r as int / 512].typed,
            post.blocks.regions_2m@ == pre.blocks.regions_2m@.update(r as int,
                RegionEntry { typed: true, dead: false, torn_down: false, refs: 1 }),
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| r * 512 <= i < (r + 1) * 512 ==> #[trigger] pre.blocks.pages@[i].kind is Reserved,
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i]
                == if region_2m(i) == r { free_entry() } else { pre.blocks.pages@[i] },
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                ==> region_2m((p / 4096) as int) != r,
            post.frames_wf(),
            forall|i: usize| #[trigger] pre.frames@.contains_key(i) ==> post.frames@.contains_key(i),
            forall|i: usize| #[trigger] block_has_page(BlockRef::Two(r), i) ==> post.frames@.contains_key(i),
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
            post.zeroing == pre.zeroing,
            post.holders == pre.holders,
            post.stop_ipis == pre.stop_ipis,
        ensures
            post.wf(),
            !post.holders@.contains_key(BlockRef::Two(r)),
            !block_active(&post.zeroing, BlockRef::Two(r)),
    {
        let a = pre.blocks;
        let b = post.blocks;
        let two = BlockRef::Two(r);
        // A base or a member, before or after, is the same entry: the region's pages were neither.
        assert forall|i: int| a.tracks(i) && ((#[trigger] b.pages@[i]).kind is Base || b.pages@[i].kind is Member
            || a.pages@[i].kind is Base || a.pages@[i].kind is Member) implies b.pages@[i] == a.pages@[i] by {
            if region_2m(i) == r {
                assert(a.pages@[i].kind is Reserved);
            }
        }
        // Outside the region every page keeps its block. Inside it, each page was its own untyped block.
        assert forall|i: usize| a.tracks(i as int) implies {
            &&& region_2m(i as int) != r ==> #[trigger] block_ref(&b, i) == block_ref(&a, i)
            &&& region_2m(i as int) == r ==> {
                &&& block_ref(&a, i) == BlockRef::Small(i)
                &&& !block_typed(&a, BlockRef::Small(i))
                &&& block_ref(&b, i) == two
            }
        } by {
            lemma_region_of_region(i as int);
            if region_2m(i as int) == r {
                assert(a.pages@[i as int].kind is Reserved);
            }
        }
        assert forall|br: BlockRef| br != two implies #[trigger] block_typed(&b, br) == block_typed(&a, br) by {
            match br {
                BlockRef::Small(x) => {
                    if a.tracks(x as int) && region_2m(x as int) == r {
                        assert(a.pages@[x as int].kind is Reserved);
                    }
                },
                _ => {},
            }
        }
        assert forall|br: BlockRef| #[trigger] block_typed(&a, br) implies {
            &&& br != two
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
        assert(!pre.zeroing.active_2m@[r as int]);
        assert(!pre.holders@.contains_key(two));
        assert(zeroing_typed(&post.zeroing, &b)) by {
            assert forall|x: usize| #[trigger] post.zeroing.blocks@.contains_key(x) implies {
                &&& post.zeroing.blocks@[x] == PAGES_PER_2M ==> {
                    &&& b.regions_2m@[(x / PAGES_PER_2M) as int].typed
                    &&& !b.regions_2m@[(x / PAGES_PER_2M) as int].dead
                }
                &&& post.zeroing.blocks@[x] == PAGES_PER_1G ==> {
                    &&& b.regions_1g@[(x / PAGES_PER_1G) as int].typed
                    &&& !b.regions_1g@[(x / PAGES_PER_1G) as int].dead
                }
            } by {
                assert(pre.zeroing.blocks@.contains_key(x));
            }
        }
        assert(list_pages_used(&post.list, &b)) by {
            assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && b.tracks_addr(p) implies {
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
                &&& b.tracks(i as int)
                &&& frame_in_block(block_ref(&b, i), post.tables.payload_of(m))
                &&& post.holders@.contains_key(block_ref(&b, i))
                &&& post.holders@[block_ref(&b, i)].contains(m)
            } by {
                assert(pre.tables.is_cap(&pre.list, m));
                let i = pre.tables.payload_of(m).base / 4096;
                assert(block_typed(&a, block_ref(&a, i)));
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
                &&& b.tracks_addr(post.tables.payload_of(m).base)
                &&& block_ref(&b, post.tables.payload_of(m).base / 4096) == br
            } || (m < NODE_SPACE && post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Mapping)) by {
                assert(pre.holders@.contains_key(br));
                assert(block_typed(&a, br));
                assert(pre.holders@[br].contains(m));
                if pre.tables.is_cap(&pre.list, m) && pre.tables.payload_of(m).kind is Frame && a.tracks_addr(pre.tables.payload_of(m).base)
                    && block_ref(&a, pre.tables.payload_of(m).base / 4096) == br {
                    assert(block_ref(&b, pre.tables.payload_of(m).base / 4096) == br);
                }
            }
            assert forall|x: int| 0 <= x < NUM_2M && #[trigger] post.zeroing.active_2m@[x] implies {
                &&& b.regions_2m@[x].typed
                &&& b.regions_2m@[x].refs == 1
            } by {
                assert(pre.zeroing.active_2m@[x]);
            }
        }
        assert(objects_wf(&post.tables, &b, post.holders@)) by {
            assert forall|x: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(x)) implies b.pages@[x as int].object is Frame by {
                assert(block_typed(&a, BlockRef::Small(x)));
                assert(b.pages@[x as int] == a.pages@[x as int]);
            }
            assert forall|x: usize| b.tracks(x as int) && (#[trigger] b.pages@[x as int]).kind is Base
                && b.pages@[x as int].object is Frame implies {
                &&& b.pages@[x as int].order == 0
                &&& b.pages@[x as int].refs == 0 ==> post.holders@.contains_key(BlockRef::Small(x))
            } by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
            }
            assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
                &&& b.tracks_addr(l)
                &&& b.pages@[(l / 4096) as int].kind is Base
                &&& b.pages@[(l / 4096) as int].object is TableLeaf
                &&& b.pages@[(l / 4096) as int].order == 1
            } by {
                assert(a.pages@[(l / 4096) as int].kind is Base);
            }
            assert forall|x: usize| b.tracks(x as int) && #[trigger] leaf_block(&b, x)
                implies post.tables.owner@.contains_key((x * 4096) as usize) by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(leaf_block(&a, x));
            }
            assert forall|x: usize| x < NUM_2M && (#[trigger] b.regions_2m@[x as int]).typed
                && b.regions_2m@[x as int].refs == 0 implies post.holders@.contains_key(BlockRef::Two(x)) by {
                assert(x != r);
                assert(a.regions_2m@[x as int].typed);
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
            assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(&b, x)
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
            assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(&b, x)
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
            assert forall|x: usize| b.tracks(x as int) && #[trigger] thread_block(&b, x)
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
            assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(&b, x)
                implies post.processes.records@.contains_key((x * 4096) as usize) by {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(process_block(&a, x));
            }
        }
        assert(frames_held(post.frames@, post.holders@));
        assert forall|i: usize| pre.blocks.tracks(i as int) && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
            && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
            implies #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i) by {}
        Self::lemma_zeroing_changed(pre, post);
    }

    /// What the blocks owe the invariant once frame capability child, the only capability that
    /// changed, is the first holder of the region br boot typed for it.
    proof fn lemma_boot_frame_new(pre: Self, post: Self, child: usize, br: BlockRef)
        requires
            Self::derive_step(pre, post, child),
            child % 4096 != 0,
            post.is_cap(child),
            post.payload_of(child).kind is Frame,
            pre.blocks.tracks_addr(post.payload_of(child).base),
            block_ref(&pre.blocks, post.payload_of(child).base / 4096) == br,
            frame_in_block(br, post.payload_of(child)),
            br is Two,
            !pre.holders@.contains_key(br),
            block_typed(&pre.blocks, br),
            block_refs(&pre.blocks, br) == 1,
            !block_dead(&pre.blocks, br),
            !block_active(&pre.zeroing, br),
            forall|i: usize| #[trigger] block_has_page(br, i) ==> pre.frames@.contains_key(i),
            post.holders@ == pre.holders@.insert(br, set![child]),
            post.blocks == pre.blocks,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.list.pages@.dom() == pre.list.pages@.dom(),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            frames_held(post.frames@, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        pre.lemma_slot_not_owned(child);
        Self::lemma_same_leaf_nodes(pre, post, child, child);
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
        pre.lemma_slot_not_table_page(child);
        Self::lemma_same_table_nodes(pre, post, child, child);
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
        lemma_spaces_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks);
        lemma_threads_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks);
        lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
        lemma_holders_frame_new(
            &pre.list,
            &pre.tables,
            &post.list,
            &post.tables,
            &pre.blocks,
            &pre.zeroing,
            pre.holders@,
            child,
            br,
        );
        assert(frames_held(post.frames@, post.holders@)) by {
            assert forall|k: BlockRef, i: usize| #[trigger] post.holders@.contains_key(k) && #[trigger] block_has_page(k, i)
                implies post.frames@.contains_key(i) by {
                if k != br {
                    assert(pre.holders@.contains_key(k));
                }
            }
        }
        assert(objects_wf(&post.tables, &post.blocks, post.holders@)) by {
            assert forall|x: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(x)) implies post.blocks.pages@[x as int].object is Frame by {
                assert(pre.holders@.contains_key(BlockRef::Small(x)));
            }
        }
    }

    /// What the blocks owe the invariant once frame capability child, the only capability that
    /// changed, joins the holders of the region br an earlier boot step typed, with one more reference.
    proof fn lemma_boot_frame_joins(pre: Self, post: Self, child: usize, br: BlockRef)
        requires
            Self::derive_step(pre, post, child),
            child % 4096 != 0,
            post.is_cap(child),
            post.payload_of(child).kind is Frame,
            pre.blocks.tracks_addr(post.payload_of(child).base),
            block_ref(&pre.blocks, post.payload_of(child).base / 4096) == br,
            frame_in_block(br, post.payload_of(child)),
            br is Two,
            pre.holders@.contains_key(br),
            block_refs(&pre.blocks, br) < usize::MAX,
            blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br)),
            post.holders@ == pre.holders@.insert(br, pre.holders@[br].insert(child)),
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.list.pages@.dom() == pre.list.pages@.dom(),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            frames_held(post.frames@, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        pre.lemma_slot_not_owned(child);
        Self::lemma_same_leaf_nodes(pre, post, child, child);
        pre.lemma_slot_not_table_page(child);
        Self::lemma_same_table_nodes(pre, post, child, child);
        let refs = (block_refs(&pre.blocks, br) + 1) as usize;
        let dead = block_dead(&pre.blocks, br);
        lemma_holders_frame_added(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, child, br);
        lemma_zeroing_typed_refs_changed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, br, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert forall|x: BlockRef| #[trigger] post.holders@.contains_key(x) == pre.holders@.contains_key(x) by {}
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_refs_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, post.holders@, br, refs, dead);
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_refs_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, br, refs, dead);
        lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, refs, dead);
        assert(frames_held(post.frames@, post.holders@)) by {
            assert forall|k: BlockRef, i: usize| #[trigger] post.holders@.contains_key(k) && #[trigger] block_has_page(k, i)
                implies post.frames@.contains_key(i) by {
                assert(pre.holders@.contains_key(k));
            }
        }
    }

    /// A frame capability covers exactly its block's pages.
    proof fn lemma_frame_covers(s: Self, child: usize, base: usize, order: u8, rights: u32)
        requires
            s.is_cap(child),
            s.payload_of(child) == boot_frame_payload(base, order, rights),
        ensures
            forall|o: ObjectId| #[trigger] s.view().covers(child, o) <==> in_block(base, order, o),
    {
        let b = s.view();
        assert(b.names[child] == base && b.pages[child] == pow2(order as nat));
    }

    /// The step after boot_root_untyped, once per block of dom0's image: a frame capability for the
    /// aligned block of order pages at base, at most 512, in slot i of the root's second leaf, below
    /// the list's synthetic root as the root's other capabilities are. The block lies in the 2M region
    /// r = frame_region(base). The first block in r types it as a large frame, its pages Reserved to
    /// Free under the region, so nothing becomes free, and hands the kernel their permissions as a
    /// frame's; a later block in r finds it typed. Either way the capability takes one reference on r
    /// and joins its holders. It carries no control, so the root's reach grows by the block's pages and
    /// nobody else's by anything outside them. See design/root-process-at-boot/.
    pub fn boot_root_frame(
        &mut self,
        root: usize,
        process: usize,
        leaf2: usize,
        i: usize,
        base: usize,
        order: u8,
        rights: u32,
        Tracked(perms): Tracked<Map<usize, PagePerm4k>>,
    )
        requires
            old(self).wf(),
            root == old(self).list.seq@[0],
            old(self).tables.has_slot(&old(self).list, process, i),
            old(self).tables.leaf(process, 1) == leaf2,
            ROOT_FRAME_SLOT <= i < 2 * NODES_PER_PAGE,
            !old(self).list.nodes@[leaf2 + (i - NODES_PER_PAGE)].live,
            order <= 9,
            base as int % block_bytes(order) == 0,
            old(self).blocks.tracks_addr(base),
            rights & CONTROL_RIGHT == 0,
            forall|j: usize| #[trigger] perms.contains_key(j) ==> perms[j].addr() == j * 4096,
            old(self).blocks.regions_2m@[frame_region(base) as int].typed ==> {
                &&& old(self).holders@.contains_key(BlockRef::Two(frame_region(base)))
                &&& !old(self).blocks.regions_2m@[frame_region(base) as int].dead
                &&& old(self).blocks.regions_2m@[frame_region(base) as int].refs < usize::MAX
            },
            !old(self).blocks.regions_2m@[frame_region(base) as int].typed ==> {
                &&& forall|j: int| frame_region(base) * 512 <= j < (frame_region(base) + 1) * 512
                    ==> #[trigger] old(self).blocks.pages@[j].kind is Reserved
                &&& forall|j: usize| frame_region(base) * 512 <= j < (frame_region(base) + 1) * 512
                    ==> #[trigger] perms.contains_key(j)
                &&& forall|p: usize| #[trigger] old(self).list.pages@.dom().contains(p) && old(self).blocks.tracks_addr(p)
                    ==> region_2m((p / 4096) as int) != frame_region(base)
            },
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).wf(),
            final(self).list.seq@[0] == root,
            final(self).tables.roots == old(self).tables.roots,
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.has_slot(&final(self).list, process, i),
            final(self).tables.node_of(process, i) == leaf2 + (i - NODES_PER_PAGE),
            final(self).is_cap((leaf2 + (i - NODES_PER_PAGE)) as usize),
            final(self).payload_of((leaf2 + (i - NODES_PER_PAGE)) as usize) == boot_frame_payload(base, order, rights),
            final(self).list.is_child(root, (leaf2 + (i - NODES_PER_PAGE)) as usize),
            final(self).list.nodes@[leaf2 + (i - NODES_PER_PAGE)].depth == 1,
            Self::adds_cap(*old(self), *final(self), (leaf2 + (i - NODES_PER_PAGE)) as usize),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j != leaf2 + (i - NODES_PER_PAGE)
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live
                && final(self).list.nodes@[j].depth == old(self).list.nodes@[j].depth,
            final(self).list.parent@ == old(self).list.parent@.insert((leaf2 + (i - NODES_PER_PAGE)) as usize, root),
            ({
                let r = frame_region(base);
                let held = if old(self).holders@.contains_key(BlockRef::Two(r)) {
                    old(self).holders@[BlockRef::Two(r)]
                } else {
                    Set::<usize>::empty()
                };
                let refs = if old(self).blocks.regions_2m@[r as int].typed { old(self).blocks.regions_2m@[r as int].refs as int } else { 0 };
                &&& final(self).blocks.regions_2m@[r as int].typed
                &&& !final(self).blocks.regions_2m@[r as int].dead
                &&& final(self).blocks.regions_2m@[r as int].refs == refs + 1
                &&& final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@.update(r as int, final(self).blocks.regions_2m@[r as int])
                &&& final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@
                &&& final(self).holders@ == old(self).holders@.insert(BlockRef::Two(r), held.insert((leaf2 + (i - NODES_PER_PAGE)) as usize))
                &&& forall|j: int| old(self).blocks.tracks(j) && region_2m(j) != r ==> #[trigger] final(self).blocks.pages@[j] == old(self).blocks.pages@[j]
            }),
            final(self).blocks.free_perms == old(self).blocks.free_perms,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            final(self).table_pages == old(self).table_pages,
            final(self).list.pages@.dom() == old(self).list.pages@.dom(),
            forall|o: usize| #[trigger] final(self).view().reach(process, o)
                <==> (old(self).view().reach(process, o) || in_block(base, order, o)),
            forall|r: usize, o: usize| #[trigger] final(self).view().reach(r, o) && !old(self).view().reach(r, o)
                ==> in_block(base, order, o),
    {
        let ghost pre = *old(self);
        let r = base / 4096 / PAGES_PER_2M;
        proof {
            lemma_block_in_2m(base, order);
            assert(r == frame_region(base));
            assert(r < NUM_2M);
            pre.lemma_slot(process, i);
            assert(index_entry(i) == 1);
            assert(index_slot(i) == i - NODES_PER_PAGE);
            assert(pre.tables.node_of(process, i) == leaf2 + (i - NODES_PER_PAGE));
            pre.lemma_slot_bound(pre.tables.node_of(process, i));
            pre.list.lemma_link(0);
            pre.list.lemma_live_valid(root);
            pre.list.lemma_valid_bound(root);
            pre.list.lemma_seq_fits();
            assert(pre.list.nodes@[root as int].depth == 0);
        }
        let child = leaf2 + (i - NODES_PER_PAGE);
        let typed = self.blocks.region(Large::Two, r).typed;
        if !typed {
            // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
            let tracked mut steps = Steps::fresh();
            self.blocks.type_reserved_2m(r, Tracked(&mut steps));
            proof {
                self.frames.borrow_mut().tracked_union_prefer_right(perms);
                let me = *self;
                assert(me.frames_wf()) by {
                    assert forall|j: usize| #[trigger] me.frames@.contains_key(j) implies me.frames@[j].addr() == j * 4096 by {
                        if !perms.contains_key(j) {
                            assert(pre.frames@.contains_key(j));
                        }
                    }
                }
                assert forall|j: usize| #[trigger] block_has_page(BlockRef::Two(r), j) implies me.frames@.contains_key(j) by {
                    assert(perms.contains_key(j));
                }
                Self::lemma_reserved_typed_2m(pre, me, r);
            }
        }
        let ghost mid = *self;
        proof {
            assert(mid.wf());
            assert(mid.list == pre.list && mid.tables == pre.tables);
            assert(mid.view() == pre.view());
            lemma_region_2m_of_bytes(base as int, r);
            assert(block_ref(&mid.blocks, base / 4096) == BlockRef::Two(r));
        }
        if typed {
            let added = self.blocks.add_large_ref(Large::Two, r);
            proof {
                assert(added);
                lemma_same_structure(&mid.blocks, &self.blocks);
                assert(blocks_refs_changed(&mid.blocks, &self.blocks, BlockRef::Two(r),
                    (block_refs(&mid.blocks, BlockRef::Two(r)) + 1) as usize, block_dead(&mid.blocks, BlockRef::Two(r))));
            }
        }
        self.list.derive(root, child, NodeKind::Capability);
        proof {
            mid.tables.lemma_wf_same_pages(&mid.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            process,
            i,
            Payload { kind: CapKind::Frame, order, rights, base, badge: 0, reserved: 0 },
        );
        self.holders = Ghost(if typed {
            mid.holders@.insert(BlockRef::Two(r), mid.holders@[BlockRef::Two(r)].insert(child))
        } else {
            mid.holders@.insert(BlockRef::Two(r), set![child])
        });
        proof {
            let post = *self;
            let br = BlockRef::Two(r);
            assert(post.payload_of(child) == boot_frame_payload(base, order, rights));
            assert(payload_wf(post.payload_of(child)));
            Self::lemma_derive_caps_wf(mid, post, child);
            Self::lemma_hidden_frame(mid, post, child, child);
            Self::lemma_table_nodes_caps_frame(mid, post, child, child);
            Self::lemma_space_nodes_caps_frame(mid, post, child, child);
            Self::lemma_bindings_caps_frame(mid, post, child, child);
            Self::lemma_devices_caps_frame(mid, post, child, child);
            if typed {
                Self::lemma_boot_frame_joins(mid, post, child, br);
            } else {
                Self::lemma_boot_frame_new(mid, post, child, br);
            }
            lemma_parents_derived(mid.list, post.list, root, child);
            Self::lemma_tlb_same(mid, post);
            assert(post.wf());
            Self::lemma_derive_step_adds_cap(mid, post, child);
            lemma_has(post.list.seq@, child);
            assert(post.list.is_child(root, child));
            assert(post.tables.has_slot(&post.list, process, i));
            Self::lemma_boot_held_view(mid, post, root, process, i, child);
            Self::lemma_frame_covers(post, child, base, order, rights);
            let live = |x: NodeId| x < NODE_SPACE && mid.list.nodes@[x as int].live;
            lemma_adds_held_reach(mid.view(), post.view(), process, root, child, live);
            assert forall|o: usize| #[trigger] post.view().reach(process, o)
                <==> (pre.view().reach(process, o) || in_block(base, order, o)) by {
                assert(post.view().covers(child, o) == in_block(base, order, o));
            }
            assert forall|r: usize, o: usize| #[trigger] post.view().reach(r, o) && !pre.view().reach(r, o)
                implies in_block(base, order, o) by {
                assert(post.view().covers(child, o) == in_block(base, order, o));
            }
            Self::lemma_derive_step_adds_cap(pre, post, child);
            if !typed {
                assert(set![child] =~= Set::<usize>::empty().insert(child));
            }
        }
    }
}

} // verus!
