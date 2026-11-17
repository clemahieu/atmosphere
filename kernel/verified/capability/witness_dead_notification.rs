// SPDX-License-Identifier: MIT

//! The witness that a dead notification's teardown wakes a thread blocked on it with an error,
//! then frees the block. It lives beside `witness` so that file stays within the size the gate
//! allows. Only Verus compiles this module, so no image contains it.
//! design/teardown-driven-by-retype/, design/witness-per-way-an-operation-succeeds/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_kernel::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::charge::*;
use crate::capability::cpu::*;
use crate::capability::decompose::*;
use crate::capability::delete::*;
use crate::capability::derive::*;
use crate::capability::destroy::*;
use crate::capability::endpoint::*;
use crate::capability::device_space::{device_path, device_range_bytes, DeviceRange};
use crate::capability::guest_space::{guest_path, guest_range_bytes, GuestPhysRange};
use crate::capability::device::{
    binding_device, binding_node, bound_record, device_of, device_payload, lemma_device_object, devices_wf, DeviceInfo, IOMMU_DEVICES, MAX_DEVICES,
};
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::notification::*;
use crate::capability::operation::Outcome;
use crate::capability::position::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::reclaim_process::*;
use crate::capability::reclaim_thread::*;
use crate::capability::refs::*;
use crate::capability::reply::*;
use crate::capability::retype::*;
use crate::capability::revoke::*;
use crate::capability::schedule::*;
use crate::capability::space::*;
use crate::capability::steps::*;
use crate::capability::switch::*;
use crate::arch::{outcome_written, partial_frame, report_tags_tlb, saved_frame, user_frame, user_rip, FrameKind, Processor, Registers};
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;
use crate::capability::witness::{
    lemma_added_children, lemma_block_page, lemma_slot_kept_but, lemma_slot_kept_two,
    lemma_tables_bound_nonneg, witness_alive, witness_block, witness_root, WITNESS_FRAME_SLOT,
    WITNESS_PROCESS_SLOT, WITNESS_THREAD_SLOT,
};

impl CapKernel {
    /// Addresses, core 1 and the free pages the waiter witness retypes, taken from `booted` here so the
    /// witness can hide `booted` and not carry its quantifiers for the rest of the query.
    #[verifier::spinoff_prover]
    proof fn lemma_wakes_waiter_prepared(
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
        base: usize,
    )
        requires
            self.booted(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root),
            image_tables_bound(image) + 2 <= untyped_tables(page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0]).base, image_tables_bound(image)),
        ensures
            self.wf(),
            self.root_live(process),
            self.tables.roots@.contains_key(process),
            self.processes.records@.contains_key(process),
            !self.processes.records@[process].value().dead,
            self.cores@.len() == NUM_CPUS,
            ({
                let u = (leaf + ROOT_UNTYPED_SLOT) as usize;
                let cs = (ROOT_CORE_SLOT + 1) as usize;
                let core_cap = (leaf + cs) as usize;
                let b2 = (base + PROCESS_BYTES) as usize;
                let bt = (b2 + 2 * PAGE_SZ) as usize;
                let bl = (b2 + 4 * PAGE_SZ) as usize;
                let bn = (b2 + 6 * PAGE_SZ) as usize;
                let first = page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0]);
                &&& self.slot_holds(process, ROOT_UNTYPED_SLOT, u, first)
                &&& self.list.nodes@[u as int].live
                &&& self.list.nodes@[u as int].depth == 1
                &&& self.tables.is_cap(&self.list, u)
                &&& self.slot_holds(process, cs, core_cap, core_payload(1, MAX_PRIORITY))
                &&& self.list.nodes@[core_cap as int].depth == 1
                &&& self.cores@[1].current_thread is None
                &&& self.cores@[1].generation == 1
                &&& self.cores@[1].next_pcid == 1
                &&& self.cores@[1].space is None
                &&& base + 2 * PROCESS_BYTES <= NODE_SPACE
                &&& base % PROCESS_BYTES == 0
                &&& bt == (base + 10 * PAGE_SZ) as usize
                &&& bn == (base + 14 * PAGE_SZ) as usize
                &&& bn % PAGE_SZ == 0
                &&& b2 % PAGE_SZ == 0
                &&& b2 / PAGE_SZ == base / PAGE_SZ + 8
                &&& bt / PAGE_SZ == b2 / PAGE_SZ + 2
                &&& bl / PAGE_SZ == b2 / PAGE_SZ + 4
                &&& bn / PAGE_SZ == b2 / PAGE_SZ + 6
                &&& forall|i: int| base / PAGE_SZ <= i < base / PAGE_SZ + 8
                    ==> #[trigger] self.blocks.pages@[i].kind is Free
                &&& forall|i: int| b2 / PAGE_SZ <= i < b2 / PAGE_SZ + 8
                    ==> #[trigger] self.blocks.pages@[i].kind is Free
                &&& self.destination_at(process, None) == Some(process)
                &&& self.tables.leaf(process, 2) == NO_LEAF
                &&& self.can_retype_under(process, ROOT_UNTYPED_SLOT, b2, 1)
                &&& self.blocks.small_free((b2 / PAGE_SZ) as int, 1)
                &&& self.can_retype_leaf(process, ROOT_UNTYPED_SLOT, Position { through: None, index: 2 }, b2)
                &&& self.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3)
                &&& self.blocks.small_free((base / PAGE_SZ) as int, 3)
                &&& self.blocks.tracks_addr_run(base, order_pages(3))
                &&& self.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER)
                &&& self.blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize)
                &&& self.blocks.tracks_addr_run(bt, order_pages(THREAD_ORDER as usize))
                &&& self.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1)
                &&& self.blocks.small_free((bl / PAGE_SZ) as int, 1)
                &&& self.blocks.tracks_addr_run(bl, order_pages(1))
                &&& self.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0)
                &&& self.blocks.small_free((bn / PAGE_SZ) as int, 0)
                &&& self.blocks.tracks_addr_run(bn, order_pages(0))
            }),
    {
        let s0 = *self;
        let bs = runs_blocks(free, MAX_ORDER as nat);
        let first = page_block_payload(bs[0]);
        let itb = image_tables_bound(image);
        let u = (leaf + ROOT_UNTYPED_SLOT) as usize;
        let cs = (ROOT_CORE_SLOT + 1) as usize;
        let core_cap = (leaf + cs) as usize;
        lemma2_to64();
        lemma_tables_bound_nonneg(image);
        assert(0 < untyped);
        assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
        assert(1usize < NUM_CPUS) by (compute_only);
        assert(s0.slot_holds(process, cs, core_cap, core_payload(1, MAX_PRIORITY))) by {
            reveal(CapKernel::booted);
        }
        assert(s0.list.nodes@[core_cap as int].depth == 1) by {
            reveal(CapKernel::booted);
        }
        assert(s0.tables.caps_wf(&s0.list)) by {
            reveal(CapKernel::wf);
        }
        assert(s0.cores@.len() == NUM_CPUS) by {
            reveal(CapKernel::wf);
        }
        assert(s0.cores@[1].current_thread is None && s0.cores@[1].generation == 1
            && s0.cores@[1].next_pcid == 1 && s0.cores@[1].space is None) by {
            reveal(CapKernel::booted);
        }
        assert(s0.tables.is_cap(&s0.list, u));
        assert(s0.list.nodes@[u as int].live);
        assert(s0.list.nodes@[u as int].depth == 1) by {
            reveal(CapKernel::booted);
        }
        assert(cap_wf(first));
        assert(payload_wf(first));
        assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
        assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
        assert(s0.processes.records@.contains_key(process) && !s0.processes.records@[process].value().dead) by {
            reveal(CapKernel::booted);
            reveal(CapKernel::wf);
        }
        assert(s0.root_live(process));
        assert(s0.tables.roots@.contains_key(process)) by {
            reveal(CapKernel::booted);
        }
        assert(s0.wf());
        assert(witness_root(s0, process, u, first));
        assert(s0.root_untyped(process) == u);
        lemma_pow2_pos(first.order as nat);
        lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
        lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
        assert((itb + 2) * PROCESS_BYTES <= block_bytes(first.order));
        assert(first.base + block_bytes(first.order) <= NODE_SPACE);
        assert(base == first.base + itb * PROCESS_BYTES);
        assert(base + 2 * PROCESS_BYTES <= NODE_SPACE);
        assert(cursor_block(first.base, itb) == base);
        assert(cursor_block(first.base, itb + 1) == base + PROCESS_BYTES);
        assert(s0.root_table_block(process, cursor_block(first.base, itb)));
        assert(s0.root_table_block(process, cursor_block(first.base, itb + 1)));
        assert(witness_block(s0, base, first));
        assert(witness_block(s0, (base + PROCESS_BYTES) as usize, first));
        assert(block_bytes(3) == PROCESS_BYTES);
        assert(block_bytes(1) == 2 * PAGE_SZ);
        assert(block_bytes(0) == PAGE_SZ);
        assert(base % PROCESS_BYTES == 0);
        s0.lemma_page_span();
        lemma_runs_blocks(free, MAX_ORDER as nat, s0.blocks.page_count());
        let b0 = bs[0];
        assert(first.base == b0.0 * PAGE_SZ);
        assert((b0.1 as u8) as nat == b0.1);
        lemma_fundamental_div_mod_converse(base as int, PAGE_SZ as int, b0.0 + 8 * itb, 0);
        assert(base / PAGE_SZ == b0.0 + 8 * itb);
        let b2 = (base + PROCESS_BYTES) as usize;
        let bt = (b2 + 2 * PAGE_SZ) as usize;
        let bl = (b2 + 4 * PAGE_SZ) as usize;
        let bn = (b2 + 6 * PAGE_SZ) as usize;
        lemma_block_page(base, 0);
        lemma_block_page(b2, 0);
        lemma_block_page(b2, 2);
        lemma_block_page(b2, 4);
        lemma_block_page(b2, 6);
        assert(b2 % PROCESS_BYTES == 0);
        assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
        assert(bt / PAGE_SZ == b2 / PAGE_SZ + 2);
        assert(bl / PAGE_SZ == b2 / PAGE_SZ + 4);
        assert(bn / PAGE_SZ == b2 / PAGE_SZ + 6);
        assert(bt == (base + 10 * PAGE_SZ) as usize);
        assert(bn == (base + 14 * PAGE_SZ) as usize);
        assert(bn % PAGE_SZ == 0);
        assert(b2 % PAGE_SZ == 0);
        assert forall|i: int| base / PAGE_SZ <= i < base / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
            assert(s0.blocks.pages@[base / PAGE_SZ + (i - base / PAGE_SZ)].kind is Free);
        }
        assert forall|i: int| b2 / PAGE_SZ <= i < b2 / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
            assert(s0.blocks.pages@[b2 / PAGE_SZ + (i - b2 / PAGE_SZ)].kind is Free);
        }
        assert(s0.destination_at(process, None) == Some(process));
        assert(s0.tables.leaf(process, 2) == NO_LEAF);
        assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b2, 1));
        assert(s0.blocks.small_free((b2 / PAGE_SZ) as int, 1));
        assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, Position { through: None, index: 2 }, b2));
        assert(s0.payload_of(u) == first);
        assert(block_within(base, 3, first));
        assert(1 < MAX_DEPTH) by (compute_only);
        assert(s0.list.nodes@[u as int].depth < MAX_DEPTH);
        assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
        assert(s0.blocks.small_free((base / PAGE_SZ) as int, 3));
        assert(witness_block(s0, base, first));
        assert(witness_block(s0, b2, first));
        assert(s0.blocks.tracks_addr_run(base, order_pages(3)));
        assert(!s0.blocks.covered((b2 / PAGE_SZ) as int));
        assert(region_2m(b2 / PAGE_SZ + 2) == region_2m((b2 / PAGE_SZ) as int));
        assert(region_1g(b2 / PAGE_SZ + 2) == region_1g((b2 / PAGE_SZ) as int));
        assert(!s0.blocks.covered(b2 / PAGE_SZ + 2));
        assert(region_2m(b2 / PAGE_SZ + 4) == region_2m((b2 / PAGE_SZ) as int));
        assert(region_1g(b2 / PAGE_SZ + 4) == region_1g((b2 / PAGE_SZ) as int));
        assert(!s0.blocks.covered(b2 / PAGE_SZ + 4));
        assert(region_2m(b2 / PAGE_SZ + 6) == region_2m((b2 / PAGE_SZ) as int));
        assert(region_1g(b2 / PAGE_SZ + 6) == region_1g((b2 / PAGE_SZ) as int));
        assert(!s0.blocks.covered(b2 / PAGE_SZ + 6));
        assert(block_within(b2, 3, first));
        assert(bt as int % block_bytes(1) == 0);
        assert(bt as int + block_bytes(1) <= b2 as int + block_bytes(3));
        assert(block_within(bt, THREAD_ORDER, first));
        assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
        assert(!s0.blocks.covered((bt / PAGE_SZ) as int));
        assert(s0.blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize)) by {
            assert forall|k: int| 0 <= k < order_pages(THREAD_ORDER as usize) implies #[trigger] s0.blocks.pages@[(bt / PAGE_SZ) as int + k].kind is Free by {
                assert(bt / PAGE_SZ + k == b2 / PAGE_SZ + 2 + k);
                assert(s0.blocks.pages@[(b2 / PAGE_SZ + 2 + k) as int].kind is Free);
            }
        }
        assert(s0.blocks.tracks_addr_run(b2, order_pages(3)));
        assert(s0.blocks.tracks_addr_run(bt, order_pages(THREAD_ORDER as usize)));
        assert(bl as int % block_bytes(1) == 0);
        assert(bl as int + block_bytes(1) <= b2 as int + block_bytes(3));
        assert(block_within(bl, 1, first));
        assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
        assert(!s0.blocks.covered((bl / PAGE_SZ) as int));
        assert(s0.blocks.small_free((bl / PAGE_SZ) as int, 1)) by {
            assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[(bl / PAGE_SZ) as int + k].kind is Free by {
                assert(bl / PAGE_SZ + k == b2 / PAGE_SZ + 4 + k);
                assert(s0.blocks.pages@[(b2 / PAGE_SZ + 4 + k) as int].kind is Free);
            }
        }
        assert(s0.blocks.tracks_addr_run(bl, order_pages(1)));
        assert(bn as int % block_bytes(0) == 0);
        assert(bn as int + block_bytes(0) <= b2 as int + block_bytes(3));
        assert(block_within(bn, 0, first));
        assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
        assert(!s0.blocks.covered((bn / PAGE_SZ) as int));
        assert(s0.blocks.pages@[(bn / PAGE_SZ) as int].kind is Free);
        assert(s0.blocks.small_free((bn / PAGE_SZ) as int, 0));
        assert(s0.blocks.tracks_addr_run(bn, order_pages(0)));
    }

    /// A retype that types a run outside `base` leaves that block inside the same untyped and free,
    /// so a later retype of it can be proved without unfolding `booted` again.
    #[verifier::spinoff_prover]
    proof fn lemma_wakes_block_survives(
        pre: Self,
        post: Self,
        process: usize,
        base: usize,
        order: u8,
        child: usize,
        page: int,
        used: usize,
        filled: Option<(usize, int)>,
    )
        requires
            Self::retype_keeps(pre, post, child, page, used, filled),
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            pre.can_retype_under(process, ROOT_UNTYPED_SLOT, base, order),
            pre.blocks.small_free((base / PAGE_SZ) as int, order as usize),
            pre.blocks.tracks_addr_run(base, order_pages(order as usize)),
            (base / PAGE_SZ) as int + order_pages(order as usize) <= page || page + order_pages(used) <= (base / PAGE_SZ) as int,
        ensures
            post.can_retype_under(process, ROOT_UNTYPED_SLOT, base, order),
            post.blocks.small_free((base / PAGE_SZ) as int, order as usize),
            post.blocks.tracks_addr_run(base, order_pages(order as usize)),
    {
        let parent = pre.tables.node_of(process, ROOT_UNTYPED_SLOT);
        let bp = (base / PAGE_SZ) as int;
        let n = order_pages(order as usize);
        let m = order_pages(used);
        assert(pre.tables.has_slot(&pre.list, process, ROOT_UNTYPED_SLOT));
        assert(post.tables.has_slot(&post.list, process, ROOT_UNTYPED_SLOT));
        assert(post.tables.node_of(process, ROOT_UNTYPED_SLOT) == parent);
        assert(pre.is_cap(parent));
        assert(post.is_cap(parent));
        assert(post.payload_of(parent) == pre.payload_of(parent));
        assert(post.list.nodes@[parent as int].depth == pre.list.nodes@[parent as int].depth);
        assert(block_within(base, order, pre.payload_of(parent)));
        assert(block_within(base, order, post.payload_of(parent)));
        assert(post.can_retype_under(process, ROOT_UNTYPED_SLOT, base, order));
        assert(!pre.blocks.covered(bp));
        assert(post.blocks.regions_2m@ == pre.blocks.regions_2m@);
        assert(post.blocks.regions_1g@ == pre.blocks.regions_1g@);
        assert(post.blocks.regions_2m@[region_2m(bp)] == pre.blocks.regions_2m@[region_2m(bp)]);
        assert(post.blocks.regions_1g@[region_1g(bp)] == pre.blocks.regions_1g@[region_1g(bp)]);
        assert(!post.blocks.covered(bp));
        assert forall|k: int| 0 <= k < n implies #[trigger] post.blocks.pages@[bp + k].kind is Free by {
            assert(pre.blocks.pages@[bp + k].kind is Free);
            assert(bp + n <= pre.blocks.pages@.len());
            assert(pre.blocks.tracks(bp + k));
            if bp + n <= page {
                assert(bp + k < page);
            } else {
                assert(page + m <= bp);
                assert(page + m <= bp + k);
            }
            assert(!(page <= bp + k < page + m));
            assert(post.blocks.pages@[bp + k].kind == pre.blocks.pages@[bp + k].kind);
        }
        assert(post.blocks.small_free(bp, order as usize));
        assert(post.blocks.tracks_addr_run(base, n));
    }

    /// A retype that fills `child` leaves every other slot holding the capability it held.
    #[verifier::spinoff_prover]
    proof fn lemma_wakes_slot_kept(
        pre: Self,
        post: Self,
        root: usize,
        slot: usize,
        n: usize,
        p: Payload,
        child: usize,
        page: int,
        used: usize,
        filled: Option<(usize, int)>,
    )
        requires
            Self::retype_keeps(pre, post, child, page, used, filled),
            pre.slot_holds(root, slot, n, p),
            n != child,
        ensures
            post.slot_holds(root, slot, n, p),
            post.list.nodes@[n as int].depth == pre.list.nodes@[n as int].depth,
    {
        assert(pre.tables.has_slot(&pre.list, root, slot));
        assert(post.tables.has_slot(&post.list, root, slot));
        assert(post.tables.node_of(root, slot) == n);
        assert(pre.is_cap(n));
        assert(post.is_cap(n));
        assert(post.payload_of(n) == p);
        assert(post.list.nodes@[n as int].depth == pre.list.nodes@[n as int].depth);
        assert(post.slot_holds(root, slot, n, p));
    }

    /// A move of one capability leaves every other slot holding the capability it held, at the depth
    /// it had.
    #[verifier::spinoff_prover]
    proof fn lemma_wakes_move_keeps_slot(
        pre: Self,
        post: Self,
        root: usize,
        from: Position,
        to: Position,
        slot_root: usize,
        slot: usize,
        n: usize,
        p: Payload,
    )
        requires
            Self::cap_moved_at(pre, post, root, from, to),
            pre.slot_holds(slot_root, slot, n, p),
            n != pre.tables.node_of(pre.table_at(root, from.through)->0, from.index),
            n != pre.tables.node_of(pre.table_at(root, to.through)->0, to.index),
            post.tables.has_slot(&post.list, slot_root, slot),
            post.tables.node_of(slot_root, slot) == n,
        ensures
            post.slot_holds(slot_root, slot, n, p),
            post.list.nodes@[n as int].depth == pre.list.nodes@[n as int].depth,
    {
        let src = pre.table_at(root, from.through)->0;
        let dst = pre.table_at(root, to.through)->0;
        let i = pre.tables.node_of(src, from.index);
        let m = pre.tables.node_of(dst, to.index);
        assert(Self::cap_moved_between(pre, post, src, from.index, dst, to.index));
        assert(Self::caps_frame(pre, post, i, m));
        Self::lemma_caps_frame(pre, post, i, m, n);
        assert(0 <= n < NODE_SPACE);
        assert(post.list.nodes@[n as int].depth == pre.list.nodes@[n as int].depth);
        assert(post.slot_holds(slot_root, slot, n, p));
    }

    /// The root's entry-0 leaf stays a slot through the place that adds the thread's placement node:
    /// that node is one past a page, and the leaf is page-aligned.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_slot(
        s0: Self,
        s1: Self,
        s2: Self,
        s3: Self,
        s4: Self,
        s5: Self,
        s6: Self,
        s7: Self,
        s8: Self,
        s8a: Self,
        s8b: Self,
        s9: Self,
        s10: Self,
        process: usize,
        base: usize,
        b2: usize,
        bt: usize,
        bl: usize,
        bn: usize,
        np: usize,
        nt: usize,
        nn: usize,
        core_cap: usize,
        from_notif: Position,
        to_notif: Position,
        registers: Registers,
    )
        requires
            s0.tables.roots@.contains_key(process),
            Self::retype_keeps(s0, s1, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2))),
            Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None),
            Self::retype_keeps(s2, s3, nt, (bt / PAGE_SZ) as int, 1, None),
            Self::retype_keeps(s3, s4, bl, (bl / PAGE_SZ) as int, 1, Some((base, 0))),
            Self::retype_keeps(s4, s5, nn, (bn / PAGE_SZ) as int, 0, None),
            Self::cap_moved_at(s5, s6, process, from_notif, to_notif),
            s6.wf(),
            s6.tables.has_slot(&s6.list, process, ROOT_UNTYPED_SLOT),
            b2 % PAGE_SZ == 0,
            bt == b2 + 2 * PAGE_SZ,
            Self::placed(s6, s7, core_cap, bt, Placement { core: 1, priority: 0 }),
            Self::state_written(s7, s8, bt, ThreadState::Runnable { core: 1 }),
            s8a.tables == s8.tables && s8a.list == s8.list,
            s8b.tables == s8a.tables && s8b.list == s8a.list,
            Self::switch_frame(s8b, s9, 1, bt),
            Self::wait_blocked(s9, s10, 1, base, 1, registers),
        ensures
            s10.tables.has_slot(&s10.list, process, ROOT_UNTYPED_SLOT),
            s6.tables.leaf(process, 0) as int % PAGE_SZ as int == 0,
            placement_node(bt) as int % PAGE_SZ as int == 1,
    {
        assert(s0.tables.roots@.contains_key(process));
        assert(Self::retype_keeps(s0, s1, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2))));
        assert(s1.tables.roots@.contains_key(process));
        assert(Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None));
        assert(s2.tables.roots@.contains_key(process));
        assert(Self::retype_keeps(s2, s3, nt, (bt / PAGE_SZ) as int, 1, None));
        assert(s3.tables.roots@.contains_key(process));
        assert(Self::retype_keeps(s3, s4, bl, (bl / PAGE_SZ) as int, 1, Some((base, 0))));
        assert(s4.tables.roots@.contains_key(process));
        assert(Self::retype_keeps(s4, s5, nn, (bn / PAGE_SZ) as int, 0, None));
        assert(s5.tables.roots@.contains_key(process));
        assert(Self::cap_moved_at(s5, s6, process, from_notif, to_notif));
        let src = s5.table_at(process, from_notif.through)->0;
        let dst = s5.table_at(process, to_notif.through)->0;
        assert(Self::cap_moved_between(s5, s6, src, from_notif.index, dst, to_notif.index));
        assert(s6.tables.roots == s5.tables.roots);
        assert(s6.tables.roots@.contains_key(process));
        assert(s6.tables.has_slot(&s6.list, process, ROOT_UNTYPED_SLOT));
        assert(index_entry(ROOT_UNTYPED_SLOT) == 0) by (compute_only);
        let l = s6.tables.leaf(process, 0);
        assert(l != NO_LEAF);
        assert(s6.list.nodes@[l as int].live);
        reveal(CapKernel::wf);
        assert(s6.wf());
        assert(s6.tables.wf(&s6.list));
        reveal(Tables::roots_wf);
        assert(s6.tables.root_wf(process));
        assert(0 < ROOT_ENTRIES) by (compute_only);
        assert(s6.tables.owner@.contains_key(l));
        reveal(Tables::leaves_wf);
        assert(s6.tables.leaf_wf(&s6.list, l));
        assert(l % LEAF_BYTES == 0);
        assert(LEAF_BYTES == 2 * PAGE_SZ) by (compute_only);
        lemma_fundamental_div_mod(l as int, LEAF_BYTES as int);
        let q = l as int / LEAF_BYTES as int;
        assert(l as int == LEAF_BYTES as int * q);
        assert(LEAF_BYTES as int == 2 * PAGE_SZ as int);
        assert(l as int == (2 * PAGE_SZ as int) * q);
        assert(l as int == (2 * q) * PAGE_SZ as int) by (nonlinear_arith)
            requires
                l as int == (2 * PAGE_SZ as int) * q,
                PAGE_SZ > 0,
        ;
        lemma_mod_multiples_basic(2 * q, PAGE_SZ as int);
        assert(l as int % PAGE_SZ as int == 0);
        assert(b2 % PAGE_SZ == 0);
        assert(bt == b2 + 2 * PAGE_SZ);
        lemma_mod_multiples_basic(2, PAGE_SZ as int);
        lemma_add_mod_noop(b2 as int, (2 * PAGE_SZ) as int, PAGE_SZ as int);
        lemma_small_mod(0, PAGE_SZ as nat);
        assert(bt as int % PAGE_SZ as int == 0);
        let px = placement_node(bt);
        assert(px == bt + 1);
        lemma_add_mod_noop(bt as int, 1, PAGE_SZ as int);
        lemma_small_mod(1, PAGE_SZ as nat);
        assert(px as int % PAGE_SZ as int == 1);
        assert(l != px);
        assert(Self::placed(s6, s7, core_cap, bt, Placement { core: 1, priority: 0 }));
        assert(s7.tables == s6.tables);
        assert(s7.list.nodes@[l as int].live);
        assert(s7.tables.has_slot(&s7.list, process, ROOT_UNTYPED_SLOT));
        assert(Self::state_written(s7, s8, bt, ThreadState::Runnable { core: 1 }));
        assert(s8.tables == s7.tables && s8.list == s7.list);
        assert(s8a.tables == s8.tables && s8a.list == s8.list);
        assert(s8b.tables == s8a.tables && s8b.list == s8a.list);
        assert(Self::switch_frame(s8b, s9, 1, bt));
        assert(s9.tables == s8b.tables && s9.list == s8b.list);
        assert(Self::wait_blocked(s9, s10, 1, base, 1, registers));
        assert(s10 == (CapKernel { endpoints: s10.endpoints, threads: s10.threads, cores: s10.cores, ..s9 }));
        assert(s10.tables == s9.tables && s10.list == s9.list);
        assert(s10.tables.has_slot(&s10.list, process, ROOT_UNTYPED_SLOT));
    }

    /// `wf` fixes the core array's length at `NUM_CPUS`.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_cores(k: Self)
        requires
            k.wf(),
        ensures
            k.cores@.len() == NUM_CPUS,
    {
        reveal(CapKernel::wf);
        assert(k.cores@.len() == NUM_CPUS);
    }

    /// Waking one blocked thread whose placement outranks an idle core records that core.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_resched(pre: Self, t: usize, acc: Seq<usize>)
        requires
            pre.threads.records@.contains_key(t),
            pre.threads.records@[t].value().state is Blocked,
            pre.threads.records@[t].value().placement == Some(Placement { core: 1, priority: 0 }),
            pre.outranks_current(1, 0),
        ensures
            Self::queue_wake_resched(pre, seq![t], acc) == acc.push(1),
    {
        assert(seq![t].len() == 1);
        assert(seq![t][0] == t);
        assert(seq![t].drop_first() =~= Seq::<usize>::empty());
        assert(Self::queue_wake_step(pre, t, acc) == acc.push(1));
        assert(Self::queue_wake_resched(pre, Seq::<usize>::empty(), acc.push(1)) == acc.push(1));
        assert(Self::queue_wake_resched(pre, seq![t], acc) == acc.push(1));
    }

    /// One retype keeps the root untyped: its slot, payload, depth, process record and root entry.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_retype_keeps(
        pre: Self,
        post: Self,
        process: usize,
        u: usize,
        child: usize,
        page: int,
        order: usize,
        filled: Option<(usize, int)>,
    )
        requires
            pre.is_cap(u),
            pre.tables.has_slot(&pre.list, process, ROOT_UNTYPED_SLOT),
            pre.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            pre.processes.records@.contains_key(process),
            !pre.processes.records@[process].value().dead,
            pre.tables.roots@.contains_key(process),
            Self::retype_keeps(pre, post, child, page, order, filled),
        ensures
            post.is_cap(u),
            post.payload_of(u) == pre.payload_of(u),
            post.list.nodes@[u as int].depth == pre.list.nodes@[u as int].depth,
            post.tables.has_slot(&post.list, process, ROOT_UNTYPED_SLOT),
            post.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            post.processes.records@.contains_key(process),
            !post.processes.records@[process].value().dead,
            post.tables.roots@.contains_key(process),
    {
        assert(Self::retype_keeps(pre, post, child, page, order, filled));
        assert(pre.is_cap(u));
        assert(post.is_cap(u) && post.payload_of(u) == pre.payload_of(u));
        assert(post.list.nodes@[u as int].depth == pre.list.nodes@[u as int].depth);
        assert(pre.tables.has_slot(&pre.list, process, ROOT_UNTYPED_SLOT));
        assert(post.tables.has_slot(&post.list, process, ROOT_UNTYPED_SLOT));
        assert(post.tables.node_of(process, ROOT_UNTYPED_SLOT) == pre.tables.node_of(process, ROOT_UNTYPED_SLOT));
        assert(post.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(pre.processes.records@.contains_key(process));
        assert(!pre.processes.records@[process].value().dead);
        assert(post.processes.records@[process].value().dead == pre.processes.records@[process].value().dead);
        assert(post.processes.records@.contains_key(process));
        assert(!post.processes.records@[process].value().dead);
        assert(pre.tables.roots@.contains_key(process));
        assert(post.tables.roots@.contains_key(process));
    }

    /// The root untyped still says what boot gave it after the witness's retypes.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_retyped(
        s0: Self,
        s1: Self,
        s2: Self,
        s3: Self,
        s4: Self,
        s5: Self,
        process: usize,
        base: usize,
        b2: usize,
        bt: usize,
        bl: usize,
        bn: usize,
        u: usize,
        np: usize,
        nt: usize,
        nn: usize,
        free: Seq<(usize, usize)>,
    )
        requires
            s0.wf(),
            s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0])),
            s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0),
            s0.list.nodes@[u as int].depth == 1,
            s0.processes.records@.contains_key(process),
            !s0.processes.records@[process].value().dead,
            s0.tables.roots@.contains_key(process),
            base + 2 * PROCESS_BYTES <= NODE_SPACE,
            b2 == (base + PROCESS_BYTES) as usize,
            Self::retype_keeps(s0, s1, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2))),
            Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None),
            Self::retype_keeps(s2, s3, nt, (bt / PAGE_SZ) as int, 1, None),
            Self::retype_keeps(s3, s4, bl, (bl / PAGE_SZ) as int, 1, Some((base, 0))),
            Self::retype_keeps(s4, s5, nn, (bn / PAGE_SZ) as int, 0, None),
        ensures
            s5.is_cap(u),
            s5.payload_of(u) == page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0]),
            s5.payload_of(u).kind is Untyped,
            s5.payload_of(u).rights & right_bit(Right::Retype) != 0,
            block_within(bn, 0, s5.payload_of(u)),
            s5.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            s5.list.nodes@[u as int].depth == 1,
            s5.processes.records@.contains_key(process),
            !s5.processes.records@[process].value().dead,
            s5.tables.roots@.contains_key(process),
            u < NODE_SPACE,
            b2 < NODE_SPACE,
    {
        let first = page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0]);
        assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
        assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
        assert(s0.is_cap(u) && s0.payload_of(u) == first);
        assert(s0.list.nodes@[u as int].depth == 1);
        assert(s0.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
        assert(first.kind is Untyped);
        assert(first.rights & right_bit(Right::Retype) != 0);
        assert(block_within(bn, 0, first));
        Self::lemma_witness_dead_notification_wakes_retype_keeps(
            s0, s1, process, u, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2)),
        );
        assert(s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
        Self::lemma_witness_dead_notification_wakes_retype_keeps(
            s1, s2, process, u, np, (base / PAGE_SZ) as int, 3, None,
        );
        assert(s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
        Self::lemma_witness_dead_notification_wakes_retype_keeps(
            s2, s3, process, u, nt, (bt / PAGE_SZ) as int, 1, None,
        );
        assert(s3.payload_of(u) == first && s3.list.nodes@[u as int].depth == 1);
        Self::lemma_witness_dead_notification_wakes_retype_keeps(
            s3, s4, process, u, bl, (bl / PAGE_SZ) as int, 1, Some((base, 0)),
        );
        assert(s4.payload_of(u) == first && s4.list.nodes@[u as int].depth == 1);
        Self::lemma_witness_dead_notification_wakes_retype_keeps(
            s4, s5, process, u, nn, (bn / PAGE_SZ) as int, 0, None,
        );
        assert(s5.payload_of(u) == first && s5.list.nodes@[u as int].depth == 1);
        assert(s5.payload_of(u).kind is Untyped);
        assert(s5.payload_of(u).rights & right_bit(Right::Retype) != 0);
        assert(block_within(bn, 0, s5.payload_of(u)));
        assert(u < NODE_SPACE) by {
            reveal(CapKernel::wf);
            assert(s0.wf());
            assert(s0.list.wf());
            assert(s0.list.nodes@.len() == NODE_SPACE);
            assert(s0.is_cap(u));
            assert(s0.list.nodes@[u as int].live);
        }
        assert(PROCESS_BYTES > 0) by (compute_only);
        assert(b2 < NODE_SPACE) by (nonlinear_arith)
            requires
                b2 == (base + PROCESS_BYTES) as usize,
                PROCESS_BYTES > 0,
                base + 2 * PROCESS_BYTES <= NODE_SPACE,
        ;
    }

    /// Moving the notification leaves the root untyped, and the move keeps the blocks and the process.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_untyped(
        s5: Self,
        s6: Self,
        process: usize,
        base: usize,
        u: usize,
        nn: usize,
        nn2: usize,
        bn: usize,
        free: Seq<(usize, usize)>,
        from_notif: Position,
        to_notif: Position,
    )
        requires
            s5.is_cap(u),
            s5.payload_of(u) == page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0]),
            s5.payload_of(u).kind is Untyped,
            s5.payload_of(u).rights & right_bit(Right::Retype) != 0,
            block_within(bn, 0, s5.payload_of(u)),
            s5.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            s5.processes.records@.contains_key(process),
            !s5.processes.records@[process].value().dead,
            s5.tables.roots@.contains_key(process),
            s5.table_at(process, None) == Some(process),
            s5.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base),
            s5.tables.node_of(process, WITNESS_FRAME_SLOT) == nn,
            s5.tables.node_of(base, 1) == nn2,
            Self::cap_moved_at(s5, s6, process, from_notif, to_notif),
            from_notif == (Position { through: None, index: WITNESS_FRAME_SLOT }),
            to_notif == (Position { through: Some(WITNESS_PROCESS_SLOT), index: 1 }),
            u != nn && u != nn2,
            Self::move_kept(s5, s6),
            s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
        ensures
            s6.is_cap(u),
            s6.payload_of(u).kind is Untyped,
            s6.payload_of(u).rights & right_bit(Right::Retype) != 0,
            block_within(bn, 0, s6.payload_of(u)),
            s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            s6.blocks == s5.blocks,
            s6.processes.records@.contains_key(process),
            !s6.processes.records@[process].value().dead,
            s6.tables.roots@.contains_key(process),
    {
        let first = page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0]);
        assert(s5.is_cap(u) && s5.payload_of(u) == first);
        assert(from_notif == (Position { through: None, index: WITNESS_FRAME_SLOT }));
        assert(to_notif == (Position { through: Some(WITNESS_PROCESS_SLOT), index: 1 }));
        assert(Self::cap_moved_at(s5, s6, process, from_notif, to_notif));
        let src = s5.table_at(process, from_notif.through)->0;
        let dst = s5.table_at(process, to_notif.through)->0;
        assert(s5.table_at(process, None) == Some(process));
        assert(s5.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
        assert(src == process && dst == base);
        assert(Self::cap_moved_between(s5, s6, src, from_notif.index, dst, to_notif.index));
        let i = s5.tables.node_of(src, from_notif.index);
        let n = s5.tables.node_of(dst, to_notif.index);
        assert(s5.tables.node_of(process, WITNESS_FRAME_SLOT) == nn);
        assert(s5.tables.node_of(base, 1) == nn2);
        assert(i == nn && n == nn2);
        assert(Self::caps_frame(s5, s6, nn, nn2));
        assert(u != nn && u != nn2);
        Self::lemma_caps_frame(s5, s6, nn, nn2, u);
        assert(s6.is_cap(u) && s6.payload_of(u) == first);
        assert(s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(Self::move_frame(s5, s6, i, n));
        assert(s6.tables.roots == s5.tables.roots);
        assert(Self::move_kept(s5, s6));
        assert(s6.blocks == s5.blocks);
        assert(s6.processes.records == s5.processes.records);
        assert(s6.payload_of(u).kind is Untyped);
        assert(s6.payload_of(u).rights & right_bit(Right::Retype) != 0);
        assert(block_within(bn, 0, s6.payload_of(u)));
        assert(s6.processes.records@.contains_key(process) && !s6.processes.records@[process].value().dead);
        assert(s6.tables.roots@.contains_key(process));
    }

    /// The retypes, the move and the wait, as one call the witness's own query can afford.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_bridge(
        s0: Self,
        s1: Self,
        s2: Self,
        s3: Self,
        s4: Self,
        s5: Self,
        s6: Self,
        s7: Self,
        s8: Self,
        s8a: Self,
        s8b: Self,
        s9: Self,
        s10: Self,
        process: usize,
        base: usize,
        b2: usize,
        bt: usize,
        bl: usize,
        bn: usize,
        u: usize,
        np: usize,
        nt: usize,
        nn: usize,
        nn2: usize,
        core_cap: usize,
        free: Seq<(usize, usize)>,
        from_notif: Position,
        to_notif: Position,
        registers: Registers,
    )
        requires
            s0.wf(),
            s10.wf(),
            s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, page_block_payload(runs_blocks(free, MAX_ORDER as nat)[0])),
            s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0),
            s0.list.nodes@[u as int].depth == 1,
            s0.processes.records@.contains_key(process),
            !s0.processes.records@[process].value().dead,
            s0.tables.roots@.contains_key(process),
            base + 2 * PROCESS_BYTES <= NODE_SPACE,
            b2 == (base + PROCESS_BYTES) as usize,
            b2 % PAGE_SZ == 0,
            Self::retype_keeps(s0, s1, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2))),
            Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, Position { through: None, index: 2 }, b2),
            Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None),
            Self::retype_keeps(s2, s3, nt, (bt / PAGE_SZ) as int, 1, None),
            Self::retype_keeps(s3, s4, bl, (bl / PAGE_SZ) as int, 1, Some((base, 0))),
            Self::leaf_retyped(s3, s4, process, ROOT_UNTYPED_SLOT, Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 }, bl),
            Self::retype_keeps(s4, s5, nn, (bn / PAGE_SZ) as int, 0, None),
            Self::queue_retyped(s4, s5, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bn, CapKind::Notification),
            Self::queue_retype_keeps(s4, s5),
            s5.blocks.pages@.len() == s4.blocks.pages@.len(),
            s4.blocks.tracks_addr_run(bn, order_pages(0)),
            s4.tables.has_slot(&s4.list, base, 1),
            s4.tables.node_of(base, 1) == nn2,
            s5.tables.node_of(process, WITNESS_FRAME_SLOT) == nn,
            s5.tables.node_of(base, 1) == nn2,
            s5.table_at(process, None) == Some(process),
            s5.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base),
            Self::cap_moved_at(s5, s6, process, from_notif, to_notif),
            u != nn && u != nn2 && b2 != nn2,
            s6.list.nodes@[b2 as int].live,
            s6.list.parent@[b2] == u,
            s6.tables.has_slot(&s6.list, process, ROOT_UNTYPED_SLOT),
            s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            s6.tables.node_of(base, 1) == nn2,
            s6.tables.leaf(process, 0) as int % PAGE_SZ as int == 0,
            placement_node(bt) as int % PAGE_SZ as int == 1,
            Self::move_kept(s5, s6),
            Self::placed(s6, s7, core_cap, bt, Placement { core: 1, priority: 0 }),
            Self::place_kept(s6, s7, process),
            Self::state_written(s7, s8, bt, ThreadState::Runnable { core: 1 }),
            s8a.list == s8.list && s8a.tables == s8.tables && s8a.blocks == s8.blocks && s8a.processes == s8.processes,
            s8b.list == s8a.list && s8b.tables == s8a.tables && s8b.blocks == s8a.blocks && s8b.processes == s8a.processes,
            Self::switch_frame(s8b, s9, 1, bt),
            s9.holds_notification(base, 1, RECEIVE_RIGHT),
            s9.notification_at(base, 1) == bn,
            Self::wait_blocked(s9, s10, 1, base, 1, registers),
            s6.list.parent@.contains_key(b2),
            from_notif == (Position { through: None, index: WITNESS_FRAME_SLOT }),
            to_notif == (Position { through: Some(WITNESS_PROCESS_SLOT), index: 1 }),
        ensures
            s10.is_cap(u),
            s10.payload_of(u).kind is Untyped,
            s10.payload_of(u).rights & right_bit(Right::Retype) != 0,
            block_within(bn, 0, s10.payload_of(u)),
            s10.list.nodes@[b2 as int].live,
            s10.list.parent@[b2] == u,
            s10.list.parent@.contains_key(b2),
            s10.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            s10.root_live(process),
            s10.tables.roots@.contains_key(process),
            b2 < NODE_SPACE,
            u < NODE_SPACE,
            s10.list.nodes@.len() == NODE_SPACE,
            s10.is_cap(nn2),
            s10.payload_of(nn2).kind is Notification,
            s10.payload_of(nn2).base == bn,
            s10.blocks.tracks((bn / PAGE_SZ) as int),
            s10.blocks.pages@[(bn / PAGE_SZ) as int].kind is Base,
            s10.blocks.pages@[(bn / PAGE_SZ) as int].object is Notification,
            s10.blocks.pages@[(bn / PAGE_SZ) as int].refs == 1,
            !s10.blocks.pages@[(bn / PAGE_SZ) as int].dead,
    {
        Self::lemma_witness_dead_notification_wakes_retyped(
            s0, s1, s2, s3, s4, s5,
            process, base, b2, bt, bl, bn, u, np, nt, nn, free,
        );
        assert(s5.is_cap(u));
        assert(s5.payload_of(u).kind is Untyped);
        assert(s5.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(s5.processes.records@.contains_key(process) && !s5.processes.records@[process].value().dead);
        assert(s5.tables.roots@.contains_key(process));
        assert(u < NODE_SPACE && b2 < NODE_SPACE);
        assert(from_notif == (Position { through: None, index: WITNESS_FRAME_SLOT }));
        assert(to_notif == (Position { through: Some(WITNESS_PROCESS_SLOT), index: 1 }));
        Self::lemma_witness_dead_notification_wakes_untyped(
            s5, s6, process, base, u, nn, nn2, bn, free, from_notif, to_notif,
        );
        assert(s6.is_cap(u));
        assert(s6.payload_of(u).kind is Untyped);
        assert(s6.payload_of(u).rights & right_bit(Right::Retype) != 0);
        assert(block_within(bn, 0, s6.payload_of(u)));
        assert(s6.blocks == s5.blocks);
        assert(s6.processes.records@.contains_key(process) && !s6.processes.records@[process].value().dead);
        assert(s6.tables.roots@.contains_key(process));
        assert(s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(u != nn2 && b2 != nn2);
        assert(s6.list.parent@.contains_key(b2));
        Self::lemma_witness_dead_notification_wakes_kept(
            s0, s1, s2, s3, s4, s5, s6, s7, s8, s8a, s8b, s9, s10,
            process, base, b2, bt, bl, bn, u, np, nt, nn, nn2, core_cap,
            free, from_notif, to_notif, registers,
        );
    }

    /// The untyped, the notification and its block, carried from the move to the blocked wait.
    #[verifier::spinoff_prover]
    proof fn lemma_witness_dead_notification_wakes_kept(
        s0: Self,
        s1: Self,
        s2: Self,
        s3: Self,
        s4: Self,
        s5: Self,
        s6: Self,
        s7: Self,
        s8: Self,
        s8a: Self,
        s8b: Self,
        s9: Self,
        s10: Self,
        process: usize,
        base: usize,
        b2: usize,
        bt: usize,
        bl: usize,
        bn: usize,
        u: usize,
        np: usize,
        nt: usize,
        nn: usize,
        nn2: usize,
        core_cap: usize,
        free: Seq<(usize, usize)>,
        from_notif: Position,
        to_notif: Position,
        registers: Registers,
    )
        requires
            s6.is_cap(u),
            s6.payload_of(u).kind is Untyped,
            s6.payload_of(u).rights & right_bit(Right::Retype) != 0,
            block_within(bn, 0, s6.payload_of(u)),
            s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            s6.list.nodes@[b2 as int].live,
            s6.list.parent@[b2] == u,
            s6.list.parent@.contains_key(b2),
            s6.blocks == s5.blocks,
            s6.processes.records@.contains_key(process),
            !s6.processes.records@[process].value().dead,
            s6.tables.roots@.contains_key(process),
            u < NODE_SPACE,
            b2 < NODE_SPACE,
            b2 % PAGE_SZ == 0,
            placement_node(bt) as int % PAGE_SZ as int == 1,
            u != nn2 && b2 != nn2,
            s6.tables.node_of(base, 1) == nn2,
            Self::queue_retyped(s4, s5, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bn, CapKind::Notification),
            s4.blocks.tracks_addr_run(bn, order_pages(0)),
            s5.blocks.pages@.len() == s4.blocks.pages@.len(),
            Self::placed(s6, s7, core_cap, bt, Placement { core: 1, priority: 0 }),
            Self::place_kept(s6, s7, process),
            Self::state_written(s7, s8, bt, ThreadState::Runnable { core: 1 }),
            s8a.list == s8.list && s8a.tables == s8.tables && s8a.blocks == s8.blocks && s8a.processes == s8.processes,
            s8b.list == s8a.list && s8b.tables == s8a.tables && s8b.blocks == s8a.blocks && s8b.processes == s8a.processes,
            Self::switch_frame(s8b, s9, 1, bt),
            s9.holds_notification(base, 1, RECEIVE_RIGHT),
            s9.notification_at(base, 1) == bn,
            Self::wait_blocked(s9, s10, 1, base, 1, registers),
            s10.wf(),
        ensures
            s10.is_cap(u),
            s10.payload_of(u).kind is Untyped,
            s10.payload_of(u).rights & right_bit(Right::Retype) != 0,
            block_within(bn, 0, s10.payload_of(u)),
            s10.list.nodes@[b2 as int].live,
            s10.list.parent@[b2] == u,
            s10.list.parent@.contains_key(b2),
            s10.tables.node_of(process, ROOT_UNTYPED_SLOT) == u,
            s10.root_live(process),
            s10.tables.roots@.contains_key(process),
            b2 < NODE_SPACE,
            u < NODE_SPACE,
            s10.list.nodes@.len() == NODE_SPACE,
            s10.is_cap(nn2),
            s10.payload_of(nn2).kind is Notification,
            s10.payload_of(nn2).base == bn,
            s10.blocks.tracks((bn / PAGE_SZ) as int),
            s10.blocks.pages@[(bn / PAGE_SZ) as int].kind is Base,
            s10.blocks.pages@[(bn / PAGE_SZ) as int].object is Notification,
            s10.blocks.pages@[(bn / PAGE_SZ) as int].refs == 1,
            !s10.blocks.pages@[(bn / PAGE_SZ) as int].dead,
    {
        let px = placement_node(bt);
        assert(px as int % PAGE_SZ as int == 1);
        assert(b2 != px);
        assert(Self::placed(s6, s7, core_cap, bt, Placement { core: 1, priority: 0 }));
        assert(Self::place_kept(s6, s7, process));
        assert(s7.tables == s6.tables && s7.blocks == s6.blocks && s7.processes == s6.processes);
        assert(s7.is_cap(u) == s6.is_cap(u));
        assert(s7.payload_of(u) == s6.payload_of(u));
        assert(s7.list.nodes@[b2 as int].live);
        assert(s7.list.parent@ == s6.list.parent@.insert(px, core_cap));
        assert(s7.list.parent@.contains_key(b2));
        assert(s6.list.parent@[b2] == u);
        assert(s7.list.parent@[b2] == u);
        assert(s7.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(Self::state_written(s7, s8, bt, ThreadState::Runnable { core: 1 }));
        assert(s8.list == s7.list && s8.tables == s7.tables && s8.blocks == s7.blocks && s8.processes == s7.processes);
        assert(s8a.list == s8.list && s8a.tables == s8.tables && s8a.blocks == s8.blocks && s8a.processes == s8.processes);
        assert(s8b.list == s8a.list && s8b.tables == s8a.tables && s8b.blocks == s8a.blocks && s8b.processes == s8a.processes);
        assert(Self::switch_frame(s8b, s9, 1, bt));
        assert(s9.list == s8b.list && s9.tables == s8b.tables && s9.blocks == s8b.blocks && s9.processes == s8b.processes);
        assert(Self::wait_blocked(s9, s10, 1, base, 1, registers));
        assert(s10 == (CapKernel { endpoints: s10.endpoints, threads: s10.threads, cores: s10.cores, ..s9 }));
        assert(s10.list == s9.list && s10.tables == s9.tables && s10.blocks == s9.blocks && s10.processes == s9.processes);
        assert(s10.is_cap(u) && s10.payload_of(u) == s6.payload_of(u));
        assert(s10.list.nodes@[b2 as int].live && s10.list.parent@[b2] == u);
        assert(s10.list.parent@.contains_key(b2));
        assert(s10.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(s10.tables.roots@.contains_key(process));
        assert(s10.processes.records@.contains_key(process) && !s10.processes.records@[process].value().dead);
        assert(s10.root_live(process));
        assert(s10.payload_of(u).kind is Untyped);
        assert(s10.payload_of(u).rights & right_bit(Right::Retype) != 0);
        assert(block_within(bn, 0, s10.payload_of(u)));
        assert(s9.tables.node_of(base, 1) == nn2);
        assert(s9.holds_notification(base, 1, RECEIVE_RIGHT));
        assert(s9.is_cap(nn2) && s9.payload_of(nn2).kind is Notification);
        assert(s9.notification_at(base, 1) == bn);
        assert(s9.payload_of(nn2).base == bn);
        assert(s10.tables.node_of(base, 1) == nn2);
        assert(s10.is_cap(nn2) && s10.payload_of(nn2).kind is Notification && s10.payload_of(nn2).base == bn);
        assert(Self::queue_retyped(s4, s5, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bn, CapKind::Notification));
        assert(s5.blocks.pages@[(bn / PAGE_SZ) as int].kind is Base);
        assert(s5.blocks.pages@[(bn / PAGE_SZ) as int].object == queue_object_of(CapKind::Notification));
        assert(s5.blocks.pages@[(bn / PAGE_SZ) as int].object is Notification);
        assert(s5.blocks.pages@[(bn / PAGE_SZ) as int].refs == 1);
        assert(!s5.blocks.pages@[(bn / PAGE_SZ) as int].dead);
        assert(order_pages(0) == 1);
        assert(s4.blocks.tracks_addr_run(bn, order_pages(0)));
        assert(s5.blocks.pages@.len() == s4.blocks.pages@.len());
        assert(s5.blocks.tracks((bn / PAGE_SZ) as int));
        assert(s10.blocks == s5.blocks);
        assert(s10.blocks.tracks((bn / PAGE_SZ) as int));
        assert(s10.blocks.pages@[(bn / PAGE_SZ) as int].kind is Base);
        assert(s10.blocks.pages@[(bn / PAGE_SZ) as int].object is Notification);
        assert(s10.blocks.pages@[(bn / PAGE_SZ) as int].refs == 1);
        assert(!s10.blocks.pages@[(bn / PAGE_SZ) as int].dead);
        assert(s10.list.nodes@.len() == NODE_SPACE) by {
            reveal(CapKernel::wf);
            assert(s10.wf());
            assert(s10.list.wf());
        }
    }

    /// The witness's solver query stops at the wait; this function proves the delete and the two reclaims.
    #[verifier::spinoff_prover]
    fn witness_dead_notification_wakes_reclaims(
        &mut self,
        process: usize,
        to: Position,
        base: usize,
        bt: usize,
        bn: usize,
        b2: usize,
        u: Ghost<usize>,
        nn2: Ghost<usize>,
        registers: Registers,
        Tracked(steps): Tracked<&mut Steps>,
    ) -> (ret: (Option<Payload>, ReclaimStep, ReclaimStep))
        requires
            old(self).wf(),
            old(self).root_live(process),
            old(self).tables.roots@.contains_key(process),
            old(self).can_delete_at(process, to),
            old(self).cap_at(process, to) == Some(nn2@),
            old(self).is_cap(nn2@),
            old(self).payload_of(nn2@).kind is Notification,
            old(self).payload_of(nn2@).base == bn,
            nn2@ != u@,
            b2 != nn2@,
            nn2@ % PAGE_SZ != 0,
            b2 < NODE_SPACE,
            u@ < NODE_SPACE,
            old(self).list.nodes@.len() == NODE_SPACE,
            old(self).tables.has_slot(&old(self).list, process, ROOT_UNTYPED_SLOT),
            old(self).tables.node_of(process, ROOT_UNTYPED_SLOT) == u@,
            old(self).is_cap(u@),
            old(self).payload_of(u@).kind is Untyped,
            old(self).payload_of(u@).rights & right_bit(Right::Retype) != 0,
            block_within(bn, 0, old(self).payload_of(u@)),
            old(self).list.nodes@[b2 as int].live,
            old(self).list.parent@.contains_key(b2),
            old(self).list.parent@[b2] == u@,
            bn % PAGE_SZ == 0,
            bn == (base + 14 * PAGE_SZ) as usize,
            bt == (base + 10 * PAGE_SZ) as usize,
            bn / PAGE_SZ == base / PAGE_SZ + 14,
            1 < old(self).cores@.len(),
            old(self).blocks.tracks((bn / PAGE_SZ) as int),
            old(self).blocks.pages@[(bn / PAGE_SZ) as int].kind is Base,
            old(self).blocks.pages@[(bn / PAGE_SZ) as int].object is Notification,
            old(self).blocks.pages@[(bn / PAGE_SZ) as int].refs == 1,
            !old(self).blocks.pages@[(bn / PAGE_SZ) as int].dead,
            old(self).endpoints.records@.contains_key(bn),
            old(self).endpoints.records@[bn].value().waiters@ =~= seq![bt],
            old(self).threads.records@.contains_key(bt),
            old(self).threads.records@[bt].value().state == (ThreadState::Blocked { object: bn }),
            old(self).threads.records@[bt].value().placement == Some(Placement { core: 1, priority: 0 }),
            old(self).threads.records@[bt].value().frame == partial_frame(registers),
            old(self).cores@[1].current_thread is None,
        ensures
            ret.0 is Some,
            ret.1 is Slice,
            ret.2 is Freed,
            final(self).wf(),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().state == (ThreadState::Runnable { core: 1 }),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().frame
                == outcome_written(partial_frame(registers), crate::capability::operation::status_only(crate::capability::operation::STATUS_ERROR)),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().frame.spec_status_word()
                == crate::capability::operation::STATUS_ERROR,
            final(self).resched_ipis@.len() > 0,
            final(self).resched_ipis@.last() == 1,
            final(self).blocks.pages@[(base / PAGE_SZ + 14) as int].kind is Free,
            !final(self).endpoints.records@.contains_key((base + 14 * PAGE_SZ) as usize),
    {
        hide(CapKernel::wf);
        let ghost s10 = *old(self);
        let deleted = self.delete(process, to);
        let ghost s11 = *self;
        proof {
            assert(s10.can_delete_at(process, to));
            assert(Self::delete_answered(s10, s11, process, to, deleted));
            assert(deleted is Some);
            assert(Self::cap_deleted_at(s10, s11, process, to));
            assert(s10.cap_at(process, to) == Some(nn2@));
            assert(Self::object_dropped(s10, s11, nn2@));
            assert(s10.is_cap(nn2@) && queue_kind(s10.payload_of(nn2@).kind));
            let e = s10.payload_of(nn2@).base;
            assert(e == bn);
            let br = BlockRef::Small(bn / PAGE_SZ);
            assert(block_refs(&s10.blocks, br) == 1);
            assert(!block_dead(&s10.blocks, br));
            assert(blocks_refs_changed(
                &s10.blocks,
                &s11.blocks,
                br,
                0,
                true,
            ));
            assert(Self::page_count_kept(s10, s11));
            assert(block_refs(&s11.blocks, br) == 0);
            assert(block_dead(&s11.blocks, br));
            assert(s11.blocks.tracks((bn / PAGE_SZ) as int));
            assert(s11.blocks.pages@[(bn / PAGE_SZ) as int].kind is Base);
            assert(s11.blocks.pages@[(bn / PAGE_SZ) as int].object is Notification);
            assert(s11.blocks.pages@[(bn / PAGE_SZ) as int].refs == 0);
            assert(s11.blocks.pages@[(bn / PAGE_SZ) as int].dead);
            assert(queue_object(s11.blocks.pages@[(bn / PAGE_SZ) as int].object));
            assert(s11.queue_object_dead(bn / PAGE_SZ));
            assert(s11.endpoints.records == s10.endpoints.records);
            assert(s11.endpoints.records@[bn].value().waiters@ =~= seq![bt]);
            assert(s11.threads == s10.threads);
            assert(Self::delete_kept(s10, s11, process));
            assert(s11.cores == s10.cores);
            assert(s11.processes == s10.processes);
            assert(s11.root_live(process));
            assert(s11.tables == s10.tables);
            assert(s11.tables.roots@.contains_key(process));
            assert(Self::caps_frame(s10, s11, nn2@, nn2@));
            assert forall|j: int| 0 <= j < NODE_SPACE && j != nn2@ implies #[trigger] s11.list.nodes@[j].live == s10.list.nodes@[j].live by {
                assert(Self::caps_frame(s10, s11, nn2@, nn2@));
            }
            lemma_slot_kept_but(s10, s11, process, ROOT_UNTYPED_SLOT, nn2@);
            Self::lemma_caps_frame(s10, s11, nn2@, nn2@, u@);
            Self::lemma_caps_frame(s10, s11, nn2@, nn2@, b2);
            assert(s11.is_cap(u@) && s11.payload_of(u@) == s10.payload_of(u@));
            assert(s11.list.nodes@[b2 as int].live);
            assert(s11.list.parent@ == s10.list.parent@);
            assert(s11.list.parent@[b2] == u@);
            assert(s11.tables.node_of(process, ROOT_UNTYPED_SLOT) == u@);
            assert(s11.tables.has_slot(&s11.list, process, ROOT_UNTYPED_SLOT));
            assert(s11.list.parent@.contains_key(b2));
            assert(s11.list.nodes@[u@ as int].depth < MAX_DEPTH) by {
                reveal(CapKernel::wf);
                assert(s11.wf());
                assert(s11.list.wf());
                assert(s11.list.nodes@.len() == NODE_SPACE);
                assert(s11.list.nodes@[b2 as int].live);
                let s = s11.list.seq@;
                assert(has(s, b2));
                lemma_has(s, b2);
                let j = choose|j: int| 0 <= j < s.len() && s[j] == b2;
                assert(s11.list.parent@.contains_key(b2));
                assert(!s11.list.parent@.contains_key(s[0]));
                assert(j != 0);
                assert(s11.list.parent@.contains_key(s[j]));
                assert(s11.list.d(s[j]) == s11.list.d(s11.list.parent@[s[j]]) + 1);
                assert(s11.list.d(s[j]) <= MAX_DEPTH);
                assert(s11.list.parent@[s[j]] == u@);
                assert(s11.list.d(b2) == s11.list.d(u@) + 1);
                assert(s11.list.nodes@[u@ as int].depth < MAX_DEPTH);
            }
            assert(block_within(bn, 0, s11.payload_of(u@)));
            assert(s11.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
            assert(s11.endpoints.records@[bn].value().waiters@.len() == 1);
            assert(s11.can_slice_queue(process, ROOT_UNTYPED_SLOT, bn));
        }
        assert(0 < NUM_CPUS) by (compute_only);
        let slice = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bn, Tracked(steps));
        let ghost s12 = *self;
        proof {
            assert(slice is Slice);
            assert(s11.queue_sliced(s12, process, ROOT_UNTYPED_SLOT, bn));
            let ghost w = s11.endpoints.records@[bn].value().waiters@;
            assert(w =~= seq![bt]);
            assert(w.len() == 1);
            assert(s11.threads.records@.contains_key(bt));
            assert(s11.threads.records@[bt].value().state == (ThreadState::Blocked { object: bn }));
            assert(s11.threads.records@[bt].value().placement == Some(Placement { core: 1, priority: 0 }));
            assert(s11.outranks_current(1, 0)) by {
                assert(s11.cores@[1].current_thread is None);
            }
            Self::lemma_witness_dead_notification_wakes_resched(s11, bt, s11.resched_ipis@);
            assert(w.subrange(0, 1) == seq![bt]);
            assert(Self::queue_wake_resched(s11, w.subrange(0, 1), s11.resched_ipis@) == s11.resched_ipis@.push(1));
            assert(s12.threads.records@.contains_key(bt));
            assert(s12.threads.records@[bt].value().state == (ThreadState::Runnable { core: 1 }));
            assert(s12.threads.records@[bt].value().frame
                == outcome_written(partial_frame(registers), crate::capability::operation::status_only(crate::capability::operation::STATUS_ERROR)));
            assert(s12.threads.records@[bt].value().frame.spec_status_word()
                == crate::capability::operation::STATUS_ERROR);
            assert(s12.resched_ipis@ == s11.resched_ipis@.push(1));
            assert(s12.resched_ipis@.len() > 0 && s12.resched_ipis@.last() == 1);
            assert(Self::queue_slice_keeps(s11, s12));
            assert(s12.blocks == s11.blocks && s12.list == s11.list && s12.tables == s11.tables);
            assert(s12.endpoints.records@[bn].value().waiters@.len() == 0);
            assert(bn % PAGE_SZ == 0);
            lemma_fundamental_div_mod(bn as int, PAGE_SZ as int);
            assert(((bn / PAGE_SZ) * PAGE_SZ) as usize == bn);
            assert(s12.queue_is_dead(bn / PAGE_SZ));
            assert(s12.root_live(process));
            assert(s12.tables.roots@.contains_key(process));
            assert(s12.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
        }
        let freed = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bn, Tracked(steps));
        proof {
            assert(freed is Freed);
            assert(s12.queue_freed(*self, 0, process, ROOT_UNTYPED_SLOT, bn));
            assert(self.blocks.pages@[(bn / PAGE_SZ) as int].kind is Free);
            assert(bn / PAGE_SZ == base / PAGE_SZ + 14);
            assert(self.blocks.pages@[(base / PAGE_SZ + 14) as int].kind is Free);
            assert(self.endpoints.records@ == s12.endpoints.records@.remove(bn));
            assert(!self.endpoints.records@.contains_key(bn));
            assert(bn == (base + 14 * PAGE_SZ) as usize);
            assert(!self.endpoints.records@.contains_key((base + 14 * PAGE_SZ) as usize));
            assert(self.threads == s12.threads);
            assert(bt == (base + 10 * PAGE_SZ) as usize);
            assert(self.threads.records@[bt].value() == s12.threads.records@[bt].value());
            assert(self.resched_ipis == s12.resched_ipis);
            assert(self.wf());
        }
        (deleted, slice, freed)
    }

    /// From the state boot leaves, as the root at `process`, with the two order-3 blocks at `base`
    /// and `base + PROCESS_BYTES` the first free ones past those boot's tables took from the first
    /// untyped: retype a second process at `base`, a child thread at `base + 10 * PAGE_SZ` bound to
    /// it, its table leaf at `base + 12 * PAGE_SZ`, and a notification at `base + 14 * PAGE_SZ`
    /// moved into slot 1 of that process's table; place and start the child thread on core 1,
    /// switch core 1 to the new process and thread, and wait on the notification so the child blocks
    /// on its queue; then delete the notification's only capability and reclaim `base + 14 * PAGE_SZ`
    /// twice under the root's untyped. The first reclaim slices the queue, waking the child thread
    /// `Runnable` on core 1 with `STATUS_ERROR` in its saved frame and recording a reschedule IPI
    /// for core 1; the second frees the notification's block.
    /// design/teardown-driven-by-retype/, design/witness-per-way-an-operation-succeeds/.
    #[verifier::spinoff_prover]
    pub fn witness_dead_notification_wakes_waiter(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        kernel_root: Ghost<usize>,
        base: usize,
        registers: Registers,
        report: Processor,
    ) -> (ret: (WaitStep, Option<Payload>, ReclaimStep, ReclaimStep))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@, kernel_root@),
            report_tags_tlb(1, report),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret.0 is Blocked,
            ret.1 is Some,
            ret.2 is Slice,
            ret.3 is Freed,
            final(self).wf(),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().state == (ThreadState::Runnable { core: 1 }),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().frame
                == outcome_written(partial_frame(registers), crate::capability::operation::status_only(crate::capability::operation::STATUS_ERROR)),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().frame.spec_status_word()
                == crate::capability::operation::STATUS_ERROR,
            final(self).resched_ipis@.len() > 0,
            final(self).resched_ipis@.last() == 1,
            final(self).blocks.pages@[(base / PAGE_SZ + 14) as int].kind is Free,
            !final(self).endpoints.records@.contains_key((base + 14 * PAGE_SZ) as usize),
    {
        hide(CapKernel::wf);
        hide(CapKernel::booted);
        let ghost s0 = *self;
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let cs = (ROOT_CORE_SLOT + 1) as usize;
        let ghost core_cap = (leaf@ + cs) as usize;
        proof {
            s0.lemma_wakes_waiter_prepared(
                root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@, kernel_root@, base,
            );
            assert(s0.wf());
            assert(s0.root_live(process));
            assert(s0.tables.roots@.contains_key(process));
            assert(s0.list.nodes@[u as int].live);
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.slot_holds(process, cs, core_cap, core_payload(1, MAX_PRIORITY)));
            assert(s0.list.nodes@[core_cap as int].depth == 1);
            assert(s0.cores@[1].current_thread is None && s0.cores@[1].generation == 1
                && s0.cores@[1].next_pcid == 1 && s0.cores@[1].space is None);
        }
        let b2 = base + PROCESS_BYTES;
        let bt = b2 + 2 * PAGE_SZ;
        let bl = b2 + 4 * PAGE_SZ;
        let bn = b2 + 6 * PAGE_SZ;
        let ghost np = (b2 + 1) as usize;
        let ghost nt = (b2 + 2) as usize;
        let ghost nn = (b2 + 3) as usize;
        let ghost nn2 = (bl + 1) as usize;
        proof {
            assert(b2 == (base + PROCESS_BYTES) as usize);
            assert(bt == (base + 10 * PAGE_SZ) as usize);
            assert(bn == (base + 14 * PAGE_SZ) as usize);
            assert(bn % PAGE_SZ == 0);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == b2 / PAGE_SZ + 2);
            assert(bl / PAGE_SZ == b2 / PAGE_SZ + 4);
            assert(bn / PAGE_SZ == b2 / PAGE_SZ + 6);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s0.blocks.small_free((base / PAGE_SZ) as int, 3));
            assert(s0.blocks.tracks_addr_run(base, order_pages(3)));
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(s0.blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize));
            assert(s0.blocks.tracks_addr_run(bt, order_pages(THREAD_ORDER as usize)));
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s0.blocks.small_free((bl / PAGE_SZ) as int, 1));
            assert(s0.blocks.tracks_addr_run(bl, order_pages(1)));
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
            assert(s0.blocks.small_free((bn / PAGE_SZ) as int, 0));
            assert(s0.blocks.tracks_addr_run(bn, order_pages(0)));
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, Position { through: None, index: 2 }, b2));
            assert forall|i: int| base / PAGE_SZ <= i < base / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[i].kind is Free);
            }
            assert forall|i: int| b2 / PAGE_SZ <= i < b2 / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[i].kind is Free);
            }
        }

        // Retype the root's entry-2 leaf (`b2`) and the child process (`base`).
        let tracked mut steps = Steps::fresh();
        let at1 = Position { through: None, index: 2 };
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b2, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at1, b2));
            assert(s1.tables.leaf(process, 2) == b2);
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_THREAD_SLOT) && index_entry(WITNESS_THREAD_SLOT) == 2);
            assert(index_ok(WITNESS_FRAME_SLOT) && index_entry(WITNESS_FRAME_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_FRAME_SLOT));
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s1.tables.node_of(process, WITNESS_THREAD_SLOT) == nt);
            assert(s1.tables.node_of(process, WITNESS_FRAME_SLOT) == nn);
            assert(b2 + PAGE_SZ <= base + 2 * PROCESS_BYTES);
            assert(np < NODE_SPACE && nt < NODE_SPACE && nn < NODE_SPACE);
            assert(!s1.list.nodes@[np as int].live);
            assert(!s1.list.nodes@[nt as int].live);
            assert(!s1.list.nodes@[nn as int].live);
            assert(Self::page_count_kept(s0, s1));
            assert(Self::retype_keeps(s0, s1, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2))));
            assert((base / PAGE_SZ) as int + order_pages(3) <= (b2 / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s0, s1, process, base, 3, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2)));
            assert((b2 / PAGE_SZ) as int + order_pages(1) <= (bt / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s0, s1, process, bt, THREAD_ORDER, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2)));
            assert((b2 / PAGE_SZ) as int + order_pages(1) <= (bl / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s0, s1, process, bl, 1, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2)));
            assert((b2 / PAGE_SZ) as int + order_pages(1) <= (bn / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s0, s1, process, bn, 0, b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2)));
            assert(s0.slot_holds(process, cs, core_cap, core_payload(1, MAX_PRIORITY)));
            assert(s0.list.nodes@[core_cap as int].depth == 1);
            assert(core_cap != b2);
            Self::lemma_wakes_slot_kept(s0, s1, process, cs, core_cap, core_payload(1, MAX_PRIORITY), b2, (b2 / PAGE_SZ) as int, 1, Some((process, 2)));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / PAGE_SZ) as int, 3));
            assert(s1.blocks.tracks_addr_run(base, order_pages(3)));
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }

        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, Tracked(&mut steps));
        let ghost s2 = *self;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None));
            assert(s2.processes.records@.contains_key(base));
            assert(!s2.processes.records@[base].value().dead);
            assert(s2.payload_of(np) == process_of(base));
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s2.list.nodes@[np as int].depth == 2);
            assert(s2.is_cap(np));
            assert(block_refs(&s2.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(!s2.cap_dead(np));
            assert(s2.can_hold_thread(process, WITNESS_PROCESS_SLOT));
            assert(Self::page_count_kept(s1, s2));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(s1.blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize));
            assert(s1.blocks.tracks_addr_run(bt, order_pages(THREAD_ORDER as usize)));
            assert((base / PAGE_SZ) as int + order_pages(3) <= (bt / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s1, s2, process, bt, THREAD_ORDER, np, (base / PAGE_SZ) as int, 3, None);
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s1.blocks.small_free((bl / PAGE_SZ) as int, 1));
            assert(s1.blocks.tracks_addr_run(bl, order_pages(1)));
            assert((base / PAGE_SZ) as int + order_pages(3) <= (bl / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s1, s2, process, bl, 1, np, (base / PAGE_SZ) as int, 3, None);
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
            assert(s1.blocks.small_free((bn / PAGE_SZ) as int, 0));
            assert(s1.blocks.tracks_addr_run(bn, order_pages(0)));
            assert((base / PAGE_SZ) as int + order_pages(3) <= (bn / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s1, s2, process, bn, 0, np, (base / PAGE_SZ) as int, 3, None);
            assert(core_cap != np);
            Self::lemma_wakes_slot_kept(s1, s2, process, cs, core_cap, core_payload(1, MAX_PRIORITY), np, (base / PAGE_SZ) as int, 3, None);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.node_of(process, WITNESS_THREAD_SLOT) == nt);
            assert(!s2.list.nodes@[nt as int].live);
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(s2.blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize));
            assert(s2.blocks.tracks_addr_run(bt, order_pages(THREAD_ORDER as usize)));
            assert(s2.can_retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT));
        }

        // Retype child thread `bt` bound to `base`, then `base`'s entry-0 leaf `bl`, then the
        // notification `bn` in root's slot 259.
        let ok3 = self.retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT, Tracked(&mut steps));
        let ghost s3 = *self;
        proof {
            assert(ok3);
            assert(Self::retype_keeps(s2, s3, nt, (bt / PAGE_SZ) as int, 1, None));
            assert(Self::thread_retyped(s2, s3, process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT));
            assert(core_cap != nt);
            Self::lemma_wakes_slot_kept(s2, s3, process, cs, core_cap, core_payload(1, MAX_PRIORITY), nt, (bt / PAGE_SZ) as int, 1, None);
            assert(s3.is_cap(nt) && s3.payload_of(nt) == thread_of(bt));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_THREAD_SLOT));
            assert(s3.tables.node_of(process, WITNESS_THREAD_SLOT) == nt);
            assert(s3.slot_holds(process, WITNESS_THREAD_SLOT, nt, thread_of(bt)));
            assert(s3.threads.records@[bt].value() == ThreadRecord { process: Some(base), ..fresh_thread() }) by {
                reveal(CapKernel::thread_retyped_records);
            }
            assert(s3.tables.roots@.contains_key(base));
            assert(s3.tables.leaf(base, 0) == NO_LEAF);
            assert(s3.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(Self::page_count_kept(s2, s3));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s2.blocks.small_free((bl / PAGE_SZ) as int, 1));
            assert(s2.blocks.tracks_addr_run(bl, order_pages(1)));
            assert((bt / PAGE_SZ) as int + order_pages(THREAD_ORDER as usize) <= (bl / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s2, s3, process, bl, 1, nt, (bt / PAGE_SZ) as int, 1, None);
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
            assert(s2.blocks.small_free((bn / PAGE_SZ) as int, 0));
            assert(s2.blocks.tracks_addr_run(bn, order_pages(0)));
            assert((bt / PAGE_SZ) as int + order_pages(THREAD_ORDER as usize) <= (bn / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s2, s3, process, bn, 0, nt, (bt / PAGE_SZ) as int, 1, None);
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s3.blocks.small_free((bl / PAGE_SZ) as int, 1));
            assert(s3.blocks.tracks_addr_run(bl, order_pages(1)));
            assert(s3.can_retype_leaf(process, ROOT_UNTYPED_SLOT, Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 }, bl));
        }

        let at2 = Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 };
        let ok4 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl, Tracked(&mut steps));
        let ghost s4 = *self;
        proof {
            assert(ok4);
            assert(Self::leaf_retyped(s3, s4, process, ROOT_UNTYPED_SLOT, at2, bl));
            assert(s4.tables.leaf(base, 0) == bl);
            assert(index_ok(1) && index_entry(1) == 0) by (compute_only);
            assert(s4.tables.has_slot(&s4.list, base, 1));
            assert(s4.tables.node_of(base, 1) == nn2);
            assert(bl + PAGE_SZ <= base + 2 * PROCESS_BYTES && nn2 < NODE_SPACE);
            assert(!s4.list.nodes@[nn2 as int].live);
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_FRAME_SLOT));
            assert(s4.tables.node_of(process, WITNESS_FRAME_SLOT) == nn);
            assert(!s4.list.nodes@[nn as int].live);
            assert(Self::page_count_kept(s3, s4));
            assert(Self::retype_keeps(s3, s4, bl, (bl / PAGE_SZ) as int, 1, Some((base, 0))));
            assert(Self::leaf_retype_kept(s3, s4));
            assert(core_cap != bl && nt != bl);
            Self::lemma_wakes_slot_kept(s3, s4, process, cs, core_cap, core_payload(1, MAX_PRIORITY), bl, (bl / PAGE_SZ) as int, 1, Some((base, 0)));
            Self::lemma_wakes_slot_kept(s3, s4, process, WITNESS_THREAD_SLOT, nt, thread_of(bt), bl, (bl / PAGE_SZ) as int, 1, Some((base, 0)));
            assert(s4.threads == s3.threads);
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
            assert(s3.blocks.small_free((bn / PAGE_SZ) as int, 0));
            assert(s3.blocks.tracks_addr_run(bn, order_pages(0)));
            assert((bl / PAGE_SZ) as int + order_pages(1) <= (bn / PAGE_SZ) as int);
            Self::lemma_wakes_block_survives(s3, s4, process, bn, 0, bl, (bl / PAGE_SZ) as int, 1, Some((base, 0)));
            assert(s4.can_retype_under(process, ROOT_UNTYPED_SLOT, bn, 0));
            assert(s4.blocks.small_free((bn / PAGE_SZ) as int, 0));
            assert(s4.blocks.tracks_addr_run(bn, order_pages(0)));
            assert(s4.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bn, 0));
        }

        let ok5 = self.retype_notification(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bn, Tracked(&mut steps));
        let ghost s5 = *self;
        let from_notif = Position { through: None, index: WITNESS_FRAME_SLOT };
        let to_notif = Position { through: Some(WITNESS_PROCESS_SLOT), index: 1 };
        proof {
            assert(ok5);
            assert(Self::queue_retyped(s4, s5, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bn, CapKind::Notification));
            assert(Self::retype_keeps(s4, s5, nn, (bn / PAGE_SZ) as int, 0, None));
            assert(Self::queue_retype_keeps(s4, s5));
            assert(core_cap != nn && nt != nn);
            Self::lemma_wakes_slot_kept(s4, s5, process, cs, core_cap, core_payload(1, MAX_PRIORITY), nn, (bn / PAGE_SZ) as int, 0, None);
            Self::lemma_wakes_slot_kept(s4, s5, process, WITNESS_THREAD_SLOT, nt, thread_of(bt), nn, (bn / PAGE_SZ) as int, 0, None);
            assert(s5.threads == s4.threads);
            assert(s4.list.wf() && s5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s4.list.nodes@[u as int].live);
            assert(s4.list.nodes@[b2 as int].live);
            assert(s4.list.parent@[b2] == u);
            assert(u != nn && u != nn2 && nn2 != nn && b2 != nn && b2 != nn2);
            lemma_added_children(s4.list, s5.list, nn, u);
            assert(forall|x: usize| !#[trigger] s5.list.is_child(nn, x));
            assert(s5.list.nodes@[nn as int].depth == 2);
            assert(s5.list.nodes@[u as int].depth == 1);
            assert(s5.list.nodes@[b2 as int].live);
            assert(s5.list.parent@[b2] == u);
            assert(s5.table_at(process, None) == Some(process));
            assert(s5.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s5.cap_at(process, from_notif) == Some(nn));
            assert(s5.can_move_at(process, from_notif, to_notif));
        }

        // Move the notification's sole capability into slot 1 of `base`'s table, then place and
        // start `bt` on core 1, load `base` on core 1, and wait on the notification.
        let ok6 = self.move_cap(process, from_notif, to_notif);
        let ghost s6 = *self;
        proof {
            assert(ok6);
            assert(Self::cap_moved_at(s5, s6, process, from_notif, to_notif));
            assert(s6.list.childless(nn2) && s6.list.nodes@[nn2 as int].depth == 2
                && s6.list.nodes@[nn2 as int].live
                && (forall|x: usize| !#[trigger] s6.list.is_child(nn2, x))
                && s6.list.nodes@[b2 as int].live && s6.list.parent@[b2] == u
                && s6.list.parent@.contains_key(b2)
                && s6.can_place(process, WITNESS_THREAD_SLOT, cs, 0)
                && s6.holds_core(process, cs, 0)
                && Self::move_kept(s5, s6)
                && s6.threads.records == s5.threads.records) by {
            assert(s5.list.wf() && s6.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s6.list.parent@ == moved_parent(s5.list.parent@, nn, nn2));
            assert(s5.list.nodes@[nn as int].depth == 2);
            assert(s5.list.d(s5.list.seq@[0]) == 0);
            assert(s6.list.seq@[0] == s5.list.seq@[0]);
            assert(!s5.list.nodes@[nn2 as int].live);
            assert(s5.list.parent@[nn] != nn2) by {
                assert(s5.list.parent@[nn] == u);
            }
            assert forall|x: usize| !#[trigger] s6.list.is_child(nn2, x) by {
                if s6.list.is_child(nn2, x) {
                    lemma_listed_live(s6.list, x);
                    assert(x != nn);
                    if x == nn2 {
                        assert(s6.list.parent@[nn2] == rename(s5.list.parent@[nn], nn, nn2));
                    } else {
                        assert(s5.list.nodes@[x as int].live);
                        assert(has(s5.list.seq@, x));
                        lemma_has(s5.list.seq@, x);
                        assert(x != s5.list.seq@[0]);
                        assert(s5.list.parent@.contains_key(x));
                        s5.list.lemma_parent_live(x);
                        assert(s5.list.parent@[x] != nn2);
                        assert(s6.list.parent@[x] == rename(s5.list.parent@[x], nn, nn2));
                        assert(s5.list.parent@[x] == nn);
                        assert(s5.list.is_child(nn, x));
                    }
                }
            }
            assert(s6.list.nodes@[nn2 as int].depth == 2);
            assert(s6.list.nodes@[nn2 as int].live) by {
                reveal(CapKernel::wf);
            }
            if !s6.list.childless(nn2) {
                s6.list.lemma_next_is_child(nn2);
            }
            assert(s6.list.childless(nn2));
            assert(nn % PAGE_SZ != 0 && nn2 % PAGE_SZ != 0);
            lemma_slot_kept_two(s5, s6, process, cs, nn, nn2);
            lemma_slot_kept_two(s5, s6, process, WITNESS_THREAD_SLOT, nn, nn2);
            lemma_slot_kept_two(s5, s6, process, ROOT_UNTYPED_SLOT, nn, nn2);
            lemma_slot_kept_two(s5, s6, base, 1, nn, nn2);
            assert(s6.list.nodes@[b2 as int].live && s6.list.parent@[b2] == u);
            assert(s6.list.parent@.contains_key(b2));
            assert(s5.slot_holds(process, cs, core_cap, core_payload(1, MAX_PRIORITY)));
            assert(s5.list.nodes@[core_cap as int].depth == 1);
            assert(s5.tables.node_of(process, WITNESS_FRAME_SLOT) == nn);
            assert(s5.tables.node_of(base, 1) == nn2);
            assert(core_cap != nn && core_cap != nn2);
            Self::lemma_wakes_move_keeps_slot(s5, s6, process, from_notif, to_notif, process, cs, core_cap, core_payload(1, MAX_PRIORITY));
            assert(s6.slot_holds(process, cs, core_cap, core_payload(1, MAX_PRIORITY)));
            assert(s6.list.nodes@[core_cap as int].depth == 1);
            assert(s5.slot_holds(process, WITNESS_THREAD_SLOT, nt, thread_of(bt)));
            assert(nt != nn && nt != nn2);
            Self::lemma_wakes_move_keeps_slot(s5, s6, process, from_notif, to_notif, process, WITNESS_THREAD_SLOT, nt, thread_of(bt));
            assert(s6.slot_holds(process, WITNESS_THREAD_SLOT, nt, thread_of(bt)));
            assert(s6.tables.has_slot(&s6.list, process, cs));
            assert(s6.tables.node_of(process, cs) == core_cap);
            assert(s6.is_cap(core_cap) && s6.payload_of(core_cap) == core_payload(1, MAX_PRIORITY));
            assert(s6.payload_of(core_cap).kind is Core && s6.payload_of(core_cap).priority == MAX_PRIORITY);
            assert(s6.tables.has_slot(&s6.list, process, WITNESS_THREAD_SLOT));
            assert(s6.tables.node_of(process, WITNESS_THREAD_SLOT) == nt);
            assert(s6.is_cap(nt) && s6.payload_of(nt) == thread_of(bt));
            assert(THREAD_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(Self::move_kept(s5, s6));
            assert(s6.threads.records == s5.threads.records);
            assert(s6.processes.records == s5.processes.records);
            assert(s6.threads.records@[bt].value().state is Inactive);
            assert(!s6.threads.records@[bt].value().dying);
            assert(s6.threads.records@[bt].value().placement is None);
            assert(s6.threads.records@[bt].value().process == Some(base));
            assert(!s6.processes.records@[base].value().dead);
            assert(!s6.cap_dead(nt));
            assert(s6.can_control(process, WITNESS_THREAD_SLOT));
            assert(1 < MAX_DEPTH) by (compute_only);
            assert(s6.holds_core(process, cs, 0));
            assert(s6.can_place(process, WITNESS_THREAD_SLOT, cs, 0));
            }
        }

        let placed = self.place(process, WITNESS_THREAD_SLOT, cs, 0);
        let ghost s7 = *self;
        proof {
            assert(placed);
            lemma_core_object(1);
            assert(Self::placed(s6, s7, core_cap, bt, Placement { core: 1, priority: 0 }));
            assert(s7.can_start(process, WITNESS_THREAD_SLOT));
            assert(s7.endpoints == s6.endpoints);
            // Place adds the thread's placement node under the core capability. The notification,
            // already childless, is not that node, so it stays childless at the depth it had.
            assert(s7.list.childless(nn2) && s7.list.nodes@[nn2 as int].depth == 2) by {
                let px = placement_node(bt);
                assert(px == (bt + 1) as usize);
                assert(px != nn2 && px != core_cap && core_cap != nn2);
                assert(s6.list.wf() && s7.list.wf()) by {
                    reveal(CapKernel::wf);
                    assert(s6.wf() && s7.wf());
                }
                assert(s7.list.parent@ == s6.list.parent@.insert(px, core_cap));
                assert(s7.list.seq@[0] == s6.list.seq@[0]);
                assert forall|x: usize| !#[trigger] s7.list.is_child(nn2, x) by {
                    if s7.list.is_child(nn2, x) {
                        if x == px {
                            assert(s7.list.parent@[px] == core_cap);
                        } else {
                            lemma_listed_live(s7.list, x);
                            assert(s7.list.nodes@[x as int].live == s6.list.nodes@[x as int].live);
                            assert(has(s6.list.seq@, x));
                            lemma_has(s6.list.seq@, x);
                            let k = choose|k: int| 0 <= k < s6.list.seq@.len() && s6.list.seq@[k] == x;
                            let j = choose|j: int| 0 <= j < s7.list.seq@.len() && s7.list.seq@[j] == x;
                            assert(j != 0);
                            assert(s7.list.parent@.contains_key(s7.list.seq@[j]));
                            assert(s6.list.parent@.contains_key(x));
                            if k == 0 {
                                assert(!s6.list.parent@.contains_key(s6.list.seq@[0]));
                            }
                            assert(s6.list.parent@.contains_key(s6.list.seq@[k]));
                            assert(s6.list.is_child(nn2, x));
                        }
                    }
                }
                assert(s7.list.nodes@[nn2 as int].live);
                assert(s7.list.nodes@[nn2 as int].depth == s6.list.nodes@[nn2 as int].depth);
                assert(s6.list.nodes@[nn2 as int].depth == 2);
                assert(nn2 < NODE_SPACE);
                if !s7.list.childless(nn2) {
                    s7.list.lemma_next_is_child(nn2);
                }
            }
        }

        let started = self.start(process, WITNESS_THREAD_SLOT);
        let ghost s8 = *self;
        proof {
            assert(started);
            assert(Self::state_written(s7, s8, bt, ThreadState::Runnable { core: 1 }));
            assert(s8.list == s7.list && s8.endpoints == s7.endpoints);
            assert(witness_alive(s8, base) && space_wf(&s8.list, &s8.spaces, &s8.blocks, base)) by {
                reveal(CapKernel::wf);
                assert(process_spaces_wf(&s8.spaces, &s8.processes));
            }
            assert(s8.spaces.roots@.contains_key(base) && s8.spaces.records@[base].value().kind is Process);
            assert(s8.cores@[1].current_thread is None && s8.cores@[1].generation == 1 && s8.cores@[1].space is None
                && !s8.processes.records@[base].value().dead
                && !s8.threads.records@[bt].value().pending_stop) by {
                reveal(CapKernel::wf);
                reveal(current_wf);
            }
            lemma_block_page(base, SPACE_ROOT_PAGE as int);
        }

        let pcid = self.load_space(1, base, report, Tracked(&mut steps));
        let ghost s8a = *self;
        self.switch_space(1, Some(base), base + SPACE_ROOT_PAGE * PAGE_SZ, pcid, report);
        let ghost s8b = *self;
        proof {
            assert(s8a.list == s8.list && s8a.endpoints == s8.endpoints && s8a.threads == s8.threads);
            assert(s8b.list == s8a.list && s8b.endpoints == s8a.endpoints && s8b.threads == s8a.threads);
            assert(self.threads.records@[bt].value().state == (ThreadState::Runnable { core: 1 }));
            assert(self.threads.records@[bt].value().process == Some(base));
            assert(self.threads.records@[bt].value().placement == Some(Placement { core: 1, priority: 0 }));
        }
        self.switch_in(1, bt);
        let ghost s9 = *self;
        proof {
            assert(Self::switch_frame(s8b, s9, 1, bt));
            assert(s9.list == s8b.list && s9.endpoints == s8b.endpoints);
            assert(s9.cores@[1].current_thread == Some(bt));
            assert(s9.threads.records@[bt].value().placement == Some(Placement { core: 1, priority: 0 }));
            assert(s9.current_live(1));
            assert(s9.caller_live(1, base));
            assert(s9.holds_notification(base, 1, RECEIVE_RIGHT)) by {
                assert(s9.tables.has_slot(&s9.list, base, 1));
                assert(s9.is_cap(nn2) && s9.payload_of(nn2) == queue_of(CapKind::Notification, bn));
                assert(NOTIFICATION_RIGHTS & RECEIVE_RIGHT == RECEIVE_RIGHT) by (compute_only);
            }
            assert(s9.can_wait(1, base, 1));
            // The retype wrote a fresh record, and every step since kept the endpoint records.
            assert(s9.endpoints.records@[bn].value() == fresh_record()) by {
                assert(Self::queue_retyped(s4, s5, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bn, CapKind::Notification));
                assert(s5.endpoints.records@[bn].value() == fresh_record());
                assert(Self::cap_moved_at(s5, s6, process, from_notif, to_notif));
                let src = s5.table_at(process, from_notif.through)->0;
                let dst = s5.table_at(process, to_notif.through)->0;
                assert(Self::cap_moved_between(s5, s6, src, from_notif.index, dst, to_notif.index));
                let i = s5.tables.node_of(src, from_notif.index);
                let n = s5.tables.node_of(dst, to_notif.index);
                assert(Self::move_frame(s5, s6, i, n));
                assert(s6.endpoints.records == s5.endpoints.records);
                assert(s7.endpoints == s6.endpoints);
                assert(s8.endpoints == s7.endpoints);
                assert(s8a.endpoints == s8.endpoints);
                assert(s8b.endpoints == s8a.endpoints);
                assert(s9.endpoints == s8b.endpoints);
            }
            assert(s9.notification_at(base, 1) == bn);
            assert(s9.notification_record(base, 1) == fresh_record());
            assert(0u64 & SIGNAL_BITS == 0) by (compute_only); // not a page size: zero signal bits
            assert(!s9.wait_signalled(base, 1));
            assert(s9.threads.records@[bt].value().queued == NONE) by {
                assert(s3.threads.records@[bt].value() == ThreadRecord { process: Some(base), ..fresh_thread() });
                assert(fresh_thread().queued == NONE);
                assert(s4.threads == s3.threads);
                assert(s5.threads == s4.threads);
                assert(s6.threads.records == s5.threads.records);
                assert(s7.threads.records@[bt].value() == ThreadRecord {
                    placement: Some(Placement { core: 1, priority: 0 }),
                    ..s6.threads.records@[bt].value()
                });
                assert(Self::state_written(s7, s8, bt, ThreadState::Runnable { core: 1 }));
                assert(same_thread_but_links(
                    s8.threads.records@[bt].value(),
                    ThreadRecord { state: ThreadState::Runnable { core: 1 }, ..s7.threads.records@[bt].value() },
                ));
                assert(s8a.threads == s8.threads);
                assert(s8b.threads == s8a.threads);
                assert(keeps_wait(s8b.threads.records@[bt].value(), s9.threads.records@[bt].value()));
            }
        }

        let waited = self.wait(1, base, 1, registers);
        let ghost s10 = *self;
        proof {
            assert(waited is Blocked);
            assert(Self::wait_blocked(s9, s10, 1, base, 1, registers));
            assert(s10.threads.records@[bt].value().state == (ThreadState::Blocked { object: bn }));
            assert(s10.threads.records@[bt].value().placement == Some(Placement { core: 1, priority: 0 }));
            assert(s10.threads.records@[bt].value().frame == partial_frame(registers));
            assert(s9.endpoints.records@[bn].value().waiters@ == fresh_record().waiters@);
            assert(fresh_record().waiters@ == Seq::<usize>::empty());
            assert(s10.endpoints.records@[bn].value().waiters@ == fresh_record().waiters@.push(bt));
            assert(s10.endpoints.records@[bn].value().waiters@ =~= seq![bt]);
            assert(s10.cores@[1].current_thread is None);
            assert(s10.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s10.cap_at(process, to_notif) == Some(nn2));
            // Wait rewrites the queue, the thread and this core. The capability list is the one place left childless.
            assert(s10.list == s9.list) by {
                assert(s10 == (CapKernel { endpoints: s10.endpoints, threads: s10.threads, cores: s10.cores, ..s9 }));
            }
            assert(s9.list == s7.list);
            assert(s10.list.childless(nn2));
            assert(s10.list.nodes@[nn2 as int].depth == 2);
            assert(s10.can_delete_at(process, to_notif));
            assert(s10.is_cap(u) && s10.payload_of(u).kind is Untyped
                && s10.payload_of(u).rights & right_bit(Right::Retype) != 0
                && block_within(bn, 0, s10.payload_of(u))
                && s10.is_cap(nn2) && s10.payload_of(nn2).kind is Notification
                && s10.payload_of(nn2).base == bn
                && s10.list.nodes@[b2 as int].live && s10.list.parent@[b2] == u
                && s10.list.parent@.contains_key(b2)
                && s10.tables.has_slot(&s10.list, process, ROOT_UNTYPED_SLOT)
                && s10.tables.node_of(process, ROOT_UNTYPED_SLOT) == u
                && s10.tables.roots@.contains_key(process)
                && s10.root_live(process)
                && s10.list.nodes@.len() == NODE_SPACE
                && b2 < NODE_SPACE && u < NODE_SPACE
                && s10.blocks.tracks((bn / PAGE_SZ) as int)
                && s10.blocks.pages@[(bn / PAGE_SZ) as int].kind is Base
                && s10.blocks.pages@[(bn / PAGE_SZ) as int].object is Notification
                && s10.blocks.pages@[(bn / PAGE_SZ) as int].refs == 1
                && !s10.blocks.pages@[(bn / PAGE_SZ) as int].dead
                && 1 < s10.cores@.len()
                && nn2 % PAGE_SZ != 0
                && u != nn2 && b2 != nn2) by {
            assert(s6.wf());
            assert(b2 % PAGE_SZ == 0);
            assert(bt == b2 + 2 * PAGE_SZ);
            assert(s8a.tables == s8.tables && s8a.list == s8.list);
            assert(s8b.tables == s8a.tables && s8b.list == s8a.list);
            Self::lemma_witness_dead_notification_wakes_slot(
                s0, s1, s2, s3, s4, s5, s6, s7, s8, s8a, s8b, s9, s10,
                process, base, b2, bt, bl, bn, np, nt, nn, core_cap, from_notif, to_notif, registers,
            );
            assert(s8a.blocks == s8.blocks && s8a.processes == s8.processes);
            assert(s8b.blocks == s8a.blocks && s8b.processes == s8a.processes);
            assert(s5.blocks.pages@.len() == s4.blocks.pages@.len());
            assert(s0.wf());
            assert(s10.wf());
            assert(Self::place_kept(s6, s7, process));
            assert(from_notif == (Position { through: None, index: WITNESS_FRAME_SLOT }));
            assert(to_notif == (Position { through: Some(WITNESS_PROCESS_SLOT), index: 1 }));
            assert(s6.list.parent@.contains_key(b2));
            assert(u != nn2 && b2 != nn2);
            Self::lemma_witness_dead_notification_wakes_bridge(
                s0, s1, s2, s3, s4, s5, s6, s7, s8, s8a, s8b, s9, s10,
                process, base, b2, bt, bl, bn, u, np, nt, nn, nn2, core_cap,
                free@, from_notif, to_notif, registers,
            );
            assert(s10.is_cap(u) && s10.payload_of(u).kind is Untyped);
            assert(s10.payload_of(u).rights & right_bit(Right::Retype) != 0);
            assert(block_within(bn, 0, s10.payload_of(u)));
            assert(s10.is_cap(nn2) && s10.payload_of(nn2).kind is Notification && s10.payload_of(nn2).base == bn);
            assert(s10.list.nodes@[b2 as int].live && s10.list.parent@[b2] == u);
            assert(s10.tables.has_slot(&s10.list, process, ROOT_UNTYPED_SLOT));
            assert(s10.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s10.tables.roots@.contains_key(process) && s10.root_live(process));
            assert(s10.list.nodes@.len() == NODE_SPACE);
            assert(b2 < NODE_SPACE && u < NODE_SPACE);
            assert(s10.blocks.tracks((bn / PAGE_SZ) as int));
            assert(s10.blocks.pages@[(bn / PAGE_SZ) as int].kind is Base);
            assert(s10.blocks.pages@[(bn / PAGE_SZ) as int].object is Notification);
            assert(s10.blocks.pages@[(bn / PAGE_SZ) as int].refs == 1);
            assert(!s10.blocks.pages@[(bn / PAGE_SZ) as int].dead);
            assert(bn / PAGE_SZ == base / PAGE_SZ + 14);
            Self::lemma_witness_dead_notification_wakes_cores(s10);
            assert(1 < NUM_CPUS) by (compute_only);
            assert(1 < s10.cores@.len());
            assert(s10.list.parent@.contains_key(b2));
            assert(nn2 % PAGE_SZ != 0);
            }
        }

        let (deleted, slice, freed) = self.witness_dead_notification_wakes_reclaims(
            process, to_notif, base, bt, bn, b2, Ghost(u), Ghost(nn2), registers, Tracked(&mut steps),
        );
        (waited, deleted, slice, freed)

    }
}

} // verus!
