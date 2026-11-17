// SPDX-License-Identifier: MIT

//! The witnesses for skipping and removing stale notification waiters on `signal` and `wait` and
//! for unlinking and freeing a destroyed queued thread.
//! It is a module of its own so `witness.rs` stays within the file-size bound and its shared
//! solver context does not grow with these proofs. Only Verus compiles this module, so no image
//! contains it.

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
use crate::capability::operation::{Outcome, STATUS_OK};
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
use crate::util::page_ptr_util_u::mem_valid;

use crate::capability::witness::*;

impl CapKernel {

    /// Proves that pages `b3 / PAGE_SZ + 2..b3 / PAGE_SZ + 8` still have zero stale epoch in `s3`.
    #[verifier::spinoff_prover]
    proof fn lemma_setup_waiter_stale_zero(pre_boot: Self, s3: Self, b3: usize)
        requires
            pre_boot.wf(),
            pre_boot.flush_epoch == 0,
            s3.wf(),
            s3.stale_epoch == pre_boot.stale_epoch,
            b3 % PAGE_SZ == 0,
            b3 / PAGE_SZ + 8 <= pre_boot.blocks.pages@.len(),
        ensures
            forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> #[trigger] s3.stale_epoch.pages@[j] == 0,
    {
        reveal(CapKernel::wf);
        pre_boot.lemma_page_span();
        assert(pre_boot.tlb_wf());
        assert forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8
            implies #[trigger] s3.stale_epoch.pages@[j] == 0 by {
            assert(pre_boot.stale_epoch.pages@[j] <= pre_boot.flush_epoch);
        }
    }

    /// Tables and process liveness preserved across `witness_spawn_placed_waiter` and
    /// `witness_spawn_and_block_waiter`, kept opaque so callers do not carry extra quantifiers.
    #[verifier::opaque]
    pub open spec fn waiter_tables_kept(pre: Self, post: Self) -> bool {
        &&& post.tables.roots == pre.tables.roots
        &&& forall|r: usize, e: int| pre.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES
            ==> (#[trigger] post.tables.leaf(r, e)) == pre.tables.leaf(r, e)
        &&& forall|r: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, r, i) ==> {
            &&& post.tables.has_slot(&post.list, r, i)
            &&& post.tables.node_of(r, i) == pre.tables.node_of(r, i)
        }
        &&& forall|x: usize| #[trigger] pre.is_cap(x) ==> {
            &&& post.is_cap(x)
            &&& post.payload_of(x) == pre.payload_of(x)
        }
        &&& forall|p: usize| #[trigger] pre.processes.records@.contains_key(p) ==> {
            &&& post.processes.records@.contains_key(p)
            &&& post.processes.records@[p].value().dead == pre.processes.records@[p].value().dead
        }
    }

    /// Helper for `witness_setup_waiter_process`: preserves depth 1 across `derive` for nodes
    /// other than the derived child `nc`.
    #[verifier::spinoff_prover]
    proof fn lemma_setup_waiter_depth(s2: Self, s3: Self, nc: usize, ne: usize, x: usize)
        requires
            s2.wf(),
            s3.wf(),
            Self::derive_linked(s2, s3, nc, ne),
            Self::derive_step(s2, s3, nc),
            x != nc,
            s2.is_cap(x),
            s2.list.nodes@[x as int].depth == 1,
        ensures
            s3.is_cap(x),
            s3.list.nodes@[x as int].live,
            s3.list.nodes@[x as int].depth == 1,
    {
        s2.lemma_slot_bound(x);
        Self::lemma_caps_frame(s2, s3, nc, nc, x);
        lemma_depth_one_kept(s2.list, s3.list, nc, x);
    }

    /// Helper for `witness_setup_waiter_process`: proves `bt1`/`bt2` alignment, free ranges,
    /// `can_retype_under`, and thread-record absence in `s3`.
    #[verifier::spinoff_prover]
    proof fn lemma_setup_waiter_bt(
        pre_boot: Self,
        s3: Self,
        process: usize,
        leaf: usize,
        first: Payload,
        base: usize,
        b3: usize,
    )
        requires
            pre_boot.wf(),
            s3.wf(),
            s3.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            base % PROCESS_BYTES == 0,
            base % PAGE_SZ == 0,
            base + 3 * PROCESS_BYTES <= NODE_SPACE,
            leaf + LEAF_BYTES <= NODE_SPACE,
            b3 == (base + 2 * PROCESS_BYTES) as usize,
            b3 % PAGE_SZ == 0,
            witness_block(pre_boot, b3, first),
            pre_boot.blocks.tracks((b3 / PAGE_SZ + 7) as int),
            s3.blocks.tracks_addr_run(b3, 8),
            forall|x: int| 0 <= x < s3.blocks.num_2m()
                ==> (#[trigger] s3.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed,
            forall|x: int| 0 <= x < s3.blocks.num_1g()
                ==> (#[trigger] s3.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed,
            forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> {
                &&& (#[trigger] s3.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                &&& s3.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                &&& s3.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
            },
            s3.root_untyped(process) == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s3.slot_holds(process, ROOT_UNTYPED_SLOT, (leaf + ROOT_UNTYPED_SLOT) as usize, first),
            s3.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].live,
            s3.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].depth == 1,
            first.kind is Untyped,
            first.rights == UNTYPED_RIGHTS,
        ensures
            ({
                let bt1 = (b3 + 2 * PAGE_SZ) as usize;
                let bt2 = (b3 + 4 * PAGE_SZ) as usize;
                &&& b3 + 6 * PAGE_SZ <= NODE_SPACE
                &&& s3.blocks.tracks_addr_run(bt1, 2)
                &&& s3.blocks.tracks_addr_run(bt2, 2)
                &&& bt1 % THREAD_BYTES == 0
                &&& bt1 / PAGE_SZ == b3 / PAGE_SZ + 2
                &&& s3.blocks.small_free((bt1 / PAGE_SZ) as int, THREAD_ORDER as usize)
                &&& s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER)
                &&& !s3.threads.records@.contains_key(bt1)
                &&& bt2 % THREAD_BYTES == 0
                &&& bt2 / PAGE_SZ == b3 / PAGE_SZ + 4
                &&& s3.blocks.small_free((bt2 / PAGE_SZ) as int, THREAD_ORDER as usize)
                &&& s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bt2, THREAD_ORDER)
                &&& !s3.threads.records@.contains_key(bt2)
            }),
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost u = (leaf + ROOT_UNTYPED_SLOT) as usize;
        let ghost bt1 = (b3 + 2 * PAGE_SZ) as usize;
        let ghost bt2 = (b3 + 4 * PAGE_SZ) as usize;
        assert(PROCESS_BYTES == 8 * PAGE_SZ);
        assert(THREAD_BYTES == 2 * PAGE_SZ);
        assert(b3 == base + 2 * PROCESS_BYTES);
        assert(bt1 == b3 + 2 * PAGE_SZ);
        assert(bt2 == b3 + 4 * PAGE_SZ);
        assert(b3 + 6 * PAGE_SZ <= NODE_SPACE);
        assert(order_pages(THREAD_ORDER as usize) == 2) by (compute_only);
        assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
        assert(1usize < MAX_DEPTH) by (compute_only);
        assert(THREAD_ORDER == 1) by (compute_only);
        lemma2_to64();
        assert(block_bytes(3) == 8 * PAGE_SZ);
        assert(block_bytes(THREAD_ORDER) == 2 * PAGE_SZ);
        assert(b3 % PROCESS_BYTES == 0) by (nonlinear_arith)
            requires
                base % PROCESS_BYTES == 0,
                b3 == base + 2 * PROCESS_BYTES;
        lemma_block_page(b3, 2);
        lemma_block_page(b3, 4);
        assert(bt1 % THREAD_BYTES == 0 && bt2 % THREAD_BYTES == 0) by (nonlinear_arith)
            requires
                base % PROCESS_BYTES == 0,
                PROCESS_BYTES == 8 * PAGE_SZ,
                THREAD_BYTES == 2 * PAGE_SZ,
                PAGE_SZ > 0,
                b3 == base + 2 * PROCESS_BYTES,
                bt1 == b3 + 2 * PAGE_SZ,
                bt2 == b3 + 4 * PAGE_SZ;
        assert(s3.blocks.tracks_addr_run(bt1, 2));
        assert(s3.blocks.tracks_addr_run(bt2, 2));
        assert(bt1 / PAGE_SZ == b3 / PAGE_SZ + 2);
        assert(bt2 / PAGE_SZ == b3 / PAGE_SZ + 4);
        assert(!s3.blocks.covered((bt1 / PAGE_SZ) as int)) by {
            reveal(CapKernel::wf);
            assert(s3.blocks.tracks((bt1 / PAGE_SZ) as int));
            assert(0 <= region_2m((bt1 / PAGE_SZ) as int) < s3.blocks.num_2m());
            assert(0 <= region_1g((bt1 / PAGE_SZ) as int) < s3.blocks.num_1g());
            assert(pre_boot.blocks.num_2m() == s3.blocks.num_2m());
            assert(pre_boot.blocks.num_1g() == s3.blocks.num_1g());
            assert(!pre_boot.blocks.covered((b3 / PAGE_SZ) as int));
        }
        assert(!s3.blocks.covered((bt2 / PAGE_SZ) as int)) by {
            reveal(CapKernel::wf);
            assert(s3.blocks.tracks((bt2 / PAGE_SZ) as int));
            assert(0 <= region_2m((bt2 / PAGE_SZ) as int) < s3.blocks.num_2m());
            assert(0 <= region_1g((bt2 / PAGE_SZ) as int) < s3.blocks.num_1g());
            assert(pre_boot.blocks.num_2m() == s3.blocks.num_2m());
            assert(pre_boot.blocks.num_1g() == s3.blocks.num_1g());
            assert(!pre_boot.blocks.covered((b3 / PAGE_SZ) as int));
        }
        assert(s3.blocks.small_free((bt1 / PAGE_SZ) as int, 1)) by {
            assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s3.blocks.pages@[bt1 / PAGE_SZ + k].kind is Free by {
                assert(bt1 / PAGE_SZ + k == b3 / PAGE_SZ + (2 + k));
                assert(pre_boot.blocks.pages@[b3 / PAGE_SZ + (2 + k)].kind is Free);
            }
        }
        assert(s3.blocks.small_free((bt2 / PAGE_SZ) as int, 1)) by {
            assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s3.blocks.pages@[bt2 / PAGE_SZ + k].kind is Free by {
                assert(bt2 / PAGE_SZ + k == b3 / PAGE_SZ + (4 + k));
                assert(pre_boot.blocks.pages@[b3 / PAGE_SZ + (4 + k)].kind is Free);
            }
        }
        assert(s3.root_untyped(process) == u);
        assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
        assert(s3.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
        assert(s3.list.nodes@[u as int].depth == 1);
        assert(block_within(bt1, THREAD_ORDER, first));
        assert(block_within(bt2, THREAD_ORDER, first));
        assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER));
        assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bt2, THREAD_ORDER));
        assert(!s3.threads.records@.contains_key(bt1)) by {
            reveal(CapKernel::wf);
            if s3.threads.records@.contains_key(bt1) {
                assert(thread_wf(&s3.list, &s3.threads, &s3.blocks, bt1));
            }
        }
        assert(!s3.threads.records@.contains_key(bt2)) by {
            reveal(CapKernel::wf);
            if s3.threads.records@.contains_key(bt2) {
                assert(thread_wf(&s3.list, &s3.threads, &s3.blocks, bt2));
            }
        }
    }

    /// Helper for `witness_setup_waiter_process`: proves post-`derive` state and waiter-slot facts.
    #[verifier::spinoff_prover]
    proof fn lemma_setup_waiter_s3(
        pre_boot: Self,
        s2: Self,
        s3: Self,
        process: usize,
        p2: usize,
        leaf: usize,
        first: Payload,
        base: usize,
        b3: usize,
        t: usize,
        kernel_root: usize,
    )
        requires
            pre_boot.wf(),
            pre_boot.flush_epoch == 0,
            s2.wf(),
            s3.wf(),
            s2.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            s3.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            base % PROCESS_BYTES == 0,
            base % PAGE_SZ == 0,
            base + 3 * PROCESS_BYTES <= NODE_SPACE,
            p2 == (base + PROCESS_BYTES) as usize,
            b3 == (base + 2 * PROCESS_BYTES) as usize,
            b3 % PAGE_SZ == 0,
            leaf % PAGE_SZ == 0,
            leaf + LEAF_BYTES <= NODE_SPACE,
            (base + 2 * PAGE_SZ) as usize != leaf,
            witness_block(pre_boot, b3, first),
            pre_boot.blocks.tracks((b3 / PAGE_SZ + 7) as int),
            first.kind is Untyped,
            first.rights == UNTYPED_RIGHTS,
            Self::cap_derived_at(
                s2,
                s3,
                process,
                WITNESS_FRAME_SLOT,
                Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT },
                RECEIVE_RIGHT,
                base,
                0,
                0,
            ),
            Self::derive_step(s2, s3, (b3 + 1) as usize),
            Self::derive_counted(s2, s3, (base + 2 * PAGE_SZ + 3) as usize),
            Self::derive_kept(s2, s3),
            Self::derive_linked(s2, s3, (b3 + 1) as usize, (base + 2 * PAGE_SZ + 3) as usize),
            s2.blocks.tracks_addr_run(b3, 8),
            s2.stale_epoch == pre_boot.stale_epoch,
            s2.flush_epoch == 0,
            s2.cores@[0].current_thread == Some(t),
            s2.cores@[0].generation == 1,
            s2.loaded(0, process),
            s2.spaces.kernel_root@ == kernel_root,
            kernel_root % PAGE_SZ == 0,
            crate::util::page_ptr_util_u::mem_valid(kernel_root),
            s2.threads.queues.all_empty(),
            s2.threads.records@.contains_key(t),
            s2.threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            s2.threads.records@[t].value().process == Some(process),
            !s2.threads.records@[t].value().dying,
            !s2.threads.records@[t].value().pending_stop,
            s2.threads.records@[t].value().queued != base,
            s2.processes.records@.contains_key(process),
            !s2.processes.records@[process].value().dead,
            s2.processes.records@.contains_key(p2),
            !s2.processes.records@[p2].value().dead,
            s2.tables.roots@.contains_key(process),
            s2.root_live(process),
            s2.root_untyped(process) == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s2.tables.leaf(process, 0) == leaf,
            s2.tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            s2.tables.roots@.contains_key(p2),
            s2.tables.leaf(p2, 0) == b3,
            s2.tables.leaf(p2, 2) == NO_LEAF,
            s2.slot_holds(process, ROOT_UNTYPED_SLOT, (leaf + ROOT_UNTYPED_SLOT) as usize, first),
            s2.slot_holds(process, ROOT_CORE_SLOT, (leaf + ROOT_CORE_SLOT) as usize, core_payload(0, MAX_PRIORITY)),
            s2.is_cap((leaf + ROOT_UNTYPED_SLOT) as usize),
            s2.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].depth == 1,
            s2.is_cap((leaf + ROOT_CORE_SLOT) as usize),
            s2.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].depth == 1,
            s2.slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            s2.is_cap((base + 2 * PAGE_SZ + 1) as usize),
            s2.list.nodes@[(base + 2 * PAGE_SZ + 1) as int].depth == 2,
            s2.list.parent@[(base + 2 * PAGE_SZ + 1) as usize] == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s2.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1,
            s2.slot_holds(process, WITNESS_FRAME_SLOT, (base + 2 * PAGE_SZ + 3) as usize, notification_of(base)),
            s2.is_cap((base + 2 * PAGE_SZ + 3) as usize),
            s2.list.nodes@[(base + 2 * PAGE_SZ + 3) as int].depth == 2,
            s2.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT),
            s2.notification_at(process, WITNESS_FRAME_SLOT) == base,
            s2.slot_holds(
                process,
                WITNESS_BADGED_SLOT,
                (base + 2 * PAGE_SZ + 2) as usize,
                s2.payload_of((base + 2 * PAGE_SZ + 2) as usize),
            ),
            s2.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT),
            s2.notification_at(process, WITNESS_BADGED_SLOT) == base,
            s2.payload_of((base + 2 * PAGE_SZ + 2) as usize).badge == 0x4000_0000_0000_0000, // not a page size: bit 62 of the word
            s2.endpoints.records@.contains_key(base),
            s2.endpoints.records@[base].value() == fresh_record(),
            s2.blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            block_ref(&s2.blocks, base / PAGE_SZ) == BlockRef::Small(base / PAGE_SZ),
            s2.caller_live(0, process),
            witness_empty(s2, process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize),
            witness_empty(s2, process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize),
            witness_empty(s2, p2, WITNESS_CHILD_SLOT, (b3 + 1) as usize),
            forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> {
                &&& (#[trigger] s2.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                &&& s2.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                &&& s2.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
            },
            forall|x: int| 0 <= x < s2.blocks.num_2m()
                ==> (#[trigger] s2.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed,
            forall|x: int| 0 <= x < s2.blocks.num_1g()
                ==> (#[trigger] s2.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed,
        ensures
            s3.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            s3.wf(),
            s3.tables.roots@.contains_key(process),
            s3.root_live(process),
            s3.caller_live(0, process),
            s3.flush_epoch == 0,
            s3.cores@[0].current_thread == Some(t),
            s3.cores@[0].generation == 1,
            s3.loaded(0, process),
            s3.spaces.kernel_root@ == kernel_root,
            kernel_root % PAGE_SZ == 0,
            crate::util::page_ptr_util_u::mem_valid(kernel_root),
            s3.threads.queues.all_empty(),
            s3.threads.records@.contains_key(t),
            s3.threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            s3.threads.records@[t].value().process == Some(process),
            !s3.threads.records@[t].value().dying,
            !s3.threads.records@[t].value().pending_stop,
            s3.threads.records@[t].value().queued != base,
            s3.processes.records@.contains_key(process),
            !s3.processes.records@[process].value().dead,
            ({
                let bt1 = (b3 + 2 * PAGE_SZ) as usize;
                let bt2 = (b3 + 4 * PAGE_SZ) as usize;
                let u = (leaf + ROOT_UNTYPED_SLOT) as usize;
                let np2 = (base + 2 * PAGE_SZ + 1) as usize;
                let core0 = (leaf + ROOT_CORE_SLOT) as usize;
                &&& b3 + 6 * PAGE_SZ <= NODE_SPACE
                &&& s3.blocks.tracks_addr_run(bt1, 2)
                &&& s3.blocks.tracks_addr_run(bt2, 2)
                &&& p2 != process
                &&& s3.root_untyped(process) == u
                &&& s3.slot_holds(process, ROOT_UNTYPED_SLOT, u, first)
                &&& s3.list.nodes@[u as int].live
                &&& s3.list.nodes@[u as int].depth == 1
                &&& s3.slot_holds(process, ROOT_CORE_SLOT, core0, core_payload(0, MAX_PRIORITY))
                &&& s3.list.nodes@[core0 as int].depth == 1
                &&& s3.tables.leaf(process, 0) == leaf
                &&& leaf + LEAF_BYTES <= NODE_SPACE
                &&& s3.tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize
                &&& s3.slot_holds(process, WITNESS_PROCESS_SLOT, np2, process_of(p2))
                &&& s3.list.nodes@[np2 as int].depth == 2
                &&& s3.list.parent@[np2] == u
                &&& !s3.cap_dead(np2)
                &&& s3.processes.records@.contains_key(p2)
                &&& !s3.processes.records@[p2].value().dead
                &&& s3.tables.roots@.contains_key(p2)
                &&& s3.tables.leaf(p2, 0) == b3
                &&& s3.spaces.roots@.contains_key(process)
                &&& s3.spaces.roots@.contains_key(p2)
                &&& s3.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1
                &&& s3.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT)
                &&& s3.notification_at(process, WITNESS_FRAME_SLOT) == base
                &&& s3.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT)
                &&& s3.notification_at(process, WITNESS_BADGED_SLOT) == base
                &&& s3.payload_of(s3.tables.node_of(process, WITNESS_BADGED_SLOT)).badge
                    == 0x4000_0000_0000_0000 // not a page size: bit 62 of the word
                &&& s3.holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT)
                &&& s3.notification_at(p2, WITNESS_CHILD_SLOT) == base
                &&& s3.caller_live(0, p2) == (s3.cores@[0].current_thread is Some
                    && s3.threads.records@[s3.cores@[0].current_thread->Some_0].value().process == Some(p2)
                    && s3.root_live(p2))
                &&& s3.root_live(p2)
                &&& s3.endpoints.records@.contains_key(base)
                &&& s3.endpoints.records@[base].value() == fresh_record()
                &&& s3.blocks.pages@[(base / PAGE_SZ) as int].object is Notification
                &&& witness_empty(s3, process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize)
                &&& witness_empty(s3, process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize)
                &&& s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER)
                &&& s3.blocks.small_free((bt1 / PAGE_SZ) as int, THREAD_ORDER as usize)
                &&& bt1 % THREAD_BYTES == 0
                &&& bt1 / PAGE_SZ == b3 / PAGE_SZ + 2
                &&& !s3.threads.records@.contains_key(bt1)
                &&& s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bt2, THREAD_ORDER)
                &&& s3.blocks.small_free((bt2 / PAGE_SZ) as int, THREAD_ORDER as usize)
                &&& bt2 % THREAD_BYTES == 0
                &&& bt2 / PAGE_SZ == b3 / PAGE_SZ + 4
                &&& !s3.threads.records@.contains_key(bt2)
                &&& s3.stale_epoch == pre_boot.stale_epoch
                &&& forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8
                    ==> s3.stale_epoch.pages@[j] == 0
                &&& forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> {
                    &&& (#[trigger] s3.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                    &&& s3.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                    &&& s3.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
                }
                &&& forall|x: int| 0 <= x < s3.blocks.num_2m()
                    ==> (#[trigger] s3.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed
                &&& forall|x: int| 0 <= x < s3.blocks.num_1g()
                    ==> (#[trigger] s3.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed
            }),
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost u = (leaf + ROOT_UNTYPED_SLOT) as usize;
        let ghost core0 = (leaf + ROOT_CORE_SLOT) as usize;
        let ghost lb = (base + 2 * PAGE_SZ) as usize;
        let ghost np2 = (lb + 1) as usize;
        let ghost ne = (lb + 3) as usize;
        let ghost nc = (b3 + 1) as usize;
        assert(s3.slot_holds(p2, WITNESS_CHILD_SLOT, nc, child_of(notification_of(base), RECEIVE_RIGHT, base, 0)));
        assert(right_bit(Right::Receive) == RECEIVE_RIGHT) by (compute_only);
        assert((RECEIVE_RIGHT & RECEIVE_RIGHT) != 0) by (compute_only);
        assert(s3.holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT));
        assert(s3.notification_at(p2, WITNESS_CHILD_SLOT) == base);
        assert(s3.root_live(p2));
        assert(s3.spaces.roots@.contains_key(process)) by {
            reveal(CapKernel::wf);
        }
        assert(s3.spaces.roots@.contains_key(p2)) by {
            reveal(CapKernel::wf);
        }
        assert(p2 != process) by {
            assert(s3.tables.leaf(process, 2) == lb);
            assert(s3.tables.leaf(p2, 2) == NO_LEAF);
        }
        Self::lemma_caps_frame(s2, s3, nc, nc, u);
        Self::lemma_caps_frame(s2, s3, nc, nc, core0);
        Self::lemma_caps_frame(s2, s3, nc, nc, np2);
        Self::lemma_setup_waiter_depth(s2, s3, nc, ne, u);
        Self::lemma_setup_waiter_depth(s2, s3, nc, ne, core0);
        assert(s3.list.nodes@[np2 as int].depth == 2 && s3.list.parent@[np2] == u && !s3.cap_dead(np2)) by {
            reveal(CapKernel::wf);
            assert(has(s3.list.seq@, np2));
            crate::capability::list::lemma_has(s3.list.seq@, np2);
            assert(s3.list.seq@[0] == s2.list.seq@[0]);
            assert(s3.list.is_child(u, np2));
            lemma_child_depth(s3.list, u, np2);
        }
        assert(s3.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
        assert(s3.slot_holds(process, ROOT_CORE_SLOT, core0, core_payload(0, MAX_PRIORITY)));
        assert(s3.slot_holds(process, WITNESS_PROCESS_SLOT, np2, process_of(p2)));
        assert(s3.processes.records@.contains_key(p2) && !s3.processes.records@[p2].value().dead);
        assert(s3.tables.roots@.contains_key(p2) && s3.tables.leaf(p2, 0) == b3);
        assert(base / PAGE_SZ != p2 / PAGE_SZ) by {
            assert(PROCESS_BYTES == 8 * PAGE_SZ);
        }
        assert(s3.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1) by {
            reveal(CapKernel::wf);
            assert(block_ref(&s2.blocks, base / PAGE_SZ) == BlockRef::Small(base / PAGE_SZ));
            assert(block_typed(&s2.blocks, BlockRef::Small(p2 / PAGE_SZ)));
            assert(block_refs(&s3.blocks, BlockRef::Small(p2 / PAGE_SZ))
                == block_refs(&s2.blocks, BlockRef::Small(p2 / PAGE_SZ)));
        }
        assert(s3.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT));
        assert(s3.notification_at(process, WITNESS_FRAME_SLOT) == base);
        assert(s3.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT));
        assert(s3.notification_at(process, WITNESS_BADGED_SLOT) == base);
        assert(s3.payload_of(s3.tables.node_of(process, WITNESS_BADGED_SLOT)).badge == 0x4000_0000_0000_0000); // not a page size: bit 62 of the word
        assert(s3.endpoints.records == s2.endpoints.records);
        assert(s3.blocks.pages@[(base / PAGE_SZ) as int].object == s2.blocks.pages@[(base / PAGE_SZ) as int].object);
        assert(s3.endpoints.records@.contains_key(base)
            && s3.endpoints.records@[base].value() == fresh_record()
            && s3.blocks.pages@[(base / PAGE_SZ) as int].object is Notification);
        Self::lemma_caps_frame(s2, s3, nc, nc, ne);
        Self::lemma_caps_frame(s2, s3, nc, nc, (lb + 2) as usize);
        assert(witness_empty(s3, process, WITNESS_STALE_THREAD_SLOT, (lb + 4) as usize));
        assert(witness_empty(s3, process, WITNESS_LIVE_THREAD_SLOT, (lb + 5) as usize));
        assert(s3.cores@[0].space == Some(process)) by {
            reveal(CapKernel::wf);
            reveal(current_wf);
            assert(runs(s3.cores@, 0, t));
            assert(runs_in_space(s3.cores@, s3.threads.records@, 0, t));
        }
        s3.lemma_named_depends(0, process);
        assert(s3.threads.records == s2.threads.records && s3.threads.queues == s2.threads.queues);
        assert(s3.caller_live(0, process));
        assert(s3.threads.records@[t].value().queued != base);
        assert(order_pages(3) == 8) by (compute_only);
        assert(witness_block(pre_boot, b3, first));
        assert(pre_boot.blocks.tracks((b3 / PAGE_SZ + 7) as int));
        Self::lemma_setup_waiter_stale_zero(pre_boot, s3, b3);
        assert forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 implies {
            &&& s3.stale_epoch.pages@[j] == 0
            &&& (#[trigger] s3.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
            &&& s3.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
            &&& s3.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
        } by {}
        assert forall|x: int| 0 <= x < s3.blocks.num_2m()
            implies (#[trigger] s3.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed by {}
        assert forall|x: int| 0 <= x < s3.blocks.num_1g()
            implies (#[trigger] s3.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed by {}
        assert(s3.root_untyped(process) == u);
        assert(s3.tables.leaf(process, 0) == leaf);
        assert(s3.blocks.tracks_addr_run(b3, 8));
        Self::lemma_setup_waiter_bt(pre_boot, s3, process, leaf, first, base, b3);
        assert(s3.caller_live(0, p2) == (s3.cores@[0].current_thread is Some
            && s3.threads.records@[s3.cores@[0].current_thread->Some_0].value().process == Some(p2)
            && s3.root_live(p2)));
        assert(s3.stale_epoch == pre_boot.stale_epoch);
    }

    /// Helper for `witness_setup_waiter_process`: proves `retype_process` preserves existing caps,
    /// frames `s1`, and sets up preconditions for `lemma_setup_waiter_s2`.
    #[verifier::spinoff_prover]
    proof fn lemma_setup_waiter_s1(
        pre_boot: Self,
        s0: Self,
        s1: Self,
        process: usize,
        p2: usize,
        leaf: usize,
        first: Payload,
        base: usize,
        b3: usize,
        t: usize,
        kernel_root: usize,
    )
        requires
            pre_boot.wf(),
            pre_boot.flush_epoch == 0,
            s0.wf(),
            s1.wf(),
            s0.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            s1.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            base % PROCESS_BYTES == 0,
            base % PAGE_SZ == 0,
            base + 3 * PROCESS_BYTES <= NODE_SPACE,
            p2 == (base + PROCESS_BYTES) as usize,
            b3 == (base + 2 * PROCESS_BYTES) as usize,
            b3 % PAGE_SZ == 0,
            leaf % PAGE_SZ == 0,
            leaf + LEAF_BYTES <= NODE_SPACE,
            (base + 2 * PAGE_SZ) as usize != leaf,
            witness_block(pre_boot, b3, first),
            pre_boot.blocks.tracks((b3 / PAGE_SZ + 7) as int),
            first.kind is Untyped,
            first.rights == UNTYPED_RIGHTS,
            Self::process_retype_answered(s0, s1, process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2, true),
            Self::process_retype_kept(s0, s1),
            Self::process_retype_done(s0, s1, process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2),
            Self::process_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2),
            s0.blocks.tracks_addr_run(b3, 8),
            s0.stale_epoch == pre_boot.stale_epoch,
            s0.flush_epoch == 0,
            s0.cores@[0].current_thread == Some(t),
            s0.cores@[0].generation == 1,
            s0.caller_live(0, process),
            s0.spaces.kernel_root@ == kernel_root,
            kernel_root % PAGE_SZ == 0,
            crate::util::page_ptr_util_u::mem_valid(kernel_root),
            s0.threads.queues.all_empty(),
            s0.threads.records@.contains_key(t),
            s0.threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            s0.threads.records@[t].value().process == Some(process),
            !s0.threads.records@[t].value().dying,
            !s0.threads.records@[t].value().pending_stop,
            s0.threads.records@[t].value().queued != base,
            s0.processes.records@.contains_key(process),
            !s0.processes.records@[process].value().dead,
            s0.tables.roots@.contains_key(process),
            s0.root_live(process),
            s0.root_untyped(process) == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s0.tables.leaf(process, 0) == leaf,
            s0.tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            s0.slot_holds(process, ROOT_UNTYPED_SLOT, (leaf + ROOT_UNTYPED_SLOT) as usize, first),
            s0.slot_holds(process, ROOT_CORE_SLOT, (leaf + ROOT_CORE_SLOT) as usize, core_payload(0, MAX_PRIORITY)),
            s0.is_cap((leaf + ROOT_UNTYPED_SLOT) as usize),
            s0.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].live,
            s0.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].depth == 1,
            s0.is_cap((leaf + ROOT_CORE_SLOT) as usize),
            s0.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].live,
            s0.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].depth == 1,
            s0.slot_holds(process, WITNESS_FRAME_SLOT, (base + 2 * PAGE_SZ + 3) as usize, notification_of(base)),
            s0.is_cap((base + 2 * PAGE_SZ + 3) as usize),
            s0.list.nodes@[(base + 2 * PAGE_SZ + 3) as int].depth == 2,
            s0.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT),
            s0.notification_at(process, WITNESS_FRAME_SLOT) == base,
            s0.slot_holds(
                process,
                WITNESS_BADGED_SLOT,
                (base + 2 * PAGE_SZ + 2) as usize,
                s0.payload_of((base + 2 * PAGE_SZ + 2) as usize),
            ),
            s0.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT),
            s0.notification_at(process, WITNESS_BADGED_SLOT) == base,
            s0.payload_of((base + 2 * PAGE_SZ + 2) as usize).badge == 0x4000_0000_0000_0000, // not a page size: bit 62 of the word
            s0.endpoints.records@.contains_key(base),
            s0.endpoints.records@[base].value() == fresh_record(),
            s0.blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            s0.blocks.pages@[(base / PAGE_SZ) as int].refs == 2,
            block_refs(&s0.blocks, BlockRef::Small(base / PAGE_SZ)) == 2,
            witness_empty(s0, process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize),
            witness_empty(s0, process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize),
            forall|j: int| b3 / PAGE_SZ <= j < b3 / PAGE_SZ + 8 ==> {
                &&& (#[trigger] s0.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                &&& s0.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                &&& s0.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
            },
            forall|x: int| 0 <= x < s0.blocks.num_2m()
                ==> (#[trigger] s0.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed,
            forall|x: int| 0 <= x < s0.blocks.num_1g()
                ==> (#[trigger] s0.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed,
        ensures
            s1.blocks.tracks_addr_run(b3, 8),
            s1.stale_epoch == pre_boot.stale_epoch,
            s1.flush_epoch == 0,
            s1.cores@[0].current_thread == Some(t),
            s1.cores@[0].generation == 1,
            s1.caller_live(0, process),
            s1.spaces.kernel_root@ == kernel_root,
            s1.threads.queues.all_empty(),
            s1.threads.records@.contains_key(t),
            s1.threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            s1.threads.records@[t].value().process == Some(process),
            !s1.threads.records@[t].value().dying,
            !s1.threads.records@[t].value().pending_stop,
            s1.threads.records@[t].value().queued != base,
            s1.processes.records@.contains_key(process),
            !s1.processes.records@[process].value().dead,
            s1.processes.records@.contains_key(p2),
            !s1.processes.records@[p2].value().dead,
            s1.tables.roots@.contains_key(process),
            s1.root_live(process),
            s1.root_untyped(process) == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s1.tables.leaf(process, 0) == leaf,
            s1.tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            s1.tables.roots@.contains_key(p2),
            s1.tables.leaf(p2, 0) == NO_LEAF,
            s1.tables.leaf(p2, 2) == NO_LEAF,
            s1.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(p2),
            s1.slot_holds(process, ROOT_UNTYPED_SLOT, (leaf + ROOT_UNTYPED_SLOT) as usize, first),
            s1.slot_holds(process, ROOT_CORE_SLOT, (leaf + ROOT_CORE_SLOT) as usize, core_payload(0, MAX_PRIORITY)),
            s1.is_cap((leaf + ROOT_UNTYPED_SLOT) as usize),
            s1.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].live,
            s1.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].depth == 1,
            s1.is_cap((leaf + ROOT_CORE_SLOT) as usize),
            s1.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].live,
            s1.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].depth == 1,
            s1.slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            s1.is_cap((base + 2 * PAGE_SZ + 1) as usize),
            s1.list.nodes@[(base + 2 * PAGE_SZ + 1) as int].depth == 2,
            s1.list.parent@[(base + 2 * PAGE_SZ + 1) as usize] == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s1.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1,
            s1.slot_holds(process, WITNESS_FRAME_SLOT, (base + 2 * PAGE_SZ + 3) as usize, notification_of(base)),
            s1.is_cap((base + 2 * PAGE_SZ + 3) as usize),
            s1.list.nodes@[(base + 2 * PAGE_SZ + 3) as int].depth == 2,
            s1.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT),
            s1.notification_at(process, WITNESS_FRAME_SLOT) == base,
            s1.slot_holds(
                process,
                WITNESS_BADGED_SLOT,
                (base + 2 * PAGE_SZ + 2) as usize,
                s1.payload_of((base + 2 * PAGE_SZ + 2) as usize),
            ),
            s1.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT),
            s1.notification_at(process, WITNESS_BADGED_SLOT) == base,
            s1.payload_of((base + 2 * PAGE_SZ + 2) as usize).badge == 0x4000_0000_0000_0000, // not a page size: bit 62 of the word
            s1.endpoints.records@.contains_key(base),
            s1.endpoints.records@[base].value() == fresh_record(),
            s1.blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            s1.blocks.pages@[(base / PAGE_SZ) as int].refs == 2,
            block_refs(&s1.blocks, BlockRef::Small(base / PAGE_SZ)) == 2,
            witness_empty(s1, process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize),
            witness_empty(s1, process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize),
            forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> {
                &&& (#[trigger] s1.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                &&& s1.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                &&& s1.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
            },
            forall|x: int| 0 <= x < s1.blocks.num_2m()
                ==> (#[trigger] s1.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed,
            forall|x: int| 0 <= x < s1.blocks.num_1g()
                ==> (#[trigger] s1.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed,
            s1.can_retype_leaf(process, ROOT_UNTYPED_SLOT, Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 }, b3),
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost u = (leaf + ROOT_UNTYPED_SLOT) as usize;
        let ghost core0 = (leaf + ROOT_CORE_SLOT) as usize;
        let ghost lb = (base + 2 * PAGE_SZ) as usize;
        let ghost np2 = (lb + 1) as usize;
        let ghost ne = (lb + 3) as usize;
        assert(Self::retype_keeps(s0, s1, np2, (p2 / PAGE_SZ) as int, 3, None));
        Self::lemma_caps_frame(s0, s1, np2, np2, u);
        Self::lemma_caps_frame(s0, s1, np2, np2, core0);
        Self::lemma_caps_frame(s0, s1, np2, np2, ne);
        Self::lemma_caps_frame(s0, s1, np2, np2, (lb + 2) as usize);
        assert(s1.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
        assert(s1.slot_holds(process, ROOT_CORE_SLOT, core0, core_payload(0, MAX_PRIORITY)));
        assert(s1.is_cap(u) && s1.list.nodes@[u as int].live && s1.list.nodes@[u as int].depth == 1);
        assert(s1.is_cap(core0) && s1.list.nodes@[core0 as int].live && s1.list.nodes@[core0 as int].depth == 1);
        assert(s1.endpoints.records == s0.endpoints.records);
        assert(s1.slot_holds(process, WITNESS_FRAME_SLOT, ne, notification_of(base)));
        assert(s1.slot_holds(process, WITNESS_BADGED_SLOT, (lb + 2) as usize, s0.payload_of((lb + 2) as usize)));
        assert(s1.slot_holds(process, WITNESS_PROCESS_SLOT, np2, process_of(p2)));
        assert(s1.list.nodes@[np2 as int].depth == 2);
        assert(s1.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1);
        assert(s1.tables.roots@.contains_key(p2));
        assert(s1.tables.leaf(p2, 0) == NO_LEAF);
        assert(s1.tables.leaf(p2, 2) == NO_LEAF);
        assert(s1.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(p2));
        assert(PROCESS_BYTES == 8 * PAGE_SZ);
        assert(base / PAGE_SZ + 8 == p2 / PAGE_SZ && p2 / PAGE_SZ + 8 == b3 / PAGE_SZ) by (nonlinear_arith)
            requires
                PROCESS_BYTES == 8 * PAGE_SZ,
                PAGE_SZ > 0,
                base % PROCESS_BYTES == 0,
                p2 == base + PROCESS_BYTES,
                b3 == base + 2 * PROCESS_BYTES;
        assert(!s1.blocks.covered((b3 / PAGE_SZ) as int)) by {
            reveal(CapKernel::wf);
            assert(s1.blocks.tracks((b3 / PAGE_SZ) as int));
            assert(0 <= region_2m((b3 / PAGE_SZ) as int) < s1.blocks.num_2m());
            assert(0 <= region_1g((b3 / PAGE_SZ) as int) < s1.blocks.num_1g());
            assert(s0.blocks.num_2m() == s1.blocks.num_2m());
            assert(s0.blocks.num_1g() == s1.blocks.num_1g());
            assert(!pre_boot.blocks.covered((b3 / PAGE_SZ) as int));
        }
        assert(s1.blocks.small_free((b3 / PAGE_SZ) as int, 1)) by {
            assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s1.blocks.pages@[b3 / PAGE_SZ + k].kind is Free by {
                assert(pre_boot.blocks.pages@[b3 / PAGE_SZ + k].kind is Free);
            }
        }
        lemma2_to64();
        assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
        assert(1usize < MAX_DEPTH) by (compute_only);
        assert(block_bytes(1) == 2 * PAGE_SZ);
        assert(block_bytes(3) == 8 * PAGE_SZ);
        assert(block_bytes(1) == THREAD_BYTES);
        assert(b3 % THREAD_BYTES == 0) by (nonlinear_arith)
            requires
                THREAD_BYTES == 2 * PAGE_SZ,
                PROCESS_BYTES == 8 * PAGE_SZ,
                PAGE_SZ > 0,
                b3 % PROCESS_BYTES == 0;
        assert(block_within(b3, 1, first));
        assert(s1.blocks.tracks_addr_run(b3, 8));
        assert(s1.blocks.tracks_addr_run(b3, 2));
        assert(s1.tables.leaf(p2, 0) == NO_LEAF);
        assert(b3 != NO_LEAF);
        assert(s1.can_retype_leaf(process, ROOT_UNTYPED_SLOT, Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 }, b3));
        assert(s1.is_cap(ne));
        assert(s1.list.nodes@[ne as int].depth == 2);
        assert(s1.list.parent@[np2] == u);
        assert(s1.root_untyped(process) == u);
        assert(s1.tables.leaf(process, 0) == leaf);
        assert(s1.tables.leaf(process, 2) == lb);
        assert(s1.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT));
        assert(s1.notification_at(process, WITNESS_FRAME_SLOT) == base);
        assert(s1.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT));
        assert(s1.notification_at(process, WITNESS_BADGED_SLOT) == base);
        assert(s1.payload_of((lb + 2) as usize).badge == 0x4000_0000_0000_0000); // not a page size: bit 62 of the word
        assert(s1.blocks.pages@[(base / PAGE_SZ) as int] == s0.blocks.pages@[(base / PAGE_SZ) as int]);
        assert(s1.blocks.pages@[(base / PAGE_SZ) as int].refs == 2);
        assert(s1.blocks.pages@[(base / PAGE_SZ) as int].object is Notification);
        assert(block_refs(&s1.blocks, BlockRef::Small(base / PAGE_SZ)) == 2) by {
            reveal(CapKernel::wf);
        }
        assert(witness_empty(s1, process, WITNESS_STALE_THREAD_SLOT, (lb + 4) as usize));
        assert(witness_empty(s1, process, WITNESS_LIVE_THREAD_SLOT, (lb + 5) as usize));
        assert(s1.threads == s0.threads);
        assert(s1.stale_epoch == pre_boot.stale_epoch);
        assert(s1.caller_live(0, process));
        assert(order_pages(3) == 8) by (compute_only);
        assert forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 implies {
            &&& (#[trigger] s1.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
            &&& s1.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
            &&& s1.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
        } by {}
        assert forall|x: int| 0 <= x < s1.blocks.num_2m()
            implies (#[trigger] s1.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed by {}
        assert forall|x: int| 0 <= x < s1.blocks.num_1g()
            implies (#[trigger] s1.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed by {}
        assert(s1.blocks.tracks_addr_run(b3, 8));
    }

    /// Helper for `lemma_setup_waiter_s2`: proves `s2.loaded(0, process)` and `base` block
    /// refcount in an isolated context with `CapKernel::wf` revealed only here.
    #[verifier::spinoff_prover]
    proof fn lemma_setup_waiter_s2_loaded(s2: Self, process: usize, t: usize, base: usize)
        requires
            s2.wf(),
            s2.cores@[0].current_thread == Some(t),
            s2.threads.records@.contains_key(t),
            s2.threads.records@[t].value().process == Some(process),
            s2.caller_live(0, process),
            s2.blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            s2.blocks.pages@[(base / PAGE_SZ) as int].refs == 2,
            s2.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT),
            s2.notification_at(process, WITNESS_FRAME_SLOT) == base,
        ensures
            s2.loaded(0, process),
            block_ref(&s2.blocks, base / PAGE_SZ) == BlockRef::Small(base / PAGE_SZ),
            block_refs(&s2.blocks, BlockRef::Small(base / PAGE_SZ)) == 2,
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        assert(block_ref(&s2.blocks, base / PAGE_SZ) == BlockRef::Small(base / PAGE_SZ)
            && block_refs(&s2.blocks, BlockRef::Small(base / PAGE_SZ)) == 2) by {
            reveal(CapKernel::wf);
            reveal(BlockTable::counts_wf);
            s2.lemma_slot(process, WITNESS_FRAME_SLOT);
            let n = s2.tables.node_of(process, WITNESS_FRAME_SLOT);
            assert(s2.is_cap(n));
            assert(endpoint_wf(&s2.endpoints, &s2.blocks, base));
            s2.blocks.lemma_not_free_uncovered((base / PAGE_SZ) as int);
        }
        assert(s2.cores@[0].space == Some(process)) by {
            reveal(CapKernel::wf);
            reveal(current_wf);
            assert(runs(s2.cores@, 0, t));
            assert(runs_in_space(s2.cores@, s2.threads.records@, 0, t));
        }
        s2.lemma_named_depends(0, process);
    }

    /// Helper for `witness_setup_waiter_process`: proves `retype_leaf` preserves waiter slots,
    /// `s2.caller_live(0, process)`, and `s2.can_derive_at(...)` for `WITNESS_CHILD_SLOT`.
    #[verifier::spinoff_prover]
    proof fn lemma_setup_waiter_s2(
        pre_boot: Self,
        s1: Self,
        s2: Self,
        process: usize,
        p2: usize,
        leaf: usize,
        first: Payload,
        base: usize,
        b3: usize,
        t: usize,
        kernel_root: usize,
    )
        requires
            s1.wf(),
            s2.wf(),
            s1.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            s2.blocks.pages@.len() == pre_boot.blocks.pages@.len(),
            base % PROCESS_BYTES == 0,
            base % PAGE_SZ == 0,
            base + 3 * PROCESS_BYTES <= NODE_SPACE,
            p2 == (base + PROCESS_BYTES) as usize,
            b3 == (base + 2 * PROCESS_BYTES) as usize,
            b3 % PAGE_SZ == 0,
            leaf % PAGE_SZ == 0,
            leaf + LEAF_BYTES <= NODE_SPACE,
            (base + 2 * PAGE_SZ) as usize != leaf,
            first.kind is Untyped,
            first.rights == UNTYPED_RIGHTS,
            Self::leaf_retyped(
                s1,
                s2,
                process,
                ROOT_UNTYPED_SLOT,
                Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 },
                b3,
            ),
            Self::leaf_retype_spared(s1, s2, b3),
            Self::leaf_retype_kept(s1, s2),
            Self::same_tree(s1, s2),
            s1.blocks.tracks_addr_run(b3, 8),
            s1.stale_epoch == pre_boot.stale_epoch,
            s1.flush_epoch == 0,
            s1.cores@[0].current_thread == Some(t),
            s1.cores@[0].generation == 1,
            s1.caller_live(0, process),
            s1.spaces.kernel_root@ == kernel_root,
            kernel_root % PAGE_SZ == 0,
            crate::util::page_ptr_util_u::mem_valid(kernel_root),
            s1.threads.queues.all_empty(),
            s1.threads.records@.contains_key(t),
            s1.threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            s1.threads.records@[t].value().process == Some(process),
            !s1.threads.records@[t].value().dying,
            !s1.threads.records@[t].value().pending_stop,
            s1.threads.records@[t].value().queued != base,
            s1.processes.records@.contains_key(process),
            !s1.processes.records@[process].value().dead,
            s1.processes.records@.contains_key(p2),
            !s1.processes.records@[p2].value().dead,
            s1.tables.roots@.contains_key(process),
            s1.root_live(process),
            s1.root_untyped(process) == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s1.tables.leaf(process, 0) == leaf,
            s1.tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            s1.tables.roots@.contains_key(p2),
            s1.tables.leaf(p2, 0) == NO_LEAF,
            s1.tables.leaf(p2, 2) == NO_LEAF,
            s1.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(p2),
            s1.slot_holds(process, ROOT_UNTYPED_SLOT, (leaf + ROOT_UNTYPED_SLOT) as usize, first),
            s1.slot_holds(process, ROOT_CORE_SLOT, (leaf + ROOT_CORE_SLOT) as usize, core_payload(0, MAX_PRIORITY)),
            s1.is_cap((leaf + ROOT_UNTYPED_SLOT) as usize),
            s1.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].live,
            s1.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].depth == 1,
            s1.is_cap((leaf + ROOT_CORE_SLOT) as usize),
            s1.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].live,
            s1.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].depth == 1,
            s1.slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            s1.is_cap((base + 2 * PAGE_SZ + 1) as usize),
            s1.list.nodes@[(base + 2 * PAGE_SZ + 1) as int].depth == 2,
            s1.list.parent@[(base + 2 * PAGE_SZ + 1) as usize] == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s1.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1,
            s1.slot_holds(process, WITNESS_FRAME_SLOT, (base + 2 * PAGE_SZ + 3) as usize, notification_of(base)),
            s1.is_cap((base + 2 * PAGE_SZ + 3) as usize),
            s1.list.nodes@[(base + 2 * PAGE_SZ + 3) as int].depth == 2,
            s1.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT),
            s1.notification_at(process, WITNESS_FRAME_SLOT) == base,
            s1.slot_holds(
                process,
                WITNESS_BADGED_SLOT,
                (base + 2 * PAGE_SZ + 2) as usize,
                s1.payload_of((base + 2 * PAGE_SZ + 2) as usize),
            ),
            s1.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT),
            s1.notification_at(process, WITNESS_BADGED_SLOT) == base,
            s1.payload_of((base + 2 * PAGE_SZ + 2) as usize).badge == 0x4000_0000_0000_0000, // not a page size: bit 62 of the word
            s1.endpoints.records@.contains_key(base),
            s1.endpoints.records@[base].value() == fresh_record(),
            s1.blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            s1.blocks.pages@[(base / PAGE_SZ) as int].refs == 2,
            block_refs(&s1.blocks, BlockRef::Small(base / PAGE_SZ)) == 2,
            witness_empty(s1, process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize),
            witness_empty(s1, process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize),
            forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> {
                &&& (#[trigger] s1.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                &&& s1.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                &&& s1.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
            },
            forall|x: int| 0 <= x < s1.blocks.num_2m()
                ==> (#[trigger] s1.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed,
            forall|x: int| 0 <= x < s1.blocks.num_1g()
                ==> (#[trigger] s1.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed,
        ensures
            s2.blocks.tracks_addr_run(b3, 8),
            s2.stale_epoch == pre_boot.stale_epoch,
            s2.flush_epoch == 0,
            s2.cores@[0].current_thread == Some(t),
            s2.cores@[0].generation == 1,
            s2.loaded(0, process),
            s2.caller_live(0, process),
            s2.spaces.kernel_root@ == kernel_root,
            s2.threads.queues.all_empty(),
            s2.threads.records@.contains_key(t),
            s2.threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            s2.threads.records@[t].value().process == Some(process),
            !s2.threads.records@[t].value().dying,
            !s2.threads.records@[t].value().pending_stop,
            s2.threads.records@[t].value().queued != base,
            s2.processes.records@.contains_key(process),
            !s2.processes.records@[process].value().dead,
            s2.processes.records@.contains_key(p2),
            !s2.processes.records@[p2].value().dead,
            s2.tables.roots@.contains_key(process),
            s2.root_live(process),
            s2.root_untyped(process) == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s2.tables.leaf(process, 0) == leaf,
            s2.tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            s2.tables.roots@.contains_key(p2),
            s2.tables.leaf(p2, 0) == b3,
            s2.tables.leaf(p2, 2) == NO_LEAF,
            s2.slot_holds(process, ROOT_UNTYPED_SLOT, (leaf + ROOT_UNTYPED_SLOT) as usize, first),
            s2.slot_holds(process, ROOT_CORE_SLOT, (leaf + ROOT_CORE_SLOT) as usize, core_payload(0, MAX_PRIORITY)),
            s2.is_cap((leaf + ROOT_UNTYPED_SLOT) as usize),
            s2.list.nodes@[(leaf + ROOT_UNTYPED_SLOT) as int].depth == 1,
            s2.is_cap((leaf + ROOT_CORE_SLOT) as usize),
            s2.list.nodes@[(leaf + ROOT_CORE_SLOT) as int].depth == 1,
            s2.slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            s2.is_cap((base + 2 * PAGE_SZ + 1) as usize),
            s2.list.nodes@[(base + 2 * PAGE_SZ + 1) as int].depth == 2,
            s2.list.parent@[(base + 2 * PAGE_SZ + 1) as usize] == (leaf + ROOT_UNTYPED_SLOT) as usize,
            s2.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1,
            s2.slot_holds(process, WITNESS_FRAME_SLOT, (base + 2 * PAGE_SZ + 3) as usize, notification_of(base)),
            s2.is_cap((base + 2 * PAGE_SZ + 3) as usize),
            s2.list.nodes@[(base + 2 * PAGE_SZ + 3) as int].depth == 2,
            s2.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT),
            s2.notification_at(process, WITNESS_FRAME_SLOT) == base,
            s2.slot_holds(
                process,
                WITNESS_BADGED_SLOT,
                (base + 2 * PAGE_SZ + 2) as usize,
                s2.payload_of((base + 2 * PAGE_SZ + 2) as usize),
            ),
            s2.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT),
            s2.notification_at(process, WITNESS_BADGED_SLOT) == base,
            s2.payload_of((base + 2 * PAGE_SZ + 2) as usize).badge == 0x4000_0000_0000_0000, // not a page size: bit 62 of the word
            s2.endpoints.records@.contains_key(base),
            s2.endpoints.records@[base].value() == fresh_record(),
            s2.blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            block_ref(&s2.blocks, base / PAGE_SZ) == BlockRef::Small(base / PAGE_SZ),
            witness_empty(s2, process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize),
            witness_empty(s2, process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize),
            witness_empty(s2, p2, WITNESS_CHILD_SLOT, (b3 + 1) as usize),
            forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> {
                &&& (#[trigger] s2.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                &&& s2.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                &&& s2.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
            },
            forall|x: int| 0 <= x < s2.blocks.num_2m()
                ==> (#[trigger] s2.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed,
            forall|x: int| 0 <= x < s2.blocks.num_1g()
                ==> (#[trigger] s2.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed,
            s2.can_derive_at(
                process,
                WITNESS_FRAME_SLOT,
                Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT },
                RECEIVE_RIGHT,
                base,
                0,
                0,
            ),
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost u = (leaf + ROOT_UNTYPED_SLOT) as usize;
        let ghost core0 = (leaf + ROOT_CORE_SLOT) as usize;
        let ghost lb = (base + 2 * PAGE_SZ) as usize;
        let ghost np2 = (lb + 1) as usize;
        let ghost ne = (lb + 3) as usize;
        assert(s2.tables.leaf(p2, 0) == b3);
        assert(s2.tables.leaf(p2, 2) == NO_LEAF);
        assert(s2.tables.leaf(process, 2) == lb);
        assert(index_ok(WITNESS_CHILD_SLOT) && index_entry(WITNESS_CHILD_SLOT) == 0
            && index_slot(WITNESS_CHILD_SLOT) == 1) by (compute_only);
        assert(witness_empty(s2, p2, WITNESS_CHILD_SLOT, (b3 + 1) as usize));
        assert(s2.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
        assert(s2.slot_holds(process, ROOT_CORE_SLOT, core0, core_payload(0, MAX_PRIORITY)));
        assert(s2.is_cap(u) && s2.list.nodes@[u as int].live && s2.list.nodes@[u as int].depth == 1);
        assert(s2.is_cap(core0) && s2.list.nodes@[core0 as int].live && s2.list.nodes@[core0 as int].depth == 1);
        s2.lemma_slot_bound(u);
        s2.lemma_slot_bound(core0);
        assert(s2.slot_holds(process, WITNESS_PROCESS_SLOT, np2, process_of(p2)));
        s2.lemma_slot_bound(np2);
        assert(s2.is_cap(np2) && s2.list.nodes@[np2 as int].live && s2.list.nodes@[np2 as int].depth == 2);
        assert(s2.list.parent@[np2] == u);
        assert(PROCESS_BYTES == 8 * PAGE_SZ);
        assert(p2 / PAGE_SZ + 8 == b3 / PAGE_SZ && base / PAGE_SZ + 16 == b3 / PAGE_SZ) by (nonlinear_arith)
            requires
                PROCESS_BYTES == 8 * PAGE_SZ,
                PAGE_SZ > 0,
                base % PROCESS_BYTES == 0,
                p2 == base + PROCESS_BYTES,
                b3 == base + 2 * PROCESS_BYTES;
        assert(s2.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1);
        assert(s2.endpoints.records == s1.endpoints.records);
        assert(s2.slot_holds(process, WITNESS_FRAME_SLOT, ne, notification_of(base)));
        assert(s2.slot_holds(process, WITNESS_BADGED_SLOT, (lb + 2) as usize, s1.payload_of((lb + 2) as usize)));
        assert(NOTIFICATION_RIGHTS == (SEND_RIGHT | RECEIVE_RIGHT)) by (compute_only);
        assert(RECEIVE_RIGHT & !NOTIFICATION_RIGHTS == 0) by (compute_only);
        assert(RECEIVE_RIGHT & right_bit(Right::Control) == 0) by (compute_only);
        assert(2usize < MAX_DEPTH) by (compute_only);
        assert(s1.is_cap(ne));
        assert(s1.list.nodes@[ne as int].depth == 2);
        s1.lemma_slot_bound(ne);
        assert(ne != b3) by {
            assert(PROCESS_BYTES == 8 * PAGE_SZ);
        }
        assert(s2.list.nodes@[ne as int].depth == 2);
        s2.lemma_notification_derive(
            process,
            WITNESS_FRAME_SLOT,
            p2,
            WITNESS_CHILD_SLOT,
            RECEIVE_RIGHT,
            base,
            0,
            0,
        );
        assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
        assert(base / PAGE_SZ != p2 / PAGE_SZ && base / PAGE_SZ != b3 / PAGE_SZ) by {
            assert(PROCESS_BYTES == 8 * PAGE_SZ);
        }
        assert(s2.blocks.pages@[(base / PAGE_SZ) as int] == s1.blocks.pages@[(base / PAGE_SZ) as int]);
        assert(s2.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(p2));
        assert(s2.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT));
        assert(s2.notification_at(process, WITNESS_FRAME_SLOT) == base);
        assert(s2.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT));
        assert(s2.notification_at(process, WITNESS_BADGED_SLOT) == base);
        assert(s2.payload_of((lb + 2) as usize).badge == 0x4000_0000_0000_0000); // not a page size: bit 62 of the word
        assert(s2.endpoints.records@.contains_key(base)
            && s2.endpoints.records@[base].value() == fresh_record()
            && s2.blocks.pages@[(base / PAGE_SZ) as int].object is Notification);
        assert(witness_empty(s2, process, WITNESS_STALE_THREAD_SLOT, (lb + 4) as usize));
        assert(witness_empty(s2, process, WITNESS_LIVE_THREAD_SLOT, (lb + 5) as usize));
        assert(s2.threads == s1.threads);
        assert(order_pages(3) == 8) by (compute_only);
        assert forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 implies {
            &&& (#[trigger] s2.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
            &&& s2.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
            &&& s2.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
        } by {}
        assert forall|x: int| 0 <= x < s2.blocks.num_2m()
            implies (#[trigger] s2.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed by {}
        assert forall|x: int| 0 <= x < s2.blocks.num_1g()
            implies (#[trigger] s2.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed by {}
        assert(s2.stale_epoch == pre_boot.stale_epoch);
        assert(s2.blocks.tracks_addr_run(b3, 8));
        Self::lemma_setup_waiter_s2_loaded(s2, process, t, base);
        assert(s2.caller_live(0, process));
        assert(s2.can_derive_at(
            process,
            WITNESS_FRAME_SLOT,
            Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT },
            RECEIVE_RIGHT,
            base,
            0,
            0,
        ));
    }

    /// Extends `witness_setup_badged_notification` by retyping a child process `p2` at
    /// `base + PROCESS_BYTES` (slot `WITNESS_PROCESS_SLOT`), a leaf for `p2` at
    /// `base + 2 * PROCESS_BYTES`, and deriving a notification receive capability into
    /// `p2`'s `WITNESS_CHILD_SLOT`. Leaves two 2-page thread slots (`+2` and `+4` pages inside the
    /// third block) free for `witness_spawn_placed_waiter`.
    #[verifier::spinoff_prover]
    fn witness_setup_waiter_process(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: usize,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        kernel_root: usize,
        base: usize,
        report: Processor,
    )
        requires
            old(self).booted(root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@, kernel_root),
            image_tables_bound(image@) + 3 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            report_tags_tlb(0, report),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            final(self).tables.roots@.contains_key(process),
            final(self).root_live(process),
            final(self).caller_live(0, process),
            final(self).flush_epoch == 0,
            final(self).cores@[0].current_thread == Some(t),
            final(self).cores@[0].generation == 1,
            final(self).loaded(0, process),
            final(self).spaces.kernel_root@ == kernel_root,
            kernel_root % PAGE_SZ == 0,
            crate::util::page_ptr_util_u::mem_valid(kernel_root),
            final(self).threads.queues.all_empty(),
            final(self).threads.records@.contains_key(t),
            final(self).threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            final(self).threads.records@[t].value().process == Some(process),
            !final(self).threads.records@[t].value().dying,
            !final(self).threads.records@[t].value().pending_stop,
            final(self).threads.records@[t].value().queued != base,
            final(self).processes.records@.contains_key(process),
            !final(self).processes.records@[process].value().dead,
            ({
                let first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
                let p2 = (base + PROCESS_BYTES) as usize;
                let b3 = (base + 2 * PROCESS_BYTES) as usize;
                let bt1 = (b3 + 2 * PAGE_SZ) as usize;
                let bt2 = (b3 + 4 * PAGE_SZ) as usize;
                let u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
                let np2 = (base + 2 * PAGE_SZ + 1) as usize;
                let core0 = (leaf@ + ROOT_CORE_SLOT) as usize;
                &&& base % PROCESS_BYTES == 0
                &&& base % PAGE_SZ == 0
                &&& base + 3 * PROCESS_BYTES <= NODE_SPACE
                &&& b3 + 6 * PAGE_SZ <= NODE_SPACE
                &&& final(self).blocks.tracks_addr_run(bt1, 2)
                &&& final(self).blocks.tracks_addr_run(bt2, 2)
                &&& p2 != process
                &&& final(self).root_untyped(process) == u
                &&& final(self).slot_holds(process, ROOT_UNTYPED_SLOT, u, first)
                &&& final(self).list.nodes@[u as int].live
                &&& final(self).list.nodes@[u as int].depth == 1
                &&& final(self).slot_holds(process, ROOT_CORE_SLOT, core0, core_payload(0, MAX_PRIORITY))
                &&& final(self).list.nodes@[core0 as int].depth == 1
                &&& final(self).tables.leaf(process, 0) == leaf@
                &&& leaf@ + LEAF_BYTES <= NODE_SPACE
                &&& final(self).tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize
                &&& final(self).slot_holds(process, WITNESS_PROCESS_SLOT, np2, process_of(p2))
                &&& final(self).list.nodes@[np2 as int].depth == 2
                &&& final(self).list.parent@[np2] == u
                &&& (base + 2 * PAGE_SZ) as usize != leaf@
                &&& leaf@ % PAGE_SZ == 0
                &&& !final(self).cap_dead(np2)
                &&& final(self).processes.records@.contains_key(p2)
                &&& !final(self).processes.records@[p2].value().dead
                &&& final(self).tables.roots@.contains_key(p2)
                &&& final(self).tables.leaf(p2, 0) == b3
                &&& final(self).spaces.roots@.contains_key(process)
                &&& final(self).spaces.roots@.contains_key(p2)
                &&& final(self).blocks.pages@[(p2 / PAGE_SZ) as int].refs == 1
                &&& final(self).holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT)
                &&& final(self).notification_at(process, WITNESS_FRAME_SLOT) == base
                &&& final(self).holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT)
                &&& final(self).notification_at(process, WITNESS_BADGED_SLOT) == base
                &&& final(self).payload_of(final(self).tables.node_of(process, WITNESS_BADGED_SLOT)).badge
                    == 0x4000_0000_0000_0000 // not a page size: bit 62 of the word
                &&& final(self).holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT)
                &&& final(self).notification_at(p2, WITNESS_CHILD_SLOT) == base
                &&& final(self).caller_live(0, p2) == (final(self).cores@[0].current_thread is Some
                    && final(self).threads.records@[final(self).cores@[0].current_thread->Some_0].value().process == Some(p2)
                    && final(self).root_live(p2))
                &&& final(self).root_live(p2)
                &&& final(self).endpoints.records@.contains_key(base)
                &&& final(self).endpoints.records@[base].value() == fresh_record()
                &&& final(self).blocks.pages@[(base / PAGE_SZ) as int].object is Notification
                &&& witness_empty(*final(self), process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize)
                &&& witness_empty(*final(self), process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize)
                &&& final(self).can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER)
                &&& final(self).blocks.small_free((bt1 / PAGE_SZ) as int, THREAD_ORDER as usize)
                &&& bt1 % THREAD_BYTES == 0
                &&& bt1 / PAGE_SZ == b3 / PAGE_SZ + 2
                &&& !final(self).threads.records@.contains_key(bt1)
                &&& final(self).can_retype_under(process, ROOT_UNTYPED_SLOT, bt2, THREAD_ORDER)
                &&& final(self).blocks.small_free((bt2 / PAGE_SZ) as int, THREAD_ORDER as usize)
                &&& bt2 % THREAD_BYTES == 0
                &&& bt2 / PAGE_SZ == b3 / PAGE_SZ + 4
                &&& !final(self).threads.records@.contains_key(bt2)
                &&& final(self).stale_epoch == old(self).stale_epoch
                &&& forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8
                    ==> final(self).stale_epoch.pages@[j] == 0
                &&& forall|j: int| b3 / PAGE_SZ + 2 <= j < b3 / PAGE_SZ + 8 ==> {
                    &&& (#[trigger] final(self).blocks.pages@[j]).kind == old(self).blocks.pages@[j].kind
                    &&& final(self).blocks.pages@[j].object == old(self).blocks.pages@[j].object
                    &&& final(self).blocks.pages@[j].order == old(self).blocks.pages@[j].order
                }
                &&& forall|x: int| 0 <= x < final(self).blocks.num_2m()
                    ==> (#[trigger] final(self).blocks.regions_2m@[x]).typed == old(self).blocks.regions_2m@[x].typed
                &&& forall|x: int| 0 <= x < final(self).blocks.num_1g()
                    ==> (#[trigger] final(self).blocks.regions_1g@[x]).typed == old(self).blocks.regions_1g@[x].typed
            }),
    {
        hide(CapKernel::wf);
        hide(CapKernel::booted);
        hide(BlockTable::counts_wf);
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost core0 = (leaf@ + ROOT_CORE_SLOT) as usize;
        let ghost lb = (base + 2 * PAGE_SZ) as usize;
        let ghost np2 = (lb + 1) as usize;
        let ghost ne = (lb + 3) as usize;
        let ghost pre_boot = *self;
        proof {
            lemma_tables_bound_nonneg(image@);
            lemma_booted_entry(pre_boot, root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@, kernel_root);
            pre_boot.lemma_booted_notification_setup(root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@, kernel_root, base);
            assert(pre_boot.root_table_block(process, base));
            lemma2_to64();
            assert(cap_wf(first)) by {
                reveal(CapKernel::wf);
            }
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(PROCESS_BYTES == 8 * PAGE_SZ);
            assert(THREAD_BYTES == 2 * PAGE_SZ);
            assert(base % PROCESS_BYTES == 0);
            assert(base % PAGE_SZ == 0) by (nonlinear_arith)
                requires base % PROCESS_BYTES == 0, PROCESS_BYTES == 8 * PAGE_SZ;
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 3) * PROCESS_BYTES <= block_bytes(first.order));
            assert(base + 3 * PROCESS_BYTES <= NODE_SPACE);
            assert(first.base <= base && base + 3 * PROCESS_BYTES <= first.base + block_bytes(first.order));
            assert forall|j: int| 0 <= j < 3 implies #[trigger] witness_block(pre_boot, cursor_block(base, j), first) by {
                reveal(CapKernel::booted);
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(pre_boot.root_table_block(process, cursor_block(first.base, itb + j)));
            }
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            assert(witness_block(pre_boot, (base + PROCESS_BYTES) as usize, first));
            assert(witness_block(pre_boot, (base + 2 * PROCESS_BYTES) as usize, first));
        }
        let p2 = base + PROCESS_BYTES;
        let b3 = p2 + PROCESS_BYTES;
        self.witness_setup_badged_notification(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root, base, report);
        let ghost s0 = *self;
        proof {
            assert(b3 + 6 * PAGE_SZ < base + 3 * PROCESS_BYTES);
            lemma_block_page(p2, 0);
            lemma_block_page(b3, 0);
            lemma_block_page(b3, 2);
            lemma_block_page(b3, 4);
            assert(s0.blocks.tracks_addr_run(p2, 8));
            assert(s0.blocks.tracks_addr_run(b3, 8));
            assert(!s0.blocks.covered((p2 / PAGE_SZ) as int)) by {
                reveal(CapKernel::wf);
                assert(s0.blocks.tracks((p2 / PAGE_SZ) as int));
                assert(0 <= region_2m((p2 / PAGE_SZ) as int) < s0.blocks.num_2m());
                assert(0 <= region_1g((p2 / PAGE_SZ) as int) < s0.blocks.num_1g());
            }
            assert(s0.blocks.small_free((p2 / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s0.blocks.pages@[p2 / PAGE_SZ + k].kind is Free by {
                    assert(pre_boot.blocks.pages@[p2 / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.tables.leaf(process, 0) == leaf@);
            assert(leaf@ % PAGE_SZ == 0) by {
                reveal(CapKernel::wf);
                reveal(Tables::leaves_wf);
                s0.lemma_slot(process, ROOT_UNTYPED_SLOT);
                assert(s0.tables.owner@.contains_key(leaf@));
            }
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            assert(1usize < MAX_DEPTH) by (compute_only);
            assert(PROCESS_ORDER == 3) by (compute_only);
            assert(block_within(p2, PROCESS_ORDER, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.list.nodes@[core0 as int].depth == 1);
            s0.lemma_slot_bound(u);
            s0.lemma_slot_bound(core0);
            assert(s0.is_cap(u) && s0.is_cap(core0));
            assert(s0.blocks.pages@[(base / PAGE_SZ) as int].object is Notification) by {
                reveal(CapKernel::wf);
            }
            assert(s0.blocks.pages@[(base / PAGE_SZ) as int].refs == 2);
            assert(block_refs(&s0.blocks, BlockRef::Small(base / PAGE_SZ)) == 2) by {
                reveal(CapKernel::wf);
            }
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, p2, PROCESS_ORDER));
            assert(s0.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2, PROCESS_ORDER));
            s0.lemma_slot(process, WITNESS_FRAME_SLOT);
            assert(s0.slot_holds(process, WITNESS_FRAME_SLOT, ne, notification_of(base)));
            assert(s0.slot_holds(process, WITNESS_BADGED_SLOT, (lb + 2) as usize, s0.payload_of((lb + 2) as usize)));
            assert(pre_boot.flush_epoch == 0) by {
                reveal(CapKernel::booted);
            }
            assert(b3 == (base + 2 * PROCESS_BYTES) as usize);
            assert(b3 % PAGE_SZ == 0) by {
                assert(PROCESS_BYTES == 8 * PAGE_SZ);
            }
            assert(order_pages(3) == 8) by (compute_only);
            assert forall|j: int| b3 / PAGE_SZ <= j < b3 / PAGE_SZ + 8 implies {
                &&& (#[trigger] s0.blocks.pages@[j]).kind == pre_boot.blocks.pages@[j].kind
                &&& s0.blocks.pages@[j].object == pre_boot.blocks.pages@[j].object
                &&& s0.blocks.pages@[j].order == pre_boot.blocks.pages@[j].order
            } by {}
            assert forall|x: int| 0 <= x < s0.blocks.num_2m()
                implies (#[trigger] s0.blocks.regions_2m@[x]).typed == pre_boot.blocks.regions_2m@[x].typed by {}
            assert forall|x: int| 0 <= x < s0.blocks.num_1g()
                implies (#[trigger] s0.blocks.regions_1g@[x]).typed == pre_boot.blocks.regions_1g@[x].typed by {}
        }
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::process_retype_answered(s0, s1, process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2, true));
            assert(Self::process_retype_kept(s0, s1));
            assert(Self::process_retype_done(s0, s1, process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2));
            assert(Self::process_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, p2));
            Self::lemma_setup_waiter_s1(pre_boot, s0, s1, process, p2, leaf@, first, base, b3, t, kernel_root);
        }
        let ok2 = self.retype_leaf(
            process,
            ROOT_UNTYPED_SLOT,
            Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 },
            b3,
            Tracked(&mut steps),
        );
        let ghost s2 = *self;
        proof {
            assert(ok2);
            assert(Self::leaf_retyped(s1, s2, process, ROOT_UNTYPED_SLOT, Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 }, b3));
            assert(Self::leaf_retype_spared(s1, s2, b3));
            assert(Self::leaf_retype_kept(s1, s2));
            assert(Self::same_tree(s1, s2));
            Self::lemma_setup_waiter_s2(pre_boot, s1, s2, process, p2, leaf@, first, base, b3, t, kernel_root);
        }
        let ok3 = self.derive(
            process,
            WITNESS_FRAME_SLOT,
            Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT },
            RECEIVE_RIGHT,
            base,
            0,
            0,
        );
        proof {
            let s3 = *self;
            let ghost nc = (b3 + 1) as usize;
            assert(ok3);
            assert(Self::cap_derived_at(
                s2,
                s3,
                process,
                WITNESS_FRAME_SLOT,
                Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT },
                RECEIVE_RIGHT,
                base,
                0,
                0,
            ));
            assert(Self::derive_step(s2, s3, nc));
            assert(Self::derive_counted(s2, s3, ne));
            assert(Self::derive_kept(s2, s3));
            assert(Self::derive_linked(s2, s3, nc, ne));
            Self::lemma_setup_waiter_s3(pre_boot, s2, s3, process, p2, leaf@, first, base, b3, t, kernel_root);
        }
    }

    /// Helper for `lemma_spawn_placed_s2`: proves table preservation and empty slots across `place`.
    #[verifier::spinoff_prover]
    proof fn lemma_spawn_placed_s2_tables(
        s0: Self,
        s1: Self,
        s2: Self,
        process: usize,
        slot: usize,
        core_node: usize,
        bt: usize,
    )
        requires
            s0.wf(),
            s1.wf(),
            s2.wf(),
            Self::placed(s1, s2, core_node, bt, Placement { core: 0, priority: 1 }),
            s1.tables.roots == s0.tables.roots,
            Self::waiter_tables_kept(s0, s1),
            s1.list.nodes@[bt as int].kind is Binding,
            !s1.list.nodes@[(bt + 1) as int].live,
            (bt + 1) < NODE_SPACE,
            forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
                ==> #[trigger] witness_empty(s1, process, s, node),
        ensures
            s2.tables == s1.tables,
            s2.processes == s1.processes,
            Self::waiter_tables_kept(s0, s2),
            forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
                ==> #[trigger] witness_empty(s2, process, s, node),
    {
        assert forall|r: usize, i: usize| #[trigger] s1.tables.has_slot(&s1.list, r, i) implies {
            &&& s2.tables.has_slot(&s2.list, r, i)
            &&& s2.tables.node_of(r, i) == s1.tables.node_of(r, i)
        } by {
            reveal(CapKernel::wf);
            reveal(Tables::leaves_wf);
            s1.lemma_slot(r, i);
            s1.lemma_slot_bound(s1.tables.node_of(r, i));
            assert(s1.tables.leaf(r, index_entry(i)) != (bt + 1) as usize) by {
                let l = s1.tables.leaf(r, index_entry(i));
                assert(l % LEAF_BYTES == 0);
                assert(((bt + 1) as int) % (PAGE_SZ as int) == 1);
            }
            assert(s2.list.nodes@[s1.tables.leaf(r, index_entry(i)) as int].live);
        }
        assert forall|x: usize| #[trigger] s1.is_cap(x) implies {
            &&& s2.is_cap(x)
            &&& s2.payload_of(x) == s1.payload_of(x)
        } by {
            s1.lemma_slot_bound(x);
            assert(x != (bt + 1) as usize);
        }
        assert forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
            implies #[trigger] witness_empty(s2, process, s, node) by {
            assert(witness_empty(s1, process, s, node));
            reveal(CapKernel::wf);
            reveal(Tables::leaves_wf);
            s1.lemma_slot(process, s);
            assert(page_of(node) != bt) by {
                if page_of(node) == bt {
                    assert(s1.list.nodes@[bt as int].kind is Hidden);
                    assert(s1.list.nodes@[bt as int].kind is Binding);
                }
            }
            assert(node != (bt + 1) as usize);
        }
        assert(Self::waiter_tables_kept(s0, s2)) by {
            reveal(CapKernel::waiter_tables_kept);
        }
    }

    /// Helper for `witness_spawn_placed_waiter`: carries tree, table, thread, and empty-slot
    /// facts across `place` in `s2` with `waiter_tables_kept` and list quantifiers isolated here.
    #[verifier::spinoff_prover]
    proof fn lemma_spawn_placed_s2(
        s0: Self,
        s1: Self,
        s2: Self,
        process: usize,
        slot: usize,
        core_node: usize,
        np2: usize,
        nt: usize,
        bt: usize,
    )
        requires
            s0.wf(),
            s1.wf(),
            s2.wf(),
            Self::placed(s1, s2, core_node, bt, Placement { core: 0, priority: 1 }),
            s1.tables.roots == s0.tables.roots,
            Self::waiter_tables_kept(s0, s1),
            s1.list.is_child(np2, bt),
            s1.list.childless(nt),
            core_node != nt,
            s1.list.nodes@[bt as int].kind is Binding,
            !s1.list.nodes@[(bt + 1) as int].live,
            (bt + 1) < NODE_SPACE,
            nt < NODE_SPACE,
            s1.list.nodes@[nt as int].live,
            forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0 ==> !(#[trigger] s1.list.nodes@[bt + k]).live,
            forall|x: usize| #[trigger] s0.list.is_child(core_node, x) ==> s1.list.is_child(core_node, x),
            forall|x: usize| #[trigger] s1.list.is_child(core_node, x) ==> s0.list.is_child(core_node, x),
            forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
                ==> #[trigger] witness_empty(s1, process, s, node),
            forall|u: usize| u != bt && #[trigger] s0.threads.records@.contains_key(u) ==> {
                &&& s1.threads.records@.contains_key(u)
                &&& s1.threads.records@[u] == s0.threads.records@[u]
            },
            s1.threads.records@.dom() == s0.threads.records@.dom().insert(bt),
            forall|k: int| 0 <= k < NODE_SPACE && k != nt && k != bt ==> {
                &&& (#[trigger] s1.list.nodes@[k]).live == s0.list.nodes@[k].live
                &&& s0.list.valid(k as usize) ==> (
                    s1.list.nodes@[k].kind == s0.list.nodes@[k].kind
                    && s1.list.nodes@[k].depth == s0.list.nodes@[k].depth
                )
            },
        ensures
            s2.list.childless(nt),
            s2.list.is_child(np2, bt),
            s2.list.is_child(core_node, (bt + 1) as usize),
            s2.list.nodes@[(bt + 1) as int].kind is Placement,
            s2.list.childless((bt + 1) as usize),
            s2.tables == s1.tables,
            s2.processes == s1.processes,
            Self::waiter_tables_kept(s0, s2),
            forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
                ==> #[trigger] witness_empty(s2, process, s, node),
            forall|x: usize| #[trigger] s0.list.is_child(core_node, x)
                ==> s2.list.is_child(core_node, x),
            forall|x: usize| #[trigger] s2.list.is_child(core_node, x)
                ==> x == (bt + 1) as usize || s0.list.is_child(core_node, x),
            forall|u: usize| u != bt && #[trigger] s0.threads.records@.contains_key(u) ==> {
                &&& s2.threads.records@.contains_key(u)
                &&& s2.threads.records@[u] == s0.threads.records@[u]
            },
            s2.threads.records@.dom() == s0.threads.records@.dom().insert(bt),
            forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0 && k != 1
                ==> !(#[trigger] s2.list.nodes@[bt + k]).live,
            forall|k: int| 0 <= k < NODE_SPACE && k != nt && k != bt && k != bt + 1 ==> {
                &&& (#[trigger] s2.list.nodes@[k]).live == s0.list.nodes@[k].live
                &&& s0.list.valid(k as usize) ==> (
                    s2.list.nodes@[k].kind == s0.list.nodes@[k].kind
                    && s2.list.nodes@[k].depth == s0.list.nodes@[k].depth
                )
            },
    {
        assert forall|y: usize| !#[trigger] s2.list.is_child(nt, y) by {
            if s2.list.is_child(nt, y) {
                if y == (bt + 1) as usize {
                    assert(s2.list.parent@[(bt + 1) as usize] == core_node);
                } else {
                    reveal(CapKernel::wf);
                    crate::capability::list::lemma_has(s2.list.seq@, y);
                    let k = choose|k: int| 0 <= k < s2.list.seq@.len() && s2.list.seq@[k] == y;
                    s2.list.lemma_link(k);
                    assert(s1.list.nodes@[y as int].live);
                    crate::capability::list::lemma_has(s1.list.seq@, y);
                    assert(s1.list.is_child(nt, y));
                    s1.list.lemma_childless(nt, y);
                }
            }
        }
        assert(s2.list.childless(nt)) by {
            if !s2.list.childless(nt) {
                reveal(CapKernel::wf);
                s2.list.lemma_next_is_child(nt);
            }
        }
        assert(s2.list.nodes@[bt as int].live && bt != (bt + 1) as usize && s2.list.parent@[bt] == np2) by {
            reveal(CapKernel::wf);
            crate::capability::list::lemma_has(s1.list.seq@, bt);
            let k = choose|k: int| 0 <= k < s1.list.seq@.len() && s1.list.seq@[k] == bt;
            s1.list.lemma_link(k);
        }
        assert(has(s2.list.seq@, bt)) by {
            reveal(CapKernel::wf);
            assert(s2.list.nodes@[bt as int].live);
        }
        crate::capability::list::lemma_has(s2.list.seq@, bt);
        assert forall|y: usize| !#[trigger] s2.list.is_child((bt + 1) as usize, y) by {
            if s2.list.is_child((bt + 1) as usize, y) {
                if y == (bt + 1) as usize {
                    assert(s2.list.parent@[(bt + 1) as usize] == core_node);
                } else {
                    reveal(CapKernel::wf);
                    crate::capability::list::lemma_has(s2.list.seq@, y);
                    let k = choose|k: int| 0 <= k < s2.list.seq@.len() && s2.list.seq@[k] == y;
                    s2.list.lemma_link(k);
                    assert(s1.list.nodes@[y as int].live);
                    assert(s1.list.parent@[y] == (bt + 1) as usize);
                    s1.list.lemma_link(0);
                    crate::capability::list::lemma_has(s1.list.seq@, y);
                    let j = choose|j: int| 0 <= j < s1.list.seq@.len() && s1.list.seq@[j] == y;
                    s1.list.lemma_link(j);
                    if y == s1.list.seq@[0] {
                        assert(s1.list.parent@.contains_key(s1.list.seq@[0]));
                    }
                    s1.list.lemma_dead_childless((bt + 1) as usize, y);
                }
            }
        }
        assert(s2.list.childless((bt + 1) as usize)) by {
            if !s2.list.childless((bt + 1) as usize) {
                reveal(CapKernel::wf);
                s2.list.lemma_next_is_child((bt + 1) as usize);
            }
        }
        Self::lemma_spawn_placed_s2_tables(s0, s1, s2, process, slot, core_node, bt);
        assert forall|x: usize| #[trigger] s1.list.is_child(core_node, x)
            implies s2.list.is_child(core_node, x) by {
            reveal(CapKernel::wf);
            crate::capability::list::lemma_has(s1.list.seq@, x);
            let k = choose|k: int| 0 <= k < s1.list.seq@.len() && s1.list.seq@[k] == x;
            s1.list.lemma_link(k);
            assert(x != (bt + 1) as usize);
            assert(s2.list.nodes@[x as int].live);
            assert(has(s2.list.seq@, x));
            crate::capability::list::lemma_has(s2.list.seq@, x);
        }
        assert forall|x: usize| #[trigger] s2.list.is_child(core_node, x)
            implies x == (bt + 1) as usize || s1.list.is_child(core_node, x) by {
            if x != (bt + 1) as usize {
                reveal(CapKernel::wf);
                crate::capability::list::lemma_has(s2.list.seq@, x);
                let k = choose|k: int| 0 <= k < s2.list.seq@.len() && s2.list.seq@[k] == x;
                s2.list.lemma_link(k);
                assert(has(s1.list.seq@, x));
                crate::capability::list::lemma_has(s1.list.seq@, x);
            }
        }
        assert(Self::waiter_tables_kept(s0, s2)) by {
            reveal(CapKernel::waiter_tables_kept);
        }
    }

    /// Retypes a thread at `bt` into `slot` (bound to `p2` via `WITNESS_PROCESS_SLOT`), places it on
    /// core 0 at priority 1 via `core_slot`, and starts it.
    #[verifier::spinoff_prover]
    fn witness_spawn_placed_waiter(
        &mut self,
        process: usize,
        p2: usize,
        leaf: Ghost<usize>,
        first: Ghost<Payload>,
        base: usize,
        slot: usize,
        core_slot: usize,
        core_prio: Ghost<usize>,
        bt: usize,
    )
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(process),
            old(self).root_live(process),
            old(self).processes.records@.contains_key(process),
            !old(self).processes.records@[process].value().dead,
            old(self).tables.roots@.contains_key(p2),
            old(self).processes.records@.contains_key(p2),
            !old(self).processes.records@[p2].value().dead,
            old(self).blocks.pages@[(p2 / PAGE_SZ) as int].refs <= 2,
            old(self).tables.leaf(process, 0) == leaf@,
            leaf@ % PAGE_SZ == 0,
            leaf@ + LEAF_BYTES <= NODE_SPACE,
            base % PAGE_SZ == 0,
            (base + 2 * PAGE_SZ) as usize != leaf@,
            base + 3 * PROCESS_BYTES <= NODE_SPACE,
            old(self).tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            old(self).root_untyped(process) == (leaf@ + ROOT_UNTYPED_SLOT) as usize,
            old(self).slot_holds(process, ROOT_UNTYPED_SLOT, (leaf@ + ROOT_UNTYPED_SLOT) as usize, first@),
            old(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].live,
            old(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].depth == 1,
            first@.kind is Untyped,
            first@.rights == UNTYPED_RIGHTS,
            old(self).slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            old(self).list.nodes@[base + 2 * PAGE_SZ + 1].depth == 2,
            1 <= core_prio@ <= MAX_PRIORITY,
            old(self).tables.has_slot(&old(self).list, process, core_slot),
            old(self).slot_holds(process, core_slot, old(self).tables.node_of(process, core_slot), core_payload(0, core_prio@)),
            old(self).list.nodes@[old(self).tables.node_of(process, core_slot) as int].depth < MAX_DEPTH,
            index_ok(slot),
            index_entry(slot) == 2,
            index_slot(slot) >= 4,
            witness_empty(*old(self), process, slot, (base + 2 * PAGE_SZ + index_slot(slot)) as usize),
            old(self).can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER),
            old(self).blocks.tracks_addr_run(bt, 2),
            old(self).blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize),
            bt % THREAD_BYTES == 0,
            bt / PAGE_SZ >= base / PAGE_SZ + 18,
            !old(self).threads.records@.contains_key(bt),
            old(self).threads.queues.all_empty(),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            final(self).tables.roots == old(self).tables.roots,
            Self::waiter_tables_kept(*old(self), *final(self)),
            final(self).endpoints == old(self).endpoints,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).cores == old(self).cores,
            final(self).spaces == old(self).spaces,
            final(self).root_untyped(process) == (leaf@ + ROOT_UNTYPED_SLOT) as usize,
            final(self).slot_holds(process, ROOT_UNTYPED_SLOT, (leaf@ + ROOT_UNTYPED_SLOT) as usize, first@),
            final(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].live,
            final(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].depth == 1,
            final(self).slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            final(self).list.nodes@[base + 2 * PAGE_SZ + 1].depth == 2,
            final(self).slot_holds(process, core_slot, old(self).tables.node_of(process, core_slot), core_payload(0, core_prio@)),
            final(self).list.nodes@[old(self).tables.node_of(process, core_slot) as int].depth
                == old(self).list.nodes@[old(self).tables.node_of(process, core_slot) as int].depth,
            final(self).slot_holds(process, slot, (base + 2 * PAGE_SZ + index_slot(slot)) as usize, thread_of(bt)),
            final(self).list.childless((base + 2 * PAGE_SZ + index_slot(slot)) as usize),
            final(self).list.nodes@[(base + 2 * PAGE_SZ + index_slot(slot)) as int].depth == 2,
            final(self).blocks.pages@[(p2 / PAGE_SZ) as int].refs == old(self).blocks.pages@[(p2 / PAGE_SZ) as int].refs + 1,
            final(self).blocks.pages@[(bt / PAGE_SZ) as int].refs == 1,
            forall|s: usize, node: usize| s != slot && witness_empty(*old(self), process, s, node)
                ==> #[trigger] witness_empty(*final(self), process, s, node),
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            final(self).flush_epoch == old(self).flush_epoch,
            forall|j: int| 0 <= j < old(self).blocks.pages@.len() && j != p2 / PAGE_SZ && j != bt / PAGE_SZ && j != bt / PAGE_SZ + 1
                ==> #[trigger] final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            final(self).threads.records@.dom() == old(self).threads.records@.dom().insert(bt),
            final(self).threads.records@[bt].value().state == (ThreadState::Runnable { core: 0 }),
            final(self).threads.records@[bt].value().queued == NONE,
            final(self).threads.records@[bt].value().process == Some(p2),
            final(self).threads.records@[bt].value().placement == Some(Placement { core: 0, priority: 1 }),
            !final(self).threads.records@[bt].value().dying,
            !final(self).threads.records@[bt].value().pending_stop,
            final(self).threads.queues.queue(0, 1) == seq![bt],
            forall|d: int, p: int| 0 <= d < NUM_CPUS && 0 <= p < NUM_PRIORITIES && (d != 0 || p != 1)
                ==> (#[trigger] final(self).threads.queues.queue(d, p)) == Seq::<usize>::empty(),
            forall|u: usize| u != bt && #[trigger] old(self).threads.records@.contains_key(u) ==> (
                final(self).threads.records@.contains_key(u)
                && same_record_perm_but_links(old(self).threads.records@[u], final(self).threads.records@[u])
            ),
            final(self).list.is_child((base + 2 * PAGE_SZ + 1) as usize, bt),
            final(self).list.is_child(old(self).tables.node_of(process, core_slot), (bt + 1) as usize),
            final(self).list.nodes@[(bt + 1) as int].kind is Placement,
            final(self).list.childless((bt + 1) as usize),
            forall|x: usize| #[trigger] old(self).list.is_child(old(self).tables.node_of(process, core_slot), x)
                ==> final(self).list.is_child(old(self).tables.node_of(process, core_slot), x),
            forall|x: usize| #[trigger] final(self).list.is_child(old(self).tables.node_of(process, core_slot), x)
                ==> x == (bt + 1) as usize || old(self).list.is_child(old(self).tables.node_of(process, core_slot), x),
            forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0 && k != 1
                ==> !(#[trigger] final(self).list.nodes@[bt + k]).live,
            forall|k: int| 0 <= k < NODE_SPACE && k != (base + 2 * PAGE_SZ + index_slot(slot)) && k != bt && k != bt + 1 ==> {
                &&& (#[trigger] final(self).list.nodes@[k]).live == old(self).list.nodes@[k].live
                &&& old(self).list.valid(k as usize) ==> (
                    final(self).list.nodes@[k].kind == old(self).list.nodes@[k].kind
                    && final(self).list.nodes@[k].depth == old(self).list.nodes@[k].depth
                )
            },
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost s0 = *self;
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost np2 = (base + 2 * PAGE_SZ + 1) as usize;
        let ghost core_node = s0.tables.node_of(process, core_slot);
        let ghost nt = (base + 2 * PAGE_SZ + index_slot(slot)) as usize;
        let ghost bt_page = bt / PAGE_SZ;
        proof {
            assert(bt % PAGE_SZ == 0) by (nonlinear_arith)
                requires bt % THREAD_BYTES == 0, THREAD_BYTES == 2 * PAGE_SZ;
            assert(s0.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s0.tables.wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(s0.blocks.pages@[(p2 / PAGE_SZ) as int].refs < usize::MAX);
            assert(!s0.cap_dead(np2)) by {
                reveal(CapKernel::wf);
            }
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(2usize < MAX_DEPTH) by (compute_only);
            assert(s0.blocks.pages@[(p2 / PAGE_SZ) as int].kind is Base && s0.blocks.pages@[(p2 / PAGE_SZ) as int].order == PROCESS_ORDER) by {
                reveal(CapKernel::wf);
            }
            assert(s0.can_hold_thread(process, WITNESS_PROCESS_SLOT));
            assert(order_pages(THREAD_ORDER as usize) == 2) by (compute_only);
            assert(s0.blocks.pages@[(bt_page as int) + 0].kind is Free);
            assert(s0.blocks.pages@[(bt_page as int) + 1].kind is Free);
            assert(s0.blocks.pages@[bt_page as int].kind is Free);
            assert(s0.can_retype_thread(process, ROOT_UNTYPED_SLOT, slot, bt, WITNESS_PROCESS_SLOT));
            s0.lemma_slot(process, core_slot);
            s0.lemma_slot_bound(core_node);
            assert(core_node < NODE_SPACE && s0.list.nodes@[core_node as int].live);
            assert(page_of(core_node) / PAGE_SZ != bt_page) by {
                reveal(CapKernel::wf);
                reveal(Tables::leaves_wf);
                s0.lemma_slot(process, core_slot);
                let l = page_of(core_node);
                assert(s0.tables.owner@.contains_key(l));
                assert(s0.list.pages@.dom().contains(l));
                assert(s0.blocks.tracks_addr(l));
            }
            assert(core_node / PAGE_SZ != bt_page);
            assert(nt / PAGE_SZ == ((base + 2 * PAGE_SZ) as usize) / PAGE_SZ);
            assert(((base + 2 * PAGE_SZ) as usize) / PAGE_SZ == base / PAGE_SZ + 2);
            assert(nt != bt && nt != bt + 1);
            assert(nt != u && nt != np2 && nt != core_node);
            assert(bt < bt + 1 < bt + NODES_PER_PAGE);
            assert(u != bt && np2 != bt && core_node != bt);
            assert(((bt + 1) as int) / (PAGE_SZ as int) == bt_page as int);
            assert(np2 / PAGE_SZ == base / PAGE_SZ + 2);
            assert(np2 / PAGE_SZ != bt_page);
            assert(page_of(u) / PAGE_SZ != bt_page) by {
                reveal(CapKernel::wf);
                s0.lemma_slot(process, ROOT_UNTYPED_SLOT);
                assert(s0.tables.owner@.contains_key(page_of(u)));
            }
            assert(u / PAGE_SZ != bt_page);
            assert((bt + 1) as usize / PAGE_SZ != u / PAGE_SZ);
            assert(u != bt + 1 && np2 != bt + 1 && core_node != bt + 1);
            assert(p2 / PAGE_SZ != bt_page && p2 / PAGE_SZ != bt_page + 1) by {
                reveal(CapKernel::wf);
                assert(s0.processes.records@.contains_key(p2));
            }
        }
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_thread(process, ROOT_UNTYPED_SLOT, slot, bt, WITNESS_PROCESS_SLOT, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::retype_keeps(s0, s1, nt, bt_page as int, 1, None));
            assert(s1.blocks.pages@[bt_page as int].refs == 1);
            assert(s1.slot_holds(process, ROOT_UNTYPED_SLOT, u, first@));
            assert(s1.slot_holds(process, WITNESS_PROCESS_SLOT, np2, process_of(p2)));
            assert(s1.slot_holds(process, core_slot, core_node, core_payload(0, core_prio@)));
            assert(s1.slot_holds(process, slot, nt, thread_of(bt)));
            assert(s0.list.wf() && s1.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(Self::typed_nodes(s0.list, s1.list, nt, bt));
            assert(s1.list.parent@ == s0.list.parent@.insert(nt, u).insert(bt, np2));
            assert forall|x: usize| x != nt && x != bt && #[trigger] s0.list.parent@.contains_key(x)
                implies s1.list.parent@[x] == s0.list.parent@[x] by {}
            lemma_children_kept(s0.list, s1.list, nt, bt, nt);
            assert(nt != u && nt != np2) by {
                assert(u / PAGE_SZ == leaf@ / PAGE_SZ);
                assert(nt / PAGE_SZ == (base + 2 * PAGE_SZ) as usize / PAGE_SZ);
                assert((base + 2 * PAGE_SZ) as usize != leaf@);
                assert(leaf@ % PAGE_SZ == 0);
                assert(nt / PAGE_SZ != u / PAGE_SZ);
                assert(index_slot(slot) >= 4);
            }
            assert forall|x: usize| !#[trigger] s1.list.is_child(nt, x) by {
                if s1.list.is_child(nt, x) {
                    if x == nt {
                        assert(s1.list.parent@[nt] == u);
                    } else if x == bt {
                        assert(s1.list.parent@[bt] == np2);
                    } else {
                        s0.list.lemma_dead_childless(nt, x);
                    }
                }
            }
            assert(s1.list.childless(nt)) by {
                if !s1.list.childless(nt) {
                    s1.list.lemma_next_is_child(nt);
                }
            }
            assert(s1.list.is_child(np2, bt));
            assert(!s1.cap_dead(nt));
            assert(s1.can_control(process, slot));
            assert(s1.holds_core(process, core_slot, 0));
            assert(s1.can_place(process, slot, core_slot, 1));
            assert(s1.blocks.pages@[bt_page as int].order == 1);
            assert(!s1.list.nodes@[(bt + 1) as int].live);
            assert(s0.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(core_node != nt && core_node != bt) by {
                reveal(CapKernel::wf);
                assert(core_node / PAGE_SZ == page_of(core_node) / PAGE_SZ);
                assert(core_node / PAGE_SZ != bt_page);
                assert(((bt + 1) as int) / (PAGE_SZ as int) == bt_page as int);
                s0.lemma_slot(process, core_slot);
                assert(s0.tables.owner@.contains_key(page_of(core_node)));
                assert(page_of(core_node) == s0.tables.leaf(process, index_entry(core_slot)));
                if core_node == nt {
                    assert(page_of(nt) == (base + 2 * PAGE_SZ) as usize);
                    assert(s0.tables.owner@[page_of(core_node)].1 == index_entry(core_slot));
                    assert(s0.tables.owner@[page_of(nt)].1 == 2);
                }
            }
            lemma_children_kept(s0.list, s1.list, nt, bt, core_node);
            assert(!s0.list.valid(bt));
            assert forall|x: usize| #[trigger] s0.list.is_child(core_node, x)
                implies s1.list.is_child(core_node, x) by {
                assert(x != nt && x != bt) by {
                    if x == nt {
                        assert(!s0.list.nodes@[nt as int].live);
                        crate::capability::list::lemma_has(s0.list.seq@, nt);
                        let k = choose|k: int| 0 <= k < s0.list.seq@.len() && s0.list.seq@[k] == nt;
                        s0.list.lemma_link(k);
                    }
                    if x == bt {
                        crate::capability::list::lemma_has(s0.list.seq@, bt);
                        let k = choose|k: int| 0 <= k < s0.list.seq@.len() && s0.list.seq@[k] == bt;
                        s0.list.lemma_link(k);
                        s0.list.lemma_live_valid(bt);
                    }
                }
                crate::capability::list::lemma_has(s0.list.seq@, x);
                let k = choose|k: int| 0 <= k < s0.list.seq@.len() && s0.list.seq@[k] == x;
                s0.list.lemma_link(k);
                assert(0 <= (x as int) < NODE_SPACE) by {
                    assert(s0.list.nodes@.len() == NODE_SPACE);
                }
                assert(s1.list.nodes@[x as int].live);
                crate::capability::list::lemma_has(s1.list.seq@, x);
                assert(s1.list.seq@[0] == s0.list.seq@[0]);
                assert(s1.list.parent@[x] == s0.list.parent@[x]);
            }
            assert forall|x: usize| #[trigger] s1.list.is_child(core_node, x)
                implies s0.list.is_child(core_node, x) by {
                assert(x != nt && x != bt) by {
                    if x == nt {
                        assert(s1.list.parent@[nt] == u);
                        assert(s1.payload_of(core_node).kind is Core && s1.payload_of(u).kind is Untyped);
                    }
                    if x == bt {
                        assert(s1.list.parent@[bt] == np2);
                        assert(s1.payload_of(core_node).kind is Core && s1.payload_of(np2).kind is Process);
                    }
                }
            }
            assert(s1.list.parent@ == s0.list.parent@.insert(nt, u).insert(bt, np2));
            assert(s1.blocks.pages@[(p2 / PAGE_SZ) as int].refs == s0.blocks.pages@[(p2 / PAGE_SZ) as int].refs + 1);
            assert(s1.root_live(process));
            assert(s1.list.nodes@[nt as int].depth == 2) by {
                assert(s1.list.parent@[nt] == u);
                assert(s1.list.nodes@[u as int].depth == 1);
                s1.list.lemma_link(0);
                crate::capability::list::lemma_has(s1.list.seq@, nt);
                let k = choose|k: int| 0 <= k < s1.list.seq@.len() && s1.list.seq@[k] == nt;
                s1.list.lemma_link(k);
                assert(k > 0) by {
                    if k == 0 {
                        assert(s1.list.parent@.contains_key(s1.list.seq@[0]));
                    }
                }
            }
            assert(s1.tables.roots == s0.tables.roots);
            assert(forall|r: usize, e: int| s0.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES
                ==> (#[trigger] s1.tables.leaf(r, e)) == s0.tables.leaf(r, e));
            assert(forall|r: usize, i: usize| #[trigger] s0.tables.has_slot(&s0.list, r, i) ==> {
                &&& s1.tables.has_slot(&s1.list, r, i)
                &&& s1.tables.node_of(r, i) == s0.tables.node_of(r, i)
            });
            assert(forall|x: usize| #[trigger] s0.is_cap(x) ==> {
                &&& s1.is_cap(x)
                &&& s1.payload_of(x) == s0.payload_of(x)
            });
            assert(forall|p: usize| #[trigger] s0.processes.records@.contains_key(p) ==> {
                &&& s1.processes.records@.contains_key(p)
                &&& s1.processes.records@[p].value().dead == s0.processes.records@[p].value().dead
            });
            reveal(CapKernel::thread_retyped_records);
            assert(s1.endpoints == s0.endpoints);
            assert(s1.threads.records@.dom() == s0.threads.records@.dom().insert(bt));
            assert(forall|u: usize| u != bt && #[trigger] s0.threads.records@.contains_key(u) ==> {
                &&& s1.threads.records@.contains_key(u)
                &&& s1.threads.records@[u] == s0.threads.records@[u]
            });
            assert((bt + 1) < NODE_SPACE) by {
                reveal(CapKernel::wf);
                lemma2_to64();
                assert(cap_wf(first@));
                assert(block_within(bt, THREAD_ORDER, first@));
                assert(block_bytes(1) == 2 * PAGE_SZ);
                assert(THREAD_BYTES == 2 * PAGE_SZ);
            }
            assert forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
                implies #[trigger] witness_empty(s1, process, s, node) by {
                reveal(CapKernel::wf);
                reveal(Tables::leaves_wf);
                s0.lemma_slot(process, s);
                s0.lemma_slot(process, slot);
                assert(node != nt) by {
                    if index_entry(s) != index_entry(slot) {
                        s0.tables.lemma_entry(process, index_entry(s));
                        s0.tables.lemma_entry(process, index_entry(slot));
                        assert(s0.tables.owner@[page_of(node)] == (process, index_entry(s) as int));
                        assert(s0.tables.owner@[page_of(nt)] == (process, index_entry(slot) as int));
                        assert(page_of(node) != page_of(nt));
                    }
                }
            }
            assert(forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0
                ==> !(#[trigger] s1.list.nodes@[bt + k]).live);
            assert forall|k: int| 0 <= k < NODE_SPACE && k != nt && k != bt implies {
                &&& (#[trigger] s1.list.nodes@[k]).live == s0.list.nodes@[k].live
                &&& s0.list.valid(k as usize) ==> (
                    s1.list.nodes@[k].kind == s0.list.nodes@[k].kind
                    && s1.list.nodes@[k].depth == s0.list.nodes@[k].depth
                )
            } by {}
            assert(Self::waiter_tables_kept(s0, s1)) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            s1.lemma_slot_bound(nt);
        }
        let ok2 = self.place(process, slot, core_slot, 1);
        let ghost s2 = *self;
        proof {
            assert(ok2);
            lemma_core_object(0);
            assert(Self::placed(s1, s2, core_node, bt, Placement { core: 0, priority: 1 }));
            assert(s2.list.nodes@[nt as int].depth == 2);
            assert(s2.slot_holds(process, slot, nt, thread_of(bt)));
            assert(!s2.cap_dead(nt));
            assert(s2.can_control(process, slot));
            assert(s2.can_start(process, slot));
            Self::lemma_spawn_placed_s2(s0, s1, s2, process, slot, core_node, np2, nt, bt);
        }
        let ok3 = self.start(process, slot);
        proof {
            let s3 = *self;
            assert(ok3);
            assert(Self::state_written(s2, s3, bt, ThreadState::Runnable { core: 0 }));
            assert(s3.list == s2.list);
            assert(s3.tables == s2.tables);
            assert(s3.processes == s2.processes);
            assert(s3.endpoints == s2.endpoints);
            assert(Self::waiter_tables_kept(s0, s3)) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert(s3.threads.records@.dom() == s0.threads.records@.dom().insert(bt));
            assert forall|u: usize| u != bt && #[trigger] s0.threads.records@.contains_key(u) implies {
                &&& s3.threads.records@.contains_key(u)
                &&& same_record_perm_but_links(s0.threads.records@[u], s3.threads.records@[u])
            } by {
                assert(s2.threads.records@.contains_key(u) && s2.threads.records@[u] == s0.threads.records@[u]);
                assert(same_record_perm_but_links(s2.threads.records@[u], s3.threads.records@[u]));
            }
            assert forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
                implies #[trigger] witness_empty(s3, process, s, node) by {
                assert(witness_empty(s2, process, s, node));
            }
            assert(forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0 && k != 1
                ==> !(#[trigger] s3.list.nodes@[bt + k]).live);
            assert forall|k: int| 0 <= k < NODE_SPACE && k != nt && k != bt && k != bt + 1 implies {
                &&& (#[trigger] s3.list.nodes@[k]).live == s0.list.nodes@[k].live
                &&& s0.list.valid(k as usize) ==> (
                    s3.list.nodes@[k].kind == s0.list.nodes@[k].kind
                    && s3.list.nodes@[k].depth == s0.list.nodes@[k].depth
                )
            } by {}
            assert(s3.blocks == s1.blocks);
            assert(s3.list.nodes@[nt as int].depth == 2);
            assert(s3.threads.queues.queue(0, 1) == seq![bt]);
            assert forall|d: int, p: int| 0 <= d < NUM_CPUS && 0 <= p < NUM_PRIORITIES && (d != 0 || p != 1)
                implies (#[trigger] s3.threads.queues.queue(d, p)) == Seq::<usize>::empty() by {}
        }
    }

    /// Helper for `witness_switch_and_block_waiter`: proves all run queues are empty in `s3` after `t`
    /// resumes on core 0.
    #[verifier::spinoff_prover]
    proof fn lemma_switch_and_block_all_empty(s0: Self, s3: Self, t: usize, bt: usize)
        requires
            s0.wf(),
            s3.wf(),
            s0.threads.queues.queue(0, 1) == seq![bt],
            forall|d: int, p: int| 0 <= d < NUM_CPUS && 0 <= p < NUM_PRIORITIES && (d != 0 || p != 1)
                ==> (#[trigger] s0.threads.queues.queue(d, p)) == Seq::<usize>::empty(),
            s3.threads.records@.dom() == s0.threads.records@.dom(),
            forall|u: usize| u != t && u != bt && #[trigger] s0.threads.records@.contains_key(u)
                ==> s3.threads.records@[u].value().state == s0.threads.records@[u].value().state,
            !(s3.threads.records@[t].value().state is Runnable),
            !(s3.threads.records@[bt].value().state is Runnable),
        ensures
            s3.threads.queues.all_empty(),
    {
        reveal(CapKernel::wf);
        reveal(queues_wf);
        assert(queues_wf(&s3.threads.queues, s3.threads.records@));
        assert(s3.threads.queues.seqs@.len() == NUM_CPUS);
        assert forall|d: int| 0 <= d < NUM_CPUS implies (#[trigger] s3.threads.queues.seqs@[d]).len() == NUM_PRIORITIES by {}
        assert forall|d: int, p: int| 0 <= d < NUM_CPUS && 0 <= p < NUM_PRIORITIES
            implies (#[trigger] s3.threads.queues.queue(d, p)) == Seq::<usize>::empty() by {
            let q = s3.threads.queues.queue(d, p);
            if q.len() > 0 {
                assert(single_queue_wf(&s3.threads.queues, s3.threads.records@, d, p));
                let u = q[0];
                assert(s3.threads.records@.contains_key(u));
                assert(s3.threads.records@[u].value().state == (ThreadState::Runnable { core: d as usize }));
                assert(u != t && u != bt);
                assert(s0.threads.records@[u].value().state == s3.threads.records@[u].value().state);
                assert(s0.threads.queues.queue(d, p).contains(u));
                if d == 0 && p == 1 {
                    assert(s0.threads.queues.queue(0, 1)[0] == bt);
                }
            }
        }
    }

    /// Switches core 0 from `t` (in `process`) to runnable thread `bt` (in `p2`), blocks `bt` on
    /// `base` via `p2`'s `WITNESS_CHILD_SLOT`, and switches core 0 back to `t`.
    #[verifier::spinoff_prover]
    fn witness_switch_and_block_waiter(
        &mut self,
        process: usize,
        p2: usize,
        t: usize,
        base: usize,
        bt: usize,
        kernel_root: usize,
        report: Processor,
        registers: Registers,
    )
        requires
            old(self).wf(),
            old(self).cores@[0].current_thread == Some(t),
            old(self).cores@[0].generation + 2 <= ID_GENERATION_MAX,
            old(self).loaded(0, process),
            old(self).spaces.kernel_root@ == kernel_root,
            kernel_root % PAGE_SZ == 0,
            crate::util::page_ptr_util_u::mem_valid(kernel_root),
            report_tags_tlb(0, report),
            old(self).tables.roots@.contains_key(process),
            old(self).tables.roots@.contains_key(p2),
            old(self).spaces.roots@.contains_key(process),
            old(self).spaces.roots@.contains_key(p2),
            old(self).processes.records@.contains_key(process),
            !old(self).processes.records@[process].value().dead,
            old(self).processes.records@.contains_key(p2),
            !old(self).processes.records@[p2].value().dead,
            old(self).root_live(p2),
            old(self).holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT),
            old(self).notification_at(p2, WITNESS_CHILD_SLOT) == base,
            old(self).endpoints.records@.contains_key(base),
            old(self).endpoints.records@[base].value().word & SIGNAL_BITS == 0,
            old(self).blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            t != bt,
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            old(self).threads.records@[t].value().process == Some(process),
            !old(self).threads.records@[t].value().dying,
            !old(self).threads.records@[t].value().pending_stop,
            old(self).threads.records@[t].value().queued != base,
            old(self).threads.records@.contains_key(bt),
            old(self).threads.records@[bt].value().state == (ThreadState::Runnable { core: 0 }),
            old(self).threads.records@[bt].value().queued == NONE,
            old(self).threads.records@[bt].value().process == Some(p2),
            old(self).threads.records@[bt].value().placement == Some(Placement { core: 0, priority: 1 }),
            !old(self).threads.records@[bt].value().dying,
            !old(self).threads.records@[bt].value().pending_stop,
            old(self).threads.queues.queue(0, 1) == seq![bt],
            forall|d: int, p: int| 0 <= d < NUM_CPUS && 0 <= p < NUM_PRIORITIES && (d != 0 || p != 1)
                ==> (#[trigger] old(self).threads.queues.queue(d, p)) == Seq::<usize>::empty(),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            final(self).tables == old(self).tables,
            final(self).list == old(self).list,
            final(self).blocks == old(self).blocks,
            final(self).processes == old(self).processes,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces.roots == old(self).spaces.roots,
            final(self).cores@[0].current_thread == Some(t),
            final(self).cores@[0].generation <= old(self).cores@[0].generation + 2,
            final(self).loaded(0, process),
            final(self).caller_live(0, process),
            final(self).root_live(process),
            final(self).threads.queues.all_empty(),
            final(self).threads.records@.dom() == old(self).threads.records@.dom(),
            final(self).threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            final(self).threads.records@[t].value().process == Some(process),
            !final(self).threads.records@[t].value().dying,
            !final(self).threads.records@[t].value().pending_stop,
            final(self).threads.records@[t].value().queued != base,
            final(self).threads.records@[bt].value().state == (ThreadState::Blocked { object: base }),
            final(self).threads.records@[bt].value().queued == base,
            final(self).threads.records@[bt].value().process == Some(p2),
            final(self).threads.records@[bt].value().placement == Some(Placement { core: 0, priority: 1 }),
            !final(self).threads.records@[bt].value().dying,
            !final(self).threads.records@[bt].value().pending_stop,
            final(self).threads.records@[bt].value().frame == partial_frame(registers),
            final(self).threads.records@[bt].value().saved is Partial,
            forall|u: usize| u != t && u != bt && #[trigger] old(self).threads.records@.contains_key(u) ==> {
                &&& final(self).threads.records@[u].value().state == old(self).threads.records@[u].value().state
                &&& final(self).threads.records@[u].value().queued == old(self).threads.records@[u].value().queued
                &&& final(self).threads.records@[u].value().process == old(self).threads.records@[u].value().process
                &&& final(self).threads.records@[u].value().placement == old(self).threads.records@[u].value().placement
                &&& final(self).threads.records@[u].value().dying == old(self).threads.records@[u].value().dying
                &&& final(self).threads.records@[u].value().pending_stop == old(self).threads.records@[u].value().pending_stop
                &&& final(self).threads.records@[u].value().frame == old(self).threads.records@[u].value().frame
                &&& final(self).threads.records@[u].value().saved == old(self).threads.records@[u].value().saved
            },
            final(self).endpoints.records@.dom() == old(self).endpoints.records@.dom(),
            final(self).endpoints.records@.contains_key(base),
            final(self).endpoints.records@[base].is_init(),
            forall|x: usize| x != base && #[trigger] final(self).endpoints.records@.contains_key(x) ==> {
                &&& final(self).endpoints.records@[x].is_init()
                &&& final(self).endpoints.records@[x].value() == old(self).endpoints.records@[x].value()
            },
            final(self).endpoints.records@[base].value().word == (old(self).endpoints.records@[base].value().word | WAITER_BIT),
            final(self).endpoints.records@[base].value().waiters@ == old(self).endpoints.records@[base].value().waiters@.push(bt),
            final(self).endpoints.records@[base].value().head == if old(self).endpoints.records@[base].value().head == NONE {
                bt
            } else {
                old(self).endpoints.records@[base].value().head
            },
            final(self).endpoints.records@[base].value().tail == bt,
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost s0 = *self;
        proof {
            assert(!s0.endpoints.records@[base].value().waiters@.contains(t)) by {
                reveal(CapKernel::wf);
                reveal(waits_wf);
                if s0.endpoints.records@[base].value().waiters@.contains(t) {
                    assert(s0.endpoints.records@.contains_key(base));
                    let s = s0.endpoints.records@[base].value().waiters@;
                    let i = choose|i: int| 0 <= i < s.len() && s[i] == t;
                    assert(waiter_linked(s, s0.threads.records@, base, i));
                }
            }
            assert(kernel_root % PAGE_SZ == 0);
            assert(s0.spaces.records@.contains_key(p2) && s0.spaces.records@[p2].value().kind is Process) by {
                reveal(CapKernel::wf);
            }
        }
        let tracked mut steps = Steps::fresh();
        self.switch_thread(0, registers, FrameKind::Full, Some(bt), kernel_root, report, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(s1.endpoints == s0.endpoints);
            assert(s1.cores@[0].current_thread == Some(bt));
            assert(s1.cores@[0].generation <= s0.cores@[0].generation + 1);
            assert(s1.caller_live(0, p2));
            assert(s1.holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT));
            assert(s1.notification_at(p2, WITNESS_CHILD_SLOT) == base);
            assert(!s1.wait_signalled(p2, WITNESS_CHILD_SLOT));
            assert(s1.threads.records@[bt].value().queued == NONE) by {
                reveal(CapKernel::wf);
                reveal(waits_wf);
                if s1.threads.records@[bt].value().queued != NONE {
                    let q = s1.threads.records@[bt].value().queued;
                    assert(s1.endpoints.records@.contains_key(q));
                    assert(s1.endpoints.records@[q] == s0.endpoints.records@[q]);
                    let s = s0.endpoints.records@[q].value().waiters@;
                    let i = choose|i: int| 0 <= i < s.len() && s[i] == bt;
                    assert(waiter_linked(s, s0.threads.records@, q, i));
                }
            }
            assert(s1.can_wait(0, p2, WITNESS_CHILD_SLOT));
            assert(!s1.endpoints.records@[base].value().waiters@.contains(t));
            assert(s1.threads.records@[t].value().queued != base) by {
                reveal(CapKernel::wf);
                reveal(waits_wf);
                if s1.threads.records@[t].value().queued == base {
                    assert(s1.endpoints.records@[base].value().waiters@.contains(t));
                }
            }
            assert(s1.threads.records@[t].value().state == (ThreadState::Runnable { core: 0 }));
            assert(s1.threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }));
            assert(s1.threads.records@[t].value().process == Some(process));
            assert(!s1.threads.records@[t].value().dying);
        }
        let step = self.wait(0, p2, WITNESS_CHILD_SLOT, registers);
        let ghost s2 = *self;
        proof {
            assert(step is Blocked);
            assert(Self::wait_blocked(s1, s2, 0, p2, WITNESS_CHILD_SLOT, registers));
            assert(s2.cores@[0].current_thread is None);
            assert(s2.threads.records@[bt].value().state == (ThreadState::Blocked { object: base }));
            assert(s2.threads.records@[bt].value().queued == base);
            assert(s2.threads.records@[t].value().state == (ThreadState::Runnable { core: 0 }));
            assert(s2.threads.records@[t].value().queued != base);
            assert(base != NONE) by {
                reveal(CapKernel::wf);
                assert(endpoint_wf(&s0.endpoints, &s0.blocks, base));
            }
            assert(s1.endpoints.records@[base] == s0.endpoints.records@[base]);
            assert(s1.threads.records@[bt].value().queued != base);
            assert(s2.endpoints.records@[base].value().waiters@ == s1.endpoints.records@[base].value().waiters@.push(bt));
            assert(s2.endpoints.records@[base].value().waiters@ == s0.endpoints.records@[base].value().waiters@.push(bt));
            assert(s2.endpoints.records@[base].value().head == if s0.endpoints.records@[base].value().head == NONE {
                bt
            } else {
                s0.endpoints.records@[base].value().head
            });
            assert(s2.endpoints.records@[base].value().tail == bt);
            assert(s2.endpoints.records@.dom() == s1.endpoints.records@.dom());
            assert(s2.endpoints.records@.contains_key(base));
            assert(s2.endpoints.records@[base].is_init());
            assert forall|x: usize| x != base && #[trigger] s2.endpoints.records@.contains_key(x) implies {
                &&& s2.endpoints.records@[x].is_init()
                &&& s2.endpoints.records@[x].value() == s0.endpoints.records@[x].value()
            } by {
                assert(s1.threads.records@[bt].value().queued == NONE);
                assert(x != NONE) by {
                    reveal(CapKernel::wf);
                    reveal(waits_wf);
                }
                assert(s2.endpoints.records@[x] == s1.endpoints.records@[x]);
                assert(s1.endpoints.records@[x] == s0.endpoints.records@[x]);
            }
            assert(s2.threads.records@[t].value().process == Some(process));
            assert(!s2.threads.records@[t].value().dying);
            assert(s2.cores@[0].generation < ID_GENERATION_MAX);
            assert(s2.spaces.roots@.contains_key(process));
            assert(s2.spaces.records@.contains_key(process) && s2.spaces.records@[process].value().kind is Process) by {
                reveal(CapKernel::wf);
            }
            assert(kernel_root % PAGE_SZ == 0 && mem_valid(kernel_root));
        }
        self.switch_thread(0, registers, FrameKind::Full, Some(t), kernel_root, report, Tracked(&mut steps));
        proof {
            let s3 = *self;
            assert(s3.endpoints == s2.endpoints);
            assert(s3.endpoints.records@[base] == s2.endpoints.records@[base]);
            assert(s3.cores@[0].current_thread == Some(t));
            assert(s3.cores@[0].generation <= s0.cores@[0].generation + 2);
            assert(s3.loaded(0, process));
            assert(s3.caller_live(0, process));
            assert(s3.root_live(process));
            assert(!s3.endpoints.records@[base].value().waiters@.contains(t)) by {
                reveal(CapKernel::wf);
                reveal(waits_wf);
                if s3.endpoints.records@[base].value().waiters@.contains(t) {
                    assert(s3.endpoints.records@.contains_key(base));
                    let s = s3.endpoints.records@[base].value().waiters@;
                    let i = choose|i: int| 0 <= i < s.len() && s[i] == t;
                    assert(waiter_linked(s, s3.threads.records@, base, i));
                }
            }
            assert(s3.threads.records@[t].value().queued != base) by {
                reveal(CapKernel::wf);
                reveal(waits_wf);
                if s3.threads.records@[t].value().queued == base {
                    assert(s3.endpoints.records@[base].value().waiters@.contains(t));
                }
            }
            Self::lemma_switch_and_block_all_empty(s0, s3, t, bt);
            assert(s3.threads.queues.all_empty());
            assert(!s3.threads.records@[t].value().pending_stop) by {
                reveal(current_wf);
            }
            assert forall|u: usize| u != t && u != bt && #[trigger] s0.threads.records@.contains_key(u) implies {
                &&& s3.threads.records@[u].value().state == s0.threads.records@[u].value().state
                &&& s3.threads.records@[u].value().queued == s0.threads.records@[u].value().queued
                &&& s3.threads.records@[u].value().process == s0.threads.records@[u].value().process
                &&& s3.threads.records@[u].value().placement == s0.threads.records@[u].value().placement
                &&& s3.threads.records@[u].value().dying == s0.threads.records@[u].value().dying
                &&& s3.threads.records@[u].value().pending_stop == s0.threads.records@[u].value().pending_stop
                &&& s3.threads.records@[u].value().frame == s0.threads.records@[u].value().frame
                &&& s3.threads.records@[u].value().saved == s0.threads.records@[u].value().saved
            } by {
                assert(s1.threads.records@[u].value().state == s0.threads.records@[u].value().state);
                assert(s1.threads.records@[u].value().queued == s0.threads.records@[u].value().queued);
                assert(s1.threads.records@[u].value().process == s0.threads.records@[u].value().process);
                assert(s1.threads.records@[u].value().placement == s0.threads.records@[u].value().placement);
                assert(s1.threads.records@[u].value().dying == s0.threads.records@[u].value().dying);
                assert(s1.threads.records@[u].value().pending_stop == s0.threads.records@[u].value().pending_stop);
                assert(s1.threads.records@[u].value().frame == s0.threads.records@[u].value().frame);
                assert(s1.threads.records@[u].value().saved == s0.threads.records@[u].value().saved);
                assert(s2.threads.records@[u].value().state == s1.threads.records@[u].value().state);
                assert(s2.threads.records@[u].value().queued == s1.threads.records@[u].value().queued);
                assert(s2.threads.records@[u].value().process == s1.threads.records@[u].value().process);
                assert(s2.threads.records@[u].value().placement == s1.threads.records@[u].value().placement);
                assert(s2.threads.records@[u].value().dying == s1.threads.records@[u].value().dying);
                assert(s2.threads.records@[u].value().pending_stop == s1.threads.records@[u].value().pending_stop);
                assert(s2.threads.records@[u].value().frame == s1.threads.records@[u].value().frame);
                assert(s2.threads.records@[u].value().saved == s1.threads.records@[u].value().saved);
            }
        }
    }

    /// Proves that `destroy` leaves empty run queues empty when the destroyed thread is no longer `Runnable`.
    #[verifier::spinoff_prover]
    proof fn lemma_destroy_keeps_queues_empty(s2: Self, s3: Self, bt1: usize)
        requires
            s2.wf(),
            s3.wf(),
            s2.threads.queues.all_empty(),
            Self::thread_destroyed(s2, s3, 0, bt1),
            !(s3.threads.records@[bt1].value().state is Runnable),
        ensures
            s3.threads.queues.all_empty(),
    {
        reveal(CapKernel::wf);
        reveal(queues_wf);
        assert(queues_wf(&s3.threads.queues, s3.threads.records@));
        assert(s3.threads.queues.seqs@.len() == NUM_CPUS);
        assert forall|d: int| 0 <= d < NUM_CPUS implies (#[trigger] s3.threads.queues.seqs@[d]).len() == NUM_PRIORITIES by {}
        assert forall|d: int, p: int| 0 <= d < NUM_CPUS && 0 <= p < NUM_PRIORITIES
            implies (#[trigger] s3.threads.queues.queue(d, p)) == Seq::<usize>::empty() by {
            let q = s3.threads.queues.queue(d, p);
            if q.len() > 0 {
                assert(single_queue_wf(&s3.threads.queues, s3.threads.records@, d, p));
                let u = q[0];
                assert(s3.threads.records@.contains_key(u));
                assert(s3.threads.records@[u].value().state == (ThreadState::Runnable { core: d as usize }));
                assert(u != bt1);
                assert(same_record_perm_but_links(s2.threads.records@[u], s3.threads.records@[u]));
                assert(s2.threads.records@.contains_key(u));
                assert(s2.threads.queues.queue(d, p).contains(u));
                assert(s2.threads.queues.queue(d, p).len() > 0);
            }
        }
    }

    /// Proves `s4.selected(0, bt2)` after `signal` wakes `bt2` on core 0 at priority 1 from empty queues.
    #[verifier::spinoff_prover]
    proof fn lemma_signal_skips_selected(s3: Self, s4: Self, process: usize, bt2: usize)
        requires
            s3.wf(),
            s4.wf(),
            s3.threads.queues.all_empty(),
            Self::signal_woke_at(s3, s4, process, WITNESS_BADGED_SLOT, 1),
            s4.threads.queues.queue(0, 1) == s3.threads.queues.queue(0, 1).push(bt2),
            forall|p: int| 0 <= p < NUM_PRIORITIES && p != 1
                ==> (#[trigger] s4.threads.queues.queue(0, p)) == s3.threads.queues.queue(0, p),
        ensures
            s4.threads.queues.queue(0, 1) == seq![bt2],
            s4.selected(0, bt2),
    {
        assert(s4.threads.queues.queue(0, 1) =~= seq![bt2]);
        assert forall|p: int| 0 <= p < NUM_PRIORITIES && p != 1
            implies #[trigger] s4.threads.queues.queue(0, p) == Seq::<usize>::empty() by {
            assert(s3.threads.queues.queue(0, p) == Seq::<usize>::empty());
        }
        s4.lemma_selected_alone(0, bt2);
    }

    /// Combines `witness_spawn_placed_waiter` and `witness_switch_and_block_waiter`.
    #[verifier::spinoff_prover]
    fn witness_spawn_and_block_waiter(
        &mut self,
        process: usize,
        p2: usize,
        leaf: Ghost<usize>,
        first: Ghost<Payload>,
        t: usize,
        base: usize,
        slot: usize,
        core_slot: usize,
        core_prio: Ghost<usize>,
        bt: usize,
        kernel_root: usize,
        report: Processor,
        registers: Registers,
    )
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(process),
            old(self).root_live(process),
            old(self).caller_live(0, process),
            old(self).tables.roots@.contains_key(p2),
            old(self).spaces.roots@.contains_key(process),
            old(self).spaces.roots@.contains_key(p2),
            old(self).processes.records@.contains_key(p2),
            !old(self).processes.records@[p2].value().dead,
            old(self).blocks.pages@[(p2 / PAGE_SZ) as int].refs <= 2,
            old(self).root_live(p2),
            old(self).cores@[0].current_thread == Some(t),
            old(self).cores@[0].generation + 2 <= ID_GENERATION_MAX,
            old(self).loaded(0, process),
            old(self).spaces.kernel_root@ == kernel_root,
            kernel_root % PAGE_SZ == 0,
            crate::util::page_ptr_util_u::mem_valid(kernel_root),
            report_tags_tlb(0, report),
            t != bt,
            old(self).threads.records@.contains_key(t),
            old(self).threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            old(self).threads.records@[t].value().process == Some(process),
            !old(self).threads.records@[t].value().dying,
            !old(self).threads.records@[t].value().pending_stop,
            old(self).threads.records@[t].value().queued != base,
            old(self).threads.queues.all_empty(),
            old(self).processes.records@.contains_key(process),
            !old(self).processes.records@[process].value().dead,
            old(self).tables.leaf(process, 0) == leaf@,
            leaf@ % PAGE_SZ == 0,
            leaf@ + LEAF_BYTES <= NODE_SPACE,
            base % PAGE_SZ == 0,
            (base + 2 * PAGE_SZ) as usize != leaf@,
            base + 3 * PROCESS_BYTES <= NODE_SPACE,
            old(self).tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            old(self).root_untyped(process) == (leaf@ + ROOT_UNTYPED_SLOT) as usize,
            old(self).slot_holds(process, ROOT_UNTYPED_SLOT, (leaf@ + ROOT_UNTYPED_SLOT) as usize, first@),
            old(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].live,
            old(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].depth == 1,
            first@.kind is Untyped,
            first@.rights == UNTYPED_RIGHTS,
            old(self).slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            old(self).list.nodes@[base + 2 * PAGE_SZ + 1].depth == 2,
            1 <= core_prio@ <= MAX_PRIORITY,
            old(self).tables.has_slot(&old(self).list, process, core_slot),
            old(self).slot_holds(process, core_slot, old(self).tables.node_of(process, core_slot), core_payload(0, core_prio@)),
            old(self).list.nodes@[old(self).tables.node_of(process, core_slot) as int].depth < MAX_DEPTH,
            old(self).holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT),
            old(self).notification_at(p2, WITNESS_CHILD_SLOT) == base,
            old(self).endpoints.records@.contains_key(base),
            old(self).endpoints.records@[base].value().word & SIGNAL_BITS == 0,
            old(self).blocks.pages@[(base / PAGE_SZ) as int].object is Notification,
            index_ok(slot),
            index_entry(slot) == 2,
            index_slot(slot) >= 4,
            witness_empty(*old(self), process, slot, (base + 2 * PAGE_SZ + index_slot(slot)) as usize),
            old(self).can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER),
            old(self).blocks.tracks_addr_run(bt, 2),
            old(self).blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize),
            bt % THREAD_BYTES == 0,
            bt / PAGE_SZ >= base / PAGE_SZ + 18,
            !old(self).threads.records@.contains_key(bt),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            final(self).tables.roots == old(self).tables.roots,
            Self::waiter_tables_kept(*old(self), *final(self)),
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces.roots == old(self).spaces.roots,
            final(self).cores@[0].current_thread == Some(t),
            final(self).cores@[0].generation <= old(self).cores@[0].generation + 2,
            final(self).loaded(0, process),
            final(self).caller_live(0, process),
            final(self).root_live(process),
            final(self).root_live(p2),
            final(self).threads.queues.all_empty(),
            final(self).root_untyped(process) == (leaf@ + ROOT_UNTYPED_SLOT) as usize,
            final(self).slot_holds(process, ROOT_UNTYPED_SLOT, (leaf@ + ROOT_UNTYPED_SLOT) as usize, first@),
            final(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].live,
            final(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].depth == 1,
            final(self).slot_holds(process, WITNESS_PROCESS_SLOT, (base + 2 * PAGE_SZ + 1) as usize, process_of(p2)),
            final(self).list.nodes@[base + 2 * PAGE_SZ + 1].depth == 2,
            final(self).slot_holds(process, core_slot, old(self).tables.node_of(process, core_slot), core_payload(0, core_prio@)),
            final(self).list.nodes@[old(self).tables.node_of(process, core_slot) as int].depth
                == old(self).list.nodes@[old(self).tables.node_of(process, core_slot) as int].depth,
            final(self).holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT),
            final(self).notification_at(p2, WITNESS_CHILD_SLOT) == base,
            final(self).slot_holds(process, slot, (base + 2 * PAGE_SZ + index_slot(slot)) as usize, thread_of(bt)),
            final(self).list.childless((base + 2 * PAGE_SZ + index_slot(slot)) as usize),
            final(self).list.nodes@[(base + 2 * PAGE_SZ + index_slot(slot)) as int].depth == 2,
            final(self).blocks.pages@[(p2 / PAGE_SZ) as int].refs == old(self).blocks.pages@[(p2 / PAGE_SZ) as int].refs + 1,
            final(self).blocks.pages@[(bt / PAGE_SZ) as int].refs == 1,
            forall|s: usize, node: usize| s != slot && witness_empty(*old(self), process, s, node)
                ==> #[trigger] witness_empty(*final(self), process, s, node),
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            final(self).flush_epoch == old(self).flush_epoch,
            forall|j: int| 0 <= j < old(self).blocks.pages@.len() && j != p2 / PAGE_SZ && j != bt / PAGE_SZ && j != bt / PAGE_SZ + 1
                ==> #[trigger] final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            final(self).threads.records@.dom() == old(self).threads.records@.dom().insert(bt),
            final(self).threads.records@[t].value().placement == Some(Placement { core: 0, priority: 0 }),
            final(self).threads.records@[t].value().process == Some(process),
            !final(self).threads.records@[t].value().dying,
            !final(self).threads.records@[t].value().pending_stop,
            final(self).threads.records@[t].value().queued != base,
            final(self).threads.records@[bt].value().state == (ThreadState::Blocked { object: base }),
            final(self).threads.records@[bt].value().queued == base,
            final(self).threads.records@[bt].value().process == Some(p2),
            final(self).threads.records@[bt].value().placement == Some(Placement { core: 0, priority: 1 }),
            !final(self).threads.records@[bt].value().dying,
            !final(self).threads.records@[bt].value().pending_stop,
            final(self).threads.records@[bt].value().frame == partial_frame(registers),
            final(self).threads.records@[bt].value().saved is Partial,
            forall|u: usize| u != t && u != bt && #[trigger] old(self).threads.records@.contains_key(u) ==> {
                &&& final(self).threads.records@[u].value().state == old(self).threads.records@[u].value().state
                &&& final(self).threads.records@[u].value().queued == old(self).threads.records@[u].value().queued
                &&& final(self).threads.records@[u].value().process == old(self).threads.records@[u].value().process
                &&& final(self).threads.records@[u].value().placement == old(self).threads.records@[u].value().placement
                &&& final(self).threads.records@[u].value().dying == old(self).threads.records@[u].value().dying
                &&& final(self).threads.records@[u].value().pending_stop == old(self).threads.records@[u].value().pending_stop
                &&& final(self).threads.records@[u].value().frame == old(self).threads.records@[u].value().frame
                &&& final(self).threads.records@[u].value().saved == old(self).threads.records@[u].value().saved
            },
            final(self).endpoints.records@.dom() == old(self).endpoints.records@.dom(),
            final(self).endpoints.records@.contains_key(base),
            final(self).endpoints.records@[base].is_init(),
            forall|x: usize| x != base && #[trigger] final(self).endpoints.records@.contains_key(x) ==> {
                &&& final(self).endpoints.records@[x].is_init()
                &&& final(self).endpoints.records@[x].value() == old(self).endpoints.records@[x].value()
            },
            final(self).endpoints.records@[base].value().word == (old(self).endpoints.records@[base].value().word | WAITER_BIT),
            final(self).endpoints.records@[base].value().waiters@ == old(self).endpoints.records@[base].value().waiters@.push(bt),
            final(self).endpoints.records@[base].value().head == if old(self).endpoints.records@[base].value().head == NONE {
                bt
            } else {
                old(self).endpoints.records@[base].value().head
            },
            final(self).endpoints.records@[base].value().tail == bt,
            forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0 && k != 1
                ==> !(#[trigger] final(self).list.nodes@[bt + k]).live,
            final(self).list.is_child((base + 2 * PAGE_SZ + 1) as usize, bt),
            final(self).list.is_child(old(self).tables.node_of(process, core_slot), (bt + 1) as usize),
            final(self).list.nodes@[(bt + 1) as int].kind is Placement,
            final(self).list.childless((bt + 1) as usize),
            forall|x: usize| #[trigger] old(self).list.is_child(old(self).tables.node_of(process, core_slot), x)
                ==> final(self).list.is_child(old(self).tables.node_of(process, core_slot), x),
            forall|x: usize| #[trigger] final(self).list.is_child(old(self).tables.node_of(process, core_slot), x)
                ==> x == (bt + 1) as usize || old(self).list.is_child(old(self).tables.node_of(process, core_slot), x),
            forall|k: int| 0 <= k < NODE_SPACE && k != (base + 2 * PAGE_SZ + index_slot(slot)) && k != bt && k != bt + 1 ==> {
                &&& (#[trigger] final(self).list.nodes@[k]).live == old(self).list.nodes@[k].live
                &&& old(self).list.valid(k as usize) ==> (
                    final(self).list.nodes@[k].kind == old(self).list.nodes@[k].kind
                    && final(self).list.nodes@[k].depth == old(self).list.nodes@[k].depth
                )
            },
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost s0 = *self;
        self.witness_spawn_placed_waiter(process, p2, leaf, first, base, slot, core_slot, core_prio, bt);
        let ghost s1 = *self;
        proof {
            let ghost n = s0.tables.node_of(p2, WITNESS_CHILD_SLOT);
            s0.lemma_slot(p2, WITNESS_CHILD_SLOT);
            s0.lemma_slot_bound(n);
            assert(s0.list.nodes@[n as int].live);
            assert(!s0.list.nodes@[((base + 2 * PAGE_SZ + index_slot(slot)) as usize) as int].live);
            assert(n != (base + 2 * PAGE_SZ + index_slot(slot)) as usize);
            assert(bt % PAGE_SZ == 0) by (nonlinear_arith)
                requires bt % THREAD_BYTES == 0, THREAD_BYTES == 2 * PAGE_SZ;
            assert(((bt + 1) as int) / (PAGE_SZ as int) == (bt as int) / (PAGE_SZ as int)) by (nonlinear_arith)
                requires bt % THREAD_BYTES == 0, THREAD_BYTES == 2 * PAGE_SZ, PAGE_SZ > 1;
            assert(order_pages(THREAD_ORDER as usize) == 2) by (compute_only);
            assert(s0.blocks.pages@[(bt / PAGE_SZ) as int + 0].kind is Free);
            assert(s0.blocks.pages@[(bt / PAGE_SZ) as int].kind is Free);
            assert(page_of(n) / PAGE_SZ != bt / PAGE_SZ) by {
                reveal(CapKernel::wf);
                reveal(Tables::leaves_wf);
                assert(s0.tables.owner@.contains_key(page_of(n)));
                assert(s0.list.pages@.dom().contains(page_of(n)));
            }
            assert(n / PAGE_SZ == page_of(n) / PAGE_SZ);
            assert(n != bt && n != bt + 1);
            assert(s1.holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT)
                && s1.notification_at(p2, WITNESS_CHILD_SLOT) == base
                && s1.root_live(p2)
                && s1.processes.records@.contains_key(process)
                && !s1.processes.records@[process].value().dead
                && s1.processes.records@.contains_key(p2)
                && !s1.processes.records@[p2].value().dead) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert(s0.blocks.pages@[(p2 / PAGE_SZ) as int].object is Process) by {
                reveal(CapKernel::wf);
            }
            assert(base / PAGE_SZ != p2 / PAGE_SZ && base / PAGE_SZ != bt / PAGE_SZ && base / PAGE_SZ != bt / PAGE_SZ + 1);
            assert(s1.blocks.pages@[(base / PAGE_SZ) as int] == s0.blocks.pages@[(base / PAGE_SZ) as int]);
        }
        self.witness_switch_and_block_waiter(process, p2, t, base, bt, kernel_root, report, registers);
        proof {
            let ghost s2 = *self;
            assert(Self::waiter_tables_kept(s0, s2)) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert forall|s: usize, node: usize| s != slot && witness_empty(s0, process, s, node)
                implies #[trigger] witness_empty(s2, process, s, node) by {
                assert(witness_empty(s1, process, s, node));
            }
        }
    }

    /// From the state boot leaves, as the root at `process`, with three free order-3 blocks past
    /// those boot's tables at `base`, `base + PROCESS_BYTES`, and `base + 2 * PROCESS_BYTES`: enter
    /// root thread `t` on core 0, retype notification `base` and child process `p2`, spawn two
    /// secondary threads `bt1` (`base + 18 * PAGE_SZ`) and `bt2` (`base + 20 * PAGE_SZ`) bound to
    /// `p2` and block both in order (`waiters == [bt1, bt2]`) on `base`, destroy `bt1` so the
    /// queue's head is stale (`Dead` yet still listed), and signal `base` through the badged send
    /// capability. The destroy leaves `bt1` listed as the queue's stale head; `signal` skips and
    /// removes `bt1` (clearing `bt1`'s queue links), wakes `bt2` into `Runnable` on core 0 with
    /// `wait_outcome(2^62)` in its saved frame and clears `base`'s word and queue, and `tick`
    /// switches `bt2` onto core 0.
    #[verifier::spinoff_prover]
    pub fn witness_signal_skips_stale_notification_waiter(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: usize,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        kernel_root: usize,
        base: usize,
        report: Processor,
        registers: Registers,
    ) -> (ret: (bool, bool, bool, TickStep, (FrameKind, Registers)))
        requires
            old(self).booted(root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@, kernel_root),
            image_tables_bound(image@) + 3 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            report_tags_tlb(0, report),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            ret.0,
            ret.1,
            ret.2,
            ret.3 is Switched,
            ret.4 == (FrameKind::Partial, outcome_written(partial_frame(registers), wait_outcome(0x4000_0000_0000_0000u64))), // not a page size: bit 62 of the word
            ({
                let bt2 = (base + 20 * PAGE_SZ) as usize;
                &&& final(self).wf()
                &&& final(self).endpoints.records@[base].value().waiters@ == Seq::<usize>::empty()
                &&& final(self).endpoints.records@[base].value().word == 0
                &&& final(self).cores@[0].current_thread == Some(bt2)
            }),
    {
        hide(CapKernel::wf);
        hide(CapKernel::booted);
        hide(BlockTable::counts_wf);
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        self.witness_setup_waiter_process(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root, base, report);
        let p2 = base + PROCESS_BYTES;
        let b3 = p2 + PROCESS_BYTES;
        let bt1 = b3 + 2 * PAGE_SZ;
        let bt2 = b3 + 4 * PAGE_SZ;
        let ghost s0 = *self;
        proof {
            assert((0u64 & SIGNAL_BITS) == 0u64) by (compute_only);
            assert((WAITER_BIT & SIGNAL_BITS) == 0u64) by (compute_only);
        }
        self.witness_spawn_and_block_waiter(
            process, p2, leaf, Ghost(first), t, base, WITNESS_STALE_THREAD_SLOT, ROOT_CORE_SLOT, Ghost(MAX_PRIORITY),
            bt1, kernel_root, report, registers,
        );
        let ghost s1 = *self;
        proof {
            assert((0u64 | WAITER_BIT) == WAITER_BIT) by (bit_vector)
                requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert(s1.endpoints.records@[base].value().waiters@ == seq![bt1]);
            assert(s1.endpoints.records@[base].value().word == WAITER_BIT);
            assert(s1.blocks.pages@[(p2 / PAGE_SZ) as int].refs == 2);
            assert(index_slot(WITNESS_STALE_THREAD_SLOT) == 4) by (compute_only);
            assert(s1.slot_holds(process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize, thread_of(bt1)));
            assert(s1.threads.records@.contains_key(bt1));
            assert(s1.threads.records@[bt1].value().state == (ThreadState::Blocked { object: base }));
            assert(!s1.threads.records@[bt1].value().dying);
            assert(s1.threads.records@[bt1].value().process == Some(p2));
            assert(!s1.blocks.covered((bt2 / PAGE_SZ) as int)) by {
                reveal(CapKernel::wf);
                assert(s1.blocks.tracks((bt2 / PAGE_SZ) as int));
                assert(0 <= region_2m((bt2 / PAGE_SZ) as int) < s1.blocks.num_2m());
                assert(0 <= region_1g((bt2 / PAGE_SZ) as int) < s1.blocks.num_1g());
            }
            assert(s1.blocks.small_free((bt2 / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s1.blocks.pages@[bt2 / PAGE_SZ + k].kind is Free by {
                    assert(bt2 / PAGE_SZ + k != p2 / PAGE_SZ && bt2 / PAGE_SZ + k != bt1 / PAGE_SZ && bt2 / PAGE_SZ + k != bt1 / PAGE_SZ + 1);
                }
            }
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, bt2, THREAD_ORDER));
            assert(1usize < MAX_DEPTH) by (compute_only);
            assert(s1.root_untyped(process) == s0.root_untyped(process)
                && s1.tables.leaf(process, 0) == leaf@
                && s1.tables.leaf(process, 2) == s0.tables.leaf(process, 2)
                && s1.processes.records@.contains_key(process)
                && !s1.processes.records@[process].value().dead
                && s1.processes.records@.contains_key(p2)
                && !s1.processes.records@[p2].value().dead
                && s1.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT)
                && s1.notification_at(process, WITNESS_BADGED_SLOT) == base
                && s1.payload_of(s1.tables.node_of(process, WITNESS_BADGED_SLOT)).badge == 0x4000_0000_0000_0000 // not a page size: bit 62 of the word
                && s1.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT)
                && s1.notification_at(process, WITNESS_FRAME_SLOT) == base
                && s1.holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT)
                && s1.notification_at(p2, WITNESS_CHILD_SLOT) == base) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, bt2, THREAD_ORDER));
        }
        self.witness_spawn_and_block_waiter(
            process, p2, leaf, Ghost(first), t, base, WITNESS_LIVE_THREAD_SLOT, ROOT_CORE_SLOT, Ghost(MAX_PRIORITY),
            bt2, kernel_root, report, registers,
        );
        let ghost s2 = *self;
        proof {
            assert((0u64 | WAITER_BIT) == WAITER_BIT) by (bit_vector)
                requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert((WAITER_BIT | WAITER_BIT) == WAITER_BIT) by (bit_vector)
                requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert(seq![bt1].push(bt2) =~= seq![bt1, bt2]);
            assert(s2.endpoints.records@[base].value().waiters@ == seq![bt1, bt2]);
            assert(s2.endpoints.records@[base].value().head == bt1);
            assert(s2.endpoints.records@[base].value().word == WAITER_BIT);
            assert(bt1 != t && bt1 != bt2) by {
                assert(PROCESS_BYTES == 8 * PAGE_SZ);
            }
            assert(index_slot(WITNESS_LIVE_THREAD_SLOT) == 5) by (compute_only);
            assert((base + 2 * PAGE_SZ + 4) as int != (base + 2 * PAGE_SZ + 5) as int);
            assert((base + 2 * PAGE_SZ + 4) as int != bt2 as int && (base + 2 * PAGE_SZ + 4) as int != (bt2 + 1) as int) by {
                assert(PROCESS_BYTES == 8 * PAGE_SZ);
            }
            assert(s2.slot_holds(process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize, thread_of(bt1))
                && s2.processes.records@.contains_key(p2)
                && !s2.processes.records@[p2].value().dead
                && s2.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT)
                && s2.notification_at(process, WITNESS_BADGED_SLOT) == base
                && s2.payload_of(s2.tables.node_of(process, WITNESS_BADGED_SLOT)).badge == 0x4000_0000_0000_0000 // not a page size: bit 62 of the word
                && s2.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT)
                && s2.notification_at(process, WITNESS_FRAME_SLOT) == base) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert(s2.threads.records@[bt1].value().state == (ThreadState::Blocked { object: base }));
            assert(!s2.threads.records@[bt1].value().dying);
            assert(s2.threads.records@[bt1].value().process == Some(p2));
            assert(!s2.cap_dead((base + 2 * PAGE_SZ + 4) as usize));
            assert(THREAD_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s2.can_destroy(process, WITNESS_STALE_THREAD_SLOT));
            assert(s2.threads.records@.contains_key(bt2));
            assert(s2.threads.records@[bt2].value().state == (ThreadState::Blocked { object: base }));
            assert(s2.threads.records@[bt2].value().placement == Some(Placement { core: 0, priority: 1 }));
        }
        let tracked mut steps = Steps::fresh();
        let destroyed = self.destroy(0, process, WITNESS_STALE_THREAD_SLOT, Tracked(&mut steps));
        let ghost s3 = *self;
        proof {
            assert(destroyed);
            assert(Self::thread_destroyed(s2, s3, 0, bt1));
            assert(s3.threads.records@.contains_key(bt2));
            assert(same_record_perm_but_links(s2.threads.records@[bt2], s3.threads.records@[bt2]));
            assert(s3.threads.records@[bt1].value().state is Dead);
            assert(s3.threads.records@[bt1].value().queued == base);
            assert(s3.threads.records@[bt2].value().state == (ThreadState::Blocked { object: base }));
            assert(s3.threads.records@[bt2].value().placement == Some(Placement { core: 0, priority: 1 }));
            assert(s3.endpoints.records@[base].value().waiters@ == seq![bt1, bt2]);
            assert(s3.endpoints.records@[base].value().word == WAITER_BIT);
            assert(s3.endpoints.records@[base].value().waiters@[0] == bt1);
            assert(s3.endpoints.records@[base].value().waiters@[1] == bt2);
            assert(s3.stale_prefix(base, 1, (SIGNAL_STALE_BUDGET - 1) as nat) == 0);
            assert(s3.stale_prefix(base, 0, SIGNAL_STALE_BUDGET as nat) == 1);
            Self::lemma_destroy_keeps_queues_empty(s2, s3, bt1);
            assert(s3.threads.queues.all_empty());
            assert(s3.can_signal(process, WITNESS_BADGED_SLOT));
        }
        let tracked mut sig_steps = Steps::fresh();
        let signalled = self.signal(process, WITNESS_BADGED_SLOT, Tracked(&mut sig_steps));
        let ghost s4 = *self;
        proof {
            assert(signalled);
            assert(Self::signalled(s3, s4, process, WITNESS_BADGED_SLOT));
            assert(Self::signal_woke_at(s3, s4, process, WITNESS_BADGED_SLOT, 1));
            let badge: u64 = 0x4000_0000_0000_0000u64; // not a page size: bit 62 of the word
            assert(((WAITER_BIT | badge) & SIGNAL_BITS) == badge) by (bit_vector)
                requires
                    badge == 0x4000_0000_0000_0000u64, // not a page size: bit 62 of the word
                    WAITER_BIT == 0x8000_0000_0000_0000u64, // not a page size: WAITER_BIT
                    SIGNAL_BITS == 0x7fff_ffff_ffff_ffffu64; // not a page size: SIGNAL_BITS
            assert(s4.endpoints.records@[base].value().waiters@ =~= Seq::<usize>::empty());
            assert(s4.endpoints.records@[base].value().word == 0);
            assert(s4.threads.records@[bt1].value().state is Dead);
            assert(s4.threads.records@[bt1].value().queued == NONE);
            assert(s4.threads.records@[bt1].value().wait_prev == NONE);
            assert(s4.threads.records@[bt1].value().wait_next == NONE);
            assert(s4.threads.records@[bt2].value().state == (ThreadState::Runnable { core: 0 }));
            assert(s4.threads.records@[bt2].value().queued == NONE);
            assert(s4.threads.records@[bt2].value().frame
                == outcome_written(partial_frame(registers), wait_outcome(0x4000_0000_0000_0000u64))); // not a page size: bit 62 of the word
            assert(s4.threads.records@[bt2].value().saved is Partial);
            assert(!s4.must_leave(0));
            assert(s4.threads.queues.queue(0, 1) == s3.threads.queues.queue(0, 1).push(bt2));
            assert forall|p: int| 0 <= p < NUM_PRIORITIES && p != 1
                implies (#[trigger] s4.threads.queues.queue(0, p)) == s3.threads.queues.queue(0, p) by {}
            Self::lemma_signal_skips_selected(s3, s4, process, bt2);
            assert(s4.selected(0, bt2));
            assert(s4.preempts(0, bt2));
            assert(s4.can_run(bt2));
            assert(s4.cores@[0].generation < ID_GENERATION_MAX);
            reveal(CapKernel::wf);
            assert(thread_wf(&s4.list, &s4.threads, &s4.blocks, bt1));
            assert(thread_wf(&s4.list, &s4.threads, &s4.blocks, bt2));
        }
        let stale_rec = *crate::pptr::PPtr::<ThreadRecord>::from_usize(bt1 + THREAD_RECORD_PAGE * PAGE_SZ).borrow(
            Tracked(self.threads.records.borrow().tracked_borrow(bt1)),
        );
        let stale_unlinked = stale_rec.queued == NONE && stale_rec.wait_prev == NONE && stale_rec.wait_next == NONE;
        let record = crate::pptr::PPtr::<ThreadRecord>::from_usize(bt2 + THREAD_RECORD_PAGE * PAGE_SZ).borrow(
            Tracked(self.threads.records.borrow().tracked_borrow(bt2)),
        );
        let resumed = record.resume_frame();
        let tracked mut tick_steps = Steps::fresh();
        let tick_step = self.tick(0, registers, kernel_root, report, Tracked(&mut tick_steps));
        proof {
            let s5 = *self;
            assert(tick_step is Switched);
            assert(Self::switched(s4, s5, 0, registers, bt2));
            assert(s5.cores@[0].current_thread == Some(bt2));
            assert(bt2 == (base + 20 * PAGE_SZ) as usize);
        }
        (destroyed, signalled, stale_unlinked, tick_step, resumed)
    }

    /// From the state boot leaves, with three free order-3 blocks at `base`, `base + PROCESS_BYTES`,
    /// and `base + 2 * PROCESS_BYTES`: spawn and block `bt1` (`base + 18 * PAGE_SZ`) alone on
    /// notification `base` (`word == WAITER_BIT`), destroy `bt1`, and signal `base` with badge `2^62`.
    /// `signal` removes the solo stale waiter `bt1`, clears `WAITER_BIT` (bit 63), and sets word to
    /// `2^62`; root `t`'s subsequent `wait` therefore returns `Returned(2^62)` at once without
    /// blocking behind the dead thread and leaves `base`'s word zero.
    #[verifier::spinoff_prover]
    pub fn witness_signal_clears_stale_waiter_bit(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: usize,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        kernel_root: usize,
        base: usize,
        report: Processor,
        registers: Registers,
    ) -> (ret: (bool, bool, WaitStep))
        requires
            old(self).booted(root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@, kernel_root),
            image_tables_bound(image@) + 3 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            report_tags_tlb(0, report),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            ret.0,
            ret.1,
            ret.2 == WaitStep::Returned(0x4000_0000_0000_0000u64), // not a page size: bit 62 of the word
            final(self).wf(),
            final(self).endpoints.records@[base].value().waiters@ == Seq::<usize>::empty(),
            final(self).endpoints.records@[base].value().word == 0,
            final(self).threads.records@[(base + 18 * PAGE_SZ) as usize].value().queued == NONE,
    {
        hide(CapKernel::wf);
        hide(CapKernel::booted);
        hide(BlockTable::counts_wf);
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        self.witness_setup_waiter_process(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root, base, report);
        let p2 = base + PROCESS_BYTES;
        let b3 = p2 + PROCESS_BYTES;
        let bt1 = b3 + 2 * PAGE_SZ;
        proof {
            assert((0u64 & SIGNAL_BITS) == 0u64) by (compute_only);
            assert((WAITER_BIT & SIGNAL_BITS) == 0u64) by (compute_only);
        }
        self.witness_spawn_and_block_waiter(
            process, p2, leaf, Ghost(first), t, base, WITNESS_STALE_THREAD_SLOT, ROOT_CORE_SLOT, Ghost(MAX_PRIORITY),
            bt1, kernel_root, report, registers,
        );
        let ghost s1 = *self;
        proof {
            assert((0u64 | WAITER_BIT) == WAITER_BIT) by (bit_vector)
                requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert(THREAD_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s1.slot_holds(process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize, thread_of(bt1))
                && s1.processes.records@.contains_key(p2)
                && !s1.processes.records@[p2].value().dead
                && s1.holds_notification(process, WITNESS_BADGED_SLOT, SEND_RIGHT)
                && s1.notification_at(process, WITNESS_BADGED_SLOT) == base
                && s1.payload_of(s1.tables.node_of(process, WITNESS_BADGED_SLOT)).badge == 0x4000_0000_0000_0000 // not a page size: bit 62 of the word
                && s1.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT)
                && s1.notification_at(process, WITNESS_FRAME_SLOT) == base) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert(s1.can_destroy(process, WITNESS_STALE_THREAD_SLOT));
        }
        let tracked mut steps = Steps::fresh();
        let destroyed = self.destroy(0, process, WITNESS_STALE_THREAD_SLOT, Tracked(&mut steps));
        let ghost s2 = *self;
        proof {
            assert(destroyed);
            assert(s2.threads.records@[bt1].value().state is Dead);
            assert(s2.endpoints.records@[base].value().waiters@ == seq![bt1]);
            assert(s2.endpoints.records@[base].value().word == WAITER_BIT);
            assert(s2.stale_prefix(base, 1, (SIGNAL_STALE_BUDGET - 1) as nat) == 0);
            assert(SIGNAL_STALE_BUDGET >= 2) by (compute_only);
            assert(s2.stale_prefix(base, 0, SIGNAL_STALE_BUDGET as nat) == 1);
            assert(s2.can_signal(process, WITNESS_BADGED_SLOT));
        }
        let tracked mut sig_steps = Steps::fresh();
        let signalled = self.signal(process, WITNESS_BADGED_SLOT, Tracked(&mut sig_steps));
        let ghost s3 = *self;
        proof {
            assert(signalled);
            let badge: u64 = 0x4000_0000_0000_0000u64; // not a page size: bit 62 of the word
            assert(((WAITER_BIT & !WAITER_BIT) | badge) == badge) by (bit_vector)
                requires
                    badge == 0x4000_0000_0000_0000u64, // not a page size: bit 62 of the word
                    WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert((badge & SIGNAL_BITS) == badge && (badge & !SIGNAL_BITS) == 0) by (bit_vector)
                requires
                    badge == 0x4000_0000_0000_0000u64, // not a page size: bit 62 of the word
                    SIGNAL_BITS == 0x7fff_ffff_ffff_ffffu64; // not a page size: SIGNAL_BITS
            assert(s3.endpoints.records@[base].value().waiters@ =~= Seq::<usize>::empty());
            assert(s3.endpoints.records@[base].value().word == badge);
            assert(s3.threads.records@[bt1].value().queued == NONE);
            assert(s3.tables == s2.tables && s3.list == s2.list && s3.processes == s2.processes);
            assert(s3.cores == s2.cores);
            assert(s3.threads.records@[t] == s2.threads.records@[t]);
            assert(s3.caller_live(0, process));
            assert(s3.holds_notification(process, WITNESS_FRAME_SLOT, RECEIVE_RIGHT));
            assert(s3.notification_at(process, WITNESS_FRAME_SLOT) == base);
            assert(s3.wait_signalled(process, WITNESS_FRAME_SLOT));
        }
        let waited = self.wait(0, process, WITNESS_FRAME_SLOT, registers);
        proof {
            let s4 = *self;
            assert(waited == WaitStep::Returned(0x4000_0000_0000_0000u64)); // not a page size: bit 62 of the word
            assert(s4.endpoints.records@[base].value().waiters@ == Seq::<usize>::empty());
            assert(s4.endpoints.records@[base].value().word == 0);
            assert(s4.threads.records@[bt1] == s3.threads.records@[bt1]);
            assert(bt1 == (base + 18 * PAGE_SZ) as usize);
        }
        (destroyed, signalled, waited)
    }

    /// Helper for `witness_destroyed_queued_thread_freed`: revokes the child core cap at
    /// `WITNESS_LIVE_THREAD_SLOT` to drop `bt1`'s placement node, deletes `bt1`'s capability, and
    /// runs `reclaim` twice (`Slice` to unbind `bt1`, then `Freed` to unlink `bt1` from `base` and
    /// free `bt1`'s block).
    #[verifier::spinoff_prover]
    fn witness_teardown_destroyed_queued_thread(
        &mut self,
        process: usize,
        p2: usize,
        leaf: Ghost<usize>,
        first: Ghost<Payload>,
        base: usize,
        bt1: usize,
    ) -> (ret: (Option<Payload>, ReclaimStep, ReclaimStep))
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(process),
            old(self).root_live(process),
            old(self).tables.roots@.contains_key(p2),
            old(self).processes.records@.contains_key(p2),
            old(self).threads.records@.contains_key(bt1),
            old(self).threads.records@[bt1].value().state is Dead,
            old(self).threads.records@[bt1].value().queued == base,
            old(self).threads.records@[bt1].value().wait_prev == NONE,
            old(self).threads.records@[bt1].value().wait_next == NONE,
            old(self).threads.records@[bt1].value().process == Some(p2),
            old(self).endpoints.records@.contains_key(base),
            old(self).endpoints.records@[base].value().waiters@ == seq![bt1],
            old(self).endpoints.records@[base].value().word == WAITER_BIT,
            base % PAGE_SZ == 0,
            base + 3 * PROCESS_BYTES <= NODE_SPACE,
            old(self).tables.leaf(process, 0) == leaf@,
            leaf@ % PAGE_SZ == 0,
            old(self).tables.leaf(process, 2) == (base + 2 * PAGE_SZ) as usize,
            old(self).blocks.pages@[(bt1 / PAGE_SZ) as int].refs == 1,
            old(self).root_untyped(process) == (leaf@ + ROOT_UNTYPED_SLOT) as usize,
            old(self).slot_holds(process, ROOT_UNTYPED_SLOT, (leaf@ + ROOT_UNTYPED_SLOT) as usize, first@),
            old(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].live,
            old(self).list.nodes@[(leaf@ + ROOT_UNTYPED_SLOT) as int].depth == 1,
            first@.kind is Untyped,
            first@.rights == UNTYPED_RIGHTS,
            old(self).slot_holds(process, WITNESS_STALE_THREAD_SLOT, (base + 2 * PAGE_SZ + 4) as usize, thread_of(bt1)),
            old(self).list.childless((base + 2 * PAGE_SZ + 4) as usize),
            old(self).list.nodes@[(base + 2 * PAGE_SZ + 4) as int].depth == 2,
            old(self).slot_holds(process, WITNESS_LIVE_THREAD_SLOT, (base + 2 * PAGE_SZ + 5) as usize, core_payload(0, 1)),
            forall|x: usize| #[trigger] old(self).list.is_child((base + 2 * PAGE_SZ + 5) as usize, x)
                <==> x == (bt1 + 1) as usize,
            old(self).list.nodes@[(bt1 + 1) as int].kind is Placement,
            forall|x: usize| !#[trigger] old(self).list.is_child((bt1 + 1) as usize, x),
            forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0 && k != 1
                ==> !(#[trigger] old(self).list.nodes@[bt1 + k]).live,
            bt1 % THREAD_BYTES == 0,
            bt1 / PAGE_SZ == base / PAGE_SZ + 18,
            old(self).can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER),
            old(self).flush_epoch == 0,
            old(self).stale_epoch.pages@[(bt1 / PAGE_SZ) as int] == 0,
            old(self).stale_epoch.pages@[(bt1 / PAGE_SZ + 1) as int] == 0,
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            ret.0 is Some,
            ret.1 is Slice,
            ret.2 is Freed,
            final(self).wf(),
            !final(self).threads.records@.contains_key(bt1),
            final(self).endpoints.records@.contains_key(base),
            final(self).endpoints.records@[base].value().waiters@ == Seq::<usize>::empty(),
            (final(self).endpoints.records@[base].value().word & WAITER_BIT) == 0,
            final(self).blocks.pages@[(bt1 / PAGE_SZ) as int].kind is Free,
            final(self).blocks.pages@[bt1 / PAGE_SZ + 1int].kind is Free,
    {
        hide(CapKernel::wf);
        hide(BlockTable::counts_wf);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost lb = (base + 2 * PAGE_SZ) as usize;
        let ghost nc = (lb + 5) as usize;
        let ghost nt = (lb + 4) as usize;
        let at_core = Position { through: None, index: WITNESS_LIVE_THREAD_SLOT };
        let at_thread = Position { through: None, index: WITNESS_STALE_THREAD_SLOT };
        let ghost s3 = *self;
        proof {
            assert(s3.cap_at(process, at_core) == Some(nc));
            assert(s3.list.is_child(nc, (bt1 + 1) as usize));
            assert(s3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s3.tables.leaf(process, 2) == lb);
        }
        let tracked mut steps = Steps::fresh();
        let revoked = self.revoke(process, at_core, Tracked(&mut steps));
        let ghost s4 = *self;
        proof {
            assert(!(revoked is Refused));
            assert(s4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let gone = choose|gone: Seq<usize>| revoked_seq(s3.list, s4.list, nc, gone);
            assert forall|i: int| 0 <= i < gone.len() implies #[trigger] gone[i] == (bt1 + 1) as usize by {
                let x = gone[i];
                assert forall|y: usize, z: usize| #[trigger] s3.list.is_child(nc, y) implies !#[trigger] s3.list.is_child(y, z) by {
                    assert(y == (bt1 + 1) as usize);
                }
                lemma_below_child(s3.list, nc, x);
            }
            if gone.len() > 1 {
                assert(gone[0] == (bt1 + 1) as usize && gone[1] == (bt1 + 1) as usize && gone[0] != gone[1]);
            }
            assert(s3.list.seq@.len() - s4.list.seq@.len() <= 1);
            assert(s4.flush_epoch <= 1);
            assert(revoked is Done);
            assert(Self::cap_revoked_at(s3, s4, process, at_core));
            assert(!s4.list.nodes@[bt1 + 1].live) by {
                if s4.list.nodes@[bt1 + 1].live {
                    s4.list.lemma_live_valid((bt1 + 1) as usize);
                    s4.list.lemma_link(0);
                    crate::capability::list::lemma_has(s4.list.seq@, (bt1 + 1) as usize);
                    let k = choose|k: int| 0 <= k < s4.list.seq@.len() && s4.list.seq@[k] == (bt1 + 1) as usize;
                    s4.list.lemma_link(k);
                    assert(s4.list.seq@[k] == (bt1 + 1) as usize);
                    assert(s4.list.seq@.contains((bt1 + 1) as usize));
                    assert(s3.list.is_child(nc, (bt1 + 1) as usize));
                    assert(s3.list.nodes@[nc as int].depth + 1 == s3.list.nodes@[(bt1 + 1) as int].depth) by {
                        crate::capability::list::lemma_has(s3.list.seq@, (bt1 + 1) as usize);
                        let j = choose|j: int| 0 <= j < s3.list.seq@.len() && s3.list.seq@[j] == (bt1 + 1) as usize;
                        s3.list.lemma_link(j);
                    }
                    assert(s4.list.nodes@[(bt1 + 1) as int].depth == s3.list.nodes@[(bt1 + 1) as int].depth);
                    assert(((bt1 + 1) as usize) != s4.list.seq@[0]);
                    assert(s4.list.parent@[(bt1 + 1) as usize] == nc);
                    assert(s4.list.is_child(nc, (bt1 + 1) as usize));
                }
            }
            assert(s4.list.nodes@[bt1 as int].live) by {
                assert(s3.list.nodes@[bt1 as int].live) by {
                    reveal(CapKernel::wf);
                }
                assert(!gone.contains(bt1)) by {
                    if gone.contains(bt1) {
                        let i = choose|i: int| 0 <= i < gone.len() && gone[i] == bt1;
                        assert(gone[i] == (bt1 + 1) as usize);
                    }
                }
                lemma_revoke_took_only(s3.list, s4.list, nc, gone, bt1);
            }
            assert(Self::threads_revoked(s3, s4));
            assert(s4.threads.records@[bt1].value().state is Dead);
            assert(s4.threads.records@[bt1].value().queued == base);
            assert(s4.threads.records@[bt1].value().wait_prev == NONE);
            assert(s4.threads.records@[bt1].value().wait_next == NONE);
            assert(s4.endpoints.records@.contains_key(base) && s4.endpoints.records@[base].value().waiters@ == seq![bt1]) by {
                reveal(CapKernel::wf);
                reveal(waits_wf);
                assert(s4.threads.records@.contains_key(bt1));
                let s = s4.endpoints.records@[base].value().waiters@;
                assert(s.contains(bt1));
                let idx = choose|idx: int| 0 <= idx < s.len() && s[idx] == bt1;
                assert(wait_queue_wf(s4.endpoints.records@[base].value(), s4.threads.records@, base));
                assert(waiter_linked(s, s4.threads.records@, base, idx));
                if idx > 0 {
                    assert(waiter_linked(s, s4.threads.records@, base, idx - 1));
                    assert(thread_wf(&s4.list, &s4.threads, &s4.blocks, s[idx - 1]));
                }
                if idx + 1 < s.len() {
                    assert(waiter_linked(s, s4.threads.records@, base, idx + 1));
                    assert(thread_wf(&s4.list, &s4.threads, &s4.blocks, s[idx + 1]));
                }
                assert(s.len() == 1);
                assert(s =~= seq![bt1]);
            }
            assert(s4.threads.records@[bt1].value().process == Some(p2));
            assert(nt != bt1 + 1) by {
                reveal(CapKernel::wf);
                assert(((bt1 + 1) as int) / (PAGE_SZ as int) == (bt1 as int) / (PAGE_SZ as int)) by (nonlinear_arith)
                    requires bt1 % THREAD_BYTES == 0, THREAD_BYTES == 2 * PAGE_SZ, PAGE_SZ > 1;
                assert(nt / PAGE_SZ == lb / PAGE_SZ);
                assert(lb / PAGE_SZ == base / PAGE_SZ + 2);
            }
            s3.lemma_slot(process, WITNESS_STALE_THREAD_SLOT);
            assert(s3.is_cap(nt));
            assert(s3.list.nodes@[lb as int].live) by {
                reveal(CapKernel::wf);
                assert(s3.tables.owner@.contains_key(lb));
            }
            assert(lb != (bt1 + 1) as usize) by {
                assert(((bt1 + 1) as int) / (PAGE_SZ as int) == (bt1 as int) / (PAGE_SZ as int)) by (nonlinear_arith)
                    requires bt1 % THREAD_BYTES == 0, THREAD_BYTES == 2 * PAGE_SZ, PAGE_SZ > 1;
                assert(lb / PAGE_SZ == base / PAGE_SZ + 2);
                assert(bt1 / PAGE_SZ == base / PAGE_SZ + 18);
            }
            assert(!gone.contains(lb)) by {
                if gone.contains(lb) {
                    let i = choose|i: int| 0 <= i < gone.len() && gone[i] == lb;
                    assert(gone[i] == (bt1 + 1) as usize);
                }
            }
            lemma_revoke_took_only(s3.list, s4.list, nc, gone, lb);
            assert(s4.list.nodes@[lb as int].live);
            assert(s4.list.nodes@[nt as int].live) by {
                assert(!gone.contains(nt)) by {
                    if gone.contains(nt) {
                        let i = choose|i: int| 0 <= i < gone.len() && gone[i] == nt;
                        assert(gone[i] == (bt1 + 1) as usize);
                    }
                }
                lemma_revoke_took_only(s3.list, s4.list, nc, gone, nt);
            }
            assert(s4.list.nodes@[nt as int].kind is Capability);
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_STALE_THREAD_SLOT));
            assert(s4.is_cap(nt));
            assert(s4.slot_holds(process, WITNESS_STALE_THREAD_SLOT, nt, thread_of(bt1)));
            assert(s4.list.childless(nt)) by {
                if !s4.list.childless(nt) {
                    s4.list.lemma_next_is_child(nt);
                    let ch = choose|ch: usize| s4.list.is_child(nt, ch);
                    crate::capability::list::lemma_has(s4.list.seq@, ch);
                    let k = choose|k: int| 0 <= k < s4.list.seq@.len() && s4.list.seq@[k] == ch;
                    s4.list.lemma_link(k);
                    assert(s4.list.nodes@[ch as int].live);
                    assert(s3.list.nodes@[ch as int].live);
                    s3.list.lemma_live_valid(ch);
                    s3.list.lemma_link(0);
                    crate::capability::list::lemma_has(s3.list.seq@, ch);
                    let j = choose|j: int| 0 <= j < s3.list.seq@.len() && s3.list.seq@[j] == ch;
                    s3.list.lemma_link(j);
                    if ch == s3.list.seq@[0] {
                        assert(s3.list.parent@.contains_key(s3.list.seq@[0]));
                    }
                    assert(s3.list.is_child(nt, ch));
                    s3.lemma_slot_bound(nt);
                    assert(s3.list.nodes@[nt as int].live);
                    s3.list.lemma_childless(nt, ch);
                }
            }
            assert(s4.cap_at(process, at_thread) == Some(nt));
            assert(s4.list.nodes@[nt as int].depth == s3.list.nodes@[nt as int].depth);
            assert(s4.list.nodes@[nt as int].depth > 0);
            assert(s4.can_delete_at(process, at_thread));
            assert(s3.list.nodes@[u as int].kind is Capability);
            assert(u != (bt1 + 1) as usize);
            assert(!gone.contains(u)) by {
                if gone.contains(u) {
                    let i = choose|i: int| 0 <= i < gone.len() && gone[i] == u;
                    assert(gone[i] == (bt1 + 1) as usize);
                }
            }
            s3.lemma_slot(process, ROOT_UNTYPED_SLOT);
            assert(leaf@ % PAGE_SZ == 0) by {
                reveal(CapKernel::wf);
                reveal(Tables::leaves_wf);
                assert(s3.tables.owner@.contains_key(leaf@));
            }
            assert(((bt1 + 1) as int) % (PAGE_SZ as int) == 1) by (nonlinear_arith)
                requires bt1 % THREAD_BYTES == 0, THREAD_BYTES == 2 * PAGE_SZ, PAGE_SZ > 1;
            assert(leaf@ != (bt1 + 1) as usize);
            assert(!gone.contains(leaf@)) by {
                if gone.contains(leaf@) {
                    let i = choose|i: int| 0 <= i < gone.len() && gone[i] == leaf@;
                    assert(gone[i] == (bt1 + 1) as usize);
                }
            }
            s3.lemma_slot_bound(leaf@);
            assert(s3.list.nodes@[leaf@ as int].live) by {
                reveal(CapKernel::wf);
                reveal(Tables::leaves_wf);
            }
            lemma_revoke_took_only(s3.list, s4.list, nc, gone, leaf@);
            s3.lemma_slot_bound(u);
            lemma_revoke_took_only(s3.list, s4.list, nc, gone, u);
            assert(s4.list.nodes@[u as int].live);
            assert(s4.list.nodes@[u as int].kind is Capability);
            assert(s4.tables.has_slot(&s4.list, process, ROOT_UNTYPED_SLOT));
            assert(s4.is_cap(u));
            assert(s4.slot_holds(process, ROOT_UNTYPED_SLOT, u, first@));
            assert(s3.list.nodes@[u as int].depth == 1);
            assert(s4.list.nodes@[u as int].live && s4.list.nodes@[u as int].depth == 1);
            assert(s4.blocks.pages@[(bt1 / PAGE_SZ) as int].refs == 1) by {
                reveal(CapKernel::wf);
                assert(thread_wf(&s3.list, &s3.threads, &s3.blocks, bt1));
                assert(thread_wf(&s4.list, &s4.threads, &s4.blocks, bt1));
                assert(s4.is_cap(nt) && s4.payload_of(nt) == thread_of(bt1));
                assert(s4.threads.holders@[bt1].contains(nt));
                assert forall|x: usize| #[trigger] s4.threads.holders@[bt1].contains(x)
                    implies s3.threads.holders@[bt1].contains(x) by {
                    assert(s4.is_cap(x) && s4.payload_of(x).kind is Thread && s4.payload_of(x).base == bt1);
                    s4.lemma_slot_bound(x);
                    assert(s3.list.nodes@[x as int].live);
                    assert(s3.list.nodes@[x as int].kind is Capability);
                    assert(s3.is_cap(x));
                }
                assert(s4.threads.holders@[bt1].subset_of(s3.threads.holders@[bt1]));
                vstd::set_lib::lemma_len_subset(s4.threads.holders@[bt1], s3.threads.holders@[bt1]);
            }
        }
        let deleted = self.delete(process, at_thread);
        let ghost s5 = *self;
        proof {
            assert(deleted is Some);
            assert(Self::cap_deleted_at(s4, s5, process, at_thread));
            assert(Self::object_dropped(s4, s5, nt));
            assert(s5.blocks.pages@[(bt1 / PAGE_SZ) as int].refs == 0);
            lemma_deleted_dead(s5, nt);
            assert(s5.threads.records@[bt1].value().queued == base);
            assert(s5.threads.records@[bt1].value().wait_prev == NONE);
            assert(s5.threads.records@[bt1].value().wait_next == NONE);
            assert(s5.endpoints.records == s4.endpoints.records);
            lemma_slot_kept_but(s4, s5, process, ROOT_UNTYPED_SLOT, nt);
            Self::lemma_caps_frame(s4, s5, nt, nt, u);
            assert(s5.slot_holds(process, ROOT_UNTYPED_SLOT, u, first@));
            assert(s5.list.nodes@[u as int].depth == 1) by {
                reveal(CapKernel::wf);
                assert(s4.list.nodes@[u as int].live);
                assert(s4.list.nodes@[u as int].depth == 1);
                s4.list.lemma_anc_depth(u, 1);
                assert(s4.list.anc(u, 1) == s4.list.anc(s4.list.parent@[u], 0));
                assert(s4.list.parent@[u] == s4.list.seq@[0]);
                assert(s5.list.parent@ == s4.list.parent@);
                assert(s5.list.nodes@[u as int].live);
                s4.list.lemma_link(0);
                let ghost r = s4.list.seq@[0];
                assert(s4.list.nodes@[r as int].depth == 0);
                assert(r != nt);
                assert(s5.list.nodes@[r as int].live);
                crate::capability::list::lemma_has(s5.list.seq@, r);
                let kr = choose|kr: int| 0 <= kr < s5.list.seq@.len() && s5.list.seq@[kr] == r;
                if kr > 0 {
                    assert(s5.list.parent@.contains_key(r));
                    assert(s4.list.parent@.contains_key(s4.list.seq@[0]));
                }
                assert(s5.list.seq@[0] == r);
                Self::lemma_depth_1_kept(s4.list, s5.list, u);
            }
            assert(1usize < MAX_DEPTH) by (compute_only);
            assert(block_within(bt1, THREAD_ORDER, first@));
            assert(s5.can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER));
            assert(s5.thread_is_dead(bt1));
            assert(s5.can_unbind_thread(process, ROOT_UNTYPED_SLOT, bt1));
            assert forall|k: int| 0 <= k < NODES_PER_PAGE && k != 0
                implies !(#[trigger] s5.list.nodes@[bt1 + k]).live by {
                assert(bt1 + k != nt);
                assert(s5.list.nodes@[bt1 + k].live == s4.list.nodes@[bt1 + k].live);
            }
        }
        let reclaimed1 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bt1, Tracked(&mut steps));
        let ghost s6_pre = *self;
        proof {
            assert(reclaimed1 is Slice);
            assert(s5.thread_unbound(s6_pre, process, ROOT_UNTYPED_SLOT, bt1));
            assert(Self::unbound(s5, s6_pre, bt1));
            assert forall|k: int| 0 <= k < NODES_PER_PAGE implies !(#[trigger] s6_pre.list.nodes@[bt1 + k]).live by {
                if k != 0 {
                    assert(s6_pre.list.nodes@[bt1 + k].live == s5.list.nodes@[bt1 + k].live);
                }
            }
            assert(s6_pre.thread_is_spent(bt1));
            assert(s6_pre.threads.records@[bt1].value().queued == base);
            assert(s6_pre.threads.records@[bt1].value().wait_prev == NONE);
            assert(s6_pre.threads.records@[bt1].value().wait_next == NONE);
            assert(s6_pre.endpoints.records == s5.endpoints.records);
        }
        self.witness_acknowledge_all();
        let ghost s6 = *self;
        proof {
            assert(s6.thread_is_spent(bt1));
            assert(s6.threads.records@[bt1].value().queued == base);
            assert(s6.threads.records@[bt1].value().wait_prev == NONE);
            assert(s6.threads.records@[bt1].value().wait_next == NONE);
            assert(s6.endpoints.records == s6_pre.endpoints.records);
            assert(s6.tlb_wf()) by {
                reveal(CapKernel::wf);
            }
            s6.lemma_page_span();
            assert(s6.blocks.pages@.len() == s3.blocks.pages@.len());
            assert(s3.blocks.tracks((bt1 / PAGE_SZ) as int) && s3.blocks.tracks((bt1 / PAGE_SZ + 1) as int)) by {
                reveal(CapKernel::wf);
            }
            assert(s6.blocks.tracks((bt1 / PAGE_SZ) as int));
            assert(s6.blocks.tracks((bt1 / PAGE_SZ + 1) as int));
            assert(s6.acknowledged(bt1 / PAGE_SZ)) by {
                assert(s6.stale_epoch.pages@[(bt1 / PAGE_SZ) as int] <= s6.flush_epoch);
            }
            assert(s6.acknowledged((bt1 / PAGE_SZ + 1) as usize)) by {
                assert(s6.stale_epoch.pages@[(bt1 / PAGE_SZ + 1) as int] <= s6.flush_epoch);
            }
            lemma_slot_kept_but(s5, s6_pre, process, ROOT_UNTYPED_SLOT, bt1);
            assert(s6.can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER));
        }
        let reclaimed2 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bt1, Tracked(&mut steps));
        proof {
            let s7 = *self;
            assert(reclaimed2 is Freed);
            assert(s6.thread_freed(s7, 0, process, ROOT_UNTYPED_SLOT, bt1));
            assert(!s7.threads.records@.contains_key(bt1));
            reveal(CapKernel::unlinked_waiter);
            let mid = choose|mid: Self| #[trigger] Self::unlinked_waiter(s6, mid, bt1) && s7.endpoints == mid.endpoints;
            assert(s6.endpoints.records@.contains_key(base));
            assert(s6.endpoints.records@[base].value().waiters@ == seq![bt1]);
            let ghost w6 = s6.endpoints.records@[base].value().word;
            assert(((w6 & !WAITER_BIT) & WAITER_BIT) == 0u64) by (bit_vector)
                requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert(s7.endpoints.records@.contains_key(base));
            assert(s7.endpoints.records@[base].value().head == NONE);
            if s7.endpoints.records@[base].value().waiters@.len() > 0 {
                reveal(CapKernel::wf);
                reveal(waits_wf);
                let h = s7.endpoints.records@[base].value().waiters@[0];
                assert(mid.endpoints.records@[base].value().waiters@[0] == h);
                assert(wait_queue_wf(mid.endpoints.records@[base].value(), mid.threads.records@, base));
                assert(waiter_linked(mid.endpoints.records@[base].value().waiters@, mid.threads.records@, base, 0));
                assert(mid.threads.records@.contains_key(h));
                assert(thread_wf(&mid.list, &mid.threads, &mid.blocks, h));
                assert(h % THREAD_BYTES == 0);
                lemma_block_page(h, 0);
                assert(NONE % PAGE_SZ == PAGE_MASK);
            }
            assert(s7.endpoints.records@[base].value().waiters@ =~= Seq::<usize>::empty());
            assert((s7.endpoints.records@[base].value().word & WAITER_BIT) == 0);
        }
        (deleted, reclaimed1, reclaimed2)
    }

    /// From the state boot leaves, with three free order-3 blocks at `base`, `base + PROCESS_BYTES`,
    /// and `base + 2 * PROCESS_BYTES`: spawn `bt1` (`base + 18 * PAGE_SZ`) via a child core cap in
    /// `WITNESS_LIVE_THREAD_SLOT`, block `bt1` alone on notification `base` (`word == WAITER_BIT`),
    /// destroy `bt1`, and tear `bt1` down (revoke child core cap, delete thread cap, and two `reclaim`
    /// calls): the first `reclaim` (`Slice`) unbinds `bt1`, and the second (`Freed`) unlinks `bt1`
    /// from `base`'s queue (clearing `WAITER_BIT` so `base.word == 0` and `base.waiters@ == empty`)
    /// before freeing `bt1`'s block.
    #[verifier::spinoff_prover]
    pub fn witness_destroyed_queued_thread_freed(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: usize,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        kernel_root: usize,
        base: usize,
        report: Processor,
        registers: Registers,
    ) -> (ret: (bool, Option<Payload>, ReclaimStep, ReclaimStep))
        requires
            old(self).booted(root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@, kernel_root),
            image_tables_bound(image@) + 3 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            report_tags_tlb(0, report),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            ret.0,
            ret.1 is Some,
            ret.2 is Slice,
            ret.3 is Freed,
            ({
                let bt1 = (base + 18 * PAGE_SZ) as usize;
                &&& final(self).wf()
                &&& !final(self).threads.records@.contains_key(bt1)
                &&& final(self).endpoints.records@.contains_key(base)
                &&& final(self).endpoints.records@[base].value().waiters@ == Seq::<usize>::empty()
                &&& (final(self).endpoints.records@[base].value().word & WAITER_BIT) == 0
                &&& final(self).blocks.pages@[(bt1 / PAGE_SZ) as int].kind is Free
                &&& final(self).blocks.pages@[bt1 / PAGE_SZ + 1int].kind is Free
            }),
    {
        hide(CapKernel::wf);
        hide(CapKernel::booted);
        hide(BlockTable::counts_wf);
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        self.witness_setup_waiter_process(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root, base, report);
        let p2 = base + PROCESS_BYTES;
        let b3 = p2 + PROCESS_BYTES;
        let bt1 = b3 + 2 * PAGE_SZ;
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost lb = (base + 2 * PAGE_SZ) as usize;
        let ghost nc = (lb + 5) as usize;
        let ghost np2 = (lb + 1) as usize;
        let ghost s0 = *self;
        proof {
            assert((0u64 & SIGNAL_BITS) == 0u64) by (compute_only);
            assert((WAITER_BIT & SIGNAL_BITS) == 0u64) by (compute_only);
            assert(CORE_RIGHTS & !CORE_RIGHTS == 0) by (compute_only);
            s0.lemma_console_power_derive(process, ROOT_CORE_SLOT, process, WITNESS_LIVE_THREAD_SLOT, CORE_RIGHTS, CORE_OBJECTS, 1, 0);
            assert(core_object(0) == CORE_OBJECTS);
            assert(s0.can_derive_at(
                process,
                ROOT_CORE_SLOT,
                Position { through: None, index: WITNESS_LIVE_THREAD_SLOT },
                CORE_RIGHTS,
                CORE_OBJECTS,
                1,
                0,
            ));
        }
        let child_core = self.derive(
            process,
            ROOT_CORE_SLOT,
            Position { through: None, index: WITNESS_LIVE_THREAD_SLOT },
            CORE_RIGHTS,
            CORE_OBJECTS,
            1,
            0,
        );
        let ghost s1 = *self;
        proof {
            assert(child_core);
            assert(Self::cap_derived_between(s0, s1, process, ROOT_CORE_SLOT, process, WITNESS_LIVE_THREAD_SLOT, CORE_RIGHTS, CORE_OBJECTS, 1, 0));
            assert(Self::derive_step(s0, s1, nc));
            assert(s1.slot_holds(process, WITNESS_LIVE_THREAD_SLOT, nc, core_payload(0, 1)));
            assert(s1.list.nodes@[nc as int].depth == 2);
            Self::lemma_slot_stays(s0, s1, process, ROOT_UNTYPED_SLOT);
            Self::lemma_caps_frame(s0, s1, nc, nc, u);
            Self::lemma_caps_frame(s0, s1, nc, nc, np2);
            Self::lemma_caps_frame(s0, s1, nc, nc, (b3 + 1) as usize);
            s0.lemma_slot_bound(u);
            assert(Self::caps_frame(s0, s1, nc, nc));
            assert(s1.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.wf() && s1.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(nc != u && nc != (leaf@ + ROOT_CORE_SLOT) as usize && nc != np2) by {
                assert(leaf@ % PAGE_SZ == 0) by {
                    reveal(CapKernel::wf);
                    reveal(Tables::leaves_wf);
                    s0.lemma_slot(process, ROOT_UNTYPED_SLOT);
                    assert(s0.tables.owner@.contains_key(leaf@));
                }
                assert(nc / PAGE_SZ == base / PAGE_SZ + 2);
                assert(u / PAGE_SZ == leaf@ / PAGE_SZ);
                assert(((leaf@ + ROOT_CORE_SLOT) as usize) / PAGE_SZ == leaf@ / PAGE_SZ);
                assert((base + 2 * PAGE_SZ) as usize != leaf@);
                assert(base % PAGE_SZ == 0);
                assert(nc / PAGE_SZ != leaf@ / PAGE_SZ);
            }
            Self::lemma_depth_1_kept(s0.list, s1.list, u);
            assert(s1.list.nodes@[u as int].depth == s0.list.nodes@[u as int].depth);
            assert(s1.list.nodes@[np2 as int].depth == 2) by {
                assert(s1.list.nodes@[np2 as int].live);
                assert(s1.list.parent@[np2] == u);
                assert(s0.list.nodes@[np2 as int].depth == 2);
                s0.list.lemma_link(0);
                crate::capability::list::lemma_has(s1.list.seq@, np2);
                let j = choose|j: int| 0 <= j < s1.list.seq@.len() && s1.list.seq@[j] == np2;
                s1.list.lemma_link(j);
                assert(j != 0);
            }
            assert(Self::derive_untracked(s0, s1, (leaf@ + ROOT_CORE_SLOT) as usize));
            assert(s1.blocks == s0.blocks);
            assert(witness_empty(s1, process, WITNESS_STALE_THREAD_SLOT, (lb + 4) as usize));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, bt1, THREAD_ORDER));
            assert(s1.spaces.roots@.contains_key(process) && s1.spaces.roots@.contains_key(p2)) by {
                reveal(CapKernel::wf);
            }
            assert(s1.blocks.tracks_addr_run(bt1, 2));
            assert(s1.blocks.pages@[(p2 / PAGE_SZ) as int] == s0.blocks.pages@[(p2 / PAGE_SZ) as int]);
            Self::lemma_slot_stays(s0, s1, p2, WITNESS_CHILD_SLOT);
            assert(nc != (b3 + 1) as usize) by {
                assert(PROCESS_BYTES == 8 * PAGE_SZ);
            }
            assert(index_ok(WITNESS_CHILD_SLOT) && index_entry(WITNESS_CHILD_SLOT) == 0 && index_slot(WITNESS_CHILD_SLOT) == 1) by (compute_only);
            assert(s0.tables.node_of(p2, WITNESS_CHILD_SLOT) == (b3 + 1) as usize);
            assert(s0.is_cap((b3 + 1) as usize));
            Self::lemma_caps_frame(s0, s1, nc, nc, (b3 + 1) as usize);
            assert(s1.holds_notification(p2, WITNESS_CHILD_SLOT, RECEIVE_RIGHT));
            assert(s1.notification_at(p2, WITNESS_CHILD_SLOT) == base);
            assert(s1.list.parent@ == s0.list.parent@.insert(nc, (leaf@ + ROOT_CORE_SLOT) as usize));
            assert forall|x: usize| x != nc && x != nc && #[trigger] s0.list.parent@.contains_key(x)
                implies s1.list.parent@[x] == s0.list.parent@[x] by {}
            lemma_children_kept(s0.list, s1.list, nc, nc, nc);
            assert forall|x: usize| !#[trigger] s1.list.is_child(nc, x) by {
                if s1.list.is_child(nc, x) {
                    if x == nc {
                        assert(s1.list.parent@[nc] == (leaf@ + ROOT_CORE_SLOT) as usize);
                    } else {
                        s0.list.lemma_dead_childless(nc, x);
                    }
                }
            }
        }
        self.witness_spawn_and_block_waiter(
            process, p2, leaf, Ghost(first), t, base, WITNESS_STALE_THREAD_SLOT, WITNESS_LIVE_THREAD_SLOT, Ghost(1usize),
            bt1, kernel_root, report, registers,
        );
        let ghost s2 = *self;
        proof {
            assert((0u64 | WAITER_BIT) == WAITER_BIT) by (bit_vector)
                requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
            assert(s2.endpoints.records@.contains_key(base));
            assert(s2.endpoints.records@[base].value().waiters@ == seq![bt1]);
            assert(s2.endpoints.records@[base].value().word == WAITER_BIT);
            assert(crate::capability::endpoint::waiter_linked(
                s2.endpoints.records@[base].value().waiters@,
                s2.threads.records@,
                base,
                0,
            )) by {
                reveal(CapKernel::wf);
                reveal(waits_wf);
            }
            assert(THREAD_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s2.slot_holds(process, WITNESS_STALE_THREAD_SLOT, (lb + 4) as usize, thread_of(bt1))
                && s2.processes.records@.contains_key(p2)
                && !s2.processes.records@[p2].value().dead) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert(s2.can_destroy(process, WITNESS_STALE_THREAD_SLOT));
        }
        let tracked mut steps = Steps::fresh();
        let destroyed = self.destroy(0, process, WITNESS_STALE_THREAD_SLOT, Tracked(&mut steps));
        let ghost s3 = *self;
        proof {
            assert(destroyed);
            assert(Self::thread_destroyed(s2, s3, 0, bt1));
            assert(s3.endpoints.records == s2.endpoints.records);
            assert(s3.endpoints.records@[base].value().word == WAITER_BIT);
            assert(s3.threads.records@[bt1].value().state is Dead);
            assert(s3.threads.records@[bt1].value().queued == base);
            assert(s3.threads.records@[bt1].value().wait_prev == NONE);
            assert(s3.threads.records@[bt1].value().wait_next == NONE);
            assert(s3.flush_epoch == 0);
            assert(s3.list == s2.list);
            assert(s3.list.nodes@[(lb + 4) as int].depth == 2);
            assert(s3.list.nodes@[(bt1 + 1) as int].kind is Placement);
            assert(s3.list.is_child(nc, (bt1 + 1) as usize));
            assert(s2.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s2.list.nodes@[(bt1 + 1) as int].live) by {
                crate::capability::list::lemma_has(s2.list.seq@, (bt1 + 1) as usize);
                let k = choose|k: int| 0 <= k < s2.list.seq@.len() && s2.list.seq@[k] == (bt1 + 1) as usize;
                s2.list.lemma_link(k);
            }
            assert forall|x: usize| !#[trigger] s3.list.is_child((bt1 + 1) as usize, x) by {
                s2.list.lemma_childless((bt1 + 1) as usize, x);
            }
            assert(bt1 == (base + 18 * PAGE_SZ) as usize);
            Self::lemma_slot_stays(s0, s1, process, ROOT_UNTYPED_SLOT);
            assert(s1.tables.leaf(process, 0) == leaf@);
            assert(s2.tables.leaf(process, 0) == leaf@
                && s2.tables.leaf(process, 2) == s1.tables.leaf(process, 2)
                && s2.slot_holds(process, ROOT_UNTYPED_SLOT, u, first)
                && s2.slot_holds(process, WITNESS_LIVE_THREAD_SLOT, nc, core_payload(0, 1))
                && s2.slot_holds(process, WITNESS_STALE_THREAD_SLOT, (lb + 4) as usize, thread_of(bt1))
                && s2.processes.records@.contains_key(p2)
                && s2.tables.roots@.contains_key(p2)) by {
                reveal(CapKernel::waiter_tables_kept);
            }
            assert(s2.tables.roots == s1.tables.roots);
            assert(s3.tables == s2.tables);
            assert(s3.tables.leaf(process, 0) == leaf@);
            assert(s3.blocks == s2.blocks);
            assert(s3.blocks.pages@[(bt1 / PAGE_SZ) as int].refs == 1);
        }
        let (deleted, reclaimed1, reclaimed2) = self.witness_teardown_destroyed_queued_thread(
            process, p2, leaf, Ghost(first), base, bt1,
        );
        (destroyed, deleted, reclaimed1, reclaimed2)
    }

} // impl CapKernel

} // verus!
