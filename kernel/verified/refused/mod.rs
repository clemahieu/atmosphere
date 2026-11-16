// SPDX-License-Identifier: MIT

//! False claims for the caller's-view contracts, for the operation ways whose contracts admit an
//! unchanged table view, for the queue lock, for boot, charge, notification, print, power, inspect
//! and enter_flush, and for tick, switch_thread, the boot thread and check_current. An unchanged
//! kernel meets no ok or again arm whose specification does not admit it, and no success ensures of
//! destroy, place, start, suspend, unmap or the register operations. No contract lets a slot it does
//! not name change. QueueLock::new's ensures fails for a lock that is not well-formed, and acquire's
//! and release's ensures fail for an unchanged core on the lock the operation borrows. kernel_init's
//! Some at an unchanged kernel is not the booted state, charge does not leave the counter it was
//! given, signal and wait do not write the notification word, print and power_off at the other bool
//! are not what the slot holds, inspect's Some is not the slot's payload, and enter_flush does not
//! bring a core that is behind the epoch up to it. tick's Switched and Dropped meet no unchanged
//! kernel, and tick's Kept, where no selected thread preempts, is another result. switch_thread and
//! enter_boot_thread do not make a thread current on an unchanged kernel. check_current's MovedOff
//! does not move a thread off an unchanged kernel, and its Kept, where the thread need not leave,
//! is MovedOff. map_nested, load_space, switch_space, flush_iommu and acknowledge meet no unchanged
//! kernel. probe_at's Some clears accessed and dirty bits in the level 1 table's words and leaves the
//! view as it was, so the unchanged kernel includes those words and the probed prefix does not hold.
//! add_devices does not record the devices, bind_device does not make the binding node a child of the
//! space, unbind_device_at does not advance the flush epoch or drop the device from the view's binds,
//! and map_device writes neither a page nor a large page into the device space.
//! reclaim's Freed, at a dead queue the untyped covers, its Unlinked, at a live leaf node, and its
//! Slice, at a leaf with a slot left, meet no unchanged kernel, and neither does reclaim_frame's or
//! reclaim_large_frame's Freed once the frame is acknowledged. The three Again ways stay exempt.
//! retype_endpoint and retype_notification do not make the free page a live endpoint or notification,
//! retype_reply does not make it a reply, and retype_space does not make the free block a space.
//! revoke's Exhausted does not put the flush epoch at its limit.
//! tools/check-refused.py runs each module under cfg(refused), which nothing else sets, so the claims
//! are in no image and no verify count. design/refused-claim-per-way/.
//!
//! Each claim is a trait's proof function, specified here, with its body in the module. The
//! specification and the body are different files, so the refusal's body span is the module's, which
//! is the span the check joins to the clause.
//!
//! Retype's free-kind again arm is not a claim. spec_retyped's arm for that status is `post == pre`
//! while the frame is not yet acknowledged (capability/operation.rs, the RETYPE_FREE again arm), so
//! an unchanged post meets the arm.

pub mod delete_ok;
pub mod revoke_ok;
pub mod revoke_again;
pub mod link_ok;
pub mod map_ok;
pub mod inspect_ok;
pub mod retype_frame_ok;
pub mod retype_large_again;
pub mod retype_large_ok;
pub mod retype_table_ok;
pub mod retype_leaf_ok;
pub mod retype_free_ok;
pub mod retype_process_ok;
pub mod retype_thread_ok;
pub mod derive_ok;
pub mod move_ok;
pub mod unnamed_delete;
pub mod unnamed_revoke;
pub mod unnamed_revoke_value;
pub mod unnamed_link;
pub mod unnamed_map;
pub mod unnamed_inspect;
pub mod unnamed_retype;
pub mod unnamed_derive;
pub mod destroy_ok;
pub mod place_ok;
pub mod start_ok;
pub mod suspend_suspended;
pub mod suspend_again;
pub mod unmap_ok;
pub mod read_registers_none;
pub mod write_registers_ok;
pub mod unnamed_move;
pub mod queue_lock_new;
pub mod queue_lock_acquire;
pub mod queue_lock_release;
pub mod kernel_init_some;
pub mod charge_returns;
pub mod signal_ok;
pub mod wait_some;
pub mod print_false;
pub mod power_off_false;
pub mod inspect_other;
pub mod enter_flush_returns;
pub mod tick_switched;
pub mod tick_kept;
pub mod tick_dropped;
pub mod switch_thread_returns;
pub mod enter_boot_thread_returns;
pub mod check_current_kept;
pub mod check_current_moved_off;
pub mod map_nested_ok;
pub mod load_space_returns;
pub mod switch_space_returns;
pub mod flush_iommu_returns;
pub mod acknowledge_returns;
pub mod probe_at_some;
pub mod add_devices_ok;
pub mod bind_device_ok;
pub mod unbind_device_ok;
pub mod map_device_ok;
pub mod reclaim_freed;
pub mod reclaim_unlinked;
pub mod reclaim_slice;
pub mod reclaim_frame_freed;
pub mod reclaim_large_freed;
pub mod retype_endpoint_ok;
pub mod retype_notification_ok;
pub mod retype_reply_ok;
pub mod retype_space_ok;
pub mod revoke_exhausted;

use vstd::prelude::*;

verus! {

use crate::arch::{user_rip, FrameKind, Registers, saved_frame, tag_written};
use crate::capability::thread::{CurrentStep, SuspendStep, ThreadState, entry_frame_save, runs_in_space, same_record_perm_but_links};
use crate::capability::unmap::Unmapped;
use crate::define::{ENTRIES, NUM_CPUS, NUM_IOMMUS, PAGE_SZ, PAGES_PER_1G, PAGES_PER_2M, PCID_MAX};
use vstd::arithmetic::power2::pow2;
use crate::util::page_ptr_util_u::mem_valid;
use crate::capability::boot_image::{image_blocks, ImageRun, ROOT_FRAME_SLOTS};
use crate::capability::boot_memory::{runs_blocks, ROOT_UNTYPED_SLOTS};
use crate::capability::boot_table::{image_tables_bound, image_virt_wf, untyped_tables};
use crate::capability::decompose::page_block_payload;
use crate::array::Array;
use crate::capability::kernel::{CapKernel, holds_id, id_pcid, ID_GENERATION_MAX, KERNEL_TAG, TlbEntry};
use crate::capability::device::{DeviceInfo, MAX_DEVICES, binding_node, device_of, device_payload, unbound_record};
use crate::capability::device_space::DeviceRange;
use crate::capability::guest_space::GuestPhysRange;
use crate::capability::list::{NODE_SPACE, NODES_PER_PAGE};
use crate::capability::revoke::{RevokeStep, REVOKE_STEP_STEPS, UNLINK_ARM_STEPS};
use crate::capability::link::tree_of;
use crate::capability::mapping::{space_mapping, space_says, SpacePath};
use crate::capability::probe::Probed;
use crate::capability::reach::{discharges, Effect, Right, saves_own_frame};
use crate::capability::schedule::{at_back_of_priority, queued_at_back, thread_priority};
use crate::capability::space::{fresh_root, space_of, SPACE_ROOT_PAGE, SpaceKind, Spaces};
use crate::capability::reply::{fresh_reply, reply_of};
use crate::capability::switch::TickStep;
use crate::capability::view::bound_threads;
use crate::capability::block::{Large, ObjectType, PageKind, SMALL_PAGES_MAX};
use crate::capability::process::PROCESS_ORDER;
use crate::capability::reclaim::{FrameReclaimStep, LEAF_SLICE_BUDGET, ReclaimStep};
use crate::capability::table::{CapKind, Payload, MAX_ORDER};
use crate::capability::zero::{large_level, level_pages};
use crate::queue_lock::{Core, QueueLock};
use crate::capability::operation::*;
use crate::capability::position::{Position, spec_position};

pub trait DeleteOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>)
        requires
            pre.wf(),
            pre.delete_allowed(root, at),
            post == pre,
        ensures
            CapKernel::delete_contract(pre, post, root, at, status_only(STATUS_OK)),
    ;
}

pub trait RevokeOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>)
        requires
            pre.wf(),
            pre.revoke_allowed(root, at),
            post == pre,
        ensures
            CapKernel::revoke_contract(pre, post, root, at, status_only(STATUS_OK)),
    ;
}

pub trait RevokeAgain {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>)
        requires
            pre.wf(),
            pre.revoke_allowed(root, at),
            post == pre,
        ensures
            CapKernel::revoke_contract(pre, post, root, at, status_only(STATUS_AGAIN)),
    ;
}

pub trait LinkOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, level: u64, from: usize, child: usize)
        requires
            pre.wf(),
            pre.link_allowed(root, slot, va, level, from, child),
            post == pre,
        ensures
            CapKernel::link_contract(pre, post, root, slot, va, level, from, child, status_only(STATUS_OK)),
    ;
}

pub trait MapOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize)
        requires
            pre.wf(),
            pre.map_allowed(root, slot, va, level, from, page),
            post == pre,
        ensures
            CapKernel::map_contract(pre, post, root, slot, va, level, from, page, status_only(STATUS_OK)),
    ;
}

pub trait InspectOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Option<Position>)
        requires
            pre.wf(),
            pre.inspect_allowed(root, at),
            post == pre,
        ensures
            CapKernel::inspect_contract(pre, post, root, at, status_only(STATUS_OK)),
    ;
}

pub trait RetypeFrameOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_FRAME, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_FRAME, from, base, word, level, status_only(STATUS_OK)),
    ;
}

pub trait RetypeLargeAgain {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_LARGE_FRAME, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_LARGE_FRAME, from, base, word, level, status_only(STATUS_AGAIN)),
    ;
}

pub trait RetypeLargeOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_LARGE_FRAME, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_LARGE_FRAME, from, base, word, level, status_only(STATUS_OK)),
    ;
}

pub trait RetypeTableOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_TABLE_PAGE, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_TABLE_PAGE, from, base, word, level, status_only(STATUS_OK)),
    ;
}

pub trait RetypeLeafOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_LEAF, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_LEAF, from, base, word, level, status_only(STATUS_OK)),
    ;
}

pub trait RetypeFreeOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_FREE, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_FREE, from, base, word, level, status_only(STATUS_OK)),
    ;
}

pub trait RetypeProcessOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_PROCESS, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_PROCESS, from, base, word, level, status_only(STATUS_OK)),
    ;
}

pub trait RetypeThreadOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, base: usize, word: u64, level: usize)
        requires
            pre.wf(),
            pre.retype_allowed(root, RETYPE_THREAD, from, base, word, level),
            post == pre,
        ensures
            CapKernel::retype_contract(pre, post, root, RETYPE_THREAD, from, base, word, level, status_only(STATUS_OK)),
    ;
}

pub trait DeriveOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: Option<Position>, to: Option<Position>, rights: u64, base: usize, order: u64, badge: u64)
        requires
            pre.wf(),
            pre.derive_allowed(root, from, to, rights, base, order, badge),
            post == pre,
        ensures
            CapKernel::derive_contract(pre, post, root, from, to, rights, base, order, badge, status_only(STATUS_OK)),
    ;
}

pub trait MoveOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: Option<Position>, to: Option<Position>)
        requires
            pre.wf(),
            pre.move_allowed(root, from, to),
            post == pre,
        ensures
            CapKernel::move_contract(pre, post, root, from, to, status_only(STATUS_OK)),
    ;
}

pub trait DestroyOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, i: usize, ret: bool)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_destroy(root, i),
            post == pre,
            ret,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::destroy_answered(pre, post, root, i, ret),
            CapKernel::destroy_kept(pre, post),
            ret ==> CapKernel::destroy_done(pre, post, c, root, i),
    ;
}

pub trait PlaceOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, j: usize, priority: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_place(root, i, j, priority),
            post == pre,
            ret,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::place_answered(pre, post, root, i, j, priority, ret),
            CapKernel::place_kept(pre, post, root),
            ret ==> CapKernel::place_done(pre, post, root, i, j, priority),
    ;
}

pub trait StartOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_start(root, i),
            post == pre,
            ret,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::start_answered(pre, post, root, i, ret),
            CapKernel::start_kept(pre, post),
            ret ==> CapKernel::start_done(pre, post, root, i),
    ;
}

pub trait SuspendSuspended {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, i: usize, ret: SuspendStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_suspend(root, i),
            !pre.stops_elsewhere(c, root, i),
            post == pre,
            ret is Suspended,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::suspend_answered(pre, post, c, root, i, ret),
    ;
}

pub trait SuspendAgain {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, i: usize, ret: SuspendStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.stops_elsewhere(c, root, i),
            post == pre,
            ret is Again,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::suspend_answered(pre, post, c, root, i, ret),
    ;
}

pub trait UnmapOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, level: u64, ret: Option<Unmapped>)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_unmap_at(root, slot, va, level),
            post == pre,
            ret is Some,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::unmap_answered(pre, post, root, slot, va, level, ret is Some),
            CapKernel::unmap_kept(pre, post),
            ret is Some ==> CapKernel::page_unmapped(pre, post, root, slot, va, level, ret->0),
    ;
}

pub trait ReadRegistersNone {
    proof fn wrong(kernel: CapKernel, root: usize, i: usize, ret: Option<Registers>)
        requires
            kernel.wf(),
            kernel.tables.roots@.contains_key(root),
            kernel.root_live(root),
            kernel.can_set_registers(root, i),
            ret is None,
        ensures
            kernel.read_registers_answered(root, i, ret),
            kernel.read_registers_done(root, i, ret),
    ;
}

pub trait WriteRegistersOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, frame: Registers, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_set_registers(root, i),
            user_rip(frame.spec_pc()),
            post == pre,
            ret,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::write_registers_answered(pre, post, root, i, frame, ret),
            CapKernel::write_registers_kept(pre, post),
            ret ==> CapKernel::write_registers_done(pre, post, root, i, frame),
    ;
}

pub trait UnnamedDelete {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_deleted(pre, post, root, frame, out),
        ensures
            unnamed_delete::unnamed(pre, post, root, frame),
    ;
}

pub trait UnnamedRevoke {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_revoked(pre, post, root, frame, out),
            pre.revoke_allowed(root, spec_position(frame.slot())),
        ensures
            unnamed_revoke::unnamed(pre, post, root, frame),
    ;
}

pub trait UnnamedRevokeValue {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_revoked(pre, post, root, frame, out),
        ensures
            unnamed_revoke_value::unnamed(pre, post),
    ;
}

pub trait UnnamedLink {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_linked(pre, post, root, frame, out),
        ensures
            unnamed_link::unnamed(pre, post),
    ;
}

pub trait UnnamedMap {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_mapped(pre, post, root, frame, out),
        ensures
            unnamed_map::unnamed(pre, post),
    ;
}

pub trait UnnamedInspect {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            CapKernel::invoked(pre, post, root, frame, out),
        ensures
            unnamed_inspect::unnamed(pre, post),
    ;
}

pub trait UnnamedRetype {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_retyped(pre, post, root, frame, out),
        ensures
            unnamed_retype::unnamed(pre, post, root, frame),
    ;
}

pub trait UnnamedDerive {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_derived(pre, post, root, frame, out),
        ensures
            unnamed_derive::unnamed(pre, post, root, frame),
    ;
}

pub trait UnnamedMove {
    proof fn claim(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            CapKernel::spec_moved(pre, post, root, frame, out),
        ensures
            unnamed_move::unnamed(pre, post, root, frame),
    ;
}

/// `QueueLock::new` at a lock that is not well-formed. The core map is the one new ensures.
pub trait QueueLockNew {
    proof fn wrong(lock: QueueLock, cores: Map<int, Core>)
        requires
            !lock.wf(),
            forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] cores.dom().contains(c) && cores[c].idle() && cores[c].cpu == c && cores[c].for_lock(lock),
        ensures
            lock.wf(),
            forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] cores.dom().contains(c) && cores[c].idle() && cores[c].cpu == c && cores[c].for_lock(lock),
    ;
}

/// `QueueLock::acquire` at an unchanged lock and an unchanged core, still idle.
pub trait QueueLockAcquire {
    proof fn unchanged(lock: &QueueLock, cpu: usize, pre_core: Core, post_core: Core)
        requires
            lock.wf(),
            cpu < NUM_CPUS,
            pre_core.idle(),
            pre_core.cpu == cpu,
            pre_core.for_lock(*lock),
            post_core.cpu == pre_core.cpu,
            post_core.loc == pre_core.loc,
            post_core.place_id == pre_core.place_id,
            post_core.behind_id == pre_core.behind_id,
            post_core.front_id == pre_core.front_id,
            post_core.state.id() == pre_core.state.id(),
            post_core.swapped == pre_core.swapped,
            post_core.granted == pre_core.granted,
            post_core.idle(),
        ensures
            post_core.holding() && post_core.swapped <= post_core.granted && post_core.granted <= post_core.swapped + NUM_CPUS - 1,
            post_core.cpu == cpu,
            post_core.for_lock(*lock),
    ;
}

/// `QueueLock::release` at an unchanged lock and an unchanged core, still holding.
pub trait QueueLockRelease {
    proof fn unchanged(lock: &QueueLock, cpu: usize, pre_core: Core, post_core: Core)
        requires
            lock.wf(),
            cpu < NUM_CPUS,
            pre_core.holding(),
            pre_core.cpu == cpu,
            pre_core.for_lock(*lock),
            post_core.cpu == pre_core.cpu,
            post_core.loc == pre_core.loc,
            post_core.place_id == pre_core.place_id,
            post_core.behind_id == pre_core.behind_id,
            post_core.front_id == pre_core.front_id,
            post_core.state.id() == pre_core.state.id(),
            post_core.holding(),
        ensures
            post_core.idle(),
            post_core.cpu == cpu,
            post_core.for_lock(*lock),
    ;
}

/// `kernel_init`'s Some at an unchanged kernel. The free runs and the image are a success case, so
/// the refusal biconditional holds, and the returned counts are not a booted kernel's.
pub trait KernelInitSome {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        root: usize,
        process: usize,
        leaf: usize,
        frames: usize,
        t: usize,
        free: Seq<(usize, usize)>,
        image: Seq<ImageRun>,
        present: Seq<bool>,
        kernel_root: usize,
        ret: Option<(usize, usize)>,
    )
        requires
            post == pre,
            ret is Some,
            ({
                let bs = runs_blocks(free, MAX_ORDER as nat);
                &&& bs.len() != 0
                &&& bs.len() <= ROOT_UNTYPED_SLOTS
                &&& image_blocks(image).len() <= ROOT_FRAME_SLOTS
                &&& image_virt_wf(image)
                &&& image_tables_bound(image) <= untyped_tables(page_block_payload(bs[0]))
            }),
            match ret {
                Some((untyped, frame)) => !post.booted(
                    root,
                    process,
                    leaf,
                    frames,
                    t,
                    free,
                    image,
                    untyped,
                    frame,
                    present,
                    kernel_root,
                ),
                None => false,
            },
        ensures
            ret is None <==> ({
                let bs = runs_blocks(free, MAX_ORDER as nat);
                ||| bs.len() > ROOT_UNTYPED_SLOTS
                ||| bs.len() == 0
                ||| image_blocks(image).len() > ROOT_FRAME_SLOTS
                ||| !image_virt_wf(image)
                ||| image_tables_bound(image) > untyped_tables(page_block_payload(bs[0]))
            }),
            ret matches Some((untyped, frame)) ==> post.booted(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root),
    ;
}

/// `charge` where the counter moved and the kernel did not. The entry's since is not the reading it
/// was given.
pub trait ChargeReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, now: u64)
        requires
            pre.wf(),
            c < NUM_CPUS,
            post == pre,
            pre.cores@[c as int].since != now,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            CapKernel::charged_entry(pre, post, c as int, now),
            post.view() == pre.view(),
    ;
}

/// `signal`'s success where the badge sets a bit and the kernel does not take it.
pub trait SignalOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_signal(root, i),
            post == pre,
            ret,
            ({
                let w = pre.notification_record(root, i).word;
                let b = pre.payload_of(pre.tables.node_of(root, i)).badge as u64;
                (w | b) != w
            }),
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            ret == pre.can_signal(root, i),
            !ret ==> post == pre,
            ret ==> CapKernel::signalled(pre, post, root, i),
    ;
}

/// `wait`'s Some where the word has a signalled bit and the kernel does not clear it.
pub trait WaitSome {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: Option<u64>)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_wait(root, i),
            post == pre,
            ret is Some,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            ret is Some == pre.can_wait(root, i),
            ret is None ==> post == pre,
            ret is Some ==> CapKernel::waited(pre, post, root, i, ret->0),
    ;
}

/// `print`'s true at a slot that holds the console, claimed false.
pub trait PrintFalse {
    proof fn wrong(pre: CapKernel, post: CapKernel, root: usize, i: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.holds_console(root, i),
            post == pre,
            !ret,
        ensures
            CapKernel::page_count_kept(pre, post),
            post == pre,
            ret == pre.holds_console(root, i),
            discharges(pre.view(), post.view(), root, Effect::Local),
    ;
}

/// `power_off`'s true at a slot that holds power, claimed false.
pub trait PowerOffFalse {
    proof fn wrong(kernel: CapKernel, root: usize, i: usize, ret: bool)
        requires
            kernel.wf(),
            kernel.tables.roots@.contains_key(root),
            kernel.root_live(root),
            kernel.holds_power(root, i),
            !ret,
        ensures
            ret == kernel.holds_power(root, i),
            discharges(kernel.view(), kernel.view(), root, Effect::Local),
    ;
}

/// `inspect`'s Some of a payload other than the one the slot holds.
pub trait InspectOther {
    proof fn wrong(kernel: CapKernel, root: usize, at: Position, ret: Option<(Payload, u64)>)
        requires
            kernel.wf(),
            kernel.tables.roots@.contains_key(root),
            kernel.root_live(root),
            kernel.cap_at(root, at) is Some,
            ret is Some,
            match (ret, kernel.cap_at(root, at)) {
                (Some((payload, _)), Some(n)) => payload != kernel.payload_of(n),
                _ => false,
            },
        ensures
            kernel.inspect_found(root, at, ret),
            kernel.inspect_reads(root, at, ret),
            discharges(kernel.view(), kernel.view(), root, Effect::Local),
    ;
}

/// `enter_flush` at an unchanged kernel whose core is behind the epoch. The requires are the
/// operation's plus that unchanged kernel; nothing says the core is already caught up.
pub trait EnterFlushReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize)
        requires
            pre.wf(),
            c < NUM_CPUS,
            post == pre,
            pre.acked(c as int) < pre.flush_epoch,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            CapKernel::only_core_changed(pre, post, c as int),
            post.acked(c as int) == post.flush_epoch,
            pre.acked(c as int) == pre.flush_epoch ==> post == pre,
    ;
}

/// `tick`'s Switched at an unchanged idle core a selected runnable thread would take.
pub trait TickSwitched {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, kernel_root: usize, ret: TickStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            kernel_root == pre.spaces.kernel_root@,
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
            post == pre,
            pre.cores@[c as int].current_thread is None,
            !pre.must_leave(c as int),
            pre.current_live(c as int),
            ret is Switched,
            exists|t: usize| #[trigger] pre.selected(c as int, t) && pre.preempts(c as int, t) && pre.can_run(t)
                && pre.cores@[c as int].generation < ID_GENERATION_MAX,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            CapKernel::consumed_kept(pre, post),
            post.current_live(c as int),
            !pre.must_leave(c as int) ==> CapKernel::ticked(pre, post, c as int, frame, ret),
            pre.must_leave(c as int) ==> exists|mid: CapKernel|
                #![trigger CapKernel::moved_off(pre, mid, c as int, frame, FrameKind::Full)]
                CapKernel::moved_off(pre, mid, c as int, frame, FrameKind::Full)
                && mid.wf()
                && CapKernel::ticked(mid, post, c as int, frame, ret),
    ;
}

/// `tick`'s Dropped at an unchanged idle core. A selected thread that cannot run would leave its queue.
pub trait TickDropped {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, kernel_root: usize, ret: TickStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            kernel_root == pre.spaces.kernel_root@,
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
            post == pre,
            pre.cores@[c as int].current_thread is None,
            !pre.must_leave(c as int),
            pre.current_live(c as int),
            ret is Dropped,
            exists|t: usize| #[trigger] pre.selected(c as int, t) && pre.preempts(c as int, t) && !pre.can_run(t),
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            CapKernel::consumed_kept(pre, post),
            post.current_live(c as int),
            !pre.must_leave(c as int) ==> CapKernel::ticked(pre, post, c as int, frame, ret),
            pre.must_leave(c as int) ==> exists|mid: CapKernel|
                #![trigger CapKernel::moved_off(pre, mid, c as int, frame, FrameKind::Full)]
                CapKernel::moved_off(pre, mid, c as int, frame, FrameKind::Full)
                && mid.wf()
                && CapKernel::ticked(mid, post, c as int, frame, ret),
    ;
}

/// `tick`'s Kept where no selected thread preempts, at a result other than Kept. The kernel is unchanged.
pub trait TickKept {
    proof fn wrong(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, kernel_root: usize, ret: TickStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            kernel_root == pre.spaces.kernel_root@,
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
            post == pre,
            !pre.must_leave(c as int),
            pre.current_live(c as int),
            forall|t: usize| #[trigger] pre.selected(c as int, t) ==> !pre.preempts(c as int, t),
            !(ret is Kept),
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            CapKernel::consumed_kept(pre, post),
            post.current_live(c as int),
            !pre.must_leave(c as int) ==> CapKernel::ticked(pre, post, c as int, frame, ret),
            pre.must_leave(c as int) ==> exists|mid: CapKernel|
                #![trigger CapKernel::moved_off(pre, mid, c as int, frame, FrameKind::Full)]
                CapKernel::moved_off(pre, mid, c as int, frame, FrameKind::Full)
                && mid.wf()
                && CapKernel::ticked(mid, post, c as int, frame, ret),
    ;
}

/// `enter_boot_thread` at an unchanged kernel. The boot thread stays inactive and the core stays idle.
pub trait EnterBootThreadReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, t: usize)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.cores@[c as int].current_thread is None,
            pre.threads.boot_thread@ == Some(t),
            pre.threads.records@.contains_key(t),
            pre.threads.records@[t].value().state is Inactive,
            pre.threads.records@[t].value().placement is Some,
            pre.threads.records@[t].value().placement->Some_0.core == c,
            runs_in_space(pre.cores@, pre.threads.records@, c as int, t),
            post == pre,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            CapKernel::switch_frame(pre, post, c as int, t),
            post.threads.queues == pre.threads.queues,
            post.cores@[c as int].current_thread == Some(t),
            post.threads.records@[t].value().state == (ThreadState::Running { core: c }),
            post.threads.records@[t].value().frame == pre.threads.records@[t].value().frame,
            post.threads.records@[t].value().saved == pre.threads.records@[t].value().saved,
            post.threads.records@[t].value().save == pre.threads.records@[t].value().save,
            post.threads.records@[t].value().pending_stop == pre.threads.records@[t].value().pending_stop,
            post.threads.records@[t].value().dying == pre.threads.records@[t].value().dying,
            post.threads.records@[t].value().process == pre.threads.records@[t].value().process,
            post.threads.records@[t].value().placement == pre.threads.records@[t].value().placement,
            post.stop_ipis == pre.stop_ipis,
    ;
}

/// `check_current`'s Kept where the thread need not leave, claimed as MovedOff. The kernel is unchanged.
pub trait CheckCurrentKept {
    proof fn wrong(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, saved: FrameKind, ret: CurrentStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            post == pre,
            !pre.must_leave(c as int),
            pre.current_live(c as int),
            ret is MovedOff,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            ret is MovedOff == pre.must_leave(c as int),
            ret is Kept == !pre.must_leave(c as int),
            ret is Kept ==> post == pre,
            post.current_live(c as int),
            ret is Kept ==> post.view() == pre.view(),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
            ret is MovedOff ==> CapKernel::moved_off(pre, post, c as int, frame, saved),
    ;
}

/// `check_current`'s MovedOff at an unchanged kernel whose current thread must leave.
pub trait CheckCurrentMovedOff {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, saved: FrameKind, ret: CurrentStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            post == pre,
            pre.must_leave(c as int),
            !pre.current_live(c as int),
            ret is MovedOff,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            ret is MovedOff == pre.must_leave(c as int),
            ret is Kept == !pre.must_leave(c as int),
            ret is Kept ==> post == pre,
            post.current_live(c as int),
            ret is Kept ==> post.view() == pre.view(),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
            ret is MovedOff ==> CapKernel::moved_off(pre, post, c as int, frame, saved),
    ;
}

/// `switch_thread` at an unchanged idle core whose register already names the arriving thread's space.
/// The space clauses hold; the thread is still runnable and not current.
pub trait SwitchThreadReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, saved: FrameKind, next: Option<usize>, kernel_root: usize)
        requires
            pre.wf(),
            c < NUM_CPUS,
            kernel_root == pre.spaces.kernel_root@,
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
            match pre.cores@[c as int].current_thread {
                Some(o) => !pre.threads.records@[o].value().pending_stop,
                None => true,
            },
            match next {
                Some(t) => {
                    &&& pre.threads.records@.contains_key(t)
                    &&& pre.threads.records@[t].value().state == (ThreadState::Runnable { core: c })
                    &&& pre.threads.records@[t].value().process is Some
                    &&& !pre.threads.records@[t].value().dying
                    &&& pre.processes.records@.contains_key(pre.threads.records@[t].value().process->Some_0)
                    &&& !pre.processes.records@[pre.threads.records@[t].value().process->Some_0].value().dead
                    &&& pre.spaces.roots@.contains_key(pre.threads.records@[t].value().process->Some_0)
                    &&& pre.spaces.records@[pre.threads.records@[t].value().process->Some_0].value().kind is Process
                    &&& pre.cores@[c as int].generation < ID_GENERATION_MAX
                },
                None => true,
            },
            post == pre,
            next is Some,
            pre.cores@[c as int].current_thread is None,
            ({
                let t = next->Some_0;
                let p = pre.threads.records@[t].value().process->Some_0;
                let pcid = id_pcid(pre.spaces.loaded@[p].value().ids@[c as int]);
                let tag = tag_written(c as int, pcid);
                &&& pre.spaces.loaded@.contains_key(p)
                &&& pre.cores@[c as int].space == Some(p)
                &&& pre.loaded(c as int, p)
                &&& holds_id(pre.cores@, pre.spaces.loaded@, c as int, p)
                &&& pre.spaces.registers@[c as int].root() == p + SPACE_ROOT_PAGE * PAGE_SZ
                &&& pre.spaces.registers@[c as int].tag() == tag
                &&& pre.cores@[c as int].next_pcid != PCID_MAX
                &&& pre.tlb@.tags(c as int) == pre.tlb@.tags(c as int).insert(tag)
            }),
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            CapKernel::consumed_kept(pre, post),
            post.cores@[c as int].current_thread == next,
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d],
            forall|d: int| d != c ==> #[trigger] post.spaces.registers@[d] == pre.spaces.registers@[d],
            post.spaces.kernel_root == pre.spaces.kernel_root,
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.spaces.holders == pre.spaces.holders,
            post.spaces.bound == pre.spaces.bound,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && !(d == c as int && next is Some
                && r == pre.threads.records@[next->Some_0].value().process->Some_0)
                ==> #[trigger] post.loaded(d, r) == pre.loaded(d, r),
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.table_pages == pre.table_pages,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            post.iommus == pre.iommus,
            post.devices == pre.devices,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints,
            post.replies == pre.replies,
            post.threads.records@.dom() == pre.threads.records@.dom(),
            post.threads.holders == pre.threads.holders,
            post.threads.boot_thread == pre.threads.boot_thread,
            forall|x: usize| #[trigger] post.threads.records@.contains_key(x)
                && pre.cores@[c as int].current_thread != Some(x) && next != Some(x)
                ==> same_record_perm_but_links(pre.threads.records@[x], post.threads.records@[x]),
            match pre.cores@[c as int].current_thread {
                Some(o) => saves_own_frame(pre.view(), post.view(), o),
                None => post.view() == pre.view(),
            },
            match pre.cores@[c as int].current_thread {
                Some(o) => {
                    let prio = thread_priority(pre.threads.records@[o].value());
                    &&& post.threads.records@[o].value().state == (ThreadState::Runnable { core: c })
                    &&& post.threads.records@[o].value().frame == saved_frame(frame, saved)
                    &&& post.threads.records@[o].value().saved == saved
                    &&& post.threads.records@[o].value().save@ == entry_frame_save(frame, saved)
                    &&& post.threads.records@[o].value().process == pre.threads.records@[o].value().process
                    &&& post.threads.records@[o].value().placement == pre.threads.records@[o].value().placement
                    &&& post.threads.records@[o].value().dying == pre.threads.records@[o].value().dying
                    &&& at_back_of_priority(&post.threads.queues, post.threads.records@, c as int, prio, o)
                    &&& (next is None ==> queued_at_back(&pre.threads.queues, &post.threads.queues, c as int, prio as int, o))
                },
                None => true,
            },
            match next {
                Some(t) => {
                    let p = pre.threads.records@[t].value().process->Some_0;
                    let pcid = id_pcid(post.spaces.loaded@[p].value().ids@[c as int]);
                    let tag = tag_written(c as int, pcid);
                    &&& post.threads.records@[t].value().state == (ThreadState::Running { core: c })
                    &&& post.threads.records@[t].value().process == Some(p)
                    &&& post.threads.records@[t].value().placement == pre.threads.records@[t].value().placement
                    &&& !post.threads.records@[t].value().dying
                    &&& !post.processes.records@[p].value().dead
                    &&& post.current_live(c as int)
                    &&& post.threads.records@[t].value().frame == pre.threads.records@[t].value().frame
                    &&& post.threads.records@[t].value().saved == pre.threads.records@[t].value().saved
                    &&& post.threads.records@[t].value().save == pre.threads.records@[t].value().save
                    &&& pre.cores@[c as int].next_pcid != PCID_MAX
                        ==> post.cores@[c as int].next_pcid <= pre.cores@[c as int].next_pcid + 1
                    &&& post.cores@[c as int].space == Some(p)
                    &&& post.loaded(c as int, p)
                    &&& holds_id(post.cores@, post.spaces.loaded@, c as int, p)
                    &&& post.spaces.registers@[c as int].root() == p + SPACE_ROOT_PAGE * PAGE_SZ
                    &&& post.spaces.registers@[c as int].tag() == tag
                    &&& (holds_id(pre.cores@, pre.spaces.loaded@, c as int, p)
                        || pre.cores@[c as int].next_pcid != PCID_MAX) ==> {
                        &&& post.cores@[c as int].generation == pre.cores@[c as int].generation
                        &&& post.tlb@.tags(c as int) == pre.tlb@.tags(c as int).insert(tag)
                    }
                    &&& (!holds_id(pre.cores@, pre.spaces.loaded@, c as int, p)
                        && pre.cores@[c as int].next_pcid == PCID_MAX) ==> {
                        &&& post.cores@[c as int].generation == pre.cores@[c as int].generation + 1
                        &&& post.tlb@.tags(c as int) == Set::<usize>::empty().insert(tag)
                    }
                },
                None => {
                    &&& post.cores@[c as int].space is None
                    &&& post.spaces.registers@[c as int].root() == kernel_root
                    &&& post.spaces.registers@[c as int].tag() == tag_written(c as int, KERNEL_TAG)
                    &&& post.cores@[c as int].generation == pre.cores@[c as int].generation
                    &&& post.cores@[c as int].next_pcid == pre.cores@[c as int].next_pcid
                    &&& post.tlb@.tags(c as int) == pre.tlb@.tags(c as int).insert(tag_written(c as int, KERNEL_TAG))
                },
            },
    ;
}

/// `map_nested`'s success at an unchanged kernel. The call is allowed, and neither a page nor a large
/// page was written into the nested table.
pub trait MapNestedOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, r: GuestPhysRange, from: usize, page: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_map_nested(root, slot, r, from, page),
            post == pre,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            post.stale_epoch == pre.stale_epoch,
            post.cores == pre.cores,
            post.iommus.present == pre.iommus.present,
            ret == pre.can_map_nested(root, slot, r, from, page),
            post.spaces.loaded == pre.spaces.loaded,
            !ret ==> post == pre,
            ret && r.large() ==> CapKernel::map_large_done(pre, post, root, slot, r.path(), from, page),
            ret && !r.large() ==> CapKernel::map_done(pre, post, root, slot, r.path(), from, page),
            ret ==> discharges(pre.view(), post.view(), root, Effect::Share { space: pre.tables.node_of(root, slot), from: pre.tables.node_of(root, from) }),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
    ;
}

/// `load_space` at an unchanged kernel. The core list, the id word and the retire are as they were,
/// and the returned pcid is not one the ensures name. The space's core-list page is named because a
/// well-formed space has one, which the ensures read.
pub trait LoadSpaceReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, s: usize, pcid: usize)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.spaces.roots@.contains_key(s),
            pre.spaces.records@[s].value().kind is Process,
            pre.cores@[c as int].generation < ID_GENERATION_MAX,
            pre.cores@[c as int].space is None || pre.cores@[c as int].space == Some(s)
                || holds_id(pre.cores@, pre.spaces.loaded@, c as int, s)
                || pre.cores@[c as int].next_pcid != PCID_MAX,
            pre.spaces.loaded@.contains_key(s),
            post == pre,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            pre.cores@[c as int].next_pcid != PCID_MAX ==> {
                &&& post.cores@[c as int].generation == pre.cores@[c as int].generation
                &&& post.cores@[c as int].next_pcid <= pre.cores@[c as int].next_pcid + 1
            },
            CapKernel::step_ok(pre, post, c as int),
            post.loaded(c as int, s),
            post.spaces.loaded@[s].value().retired == 0,
            post.depends(c as int, s),
            1 <= pcid < PCID_MAX,
            holds_id(post.cores@, post.spaces.loaded@, c as int, s),
            id_pcid(post.spaces.loaded@[s].value().ids@[c as int]) == pcid,
            holds_id(pre.cores@, pre.spaces.loaded@, c as int, s) ==> {
                &&& pcid == id_pcid(pre.spaces.loaded@[s].value().ids@[c as int])
                &&& post.cores@[c as int].generation == pre.cores@[c as int].generation
                &&& post.tlb == pre.tlb
            },
            !holds_id(pre.cores@, pre.spaces.loaded@, c as int, s) ==> ({
                &&& !pre.tlb@.tags(c as int).contains(pcid)
                &&& post.cores@[c as int].generation == pre.cores@[c as int].generation
                &&& post.tlb == pre.tlb
            } || {
                &&& post.cores@[c as int].generation == pre.cores@[c as int].generation + 1
                &&& post.tlb@.tags(c as int) == Set::<usize>::empty()
                &&& post.tlb@[c as int] == Set::<TlbEntry>::empty()
                &&& post.acked(c as int) == pre.flush_epoch
            }),
            !holds_id(pre.cores@, pre.spaces.loaded@, c as int, s) && pre.cores@[c as int].next_pcid == PCID_MAX ==> {
                &&& post.cores@[c as int].generation == pre.cores@[c as int].generation + 1
                &&& post.tlb@.tags(c as int) == Set::<usize>::empty()
            },
            forall|r: usize| r != s && #[trigger] holds_id(post.cores@, post.spaces.loaded@, c as int, r) ==> {
                &&& holds_id(pre.cores@, pre.spaces.loaded@, c as int, r)
                &&& post.spaces.loaded@[r] == pre.spaces.loaded@[r]
            },
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && d != c ==> #[trigger] holds_id(post.cores@, post.spaces.loaded@, d, r) == holds_id(pre.cores@, pre.spaces.loaded@, d, r),
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && d != c && post.spaces.loaded@.contains_key(r)
                ==> #[trigger] post.spaces.loaded@[r].value().ids@[d] == pre.spaces.loaded@[r].value().ids@[d],
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d],
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.tlb@[d] == pre.tlb@[d],
            forall|e: TlbEntry| #[trigger] post.tlb@[c as int].contains(e) ==> pre.tlb@[c as int].contains(e),
            post.cores@[c as int].current_thread == pre.cores@[c as int].current_thread,
            post.cores@[c as int].space == pre.cores@[c as int].space,
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && !(d == c as int && r == s)
                ==> #[trigger] post.loaded(d, r) == pre.loaded(d, r),
            forall|e: TlbEntry| e.space == s && space_says(tree_of(&pre.table_pages, &pre.spaces), s, e.page)
                ==> #[trigger] post.core_may_hold(c as int, e),
            post.spaces.loaded@ == pre.spaces.loaded@.insert(s, post.spaces.loaded@[s]),
            post.spaces.loaded@.dom() == pre.spaces.loaded@.dom(),
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.spaces.holders == pre.spaces.holders,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            post.spaces.registers == pre.spaces.registers,
            post.spaces.kernel_root == pre.spaces.kernel_root,
            post.spaces.bound == pre.spaces.bound,
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.table_pages == pre.table_pages,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            post.iommus == pre.iommus,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints,
            post.replies == pre.replies,
    ;
}

/// `switch_space` at an unchanged kernel. The core's record, its base register and its tag set are
/// as they were, so they do not name the space the call points them at.
pub trait SwitchSpaceReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, space: Option<usize>, root: usize, tag: usize)
        requires
            pre.wf(),
            c < NUM_CPUS,
            root % PAGE_SZ == 0,
            space is None ==> mem_valid(root),
            match space {
                Some(s) => {
                    &&& root == s + SPACE_ROOT_PAGE * PAGE_SZ
                    &&& pre.loaded(c as int, s)
                    &&& pre.spaces.loaded@[s].value().retired == 0
                    &&& holds_id(pre.cores@, pre.spaces.loaded@, c as int, s)
                    &&& tag == id_pcid(pre.spaces.loaded@[s].value().ids@[c as int])
                },
                None => {
                    &&& root == pre.spaces.kernel_root@
                    &&& tag == KERNEL_TAG
                },
            },
            match pre.cores@[c as int].current_thread {
                Some(t) => pre.threads.records@[t].value().pending_stop
                    || (space is Some && pre.threads.records@[t].value().process == space),
                None => true,
            },
            post == pre,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            post.cores@[c as int].space == space,
            post.spaces.registers@[c as int].root() == root,
            post.spaces.registers@[c as int].tag() == tag_written(c as int, tag),
            forall|d: int| d != c ==> #[trigger] post.spaces.registers@[d] == pre.spaces.registers@[d],
            post.cores@[c as int].current_thread == pre.cores@[c as int].current_thread,
            post.cores@[c as int].acked_epoch == pre.cores@[c as int].acked_epoch,
            post.cores@[c as int].generation == pre.cores@[c as int].generation,
            post.cores@[c as int].next_pcid == pre.cores@[c as int].next_pcid,
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d],
            forall|d: int, r: usize| 0 <= d < NUM_CPUS ==> #[trigger] holds_id(post.cores@, post.spaces.loaded@, d, r) == holds_id(pre.cores@, pre.spaces.loaded@, d, r),
            post.tlb@.len() == pre.tlb@.len(),
            forall|d: int| #[trigger] post.tlb@[d] == pre.tlb@[d],
            post.tlb@.tags(c as int) == pre.tlb@.tags(c as int).insert(tag_written(c as int, tag)),
            forall|d: int| d != c ==> #[trigger] post.tlb@.tags(d) == pre.tlb@.tags(d),
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.spaces.loaded == pre.spaces.loaded,
            post.spaces.holders == pre.spaces.holders,
            post.spaces.bound == pre.spaces.bound,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            post.spaces.kernel_root == pre.spaces.kernel_root,
            post.spaces == (Spaces { registers: post.spaces.registers, ..pre.spaces }),
            post.list == pre.list,
            post.tables == pre.tables,
            post.blocks == pre.blocks,
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.table_pages == pre.table_pages,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            post.iommus == pre.iommus,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints,
            post.replies == pre.replies,
    ;
}

/// `flush_iommu` at an unchanged kernel. The IOMMU has not taken the epoch and its IOTLB model is
/// not empty.
pub trait FlushIommuReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, i: usize)
        requires
            pre.wf(),
            i < NUM_IOMMUS,
            pre.iommu_present(i as int),
            post == pre,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            post.iommu_acked(i as int) == pre.flush_epoch,
            forall|j: int| 0 <= j < NUM_IOMMUS && j != i ==> #[trigger] post.iommu_acked(j) == pre.iommu_acked(j),
            post.iommus.tlb@[i as int] == Set::<TlbEntry>::empty(),
            CapKernel::only_iommu_changed(pre, post, i as int),
    ;
}

/// `acknowledge` at an unchanged kernel. The core has not taken the epoch, and neither its TLB nor
/// the tags it may hold entries under are empty.
pub trait AcknowledgeReturns {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize)
        requires
            pre.wf(),
            c < NUM_CPUS,
            post == pre,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            CapKernel::step_ok(pre, post, c as int),
            post.acked(c as int) == pre.flush_epoch,
            post.tlb@[c as int] == Set::<TlbEntry>::empty(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.tlb@[d] == pre.tlb@[d],
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            CapKernel::only_core_changed(pre, post, c as int),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d],
            post.cores@[c as int].generation == pre.cores@[c as int].generation,
            post.cores@[c as int].next_pcid == pre.cores@[c as int].next_pcid,
            post.tlb@.tags(c as int) == Set::<usize>::empty(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.tlb@.tags(d) == pre.tlb@.tags(d),
    ;
}

/// `probe_at`'s Some at an unchanged kernel. The call is allowed. The view is what the specification
/// keeps, and the level 1 table's words are part of the kernel, so an unchanged kernel has not cleared
/// their accessed and dirty bits.
pub trait ProbeAtSome {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, va: u64, count: u64, ret: Option<Probed>)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_probe(root, slot, va, count),
            post == pre,
            ret is Some,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::probe_answered(pre, post, root, slot, va, count, ret is Some),
            ret is Some ==> CapKernel::probe_done(pre, post, root, slot, va, count, ret->0),
            discharges(pre.view(), post.view(), root, Effect::Local),
            CapKernel::threads_bound_kept(pre, post),
    ;
}

/// `add_devices`'s success at an unchanged kernel. The call is allowed, the device table was empty, and
/// boot gave at least one device: an empty list is a success that writes nothing, and this is the
/// success that records a device. The step counter is unchanged, so the operation's bound on it holds.
/// An unchanged table keeps the count it had, and the free slots stay free.
pub trait AddDevicesOk {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        first: usize,
        root: usize,
        slot: usize,
        devices: &Array<DeviceInfo, MAX_DEVICES>,
        count: usize,
        pre_steps: nat,
        post_steps: nat,
        ret: bool,
    )
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            first == pre.list.seq@[0],
            pre.devices.count == 0,
            devices.wf(),
            0 < count <= MAX_DEVICES,
            slot + count <= usize::MAX,
            post == pre,
            post_steps == pre_steps,
            pre.can_add_devices(root, slot, devices@, count),
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post_steps <= pre_steps + MAX_DEVICES * (MAX_DEVICES + 1),
            post.wf(),
            ret == pre.can_add_devices(root, slot, devices@, count),
            post.tables.roots == pre.tables.roots,
            post.tables.owner == pre.tables.owner,
            post.list.seq@[0] == pre.list.seq@[0],
            post.blocks == pre.blocks,
            post.iommus == pre.iommus,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints,
            post.replies == pre.replies,
            post.spaces == pre.spaces,
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            ret ==> post.devices.count == count,
            ret ==> forall|k: int| 0 <= k < count ==> #[trigger] post.devices.records@[k] == unbound_record(devices@[k]),
            ret ==> forall|k: int| 0 <= k < count ==> post.slot_holds(root, (slot + k) as usize, pre.tables.node_of(root, (slot + k) as usize), device_payload(k)),
            ret ==> forall|k: int| 0 <= k < count ==> #[trigger] post.list.is_child(first, pre.tables.node_of(root, (slot + k) as usize)),
            ret ==> post.devices.records@.len() == pre.devices.records@.len(),
            ret ==> forall|k: int| count <= k < pre.devices.records@.len() ==> #[trigger] post.devices.records@[k] == pre.devices.records@[k],
            ret ==> forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && pre.apart_from_devices(root, slot, count as int, i) ==> post.list.nodes@[i].live == pre.list.nodes@[i].live && post.list.nodes@[i].kind == pre.list.nodes@[i].kind && post.list.nodes@[i].depth == pre.list.nodes@[i].depth,
            ret ==> forall|x: usize| #![trigger post.list.parent@.contains_key(x)] pre.apart_from_devices(root, slot, count as int, x as int) ==> post.list.parent@.contains_key(x) == pre.list.parent@.contains_key(x) && (pre.list.parent@.contains_key(x) ==> post.list.parent@[x] == pre.list.parent@[x]),
            ret ==> forall|x: usize| #![trigger post.is_cap(x)] #![trigger pre.is_cap(x)] pre.apart_from_devices(root, slot, count as int, x as int) ==> post.is_cap(x) == pre.is_cap(x) && (pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x)),
    ;
}

/// `bind_device`'s success at an unchanged kernel. The call is allowed, and the binding node did not
/// become a child of the space, so the view's binds did not gain the device.
pub trait BindDeviceOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, j: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_bind_device(root, i, j),
            post == pre,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            ret == pre.can_bind_device(root, i, j),
            !ret ==> post == pre,
            ret ==> CapKernel::device_bound(pre, post, pre.tables.node_of(root, j), device_of(pre.payload_of(pre.tables.node_of(root, i)).base)),
            ret ==> post.view().binds == pre.view().binds.insert(pre.payload_of(pre.tables.node_of(root, i)).base, pre.payload_of(pre.tables.node_of(root, j)).base),
            discharges(pre.view(), post.view(), root, Effect::Local),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
    ;
}

/// `unbind_device_at`'s success at an unchanged kernel. The call is allowed. The step counter is
/// unchanged, so the operation's bound on it holds. The flush epoch did not advance and the binding
/// node is still live, so the device did not leave the view's binds.
pub trait UnbindDeviceOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, i: usize, pre_steps: nat, post_steps: nat, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_unbind_device(root, i),
            post == pre,
            post_steps == pre_steps,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            post_steps <= pre_steps + UNLINK_ARM_STEPS,
            ret == pre.can_unbind_device(root, i),
            !ret ==> post == pre,
            ret ==> CapKernel::device_unbound(pre, post, binding_node(&pre.devices, device_of(pre.payload_of(pre.tables.node_of(root, i)).base))),
            ret ==> !post.list.nodes@[binding_node(&pre.devices, device_of(pre.payload_of(pre.tables.node_of(root, i)).base)) as int].live,
            ret ==> forall|y: int| #![trigger post.list.nodes@[y]] 0 <= y < NODE_SPACE && y != binding_node(&pre.devices, device_of(pre.payload_of(pre.tables.node_of(root, i)).base)) as int ==> post.list.nodes@[y].live == pre.list.nodes@[y].live && post.list.nodes@[y].kind == pre.list.nodes@[y].kind && post.list.nodes@[y].depth == pre.list.nodes@[y].depth,
            ret ==> post.list.parent == pre.list.parent,
            ret ==> post.tables == pre.tables,
            ret ==> post.table_pages == pre.table_pages,
            ret ==> post.mappings == pre.mappings,
            ret ==> post.threads == pre.threads,
            ret ==> post.processes == pre.processes,
            ret ==> post.endpoints == pre.endpoints,
            ret ==> post.replies == pre.replies,
            ret ==> post.holders == pre.holders,
            ret ==> post.iommus == pre.iommus,
            ret ==> post.cores == pre.cores,
            ret ==> post.view().binds == pre.view().binds.remove(pre.payload_of(pre.tables.node_of(root, i)).base),
            ret ==> forall|q: usize, a: usize, b: usize| device_of(post.payload_of(post.tables.node_of(q, a)).base) == device_of(pre.payload_of(pre.tables.node_of(root, i)).base) ==> !#[trigger] post.can_bind_device(q, a, b),
            discharges(pre.view(), post.view(), root, Effect::Local),
    ;
}

/// `map_device`'s success at an unchanged kernel. The call is allowed and nothing was written, so
/// neither a page nor a large page was mapped into the device space.
pub trait MapDeviceOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, slot: usize, r: DeviceRange, from: usize, page: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_map_device(root, slot, r, from, page),
            post == pre,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            post.stale_epoch == pre.stale_epoch,
            post.cores == pre.cores,
            post.iommus.present == pre.iommus.present,
            ret == pre.can_map_device(root, slot, r, from, page),
            post.spaces.loaded == pre.spaces.loaded,
            !ret ==> post == pre,
            ret && r.large() ==> CapKernel::map_large_done(pre, post, root, slot, r.path(), from, page),
            ret && !r.large() ==> CapKernel::map_done(pre, post, root, slot, r.path(), from, page),
            ret ==> discharges(pre.view(), post.view(), root, Effect::Share { space: pre.tables.node_of(root, slot), from: pre.tables.node_of(root, from) }),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
    ;
}


/// reclaim's Freed meets no unchanged kernel: a dead queue the untyped covers is still that queue.
/// The requires are the operation's, the unchanged kernel and this way. The other success
/// conditions are closed, so Verus meets every ensures conjunct except the one this way changes.
/// design/refused-claim-per-way/.
pub trait ReclaimFreed {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, from: usize, base: usize, pre_steps: nat, post_steps: nat, ret: ReclaimStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            post == pre,
            post_steps == pre_steps,
            ret is Freed,
            pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ),
            !pre.can_unlink_leaf(root, from, base),
            !pre.can_slice_leaf(root, from, base),
            pre.view().holds_right(root, pre.tables.node_of(root, from), Right::Retype),
            !pre.spaces.roots@.contains_key(base),
            !pre.processes.records@.contains_key(base),
            !pre.table_pages.maps@.contains_key(base),
            !pre.threads.records@.contains_key(base),
            !pre.can_reclaim_large(root, from, base, 9),
            !pre.can_reclaim_large(root, from, base, 18),
            !pre.can_unlink_table(root, from, base),
            !pre.can_slice_table(root, from, base),
            !pre.can_cut_table(root, from, base),
            !pre.can_cut_space(root, from, base),
            !pre.can_retire_process(root, from, base),
            !pre.can_cut_process_space(root, from, base),
            !pre.can_unbind_thread(root, from, base),
            !(pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.table_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.space_is_spent(base)),
            !(pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base)),
            !pre.frame_is_dead(base / PAGE_SZ),
            !pre.reply_is_dead(base / PAGE_SZ),
            !pre.leaf_is_empty(base),
            !pre.table_is_empty(base),
            !pre.space_is_empty(base),
            !pre.thread_is_spent(base),
            !pre.process_is_spent(base),
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post_steps <= pre_steps + (NODES_PER_PAGE - 1) + LEAF_SLICE_BUDGET * (REVOKE_STEP_STEPS + 1) + (NODES_PER_PAGE + 2 * (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX),
            post.wf(),
            CapKernel::mappings_shrunk(pre, post),
            ret is Refused || ret is Again ==> post == pre,
            !((pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(base / PAGE_SZ)) || pre.can_unlink_leaf(root, from, base) || (pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base)) || pre.can_slice_leaf(root, from, base) || pre.can_unlink_table(root, from, base) || pre.can_slice_table(root, from, base) || (pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base)) || pre.can_cut_space(root, from, base) || (pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base)) || pre.can_retire_process(root, from, base) || pre.can_cut_process_space(root, from, base) || (pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)) || pre.can_unbind_thread(root, from, base) || (pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base)) || pre.can_reclaim_large(root, from, base, 9) || pre.can_reclaim_large(root, from, base, 18) || (pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ)) || (pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ))) ==> ret is Refused,
            pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ) ==> ret is Freed && pre.queue_freed(post, c, root, from, base),
            pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ) ==> ret is Freed && pre.reply_freed(post, c, root, from, base),
            pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(base / PAGE_SZ) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed && pre.frame_freed(post, c, root, from, base) } else { ret is Again },
            pre.can_reclaim_large(root, from, base, 9) ==> if pre.region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M) { ret is Freed && pre.large_frame_freed(post, c, root, from, base, 9) } else { ret is Again },
            pre.can_reclaim_large(root, from, base, 18) ==> if pre.region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G) { ret is Freed && pre.large_frame_freed(post, c, root, from, base, 18) } else { ret is Again },
            !pre.view().holds_right(root, pre.tables.node_of(root, from), Right::Retype) ==> ret is Refused,
            pre.spaces.roots@.contains_key(base) && !pre.dead_io_space(base) && !pre.can_retire_process(root, from, base) && !pre.can_cut_process_space(root, from, base) && !(pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)) ==> ret is Refused,
            pre.can_cut_space(root, from, base) ==> ret is Slice,
            pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.can_retype_under(root, from, base, 3) && pre.space_is_spent(base) ==> ret is Again || ret is Freed,
            pre.spaces.roots@.contains_key(base) && !(pre.spaces.records@[base].value().kind is Process) && ret is Slice ==> pre.space_children_cut(post, root, from, base),
            pre.processes.records@.contains_key(base) && (pre.blocks.pages@[(base / PAGE_SZ) as int].refs != 0 || (!pre.process_released(base) && !pre.can_retire_process(root, from, base))) ==> ret is Refused,
            pre.processes.records@.contains_key(base) && (exists|d: int, t: usize| #![trigger pre.cores@[d], pre.threads.records@[t]] 0 <= d < NUM_CPUS && pre.cores@[d].current_thread == Some(t) && pre.threads.records@[t].value().process == Some(base)) ==> ret is Refused,
            pre.processes.records@.contains_key(base) && (exists|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base && #[trigger] pre.tlb@[d].contains(e)) ==> !pre.process_released(base) && (ret is Refused || ret is Slice && pre.process_retired(post, base)),
            pre.can_retire_process(root, from, base) ==> ret is Slice && pre.process_retired(post, base),
            pre.processes.records@.contains_key(base) && pre.process_space_named(base) ==> ret is Refused,
            pre.can_cut_process_space(root, from, base) ==> ret is Slice && pre.process_space_cut(post, root, from, base),
            pre.processes.records@.contains_key(base) && ret is Slice ==> pre.process_retired(post, base) || pre.process_space_cut(post, root, from, base),
            pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.processes.records@.contains_key(base) && ret is Freed ==> pre.process_freed(post, c, root, from, base),
            pre.spaces.roots@.contains_key(base) && !(pre.spaces.records@[base].value().kind is Process) && ret is Freed ==> pre.space_freed(post, c, root, from, base),
            pre.can_unlink_table(root, from, base) ==> ret is Unlinked,
            pre.can_slice_table(root, from, base) ==> ret is Slice,
            pre.can_cut_table(root, from, base) ==> ret is Slice && pre.table_children_cut(post, root, from, base),
            pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.can_retype_under(root, from, base, 3) && pre.table_is_spent(base) ==> ret is Again || ret is Freed,
            pre.table_pages.maps@.contains_key(base) && ret is Unlinked ==> pre.table_page_unlinked(post, root, from, base),
            pre.table_pages.maps@.contains_key(base) && ret is Slice ==> pre.table_sliced(post, root, from, base),
            pre.table_pages.maps@.contains_key(base) && ret is Freed ==> pre.table_freed(post, c, root, from, base),
            pre.can_unbind_thread(root, from, base) ==> ret is Slice,
            pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base) ==> if pre.acknowledged(base / PAGE_SZ) && pre.acknowledged((base / PAGE_SZ + 1) as usize) { ret is Freed } else { ret is Again },
            pre.threads.records@.contains_key(base) && ret is Slice ==> pre.thread_unbound(post, root, from, base),
            pre.threads.records@.contains_key(base) && ret is Freed ==> pre.thread_freed(post, c, root, from, base),
            pre.can_unlink_leaf(root, from, base) ==> ret is Unlinked && pre.leaf_unlinked(post, root, from, base),
            pre.can_slice_leaf(root, from, base) ==> ret is Slice && pre.leaf_sliced(post, root, from, base),
            pre.can_slice_leaf(root, from, base) && pre.leaf_slots_childless(base) ==> pre.leaf_slice_kept(post, base),
            pre.can_slice_leaf(root, from, base) && pre.leaf_slots_childless(base) && pre.leaf_live_slots(base) <= LEAF_SLICE_BUDGET ==> post.leaf_is_empty(base),
            pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) && pre.acknowledged((base / PAGE_SZ + 1) as usize) { ret is Freed && pre.leaf_freed(post, c, root, from, base) } else { ret is Again },
            ret is Again ==> !pre.acknowledged(base / PAGE_SZ) || !pre.acknowledged((base / PAGE_SZ + 1) as usize) || !pre.region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M) || !pre.region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G),
            ret is Freed ==> pre.frame_freed(post, c, root, from, base) || pre.large_frame_freed(post, c, root, from, base, 9) || pre.large_frame_freed(post, c, root, from, base, 18) || pre.leaf_freed(post, c, root, from, base) || pre.table_freed(post, c, root, from, base) || pre.space_freed(post, c, root, from, base) || pre.thread_freed(post, c, root, from, base) || pre.process_freed(post, c, root, from, base) || pre.queue_freed(post, c, root, from, base) || pre.reply_freed(post, c, root, from, base),
            ret is Slice ==> pre.leaf_sliced(post, root, from, base) || pre.table_sliced(post, root, from, base) || pre.space_children_cut(post, root, from, base) || pre.thread_unbound(post, root, from, base) || pre.process_retired(post, base) || pre.process_space_cut(post, root, from, base),
            ret is Unlinked ==> pre.leaf_unlinked(post, root, from, base) || pre.table_page_unlinked(post, root, from, base),
    ;
}

/// reclaim's Unlinked meets no unchanged kernel: the leaf's hidden node is still live.
/// The requires are the operation's, the unchanged kernel and this way. The other success
/// conditions are closed, so Verus meets every ensures conjunct except the one this way changes.
/// design/refused-claim-per-way/.
pub trait ReclaimUnlinked {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, from: usize, base: usize, pre_steps: nat, post_steps: nat, ret: ReclaimStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            post == pre,
            post_steps == pre_steps,
            ret is Unlinked,
            pre.can_unlink_leaf(root, from, base),
            !pre.can_slice_leaf(root, from, base),
            !(pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ)),
            !(pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ)),
            pre.view().holds_right(root, pre.tables.node_of(root, from), Right::Retype),
            !pre.spaces.roots@.contains_key(base),
            !pre.processes.records@.contains_key(base),
            !pre.table_pages.maps@.contains_key(base),
            !pre.threads.records@.contains_key(base),
            !pre.can_reclaim_large(root, from, base, 9),
            !pre.can_reclaim_large(root, from, base, 18),
            !pre.can_unlink_table(root, from, base),
            !pre.can_slice_table(root, from, base),
            !pre.can_cut_table(root, from, base),
            !pre.can_cut_space(root, from, base),
            !pre.can_retire_process(root, from, base),
            !pre.can_cut_process_space(root, from, base),
            !pre.can_unbind_thread(root, from, base),
            !(pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.table_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.space_is_spent(base)),
            !(pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base)),
            !pre.frame_is_dead(base / PAGE_SZ),
            !pre.reply_is_dead(base / PAGE_SZ),
            !pre.leaf_is_empty(base),
            !pre.table_is_empty(base),
            !pre.space_is_empty(base),
            !pre.thread_is_spent(base),
            !pre.process_is_spent(base),
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post_steps <= pre_steps + (NODES_PER_PAGE - 1) + LEAF_SLICE_BUDGET * (REVOKE_STEP_STEPS + 1) + (NODES_PER_PAGE + 2 * (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX),
            post.wf(),
            CapKernel::mappings_shrunk(pre, post),
            ret is Refused || ret is Again ==> post == pre,
            !((pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(base / PAGE_SZ)) || pre.can_unlink_leaf(root, from, base) || (pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base)) || pre.can_slice_leaf(root, from, base) || pre.can_unlink_table(root, from, base) || pre.can_slice_table(root, from, base) || (pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base)) || pre.can_cut_space(root, from, base) || (pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base)) || pre.can_retire_process(root, from, base) || pre.can_cut_process_space(root, from, base) || (pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)) || pre.can_unbind_thread(root, from, base) || (pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base)) || pre.can_reclaim_large(root, from, base, 9) || pre.can_reclaim_large(root, from, base, 18) || (pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ)) || (pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ))) ==> ret is Refused,
            pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ) ==> ret is Freed && pre.queue_freed(post, c, root, from, base),
            pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ) ==> ret is Freed && pre.reply_freed(post, c, root, from, base),
            pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(base / PAGE_SZ) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed && pre.frame_freed(post, c, root, from, base) } else { ret is Again },
            pre.can_reclaim_large(root, from, base, 9) ==> if pre.region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M) { ret is Freed && pre.large_frame_freed(post, c, root, from, base, 9) } else { ret is Again },
            pre.can_reclaim_large(root, from, base, 18) ==> if pre.region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G) { ret is Freed && pre.large_frame_freed(post, c, root, from, base, 18) } else { ret is Again },
            !pre.view().holds_right(root, pre.tables.node_of(root, from), Right::Retype) ==> ret is Refused,
            pre.spaces.roots@.contains_key(base) && !pre.dead_io_space(base) && !pre.can_retire_process(root, from, base) && !pre.can_cut_process_space(root, from, base) && !(pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)) ==> ret is Refused,
            pre.can_cut_space(root, from, base) ==> ret is Slice,
            pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.can_retype_under(root, from, base, 3) && pre.space_is_spent(base) ==> ret is Again || ret is Freed,
            pre.spaces.roots@.contains_key(base) && !(pre.spaces.records@[base].value().kind is Process) && ret is Slice ==> pre.space_children_cut(post, root, from, base),
            pre.processes.records@.contains_key(base) && (pre.blocks.pages@[(base / PAGE_SZ) as int].refs != 0 || (!pre.process_released(base) && !pre.can_retire_process(root, from, base))) ==> ret is Refused,
            pre.processes.records@.contains_key(base) && (exists|d: int, t: usize| #![trigger pre.cores@[d], pre.threads.records@[t]] 0 <= d < NUM_CPUS && pre.cores@[d].current_thread == Some(t) && pre.threads.records@[t].value().process == Some(base)) ==> ret is Refused,
            pre.processes.records@.contains_key(base) && (exists|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base && #[trigger] pre.tlb@[d].contains(e)) ==> !pre.process_released(base) && (ret is Refused || ret is Slice && pre.process_retired(post, base)),
            pre.can_retire_process(root, from, base) ==> ret is Slice && pre.process_retired(post, base),
            pre.processes.records@.contains_key(base) && pre.process_space_named(base) ==> ret is Refused,
            pre.can_cut_process_space(root, from, base) ==> ret is Slice && pre.process_space_cut(post, root, from, base),
            pre.processes.records@.contains_key(base) && ret is Slice ==> pre.process_retired(post, base) || pre.process_space_cut(post, root, from, base),
            pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.processes.records@.contains_key(base) && ret is Freed ==> pre.process_freed(post, c, root, from, base),
            pre.spaces.roots@.contains_key(base) && !(pre.spaces.records@[base].value().kind is Process) && ret is Freed ==> pre.space_freed(post, c, root, from, base),
            pre.can_unlink_table(root, from, base) ==> ret is Unlinked,
            pre.can_slice_table(root, from, base) ==> ret is Slice,
            pre.can_cut_table(root, from, base) ==> ret is Slice && pre.table_children_cut(post, root, from, base),
            pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.can_retype_under(root, from, base, 3) && pre.table_is_spent(base) ==> ret is Again || ret is Freed,
            pre.table_pages.maps@.contains_key(base) && ret is Unlinked ==> pre.table_page_unlinked(post, root, from, base),
            pre.table_pages.maps@.contains_key(base) && ret is Slice ==> pre.table_sliced(post, root, from, base),
            pre.table_pages.maps@.contains_key(base) && ret is Freed ==> pre.table_freed(post, c, root, from, base),
            pre.can_unbind_thread(root, from, base) ==> ret is Slice,
            pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base) ==> if pre.acknowledged(base / PAGE_SZ) && pre.acknowledged((base / PAGE_SZ + 1) as usize) { ret is Freed } else { ret is Again },
            pre.threads.records@.contains_key(base) && ret is Slice ==> pre.thread_unbound(post, root, from, base),
            pre.threads.records@.contains_key(base) && ret is Freed ==> pre.thread_freed(post, c, root, from, base),
            pre.can_unlink_leaf(root, from, base) ==> ret is Unlinked && pre.leaf_unlinked(post, root, from, base),
            pre.can_slice_leaf(root, from, base) ==> ret is Slice && pre.leaf_sliced(post, root, from, base),
            pre.can_slice_leaf(root, from, base) && pre.leaf_slots_childless(base) ==> pre.leaf_slice_kept(post, base),
            pre.can_slice_leaf(root, from, base) && pre.leaf_slots_childless(base) && pre.leaf_live_slots(base) <= LEAF_SLICE_BUDGET ==> post.leaf_is_empty(base),
            pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) && pre.acknowledged((base / PAGE_SZ + 1) as usize) { ret is Freed && pre.leaf_freed(post, c, root, from, base) } else { ret is Again },
            ret is Again ==> !pre.acknowledged(base / PAGE_SZ) || !pre.acknowledged((base / PAGE_SZ + 1) as usize) || !pre.region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M) || !pre.region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G),
            ret is Freed ==> pre.frame_freed(post, c, root, from, base) || pre.large_frame_freed(post, c, root, from, base, 9) || pre.large_frame_freed(post, c, root, from, base, 18) || pre.leaf_freed(post, c, root, from, base) || pre.table_freed(post, c, root, from, base) || pre.space_freed(post, c, root, from, base) || pre.thread_freed(post, c, root, from, base) || pre.process_freed(post, c, root, from, base) || pre.queue_freed(post, c, root, from, base) || pre.reply_freed(post, c, root, from, base),
            ret is Slice ==> pre.leaf_sliced(post, root, from, base) || pre.table_sliced(post, root, from, base) || pre.space_children_cut(post, root, from, base) || pre.thread_unbound(post, root, from, base) || pre.process_retired(post, base) || pre.process_space_cut(post, root, from, base),
            ret is Unlinked ==> pre.leaf_unlinked(post, root, from, base) || pre.table_page_unlinked(post, root, from, base),
    ;
}

/// reclaim's Slice meets no unchanged kernel: the leaf's list is not shorter.
/// The requires are the operation's, the unchanged kernel and this way. The other success
/// conditions are closed, so Verus meets every ensures conjunct except the one this way changes.
/// design/refused-claim-per-way/.
pub trait ReclaimSlice {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, from: usize, base: usize, pre_steps: nat, post_steps: nat, ret: ReclaimStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            post == pre,
            post_steps == pre_steps,
            ret is Slice,
            pre.can_slice_leaf(root, from, base),
            !pre.leaf_slots_childless(base),
            !pre.can_unlink_leaf(root, from, base),
            !(pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ)),
            !(pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ)),
            pre.view().holds_right(root, pre.tables.node_of(root, from), Right::Retype),
            !pre.spaces.roots@.contains_key(base),
            !pre.processes.records@.contains_key(base),
            !pre.table_pages.maps@.contains_key(base),
            !pre.threads.records@.contains_key(base),
            !pre.can_reclaim_large(root, from, base, 9),
            !pre.can_reclaim_large(root, from, base, 18),
            !pre.can_unlink_table(root, from, base),
            !pre.can_slice_table(root, from, base),
            !pre.can_cut_table(root, from, base),
            !pre.can_cut_space(root, from, base),
            !pre.can_retire_process(root, from, base),
            !pre.can_cut_process_space(root, from, base),
            !pre.can_unbind_thread(root, from, base),
            !(pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.table_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 3) && pre.space_is_spent(base)),
            !(pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base)),
            !(pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base)),
            !pre.frame_is_dead(base / PAGE_SZ),
            !pre.reply_is_dead(base / PAGE_SZ),
            !pre.leaf_is_empty(base),
            !pre.table_is_empty(base),
            !pre.space_is_empty(base),
            !pre.thread_is_spent(base),
            !pre.process_is_spent(base),
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post_steps <= pre_steps + (NODES_PER_PAGE - 1) + LEAF_SLICE_BUDGET * (REVOKE_STEP_STEPS + 1) + (NODES_PER_PAGE + 2 * (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX),
            post.wf(),
            CapKernel::mappings_shrunk(pre, post),
            ret is Refused || ret is Again ==> post == pre,
            !((pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(base / PAGE_SZ)) || pre.can_unlink_leaf(root, from, base) || (pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base)) || pre.can_slice_leaf(root, from, base) || pre.can_unlink_table(root, from, base) || pre.can_slice_table(root, from, base) || (pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base)) || pre.can_cut_space(root, from, base) || (pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base)) || pre.can_retire_process(root, from, base) || pre.can_cut_process_space(root, from, base) || (pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)) || pre.can_unbind_thread(root, from, base) || (pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base)) || pre.can_reclaim_large(root, from, base, 9) || pre.can_reclaim_large(root, from, base, 18) || (pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ)) || (pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ))) ==> ret is Refused,
            pre.can_retype_under(root, from, base, 0) && pre.queue_is_dead(base / PAGE_SZ) ==> ret is Freed && pre.queue_freed(post, c, root, from, base),
            pre.can_retype_under(root, from, base, 0) && pre.reply_is_dead(base / PAGE_SZ) ==> ret is Freed && pre.reply_freed(post, c, root, from, base),
            pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(base / PAGE_SZ) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed && pre.frame_freed(post, c, root, from, base) } else { ret is Again },
            pre.can_reclaim_large(root, from, base, 9) ==> if pre.region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M) { ret is Freed && pre.large_frame_freed(post, c, root, from, base, 9) } else { ret is Again },
            pre.can_reclaim_large(root, from, base, 18) ==> if pre.region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G) { ret is Freed && pre.large_frame_freed(post, c, root, from, base, 18) } else { ret is Again },
            !pre.view().holds_right(root, pre.tables.node_of(root, from), Right::Retype) ==> ret is Refused,
            pre.spaces.roots@.contains_key(base) && !pre.dead_io_space(base) && !pre.can_retire_process(root, from, base) && !pre.can_cut_process_space(root, from, base) && !(pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base)) ==> ret is Refused,
            pre.can_cut_space(root, from, base) ==> ret is Slice,
            pre.can_retype_under(root, from, base, 3) && pre.space_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.can_retype_under(root, from, base, 3) && pre.space_is_spent(base) ==> ret is Again || ret is Freed,
            pre.spaces.roots@.contains_key(base) && !(pre.spaces.records@[base].value().kind is Process) && ret is Slice ==> pre.space_children_cut(post, root, from, base),
            pre.processes.records@.contains_key(base) && (pre.blocks.pages@[(base / PAGE_SZ) as int].refs != 0 || (!pre.process_released(base) && !pre.can_retire_process(root, from, base))) ==> ret is Refused,
            pre.processes.records@.contains_key(base) && (exists|d: int, t: usize| #![trigger pre.cores@[d], pre.threads.records@[t]] 0 <= d < NUM_CPUS && pre.cores@[d].current_thread == Some(t) && pre.threads.records@[t].value().process == Some(base)) ==> ret is Refused,
            pre.processes.records@.contains_key(base) && (exists|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && e.space == base && #[trigger] pre.tlb@[d].contains(e)) ==> !pre.process_released(base) && (ret is Refused || ret is Slice && pre.process_retired(post, base)),
            pre.can_retire_process(root, from, base) ==> ret is Slice && pre.process_retired(post, base),
            pre.processes.records@.contains_key(base) && pre.process_space_named(base) ==> ret is Refused,
            pre.can_cut_process_space(root, from, base) ==> ret is Slice && pre.process_space_cut(post, root, from, base),
            pre.processes.records@.contains_key(base) && ret is Slice ==> pre.process_retired(post, base) || pre.process_space_cut(post, root, from, base),
            pre.can_retype_under(root, from, base, PROCESS_ORDER) && pre.process_is_spent(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.processes.records@.contains_key(base) && ret is Freed ==> pre.process_freed(post, c, root, from, base),
            pre.spaces.roots@.contains_key(base) && !(pre.spaces.records@[base].value().kind is Process) && ret is Freed ==> pre.space_freed(post, c, root, from, base),
            pre.can_unlink_table(root, from, base) ==> ret is Unlinked,
            pre.can_slice_table(root, from, base) ==> ret is Slice,
            pre.can_cut_table(root, from, base) ==> ret is Slice && pre.table_children_cut(post, root, from, base),
            pre.can_retype_under(root, from, base, 3) && pre.table_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) { ret is Freed } else { ret is Again },
            pre.can_retype_under(root, from, base, 3) && pre.table_is_spent(base) ==> ret is Again || ret is Freed,
            pre.table_pages.maps@.contains_key(base) && ret is Unlinked ==> pre.table_page_unlinked(post, root, from, base),
            pre.table_pages.maps@.contains_key(base) && ret is Slice ==> pre.table_sliced(post, root, from, base),
            pre.table_pages.maps@.contains_key(base) && ret is Freed ==> pre.table_freed(post, c, root, from, base),
            pre.can_unbind_thread(root, from, base) ==> ret is Slice,
            pre.can_retype_under(root, from, base, 1) && pre.thread_is_spent(base) ==> if pre.acknowledged(base / PAGE_SZ) && pre.acknowledged((base / PAGE_SZ + 1) as usize) { ret is Freed } else { ret is Again },
            pre.threads.records@.contains_key(base) && ret is Slice ==> pre.thread_unbound(post, root, from, base),
            pre.threads.records@.contains_key(base) && ret is Freed ==> pre.thread_freed(post, c, root, from, base),
            pre.can_unlink_leaf(root, from, base) ==> ret is Unlinked && pre.leaf_unlinked(post, root, from, base),
            pre.can_slice_leaf(root, from, base) ==> ret is Slice && pre.leaf_sliced(post, root, from, base),
            pre.can_slice_leaf(root, from, base) && pre.leaf_slots_childless(base) ==> pre.leaf_slice_kept(post, base),
            pre.can_slice_leaf(root, from, base) && pre.leaf_slots_childless(base) && pre.leaf_live_slots(base) <= LEAF_SLICE_BUDGET ==> post.leaf_is_empty(base),
            pre.can_retype_under(root, from, base, 1) && pre.leaf_is_empty(base) ==> if pre.acknowledged(base / PAGE_SZ) && pre.acknowledged((base / PAGE_SZ + 1) as usize) { ret is Freed && pre.leaf_freed(post, c, root, from, base) } else { ret is Again },
            ret is Again ==> !pre.acknowledged(base / PAGE_SZ) || !pre.acknowledged((base / PAGE_SZ + 1) as usize) || !pre.region_acknowledged(Large::Two, base / PAGE_SZ / PAGES_PER_2M) || !pre.region_acknowledged(Large::One, base / PAGE_SZ / PAGES_PER_1G),
            ret is Freed ==> pre.frame_freed(post, c, root, from, base) || pre.large_frame_freed(post, c, root, from, base, 9) || pre.large_frame_freed(post, c, root, from, base, 18) || pre.leaf_freed(post, c, root, from, base) || pre.table_freed(post, c, root, from, base) || pre.space_freed(post, c, root, from, base) || pre.thread_freed(post, c, root, from, base) || pre.process_freed(post, c, root, from, base) || pre.queue_freed(post, c, root, from, base) || pre.reply_freed(post, c, root, from, base),
            ret is Slice ==> pre.leaf_sliced(post, root, from, base) || pre.table_sliced(post, root, from, base) || pre.space_children_cut(post, root, from, base) || pre.thread_unbound(post, root, from, base) || pre.process_retired(post, base) || pre.process_space_cut(post, root, from, base),
            ret is Unlinked ==> pre.leaf_unlinked(post, root, from, base) || pre.table_page_unlinked(post, root, from, base),
    ;
}

/// reclaim_frame's Freed meets no unchanged kernel: the dead frame every core has acknowledged is still that frame.
/// design/refused-claim-per-way/.
pub trait ReclaimFrameFreed {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, from: usize, base: usize, pre_steps: nat, post_steps: nat, ret: FrameReclaimStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            post == pre,
            post_steps == pre_steps,
            ret is Freed,
            pre.can_retype_under(root, from, base, 0),
            pre.frame_is_dead(base / PAGE_SZ),
            pre.acknowledged(base / PAGE_SZ),
        ensures
            CapKernel::page_count_kept(pre, post),
            post_steps <= pre_steps + (NUM_CPUS + NUM_IOMMUS) + SMALL_PAGES_MAX,
            post.wf(),
            CapKernel::same_tree(pre, post),
            CapKernel::frame_reclaim_answered(pre, post, root, from, base, ret),
            ret is Freed ==> pre.frame_freed(post, c, root, from, base),
    ;
}

/// reclaim_large_frame's Freed meets no unchanged kernel: the dead large frame every core has acknowledged is still typed.
/// design/refused-claim-per-way/.
pub trait ReclaimLargeFreed {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, root: usize, from: usize, base: usize, pre_steps: nat, post_steps: nat, order: u8, ret: FrameReclaimStep)
        requires
            pre.wf(),
            c < NUM_CPUS,
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            post == pre,
            post_steps == pre_steps,
            ret is Freed,
            pre.can_reclaim_large(root, from, base, order),
            pre.region_acknowledged(large_level(order), base / PAGE_SZ / level_pages(large_level(order))),
        ensures
            CapKernel::page_count_kept(pre, post),
            post_steps <= pre_steps + NUM_CPUS + NUM_IOMMUS,
            ret is Refused ==> post_steps == pre_steps,
            post.wf(),
            CapKernel::same_tree(pre, post),
            CapKernel::large_reclaim_answered(pre, post, root, from, base, order, ret),
            ret is Freed ==> pre.large_frame_freed(post, c, root, from, base, order),
    ;
}

/// retype_reply's success block, from its ensures: the free page at `base` is a live reply and the
/// capability at `to` is its one holder. design/refused-claim-per-way/.
pub open spec fn reply_retyped(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize) -> bool {
    let parent = pre.tables.node_of(root, from);
    let child = pre.tables.node_of(root, to);
    let page = (base / PAGE_SZ) as int;
    &&& pre.view().holds_right(root, parent, Right::Retype)
    &&& post.blocks.pages@[page].kind is Base
    &&& post.blocks.pages@[page].object is Reply
    &&& post.blocks.pages@[page].order == 0
    &&& post.blocks.pages@[page].refs == 1
    &&& !post.blocks.pages@[page].dead
    &&& forall|i: int| pre.blocks.tracks(i) && i != page
        ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i]
    &&& post.replies.records@.contains_key(base)
    &&& post.replies.records@[base].value() == fresh_reply()
    &&& post.view().holds(root, child)
    &&& post.payload_of(child) == reply_of(base)
    &&& post.list.is_child(parent, child)
    &&& post.list.parent@ == pre.list.parent@.insert(child, parent)
    &&& post.list.nodes@[child as int].depth == pre.list.nodes@[parent as int].depth + 1
    &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != child
        ==> post.list.nodes@[i].live == pre.list.nodes@[i].live
    &&& CapKernel::retype_keeps(pre, post, child, page, 0, None)
    &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, pages: pow2(0), into: None })
}

/// retype_space's success block, from its ensures: the free block at `base` is a space of `kind` and
/// the capability at `to` is its one holder. design/refused-claim-per-way/.
pub open spec fn space_retyped(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, kind: SpaceKind) -> bool {
    let parent = pre.tables.node_of(root, from);
    let child = pre.tables.node_of(root, to);
    &&& CapKernel::retype_keeps(pre, post, child, (base / PAGE_SZ) as int, 3, None)
    &&& post.list.nodes@[child as int].depth == pre.list.nodes@[parent as int].depth + 1
    &&& pre.view().holds_right(root, parent, Right::Retype)
    &&& pre.blocks.pages@[(base / PAGE_SZ) as int].kind is Free
    &&& post.view().holds(root, child)
    &&& post.payload_of(child) == space_of(base)
    &&& post.list.is_child(parent, child)
    &&& post.list.parent@ == pre.list.parent@.insert(child, parent)
    &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != child
        ==> post.list.nodes@[i].live == pre.list.nodes@[i].live
    &&& post.spaces.roots@.contains_key(base)
    &&& post.spaces.records@[base].value().kind == kind
    &&& post.spaces.records@[base].value().table == fresh_root(base)
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] post.loaded(c, base)
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] holds_id(post.cores@, post.spaces.loaded@, c, base)
    &&& space_mapping(tree_of(&post.table_pages, &post.spaces), base) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty()
    &&& forall|r: usize| #[trigger] pre.spaces.roots@.contains_key(r) ==>
        space_mapping(tree_of(&post.table_pages, &post.spaces), r)
            == space_mapping(tree_of(&pre.table_pages, &pre.spaces), r)
    &&& forall|i: usize| i < ENTRIES ==> #[trigger] post.spaces.roots@[base].value()[i].is_empty()
    &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
    &&& post.spaces.registers == pre.spaces.registers
    &&& post.spaces.kernel_root == pre.spaces.kernel_root
    &&& post.spaces.bound@ == pre.spaces.bound@.insert(base, Set::<usize>::empty())
    &&& forall|s: usize| #[trigger] pre.spaces.roots@.contains_key(s) ==> post.spaces.roots@[s] == pre.spaces.roots@[s]
    &&& post.blocks.pages@[(base / PAGE_SZ) as int].refs == 1
    &&& !post.blocks.pages@[(base / PAGE_SZ) as int].dead
    &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, pages: pow2(3), into: None })
}

/// retype_endpoint's success meets no unchanged kernel: the free page is still free, so it is not a live endpoint.
/// design/refused-claim-per-way/.
pub trait RetypeEndpointOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_retype_block(root, from, to, base, 0),
            post == pre,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            CapKernel::queue_retype_keeps(pre, post),
            ret == pre.can_retype_block(root, from, to, base, 0),
            !ret ==> post == pre,
            ret ==> CapKernel::queue_retyped(pre, post, root, from, to, base, CapKind::Endpoint),
    ;
}

/// retype_notification's success meets no unchanged kernel: the free page is still free, so it is not a live notification.
/// design/refused-claim-per-way/.
pub trait RetypeNotificationOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_retype_block(root, from, to, base, 0),
            post == pre,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            CapKernel::queue_retype_keeps(pre, post),
            ret == pre.can_retype_block(root, from, to, base, 0),
            !ret ==> post == pre,
            ret ==> CapKernel::queue_retyped(pre, post, root, from, to, base, CapKind::Notification),
    ;
}

/// retype_reply's success meets no unchanged kernel: the free page is still free, so it is not a live reply.
/// design/refused-claim-per-way/.
pub trait RetypeReplyOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, ret: bool)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_retype_block(root, from, to, base, 0),
            post == pre,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
            CapKernel::same_tree(pre, post),
            post.stale_epoch == pre.stale_epoch,
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.mappings == pre.mappings,
            ret == pre.can_retype_block(root, from, to, base, 0),
            !ret ==> post == pre,
            ret ==> reply_retyped(pre, post, root, from, to, base),
    ;
}

/// retype_space's success meets no unchanged kernel: the free block is still free, so it is not a space.
/// design/refused-claim-per-way/.
pub trait RetypeSpaceOk {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, from: usize, to: usize, base: usize, kind: SpaceKind, ret: bool)
        requires
            !(kind is Process),
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.can_retype_block(root, from, to, base, 3),
            post == pre,
            ret,
        ensures
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            post.wf(),
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
            ret == pre.can_retype_block(root, from, to, base, 3),
            !ret ==> post == pre,
            post.devices == pre.devices,
            post.iommus == pre.iommus,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints,
            post.replies == pre.replies,
            post.tables.roots == pre.tables.roots,
            post.table_pages == pre.table_pages,
            post.stale_epoch == pre.stale_epoch,
            post.flush_epoch == pre.flush_epoch,
            post.targeted == pre.targeted,
            post.cores == pre.cores,
            ret ==> space_retyped(pre, post, root, from, to, base, kind),
    ;
}

/// revoke's Exhausted meets no unchanged kernel: the flush epoch is not at its limit, and the run was not taken.
/// design/refused-claim-per-way/.
pub trait RevokeExhausted {
    proof fn unchanged(pre: CapKernel, post: CapKernel, root: usize, at: Position, ret: RevokeStep)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            post == pre,
            ret is Exhausted,
        ensures
            CapKernel::page_count_kept(pre, post),
            post.wf(),
            CapKernel::mappings_shrunk(pre, post),
            CapKernel::records_shrunk(pre, post),
            CapKernel::blocks_revoked(pre, post),
            CapKernel::revoke_preserved(pre, post),
            CapKernel::revoke_answered(pre, post, root, at, ret),
            !(ret is Refused) ==> CapKernel::cap_revoking_at(pre, post, root, at),
            ret is Done ==> CapKernel::cap_revoked_at(pre, post, root, at),
    ;
}
} // verus!
