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
//! is MovedOff.
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

use vstd::prelude::*;

verus! {

use crate::arch::{user_rip, FrameKind, Registers, saved_frame, tag_written};
use crate::capability::thread::{CurrentStep, SuspendStep, ThreadState, entry_frame_save, runs_in_space, same_record_perm_but_links};
use crate::capability::unmap::Unmapped;
use crate::define::{NUM_CPUS, PAGE_SZ, PCID_MAX};
use crate::util::page_ptr_util_u::mem_valid;
use crate::capability::boot_image::{image_blocks, ImageRun, ROOT_FRAME_SLOTS};
use crate::capability::boot_memory::{runs_blocks, ROOT_UNTYPED_SLOTS};
use crate::capability::boot_table::{image_tables_bound, image_virt_wf, untyped_tables};
use crate::capability::decompose::page_block_payload;
use crate::capability::kernel::{CapKernel, holds_id, id_pcid, ID_GENERATION_MAX, KERNEL_TAG};
use crate::capability::reach::{discharges, Effect, saves_own_frame};
use crate::capability::schedule::{at_back_of_priority, queued_at_back, thread_priority};
use crate::capability::space::SPACE_ROOT_PAGE;
use crate::capability::switch::TickStep;
use crate::capability::view::bound_threads;
use crate::capability::table::{Payload, MAX_ORDER};
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

} // verus!
