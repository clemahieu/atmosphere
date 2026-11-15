// SPDX-License-Identifier: MIT

//! False claims for the caller's-view contracts. An unchanged kernel meets no ok or again arm whose
//! specification does not admit it, and no contract lets a slot it does not name change.
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
pub mod unnamed_move;

use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::kernel::CapKernel;
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

} // verus!
