// SPDX-License-Identifier: MIT

//! Guarded kernel invocations over an `Allocator<Eager>`.
//!
//! An unverified caller cannot safely hold `&mut Tracked<Caller>` once the heap allocator owns
//! the token, because kernel operations that overwrite or duplicate `Eager`'s own `space` slot,
//! held `frame` slots, or `untyped` capability — or that break `pages_wf` / `sealed` via a
//! `reaches_through` destination — would violate `Eager::serves` before `Allocator::give_back`.
//! Instead, `invoke` borrows the token inside verified code, rejects calls that target the
//! source's slots or use a `reaches_through` destination, executes the `acall` wrapper, proves
//! `Eager::serves` still holds, and returns the token to the allocator.

use vstd::prelude::*;
use aheap::allocator::Allocator;
#[cfg(verus_keep_ghost)]
use verified::capability::position::spec_position;
#[cfg(verus_keep_ghost)]
use verified::capability::rely::reaches_through;
use verified::capability::operation::{
    status_only_outcome, Outcome, RETYPE_FRAME, RETYPE_LARGE_FRAME, RETYPE_PROCESS, RETYPE_THREAD,
    STATUS_REFUSED,
};
#[cfg(verus_keep_ghost)]
use verified::capability::operation::status_only;

#[cfg(verus_keep_ghost)]
use crate::eager::frame_slot;
use crate::eager::{Eager, WINDOW_BYTES};

verus! {

/// The kernel operations a process may invoke through the heap allocator's caller token.
///
/// Operations that require per-page or foreign-space authority (`map`, `unmap`, `map_own`,
/// `unmap_own`) are excluded: own-space mapping moves through `PageToken`s held by `Eager` or the
/// caller directly.
#[derive(Clone, Copy)]
pub enum GuardedCall {
    Retype { untyped: u64, kind: u64, base: u64, word: u64, level: u64 },
    Derive { from: u64, to: u64, rights: u64, base: u64, order: u64 },
    MoveCap { from: u64, to: u64 },
    Delete { at: u64 },
    Revoke { at: u64 },
    Destroy { slot: u64 },
    Place { slot: u64, core: u64, priority: u64 },
    Start { slot: u64 },
    Suspend { slot: u64 },
    ReadRegisters { slot: u64, index: u64 },
    WriteRegisters { slot: u64, index: u64, words: [u64; 4] },
    Inspect { at: u64 },
    Link { slot: u64, va: u64, level: u64, from: u64, child: u64 },
}

/// Whether `slot` is one of `eager`'s own source slots in the caller's table: its root space
/// capability, its untyped capability, or any of the frame slots it allocates from.
pub open spec fn is_source_slot(eager: &Eager, slot: usize) -> bool {
    ||| slot as u64 == eager.space()
    ||| slot as u64 == eager.untyped()
    ||| exists|i: int| 0 <= i < eager.pages() && frame_slot(eager.slots() as int, i) == slot as int
}

/// Whether `word` is a local position (does not reach through another process capability) whose
/// slot index is one of `eager`'s source slots.
pub open spec fn local_targets_source(eager: &Eager, word: u64) -> bool {
    !reaches_through(word) && spec_position(word) is Some && is_source_slot(eager, spec_position(word)->0.index)
}

/// Whether `call` avoids every slot and position that could break `eager.serves(caller)` or
/// mutate `eager`'s own backing untyped / frame capabilities.
pub open spec fn call_keeps_source(eager: &Eager, call: GuardedCall) -> bool {
    match call {
        GuardedCall::Retype { untyped, kind, base: _, word, level: _ } => {
            &&& untyped != eager.untyped()
            &&& ((kind == RETYPE_FRAME || kind == RETYPE_LARGE_FRAME
                    || kind == RETYPE_PROCESS || kind == RETYPE_THREAD)
                ==> !is_source_slot(eager, word as usize))
        },
        GuardedCall::Derive { from, to, rights: _, base: _, order: _ } => {
            &&& !reaches_through(from)
            &&& !reaches_through(to)
            &&& !local_targets_source(eager, from)
            &&& !local_targets_source(eager, to)
        },
        GuardedCall::MoveCap { from, to } => {
            &&& !reaches_through(to)
            &&& !local_targets_source(eager, from)
            &&& !local_targets_source(eager, to)
        },
        GuardedCall::Delete { at } => {
            !local_targets_source(eager, at)
        },
        GuardedCall::Revoke { at } => {
            !local_targets_source(eager, at)
        },
        GuardedCall::Destroy { slot: _ }
        | GuardedCall::Place { slot: _, core: _, priority: _ }
        | GuardedCall::Start { slot: _ }
        | GuardedCall::Suspend { slot: _ }
        | GuardedCall::ReadRegisters { slot: _, index: _ }
        | GuardedCall::WriteRegisters { slot: _, index: _, words: _ }
        | GuardedCall::Inspect { at: _ } => true,
        GuardedCall::Link { slot, va, level: _, from, child: _ } => {
            &&& from != eager.untyped()
            &&& !(slot == eager.space()
                && (eager.window() as u64) <= va
                && va < (eager.window() + WINDOW_BYTES) as u64)
        },
    }
}

/// Invokes `call` using the caller token held inside `alloc`, rejecting any call that would
/// overwrite or duplicate `Eager`'s source capabilities or weaken `pages_wf` / `sealed` with
/// `STATUS_REFUSED`.
pub(crate) fn invoke(alloc: &mut Allocator<Eager>, call: GuardedCall) -> (out: Outcome)
    ensures
        final(alloc).heap() == old(alloc).heap(),
        final(alloc).src() == old(alloc).src(),
        final(alloc).src_view() == old(alloc).src_view(),
        final(alloc).spares() == old(alloc).spares(),
        final(alloc).live() == old(alloc).live(),
        final(alloc).held() == old(alloc).held(),
        !old(alloc).held() || !call_keeps_source(&old(alloc).src(), call)
            ==> out == status_only(STATUS_REFUSED),
{
    let allowed = check_call(alloc.source(), call);
    if !allowed {
        return status_only_outcome(STATUS_REFUSED);
    }
    let Some(mut caller) = alloc.lend() else {
        return status_only_outcome(STATUS_REFUSED);
    };
    let out = alloc.source().invoke_guarded(&mut caller, call);
    alloc.give_back(caller);
    out
}

fn check_call(eager: &Eager, call: GuardedCall) -> (r: bool)
    ensures
        r == call_keeps_source(eager, call),
{
    match call {
        GuardedCall::Retype { untyped, kind, base: _, word, level: _ } => {
            if untyped == eager.exec_untyped() {
                return false;
            }
            if kind == RETYPE_FRAME || kind == RETYPE_LARGE_FRAME
                || kind == RETYPE_PROCESS || kind == RETYPE_THREAD
            {
                !eager.exec_is_source_slot(word as usize)
            } else {
                true
            }
        },
        GuardedCall::Derive { from, to, rights: _, base: _, order: _ } => {
            !is_through(from) && !is_through(to)
                && !check_local_targets_source(eager, from)
                && !check_local_targets_source(eager, to)
        },
        GuardedCall::MoveCap { from, to } => {
            !is_through(to)
                && !check_local_targets_source(eager, from)
                && !check_local_targets_source(eager, to)
        },
        GuardedCall::Delete { at } => !check_local_targets_source(eager, at),
        GuardedCall::Revoke { at } => !check_local_targets_source(eager, at),
        GuardedCall::Destroy { slot: _ }
        | GuardedCall::Place { slot: _, core: _, priority: _ }
        | GuardedCall::Start { slot: _ }
        | GuardedCall::Suspend { slot: _ }
        | GuardedCall::ReadRegisters { slot: _, index: _ }
        | GuardedCall::WriteRegisters { slot: _, index: _, words: _ }
        | GuardedCall::Inspect { at: _ } => true,
        GuardedCall::Link { slot, va, level: _, from, child: _ } => {
            from != eager.exec_untyped()
                && !(slot == eager.exec_space()
                    && (eager.exec_window() as u64) <= va
                    && va < (eager.exec_window() + WINDOW_BYTES) as u64)
        },
    }
}

fn is_through(word: u64) -> (r: bool)
    ensures
        r == reaches_through(word),
{
    let pos = verified::capability::position::position(word);
    match pos {
        Some(p) => p.through.is_some(),
        None => false,
    }
}

fn check_local_targets_source(eager: &Eager, word: u64) -> (r: bool)
    ensures
        r == local_targets_source(eager, word),
{
    let pos = verified::capability::position::position(word);
    match pos {
        Some(p) => p.through.is_none() && eager.exec_is_source_slot(p.index),
        None => false,
    }
}

} // verus!
