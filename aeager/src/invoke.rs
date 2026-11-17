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
#[cfg(verus_keep_ghost)]
use acall::memory::derive_from_frame;
#[cfg(verus_keep_ghost)]
use acall::step::{tokens_kept, slot_names_own_space};
use aheap::allocator::Allocator;
#[cfg(verus_keep_ghost)]
use aheap::source::SpanSource;
#[cfg(verus_keep_ghost)]
use verified::capability::caller::view_frame;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::position::spec_position;
#[cfg(verus_keep_ghost)]
use verified::capability::refs::{block_ref, block_refs};
#[cfg(verus_keep_ghost)]
use verified::capability::rely::reaches_through;
#[cfg(verus_keep_ghost)]
use verified::capability::table::block_bytes;
use verified::capability::operation::{
    status_only_outcome, Outcome, RETYPE_FRAME, RETYPE_LARGE_FRAME, RETYPE_PROCESS, RETYPE_THREAD,
    STATUS_REFUSED,
};
#[cfg(verus_keep_ghost)]
use verified::capability::operation::{status_only, STATUS_OK};
#[cfg(verus_keep_ghost)]
use verified::define::PAGE_SZ;

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

/// The `acall` caller's-view contract for `call`, from `entry` to `post` in the caller's process
/// at `root`, returning `out`.
pub open spec fn call_contract(
    entry: CapKernel,
    post: CapKernel,
    root: usize,
    call: GuardedCall,
    out: Outcome,
) -> bool {
    match call {
        GuardedCall::Retype { untyped, kind, base, word, level } =>
            CapKernel::retype_contract(entry, post, root, kind, untyped as usize, base as usize, word, level as usize, out),
        GuardedCall::Derive { from, to, rights, base, order } =>
            CapKernel::derive_contract(entry, post, root, spec_position(from), spec_position(to), rights, base as usize, order, 0, out),
        GuardedCall::MoveCap { from, to } =>
            CapKernel::move_contract(entry, post, root, spec_position(from), spec_position(to), out),
        GuardedCall::Delete { at } =>
            CapKernel::delete_contract(entry, post, root, spec_position(at), out),
        GuardedCall::Revoke { at } =>
            CapKernel::revoke_contract(entry, post, root, spec_position(at), out),
        GuardedCall::Destroy { slot } =>
            CapKernel::destroy_contract(entry, post, root, slot as usize, out),
        GuardedCall::Place { slot, core, priority } =>
            CapKernel::place_contract(entry, post, root, slot as usize, core as usize, priority as usize, out),
        GuardedCall::Start { slot } =>
            CapKernel::start_contract(entry, post, root, slot as usize, out),
        GuardedCall::Suspend { slot } =>
            CapKernel::suspend_contract(entry, post, root, slot as usize, out),
        GuardedCall::ReadRegisters { slot, index } =>
            CapKernel::read_registers_contract(entry, post, root, slot as usize, index, out),
        GuardedCall::WriteRegisters { slot, index, words: _ } =>
            CapKernel::write_registers_contract(entry, post, root, slot as usize, index, out),
        GuardedCall::Inspect { at } =>
            CapKernel::inspect_contract(entry, post, root, spec_position(at), out),
        GuardedCall::Link { slot, va, level, from, child } =>
            CapKernel::link_contract(entry, post, root, slot as usize, va, level, from as usize, child as usize, out),
    }
}

/// Whether `call` keeps block reference counts and sole ownership for frames in `root`'s table:
/// every call other than an accepted `Derive` from a frame capability keeps `CapKernel::count_kept`
/// for all of `root`'s frames; an accepted `Derive` from a frame capability keeps the block, count
/// and `held_by` of every frame in `root`'s table whose page lies in another block.
pub open spec fn call_keeps_count(
    entry: CapKernel,
    post: CapKernel,
    root: usize,
    call: GuardedCall,
    out: Outcome,
) -> bool {
    match call {
        GuardedCall::Derive { from, to: _, rights: _, base: _, order: _ } => {
            &&& (out.status != STATUS_OK || !derive_from_frame(entry, root, from))
                ==> CapKernel::count_kept(entry, post, root)
            &&& (out.status == STATUS_OK && derive_from_frame(entry, root, from))
                ==> forall|j: usize, page: usize|
                    entry.table_view(root).contains_key(j)
                        && entry.table_view(root)[j].kind is Frame
                        && (page as int) * PAGE_SZ < block_bytes(entry.table_view(root)[j].order)
                        && block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page))
                            != block_ref(&entry.blocks, view_frame(entry.table_view(root)[spec_position(from)->0.index], 0))
                        ==> {
                        let br = block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page));
                        &&& #[trigger] block_ref(&post.blocks, view_frame(entry.table_view(root)[j], page)) == br
                        &&& block_refs(&post.blocks, br) == block_refs(&entry.blocks, br)
                        &&& entry.held_by(br, root) ==> post.held_by(br, root)
                    }
        },
        _ => CapKernel::count_kept(entry, post, root),
    }
}

/// Whether a `Derive` or `MoveCap` from `from` to `to` cannot overwrite `s` with a foreign
/// space-writing capability.
pub open spec fn slot_target_keeps_space(
    pre: CapKernel,
    entry: CapKernel,
    root: usize,
    from: u64,
    to: u64,
    s: usize,
) -> bool {
    (!reaches_through(to) && (spec_position(to) is None || spec_position(to)->0.index != s))
        || (!reaches_through(from) && spec_position(from) is Some
            && slot_names_own_space(pre, root, spec_position(from)->0.index))
        || entry.table_view(root).contains_key(s)
}

/// Whether `call` cannot overwrite slot `s` with a foreign space-writing capability: true when
/// `call` populates no slot, targets another slot, copies or derives from a slot naming `root`'s
/// own space, or finds `s` already occupied at `entry`.
pub open spec fn call_keeps_slot_space(
    pre: CapKernel,
    entry: CapKernel,
    root: usize,
    call: GuardedCall,
    s: usize,
) -> bool {
    match call {
        GuardedCall::Retype { untyped: _, kind, base: _, word, level: _ } =>
            kind != RETYPE_PROCESS || word as usize != s || entry.table_view(root).contains_key(s),
        GuardedCall::Derive { from, to, rights: _, base: _, order: _ } =>
            slot_target_keeps_space(pre, entry, root, from, to, s),
        GuardedCall::MoveCap { from, to } =>
            slot_target_keeps_space(pre, entry, root, from, to, s),
        _ => true,
    }
}

/// Invokes `call` using the caller token held inside `alloc`, rejecting any call that would
/// overwrite or duplicate `Eager`'s source capabilities or weaken `pages_wf` / `sealed` with
/// `STATUS_REFUSED`. When the token is held and the call is allowed, executes the `acall` wrapper
/// and ties the returned outcome and updated token state to `call_contract`.
pub fn invoke(alloc: &mut Allocator<Eager>, call: GuardedCall) -> (out: Outcome)
    ensures
        final(alloc).heap() == old(alloc).heap(),
        final(alloc).src() == old(alloc).src(),
        final(alloc).src_view() == old(alloc).src_view(),
        final(alloc).spares() == old(alloc).spares(),
        final(alloc).live() == old(alloc).live(),
        final(alloc).held() == old(alloc).held(),
        !old(alloc).held() || !call_keeps_source(&old(alloc).src(), call) ==> {
            &&& out == status_only(STATUS_REFUSED)
            &&& final(alloc).token() == old(alloc).token()
        },
        old(alloc).held() && call_keeps_source(&old(alloc).src(), call) ==> {
            let pre = old(alloc).token()->0;
            let post = final(alloc).token()->0;
            &&& final(alloc).token() is Some
            &&& final(alloc).src().serves(post)
            &&& post.wf()
            &&& post.root() == pre.root()
            &&& post.entry().wf()
            &&& CapKernel::rely(pre.kernel(), post.entry(), post.root())
            &&& post.history() == pre.history().push((post.entry(), post.kernel()))
            &&& tokens_kept(pre, post)
            &&& post.pages_wf()
            &&& call_contract(post.entry(), post.kernel(), post.root(), call, out)
            &&& CapKernel::space_kept(post.entry(), post.kernel(), post.root())
            &&& call_keeps_count(post.entry(), post.kernel(), post.root(), call, out)
            &&& forall|s: usize|
                #[trigger] slot_names_own_space(pre.kernel(), pre.root(), s)
                    && call_keeps_slot_space(pre.kernel(), post.entry(), post.root(), call, s)
                    ==> slot_names_own_space(post.kernel(), post.root(), s)
        },
{
    proof {
        alloc.lemma_wf();
    }
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
