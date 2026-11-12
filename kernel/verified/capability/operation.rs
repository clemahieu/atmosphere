// SPDX-License-Identifier: MIT

//! The operations a process invokes through the one syscall entry, by the number in the operation
//! position, and what returns: the status in the status word's low 16 bits and the result words. The
//! frame's positions are the arch module's syscall register table. asys holds the same numbers for user
//! space, and the kernel crate checks at compile time that the two agree. See
//! design/syscall-abi-in-registers/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::tree_of;
#[cfg(verus_keep_ghost)]
use crate::capability::list::NODE_SPACE;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::space_mapping;
use crate::capability::position::*;
use crate::capability::probe::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::retype::RetypeStep;
use crate::capability::revoke::RevokeStep;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::bound_threads;
use crate::capability::steps::Steps;
use crate::capability::thread::*;
use crate::capability::unmap::Unmapped;
use crate::define::*;
use crate::pptr::*;
use crate::arch::Registers;

/// The operation was done.
pub const STATUS_OK: u64 = 0;

/// The capability, its rights or the arguments do not allow the operation.
pub const STATUS_REFUSED: u64 = 1;

/// No operation has the number in the operation position.
pub const STATUS_UNKNOWN: u64 = 2;

/// The operation took a bounded step and is not finished; the same invocation again goes on from where
/// it stopped. See design/one-lock-bounded-steps/.
pub const STATUS_AGAIN: u64 = 3;

/// invoke_retype's bound in the step counter: a table page's retype, the largest of the four kinds.
/// See design/one-lock-bounded-steps/.
pub const INVOKE_RETYPE_STEPS: usize = crate::capability::space::RETYPE_TABLE_PAGE_STEPS;

/// invoke_derive's bound in the step counter: none, since derive runs no loop and calls nothing
/// counted.
pub const INVOKE_DERIVE_STEPS: usize = 0;

/// invoke_move's bound in the step counter: none, since a move runs no loop and calls nothing counted.
pub const INVOKE_MOVE_STEPS: usize = 0;

/// invoke_delete's bound in the step counter: none, since delete runs no loop and calls nothing
/// counted.
pub const INVOKE_DELETE_STEPS: usize = 0;

/// invoke_revoke's bound in the step counter: one revoke's.
pub const INVOKE_REVOKE_STEPS: usize = crate::capability::revoke::REVOKE_STEPS;

/// invoke_link's bound in the step counter: none, since link_at walks a fixed number of levels and
/// calls nothing counted.
pub const INVOKE_LINK_STEPS: usize = 0;

/// invoke_map's bound in the step counter: none, since map_at walks a fixed number of levels and calls
/// nothing counted.
pub const INVOKE_MAP_STEPS: usize = 0;

/// invoke_unmap's bound in the step counter: one unmap_at's.
pub const INVOKE_UNMAP_STEPS: usize = crate::capability::unmap::UNMAP_AT_STEPS;

/// invoke_probe's bound in the step counter: one probe_at's, an entry each.
pub const INVOKE_PROBE_STEPS: usize = PROBE_MAX as usize;

pub const OPERATION_RETYPE: u64 = 1;
pub const OPERATION_DERIVE: u64 = 2;
pub const OPERATION_MOVE: u64 = 3;
pub const OPERATION_DELETE: u64 = 5;
pub const OPERATION_REVOKE: u64 = 6;
pub const OPERATION_MAP: u64 = 7;
pub const OPERATION_UNMAP: u64 = 8;
pub const OPERATION_DESTROY: u64 = 9;
pub const OPERATION_SEND: u64 = 10;
pub const OPERATION_RECEIVE: u64 = 11;
pub const OPERATION_CALL: u64 = 12;
pub const OPERATION_REPLY_RECV: u64 = 13;
pub const OPERATION_PRINT: u64 = 14;
pub const OPERATION_INSPECT: u64 = 15;
pub const OPERATION_LINK: u64 = 16;
pub const OPERATION_PROBE: u64 = 17;
pub const OPERATION_POWER_OFF: u64 = 18;

/// Retype's kind in argument 1 for a 4K frame.
pub const RETYPE_FRAME: u64 = 0;

/// Retype's kind in argument 1 for a 2M frame, a block of order 9.
pub const RETYPE_LARGE_FRAME: u64 = 1;

/// Retype's kind in argument 1 for a table page, of the level in argument 4.
pub const RETYPE_TABLE_PAGE: u64 = 2;

/// Retype's kind in argument 1 for a table leaf, at the base in argument 2, in the root entry the
/// position word in argument 3 names. Every other kind is refused until it is wired.
pub const RETYPE_LEAF: u64 = 3;

/// What an invocation returns to its thread: the status word and results 1 to 4, which
/// Registers::write_outcome puts at their positions in the frame.
#[derive(Clone, Copy)]
pub struct Outcome {
    pub status: u64,
    pub result_1: u64,
    pub result_2: u64,
    pub result_3: u64,
    pub result_4: u64,
}

/// The outcome of an operation that returns a status and no result words.
pub open spec fn status_only(status: u64) -> Outcome {
    Outcome { status, result_1: 0, result_2: 0, result_3: 0, result_4: 0 }
}

/// The outcome of an operation that returns a status and no result words.
pub fn status_only_outcome(status: u64) -> (ret: Outcome)
    ensures
        ret == status_only(status),
{
    Outcome { status, result_1: 0, result_2: 0, result_3: 0, result_4: 0 }
}

/// What a process asks of the capability named in the slot.
pub enum Operation {
    Retype,
    Derive,
    Move,
    Delete,
    Revoke,
    Map,
    Unmap,
    Destroy,
    Send,
    Receive,
    Call,
    ReplyRecv,
    Print,
    Inspect,
    Link,
    Probe,
    PowerOff,
}

impl Operation {
    /// The number a process puts in the operation position to invoke the operation.
    pub open spec fn number(self) -> u64 {
        match self {
            Operation::Retype => OPERATION_RETYPE,
            Operation::Derive => OPERATION_DERIVE,
            Operation::Move => OPERATION_MOVE,
            Operation::Delete => OPERATION_DELETE,
            Operation::Revoke => OPERATION_REVOKE,
            Operation::Map => OPERATION_MAP,
            Operation::Unmap => OPERATION_UNMAP,
            Operation::Destroy => OPERATION_DESTROY,
            Operation::Send => OPERATION_SEND,
            Operation::Receive => OPERATION_RECEIVE,
            Operation::Call => OPERATION_CALL,
            Operation::ReplyRecv => OPERATION_REPLY_RECV,
            Operation::Print => OPERATION_PRINT,
            Operation::Inspect => OPERATION_INSPECT,
            Operation::Link => OPERATION_LINK,
            Operation::Probe => OPERATION_PROBE,
            Operation::PowerOff => OPERATION_POWER_OFF,
        }
    }
}

/// The operation a number names, if any.
pub open spec fn spec_operation(number: u64) -> Option<Operation> {
    if exists|operation: Operation| operation.number() == number {
        Some(choose|operation: Operation| operation.number() == number)
    } else {
        None
    }
}

/// Each operation has its own number, so the number a process passes names one operation.
pub proof fn lemma_number_names_one_operation(operation: Operation)
    ensures
        spec_operation(operation.number()) == Some(operation),
{
}

/// The operation a number from user space names, or None when no operation has it.
pub fn operation(number: u64) -> (ret: Option<Operation>)
    ensures
        ret == spec_operation(number),
{
    let ret = match number {
        OPERATION_RETYPE => Some(Operation::Retype),
        OPERATION_DERIVE => Some(Operation::Derive),
        OPERATION_MOVE => Some(Operation::Move),
        OPERATION_DELETE => Some(Operation::Delete),
        OPERATION_REVOKE => Some(Operation::Revoke),
        OPERATION_MAP => Some(Operation::Map),
        OPERATION_UNMAP => Some(Operation::Unmap),
        OPERATION_DESTROY => Some(Operation::Destroy),
        OPERATION_SEND => Some(Operation::Send),
        OPERATION_RECEIVE => Some(Operation::Receive),
        OPERATION_CALL => Some(Operation::Call),
        OPERATION_REPLY_RECV => Some(Operation::ReplyRecv),
        OPERATION_PRINT => Some(Operation::Print),
        OPERATION_INSPECT => Some(Operation::Inspect),
        OPERATION_LINK => Some(Operation::Link),
        OPERATION_PROBE => Some(Operation::Probe),
        OPERATION_POWER_OFF => Some(Operation::PowerOff),
        _ => None,
    };
    proof {
        if ret is Some {
            lemma_number_names_one_operation(ret->0);
        }
    }
    ret
}

/// What a probe's outcome says, with the words it read: the masks in results 1 and 2, and each bit
/// maintained when result 3 or 4 is 1.
pub open spec fn probed_of(out: Outcome, read: Seq<usize>) -> Probed {
    Probed {
        accessed: out.result_1,
        dirty: out.result_2,
        accessed_maintained: out.result_3 == 1,
        dirty_maintained: out.result_4 == 1,
        read: Ghost(read),
    }
}

/// The outcome of a probe that returned r: ok, with the masks in results 1 and 2 and each fact in results
/// 3 and 4 as 1 or 0.
pub fn probe_outcome(r: Probed) -> (ret: Outcome)
    ensures
        ret.status == STATUS_OK,
        ret.result_3 <= 1,
        ret.result_4 <= 1,
        probed_of(ret, r.read@) == r,
{
    Outcome {
        status: STATUS_OK,
        result_1: r.accessed,
        result_2: r.dirty,
        result_3: if r.accessed_maintained { 1 } else { 0 },
        result_4: if r.dirty_maintained { 1 } else { 0 },
    }
}

/// What an unmap's outcome says, with the word it read: the accessed and dirty bits in results 1 and 2,
/// and each bit maintained, when result 3 or 4 is 1.
pub open spec fn unmapped_of(out: Outcome, read: usize) -> Unmapped {
    Unmapped {
        accessed: out.result_1 == 1,
        dirty: out.result_2 == 1,
        accessed_maintained: out.result_3 == 1,
        dirty_maintained: out.result_4 == 1,
        read: Ghost(read),
    }
}

/// The outcome of an unmap that returned r: ok, with each bit in results 1 and 2 and each fact in results
/// 3 and 4 as 1 or 0.
pub fn unmap_outcome(r: Unmapped) -> (ret: Outcome)
    ensures
        ret.status == STATUS_OK,
        ret.result_1 <= 1,
        ret.result_2 <= 1,
        ret.result_3 <= 1,
        ret.result_4 <= 1,
        unmapped_of(ret, r.read@) == r,
{
    Outcome {
        status: STATUS_OK,
        result_1: if r.accessed { 1 } else { 0 },
        result_2: if r.dirty { 1 } else { 0 },
        result_3: if r.accessed_maintained { 1 } else { 0 },
        result_4: if r.dirty_maintained { 1 } else { 0 },
    }
}

impl CapKernel {
    /// What the invocation in frame returns to a thread of the process whose table is at root, for an
    /// operation that leaves the kernel unchanged: for print, ok exactly when the slot holds a console
    /// capability and refused otherwise; for power-off, ok exactly when the slot holds a power capability
    /// and refused otherwise; for inspect, its outcome at the position the slot's word names, and
    /// refused for a word that names none; refused for every operation not wired yet;
    /// and unknown for a number no operation has. Print's words are arguments 1 to 5 and power-off's
    /// word is argument 1, as design/syscall-abi-in-registers/ places them; neither decides the status.
    pub open spec fn spec_outcome(&self, root: usize, frame: Registers) -> Outcome {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Print) => status_only(
                if self.holds_console(root, frame.slot() as usize) { STATUS_OK } else { STATUS_REFUSED },
            ),
            Some(Operation::PowerOff) => status_only(
                if self.holds_power(root, frame.slot() as usize) { STATUS_OK } else { STATUS_REFUSED },
            ),
            Some(Operation::Inspect) => match spec_position(frame.slot()) {
                Some(at) => self.spec_inspect_at(root, at),
                None => status_only(STATUS_REFUSED),
            },
            Some(_) => status_only(STATUS_REFUSED),
            None => status_only(STATUS_UNKNOWN),
        }
    }

    /// Whether the retype in frame by a thread of the process whose table is at root is allowed, by
    /// the kind in argument 1: a 4K frame by can_retype_frame, a 2M frame by can_retype_large, a table
    /// page by can_retype_table_page and a leaf by can_retype_leaf, over the untyped in the slot, the
    /// base in argument 2, the slot in argument 3, the level in argument 4 and the position word in
    /// argument 3 as each kind reads them. Every other kind is refused.
    pub open spec fn allows_retype(&self, root: usize, frame: Registers) -> bool {
        let from = frame.slot() as usize;
        let base = frame.argument(2) as usize;
        let at = spec_position(frame.argument(3));
        ||| frame.argument(1) == RETYPE_FRAME && self.can_retype_frame(root, from, frame.argument(3) as usize, base)
        ||| frame.argument(1) == RETYPE_LARGE_FRAME && self.can_retype_large(root, from, frame.argument(3) as usize, base, 9)
        ||| frame.argument(1) == RETYPE_TABLE_PAGE && self.can_retype_table_page(root, from, base, frame.argument(4) as usize)
        ||| frame.argument(1) == RETYPE_LEAF && at is Some && self.can_retype_leaf(root, from, at->0, base)
    }

    /// A retype in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_retype fails; for the 4K frame kind in argument 1, ok with the frame
    /// at the base in argument 2 retyped under the untyped in the slot into the slot in argument 3; for
    /// the 2M frame kind, again with the block at the base in argument 2 a step further zeroed and no
    /// slot changed, or ok with the 2M frame retyped into the slot in argument 3 once the block is all
    /// zero; for the table page kind, ok with an unlinked table page of the level in argument 4 at the
    /// base in argument 2 under the untyped in the slot; or, for the leaf kind, ok with a table leaf at
    /// the base in argument 2 under the untyped in the slot, in the root entry the position word in
    /// argument 3 names. Every arm but the table page's leaves every space's tables as they were.
    pub open spec fn spec_retyped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| !pre.allows_retype(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& frame.argument(1) == RETYPE_FRAME
            &&& out == status_only(STATUS_OK)
            &&& Self::frame_retyped(pre, post, root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LARGE_FRAME
            &&& out == status_only(STATUS_AGAIN)
            &&& Self::large_frame_zeroing(pre, post, root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, 9)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LARGE_FRAME
            &&& out == status_only(STATUS_OK)
            &&& Self::large_frame_retyped(pre, post, root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, 9)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_TABLE_PAGE
            &&& out == status_only(STATUS_OK)
            &&& Self::table_page_retyped(pre, post, root, frame.slot() as usize, frame.argument(2) as usize, frame.argument(4) as usize)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LEAF
            &&& out == status_only(STATUS_OK)
            &&& spec_position(frame.argument(3)) is Some
            &&& Self::leaf_retyped(pre, post, root, frame.slot() as usize, spec_position(frame.argument(3))->0, frame.argument(2) as usize)
            &&& Self::same_tree(pre, post)
        }
    }

    /// What a retype of the order-3 block at base as a table page of level did, under the untyped at
    /// index from of the table at root: the retype was allowed and the block free, the page is an empty
    /// table of that level that no space links and no capability names, the untyped's child, its node
    /// not live before and hidden after, the one entry the parent map gains and the only node whose
    /// liveness or kind changed, no thread bound but as it was, the block table changed in the block's
    /// pages alone, every space's mapping as it was, and the step discharges the retype's effect.
    pub open spec fn table_page_retyped(pre: Self, post: Self, root: usize, from: usize, base: usize, level: usize) -> bool {
        let parent = pre.tables.node_of(root, from);
        &&& pre.can_retype_table_page(root, from, base, level)
        &&& pre.view().holds_right(root, parent, Right::Retype)
        &&& pre.blocks.pages@[(base / PAGE_SZ) as int].kind is Free
        &&& post.table_pages.maps@.contains_key(base)
        &&& post.table_pages.records@[base].value() == fresh_table(level)
        &&& forall|i: usize| i < ENTRIES ==> #[trigger] post.table_pages.maps@[base].value()[i].is_empty()
        &&& post.list.is_child(parent, base)
        &&& !pre.list.nodes@[base as int].live
        &&& post.list.parent@ == pre.list.parent@.insert(base, parent)
        &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base
            ==> post.list.nodes@[i].live == pre.list.nodes@[i].live
        &&& post.list.nodes@[base as int].kind is Hidden
        &&& forall|x: usize| #![trigger post.list.nodes@[x as int]] pre.list.valid(x) && x != base
            ==> post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
        &&& forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x)
        &&& post.tables == pre.tables
        &&& post.spaces == pre.spaces
        &&& forall|r: usize| #[trigger] pre.spaces.roots@.contains_key(r) ==>
            space_mapping(tree_of(&post.table_pages, &post.spaces), r) == space_mapping(tree_of(&pre.table_pages, &pre.spaces), r)
        &&& pre.blocks.kept_but_run(post.blocks, (base / PAGE_SZ) as int, 3)
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, into: None })
    }

    /// A link in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_link_at fails over the arguments, or ok
    /// with the table page at the base in argument 4,
    /// under the untyped in argument 3, linked into the entry the address in argument 1 and the level in
    /// argument 2 name in the space of the capability in the slot.
    pub open spec fn spec_linked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| !pre.allows_link(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::table_linked(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize)
        }
    }

    /// A map in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_map_at fails over the arguments, or ok with the page at the offset in argument 4 of the
    /// frame in argument 3 mapped into the entry the address in argument 1 and the level in argument 2
    /// name in the space of the capability in the slot.
    pub open spec fn spec_mapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| !pre.allows_map(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::page_mapped(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize)
        }
    }

    /// An unmap in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_unmap_at fails over the arguments, or ok with the entry the address in argument 1 and the
    /// level in argument 2 name in the space of the capability in the slot cleared, its accessed and dirty
    /// bits as read before it was cleared in results 1 and 2, and whether the target maintains each bit in
    /// results 3 and 4, each result 1 when it holds and 0 when it does not.
    pub open spec fn spec_unmapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| !pre.allows_unmap(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out.status == STATUS_OK
            &&& out.result_1 <= 1
            &&& out.result_2 <= 1
            &&& out.result_3 <= 1
            &&& out.result_4 <= 1
            &&& exists|read: usize| Self::page_unmapped(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), #[trigger] unmapped_of(out, read))
        }
    }

    /// A probe in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_probe fails over the arguments, or ok with the accessed and dirty bits of the count in
    /// argument 2 of level 1 entries, from the one the address in argument 1 names in the space of the
    /// capability in the slot, read and cleared, the accessed mask in result 1, the dirty mask in result 2,
    /// and whether the target maintains each bit in results 3 and 4, 1 when it does and 0 when it does not.
    pub open spec fn spec_probed(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| !pre.allows_probe(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out.status == STATUS_OK
            &&& pre.allows_probe(root, frame)
            &&& out.result_3 <= 1
            &&& out.result_4 <= 1
            &&& exists|read: Seq<usize>| Self::probe_done(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), #[trigger] probed_of(out, read))
        }
    }

    /// A derive in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_derive fails, or ok with a child of the capability at the position the
    /// slot's word names, in the caller's own table, put at the position the word in argument 1 names,
    /// with the rights in argument 2 and the block of the order in argument 4 at the base in argument 3,
    /// the one entry the parent map gains and the only node whose kind, liveness or capability changed,
    /// no root entry changed, and every thread bound as it was. Rights wider than 32 bits and an order
    /// wider than 8 are refused, since no capability holds them, and so is a source word naming another
    /// process's table: derive takes its parent from the caller's own.
    pub open spec fn spec_derived(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        let child = pre.tables.node_of(pre.table_at(root, to->0.through)->0, to->0.index);
        ||| !pre.allows_derive(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& frame.argument(2) <= u32::MAX as u64
            &&& frame.argument(4) <= u8::MAX as u64
            &&& from is Some
            &&& from->0.through is None
            &&& to is Some
            &&& Self::cap_derived_at(pre, post, root, from->0.index, to->0, frame.argument(2) as u32, frame.argument(3) as usize, frame.argument(4) as u8)
            &&& post.list.parent@ == pre.list.parent@.insert(child, pre.tables.node_of(root, from->0.index))
            &&& post.tables.roots == pre.tables.roots
            &&& Self::caps_frame(pre, post, child, child)
            &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
        }
    }

    /// A move in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_move fails, or ok with the capability at the position the slot's
    /// word names moved to the position the word in argument 1 names, every thread bound as it was.
    pub open spec fn spec_moved(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        ||| !pre.allows_move(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& from is Some
            &&& to is Some
            &&& Self::cap_moved_at(pre, post, root, from->0, to->0)
            &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
        }
    }

    /// A delete in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_delete fails, or ok with the childless capability at the position the
    /// slot's word names gone, every thread bound as it was.
    pub open spec fn spec_deleted(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let at = spec_position(frame.slot());
        ||| !pre.allows_delete(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& at is Some
            &&& Self::cap_deleted_at(pre, post, root, at->0)
            &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
        }
    }

    /// A revoke in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, when allows_revoke fails; refused with the flush epoch at
    /// its limit, after the steps
    /// it took on the run of the capability at the position the slot's word names; again with a step of
    /// that run taken and some of it left; or ok with the run empty. See
    /// design/revoke-by-depth-first-list/.
    pub open spec fn spec_revoked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let at = spec_position(frame.slot());
        ||| !pre.allows_revoke(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_REFUSED)
            &&& at is Some
            &&& post.flush_epoch == usize::MAX
            &&& Self::cap_revoking_at(pre, post, root, at->0)
        }
        ||| {
            &&& out == status_only(STATUS_AGAIN)
            &&& at is Some
            &&& !post.list.childless(pre.cap_at(root, at->0)->0)
            &&& Self::cap_revoking_at(pre, post, root, at->0)
        }
        ||| out == status_only(STATUS_OK) && at is Some && Self::cap_revoked_at(pre, post, root, at->0)
    }

    /// Whether the link in frame is allowed: can_link_at over the address in argument 1, the level in
    /// argument 2, the untyped in argument 3 and the table page in argument 4, in the space of the
    /// capability in the slot.
    pub open spec fn allows_link(&self, root: usize, frame: Registers) -> bool {
        self.can_link_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize)
    }

    /// Whether the map in frame is allowed: can_map_at over the address in argument 1, the level in
    /// argument 2, the frame in argument 3 and the offset in argument 4, in the space of the capability
    /// in the slot.
    pub open spec fn allows_map(&self, root: usize, frame: Registers) -> bool {
        self.can_map_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize)
    }

    /// Whether the unmap in frame is allowed: can_unmap_at over the address in argument 1 and the level
    /// in argument 2, in the space of the capability in the slot.
    pub open spec fn allows_unmap(&self, root: usize, frame: Registers) -> bool {
        self.can_unmap_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2))
    }

    /// Whether the probe in frame is allowed: can_probe over the address in argument 1 and the count in
    /// argument 2, in the space of the capability in the slot.
    pub open spec fn allows_probe(&self, root: usize, frame: Registers) -> bool {
        self.can_probe(root, frame.slot() as usize, frame.argument(1), frame.argument(2))
    }

    /// Whether the derive in frame is allowed: rights that fit 32 bits in argument 2, an order that fits
    /// 8 in argument 4, a slot word naming a position of the caller's own table and argument 1 a
    /// position, and can_derive_at over them and the base in argument 3.
    pub open spec fn allows_derive(&self, root: usize, frame: Registers) -> bool {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        &&& frame.argument(2) <= u32::MAX as u64
        &&& frame.argument(4) <= u8::MAX as u64
        &&& from is Some
        &&& from->0.through is None
        &&& to is Some
        &&& self.can_derive_at(root, from->0.index, to->0, frame.argument(2) as u32, frame.argument(3) as usize, frame.argument(4) as u8)
    }

    /// Whether the move in frame is allowed: the slot word and argument 1 each a position, and
    /// can_move_at between them.
    pub open spec fn allows_move(&self, root: usize, frame: Registers) -> bool {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        &&& from is Some
        &&& to is Some
        &&& self.can_move_at(root, from->0, to->0)
    }

    /// Whether the delete in frame is allowed: the slot word a position, and can_delete_at there.
    pub open spec fn allows_delete(&self, root: usize, frame: Registers) -> bool {
        let at = spec_position(frame.slot());
        at is Some && self.can_delete_at(root, at->0)
    }

    /// Whether the revoke in frame takes a step: the slot word a position that holds a capability.
    pub open spec fn allows_revoke(&self, root: usize, frame: Registers) -> bool {
        let at = spec_position(frame.slot());
        at is Some && self.cap_at(root, at->0) is Some
    }

    /// Whether the invocation in frame by a thread of the process whose table is at root is allowed: for
    /// an operation that can change the kernel, its allows_ predicate over the frame's decoded
    /// arguments; for every other operation, which leaves the kernel unchanged, that spec_outcome is not
    /// a refusal.
    pub open spec fn allows(&self, root: usize, frame: Registers) -> bool {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Retype) => self.allows_retype(root, frame),
            Some(Operation::Derive) => self.allows_derive(root, frame),
            Some(Operation::Move) => self.allows_move(root, frame),
            Some(Operation::Delete) => self.allows_delete(root, frame),
            Some(Operation::Revoke) => self.allows_revoke(root, frame),
            Some(Operation::Link) => self.allows_link(root, frame),
            Some(Operation::Map) => self.allows_map(root, frame),
            Some(Operation::Unmap) => self.allows_unmap(root, frame),
            Some(Operation::Probe) => self.allows_probe(root, frame),
            _ => self.spec_outcome(root, frame) != status_only(STATUS_REFUSED),
        }
    }

    /// What the invocation in frame by a thread of the process whose table is at root did, from pre to
    /// post with out returned, with each table position decoded from its word: a retype's effect for retype, a derive's for derive, a move's for move, a
    /// delete's for delete, a revoke's for revoke, a link's for link, a map's for map, an unmap's for
    /// unmap, a probe's for probe, and for every other operation the kernel unchanged with spec_outcome
    /// returned. Each is refused with nothing changed exactly when allows fails, as
    /// lemma_refused_exactly says.
    pub open spec fn invoked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Retype) => Self::spec_retyped(pre, post, root, frame, out),
            Some(Operation::Derive) => Self::spec_derived(pre, post, root, frame, out),
            Some(Operation::Move) => Self::spec_moved(pre, post, root, frame, out),
            Some(Operation::Delete) => Self::spec_deleted(pre, post, root, frame, out),
            Some(Operation::Revoke) => Self::spec_revoked(pre, post, root, frame, out),
            Some(Operation::Link) => Self::spec_linked(pre, post, root, frame, out),
            Some(Operation::Map) => Self::spec_mapped(pre, post, root, frame, out),
            Some(Operation::Unmap) => Self::spec_unmapped(pre, post, root, frame, out),
            Some(Operation::Probe) => Self::spec_probed(pre, post, root, frame, out),
            _ => post == pre && out == pre.spec_outcome(root, frame),
        }
    }

    /// Every invocation is refused with nothing changed exactly when allows fails, but a revoke, which
    /// is also refused with the flush epoch at its limit after the steps it took on a capability it
    /// was allowed to revoke.
    pub proof fn lemma_refused_exactly(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
        ensures
            !pre.allows(root, frame) ==> out == status_only(STATUS_REFUSED) && post == pre,
            spec_operation(frame.operation_number()) != Some(Operation::Revoke) && out == status_only(STATUS_REFUSED)
                ==> !pre.allows(root, frame) && post == pre,
            spec_operation(frame.operation_number()) == Some(Operation::Revoke) && out == status_only(STATUS_REFUSED)
                && pre.allows(root, frame) ==> post.flush_epoch == usize::MAX,
    {
    }

    /// A word with a bit above bit 31 set, where derive, move, delete, revoke or inspect reads a position,
    /// or where retype's leaf kind reads its root entry, is refused with the kernel unchanged.
    pub proof fn lemma_wide_position_refused(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            ({
                let op = spec_operation(frame.operation_number());
                ||| (op == Some(Operation::Derive) || op == Some(Operation::Move) || op == Some(Operation::Delete)
                    || op == Some(Operation::Revoke) || op == Some(Operation::Inspect)) && frame.slot() >> POSITION_WIDTH != 0
                ||| (op == Some(Operation::Derive) || op == Some(Operation::Move)) && frame.argument(1) >> POSITION_WIDTH != 0
                ||| op == Some(Operation::Retype) && frame.argument(1) == RETYPE_LEAF && frame.argument(3) >> POSITION_WIDTH != 0
            }),
        ensures
            out == status_only(STATUS_REFUSED),
            post == pre,
    {
    }

    /// An unmap, allowed or refused, leaves the tables, the list's parents and the bound threads as they
    /// were, and changes the kind or the liveness of no node but a mapping node, so no capability.
    pub proof fn lemma_unmapped_frame(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::spec_unmapped(pre, post, root, frame, out),
        ensures
            post.tables == pre.tables,
            post.list.parent == pre.list.parent,
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
            forall|x: int| 0 <= x < NODE_SPACE && (#[trigger] post.list.nodes@[x].kind != pre.list.nodes@[x].kind
                || post.list.nodes@[x].live != pre.list.nodes@[x].live) ==> pre.list.nodes@[x].kind is Mapping
                && !post.list.nodes@[x].live,
    {
        if post != pre {
            let read = choose|read: usize| Self::page_unmapped(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), #[trigger] unmapped_of(out, read));
            Self::lemma_page_unmapped_frame(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), unmapped_of(out, read));
        }
    }

    /// Core c's step for the invocation its current thread entered the kernel with, in frame. The
    /// caller is core c's current thread and the table is its process's, never a name from user
    /// space, and check_current runs first: design/one-lock-bounded-steps/. Returns None when core c
    /// runs no thread after the check, so nothing returns to user mode, and then the step is the
    /// check's alone: the thread moved off, or nothing when core c ran none. Otherwise what returns to
    /// the thread, with the operation's effect on the kernel.
    pub fn dispatch(&mut self, c: usize, frame: Registers) -> (ret: Option<Outcome>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            ret is None <==> old(self).must_leave(c as int) || old(self).cores@[c as int].current_thread is None,
            // A caller that must leave, among them one acting within a dead process, reaches no
            // operation and gets nothing back: it is moved off its core and nothing else changes.
            ({
                let t = old(self).cores@[c as int].current_thread->Some_0;
                old(self).cores@[c as int].current_thread is Some
                    && old(self).processes.records@[old(self).threads.records@[t].value().process->Some_0].value().dead
                    ==> ret is None
            }),
            old(self).must_leave(c as int) ==> Self::moved_off(*old(self), *final(self), c as int, frame),
            old(self).cores@[c as int].current_thread is None ==> *final(self) == *old(self),
            ret is Some ==> {
                let t = old(self).cores@[c as int].current_thread->Some_0;
                let root = old(self).threads.records@[t].value().process->Some_0;
                &&& old(self).root_live(root)
                &&& old(self).cores@[c as int].space == Some(root)
                &&& final(self).cores@[c as int].space == Some(root)
                &&& Self::invoked(*old(self), *final(self), root, frame, ret->0)
            },
    {
        // The one counter of this entry, on a path that holds the kernel's lock: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        if self.check_current(c, frame, Tracked(&mut steps)) {
            return None;
        }
        let t = match self.cores.get(c).current_thread {
            Some(t) => t,
            None => { return None; },
        };
        proof {
            self.lemma_current_root_live(c as int);
            assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
        }
        let record = *PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ).borrow(
            Tracked(self.threads.records.borrow().tracked_borrow(t)),
        );
        let root = match record.process {
            Some(root) => root,
            None => { proof { assert(false); } return None; },
        };
        proof {
            // The caller has no stop pending, so its core has its process's space loaded.
            reveal(current_wf);
            assert(runs(self.cores@, c as int, t));
            assert(!self.threads.records@[t].value().pending_stop);
            assert(self.cores@[c as int].space == Some(root));
        }
        match operation(frame.operation_number()) {
            Some(Operation::Retype) => Some(self.invoke_retype(root, frame, Tracked(&mut steps))),
            Some(Operation::Derive) => Some(self.invoke_derive(root, frame, Tracked(&mut steps))),
            Some(Operation::Move) => Some(self.invoke_move(root, frame, Tracked(&mut steps))),
            Some(Operation::Delete) => Some(self.invoke_delete(root, frame, Tracked(&mut steps))),
            Some(Operation::Revoke) => Some(self.invoke_revoke(root, frame, Tracked(&mut steps))),
            Some(Operation::Link) => Some(self.invoke_link(root, frame, Tracked(&mut steps))),
            Some(Operation::Map) => Some(self.invoke_map(root, frame, Tracked(&mut steps))),
            Some(Operation::Unmap) => Some(self.invoke_unmap(root, frame, Tracked(&mut steps))),
            Some(Operation::Probe) => Some(self.invoke_probe(root, frame, Tracked(&mut steps))),
            Some(Operation::Print) => Some(status_only_outcome(
                self.print(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3), frame.argument(4), frame.argument(5), Tracked(&mut steps)),
            )),
            Some(Operation::PowerOff) => Some(status_only_outcome(self.power_off(root, frame.slot() as usize, Tracked(&mut steps)))),
            Some(Operation::Inspect) => match position(frame.slot()) {
                Some(at) => Some(self.inspect(root, at, Tracked(&mut steps))),
                None => Some(status_only_outcome(STATUS_REFUSED)),
            },
            Some(_) => Some(status_only_outcome(STATUS_REFUSED)),
            None => Some(status_only_outcome(STATUS_UNKNOWN)),
        }
    }

    /// The retype in frame, by a thread of the process whose table is at root.
    fn invoke_retype(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_RETYPE_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_retyped(*old(self), *final(self), root, frame, ret),
    {
        let status = if frame.argument(1) == RETYPE_FRAME {
            if self.retype_frame(root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, Tracked(steps)) {
                STATUS_OK
            } else {
                STATUS_REFUSED
            }
        } else if frame.argument(1) == RETYPE_LARGE_FRAME {
            match self.retype_large_frame(root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, 9, Tracked(steps)) {
                RetypeStep::Refused => STATUS_REFUSED,
                RetypeStep::Again => STATUS_AGAIN,
                RetypeStep::Done => STATUS_OK,
            }
        } else if frame.argument(1) == RETYPE_TABLE_PAGE {
            if self.retype_table_page(root, frame.slot() as usize, frame.argument(2) as usize, frame.argument(4) as usize, Tracked(steps)) {
                STATUS_OK
            } else {
                STATUS_REFUSED
            }
        } else if frame.argument(1) == RETYPE_LEAF {
            match position(frame.argument(3)) {
                Some(at) => {
                    if self.retype_leaf(root, frame.slot() as usize, at, frame.argument(2) as usize, Tracked(steps)) {
                        STATUS_OK
                    } else {
                        STATUS_REFUSED
                    }
                },
                None => STATUS_REFUSED,
            }
        } else {
            STATUS_REFUSED
        };
        status_only_outcome(status)
    }

    /// The derive in frame, by a thread of the process whose table is at root.
    fn invoke_derive(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_DERIVE_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_derived(*old(self), *final(self), root, frame, ret),
    {
        let from = match position(frame.slot()) {
            Some(Position { through: None, index }) => Some(index),
            _ => None,
        };
        let done = match (from, position(frame.argument(1))) {
            (Some(from), Some(to)) => frame.argument(2) <= u32::MAX as u64 && frame.argument(4) <= u8::MAX as u64
                && self.derive(root, from, to, frame.argument(2) as u32, frame.argument(3) as usize, frame.argument(4) as u8),
            _ => false,
        };
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The move in frame, by a thread of the process whose table is at root.
    fn invoke_move(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_MOVE_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_moved(*old(self), *final(self), root, frame, ret),
    {
        let done = match (position(frame.slot()), position(frame.argument(1))) {
            (Some(from), Some(to)) => self.move_cap(root, from, to),
            _ => false,
        };
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The delete in frame, by a thread of the process whose table is at root.
    fn invoke_delete(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_DELETE_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_deleted(*old(self), *final(self), root, frame, ret),
    {
        let done = match position(frame.slot()) {
            Some(at) => self.delete(root, at).is_some(),
            None => false,
        };
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The revoke in frame, by a thread of the process whose table is at root.
    fn invoke_revoke(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_REVOKE_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_revoked(*old(self), *final(self), root, frame, ret),
    {
        let status = match position(frame.slot()) {
            Some(at) => match self.revoke(root, at, Tracked(steps)) {
                RevokeStep::Done => STATUS_OK,
                RevokeStep::Again => STATUS_AGAIN,
                RevokeStep::Refused | RevokeStep::Exhausted => STATUS_REFUSED,
            },
            None => STATUS_REFUSED,
        };
        status_only_outcome(status)
    }

    /// The link in frame, by a thread of the process whose table is at root.
    fn invoke_link(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_LINK_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_linked(*old(self), *final(self), root, frame, ret),
    {
        let done = self.link_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize);
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The map in frame, by a thread of the process whose table is at root.
    fn invoke_map(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_MAP_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_mapped(*old(self), *final(self), root, frame, ret),
    {
        let done = self.map_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize);
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The unmap in frame, by a thread of the process whose table is at root.
    fn invoke_unmap(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_UNMAP_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_unmapped(*old(self), *final(self), root, frame, ret),
    {
        let ghost pre = *self;
        match self.unmap_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), Tracked(steps)) {
            Some(r) => {
                let out = unmap_outcome(r);
                proof {
                    assert(Self::page_unmapped(pre, *self, root, frame.slot() as usize, frame.argument(1), frame.argument(2), unmapped_of(out, r.read@)));
                }
                out
            },
            None => status_only_outcome(STATUS_REFUSED),
        }
    }

    /// The probe in frame, by a thread of the process whose table is at root.
    fn invoke_probe(&mut self, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_PROBE_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_probed(*old(self), *final(self), root, frame, ret),
    {
        let ghost pre = *self;
        match self.probe_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), Tracked(steps)) {
            Some(r) => {
                let out = probe_outcome(r);
                proof {
                    assert(Self::probe_done(pre, *self, root, frame.slot() as usize, frame.argument(1), frame.argument(2), probed_of(out, r.read@)));
                }
                out
            },
            None => status_only_outcome(STATUS_REFUSED),
        }
    }
}

} // verus!
