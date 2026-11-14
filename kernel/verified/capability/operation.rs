// SPDX-License-Identifier: MIT

//! The operations a process invokes through the one syscall entry, by the number in the operation
//! position, and what returns: the status in the status word's low 16 bits and the result words. The
//! frame's positions are the arch module's syscall register table. asys holds the same numbers for user
//! space, and the kernel crate checks at compile time that the two agree. See
//! design/syscall-abi-in-registers/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::inspect::inspected;
use crate::capability::inspect::inspect_outcome;
#[cfg(verus_keep_ghost)]
use crate::capability::cpu::core_of;
#[cfg(verus_keep_ghost)]
use crate::capability::endpoint::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reply::*;
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
use crate::capability::process::PROCESS_ORDER;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::reclaim::FrameReclaimStep;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::{block_refs, BlockRef};
use crate::capability::retype::RetypeStep;
use crate::capability::revoke::RevokeStep;
#[cfg(verus_keep_ghost)]
use crate::capability::revoke::REVOKE_BUDGET;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::schedule::{at_back_of_priority, queued_at_back};
#[cfg(verus_keep_ghost)]
use crate::capability::view::{bound_threads, right_bit};
use crate::capability::steps::Steps;
use crate::capability::thread::*;
use crate::capability::unmap::Unmapped;
use crate::define::*;
use crate::pptr::*;
use crate::arch::{FrameKind, Registers, FRAME_WORDS};
#[cfg(verus_keep_ghost)]
use crate::arch::{lemma_register_words, lemma_registers_of, register_words, registers_of, user_rip};

/// The operation was done.
pub const STATUS_OK: u64 = 0;

/// The capability, its rights or the arguments do not allow the operation.
pub const STATUS_REFUSED: u64 = 1;

/// No operation has the number in the operation position.
pub const STATUS_UNKNOWN: u64 = 2;

/// The operation took a bounded step and is not finished; the same invocation again goes on from where
/// it stopped. See design/one-lock-bounded-steps/.
pub const STATUS_AGAIN: u64 = 3;

/// invoke_retype's bound in the step counter: a table page's retype, the largest of the seven kinds.
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

/// invoke_destroy's bound in the step counter: one destroy's, an IPI's turn for each core.
pub const INVOKE_DESTROY_STEPS: usize = NUM_CPUS;

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

/// dispatch's bound in the step counter: the check of its current thread, then the largest of the
/// operations it runs, which is revoke's. See design/one-lock-bounded-steps/.
pub const DISPATCH_STEPS: usize = CHECK_CURRENT_STEPS + INVOKE_REVOKE_STEPS;

/// B, the bound of one entry that holds the kernel's lock: dispatch's, then the acknowledgement of a
/// flush. The flush IPI's entry, CapKernel::enter_flush, stays within it. Each such entry makes the
/// one counter it is held to. See design/one-lock-bounded-steps/.
pub const ENTRY_STEPS: usize = DISPATCH_STEPS + ACKNOWLEDGE_STEPS;

/// Every operation dispatch runs stays within revoke's bound, so dispatch stays within its own.
pub proof fn lemma_revoke_bounds_the_operations()
    ensures
        INVOKE_RETYPE_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_DERIVE_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_MOVE_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_DELETE_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_LINK_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_MAP_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_UNMAP_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_PROBE_STEPS <= INVOKE_REVOKE_STEPS,
        INVOKE_DESTROY_STEPS <= INVOKE_REVOKE_STEPS,
        crate::capability::console::PRINT_BYTES <= INVOKE_REVOKE_STEPS,
        crate::capability::power::POWER_OFF_STEPS <= INVOKE_REVOKE_STEPS,
        crate::capability::inspect::INSPECT_STEPS <= INVOKE_REVOKE_STEPS,
        ACKNOWLEDGE_STEPS <= ENTRY_STEPS,
{
}

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
pub const OPERATION_READ_REGISTERS: u64 = 19;
pub const OPERATION_WRITE_REGISTERS: u64 = 20;
pub const OPERATION_PLACE: u64 = 21;
pub const OPERATION_START: u64 = 22;
pub const OPERATION_SUSPEND: u64 = 23;

/// Retype's kind in argument 1 for a 4K frame.
pub const RETYPE_FRAME: u64 = 0;

/// Retype's kind in argument 1 for a 2M frame, a block of order 9.
pub const RETYPE_LARGE_FRAME: u64 = 1;

/// Retype's kind in argument 1 for a table page, of the level in argument 4.
pub const RETYPE_TABLE_PAGE: u64 = 2;

/// Retype's kind in argument 1 for a table leaf, at the base in argument 2, in the root entry the
/// position word in argument 3 names.
pub const RETYPE_LEAF: u64 = 3;

/// Retype's kind in argument 1 that frees the dead frame at the base in argument 2, of the order in
/// argument 4, 0, 9 or 18, under the untyped in the slot: the frame part of reclaim.
pub const RETYPE_FREE: u64 = 4;

/// Retype's kind in argument 1 for a process, of the order-3 block at the base in argument 2, with its
/// capability in the slot in argument 3.
pub const RETYPE_PROCESS: u64 = 5;

/// Retype's kind in argument 1 for a thread, of the order-1 block at the base in argument 2, with its
/// capability in the slot in argument 3, bound to the process whose capability is in the slot in
/// argument 4. Every other kind is refused until it is wired.
pub const RETYPE_THREAD: u64 = 6;

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
    ReadRegisters,
    WriteRegisters,
    Place,
    Start,
    Suspend,
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
            Operation::ReadRegisters => OPERATION_READ_REGISTERS,
            Operation::WriteRegisters => OPERATION_WRITE_REGISTERS,
            Operation::Place => OPERATION_PLACE,
            Operation::Start => OPERATION_START,
            Operation::Suspend => OPERATION_SUSPEND,
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
        OPERATION_READ_REGISTERS => Some(Operation::ReadRegisters),
        OPERATION_WRITE_REGISTERS => Some(Operation::WriteRegisters),
        OPERATION_PLACE => Some(Operation::Place),
        OPERATION_START => Some(Operation::Start),
        OPERATION_SUSPEND => Some(Operation::Suspend),
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

/// A word index read registers and write registers accept: a multiple of four within the frame.
/// design/syscall-abi-in-registers/, under Thread and process operations.
pub open spec fn window_index(index: u64) -> bool {
    index % 4 == 0 && index < FRAME_WORDS
}

/// The frame's words with the window of four from index written from arguments 2 to 5 of frame, an
/// argument past the frame's end ignored: what a write registers stores, before the user-return rule.
pub open spec fn window_written(words: Seq<u64>, index: int, frame: Registers) -> Seq<u64> {
    Seq::new(words.len(), |k: int| if index <= k < index + 4 { frame.spec_argument((k - index + 2) as usize) } else { words[k] })
}

/// Word index + k of the frame's words, or zero past the frame's end.
pub open spec fn window_word(words: Seq<u64>, index: int, k: int) -> u64 {
    if index + k < words.len() { words[index + k] } else { 0 }
}

/// What a read registers of the window of four from index returns: ok, with word index + k - 1 of the
/// frame in result k, zero past the frame's end.
pub open spec fn window_read(words: Seq<u64>, index: int) -> Outcome {
    Outcome {
        status: STATUS_OK,
        result_1: window_word(words, index, 0),
        result_2: window_word(words, index, 1),
        result_3: window_word(words, index, 2),
        result_4: window_word(words, index, 3),
    }
}

/// Word index + k of r, or zero past the frame's end.
fn window_word_of(r: &Registers, index: usize, k: usize) -> (ret: u64)
    requires
        index < FRAME_WORDS,
        k < 4,
    ensures
        ret == window_word(register_words(*r), index as int, k as int),
{
    proof {
        lemma_register_words(*r);
    }
    if index + k < FRAME_WORDS { r.word(index + k) } else { 0 }
}

/// The outcome of a read of the window of four from index of r.
fn read_window(r: &Registers, index: usize) -> (ret: Outcome)
    requires
        index < FRAME_WORDS,
    ensures
        ret == window_read(register_words(*r), index as int),
{
    Outcome {
        status: STATUS_OK,
        result_1: window_word_of(r, index, 0),
        result_2: window_word_of(r, index, 1),
        result_3: window_word_of(r, index, 2),
        result_4: window_word_of(r, index, 3),
    }
}

/// r with the window of four from index written from arguments 2 to 5 of frame.
fn write_window(r: Registers, index: usize, frame: &Registers) -> (ret: Registers)
    requires
        index < FRAME_WORDS,
    ensures
        register_words(ret) == window_written(register_words(r), index as int, *frame),
{
    proof {
        lemma_register_words(r);
    }
    let mut ret = r;
    ret.set_word(index, frame.argument(2));
    if index + 1 < FRAME_WORDS {
        ret.set_word(index + 1, frame.argument(3));
    }
    if index + 2 < FRAME_WORDS {
        ret.set_word(index + 2, frame.argument(4));
    }
    if index + 3 < FRAME_WORDS {
        ret.set_word(index + 3, frame.argument(5));
    }
    proof {
        assert(register_words(ret) =~= window_written(register_words(r), index as int, *frame));
    }
    ret
}

impl CapKernel {
    /// The thread the capability at index i of the table at root names.
    pub open spec fn thread_named(&self, root: usize, i: usize) -> usize {
        self.payload_of(self.tables.node_of(root, i)).base
    }

    /// The words of the saved frame of the thread the capability at index i of the table at root
    /// names, in register_words' order.
    pub open spec fn frame_words(&self, root: usize, i: usize) -> Seq<u64> {
        register_words(self.threads.records@[self.thread_named(root, i)].value().frame)
    }

    /// The frame the write registers in frame asks to store, before the user-return rule: the saved
    /// frame of the thread the slot names, with the window from argument 1 written from arguments 2 to 5.
    pub open spec fn written_input(&self, root: usize, frame: Registers) -> Registers {
        registers_of(window_written(self.frame_words(root, frame.slot() as usize), frame.argument(1) as int, frame))
    }

    /// Whether the write registers in frame is allowed: argument 1 a multiple of four within the frame,
    /// the slot, an index in the caller's own table, a control capability for an Inactive thread that is
    /// not dead, and the program counter the written frame would hold a user address.
    /// design/syscall-abi-in-registers/, under Thread and process operations.
    pub open spec fn allows_write_registers(&self, root: usize, frame: Registers) -> bool {
        &&& window_index(frame.argument(1))
        &&& self.can_set_registers(root, frame.slot() as usize)
        &&& user_rip(self.written_input(root, frame).spec_pc())
    }

    /// A write registers in frame by a thread of the process whose table is at root, from pre to post
    /// with out returned: refused with nothing changed, exactly when allows_write_registers fails, or ok
    /// with the saved frame of the thread the slot names written as frame_written says, from
    /// written_input: the window from argument 1 holds arguments 2 to 5, every other word what the frame
    /// held, and then the user-return rule applies to the whole frame.
    pub open spec fn spec_registers_written(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| !pre.allows_write_registers(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& pre.allows_write_registers(root, frame)
            &&& out == status_only(STATUS_OK)
            &&& Self::frame_written(pre, post, pre.thread_named(root, frame.slot() as usize), pre.written_input(root, frame))
        }
    }

    /// What the read registers in frame returns: refused unless argument 1 is a multiple of four
    /// within the frame and the slot, an index in the caller's own table, holds a control capability for
    /// an Inactive thread that is not dead; ok otherwise, with the words of that thread's saved frame
    /// from argument 1 in results 1 to 4, zero past the frame's end.
    pub open spec fn spec_read_registers(&self, root: usize, frame: Registers) -> Outcome {
        if window_index(frame.argument(1)) && self.can_set_registers(root, frame.slot() as usize) {
            window_read(self.frame_words(root, frame.slot() as usize), frame.argument(1) as int)
        } else {
            status_only(STATUS_REFUSED)
        }
    }

    /// What the invocation in frame returns to a thread of the process whose table is at root, for an
    /// operation that leaves the kernel unchanged: for print, ok exactly when the slot holds a console
    /// capability and refused otherwise; for power-off, ok exactly when the slot holds a power capability
    /// and refused otherwise; for inspect, its outcome at the position the slot's word names, and
    /// refused for a word that names none; for read registers, spec_read_registers; refused for every
    /// operation not wired yet;
    /// and unknown for a number no operation has. Print's words are arguments 1 to 5 and power-off's
    /// word is argument 1, as design/syscall-abi-in-registers/ places them; neither decides the status.
    /// Print, power-off and inspect call here the predicates their ensures call, as
    /// design/invoked-arm-is-the-operation-postcondition/ requires. The kernel is unchanged, so the
    /// discharge is this kernel with itself; inspect's payload is the one the position holds.
    pub open spec fn spec_outcome(&self, root: usize, frame: Registers) -> Outcome {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Print) => {
                let slot = frame.slot() as usize;
                let _discharged = discharges(self.view(), self.view(), root, Effect::Local);
                status_only(if self.holds_console(root, slot) { STATUS_OK } else { STATUS_REFUSED })
            },
            Some(Operation::PowerOff) => {
                let slot = frame.slot() as usize;
                let _discharged = discharges(self.view(), self.view(), root, Effect::Local);
                status_only(if self.holds_power(root, slot) { STATUS_OK } else { STATUS_REFUSED })
            },
            Some(Operation::Inspect) => match spec_position(frame.slot()) {
                Some(at) => {
                    let ret = match self.cap_at(root, at) {
                        Some(n) => Some(self.payload_of(n)),
                        None => None,
                    };
                    let _found = self.inspect_found(root, at, ret);
                    let _reads = self.inspect_reads(root, at, ret);
                    let _discharged = discharges(self.view(), self.view(), root, Effect::Local);
                    self.spec_inspect_at(root, at)
                },
                None => status_only(STATUS_REFUSED),
            },
            Some(Operation::ReadRegisters) => self.spec_read_registers(root, frame),
            Some(_) => status_only(STATUS_REFUSED),
            None => status_only(STATUS_UNKNOWN),
        }
    }

    /// Whether the retype in frame by a thread of the process whose table is at root is allowed, by
    /// the kind in argument 1: a 4K frame by can_retype_frame, a 2M frame by can_retype_large, a table
    /// page by can_retype_table_page and a leaf by can_retype_leaf, over the untyped in the slot, the
    /// base in argument 2, the slot in argument 3, the level in argument 4 and the position word in
    /// argument 3 as each kind reads them; the free kind by can_free_frame, over the untyped in the
    /// slot, the base in argument 2 and the order in argument 4; and a process by can_retype_block of
    /// its order-3 block, over the untyped in the slot, the slot in argument 3 and the base in argument
    /// 2; and a thread by can_retype_thread, over the untyped in the slot, the slot in argument 3, the
    /// base in argument 2 and the process capability in the slot in argument 4. Every other kind is
    /// refused.
    pub open spec fn allows_retype(&self, root: usize, frame: Registers) -> bool {
        let from = frame.slot() as usize;
        let base = frame.argument(2) as usize;
        let at = spec_position(frame.argument(3));
        ||| frame.argument(1) == RETYPE_FRAME && self.can_retype_frame(root, from, frame.argument(3) as usize, base)
        ||| frame.argument(1) == RETYPE_LARGE_FRAME && self.can_retype_large(root, from, frame.argument(3) as usize, base, 9)
        ||| frame.argument(1) == RETYPE_TABLE_PAGE && self.can_retype_table_page(root, from, base, frame.argument(4) as usize)
        ||| frame.argument(1) == RETYPE_LEAF && at is Some && self.can_retype_leaf(root, from, at->0, base)
        ||| frame.argument(1) == RETYPE_FREE && self.can_free_frame(root, from, base, frame.argument(4) as usize)
        ||| frame.argument(1) == RETYPE_PROCESS && self.can_retype_block(root, from, frame.argument(3) as usize, base, PROCESS_ORDER)
        ||| frame.argument(1) == RETYPE_THREAD && self.can_retype_thread(root, from, frame.argument(3) as usize, base, frame.argument(4) as usize)
    }

    /// The free kind may run on the frame of the order at base, under the untyped at index from of the
    /// table at root: a dead 4K frame the untyped covers at order 0, as reclaim_frame frees, and a dead
    /// 2M or 1G frame at order 9 or 18, as reclaim_large_frame frees.
    pub open spec fn can_free_frame(&self, root: usize, from: usize, base: usize, order: usize) -> bool {
        ||| order == 0 && self.can_retype_under(root, from, base, 0) && self.frame_is_dead(base / PAGE_SZ)
        ||| (order == 9 || order == 18) && self.can_reclaim_large(root, from, base, order as u8)
    }

    /// Every core has acknowledged the staleness of the frame of the order at base, so no core may
    /// hold a translation to it and the free can run: the page at order 0, the region otherwise.
    pub open spec fn frame_free_acknowledged(&self, base: usize, order: usize) -> bool {
        if order == 0 {
            self.acknowledged(base / PAGE_SZ)
        } else {
            let level = crate::capability::zero::large_level(order as u8);
            self.region_acknowledged(level, base / PAGE_SZ / crate::capability::zero::level_pages(level))
        }
    }

    /// A retype in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_retype fails; for the 4K frame kind in argument 1, ok with the frame
    /// at the base in argument 2 retyped under the untyped in the slot into the slot in argument 3; for
    /// the 2M frame kind, again with the block at the base in argument 2 a step further zeroed and no
    /// slot changed, or ok with the 2M frame retyped into the slot in argument 3 once the block is all
    /// zero; for the table page kind, ok with an unlinked table page of the level in argument 4 at the
    /// base in argument 2 under the untyped in the slot; or, for the leaf kind, ok with a table leaf at
    /// the base in argument 2 under the untyped in the slot, in the root entry the position word in
    /// argument 3 names, the block table changed in the leaf's two pages alone; or, for the free kind,
    /// again with nothing changed while a core has not acknowledged the frame's staleness, and ok with
    /// the frame of the order in argument 4 at the base in argument 2 freed by reclaim once every core
    /// has, as frame_freed says at order 0 and large_frame_freed at order 9 or 18; or, for the process kind, ok with a process at the base in argument 2 under the untyped in
    /// the slot, its capability in the slot in argument 3, as process_retyped says; or, for the thread
    /// kind, ok with a thread at the base in argument 2 under the untyped in the slot, its capability in
    /// the slot in argument 3, bound to the process whose capability is in the slot in argument 4, as
    /// thread_retyped says. Every arm but the table page's and the process's leaves every space's
    /// tables as they were. Each arm that answers calls the predicates the ensures of the operation
    /// invoke_retype calls for its kind call, so it carries that operation's postcondition:
    /// design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn spec_retyped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let from = frame.slot() as usize;
        let base = frame.argument(2) as usize;
        let to = frame.argument(3) as usize;
        let level = frame.argument(4) as usize;
        ||| !pre.allows_retype(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& frame.argument(1) == RETYPE_FRAME
            &&& out == status_only(STATUS_OK)
            &&& Self::frame_retype_answered(pre, post, root, from, to, base, true)
            &&& Self::frame_retype_kept(pre, post)
            &&& Self::frame_retyped(pre, post, root, from, to, base)
            &&& Self::retype_keeps(pre, post, pre.tables.node_of(root, to), (base / PAGE_SZ) as int, 0, None)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LARGE_FRAME
            &&& out == status_only(STATUS_AGAIN)
            &&& Self::large_retype_answered(pre, post, root, from, to, base, 9, false)
            &&& Self::large_retype_kept(pre, post)
            &&& Self::large_retype_cursor(pre, post, base, false)
            &&& Self::large_frame_zeroing(pre, post, root, from, to, base, 9)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LARGE_FRAME
            &&& out == status_only(STATUS_OK)
            &&& Self::large_retype_answered(pre, post, root, from, to, base, 9, false)
            &&& Self::large_retype_kept(pre, post)
            &&& Self::large_retype_cursor(pre, post, base, false)
            &&& Self::large_frame_retyped(pre, post, root, from, to, base, 9)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_TABLE_PAGE
            &&& out == status_only(STATUS_OK)
            &&& Self::table_page_retype_answered(pre, post, root, from, base, level, true)
            &&& Self::table_page_retype_kept(pre, post)
            &&& Self::table_page_retype_done(pre, post, root, from, base, level)
            &&& Self::table_page_retyped(pre, post, root, from, base, level)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LEAF
            &&& out == status_only(STATUS_OK)
            &&& spec_position(frame.argument(3)) is Some
            &&& Self::leaf_retype_answered(pre, post, root, from, spec_position(frame.argument(3))->0, base, true)
            &&& Self::leaf_retype_kept(pre, post)
            &&& Self::leaf_retyped(pre, post, root, from, spec_position(frame.argument(3))->0, base)
            &&& Self::leaf_retype_spared(pre, post, base)
            &&& pre.blocks.kept_but_run(post.blocks, (base / PAGE_SZ) as int, 1)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_FREE
            &&& pre.allows_retype(root, frame)
            &&& !pre.frame_free_acknowledged(base, level)
            &&& out == status_only(STATUS_AGAIN)
            &&& post == pre
        }
        ||| {
            &&& frame.argument(1) == RETYPE_FREE
            &&& level == 0
            &&& pre.allows_retype(root, frame)
            &&& pre.frame_free_acknowledged(base, level)
            &&& out == status_only(STATUS_OK)
            &&& Self::frame_reclaim_answered(pre, post, root, from, base, FrameReclaimStep::Freed)
            &&& exists|c: usize| c < NUM_CPUS && #[trigger] pre.frame_freed(post, c, root, from, base)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_FREE
            &&& (level == 9 || level == 18)
            &&& pre.allows_retype(root, frame)
            &&& pre.frame_free_acknowledged(base, level)
            &&& out == status_only(STATUS_OK)
            &&& Self::large_reclaim_answered(pre, post, root, from, base, level as u8, FrameReclaimStep::Freed)
            &&& exists|c: usize| c < NUM_CPUS && #[trigger] pre.large_frame_freed(post, c, root, from, base, level as u8)
            &&& Self::same_tree(pre, post)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_PROCESS
            &&& out == status_only(STATUS_OK)
            &&& Self::process_retype_answered(pre, post, root, from, to, base, true)
            &&& Self::process_retype_kept(pre, post)
            &&& Self::process_retype_done(pre, post, root, from, to, base)
            &&& Self::process_retyped(pre, post, root, from, to, base)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_THREAD
            &&& out == status_only(STATUS_OK)
            &&& Self::thread_retyped(pre, post, root, from, to, base, level)
        }
    }

    /// What a retype of the order-3 block at base as a table page of level did, under the untyped at
    /// index from of the table at root: the retype was allowed and the block free, the page is an empty
    /// table of that level that no space links and no capability names, the untyped's child, its node
    /// not live before and hidden after, the one entry the parent map gains and the only node whose
    /// liveness or kind changed, no thread bound but as it was, the block table changed in the block's
    /// pages alone, every space's mapping and the processes as they were, and the step discharges the
    /// retype's effect.
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
        &&& Self::table_page_retyped_fields(pre, post, base)
        &&& post.processes == pre.processes
        &&& post.endpoints == pre.endpoints
        &&& post.replies == pre.replies
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, pages: pow2(3), into: None })
    }

    /// Additional table-page retype preservation facts kept opaque outside `invoke_retype` and
    /// `lemma_retype_contract` so global quantifier context does not grow.
    #[verifier::opaque]
    pub open spec fn table_page_retyped_fields(pre: Self, post: Self, base: usize) -> bool {
        &&& !post.blocks.pages@[(base / PAGE_SZ) as int].dead
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base])
        &&& post.table_pages.records@ == pre.table_pages.records@.insert(base, post.table_pages.records@[base])
        &&& forall|x: usize| #![trigger post.list.nodes@[x as int]] pre.list.valid(x) && x != base
            ==> post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
    }

    /// A link in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_link_at fails over the arguments, or ok
    /// with the table page at the base in argument 4,
    /// under the untyped in argument 3, linked into the entry the address in argument 1 and the level in
    /// argument 2 name in the space of the capability in the slot; either way the cores, the flush epoch
    /// and every thread's binding are as link_kept says.
    pub open spec fn spec_linked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let slot = frame.slot() as usize;
        let va = frame.argument(1);
        let level = frame.argument(2);
        let from = frame.argument(3) as usize;
        let child = frame.argument(4) as usize;
        &&& Self::link_kept(pre, post)
        &&& {
            ||| out == status_only(STATUS_REFUSED) && Self::link_answered(pre, post, root, slot, va, level, from, child, false)
            ||| {
                &&& out == status_only(STATUS_OK)
                &&& Self::link_answered(pre, post, root, slot, va, level, from, child, true)
                &&& Self::table_linked(pre, post, root, slot, va, level, from, child)
            }
        }
    }

    /// A map in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_map_at fails over the arguments, or ok with the page at the offset in argument 4 of the
    /// frame in argument 3 mapped into the entry the address in argument 1 and the level in argument 2
    /// name in the space of the capability in the slot; either way the cores, the flush epoch and every
    /// thread's binding are as map_kept says.
    pub open spec fn spec_mapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let slot = frame.slot() as usize;
        let va = frame.argument(1);
        let level = frame.argument(2);
        let from = frame.argument(3) as usize;
        let page = frame.argument(4) as usize;
        &&& Self::map_kept(pre, post)
        &&& {
            ||| out == status_only(STATUS_REFUSED) && Self::map_answered(pre, post, root, slot, va, level, from, page, false)
            ||| {
                &&& out == status_only(STATUS_OK)
                &&& Self::map_answered(pre, post, root, slot, va, level, from, page, true)
                &&& Self::page_mapped(pre, post, root, slot, va, level, from, page)
            }
        }
    }

    /// An unmap in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_unmap_at fails over the arguments, or ok with the entry the address in argument 1 and the
    /// level in argument 2 name in the space of the capability in the slot cleared, its accessed and dirty
    /// bits as read before it was cleared in results 1 and 2, and whether the target maintains each bit in
    /// results 3 and 4, each result 1 when it holds and 0 when it does not; either way the cores, the
    /// spaces, the table pages' records and every thread's binding are as unmap_kept says.
    pub open spec fn spec_unmapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let slot = frame.slot() as usize;
        let va = frame.argument(1);
        let level = frame.argument(2);
        &&& Self::unmap_kept(pre, post)
        &&& {
            ||| out == status_only(STATUS_REFUSED) && Self::unmap_answered(pre, post, root, slot, va, level, false)
            ||| {
                &&& out.status == STATUS_OK
                &&& Self::unmap_answered(pre, post, root, slot, va, level, true)
                &&& out.result_1 <= 1
                &&& out.result_2 <= 1
                &&& out.result_3 <= 1
                &&& out.result_4 <= 1
                &&& exists|read: usize| Self::page_unmapped(pre, post, root, slot, va, level, #[trigger] unmapped_of(out, read))
            }
        }
    }

    /// Every thread is bound to the process it was bound to from pre to post. An operation's ensures and
    /// its arm of invoked both call it: design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn threads_bound_kept(pre: Self, post: Self) -> bool {
        bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
    }

    /// A probe in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when can_probe fails over the arguments, or ok with the accessed and dirty bits of the count in
    /// argument 2 of level 1 entries, from the one the address in argument 1 names in the space of the
    /// capability in the slot, read and cleared, the accessed mask in result 1, the dirty mask in result 2,
    /// and whether the target maintains each bit in results 3 and 4, 1 when it does and 0 when it does not;
    /// either way the step discharges as a local one and every thread stays bound as it was.
    pub open spec fn spec_probed(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let slot = frame.slot() as usize;
        let va = frame.argument(1);
        let count = frame.argument(2);
        &&& discharges(pre.view(), post.view(), root, Effect::Local)
        &&& Self::threads_bound_kept(pre, post)
        &&& {
            ||| out == status_only(STATUS_REFUSED) && Self::probe_answered(pre, post, root, slot, va, count, false)
            ||| {
                &&& out.status == STATUS_OK
                &&& Self::probe_answered(pre, post, root, slot, va, count, true)
                &&& out.result_3 <= 1
                &&& out.result_4 <= 1
                &&& exists|read: Seq<usize>| Self::probe_done(pre, post, root, slot, va, count, #[trigger] probed_of(out, read))
            }
        }
    }

    /// A derive in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_derive fails, or ok with a child of
    /// the capability at the position the slot's word names, in the caller's own table, put at the
    /// position the word in argument 1 names, with the rights in argument 2, the block of the order in
    /// argument 4 at the base in argument 3 and the badge in argument 5, or the parent's when it is 0,
    /// as derive_step, cap_derived_at, derive_counted, derive_linked and derive_untracked say; either
    /// way what derive_kept and same_tree say is as it was. Rights wider than 32 bits and an order wider
    /// than 8 are refused, since no capability holds them, and so is a source word naming another
    /// process's table: derive takes its parent from the caller's own.
    pub open spec fn spec_derived(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        let rights = frame.argument(2) as u32;
        let base = frame.argument(3) as usize;
        let order = frame.argument(4) as u8;
        let badge = frame.argument(5) as usize;
        let parent = pre.tables.node_of(root, from->0.index);
        let child = pre.tables.node_of(pre.table_at(root, to->0.through)->0, to->0.index);
        &&& Self::derive_kept(pre, post)
        &&& Self::same_tree(pre, post)
        &&& {
            ||| !pre.allows_derive(root, frame) && out == status_only(STATUS_REFUSED) && post == pre
            ||| {
                &&& out == status_only(STATUS_OK)
                &&& frame.argument(2) <= u32::MAX as u64
                &&& frame.argument(4) <= u8::MAX as u64
                &&& from is Some
                &&& from->0.through is None
                &&& to is Some
                &&& Self::derive_answered(pre, post, root, from->0.index, to->0, rights, base, order, badge, true)
                &&& Self::derive_step(pre, post, child)
                &&& Self::cap_derived_at(pre, post, root, from->0.index, to->0, rights, base, order, badge)
                &&& Self::derive_counted(pre, post, parent)
                &&& Self::derive_linked(pre, post, child, parent)
                &&& Self::derive_untracked(pre, post, parent)
            }
        }
    }

    /// A move in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_move fails, or ok with the capability
    /// at the position the slot's word names moved to the position the word in argument 1 names, as
    /// cap_moved_at says, and every space's tables as they were; either way the cores, the block table,
    /// the IOMMUs, the process, device and space records, the flush epoch and every thread's binding are
    /// as move_kept says.
    pub open spec fn spec_moved(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        &&& Self::move_kept(pre, post)
        &&& {
            ||| {
                &&& !pre.allows_move(root, frame)
                &&& out == status_only(STATUS_REFUSED)
                &&& post == pre
                &&& from is Some && to is Some ==> Self::move_answered(pre, post, root, from->0, to->0, false)
            }
            ||| {
                &&& out == status_only(STATUS_OK)
                &&& from is Some
                &&& to is Some
                &&& Self::move_answered(pre, post, root, from->0, to->0, true)
                &&& Self::cap_moved_at(pre, post, root, from->0, to->0)
                &&& Self::same_tree(pre, post)
            }
        }
    }

    /// A delete in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_delete fails, or ok with the childless capability at the position the
    /// slot's word names gone with the reference it held, as delete_answered says of the payload it took
    /// out; either way what delete_kept says is kept.
    pub open spec fn spec_deleted(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let at = spec_position(frame.slot());
        &&& Self::delete_kept(pre, post, root)
        &&& {
            ||| at is None && out == status_only(STATUS_REFUSED) && post == pre
            ||| at is Some && out == status_only(STATUS_REFUSED) && Self::delete_answered(pre, post, root, at->0, None)
            ||| {
                &&& at is Some
                &&& out == status_only(STATUS_OK)
                &&& Self::delete_answered(pre, post, root, at->0, Some(pre.payload_of(pre.cap_at(root, at->0)->0)))
                &&& Self::cap_deleted_at(pre, post, root, at->0)
                &&& Self::object_dropped(pre, post, pre.cap_at(root, at->0)->0)
            }
        }
    }

    /// A revoke in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, when allows_revoke fails; refused with the flush epoch at
    /// its limit, which a revoke reaches only from an epoch within REVOKE_BUDGET of it, raised by no more
    /// than the nodes it took of the run of the capability at the position the slot's word names; again
    /// with exactly REVOKE_BUDGET nodes of that run taken and some of it left; or ok with the run empty.
    /// Whatever steps it took raised no block's count. Every arm calls the predicates revoke's ensures
    /// calls: revoke_preserved, mappings_shrunk, records_shrunk and blocks_revoked, and revoke_answered
    /// with the step, Refused and Exhausted both where the status is refused. See
    /// design/revoke-by-depth-first-list/ and design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn spec_revoked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let at = spec_position(frame.slot());
        &&& Self::revoke_preserved(pre, post)
        &&& Self::mappings_shrunk(pre, post)
        &&& Self::records_shrunk(pre, post)
        &&& Self::blocks_revoked(pre, post)
        &&& {
            ||| {
                &&& !pre.allows_revoke(root, frame)
                &&& out == status_only(STATUS_REFUSED)
                &&& post == pre
                &&& at is Some ==> Self::revoke_answered(pre, post, root, at->0, RevokeStep::Refused)
            }
            ||| {
                &&& out == status_only(STATUS_REFUSED)
                &&& at is Some
                &&& Self::revoke_answered(pre, post, root, at->0, RevokeStep::Exhausted)
                &&& pre.flush_epoch + REVOKE_BUDGET >= usize::MAX
                &&& post.flush_epoch == usize::MAX
                &&& pre.flush_epoch + (pre.list.seq@.len() - post.list.seq@.len()) >= usize::MAX
                &&& Self::cap_revoking_at(pre, post, root, at->0)
                &&& Self::counts_lowered(pre, post)
            }
            ||| {
                &&& out == status_only(STATUS_AGAIN)
                &&& at is Some
                &&& Self::revoke_answered(pre, post, root, at->0, RevokeStep::Again)
                &&& !post.list.childless(pre.cap_at(root, at->0)->0)
                &&& pre.list.seq@.len() - post.list.seq@.len() == REVOKE_BUDGET
                &&& Self::cap_revoking_at(pre, post, root, at->0)
                &&& Self::counts_lowered(pre, post)
            }
            ||| {
                &&& out == status_only(STATUS_OK)
                &&& at is Some
                &&& Self::revoke_answered(pre, post, root, at->0, RevokeStep::Done)
                &&& Self::cap_revoked_at(pre, post, root, at->0)
                &&& Self::counts_lowered(pre, post)
            }
        }
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
    /// position, and can_derive_at over them, the base in argument 3 and the badge in argument 5.
    pub open spec fn allows_derive(&self, root: usize, frame: Registers) -> bool {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        &&& frame.argument(2) <= u32::MAX as u64
        &&& frame.argument(4) <= u8::MAX as u64
        &&& from is Some
        &&& from->0.through is None
        &&& to is Some
        &&& self.can_derive_at(root, from->0.index, to->0, frame.argument(2) as u32, frame.argument(3) as usize, frame.argument(4) as u8, frame.argument(5) as usize)
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

    /// Whether the destroy in frame is allowed: can_destroy at the index the slot names, in the caller's
    /// own table.
    pub open spec fn allows_destroy(&self, root: usize, frame: Registers) -> bool {
        self.can_destroy(root, frame.slot() as usize)
    }

    /// A destroy in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_destroy fails, or ok with the process
    /// or thread the slot's capability names destroyed from some core, as destroy_done says; either way
    /// what destroy_kept says is kept.
    pub open spec fn spec_destroyed(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let i = frame.slot() as usize;
        &&& Self::destroy_kept(pre, post)
        &&& {
            ||| {
                &&& !pre.allows_destroy(root, frame)
                &&& out == status_only(STATUS_REFUSED)
                &&& post == pre
                &&& Self::destroy_answered(pre, post, root, i, false)
            }
            ||| {
                &&& pre.allows_destroy(root, frame)
                &&& out == status_only(STATUS_OK)
                &&& Self::destroy_answered(pre, post, root, i, true)
                &&& exists|c: usize| c < NUM_CPUS && #[trigger] Self::destroy_done(pre, post, c, root, i)
            }
        }
    }

    /// Whether the place in frame is allowed: can_place of the thread at the index the slot names, through
    /// the core capability at the index argument 1 names, both in the caller's own table, at the priority
    /// in argument 2.
    pub open spec fn allows_place(&self, root: usize, frame: Registers) -> bool {
        self.can_place(root, frame.slot() as usize, frame.argument(1) as usize, frame.argument(2) as usize)
    }

    /// A place in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_place fails, or ok with the thread the
    /// slot's capability placed through the core capability at argument 1 at the priority in argument
    /// 2, as place_done says; either way what place_kept says is kept.
    pub open spec fn spec_placed(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let i = frame.slot() as usize;
        let j = frame.argument(1) as usize;
        let priority = frame.argument(2) as usize;
        &&& Self::place_kept(pre, post, root)
        &&& {
            ||| {
                &&& !pre.allows_place(root, frame)
                &&& out == status_only(STATUS_REFUSED)
                &&& post == pre
                &&& Self::place_answered(pre, post, root, i, j, priority, false)
            }
            ||| {
                &&& pre.allows_place(root, frame)
                &&& out == status_only(STATUS_OK)
                &&& Self::place_answered(pre, post, root, i, j, priority, true)
                &&& Self::place_done(pre, post, root, i, j, priority)
            }
        }
    }

    /// Whether the start in frame is allowed: can_start of the thread at the index the slot names in the
    /// caller's own table.
    pub open spec fn allows_start(&self, root: usize, frame: Registers) -> bool {
        self.can_start(root, frame.slot() as usize)
    }

    /// A start in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, exactly when allows_start fails, or ok with the thread
    /// the slot's capability names Runnable on the core it is placed on, as start_done says; either way
    /// what start_kept says is kept. design/cpu-time-as-capability/.
    pub open spec fn spec_started(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let i = frame.slot() as usize;
        &&& Self::start_kept(pre, post)
        &&& {
            ||| {
                &&& !pre.allows_start(root, frame)
                &&& out == status_only(STATUS_REFUSED)
                &&& post == pre
                &&& Self::start_answered(pre, post, root, i, false)
            }
            ||| {
                &&& pre.allows_start(root, frame)
                &&& out == status_only(STATUS_OK)
                &&& Self::start_answered(pre, post, root, i, true)
                &&& Self::start_done(pre, post, root, i)
            }
        }
    }

    /// Whether the suspend in frame is allowed: can_suspend of the thread at the index the slot names in
    /// the caller's own table.
    pub open spec fn allows_suspend(&self, root: usize, frame: Registers) -> bool {
        self.can_suspend(root, frame.slot() as usize)
    }

    /// A suspend in frame from core c by a thread of the process whose table is at root, from pre to
    /// post with out returned: the status of the suspend's answer, refused, ok for Suspended or again,
    /// with what suspend_answered says of that answer.
    pub open spec fn suspended_from(pre: Self, post: Self, c: usize, root: usize, frame: Registers, out: Outcome) -> bool {
        let i = frame.slot() as usize;
        ||| out == status_only(STATUS_REFUSED) && Self::suspend_answered(pre, post, c, root, i, SuspendStep::Refused)
        ||| out == status_only(STATUS_OK) && Self::suspend_answered(pre, post, c, root, i, SuspendStep::Suspended)
        ||| out == status_only(STATUS_AGAIN) && Self::suspend_answered(pre, post, c, root, i, SuspendStep::Again)
    }

    /// A suspend in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned, from the core the caller runs on: invoked does not name the core, and dispatched says
    /// which it is. Refused with nothing changed exactly when allows_suspend fails; again only for a
    /// thread Running on a core other than the caller's, whose stop is then pending; ok otherwise, with
    /// the thread Inactive and the caller's core running nothing when it was the thread it ran.
    pub open spec fn spec_suspended(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        exists|c: usize| c < NUM_CPUS && #[trigger] Self::suspended_from(pre, post, c, root, frame, out)
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
            Some(Operation::Destroy) => self.allows_destroy(root, frame),
            Some(Operation::WriteRegisters) => self.allows_write_registers(root, frame),
            Some(Operation::Place) => self.allows_place(root, frame),
            Some(Operation::Start) => self.allows_start(root, frame),
            Some(Operation::Suspend) => self.allows_suspend(root, frame),
            _ => self.spec_outcome(root, frame) != status_only(STATUS_REFUSED),
        }
    }

    /// What the invocation in frame by a thread of the process whose table is at root did, from pre to
    /// post with out returned, with each table position decoded from its word: a retype's effect for retype, a derive's for derive, a move's for move, a
    /// delete's for delete, a revoke's for revoke, a link's for link, a map's for map, an unmap's for
    /// unmap, a probe's for probe, a destroy's for destroy, a write registers' for write registers, a
    /// place's for place, a start's for start, a suspend's for suspend, and for every other operation the
    /// kernel unchanged with spec_outcome
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
            Some(Operation::Destroy) => Self::spec_destroyed(pre, post, root, frame, out),
            Some(Operation::WriteRegisters) => Self::spec_registers_written(pre, post, root, frame, out),
            Some(Operation::Place) => Self::spec_placed(pre, post, root, frame, out),
            Some(Operation::Start) => Self::spec_started(pre, post, root, frame, out),
            Some(Operation::Suspend) => Self::spec_suspended(pre, post, root, frame, out),
            _ => post == pre && out == pre.spec_outcome(root, frame),
        }
    }

    /// Every invocation is refused with nothing changed exactly when allows fails, but a revoke, which
    /// is also refused with the flush epoch at its limit after the steps it took on a capability it
    /// was allowed to revoke, and that only from an epoch within REVOKE_BUDGET of the limit.
    pub proof fn lemma_refused_exactly(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
        ensures
            !pre.allows(root, frame) ==> out == status_only(STATUS_REFUSED) && post == pre,
            spec_operation(frame.operation_number()) != Some(Operation::Revoke) && out == status_only(STATUS_REFUSED)
                ==> !pre.allows(root, frame) && post == pre,
            spec_operation(frame.operation_number()) == Some(Operation::Revoke) && out == status_only(STATUS_REFUSED)
                && pre.allows(root, frame) ==> pre.flush_epoch + REVOKE_BUDGET >= usize::MAX && post.flush_epoch == usize::MAX,
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

    /// A retype of the free kind naming a dead 4K frame reaches reclaim_frame: refused with nothing
    /// changed unless the caller may retype the page and its frame is dead; again with nothing changed
    /// while a core or IOMMU has not acknowledged the page's staleness; ok once every core and present
    /// IOMMU has, with the page freed by reclaim_frame, so the next 4K retype of it can succeed.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_reclaim_frame(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_FREE,
            frame.argument(4) == 0,
        ensures
            ({
                let from = frame.slot() as usize;
                let base = frame.argument(2) as usize;
                let page = base / PAGE_SZ;
                &&& !(pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(page))
                    ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(page) && !pre.acknowledged(page)
                    ==> out == status_only(STATUS_AGAIN) && post == pre
                &&& pre.can_retype_under(root, from, base, 0) && pre.frame_is_dead(page) && pre.acknowledged(page)
                    ==> out == status_only(STATUS_OK) && post.blocks.small_free(page as int, 0)
                        && exists|c: usize| c < NUM_CPUS && #[trigger] pre.frame_freed(post, c, root, from, base)
            }),
    {
    }

    /// A retype of the free kind naming a dead 2M or 1G frame reaches reclaim_large_frame: refused with
    /// nothing changed unless can_reclaim_large holds over the frame's arguments; again with nothing
    /// changed while a core or IOMMU has not acknowledged the region's staleness; ok once every core and
    /// present IOMMU has, with the region freed by reclaim_large_frame, free and not being zeroed, so the
    /// next large-frame retype of it can succeed. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_reclaim_large_frame(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_FREE,
            frame.argument(4) == 9 || frame.argument(4) == 18,
        ensures
            ({
                let from = frame.slot() as usize;
                let base = frame.argument(2) as usize;
                let order = frame.argument(4) as u8;
                let level = crate::capability::zero::large_level(order);
                let r = base / PAGE_SZ / crate::capability::zero::level_pages(level);
                &&& !pre.can_reclaim_large(root, from, base, order)
                    ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_reclaim_large(root, from, base, order) && !pre.region_acknowledged(level, r)
                    ==> out == status_only(STATUS_AGAIN) && post == pre
                &&& pre.can_reclaim_large(root, from, base, order) && pre.region_acknowledged(level, r)
                    ==> out == status_only(STATUS_OK) && post.blocks.large_free(level, r as int) && !post.zeroing.active(level, r)
                        && exists|c: usize| c < NUM_CPUS && #[trigger] pre.large_frame_freed(post, c, root, from, base, order)
            }),
    {
        if pre.can_reclaim_large(root, frame.slot() as usize, frame.argument(2) as usize, frame.argument(4) as u8)
            && pre.region_acknowledged(
                crate::capability::zero::large_level(frame.argument(4) as u8),
                frame.argument(2) as usize / PAGE_SZ / crate::capability::zero::level_pages(crate::capability::zero::large_level(frame.argument(4) as u8)),
            )
        {
            let c = choose|c: usize| c < NUM_CPUS
                && #[trigger] pre.large_frame_freed(post, c, root, frame.slot() as usize, frame.argument(2) as usize, frame.argument(4) as usize as u8);
            assert(pre.large_frame_freed(post, c, root, frame.slot() as usize, frame.argument(2) as usize, frame.argument(4) as u8));
        }
    }

    /// A retype of the 2M frame kind reaches retype_large_frame: refused with nothing changed unless
    /// can_retype_large holds over the frame's arguments; when it does, again with the block a step
    /// further zeroed, as large_frame_zeroing says, or ok with the 2M frame retyped into the slot in
    /// argument 3, as large_frame_retyped says; and again on the step that begins a block not being
    /// zeroed, since one step zeroes less than a region. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_retype_large_frame(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_LARGE_FRAME,
        ensures
            ({
                let from = frame.slot() as usize;
                let to = frame.argument(3) as usize;
                let base = frame.argument(2) as usize;
                &&& !pre.can_retype_large(root, from, to, base, 9) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_retype_large(root, from, to, base, 9) ==> {
                    ||| out == status_only(STATUS_AGAIN) && Self::large_frame_zeroing(pre, post, root, from, to, base, 9)
                    ||| out == status_only(STATUS_OK) && Self::large_frame_retyped(pre, post, root, from, to, base, 9)
                }
                &&& pre.can_retype_large(root, from, to, base, 9) && !pre.zeroing.active(
                        crate::capability::zero::large_level(9),
                        base / PAGE_SZ / crate::capability::zero::level_pages(crate::capability::zero::large_level(9)),
                    )
                    ==> out == status_only(STATUS_AGAIN) && Self::large_frame_zeroing(pre, post, root, from, to, base, 9)
            }),
    {
    }

    /// A retype of the 4K frame kind reaches retype_frame: refused with nothing changed unless
    /// can_retype_frame holds over the untyped in the slot, the slot in argument 3 and the base in
    /// argument 2, and ok with the frame retyped into that slot as frame_retyped says when it does.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_retype_frame(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_FRAME,
        ensures
            ({
                let from = frame.slot() as usize;
                let to = frame.argument(3) as usize;
                let base = frame.argument(2) as usize;
                &&& !pre.can_retype_frame(root, from, to, base) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_retype_frame(root, from, to, base)
                    ==> out == status_only(STATUS_OK) && Self::frame_retyped(pre, post, root, from, to, base)
            }),
    {
    }

    /// A retype of the leaf kind reaches retype_leaf: refused with nothing changed unless the word in
    /// argument 3 decodes to a position and can_retype_leaf holds over the untyped in the slot, that
    /// position and the base in argument 2; ok with the leaf in the root entry the position names, as
    /// leaf_retyped says, when it does. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_retype_leaf(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_LEAF,
        ensures
            ({
                let from = frame.slot() as usize;
                let at = spec_position(frame.argument(3));
                let base = frame.argument(2) as usize;
                &&& !(at is Some && pre.can_retype_leaf(root, from, at->0, base)) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& at is Some && pre.can_retype_leaf(root, from, at->0, base)
                    ==> out == status_only(STATUS_OK) && Self::leaf_retyped(pre, post, root, from, at->0, base)
            }),
    {
    }

    /// A retype of the table page kind reaches retype_table_page: refused with nothing changed unless
    /// can_retype_table_page holds over the untyped in the slot, the base in argument 2 and the level
    /// in argument 4, and ok with an unlinked table page of that level at that base, as
    /// table_page_retyped says, when it does. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_retype_table_page(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_TABLE_PAGE,
        ensures
            ({
                let from = frame.slot() as usize;
                let base = frame.argument(2) as usize;
                let level = frame.argument(4) as usize;
                &&& !pre.can_retype_table_page(root, from, base, level) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_retype_table_page(root, from, base, level)
                    ==> out == status_only(STATUS_OK) && Self::table_page_retyped(pre, post, root, from, base, level)
            }),
    {
    }

    /// A retype of the process kind reaches retype_process: refused with nothing changed unless
    /// can_retype_block holds of the order-3 block at the base in argument 2, under the untyped in the
    /// slot, into the slot in argument 3, and ok with a process there, as process_retyped says, when it
    /// does. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_retype_process(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_PROCESS,
        ensures
            ({
                let from = frame.slot() as usize;
                let to = frame.argument(3) as usize;
                let base = frame.argument(2) as usize;
                &&& !pre.can_retype_block(root, from, to, base, PROCESS_ORDER) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_retype_block(root, from, to, base, PROCESS_ORDER)
                    ==> out == status_only(STATUS_OK) && Self::process_retyped(pre, post, root, from, to, base)
            }),
    {
    }

    /// A retype of the thread kind reaches retype_thread: refused with nothing changed unless
    /// can_retype_thread holds of the order-1 block at the base in argument 2, under the untyped in the
    /// slot, into the slot in argument 3, bound to the process whose capability is in the slot in
    /// argument 4, and ok with a thread there, as thread_retyped says, when it does.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_retype_thread(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_THREAD,
        ensures
            ({
                let from = frame.slot() as usize;
                let to = frame.argument(3) as usize;
                let base = frame.argument(2) as usize;
                let j = frame.argument(4) as usize;
                &&& !pre.can_retype_thread(root, from, to, base, j) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_retype_thread(root, from, to, base, j)
                    ==> out == status_only(STATUS_OK) && Self::thread_retyped(pre, post, root, from, to, base, j)
            }),
    {
    }

    /// A thread retyped through dispatch can be used at once: the control capability in the slot in
    /// argument 3 lets its registers be set and lets it be placed through any core capability that
    /// allows the priority, and the process capability in the slot in argument 4 can take a further
    /// thread while the process's block, which counts one reference more, can count another. A
    /// witness that sets the registers of, places, or retypes a second thread into the same process
    /// starts from this.
    pub proof fn lemma_retyped_thread_usable(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Retype),
            frame.argument(1) == RETYPE_THREAD,
            out == status_only(STATUS_OK),
        ensures
            ({
                let to = frame.argument(3) as usize;
                let j = frame.argument(4) as usize;
                let br = BlockRef::Small(pre.payload_of(pre.tables.node_of(root, j)).base / PAGE_SZ);
                &&& post.can_set_registers(root, to)
                &&& forall|k: usize, priority: usize| #[trigger] post.holds_core(root, k, priority)
                    ==> post.can_place(root, to, k, priority)
                &&& block_refs(&post.blocks, br) == block_refs(&pre.blocks, br) + 1
                &&& block_refs(&post.blocks, br) != usize::MAX ==> post.can_hold_thread(root, j)
            }),
    {
        let from = frame.slot() as usize;
        let to = frame.argument(3) as usize;
        let base = frame.argument(2) as usize;
        let j = frame.argument(4) as usize;
        Self::lemma_entry_reaches_retype_thread(pre, post, root, frame, out);
        assert(pre.can_retype_thread(root, from, to, base, j));
        assert(Self::thread_retyped(pre, post, root, from, to, base, j));
        reveal(CapKernel::thread_retyped_records);
        let child = pre.tables.node_of(root, to);
        let n = pre.tables.node_of(root, j);
        let p = pre.payload_of(n).base;
        pre.lemma_process_cap(n);
        assert(post.tables.has_slot(&post.list, root, to) && post.tables.node_of(root, to) == child);
        assert(post.tables.has_slot(&post.list, root, j) && post.tables.node_of(root, j) == n);
        assert(post.processes.records@[p].value().dead == pre.processes.records@[p].value().dead);
        assert(THREAD_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
        assert(post.payload_of(child).rights & right_bit(Right::Control) != 0);
        assert(post.can_control(root, to));
    }

    /// A link reaches link_at: refused with nothing changed unless can_link_at holds over the frame's
    /// arguments, and ok with the table page linked as table_linked says when it does.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_link_at(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Link),
        ensures
            ({
                let slot = frame.slot() as usize;
                let va = frame.argument(1);
                let level = frame.argument(2);
                let from = frame.argument(3) as usize;
                let child = frame.argument(4) as usize;
                &&& !pre.can_link_at(root, slot, va, level, from, child) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_link_at(root, slot, va, level, from, child)
                    ==> out == status_only(STATUS_OK) && Self::table_linked(pre, post, root, slot, va, level, from, child)
            }),
    {
    }

    /// A map reaches map_at: refused with nothing changed unless can_map_at holds over the frame's
    /// arguments, and ok with the page mapped as page_mapped says when it does.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_map_at(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Map),
        ensures
            ({
                let slot = frame.slot() as usize;
                let va = frame.argument(1);
                let level = frame.argument(2);
                let from = frame.argument(3) as usize;
                let page = frame.argument(4) as usize;
                &&& !pre.can_map_at(root, slot, va, level, from, page) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_map_at(root, slot, va, level, from, page)
                    ==> out == status_only(STATUS_OK) && Self::page_mapped(pre, post, root, slot, va, level, from, page)
            }),
    {
    }

    /// A revoke reaches revoke: refused with nothing changed unless the slot's word names a position
    /// holding a capability; otherwise revoke's Done, ok with the capability's run empty; its Again,
    /// again with some of the run left; or its Exhausted, refused with the flush epoch at its limit, and
    /// only from an epoch within REVOKE_BUDGET of it, raised to the limit by no more than the nodes it
    /// took, so from any other epoch Done or Again. Each of the three took steps of the capability's run
    /// alone, at most REVOKE_BUDGET of them, and Again exactly REVOKE_BUDGET, so a caller repeating on
    /// again shortens the run each time.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_revoke(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Revoke),
        ensures
            ({
                let at = spec_position(frame.slot())->0;
                let c = pre.cap_at(root, at)->0;
                &&& !pre.allows_revoke(root, frame) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.allows_revoke(root, frame) ==> {
                    ||| out == status_only(STATUS_OK) && Self::cap_revoked_at(pre, post, root, at)
                    ||| out == status_only(STATUS_AGAIN) && !post.list.childless(c) && Self::cap_revoking_at(pre, post, root, at)
                        && pre.list.seq@.len() - post.list.seq@.len() == REVOKE_BUDGET
                    ||| out == status_only(STATUS_REFUSED) && pre.flush_epoch + REVOKE_BUDGET >= usize::MAX
                        && post.flush_epoch == usize::MAX && Self::cap_revoking_at(pre, post, root, at)
                        && pre.flush_epoch + (pre.list.seq@.len() - post.list.seq@.len()) >= usize::MAX
                }
                &&& pre.allows_revoke(root, frame) && pre.flush_epoch + REVOKE_BUDGET < usize::MAX ==> {
                    ||| out == status_only(STATUS_OK) && Self::cap_revoked_at(pre, post, root, at)
                    ||| out == status_only(STATUS_AGAIN) && !post.list.childless(c) && Self::cap_revoking_at(pre, post, root, at)
                        && pre.list.seq@.len() - post.list.seq@.len() == REVOKE_BUDGET
                }
            }),
    {
    }

    /// A destroy reaches destroy: refused with nothing changed unless the slot holds a process or
    /// thread capability with control whose object is not dead; ok otherwise, with that process's
    /// record dead and an IPI for each core that has its space loaded, as process_destroyed says, or
    /// that thread destroyed from some core as thread_destroyed says, every capability and every
    /// thread's binding staying. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_destroy(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Destroy),
        ensures
            ({
                let i = frame.slot() as usize;
                let n = pre.tables.node_of(root, i);
                let o = pre.payload_of(n).base;
                &&& !pre.can_destroy(root, i) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_destroy(root, i) ==> out == status_only(STATUS_OK)
                    && bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
                &&& pre.can_destroy(root, i) && pre.payload_of(n).kind is Process ==> Self::process_destroyed(pre, post, o)
                &&& pre.can_destroy(root, i) && pre.payload_of(n).kind is Thread
                    ==> exists|c: usize| c < NUM_CPUS && #[trigger] Self::thread_destroyed(pre, post, c, o)
            }),
    {
    }

    /// A place reaches place: refused with nothing changed unless the slot holds a live, Inactive,
    /// unplaced thread with control and argument 1 a core capability below the depth limit whose
    /// maximum priority is at least the priority in argument 2; ok otherwise, with the thread placed on
    /// that core at that priority under the core capability, as placed says.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_place(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Place),
        ensures
            ({
                let i = frame.slot() as usize;
                let j = frame.argument(1) as usize;
                let priority = frame.argument(2) as usize;
                let m = pre.tables.node_of(root, j);
                let t = pre.payload_of(pre.tables.node_of(root, i)).base;
                &&& !pre.can_place(root, i, j, priority) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_place(root, i, j, priority) ==> out == status_only(STATUS_OK)
                    && Self::placed(pre, post, m, t, Placement { core: core_of(pre.payload_of(m).base), priority })
            }),
    {
    }

    /// A start reaches start: refused with nothing changed unless the slot holds a live, Inactive thread
    /// with control, bound to a process and placed; ok otherwise, with the thread Runnable at the back of
    /// its priority on the core it is placed on, and a reschedule IPI recorded for that core exactly when
    /// it outranks what that core runs. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_start(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Start),
        ensures
            ({
                let i = frame.slot() as usize;
                let t = pre.payload_of(pre.tables.node_of(root, i)).base;
                let pl = pre.threads.records@[t].value().placement->Some_0;
                &&& !pre.can_start(root, i) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_start(root, i) ==> out == status_only(STATUS_OK)
                    && Self::state_written(pre, post, t, ThreadState::Runnable { core: pl.core })
                    && at_back_of_priority(&post.threads.queues, post.threads.records@, pl.core as int, pl.priority, t)
                    && post.resched_ipis@ == if pre.outranks_current(pl.core as int, pl.priority) {
                        pre.resched_ipis@.push(pl.core)
                    } else {
                        pre.resched_ipis@
                    }
            }),
    {
    }

    /// A suspend reaches suspend: refused with nothing changed unless the slot holds a live thread with
    /// control that is Inactive, Runnable or Running; again only for a thread Running, with its stop
    /// pending and a stop IPI recorded for its core; ok otherwise, with the thread Inactive and no stop
    /// pending, which a thread that is not Running always reaches. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_suspend(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Suspend),
        ensures
            ({
                let i = frame.slot() as usize;
                let t = pre.payload_of(pre.tables.node_of(root, i)).base;
                let r = pre.threads.records@[t].value();
                &&& out == status_only(STATUS_REFUSED) || out == status_only(STATUS_OK) || out == status_only(STATUS_AGAIN)
                &&& !pre.can_suspend(root, i) <==> out == status_only(STATUS_REFUSED)
                &&& !pre.can_suspend(root, i) ==> post == pre
                &&& pre.can_suspend(root, i) && !(r.state is Running) ==> out == status_only(STATUS_OK)
                &&& out == status_only(STATUS_OK) ==> Self::record_written(pre, post, t, ThreadRecord { state: ThreadState::Inactive, pending_stop: false, ..r })
                    && post.stop_ipis == pre.stop_ipis
                &&& out == status_only(STATUS_AGAIN) ==> r.state is Running
                    && Self::record_written(pre, post, t, ThreadRecord { pending_stop: true, ..r })
                    && post.stop_ipis@ == pre.stop_ipis@.push(r.state->Running_core)
                    && post.cores == pre.cores
            }),
    {
        let c = choose|c: usize| c < NUM_CPUS && #[trigger] Self::suspended_from(pre, post, c, root, frame, out);
        assert(Self::suspended_from(pre, post, c, root, frame, out));
    }

    /// A read registers reaches read_registers: the kernel is unchanged; refused unless argument 1 is a
    /// multiple of four within the frame and the slot holds a control capability for an Inactive thread
    /// that is not dead; ok otherwise, with that thread's saved frame from argument 1 in results 1 to 4,
    /// zero past the frame's end. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_read_registers(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::ReadRegisters),
        ensures
            post == pre,
            ({
                let i = frame.slot() as usize;
                let index = frame.argument(1);
                &&& !(window_index(index) && pre.can_set_registers(root, i)) ==> out == status_only(STATUS_REFUSED)
                &&& window_index(index) && pre.can_set_registers(root, i)
                    ==> out.status == STATUS_OK && out == window_read(pre.frame_words(root, i), index as int)
            }),
    {
    }

    /// A write registers reaches write_registers: refused with nothing changed unless argument 1 is a
    /// multiple of four within the frame, the slot holds a control capability for an Inactive thread
    /// that is not dead, and the frame with the window written returns to a user address; ok otherwise,
    /// with that thread's saved frame the user frame of the window written over what it held, as
    /// frame_written says. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_write_registers(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::WriteRegisters),
        ensures
            ({
                let i = frame.slot() as usize;
                let index = frame.argument(1);
                let input = pre.written_input(root, frame);
                &&& !pre.allows_write_registers(root, frame) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.allows_write_registers(root, frame) ==> out == status_only(STATUS_OK)
                    && Self::frame_written(pre, post, pre.thread_named(root, i), input)
                &&& pre.allows_write_registers(root, frame) ==> window_index(index) && pre.can_set_registers(root, i)
                    && user_rip(input.spec_pc())
                    && register_words(input) == window_written(pre.frame_words(root, i), index as int, frame)
            }),
    {
        if pre.allows_write_registers(root, frame) {
            let i = frame.slot() as usize;
            lemma_register_words(pre.threads.records@[pre.thread_named(root, i)].value().frame);
            lemma_registers_of(window_written(pre.frame_words(root, i), frame.argument(1) as int, frame));
        }
    }

    /// An unmap reaches unmap_at: refused with nothing changed unless the caller may unmap the entry the
    /// address in argument 1 and the level in argument 2 name, in the space of the capability in the
    /// slot; ok otherwise, with that entry unmapped as page_unmapped says and its bits in the results.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_unmap_at(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Unmap),
        ensures
            ({
                let slot = frame.slot() as usize;
                let va = frame.argument(1);
                let level = frame.argument(2);
                &&& !pre.can_unmap_at(root, slot, va, level) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_unmap_at(root, slot, va, level) ==> out.status == STATUS_OK
                    && exists|read: usize| Self::page_unmapped(pre, post, root, slot, va, level, #[trigger] unmapped_of(out, read))
            }),
    {
    }

    /// A probe reaches probe_at: refused with nothing changed unless the caller may probe the count in
    /// argument 2 of level 1 entries from the one the address in argument 1 names, in the space of the
    /// capability in the slot; ok otherwise, with those entries probed as probe_done says and the masks
    /// in the results. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_probe_at(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Probe),
        ensures
            ({
                let slot = frame.slot() as usize;
                let va = frame.argument(1);
                let count = frame.argument(2);
                &&& !pre.can_probe(root, slot, va, count) ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& pre.can_probe(root, slot, va, count) ==> out.status == STATUS_OK
                    && exists|read: Seq<usize>| Self::probe_done(pre, post, root, slot, va, count, #[trigger] probed_of(out, read))
            }),
    {
    }

    /// An inspect reaches inspect: the kernel is unchanged; refused unless the slot's word names a
    /// position holding a capability; ok when it does, with that capability's payload in the results as
    /// inspected packs it. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_inspect(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
        ensures
            post == pre,
            ({
                let at = spec_position(frame.slot());
                &&& !(at is Some && pre.cap_at(root, at->0) is Some) ==> out == status_only(STATUS_REFUSED)
                &&& at is Some && pre.cap_at(root, at->0) is Some
                    ==> out.status == STATUS_OK && out == inspected(pre.payload_of(pre.cap_at(root, at->0)->0))
            }),
    {
    }

    /// A print reaches print: the kernel is unchanged, refused unless the slot holds a console
    /// capability, and ok when it does, whatever words arguments 1 to 5 carry.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_print(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Print),
        ensures
            ({
                let slot = frame.slot() as usize;
                &&& post == pre
                &&& !pre.holds_console(root, slot) ==> out == status_only(STATUS_REFUSED)
                &&& pre.holds_console(root, slot) ==> out == status_only(STATUS_OK)
            }),
    {
    }

    /// A power-off reaches power_off: the kernel is unchanged, refused unless the slot holds a power
    /// capability, and ok when it does. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_power_off(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::PowerOff),
        ensures
            ({
                let slot = frame.slot() as usize;
                &&& post == pre
                &&& !pre.holds_power(root, slot) ==> out == status_only(STATUS_REFUSED)
                &&& pre.holds_power(root, slot) ==> out == status_only(STATUS_OK)
            }),
    {
    }

    /// A derive reaches derive: refused with nothing changed unless the rights in argument 2 fit 32 bits,
    /// the order in argument 4 fits 8, the slot's word names a position of the caller's own table,
    /// argument 1 names a position, and can_derive_at holds over them, the base in argument 3 and the
    /// badge in argument 5; ok when they do, with the capability derived at argument 1's position as
    /// cap_derived_at says.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_derive(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Derive),
        ensures
            ({
                let from = spec_position(frame.slot());
                let to = spec_position(frame.argument(1));
                let rights = frame.argument(2);
                let base = frame.argument(3) as usize;
                let order = frame.argument(4);
                let badge = frame.argument(5) as usize;
                let succeeds = rights <= u32::MAX as u64 && order <= u8::MAX as u64 && from is Some
                    && from->0.through is None && to is Some
                    && pre.can_derive_at(root, from->0.index, to->0, rights as u32, base, order as u8, badge);
                &&& !succeeds ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& succeeds ==> out == status_only(STATUS_OK)
                    && Self::cap_derived_at(pre, post, root, from->0.index, to->0, rights as u32, base, order as u8, badge)
            }),
    {
    }

    /// A move reaches move_cap: refused with nothing changed unless the slot's word and argument 1 each
    /// name a position and can_move_at holds between them; ok when they do, with the capability moved
    /// as cap_moved_at says. design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_move_cap(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Move),
        ensures
            ({
                let from = spec_position(frame.slot());
                let to = spec_position(frame.argument(1));
                let succeeds = from is Some && to is Some && pre.can_move_at(root, from->0, to->0);
                &&& !succeeds ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& succeeds ==> out == status_only(STATUS_OK) && Self::cap_moved_at(pre, post, root, from->0, to->0)
            }),
    {
    }

    /// A delete reaches delete: refused with nothing changed unless the slot's word names a position and
    /// can_delete_at holds there; ok when it does, with the capability there deleted as cap_deleted_at
    /// says and the reference it held dropped as object_dropped says. delete's Some is the payload it
    /// took out, which the entry does not return: the status is the whole answer.
    /// design/witness-per-way-an-operation-succeeds/.
    pub proof fn lemma_entry_reaches_delete(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            Self::invoked(pre, post, root, frame, out),
            spec_operation(frame.operation_number()) == Some(Operation::Delete),
        ensures
            ({
                let at = spec_position(frame.slot());
                let succeeds = at is Some && pre.can_delete_at(root, at->0);
                &&& !succeeds ==> out == status_only(STATUS_REFUSED) && post == pre
                &&& succeeds ==> out == status_only(STATUS_OK) && Self::cap_deleted_at(pre, post, root, at->0)
                    && Self::object_dropped(pre, post, pre.cap_at(root, at->0)->0)
            }),
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

    /// What dispatch proves of core c's step for frame, which answered ret: well formed, and the
    /// caller's operation as invoked says when one returns to it. A destroy of the caller's own process
    /// or thread leaves the caller to check_current at core c's next entry, which moves it off.
    pub open spec fn dispatched(pre: Self, post: Self, c: int, frame: Registers, ret: Option<Outcome>) -> bool {
        &&& Self::step_ok(pre, post, c)
        &&& (ret is None <==> pre.must_leave(c) || pre.cores@[c].current_thread is None)
        // A caller that must leave, among them one acting within a dead process, reaches no
        // operation and gets nothing back: it is moved off its core and nothing else changes.
        &&& ({
            let t = pre.cores@[c].current_thread->Some_0;
            pre.cores@[c].current_thread is Some
                && pre.processes.records@[pre.threads.records@[t].value().process->Some_0].value().dead
                ==> ret is None
        })
        &&& (pre.must_leave(c) ==> Self::moved_off(pre, post, c, frame, FrameKind::Partial))
        &&& (pre.cores@[c].current_thread is None ==> post == pre)
        &&& (ret is Some ==> {
            let t = pre.cores@[c].current_thread->Some_0;
            let root = pre.threads.records@[t].value().process->Some_0;
            &&& pre.root_live(root)
            &&& pre.cores@[c].space == Some(root)
            &&& post.cores@[c].space == Some(root)
            &&& Self::invoked(pre, post, root, frame, ret->0)
            &&& spec_operation(frame.operation_number()) == Some(Operation::Destroy) && ret->0 == status_only(STATUS_OK)
                && pre.destroys_own(c, root, frame.slot() as usize) ==> post.must_leave(c)
            &&& spec_operation(frame.operation_number()) == Some(Operation::Suspend)
                ==> Self::suspended_from(pre, post, c as usize, root, frame, ret->0)
        })
    }

    /// dispatch begins with check_current on core c: when pre.must_leave(c), check_current's MovedOff
    /// arm moves the current thread off and dispatch returns None without reaching invoked; when
    /// !pre.must_leave(c), check_current's Kept arm keeps pre, returning None with post == pre when
    /// core c runs no thread and proceeding to invoked with ret is Some for core c's live current
    /// thread otherwise.
    pub proof fn lemma_entry_reaches_check_current(pre: Self, post: Self, c: int, frame: Registers, ret: Option<Outcome>)
        requires
            pre.wf(),
            0 <= c < NUM_CPUS,
            Self::dispatched(pre, post, c, frame, ret),
        ensures
            pre.must_leave(c) ==> ret is None && Self::moved_off(pre, post, c, frame, FrameKind::Partial),
            !pre.must_leave(c) ==> pre.current_live(c),
            !pre.must_leave(c) && pre.cores@[c].current_thread is None ==> ret is None && post == pre,
            (!pre.must_leave(c) && pre.cores@[c].current_thread is Some) <==> ret is Some,
            !pre.must_leave(c) && pre.cores@[c].current_thread is Some ==> ({
                let t = pre.cores@[c].current_thread->Some_0;
                let root = pre.threads.records@[t].value().process->Some_0;
                &&& ret is Some
                &&& pre.root_live(root)
                &&& Self::invoked(pre, post, root, frame, ret->0)
            }),
    {
        reveal(current_wf);
        if let Some(t) = pre.cores@[c].current_thread {
            assert(runs(pre.cores@, c, t));
            assert(pre.threads.records@.contains_key(t));
        }
    }

    /// Core c's step for the invocation its current thread entered the kernel with, in frame. The
    /// caller is core c's current thread and the table is its process's, never a name from user
    /// space, and check_current runs first: design/one-lock-bounded-steps/. Returns None when core c
    /// runs no thread after the check, so nothing returns to user mode, and then the step is the
    /// check's alone: the thread moved off with its partial frame copy, or nothing when core c ran
    /// none. Otherwise what returns to the thread, with the operation's effect on the kernel.
    pub fn dispatch(&mut self, c: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Outcome>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            final(steps).count <= old(steps).count + DISPATCH_STEPS,
            Self::dispatched(*old(self), *final(self), c as int, frame, ret),
    {
        proof {
            lemma_revoke_bounds_the_operations();
        }
        match self.check_current(c, frame, FrameKind::Partial, Tracked(steps)) {
            CurrentStep::MovedOff => { return None; },
            CurrentStep::Kept => {},
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
            Some(Operation::Retype) => Some(self.invoke_retype(c, root, frame, Tracked(steps))),
            Some(Operation::Derive) => Some(self.invoke_derive(root, frame, Tracked(steps))),
            Some(Operation::Move) => Some(self.invoke_move(root, frame, Tracked(steps))),
            Some(Operation::Delete) => Some(self.invoke_delete(root, frame, Tracked(steps))),
            Some(Operation::Revoke) => Some(self.invoke_revoke(root, frame, Tracked(steps))),
            Some(Operation::Link) => Some(self.invoke_link(root, frame, Tracked(steps))),
            Some(Operation::Map) => Some(self.invoke_map(root, frame, Tracked(steps))),
            Some(Operation::Unmap) => Some(self.invoke_unmap(root, frame, Tracked(steps))),
            Some(Operation::Probe) => Some(self.invoke_probe(root, frame, Tracked(steps))),
            Some(Operation::Destroy) => Some(self.invoke_destroy(c, root, frame, Tracked(steps))),
            Some(Operation::ReadRegisters) => Some(self.invoke_read_registers(root, frame)),
            Some(Operation::WriteRegisters) => Some(self.invoke_write_registers(root, frame)),
            Some(Operation::Place) => Some(self.invoke_place(root, frame)),
            Some(Operation::Start) => Some(self.invoke_start(root, frame)),
            Some(Operation::Suspend) => Some(self.invoke_suspend(c, root, frame)),
            Some(Operation::Print) => Some(status_only_outcome(
                if self.print(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3), frame.argument(4), frame.argument(5), Tracked(steps)) {
                    STATUS_OK
                } else {
                    STATUS_REFUSED
                },
            )),
            Some(Operation::PowerOff) => Some(status_only_outcome(
                if self.power_off(root, frame.slot() as usize, Tracked(steps)) { STATUS_OK } else { STATUS_REFUSED },
            )),
            Some(Operation::Inspect) => Some(match position(frame.slot()) {
                Some(at) => match self.inspect(root, at, Tracked(steps)) {
                    Some(payload) => inspect_outcome(payload),
                    None => status_only_outcome(STATUS_REFUSED),
                },
                None => status_only_outcome(STATUS_REFUSED),
            }),
            Some(_) => Some(status_only_outcome(STATUS_REFUSED)),
            None => Some(status_only_outcome(STATUS_UNKNOWN)),
        }
    }

    /// Core c's entry for the invocation in frame: dispatch, then, when core c is behind the flush
    /// epoch, its acknowledgement, which flushes it. So the core returns to whatever it runs next
    /// holding no translation of a page that is not mapped, whichever core's unmap left it behind, and
    /// a map that follows on it sees only what the tables say. design/flush-without-waiting/. The
    /// entry makes its one counter in steps, whatever the caller passed, and holds it to ENTRY_STEPS.
    pub fn enter(&mut self, c: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Outcome>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            final(steps).count <= ENTRY_STEPS,
            Self::step_ok(*old(self), *final(self), c as int),
            exists|mid: Self| #[trigger] Self::dispatched(*old(self), mid, c as int, frame, ret)
                && Self::only_core_changed(mid, *final(self), c as int),
            final(self).acked(c as int) == final(self).flush_epoch,
            forall|e: TlbEntry| #[trigger] final(self).tlb@[c as int].contains(e) ==> final(self).mapped@.contains(e.page),
    {
        // The one counter of this entry, on a path that holds the kernel's lock, made here whatever the
        // caller passed: design/one-lock-bounded-steps/.
        proof {
            *steps = Steps::fresh();
        }
        let ret = self.dispatch(c, frame, Tracked(steps));
        let ghost mid = *self;
        if self.cores.get(c).acked_epoch < self.flush_epoch {
            self.acknowledge(c, Tracked(steps));
        }
        proof {
            let post = *self;
            assert(Self::dispatched(*old(self), mid, c as int, frame, ret));
            assert(Self::only_core_changed(mid, post, c as int));
            assert forall|e: TlbEntry| #[trigger] post.tlb@[c as int].contains(e) implies post.mapped@.contains(e.page) by {
                if !post.mapped@.contains(e.page) {
                    assert(post.blocks.tracks(e.page as int));
                    assert(post.stale_epoch.above(post.acked(c as int), e.page));
                    assert(post.stale_epoch.pages@[e.page as int] <= post.flush_epoch);
                }
            }
        }
        ret
    }

    /// Core c's entry for the flush IPI: when core c is behind the flush epoch, its acknowledgement,
    /// which flushes it, and nothing otherwise. The entry makes its one counter in steps, whatever the
    /// caller passed, and holds it to ENTRY_STEPS. design/flush-without-waiting/.
    pub fn enter_flush(&mut self, c: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            final(steps).count <= ENTRY_STEPS,
            Self::step_ok(*old(self), *final(self), c as int),
            Self::only_core_changed(*old(self), *final(self), c as int),
            final(self).acked(c as int) == final(self).flush_epoch,
            old(self).acked(c as int) == old(self).flush_epoch ==> *final(self) == *old(self),
    {
        // The one counter of this entry, on a path that holds the kernel's lock, made here whatever the
        // caller passed: design/one-lock-bounded-steps/.
        proof {
            *steps = Steps::fresh();
            lemma_revoke_bounds_the_operations();
        }
        if self.cores.get(c).acked_epoch < self.flush_epoch {
            self.acknowledge(c, Tracked(steps));
        } else {
            self.no_op(c);
        }
    }

    /// The retype in frame, by a thread of the process whose table is at root.
    fn invoke_retype(&mut self, c: usize, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            c < NUM_CPUS,
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
                proof {
                    reveal(CapKernel::table_page_retyped_fields);
                }
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
        } else if frame.argument(1) == RETYPE_FREE {
            let order = frame.argument(4);
            if order == 0 {
                let step = self.reclaim_frame(c, root, frame.slot() as usize, frame.argument(2) as usize, Tracked(steps));
                proof {
                    if step is Freed {
                        assert(old(self).frame_freed(*self, c, root, frame.slot() as usize, frame.argument(2) as usize));
                    }
                }
                match step {
                    FrameReclaimStep::Freed => STATUS_OK,
                    FrameReclaimStep::Again => STATUS_AGAIN,
                    FrameReclaimStep::Refused => STATUS_REFUSED,
                }
            } else if order == 9 || order == 18 {
                let step = self.reclaim_large_frame(c, root, frame.slot() as usize, frame.argument(2) as usize, order as u8, Tracked(steps));
                proof {
                    if step is Freed {
                        assert(old(self).large_frame_freed(*self, c, root, frame.slot() as usize, frame.argument(2) as usize, order as usize as u8));
                    }
                }
                match step {
                    FrameReclaimStep::Freed => STATUS_OK,
                    FrameReclaimStep::Again => STATUS_AGAIN,
                    FrameReclaimStep::Refused => STATUS_REFUSED,
                }
            } else {
                STATUS_REFUSED
            }
        } else if frame.argument(1) == RETYPE_PROCESS {
            if self.retype_process(root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, Tracked(steps)) {
                STATUS_OK
            } else {
                STATUS_REFUSED
            }
        } else if frame.argument(1) == RETYPE_THREAD {
            if self.retype_thread(root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, frame.argument(4) as usize, Tracked(steps)) {
                STATUS_OK
            } else {
                STATUS_REFUSED
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
                && self.derive(root, from, to, frame.argument(2) as u32, frame.argument(3) as usize, frame.argument(4) as u8, frame.argument(5) as usize),
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
            None => {
                proof {
                    old(self).lemma_no_op_discharges(root);
                }
                false
            },
        };
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The read registers in frame, by a thread of the process whose table is at root.
    fn invoke_read_registers(&self, root: usize, frame: Registers) -> (ret: Outcome)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
            self.root_live(root),
        ensures
            ret == self.spec_read_registers(root, frame),
    {
        let index = frame.argument(1);
        if index % 4 != 0 || index >= FRAME_WORDS as u64 {
            return status_only_outcome(STATUS_REFUSED);
        }
        match self.read_registers(root, frame.slot() as usize) {
            Some(r) => read_window(&r, index as usize),
            None => status_only_outcome(STATUS_REFUSED),
        }
    }

    /// The write registers in frame, by a thread of the process whose table is at root: the window
    /// written over the saved frame read_registers returns, then stored by write_registers.
    fn invoke_write_registers(&mut self, root: usize, frame: Registers) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_registers_written(*old(self), *final(self), root, frame, ret),
    {
        let index = frame.argument(1);
        if index % 4 != 0 || index >= FRAME_WORDS as u64 {
            return status_only_outcome(STATUS_REFUSED);
        }
        let current = match self.read_registers(root, frame.slot() as usize) {
            Some(r) => r,
            None => { return status_only_outcome(STATUS_REFUSED); },
        };
        let input = write_window(current, index as usize, &frame);
        proof {
            lemma_register_words(input);
            assert(input == old(self).written_input(root, frame));
        }
        if self.write_registers(root, frame.slot() as usize, input) {
            status_only_outcome(STATUS_OK)
        } else {
            status_only_outcome(STATUS_REFUSED)
        }
    }

    /// The destroy in frame, by core c's current thread, of the process whose table is at root.
    fn invoke_destroy(&mut self, c: usize, root: usize, frame: Registers, Tracked(steps): Tracked<&mut Steps>) -> (ret: Outcome)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + INVOKE_DESTROY_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_destroyed(*old(self), *final(self), root, frame, ret),
            ret == status_only(STATUS_OK) && old(self).destroys_own(c as int, root, frame.slot() as usize)
                ==> final(self).must_leave(c as int),
    {
        let done = self.destroy(c, root, frame.slot() as usize, Tracked(steps));
        proof {
            let pre = *old(self);
            let post = *self;
            if done {
                assert(Self::destroy_done(pre, post, c, root, frame.slot() as usize));
            }
        }
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The place in frame, by a thread of the process whose table is at root.
    fn invoke_place(&mut self, root: usize, frame: Registers) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_placed(*old(self), *final(self), root, frame, ret),
    {
        let done = self.place(root, frame.slot() as usize, frame.argument(1) as usize, frame.argument(2) as usize);
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The start in frame, by a thread of the process whose table is at root.
    fn invoke_start(&mut self, root: usize, frame: Registers) -> (ret: Outcome)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::spec_started(*old(self), *final(self), root, frame, ret),
    {
        let done = self.start(root, frame.slot() as usize);
        status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED })
    }

    /// The suspend in frame, by core c's current thread, of the process whose table is at root.
    fn invoke_suspend(&mut self, c: usize, root: usize, frame: Registers) -> (ret: Outcome)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores@[c as int].space == old(self).cores@[c as int].space,
            Self::suspended_from(*old(self), *final(self), c, root, frame, ret),
    {
        let step = self.suspend(c, root, frame.slot() as usize);
        status_only_outcome(match step {
            SuspendStep::Refused => STATUS_REFUSED,
            SuspendStep::Suspended => STATUS_OK,
            SuspendStep::Again => STATUS_AGAIN,
        })
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
            None => {
                // The slot word names no position, so revoke is not called. The arm still carries what
                // an unchanged kernel satisfies of revoke's ensures, and blocks_revoked is opaque.
                proof {
                    Self::lemma_blocks_revoked_none(*old(self), *self);
                    assert(Self::mappings_shrunk(*old(self), *self));
                    assert(Self::records_shrunk(*old(self), *self));
                    assert(Self::revoke_preserved(*old(self), *self));
                }
                STATUS_REFUSED
            },
        };
        proof {
            if spec_position(frame.slot()) is Some {
                Self::lemma_revoked_counts_lowered(*old(self), *self);
            }
        }
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
