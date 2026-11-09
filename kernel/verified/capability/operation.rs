//! The operations a process invokes through the one syscall entry, by the number in the operation
//! position, and what returns: the status in the status word's low 16 bits and the result words. The
//! frame's positions are the arch module's syscall register table. asys holds the same numbers for user
//! space, and the kernel crate checks at compile time that the two agree. See
//! design/syscall-abi-in-registers/.
use vstd::prelude::*;

verus! {

use crate::capability::inspect::*;
use crate::capability::kernel::*;
use crate::capability::map::*;
use crate::capability::probe::*;
use crate::capability::reach::*;
use crate::capability::retype::RetypeStep;
use crate::capability::revoke::RevokeStep;
use crate::capability::space::*;
use crate::capability::thread::*;
use crate::define::NUM_CPUS;
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

pub const OPERATION_RETYPE: u64 = 1;
pub const OPERATION_DERIVE: u64 = 2;
pub const OPERATION_MOVE: u64 = 3;
pub const OPERATION_CLAIM: u64 = 4;
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

/// Retype's kind in argument 1 for a 4K frame.
pub const RETYPE_FRAME: u64 = 0;

/// Retype's kind in argument 1 for a 2M frame, a block of order 9.
pub const RETYPE_LARGE_FRAME: u64 = 1;

/// Retype's kind in argument 1 for a table page, of the level in argument 4. Every other kind is
/// refused until it is wired.
pub const RETYPE_TABLE_PAGE: u64 = 2;

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
    Claim,
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
}

impl Operation {
    /// The number a process puts in the operation position to invoke the operation.
    pub open spec fn number(self) -> u64 {
        match self {
            Operation::Retype => OPERATION_RETYPE,
            Operation::Derive => OPERATION_DERIVE,
            Operation::Move => OPERATION_MOVE,
            Operation::Claim => OPERATION_CLAIM,
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
        OPERATION_CLAIM => Some(Operation::Claim),
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

impl CapKernel {
    /// What the invocation in frame returns to a thread of the process whose table is at root, for an
    /// operation that leaves the kernel unchanged: print's status for print, inspect's outcome for
    /// inspect, refused for every operation not wired yet, and unknown for a number no operation has.
    /// Print's words are arguments 1 to 5, as design/syscall-abi-in-registers/ places them.
    pub open spec fn spec_outcome(&self, root: usize, frame: Registers) -> Outcome {
        match spec_operation(frame.operation_number()) {
            Some(Operation::Print) => status_only(
                if self.can_print(root, frame.slot() as usize) { STATUS_OK } else { STATUS_REFUSED },
            ),
            Some(Operation::Inspect) => self.spec_inspect(root, frame.slot() as usize),
            Some(_) => status_only(STATUS_REFUSED),
            None => status_only(STATUS_UNKNOWN),
        }
    }

    /// A retype in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed; for the 4K frame kind in argument 1, ok with the frame
    /// at the base in argument 2 retyped under the untyped in the slot into the slot in argument 3; for
    /// the 2M frame kind, again with the block at the base in argument 2 a step further zeroed and no
    /// slot changed, or ok with the 2M frame retyped into the slot in argument 3 once the block is all
    /// zero; or, for the table page kind, ok with an unlinked table page of the level in argument 4 at
    /// the base in argument 2 under the untyped in the slot. A
    /// retype the arguments allow can still be refused, when the block table finds the memory is not free.
    pub open spec fn spec_retyped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& frame.argument(1) == RETYPE_FRAME
            &&& out == status_only(STATUS_OK)
            &&& Self::frame_retyped(pre, post, root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LARGE_FRAME
            &&& out == status_only(STATUS_AGAIN)
            &&& Self::large_frame_zeroing(pre, post, root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, 9)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_LARGE_FRAME
            &&& out == status_only(STATUS_OK)
            &&& Self::large_frame_retyped(pre, post, root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, 9)
        }
        ||| {
            &&& frame.argument(1) == RETYPE_TABLE_PAGE
            &&& out == status_only(STATUS_OK)
            &&& Self::table_page_retyped(pre, post, root, frame.slot() as usize, frame.argument(2) as usize, frame.argument(4) as usize)
        }
    }

    /// What a retype of the order-3 block at base as a table page of level did, under the untyped at
    /// index from of the table at root: the retype was allowed and the block free, the page is an empty
    /// table of that level that no space links and no capability names, the untyped's child, and the
    /// step discharges the retype's effect.
    pub open spec fn table_page_retyped(pre: Self, post: Self, root: usize, from: usize, base: usize, level: usize) -> bool {
        let parent = pre.tables.node_of(root, from);
        &&& pre.can_retype_under(root, from, base, 3)
        &&& pre.view().holds_right(root, parent, Right::Retype)
        &&& pre.blocks.pages@[(base / 4096) as int].kind is Free
        &&& 1 <= level <= 3
        &&& post.table_pages.maps@.contains_key(base)
        &&& post.table_pages.records@[base].value() == fresh_table(level)
        &&& forall|i: usize| i < 512 ==> #[trigger] post.table_pages.maps@[base].value()[i].is_empty()
        &&& post.list.is_child(parent, base)
        &&& forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x)
        &&& post.tables == pre.tables
        &&& post.spaces == pre.spaces
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base })
    }

    /// A link in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the table page at the base in argument 4,
    /// under the untyped in argument 3, linked into the entry the address in argument 1 and the level in
    /// argument 2 name in the space of the capability in the slot.
    pub open spec fn spec_linked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::table_linked(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize)
        }
    }

    /// A map in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the page at the offset in argument 4 of the
    /// frame in argument 3 mapped into the entry the address in argument 1 and the level in argument 2
    /// name in the space of the capability in the slot.
    pub open spec fn spec_mapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::page_mapped(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize)
        }
    }

    /// An unmap in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the entry the address in argument 1 and the
    /// level in argument 2 name in the space of the capability in the slot cleared.
    pub open spec fn spec_unmapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::page_unmapped(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2))
        }
    }

    /// A probe in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the accessed and dirty bits of the count in
    /// argument 2 of level 1 entries, from the one the address in argument 1 names in the space of the
    /// capability in the slot, read and cleared, the accessed mask in result 1, the dirty mask in result 2,
    /// and whether the target maintains each bit in results 3 and 4, 1 when it does and 0 when it does not.
    pub open spec fn spec_probed(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out.status == STATUS_OK
            &&& out.result_3 <= 1
            &&& out.result_4 <= 1
            &&& exists|read: Seq<usize>| Self::probe_done(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), #[trigger] probed_of(out, read))
        }
    }

    /// A derive in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with a child of the capability in the slot put in
    /// the slot in argument 1, with the rights in argument 2 and the block of the order in argument 4 at
    /// the base in argument 3. Rights wider than 32 bits and an order wider than 8 are refused, since no
    /// capability holds them.
    pub open spec fn spec_derived(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& frame.argument(2) <= u32::MAX as u64
            &&& frame.argument(4) <= u8::MAX as u64
            &&& Self::cap_derived(pre, post, root, frame.slot() as usize, frame.argument(1) as usize, frame.argument(2) as u32, frame.argument(3) as usize, frame.argument(4) as u8)
        }
    }

    /// A move in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the capability in the slot moved to the slot
    /// in argument 1.
    pub open spec fn spec_moved(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::cap_moved(pre, post, root, frame.slot() as usize, frame.argument(1) as usize)
        }
    }

    /// A delete in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the childless capability in the slot gone.
    pub open spec fn spec_deleted(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| out == status_only(STATUS_OK) && Self::cap_deleted(pre, post, root, frame.slot() as usize)
    }

    /// A revoke in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed; refused with the flush epoch at its limit, after the steps
    /// it took on the run of the capability in the slot; again with a step of that run taken and some of
    /// it left; or ok with the run empty. See design/revoke-by-depth-first-list/.
    pub open spec fn spec_revoked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        let i = frame.slot() as usize;
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_REFUSED)
            &&& post.flush_epoch == usize::MAX
            &&& Self::cap_revoking(pre, post, root, i)
        }
        ||| {
            &&& out == status_only(STATUS_AGAIN)
            &&& !post.list.childless(pre.tables.node_of(root, i))
            &&& Self::cap_revoking(pre, post, root, i)
        }
        ||| out == status_only(STATUS_OK) && Self::cap_revoked(pre, post, root, i)
    }

    /// What the invocation in frame by a thread of the process whose table is at root did, from pre to
    /// post with out returned: a retype's effect for retype, a derive's for derive, a move's for move, a
    /// delete's for delete, a revoke's for revoke, a link's for link, a map's for map, an unmap's for
    /// unmap, a probe's for probe, and for every other operation the kernel unchanged with spec_outcome returned.
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

    /// Core c's step for the invocation its current thread entered the kernel with, in frame. The
    /// caller is core c's current thread and the table is its process's, never a name from user
    /// space, and check_current runs first: design/one-lock-bounded-steps/. Returns None when core c
    /// runs no thread after the check, so nothing returns to user mode; otherwise what returns to the
    /// thread, with the operation's effect on the kernel.
    pub fn dispatch(&mut self, c: usize, frame: Registers) -> (ret: Option<Outcome>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            ret is None <==> old(self).must_leave(c as int) || old(self).cores@[c as int].current_thread is None,
            ret is Some ==> {
                let t = old(self).cores@[c as int].current_thread->Some_0;
                let root = old(self).threads.records@[t].value().process->Some_0;
                Self::invoked(*old(self), *final(self), root, frame, ret->0)
            },
    {
        if self.check_current(c, frame) {
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
        let record = *PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096).borrow(
            Tracked(self.threads.records.borrow().tracked_borrow(t)),
        );
        let root = match record.process {
            Some(root) => root,
            None => { proof { assert(false); } return None; },
        };
        match operation(frame.operation_number()) {
            Some(Operation::Retype) => {
                let status = if frame.argument(1) == RETYPE_FRAME {
                    if self.retype_frame(root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize) {
                        STATUS_OK
                    } else {
                        STATUS_REFUSED
                    }
                } else if frame.argument(1) == RETYPE_LARGE_FRAME {
                    match self.retype_large_frame(root, frame.slot() as usize, frame.argument(3) as usize, frame.argument(2) as usize, 9) {
                        RetypeStep::Refused => STATUS_REFUSED,
                        RetypeStep::Again => STATUS_AGAIN,
                        RetypeStep::Done => STATUS_OK,
                    }
                } else if frame.argument(1) == RETYPE_TABLE_PAGE {
                    if self.retype_table_page(root, frame.slot() as usize, frame.argument(2) as usize, frame.argument(4) as usize) {
                        STATUS_OK
                    } else {
                        STATUS_REFUSED
                    }
                } else {
                    STATUS_REFUSED
                };
                Some(status_only_outcome(status))
            },
            Some(Operation::Derive) => {
                let done = frame.argument(2) <= u32::MAX as u64 && frame.argument(4) <= u8::MAX as u64 && self.derive(
                    root,
                    frame.slot() as usize,
                    frame.argument(1) as usize,
                    frame.argument(2) as u32,
                    frame.argument(3) as usize,
                    frame.argument(4) as u8,
                );
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Move) => {
                let done = self.move_cap(root, frame.slot() as usize, frame.argument(1) as usize);
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Delete) => {
                let done = self.delete(root, frame.slot() as usize).is_some();
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Revoke) => {
                let status = match self.revoke(root, frame.slot() as usize) {
                    RevokeStep::Done => STATUS_OK,
                    RevokeStep::Again => STATUS_AGAIN,
                    RevokeStep::Refused | RevokeStep::Exhausted => STATUS_REFUSED,
                };
                Some(status_only_outcome(status))
            },
            Some(Operation::Link) => {
                let done = self.link_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize);
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Map) => {
                let done = self.map_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize);
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Unmap) => {
                let done = self.unmap_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2));
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Probe) => {
                let ghost pre = *self;
                match self.probe_at(root, frame.slot() as usize, frame.argument(1), frame.argument(2)) {
                Some(r) => {
                    let out = probe_outcome(r);
                    proof {
                        assert(Self::probe_done(pre, *self, root, frame.slot() as usize, frame.argument(1), frame.argument(2), probed_of(out, r.read@)));
                    }
                    Some(out)
                },
                    None => Some(status_only_outcome(STATUS_REFUSED)),
                }
            },
            Some(Operation::Print) => Some(
                status_only_outcome(
                    self.print(root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3), frame.argument(4), frame.argument(5)),
                ),
            ),
            Some(Operation::Inspect) => Some(self.inspect(root, frame.slot() as usize)),
            Some(_) => Some(status_only_outcome(STATUS_REFUSED)),
            None => Some(status_only_outcome(STATUS_UNKNOWN)),
        }
    }
}

} // verus!
