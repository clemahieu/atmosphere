//! The operations a process invokes through the one syscall entry, by the number it puts in rax, and
//! what returns: the status in rax's low 16 bits and the result words in rdi, rsi, rdx and r8. asys holds the same numbers for user space, and the
//! kernel crate checks at compile time that the two agree. See design/syscall-abi-in-registers/.
use vstd::prelude::*;

verus! {

use crate::capability::inspect::*;
use crate::capability::kernel::*;
use crate::capability::map::*;
use crate::capability::reach::*;
use crate::capability::space::*;
use crate::capability::thread::*;
use crate::define::NUM_CPUS;
use crate::pptr::*;
use crate::trap::Registers;

/// The operation was done.
pub const STATUS_OK: u64 = 0;

/// The capability, its rights or the arguments do not allow the operation.
pub const STATUS_REFUSED: u64 = 1;

/// No operation has the number in rax.
pub const STATUS_UNKNOWN: u64 = 2;

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

/// Retype's kind in rsi for a 4K frame.
pub const RETYPE_FRAME: u64 = 0;

/// Retype's kind in rsi for a table page, of the level in r9. Every other kind is refused until it is
/// wired.
pub const RETYPE_TABLE_PAGE: u64 = 2;

/// What an invocation returns to its thread: the status for rax and the result words for rdi, rsi, rdx
/// and r8.
#[derive(Clone, Copy)]
pub struct Outcome {
    pub status: u64,
    pub rdi: u64,
    pub rsi: u64,
    pub rdx: u64,
    pub r8: u64,
}

/// The outcome of an operation that returns a status and no result words.
pub open spec fn status_only(status: u64) -> Outcome {
    Outcome { status, rdi: 0, rsi: 0, rdx: 0, r8: 0 }
}

/// The outcome of an operation that returns a status and no result words.
pub fn status_only_outcome(status: u64) -> (ret: Outcome)
    ensures
        ret == status_only(status),
{
    Outcome { status, rdi: 0, rsi: 0, rdx: 0, r8: 0 }
}

/// What a process asks of the capability named in rdi.
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
}

impl Operation {
    /// The number a process puts in rax to invoke the operation.
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
        _ => None,
    };
    proof {
        if ret is Some {
            lemma_number_names_one_operation(ret->0);
        }
    }
    ret
}

impl CapKernel {
    /// What the invocation in frame returns to a thread of the process whose table is at root, for an
    /// operation that leaves the kernel unchanged: print's status for print, inspect's outcome for
    /// inspect, refused for every operation not wired yet, and unknown for a number no operation has.
    /// The slot is rdi and print's words are rsi, rdx, r8, r9 and r10, as
    /// design/syscall-abi-in-registers/ places them.
    pub open spec fn spec_outcome(&self, root: usize, frame: Registers) -> Outcome {
        match spec_operation(frame.rax) {
            Some(Operation::Print) => status_only(
                if self.can_print(root, frame.rdi as usize) { STATUS_OK } else { STATUS_REFUSED },
            ),
            Some(Operation::Inspect) => self.spec_inspect(root, frame.rdi as usize),
            Some(_) => status_only(STATUS_REFUSED),
            None => status_only(STATUS_UNKNOWN),
        }
    }

    /// A retype in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed; for the 4K frame kind in rsi, ok with the frame at the
    /// base in rdx retyped under the untyped in rdi into the slot in r8; or, for the table page kind, ok
    /// with an unlinked table page of the level in r9 at the base in rdx under the untyped in rdi. A
    /// retype the arguments allow can still be refused, when the block table finds the memory is not free.
    pub open spec fn spec_retyped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& frame.rsi == RETYPE_FRAME
            &&& out == status_only(STATUS_OK)
            &&& Self::frame_retyped(pre, post, root, frame.rdi as usize, frame.r8 as usize, frame.rdx as usize)
        }
        ||| {
            &&& frame.rsi == RETYPE_TABLE_PAGE
            &&& out == status_only(STATUS_OK)
            &&& Self::table_page_retyped(pre, post, root, frame.rdi as usize, frame.rdx as usize, frame.r9 as usize)
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
    /// returned: refused with nothing changed, or ok with the table page at the base in r9, under the
    /// untyped in r8, linked into the entry the address in rsi and the level in rdx name in the space of
    /// the capability in rdi.
    pub open spec fn spec_linked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::table_linked(pre, post, root, frame.rdi as usize, frame.rsi, frame.rdx, frame.r8 as usize, frame.r9 as usize)
        }
    }

    /// A map in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the page at the offset in r9 of the frame in r8
    /// mapped into the entry the address in rsi and the level in rdx name in the space of the capability
    /// in rdi.
    pub open spec fn spec_mapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::page_mapped(pre, post, root, frame.rdi as usize, frame.rsi, frame.rdx, frame.r8 as usize, frame.r9 as usize)
        }
    }

    /// An unmap in frame by a thread of the process whose table is at root, from pre to post with out
    /// returned: refused with nothing changed, or ok with the entry the address in rsi and the level in
    /// rdx name in the space of the capability in rdi cleared.
    pub open spec fn spec_unmapped(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        ||| out == status_only(STATUS_REFUSED) && post == pre
        ||| {
            &&& out == status_only(STATUS_OK)
            &&& Self::page_unmapped(pre, post, root, frame.rdi as usize, frame.rsi, frame.rdx)
        }
    }

    /// What the invocation in frame by a thread of the process whose table is at root did, from pre to
    /// post with out returned: a retype's effect for retype, a link's for link, a map's for map, an
    /// unmap's for unmap, and for every other operation the kernel unchanged with spec_outcome returned.
    pub open spec fn invoked(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome) -> bool {
        match spec_operation(frame.rax) {
            Some(Operation::Retype) => Self::spec_retyped(pre, post, root, frame, out),
            Some(Operation::Link) => Self::spec_linked(pre, post, root, frame, out),
            Some(Operation::Map) => Self::spec_mapped(pre, post, root, frame, out),
            Some(Operation::Unmap) => Self::spec_unmapped(pre, post, root, frame, out),
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
        match operation(frame.rax) {
            Some(Operation::Retype) => {
                let done = if frame.rsi == RETYPE_FRAME {
                    self.retype_frame(root, frame.rdi as usize, frame.r8 as usize, frame.rdx as usize)
                } else if frame.rsi == RETYPE_TABLE_PAGE {
                    self.retype_table_page(root, frame.rdi as usize, frame.rdx as usize, frame.r9 as usize)
                } else {
                    false
                };
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Link) => {
                let done = self.link_at(root, frame.rdi as usize, frame.rsi, frame.rdx, frame.r8 as usize, frame.r9 as usize);
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Map) => {
                let done = self.map_at(root, frame.rdi as usize, frame.rsi, frame.rdx, frame.r8 as usize, frame.r9 as usize);
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Unmap) => {
                let done = self.unmap_at(root, frame.rdi as usize, frame.rsi, frame.rdx);
                Some(status_only_outcome(if done { STATUS_OK } else { STATUS_REFUSED }))
            },
            Some(Operation::Print) => Some(
                status_only_outcome(
                    self.print(root, frame.rdi as usize, frame.rsi, frame.rdx, frame.r8, frame.r9, frame.r10),
                ),
            ),
            Some(Operation::Inspect) => Some(self.inspect(root, frame.rdi as usize)),
            Some(_) => Some(status_only_outcome(STATUS_REFUSED)),
            None => Some(status_only_outcome(STATUS_UNKNOWN)),
        }
    }
}

} // verus!
