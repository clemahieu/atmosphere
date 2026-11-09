//! The operations a process invokes through the one syscall entry, by the number it puts in rax, and
//! the status rax returns in its low 16 bits. asys holds the same numbers for user space, and the
//! kernel crate checks at compile time that the two agree. See design/syscall-abi-in-registers/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
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
    /// The status the invocation in frame returns to a thread of the process whose table is at root:
    /// print's for print, refused for every other operation, none of which is wired yet, and unknown
    /// for a number no operation has. The slot is rdi and print's words are rsi, rdx, r8, r9 and r10, as
    /// design/syscall-abi-in-registers/ places them.
    pub open spec fn spec_status(&self, root: usize, frame: Registers) -> u64 {
        match spec_operation(frame.rax) {
            Some(Operation::Print) => if self.can_print(root, frame.rdi as usize) { STATUS_OK } else { STATUS_REFUSED },
            Some(_) => STATUS_REFUSED,
            None => STATUS_UNKNOWN,
        }
    }

    /// Core c's step for the invocation its current thread entered the kernel with, in frame. The
    /// caller is core c's current thread and the table is its process's, never a name from user
    /// space, and check_current runs first: design/one-lock-bounded-steps/. Returns None when core c
    /// runs no thread after the check, so nothing returns to user mode; otherwise the status for rax,
    /// with the kernel unchanged.
    pub fn dispatch(&mut self, c: usize, frame: Registers) -> (ret: Option<u64>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            ret is None <==> old(self).must_leave(c as int) || old(self).cores@[c as int].current_thread is None,
            ret is Some ==> {
                let t = old(self).cores@[c as int].current_thread->Some_0;
                let root = old(self).threads.records@[t].value().process->Some_0;
                &&& *final(self) == *old(self)
                &&& ret->0 == old(self).spec_status(root, frame)
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
            Some(Operation::Print) => Some(
                self.print(root, frame.rdi as usize, frame.rsi, frame.rdx, frame.r8, frame.r9, frame.r10),
            ),
            Some(_) => Some(STATUS_REFUSED),
            None => Some(STATUS_UNKNOWN),
        }
    }
}

} // verus!
