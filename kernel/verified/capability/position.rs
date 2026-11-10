//! A table position: how an operation names the slot it acts on. The index is into the caller's own
//! table or, through a process capability with the control right held in the caller's own table, into
//! that process's table. One hop, so lookup stays constant time and no capability names a table. See
//! design/process-holds-capabilities/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::define::*;

/// A table position as its caller names it: `index` in the caller's own table when `through` is None,
/// and otherwise in the table of the process that the capability at index `through` of the caller's
/// table names.
#[derive(Clone, Copy)]
pub struct Position {
    pub through: Option<usize>,
    pub index: usize,
}

impl CapKernel {
    /// The table a position is in, for a caller whose table is at root: the caller's own, or the table
    /// of the process named through a capability of the caller's. There is none when `through` names no
    /// slot, an empty one, or a capability that is not a process's or lacks control: a thread's
    /// capability names no table. Whether the process is dead is not read, so an operation that
    /// refuses a dead process's table reads that itself.
    pub open spec fn table_at(&self, root: usize, through: Option<usize>) -> Option<usize> {
        match through {
            None => Some(root),
            Some(cap) => {
                let c = self.tables.node_of(root, cap);
                if self.tables.has_slot(&self.list, root, cap) && self.is_cap(c) && self.payload_of(c).kind is Process
                    && self.payload_of(c).rights & right_bit(Right::Control) != 0 {
                    Some(self.payload_of(c).base)
                } else {
                    None
                }
            },
        }
    }

    /// The capability at a position: there is none when the position is in no table, its index names
    /// no slot of that table, or the slot holds no capability.
    pub open spec fn cap_at(&self, root: usize, at: Position) -> Option<usize> {
        match self.table_at(root, at.through) {
            Some(table) => {
                let n = self.tables.node_of(table, at.index);
                if self.tables.has_slot(&self.list, table, at.index) && self.is_cap(n) {
                    Some(n)
                } else {
                    None
                }
            },
            None => None,
        }
    }

    /// Finds the table a position is in: one lookup in the caller's table when the position names
    /// another's. `through` comes from user space, so it can be refused.
    pub fn find_table(&self, root: usize, through: Option<usize>) -> (ret: Option<usize>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret == self.table_at(root, through),
            ret is Some ==> self.tables.roots@.contains_key(ret->0),
    {
        let cap = match through {
            Some(cap) => cap,
            None => { return Some(root); },
        };
        let (c, payload) = match self.tables.lookup(&self.list, root, cap) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(c);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return None;
        }
        let process = match payload.kind {
            CapKind::Process => true,
            _ => false,
        };
        proof {
            self.lemma_slot(root, cap);
            assert(self.tables.is_cap(&self.list, c));
            assert(payload == self.payload_of(c));
            assert(right_bit(Right::Control) == 128);
        }
        if !process || payload.rights & 128 == 0 {
            return None;
        }
        proof {
            assert(self.processes.records@.contains_key(payload.base));
        }
        Some(payload.base)
    }

    /// Finds the capability at a position, with what it says. The position comes from user space, so
    /// it can be refused. What is found, the caller commands: it holds the capability, or controls the
    /// process that does.
    pub fn find_cap(&self, root: usize, at: Position) -> (ret: Option<(usize, Payload)>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret is Some == self.cap_at(root, at) is Some,
            ret is Some ==> {
                let (n, payload) = ret->0;
                &&& n == self.cap_at(root, at)->0
                &&& payload == self.payload_of(n)
                &&& n < NODE_SPACE
                &&& self.list.valid(n)
                &&& self.is_cap(n)
                &&& self.tables.owner@[page_of(n)].0 == self.table_at(root, at.through)->0
                &&& self.view().commands(root, n)
            },
    {
        let table = match self.find_table(root, at.through) {
            Some(table) => table,
            None => { return None; },
        };
        let (n, payload) = match self.tables.lookup(&self.list, table, at.index) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return None;
        }
        proof {
            self.lemma_slot(table, at.index);
            assert(self.tables.is_cap(&self.list, n));
            assert(payload == self.payload_of(n));
            self.list.lemma_valid_bound(n);
            self.lemma_commands(root, at.through, n);
        }
        Some((n, payload))
    }

    /// No position goes through a thread's capability, or through a process's without control: such a
    /// capability names no table, so an operation on a position through it is refused.
    pub proof fn lemma_no_position_through(&self, root: usize, cap: usize, index: usize)
        requires
            ({
                let c = self.tables.node_of(root, cap);
                ||| !(self.payload_of(c).kind is Process)
                ||| self.payload_of(c).rights & right_bit(Right::Control) == 0
            }),
        ensures
            self.table_at(root, Some(cap)) is None,
            self.cap_at(root, Position { through: Some(cap), index }) is None,
    {
    }

    /// In the caller's own table a position is its index: the capability there is the one in that
    /// slot of the table at root.
    pub proof fn lemma_own_position(&self, root: usize, index: usize)
        ensures
            self.cap_at(root, Position { through: None, index }) is Some
                == (self.tables.has_slot(&self.list, root, index) && self.is_cap(self.tables.node_of(root, index))),
            self.cap_at(root, Position { through: None, index }) is Some
                ==> self.cap_at(root, Position { through: None, index })->0 == self.tables.node_of(root, index),
    {
    }

    /// A caller commands every capability in a table one of its positions can be in: it holds what
    /// its own table holds, and through a process capability with control, what that process's does.
    pub proof fn lemma_commands(&self, root: usize, through: Option<usize>, n: usize)
        requires
            self.wf(),
            self.table_at(root, through) is Some,
            self.is_cap(n),
            self.tables.owner@[page_of(n)].0 == self.table_at(root, through)->0,
        ensures
            self.view().commands(root, n),
    {
        let s = self.view();
        match through {
            None => {
                assert(s.holds(root, n));
            },
            Some(cap) => {
                let c = self.tables.node_of(root, cap);
                self.lemma_slot(root, cap);
                assert(s.holds_right(root, c, Right::Control));
                assert(s.names[c] == self.payload_of(c).base);
                assert(s.holds(s.names[c], n));
            },
        }
    }
}

} // verus!
