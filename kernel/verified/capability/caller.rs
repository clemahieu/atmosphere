//! The caller's view: a table as the process it belongs to reads it, slot by slot, so a contract on an
//! operation speaks of the caller's slots and not of the list or the tables. A contract here is proven
//! from the operation's specification in invoked, and a verified user crate carries it as the ensures
//! of the operation's syscall wrapper. See design/theorem-over-reach/ and
//! design/process-holds-capabilities/.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::arch::Registers;
use crate::capability::derive::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::operation::*;
use crate::capability::position::*;
use crate::capability::reach::*;
use crate::capability::table::*;
use crate::capability::view::*;

/// What a slot holding a capability says to the process whose table it is in: the capability's kind,
/// the block or object it names and the block's order, its rights, and the node it was derived from.
pub ghost struct SlotView {
    pub kind: CapKind,
    pub base: usize,
    pub order: u8,
    pub rights: u32,
    pub parent: usize,
}

/// Two indices of a table with the same root entry and the same place in its leaf are one index.
proof fn lemma_index_parts(i: usize, j: usize)
    requires
        index_entry(i) == index_entry(j),
        index_slot(i) == index_slot(j),
    ensures
        i == j,
{
    assert(i == 128 * (i / 128) + i % 128) by (nonlinear_arith);
    assert(j == 128 * (j / 128) + j % 128) by (nonlinear_arith);
}

/// A slot's capability may change the space it names, as writes_space reads it: a device space's with
/// the write right, or a process's with the control right.
pub open spec fn view_writes_space(v: SlotView) -> bool {
    ||| v.kind is Space && v.rights & right_bit(Right::Write) != 0
    ||| v.kind is Process && v.rights & right_bit(Right::Control) != 0
}

/// A slot's capability may retype the block of the order at base, as can_retype_under reads it within
/// one view: an untyped with the retype right whose block holds that one.
pub open spec fn view_retypes(v: SlotView, base: usize, order: u8) -> bool {
    &&& v.kind is Untyped
    &&& v.rights & right_bit(Right::Retype) != 0
    &&& order <= v.order
    &&& v.base <= base
    &&& base as int % block_bytes(order) == 0
    &&& base as int + block_bytes(order) <= v.base as int + block_bytes(v.order)
}

impl CapKernel {
    /// Index i of the table at root is a slot that holds a capability.
    pub open spec fn holds_slot(&self, root: usize, i: usize) -> bool {
        self.tables.has_slot(&self.list, root, i) && self.is_cap(self.tables.node_of(root, i))
    }

    /// What the capability in the slot at index i of the table at root says.
    pub open spec fn slot_view(&self, root: usize, i: usize) -> SlotView {
        let n = self.tables.node_of(root, i);
        let p = self.payload_of(n);
        SlotView { kind: p.kind, base: p.base, order: p.order, rights: p.rights, parent: self.list.parent@[n] }
    }

    /// The table at root as its process reads it: each index that is a slot holding a capability, and
    /// what that capability says.
    pub open spec fn table_view(&self, root: usize) -> Map<usize, SlotView> {
        Map::new(
            Set::range(0usize, TABLE_INDICES).filter(|i: usize| self.holds_slot(root, i)),
            |i: usize| self.slot_view(root, i),
        )
    }

    /// The table a position is in, read from the caller's view: the caller's own, or the table of the
    /// process a process capability with control in the caller's view names.
    pub open spec fn view_table_at(&self, root: usize, through: Option<usize>) -> Option<usize> {
        match through {
            None => Some(root),
            Some(cap) => {
                let v = self.table_view(root);
                if v.contains_key(cap) && v[cap].kind is Process && v[cap].rights & right_bit(Right::Control) != 0 {
                    Some(v[cap].base)
                } else {
                    None
                }
            },
        }
    }

    /// The table view holds exactly the indices that are slots holding a capability, each saying what
    /// its capability says.
    pub proof fn lemma_table_view(&self, root: usize, i: usize)
        ensures
            self.table_view(root).contains_key(i) == self.holds_slot(root, i),
            self.holds_slot(root, i) ==> self.table_view(root)[i] == self.slot_view(root, i),
    {
        broadcast use vstd::set::lemma_set_filter, vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;
    }

    /// The caller's view agrees with view_of: an index is in the table's view exactly when it is a slot
    /// whose capability that table's process holds, and the view's entry says what view_of says the
    /// capability names, how many pages it covers, which rights it carries and what its parent is.
    pub proof fn lemma_table_view_agrees(&self, root: usize, i: usize)
        requires
            self.wf(),
        ensures
            self.table_view(root).contains_key(i)
                == (self.tables.has_slot(&self.list, root, i) && self.view().holds(root, self.tables.node_of(root, i))),
            self.table_view(root).contains_key(i) ==> {
                let n = self.tables.node_of(root, i);
                let v = self.table_view(root)[i];
                &&& self.view().names[n] == v.base
                &&& self.view().pages[n] == pow2(v.order as nat)
                &&& forall|r: Right| #[trigger] self.view().rights.contains((n, r)) == (v.rights & right_bit(r) != 0)
                &&& self.view().parent[n] == v.parent
            },
    {
        self.lemma_table_view(root, i);
        if self.tables.has_slot(&self.list, root, i) {
            self.lemma_slot(root, i);
        }
    }

    /// The view's table is the one table_at finds.
    pub proof fn lemma_view_table_at(&self, root: usize, through: Option<usize>)
        ensures
            self.view_table_at(root, through) == self.table_at(root, through),
    {
        if let Some(cap) = through {
            self.lemma_table_view(root, cap);
        }
    }

    /// Whether a capability may be deleted, as the kernel reads it beyond any one table's view: it is
    /// not the list's first node, and nothing was derived from it, in any table or none.
    pub open spec fn deletable(&self, n: usize) -> bool {
        &&& self.list.nodes@[n as int].depth > 0
        &&& self.list.childless(n)
    }

    /// Delete's condition over the caller's view: the position word names a position, the position is
    /// in a table, the slot there holds a capability, and that capability is deletable.
    pub open spec fn delete_allowed(&self, root: usize, at: Option<Position>) -> bool {
        let table = self.view_table_at(root, at->0.through);
        &&& at is Some
        &&& table is Some
        &&& self.table_view(table->0).contains_key(at->0.index)
        &&& self.deletable(self.tables.node_of(table->0, at->0.index))
    }

    /// Delete's contract over the caller's view, for the position word decoded to at: refused, with
    /// every table's view as it was, exactly when delete_allowed fails; otherwise ok, with the slot at
    /// the position gone from its table's view and every other slot of every table as it was.
    pub open spec fn delete_contract(pre: Self, post: Self, root: usize, at: Option<Position>, out: Outcome) -> bool {
        ||| {
            &&& !pre.delete_allowed(root, at)
            &&& out == status_only(STATUS_REFUSED)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            let table = pre.view_table_at(root, at->0.through)->0;
            &&& pre.delete_allowed(root, at)
            &&& out == status_only(STATUS_OK)
            &&& post.table_view(table) == pre.table_view(table).remove(at->0.index)
            &&& forall|t: usize| t != table ==> #[trigger] post.table_view(t) == pre.table_view(t)
        }
    }

    /// A step that leaves the tables as they were and changes no node's liveness but n's, a slot's,
    /// leaves every table's slots as they were.
    pub proof fn lemma_slots_stay(pre: Self, post: Self, n: usize, t: usize, j: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            post.tables == pre.tables,
            n % 4096 != 0,
        ensures
            post.tables.has_slot(&post.list, t, j) == pre.tables.has_slot(&pre.list, t, j),
    {
        let leaf = pre.tables.leaf(t, index_entry(j));
        if index_ok(j) && pre.tables.roots@.contains_key(t) && leaf != NO_LEAF {
            assert(0 <= index_entry(j) < ROOT_ENTRIES);
            pre.tables.lemma_entry(t, index_entry(j));
            pre.tables.lemma_leaf(&pre.list, leaf);
            assert(leaf % 4096 == 0);
            pre.lemma_slot_bound(leaf);
            assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
        }
    }

    /// Delete's specification implies its contract.
    pub proof fn lemma_delete_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::spec_deleted(pre, post, root, frame, out),
        ensures
            Self::delete_contract(pre, post, root, spec_position(frame.slot()), out),
    {
        let at = spec_position(frame.slot());
        if let Some(a) = at {
            pre.lemma_view_table_at(root, a.through);
            if let Some(table) = pre.table_at(root, a.through) {
                pre.lemma_table_view(table, a.index);
            }
        }
        if out == status_only(STATUS_OK) {
            let a = at->0;
            let table = pre.table_at(root, a.through)->0;
            let n = pre.cap_at(root, a)->0;
            pre.lemma_slot(table, a.index);
            assert forall|t: usize| #[trigger] post.table_view(t) == if t == table { pre.table_view(t).remove(a.index) } else { pre.table_view(t) } by {
                assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == (if t == table { pre.table_view(t).remove(a.index) } else { pre.table_view(t) }).contains_key(j)
                    && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == pre.table_view(t)[j]) by {
                    pre.lemma_table_view(t, j);
                    post.lemma_table_view(t, j);
                    Self::lemma_slots_stay(pre, post, n, t, j);
                    if pre.tables.has_slot(&pre.list, t, j) {
                        pre.lemma_slot(t, j);
                        let m = pre.tables.node_of(t, j);
                        let leaf = pre.tables.leaf(t, index_entry(j));
                        pre.lemma_slot_bound(m);
                        if m == n {
                            pre.tables.lemma_entry(t, index_entry(j));
                            pre.tables.lemma_entry(table, index_entry(a.index));
                            lemma_index_parts(j, a.index);
                        } else {
                            Self::lemma_caps_frame(pre, post, n, n, m);
                        }
                    }
                }
                assert(post.table_view(t) =~= if t == table { pre.table_view(t).remove(a.index) } else { pre.table_view(t) });
            }
        }
    }

    /// Whether the table page at child can be linked into the entry the address va and the level name in
    /// the space whose root is s, as the kernel reads it beyond any table's view: the walk finds a live
    /// table of that space with that entry empty and able to hold a child, and the child is a live,
    /// never linked or written table page one level below it.
    pub open spec fn link_fits(&self, s: usize, va: u64, level: u64, child: usize) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        match self.link_parent(s, va, level) {
            None => false,
            Some(place) => {
                &&& tree.is_table(place.table)
                &&& tree.record(place.table).space == Some(s)
                &&& !self.blocks.pages@[(place.table / 4096) as int].dead
                &&& tree.child_slot(place.table, place.entry)
                &&& tree.entry(place.table, place.entry).is_empty()
                &&& tree.is_page(child)
                &&& !self.blocks.pages@[(child / 4096) as int].dead
                &&& tree.record(child).level + 1 == tree.record(place.table).level
                &&& tree.record(child).space is None
                &&& tree.record(child).parent is None
                &&& !tree.record(child).written
            },
        }
    }

    /// Link's condition over the caller's view, for the space capability at index slot and the untyped at
    /// index from of the caller's table at root: the slot holds a capability that may change its space,
    /// naming no dead process; the untyped's slot holds one that may retype the child's order-3 block,
    /// above the deepest depth; and link_fits holds in that space. The process's liveness, the untyped's
    /// depth and link_fits read the kernel outside the view.
    pub open spec fn link_allowed(&self, root: usize, slot: usize, va: u64, level: u64, from: usize, child: usize) -> bool {
        let v = self.table_view(root);
        &&& v.contains_key(slot)
        &&& view_writes_space(v[slot])
        &&& !self.cap_dead(self.tables.node_of(root, slot))
        &&& v.contains_key(from)
        &&& view_retypes(v[from], child, 3)
        &&& self.list.nodes@[self.tables.node_of(root, from) as int].depth < MAX_DEPTH
        &&& self.link_fits(v[slot].base, va, level, child)
    }

    /// Link's contract over the caller's view: no slot of any table changes, whatever the status. Refused,
    /// with every space's tables as they were, exactly when link_allowed fails; otherwise ok, with the
    /// space the slot names gaining the child in the entry the walk found, as linked says.
    pub open spec fn link_contract(pre: Self, post: Self, root: usize, slot: usize, va: u64, level: u64, from: usize, child: usize, out: Outcome) -> bool {
        &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        &&& {
            ||| {
                &&& !pre.link_allowed(root, slot, va, level, from, child)
                &&& out == status_only(STATUS_REFUSED)
                &&& tree_of(&post.table_pages, &post.spaces) == tree_of(&pre.table_pages, &pre.spaces)
            }
            ||| {
                let s = pre.table_view(root)[slot].base;
                let place = pre.link_parent(s, va, level)->0;
                &&& pre.link_allowed(root, slot, va, level, from, child)
                &&& out == status_only(STATUS_OK)
                &&& linked(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), place.table, place.entry, child, s)
            }
        }
    }

    /// Link's specification implies its contract.
    pub proof fn lemma_link_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::spec_linked(pre, post, root, frame, out),
        ensures
            Self::link_contract(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize, out),
    {
        let slot = frame.slot() as usize;
        let from = frame.argument(3) as usize;
        pre.lemma_table_view(root, slot);
        pre.lemma_table_view(root, from);
        assert(pre.link_allowed(root, slot, frame.argument(1), frame.argument(2), from, frame.argument(4) as usize)
            == pre.allows_link(root, frame));
        assert(post.list == pre.list && post.tables == pre.tables);
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == pre.table_view(t).contains_key(j)
                && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == pre.table_view(t)[j]) by {
                pre.lemma_table_view(t, j);
                post.lemma_table_view(t, j);
            }
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }
}

} // verus!
