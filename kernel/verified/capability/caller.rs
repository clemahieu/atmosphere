//! The caller's view: a table as the process it belongs to reads it, slot by slot, so a contract on an
//! operation speaks of the caller's slots and not of the list or the tables. A contract here is proven
//! from the operation's specification in invoked, and a verified user crate carries it as the ensures
//! of the operation's syscall wrapper. See design/theorem-over-reach/ and
//! design/process-holds-capabilities/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arch::Registers;
#[cfg(verus_keep_ghost)]
use crate::capability::block::{Large, NUM_2M};
#[cfg(verus_keep_ghost)]
use crate::define::PAGES_PER_2M;
#[cfg(verus_keep_ghost)]
use crate::capability::derive::*;
#[cfg(verus_keep_ghost)]
use crate::capability::inspect::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::operation::*;
#[cfg(verus_keep_ghost)]
use crate::capability::position::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::retype::FRAME_RIGHTS;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
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

/// What a slot says that holds the frame capability a retype makes of the block of the order at base,
/// under the capability at node parent.
pub open spec fn frame_view(base: usize, order: u8, parent: usize) -> SlotView {
    SlotView { kind: CapKind::Frame, base, order, rights: FRAME_RIGHTS, parent }
}

/// The page at this offset of the block a slot's frame capability names, as frame_of reads it.
pub open spec fn view_frame(v: SlotView, page: usize) -> usize {
    (v.base / 4096 + page) as usize
}

/// A child with these rights and this block narrows a slot's capability, as narrows reads it within one
/// view: rights no wider and a block within its own, and a block narrower than its own only of an
/// untyped or a frame, without control.
pub open spec fn view_narrows(v: SlotView, rights: u32, base: usize, order: u8) -> bool {
    &&& rights & !v.rights == 0
    &&& order <= v.order
    &&& v.base <= base
    &&& base as int % block_bytes(order) == 0
    &&& base as int + block_bytes(order) <= v.base as int + block_bytes(v.order)
    &&& (base != v.base || order != v.order) ==> {
        &&& v.kind is Untyped || v.kind is Frame
        &&& rights & right_bit(Right::Control) == 0
    }
}

/// What a slot says that holds the child a derive makes of the capability a slot's view v says, with
/// these rights and this block, under the capability at node parent.
pub open spec fn derived_view(v: SlotView, rights: u32, base: usize, order: u8, parent: usize) -> SlotView {
    SlotView { kind: v.kind, base, order, rights, parent }
}

/// What a slot says after a move of the capability at node i to node n: a capability derived from the
/// one moved names n as its parent.
pub open spec fn moved_view(v: SlotView, i: usize, n: usize) -> SlotView {
    SlotView { kind: v.kind, base: v.base, order: v.order, rights: v.rights, parent: rename(v.parent, i, n) }
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

    /// A step that leaves the root entries as they were and changes no node's liveness but n's and m's,
    /// slots', leaves every table's slots as they were.
    pub proof fn lemma_slots_stay(pre: Self, post: Self, n: usize, m: usize, t: usize, j: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            post.tables.roots == pre.tables.roots,
            n % 4096 != 0,
            m % 4096 != 0,
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
                    Self::lemma_slots_stay(pre, post, n, n, t, j);
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

    /// A slot a revoke of capability c may take from the table at t, as the kernel reads it beyond any
    /// table's view: the capability in it is in c's run, or the leaf holding it is.
    pub open spec fn revokes_slot(&self, c: usize, t: usize, j: usize) -> bool {
        ||| self.list.in_run(c, self.tables.node_of(t, j))
        ||| self.list.in_run(c, self.tables.leaf(t, index_entry(j)))
    }

    /// Revoke's condition over the caller's view: the position word names a position, the position is
    /// in a table, and the slot there holds a capability. Nothing outside the view decides it.
    pub open spec fn revoke_allowed(&self, root: usize, at: Option<Position>) -> bool {
        let table = self.view_table_at(root, at->0.through);
        &&& at is Some
        &&& table is Some
        &&& self.table_view(table->0).contains_key(at->0.index)
    }

    /// What revoking capability c kept of every table: each slot after was a slot before, saying the
    /// same, and each slot gone is one revokes_slot names.
    pub open spec fn revoke_kept(pre: Self, post: Self, c: usize) -> bool {
        &&& forall|t: usize, j: usize| #[trigger] post.table_view(t).contains_key(j)
            ==> pre.table_view(t).contains_key(j) && post.table_view(t)[j] == pre.table_view(t)[j]
        &&& forall|t: usize, j: usize| #[trigger] pre.table_view(t).contains_key(j) && !post.table_view(t).contains_key(j)
            ==> pre.revokes_slot(c, t, j)
    }

    /// Revoke's contract over the caller's view, for the position word decoded to at: refused, with every
    /// table's view as it was, exactly when revoke_allowed fails. Otherwise the capability c at the
    /// position lost some of its run: only slots revokes_slot names left any table, every other slot
    /// says what it said, and c's own slot stays unless the leaf holding it was in the run. Then refused
    /// with the flush epoch at its limit, again with some of the run left, or ok with c childless.
    /// The epoch and c's run read the kernel outside the view.
    pub open spec fn revoke_contract(pre: Self, post: Self, root: usize, at: Option<Position>, out: Outcome) -> bool {
        ||| {
            &&& !pre.revoke_allowed(root, at)
            &&& out == status_only(STATUS_REFUSED)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            let table = pre.view_table_at(root, at->0.through)->0;
            let i = at->0.index;
            let c = pre.tables.node_of(table, i);
            &&& pre.revoke_allowed(root, at)
            &&& Self::revoke_kept(pre, post, c)
            &&& !pre.list.in_run(c, pre.tables.leaf(table, index_entry(i))) ==> post.table_view(table).contains_key(i)
            &&& {
                ||| out == status_only(STATUS_REFUSED) && post.flush_epoch == usize::MAX
                ||| out == status_only(STATUS_AGAIN) && !post.list.childless(c)
                ||| {
                    &&& out == status_only(STATUS_OK)
                    &&& post.list.childless(c)
                    &&& forall|x: usize| !#[trigger] post.list.is_child(c, x)
                }
            }
        }
    }

    /// Revoke's specification implies its contract.
    pub proof fn lemma_revoke_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::spec_revoked(pre, post, root, frame, out),
        ensures
            Self::revoke_contract(pre, post, root, spec_position(frame.slot()), out),
    {
        let at = spec_position(frame.slot());
        if let Some(a) = at {
            pre.lemma_view_table_at(root, a.through);
            if let Some(table) = pre.table_at(root, a.through) {
                pre.lemma_table_view(table, a.index);
            }
        }
        if pre.allows_revoke(root, frame) {
            let a = at->0;
            let table = pre.table_at(root, a.through)->0;
            let c = pre.cap_at(root, a)->0;
            assert(post.tables == pre.tables);
            assert forall|t: usize, j: usize| #[trigger] post.table_view(t).contains_key(j) || #[trigger] pre.table_view(t).contains_key(j) implies {
                &&& post.table_view(t).contains_key(j) ==> pre.table_view(t).contains_key(j) && post.table_view(t)[j] == pre.table_view(t)[j]
                &&& pre.table_view(t).contains_key(j) && !post.table_view(t).contains_key(j) ==> pre.revokes_slot(c, t, j)
            } by {
                Self::lemma_revoke_slot(pre, post, c, t, j);
            }
            Self::lemma_revoke_slot(pre, post, c, table, a.index);
        }
    }

    /// One slot across a revoke of c: a slot after was a slot before, saying the same, and a slot gone
    /// is one revokes_slot names.
    proof fn lemma_revoke_slot(pre: Self, post: Self, c: usize, t: usize, j: usize)
        requires
            pre.wf(),
            post.tables == pre.tables,
            post.list.parent == pre.list.parent,
            run_shrunk(pre.list, post.list, c),
        ensures
            post.table_view(t).contains_key(j) ==> pre.table_view(t).contains_key(j) && post.table_view(t)[j] == pre.table_view(t)[j],
            pre.table_view(t).contains_key(j) && !post.table_view(t).contains_key(j) ==> pre.revokes_slot(c, t, j),
            pre.tables.has_slot(&pre.list, t, j) && !pre.list.in_run(c, pre.tables.leaf(t, index_entry(j)))
                ==> post.tables.has_slot(&post.list, t, j),
    {
        pre.lemma_table_view(t, j);
        post.lemma_table_view(t, j);
        let leaf = pre.tables.leaf(t, index_entry(j));
        if index_ok(j) && pre.tables.roots@.contains_key(t) && leaf != NO_LEAF {
            assert(0 <= index_entry(j) < ROOT_ENTRIES);
            pre.tables.lemma_entry(t, index_entry(j));
            pre.tables.lemma_leaf(&pre.list, leaf);
            assert(page_of(leaf) == leaf);
            pre.lemma_slot_bound(leaf);
            assert(post.list.nodes@[leaf as int].live ==> pre.list.nodes@[leaf as int].live);
        }
        if pre.tables.has_slot(&pre.list, t, j) {
            pre.lemma_slot(t, j);
            let x = pre.tables.node_of(t, j);
            pre.lemma_slot_bound(x);
            assert(post.list.nodes@[x as int].live ==> pre.list.nodes@[x as int].live
                && post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind);
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

    /// Whether a page can be mapped into the entry the address va and the level name in the space whose
    /// root is s, as the kernel reads it beyond any table's view: at level 1 the walk reaches a live level
    /// 1 table whose entry is empty, and at level 2 a live level 2 table whose entry is empty, the address
    /// naming no level 1 entry below it.
    pub open spec fn map_fits(&self, s: usize, va: u64, level: u64) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let p = address_path(va);
        ||| {
            let t = walk_table(tree, s, p)->0;
            &&& level == 1
            &&& walk_table(tree, s, p) is Some
            &&& !self.blocks.pages@[(t / 4096) as int].dead
            &&& p.l1 < 512
            &&& tree.entry(t, p.l1).is_empty()
        }
        ||| {
            let t = walk_large_table(tree, s, p)->0;
            &&& level == 2
            &&& walk_large_table(tree, s, p) is Some
            &&& !self.blocks.pages@[(t / 4096) as int].dead
            &&& p.l2 < 512
            &&& p.l1 == 0
            &&& tree.entry(t, p.l2).is_empty()
        }
    }

    /// Map's condition over the caller's view, for the space capability at index slot and the frame at
    /// index from of the caller's table at root: the address names an entry at level 1 or 2; the slot
    /// holds a capability that may change its space, naming no dead process and a process's space; the
    /// frame's slot holds a frame capability with the read right whose block holds the page at the
    /// offset, the 2M run of 512 pages from a 512-aligned offset of a 2M or 1G frame at level 2; the
    /// frame's capability is above the deepest depth and the page's block is below the reference limit;
    /// and map_fits holds in that space. The process's liveness, the space's kind, the depth, the block's
    /// count and map_fits read the kernel outside the view.
    pub open spec fn map_allowed(&self, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize) -> bool {
        let v = self.table_view(root);
        &&& names_entry(va, level)
        &&& v.contains_key(slot)
        &&& view_writes_space(v[slot])
        &&& !self.cap_dead(self.tables.node_of(root, slot))
        &&& self.spaces.records@[v[slot].base].value().kind == SpaceKind::Process
        &&& v.contains_key(from)
        &&& v[from].kind is Frame
        &&& v[from].rights & right_bit(Right::Read) != 0
        &&& {
            ||| level == 1 && (page as int) * 4096 < block_bytes(v[from].order)
            ||| {
                &&& level == 2
                &&& v[from].order == 9 || v[from].order == 18
                &&& page % 512 == 0
                &&& (page as int) * 4096 + 512 * 4096 <= block_bytes(v[from].order)
            }
        }
        &&& self.list.nodes@[self.tables.node_of(root, from) as int].depth < MAX_DEPTH
        &&& block_refs(&self.blocks, block_ref(&self.blocks, view_frame(v[from], page))) != usize::MAX
        &&& self.map_fits(v[slot].base, va, level)
    }

    /// Map's contract over the caller's view: no slot of any table changes, whatever the status. Refused,
    /// with every space's tables as they were, exactly when map_allowed fails; otherwise ok, with the
    /// space the slot names gaining, at the path the address names, the entry that maps the frame's page
    /// with the frame's rights, large at level 2, and every other space's mappings as they were.
    pub open spec fn map_contract(pre: Self, post: Self, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize, out: Outcome) -> bool {
        &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        &&& {
            ||| {
                &&& !pre.map_allowed(root, slot, va, level, from, page)
                &&& out == status_only(STATUS_REFUSED)
                &&& tree_of(&post.table_pages, &post.spaces) == tree_of(&pre.table_pages, &pre.spaces)
            }
            ||| {
                let v = pre.table_view(root);
                let s = v[slot].base;
                let a = tree_of(&pre.table_pages, &pre.spaces);
                let b = tree_of(&post.table_pages, &post.spaces);
                &&& pre.map_allowed(root, slot, va, level, from, page)
                &&& out == status_only(STATUS_OK)
                &&& space_mapping(b, s) == space_mapping(a, s).insert(address_path(va), frame_map_entry(view_frame(v[from], page), v[from].rights, level == 2))
                &&& forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r)
            }
        }
    }

    /// Map's specification implies its contract.
    pub proof fn lemma_map_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::spec_mapped(pre, post, root, frame, out),
        ensures
            Self::map_contract(pre, post, root, frame.slot() as usize, frame.argument(1), frame.argument(2), frame.argument(3) as usize, frame.argument(4) as usize, out),
    {
        let slot = frame.slot() as usize;
        let from = frame.argument(3) as usize;
        let va = frame.argument(1);
        let level = frame.argument(2);
        let page = frame.argument(4) as usize;
        pre.lemma_table_view(root, slot);
        pre.lemma_table_view(root, from);
        assert(pre.map_allowed(root, slot, va, level, from, page) == pre.allows_map(root, frame));
        if out == status_only(STATUS_OK) {
            let tree = tree_of(&pre.table_pages, &pre.spaces);
            let s = pre.payload_of(pre.tables.node_of(root, slot)).base;
            let f = pre.tables.node_of(root, from);
            let p = address_path(va);
            if level == 1 {
                pre.lemma_walk_table_facts(s, p);
                let t = walk_table(tree, s, p)->0;
                pre.lemma_map_node_place(t, p.l1);
                Self::lemma_map_slots(pre, post, mapping_node(t, p.l1), f);
            } else {
                let t3 = step(tree, s, p.l4)->0;
                pre.lemma_child_facts(s, p.l4);
                pre.lemma_child_facts(t3, p.l3);
                let t = walk_large_table(tree, s, p)->0;
                pre.lemma_map_node_place(t, p.l2);
                Self::lemma_map_slots(pre, post, mapping_node(t, p.l2), f);
            }
        }
    }

    /// A step that leaves the tables as they were and changes no node's liveness, kind or parent but
    /// node's, which no table's leaf holds, leaves every table's view as it was.
    pub proof fn lemma_map_slots(pre: Self, post: Self, node: usize, f: usize)
        requires
            pre.wf(),
            post.tables == pre.tables,
            !pre.tables.owner@.contains_key(page_of(node)),
            post.list.parent@ == pre.list.parent@.insert(node, f),
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
                &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
                &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            },
        ensures
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
    {
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == pre.table_view(t).contains_key(j)
                && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == pre.table_view(t)[j]) by {
                pre.lemma_table_view(t, j);
                post.lemma_table_view(t, j);
                let leaf = pre.tables.leaf(t, index_entry(j));
                if index_ok(j) && pre.tables.roots@.contains_key(t) && leaf != NO_LEAF {
                    assert(0 <= index_entry(j) < ROOT_ENTRIES);
                    pre.tables.lemma_entry(t, index_entry(j));
                    pre.tables.lemma_leaf(&pre.list, leaf);
                    assert(page_of(leaf) == leaf);
                    pre.lemma_slot_bound(leaf);
                    assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
                }
                if pre.tables.has_slot(&pre.list, t, j) {
                    pre.lemma_slot(t, j);
                    let x = pre.tables.node_of(t, j);
                    pre.lemma_slot_bound(x);
                    assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
                    assert(post.list.parent@[x] == pre.list.parent@[x]);
                }
            }
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }

    /// Inspect's condition over the caller's view: the position word names a position, the position is
    /// in a table, and the slot there holds a capability. Nothing outside the view decides it.
    pub open spec fn inspect_allowed(&self, root: usize, at: Option<Position>) -> bool {
        let table = self.view_table_at(root, at->0.through);
        &&& at is Some
        &&& table is Some
        &&& self.table_view(table->0).contains_key(at->0.index)
    }

    /// Inspect's contract over the caller's view, for the position word decoded to at: no slot of any
    /// table changes, whatever the status. Refused exactly when inspect_allowed fails; otherwise ok, with
    /// the kind's number, the base, the order and the rights the slot's view says in results 1 to 4.
    pub open spec fn inspect_contract(pre: Self, post: Self, root: usize, at: Option<Position>, out: Outcome) -> bool {
        &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        &&& {
            ||| {
                &&& !pre.inspect_allowed(root, at)
                &&& out == status_only(STATUS_REFUSED)
            }
            ||| {
                let v = pre.table_view(pre.view_table_at(root, at->0.through)->0)[at->0.index];
                &&& pre.inspect_allowed(root, at)
                &&& out == Outcome {
                    status: STATUS_OK,
                    result_1: spec_kind_number(v.kind),
                    result_2: v.base as u64,
                    result_3: v.order as u64,
                    result_4: v.rights as u64,
                }
            }
        }
    }

    /// Inspect's arm of invoked implies its contract.
    pub proof fn lemma_inspect_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            spec_operation(frame.operation_number()) == Some(Operation::Inspect),
            Self::invoked(pre, post, root, frame, out),
        ensures
            Self::inspect_contract(pre, post, root, spec_position(frame.slot()), out),
    {
    }

    /// A step that leaves the list and the tables as they were leaves every table's view as it was.
    pub proof fn lemma_views_same(pre: Self, post: Self)
        requires
            post.list == pre.list,
            post.tables == pre.tables,
        ensures
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
    {
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == pre.table_view(t).contains_key(j)
                && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == pre.table_view(t)[j]) by {
                pre.lemma_table_view(t, j);
                post.lemma_table_view(t, j);
            }
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }

    /// The slot at index i of the table at root is empty, as the kernel reads it outside the view: a
    /// slot whose node holds nothing.
    pub open spec fn empty_slot(&self, root: usize, i: usize) -> bool {
        &&& self.tables.has_slot(&self.list, root, i)
        &&& !self.list.nodes@[self.tables.node_of(root, i) as int].live
    }

    /// The small block of the order at base is free among the pages the block table tracks, as the
    /// kernel reads it outside the view.
    pub open spec fn small_block_free(&self, base: usize, order: usize) -> bool {
        &&& self.blocks.tracks_addr_run(base, crate::capability::block::order_pages(order))
        &&& self.blocks.small_free((base / 4096) as int, order)
    }

    /// The 2M block at base is in a region the block table has, and is free or is the one an earlier
    /// step of this retype typed and is zeroing, as the kernel reads it outside the view.
    pub open spec fn large_block_ready(&self, base: usize) -> bool {
        let r = base / 4096 / crate::capability::zero::level_pages(Large::Two);
        &&& base / 4096 / PAGES_PER_2M < NUM_2M
        &&& self.zeroing.active(Large::Two, r) || self.blocks.large_free(Large::Two, r as int)
    }

    /// A retype's condition on its untyped over the caller's view: index from of the table at root is a
    /// slot whose capability may retype the block of the order at base, above the deepest depth. The
    /// depth reads the kernel outside the view.
    pub open spec fn retype_under_allowed(&self, root: usize, from: usize, base: usize, order: u8) -> bool {
        let v = self.table_view(root);
        &&& v.contains_key(from)
        &&& view_retypes(v[from], base, order)
        &&& self.list.nodes@[self.tables.node_of(root, from) as int].depth < MAX_DEPTH
    }

    /// The root entry a leaf's retype fills, over the caller's view: the position is in the caller's
    /// table or in one a process capability with control names, naming no dead process; its index is
    /// a root entry; and that entry holds no leaf. The process's liveness and the entry read the kernel
    /// outside the view.
    pub open spec fn leaf_entry_free(&self, root: usize, at: Position) -> bool {
        let table = self.view_table_at(root, at.through);
        &&& table is Some
        &&& at.through is Some ==> !self.cap_dead(self.tables.node_of(root, at.through->0))
        &&& at.index < ROOT_ENTRIES
        &&& self.tables.leaf(table->0, at.index as int) == NO_LEAF
    }

    /// Retype's condition over the caller's view, by the kind, for the untyped at index from of the
    /// caller's table at root, the base, the word in argument 3 and the level: a 4K frame needs the
    /// untyped to cover the page, the caller's slot the word names empty and the page free; a 2M frame
    /// the same of its block, which is free or being zeroed by this retype; a table page needs its
    /// order-3 block covered and free and a level a table page has; a leaf needs the word to name a
    /// position whose root entry is free, its order-1 block covered and free, and a base that is not
    /// zero. Every other kind is refused.
    pub open spec fn retype_allowed(&self, root: usize, kind: u64, from: usize, base: usize, word: u64, level: usize) -> bool {
        let at = spec_position(word);
        ||| {
            &&& kind == RETYPE_FRAME
            &&& self.retype_under_allowed(root, from, base, 0)
            &&& self.empty_slot(root, word as usize)
            &&& self.small_block_free(base, 0)
        }
        ||| {
            &&& kind == RETYPE_LARGE_FRAME
            &&& self.retype_under_allowed(root, from, base, 9)
            &&& self.empty_slot(root, word as usize)
            &&& self.large_block_ready(base)
        }
        ||| {
            &&& kind == RETYPE_TABLE_PAGE
            &&& self.retype_under_allowed(root, from, base, 3)
            &&& 1 <= level <= 3
            &&& self.small_block_free(base, 3)
        }
        ||| {
            &&& kind == RETYPE_LEAF
            &&& at is Some
            &&& self.retype_under_allowed(root, from, base, 1)
            &&& self.leaf_entry_free(root, at->0)
            &&& base != NO_LEAF
            &&& self.small_block_free(base, 1)
        }
    }

    /// Retype's contract over the caller's view. Refused, with every table's view as it was, exactly
    /// when retype_allowed fails. A 4K frame: ok, with the caller's slot the word names now holding
    /// the frame, the untyped's child, and every other slot of every table as it was. A 2M frame:
    /// again, with every table's view as it was, or ok as a 4K frame is with the 2M block. A table
    /// page: ok, with every table's view as it was and an empty table page of the level at base. A
    /// leaf: ok, with every table's view as it was and every index of the root entry it fills an empty
    /// slot of the position's table.
    pub open spec fn retype_contract(pre: Self, post: Self, root: usize, kind: u64, from: usize, base: usize, word: u64, level: usize, out: Outcome) -> bool {
        let allowed = pre.retype_allowed(root, kind, from, base, word, level);
        let to = word as usize;
        let parent = pre.tables.node_of(root, from);
        let at = spec_position(word)->0;
        ||| {
            &&& !allowed
            &&& out == status_only(STATUS_REFUSED)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            &&& kind == RETYPE_FRAME
            &&& allowed
            &&& out == status_only(STATUS_OK)
            &&& post.table_view(root) == pre.table_view(root).insert(to, frame_view(base, 0, parent))
            &&& forall|t: usize| t != root ==> #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            &&& kind == RETYPE_LARGE_FRAME
            &&& allowed
            &&& out == status_only(STATUS_AGAIN)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            &&& kind == RETYPE_LARGE_FRAME
            &&& allowed
            &&& out == status_only(STATUS_OK)
            &&& post.table_view(root) == pre.table_view(root).insert(to, frame_view(base, 9, parent))
            &&& forall|t: usize| t != root ==> #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            &&& kind == RETYPE_TABLE_PAGE
            &&& allowed
            &&& out == status_only(STATUS_OK)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
            &&& post.table_pages.maps@.contains_key(base)
            &&& post.table_pages.records@[base].value() == fresh_table(level)
        }
        ||| {
            let table = pre.view_table_at(root, at.through)->0;
            &&& kind == RETYPE_LEAF
            &&& allowed
            &&& out == status_only(STATUS_OK)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
            &&& forall|i: usize| index_ok(i) && index_entry(i) == at.index as int ==> #[trigger] post.empty_slot(table, i)
        }
    }

    /// A step that fills the empty slot at index to of the table at root with a capability, saying v
    /// there, and changes no other node's liveness, kind, capability or parent and no root entry, adds
    /// that slot to the table's view and leaves every other slot of every table as it was.
    pub proof fn lemma_slot_added(pre: Self, post: Self, root: usize, to: usize, v: SlotView)
        requires
            pre.wf(),
            pre.empty_slot(root, to),
            Self::caps_frame(pre, post, pre.tables.node_of(root, to), pre.tables.node_of(root, to)),
            post.tables.roots == pre.tables.roots,
            forall|x: usize| x != pre.tables.node_of(root, to) ==> #[trigger] post.list.parent@[x] == pre.list.parent@[x],
            post.is_cap(pre.tables.node_of(root, to)),
            post.slot_view(root, to) == v,
        ensures
            post.table_view(root) == pre.table_view(root).insert(to, v),
            forall|t: usize| t != root ==> #[trigger] post.table_view(t) == pre.table_view(t),
    {
        let n = pre.tables.node_of(root, to);
        pre.lemma_slot(root, to);
        assert forall|t: usize| #[trigger] post.table_view(t) == if t == root { pre.table_view(t).insert(to, v) } else { pre.table_view(t) } by {
            assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == (if t == root { pre.table_view(t).insert(to, v) } else { pre.table_view(t) }).contains_key(j)
                && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == (if t == root { pre.table_view(t).insert(to, v) } else { pre.table_view(t) })[j]) by {
                pre.lemma_table_view(t, j);
                post.lemma_table_view(t, j);
                Self::lemma_slots_stay(pre, post, n, n, t, j);
                if pre.tables.has_slot(&pre.list, t, j) {
                    pre.lemma_slot(t, j);
                    let m = pre.tables.node_of(t, j);
                    pre.lemma_slot_bound(m);
                    if m == n {
                        pre.tables.lemma_entry(t, index_entry(j));
                        pre.tables.lemma_entry(root, index_entry(to));
                        lemma_index_parts(j, to);
                    } else {
                        Self::lemma_caps_frame(pre, post, n, n, m);
                    }
                }
            }
            assert(post.table_view(t) =~= if t == root { pre.table_view(t).insert(to, v) } else { pre.table_view(t) });
        }
    }

    /// A step that leaves the tables as they were, changes no node's liveness and no node's parent but
    /// the one at base, which was not live and is no leaf, and keeps every capability a capability and
    /// every other node none, leaves every table's view as it was.
    pub proof fn lemma_unslotted_node(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            post.tables == pre.tables,
            !pre.list.nodes@[base as int].live,
            !pre.tables.owner@.contains_key(base),
            forall|x: usize| x != base ==> #[trigger] post.list.parent@[x] == pre.list.parent@[x],
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base
                ==> post.list.nodes@[i].live == pre.list.nodes@[i].live,
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
        ensures
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
    {
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == pre.table_view(t).contains_key(j)
                && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == pre.table_view(t)[j]) by {
                pre.lemma_table_view(t, j);
                post.lemma_table_view(t, j);
                let leaf = pre.tables.leaf(t, index_entry(j));
                if index_ok(j) && pre.tables.roots@.contains_key(t) && leaf != NO_LEAF {
                    assert(0 <= index_entry(j) < ROOT_ENTRIES);
                    pre.tables.lemma_entry(t, index_entry(j));
                    pre.tables.lemma_leaf(&pre.list, leaf);
                    assert(page_of(leaf) == leaf);
                    pre.lemma_slot_bound(leaf);
                    assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
                }
                let x = pre.tables.node_of(t, j);
                if pre.is_cap(x) {
                    assert(x != base);
                }
            }
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }

    /// A leaf's retype leaves every table's view as it was: the slots it adds hold nothing, and every
    /// slot outside its root entry is the slot it was, of the node it was, saying what it said.
    pub proof fn lemma_leaf_views(pre: Self, post: Self, root: usize, from: usize, at: Position, base: usize)
        requires
            pre.wf(),
            Self::leaf_retyped(pre, post, root, from, at, base),
        ensures
            forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t),
    {
        let table = pre.destination_at(root, at.through)->0;
        assert(pre.blocks.pages@[(base / 4096) as int + 0].kind is Free);
        assert forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t) by {
            assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == pre.table_view(t).contains_key(j)
                && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == pre.table_view(t)[j]) by {
                pre.lemma_table_view(t, j);
                post.lemma_table_view(t, j);
                let e = index_entry(j);
                if pre.tables.has_slot(&pre.list, t, j) {
                    let x = pre.tables.node_of(t, j);
                    assert(post.tables.has_slot(&post.list, t, j));
                    if pre.is_cap(x) {
                        assert(post.is_cap(x));
                        assert(x != base);
                    }
                } else if post.tables.has_slot(&post.list, t, j) {
                    assert(pre.tables.roots@.contains_key(t));
                    assert(0 <= e < ROOT_ENTRIES);
                    if t != table || e != at.index as int {
                        let leaf = pre.tables.leaf(t, e);
                        assert(post.tables.leaf(t, e) == leaf);
                        pre.tables.lemma_entry(t, e);
                        assert(pre.blocks.pages@[(leaf / 4096) as int].kind is Base);
                        assert(leaf != base);
                        pre.tables.lemma_leaf(&pre.list, leaf);
                        assert(page_of(leaf) == leaf);
                        pre.lemma_slot_bound(leaf);
                        assert(false);
                    }
                }
            }
            assert(post.table_view(t) =~= pre.table_view(t));
        }
    }

    /// Retype's specification implies its contract.
    pub proof fn lemma_retype_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::spec_retyped(pre, post, root, frame, out),
        ensures
            Self::retype_contract(pre, post, root, frame.argument(1), frame.slot() as usize, frame.argument(2) as usize, frame.argument(3), frame.argument(4) as usize, out),
    {
        let kind = frame.argument(1);
        let from = frame.slot() as usize;
        let base = frame.argument(2) as usize;
        let word = frame.argument(3);
        let to = word as usize;
        let level = frame.argument(4) as usize;
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        pre.lemma_table_view(root, from);
        if let Some(at) = spec_position(word) {
            pre.lemma_view_table_at(root, at.through);
            if let Some(c) = at.through {
                pre.lemma_table_view(root, c);
            }
        }
        assert(pre.retype_allowed(root, kind, from, base, word, level) == pre.allows_retype(root, frame));
        if out == status_only(STATUS_REFUSED) {
            Self::lemma_views_same(pre, post);
        } else if kind == RETYPE_FRAME {
            assert(post.is_cap(child));
            assert(post.slot_view(root, to) == frame_view(base, 0, parent));
            Self::lemma_slot_added(pre, post, root, to, frame_view(base, 0, parent));
        } else if kind == RETYPE_LARGE_FRAME && out == status_only(STATUS_AGAIN) {
            Self::lemma_views_same(pre, post);
        } else if kind == RETYPE_LARGE_FRAME {
            assert(post.is_cap(child));
            assert(post.slot_view(root, to) == frame_view(base, 9, parent));
            Self::lemma_slot_added(pre, post, root, to, frame_view(base, 9, parent));
        } else if kind == RETYPE_TABLE_PAGE {
            if pre.tables.owner@.contains_key(base) {
                assert(pre.blocks.pages@[(base / 4096) as int].kind is Base);
            }
            Self::lemma_unslotted_node(pre, post, base);
        } else {
            let at = spec_position(word)->0;
            Self::lemma_leaf_views(pre, post, root, from, at, base);
            let table = pre.view_table_at(root, at.through)->0;
            assert(table == pre.destination_at(root, at.through)->0);
            assert forall|i: usize| index_ok(i) && index_entry(i) == at.index as int implies #[trigger] post.empty_slot(table, i) by {}
        }
    }

    /// Derive's condition over the caller's view, for the source position from, the destination position
    /// to, the rights, the base and the order: the rights fit 32 bits and the order 8; the source is a
    /// slot of the caller's own table holding a capability that is not a device's and that the child
    /// narrows; the destination is in a table, through a process capability with control naming no dead
    /// process when it goes through one, and its slot is empty; and the source's capability names no dead
    /// process or thread, is above the deepest depth and, for a kind whose block counts its references,
    /// names a block below the reference limit. The destination's emptiness, the process's and the
    /// source's liveness, the depth and the block's count read the kernel outside the view.
    pub open spec fn derive_allowed(&self, root: usize, from: Option<Position>, to: Option<Position>, rights: u64, base: usize, order: u64) -> bool {
        let v = self.table_view(root);
        let i = from->0.index;
        let n = self.tables.node_of(root, i);
        let table = self.view_table_at(root, to->0.through);
        &&& rights <= u32::MAX as u64
        &&& order <= u8::MAX as u64
        &&& from is Some
        &&& from->0.through is None
        &&& to is Some
        &&& table is Some
        &&& to->0.through is Some ==> !self.processes.records@[table->0].value().dead
        &&& self.empty_slot(table->0, to->0.index)
        &&& v.contains_key(i)
        &&& !(v[i].kind is Device)
        &&& view_narrows(v[i], rights as u32, base, order as u8)
        &&& !self.cap_dead(n)
        &&& self.list.nodes@[n as int].depth < MAX_DEPTH
        &&& (v[i].kind is Frame || v[i].kind is Space || v[i].kind is Thread || v[i].kind is Process)
            ==> block_refs(&self.blocks, block_ref(&self.blocks, v[i].base / 4096)) != usize::MAX
    }

    /// Derive's condition over the caller's view is the one allows_derive reads.
    pub proof fn lemma_derive_allowed(&self, root: usize, frame: Registers)
        ensures
            self.derive_allowed(root, spec_position(frame.slot()), spec_position(frame.argument(1)), frame.argument(2), frame.argument(3) as usize, frame.argument(4))
                == self.allows_derive(root, frame),
    {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        let rights = frame.argument(2) as u32;
        let base = frame.argument(3) as usize;
        let order = frame.argument(4) as u8;
        if let Some(f) = from {
            self.lemma_table_view(root, f.index);
            if self.holds_slot(root, f.index) {
                let p = self.payload_of(self.tables.node_of(root, f.index));
                assert(view_narrows(self.table_view(root)[f.index], rights, base, order) == narrows(child_of(p, rights, base, order), p));
            }
        }
        if let Some(t) = to {
            self.lemma_view_table_at(root, t.through);
        }
    }

    /// Derive's contract over the caller's view. Refused, with every table's view as it was, exactly
    /// when derive_allowed fails; otherwise ok, with the destination's slot now holding the source's
    /// child, of the source's kind with the rights and the block the arguments give, and every other
    /// slot of every table as it was, the source's included.
    pub open spec fn derive_contract(pre: Self, post: Self, root: usize, from: Option<Position>, to: Option<Position>, rights: u64, base: usize, order: u64, out: Outcome) -> bool {
        ||| {
            &&& !pre.derive_allowed(root, from, to, rights, base, order)
            &&& out == status_only(STATUS_REFUSED)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            let i = from->0.index;
            let table = pre.view_table_at(root, to->0.through)->0;
            let child = derived_view(pre.table_view(root)[i], rights as u32, base, order as u8, pre.tables.node_of(root, i));
            &&& pre.derive_allowed(root, from, to, rights, base, order)
            &&& out == status_only(STATUS_OK)
            &&& post.table_view(table) == pre.table_view(table).insert(to->0.index, child)
            &&& forall|t: usize| t != table ==> #[trigger] post.table_view(t) == pre.table_view(t)
        }
    }

    /// Derive's specification implies its contract.
    pub proof fn lemma_derive_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::spec_derived(pre, post, root, frame, out),
        ensures
            Self::derive_contract(pre, post, root, spec_position(frame.slot()), spec_position(frame.argument(1)), frame.argument(2), frame.argument(3) as usize, frame.argument(4), out),
    {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        let rights = frame.argument(2) as u32;
        let base = frame.argument(3) as usize;
        let order = frame.argument(4) as u8;
        pre.lemma_derive_allowed(root, frame);
        if let Some(f) = from {
            pre.lemma_table_view(root, f.index);
        }
        if let Some(t) = to {
            pre.lemma_view_table_at(root, t.through);
        }
        if out == status_only(STATUS_REFUSED) {
            Self::lemma_views_same(pre, post);
        } else {
            let i = from->0.index;
            let table = pre.table_at(root, to->0.through)->0;
            let child = pre.tables.node_of(table, to->0.index);
            let v = derived_view(pre.table_view(root)[i], rights, base, order, pre.tables.node_of(root, i));
            assert(post.is_cap(child));
            assert(post.slot_view(table, to->0.index) == v);
            Self::lemma_slot_added(pre, post, table, to->0.index, v);
        }
    }

    /// A capability in a slot has a live parent other than itself.
    pub proof fn lemma_slot_parent(&self, x: usize)
        requires
            self.wf(),
            self.is_cap(x),
        ensures
            self.list.parent@.contains_key(x),
            self.list.parent@[x] != x,
            self.list.parent@[x] < NODE_SPACE,
            self.list.nodes@[self.list.parent@[x] as int].live,
    {
        self.lemma_leaf_node_not_first(x);
        self.lemma_slot_bound(x);
        let s = self.list.seq@;
        lemma_has(s, x);
        let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
        assert(k != 0);
        self.list.lemma_parent_live(x);
    }

    /// Move's condition over the caller's view, for the source position from and the destination
    /// position to: each word names a position; the source is in a table and its slot holds a
    /// capability; the destination is in a table, through a process capability with control naming no
    /// dead process when it goes through one, and its slot is empty; and a source in the caller's own
    /// table names no dead process or thread, while one in a controlled table is taken whatever it
    /// names. The process's liveness, the destination's emptiness and the source's liveness read the
    /// kernel outside the view.
    pub open spec fn move_allowed(&self, root: usize, from: Option<Position>, to: Option<Position>) -> bool {
        let src = self.view_table_at(root, from->0.through);
        let dst = self.view_table_at(root, to->0.through);
        &&& from is Some
        &&& to is Some
        &&& src is Some
        &&& dst is Some
        &&& to->0.through is Some ==> !self.processes.records@[dst->0].value().dead
        &&& self.table_view(src->0).contains_key(from->0.index)
        &&& self.empty_slot(dst->0, to->0.index)
        &&& from->0.through is None ==> !self.cap_dead(self.tables.node_of(root, from->0.index))
    }

    /// The view of the table at t after a move of the capability at index from of the table at src to
    /// the empty index to of the table at dst: the source's slot gone, the destination's saying what the
    /// source's said, and every other slot saying what it said, a capability derived from the one moved
    /// naming the destination's node as its parent.
    pub open spec fn moved_table_view(&self, src: usize, from: usize, dst: usize, to: usize, t: usize) -> Map<usize, SlotView> {
        let i = self.tables.node_of(src, from);
        let n = self.tables.node_of(dst, to);
        let kept = if t == src { self.table_view(t).dom().remove(from) } else { self.table_view(t).dom() };
        Map::new(
            if t == dst { kept.insert(to) } else { kept },
            |j: usize| if t == dst && j == to { self.table_view(src)[from] } else { moved_view(self.table_view(t)[j], i, n) },
        )
    }

    /// Move's contract over the caller's view, for the source position from and the destination
    /// position to. Refused, with every table's view as it was, exactly when move_allowed fails;
    /// otherwise ok, with every table's view as moved_table_view says: the capability gone from the
    /// source's slot and in the destination's, and every other slot of every table as it was but for
    /// the parent its children name.
    pub open spec fn move_contract(pre: Self, post: Self, root: usize, from: Option<Position>, to: Option<Position>, out: Outcome) -> bool {
        ||| {
            &&& !pre.move_allowed(root, from, to)
            &&& out == status_only(STATUS_REFUSED)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.table_view(t)
        }
        ||| {
            let src = pre.view_table_at(root, from->0.through)->0;
            let dst = pre.view_table_at(root, to->0.through)->0;
            &&& pre.move_allowed(root, from, to)
            &&& out == status_only(STATUS_OK)
            &&& forall|t: usize| #[trigger] post.table_view(t) == pre.moved_table_view(src, from->0.index, dst, to->0.index, t)
        }
    }

    /// Move's condition over the caller's view is the one allows_move reads.
    pub proof fn lemma_move_allowed(&self, root: usize, frame: Registers)
        ensures
            self.move_allowed(root, spec_position(frame.slot()), spec_position(frame.argument(1))) == self.allows_move(root, frame),
    {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        if let Some(f) = from {
            self.lemma_view_table_at(root, f.through);
            if let Some(src) = self.table_at(root, f.through) {
                self.lemma_table_view(src, f.index);
            }
        }
        if let Some(t) = to {
            self.lemma_view_table_at(root, t.through);
        }
    }

    /// Move's specification implies its contract.
    pub proof fn lemma_move_contract(pre: Self, post: Self, root: usize, frame: Registers, out: Outcome)
        requires
            pre.wf(),
            Self::spec_moved(pre, post, root, frame, out),
        ensures
            Self::move_contract(pre, post, root, spec_position(frame.slot()), spec_position(frame.argument(1)), out),
    {
        let from = spec_position(frame.slot());
        let to = spec_position(frame.argument(1));
        pre.lemma_move_allowed(root, frame);
        if out == status_only(STATUS_REFUSED) {
            Self::lemma_views_same(pre, post);
        } else {
            broadcast use vstd::map::lemma_map_new_domain, vstd::map::lemma_map_new_index;
            let f = from->0;
            let d = to->0;
            pre.lemma_view_table_at(root, f.through);
            pre.lemma_view_table_at(root, d.through);
            let src = pre.table_at(root, f.through)->0;
            let dst = pre.table_at(root, d.through)->0;
            let i = pre.tables.node_of(src, f.index);
            let n = pre.tables.node_of(dst, d.index);
            pre.lemma_table_view(src, f.index);
            pre.lemma_slot(src, f.index);
            pre.lemma_slot(dst, d.index);
            pre.lemma_slot_parent(i);
            assert(post.is_cap(n));
            assert(i != n);
            assert(post.list.parent@[n] == pre.list.parent@[i]);
            assert forall|t: usize| #[trigger] post.table_view(t) == pre.moved_table_view(src, f.index, dst, d.index, t) by {
                let want = pre.moved_table_view(src, f.index, dst, d.index, t);
                assert forall|j: usize| #[trigger] post.table_view(t).contains_key(j) == want.contains_key(j)
                    && (post.table_view(t).contains_key(j) ==> post.table_view(t)[j] == want[j]) by {
                    pre.lemma_table_view(t, j);
                    post.lemma_table_view(t, j);
                    Self::lemma_slots_stay(pre, post, i, n, t, j);
                    if pre.tables.has_slot(&pre.list, t, j) {
                        pre.lemma_slot(t, j);
                        let m = pre.tables.node_of(t, j);
                        pre.lemma_slot_bound(m);
                        if m == i {
                            pre.tables.lemma_entry(t, index_entry(j));
                            pre.tables.lemma_entry(src, index_entry(f.index));
                            lemma_index_parts(j, f.index);
                        } else if m == n {
                            pre.tables.lemma_entry(t, index_entry(j));
                            pre.tables.lemma_entry(dst, index_entry(d.index));
                            lemma_index_parts(j, d.index);
                        } else {
                            Self::lemma_caps_frame(pre, post, i, n, m);
                            if pre.is_cap(m) {
                                pre.lemma_slot_parent(m);
                                assert(post.list.parent@[m] == rename(pre.list.parent@[m], i, n));
                            }
                        }
                    }
                }
                assert(post.table_view(t) =~= want);
            }
        }
    }
}

} // verus!
