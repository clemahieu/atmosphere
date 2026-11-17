// SPDX-License-Identifier: MIT

//! Reading which of up to 64 consecutive entries of one table of a space are present, and which of those
//! are leaves, where a walk stops: a 4K page at level 1, a 2M frame at level 2, or a kernel slot of a
//! process's root. Nothing changes. A process learns this way which parts of its own space are empty,
//! a whole subtree from one absent entry: design/region-map-reads-presence-at-the-first-call/. At most
//! 64 entries are read under the lock: design/one-lock-bounded-steps/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::probe::{lemma_mask_bit_set, lemma_mask_empty, mask_bit};
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::space::*;
use crate::capability::steps::Steps;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
use crate::define::*;

/// The most entries one presence read covers.
pub const PRESENCE_MAX: u64 = 64;

/// presence's bound in the step counter: an entry each. See design/one-lock-bounded-steps/.
pub const PRESENCE_STEPS: usize = PRESENCE_MAX as usize;

/// What a presence read returns: bit i of `present` is set exactly when entry i of the range is
/// present, and bit i of `leaves` exactly when it is present and a walk stops there.
#[derive(Clone, Copy)]
pub struct Presence {
    pub present: u64,
    pub leaves: u64,
}

/// The table at the level, 1 to 4, that path p reaches from root s: the root itself at level 4, and
/// below it the table each entry of p above the level names. None when s is no root or an entry on the
/// way names no table.
pub open spec fn level_table(tree: TableTree, s: usize, p: SpacePath, level: u64) -> Option<usize> {
    if !tree.is_root(s) {
        None
    } else if level >= 4 {
        Some(s)
    } else {
        match step(tree, s, p.l4) {
            None => None,
            Some(t3) => if level == 3 {
                Some(t3)
            } else {
                match step(tree, t3, p.l3) {
                    None => None,
                    Some(t2) => if level == 2 { Some(t2) } else { step(tree, t2, p.l2) },
                }
            },
        }
    }
}

/// The index path p takes in the table at the level.
pub open spec fn level_index(p: SpacePath, level: u64) -> usize {
    if level >= 4 {
        p.l4
    } else if level == 3 {
        p.l3
    } else if level == 2 {
        p.l2
    } else {
        p.l1
    }
}

/// Path q passes through entry i of the table at the level that path p reaches: it takes p's indices
/// above the level and i at it.
pub open spec fn path_under(p: SpacePath, q: SpacePath, level: u64, i: usize) -> bool {
    &&& level >= 4 ==> q.l4 == i
    &&& level < 4 ==> q.l4 == p.l4
    &&& level == 3 ==> q.l3 == i
    &&& level < 3 ==> q.l3 == p.l3
    &&& level == 2 ==> q.l2 == i
    &&& level < 2 ==> q.l2 == p.l2
    &&& level < 2 ==> q.l1 == i
}

/// Entry e of table t is present, and, when `leaf`, a walk stops there: it names no child table.
pub open spec fn entry_set(tree: TableTree, t: usize, e: usize, leaf: bool) -> bool {
    &&& tree.entry(t, e).perm.present
    &&& leaf ==> step(tree, t, e) is None
}

/// The mask of the first n entries from `first` of table t: bit j set exactly when entry first + j is
/// set as entry_set says.
pub open spec fn presence_mask(tree: TableTree, t: usize, first: usize, n: nat, leaf: bool) -> u64
    decreases n,
{
    if n == 0 {
        0
    } else {
        let m = presence_mask(tree, t, first, (n - 1) as nat, leaf);
        if entry_set(tree, t, (first + n - 1) as usize, leaf) {
            m | (1u64 << ((n - 1) as u64))
        } else {
            m
        }
    }
}

/// Bit j of the mask of n entries, n at most 64, is entry first + j's, for j below n, and clear above.
pub proof fn lemma_presence_mask(tree: TableTree, t: usize, first: usize, n: nat, leaf: bool)
    requires
        n <= 64,
    ensures
        forall|j: int| 0 <= j < 64 ==> #[trigger] mask_bit(presence_mask(tree, t, first, n, leaf), j)
            == (j < n && entry_set(tree, t, (first + j) as usize, leaf)),
    decreases n,
{
    if n == 0 {
        lemma_mask_empty();
    } else {
        let m = presence_mask(tree, t, first, (n - 1) as nat, leaf);
        lemma_presence_mask(tree, t, first, (n - 1) as nat, leaf);
        lemma_mask_bit_set(m, (n - 1) as u64);
    }
}

/// An entry absent from the table at the level that path p reaches in space s leaves every path under
/// it unmapped: no path through that entry is in the space's mapping, at any level below it.
pub proof fn lemma_absent_entry_maps_nothing(tree: TableTree, s: usize, p: SpacePath, level: u64, i: usize, q: SpacePath)
    requires
        1 <= level <= 4,
        level_table(tree, s, p, level) is Some,
        !tree.entry(level_table(tree, s, p, level)->0, i).perm.present,
        path_under(p, q, level, i),
    ensures
        walk(tree, s, q) is None,
        !space_mapping(tree, s).contains_key(q),
{
}

/// A present entry of the table at the level that path p reaches in space s, above level 1, that is no
/// leaf names the table at the level below that every path through it reaches.
pub proof fn lemma_present_entry_descends(tree: TableTree, s: usize, p: SpacePath, level: u64, i: usize, q: SpacePath)
    requires
        2 <= level <= 4,
        level_table(tree, s, p, level) is Some,
        entry_set(tree, level_table(tree, s, p, level)->0, i, false),
        !entry_set(tree, level_table(tree, s, p, level)->0, i, true),
        path_under(p, q, level, i),
    ensures
        level_table(tree, s, q, (level - 1) as u64) == step(tree, level_table(tree, s, p, level)->0, i),
        level_table(tree, s, q, (level - 1) as u64) is Some,
{
}

impl CapKernel {
    /// The refusals: an address that names no entry at the level, a count of 0 or over 64, or a range
    /// that leaves its table; an index that names no capability to a process's space, or none that may
    /// change it, or one naming a dead process; a path that reaches no table at the level.
    pub open spec fn can_read_presence(&self, root: usize, slot: usize, va: u64, level: u64, count: u64) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let n = self.tables.node_of(root, slot);
        let p = address_path(va);
        &&& names_entry(va, level)
        &&& 1 <= count <= PRESENCE_MAX
        &&& level_index(p, level) + count <= ENTRIES
        &&& self.tables.has_slot(&self.list, root, slot)
        &&& self.is_cap(n)
        &&& writes_space(self.payload_of(n))
        &&& !self.cap_dead(n)
        &&& self.spaces.records@[self.payload_of(n).base].value().kind == SpaceKind::Process
        &&& level_table(tree, self.payload_of(n).base, p, level) is Some
    }

    /// What a presence read of count entries at the level from the address va, in the space of the
    /// capability at index slot of the table at root, returns: the two masks of the table the path
    /// reaches, when can_read_presence holds, and None otherwise.
    pub open spec fn spec_presence(&self, root: usize, slot: usize, va: u64, level: u64, count: u64) -> Option<Presence> {
        if self.can_read_presence(root, slot, va, level, count) {
            let tree = tree_of(&self.table_pages, &self.spaces);
            let p = address_path(va);
            let t = level_table(tree, self.payload_of(self.tables.node_of(root, slot)).base, p, level)->0;
            let first = level_index(p, level);
            Some(Presence {
                present: presence_mask(tree, t, first, count as nat, false),
                leaves: presence_mask(tree, t, first, count as nat, true),
            })
        } else {
            None
        }
    }

    /// ret is Some exactly when can_read_presence holds, and then bit j of each mask, for j below 64,
    /// says of entry level_index + j of the table at the level what entry_set says, and is clear from
    /// count on. presence's ensures and spec_outcome_carried both call it:
    /// design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn presence_read(&self, root: usize, slot: usize, va: u64, level: u64, count: u64, ret: Option<Presence>) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let p = address_path(va);
        let t = level_table(tree, self.payload_of(self.tables.node_of(root, slot)).base, p, level)->0;
        let first = level_index(p, level);
        &&& ret is Some == self.can_read_presence(root, slot, va, level, count)
        &&& ret is Some ==> forall|j: int| 0 <= j < 64 ==> #[trigger] mask_bit((ret->0).present, j)
            == (j < count && entry_set(tree, t, (first + j) as usize, false))
        &&& ret is Some ==> forall|j: int| 0 <= j < 64 ==> #[trigger] mask_bit((ret->0).leaves, j)
            == (j < count && entry_set(tree, t, (first + j) as usize, true))
    }

    /// spec_presence's answer says what presence_read says of it.
    pub proof fn lemma_presence_read(&self, root: usize, slot: usize, va: u64, level: u64, count: u64)
        ensures
            self.presence_read(root, slot, va, level, count, self.spec_presence(root, slot, va, level, count)),
    {
        if self.can_read_presence(root, slot, va, level, count) {
            let tree = tree_of(&self.table_pages, &self.spaces);
            let p = address_path(va);
            let t = level_table(tree, self.payload_of(self.tables.node_of(root, slot)).base, p, level)->0;
            let first = level_index(p, level);
            lemma_presence_mask(tree, t, first, count as nat, false);
            lemma_presence_mask(tree, t, first, count as nat, true);
        }
    }

    /// Reads which of `count` entries, from the one the address `va` names at `level`, of the table at
    /// that level in the space of the capability at index `slot` of the table at `root`, are present and
    /// which are leaves. All of these come from user space. The kernel is unchanged. See
    /// design/syscall-abi-in-registers/. Each entry is one unit, and a count over PRESENCE_MAX is
    /// refused.
    pub fn presence(&self, root: usize, slot: usize, va: u64, level: u64, count: u64, Tracked(steps): Tracked<&mut Steps>) -> (ret: Option<Presence>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
            self.root_live(root),
        ensures
            final(steps).count <= old(steps).count + PRESENCE_STEPS,
            ret == self.spec_presence(root, slot, va, level, count),
            self.presence_read(root, slot, va, level, count, ret),
            discharges(self.view(), self.view(), root, Effect::Local),
    {
        let ghost tree = tree_of(&self.table_pages, &self.spaces);
        let ghost p = address_path(va);
        proof {
            self.lemma_no_op_discharges(root);
            self.lemma_presence_read(root, slot, va, level, count);
        }
        if !entry_named(va, level) || count == 0 || count > PRESENCE_MAX {
            return None;
        }
        let (l4, l3, l2, l1) = address_indices(va);
        let first = if level == 4 {
            l4
        } else if level == 3 {
            l3
        } else if level == 2 {
            l2
        } else {
            l1
        };
        if first + count as usize > ENTRIES {
            return None;
        }
        let (n, space) = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found,
            None => { return None; },
        };
        proof {
            self.lemma_slot(root, slot);
            assert(space == self.payload_of(n));
        }
        let n_node = self.list.get(n);
        let n_kind = match n_node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !n_node.live || !n_kind || !may_write_space(&space) {
            return None;
        }
        proof {
            assert(self.is_cap(n));
            self.lemma_written_space(n);
            self.lemma_root_table(space.base);
        }
        if self.is_cap_dead(n, space) {
            return None;
        }
        let s = space.base;
        if !same_kind(self.space_kind(s), SpaceKind::Process) {
            return None;
        }
        let mut t = s;
        let mut is_root = true;
        if level <= 3 {
            t = match self.table_step(s, true, l4) {
                Some(u) => u,
                None => { return None; },
            };
            is_root = false;
        }
        if level <= 2 {
            t = match self.table_step(t, false, l3) {
                Some(u) => u,
                None => { return None; },
            };
        }
        if level == 1 {
            t = match self.table_step(t, false, l2) {
                Some(u) => u,
                None => { return None; },
            };
        }
        proof {
            assert(level_table(tree, s, p, level) == Some(t));
            assert(self.can_read_presence(root, slot, va, level, count));
            assert(tree.record(t).level == level);
            assert(is_root == (level == 4));
            assert(is_root ==> tree.is_root(t) && !tree.is_page(t));
            assert(!is_root ==> tree.is_page(t));
        }
        let mut present: u64 = 0;
        let mut leaves: u64 = 0;
        let mut i: u64 = 0;
        let ghost start = steps.count;
        while i < count
            invariant
                self.wf(),
                0 <= i <= count <= PRESENCE_MAX,
                steps.count == start + i,
                first + count <= ENTRIES,
                1 <= level <= 4,
                tree == tree_of(&self.table_pages, &self.spaces),
                is_root ==> self.spaces.roots@.contains_key(t),
                !is_root ==> self.table_pages.maps@.contains_key(t),
                is_root ==> !self.table_pages.maps@.contains_key(t),
                tree.record(t).level == level,
                present == presence_mask(tree, t, first, i as nat, false),
                leaves == presence_mask(tree, t, first, i as nat, true),
            decreases count - i,
        {
            let e = first + i as usize;
            let entry = self.table_entry(t, is_root, e);
            let set = entry.perm.present;
            let leaf = set && (level == 1 || self.table_step(t, is_root, e).is_none());
            proof {
                assert((first + (i + 1) - 1) as usize == e);
                if level == 1 {
                    assert(!tree.child_slot(t, e));
                    assert(step(tree, t, e) is None);
                }
                assert(set == entry_set(tree, t, e, false));
                assert(leaf == entry_set(tree, t, e, true));
            }
            if set {
                present = present | (1u64 << i);
            }
            if leaf {
                leaves = leaves | (1u64 << i);
            }
            i = i + 1;
            proof {
                steps.step();
            }
        }
        proof {
            assert(level_index(p, level) == first);
        }
        Some(Presence { present, leaves })
    }
}

} // verus!
