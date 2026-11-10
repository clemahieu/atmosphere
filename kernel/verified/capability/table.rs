//! A process's capability table: a root of 512 pointers and leaves retyped on demand. A leaf is two
//! pages, an order-1 block: a node page holding the slots' list nodes, and a payload page holding what
//! each capability says at the same index. Node 0 of a leaf is its hidden node, so a leaf has 127 slots.
//! No capability names a table, so tables cannot form cycles. See design/process-holds-capabilities/.
//!
//! A table is named by its root's address, which is its process's base: the root is the first page of
//! the process object.
//!
//! The two parts of the invariant are opaque and reached through one-position lemmas: spelled out,
//! the root clause names every entry of every root the prover has seen, and the leaf clause chains
//! back through `owner` to the root clause again.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::define::*;
use crate::pptr::*;

pub const ROOT_ENTRIES: usize = 512;
/// Indices run over root entries and node positions, of which position 0 in a leaf is no slot.
pub const TABLE_INDICES: usize = 65536;
/// What a root entry holds when it has no leaf. A leaf is never at address zero.
pub const NO_LEAF: usize = 0;

#[derive(Clone, Copy)]
pub enum CapKind {
    Untyped,
    Frame,
    Process,
    Thread,
    Endpoint,
    Reply,
    Notification,
    Space,
    Device,
    Console,
    Power,
}

/// What a capability says, beyond its place in the list. 32 bytes.
#[derive(Clone, Copy)]
pub struct Payload {
    pub kind: CapKind,
    pub order: u8,
    pub rights: u32,
    pub base: usize,
    pub badge: usize,
    pub reserved: usize,
}

pub struct PayloadPage {
    pub entries: Array<Payload, NODES_PER_PAGE>,
}

pub struct TableRoot {
    pub leaves: Array<usize, ROOT_ENTRIES>,
}

/// The largest block a capability can name: 2^36 pages reach the end of the 48-bit space.
pub const MAX_ORDER: u8 = 36;

/// A block of this order, in bytes.
pub open spec fn block_bytes(order: u8) -> int {
    pow2(order as nat) as int * 4096
}

/// What a memory capability says names a block: base aligned to its size, inside the address space.
/// See design/capability-names-a-block/.
pub open spec fn payload_wf(p: Payload) -> bool {
    &&& p.order <= MAX_ORDER
    &&& p.base as int % block_bytes(p.order) == 0
    &&& p.base as int + block_bytes(p.order) <= NODE_SPACE as int
}

/// A capability of this kind names a block of memory. A device's, the console's and power's name
/// objects above the 48-bit space instead: a device's its device, devices_wf, the console's
/// CONSOLE_OBJECT and power's POWER_OBJECT.
pub open spec fn names_block(k: CapKind) -> bool {
    !(k is Device) && !(k is Console) && !(k is Power)
}

/// A capability of this kind is a holder some record counts: a frame's in its block's holders, and a
/// space's, thread's or process's in that object's. Any other kind's capability can come and go
/// without a record changing.
pub open spec fn tracked_kind(k: CapKind) -> bool {
    k is Frame || k is Space || k is Thread || k is Process
}

pub fn is_block_kind(k: CapKind) -> (ret: bool)
    ensures
        ret == names_block(k),
{
    match k {
        CapKind::Device | CapKind::Console | CapKind::Power => false,
        _ => true,
    }
}

/// What a capability says is well formed: a block for a memory capability, the console's one page for
/// a console's, and power's one page for a power capability's.
pub open spec fn cap_wf(p: Payload) -> bool {
    &&& names_block(p.kind) ==> payload_wf(p)
    &&& p.kind is Console ==> p.base == CONSOLE_OBJECT && p.order == 0
    &&& p.kind is Power ==> p.base == POWER_OBJECT && p.order == 0
}

/// The bit of a capability's rights word that grants control.
pub const CONTROL_RIGHT: u32 = 128;

/// Control is a right over threads and processes only, design/sharing-by-derive/, and reads the object
/// a capability names, so no untyped or frame capability carries it to whatever is later typed at its
/// base.
pub open spec fn control_named(p: Payload) -> bool {
    p.rights & CONTROL_RIGHT != 0 ==> p.kind is Thread || p.kind is Process
}

/// Where index i falls in a table.
pub open spec fn index_entry(i: usize) -> int { (i / NODES_PER_PAGE as usize) as int }

pub open spec fn index_slot(i: usize) -> int { (i % NODES_PER_PAGE as usize) as int }

/// Index i can name a slot at all.
pub open spec fn index_ok(i: usize) -> bool {
    i < TABLE_INDICES && index_slot(i) != 0
}

/// The list node of index i, in the leaf at `leaf`.
pub open spec fn slot_node(leaf: usize, i: usize) -> usize {
    (leaf + index_slot(i)) as usize
}

pub struct Tables {
    pub roots: Tracked<Map<usize, PointsTo<TableRoot>>>,
    /// Each leaf's payload page, by the leaf's address.
    pub payloads: Tracked<Map<usize, PointsTo<PayloadPage>>>,
    /// The root and entry that hold each leaf, so that each leaf is in one place only.
    pub owner: Ghost<Map<usize, (usize, int)>>,
}

/// A leaf's second page is page aligned. On its own, since the modulus is costly among a function's
/// other facts.
proof fn lemma_payload_page_aligned(leaf: usize)
    requires
        leaf % 8192 == 0,
    ensures
        (leaf + 4096) % 4096 == 0,
{
}

/// The record of a leaf's parent, held where its hidden node's payload would be, since a hidden node
/// has no slot. It names the root entry that points at the leaf, which the leaf's free clears at run
/// time, knowing only the leaf.
pub open spec fn parent_record(root: usize, r: usize) -> Payload {
    Payload { kind: CapKind::Untyped, order: 0, rights: 1, base: root, badge: r, reserved: 0 }
}

/// Where a slot's node lies in its leaf. On its own, like the next, for the modulus.
pub proof fn lemma_slot_in_leaf(leaf: usize, slot: usize)
    requires
        leaf % 8192 == 0,
        slot < NODES_PER_PAGE,
        leaf + slot <= usize::MAX,
    ensures
        page_of((leaf + slot) as usize) == leaf,
        ((leaf + slot) as usize) % 4096 == slot,
{
}

/// Turns a page into a leaf's payload page with every entry written, and its parent recorded.
fn new_payload_page(addr: usize, root: usize, r: usize, Tracked(page): Tracked<PagePerm4k>) -> (ret: Tracked<PointsTo<PayloadPage>>)
    requires
        page.addr() == addr,
        addr % 4096 == 0,
    ensures
        ret@.addr() == addr,
        ret@.is_init(),
        ret@.value().entries.wf(),
        ret@.value().entries@[0] == parent_record(root, r),
{
    let mut entries = Array::<Payload, NODES_PER_PAGE>::new();
    let mut k = 0;
    while k != NODES_PER_PAGE
        invariant
            0 <= k <= NODES_PER_PAGE,
            entries.wf(),
        decreases NODES_PER_PAGE - k,
    {
        entries.set(k, Payload { kind: CapKind::Untyped, order: 0, rights: 0, base: 0, badge: 0, reserved: 0 });
        k = k + 1;
    }
    entries.set(0, Payload { kind: CapKind::Untyped, order: 0, rights: 1, base: root, badge: r, reserved: 0 });
    let tracked mut typed;
    proof {
        let tracked mut page = page;
        page.leak_contents();
        typed = crate::layouts::page_into_payload_page(page);
    }
    PPtr::<PayloadPage>::from_usize(addr).put(Tracked(&mut typed), PayloadPage { entries });
    Tracked(typed)
}

impl Tables {
    /// The leaf in entry r of the table at root.
    pub open spec fn leaf(&self, root: usize, r: int) -> usize {
        self.roots@[root].value().leaves@[r]
    }

    /// The leaf's parent record, which names its root entry.
    pub open spec fn record(&self, leaf: usize) -> Payload {
        self.payloads@[leaf].value().entries@[0]
    }

    /// The root at `root` is initialised, and every leaf it names is owned by that entry.
    pub open spec fn root_wf(&self, root: usize) -> bool {
        &&& self.roots@[root].addr() == root
        &&& self.roots@[root].is_init()
        &&& self.roots@[root].value().leaves.wf()
        &&& forall|r: int| 0 <= r < ROOT_ENTRIES && #[trigger] self.leaf(root, r) != NO_LEAF ==> {
            &&& self.owner@.contains_key(self.leaf(root, r))
            &&& self.owner@[self.leaf(root, r)] == (root, r)
        }
    }

    #[verifier::opaque]
    pub open spec fn roots_wf(&self) -> bool {
        forall|root: usize| #[trigger] self.roots@.contains_key(root) ==> self.root_wf(root)
    }

    /// The owned leaf at `leaf` has a payload page, and its two pages are aligned and in the list's
    /// address space. It is where its owner says, and its record says the same: a leaf stays in its root
    /// entry until its own retype frees it, so its owner always names a root the tables hold. See
    /// design/teardown-driven-by-retype/.
    pub open spec fn leaf_wf(&self, list: &Tree, leaf: usize) -> bool {
        let (root, r) = self.owner@[leaf];
        &&& leaf != NO_LEAF
        &&& leaf % 8192 == 0
        &&& self.roots@.contains_key(root)
        &&& 0 <= r < ROOT_ENTRIES
        &&& self.leaf(root, r) == leaf
        &&& self.record(leaf).base == root
        &&& self.record(leaf).badge as int == r
        &&& list.pages@.dom().contains(leaf)
        &&& self.payloads@.contains_key(leaf)
        &&& self.payloads@[leaf].addr() == leaf + 4096
        &&& self.payloads@[leaf].is_init()
        &&& self.payloads@[leaf].value().entries.wf()
    }

    #[verifier::opaque]
    pub open spec fn leaves_wf(&self, list: &Tree) -> bool {
        forall|leaf: usize| #[trigger] self.owner@.contains_key(leaf) ==> self.leaf_wf(list, leaf)
    }

    pub open spec fn wf(&self, list: &Tree) -> bool {
        &&& self.roots_wf()
        &&& self.leaves_wf(list)
    }

    /// Node n is a live capability in a slot of some table. Node 0 of a leaf is its hidden node, and
    /// nodes in other pages are mappings and bindings, so neither counts.
    pub open spec fn is_cap(&self, list: &Tree, n: usize) -> bool {
        &&& list.nodes@[n as int].live
        &&& list.nodes@[n as int].kind is Capability
        &&& self.owner@.contains_key(page_of(n))
        &&& n % 4096 != 0
        &&& n % 4096 < NODES_PER_PAGE
    }

    /// What capability n says.
    pub open spec fn payload_of(&self, n: usize) -> Payload {
        self.payloads@[page_of(n)].value().entries@[(n % 4096) as int]
    }

    /// Every capability says something well formed.
    pub open spec fn caps_wf(&self, list: &Tree) -> bool {
        forall|n: usize| #[trigger] self.is_cap(list, n) ==> cap_wf(self.payload_of(n))
    }

    /// Every capability with the control right names a thread or a process.
    pub open spec fn control_wf(&self, list: &Tree) -> bool {
        forall|n: usize| #[trigger] self.is_cap(list, n) ==> control_named(self.payload_of(n))
    }

    /// The tables read nothing of a list but which pages it holds, so more pages keep them whole.
    pub proof fn lemma_wf_same_pages(&self, a: &Tree, b: &Tree)
        requires
            self.wf(a),
            forall|p: usize| #[trigger] a.pages@.dom().contains(p) ==> b.pages@.dom().contains(p),
        ensures
            self.wf(b),
    {
        assert(self.leaves_wf(b)) by {
            reveal(Tables::leaves_wf);
            assert forall|leaf: usize| #[trigger] self.owner@.contains_key(leaf) implies self.leaf_wf(b, leaf) by {
                assert(self.leaf_wf(a, leaf));
            }
        }
    }

    /// A root the tables hold is initialised.
    pub proof fn lemma_root(&self, root: usize)
        requires
            self.roots_wf(),
            self.roots@.contains_key(root),
        ensures
            self.roots@[root].addr() == root,
            self.roots@[root].is_init(),
            self.roots@[root].value().leaves.wf(),
    {
        reveal(Tables::roots_wf);
    }

    /// A leaf a root entry names is owned by that entry.
    pub proof fn lemma_entry(&self, root: usize, r: int)
        requires
            self.roots_wf(),
            self.roots@.contains_key(root),
            0 <= r < ROOT_ENTRIES,
            self.leaf(root, r) != NO_LEAF,
        ensures
            self.owner@.contains_key(self.leaf(root, r)),
            self.owner@[self.leaf(root, r)] == (root, r),
    {
        reveal(Tables::roots_wf);
    }

    /// An owned leaf is where its owner says and has its pages.
    pub proof fn lemma_leaf(&self, list: &Tree, leaf: usize)
        requires
            self.leaves_wf(list),
            self.owner@.contains_key(leaf),
        ensures
            self.leaf_wf(list, leaf),
    {
        reveal(Tables::leaves_wf);
    }

    /// Index i names a slot of the table at root: its leaf is in its root entry and the leaf's hidden
    /// node is live. A leaf whose hidden node is dead has no slots, so nothing is added to it while it
    /// is torn down. See design/teardown-driven-by-retype/.
    pub open spec fn has_slot(&self, list: &Tree, root: usize, i: usize) -> bool {
        &&& index_ok(i)
        &&& self.roots@.contains_key(root)
        &&& self.leaf(root, index_entry(i)) != NO_LEAF
        &&& list.nodes@[self.leaf(root, index_entry(i)) as int].live
    }

    /// The node index i names in the table at root.
    pub open spec fn node_of(&self, root: usize, i: usize) -> usize {
        slot_node(self.leaf(root, index_entry(i)), i)
    }

    pub fn new() -> (ret: Self)
        ensures
            ret.roots@ == Map::<usize, PointsTo<TableRoot>>::empty(),
            ret.owner@ == Map::<usize, (usize, int)>::empty(),
            forall|list: &Tree| #[trigger] ret.wf(list),
    {
        let ret = Self {
            roots: Tracked(Map::tracked_empty()),
            payloads: Tracked(Map::tracked_empty()),
            owner: Ghost(Map::empty()),
        };
        proof {
            assert(ret.roots_wf()) by { reveal(Tables::roots_wf); }
            assert forall|list: &Tree| #[trigger] ret.wf(list) by {
                assert(ret.leaves_wf(list)) by { reveal(Tables::leaves_wf); }
            }
        }
        ret
    }

    /// Makes the page at `root` an empty table's root. The page is the first of a process object, so
    /// only the process's retype calls this.
    pub fn put_root(&mut self, list: &Tree, root: usize, Tracked(page): Tracked<PagePerm4k>)
        requires
            old(self).wf(list),
            !old(self).roots@.contains_key(root),
            page.addr() == root,
            root % 4096 == 0,
        ensures
            final(self).wf(list),
            final(self).roots@.contains_key(root),
            forall|r: int| 0 <= r < ROOT_ENTRIES ==> #[trigger] final(self).leaf(root, r) == NO_LEAF,
            forall|t: usize| old(self).roots@.contains_key(t) ==> #[trigger] final(self).roots@.contains_key(t),
            forall|t: usize| #[trigger] old(self).roots@.contains_key(t) ==> final(self).roots@[t] == old(self).roots@[t],
            final(self).roots@.dom() == old(self).roots@.dom().insert(root),
            final(self).owner == old(self).owner,
            final(self).payloads == old(self).payloads,
            forall|t: usize, i: usize| #[trigger] old(self).has_slot(list, t, i) ==>
                final(self).has_slot(list, t, i) && final(self).node_of(t, i) == old(self).node_of(t, i),
    {
        let ghost pre = *old(self);
        let mut leaves = Array::<usize, ROOT_ENTRIES>::new();
        let mut r = 0;
        while r != ROOT_ENTRIES
            invariant
                0 <= r <= ROOT_ENTRIES,
                leaves.wf(),
                forall|j: int| 0 <= j < r ==> #[trigger] leaves@[j] == NO_LEAF,
            decreases ROOT_ENTRIES - r,
        {
            leaves.set(r, NO_LEAF);
            r = r + 1;
        }
        let tracked mut typed;
        proof {
            let tracked mut page = page;
            page.leak_contents();
            typed = crate::layouts::page_into_table_root(page);
        }
        PPtr::<TableRoot>::from_usize(root).put(Tracked(&mut typed), TableRoot { leaves });
        proof {
            self.roots.borrow_mut().tracked_insert(root, typed);
            let me = *self;
            assert(me.roots@.dom() =~= pre.roots@.dom().insert(root));
            assert(me.roots@[root].value().leaves@ == leaves@);
            assert forall|r: int| 0 <= r < ROOT_ENTRIES implies #[trigger] me.leaf(root, r) == NO_LEAF by {
                assert(leaves@[r] == NO_LEAF);
            }
            assert(me.roots_wf()) by {
                reveal(Tables::roots_wf);
                assert forall|t: usize| #[trigger] me.roots@.contains_key(t) implies me.root_wf(t) by {
                    if t == root {
                        assert forall|s: int| 0 <= s < ROOT_ENTRIES && #[trigger] me.leaf(t, s) != NO_LEAF implies {
                            &&& me.owner@.contains_key(me.leaf(t, s))
                            &&& me.owner@[me.leaf(t, s)] == (t, s)
                        } by {
                            assert(me.leaf(root, s) == NO_LEAF);
                        }
                    } else {
                        pre.lemma_root(t);
                        assert(me.roots@[t] == pre.roots@[t]);
                        assert forall|s: int| 0 <= s < ROOT_ENTRIES && #[trigger] me.leaf(t, s) != NO_LEAF implies {
                            &&& me.owner@.contains_key(me.leaf(t, s))
                            &&& me.owner@[me.leaf(t, s)] == (t, s)
                        } by {
                            assert(pre.leaf(t, s) == me.leaf(t, s));
                            pre.lemma_entry(t, s);
                        }
                    }
                }
            }
            assert(me.leaves_wf(list)) by {
                reveal(Tables::leaves_wf);
                assert forall|l: usize| #[trigger] me.owner@.contains_key(l) implies me.leaf_wf(list, l) by {
                    pre.lemma_leaf(list, l);
                    let (t, s) = pre.owner@[l];
                    assert(t != root);
                    assert(me.roots@[t] == pre.roots@[t]);
                }
            }
        }
    }

    /// Puts a leaf in entry r of a table. The caller has added its node page to the list and made its
    /// hidden node, and hands over its payload page.
    pub fn add_leaf(
        &mut self,
        list: &Tree,
        root: usize,
        r: usize,
        leaf: usize,
        Tracked(page): Tracked<PagePerm4k>,
    )
        requires
            old(self).wf(list),
            old(self).roots@.contains_key(root),
            r < ROOT_ENTRIES,
            old(self).leaf(root, r as int) == NO_LEAF,
            leaf != NO_LEAF,
            leaf % 8192 == 0,
            leaf + 8192 <= usize::MAX,
            list.pages@.dom().contains(leaf),
            !old(self).owner@.contains_key(leaf),
            page.addr() == leaf + 4096,
        ensures
            final(self).wf(list),
            final(self).leaf(root, r as int) == leaf,
            forall|e: int| e != r ==> #[trigger] final(self).leaf(root, e) == old(self).leaf(root, e),
            final(self).roots@.dom() == old(self).roots@.dom(),
            forall|t: usize| t != root && #[trigger] old(self).roots@.contains_key(t) ==> final(self).roots@[t] == old(self).roots@[t],
            final(self).owner@ == old(self).owner@.insert(leaf, (root, r as int)),
            final(self).payloads@ == old(self).payloads@.insert(leaf, final(self).payloads@[leaf]),
            forall|t: usize, i: usize| #[trigger] old(self).has_slot(list, t, i) ==>
                final(self).has_slot(list, t, i) && final(self).node_of(t, i) == old(self).node_of(t, i),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_root(root);
            lemma_payload_page_aligned(leaf);
        }
        let Tracked(typed) = new_payload_page(leaf + 4096, root, r, Tracked(page));
        proof {
            self.payloads.borrow_mut().tracked_insert(leaf, typed);
        }
        self.set_leaf(root, r, leaf);
        self.owner = Ghost(pre.owner@.insert(leaf, (root, r as int)));
        proof {
            Self::lemma_leaf_added(pre, *self, list, root, r, leaf);
        }
    }

    /// Writes entry r of the root at `root`. The caller keeps the tables' invariant.
    fn set_leaf(&mut self, root: usize, r: usize, leaf: usize)
        requires
            old(self).roots@.contains_key(root),
            old(self).roots@[root].addr() == root,
            old(self).roots@[root].is_init(),
            old(self).roots@[root].value().leaves.wf(),
            r < ROOT_ENTRIES,
        ensures
            final(self).payloads == old(self).payloads,
            final(self).owner == old(self).owner,
            final(self).roots@.dom() == old(self).roots@.dom(),
            forall|t: usize| t != root && #[trigger] old(self).roots@.contains_key(t) ==> final(self).roots@[t] == old(self).roots@[t],
            final(self).roots@[root].addr() == root,
            final(self).roots@[root].is_init(),
            final(self).roots@[root].value().leaves.wf(),
            final(self).roots@[root].value().leaves@ == old(self).roots@[root].value().leaves@.update(r as int, leaf),
    {
        let ghost pre = *old(self);
        let tracked mut root_perm;
        proof {
            root_perm = self.roots.borrow_mut().tracked_remove(root);
        }
        let root_ptr = PPtr::<TableRoot>::from_usize(root);
        let mut root_value = root_ptr.take(Tracked(&mut root_perm));
        root_value.leaves.set(r, leaf);
        root_ptr.put(Tracked(&mut root_perm), root_value);
        proof {
            self.roots.borrow_mut().tracked_insert(root, root_perm);
            assert(self.roots@.dom() =~= pre.roots@.dom());
            assert(self.roots@[root].value().leaves@ =~= pre.roots@[root].value().leaves@.update(r as int, leaf));
        }
    }

    /// The tables after a leaf goes in entry r of the table at root.
    proof fn lemma_leaf_added(pre: Self, me: Self, list: &Tree, root: usize, r: usize, leaf: usize)
        requires
            pre.wf(list),
            pre.roots@.contains_key(root),
            r < ROOT_ENTRIES,
            pre.leaf(root, r as int) == NO_LEAF,
            leaf != NO_LEAF,
            leaf % 8192 == 0,
            list.pages@.dom().contains(leaf),
            !pre.owner@.contains_key(leaf),
            me.owner@ == pre.owner@.insert(leaf, (root, r as int)),
            me.roots@.dom() == pre.roots@.dom(),
            forall|t: usize| t != root && #[trigger] pre.roots@.contains_key(t) ==> me.roots@[t] == pre.roots@[t],
            me.roots@[root].addr() == root,
            me.roots@[root].is_init(),
            me.roots@[root].value().leaves.wf(),
            me.roots@[root].value().leaves@ == pre.roots@[root].value().leaves@.update(r as int, leaf),
            me.payloads@ == pre.payloads@.insert(leaf, me.payloads@[leaf]),
            me.payloads@[leaf].addr() == leaf + 4096,
            me.payloads@[leaf].is_init(),
            me.payloads@[leaf].value().entries.wf(),
            me.payloads@[leaf].value().entries@[0] == parent_record(root, r),
        ensures
            me.wf(list),
            me.leaf(root, r as int) == leaf,
            forall|t: usize, i: usize| #[trigger] pre.has_slot(list, t, i) ==>
                me.has_slot(list, t, i) && me.node_of(t, i) == pre.node_of(t, i),
    {
        assert(me.roots@[root].value().leaves@ =~= pre.roots@[root].value().leaves@.update(r as int, leaf));
        assert(pre.roots@.dom() =~= me.roots@.dom());
        assert(me.roots_wf()) by {
            reveal(Tables::roots_wf);
            assert forall|t: usize| #[trigger] me.roots@.contains_key(t) implies me.root_wf(t) by {
                pre.lemma_root(t);
                if t != root {
                    assert(me.roots@[t] == pre.roots@[t]);
                }
                assert forall|s: int| 0 <= s < ROOT_ENTRIES && #[trigger] me.leaf(t, s) != NO_LEAF implies {
                    &&& me.owner@.contains_key(me.leaf(t, s))
                    &&& me.owner@[me.leaf(t, s)] == (t, s)
                } by {
                    if t == root && s == r as int {
                        assert(me.leaf(t, s) == leaf);
                    } else {
                        assert(me.leaf(t, s) == pre.leaf(t, s));
                        pre.lemma_entry(t, s);
                        assert(pre.leaf(t, s) != leaf);
                        assert(me.payloads@[pre.leaf(t, s)] == pre.payloads@[pre.leaf(t, s)]);
                    }
                }
            }
        }
        assert(me.leaves_wf(list)) by {
            reveal(Tables::leaves_wf);
            assert forall|l: usize| #[trigger] me.owner@.contains_key(l) implies me.leaf_wf(list, l) by {
                if l == leaf {
                    assert(me.owner@[l] == (root, r as int));
                    assert(me.leaf(root, r as int) == leaf);
                } else {
                    pre.lemma_leaf(list, l);
                    let (t, s) = pre.owner@[l];
                    assert(me.owner@[l] == pre.owner@[l]);
                    assert(me.payloads@[l] == pre.payloads@[l]);
                    if t == root {
                        assert(s != r as int);
                    } else {
                        assert(me.roots@[t] == pre.roots@[t]);
                    }
                    assert(me.leaf(t, s) == pre.leaf(t, s));
                }
            }
        }
        assert forall|t: usize, i: usize| #[trigger] pre.has_slot(list, t, i) implies
            me.has_slot(list, t, i) && me.node_of(t, i) == pre.node_of(t, i) by {
            assert(!(t == root && index_entry(i) == r as int));
            if t != root {
                assert(me.roots@[t] == pre.roots@[t]);
            }
        }
    }

    /// Finds index i in the table at root, in a fixed number of loads. An index from user space is
    /// checked here: it may be out of range, in a missing leaf, in a leaf whose hidden node is dead, or
    /// position 0 of a leaf, which is no slot. Whether the slot is occupied is for the caller to read
    /// from the list.
    pub fn lookup(&self, list: &Tree, root: usize, i: usize) -> (ret: Option<(usize, Payload)>)
        requires
            self.wf(list),
            list.store_wf(),
            self.roots@.contains_key(root),
        ensures
            ret is Some <==> self.has_slot(list, root, i),
            ret is Some ==> {
                &&& ret.unwrap().0 == self.node_of(root, i)
                &&& list.valid(ret.unwrap().0)
                &&& ret.unwrap().0 % 4096 != 0
                &&& ret.unwrap().1 == self.payloads@[self.leaf(root, index_entry(i))].value().entries@[index_slot(i)]
            },
    {
        if i >= TABLE_INDICES || i % NODES_PER_PAGE == 0 {
            return None;
        }
        let r = i / NODES_PER_PAGE;
        let slot = i % NODES_PER_PAGE;
        proof {
            self.lemma_root(root);
        }
        let root_ref = PPtr::<TableRoot>::from_usize(root).borrow(Tracked(self.roots.borrow().tracked_borrow(root)));
        let leaf = *root_ref.leaves.get(r);
        if leaf == NO_LEAF {
            return None;
        }
        proof {
            self.lemma_entry(root, r as int);
            self.lemma_leaf(list, leaf);
            lemma_slot_in_leaf(leaf, slot);
            lemma_slot_in_leaf(leaf, 0);
        }
        if !list.get(leaf).live {
            return None;
        }
        let payloads = PPtr::<PayloadPage>::from_usize(leaf + 4096).borrow(Tracked(self.payloads.borrow().tracked_borrow(leaf)));
        Some((leaf + slot, *payloads.entries.get(slot)))
    }

    /// Writes what the capability at index i says. Only that slot's payload changes.
    pub fn set_payload(&mut self, list: &Tree, root: usize, i: usize, p: Payload)
        requires
            old(self).wf(list),
            old(self).has_slot(list, root, i),
        ensures
            final(self).wf(list),
            final(self).roots == old(self).roots,
            final(self).owner == old(self).owner,
            final(self).payload_of(old(self).node_of(root, i)) == p,
            forall|n: usize| #![trigger final(self).payload_of(n)]
                n != old(self).node_of(root, i) && n % 4096 < NODES_PER_PAGE
                && old(self).owner@.contains_key(page_of(n))
                ==> final(self).payload_of(n) == old(self).payload_of(n),
    {
        let ghost pre = *old(self);
        let r = i / NODES_PER_PAGE;
        let slot = i % NODES_PER_PAGE;
        proof {
            pre.lemma_root(root);
        }
        let root_ref = PPtr::<TableRoot>::from_usize(root).borrow(Tracked(self.roots.borrow().tracked_borrow(root)));
        let leaf = *root_ref.leaves.get(r);
        proof {
            pre.lemma_entry(root, r as int);
            pre.lemma_leaf(list, leaf);
            lemma_slot_in_leaf(leaf, slot);
        }
        let tracked mut perm;
        proof {
            perm = self.payloads.borrow_mut().tracked_remove(leaf);
        }
        PPtr::<PayloadPage>::from_usize(leaf + 4096).borrow_mut(Tracked(&mut perm)).entries.set(slot, p);
        proof {
            self.payloads.borrow_mut().tracked_insert(leaf, perm);
            assert(self.payloads@ =~= pre.payloads@.insert(leaf, self.payloads@[leaf]));
            Self::lemma_payload_written(pre, *self, list, root, i, leaf, slot, p);
        }
    }

    /// The tables after index i's payload is written.
    proof fn lemma_payload_written(pre: Self, me: Self, list: &Tree, root: usize, i: usize, leaf: usize, slot: usize, p: Payload)
        requires
            pre.wf(list),
            pre.has_slot(list, root, i),
            leaf == pre.leaf(root, index_entry(i)),
            leaf == page_of(pre.node_of(root, i)),
            slot as int == index_slot(i),
            slot == pre.node_of(root, i) % 4096,
            me.roots == pre.roots,
            me.owner == pre.owner,
            me.payloads@ == pre.payloads@.insert(leaf, me.payloads@[leaf]),
            me.payloads@[leaf].addr() == pre.payloads@[leaf].addr(),
            me.payloads@[leaf].is_init(),
            me.payloads@[leaf].value().entries.wf(),
            me.payloads@[leaf].value().entries@ == pre.payloads@[leaf].value().entries@.update(slot as int, p),
        ensures
            me.wf(list),
            me.payload_of(pre.node_of(root, i)) == p,
            forall|n: usize| #![trigger me.payload_of(n)]
                n != pre.node_of(root, i) && n % 4096 < NODES_PER_PAGE
                && pre.owner@.contains_key(page_of(n))
                ==> me.payload_of(n) == pre.payload_of(n),
    {
        // Index i is a slot, so it is not position 0, where the record is.
        assert(slot != 0);
        assert forall|l: usize| #[trigger] me.record(l) == pre.record(l) by {
            if l == leaf {
                assert(me.payloads@[leaf].value().entries@[0] == pre.payloads@[leaf].value().entries@[0]);
            }
        }
        assert(me.roots_wf()) by {
            reveal(Tables::roots_wf);
            assert forall|t: usize| #[trigger] me.roots@.contains_key(t) implies me.root_wf(t) by {
                pre.lemma_root(t);
                assert forall|s: int| 0 <= s < ROOT_ENTRIES && #[trigger] me.leaf(t, s) != NO_LEAF implies {
                    &&& me.owner@.contains_key(me.leaf(t, s))
                    &&& me.owner@[me.leaf(t, s)] == (t, s)
                } by {
                    assert(me.leaf(t, s) == pre.leaf(t, s));
                    pre.lemma_entry(t, s);
                    assert(me.record(me.leaf(t, s)) == pre.record(me.leaf(t, s)));
                }
            }
        }
        assert(me.leaves_wf(list)) by {
            reveal(Tables::leaves_wf);
            assert forall|l: usize| #[trigger] me.owner@.contains_key(l) implies me.leaf_wf(list, l) by {
                assert(pre.leaf_wf(list, l));
                assert(me.record(l) == pre.record(l));
            }
        }
        assert forall|n: usize| #![trigger me.payload_of(n)]
            n != pre.node_of(root, i) && n % 4096 < NODES_PER_PAGE && pre.owner@.contains_key(page_of(n))
            implies me.payload_of(n) == pre.payload_of(n) by {
            if page_of(n) == leaf {
                assert(n % 4096 != slot);
            }
        }
    }

    /// Takes a leaf with no live node out of the tables, handing back its payload page. Its root entry,
    /// which its parent record names, is cleared in the same step, the two-way clear. It held nothing
    /// that is still a capability, and its hidden node is dead, so no index found a slot in it and
    /// nothing else changes.
    pub fn give_back_leaf(&mut self, list: &Tree, leaf: usize) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).wf(list),
            old(self).owner@.contains_key(leaf),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] list.nodes@[leaf + k]).live,
        ensures
            final(self).wf(list),
            final(self).roots@.dom() == old(self).roots@.dom(),
            final(self).leaf(old(self).owner@[leaf].0, old(self).owner@[leaf].1) == NO_LEAF,
            forall|t: usize, s: int| #![trigger final(self).leaf(t, s)] old(self).roots@.contains_key(t) && 0 <= s < ROOT_ENTRIES
                && !(t == old(self).owner@[leaf].0 && s == old(self).owner@[leaf].1)
                ==> final(self).leaf(t, s) == old(self).leaf(t, s),
            final(self).owner@ == old(self).owner@.remove(leaf),
            final(self).payloads@ == old(self).payloads@.remove(leaf),
            ret@.addr() == leaf + 4096,
            ret@.is_uninit(),
            forall|t: usize, i: usize| #[trigger] final(self).has_slot(list, t, i) == old(self).has_slot(list, t, i),
            forall|t: usize, i: usize| #[trigger] old(self).has_slot(list, t, i) ==> final(self).node_of(t, i) == old(self).node_of(t, i),
            forall|n: usize| #[trigger] final(self).is_cap(list, n) == old(self).is_cap(list, n),
            forall|n: usize| page_of(n) != leaf ==> #[trigger] final(self).payload_of(n) == old(self).payload_of(n),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_leaf(list, leaf);
        }
        let record = *PPtr::<PayloadPage>::from_usize(leaf + 4096)
            .borrow(Tracked(self.payloads.borrow().tracked_borrow(leaf)))
            .entries
            .get(0);
        let root = record.base;
        let r = record.badge;
        proof {
            pre.lemma_root(root);
        }
        self.set_leaf(root, r, NO_LEAF);
        let tracked page;
        proof {
            let tracked mut payloads = self.payloads.borrow_mut().tracked_remove(leaf);
            payloads.leak_contents();
            page = crate::layouts::payload_page_into_page(payloads);
            self.owner = Ghost(pre.owner@.remove(leaf));
            Self::lemma_leaf_given_back(pre, *self, list, leaf, root, r);
        }
        Tracked(page)
    }

    /// The tables after a leaf with no live node leaves them, its root entry cleared.
    proof fn lemma_leaf_given_back(pre: Self, me: Self, list: &Tree, leaf: usize, root: usize, r: usize)
        requires
            pre.wf(list),
            pre.owner@.contains_key(leaf),
            pre.owner@[leaf] == (root, r as int),
            r < ROOT_ENTRIES,
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] list.nodes@[leaf + k]).live,
            me.owner@ == pre.owner@.remove(leaf),
            me.payloads@ == pre.payloads@.remove(leaf),
            me.roots@.dom() == pre.roots@.dom(),
            forall|t: usize| t != root && #[trigger] pre.roots@.contains_key(t) ==> me.roots@[t] == pre.roots@[t],
            me.roots@[root].addr() == root,
            me.roots@[root].is_init(),
            me.roots@[root].value().leaves.wf(),
            me.roots@[root].value().leaves@ == pre.roots@[root].value().leaves@.update(r as int, NO_LEAF),
        ensures
            me.wf(list),
            me.leaf(root, r as int) == NO_LEAF,
            forall|t: usize, s: int| #![trigger me.leaf(t, s)] !(t == root && s == r as int) && 0 <= s < ROOT_ENTRIES
                && pre.roots@.contains_key(t) ==> me.leaf(t, s) == pre.leaf(t, s),
            forall|t: usize, i: usize| #[trigger] me.has_slot(list, t, i) == pre.has_slot(list, t, i),
            forall|t: usize, i: usize| #[trigger] pre.has_slot(list, t, i) ==> me.node_of(t, i) == pre.node_of(t, i),
            forall|n: usize| #[trigger] me.is_cap(list, n) == pre.is_cap(list, n),
            forall|n: usize| page_of(n) != leaf ==> #[trigger] me.payload_of(n) == pre.payload_of(n),
    {
        pre.lemma_leaf(list, leaf);
        assert(pre.leaf(root, r as int) == leaf);
        assert(me.leaf(root, r as int) == NO_LEAF);
        assert(!list.nodes@[leaf + 0int].live);
        assert forall|t: usize, s: int| !(t == root && s == r as int) && 0 <= s < ROOT_ENTRIES
            && pre.roots@.contains_key(t) implies #[trigger] me.leaf(t, s) == pre.leaf(t, s) by {
            if t != root {
                assert(me.roots@[t] == pre.roots@[t]);
            }
        }
        assert(me.roots_wf()) by {
            reveal(Tables::roots_wf);
            assert forall|t: usize| #[trigger] me.roots@.contains_key(t) implies me.root_wf(t) by {
                pre.lemma_root(t);
                if t != root {
                    assert(me.roots@[t] == pre.roots@[t]);
                }
                assert forall|s: int| 0 <= s < ROOT_ENTRIES && #[trigger] me.leaf(t, s) != NO_LEAF implies {
                    &&& me.owner@.contains_key(me.leaf(t, s))
                    &&& me.owner@[me.leaf(t, s)] == (t, s)
                } by {
                    assert(!(t == root && s == r as int));
                    assert(me.leaf(t, s) == pre.leaf(t, s));
                    pre.lemma_entry(t, s);
                    assert(pre.leaf(t, s) != leaf);
                }
            }
        }
        assert(me.leaves_wf(list)) by {
            reveal(Tables::leaves_wf);
            assert forall|l: usize| #[trigger] me.owner@.contains_key(l) implies me.leaf_wf(list, l) by {
                pre.lemma_leaf(list, l);
                assert(l != leaf);
                let (t, s) = pre.owner@[l];
                assert(me.owner@[l] == pre.owner@[l]);
                assert(me.payloads@[l] == pre.payloads@[l]);
                assert(pre.leaf(t, s) == l);
                assert(!(t == root && s == r as int));
                assert(me.leaf(t, s) == pre.leaf(t, s));
            }
        }
        assert forall|t: usize, i: usize| #[trigger] me.has_slot(list, t, i) == pre.has_slot(list, t, i) by {
            if index_ok(i) && pre.roots@.contains_key(t) {
                assert(0 <= index_entry(i) < ROOT_ENTRIES);
                if !(t == root && index_entry(i) == r as int) {
                    assert(me.leaf(t, index_entry(i)) == pre.leaf(t, index_entry(i)));
                }
            }
        }
        assert forall|t: usize, i: usize| #[trigger] pre.has_slot(list, t, i) implies me.node_of(t, i) == pre.node_of(t, i) by {
            assert(0 <= index_entry(i) < ROOT_ENTRIES);
            assert(!(t == root && index_entry(i) == r as int));
            assert(me.leaf(t, index_entry(i)) == pre.leaf(t, index_entry(i)));
        }
        assert forall|n: usize| #[trigger] me.is_cap(list, n) == pre.is_cap(list, n) by {
            if pre.is_cap(list, n) && page_of(n) == leaf {
                Self::lemma_node_in_leaf(leaf, n);
                assert(list.nodes@[leaf + (n % 4096) as int] == list.nodes@[n as int]);
            }
        }
        assert forall|n: usize| page_of(n) != leaf implies #[trigger] me.payload_of(n) == pre.payload_of(n) by {
            assert(me.payloads@[page_of(n)] == pre.payloads@[page_of(n)]);
        }
    }

    /// A node on a leaf's page is the leaf's address and its offset. On its own, for the modulus.
    proof fn lemma_node_in_leaf(leaf: usize, n: usize)
        requires
            page_of(n) == leaf,
        ensures
            n as int == leaf + (n % 4096) as int,
    {
    }

    /// Takes the table root at `root` out of the tables, handing back its page. Every entry of it names
    /// no leaf, so no leaf's owner names it and nothing else changes. Only the free of a dead process's
    /// block calls this.
    pub fn take_root(&mut self, list: &Tree, root: usize) -> (ret: Tracked<PagePerm4k>)
        requires
            old(self).wf(list),
            old(self).roots@.contains_key(root),
            forall|r: int| 0 <= r < ROOT_ENTRIES ==> #[trigger] old(self).leaf(root, r) == NO_LEAF,
        ensures
            final(self).wf(list),
            final(self).roots@ == old(self).roots@.remove(root),
            final(self).owner == old(self).owner,
            final(self).payloads == old(self).payloads,
            forall|l: usize| #[trigger] final(self).owner@.contains_key(l) ==> final(self).owner@[l].0 != root,
            ret@.addr() == root,
            ret@.is_uninit(),
    {
        let ghost pre = *old(self);
        let tracked page;
        proof {
            pre.lemma_root(root);
            let tracked mut typed = self.roots.borrow_mut().tracked_remove(root);
            typed.leak_contents();
            page = crate::layouts::table_root_into_page(typed);
            let me = *self;
            assert forall|l: usize| #[trigger] pre.owner@.contains_key(l) implies pre.owner@[l].0 != root by {
                pre.lemma_leaf(list, l);
                let (t, r) = pre.owner@[l];
                if t == root {
                    assert(pre.leaf(root, r) == NO_LEAF);
                }
            }
            assert(me.roots_wf()) by {
                reveal(Tables::roots_wf);
                assert forall|t: usize| #[trigger] me.roots@.contains_key(t) implies me.root_wf(t) by {
                    pre.lemma_root(t);
                    assert(me.roots@[t] == pre.roots@[t]);
                    assert forall|s: int| 0 <= s < ROOT_ENTRIES && #[trigger] me.leaf(t, s) != NO_LEAF implies {
                        &&& me.owner@.contains_key(me.leaf(t, s))
                        &&& me.owner@[me.leaf(t, s)] == (t, s)
                    } by {
                        assert(me.leaf(t, s) == pre.leaf(t, s));
                        pre.lemma_entry(t, s);
                    }
                }
            }
            assert(me.leaves_wf(list)) by {
                reveal(Tables::leaves_wf);
                assert forall|l: usize| #[trigger] me.owner@.contains_key(l) implies me.leaf_wf(list, l) by {
                    pre.lemma_leaf(list, l);
                    let (t, s) = pre.owner@[l];
                    assert(t != root);
                    assert(me.roots@[t] == pre.roots@[t]);
                }
            }
        }
        Tracked(page)
    }

    /// Reads what the capability in a slot says.
    pub fn payload_at(&self, list: &Tree, n: usize) -> (ret: Payload)
        requires
            self.wf(list),
            self.is_cap(list, n),
        ensures
            ret == self.payload_of(n),
    {
        let page = n - n % 4096;
        proof {
            self.lemma_leaf(list, page);
        }
        *PPtr::<PayloadPage>::from_usize(page + 4096)
            .borrow(Tracked(self.payloads.borrow().tracked_borrow(page)))
            .entries
            .get(n % 4096)
    }

    /// Reads entry r of the table at root.
    pub fn entry(&self, root: usize, r: usize) -> (ret: usize)
        requires
            self.roots_wf(),
            self.roots@.contains_key(root),
            r < ROOT_ENTRIES,
        ensures
            ret == self.leaf(root, r as int),
    {
        proof {
            self.lemma_root(root);
        }
        let root_ref = PPtr::<TableRoot>::from_usize(root).borrow(Tracked(self.roots.borrow().tracked_borrow(root)));
        *root_ref.leaves.get(r)
    }

    /// Two indices never name one slot, in one table or across two: a leaf is in one entry of one
    /// root, and two indices in one leaf are at two positions.
    pub proof fn lemma_slots_distinct(&self, list: &Tree, a: usize, i: usize, b: usize, j: usize)
        requires
            self.wf(list),
            self.has_slot(list, a, i),
            self.has_slot(list, b, j),
            a != b || i != j,
        ensures
            self.node_of(a, i) != self.node_of(b, j),
    {
        let la = self.leaf(a, index_entry(i));
        let lb = self.leaf(b, index_entry(j));
        self.lemma_entry(a, index_entry(i));
        self.lemma_entry(b, index_entry(j));
        self.lemma_leaf(list, la);
        self.lemma_leaf(list, lb);
        if la == lb {
            assert(a == b);
            assert(index_entry(i) == index_entry(j));
            assert(index_slot(i) != index_slot(j));
        } else {
            assert(la + 8192 <= lb || lb + 8192 <= la);
        }
    }
}

} // verus!
