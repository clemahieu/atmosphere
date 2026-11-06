//! A process's capability table: a root of 512 pointers and leaves retyped on demand. A leaf is two
//! pages, an order-1 block: a node page holding the slots' list nodes, and a payload page holding what
//! each capability says at the same index. Node 0 of a leaf is its hidden node, so a leaf has 127 slots.
//! No capability names a table, so tables cannot form cycles. See the design on atmo-6x9.6.7, sections
//! 1 and 2.
//!
//! A table is named by its root's address until the process object holds it, atmo-6x9.16.9.
//!
//! The two parts of the invariant are opaque and reached through one-position lemmas: spelled out,
//! the root clause names every entry of every root the prover has seen, and the leaf clause chains
//! back through `owner` to the root clause again.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::list::*;
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

/// What a capability says names a block: base aligned to its size, inside the address space. See the
/// design on atmo-6x9.6.7, section 3.
pub open spec fn payload_wf(p: Payload) -> bool {
    &&& p.order <= MAX_ORDER
    &&& p.base as int % block_bytes(p.order) == 0
    &&& p.base as int + block_bytes(p.order) <= NODE_SPACE as int
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

/// Turns a page into a leaf's payload page with every entry written.
fn new_payload_page(addr: usize, Tracked(page): Tracked<PagePerm4k>) -> (ret: Tracked<PointsTo<PayloadPage>>)
    requires
        page.addr() == addr,
        addr % 4096 == 0,
    ensures
        ret@.addr() == addr,
        ret@.is_init(),
        ret@.value().entries.wf(),
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

    /// The owned leaf at `leaf` is where its owner says, has a payload page, and its two pages are
    /// aligned and in the list's address space.
    pub open spec fn leaf_wf(&self, list: &Tree, leaf: usize) -> bool {
        let (root, r) = self.owner@[leaf];
        &&& leaf != NO_LEAF
        &&& leaf % 8192 == 0
        &&& self.roots@.contains_key(root)
        &&& 0 <= r < ROOT_ENTRIES
        &&& self.leaf(root, r) == leaf
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

    /// Every capability names a block.
    pub open spec fn caps_wf(&self, list: &Tree) -> bool {
        forall|n: usize| #[trigger] self.is_cap(list, n) ==> payload_wf(self.payload_of(n))
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

    pub open spec fn has_slot(&self, root: usize, i: usize) -> bool {
        &&& index_ok(i)
        &&& self.roots@.contains_key(root)
        &&& self.leaf(root, index_entry(i)) != NO_LEAF
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

    /// Adds an empty table whose root is the page at `root`.
    pub fn add_table(&mut self, list: &Tree, root: usize, Tracked(page): Tracked<PagePerm4k>)
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
            forall|t: usize, i: usize| #[trigger] old(self).has_slot(t, i) ==>
                final(self).has_slot(t, i) && final(self).node_of(t, i) == old(self).node_of(t, i),
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
            final(self).roots@.dom() == old(self).roots@.dom(),
            final(self).owner@ == old(self).owner@.insert(leaf, (root, r as int)),
            final(self).payloads@ == old(self).payloads@.insert(leaf, final(self).payloads@[leaf]),
            forall|t: usize, i: usize| #[trigger] old(self).has_slot(t, i) ==>
                final(self).has_slot(t, i) && final(self).node_of(t, i) == old(self).node_of(t, i),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_root(root);
            lemma_payload_page_aligned(leaf);
        }
        let Tracked(typed) = new_payload_page(leaf + 4096, Tracked(page));
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
        ensures
            me.wf(list),
            me.leaf(root, r as int) == leaf,
            forall|t: usize, i: usize| #[trigger] pre.has_slot(t, i) ==>
                me.has_slot(t, i) && me.node_of(t, i) == pre.node_of(t, i),
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
        assert forall|t: usize, i: usize| #[trigger] pre.has_slot(t, i) implies
            me.has_slot(t, i) && me.node_of(t, i) == pre.node_of(t, i) by {
            assert(!(t == root && index_entry(i) == r as int));
            if t != root {
                assert(me.roots@[t] == pre.roots@[t]);
            }
        }
    }

    /// Finds index i in the table at root, in a fixed number of loads. An index from user space is
    /// checked here: it may be out of range, in a missing leaf, or position 0 of a leaf, which is no
    /// slot. Whether the slot is occupied is for the caller to read from the list.
    pub fn lookup(&self, list: &Tree, root: usize, i: usize) -> (ret: Option<(usize, Payload)>)
        requires
            self.wf(list),
            self.roots@.contains_key(root),
        ensures
            ret is Some <==> self.has_slot(root, i),
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
            assert(page_of((leaf + slot) as usize) == leaf);
        }
        let payloads = PPtr::<PayloadPage>::from_usize(leaf + 4096).borrow(Tracked(self.payloads.borrow().tracked_borrow(leaf)));
        Some((leaf + slot, *payloads.entries.get(slot)))
    }

    /// Writes what the capability at index i says. Only that slot's payload changes.
    pub fn set_payload(&mut self, list: &Tree, root: usize, i: usize, p: Payload)
        requires
            old(self).wf(list),
            old(self).has_slot(root, i),
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
            assert(page_of((leaf + slot) as usize) == leaf);
        }
        let tracked mut perm;
        proof {
            perm = self.payloads.borrow_mut().tracked_remove(leaf);
        }
        PPtr::<PayloadPage>::from_usize(leaf + 4096).borrow_mut(Tracked(&mut perm)).entries.set(slot, p);
        proof {
            self.payloads.borrow_mut().tracked_insert(leaf, perm);
            let me = *self;
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
                    }
                }
            }
            assert(me.leaves_wf(list)) by {
                reveal(Tables::leaves_wf);
                assert forall|l: usize| #[trigger] me.owner@.contains_key(l) implies me.leaf_wf(list, l) by {
                    assert(pre.leaf_wf(list, l));
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
            self.has_slot(a, i),
            self.has_slot(b, j),
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
