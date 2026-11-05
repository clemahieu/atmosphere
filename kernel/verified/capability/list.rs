//! The capability list. All capabilities, mappings and bindings derived from the boot root are one
//! doubly linked list in depth-first order: a child goes straight after its parent. So a node's
//! descendants are exactly the run after it with greater depth, and revoke needs no scan, mark or
//! cursor. Only a node with no children is unlinked, so a child never loses its place. Nodes live in
//! retyped pages, reached through a page's permission plus an index, and a node id is the page's
//! address plus that index. See the design on atmo-6x9.6.7.
//!
//! Four parts of the invariant are opaque and reached through one-position lemmas: membership,
//! distinctness, the link structure and the parent-child order. Spelled out, membership is an exists
//! that hands the prover a fresh position for every position it has; the links name each position's
//! neighbours, which name theirs; and distinctness and the parent-child order pair every position
//! with every other. Together those make the prover walk the list and square its length.
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::pptr::{PPtr, PointsTo};

pub const NONE: usize = usize::MAX;

/// A node id is below this: a page address, which is below the 48-bit boundary, plus an index.
pub const NODE_SPACE: usize = 0x1_0000_0000_0000;

pub const NODES_PER_PAGE: usize = 128;

#[derive(Clone, Copy)]
pub enum NodeKind {
    Capability,
    Mapping,
    Hidden,
    Binding,
}

#[derive(Clone, Copy)]
pub struct Node {
    pub live: bool,
    pub kind: NodeKind,
    pub depth: usize,
    pub next: usize,
    pub prev: usize,
}

/// A retyped page of nodes. Every object that holds list nodes has at least one.
pub struct NodePage {
    pub nodes: Array<Node, NODES_PER_PAGE>,
}

pub struct Tree {
    pub pages: Tracked<Map<usize, PointsTo<NodePage>>>,
    /// Indexed by node id, so the proofs read one sequence whichever page a node is in.
    pub nodes: Ghost<Seq<Node>>,
    pub seq: Ghost<Seq<usize>>,
    pub parent: Ghost<Map<usize, usize>>,
}

pub open spec fn page_of(i: usize) -> usize {
    (i - i % 4096) as usize
}

/// What the ghost sequence says of an id no page holds.
pub open spec fn dead() -> Node {
    Node { live: false, kind: NodeKind::Capability, depth: 0, next: NONE, prev: NONE }
}

/// x with i renamed slot.
pub open spec fn rename(x: usize, i: usize, slot: usize) -> usize {
    if x == i { slot } else { x }
}

/// The parent map after i is renamed slot: slot takes i's parent, and whoever had i as parent
/// has slot.
pub open spec fn moved_parent(p: Map<usize, usize>, i: usize, slot: usize) -> Map<usize, usize> {
    let dom = p.dom().remove(i).remove(slot);
    Map::new(
        if p.contains_key(i) { dom.insert(slot) } else { dom },
        |x: usize| rename(p[rename(x, slot, i)], i, slot),
    )
}

impl Tree {
    /// i names a slot in a page this list holds.
    pub open spec fn valid(&self, i: usize) -> bool {
        &&& self.pages@.dom().contains(page_of(i))
        &&& i % 4096 < NODES_PER_PAGE
    }

    /// The ghost sequence is what the pages hold, and only a slot in a page can be live.
    #[verifier::opaque]
    pub open spec fn store_wf(&self) -> bool {
        &&& self.nodes@.len() == NODE_SPACE
        &&& forall|p: usize| #[trigger] self.pages@.dom().contains(p) ==> {
            &&& p % 4096 == 0
            &&& p + 4096 <= NODE_SPACE
            &&& self.pages@[p].addr() == p
            &&& self.pages@[p].is_init()
            &&& self.pages@[p].value().nodes.wf()
        }
        &&& forall|i: usize| #[trigger] self.valid(i) ==>
            self.nodes@[i as int] == self.pages@[page_of(i)].value().nodes@[(i % 4096) as int]
        &&& forall|i: int| 0 <= i < NODE_SPACE && #[trigger] self.nodes@[i].live
            ==> self.valid(i as usize)
    }

    /// The node at i.
    pub fn get(&self, i: usize) -> (n: Node)
        requires
            self.store_wf(),
            self.valid(i),
        ensures
            n == self.nodes@[i as int],
    {
        reveal(Tree::store_wf);
        let page = i - i % 4096;
        let tracked perm = self.pages.borrow().tracked_borrow(page);
        *PPtr::<NodePage>::from_usize(page).borrow(Tracked(perm)).nodes.get(i % 4096)
    }

    /// Overwrite the node at i.
    pub fn set(&mut self, i: usize, n: Node)
        requires
            old(self).store_wf(),
            old(self).valid(i),
        ensures
            final(self).store_wf(),
            final(self).nodes@ == old(self).nodes@.update(i as int, n),
            final(self).pages@.dom() == old(self).pages@.dom(),
            final(self).seq == old(self).seq,
            final(self).parent == old(self).parent,
    {
        reveal(Tree::store_wf);
        let page = i - i % 4096;
        let ghost pre = *old(self);
        let tracked mut perm = self.pages.borrow_mut().tracked_remove(page);
        PPtr::<NodePage>::from_usize(page).borrow_mut(Tracked(&mut perm)).nodes.set(i % 4096, n);
        proof {
            self.pages.borrow_mut().tracked_insert(page, perm);
        }
        self.nodes = Ghost(pre.nodes@.update(i as int, n));
        proof {
            assert(self.pages@.dom() =~= pre.pages@.dom());
            assert(self.pages@[page].value().nodes@
                == pre.pages@[page].value().nodes@.update((i % 4096) as int, n));
            assert forall|x: usize| #[trigger] self.valid(x) implies
                self.nodes@[x as int] == self.pages@[page_of(x)].value().nodes@[(x % 4096) as int] by {
                assert(pre.valid(x));
                if page_of(x) == page {
                    if x == i {
                    } else {
                        assert(x % 4096 != i % 4096);
                    }
                } else {
                    assert(self.pages@[page_of(x)] == pre.pages@[page_of(x)]);
                }
            }
            assert forall|x: int| 0 <= x < NODE_SPACE && #[trigger] self.nodes@[x].live
                implies self.valid(x as usize) by {
                if x == i as int {
                    assert(pre.valid(i));
                } else {
                    assert(pre.nodes@[x].live);
                    assert(pre.valid(x as usize));
                }
            }
        }
    }

    /// The store is well formed whatever the ghost sequence and parent map say.
    pub proof fn lemma_store_wf_same_store(a: Tree, b: Tree)
        requires
            a.store_wf(),
            a.pages@ == b.pages@,
            a.nodes@ == b.nodes@,
        ensures
            b.store_wf(),
    {
        reveal(Tree::store_wf);
        assert forall|i: usize| #[trigger] b.valid(i) implies
            b.nodes@[i as int] == b.pages@[page_of(i)].value().nodes@[(i % 4096) as int] by {
            assert(a.valid(i));
        }
        assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] b.nodes@[i].live
            implies b.valid(i as usize) by {
            assert(a.nodes@[i].live);
            assert(a.valid(i as usize));
        }
    }

    /// A slot in a page the list holds is a node id.
    pub proof fn lemma_valid_bound(&self, i: usize)
        requires
            self.store_wf(),
            self.valid(i),
        ensures
            i < NODE_SPACE,
    {
        reveal(Tree::store_wf);
    }

    /// A live node is in a page the list holds.
    pub proof fn lemma_live_valid(&self, i: usize)
        requires
            self.store_wf(),
            0 <= i < NODE_SPACE,
            self.nodes@[i as int].live,
        ensures
            self.valid(i),
    {
        reveal(Tree::store_wf);
    }
}

/// List membership.
#[verifier::opaque]
pub open spec fn has(s: Seq<usize>, x: usize) -> bool { s.contains(x) }

pub proof fn lemma_has(s: Seq<usize>, x: usize)
    ensures has(s, x) <==> s.contains(x),
{
    reveal(has);
}

/// No node is listed twice.
#[verifier::opaque]
pub open spec fn nodup(s: Seq<usize>) -> bool { s.no_duplicates() }

pub proof fn lemma_nodup(s: Seq<usize>, a: int, b: int)
    requires
        nodup(s),
        0 <= a < s.len(),
        0 <= b < s.len(),
        a != b,
    ensures
        s[a] != s[b],
{
    reveal(nodup);
}

impl Tree {
    pub open spec fn d(&self, i: usize) -> int { self.nodes@[i as int].depth as int }

    /// Every listed node is in bounds and live, and its next and prev are its list neighbours.
    /// The neighbour clause is stated over two positions already in hand, so that it never
    /// names a position the prover has not seen.
    #[verifier::opaque]
    pub open spec fn linked(&self) -> bool {
        let s = self.seq@;
        &&& forall|k: int| 0 <= k < s.len() ==>
            0 <= #[trigger] s[k] < self.nodes@.len() && self.nodes@[s[k] as int].live
        &&& self.nodes@[s[0] as int].prev == NONE
        &&& self.nodes@[s[s.len() - 1] as int].next == NONE
        &&& forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && b == a + 1 ==>
            self.nodes@[#[trigger] s[a] as int].next == #[trigger] s[b]
            && self.nodes@[s[b] as int].prev == s[a]
    }

    pub proof fn lemma_link(&self, k: int)
        requires
            self.linked(),
            0 <= k < self.seq@.len(),
        ensures
            0 <= self.seq@[k] < self.nodes@.len(),
            self.nodes@[self.seq@[k] as int].live,
            self.nodes@[self.seq@[k] as int].next
                == (if k + 1 < self.seq@.len() { self.seq@[k + 1] } else { NONE }),
            self.nodes@[self.seq@[k] as int].prev
                == (if k > 0 { self.seq@[k - 1] } else { NONE }),
    {
        reveal(Tree::linked);
    }

    pub open spec fn links(&self) -> bool {
        let s = self.seq@;
        &&& nodup(s)
        &&& s.len() > 0
        &&& s.len() < NONE
        &&& self.nodes@.len() == NODE_SPACE
        &&& self.store_wf()
        &&& self.linked()
        &&& forall|i: int| 0 <= i < self.nodes@.len() && #[trigger] self.nodes@[i].live
            ==> has(s, i as usize)
    }

    /// Every node between a parent and its child is deeper than the parent, and the parent comes
    /// first.
    #[verifier::opaque]
    pub open spec fn runs(&self) -> bool {
        let s = self.seq@;
        forall|j: int, k: int| 0 <= j < s.len() && 0 < k < s.len()
            && #[trigger] s[j] == self.parent@[#[trigger] s[k]] ==> {
            &&& j < k
            &&& forall|m: int| j < m < k ==> self.d(#[trigger] s[m]) > self.d(s[j])
        }
    }

    pub proof fn lemma_runs(&self, j: int, k: int)
        requires
            self.runs(),
            0 <= j < self.seq@.len(),
            0 < k < self.seq@.len(),
            self.seq@[j] == self.parent@[self.seq@[k]],
        ensures
            j < k,
            forall|m: int| j < m < k ==> self.d(#[trigger] self.seq@[m]) > self.d(self.seq@[j]),
    {
        reveal(Tree::runs);
    }

    /// The root is first and shallowest; everything else has an earlier parent one shallower, and
    /// everything between a parent and its child is deeper than the parent.
    pub open spec fn order(&self) -> bool {
        let s = self.seq@;
        &&& self.nodes@[s[0] as int].depth == 0
        &&& forall|k: int| 0 < k < s.len() ==> {
            &&& self.parent@.contains_key(#[trigger] s[k])
            &&& has(s, self.parent@[s[k]])
            &&& self.d(s[k]) >= 1
            &&& self.d(s[k]) == self.d(self.parent@[s[k]]) + 1
        }
        &&& self.runs()
    }

    pub open spec fn wf(&self) -> bool { self.links() && self.order() }

    /// i's ancestor n levels up.
    pub open spec fn anc(&self, i: usize, n: nat) -> usize
        decreases n
    {
        if n == 0 { i } else { self.anc(self.parent@[i], (n - 1) as nat) }
    }

    pub open spec fn is_child(&self, c: usize, i: usize) -> bool {
        self.seq@.contains(i) && i != self.seq@[0] && self.parent@[i] == c
    }

    /// If the node after c is not deeper, c has no child, whichever list position the child has.
    pub proof fn lemma_no_child(&self, c: usize, j: int)
        requires
            self.wf(),
            0 <= j < self.seq@.len(),
            self.seq@[j] == c,
            j + 1 == self.seq@.len() || self.d(self.seq@[j + 1]) <= self.d(c),
        ensures
            forall|i: usize| !#[trigger] self.is_child(c, i),
    {
        let s = self.seq@;
        assert forall|i: usize| !#[trigger] self.is_child(c, i) by {
            if self.is_child(c, i) {
                let k = choose|k: int| 0 <= k < s.len() && s[k] == i;
                assert(k != 0);
                assert(s[j] == self.parent@[s[k]]);
                self.lemma_runs(j, k);
                if k == j + 1 {
                    assert(self.d(s[k]) == self.d(c) + 1);
                } else {
                    assert(self.d(s[j + 1]) > self.d(s[j]));
                }
            }
        }
    }

    /// Everything in the run after c descends from c: its ancestor at the depth difference is c.
    /// So revoking the run touches nothing outside c's lineage.
    pub proof fn lemma_run_is_lineage(&self, j: int, k: int)
        requires
            self.wf(),
            0 <= j < k < self.seq@.len(),
            forall|m: int| j < m <= k ==> self.d(#[trigger] self.seq@[m]) > self.d(self.seq@[j]),
        ensures
            self.d(self.seq@[k]) > self.d(self.seq@[j]),
            self.anc(self.seq@[k], (self.d(self.seq@[k]) - self.d(self.seq@[j])) as nat) == self.seq@[j],
        decreases k - j
    {
        let s = self.seq@;
        let c = s[j];
        let i = s[k];
        assert(self.d(s[k]) > self.d(s[j]));
        assert(k > 0);
        lemma_has(s, self.parent@[s[k]]);
        let p = choose|p: int| 0 <= p < s.len() && s[p] == self.parent@[s[k]];
        self.lemma_runs(p, k);
        if p < j {
            assert(self.d(s[j]) > self.d(s[p]));
            assert(self.d(s[k]) == self.d(s[p]) + 1);
            assert(false);
        }
        let n = (self.d(i) - self.d(c)) as nat;
        assert(n >= 1);
        if p == j {
            assert(n == 1);
            assert(self.anc(i, 1) == self.anc(self.parent@[i], 0));
        } else {
            assert(self.d(s[p]) > self.d(s[j]));
            self.lemma_run_is_lineage(j, p);
            assert((self.d(s[p]) - self.d(s[j])) as nat == (n - 1) as nat);
            assert(self.anc(i, n) == self.anc(self.parent@[i], (n - 1) as nat));
        }
    }

    /// The converse: a node's ancestor n levels up, n being the depth difference, sits earlier,
    /// and everything from just after the ancestor to the node is deeper than the ancestor.
    pub proof fn lemma_lineage_is_run(&self, j: int, k: int, n: nat)
        requires
            self.wf(),
            0 <= j < self.seq@.len(),
            0 <= k < self.seq@.len(),
            n >= 1,
            n == self.d(self.seq@[k]) - self.d(self.seq@[j]),
            self.anc(self.seq@[k], n) == self.seq@[j],
        ensures
            j < k,
            forall|m: int| j < m <= k ==> self.d(#[trigger] self.seq@[m]) > self.d(self.seq@[j]),
        decreases n
    {
        let s = self.seq@;
        let i = s[k];
        assert(self.d(s[0]) == 0);
        assert(k != 0);
        lemma_has(s, self.parent@[i]);
        let p = choose|p: int| 0 <= p < s.len() && s[p] == self.parent@[i];
        self.lemma_runs(p, k);
        assert(self.anc(i, n) == self.anc(self.parent@[i], (n - 1) as nat));
        if n == 1 {
            if p != j { lemma_nodup(s, p, j); }
            assert(p == j);
            assert forall|m: int| j < m <= k implies self.d(#[trigger] s[m]) > self.d(s[j]) by {
                if m == k {
                    assert(self.d(s[k]) == self.d(s[p]) + 1);
                }
            }
        } else {
            assert((n - 1) as nat == self.d(s[p]) - self.d(s[j]));
            self.lemma_lineage_is_run(j, p, (n - 1) as nat);
            assert forall|m: int| j < m <= k implies self.d(#[trigger] s[m]) > self.d(s[j]) by {
                if m <= p {
                } else if m < k {
                    assert(self.d(s[m]) > self.d(s[p]));
                } else {
                    assert(self.d(s[k]) == self.d(s[p]) + 1);
                }
            }
        }
    }

    /// Put a new child straight after its parent, in constant time.
    pub fn derive(&mut self, c: usize, slot: usize, kind: NodeKind)
        requires
            old(self).wf(),
            old(self).valid(slot),
            0 <= c < old(self).nodes@.len(),
            old(self).nodes@[c as int].live,
            old(self).nodes@[c as int].depth + 1 < usize::MAX,
            0 <= slot < old(self).nodes@.len(),
            !old(self).nodes@[slot as int].live,
            old(self).seq@.len() + 1 < NONE,
        ensures
            final(self).wf(),
            final(self).is_child(c, slot),
            final(self).parent@ == old(self).parent@.insert(slot, c),
            // Only the new node and its neighbours' links change, and no one else's depth.
            forall|i: int| 0 <= i < old(self).nodes@.len() && i != slot ==>
                #[trigger] final(self).nodes@[i].depth == old(self).nodes@[i].depth,
    {
        let ghost pre = *old(self);
        let ghost s = pre.seq@;
        proof {
            lemma_has(s, c);
        }
        let ghost j = choose|j: int| 0 <= j < s.len() && s[j] == c;
        proof {
            assert forall|m: int| 0 <= m < s.len() implies
                0 <= #[trigger] s[m] < pre.nodes@.len() && s[m] != slot by {
                pre.lemma_link(m);
            }
            pre.lemma_link(j);
            pre.lemma_live_valid(c);
            if j + 1 < s.len() {
                pre.lemma_link(j + 1);
                lemma_nodup(s, j, j + 1);
                pre.lemma_live_valid(s[j + 1]);
            }
        }
        let cn = self.get(c);
        let nx = cn.next;
        self.set(slot, Node { live: true, kind, depth: cn.depth + 1, next: nx, prev: c });
        let mut cu = self.get(c);
        cu.next = slot;
        self.set(c, cu);
        if nx != NONE {
            let mut q = self.get(nx);
            q.prev = slot;
            self.set(nx, q);
        }
        let ghost mid = *self;
        let ghost t = s.insert(j + 1, slot);
        self.seq = Ghost(t);
        self.parent = Ghost(pre.parent@.insert(slot, c));
        proof {
            let me = *self;
            Tree::lemma_store_wf_same_store(mid, me);
            assert forall|m: int| 0 <= m < t.len() implies
                (m <= j ==> t[m] == s[m]) && (m == j + 1 ==> t[m] == slot)
                && (m > j + 1 ==> t[m] == s[m - 1]) by {}
            assert forall|i: int| 0 <= i < pre.nodes@.len() && i != slot implies
                #[trigger] me.nodes@[i].depth == pre.nodes@[i].depth
                && me.nodes@[i].live == pre.nodes@[i].live by {}
            lemma_insert_no_dup(s, j + 1, slot);
            lemma_linked_insert(pre, me, c, slot, j);
            assert(t[j + 1] == slot);
            assert(t.contains(slot));
            assert forall|i: int| 0 <= i < me.nodes@.len() && #[trigger] me.nodes@[i].live
                implies has(t, i as usize) by {
                lemma_has(t, i as usize);
                if i == slot as int {
                    assert(t[j + 1] == slot);
                } else {
                    assert(pre.nodes@[i].live);
                    lemma_has(s, i as usize);
                    let a = choose|a: int| 0 <= a < s.len() && s[a] == i as usize;
                    let b = if a <= j { a } else { a + 1 };
                    assert(t[b] == i as usize);
                }
            }
            assert(me.links());
            lemma_derive_order(pre, me, c, slot, j);
        }
    }

    /// Unlink a node with no children, in constant time. Its place in the list goes away and
    /// nothing else moves, so every other node keeps its parent, its depth and its run.
    pub fn remove_leaf(&mut self, i: usize)
        requires
            old(self).wf(),
            0 <= i < old(self).nodes@.len(),
            old(self).nodes@[i as int].live,
            i != old(self).seq@[0],
            old(self).nodes@[i as int].next == NONE
                || old(self).d(old(self).nodes@[i as int].next) <= old(self).d(i),
        ensures
            final(self).wf(),
            final(self).nodes@.len() == old(self).nodes@.len(),
            !final(self).nodes@[i as int].live,
            forall|x: int| 0 <= x < old(self).nodes@.len() && x != i ==>
                #[trigger] final(self).nodes@[x].live == old(self).nodes@[x].live,
            forall|x: int| 0 <= x < old(self).nodes@.len() ==>
                #[trigger] final(self).nodes@[x].depth == old(self).nodes@[x].depth,
            final(self).parent@ == old(self).parent@,
            exists|p: int| 0 <= p < old(self).seq@.len() && old(self).seq@[p] == i
                && final(self).seq@ == old(self).seq@.remove(p),
    {
        let ghost pre = *old(self);
        let ghost s = pre.seq@;
        proof {
            lemma_has(s, i);
        }
        let ghost k = choose|k: int| 0 <= k < s.len() && s[k] == i;
        proof {
            assert forall|m: int| 0 <= m < s.len() implies 0 <= #[trigger] s[m] < pre.nodes@.len() by {
                pre.lemma_link(m);
            }
            assert(k != 0);
            pre.lemma_link(k);
            pre.lemma_link(k - 1);
            lemma_nodup(s, k - 1, k);
            pre.lemma_live_valid(i);
            pre.lemma_live_valid(s[k - 1]);
            if k + 1 < s.len() {
                pre.lemma_link(k + 1);
                lemma_nodup(s, k + 1, k);
                lemma_nodup(s, k + 1, k - 1);
                pre.lemma_live_valid(s[k + 1]);
            }
            pre.lemma_no_child(i, k);
        }
        let n = self.get(i);
        let pv = n.prev;
        let nx = n.next;
        let mut p = self.get(pv);
        p.next = nx;
        self.set(pv, p);
        if nx != NONE {
            let mut q = self.get(nx);
            q.prev = pv;
            self.set(nx, q);
        }
        let mut m = self.get(i);
        m.live = false;
        self.set(i, m);
        let ghost mid = *self;
        let ghost t = s.remove(k);
        self.seq = Ghost(t);
        proof {
            let me = *self;
            Tree::lemma_store_wf_same_store(mid, me);
            assert(t.len() == s.len() - 1);
            assert forall|m: int| 0 <= m < t.len() implies
                (m < k ==> t[m] == s[m]) && (m >= k ==> t[m] == s[m + 1]) by {}
            assert forall|x: int| 0 <= x < pre.nodes@.len() && x != i implies
                #[trigger] me.nodes@[x].live == pre.nodes@[x].live by {}
            assert forall|x: int| 0 <= x < pre.nodes@.len() implies
                #[trigger] me.nodes@[x].depth == pre.nodes@[x].depth by {}
            lemma_remove_no_dup(s, k);
            assert(me.linked()) by {
                reveal(Tree::linked);
                assert forall|m: int| 0 <= m < t.len() implies
                    0 <= #[trigger] t[m] < me.nodes@.len() && me.nodes@[t[m] as int].live by {
                    let a = if m < k { m } else { m + 1 };
                    assert(t[m] == s[a]);
                    lemma_nodup(s, a, k);
                }
                assert(t[0] == s[0]);
                if k + 1 == s.len() {
                    assert(t[t.len() - 1] == s[k - 1]);
                } else {
                    assert(t[t.len() - 1] == s[s.len() - 1]);
                }
                assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && b == a + 1 implies
                    me.nodes@[#[trigger] t[a] as int].next == #[trigger] t[b]
                    && me.nodes@[t[b] as int].prev == t[a] by {
                    if a == k - 1 {
                        assert(t[a] == s[k - 1] && t[b] == s[k + 1]);
                    } else {
                        let x = if a < k { a } else { a + 1 };
                        assert(t[a] == s[x] && t[b] == s[x + 1]);
                        lemma_nodup(s, x, k);
                        lemma_nodup(s, x + 1, k);
                    }
                }
            }
            assert forall|x: int| 0 <= x < me.nodes@.len() && #[trigger] me.nodes@[x].live
                implies has(t, x as usize) by {
                assert(x != i);
                assert(pre.nodes@[x].live);
                lemma_has(s, x as usize);
                lemma_has(t, x as usize);
                let a = choose|a: int| 0 <= a < s.len() && s[a] == x as usize;
                assert(a != k);
                let b = if a < k { a } else { a - 1 };
                assert(t[b] == x as usize);
            }
            assert(me.links());
            lemma_remove_order(pre, me, i, k);
        }
    }

    /// One step of revoking c: walk down c's run to a node with no children and unlink it. The
    /// walk is bounded by the run; the list shrinks by one each step, so revocation terminates.
    /// `done` means c has no children and nothing changed.
    pub fn revoke_step(&mut self, c: usize) -> (done: bool)
        requires
            old(self).wf(),
            0 <= c < old(self).nodes@.len(),
            old(self).nodes@[c as int].live,
        ensures
            final(self).wf(),
            final(self).nodes@.len() == old(self).nodes@.len(),
            final(self).parent@ == old(self).parent@,
            final(self).nodes@[c as int].live,
            forall|x: int| 0 <= x < old(self).nodes@.len() ==>
                #[trigger] final(self).nodes@[x].depth == old(self).nodes@[x].depth,
            done ==> final(self).nodes@ == old(self).nodes@ && final(self).seq@ == old(self).seq@
                && forall|i: usize| !#[trigger] final(self).is_child(c, i),
            !done ==> final(self).seq@.len() == old(self).seq@.len() - 1
                && exists|r: usize| #[trigger] revoked_one(*old(self), *final(self), c, r),
    {
        let ghost pre = *old(self);
        let ghost s = pre.seq@;
        proof {
            lemma_has(s, c);
        }
        let ghost j = choose|j: int| 0 <= j < s.len() && s[j] == c;
        proof {
            pre.lemma_link(j);
            pre.lemma_live_valid(c);
            if j + 1 < s.len() {
                pre.lemma_link(j + 1);
                pre.lemma_live_valid(s[j + 1]);
            }
        }
        let mut cur = c;
        let ghost mut k = j;
        while self.get(cur).next != NONE
            && self.get(self.get(cur).next).depth > self.get(cur).depth
            invariant
                pre.wf(),
                *self == pre,
                s == pre.seq@,
                0 <= j < s.len(),
                s[j] == c,
                j <= k < s.len(),
                s[k] == cur,
                0 <= cur < pre.nodes@.len(),
                pre.valid(cur),
                pre.nodes@[cur as int].next == (if k + 1 < s.len() { s[k + 1] } else { NONE }),
                k + 1 < s.len() ==> 0 <= s[k + 1] < pre.nodes@.len() && pre.valid(s[k + 1]),
                forall|m: int| j < m <= k ==> pre.d(#[trigger] s[m]) > pre.d(c),
            decreases s.len() - k,
        {
            cur = self.get(cur).next;
            proof {
                k = k + 1;
                pre.lemma_link(k);
                pre.lemma_live_valid(cur);
                if k + 1 < s.len() {
                    pre.lemma_link(k + 1);
                    pre.lemma_live_valid(s[k + 1]);
                }
            }
        }
        proof {
            pre.lemma_no_child(cur, k);
        }
        if cur == c {
            return true;
        }
        proof {
            assert(k != j);
            lemma_nodup(s, k, 0);
            pre.lemma_run_is_lineage(j, k);
            pre.lemma_link(k);
        }
        self.remove_leaf(cur);
        proof {
            lemma_has(s, cur);
            assert(revoked_one(pre, *self, c, cur));
            let p = choose|p: int| 0 <= p < s.len() && s[p] == cur && self.seq@ == s.remove(p);
            assert(self.seq@.len() == s.len() - 1);
        }
        false
    }
}

impl Tree {
    /// A list of one node: the root, at node 0 of a page. This shows the invariant is inhabited.
    pub fn new(root: usize, Tracked(perm): Tracked<PointsTo<NodePage>>) -> (ret: Tree)
        requires
            root % 4096 == 0,
            root + 4096 <= NODE_SPACE,
            perm.addr() == root,
            perm.is_init(),
            perm.value().nodes.wf(),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] perm.value().nodes@[k]).live,
        ensures
            ret.wf(),
            ret.seq@ == seq![root],
            ret.parent@ == Map::<usize, usize>::empty(),
            ret.nodes@[root as int].live,
            ret.nodes@[root as int].depth == 0,
            ret.nodes@[root as int].kind == NodeKind::Capability,
            forall|x: usize| root <= x < root + NODES_PER_PAGE ==> #[trigger] ret.valid(x),
            forall|i: int| 0 <= i < NODE_SPACE && i != root ==> !(#[trigger] ret.nodes@[i]).live,
    {
        let tracked mut pages = Map::<usize, PointsTo<NodePage>>::tracked_empty();
        proof {
            pages.tracked_insert(root, perm);
        }
        let ghost m = pages;
        let ghost one: Seq<usize> = seq![root];
        let ghost nodes = Seq::new(NODE_SPACE as nat, |i: int|
            if m.dom().contains(page_of(i as usize)) && i % 4096 < NODES_PER_PAGE {
                m[page_of(i as usize)].value().nodes@[i % 4096]
            } else {
                dead()
            });
        let mut t = Tree {
            pages: Tracked(pages),
            nodes: Ghost(nodes),
            seq: Ghost(one),
            parent: Ghost(Map::empty()),
        };
        proof {
            assert(t.store_wf()) by {
                reveal(Tree::store_wf);
                assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] t.nodes@[i].live
                    implies t.valid(i as usize) by {
                    assert(t.nodes@[i] == nodes[i]);
                }
            }
            assert(t.valid(root));
        }
        t.set(root, Node { live: true, kind: NodeKind::Capability, depth: 0, next: NONE, prev: NONE });
        proof {
            let me = t;
            let s = me.seq@;
            assert(s.len() == 1 && s[0] == root);
            assert forall|i: int| 0 <= i < NODE_SPACE && i != root
                implies !(#[trigger] me.nodes@[i]).live by {
                assert(me.nodes@[i] == nodes[i]);
                if m.dom().contains(page_of(i as usize)) && i % 4096 < NODES_PER_PAGE {
                    assert(page_of(i as usize) == root);
                    assert(!m[root].value().nodes@[i % 4096].live);
                }
            }
            assert(nodup(s)) by { reveal(nodup); }
            assert(me.linked()) by { reveal(Tree::linked); }
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] me.nodes@[i].live
                implies has(s, i as usize) by {
                lemma_has(s, i as usize);
                assert(i == root);
            }
            assert(me.links());
            assert(me.runs()) by { reveal(Tree::runs); }
            assert(me.order());
            assert forall|x: usize| root <= x < root + NODES_PER_PAGE implies #[trigger] me.valid(x) by {
                assert(x % 4096 == x - root);
                assert(page_of(x) == root);
            }
        }
        t
    }

    /// Hold another page of nodes, every slot of it free.
    pub fn add_page(&mut self, page: usize, Tracked(perm): Tracked<PointsTo<NodePage>>)
        requires
            old(self).wf(),
            !old(self).pages@.dom().contains(page),
            page % 4096 == 0,
            page + 4096 <= NODE_SPACE,
            perm.addr() == page,
            perm.is_init(),
            perm.value().nodes.wf(),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] perm.value().nodes@[k]).live,
        ensures
            final(self).wf(),
            final(self).seq == old(self).seq,
            final(self).parent == old(self).parent,
            final(self).pages@.dom() == old(self).pages@.dom().insert(page),
            forall|i: usize| #[trigger] old(self).valid(i) ==>
                final(self).valid(i) && final(self).nodes@[i as int] == old(self).nodes@[i as int],
            forall|i: int| 0 <= i < NODE_SPACE ==>
                #[trigger] final(self).nodes@[i].live == old(self).nodes@[i].live,
            forall|x: usize| page <= x < page + NODES_PER_PAGE ==>
                #[trigger] final(self).valid(x) && !final(self).nodes@[x as int].live,
    {
        let ghost pre = *old(self);
        proof {
            self.pages.borrow_mut().tracked_insert(page, perm);
        }
        let ghost fresh = self.pages@[page].value().nodes@;
        let ghost nodes = Seq::new(NODE_SPACE as nat, |i: int|
            if page_of(i as usize) == page && i % 4096 < NODES_PER_PAGE {
                fresh[i % 4096]
            } else {
                pre.nodes@[i]
            });
        self.nodes = Ghost(nodes);
        proof {
            let me = *self;
            assert(me.pages@.dom() =~= pre.pages@.dom().insert(page));
            assert forall|i: usize| #[trigger] pre.valid(i) implies
                me.valid(i) && page_of(i) != page && me.nodes@[i as int] == pre.nodes@[i as int] by {
                pre.lemma_valid_bound(i);
            }
            assert(me.store_wf()) by {
                reveal(Tree::store_wf);
                assert forall|x: usize| #[trigger] me.valid(x) implies
                    me.nodes@[x as int] == me.pages@[page_of(x)].value().nodes@[(x % 4096) as int] by {
                    if page_of(x) != page {
                        assert(pre.valid(x));
                    }
                }
                assert forall|x: int| 0 <= x < NODE_SPACE && #[trigger] me.nodes@[x].live
                    implies me.valid(x as usize) by {
                    if page_of(x as usize) == page && x % 4096 < NODES_PER_PAGE {
                        assert(!fresh[x % 4096].live);
                    } else {
                        assert(pre.nodes@[x].live);
                        pre.lemma_live_valid(x as usize);
                    }
                }
            }
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] pre.nodes@[i].live
                implies me.nodes@[i] == pre.nodes@[i] by {
                pre.lemma_live_valid(i as usize);
            }
            assert forall|i: int| 0 <= i < NODE_SPACE implies
                #[trigger] me.nodes@[i].live == pre.nodes@[i].live by {
                if page_of(i as usize) == page && i % 4096 < NODES_PER_PAGE {
                    assert(!fresh[i % 4096].live);
                    if pre.nodes@[i].live {
                        pre.lemma_live_valid(i as usize);
                    }
                }
            }
            lemma_wf_same_live(pre, me);
            assert forall|x: usize| page <= x < page + NODES_PER_PAGE implies
                #[trigger] me.valid(x) && !me.nodes@[x as int].live by {
                assert(x % 4096 == x - page);
                assert(page_of(x) == page);
            }
        }
    }

    /// Give back a page holding no live node, so its block can free. Everything else in the list
    /// stays as it was.
    pub fn remove_page(&mut self, page: usize) -> (ret: Tracked<PointsTo<NodePage>>)
        requires
            old(self).wf(),
            old(self).pages@.dom().contains(page),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] old(self).nodes@[page + k]).live,
        ensures
            final(self).wf(),
            final(self).seq == old(self).seq,
            final(self).parent == old(self).parent,
            final(self).nodes == old(self).nodes,
            final(self).pages@.dom() == old(self).pages@.dom().remove(page),
            forall|p: usize| #[trigger] final(self).pages@.dom().contains(p)
                ==> final(self).pages@[p] == old(self).pages@[p],
            ret@ == old(self).pages@[page],
    {
        let ghost pre = *old(self);
        let tracked perm;
        proof {
            perm = self.pages.borrow_mut().tracked_remove(page);
            let me = *self;
            assert(me.pages@ =~= pre.pages@.remove(page));
            assert(me.store_wf()) by {
                reveal(Tree::store_wf);
                assert forall|x: usize| #[trigger] me.valid(x) implies
                    me.nodes@[x as int] == me.pages@[page_of(x)].value().nodes@[(x % 4096) as int] by {
                    assert(pre.valid(x));
                }
                assert forall|x: int| 0 <= x < NODE_SPACE && #[trigger] me.nodes@[x].live
                    implies me.valid(x as usize) by {
                    pre.lemma_live_valid(x as usize);
                    if page_of(x as usize) == page {
                        assert(x == page + x % 4096);
                        assert(!pre.nodes@[page + x % 4096].live);
                    }
                }
            }
            lemma_wf_same_live(pre, me);
        }
        Tracked(perm)
    }

    /// Rename node i to the free slot, in constant time. It keeps its place in the list, its
    /// depth and its kind, so every run is as it was.
    pub fn move_node(&mut self, i: usize, slot: usize)
        requires
            old(self).wf(),
            0 <= i < old(self).nodes@.len(),
            old(self).nodes@[i as int].live,
            old(self).valid(slot),
            0 <= slot < old(self).nodes@.len(),
            !old(self).nodes@[slot as int].live,
            i != slot,
        ensures
            final(self).wf(),
            !final(self).nodes@[i as int].live,
            final(self).nodes@[slot as int].live,
            final(self).nodes@[slot as int].depth == old(self).nodes@[i as int].depth,
            final(self).nodes@[slot as int].kind == old(self).nodes@[i as int].kind,
            exists|p: int| 0 <= p < old(self).seq@.len() && #[trigger] old(self).seq@[p] == i
                && final(self).seq@ == old(self).seq@.update(p, slot),
            final(self).parent@ == moved_parent(old(self).parent@, i, slot),
            old(self).parent@.contains_key(i) ==>
                final(self).parent@.contains_key(slot)
                && final(self).parent@[slot] == rename(old(self).parent@[i], i, slot),
            i != old(self).seq@[0] ==> final(self).parent@[slot] == old(self).parent@[i],
            forall|x: usize| x != i && x != slot && #[trigger] old(self).parent@.contains_key(x) ==>
                final(self).parent@.contains_key(x)
                && final(self).parent@[x] == rename(old(self).parent@[x], i, slot),
            forall|x: int| 0 <= x < NODE_SPACE && x != i && x != slot ==>
                #[trigger] final(self).nodes@[x].live == old(self).nodes@[x].live
                && final(self).nodes@[x].depth == old(self).nodes@[x].depth,
    {
        let ghost pre = *old(self);
        let ghost s = pre.seq@;
        proof {
            lemma_has(s, i);
        }
        let ghost p = choose|p: int| 0 <= p < s.len() && s[p] == i;
        proof {
            assert forall|m: int| 0 <= m < s.len() implies
                0 <= #[trigger] s[m] < pre.nodes@.len() && s[m] != slot by {
                pre.lemma_link(m);
            }
            pre.lemma_link(p);
            pre.lemma_live_valid(i);
            if p > 0 {
                pre.lemma_link(p - 1);
                lemma_nodup(s, p - 1, p);
                pre.lemma_live_valid(s[p - 1]);
            }
            if p + 1 < s.len() {
                pre.lemma_link(p + 1);
                lemma_nodup(s, p + 1, p);
                pre.lemma_live_valid(s[p + 1]);
                if p > 0 {
                    lemma_nodup(s, p - 1, p + 1);
                }
            }
        }
        let n = self.get(i);
        self.set(slot, n);
        let mut gone = n;
        gone.live = false;
        self.set(i, gone);
        if n.prev != NONE {
            let mut q = self.get(n.prev);
            q.next = slot;
            self.set(n.prev, q);
        }
        if n.next != NONE {
            let mut q = self.get(n.next);
            q.prev = slot;
            self.set(n.next, q);
        }
        let ghost mid = *self;
        let ghost t = s.update(p, slot);
        self.seq = Ghost(t);
        self.parent = Ghost(moved_parent(pre.parent@, i, slot));
        proof {
            let me = *self;
            Tree::lemma_store_wf_same_store(mid, me);
            assert(me.nodes@[slot as int] == pre.nodes@[i as int]);
            assert(me.nodes@[i as int] == gone);
            assert forall|x: int| 0 <= x < NODE_SPACE && x != slot implies
                #[trigger] me.nodes@[x].depth == pre.nodes@[x].depth
                && me.nodes@[x].kind == pre.nodes@[x].kind by {}
            assert forall|x: int| 0 <= x < NODE_SPACE && x != i && x != slot implies
                #[trigger] me.nodes@[x].live == pre.nodes@[x].live by {}
            lemma_update_no_dup(s, p, slot);
            lemma_linked_move(pre, me, i, slot, p);
            assert forall|x: int| 0 <= x < NODE_SPACE && #[trigger] me.nodes@[x].live
                implies has(t, x as usize) by {
                lemma_has(t, x as usize);
                if x == slot as int {
                    assert(t[p] == slot);
                } else {
                    assert(x != i);
                    assert(pre.nodes@[x].live);
                    lemma_has(s, x as usize);
                    let a = choose|a: int| 0 <= a < s.len() && s[a] == x as usize;
                    assert(a != p);
                    assert(t[a] == x as usize);
                }
            }
            assert(me.links());
            lemma_move_order(pre, me, i, slot, p);
            assert(me.parent@ == moved_parent(pre.parent@, i, slot));
            if i != s[0] {
                assert(p != 0);
                lemma_has(s, pre.parent@[i]);
                let a = choose|a: int| 0 <= a < s.len() && s[a] == pre.parent@[i];
                pre.lemma_runs(a, p);
                lemma_nodup(s, a, p);
                assert(pre.parent@[i] != i);
            }
            assert forall|x: usize| x != i && x != slot && #[trigger] pre.parent@.contains_key(x)
                implies me.parent@.contains_key(x) && me.parent@[x] == rename(pre.parent@[x], i, slot) by {
                assert(rename(x, slot, i) == x);
            }
        }
    }
}

/// What one revoke step does: r, in c's lineage below c, left the list and nothing else did.
pub open spec fn revoked_one(pre: Tree, post: Tree, c: usize, r: usize) -> bool {
    &&& has(pre.seq@, r)
    &&& pre.d(r) > pre.d(c)
    &&& pre.anc(r, (pre.d(r) - pre.d(c)) as nat) == c
    &&& !post.nodes@[r as int].live
    &&& forall|x: int| 0 <= x < pre.nodes@.len() && x != r ==>
        #[trigger] post.nodes@[x].live == pre.nodes@[x].live
    &&& exists|p: int| 0 <= p < pre.seq@.len() && pre.seq@[p] == r
        && post.seq@ == pre.seq@.remove(p)
}

/// A peer's work is untouched: a node outside c's run stays live across a revoke step. Outside
/// the run means before c, or at or after the first node following c that is not deeper than c.
pub proof fn lemma_peer_untouched(pre: Tree, post: Tree, c: usize, r: usize, j: int, q: int)
    requires
        pre.wf(),
        revoked_one(pre, post, c, r),
        0 <= j < pre.seq@.len(),
        pre.seq@[j] == c,
        0 <= q < pre.seq@.len(),
        q < j || exists|e: int| j < e <= q && pre.d(#[trigger] pre.seq@[e]) <= pre.d(c),
    ensures
        post.nodes@[pre.seq@[q] as int].live,
{
    let s = pre.seq@;
    lemma_has(s, r);
    let p = choose|p: int| 0 <= p < s.len() && s[p] == r;
    let n = (pre.d(r) - pre.d(c)) as nat;
    pre.lemma_lineage_is_run(j, p, n);
    if q < j {
        assert(p != q);
    } else {
        let e = choose|e: int| j < e <= q && pre.d(#[trigger] s[e]) <= pre.d(c);
        if p == q {
            assert(pre.d(s[e]) > pre.d(c));
        }
    }
    lemma_nodup(s, p, q);
    pre.lemma_link(q);
}

/// Splicing a node after position j keeps the links: the new node's neighbours are j and j + 1,
/// which now point at it, and every other node keeps its links and neighbours.
proof fn lemma_linked_insert(pre: Tree, me: Tree, c: usize, slot: usize, j: int)
    requires
        pre.linked(),
        nodup(pre.seq@),
        0 <= j < pre.seq@.len(),
        pre.seq@[j] == c,
        me.seq@ == pre.seq@.insert(j + 1, slot),
        forall|m: int| 0 <= m < pre.seq@.len() ==> #[trigger] pre.seq@[m] != slot,
        me.nodes@.len() == pre.nodes@.len(),
        0 <= slot < pre.nodes@.len(),
        0 <= c < pre.nodes@.len(),
        me.nodes@[slot as int].live,
        me.nodes@[slot as int].prev == c,
        me.nodes@[slot as int].next
            == (if j + 1 < pre.seq@.len() { pre.seq@[j + 1] } else { NONE }),
        me.nodes@[c as int].live == pre.nodes@[c as int].live,
        me.nodes@[c as int].next == slot,
        me.nodes@[c as int].prev == pre.nodes@[c as int].prev,
        j + 1 < pre.seq@.len() ==> {
            &&& me.nodes@[pre.seq@[j + 1] as int].live == pre.nodes@[pre.seq@[j + 1] as int].live
            &&& me.nodes@[pre.seq@[j + 1] as int].next == pre.nodes@[pre.seq@[j + 1] as int].next
            &&& me.nodes@[pre.seq@[j + 1] as int].prev == slot
        },
        forall|x: int| 0 <= x < pre.nodes@.len() && x != slot && x != c
            && (j + 1 < pre.seq@.len() ==> x != pre.seq@[j + 1])
            ==> #[trigger] me.nodes@[x] == pre.nodes@[x],
    ensures
        me.linked(),
{
    reveal(Tree::linked);
    let s = pre.seq@;
    let t = me.seq@;
    assert forall|m: int| 0 <= m < t.len() implies
        (m <= j ==> t[m] == s[m]) && (m == j + 1 ==> t[m] == slot)
        && (m > j + 1 ==> t[m] == s[m - 1]) by {}
    if j + 1 < s.len() { lemma_nodup(s, j, j + 1); }
    assert forall|k: int| 0 <= k < t.len() implies
        0 <= #[trigger] t[k] < me.nodes@.len() && me.nodes@[t[k] as int].live by {
        if k != j + 1 {
            let a = if k <= j { k } else { k - 1 };
            assert(t[k] == s[a]);
        }
    }
    assert(t[0] == s[0]);
    if j > 0 { lemma_nodup(s, 0, j); }
    if j + 1 < s.len() { lemma_nodup(s, 0, j + 1); }
    assert(me.nodes@[t[0] as int].prev == NONE);
    if j + 1 == s.len() {
        assert(t[t.len() - 1] == slot);
    } else {
        assert(t[t.len() - 1] == s[s.len() - 1]);
        lemma_nodup(s, s.len() - 1, j);
        if j + 1 < s.len() - 1 { lemma_nodup(s, s.len() - 1, j + 1); }
    }
    assert(me.nodes@[t[t.len() - 1] as int].next == NONE);
    assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && b == a + 1 implies
        me.nodes@[#[trigger] t[a] as int].next == #[trigger] t[b]
        && me.nodes@[t[b] as int].prev == t[a] by {
        if a == j {
            assert(t[a] == c && t[b] == slot);
        } else if a == j + 1 {
            assert(t[a] == slot && t[b] == s[j + 1]);
        } else {
            let x = if a <= j { a } else { a - 1 };
            assert(t[a] == s[x] && t[b] == s[x + 1]);
            lemma_nodup(s, x, j);
            if j + 1 < s.len() {
                lemma_nodup(s, x + 1, j + 1);
                if x != j + 1 { lemma_nodup(s, x, j + 1); }
            }
            if x + 1 != j { lemma_nodup(s, x + 1, j); }
        }
    }
}

proof fn lemma_derive_order(pre: Tree, me: Tree, c: usize, slot: usize, j: int)
    requires
        pre.order(),
        nodup(pre.seq@),
        0 <= j < pre.seq@.len(),
        pre.seq@[j] == c,
        me.seq@ == pre.seq@.insert(j + 1, slot),
        me.parent@ == pre.parent@.insert(slot, c),
        forall|m: int| 0 <= m < pre.seq@.len() ==>
            0 <= #[trigger] pre.seq@[m] < pre.nodes@.len() && pre.seq@[m] != slot,
        me.nodes@.len() == pre.nodes@.len(),
        0 <= slot < pre.nodes@.len(),
        me.nodes@[slot as int].depth == pre.nodes@[c as int].depth + 1,
        forall|i: int| 0 <= i < pre.nodes@.len() && i != slot ==>
            #[trigger] me.nodes@[i].depth == pre.nodes@[i].depth,
    ensures
        me.order(),
{
    let s = pre.seq@;
    let t = me.seq@;
    assert forall|m: int| 0 <= m < t.len() implies
        (m <= j ==> t[m] == s[m]) && (m == j + 1 ==> t[m] == slot)
        && (m > j + 1 ==> t[m] == s[m - 1]) by {}
    assert(t[0] == s[0]);
    lemma_insert_no_dup(s, j + 1, slot);
    assert forall|x: usize| #[trigger] has(s, x) implies has(t, x) && x != slot && me.d(x) == pre.d(x) by {
        lemma_has(s, x);
        lemma_has(t, x);
        let a = choose|a: int| 0 <= a < s.len() && s[a] == x;
        let b = if a <= j { a } else { a + 1 };
        assert(t[b] == x);
    }
    assert forall|k: int| 0 < k < t.len() implies {
        &&& me.parent@.contains_key(#[trigger] t[k])
        &&& has(t, me.parent@[t[k]])
        &&& me.d(t[k]) >= 1
        &&& me.d(t[k]) == me.d(me.parent@[t[k]]) + 1
    } by {
        if k == j + 1 {
            assert(t[k] == slot);
            lemma_has(s, c);
        } else {
            let a = if k <= j { k } else { k - 1 };
            assert(t[k] == s[a]);
            assert(a > 0);
            lemma_has(s, s[a]);
            assert(has(s, pre.parent@[s[a]]));
            assert(me.parent@[s[a]] == pre.parent@[s[a]]);
        }
    }
    assert(me.runs()) by {
        reveal(Tree::runs);
        assert forall|x: int, k: int| 0 <= x < t.len() && 0 < k < t.len()
            && #[trigger] t[x] == me.parent@[#[trigger] t[k]] implies {
            &&& x < k
            &&& forall|m: int| x < m < k ==> me.d(#[trigger] t[m]) > me.d(t[x])
        } by {
            if k == j + 1 {
                assert(t[k] == slot);
                assert(me.parent@[slot] == c);
                assert(t[j] == c);
                if x != j { lemma_nodup(t, x, j); }
                assert(x == j);
            } else if x == j + 1 {
                // Nothing has the new node as a parent yet: it is not in s, so no parent names it.
                let a = if k <= j { k } else { k - 1 };
                assert(t[k] == s[a]);
                assert(me.parent@[s[a]] == pre.parent@[s[a]]);
                assert(a > 0);
                assert(has(s, pre.parent@[s[a]]));
                lemma_has(s, slot);
                assert(false);
            } else {
                let a = if x <= j { x } else { x - 1 };
                let b = if k <= j { k } else { k - 1 };
                assert(t[x] == s[a]);
                assert(t[k] == s[b]);
                assert(b > 0);
                assert(me.parent@[s[b]] == pre.parent@[s[b]]);
                assert(s[a] == pre.parent@[s[b]]);
                pre.lemma_runs(a, b);
                lemma_has(s, s[a]);
                assert forall|m: int| x < m < k implies me.d(#[trigger] t[m]) > me.d(t[x]) by {
                    if m == j + 1 {
                        // The new node sits inside the parent's run, so a <= j.
                        assert(a <= j);
                        if a == j {
                        } else {
                            assert(a < j && j < b);
                            assert(pre.d(s[j]) > pre.d(s[a]));
                        }
                        assert(me.d(slot) == pre.d(c) + 1);
                    } else {
                        let e = if m <= j { m } else { m - 1 };
                        assert(t[m] == s[e]);
                        assert(a < e && e < b);
                        assert(pre.d(s[e]) > pre.d(s[a]));
                        lemma_has(s, s[e]);
                    }
                }
            }
        }
    }
}

/// Removing a node with no children keeps the order: every other node keeps its parent, which is
/// still in the list, and the positions between a parent and its child only lose the leaf.
proof fn lemma_remove_order(pre: Tree, me: Tree, i: usize, k: int)
    requires
        pre.order(),
        nodup(pre.seq@),
        0 < k < pre.seq@.len(),
        pre.seq@[k] == i,
        forall|x: usize| !#[trigger] pre.is_child(i, x),
        me.seq@ == pre.seq@.remove(k),
        me.parent@ == pre.parent@,
        forall|m: int| 0 <= m < pre.seq@.len() ==> 0 <= #[trigger] pre.seq@[m] < pre.nodes@.len(),
        me.nodes@.len() == pre.nodes@.len(),
        forall|x: int| 0 <= x < pre.nodes@.len() ==>
            #[trigger] me.nodes@[x].depth == pre.nodes@[x].depth,
    ensures
        me.order(),
{
    let s = pre.seq@;
    let t = me.seq@;
    assert(t.len() == s.len() - 1);
    assert forall|m: int| 0 <= m < t.len() implies
        (m < k ==> t[m] == s[m]) && (m >= k ==> t[m] == s[m + 1]) by {}
    assert(t[0] == s[0]);
    // Every node of s other than the leaf is in t, at the same depth.
    assert forall|x: usize| #[trigger] has(s, x) && x != i implies has(t, x) && me.d(x) == pre.d(x) by {
        lemma_has(s, x);
        lemma_has(t, x);
        let a = choose|a: int| 0 <= a < s.len() && s[a] == x;
        assert(a != k);
        let b = if a < k { a } else { a - 1 };
        assert(t[b] == x);
    }
    assert forall|m: int| 0 < m < t.len() implies {
        &&& me.parent@.contains_key(#[trigger] t[m])
        &&& has(t, me.parent@[t[m]])
        &&& me.d(t[m]) >= 1
        &&& me.d(t[m]) == me.d(me.parent@[t[m]]) + 1
    } by {
        let a = if m < k { m } else { m + 1 };
        assert(t[m] == s[a]);
        assert(a > 0);
        lemma_nodup(s, a, k);
        lemma_nodup(s, a, 0);
        lemma_has(s, s[a]);
        assert(has(s, s[a]));
        // The leaf is nobody's parent.
        assert(!pre.is_child(i, s[a]));
        assert(pre.parent@[s[a]] != i);
        assert(has(s, pre.parent@[s[a]]));
    }
    assert(me.runs()) by {
        reveal(Tree::runs);
        assert forall|x: int, m: int| 0 <= x < t.len() && 0 < m < t.len()
            && #[trigger] t[x] == me.parent@[#[trigger] t[m]] implies {
            &&& x < m
            &&& forall|q: int| x < q < m ==> me.d(#[trigger] t[q]) > me.d(t[x])
        } by {
            let a = if x < k { x } else { x + 1 };
            let b = if m < k { m } else { m + 1 };
            assert(t[x] == s[a]);
            assert(t[m] == s[b]);
            assert(b > 0);
            assert(s[a] == pre.parent@[s[b]]);
            pre.lemma_runs(a, b);
            lemma_nodup(s, a, k);
            lemma_has(s, s[a]);
            assert forall|q: int| x < q < m implies me.d(#[trigger] t[q]) > me.d(t[x]) by {
                let e = if q < k { q } else { q + 1 };
                assert(t[q] == s[e]);
                assert(a < e && e < b);
                assert(pre.d(s[e]) > pre.d(s[a]));
                lemma_nodup(s, e, k);
                lemma_has(s, s[e]);
            }
        }
    }
}

proof fn lemma_insert_no_dup(s: Seq<usize>, p: int, x: usize)
    requires
        nodup(s),
        0 <= p <= s.len(),
        forall|m: int| 0 <= m < s.len() ==> s[m] != x,
    ensures
        nodup(s.insert(p, x)),
{
    reveal(nodup);
    let t = s.insert(p, x);
    assert forall|a: int, b: int| 0 <= a < b < t.len() implies t[a] != t[b] by {
        let u = if a < p { a } else { a - 1 };
        let v = if b < p { b } else { b - 1 };
        if a != p && b != p { assert(s[u] != s[v]); }
    }
}

proof fn lemma_remove_no_dup(s: Seq<usize>, p: int)
    requires
        nodup(s),
        0 <= p < s.len(),
    ensures
        nodup(s.remove(p)),
{
    reveal(nodup);
    let t = s.remove(p);
    assert forall|a: int, b: int| 0 <= a < b < t.len() implies t[a] != t[b] by {
        let u = if a < p { a } else { a + 1 };
        let v = if b < p { b } else { b + 1 };
        assert(t[a] == s[u]);
        assert(t[b] == s[v]);
        assert(s[u] != s[v]);
    }
}

proof fn lemma_update_no_dup(s: Seq<usize>, p: int, x: usize)
    requires
        nodup(s),
        0 <= p < s.len(),
        forall|m: int| 0 <= m < s.len() ==> s[m] != x,
    ensures
        nodup(s.update(p, x)),
{
    reveal(nodup);
    let t = s.update(p, x);
    assert forall|a: int, b: int| 0 <= a < b < t.len() implies t[a] != t[b] by {
        if a != p && b != p { assert(s[a] != s[b]); }
    }
}

/// The list is well formed whichever free slots a store change touched: the live nodes are as they
/// were, and nothing became live.
proof fn lemma_wf_same_live(pre: Tree, me: Tree)
    requires
        pre.wf(),
        me.seq@ == pre.seq@,
        me.parent@ == pre.parent@,
        me.nodes@.len() == NODE_SPACE,
        me.store_wf(),
        forall|i: int| 0 <= i < NODE_SPACE && #[trigger] pre.nodes@[i].live ==> me.nodes@[i] == pre.nodes@[i],
        forall|i: int| 0 <= i < NODE_SPACE && #[trigger] me.nodes@[i].live ==> pre.nodes@[i].live,
    ensures
        me.wf(),
{
    let s = pre.seq@;
    assert forall|k: int| 0 <= k < s.len() implies
        0 <= #[trigger] s[k] < NODE_SPACE && pre.nodes@[s[k] as int].live
        && me.nodes@[s[k] as int] == pre.nodes@[s[k] as int] by {
        pre.lemma_link(k);
    }
    assert(me.linked()) by {
        reveal(Tree::linked);
        assert(me.nodes@[s[0] as int].prev == NONE);
        assert(me.nodes@[s[s.len() - 1] as int].next == NONE);
        assert forall|a: int, b: int| 0 <= a < s.len() && 0 <= b < s.len() && b == a + 1 implies
            me.nodes@[#[trigger] s[a] as int].next == #[trigger] s[b]
            && me.nodes@[s[b] as int].prev == s[a] by {
            pre.lemma_link(a);
        }
    }
    assert(me.links());
    assert(me.nodes@[s[0] as int].depth == 0);
    assert forall|k: int| 0 < k < s.len() implies {
        &&& me.parent@.contains_key(#[trigger] s[k])
        &&& has(s, me.parent@[s[k]])
        &&& me.d(s[k]) >= 1
        &&& me.d(s[k]) == me.d(me.parent@[s[k]]) + 1
    } by {
        lemma_has(s, pre.parent@[s[k]]);
        let a = choose|a: int| 0 <= a < s.len() && s[a] == pre.parent@[s[k]];
        assert(me.d(s[a]) == pre.d(s[a]));
    }
    assert(me.runs()) by {
        reveal(Tree::runs);
        assert forall|j: int, k: int| 0 <= j < s.len() && 0 < k < s.len()
            && #[trigger] s[j] == me.parent@[#[trigger] s[k]] implies {
            &&& j < k
            &&& forall|m: int| j < m < k ==> me.d(#[trigger] s[m]) > me.d(s[j])
        } by {
            pre.lemma_runs(j, k);
            assert forall|m: int| j < m < k implies me.d(#[trigger] s[m]) > me.d(s[j]) by {
                assert(me.d(s[m]) == pre.d(s[m]));
            }
        }
    }
}

/// Renaming i to slot keeps the links: slot takes i's neighbours, which now name it, and every
/// other node keeps its links and neighbours.
proof fn lemma_linked_move(pre: Tree, me: Tree, i: usize, slot: usize, p: int)
    requires
        pre.linked(),
        nodup(pre.seq@),
        0 <= p < pre.seq@.len(),
        pre.seq@[p] == i,
        me.seq@ == pre.seq@.update(p, slot),
        forall|m: int| 0 <= m < pre.seq@.len() ==> #[trigger] pre.seq@[m] != slot,
        me.nodes@.len() == pre.nodes@.len(),
        0 <= slot < pre.nodes@.len(),
        0 <= i < pre.nodes@.len(),
        me.nodes@[slot as int].live,
        me.nodes@[slot as int].next == pre.nodes@[i as int].next,
        me.nodes@[slot as int].prev == pre.nodes@[i as int].prev,
        p > 0 ==> {
            &&& me.nodes@[pre.seq@[p - 1] as int].live == pre.nodes@[pre.seq@[p - 1] as int].live
            &&& me.nodes@[pre.seq@[p - 1] as int].prev == pre.nodes@[pre.seq@[p - 1] as int].prev
            &&& me.nodes@[pre.seq@[p - 1] as int].next == slot
        },
        p + 1 < pre.seq@.len() ==> {
            &&& me.nodes@[pre.seq@[p + 1] as int].live == pre.nodes@[pre.seq@[p + 1] as int].live
            &&& me.nodes@[pre.seq@[p + 1] as int].next == pre.nodes@[pre.seq@[p + 1] as int].next
            &&& me.nodes@[pre.seq@[p + 1] as int].prev == slot
        },
        forall|x: int| 0 <= x < pre.nodes@.len() && x != slot && x != i
            && (p > 0 ==> x != pre.seq@[p - 1])
            && (p + 1 < pre.seq@.len() ==> x != pre.seq@[p + 1])
            ==> #[trigger] me.nodes@[x] == pre.nodes@[x],
    ensures
        me.linked(),
{
    reveal(Tree::linked);
    let s = pre.seq@;
    let t = me.seq@;
    assert(t.len() == s.len());
    assert forall|m: int| 0 <= m < t.len() implies
        (m != p ==> t[m] == s[m]) && (m == p ==> t[m] == slot) by {}
    assert forall|k: int| 0 <= k < t.len() implies
        0 <= #[trigger] t[k] < me.nodes@.len() && me.nodes@[t[k] as int].live by {
        if k != p {
            lemma_nodup(s, k, p);
            if p > 0 && k != p - 1 { lemma_nodup(s, k, p - 1); }
            if p + 1 < s.len() && k != p + 1 { lemma_nodup(s, k, p + 1); }
        }
    }
    if p != 0 {
        lemma_nodup(s, 0, p);
        if p + 1 < s.len() { lemma_nodup(s, 0, p + 1); }
        if p - 1 != 0 { lemma_nodup(s, 0, p - 1); }
    }
    assert(me.nodes@[t[0] as int].prev == NONE);
    let l = s.len() - 1;
    if p != l {
        lemma_nodup(s, l, p);
        if p > 0 && l != p - 1 { lemma_nodup(s, l, p - 1); }
        if l != p + 1 { lemma_nodup(s, l, p + 1); }
    }
    assert(me.nodes@[t[l] as int].next == NONE);
    assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && b == a + 1 implies
        me.nodes@[#[trigger] t[a] as int].next == #[trigger] t[b]
        && me.nodes@[t[b] as int].prev == t[a] by {
        if a == p {
            assert(t[a] == slot && t[b] == s[p + 1]);
        } else if b == p {
            assert(t[a] == s[p - 1] && t[b] == slot);
        } else {
            assert(t[a] == s[a] && t[b] == s[b]);
            lemma_nodup(s, a, p);
            lemma_nodup(s, b, p);
            if p > 0 {
                lemma_nodup(s, a, p - 1);
                if b != p - 1 { lemma_nodup(s, b, p - 1); }
            }
            if p + 1 < s.len() {
                lemma_nodup(s, b, p + 1);
                if a != p + 1 { lemma_nodup(s, a, p + 1); }
            }
        }
    }
}

/// Renaming i to slot keeps the order: every listed node keeps its depth under the new name, and
/// the parent map is the old one under the new names.
proof fn lemma_move_order(pre: Tree, me: Tree, i: usize, slot: usize, p: int)
    requires
        pre.order(),
        nodup(pre.seq@),
        0 <= p < pre.seq@.len(),
        pre.seq@[p] == i,
        me.seq@ == pre.seq@.update(p, slot),
        me.parent@ == moved_parent(pre.parent@, i, slot),
        forall|m: int| 0 <= m < pre.seq@.len() ==>
            0 <= #[trigger] pre.seq@[m] < pre.nodes@.len() && pre.seq@[m] != slot,
        me.nodes@.len() == pre.nodes@.len(),
        0 <= slot < pre.nodes@.len(),
        me.nodes@[slot as int].depth == pre.nodes@[i as int].depth,
        forall|x: int| 0 <= x < pre.nodes@.len() && x != slot ==>
            #[trigger] me.nodes@[x].depth == pre.nodes@[x].depth,
    ensures
        me.order(),
{
    let s = pre.seq@;
    let t = me.seq@;
    assert(t.len() == s.len());
    assert forall|m: int| 0 <= m < s.len() implies #[trigger] t[m] == rename(s[m], i, slot) by {
        if m != p { lemma_nodup(s, m, p); }
    }
    // Every listed node is listed under its new name, at its old depth.
    assert forall|x: usize| #[trigger] has(s, x) implies
        has(t, rename(x, i, slot)) && me.d(rename(x, i, slot)) == pre.d(x) by {
        lemma_has(s, x);
        lemma_has(t, rename(x, i, slot));
        let a = choose|a: int| 0 <= a < s.len() && s[a] == x;
        assert(t[a] == rename(x, i, slot));
    }
    lemma_has(s, s[0]);
    assert(me.nodes@[t[0] as int].depth == 0);
    assert forall|k: int| 0 < k < t.len() implies {
        &&& me.parent@.contains_key(#[trigger] t[k])
        &&& has(t, me.parent@[t[k]])
        &&& me.d(t[k]) >= 1
        &&& me.d(t[k]) == me.d(me.parent@[t[k]]) + 1
    } by {
        lemma_has(s, s[k]);
        let q = pre.parent@[s[k]];
        assert(has(s, q));
        assert(me.parent@.contains_key(t[k]));
        assert(me.parent@[t[k]] == rename(q, i, slot));
    }
    assert(me.runs()) by {
        reveal(Tree::runs);
        assert forall|j: int, k: int| 0 <= j < t.len() && 0 < k < t.len()
            && #[trigger] t[j] == me.parent@[#[trigger] t[k]] implies {
            &&& j < k
            &&& forall|m: int| j < m < k ==> me.d(#[trigger] t[m]) > me.d(t[j])
        } by {
            lemma_has(s, s[j]);
            lemma_has(s, s[k]);
            let q = pre.parent@[s[k]];
            assert(has(s, q));
            lemma_has(s, q);
            assert(me.parent@[t[k]] == rename(q, i, slot));
            assert(s[j] == q);
            pre.lemma_runs(j, k);
            assert forall|m: int| j < m < k implies me.d(#[trigger] t[m]) > me.d(t[j]) by {
                lemma_has(s, s[m]);
            }
        }
    }
}

/// The invariant is not vacuous: a root with one derived child, which sits in the root's run.
fn root_and_child(root: usize, Tracked(perm): Tracked<PointsTo<NodePage>>)
    requires
        root % 4096 == 0,
        root + 4096 <= NODE_SPACE,
        perm.addr() == root,
        perm.is_init(),
        perm.value().nodes.wf(),
        forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] perm.value().nodes@[k]).live,
{
    let mut t = Tree::new(root, Tracked(perm));
    let child = root + 1;
    t.derive(root, child, NodeKind::Capability);
    proof {
        let s = t.seq@;
        assert(t.is_child(root, child));
        let k = choose|k: int| 0 <= k < s.len() && s[k] == child;
        assert(k != 0);
        assert(has(s, t.parent@[s[k]]));
        lemma_has(s, root);
        let j = choose|j: int| 0 <= j < s.len() && s[j] == root;
        t.lemma_runs(j, k);
        assert(j < k);
        assert(t.d(child) == 1);
    }
}

} // verus!
