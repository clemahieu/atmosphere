//! Reach: what a process can get at, and the relation every kernel operation must keep to. The
//! security theorem is stated over these, so a capability operation's spec is written to `discharges`
//! rather than retrofitted. See the design on atmo-6x9.6.7, section 15, and the answers on
//! atmo-6x9.6.10, atmo-6x9.6.11 and atmo-6x9.6.13.
//!
//! This is a spec with no executable code. Each operation's leaf maps the kernel's state to `State`
//! and ensures `discharges` of its step. Reach is spatial: run queues and kernel lists are not in
//! `contents`, because no process can read them directly, and what a process observes through status
//! codes, timing or a refused retype is outside this theorem.
use vstd::prelude::*;

verus! {

/// A page's address. An object is named by the base of its block.
pub type ObjectId = usize;

/// A list node's id, as in capability::list.
pub type NodeId = usize;

/// The 2M block `example`'s capability covers, and the first page past it.
pub const EXAMPLE_BASE: usize = 0x200000;
pub const EXAMPLE_PAST: usize = 0x400000;

#[derive(PartialEq, Eq)]
pub enum Right {
    Read,
    Write,
    Execute,
    Retype,
    Send,
    Receive,
    Grant,
    Control,
}

pub ghost struct State {
    /// (process, capability): the process holds that capability in a slot.
    pub held: ISet<(ObjectId, NodeId)>,
    /// The object each live capability names. Only capabilities are here, not other list nodes.
    pub names: IMap<NodeId, ObjectId>,
    /// How many pages each live capability's block has, from the page it names.
    pub pages: IMap<NodeId, nat>,
    pub rights: ISet<(NodeId, Right)>,
    /// The list's parent map, so every capability is in some lineage.
    pub parent: Map<NodeId, NodeId>,
    /// (process, frame): one of the process's address spaces maps the frame.
    pub maps: Set<(ObjectId, ObjectId)>,
    /// The process each thread belongs to.
    pub process_of: Map<ObjectId, ObjectId>,
    /// (endpoint or notification, thread): the thread is blocked waiting on it.
    pub waiting: Set<(ObjectId, ObjectId)>,
    /// The caller bound to each reply.
    pub bound: Map<ObjectId, ObjectId>,
    pub dead: Set<ObjectId>,
    /// What a process can see of an object: a frame's bytes, a thread's registers, a notification's
    /// word.
    pub contents: spec_fn(ObjectId) -> Seq<u8>,
}

impl State {
    pub open spec fn holds(self, p: ObjectId, c: NodeId) -> bool {
        self.held.contains((p, c))
    }

    /// c is a live capability p holds with this right.
    pub open spec fn holds_right(self, p: ObjectId, c: NodeId, right: Right) -> bool {
        &&& self.holds(p, c)
        &&& self.names.contains_key(c)
        &&& self.rights.contains((c, right))
    }

    /// n is k links below c in its lineage.
    pub open spec fn descends(self, c: NodeId, n: NodeId, k: nat) -> bool
        decreases k,
    {
        if k == 0 {
            c == n
        } else {
            self.parent.contains_key(n) && self.descends(c, self.parent[n], (k - 1) as nat)
        }
    }

    /// p's capabilities cover o, or capabilities descended from them do, or p's spaces map it, a
    /// mapping being a hardware copy.
    pub open spec fn direct(self, p: ObjectId, o: ObjectId) -> bool {
        ||| exists|c: NodeId, n: NodeId, k: nat| #[trigger] self.descends(c, n, k) && self.holds(p, c)
            && self.covers(n, o)
        ||| self.maps.contains((p, o))
    }

    /// o is a page of the block capability n names.
    pub open spec fn covers(self, n: NodeId, o: ObjectId) -> bool {
        &&& self.names.contains_key(n)
        &&& self.pages.contains_key(n)
        &&& o % 4096 == 0
        &&& self.names[n] <= o < self.names[n] + self.pages[n] * 4096
    }

    /// The process a control capability over o gives authority over: a thread's process, since
    /// controlling a thread can make it invoke that process's capabilities.
    pub open spec fn process_behind(self, o: ObjectId) -> ObjectId {
        if self.process_of.contains_key(o) {
            self.process_of[o]
        } else {
            o
        }
    }

    /// a holds a control capability over b. Live or dead does not matter: a controller can destroy
    /// and then claim, so what b holds counts until its slots are revoked.
    pub open spec fn controls(self, a: ObjectId, b: ObjectId) -> bool {
        exists|c: NodeId| #[trigger] self.holds_right(a, c, Right::Control)
            && self.process_behind(self.names[c]) == b
    }

    /// k control links lead from a to b.
    pub open spec fn controlled(self, a: ObjectId, b: ObjectId, k: nat) -> bool
        decreases k,
    {
        if k == 0 {
            a == b
        } else {
            exists|m: ObjectId| #[trigger] self.controls(m, b) && self.controlled(a, m, (k - 1) as nat)
        }
    }

    /// The least set containing p and closed under direct reach through control.
    pub open spec fn reach(self, p: ObjectId, o: ObjectId) -> bool {
        exists|q: ObjectId, k: nat| #[trigger] self.controlled(p, q, k) && (o == q || self.direct(q, o))
    }

    /// o's contents differ between the two states.
    pub open spec fn changed(pre: Self, post: Self, o: ObjectId) -> bool {
        (pre.contents)(o) != (post.contents)(o)
    }

    /// n is a capability pre has and post does not.
    pub open spec fn removed(pre: Self, post: Self, n: NodeId) -> bool {
        pre.names.contains_key(n) && !post.names.contains_key(n)
    }
}

/// What one kernel step does. An operation changes objects only by a relation of its kind, not by
/// general write.
pub ghost enum Effect {
    /// A user-mode read or write of a frame.
    Access { frame: ObjectId },
    /// Derive, move within the caller's table, delete, map, unmap and configuration: nothing another
    /// process can see.
    Local,
    /// Start, suspend or set registers through a control capability.
    Control { cap: NodeId, thread: ObjectId },
    /// Deliver words, and perhaps a capability derived or moved from granted, to a waiting receiver.
    Deliver { cap: NodeId, receiver: ObjectId, granted: Option<NodeId> },
    /// Deliver to a reply's bound caller, once.
    Reply { cap: NodeId },
    /// Set bits in a notification, and perhaps wake a waiter.
    Signal { cap: NodeId, waiter: Option<ObjectId> },
    /// One step of revoking cap's descendants.
    Revoke { cap: NodeId },
    /// Mark the target dead through a control capability.
    Destroy { cap: NodeId },
    /// Move one node from a slot of a dead process the caller controls into the caller's table.
    Claim { cap: NodeId, from: NodeId },
    /// Type a free block under an untyped held.
    Retype { untyped: NodeId, object: ObjectId },
    /// Unlink a block's hidden node, or a slice of a dead object's teardown, under an untyped held.
    Teardown { untyped: NodeId, object: ObjectId },
}

/// p has the authority e needs.
pub open spec fn authorized(s: State, p: ObjectId, e: Effect) -> bool {
    match e {
        Effect::Access { frame } => s.maps.contains((p, frame)),
        Effect::Local => true,
        Effect::Control { cap, thread } => s.holds_right(p, cap, Right::Control) && s.names[cap] == thread,
        Effect::Deliver { cap, receiver, granted } => {
            &&& s.holds_right(p, cap, Right::Send)
            &&& s.waiting.contains((s.names[cap], receiver))
            &&& granted is Some ==> {
                &&& s.rights.contains((cap, Right::Grant))
                &&& s.holds(p, granted->0)
                &&& s.names.contains_key(granted->0)
            }
        },
        Effect::Reply { cap } => s.holds(p, cap) && s.names.contains_key(cap) && s.bound.contains_key(s.names[cap]),
        Effect::Signal { cap, waiter } => {
            &&& s.holds_right(p, cap, Right::Send)
            &&& waiter is Some ==> s.waiting.contains((s.names[cap], waiter->0))
        },
        Effect::Revoke { cap } => s.holds(p, cap) && s.names.contains_key(cap),
        Effect::Destroy { cap } => s.holds_right(p, cap, Right::Control),
        Effect::Claim { cap, from } => {
            &&& s.holds_right(p, cap, Right::Control)
            &&& s.dead.contains(s.process_behind(s.names[cap]))
            &&& s.holds(s.process_behind(s.names[cap]), from)
            &&& s.names.contains_key(from)
        },
        Effect::Retype { untyped, object } | Effect::Teardown { untyped, object } =>
            s.holds_right(p, untyped, Right::Retype),
    }
}

/// e may change what a process can see of o.
pub open spec fn may_change(s: State, e: Effect, o: ObjectId) -> bool {
    match e {
        Effect::Access { frame } => o == frame,
        Effect::Control { thread, .. } => o == thread,
        Effect::Deliver { receiver, .. } => o == receiver,
        Effect::Reply { cap } => o == s.bound[s.names[cap]],
        Effect::Signal { cap, waiter } => o == s.names[cap] || (waiter is Some && o == waiter->0),
        Effect::Retype { object, .. } => o == object,
        Effect::Teardown { object, .. } => s.waiting.contains((object, o)),
        _ => false,
    }
}

/// e may remove capability n from the list.
pub open spec fn may_remove(s: State, p: ObjectId, e: Effect, n: NodeId) -> bool {
    match e {
        Effect::Local => s.holds(p, n),
        Effect::Deliver { granted, .. } => granted == Some(n),
        Effect::Revoke { cap } => exists|k: nat| k > 0 && #[trigger] s.descends(cap, n, k),
        Effect::Claim { from, .. } => n == from,
        Effect::Teardown { object, .. } =>
            exists|c: NodeId, k: nat| #[trigger] s.descends(c, n, k) && s.holds(object, c),
        _ => false,
    }
}

/// e may add o to r's reach. Reach grows only by a grant from a holder or a retype from an untyped
/// held. A claim moves only what the claimer's reach already contains.
pub open spec fn may_grow(s: State, p: ObjectId, e: Effect, r: ObjectId, o: ObjectId) -> bool {
    match e {
        Effect::Deliver { receiver, granted, .. } => {
            &&& granted is Some
            &&& exists|k: nat| #[trigger] s.controlled(r, s.process_behind(receiver), k)
            &&& s.reach(p, o)
        },
        Effect::Retype { untyped, object } => o == object && s.reach(r, s.names[untyped]),
        _ => false,
    }
}

/// What every operation's spec ensures of a step by a thread of p. atmo-6x9.16.16 composes these into
/// the theorem.
pub open spec fn discharges(pre: State, post: State, p: ObjectId, e: Effect) -> bool {
    &&& authorized(pre, p, e)
    &&& forall|o: ObjectId| #[trigger] State::changed(pre, post, o) ==> may_change(pre, e, o)
    &&& forall|n: NodeId| #[trigger] State::removed(pre, post, n) ==> may_remove(pre, p, e, n)
    &&& forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) && !pre.reach(r, o)
        ==> may_grow(pre, p, e, r, o)
}

/// post is pre with capability n added as a child of c, held by p, covering only what c covers. A
/// child with the control right names what c names, since control reads the name alone. `live` says
/// which nodes the list holds, and n is not among them.
pub open spec fn adds_child(pre: State, post: State, p: ObjectId, c: NodeId, n: NodeId, live: spec_fn(NodeId) -> bool) -> bool {
    &&& pre.holds(p, c)
    &&& live(c)
    &&& !live(n)
    &&& forall|h: (ObjectId, NodeId)| #[trigger] pre.held.contains(h) ==> live(h.1)
    &&& forall|x: NodeId| #[trigger] pre.names.contains_key(x) ==> live(x)
    &&& forall|x: NodeId| live(x) && #[trigger] pre.parent.contains_key(x) ==> live(pre.parent[x])
    &&& forall|h: (ObjectId, NodeId)| #[trigger] post.held.contains(h) == (pre.held.contains(h) || h == (p, n))
    &&& post.parent == pre.parent.insert(n, c)
    &&& forall|x: NodeId| x != n ==> {
        &&& #[trigger] post.names.contains_key(x) == pre.names.contains_key(x)
        &&& post.pages.contains_key(x) == pre.pages.contains_key(x)
        &&& pre.names.contains_key(x) ==> post.names[x] == pre.names[x]
        &&& pre.pages.contains_key(x) ==> post.pages[x] == pre.pages[x]
    }
    &&& forall|x: NodeId, r: Right| x != n ==> #[trigger] post.rights.contains((x, r)) == pre.rights.contains((x, r))
    &&& post.rights.contains((n, Right::Control)) ==> {
        &&& pre.rights.contains((c, Right::Control))
        &&& pre.names.contains_key(c)
        &&& post.names[n] == pre.names[c]
    }
    &&& forall|o: ObjectId| #[trigger] post.covers(n, o) ==> pre.covers(c, o)
    &&& post.maps == pre.maps
    &&& post.process_of == pre.process_of
    &&& forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o)
}

/// Walking up from a live node in post walks the same nodes in pre.
proof fn lemma_adds_child_descends(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    top: NodeId,
    x: NodeId,
    k: nat,
)
    requires
        adds_child(pre, post, p, c, n, live),
        post.descends(top, x, k),
        live(x),
    ensures
        pre.descends(top, x, k),
        live(top),
    decreases k,
{
    if k > 0 {
        assert(x != n);
        assert(pre.parent.contains_key(x));
        assert(post.parent[x] == pre.parent[x]);
        assert(live(pre.parent[x]));
        lemma_adds_child_descends(pre, post, p, c, n, live, top, pre.parent[x], (k - 1) as nat);
    }
}

proof fn lemma_adds_child_direct(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    q: ObjectId,
    o: ObjectId,
)
    requires
        adds_child(pre, post, p, c, n, live),
        post.direct(q, o),
    ensures
        pre.direct(q, o),
{
    if !post.maps.contains((q, o)) {
        let (t, x, k) = choose|t: NodeId, x: NodeId, k: nat| #[trigger] post.descends(t, x, k)
            && post.holds(q, t) && post.covers(x, o);
        assert(post.held.contains((q, t)));
        if x == n {
            assert(pre.covers(c, o));
            if k == 0 {
                assert(!pre.held.contains((q, n)) || live(n));
                assert(q == p);
                assert(pre.descends(c, c, 0));
            } else {
                assert(post.parent[n] == c);
                lemma_adds_child_descends(pre, post, p, c, n, live, t, c, (k - 1) as nat);
                assert(t != n);
                assert(pre.descends(t, c, (k - 1) as nat));
                assert(pre.held.contains((q, t)));
            }
        } else {
            assert(pre.names.contains_key(x));
            lemma_adds_child_descends(pre, post, p, c, n, live, t, x, k);
            assert(t != n);
            assert(pre.held.contains((q, t)));
            assert(pre.covers(x, o));
            assert(pre.descends(t, x, k));
        }
    }
}

proof fn lemma_adds_child_controlled(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    a: ObjectId,
    b: ObjectId,
    k: nat,
)
    requires
        adds_child(pre, post, p, c, n, live),
        post.controlled(a, b, k),
    ensures
        pre.controlled(a, b, k),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] post.controls(m, b) && post.controlled(a, m, (k - 1) as nat);
        lemma_adds_child_controlled(pre, post, p, c, n, live, a, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] post.holds_right(m, t, Right::Control)
            && post.process_behind(post.names[t]) == b;
        assert(post.held.contains((m, t)));
        if t == n {
            assert(!pre.held.contains((m, n)) || live(n));
            assert(m == p);
            assert(pre.holds_right(p, c, Right::Control));
            assert(pre.process_behind(pre.names[c]) == b);
        } else {
            assert(pre.holds_right(m, t, Right::Control));
            assert(pre.process_behind(pre.names[t]) == b);
        }
        assert(pre.controls(m, b));
    }
}

/// Adding a child that covers only what its parent covers is a local step: nothing changes that a
/// process can see, nothing goes, and nobody's reach grows.
pub proof fn lemma_adds_child_discharges(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
)
    requires
        adds_child(pre, post, p, c, n, live),
    ensures
        discharges(pre, post, p, Effect::Local),
{
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, Effect::Local, x) by {
        assert(x != n);
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
        lemma_adds_child_controlled(pre, post, p, c, n, live, r, q, k);
        if o != q {
            lemma_adds_child_direct(pre, post, p, c, n, live, q, o);
        }
        assert(pre.controlled(r, q, k));
    }
}

/// post is pre without capability n, which p held. Nothing else changes, so the parent map still says
/// what it said.
pub open spec fn removes_cap(pre: State, post: State, p: ObjectId, n: NodeId) -> bool {
    &&& pre.holds(p, n)
    &&& forall|h: (ObjectId, NodeId)| #[trigger] post.held.contains(h) ==> pre.held.contains(h)
    &&& forall|x: NodeId| x != n && #[trigger] pre.names.contains_key(x) ==> post.names.contains_key(x)
    &&& forall|x: NodeId| #[trigger] post.names.contains_key(x) ==> {
        &&& pre.names.contains_key(x)
        &&& post.names[x] == pre.names[x]
    }
    &&& forall|x: NodeId| #[trigger] post.pages.contains_key(x) ==> {
        &&& pre.pages.contains_key(x)
        &&& post.pages[x] == pre.pages[x]
    }
    &&& forall|h: (NodeId, Right)| #[trigger] post.rights.contains(h) ==> pre.rights.contains(h)
    &&& post.parent == pre.parent
    &&& post.maps == pre.maps
    &&& post.process_of == pre.process_of
    &&& forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o)
}

proof fn lemma_removes_cap_controlled(pre: State, post: State, p: ObjectId, n: NodeId, a: ObjectId, b: ObjectId, k: nat)
    requires
        removes_cap(pre, post, p, n),
        post.controlled(a, b, k),
    ensures
        pre.controlled(a, b, k),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] post.controls(m, b) && post.controlled(a, m, (k - 1) as nat);
        lemma_removes_cap_controlled(pre, post, p, n, a, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] post.holds_right(m, t, Right::Control)
            && post.process_behind(post.names[t]) == b;
        assert(post.held.contains((m, t)));
        assert(post.rights.contains((t, Right::Control)));
        assert(pre.holds_right(m, t, Right::Control));
        assert(pre.controls(m, b));
    }
}

/// Removing a capability its holder chose to give up is a local step, and nobody's reach grows.
pub proof fn lemma_removes_cap_discharges(pre: State, post: State, p: ObjectId, n: NodeId)
    requires
        removes_cap(pre, post, p, n),
    ensures
        discharges(pre, post, p, Effect::Local),
{
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, Effect::Local, x) by {
        assert(x == n);
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
        lemma_removes_cap_controlled(pre, post, p, n, r, q, k);
        if o != q && !post.maps.contains((q, o)) {
            let (t, x, d) = choose|t: NodeId, x: NodeId, d: nat| #[trigger] post.descends(t, x, d)
                && post.holds(q, t) && post.covers(x, o);
            lemma_same_parent_same_descends(post, pre, t, x, d);
            assert(post.held.contains((q, t)));
            assert(pre.holds(q, t));
            assert(pre.covers(x, o));
            assert(pre.descends(t, x, d));
        }
        assert(pre.controlled(r, q, k));
    }
}

/// a's authority carries over to b through a renaming f of a's live nodes: whatever a process holds,
/// each capability's block and rights and each live node's parent are in b under the new names.
pub open spec fn simulates(a: State, b: State, live: spec_fn(NodeId) -> bool, f: spec_fn(NodeId) -> NodeId) -> bool {
    &&& forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) ==> live(h.1) && b.held.contains((h.0, f(h.1)))
    &&& forall|x: NodeId| #[trigger] a.names.contains_key(x) ==> {
        &&& live(x)
        &&& b.names.contains_key(f(x))
        &&& b.names[f(x)] == a.names[x]
    }
    &&& forall|x: NodeId| #[trigger] a.pages.contains_key(x) ==> {
        &&& b.pages.contains_key(f(x))
        &&& b.pages[f(x)] == a.pages[x]
    }
    &&& forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) ==> b.rights.contains((f(x), r))
    &&& forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) ==> {
        &&& live(a.parent[x])
        &&& b.parent.contains_key(f(x))
        &&& b.parent[f(x)] == f(a.parent[x])
    }
    &&& a.maps == b.maps
    &&& a.process_of == b.process_of
}

proof fn lemma_simulates_descends(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    top: NodeId,
    x: NodeId,
    k: nat,
)
    requires
        simulates(a, b, live, f),
        a.descends(top, x, k),
        live(x),
    ensures
        b.descends(f(top), f(x), k),
    decreases k,
{
    if k > 0 {
        assert(a.parent.contains_key(x));
        lemma_simulates_descends(a, b, live, f, top, a.parent[x], (k - 1) as nat);
    }
}

proof fn lemma_simulates_controlled(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    r: ObjectId,
    q: ObjectId,
    k: nat,
)
    requires
        simulates(a, b, live, f),
        a.controlled(r, q, k),
    ensures
        b.controlled(r, q, k),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] a.controls(m, q) && a.controlled(r, m, (k - 1) as nat);
        lemma_simulates_controlled(a, b, live, f, r, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] a.holds_right(m, t, Right::Control)
            && a.process_behind(a.names[t]) == q;
        assert(a.held.contains((m, t)));
        assert(a.names.contains_key(t));
        assert(a.rights.contains((t, Right::Control)));
        assert(b.holds_right(m, f(t), Right::Control));
        assert(b.process_behind(b.names[f(t)]) == q);
        assert(b.controls(m, q));
    }
}

/// Anything a process reaches in a it reaches in b.
pub proof fn lemma_simulates_reach(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    r: ObjectId,
    o: ObjectId,
)
    requires
        simulates(a, b, live, f),
        a.reach(r, o),
    ensures
        b.reach(r, o),
{
    let (q, k) = choose|q: ObjectId, k: nat| #[trigger] a.controlled(r, q, k) && (o == q || a.direct(q, o));
    lemma_simulates_controlled(a, b, live, f, r, q, k);
    if o != q && !a.maps.contains((q, o)) {
        let (t, x, d) = choose|t: NodeId, x: NodeId, d: nat| #[trigger] a.descends(t, x, d)
            && a.holds(q, t) && a.covers(x, o);
        assert(a.names.contains_key(x));
        assert(a.pages.contains_key(x));
        assert(a.held.contains((q, t)));
        lemma_simulates_descends(a, b, live, f, t, x, d);
        assert(b.holds(q, f(t)));
        assert(b.covers(f(x), o));
        assert(b.descends(f(t), f(x), d));
    }
    assert(b.controlled(r, q, k));
}

/// Control is transitive: if s controls m and m controls q, s reaches what q directly reaches, since
/// s can destroy m, claim its control over q, and repeat.
pub proof fn lemma_control_transitive(s: State, a: ObjectId, m: ObjectId, q: ObjectId, o: ObjectId)
    requires
        s.controls(a, m),
        s.controls(m, q),
        s.direct(q, o),
    ensures
        s.reach(a, o),
{
    assert(s.controlled(a, a, 0));
    assert(s.controlled(a, m, 1));
    assert(s.controlled(a, q, 2));
}

/// A user-mode access reads or writes only a frame the process's spaces map.
pub proof fn lemma_access_is_mapped(pre: State, post: State, p: ObjectId, frame: ObjectId, o: ObjectId)
    requires
        discharges(pre, post, p, Effect::Access { frame }),
        State::changed(pre, post, o),
    ensures
        o == frame,
        pre.maps.contains((p, o)),
{
}

/// A revoke removes only the revoker's lineage: a peer of the capability is untouched.
pub proof fn lemma_revoke_is_lineage(pre: State, post: State, p: ObjectId, cap: NodeId, n: NodeId)
    requires
        discharges(pre, post, p, Effect::Revoke { cap }),
        State::removed(pre, post, n),
    ensures
        exists|k: nat| k > 0 && #[trigger] pre.descends(cap, n, k),
{
}

/// Only a grant or a retype can add to anyone's reach.
pub proof fn lemma_reach_grows_only_by_grant_or_retype(
    pre: State,
    post: State,
    p: ObjectId,
    e: Effect,
    r: ObjectId,
    o: ObjectId,
)
    requires
        discharges(pre, post, p, e),
        post.reach(r, o),
        !(e is Retype),
        !(e is Deliver && e->Deliver_granted is Some),
    ensures
        pre.reach(r, o),
{
}

/// A state with one process, 1, holding one capability, node 10, on the 2M block at EXAMPLE_BASE, the
/// first page of which it maps.
pub open spec fn example() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 10usize)),
        names: IMap::new(|n: NodeId| n == 10, |n: NodeId| EXAMPLE_BASE),
        pages: IMap::new(|n: NodeId| n == 10, |n: NodeId| 512nat),
        rights: ISet::new(|h: (NodeId, Right)| h.0 == 10 && (h.1 == Right::Read || h.1 == Right::Write)),
        parent: Map::empty(),
        maps: set![(1usize, EXAMPLE_BASE)],
        process_of: Map::empty(),
        waiting: Set::empty(),
        bound: Map::empty(),
        dead: Set::empty(),
        contents: |o: ObjectId| Seq::empty(),
    }
}

/// `example` with a frame written.
pub open spec fn written(frame: ObjectId) -> State {
    State {
        contents: |o: ObjectId| if o == frame { seq![1u8] } else { Seq::empty() },
        ..example()
    }
}

/// The relation is inhabited: a write to a mapped frame discharges it.
pub proof fn lemma_mapped_write_discharges()
    ensures
        discharges(example(), written(EXAMPLE_BASE), 1, Effect::Access { frame: EXAMPLE_BASE }),
{
    let (pre, post, e) = (example(), written(EXAMPLE_BASE), Effect::Access { frame: EXAMPLE_BASE });
    assert(pre.maps.contains((1usize, EXAMPLE_BASE)));
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, e, o) by {
        if o != EXAMPLE_BASE {
            assert((post.contents)(o) =~= (pre.contents)(o));
        }
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_same_authority_same_reach(post, pre, r, o);
    }
}

/// And it excludes something: a write to a frame the process does not map does not discharge it.
pub proof fn lemma_unmapped_write_does_not_discharge()
    ensures
        !discharges(example(), written(EXAMPLE_PAST), 1, Effect::Access { frame: EXAMPLE_PAST }),
{
    assert(!example().maps.contains((1usize, EXAMPLE_PAST)));
}

/// With no control right in `example`, the only process 1 reaches through is itself.
proof fn lemma_example_controls_nothing(q: ObjectId, k: nat)
    requires
        example().controlled(1, q, k),
    ensures
        q == 1,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] example().controls(m, q)
            && example().controlled(1, m, (k - 1) as nat);
        let c = choose|c: NodeId| #[trigger] example().holds_right(m, c, Right::Control)
            && example().process_behind(example().names[c]) == q;
        assert(!example().rights.contains((c, Right::Control)));
    }
}

/// With no parents in `example`, a capability descends only from itself.
proof fn lemma_example_descends_from_itself(c: NodeId, n: NodeId, k: nat)
    requires
        example().descends(c, n, k),
    ensures
        c == n,
{
}

/// A capability reaches each page of its block and no other: the last page inside, and the pages just
/// past either end, are all decided by this.
pub proof fn lemma_example_reaches_its_block(o: ObjectId)
    requires
        o % 4096 == 0,
    ensures
        example().reach(1, o) == (EXAMPLE_BASE <= o < EXAMPLE_PAST),
{
    let s = example();
    if EXAMPLE_BASE <= o < EXAMPLE_PAST {
        assert(s.descends(10, 10, 0));
        assert(s.holds(1, 10));
        assert(s.direct(1, o));
        assert(s.controlled(1, 1, 0));
    }
    if s.reach(1, o) {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] s.controlled(1, q, k) && (o == q || s.direct(q, o));
        lemma_example_controls_nothing(q, k);
        if !s.maps.contains((1usize, o)) && o != 1 {
            let (c, n, d) = choose|c: NodeId, n: NodeId, d: nat| #[trigger] s.descends(c, n, d)
                && s.holds(1, c) && s.covers(n, o);
            lemma_example_descends_from_itself(c, n, d);
            assert(s.held.contains((1usize, c)));
        }
    }
}

/// Reach reads nothing but the authority fields, so contents do not change it.
proof fn lemma_same_authority_same_reach(a: State, b: State, r: ObjectId, o: ObjectId)
    requires
        a.held == b.held,
        a.names == b.names,
        a.pages == b.pages,
        a.rights == b.rights,
        a.parent == b.parent,
        a.maps == b.maps,
        a.process_of == b.process_of,
        a.reach(r, o),
    ensures
        b.reach(r, o),
{
    let (q, k) = choose|q: ObjectId, k: nat| #[trigger] a.controlled(r, q, k) && (o == q || a.direct(q, o));
    lemma_same_authority_same_controlled(a, b, r, q, k);
    if o != q {
        if a.maps.contains((q, o)) {
        } else {
            let (c, n, d) = choose|c: NodeId, n: NodeId, d: nat| #[trigger] a.descends(c, n, d)
                && a.holds(q, c) && a.covers(n, o);
            lemma_same_parent_same_descends(a, b, c, n, d);
        }
    }
}

proof fn lemma_same_parent_same_descends(a: State, b: State, c: NodeId, n: NodeId, k: nat)
    requires
        a.parent == b.parent,
        a.descends(c, n, k),
    ensures
        b.descends(c, n, k),
    decreases k,
{
    if k > 0 {
        lemma_same_parent_same_descends(a, b, c, a.parent[n], (k - 1) as nat);
    }
}

proof fn lemma_same_authority_same_controlled(a: State, b: State, r: ObjectId, q: ObjectId, k: nat)
    requires
        a.held == b.held,
        a.names == b.names,
        a.rights == b.rights,
        a.process_of == b.process_of,
        a.controlled(r, q, k),
    ensures
        b.controlled(r, q, k),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] a.controls(m, q) && a.controlled(r, m, (k - 1) as nat);
        lemma_same_authority_same_controlled(a, b, r, m, (k - 1) as nat);
        let c = choose|c: NodeId| #[trigger] a.holds_right(m, c, Right::Control)
            && a.process_behind(a.names[c]) == q;
        assert(b.holds_right(m, c, Right::Control));
        assert(b.controls(m, q));
    }
}

} // verus!
