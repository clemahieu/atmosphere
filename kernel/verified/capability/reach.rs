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

/// A block's base address.
pub type ObjectId = usize;

/// A list node's id, as in capability::list.
pub type NodeId = usize;

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
    pub held: Set<(ObjectId, NodeId)>,
    /// The object each live capability names. Only capabilities are here, not other list nodes.
    pub names: Map<NodeId, ObjectId>,
    pub rights: Set<(NodeId, Right)>,
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

    /// p's capabilities name o, or capabilities descended from them do, or p's spaces map it, a
    /// mapping being a hardware copy.
    pub open spec fn direct(self, p: ObjectId, o: ObjectId) -> bool {
        ||| exists|c: NodeId, n: NodeId, k: nat| #[trigger] self.descends(c, n, k) && self.holds(p, c)
            && self.names.contains_key(n) && self.names[n] == o
        ||| self.maps.contains((p, o))
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

/// A state with one process, 1, holding one capability, node 10, on frame 100, which it maps.
pub open spec fn example() -> State {
    State {
        held: set![(1usize, 10usize)],
        names: map![10usize => 100usize],
        rights: set![(10usize, Right::Read), (10usize, Right::Write)],
        parent: Map::empty(),
        maps: set![(1usize, 100usize)],
        process_of: Map::empty(),
        waiting: Set::empty(),
        bound: Map::empty(),
        dead: Set::empty(),
        contents: |o: ObjectId| Seq::empty(),
    }
}

/// `example` with frame 100 written.
pub open spec fn written(frame: ObjectId) -> State {
    State {
        contents: |o: ObjectId| if o == frame { seq![1u8] } else { Seq::empty() },
        ..example()
    }
}

/// The relation is inhabited: a write to a mapped frame discharges it.
pub proof fn lemma_mapped_write_discharges()
    ensures
        discharges(example(), written(100), 1, Effect::Access { frame: 100 }),
{
    let (pre, post, e) = (example(), written(100), Effect::Access { frame: 100 });
    assert(pre.maps.contains((1usize, 100usize)));
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, e, o) by {
        if o != 100 {
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
        !discharges(example(), written(200), 1, Effect::Access { frame: 200 }),
{
    assert(!example().maps.contains((1usize, 200usize)));
}

/// Reach reads nothing but the authority fields, so contents do not change it.
proof fn lemma_same_authority_same_reach(a: State, b: State, r: ObjectId, o: ObjectId)
    requires
        a.held == b.held,
        a.names == b.names,
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
                && a.holds(q, c) && a.names.contains_key(n) && a.names[n] == o;
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
