//! Reach: what a process can get at, and the relation every kernel operation must keep to. The
//! security theorem is stated over these, so a capability operation's spec is written to `discharges`
//! rather than retrofitted. See design/theorem-over-reach/, design/isolation-claim/ and
//! design/sharing-by-derive/.
//!
//! This is a spec with no executable code. Each operation's leaf maps the kernel's state to `State`
//! and ensures `discharges` of its step. Reach is spatial: run queues and kernel lists are not in
//! `contents`, because no process can read them directly, and what a process observes through status
//! codes, timing or a refused retype is outside this theorem.
use vstd::prelude::*;

verus! {

/// A page's address. An object is named by the base of its block.
pub type ObjectId = usize;

/// Devices are objects too, named above the 48-bit address space so that no block of memory covers
/// one: device d is the page DEVICE_OBJECTS + d * 4096.
pub const DEVICE_OBJECTS: usize = 0x1_0000_0000_0000;

pub open spec fn device_object(d: int) -> ObjectId {
    (DEVICE_OBJECTS + d * 4096) as usize
}

/// The console is an object too, named past every device object: the 2^36 pages from DEVICE_OBJECTS
/// are devices' room, and the console is the page after them.
pub const CONSOLE_OBJECT: usize = 0x2_0000_0000_0000;

/// Power, the authority to end the machine's run, is an object too: the page after the console's.
pub const POWER_OBJECT: usize = 0x2_0000_0000_1000;

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

    /// a holds a control capability over b. Live or dead does not matter: a controller can move what
    /// b holds out of b's table, so what b holds counts until its slots are revoked.
    pub open spec fn controls(self, a: ObjectId, b: ObjectId) -> bool {
        exists|c: NodeId| #[trigger] self.holds_right(a, c, Right::Control)
            && self.process_behind(self.names[c]) == b
    }

    /// p may act on capability c as its holder may: p holds it, or holds a control capability over the
    /// process that holds it, not over a thread of that process. One hop, as an operation names a table
    /// position: see design/process-holds-capabilities/.
    pub open spec fn commands(self, p: ObjectId, c: NodeId) -> bool {
        ||| self.holds(p, c)
        ||| exists|v: NodeId| #[trigger] self.holds_right(p, v, Right::Control)
            && !self.process_of.contains_key(self.names[v]) && self.holds(self.names[v], c)
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
    /// Derive and move within the caller's table, map, unmap and configuration, which nothing another
    /// process can see, and delete, of a slot the caller commands.
    Local,
    /// Start, suspend or set registers through a control capability.
    Control { cap: NodeId, thread: ObjectId },
    /// Deliver words, and perhaps a capability derived or moved from granted, to a waiting receiver.
    Deliver { cap: NodeId, receiver: ObjectId, granted: Option<NodeId> },
    /// Deliver to a reply's bound caller, once.
    Reply { cap: NodeId },
    /// Set bits in a notification, and perhaps wake a waiter.
    Signal { cap: NodeId, waiter: Option<ObjectId> },
    /// One step of revoking the descendants of cap, which the caller commands.
    Revoke { cap: NodeId },
    /// Mark the target dead through a control capability.
    Destroy { cap: NodeId },
    /// Move one node from a slot of a process the caller controls, live or dead, into the caller's
    /// table: a move whose source is named through cap. It takes control of the process itself, not
    /// of one of its threads.
    Claim { cap: NodeId, from: NodeId },
    /// Put a child derived from `from`, or `from` itself by a move, in a slot of the process cap
    /// names: a grant through control, where Deliver's is through a rendezvous. The caller commands
    /// `from`, and a child is derived only from one it holds. It takes control of the process itself,
    /// not of one of its threads.
    Place { cap: NodeId, from: NodeId },
    /// Type a free block under an untyped held. A table leaf goes into the caller's own table, or
    /// into the table of the process that `into`, a control capability the caller holds, names: the
    /// process itself, not one of its threads.
    Retype { untyped: NodeId, object: ObjectId, into: Option<NodeId> },
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
        Effect::Revoke { cap } => s.commands(p, cap) && s.names.contains_key(cap),
        Effect::Destroy { cap } => s.holds_right(p, cap, Right::Control),
        Effect::Claim { cap, from } => {
            &&& s.holds_right(p, cap, Right::Control)
            &&& !s.process_of.contains_key(s.names[cap])
            &&& s.holds(s.names[cap], from)
            &&& s.names.contains_key(from)
        },
        Effect::Place { cap, from } => {
            &&& s.holds_right(p, cap, Right::Control)
            &&& !s.process_of.contains_key(s.names[cap])
            &&& s.commands(p, from)
            &&& s.names.contains_key(from)
        },
        Effect::Retype { untyped, into, .. } => {
            &&& s.holds_right(p, untyped, Right::Retype)
            &&& into is Some ==> {
                &&& s.holds_right(p, into->0, Right::Control)
                &&& !s.process_of.contains_key(s.names[into->0])
            }
        },
        Effect::Teardown { untyped, .. } => s.holds_right(p, untyped, Right::Retype),
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
        Effect::Local => s.commands(p, n),
        Effect::Deliver { granted, .. } => granted == Some(n),
        Effect::Revoke { cap } => exists|k: nat| k > 0 && #[trigger] s.descends(cap, n, k),
        Effect::Claim { from, .. } | Effect::Place { from, .. } => n == from,
        Effect::Teardown { object, .. } =>
            exists|c: NodeId, k: nat| #[trigger] s.descends(c, n, k) && s.holds(object, c),
        _ => false,
    }
}

/// e may add o to r's reach. Reach grows only by a grant from a holder, over an endpoint to the
/// receiver or through control to the process controlled, or a retype from an untyped held. A claim
/// moves only what the claimer's reach already contains, and a placement gives only what the placer's
/// does.
pub open spec fn may_grow(s: State, p: ObjectId, e: Effect, r: ObjectId, o: ObjectId) -> bool {
    match e {
        Effect::Deliver { receiver, granted, .. } => {
            &&& granted is Some
            &&& exists|k: nat| #[trigger] s.controlled(r, s.process_behind(receiver), k)
            &&& s.reach(p, o)
        },
        Effect::Place { cap, .. } => {
            &&& exists|k: nat| #[trigger] s.controlled(r, s.names[cap], k)
            &&& s.reach(p, o)
        },
        Effect::Retype { untyped, object, .. } => o == object && s.reach(r, s.names[untyped]),
        _ => false,
    }
}

/// A step by p may list thread t as waiting on o, (o, t) being w, only when t is a thread of p and p
/// reaches o, so a delivery or a signal on o wakes only a waiter whose process reached o already.
pub open spec fn may_wait(s: State, p: ObjectId, w: (ObjectId, ObjectId)) -> bool {
    &&& s.process_of.contains_key(w.1)
    &&& s.process_of[w.1] == p
    &&& s.reach(p, w.0)
}

/// x, a capability of post, is s's child, or takes the place of s, which the step removed, naming
/// what s named: a derive's or a move's source.
pub open spec fn passes_right(pre: State, post: State, s: NodeId, x: NodeId) -> bool {
    &&& pre.names.contains_key(s)
    &&& {
        ||| post.parent.contains_key(x) && post.parent[x] == s
        ||| State::removed(pre, post, s) && post.names[x] == pre.names[s]
    }
}

/// e may give x, a capability new in post, the right r. A new capability has only rights its source
/// had: in a local step, the parent it was derived from or the node it was moved from; in a grant, the
/// capability granted; in a placement or a claim, the node named. A retype's new capability, naming the
/// object typed, has what its kind allows, which the retype's own spec says. No other step makes a
/// capability with a right, so none amplifies one: see design/theorem-over-reach/.
pub open spec fn may_hold(pre: State, post: State, e: Effect, x: NodeId, r: Right) -> bool {
    &&& !pre.names.contains_key(x)
    &&& match e {
        Effect::Local => exists|s: NodeId| #[trigger] passes_right(pre, post, s, x) && pre.rights.contains((s, r)),
        Effect::Deliver { granted, .. } => {
            &&& granted is Some
            &&& passes_right(pre, post, granted->0, x)
            &&& pre.rights.contains((granted->0, r))
        },
        Effect::Claim { from, .. } | Effect::Place { from, .. } => {
            &&& passes_right(pre, post, from, x)
            &&& pre.rights.contains((from, r))
        },
        Effect::Retype { object, .. } => post.names[x] == object,
        _ => false,
    }
}

/// Every right a capability of post has, it had as a capability of pre, or e may give it: rights on a
/// capability only shrink, and a new one's come from its source.
pub open spec fn keeps_rights(pre: State, post: State, e: Effect) -> bool {
    forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        ==> (pre.rights.contains((x, r)) && pre.names.contains_key(x)) || may_hold(pre, post, e, x, r)
}

/// What every operation's spec ensures of a step by a thread of p. The theorem in
/// design/theorem-over-reach/ composes these.
pub open spec fn discharges(pre: State, post: State, p: ObjectId, e: Effect) -> bool {
    &&& authorized(pre, p, e)
    &&& forall|o: ObjectId| #[trigger] State::changed(pre, post, o) ==> may_change(pre, e, o)
    &&& forall|n: NodeId| #[trigger] State::removed(pre, post, n) ==> may_remove(pre, p, e, n)
    &&& forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) && !pre.reach(r, o)
        ==> may_grow(pre, p, e, r, o)
    &&& forall|w: (ObjectId, ObjectId)| #[trigger] post.waiting.contains(w) && !pre.waiting.contains(w)
        ==> may_wait(pre, p, w)
    &&& keeps_rights(pre, post, e)
}

/// post lists no thread as waiting that pre does not.
pub open spec fn adds_no_waiter(pre: State, post: State) -> bool {
    forall|w: (ObjectId, ObjectId)| #[trigger] post.waiting.contains(w) ==> pre.waiting.contains(w)
}

/// post is pre with capability n added as a child of c, which p holds, in a slot of d, covering only
/// what c covers. `live` says which nodes the list holds, and n is not among them.
pub open spec fn places_node(
    pre: State,
    post: State,
    p: ObjectId,
    d: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
) -> bool {
    &&& pre.holds(p, c)
    &&& live(c)
    &&& !live(n)
    &&& forall|h: (ObjectId, NodeId)| #[trigger] pre.held.contains(h) ==> live(h.1)
    &&& forall|x: NodeId| #[trigger] pre.names.contains_key(x) ==> live(x)
    &&& forall|x: NodeId| live(x) && #[trigger] pre.parent.contains_key(x) ==> live(pre.parent[x])
    &&& forall|h: (ObjectId, NodeId)| #[trigger] post.held.contains(h) == (pre.held.contains(h) || h == (d, n))
    &&& post.parent == pre.parent.insert(n, c)
    &&& forall|x: NodeId| x != n ==> {
        &&& #[trigger] post.names.contains_key(x) == pre.names.contains_key(x)
        &&& post.pages.contains_key(x) == pre.pages.contains_key(x)
        &&& pre.names.contains_key(x) ==> post.names[x] == pre.names[x]
        &&& pre.pages.contains_key(x) ==> post.pages[x] == pre.pages[x]
    }
    &&& forall|x: NodeId, r: Right| x != n ==> #[trigger] post.rights.contains((x, r)) == pre.rights.contains((x, r))
    &&& forall|o: ObjectId| #[trigger] post.covers(n, o) ==> pre.covers(c, o)
    &&& post.maps == pre.maps
    &&& adds_no_waiter(pre, post)
    &&& forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o)
}

/// Such a child in a slot of p's own table.
pub open spec fn adds_node(pre: State, post: State, p: ObjectId, c: NodeId, n: NodeId, live: spec_fn(NodeId) -> bool) -> bool {
    places_node(pre, post, p, p, c, n, live)
}

/// A child placed in a slot of d, which has the control right only with what c names, since control
/// reads the name alone.
pub open spec fn places_child(
    pre: State,
    post: State,
    p: ObjectId,
    d: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
) -> bool {
    &&& places_node(pre, post, p, d, c, n, live)
    &&& post.process_of == pre.process_of
    &&& post.rights.contains((n, Right::Control)) ==> {
        &&& pre.rights.contains((c, Right::Control))
        &&& pre.names.contains_key(c)
        &&& post.names[n] == pre.names[c]
    }
}

/// Such a child in a slot of p's own table.
pub open spec fn adds_child(pre: State, post: State, p: ObjectId, c: NodeId, n: NodeId, live: spec_fn(NodeId) -> bool) -> bool {
    places_child(pre, post, p, p, c, n, live)
}

/// Such a child naming a new object inside c's block, which holds nothing, maps nothing and belongs to
/// no process, so control over it reaches only it. A retype makes one.
pub open spec fn adds_object(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
) -> bool {
    &&& adds_node(pre, post, p, c, n, live)
    &&& post.process_of == pre.process_of
    &&& post.names.contains_key(n)
    &&& post.names[n] == object
    &&& pre.covers(c, object)
    &&& forall|x: NodeId| !#[trigger] post.held.contains((object, x))
    &&& forall|x: ObjectId| !#[trigger] post.maps.contains((object, x))
    &&& !post.process_of.contains_key(object)
}

/// post with the binding node of `adds_bound_object` not yet added: the capability n alone under c.
pub open spec fn without_binding(pre: State, post: State, c: NodeId, n: NodeId) -> State {
    State { parent: pre.parent.insert(n, c), ..post }
}

/// Such a child naming a new object inside c's block and typed into the process that cp names: a
/// second node b, the binding, which is no capability, goes under cp, a capability p holds with the
/// control right, and the process map gains the object as that process's. No capability with the
/// control right names the object before, so the only control over it is the new one, and that
/// reaches the process, which p controls already. A thread's retype makes one. See
/// design/thread-bound-at-retype/.
pub open spec fn adds_bound_object(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    cp: NodeId,
    b: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
) -> bool {
    &&& adds_node(pre, without_binding(pre, post, c, n), p, c, n, live)
    &&& post.parent == pre.parent.insert(n, c).insert(b, cp)
    &&& b != n
    &&& !live(b)
    &&& post.names.contains_key(n)
    &&& post.names[n] == object
    &&& pre.covers(c, object)
    &&& pre.holds_right(p, cp, Right::Control)
    &&& !pre.process_of.contains_key(pre.names[cp])
    &&& post.process_of == pre.process_of.insert(object, pre.names[cp])
    &&& forall|x: NodeId| #[trigger] pre.rights.contains((x, Right::Control)) && pre.names.contains_key(x)
        ==> pre.names[x] != object
}

/// post is pre with thread t's binding undone: the process map loses t, and the binding node b, which
/// is no capability, leaves the parent map. Revoke's binding arm takes such a step.
pub open spec fn unbinds(pre: State, post: State, t: ObjectId, b: NodeId) -> bool {
    &&& !pre.names.contains_key(b)
    &&& post.parent == pre.parent.remove(b)
    &&& post.process_of == pre.process_of.remove(t)
    &&& post.held == pre.held
    &&& post.names == pre.names
    &&& post.pages == pre.pages
    &&& post.rights == pre.rights
    &&& post.maps == pre.maps
    &&& adds_no_waiter(pre, post)
    &&& forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o)
}

/// What a slice of an object's teardown does, apart from who may run it: it changes only what waits on
/// the object, removes only what descends from a capability the object held, grows no reach, and gives
/// no capability a right.
pub open spec fn tears_down(pre: State, post: State, object: ObjectId) -> bool {
    &&& forall|o: ObjectId| #[trigger] State::changed(pre, post, o) ==> pre.waiting.contains((object, o))
    &&& forall|n: NodeId| #[trigger] State::removed(pre, post, n)
        ==> exists|c: NodeId, k: nat| #[trigger] pre.descends(c, n, k) && pre.holds(object, c)
    &&& forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) ==> pre.reach(r, o)
    &&& adds_no_waiter(pre, post)
    &&& forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        ==> pre.rights.contains((x, r)) && pre.names.contains_key(x)
}

/// A step that changes nothing, by a holder of an untyped with the retype right, discharges a teardown.
pub proof fn lemma_no_change_discharges_teardown(s: State, p: ObjectId, untyped: NodeId, object: ObjectId)
    requires
        s.holds_right(p, untyped, Right::Retype),
    ensures
        discharges(s, s, p, Effect::Teardown { untyped, object }),
{
}

/// A revoke of a capability the object held is a slice of its teardown: what it removes descends from
/// that capability.
pub proof fn lemma_revoke_is_teardown(pre: State, post: State, object: ObjectId, cap: NodeId)
    requires
        discharges(pre, post, object, Effect::Revoke { cap }),
        pre.holds(object, cap),
        adds_no_waiter(pre, post),
    ensures
        tears_down(pre, post, object),
{
    assert forall|n: NodeId| #[trigger] State::removed(pre, post, n)
        implies exists|c: NodeId, k: nat| #[trigger] pre.descends(c, n, k) && pre.holds(object, c) by {
        assert(may_remove(pre, object, Effect::Revoke { cap }, n));
        let k = choose|k: nat| k > 0 && #[trigger] pre.descends(cap, n, k);
        assert(pre.descends(cap, n, k) && pre.holds(object, cap));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        assert(!may_grow(pre, object, Effect::Revoke { cap }, r, o));
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies pre.rights.contains((x, r)) && pre.names.contains_key(x) by {
        assert(!may_hold(pre, post, Effect::Revoke { cap }, x, r));
    }
}

/// Deleting a capability the object held is a slice of its teardown too: the capability descends from
/// itself.
pub proof fn lemma_delete_is_teardown(pre: State, post: State, object: ObjectId, cap: NodeId)
    requires
        removes_cap(pre, post, cap),
        pre.holds(object, cap),
    ensures
        tears_down(pre, post, object),
{
    lemma_removes_cap_discharges(pre, post, object, cap);
    assert forall|n: NodeId| #[trigger] State::removed(pre, post, n)
        implies exists|c: NodeId, k: nat| #[trigger] pre.descends(c, n, k) && pre.holds(object, c) by {
        assert(n == cap);
        assert(pre.descends(cap, cap, 0));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        assert(!may_grow(pre, object, Effect::Local, r, o));
    }
}

/// A teardown followed by a slice of the same object's teardown is one teardown, under the first's
/// authority, when the list's shape stayed and nothing was added. The second step needs no authority
/// of its own, since the first may have revoked the untyped itself.
pub proof fn lemma_teardown_steps_compose(a: State, b: State, c: State, p: ObjectId, untyped: NodeId, object: ObjectId)
    requires
        discharges(a, b, p, Effect::Teardown { untyped, object }),
        tears_down(b, c, object),
        a.parent == b.parent,
        a.waiting == b.waiting,
        forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) ==> a.held.contains(h),
    ensures
        discharges(a, c, p, Effect::Teardown { untyped, object }),
{
    let e = Effect::Teardown { untyped, object };
    assert forall|o: ObjectId| #[trigger] State::changed(a, c, o) implies may_change(a, e, o) by {
        if State::changed(a, b, o) {
            assert(may_change(a, e, o));
        } else {
            assert(State::changed(b, c, o));
            assert(b.waiting.contains((object, o)));
        }
    }
    assert forall|n: NodeId| #[trigger] State::removed(a, c, n) implies may_remove(a, p, e, n) by {
        if State::removed(a, b, n) {
            assert(may_remove(a, p, e, n));
        } else {
            assert(State::removed(b, c, n));
            let (t, k) = choose|t: NodeId, k: nat| #[trigger] b.descends(t, n, k) && b.holds(object, t);
            lemma_same_parent_same_descends(b, a, t, n, k);
            assert(b.held.contains((object, t)));
            assert(a.descends(t, n, k) && a.holds(object, t));
        }
    }
    assert forall|x: NodeId, r: Right| #[trigger] c.rights.contains((x, r)) && c.names.contains_key(x)
        implies (a.rights.contains((x, r)) && a.names.contains_key(x)) || may_hold(a, c, e, x, r) by {
        assert(b.rights.contains((x, r)) && b.names.contains_key(x));
        assert(!may_hold(a, b, e, x, r));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] c.reach(r, o) implies a.reach(r, o) by {
        assert(b.reach(r, o));
        assert(!may_grow(a, p, e, r, o));
    }
    assert forall|w: (ObjectId, ObjectId)| #[trigger] c.waiting.contains(w) && !a.waiting.contains(w)
        implies may_wait(a, p, w) by {
        assert(b.waiting.contains(w));
    }
}

/// Walking up from a live node in post walks the same nodes in pre.
proof fn lemma_places_node_descends(
    pre: State,
    post: State,
    p: ObjectId,
    d: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    top: NodeId,
    x: NodeId,
    k: nat,
)
    requires
        places_node(pre, post, p, d, c, n, live),
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
        lemma_places_node_descends(pre, post, p, d, c, n, live, top, pre.parent[x], (k - 1) as nat);
    }
}

/// What a process covers directly in post it did in pre, unless it is the one the child was placed
/// with, which gains what the parent covers.
proof fn lemma_places_node_direct(
    pre: State,
    post: State,
    p: ObjectId,
    d: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    q: ObjectId,
    o: ObjectId,
)
    requires
        places_node(pre, post, p, d, c, n, live),
        post.direct(q, o),
    ensures
        pre.direct(q, o) || (q == d && pre.covers(c, o)),
{
    if !post.maps.contains((q, o)) {
        let (t, x, k) = choose|t: NodeId, x: NodeId, k: nat| #[trigger] post.descends(t, x, k)
            && post.holds(q, t) && post.covers(x, o);
        assert(post.held.contains((q, t)));
        if x == n {
            assert(pre.covers(c, o));
            if k == 0 {
                assert(!pre.held.contains((q, n)) || live(n));
                assert(q == d);
            } else {
                assert(post.parent[n] == c);
                lemma_places_node_descends(pre, post, p, d, c, n, live, t, c, (k - 1) as nat);
                assert(t != n);
                assert(pre.descends(t, c, (k - 1) as nat));
                assert(pre.held.contains((q, t)));
                assert(pre.direct(q, o));
            }
        } else {
            assert(pre.names.contains_key(x));
            lemma_places_node_descends(pre, post, p, d, c, n, live, t, x, k);
            assert(t != n);
            assert(pre.held.contains((q, t)));
            assert(pre.covers(x, o));
            assert(pre.descends(t, x, k));
            assert(pre.direct(q, o));
        }
    }
}

/// In its holder's own table the child adds nothing: the holder covered it through the parent.
pub proof fn lemma_adds_child_direct(
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
        adds_node(pre, post, p, c, n, live),
        post.direct(q, o),
    ensures
        pre.direct(q, o),
{
    lemma_places_node_direct(pre, post, p, p, c, n, live, q, o);
    if q == p && pre.covers(c, o) {
        assert(pre.descends(c, c, 0));
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

/// Adding such a child adds to nobody's reach.
proof fn lemma_adds_child_reach(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    r: ObjectId,
    o: ObjectId,
)
    requires
        adds_child(pre, post, p, c, n, live),
        post.reach(r, o),
    ensures
        pre.reach(r, o),
{
    let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
    lemma_adds_child_controlled(pre, post, p, c, n, live, r, q, k);
    if o != q {
        lemma_adds_child_direct(pre, post, p, c, n, live, q, o);
    }
    assert(pre.controlled(r, q, k));
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
        pre.names.contains_key(c),
        forall|r: Right| #[trigger] post.rights.contains((n, r)) ==> pre.rights.contains((c, r)),
    ensures
        discharges(pre, post, p, Effect::Local),
{
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, Effect::Local, x) by {
        assert(x != n);
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies (pre.rights.contains((x, r)) && pre.names.contains_key(x)) || may_hold(pre, post, Effect::Local, x, r) by {
        if x == n {
            assert(passes_right(pre, post, c, n));
        }
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_adds_child_reach(pre, post, p, c, n, live, r, o);
    }
}

/// So it is also a retype, when the parent is an untyped held with the right: a retype's new object
/// lies in the untyped's block, so it adds nothing to reach either.
pub proof fn lemma_adds_child_discharges_retype(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
)
    requires
        adds_child(pre, post, p, c, n, live),
        pre.holds_right(p, c, Right::Retype),
        post.names[n] == object,
    ensures
        discharges(pre, post, p, Effect::Retype { untyped: c, object, into: None }),
{
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, Effect::Retype { untyped: c, object, into: None }, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, Effect::Retype { untyped: c, object, into: None }, x) by {
        assert(x != n);
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_adds_child_reach(pre, post, p, c, n, live, r, o);
    }
}

/// A control chain of post is one of pre, or it passes through the new capability: then pre's chains
/// lead to the process the child was placed with, and from the placer to the chain's end.
proof fn lemma_places_child_controlled(
    pre: State,
    post: State,
    p: ObjectId,
    d: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    a: ObjectId,
    b: ObjectId,
    k: nat,
)
    requires
        places_child(pre, post, p, d, c, n, live),
        post.controlled(a, b, k),
    ensures
        pre.controlled(a, b, k) || ((exists|i: nat| #[trigger] pre.controlled(a, d, i))
            && (exists|j: nat| #[trigger] pre.controlled(p, b, j))),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] post.controls(m, b) && post.controlled(a, m, (k - 1) as nat);
        lemma_places_child_controlled(pre, post, p, d, c, n, live, a, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] post.holds_right(m, t, Right::Control)
            && post.process_behind(post.names[t]) == b;
        assert(post.held.contains((m, t)));
        if t == n {
            assert(!pre.held.contains((m, n)) || live(n));
            assert(m == d);
            assert(pre.holds_right(p, c, Right::Control));
            assert(pre.process_behind(pre.names[c]) == b);
            assert(pre.controls(p, b));
            assert(pre.controlled(p, p, 0));
            assert(pre.controlled(p, b, 1));
            if pre.controlled(a, m, (k - 1) as nat) {
                assert(pre.controlled(a, d, (k - 1) as nat));
            }
        } else {
            assert(pre.holds_right(m, t, Right::Control));
            assert(pre.process_behind(pre.names[t]) == b);
            assert(pre.controls(m, b));
            if pre.controlled(a, m, (k - 1) as nat) {
                assert(pre.controlled(a, b, k));
            } else {
                let j = choose|j: nat| #[trigger] pre.controlled(p, m, j);
                assert(pre.controlled(p, b, j + 1));
            }
        }
    }
}

/// Placing such a child adds to reach only for the process it was placed with and for what controls
/// that process, and only what the placer reached.
proof fn lemma_places_child_reach(
    pre: State,
    post: State,
    p: ObjectId,
    d: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    r: ObjectId,
    o: ObjectId,
)
    requires
        places_child(pre, post, p, d, c, n, live),
        post.reach(r, o),
        !pre.reach(r, o),
    ensures
        exists|k: nat| #[trigger] pre.controlled(r, d, k),
        pre.reach(p, o),
{
    let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
    lemma_places_child_controlled(pre, post, p, d, c, n, live, r, q, k);
    if o != q {
        lemma_places_node_direct(pre, post, p, d, c, n, live, q, o);
    }
    assert(pre.controlled(p, p, 0));
    if pre.covers(c, o) {
        assert(pre.descends(c, c, 0));
        assert(pre.direct(p, o));
        assert(pre.reach(p, o));
    }
    if pre.controlled(r, q, k) {
        assert(o != q);
        assert(!pre.direct(q, o));
        assert(q == d);
        assert(pre.controlled(r, d, k));
    } else {
        let j = choose|j: nat| #[trigger] pre.controlled(p, q, j);
        assert(pre.controlled(p, q, j));
        assert(pre.reach(p, o));
    }
}

/// Placing a child of a capability the placer holds in a slot of a process it controls is a
/// placement: nothing changes that a process can see, nothing goes, and reach grows only for that
/// process and what controls it, by what the placer reached.
pub proof fn lemma_places_child_discharges(
    pre: State,
    post: State,
    p: ObjectId,
    d: ObjectId,
    cap: NodeId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
)
    requires
        places_child(pre, post, p, d, c, n, live),
        pre.holds_right(p, cap, Right::Control),
        pre.names[cap] == d,
        !pre.process_of.contains_key(d),
        pre.names.contains_key(c),
        forall|r: Right| #[trigger] post.rights.contains((n, r)) ==> pre.rights.contains((c, r)),
    ensures
        discharges(pre, post, p, Effect::Place { cap, from: c }),
{
    let e = Effect::Place { cap, from: c };
    assert(authorized(pre, p, e));
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, e, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, e, x) by {
        assert(x != n);
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) && !pre.reach(r, o) implies may_grow(pre, p, e, r, o) by {
        lemma_places_child_reach(pre, post, p, d, c, n, live, r, o);
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies (pre.rights.contains((x, r)) && pre.names.contains_key(x)) || may_hold(pre, post, e, x, r) by {
        if x == n {
            assert(passes_right(pre, post, c, n));
        }
    }
}

/// post is pre with capability n added as a child of c, held by p, without the control right. c need
/// be nobody's: boot puts the root's console below the list's first node, which no table holds.
/// `live` says which nodes the list holds; c is among them and n is not.
pub open spec fn adds_held(pre: State, post: State, p: ObjectId, c: NodeId, n: NodeId, live: spec_fn(NodeId) -> bool) -> bool {
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
    &&& post.names.contains_key(n)
    &&& post.pages.contains_key(n)
    &&& !post.rights.contains((n, Right::Control))
    &&& post.maps == pre.maps
    &&& post.process_of == pre.process_of
}

/// Walking up from a live node walks the same nodes in pre and post.
proof fn lemma_adds_held_descends(
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
        adds_held(pre, post, p, c, n, live),
        live(x),
    ensures
        post.descends(top, x, k) == pre.descends(top, x, k),
        post.descends(top, x, k) ==> live(top),
    decreases k,
{
    if k > 0 {
        assert(x != n);
        assert(post.parent.contains_key(x) == pre.parent.contains_key(x));
        if pre.parent.contains_key(x) {
            assert(post.parent[x] == pre.parent[x]);
            lemma_adds_held_descends(pre, post, p, c, n, live, top, pre.parent[x], (k - 1) as nat);
        }
    }
}

/// The control chains are pre's: the new capability carries no control, and every other keeps its
/// name and rights.
proof fn lemma_adds_held_controlled(
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
        adds_held(pre, post, p, c, n, live),
    ensures
        post.controlled(a, b, k) == pre.controlled(a, b, k),
    decreases k,
{
    if k > 0 {
        if post.controlled(a, b, k) {
            let m = choose|m: ObjectId| #[trigger] post.controls(m, b) && post.controlled(a, m, (k - 1) as nat);
            lemma_adds_held_controlled(pre, post, p, c, n, live, a, m, (k - 1) as nat);
            let t = choose|t: NodeId| #[trigger] post.holds_right(m, t, Right::Control)
                && post.process_behind(post.names[t]) == b;
            assert(t != n);
            assert(pre.holds_right(m, t, Right::Control));
            assert(pre.controls(m, b));
        }
        if pre.controlled(a, b, k) {
            let m = choose|m: ObjectId| #[trigger] pre.controls(m, b) && pre.controlled(a, m, (k - 1) as nat);
            lemma_adds_held_controlled(pre, post, p, c, n, live, a, m, (k - 1) as nat);
            let t = choose|t: NodeId| #[trigger] pre.holds_right(m, t, Right::Control)
                && pre.process_behind(pre.names[t]) == b;
            assert(pre.held.contains((m, t)));
            assert(t != n);
            assert(post.holds_right(m, t, Right::Control));
            assert(post.controls(m, b));
        }
    }
}

/// What a process covers directly in post it did in pre, or the new capability covers it.
proof fn lemma_adds_held_direct(
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
        adds_held(pre, post, p, c, n, live),
    ensures
        post.direct(q, o) ==> pre.direct(q, o) || post.covers(n, o),
        pre.direct(q, o) ==> post.direct(q, o),
{
    if post.direct(q, o) && !post.maps.contains((q, o)) && !post.covers(n, o) {
        let (t, x, k) = choose|t: NodeId, x: NodeId, k: nat| #[trigger] post.descends(t, x, k)
            && post.holds(q, t) && post.covers(x, o);
        assert(x != n);
        assert(pre.names.contains_key(x));
        lemma_adds_held_descends(pre, post, p, c, n, live, t, x, k);
        assert(t != n);
        assert(pre.held.contains((q, t)));
        assert(pre.covers(x, o));
        assert(pre.descends(t, x, k));
    }
    if pre.direct(q, o) && !pre.maps.contains((q, o)) {
        let (t, x, k) = choose|t: NodeId, x: NodeId, k: nat| #[trigger] pre.descends(t, x, k)
            && pre.holds(q, t) && pre.covers(x, o);
        assert(live(x));
        assert(x != n);
        lemma_adds_held_descends(pre, post, p, c, n, live, t, x, k);
        assert(post.held.contains((q, t)));
        assert(post.names.contains_key(x));
        assert(post.covers(x, o));
        assert(post.descends(t, x, k));
    }
}

/// Adding a held capability without control grows reach by what it covers alone: everybody keeps
/// what they reached, nobody gains anything else, and the holder reaches all it covers.
pub proof fn lemma_adds_held_reach(pre: State, post: State, p: ObjectId, c: NodeId, n: NodeId, live: spec_fn(NodeId) -> bool)
    requires
        adds_held(pre, post, p, c, n, live),
    ensures
        forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) ==> pre.reach(r, o) || post.covers(n, o),
        forall|r: ObjectId, o: ObjectId| #[trigger] pre.reach(r, o) ==> post.reach(r, o),
        forall|o: ObjectId| #[trigger] post.covers(n, o) ==> post.reach(p, o),
{
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) || post.covers(n, o) by {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
        lemma_adds_held_controlled(pre, post, p, c, n, live, r, q, k);
        lemma_adds_held_direct(pre, post, p, c, n, live, q, o);
        assert(pre.controlled(r, q, k));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] pre.reach(r, o) implies post.reach(r, o) by {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] pre.controlled(r, q, k) && (o == q || pre.direct(q, o));
        lemma_adds_held_controlled(pre, post, p, c, n, live, r, q, k);
        lemma_adds_held_direct(pre, post, p, c, n, live, q, o);
        assert(post.controlled(r, q, k));
    }
    assert forall|o: ObjectId| #[trigger] post.covers(n, o) implies post.reach(p, o) by {
        assert(post.held.contains((p, n)));
        assert(post.descends(n, n, 0));
        assert(post.direct(p, o));
        assert(post.controlled(p, p, 0));
    }
}

/// A control chain in post is one in pre, or ends at the new object after one in pre that reaches
/// p: the object holds nothing, so no chain goes on from it.
proof fn lemma_adds_object_controlled(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
    a: ObjectId,
    b: ObjectId,
    k: nat,
)
    requires
        adds_object(pre, post, p, c, n, live, object),
        post.controlled(a, b, k),
    ensures
        pre.controlled(a, b, k) || (b == object && k > 0 && pre.controlled(a, p, (k - 1) as nat)),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] post.controls(m, b) && post.controlled(a, m, (k - 1) as nat);
        lemma_adds_object_controlled(pre, post, p, c, n, live, object, a, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] post.holds_right(m, t, Right::Control)
            && post.process_behind(post.names[t]) == b;
        assert(post.held.contains((m, t)));
        if m == object {
            assert(!post.held.contains((object, t)));
        }
        assert(pre.controlled(a, m, (k - 1) as nat));
        if t == n {
            assert(!pre.held.contains((m, n)) || live(n));
            assert(m == p);
            assert(b == object);
        } else {
            assert(pre.holds_right(m, t, Right::Control));
            assert(pre.process_behind(pre.names[t]) == b);
            assert(pre.controls(m, b));
        }
    }
}

/// So the new object adds to nobody's reach: whoever reaches it now reached it through c before.
proof fn lemma_adds_object_reach(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
    r: ObjectId,
    o: ObjectId,
)
    requires
        adds_object(pre, post, p, c, n, live, object),
        post.reach(r, o),
    ensures
        pre.reach(r, o),
{
    let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
    lemma_adds_object_controlled(pre, post, p, c, n, live, object, r, q, k);
    if pre.controlled(r, q, k) {
        if o != q {
            lemma_adds_child_direct(pre, post, p, c, n, live, q, o);
        }
        assert(pre.controlled(r, q, k) && (o == q || pre.direct(q, o)));
    } else {
        let j = (k - 1) as nat;
        assert(pre.controlled(r, p, j));
        if o == q {
            assert(live(c));
            assert(pre.descends(c, c, 0));
            assert(pre.holds(p, c));
            assert(pre.covers(c, o));
            assert(pre.direct(p, o));
        } else {
            assert(post.direct(object, o));
            assert(!post.maps.contains((object, o)));
            let (t, x, i) = choose|t: NodeId, x: NodeId, i: nat| #[trigger] post.descends(t, x, i)
                && post.holds(object, t) && post.covers(x, o);
            assert(!post.held.contains((object, t)));
        }
        assert(pre.controlled(r, p, j) && (o == p || pre.direct(p, o)));
    }
}

/// So a retype that adds such an object, by a holder of the untyped with the right, discharges it.
pub proof fn lemma_adds_object_discharges_retype(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
)
    requires
        adds_object(pre, post, p, c, n, live, object),
        pre.holds_right(p, c, Right::Retype),
    ensures
        discharges(pre, post, p, Effect::Retype { untyped: c, object, into: None }),
{
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, Effect::Retype { untyped: c, object, into: None }, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, Effect::Retype { untyped: c, object, into: None }, x) by {
        assert(x != n);
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_adds_object_reach(pre, post, p, c, n, live, object, r, o);
    }
}

/// A retype followed by a local step that removes no capability and gives none a right is one retype:
/// the local step changes nothing a process can see and grows no reach, so what the two do is what the
/// retype may. A thread's retype is one, its binding under the process capability being the local
/// step.
pub proof fn lemma_retype_then_local(a: State, b: State, c: State, p: ObjectId, untyped: NodeId, object: ObjectId)
    requires
        discharges(a, b, p, Effect::Retype { untyped, object, into: None }),
        discharges(b, c, p, Effect::Local),
        forall|n: NodeId| #[trigger] b.names.contains_key(n) ==> c.names.contains_key(n),
        adds_no_waiter(b, c),
        forall|n: NodeId, r: Right| #[trigger] c.rights.contains((n, r)) && c.names.contains_key(n)
            ==> b.rights.contains((n, r)) && b.names.contains_key(n) && c.names[n] == b.names[n],
    ensures
        discharges(a, c, p, Effect::Retype { untyped, object, into: None }),
{
    let e = Effect::Retype { untyped, object, into: None };
    assert forall|o: ObjectId| #[trigger] State::changed(a, c, o) implies may_change(a, e, o) by {
        if !State::changed(a, b, o) {
            assert(State::changed(b, c, o));
            assert(may_change(b, Effect::Local, o));
        }
    }
    assert forall|n: NodeId| #[trigger] State::removed(a, c, n) implies may_remove(a, p, e, n) by {
        assert(State::removed(a, b, n));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] c.reach(r, o) && !a.reach(r, o) implies may_grow(a, p, e, r, o) by {
        if !b.reach(r, o) {
            assert(may_grow(b, p, Effect::Local, r, o));
        }
    }
    assert forall|w: (ObjectId, ObjectId)| #[trigger] c.waiting.contains(w) && !a.waiting.contains(w)
        implies may_wait(a, p, w) by {
        assert(b.waiting.contains(w));
    }
    assert forall|x: NodeId, r: Right| #[trigger] c.rights.contains((x, r)) && c.names.contains_key(x)
        implies (a.rights.contains((x, r)) && a.names.contains_key(x)) || may_hold(a, c, e, x, r) by {
        assert(b.rights.contains((x, r)) && b.names.contains_key(x));
    }
}

/// Walking up from a capability in post walks the same nodes without the binding, which nothing
/// lies under.
proof fn lemma_adds_bound_object_descends(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    cp: NodeId,
    b: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
    top: NodeId,
    x: NodeId,
    k: nat,
)
    requires
        adds_bound_object(pre, post, p, c, n, cp, b, live, object),
        post.descends(top, x, k),
        live(x) || x == n,
    ensures
        without_binding(pre, post, c, n).descends(top, x, k),
    decreases k,
{
    if k > 0 {
        assert(x != b);
        let y = post.parent[x];
        if x == n {
            assert(y == c);
            assert(live(c));
        } else {
            assert(pre.parent.contains_key(x));
            assert(y == pre.parent[x]);
            assert(live(y));
        }
        lemma_adds_bound_object_descends(pre, post, p, c, n, cp, b, live, object, top, y, (k - 1) as nat);
    }
}

/// Every control link in post is one in pre: the new capability's control reaches the process, which
/// p controlled through cp, and no other capability's control target moves, since none names the
/// object.
proof fn lemma_adds_bound_object_controlled(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    cp: NodeId,
    b: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
    a: ObjectId,
    q: ObjectId,
    k: nat,
)
    requires
        adds_bound_object(pre, post, p, c, n, cp, b, live, object),
        post.controlled(a, q, k),
    ensures
        pre.controlled(a, q, k),
    decreases k,
{
    if k > 0 {
        let mid = without_binding(pre, post, c, n);
        let m = choose|m: ObjectId| #[trigger] post.controls(m, q) && post.controlled(a, m, (k - 1) as nat);
        lemma_adds_bound_object_controlled(pre, post, p, c, n, cp, b, live, object, a, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] post.holds_right(m, t, Right::Control)
            && post.process_behind(post.names[t]) == q;
        assert(mid.held.contains((m, t)));
        if t == n {
            assert(!pre.held.contains((m, n)) || live(n));
            assert(m == p);
            assert(post.process_of.contains_key(object));
            assert(q == pre.names[cp]);
            assert(pre.process_behind(pre.names[cp]) == q);
            assert(pre.holds_right(p, cp, Right::Control));
        } else {
            assert(mid.names.contains_key(t) == pre.names.contains_key(t));
            assert(mid.rights.contains((t, Right::Control)) == pre.rights.contains((t, Right::Control)));
            assert(pre.holds_right(m, t, Right::Control));
            assert(pre.names[t] != object);
            assert(post.process_of.contains_key(pre.names[t]) == pre.process_of.contains_key(pre.names[t]));
            assert(pre.process_behind(pre.names[t]) == q);
        }
        assert(pre.controls(m, q));
    }
}

/// So a retype that adds such a bound object, by a holder of the untyped with the right, discharges
/// it: nobody's reach grows at all.
pub proof fn lemma_adds_bound_object_discharges_retype(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    n: NodeId,
    cp: NodeId,
    b: NodeId,
    live: spec_fn(NodeId) -> bool,
    object: ObjectId,
)
    requires
        adds_bound_object(pre, post, p, c, n, cp, b, live, object),
        pre.holds_right(p, c, Right::Retype),
    ensures
        discharges(pre, post, p, Effect::Retype { untyped: c, object, into: None }),
{
    let mid = without_binding(pre, post, c, n);
    let e = Effect::Retype { untyped: c, object, into: None };
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, e, o) by {
        assert((mid.contents)(o) == (pre.contents)(o));
    }
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, e, x) by {
        assert(x != n);
        assert(mid.names.contains_key(x) == pre.names.contains_key(x));
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies (pre.rights.contains((x, r)) && pre.names.contains_key(x)) || may_hold(pre, post, e, x, r) by {
        assert(mid.rights.contains((x, r)) && mid.names.contains_key(x));
        if x != n {
            assert(pre.rights.contains((x, r)) && pre.names.contains_key(x));
        } else {
            assert(!pre.names.contains_key(n));
        }
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
        lemma_adds_bound_object_controlled(pre, post, p, c, n, cp, b, live, object, r, q, k);
        if o != q && !post.maps.contains((q, o)) {
            let (t, x, d) = choose|t: NodeId, x: NodeId, d: nat| #[trigger] post.descends(t, x, d)
                && post.holds(q, t) && post.covers(x, o);
            assert(mid.names.contains_key(x));
            if x != n {
                assert(pre.names.contains_key(x));
            }
            lemma_adds_bound_object_descends(pre, post, p, c, n, cp, b, live, object, t, x, d);
            assert(mid.descends(t, x, d) && mid.holds(q, t) && mid.covers(x, o));
            assert(mid.direct(q, o));
            lemma_adds_child_direct(pre, mid, p, c, n, live, q, o);
        } else if o != q {
            assert(mid.maps.contains((q, o)));
        }
        assert(pre.controlled(r, q, k) && (o == q || pre.direct(q, o)));
    }
    assert forall|w: (ObjectId, ObjectId)| #[trigger] post.waiting.contains(w) implies pre.waiting.contains(w) by {
        assert(mid.waiting.contains(w));
    }
}

/// Walking up in post walks the same nodes in pre, since post's parent map is pre's less one entry.
proof fn lemma_unbinds_descends(pre: State, post: State, t: ObjectId, b: NodeId, top: NodeId, x: NodeId, k: nat)
    requires
        unbinds(pre, post, t, b),
        post.descends(top, x, k),
    ensures
        pre.descends(top, x, k),
    decreases k,
{
    if k > 0 {
        lemma_unbinds_descends(pre, post, t, b, top, post.parent[x], (k - 1) as nat);
    }
}

/// A control chain in post is one in pre, or ends at t after one in pre whose last process directly
/// reaches t: control over t, which reached its process in pre, now reaches t alone, and t holds
/// nothing, so no chain goes on from it.
proof fn lemma_unbinds_controlled(pre: State, post: State, t: ObjectId, b: NodeId, a: ObjectId, q: ObjectId, k: nat)
    requires
        unbinds(pre, post, t, b),
        forall|x: NodeId| !#[trigger] pre.held.contains((t, x)),
        forall|x: NodeId| #[trigger] pre.names.contains_key(x) && pre.names[x] == t ==> pre.covers(x, t),
        post.controlled(a, q, k),
    ensures
        pre.controlled(a, q, k) || (q == t && exists|m: ObjectId, j: nat| #[trigger] pre.controlled(a, m, j) && pre.direct(m, t)),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] post.controls(m, q) && post.controlled(a, m, (k - 1) as nat);
        lemma_unbinds_controlled(pre, post, t, b, a, m, (k - 1) as nat);
        let x = choose|x: NodeId| #[trigger] post.holds_right(m, x, Right::Control)
            && post.process_behind(post.names[x]) == q;
        assert(pre.held.contains((m, x)));
        assert(m != t);
        assert(pre.controlled(a, m, (k - 1) as nat));
        assert(pre.holds_right(m, x, Right::Control));
        if pre.names[x] == t {
            assert(!post.process_of.contains_key(t));
            assert(q == t);
            assert(pre.covers(x, t));
            assert(pre.descends(x, x, 0));
            assert(pre.direct(m, t));
            assert(pre.controlled(a, m, (k - 1) as nat) && pre.direct(m, t));
        } else {
            assert(post.process_of.contains_key(pre.names[x]) == pre.process_of.contains_key(pre.names[x]));
            assert(pre.process_behind(pre.names[x]) == q);
            assert(pre.controls(m, q));
        }
    }
}

/// Undoing a thread's binding is a step of revoking a capability its caller holds, when the thread
/// holds nothing, maps nothing, and every capability naming it covers it: control over the thread
/// stops reaching its process and reaches the thread alone, which the capability's holder reached
/// already.
pub proof fn lemma_unbinds_discharges_revoke(pre: State, post: State, p: ObjectId, cap: NodeId, t: ObjectId, b: NodeId)
    requires
        unbinds(pre, post, t, b),
        pre.holds(p, cap),
        pre.names.contains_key(cap),
        forall|x: NodeId| !#[trigger] pre.held.contains((t, x)),
        forall|o: ObjectId| !#[trigger] pre.maps.contains((t, o)),
        forall|x: NodeId| #[trigger] pre.names.contains_key(x) && pre.names[x] == t ==> pre.covers(x, t),
    ensures
        discharges(pre, post, p, Effect::Revoke { cap }),
{
    let e = Effect::Revoke { cap };
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, e, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
        lemma_unbinds_controlled(pre, post, t, b, r, q, k);
        if o != q && !post.maps.contains((q, o)) {
            let (x, y, d) = choose|x: NodeId, y: NodeId, d: nat| #[trigger] post.descends(x, y, d)
                && post.holds(q, x) && post.covers(y, o);
            lemma_unbinds_descends(pre, post, t, b, x, y, d);
            assert(pre.descends(x, y, d) && pre.holds(q, x) && pre.covers(y, o));
            assert(pre.direct(q, o));
        }
        if !pre.controlled(r, q, k) {
            assert(q == t);
            let (m, j) = choose|m: ObjectId, j: nat| #[trigger] pre.controlled(r, m, j) && pre.direct(m, t);
            if o != t {
                assert(!pre.maps.contains((t, o)));
                assert(post.direct(t, o));
                let (x, y, d) = choose|x: NodeId, y: NodeId, d: nat| #[trigger] post.descends(x, y, d)
                    && post.holds(t, x) && post.covers(y, o);
                assert(pre.held.contains((t, x)));
            }
            assert(pre.controlled(r, m, j) && (o == m || pre.direct(m, o)));
        } else {
            assert(pre.controlled(r, q, k) && (o == q || pre.direct(q, o)));
        }
    }
}

/// post is pre without capability n. Nothing else changes, so the parent map still says what it said.
pub open spec fn removes_cap(pre: State, post: State, n: NodeId) -> bool {
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
    &&& adds_no_waiter(pre, post)
    &&& forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o)
}

proof fn lemma_removes_cap_controlled(pre: State, post: State, n: NodeId, a: ObjectId, b: ObjectId, k: nat)
    requires
        removes_cap(pre, post, n),
        post.controlled(a, b, k),
    ensures
        pre.controlled(a, b, k),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] post.controls(m, b) && post.controlled(a, m, (k - 1) as nat);
        lemma_removes_cap_controlled(pre, post, n, a, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] post.holds_right(m, t, Right::Control)
            && post.process_behind(post.names[t]) == b;
        assert(post.held.contains((m, t)));
        assert(post.rights.contains((t, Right::Control)));
        assert(pre.holds_right(m, t, Right::Control));
        assert(pre.controls(m, b));
    }
}

/// Removing a capability by the choice of a process that commands it, its holder or a controller of
/// its holder, is a local step, and nobody's reach grows.
pub proof fn lemma_removes_cap_discharges(pre: State, post: State, p: ObjectId, n: NodeId)
    requires
        removes_cap(pre, post, n),
        pre.commands(p, n),
    ensures
        discharges(pre, post, p, Effect::Local),
{
    assert forall|x: NodeId| #[trigger] State::removed(pre, post, x) implies may_remove(pre, p, Effect::Local, x) by {
        assert(x == n);
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] post.controlled(r, q, k) && (o == q || post.direct(q, o));
        lemma_removes_cap_controlled(pre, post, n, r, q, k);
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
    &&& adds_no_waiter(b, a)
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

/// a's authority is in b through a renaming f, as `simulates` says, except that a capability p holds in
/// a may be one q holds in b. A claim's step, read backward: p took from q.
pub open spec fn simulates_claim(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    p: ObjectId,
    q: ObjectId,
) -> bool {
    &&& forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) ==> live(h.1)
        && (b.held.contains((h.0, f(h.1))) || (h.0 == p && b.held.contains((q, f(h.1)))))
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
    &&& adds_no_waiter(b, a)
}

/// With p and q the same process, that is `simulates`.
pub proof fn lemma_simulates_claim_self(a: State, b: State, live: spec_fn(NodeId) -> bool, f: spec_fn(NodeId) -> NodeId, p: ObjectId)
    requires
        simulates_claim(a, b, live, f, p, p),
    ensures
        simulates(a, b, live, f),
{
}

proof fn lemma_simulates_claim_descends(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    p: ObjectId,
    q: ObjectId,
    top: NodeId,
    x: NodeId,
    k: nat,
)
    requires
        simulates_claim(a, b, live, f, p, q),
        a.descends(top, x, k),
        live(x),
    ensures
        b.descends(f(top), f(x), k),
    decreases k,
{
    if k > 0 {
        assert(a.parent.contains_key(x));
        lemma_simulates_claim_descends(a, b, live, f, p, q, top, a.parent[x], (k - 1) as nat);
    }
}

/// A control chain in a is one in b, perhaps longer: a link through what p took from q goes through q
/// in b, which p controls.
proof fn lemma_simulates_claim_controlled(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    p: ObjectId,
    q: ObjectId,
    r: ObjectId,
    x: ObjectId,
    k: nat,
)
    requires
        simulates_claim(a, b, live, f, p, q),
        b.controls(p, q),
        a.controlled(r, x, k),
    ensures
        exists|j: nat| #[trigger] b.controlled(r, x, j),
    decreases k,
{
    if k == 0 {
        assert(b.controlled(r, x, 0));
    } else {
        let m = choose|m: ObjectId| #[trigger] a.controls(m, x) && a.controlled(r, m, (k - 1) as nat);
        lemma_simulates_claim_controlled(a, b, live, f, p, q, r, m, (k - 1) as nat);
        let j = choose|j: nat| #[trigger] b.controlled(r, m, j);
        let t = choose|t: NodeId| #[trigger] a.holds_right(m, t, Right::Control)
            && a.process_behind(a.names[t]) == x;
        assert(a.held.contains((m, t)));
        assert(a.names.contains_key(t));
        assert(a.rights.contains((t, Right::Control)));
        assert(b.rights.contains((f(t), Right::Control)));
        assert(b.names.contains_key(f(t)));
        assert(b.process_behind(b.names[f(t)]) == x);
        let j1 = (j + 1) as nat;
        if b.held.contains((m, f(t))) {
            assert(b.holds_right(m, f(t), Right::Control));
            assert(b.controls(m, x));
            assert(b.controlled(r, x, j1));
        } else {
            assert(m == p);
            assert(b.held.contains((q, f(t))));
            assert(b.holds_right(q, f(t), Right::Control));
            assert(b.controls(q, x));
            assert(b.controlled(r, q, j1));
            let j2 = (j1 + 1) as nat;
            assert(b.controlled(r, x, j2));
        }
    }
}

/// Anything a process reaches in a it reaches in b.
pub proof fn lemma_simulates_claim_reach(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    p: ObjectId,
    q: ObjectId,
    r: ObjectId,
    o: ObjectId,
)
    requires
        simulates_claim(a, b, live, f, p, q),
        b.controls(p, q),
        a.reach(r, o),
    ensures
        b.reach(r, o),
{
    let (x, k) = choose|x: ObjectId, k: nat| #[trigger] a.controlled(r, x, k) && (o == x || a.direct(x, o));
    lemma_simulates_claim_controlled(a, b, live, f, p, q, r, x, k);
    let j = choose|j: nat| #[trigger] b.controlled(r, x, j);
    if o == x || a.maps.contains((x, o)) {
        assert(b.controlled(r, x, j) && (o == x || b.direct(x, o)));
    } else {
        let (t, y, d) = choose|t: NodeId, y: NodeId, d: nat| #[trigger] a.descends(t, y, d)
            && a.holds(x, t) && a.covers(y, o);
        assert(a.names.contains_key(y));
        assert(a.pages.contains_key(y));
        assert(a.held.contains((x, t)));
        lemma_simulates_claim_descends(a, b, live, f, p, q, t, y, d);
        assert(b.covers(f(y), o));
        if b.held.contains((x, f(t))) {
            assert(b.holds(x, f(t)));
            assert(b.direct(x, o));
            assert(b.controlled(r, x, j) && (o == x || b.direct(x, o)));
        } else {
            assert(x == p);
            assert(b.held.contains((q, f(t))));
            assert(b.holds(q, f(t)));
            assert(b.direct(q, o));
            let j1 = (j + 1) as nat;
            assert(b.controlled(r, q, j1));
            assert(b.controlled(r, q, j1) && (o == q || b.direct(q, o)));
        }
    }
}

/// f names each capability of post by itself in pre, or, for one new in post, by a capability the step
/// removed: a move's renaming read backward.
pub open spec fn renames_moved(pre: State, post: State, f: spec_fn(NodeId) -> NodeId) -> bool {
    forall|x: NodeId| #[trigger] post.names.contains_key(x) && f(x) != x
        ==> !pre.names.contains_key(x) && State::removed(pre, post, f(x))
}

/// A claim's step: post's authority is all in pre, once what p took is read as q's, and p controls q,
/// so nobody's reach grows. Only the node claimed goes, and the node that takes its place has its
/// rights.
pub proof fn lemma_simulates_claim_discharges(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    from: NodeId,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
)
    requires
        simulates_claim(post, pre, live, f, p, pre.names[c]),
        renames_moved(pre, post, f),
        pre.holds_right(p, c, Right::Control),
        !pre.process_of.contains_key(pre.names[c]),
        pre.holds(pre.names[c], from),
        pre.names.contains_key(from),
        forall|x: NodeId| #[trigger] State::removed(pre, post, x) ==> x == from,
        forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o),
    ensures
        discharges(pre, post, p, Effect::Claim { cap: c, from }),
{
    let q = pre.names[c];
    assert(pre.process_behind(q) == q);
    assert(pre.controls(p, q));
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, Effect::Claim { cap: c, from }, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_simulates_claim_reach(post, pre, live, f, p, q, r, o);
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies (pre.rights.contains((x, r)) && pre.names.contains_key(x))
        || may_hold(pre, post, Effect::Claim { cap: c, from }, x, r) by {
        if f(x) != x {
            assert(State::removed(pre, post, f(x)));
            assert(passes_right(pre, post, from, x));
        }
    }
}

/// A control chain in a is one in b, or it goes through a capability d holds in a that s held in b:
/// then b's chains lead to d, and from p, which b's chains lead to s from, to the chain's end. A move
/// into d's table, read backward.
proof fn lemma_simulates_place_controlled(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    d: ObjectId,
    s: ObjectId,
    p: ObjectId,
    j: nat,
    r: ObjectId,
    x: ObjectId,
    k: nat,
)
    requires
        simulates_claim(a, b, live, f, d, s),
        b.controlled(p, s, j),
        a.controlled(r, x, k),
    ensures
        b.controlled(r, x, k) || ((exists|i: nat| #[trigger] b.controlled(r, d, i))
            && (exists|i: nat| #[trigger] b.controlled(p, x, i))),
    decreases k,
{
    if k > 0 {
        let m = choose|m: ObjectId| #[trigger] a.controls(m, x) && a.controlled(r, m, (k - 1) as nat);
        lemma_simulates_place_controlled(a, b, live, f, d, s, p, j, r, m, (k - 1) as nat);
        let t = choose|t: NodeId| #[trigger] a.holds_right(m, t, Right::Control)
            && a.process_behind(a.names[t]) == x;
        assert(a.held.contains((m, t)));
        assert(a.names.contains_key(t));
        assert(a.rights.contains((t, Right::Control)));
        assert(b.rights.contains((f(t), Right::Control)));
        assert(b.names.contains_key(f(t)));
        assert(b.process_behind(b.names[f(t)]) == x);
        if b.held.contains((m, f(t))) {
            assert(b.holds_right(m, f(t), Right::Control));
            assert(b.controls(m, x));
            if b.controlled(r, m, (k - 1) as nat) {
                assert(b.controlled(r, x, k));
            } else {
                let i = choose|i: nat| #[trigger] b.controlled(p, m, i);
                assert(b.controlled(p, x, i + 1));
            }
        } else {
            assert(m == d);
            assert(b.held.contains((s, f(t))));
            assert(b.holds_right(s, f(t), Right::Control));
            assert(b.controls(s, x));
            assert(b.controlled(p, x, j + 1));
            if b.controlled(r, m, (k - 1) as nat) {
                assert(b.controlled(r, d, (k - 1) as nat));
            }
        }
    }
}

/// Whatever a process reaches in a and not in b, b's chains lead from it to d, and p reaches it in b.
proof fn lemma_simulates_place_reach(
    a: State,
    b: State,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
    d: ObjectId,
    s: ObjectId,
    p: ObjectId,
    j: nat,
    r: ObjectId,
    o: ObjectId,
)
    requires
        simulates_claim(a, b, live, f, d, s),
        b.controlled(p, s, j),
        a.reach(r, o),
        !b.reach(r, o),
    ensures
        exists|k: nat| #[trigger] b.controlled(r, d, k),
        b.reach(p, o),
{
    let (x, k) = choose|x: ObjectId, k: nat| #[trigger] a.controlled(r, x, k) && (o == x || a.direct(x, o));
    lemma_simulates_place_controlled(a, b, live, f, d, s, p, j, r, x, k);
    if o != x && !a.maps.contains((x, o)) {
        let (t, y, h) = choose|t: NodeId, y: NodeId, h: nat| #[trigger] a.descends(t, y, h)
            && a.holds(x, t) && a.covers(y, o);
        assert(a.names.contains_key(y));
        assert(a.pages.contains_key(y));
        assert(a.held.contains((x, t)));
        lemma_simulates_claim_descends(a, b, live, f, d, s, t, y, h);
        assert(b.covers(f(y), o));
        if b.held.contains((x, f(t))) {
            assert(b.holds(x, f(t)));
            assert(b.direct(x, o));
        } else {
            assert(x == d);
            assert(b.holds(s, f(t)));
            assert(b.direct(s, o));
        }
    }
    assert(o == x || b.direct(x, o) || (x == d && b.direct(s, o)));
    if b.controlled(r, x, k) {
        assert(!(o == x || b.direct(x, o)));
        assert(b.controlled(r, d, k));
        assert(b.controlled(p, s, j) && (o == s || b.direct(s, o)));
    } else {
        let i = choose|i: nat| #[trigger] b.controlled(p, x, i);
        if o == x || b.direct(x, o) {
            assert(b.controlled(p, x, i) && (o == x || b.direct(x, o)));
        } else {
            assert(b.controlled(p, s, j) && (o == s || b.direct(s, o)));
        }
    }
}

/// A move's step into the table of the process cap names: post's authority is all in pre, once what
/// that process holds is read as held by s, which is p or a process p's control chains lead to. Only
/// the node moved goes, and reach grows only for that process and what controls it, by what p
/// reached.
pub proof fn lemma_simulates_place_discharges(
    pre: State,
    post: State,
    p: ObjectId,
    cap: NodeId,
    from: NodeId,
    s: ObjectId,
    j: nat,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
)
    requires
        simulates_claim(post, pre, live, f, pre.names[cap], s),
        renames_moved(pre, post, f),
        pre.holds_right(p, cap, Right::Control),
        !pre.process_of.contains_key(pre.names[cap]),
        pre.commands(p, from),
        pre.names.contains_key(from),
        pre.controlled(p, s, j),
        forall|x: NodeId| #[trigger] State::removed(pre, post, x) ==> x == from,
        forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o),
    ensures
        discharges(pre, post, p, Effect::Place { cap, from }),
{
    let e = Effect::Place { cap, from };
    assert(authorized(pre, p, e));
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, e, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) && !pre.reach(r, o) implies may_grow(pre, p, e, r, o) by {
        lemma_simulates_place_reach(post, pre, live, f, pre.names[cap], s, p, j, r, o);
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies (pre.rights.contains((x, r)) && pre.names.contains_key(x)) || may_hold(pre, post, e, x, r) by {
        if f(x) != x {
            assert(State::removed(pre, post, f(x)));
            assert(passes_right(pre, post, from, x));
        }
    }
}

/// A retype that names no new capability, only a node nobody holds: post's authority is all in pre,
/// and every capability of pre is still there.
pub proof fn lemma_simulated_discharges_retype(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    object: ObjectId,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
)
    requires
        simulates(post, pre, live, f),
        forall|x: NodeId| #[trigger] f(x) == x,
        pre.holds_right(p, c, Right::Retype),
        forall|x: NodeId| #[trigger] pre.names.contains_key(x) ==> post.names.contains_key(x),
        forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o),
    ensures
        discharges(pre, post, p, Effect::Retype { untyped: c, object, into: None }),
{
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, Effect::Retype { untyped: c, object, into: None }, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_simulates_reach(post, pre, live, f, r, o);
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies pre.rights.contains((x, r)) && pre.names.contains_key(x) by {
        assert(f(x) == x);
    }
}

/// A revoke's step: post's authority is all in pre, and what it removed is below the capability named.
pub proof fn lemma_simulated_discharges_revoke(
    pre: State,
    post: State,
    p: ObjectId,
    c: NodeId,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
)
    requires
        simulates(post, pre, live, f),
        forall|x: NodeId| #[trigger] f(x) == x,
        pre.commands(p, c),
        pre.names.contains_key(c),
        forall|x: NodeId| #[trigger] State::removed(pre, post, x) ==> exists|k: nat| k > 0 && #[trigger] pre.descends(c, x, k),
        forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o),
    ensures
        discharges(pre, post, p, Effect::Revoke { cap: c }),
{
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, Effect::Revoke { cap: c }, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_simulates_reach(post, pre, live, f, r, o);
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies pre.rights.contains((x, r)) && pre.names.contains_key(x) by {
        assert(f(x) == x);
    }
}

/// A local step that names no capability and removes none: post's authority is all in pre.
pub proof fn lemma_simulated_discharges_local(
    pre: State,
    post: State,
    p: ObjectId,
    live: spec_fn(NodeId) -> bool,
    f: spec_fn(NodeId) -> NodeId,
)
    requires
        simulates(post, pre, live, f),
        forall|x: NodeId| #[trigger] f(x) == x,
        forall|x: NodeId| #[trigger] pre.names.contains_key(x) ==> post.names.contains_key(x),
        forall|o: ObjectId| #[trigger] (post.contents)(o) == (pre.contents)(o),
    ensures
        discharges(pre, post, p, Effect::Local),
{
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, Effect::Local, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_simulates_reach(post, pre, live, f, r, o);
    }
    assert forall|x: NodeId, r: Right| #[trigger] post.rights.contains((x, r)) && post.names.contains_key(x)
        implies pre.rights.contains((x, r)) && pre.names.contains_key(x) by {
        assert(f(x) == x);
    }
}

/// Two steps of revoking one capability are one: what they remove descends from it in the first state,
/// since a revoke changes no parent, and reach only shrinks. The authority is the first step's, the
/// caller commanding the capability when the revoke began; the second is stated for the capability's
/// holder, since the first may have removed the capability through which the caller controls it.
pub proof fn lemma_revoke_steps_compose(a: State, b: State, c: State, p: ObjectId, holder: ObjectId, cap: NodeId)
    requires
        discharges(a, b, p, Effect::Revoke { cap }),
        discharges(b, c, holder, Effect::Revoke { cap }),
        a.parent == b.parent,
        adds_no_waiter(b, c),
    ensures
        discharges(a, c, p, Effect::Revoke { cap }),
{
    assert forall|o: ObjectId| #[trigger] State::changed(a, c, o) implies may_change(a, Effect::Revoke { cap }, o) by {
        if State::changed(a, b, o) {
            assert(may_change(a, Effect::Revoke { cap }, o));
        } else {
            assert(State::changed(b, c, o));
            assert(may_change(b, Effect::Revoke { cap }, o));
        }
    }
    assert forall|n: NodeId| #[trigger] State::removed(a, c, n) implies may_remove(a, p, Effect::Revoke { cap }, n) by {
        if State::removed(a, b, n) {
            assert(may_remove(a, p, Effect::Revoke { cap }, n));
        } else {
            assert(State::removed(b, c, n));
            let k = choose|k: nat| k > 0 && #[trigger] b.descends(cap, n, k);
            lemma_same_parent_same_descends(b, a, cap, n, k);
        }
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] c.reach(r, o) implies a.reach(r, o) by {
        assert(!may_grow(b, holder, Effect::Revoke { cap }, r, o));
        assert(b.reach(r, o));
        assert(!may_grow(a, p, Effect::Revoke { cap }, r, o));
    }
    assert forall|w: (ObjectId, ObjectId)| #[trigger] c.waiting.contains(w) && !a.waiting.contains(w)
        implies may_wait(a, p, w) by {
        assert(b.waiting.contains(w));
    }
    assert forall|x: NodeId, r: Right| #[trigger] c.rights.contains((x, r)) && c.names.contains_key(x)
        implies a.rights.contains((x, r)) && a.names.contains_key(x) by {
        assert(!may_hold(b, c, Effect::Revoke { cap }, x, r));
        assert(!may_hold(a, b, Effect::Revoke { cap }, x, r));
    }
}

/// Control is transitive: if s controls m and m controls q, s reaches what q directly reaches, since
/// s can claim m's control over q, and repeat.
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

/// Only a grant, over an endpoint or through control, or a retype can add to anyone's reach.
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
        !(e is Place),
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

/// Process 1 controls process 2 through node 10, and process 2's thread 3 through node 11. Process 2
/// holds node 20, and nobody has destroyed it.
pub open spec fn control_example() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 10usize) || h == (1usize, 11usize) || h == (2usize, 20usize)),
        names: IMap::new(
            |n: NodeId| n == 10 || n == 11 || n == 20,
            |n: NodeId| if n == 10 { 2usize } else if n == 11 { 3usize } else { EXAMPLE_BASE },
        ),
        pages: IMap::new(|n: NodeId| n == 10 || n == 11 || n == 20, |n: NodeId| 1nat),
        rights: ISet::new(|h: (NodeId, Right)| (h.0 == 10 || h.0 == 11) && h.1 == Right::Control),
        parent: Map::empty(),
        maps: Set::empty(),
        process_of: map![3usize => 2usize],
        waiting: Set::empty(),
        bound: Map::empty(),
        contents: |o: ObjectId| Seq::empty(),
    }
}

/// A claim needs control of the process, and not its death.
pub proof fn lemma_claim_from_a_live_process()
    ensures
        authorized(control_example(), 1, Effect::Claim { cap: 10, from: 20 }),
{
    let s = control_example();
    assert(s.holds_right(1, 10, Right::Control));
    assert(s.holds(2, 20));
    assert(s.names[10] == 2);
    assert(!s.process_of.contains_key(2));
}

/// Control of a thread does not let its holder claim from the thread's process.
pub proof fn lemma_no_claim_through_a_thread()
    ensures
        !authorized(control_example(), 1, Effect::Claim { cap: 11, from: 20 }),
{
    let s = control_example();
    assert(s.names[11] == 3);
    assert(s.process_of.contains_key(3));
}

/// control_example without node 20, which process 2 held.
pub open spec fn control_example_without_20() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 10usize) || h == (1usize, 11usize)),
        names: IMap::new(|n: NodeId| n == 10 || n == 11, |n: NodeId| if n == 10 { 2usize } else { 3usize }),
        pages: IMap::new(|n: NodeId| n == 10 || n == 11, |n: NodeId| 1nat),
        ..control_example()
    }
}

/// Control of a process lets its holder delete from the process's table and revoke what is there: the
/// controller commands what the process holds.
pub proof fn lemma_delete_and_revoke_through_control()
    ensures
        control_example().commands(1, 20),
        discharges(control_example(), control_example_without_20(), 1, Effect::Local),
        authorized(control_example(), 1, Effect::Revoke { cap: 20 }),
{
    let (s, t) = (control_example(), control_example_without_20());
    assert(s.holds_right(1, 10, Right::Control));
    assert(s.names[10] == 2);
    assert(!s.process_of.contains_key(2));
    assert(s.holds(2, 20));
    assert(s.commands(1, 20));
    assert(removes_cap(s, t, 20));
    lemma_removes_cap_discharges(s, t, 1, 20);
}

/// control_example with process 1 holding only node 11, its control capability over process 2's
/// thread.
pub open spec fn thread_control_example() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 11usize) || h == (2usize, 20usize)),
        ..control_example()
    }
}

/// Control of a thread does not let its holder delete from the table of the thread's process or revoke
/// what is there, though it reaches what the process holds: a table is named through a process's
/// capability.
pub proof fn lemma_no_delete_or_revoke_through_a_thread()
    ensures
        !thread_control_example().commands(1, 20),
        !may_remove(thread_control_example(), 1, Effect::Local, 20),
        !authorized(thread_control_example(), 1, Effect::Revoke { cap: 20 }),
{
    let s = thread_control_example();
    assert(!s.holds(1, 20));
    assert forall|v: NodeId| #[trigger] s.holds_right(1, v, Right::Control) implies s.process_of.contains_key(s.names[v]) by {
        assert(v == 11);
        assert(s.names[11] == 3);
    }
}

/// Control of a process lets its holder place what it holds in the process's table, and move what
/// the process holds to another of its slots.
pub proof fn lemma_place_into_a_controlled_process()
    ensures
        authorized(control_example(), 1, Effect::Place { cap: 10, from: 11 }),
        authorized(control_example(), 1, Effect::Place { cap: 10, from: 20 }),
{
    let s = control_example();
    assert(s.holds_right(1, 10, Right::Control));
    assert(s.names[10] == 2);
    assert(!s.process_of.contains_key(2));
    assert(s.holds(1, 11));
    assert(s.holds(2, 20));
    assert(s.commands(1, 20));
}

/// Nothing is placed that the placer does not command: process 2 controls nothing, so it cannot place
/// what process 1 holds, and holding control of a thread of process 2 does not let a process place
/// what process 2 holds.
pub proof fn lemma_no_place_of_what_is_not_commanded()
    ensures
        !authorized(control_example(), 2, Effect::Place { cap: 20, from: 11 }),
        !authorized(thread_control_example(), 1, Effect::Place { cap: 11, from: 20 }),
        !thread_control_example().commands(1, 20),
{
    let s = control_example();
    assert(!s.rights.contains((20usize, Right::Control)));
    let t = thread_control_example();
    assert(t.names[11] == 3);
    assert(t.process_of.contains_key(3));
    assert(!t.holds(1, 20));
    assert forall|v: NodeId| #[trigger] t.holds_right(1, v, Right::Control) implies t.process_of.contains_key(t.names[v]) by {
        assert(v == 11);
        assert(t.names[11] == 3);
    }
}

/// Control of a thread does not let its holder place anything in the table of the thread's process.
pub proof fn lemma_no_place_through_a_thread()
    ensures
        !authorized(control_example(), 1, Effect::Place { cap: 11, from: 10 }),
{
    let s = control_example();
    assert(s.names[11] == 3);
    assert(s.process_of.contains_key(3));
}

/// control_example with process 1 also holding node 12, an untyped with the retype right on the 2M
/// block at EXAMPLE_BASE.
pub open spec fn leaf_example() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)|
            h == (1usize, 10usize) || h == (1usize, 11usize) || h == (1usize, 12usize) || h == (2usize, 20usize)),
        names: IMap::new(
            |n: NodeId| n == 10 || n == 11 || n == 12 || n == 20,
            |n: NodeId| if n == 10 { 2usize } else if n == 11 { 3usize } else { EXAMPLE_BASE },
        ),
        pages: IMap::new(|n: NodeId| n == 10 || n == 11 || n == 12 || n == 20, |n: NodeId| if n == 12 { 512nat } else { 1nat }),
        rights: ISet::new(|h: (NodeId, Right)|
            ((h.0 == 10 || h.0 == 11) && h.1 == Right::Control) || h == (12usize, Right::Retype)),
        ..control_example()
    }
}

/// A table leaf goes into the table of a process the caller controls, under the caller's untyped, and
/// the step changes nothing reach reads: a leaf is no capability, so nobody's reach grows.
pub proof fn lemma_leaf_into_a_controlled_process()
    ensures
        discharges(leaf_example(), leaf_example(), 1, Effect::Retype { untyped: 12, object: EXAMPLE_BASE, into: Some(10) }),
{
    let s = leaf_example();
    assert(s.holds_right(1, 12, Right::Retype));
    assert(s.holds_right(1, 10, Right::Control));
    assert(s.names[10] == 2);
    assert(!s.process_of.contains_key(2));
}

/// No leaf goes into a table through a thread's capability, though it carries control, or through a
/// capability without the control right: neither names a table.
pub proof fn lemma_no_leaf_without_control_of_the_process()
    ensures
        authorized(leaf_example(), 1, Effect::Retype { untyped: 12, object: EXAMPLE_BASE, into: None }),
        !authorized(leaf_example(), 1, Effect::Retype { untyped: 12, object: EXAMPLE_BASE, into: Some(11) }),
        !authorized(leaf_example(), 1, Effect::Retype { untyped: 12, object: EXAMPLE_BASE, into: Some(12) }),
{
    let s = leaf_example();
    assert(s.holds_right(1, 12, Right::Retype));
    assert(s.names[11] == 3);
    assert(s.process_of.contains_key(3));
    assert(!s.rights.contains((12usize, Right::Control)));
}

/// Process 1 holds node 10, an untyped with the retype right on the 2M block at EXAMPLE_BASE, and
/// process 2 holds node 20, on the page at EXAMPLE_PAST. Nobody holds the control right.
pub open spec fn retype_example() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 10usize) || h == (2usize, 20usize)),
        names: IMap::new(|n: NodeId| n == 10 || n == 20, |n: NodeId| if n == 10 { EXAMPLE_BASE } else { EXAMPLE_PAST }),
        pages: IMap::new(|n: NodeId| n == 10 || n == 20, |n: NodeId| if n == 10 { 512nat } else { 1nat }),
        rights: ISet::new(|h: (NodeId, Right)| h == (10usize, Right::Retype)),
        parent: Map::empty(),
        maps: Set::empty(),
        process_of: Map::empty(),
        waiting: Set::empty(),
        bound: Map::empty(),
        contents: |o: ObjectId| Seq::empty(),
    }
}

/// `retype_example` after process 1 types a thread at EXAMPLE_BASE into process 2, which it does not
/// control: node 11, a control capability on the thread, goes under the untyped, and the process map
/// says the thread is process 2's.
pub open spec fn bound_elsewhere() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 10usize) || h == (1usize, 11usize) || h == (2usize, 20usize)),
        names: IMap::new(
            |n: NodeId| n == 10 || n == 11 || n == 20,
            |n: NodeId| if n == 20 { EXAMPLE_PAST } else { EXAMPLE_BASE },
        ),
        pages: IMap::new(
            |n: NodeId| n == 10 || n == 11 || n == 20,
            |n: NodeId| if n == 10 { 512nat } else if n == 11 { 2nat } else { 1nat },
        ),
        rights: ISet::new(|h: (NodeId, Right)| h == (10usize, Right::Retype) || h == (11usize, Right::Control)),
        parent: map![11usize => 10usize],
        process_of: map![EXAMPLE_BASE => 2usize],
        ..retype_example()
    }
}

/// In `retype_example`, process 1 controls nobody, so it reaches its block alone.
proof fn lemma_retype_example_controls_nothing(q: ObjectId, k: nat)
    requires
        retype_example().controlled(1, q, k),
    ensures
        q == 1,
{
    if k > 0 {
        let s = retype_example();
        let m = choose|m: ObjectId| #[trigger] s.controls(m, q) && s.controlled(1, m, (k - 1) as nat);
        let c = choose|c: NodeId| #[trigger] s.holds_right(m, c, Right::Control) && s.process_behind(s.names[c]) == q;
        assert(!s.rights.contains((c, Right::Control)));
    }
}

/// Typing a thread into a process the caller does not control does not discharge a retype, though the
/// caller holds the untyped with the right: through the new capability the caller reaches what the
/// process holds, which is not the new object.
pub proof fn lemma_retype_into_uncontrolled_process_does_not_discharge()
    ensures
        authorized(retype_example(), 1, Effect::Retype { untyped: 10, object: EXAMPLE_BASE, into: None }),
        !discharges(retype_example(), bound_elsewhere(), 1, Effect::Retype { untyped: 10, object: EXAMPLE_BASE, into: None }),
{
    let (pre, post) = (retype_example(), bound_elsewhere());
    assert(pre.holds_right(1, 10, Right::Retype));
    assert(post.holds_right(1, 11, Right::Control));
    assert(post.process_behind(post.names[11]) == 2);
    assert(post.controls(1, 2));
    assert(post.controlled(1, 1, 0));
    assert(post.controlled(1, 2, 1));
    assert(post.descends(20, 20, 0));
    assert(post.holds(2, 20));
    assert(post.covers(20, EXAMPLE_PAST));
    assert(post.direct(2, EXAMPLE_PAST));
    assert(post.reach(1, EXAMPLE_PAST));
    if pre.reach(1, EXAMPLE_PAST) {
        let (q, k) = choose|q: ObjectId, k: nat| #[trigger] pre.controlled(1, q, k) && (EXAMPLE_PAST == q || pre.direct(q, EXAMPLE_PAST));
        lemma_retype_example_controls_nothing(q, k);
        let (c, n, d) = choose|c: NodeId, n: NodeId, d: nat| #[trigger] pre.descends(c, n, d)
            && pre.holds(1, c) && pre.covers(n, EXAMPLE_PAST);
        assert(c == n);
        assert(pre.held.contains((1usize, c)));
    }
    assert(!may_grow(pre, 1, Effect::Retype { untyped: 10, object: EXAMPLE_BASE, into: None }, 1, EXAMPLE_PAST));
}

/// A thread object, 0x5000, outside the example block.
pub const WAITER: usize = 0x5000;

/// `example` with WAITER a thread of process `owner`, waiting on nothing.
pub open spec fn waiter_example(owner: ObjectId) -> State {
    State { process_of: map![WAITER => owner], ..example() }
}

/// `waiter_example` with WAITER listed as waiting on EXAMPLE_BASE, which process 1 reaches.
pub open spec fn waiting_example(owner: ObjectId) -> State {
    State { waiting: set![(EXAMPLE_BASE, WAITER)], ..waiter_example(owner) }
}

/// A step by process 1 may list a thread of its own as waiting on an object it reaches.
pub proof fn lemma_own_waiter_discharges()
    ensures
        discharges(waiter_example(1), waiting_example(1), 1, Effect::Local),
{
    let (pre, post) = (waiter_example(1), waiting_example(1));
    assert(pre.descends(10, 10, 0));
    assert(pre.holds(1, 10));
    assert(pre.covers(10, EXAMPLE_BASE));
    assert(pre.direct(1, EXAMPLE_BASE));
    assert(pre.controlled(1, 1, 0));
    assert(pre.reach(1, EXAMPLE_BASE));
    assert forall|w: (ObjectId, ObjectId)| #[trigger] post.waiting.contains(w) && !pre.waiting.contains(w)
        implies may_wait(pre, 1, w) by {
        assert(w == (EXAMPLE_BASE, WAITER));
    }
    assert forall|o: ObjectId| #[trigger] State::changed(pre, post, o) implies may_change(pre, Effect::Local, o) by {
        assert((post.contents)(o) == (pre.contents)(o));
    }
    assert forall|r: ObjectId, o: ObjectId| #[trigger] post.reach(r, o) implies pre.reach(r, o) by {
        lemma_same_authority_same_reach(post, pre, r, o);
    }
}

/// A step by process 1 may not list a thread of process 2 as waiting on what process 1 reaches: a
/// grant over that object would then reach process 2.
pub proof fn lemma_other_waiter_does_not_discharge()
    ensures
        !discharges(waiter_example(2), waiting_example(2), 1, Effect::Local),
{
    let (pre, post) = (waiter_example(2), waiting_example(2));
    assert(post.waiting.contains((EXAMPLE_BASE, WAITER)));
    assert(!pre.waiting.contains((EXAMPLE_BASE, WAITER)));
    assert(!may_wait(pre, 1, (EXAMPLE_BASE, WAITER)));
}

/// Process 1 holds node 10, a capability to the endpoint at EXAMPLE_PAST with the send right alone.
pub open spec fn send_example() -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 10usize)),
        names: IMap::new(|n: NodeId| n == 10, |n: NodeId| EXAMPLE_PAST),
        pages: IMap::new(|n: NodeId| n == 10, |n: NodeId| 1nat),
        rights: ISet::new(|h: (NodeId, Right)| h == (10usize, Right::Send)),
        parent: Map::empty(),
        maps: Set::empty(),
        process_of: Map::empty(),
        waiting: Set::empty(),
        bound: Map::empty(),
        contents: |o: ObjectId| Seq::empty(),
    }
}

/// `send_example` after process 1 derives node 11 from node 10 into its own table, with the send right,
/// and with the grant right too when `grant` says so.
pub open spec fn derived_from_send(grant: bool) -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)| h == (1usize, 10usize) || h == (1usize, 11usize)),
        names: IMap::new(|n: NodeId| n == 10 || n == 11, |n: NodeId| EXAMPLE_PAST),
        pages: IMap::new(|n: NodeId| n == 10 || n == 11, |n: NodeId| 1nat),
        rights: ISet::new(
            |h: (NodeId, Right)| h == (10usize, Right::Send) || h == (11usize, Right::Send)
                || (grant && h == (11usize, Right::Grant)),
        ),
        parent: map![11usize => 10usize],
        ..send_example()
    }
}

/// Deriving the send right from a send-only capability discharges a local step.
pub proof fn lemma_derive_send_discharges()
    ensures
        discharges(send_example(), derived_from_send(false), 1, Effect::Local),
{
    let (pre, post) = (send_example(), derived_from_send(false));
    let live = |x: NodeId| x == 10;
    assert(post.parent =~= pre.parent.insert(11, 10));
    assert(adds_child(pre, post, 1, 10, 11, live));
    lemma_adds_child_discharges(pre, post, 1, 10, 11, live);
}

/// Deriving the grant right from it does not, though the child covers only what its parent covers and
/// grows nobody's reach: with grant, its holder could pass capabilities over an endpoint it was given
/// only to send on.
pub proof fn lemma_derive_grant_from_send_only_does_not_discharge()
    ensures
        !discharges(send_example(), derived_from_send(true), 1, Effect::Local),
{
    let (pre, post) = (send_example(), derived_from_send(true));
    assert(post.rights.contains((11usize, Right::Grant)) && post.names.contains_key(11));
    assert(!pre.names.contains_key(11));
    assert forall|s: NodeId| !(#[trigger] passes_right(pre, post, s, 11) && pre.rights.contains((s, Right::Grant))) by {
        assert(!pre.rights.contains((s, Right::Grant)));
    }
    assert(!may_hold(pre, post, Effect::Local, 11, Right::Grant));
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
