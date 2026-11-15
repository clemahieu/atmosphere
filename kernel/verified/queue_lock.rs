// SPDX-License-Identifier: MIT

//! The queue lock over the kernel's state. Each waiter spins on its own cache line, so the line holding
//! the lock's word does not bounce between every waiter on each handover. On this host a lock every
//! waiter spins on fell well below a queue lock across two CCDs, in the simulation recorded on the
//! multicore decision, design/multicore-kernel-shape/. This is an MCS lock with one node per core: a core holds the lock
//! at most once, since interrupts are off while it does.
//!
//! Mutual exclusion is a matter of ghost tokens. One set of tokens is allocated per lock: `Held`, and
//! for each core `Link(c)` and `Wait(c)`. Holding the lock is holding `Held`, and the set gives out
//! each token once, so two holders are impossible (`Core::lemma_exclusive`). `Held` moves between the
//! tail's invariant (lock free), the holder's `Core`, and a waiter's node (granted, not yet noticed).
//! `Link(c)` is the right to write `nodes[c].next`: it sits in the tail's invariant while c is the
//! tail, so the core that swaps the tail learns who to link behind and takes the right to do it.
//! `Wait(c)` proves c is queued: c hands it to its predecessor's node when it links, and the
//! predecessor brings it back together with `Held` when it clears c's flag. Each node also carries a
//! ghost variable of its state, whose other half is the core's `Core`, so a core knows its own node.
//!
//! Bounded overtaking is a matter of a ghost queue in the tail's invariant: the cores that have swapped
//! themselves in as the tail and not yet released, oldest first, and `served`, how many holdings of the
//! lock have ended. A core swapping in is not in the queue, which holds each core once, so at most
//! NUM_CPUS - 1 cores are ahead of it, and holdings end in queue order, so it holds the lock once
//! `served` has risen by at most NUM_CPUS - 1 (`QueueLock::acquire`). Three ghost resources keep the
//! queue true to the nodes: each core's place, its ticket while queued, which only its `Core` holds; each
//! core's behind, who swapped in right after it, which travels with `Link(c)` and so is in the node of
//! the core it names once that core links; and the front, which travels with `Held`.
//! design/one-lock-bounded-steps/.
use vstd::atomic::{PAtomicBool, PAtomicUsize, PermissionBool, PermissionUsize};
use vstd::atomic_ghost::{AtomicInvariantPredicate, AtomicUsize};
use vstd::atomic_with_ghost;
use vstd::open_atomic_invariant;
#[cfg(verus_keep_ghost)]
use vstd::invariant::AtomicInvariant;
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};
use vstd::resource::map::{GhostMapAuth, GhostPointsTo};
#[cfg(verus_keep_ghost)]
use vstd::resource::map::GhostSubmap;
#[cfg(verus_keep_ghost)]
use vstd::set_lib::{lemma_int_range, lemma_len_subset, set_int_range};
use vstd::resource::set::GhostSingleton;
#[cfg(verus_keep_ghost)]
use vstd::resource::set::{GhostSetAuth, GhostSubset};
use vstd::resource::Loc;

use crate::arch::spin_hint;
use crate::define::NUM_CPUS;

verus! {

/// What one ghost token stands for.
pub enum Token {
    /// The lock itself.
    Held,
    /// The right to write `nodes[c].next`.
    Link(int),
    /// Core c is queued.
    Wait(int),
}

/// A token, exclusive within its lock's set.
pub type Tok = GhostSingleton<Token>;

/// `t` is absent or is `token` of lock `loc`.
pub open spec fn tok_opt(t: Option<Tok>, loc: Loc, token: Token) -> bool {
    t matches Some(t) ==> t.id() == loc && t@ == token
}

/// Two copies of one token cannot exist.
proof fn lemma_clash(tracked a: &mut Tok, tracked b: &Tok)
    requires
        old(a).id() == b.id(),
        old(a)@ == b@,
    ensures
        false,
{
    a.disjoint(b);
}

/// Core c's ticket while queued: how many holdings will have ended when it holds the lock.
pub type Place = GhostPointsTo<int, Option<nat>>;

/// The core that swapped itself in as the tail right after core c, while there is one.
pub type Behind = GhostPointsTo<int, Option<int>>;

/// The core at the front of the queue, which holds the lock or has been granted it.
pub type Front = GhostVar<Option<int>>;

/// One core's place in the protocol, agreed between its node and its `Core`.
pub enum State {
    /// Not in the queue.
    Idle,
    /// Has swapped the tail and is waiting, or has just been granted the lock.
    Queued,
    /// Holds the lock.
    Holding,
    /// Releasing: the flag is reset, the successor not yet found.
    Resetting,
    /// Releasing: the successor is core `s`, whose `Wait` the holder has taken.
    Linked(int),
}

/// The ghost constant of one node's invariant.
pub struct NodeK {
    pub loc: Loc,
    pub cpu: int,
    pub next_id: int,
    pub waiting_id: int,
    pub state_id: Loc,
    pub behind_id: Loc,
    pub front_id: Loc,
}

/// What one node's invariant holds.
pub tracked struct NodeInv {
    pub tracked next: PermissionUsize,
    pub tracked waiting: PermissionBool,
    pub tracked state: GhostVarAuth<State>,
    /// `Link(cpu)`.
    pub tracked link: Option<Tok>,
    /// `Wait(cpu)`.
    pub tracked wait: Option<Tok>,
    /// `Held`, granted to this core.
    pub tracked held: Option<Tok>,
    /// `Wait(s)` of the successor linked here.
    pub tracked succ: Option<Tok>,
    /// This core's behind, which travels with `Link(cpu)`.
    pub tracked behind: Option<Behind>,
    /// The front, granted to this core with `Held`.
    pub tracked front: Option<Front>,
}

/// `b` is this node's behind, saying `val`.
pub open spec fn behind_is(b: Option<Behind>, k: NodeK, val: Option<int>) -> bool {
    b matches Some(b) && b.id() == k.behind_id && b.key() == k.cpu && b.value() == val
}

/// `f` is the front, naming this node's core.
pub open spec fn front_is(f: Option<Front>, k: NodeK) -> bool {
    f matches Some(f) && f.id() == k.front_id && f@ == Some(k.cpu)
}

/// `next` either names no successor and holds no link, or names `s` and holds `Link(cpu)`, the behind
/// that names `s`, and `Wait(s)`.
pub open spec fn next_part(k: NodeK, v: NodeInv, next: usize) -> bool {
    if next == 0 {
        v.link is None && v.succ is None && v.behind is None
    } else {
        next <= NUM_CPUS && v.link is Some && (v.succ matches Some(t) && t@ == Token::Wait(next - 1))
            && behind_is(v.behind, k, Some(next - 1))
    }
}

pub struct NodePred;

impl InvariantPredicate<NodeK, NodeInv> for NodePred {
    open spec fn inv(k: NodeK, v: NodeInv) -> bool {
        let next = v.next.view().value;
        let waiting = v.waiting.view().value;
        &&& v.next.view().patomic == k.next_id
        &&& v.waiting.view().patomic == k.waiting_id
        &&& v.state.id() == k.state_id
        &&& tok_opt(v.link, k.loc, Token::Link(k.cpu))
        &&& tok_opt(v.wait, k.loc, Token::Wait(k.cpu))
        &&& tok_opt(v.held, k.loc, Token::Held)
        &&& (v.succ matches Some(t) ==> t.id() == k.loc)
        &&& match v.state@ {
            State::Idle => {
                next == 0 && waiting && v.link is Some && v.wait is Some && v.held is None
                    && v.succ is None && behind_is(v.behind, k, None) && v.front is None
            },
            State::Queued => {
                next_part(k, v, next) && (if waiting {
                    v.held is None && v.wait is None && v.front is None
                } else {
                    v.held is Some && v.wait is Some && front_is(v.front, k)
                })
            },
            State::Holding => next_part(k, v, next) && v.wait is Some && v.held is None && v.front is None,
            State::Resetting => {
                next_part(k, v, next) && waiting && v.wait is Some && v.held is None && v.front is None
            },
            State::Linked(s) => {
                next == s + 1 && 0 <= s < NUM_CPUS && waiting && v.link is Some && v.wait is Some
                    && v.held is None && v.succ is None && v.behind is None && v.front is None
            },
        }
    }
}

/// One core's place in the queue, on its own cache line.
#[repr(align(64))]
pub struct Node {
    /// The next waiter's core plus one, or 0.
    next: PAtomicUsize,
    /// True while this core waits.
    waiting: PAtomicBool,
    // Read only inside open_atomic_invariant!, which a cargo build erases, so only Verus compiles it.
    #[cfg(verus_keep_ghost)]
    inv: Tracked<AtomicInvariant<NodeK, NodeInv, NodePred>>,
}

/// The ghost state one node starts with.
pub tracked struct NodeInit {
    pub tracked state: GhostVarAuth<State>,
    pub tracked link: Tok,
    pub tracked wait: Tok,
    pub tracked behind: Behind,
}

impl Node {
    pub closed spec fn state_id(self) -> Loc {
        self.inv@.constant().state_id
    }

    pub closed spec fn wf(self, tk: TailK, cpu: int) -> bool {
        let k = self.inv@.constant();
        &&& k.loc == tk.loc
        &&& k.behind_id == tk.behind_id
        &&& k.front_id == tk.front_id
        &&& k.cpu == cpu
        &&& k.next_id == self.next.id()
        &&& k.waiting_id == self.waiting.id()
    }

    const fn new(Ghost(tk): Ghost<TailK>, Ghost(cpu): Ghost<int>, Tracked(init): Tracked<NodeInit>) -> (n: Node)
        requires
            init.state@ == State::Idle,
            init.link.id() == tk.loc,
            init.link@ == Token::Link(cpu),
            init.wait.id() == tk.loc,
            init.wait@ == Token::Wait(cpu),
            init.behind.id() == tk.behind_id,
            init.behind.key() == cpu,
            init.behind.value() is None,
        ensures
            n.wf(tk, cpu),
            n.state_id() == init.state.id(),
    {
        let (next, Tracked(next_perm)) = PAtomicUsize::new(0);
        let (waiting, Tracked(waiting_perm)) = PAtomicBool::new(true);
        let tracked NodeInit { state, link, wait, behind } = init;
        let ghost k = NodeK {
            loc: tk.loc,
            cpu,
            next_id: next.id(),
            waiting_id: waiting.id(),
            state_id: state.id(),
            behind_id: tk.behind_id,
            front_id: tk.front_id,
        };
        let tracked v = NodeInv {
            next: next_perm,
            waiting: waiting_perm,
            state,
            link: Some(link),
            wait: Some(wait),
            held: None,
            succ: None,
            behind: Some(behind),
            front: None,
        };
        let tracked inv = AtomicInvariant::new(k, v, 1);
        Node {
            next,
            waiting,
            #[cfg(verus_keep_ghost)]
            inv: Tracked(inv),
        }
    }
}

/// The ghost constant of the tail: the lock's token set and the ids of the queue's resources.
pub struct TailK {
    pub loc: Loc,
    pub place_id: Loc,
    pub behind_id: Loc,
    pub front_id: Loc,
}

/// What the tail's invariant holds: the token the tail stands for, and the queue.
pub tracked struct TailG {
    /// `Held` while the lock is free, `Link(c)` while core c is the tail.
    pub tracked tok: Tok,
    /// The tail core's behind, naming nobody yet.
    pub tracked behind: Option<Behind>,
    /// The front, while the lock is free.
    pub tracked front: Option<Front>,
    pub tracked places: GhostMapAuth<int, Option<nat>>,
    pub tracked behinds: GhostMapAuth<int, Option<int>>,
    pub tracked fronts: GhostVarAuth<Option<int>>,
    /// The cores that have swapped themselves in as the tail and not yet released, oldest first.
    pub ghost queue: Seq<int>,
    /// How many holdings of the lock have ended.
    pub ghost served: nat,
}

/// The queue holds each core at most once; the core at position i has ticket `served + i` and the
/// core at i + 1 behind it, the last has nobody behind it, and the first is the front.
pub open spec fn queue_ok(k: TailK, g: TailG) -> bool {
    let q = g.queue;
    &&& q.no_duplicates()
    &&& forall|i: int| 0 <= i < q.len() ==> 0 <= #[trigger] q[i] < NUM_CPUS
    &&& g.places.id() == k.place_id
    &&& g.behinds.id() == k.behind_id
    &&& g.fronts.id() == k.front_id
    &&& forall|i: int| #![trigger q[i]] 0 <= i < q.len() ==> g.places@.contains_pair(q[i], Some((g.served + i) as nat))
    &&& forall|i: int| #![trigger q[i]] 0 <= i < q.len() - 1 ==> g.behinds@.contains_pair(q[i], Some(q[i + 1]))
    &&& q.len() > 0 ==> g.behinds@.contains_pair(q.last(), None)
    &&& g.fronts@ == (if q.len() == 0 { None } else { Some(q[0]) })
}

/// The tail holds the lock and the front while 0, and the right to link behind core c, with c's
/// behind, while c + 1, when c is the last of the queue.
pub struct TailPred;

impl AtomicInvariantPredicate<TailK, usize, TailG> for TailPred {
    open spec fn atomic_inv(k: TailK, tail: usize, g: TailG) -> bool {
        &&& tail <= NUM_CPUS
        &&& g.tok.id() == k.loc
        &&& g.tok@ == (if tail == 0 { Token::Held } else { Token::Link(tail - 1) })
        &&& queue_ok(k, g)
        &&& (tail == 0 <==> g.queue.len() == 0)
        &&& if tail == 0 {
            g.behind is None && (g.front matches Some(f) && f.id() == k.front_id)
        } else {
            &&& g.queue.last() == tail - 1
            &&& g.front is None
            &&& g.behind matches Some(b) && b.id() == k.behind_id && b.key() == tail - 1 && b.value() is None
        }
    }
}

/// A queue holding each core at most once, without core c, has room for c.
proof fn lemma_room(q: Seq<int>, c: int)
    requires
        q.no_duplicates(),
        forall|i: int| 0 <= i < q.len() ==> 0 <= #[trigger] q[i] < NUM_CPUS,
        0 <= c < NUM_CPUS,
        !q.contains(c),
    ensures
        q.len() <= NUM_CPUS - 1,
{
    q.unique_seq_to_set();
    q.to_set_ensures();
    let others = set_int_range(0, NUM_CPUS as int).remove(c);
    lemma_int_range(0, NUM_CPUS as int);
    assert forall|x: int| q.to_set().contains(x) implies others.contains(x) by {
        let i = choose|i: int| 0 <= i < q.len() && q[i] == x;
    }
    lemma_len_subset(q.to_set(), others);
}

/// A core's half of the protocol: its node's state, and the tokens it carries.
pub tracked struct Core {
    pub ghost loc: Loc,
    pub ghost place_id: Loc,
    pub ghost behind_id: Loc,
    pub ghost front_id: Loc,
    pub ghost cpu: int,
    pub tracked state: GhostVar<State>,
    /// `Held`, while holding.
    pub tracked held: Option<Tok>,
    /// A link right in transit: its own on the way to the tail, its predecessor's on the way back.
    pub tracked link: Option<Tok>,
    /// Its own `Wait`, on the way to its predecessor.
    pub tracked wait: Option<Tok>,
    /// Its successor's `Wait`, on the way back to the successor.
    pub tracked succ: Option<Tok>,
    /// Its place, which only it holds.
    pub tracked place: Place,
    /// The behind that travels with `link`, or its own while it hands on the lock.
    pub tracked behind: Option<Behind>,
    /// The front, while holding.
    pub tracked front: Option<Front>,
    /// How many holdings had ended when it last swapped itself in as the tail.
    pub ghost swapped: nat,
    /// How many holdings had ended when it last came to hold the lock.
    pub ghost granted: nat,
}

impl Core {
    pub open spec fn wf(self) -> bool {
        &&& tok_opt(self.held, self.loc, Token::Held)
        &&& tok_opt(self.wait, self.loc, Token::Wait(self.cpu))
        &&& (self.link matches Some(t) ==> t.id() == self.loc)
        &&& (self.succ matches Some(t) ==> t.id() == self.loc)
        &&& self.place.id() == self.place_id
        &&& self.place.key() == self.cpu
        &&& (self.behind matches Some(b) ==> b.id() == self.behind_id)
        &&& (self.front matches Some(f) ==> f.id() == self.front_id)
    }

    /// The core is out of the queue.
    pub open spec fn idle(self) -> bool {
        &&& self.wf()
        &&& self.state@ == State::Idle
        &&& self.held is None
        &&& self.link is None
        &&& self.wait is None
        &&& self.succ is None
        &&& self.place.value() is None
        &&& self.behind is None
        &&& self.front is None
    }

    /// The core holds the lock.
    pub open spec fn holding(self) -> bool {
        &&& self.wf()
        &&& self.state@ == State::Holding
        &&& self.held is Some
        &&& self.link is None
        &&& self.wait is None
        &&& self.succ is None
        &&& self.place.value() is Some
        &&& self.behind is None
        &&& self.front matches Some(f) && f@ == Some(self.cpu)
    }

    /// The core belongs to `lock`.
    pub open spec fn for_lock(self, lock: QueueLock) -> bool {
        &&& self.loc == lock.loc()
        &&& self.place_id == lock.tail_k().place_id
        &&& self.behind_id == lock.tail_k().behind_id
        &&& self.front_id == lock.tail_k().front_id
        &&& 0 <= self.cpu < NUM_CPUS
        &&& self.state.id() == lock.state_id(self.cpu)
    }

    /// Two cores cannot hold one lock.
    pub proof fn lemma_exclusive(tracked a: Core, tracked b: Core)
        requires
            a.holding(),
            b.holding(),
            a.loc == b.loc,
        ensures
            false,
    {
        let tracked mut held = a.held.tracked_unwrap();
        lemma_clash(&mut held, b.held.tracked_borrow());
    }
}

/// `Held`, and `Link(c)` and `Wait(c)` for every core c below `n`.
pub open spec fn tokens_below(n: int) -> Set<Token>
    decreases n,
{
    if n <= 0 {
        set![Token::Held]
    } else {
        tokens_below(n - 1).insert(Token::Link(n - 1)).insert(Token::Wait(n - 1))
    }
}

proof fn lemma_tokens_below(n: int, c: int)
    requires
        0 <= c < n,
    ensures
        tokens_below(n).contains(Token::Link(c)),
        tokens_below(n).contains(Token::Wait(c)),
    decreases n,
{
    if c < n - 1 {
        lemma_tokens_below(n - 1, c);
    }
}

proof fn lemma_tokens_held(n: int)
    requires
        0 <= n,
    ensures
        tokens_below(n).contains(Token::Held),
    decreases n,
{
    if n > 0 {
        lemma_tokens_held(n - 1);
    }
}

/// `init` starts node `c` of the lock whose tail constant is `k`, and `core` is that core's half.
pub open spec fn init_ok(init: NodeInit, core: Core, k: TailK, c: int) -> bool {
    &&& init.state@ == State::Idle
    &&& init.link.id() == k.loc
    &&& init.link@ == Token::Link(c)
    &&& init.wait.id() == k.loc
    &&& init.wait@ == Token::Wait(c)
    &&& init.behind.id() == k.behind_id
    &&& init.behind.key() == c
    &&& init.behind.value() is None
    &&& core.idle()
    &&& core.loc == k.loc
    &&& core.place_id == k.place_id
    &&& core.behind_id == k.behind_id
    &&& core.front_id == k.front_id
    &&& core.cpu == c
    &&& core.state.id() == init.state.id()
}

/// `inits` and `cores` start every core from `from` up.
pub open spec fn inits_ok(inits: Map<int, NodeInit>, cores: Map<int, Core>, k: TailK, from: int) -> bool {
    forall|c: int|
        from <= c < NUM_CPUS ==> #[trigger] inits.dom().contains(c) && cores.dom().contains(c)
            && init_ok(inits[c], cores[c], k, c)
}

/// Takes the node starts for cores `from..NUM_CPUS` out of `tokens`, `places` and `behinds`, with
/// the cores' halves.
proof fn make_inits(
    tracked tokens: &mut GhostSubset<Token>,
    tracked places: &mut GhostSubmap<int, Option<nat>>,
    tracked behinds: &mut GhostSubmap<int, Option<int>>,
    k: TailK,
    from: int,
) -> (tracked r: (Map<int, NodeInit>, Map<int, Core>))
    requires
        0 <= from <= NUM_CPUS,
        old(tokens).id() == k.loc,
        old(places).id() == k.place_id,
        old(behinds).id() == k.behind_id,
        forall|c: int| from <= c < NUM_CPUS ==> #[trigger] old(tokens)@.contains(Token::Link(c)),
        forall|c: int| from <= c < NUM_CPUS ==> #[trigger] old(tokens)@.contains(Token::Wait(c)),
        forall|c: int| from <= c < NUM_CPUS ==> #[trigger] old(places)@.contains_pair(c, None),
        forall|c: int| from <= c < NUM_CPUS ==> #[trigger] old(behinds)@.contains_pair(c, None),
    ensures
        final(tokens).id() == old(tokens).id(),
        final(places).id() == old(places).id(),
        final(behinds).id() == old(behinds).id(),
        inits_ok(r.0, r.1, k, from),
    decreases NUM_CPUS - from,
{
    if from == NUM_CPUS {
        (Map::tracked_empty(), Map::tracked_empty())
    } else {
        let tracked (auth, var) = GhostVarAuth::new(State::Idle);
        assert(places@.contains_pair(from, None));
        assert(behinds@.contains_pair(from, None));
        let tracked link = tokens.split_singleton(Token::Link(from));
        let tracked wait = tokens.split_singleton(Token::Wait(from));
        let tracked place = places.split_points_to(from);
        let tracked behind = behinds.split_points_to(from);
        assert forall|c: int| from + 1 <= c < NUM_CPUS implies #[trigger] places@.contains_pair(c, None) by {
            assert(old(places)@.contains_pair(c, None));
        }
        assert forall|c: int| from + 1 <= c < NUM_CPUS implies #[trigger] behinds@.contains_pair(c, None) by {
            assert(old(behinds)@.contains_pair(c, None));
        }
        let tracked (mut inits, mut cores) = make_inits(tokens, places, behinds, k, from + 1);
        let ghost rest = inits;
        inits.tracked_insert(from, NodeInit { state: auth, link, wait, behind });
        cores.tracked_insert(
            from,
            Core {
                loc: k.loc,
                place_id: k.place_id,
                behind_id: k.behind_id,
                front_id: k.front_id,
                cpu: from,
                state: var,
                held: None,
                link: None,
                wait: None,
                succ: None,
                place,
                behind: None,
                front: None,
                swapped: 0,
                granted: 0,
            },
        );
        assert forall|c: int|
            from <= c < NUM_CPUS implies #[trigger] inits.dom().contains(c) && cores.dom().contains(c)
                && init_ok(inits[c], cores[c], k, c) by {
            if c != from {
                assert(rest.dom().contains(c));
            }
        }
        (inits, cores)
    }
}

/// Takes core `c`'s node start out of `inits`.
proof fn take_init(tracked inits: &mut Map<int, NodeInit>, cores: Map<int, Core>, k: TailK, c: int) -> (tracked init:
    NodeInit)
    requires
        0 <= c < NUM_CPUS,
        inits_ok(*old(inits), cores, k, c),
    ensures
        init_ok(init, cores[c], k, c),
        inits_ok(*final(inits), cores, k, c + 1),
{
    assert(old(inits).dom().contains(c));
    let tracked init = inits.tracked_remove(c);
    assert forall|d: int|
        c + 1 <= d < NUM_CPUS implies #[trigger] inits.dom().contains(d) && cores.dom().contains(d)
            && init_ok(inits[d], cores[d], k, d) by {
        assert(old(inits).dom().contains(d));
    }
    init
}

pub struct QueueLock {
    /// The last waiter's core plus one, or 0 when the lock is free.
    tail: AtomicUsize<TailK, TailG, TailPred>,
    nodes: [Node; NUM_CPUS],
}

impl QueueLock {
    /// The lock's token set.
    pub closed spec fn loc(self) -> Loc {
        self.tail.constant().loc
    }

    /// The tail's ghost constant.
    pub closed spec fn tail_k(self) -> TailK {
        self.tail.constant()
    }

    /// The ghost variable of core `cpu`'s node.
    pub closed spec fn state_id(self, cpu: int) -> Loc {
        self.nodes[cpu].state_id()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.tail.well_formed()
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] self.nodes[c]).wf(self.tail.constant(), c)
    }

    /// A free lock, with one `Core` per core.
    pub const fn new() -> (r: (Self, Tracked<Map<int, Core>>))
        ensures
            r.0.wf(),
            forall|c: int|
                0 <= c < NUM_CPUS ==> #[trigger] r.1@.dom().contains(c) && r.1@[c].idle()
                    && r.1@[c].cpu == c && r.1@[c].for_lock(r.0),
    {
        // The authority is dropped: the set never grows, so each token stays the only one.
        let tracked (_auth, mut tokens) = GhostSetAuth::<Token>::new(tokens_below(NUM_CPUS as int));
        proof {
            lemma_tokens_held(NUM_CPUS as int);
        }
        let tracked held = tokens.split_singleton(Token::Held);
        let ghost loc = held.id();
        proof {
            assert forall|c: int| 0 <= c < NUM_CPUS implies tokens@.contains(Token::Link(c))
                && tokens@.contains(Token::Wait(c)) by {
                lemma_tokens_below(NUM_CPUS as int, c);
            }
        }
        let ghost nobody = Map::new(set_int_range(0, NUM_CPUS as int), |d: int| None::<int>);
        let ghost unqueued = Map::new(set_int_range(0, NUM_CPUS as int), |d: int| None::<nat>);
        proof {
            lemma_int_range(0, NUM_CPUS as int);
        }
        let tracked (places, mut place_parts) = GhostMapAuth::<int, Option<nat>>::new(unqueued);
        let tracked (behinds, mut behind_parts) = GhostMapAuth::<int, Option<int>>::new(nobody);
        let tracked (fronts, front) = GhostVarAuth::<Option<int>>::new(None);
        let ghost k = TailK { loc, place_id: places.id(), behind_id: behinds.id(), front_id: fronts.id() };
        let tracked (mut inits, cores) = make_inits(&mut tokens, &mut place_parts, &mut behind_parts, k, 0);
        let ghost all = inits;
        let tracked g = TailG {
            tok: held,
            behind: None,
            front: Some(front),
            places,
            behinds,
            fronts,
            queue: Seq::empty(),
            served: 0,
        };
        let tail = AtomicUsize::new(Ghost(k), 0, Tracked(g));
        let nodes = [
            Node::new(Ghost(k), Ghost(0), Tracked(take_init(&mut inits, cores, k, 0))),
            Node::new(Ghost(k), Ghost(1), Tracked(take_init(&mut inits, cores, k, 1))),
            Node::new(Ghost(k), Ghost(2), Tracked(take_init(&mut inits, cores, k, 2))),
            Node::new(Ghost(k), Ghost(3), Tracked(take_init(&mut inits, cores, k, 3))),
            Node::new(Ghost(k), Ghost(4), Tracked(take_init(&mut inits, cores, k, 4))),
            Node::new(Ghost(k), Ghost(5), Tracked(take_init(&mut inits, cores, k, 5))),
            Node::new(Ghost(k), Ghost(6), Tracked(take_init(&mut inits, cores, k, 6))),
            Node::new(Ghost(k), Ghost(7), Tracked(take_init(&mut inits, cores, k, 7))),
            Node::new(Ghost(k), Ghost(8), Tracked(take_init(&mut inits, cores, k, 8))),
            Node::new(Ghost(k), Ghost(9), Tracked(take_init(&mut inits, cores, k, 9))),
            Node::new(Ghost(k), Ghost(10), Tracked(take_init(&mut inits, cores, k, 10))),
            Node::new(Ghost(k), Ghost(11), Tracked(take_init(&mut inits, cores, k, 11))),
            Node::new(Ghost(k), Ghost(12), Tracked(take_init(&mut inits, cores, k, 12))),
            Node::new(Ghost(k), Ghost(13), Tracked(take_init(&mut inits, cores, k, 13))),
            Node::new(Ghost(k), Ghost(14), Tracked(take_init(&mut inits, cores, k, 14))),
            Node::new(Ghost(k), Ghost(15), Tracked(take_init(&mut inits, cores, k, 15))),
            Node::new(Ghost(k), Ghost(16), Tracked(take_init(&mut inits, cores, k, 16))),
            Node::new(Ghost(k), Ghost(17), Tracked(take_init(&mut inits, cores, k, 17))),
            Node::new(Ghost(k), Ghost(18), Tracked(take_init(&mut inits, cores, k, 18))),
            Node::new(Ghost(k), Ghost(19), Tracked(take_init(&mut inits, cores, k, 19))),
            Node::new(Ghost(k), Ghost(20), Tracked(take_init(&mut inits, cores, k, 20))),
            Node::new(Ghost(k), Ghost(21), Tracked(take_init(&mut inits, cores, k, 21))),
            Node::new(Ghost(k), Ghost(22), Tracked(take_init(&mut inits, cores, k, 22))),
            Node::new(Ghost(k), Ghost(23), Tracked(take_init(&mut inits, cores, k, 23))),
            Node::new(Ghost(k), Ghost(24), Tracked(take_init(&mut inits, cores, k, 24))),
            Node::new(Ghost(k), Ghost(25), Tracked(take_init(&mut inits, cores, k, 25))),
            Node::new(Ghost(k), Ghost(26), Tracked(take_init(&mut inits, cores, k, 26))),
            Node::new(Ghost(k), Ghost(27), Tracked(take_init(&mut inits, cores, k, 27))),
            Node::new(Ghost(k), Ghost(28), Tracked(take_init(&mut inits, cores, k, 28))),
            Node::new(Ghost(k), Ghost(29), Tracked(take_init(&mut inits, cores, k, 29))),
            Node::new(Ghost(k), Ghost(30), Tracked(take_init(&mut inits, cores, k, 30))),
            Node::new(Ghost(k), Ghost(31), Tracked(take_init(&mut inits, cores, k, 31))),
        ];
        proof {
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] cores.dom().contains(c) && cores[c].idle()
                && cores[c].cpu == c && cores[c].for_lock(QueueLock { tail, nodes }) by {
                assert(all.dom().contains(c));
            }
        }
        (QueueLock { tail, nodes }, Tracked(cores))
    }

    /// Waits for the lock on behalf of `cpu`, which must not hold it. Between the swap that queues it
    /// and the lock, at most NUM_CPUS - 1 holdings end: `granted - swapped` counts them.
    #[verifier::exec_allows_no_decreases_clause]
    // exec_allows_no_decreases_clause(unproven): the spin waits for the holder to hand over: at most NUM_CPUS - 1 holdings end first, which bounds the wait only while every core keeps executing
    pub fn acquire(&self, cpu: usize, Tracked(core): Tracked<&mut Core>)
        requires
            self.wf(),
            cpu < NUM_CPUS,
            old(core).idle(),
            old(core).cpu == cpu,
            old(core).for_lock(*self),
        ensures
            final(core).holding(),
            final(core).cpu == cpu,
            final(core).for_lock(*self),
            final(core).swapped <= final(core).granted,
            final(core).granted <= final(core).swapped + NUM_CPUS - 1,
    {
        let node = &self.nodes[cpu];
        // Leave idle, taking the node's link right, behind and queued token along.
        open_atomic_invariant!(node.inv.borrow() => ni => {
            proof {
                ni.state.agree(&core.state);
                core.link = Some(ni.link.tracked_take());
                core.wait = Some(ni.wait.tracked_take());
                core.behind = Some(ni.behind.tracked_take());
                ni.state.update(&mut core.state, State::Queued);
            }
        });
        let ghost mut ticket: nat = 0;
        let previous = atomic_with_ghost!(self.tail => swap(cpu + 1); update prev -> next; ghost g => {
            let ghost q = g.queue;
            let tracked mut mine_b = core.behind.tracked_take();
            mine_b.agree(&g.behinds);
            core.place.agree(&g.places);
            if q.contains(cpu as int) {
                let i = choose|i: int| 0 <= i < q.len() && q[i] == cpu as int;
                assert(g.places@.contains_pair(q[i], Some((g.served + i) as nat)));
            }
            lemma_room(q, cpu as int);
            ticket = (g.served + q.len()) as nat;
            core.swapped = g.served;
            core.place.update(&mut g.places, Some(ticket));
            let tracked mut mine = core.link.tracked_take();
            vstd::modes::tracked_swap(&mut g.tok, &mut mine);
            if prev == 0 {
                core.held = Some(mine);
                let tracked mut f = g.front.tracked_take();
                g.fronts.update(&mut f, Some(cpu as int));
                core.front = Some(f);
            } else {
                core.link = Some(mine);
                let tracked mut pb = g.behind.tracked_take();
                pb.update(&mut g.behinds, Some(cpu as int));
                core.behind = Some(pb);
            }
            g.behind = Some(mine_b);
            g.queue = q.push(cpu as int);
            assert(g.queue.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < j < g.queue.len() implies g.queue[i] != g.queue[j] by {
                    if j == q.len() {
                        assert(q[i] == g.queue[i]);
                    } else {
                        assert(q[i] != q[j]);
                    }
                }
            }
            assert forall|i: int| #![trigger g.queue[i]] 0 <= i < g.queue.len() - 1
                implies g.behinds@.contains_pair(g.queue[i], Some(g.queue[i + 1])) by {
                if i < q.len() - 1 {
                    assert(q[i] != q[q.len() - 1]);
                    assert(g.behinds@.contains_pair(q[i], Some(q[i + 1])));
                }
            }
            assert forall|i: int| #![trigger g.queue[i]] 0 <= i < g.queue.len()
                implies g.places@.contains_pair(g.queue[i], Some((g.served + i) as nat)) by {
                if i < q.len() {
                    assert(g.places@.contains_pair(q[i], Some((g.served + i) as nat)));
                }
            }
            assert(prev <= NUM_CPUS);
        });
        if previous != 0 {
            // Link behind the previous tail, handing it `Wait(cpu)` and its behind, which names cpu.
            let pred = &self.nodes[previous - 1];
            open_atomic_invariant!(pred.inv.borrow() => ni => {
                pred.next.store(Tracked(&mut ni.next), cpu + 1);
                proof {
                    if ni.link is Some {
                        let tracked mut l = core.link.tracked_take();
                        lemma_clash(&mut l, ni.link.tracked_borrow());
                    }
                    ni.link = Some(core.link.tracked_take());
                    ni.succ = Some(core.wait.tracked_take());
                    ni.behind = Some(core.behind.tracked_take());
                }
            });
            let mut waiting = true;
            while waiting
                invariant
                    self.wf(),
                    cpu < NUM_CPUS,
                    core.wf(),
                    core.cpu == cpu,
                    core.for_lock(*self),
                    core.link is None,
                    core.wait is None,
                    core.succ is None,
                    core.behind is None,
                    core.place.value() == Some(ticket),
                    core.swapped <= ticket <= core.swapped + NUM_CPUS - 1,
                    waiting ==> core.state@ == State::Queued && core.held is None && core.front is None,
                    !waiting ==> core.holding(),
            {
                let node = &self.nodes[cpu];
                open_atomic_invariant!(node.inv.borrow() => ni => {
                    waiting = node.waiting.load(Tracked(&ni.waiting));
                    proof {
                        ni.state.agree(&core.state);
                        if !waiting {
                            core.held = Some(ni.held.tracked_take());
                            core.front = Some(ni.front.tracked_take());
                            ni.state.update(&mut core.state, State::Holding);
                        }
                    }
                });
                if waiting {
                    spin_hint();
                }
            }
        } else {
            // The lock was free: hold it, leaving `Wait(cpu)` on the node.
            open_atomic_invariant!(node.inv.borrow() => ni => {
                proof {
                    ni.state.agree(&core.state);
                    if ni.wait is Some {
                        let tracked mut w = core.wait.tracked_take();
                        lemma_clash(&mut w, ni.wait.tracked_borrow());
                    }
                    ni.wait = Some(core.wait.tracked_take());
                    ni.state.update(&mut core.state, State::Holding);
                }
            });
        }
        // At the front, the ticket is how many holdings have ended.
        atomic_with_ghost!(self.tail => no_op(); ghost g => {
            g.fronts.agree(core.front.tracked_borrow());
            core.place.agree(&g.places);
            assert(g.places@.contains_pair(g.queue[0], Some((g.served + 0) as nat)));
            core.granted = g.served;
        });
    }

    /// Hands the lock on from `cpu`, which must hold it. The spin ends when the waiter that swapped
    /// the tail links itself, which it does straight after its swap.
    #[verifier::exec_allows_no_decreases_clause]
    // exec_allows_no_decreases_clause(unproven): the spin waits for the successor that swapped the tail to link itself, which follows its swap with no loop between and so ends only while that core keeps executing
    pub fn release(&self, cpu: usize, Tracked(core): Tracked<&mut Core>)
        requires
            self.wf(),
            cpu < NUM_CPUS,
            old(core).holding(),
            old(core).cpu == cpu,
            old(core).for_lock(*self),
        ensures
            final(core).idle(),
            final(core).cpu == cpu,
            final(core).for_lock(*self),
    {
        let node = &self.nodes[cpu];
        // Reset the flag for the next wait.
        open_atomic_invariant!(node.inv.borrow() => ni => {
            node.waiting.store(Tracked(&mut ni.waiting), true);
            proof {
                ni.state.agree(&core.state);
                ni.state.update(&mut core.state, State::Resetting);
            }
        });
        let mut next = 0;
        open_atomic_invariant!(node.inv.borrow() => ni => {
            next = node.next.load(Tracked(&ni.next));
            proof {
                ni.state.agree(&core.state);
                if next != 0 {
                    core.succ = Some(ni.succ.tracked_take());
                    core.behind = Some(ni.behind.tracked_take());
                    ni.state.update(&mut core.state, State::Linked(next - 1));
                }
            }
        });
        if next == 0 {
            let freed = atomic_with_ghost!(self.tail => compare_exchange(cpu + 1, 0); update prev -> after; returning ret; ghost g => {
                if ret is Ok {
                    // cpu is both the front and the last of the queue, so it is all of it.
                    let ghost q = g.queue;
                    g.fronts.agree(core.front.tracked_borrow());
                    if q.len() > 1 {
                        assert(q[0] != q[q.len() - 1]);
                    }
                    core.place.update(&mut g.places, None);
                    let tracked mut f = core.front.tracked_take();
                    g.fronts.update(&mut f, None);
                    g.front = Some(f);
                    let tracked mut h = core.held.tracked_take();
                    vstd::modes::tracked_swap(&mut g.tok, &mut h);
                    core.link = Some(h);
                    vstd::modes::tracked_swap(&mut core.behind, &mut g.behind);
                    g.queue = Seq::empty();
                    g.served = g.served + 1;
                }
            });
            if freed.is_ok() {
                // Nobody linked: the link right and the behind are back, so the node is idle again.
                open_atomic_invariant!(node.inv.borrow() => ni => {
                    proof {
                        ni.state.agree(&core.state);
                        if ni.link is Some {
                            let tracked mut l = core.link.tracked_take();
                            lemma_clash(&mut l, ni.link.tracked_borrow());
                        }
                        ni.link = Some(core.link.tracked_take());
                        vstd::modes::tracked_swap(&mut ni.behind, &mut core.behind);
                        ni.state.update(&mut core.state, State::Idle);
                    }
                });
                return;
            }
            // A waiter has swapped the tail and is about to link itself.
            while next == 0
                invariant
                    self.wf(),
                    cpu < NUM_CPUS,
                    core.wf(),
                    core.cpu == cpu,
                    core.for_lock(*self),
                    core.held is Some,
                    core.link is None,
                    core.wait is None,
                    core.place.value() is Some,
                    core.front matches Some(f) && f@ == Some(cpu as int),
                    next == 0 ==> core.state@ == State::Resetting && core.succ is None && core.behind is None,
                    next != 0 ==> next <= NUM_CPUS && core.state@ == State::Linked(next - 1)
                        && (core.succ matches Some(t) && t@ == Token::Wait(next - 1))
                        && (core.behind matches Some(b) && b.key() == cpu && b.value() == Some(next - 1)),
            {
                spin_hint();
                let node = &self.nodes[cpu];
                open_atomic_invariant!(node.inv.borrow() => ni => {
                    next = node.next.load(Tracked(&ni.next));
                    proof {
                        ni.state.agree(&core.state);
                        if next != 0 {
                            core.succ = Some(ni.succ.tracked_take());
                            core.behind = Some(ni.behind.tracked_take());
                            ni.state.update(&mut core.state, State::Linked(next - 1));
                        }
                    }
                });
            }
        }
        // Leave the queue: the successor, which cpu's behind names, is its front now.
        atomic_with_ghost!(self.tail => no_op(); ghost g => {
            let ghost q = g.queue;
            let ghost s = (next - 1) as int;
            g.fronts.agree(core.front.tracked_borrow());
            core.behind.tracked_borrow().agree(&g.behinds);
            if q.len() == 1 {
                assert(g.behinds@.contains_pair(q.last(), None));
            }
            assert(g.behinds@.contains_pair(q[0], Some(q[1])));
            core.place.update(&mut g.places, None);
            let tracked mut b = core.behind.tracked_take();
            b.update(&mut g.behinds, None);
            core.behind = Some(b);
            let tracked mut f = core.front.tracked_take();
            g.fronts.update(&mut f, Some(s));
            core.front = Some(f);
            g.queue = q.drop_first();
            g.served = g.served + 1;
            assert forall|i: int| #![trigger g.queue[i]] 0 <= i < g.queue.len()
                implies g.places@.contains_pair(g.queue[i], Some((g.served + i) as nat)) by {
                assert(q[0] != q[i + 1]);
                assert(q[i + 1] == g.queue[i]);
            }
            assert forall|i: int| #![trigger g.queue[i]] 0 <= i < g.queue.len() - 1
                implies g.behinds@.contains_pair(g.queue[i], Some(g.queue[i + 1])) by {
                assert(q[0] != q[i + 1]);
                assert(q[i + 1] == g.queue[i]);
            }
            assert(q[0] != q[q.len() - 1]);
        });
        // Grant the lock to the successor, which is queued since we hold its `Wait`.
        let succ = &self.nodes[next - 1];
        open_atomic_invariant!(succ.inv.borrow() => ni => {
            succ.waiting.store(Tracked(&mut ni.waiting), false);
            proof {
                if ni.wait is Some {
                    let tracked mut w = core.succ.tracked_take();
                    lemma_clash(&mut w, ni.wait.tracked_borrow());
                }
                ni.held = Some(core.held.tracked_take());
                ni.wait = Some(core.succ.tracked_take());
                ni.front = Some(core.front.tracked_take());
            }
        });
        // Forget the successor, taking the behind back: the node is idle again.
        open_atomic_invariant!(node.inv.borrow() => ni => {
            node.next.store(Tracked(&mut ni.next), 0);
            proof {
                ni.state.agree(&core.state);
                ni.behind = Some(core.behind.tracked_take());
                ni.state.update(&mut core.state, State::Idle);
            }
        });
    }
}

/// The witness: constructs a free lock, takes `cpu`'s core token from its map, acquires the lock
/// and releases it, leaving the core token idle for the lock again. Built into no image.
#[cfg(verus_keep_ghost)]
pub fn witness_queue_lock(cpu: usize) -> (r: (QueueLock, Tracked<Core>))
    requires
        cpu < NUM_CPUS,
    ensures
        r.0.wf(),
        r.1@.idle(),
        r.1@.cpu == cpu,
        r.1@.for_lock(r.0),
{
    let (new_lock, Tracked(mut cores)) = QueueLock::new();
    let lock: QueueLock = new_lock;
    proof {
        assert(cores.dom().contains(cpu as int));
    }
    let tracked mut core = cores.tracked_remove(cpu as int);
    lock.acquire(cpu, Tracked(&mut core));
    lock.release(cpu, Tracked(&mut core));
    (lock, Tracked(core))
}

} // verus!
