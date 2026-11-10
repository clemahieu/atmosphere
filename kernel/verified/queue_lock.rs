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
use vstd::atomic::{PAtomicBool, PAtomicUsize, PermissionBool, PermissionUsize};
use vstd::atomic_ghost::{AtomicInvariantPredicate, AtomicUsize};
use vstd::atomic_with_ghost;
use vstd::open_atomic_invariant;
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::prelude::*;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};
use vstd::resource::set::GhostSingleton;
#[cfg(verus_keep_ghost)]
use vstd::resource::set::{GhostSetAuth, GhostSubset};
use vstd::resource::Loc;

use crate::define::NUM_CPUS;

verus! {

/// Tells the core it is in a spin. It has no effect the proof needs.
#[verifier(external_body)]
// external_body(glue): the pause instruction, which has no state a proof could see
fn spin_hint() {
    core::hint::spin_loop();
}

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
}

/// `next` either names no successor and holds no link, or names `s` and holds `Link(cpu)` and `Wait(s)`.
pub open spec fn next_part(v: NodeInv, next: usize) -> bool {
    if next == 0 {
        v.link is None && v.succ is None
    } else {
        next <= NUM_CPUS && v.link is Some && (v.succ matches Some(t) && t@ == Token::Wait(next - 1))
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
                    && v.succ is None
            },
            State::Queued => {
                next_part(v, next) && (if waiting {
                    v.held is None && v.wait is None
                } else {
                    v.held is Some && v.wait is Some
                })
            },
            State::Holding => next_part(v, next) && v.wait is Some && v.held is None,
            State::Resetting => next_part(v, next) && waiting && v.wait is Some && v.held is None,
            State::Linked(s) => {
                next == s + 1 && 0 <= s < NUM_CPUS && waiting && v.link is Some && v.wait is Some
                    && v.held is None && v.succ is None
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
    // Read only inside open_atomic_invariant!, which a cargo build erases.
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    inv: Tracked<AtomicInvariant<NodeK, NodeInv, NodePred>>,
}

/// The ghost state one node starts with.
pub tracked struct NodeInit {
    pub tracked state: GhostVarAuth<State>,
    pub tracked link: Tok,
    pub tracked wait: Tok,
}

impl Node {
    pub closed spec fn state_id(self) -> Loc {
        self.inv@.constant().state_id
    }

    pub closed spec fn wf(self, loc: Loc, cpu: int) -> bool {
        let k = self.inv@.constant();
        k.loc == loc && k.cpu == cpu && k.next_id == self.next.id() && k.waiting_id == self.waiting.id()
    }

    const fn new(Ghost(loc): Ghost<Loc>, Ghost(cpu): Ghost<int>, Tracked(init): Tracked<NodeInit>) -> (n: Node)
        requires
            init.state@ == State::Idle,
            init.link.id() == loc,
            init.link@ == Token::Link(cpu),
            init.wait.id() == loc,
            init.wait@ == Token::Wait(cpu),
        ensures
            n.wf(loc, cpu),
            n.state_id() == init.state.id(),
    {
        let (next, Tracked(next_perm)) = PAtomicUsize::new(0);
        let (waiting, Tracked(waiting_perm)) = PAtomicBool::new(true);
        let tracked NodeInit { state, link, wait } = init;
        let ghost k = NodeK {
            loc,
            cpu,
            next_id: next.id(),
            waiting_id: waiting.id(),
            state_id: state.id(),
        };
        let tracked v = NodeInv {
            next: next_perm,
            waiting: waiting_perm,
            state,
            link: Some(link),
            wait: Some(wait),
            held: None,
            succ: None,
        };
        let tracked inv = AtomicInvariant::new(k, v, 1);
        Node { next, waiting, inv: Tracked(inv) }
    }
}

/// The tail holds the lock while 0, and the right to link behind core c while c + 1.
pub struct TailPred;

impl AtomicInvariantPredicate<Loc, usize, Tok> for TailPred {
    open spec fn atomic_inv(loc: Loc, tail: usize, g: Tok) -> bool {
        tail <= NUM_CPUS && g.id() == loc && g@ == (if tail == 0 {
            Token::Held
        } else {
            Token::Link(tail - 1)
        })
    }
}

/// A core's half of the protocol: its node's state, and the tokens it carries.
pub tracked struct Core {
    pub ghost loc: Loc,
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
}

impl Core {
    pub open spec fn wf(self) -> bool {
        &&& tok_opt(self.held, self.loc, Token::Held)
        &&& tok_opt(self.wait, self.loc, Token::Wait(self.cpu))
        &&& (self.link matches Some(t) ==> t.id() == self.loc)
        &&& (self.succ matches Some(t) ==> t.id() == self.loc)
    }

    /// The core is out of the queue.
    pub open spec fn idle(self) -> bool {
        &&& self.wf()
        &&& self.state@ == State::Idle
        &&& self.held is None
        &&& self.link is None
        &&& self.wait is None
        &&& self.succ is None
    }

    /// The core holds the lock.
    pub open spec fn holding(self) -> bool {
        &&& self.wf()
        &&& self.state@ == State::Holding
        &&& self.held is Some
        &&& self.link is None
        &&& self.wait is None
        &&& self.succ is None
    }

    /// The core belongs to `lock`.
    pub open spec fn for_lock(self, lock: QueueLock) -> bool {
        &&& self.loc == lock.loc()
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

/// `init` starts node `c` of lock `loc`, and `core` is that core's half.
pub open spec fn init_ok(init: NodeInit, core: Core, loc: Loc, c: int) -> bool {
    &&& init.state@ == State::Idle
    &&& init.link.id() == loc
    &&& init.link@ == Token::Link(c)
    &&& init.wait.id() == loc
    &&& init.wait@ == Token::Wait(c)
    &&& core.idle()
    &&& core.loc == loc
    &&& core.cpu == c
    &&& core.state.id() == init.state.id()
}

/// `inits` and `cores` start every core from `from` up.
pub open spec fn inits_ok(inits: Map<int, NodeInit>, cores: Map<int, Core>, loc: Loc, from: int) -> bool {
    forall|c: int|
        from <= c < NUM_CPUS ==> #[trigger] inits.dom().contains(c) && cores.dom().contains(c)
            && init_ok(inits[c], cores[c], loc, c)
}

/// Takes the node starts for cores `from..NUM_CPUS` out of `tokens`, with the cores' halves.
proof fn make_inits(tracked tokens: &mut GhostSubset<Token>, from: int) -> (tracked r: (
    Map<int, NodeInit>,
    Map<int, Core>,
))
    requires
        0 <= from <= NUM_CPUS,
        forall|c: int| from <= c < NUM_CPUS ==> #[trigger] old(tokens)@.contains(Token::Link(c)),
        forall|c: int| from <= c < NUM_CPUS ==> #[trigger] old(tokens)@.contains(Token::Wait(c)),
    ensures
        final(tokens).id() == old(tokens).id(),
        inits_ok(r.0, r.1, old(tokens).id(), from),
    decreases NUM_CPUS - from,
{
    if from == NUM_CPUS {
        (Map::tracked_empty(), Map::tracked_empty())
    } else {
        let tracked (auth, var) = GhostVarAuth::new(State::Idle);
        let tracked link = tokens.split_singleton(Token::Link(from));
        let tracked wait = tokens.split_singleton(Token::Wait(from));
        let tracked (mut inits, mut cores) = make_inits(tokens, from + 1);
        let ghost rest = inits;
        inits.tracked_insert(from, NodeInit { state: auth, link, wait });
        cores.tracked_insert(
            from,
            Core { loc: tokens.id(), cpu: from, state: var, held: None, link: None, wait: None, succ: None },
        );
        assert forall|c: int|
            from <= c < NUM_CPUS implies #[trigger] inits.dom().contains(c) && cores.dom().contains(c)
                && init_ok(inits[c], cores[c], tokens.id(), c) by {
            if c != from {
                assert(rest.dom().contains(c));
            }
        }
        (inits, cores)
    }
}

/// Takes core `c`'s node start out of `inits`.
proof fn take_init(tracked inits: &mut Map<int, NodeInit>, cores: Map<int, Core>, loc: Loc, c: int) -> (tracked init:
    NodeInit)
    requires
        0 <= c < NUM_CPUS,
        inits_ok(*old(inits), cores, loc, c),
    ensures
        init_ok(init, cores[c], loc, c),
        inits_ok(*final(inits), cores, loc, c + 1),
{
    assert(old(inits).dom().contains(c));
    let tracked init = inits.tracked_remove(c);
    assert forall|d: int|
        c + 1 <= d < NUM_CPUS implies #[trigger] inits.dom().contains(d) && cores.dom().contains(d)
            && init_ok(inits[d], cores[d], loc, d) by {
        assert(old(inits).dom().contains(d));
    }
    init
}

pub struct QueueLock {
    /// The last waiter's core plus one, or 0 when the lock is free.
    tail: AtomicUsize<Loc, Tok, TailPred>,
    nodes: [Node; NUM_CPUS],
}

impl QueueLock {
    /// The lock's token set.
    pub closed spec fn loc(self) -> Loc {
        self.tail.constant()
    }

    /// The ghost variable of core `cpu`'s node.
    pub closed spec fn state_id(self, cpu: int) -> Loc {
        self.nodes[cpu].state_id()
    }

    pub closed spec fn wf(self) -> bool {
        &&& self.tail.well_formed()
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] self.nodes[c]).wf(self.loc(), c)
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
        let tracked (mut inits, cores) = make_inits(&mut tokens, 0);
        let ghost all = inits;
        let tail = AtomicUsize::new(Ghost(loc), 0, Tracked(held));
        let nodes = [
            Node::new(Ghost(loc), Ghost(0), Tracked(take_init(&mut inits, cores, loc, 0))),
            Node::new(Ghost(loc), Ghost(1), Tracked(take_init(&mut inits, cores, loc, 1))),
            Node::new(Ghost(loc), Ghost(2), Tracked(take_init(&mut inits, cores, loc, 2))),
            Node::new(Ghost(loc), Ghost(3), Tracked(take_init(&mut inits, cores, loc, 3))),
            Node::new(Ghost(loc), Ghost(4), Tracked(take_init(&mut inits, cores, loc, 4))),
            Node::new(Ghost(loc), Ghost(5), Tracked(take_init(&mut inits, cores, loc, 5))),
            Node::new(Ghost(loc), Ghost(6), Tracked(take_init(&mut inits, cores, loc, 6))),
            Node::new(Ghost(loc), Ghost(7), Tracked(take_init(&mut inits, cores, loc, 7))),
            Node::new(Ghost(loc), Ghost(8), Tracked(take_init(&mut inits, cores, loc, 8))),
            Node::new(Ghost(loc), Ghost(9), Tracked(take_init(&mut inits, cores, loc, 9))),
            Node::new(Ghost(loc), Ghost(10), Tracked(take_init(&mut inits, cores, loc, 10))),
            Node::new(Ghost(loc), Ghost(11), Tracked(take_init(&mut inits, cores, loc, 11))),
            Node::new(Ghost(loc), Ghost(12), Tracked(take_init(&mut inits, cores, loc, 12))),
            Node::new(Ghost(loc), Ghost(13), Tracked(take_init(&mut inits, cores, loc, 13))),
            Node::new(Ghost(loc), Ghost(14), Tracked(take_init(&mut inits, cores, loc, 14))),
            Node::new(Ghost(loc), Ghost(15), Tracked(take_init(&mut inits, cores, loc, 15))),
            Node::new(Ghost(loc), Ghost(16), Tracked(take_init(&mut inits, cores, loc, 16))),
            Node::new(Ghost(loc), Ghost(17), Tracked(take_init(&mut inits, cores, loc, 17))),
            Node::new(Ghost(loc), Ghost(18), Tracked(take_init(&mut inits, cores, loc, 18))),
            Node::new(Ghost(loc), Ghost(19), Tracked(take_init(&mut inits, cores, loc, 19))),
            Node::new(Ghost(loc), Ghost(20), Tracked(take_init(&mut inits, cores, loc, 20))),
            Node::new(Ghost(loc), Ghost(21), Tracked(take_init(&mut inits, cores, loc, 21))),
            Node::new(Ghost(loc), Ghost(22), Tracked(take_init(&mut inits, cores, loc, 22))),
            Node::new(Ghost(loc), Ghost(23), Tracked(take_init(&mut inits, cores, loc, 23))),
            Node::new(Ghost(loc), Ghost(24), Tracked(take_init(&mut inits, cores, loc, 24))),
            Node::new(Ghost(loc), Ghost(25), Tracked(take_init(&mut inits, cores, loc, 25))),
            Node::new(Ghost(loc), Ghost(26), Tracked(take_init(&mut inits, cores, loc, 26))),
            Node::new(Ghost(loc), Ghost(27), Tracked(take_init(&mut inits, cores, loc, 27))),
            Node::new(Ghost(loc), Ghost(28), Tracked(take_init(&mut inits, cores, loc, 28))),
            Node::new(Ghost(loc), Ghost(29), Tracked(take_init(&mut inits, cores, loc, 29))),
            Node::new(Ghost(loc), Ghost(30), Tracked(take_init(&mut inits, cores, loc, 30))),
            Node::new(Ghost(loc), Ghost(31), Tracked(take_init(&mut inits, cores, loc, 31))),
        ];
        proof {
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] cores.dom().contains(c) && cores[c].idle()
                && cores[c].cpu == c && cores[c].loc == loc by {
                assert(all.dom().contains(c));
            }
        }
        (QueueLock { tail, nodes }, Tracked(cores))
    }

    /// Waits for the lock on behalf of `cpu`, which must not hold it. The spin ends when the holder
    /// hands over, so it has no bound of its own.
    #[verifier::exec_allows_no_decreases_clause]
    // exec_allows_no_decreases_clause(unproven): the spin waits for the holder to hand over, and bounded overtaking is not yet proven
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
    {
        let node = &self.nodes[cpu];
        // Leave idle, taking the node's link right and queued token along.
        open_atomic_invariant!(node.inv.borrow() => ni => {
            proof {
                ni.state.agree(&core.state);
                core.link = Some(ni.link.tracked_take());
                core.wait = Some(ni.wait.tracked_take());
                ni.state.update(&mut core.state, State::Queued);
            }
        });
        let previous = atomic_with_ghost!(self.tail => swap(cpu + 1); update prev -> next; ghost g => {
            let tracked mut mine = core.link.tracked_take();
            vstd::modes::tracked_swap(&mut g, &mut mine);
            if prev == 0 {
                core.held = Some(mine);
            } else {
                core.link = Some(mine);
            }
            assert(prev <= NUM_CPUS);
        });
        if previous != 0 {
            // Link behind the previous tail, handing it `Wait(cpu)`.
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
                    waiting ==> core.state@ == State::Queued && core.held is None,
                    !waiting ==> core.holding(),
            {
                let node = &self.nodes[cpu];
                open_atomic_invariant!(node.inv.borrow() => ni => {
                    waiting = node.waiting.load(Tracked(&ni.waiting));
                    proof {
                        ni.state.agree(&core.state);
                        if !waiting {
                            core.held = Some(ni.held.tracked_take());
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
    }

    /// Hands the lock on from `cpu`, which must hold it. The spin ends when the waiter that swapped
    /// the tail links itself, so it has no bound of its own.
    #[verifier::exec_allows_no_decreases_clause]
    // exec_allows_no_decreases_clause(unproven): the spin waits for the successor to link itself, and bounded overtaking is not yet proven
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
                    ni.state.update(&mut core.state, State::Linked(next - 1));
                }
            }
        });
        if next == 0 {
            let freed = atomic_with_ghost!(self.tail => compare_exchange(cpu + 1, 0); update prev -> after; returning ret; ghost g => {
                if ret is Ok {
                    let tracked mut h = core.held.tracked_take();
                    vstd::modes::tracked_swap(&mut g, &mut h);
                    core.link = Some(h);
                }
            });
            if freed.is_ok() {
                // Nobody linked: the link right is back, so the node is idle again.
                open_atomic_invariant!(node.inv.borrow() => ni => {
                    proof {
                        ni.state.agree(&core.state);
                        if ni.link is Some {
                            let tracked mut l = core.link.tracked_take();
                            lemma_clash(&mut l, ni.link.tracked_borrow());
                        }
                        ni.link = Some(core.link.tracked_take());
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
                    next == 0 ==> core.state@ == State::Resetting && core.succ is None,
                    next != 0 ==> next <= NUM_CPUS && core.state@ == State::Linked(next - 1)
                        && (core.succ matches Some(t) && t@ == Token::Wait(next - 1)),
            {
                spin_hint();
                let node = &self.nodes[cpu];
                open_atomic_invariant!(node.inv.borrow() => ni => {
                    next = node.next.load(Tracked(&ni.next));
                    proof {
                        ni.state.agree(&core.state);
                        if next != 0 {
                            core.succ = Some(ni.succ.tracked_take());
                            ni.state.update(&mut core.state, State::Linked(next - 1));
                        }
                    }
                });
            }
        }
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
            }
        });
        // Forget the successor, taking the link right back: the node is idle again.
        open_atomic_invariant!(node.inv.borrow() => ni => {
            node.next.store(Tracked(&mut ni.next), 0);
            proof {
                ni.state.agree(&core.state);
                ni.state.update(&mut core.state, State::Idle);
            }
        });
    }
}

} // verus!
