// SPDX-License-Identifier: MIT

//! A generic per-core request/serve lending bridge, with an atomic invariant on each core's request
//! word and served word.
//!
//! For each core `c < NUM_CPUS`, one channel holds a request word written only by the requester and
//! a served word written only by the server on core `c`. The requester puts a tracked value `T`
//! into a core's request word's invariant and stores a new sequence number (`next_seq`); the server
//! on that core observes the words differing, takes `T` out, passes it through a caller-supplied
//! operation satisfying `ChannelOp<T>`, and returns the transformed value through its served word's
//! invariant with a store of the number it read. Numbers are compared for equality only, so they
//! may wrap across `usize::MAX`. `wait` prints the core it is still waiting on, through the serial
//! port, every `REPORT_SPINS` spins, and keeps waiting.

use core::marker::PhantomData;

use vstd::atomic_ghost::{AtomicInvariantPredicate, AtomicUsize};
use vstd::atomic_with_ghost;
use vstd::prelude::*;
use vstd::resource::ghost_var::{GhostVar, GhostVarAuth};
#[cfg(verus_keep_ghost)]
use vstd::resource::set::GhostSetAuth;
use vstd::resource::set::GhostSingleton;
use vstd::resource::Loc;

use crate::arch::spin_hint;
use crate::capability::steps::Steps;
use crate::define::NUM_CPUS;

verus! {

/// Next sequence number, wrapping at `usize::MAX`.
pub open spec fn next_seq(n: usize) -> usize {
    if n == usize::MAX {
        0
    } else {
        (n + 1) as usize
    }
}

/// Specification of the operation a server applies to each lent value `T`.
pub trait ChannelOp<T> {
    spec fn pre(v: T) -> bool;

    spec fn post(input: T, output: T) -> bool;
}

/// Ghost constants tying one core's request atomic invariant, served atomic invariant, `Req`
/// token, and `Srv` token together.
pub struct ChannelK {
    pub cpu: int,
    pub tok_id: Loc,
    pub req_seq_id: Loc,
    pub taken_seq_id: Loc,
    pub srv_seq_id: Loc,
    pub cleared_seq_id: Loc,
    pub input_id: Loc,
}

/// Ghost state held inside a core's `request` atomic invariant.
pub tracked struct ReqG<T> {
    pub tracked req_seq: GhostVarAuth<usize>,
    pub tracked taken_seq: GhostVarAuth<usize>,
    pub tracked turn: Option<GhostSingleton<()>>,
    pub tracked payload: Option<T>,
    pub tracked input_auth: Option<GhostVarAuth<Option<T>>>,
}

/// Atomic invariant predicate on a core's request word.
pub struct ReqPred<T, Op>(PhantomData<(T, Op)>);

impl<T, Op: ChannelOp<T>> AtomicInvariantPredicate<ChannelK, usize, ReqG<T>> for ReqPred<T, Op> {
    open spec fn atomic_inv(k: ChannelK, val: usize, g: ReqG<T>) -> bool {
        &&& g.req_seq.id() == k.req_seq_id
        &&& g.req_seq@ == val
        &&& g.taken_seq.id() == k.taken_seq_id
        &&& match g.payload {
            None => {
                &&& val == g.taken_seq@
                &&& g.turn is None
                &&& g.input_auth is None
            },
            Some(v) => {
                &&& val == next_seq(g.taken_seq@)
                &&& val != g.taken_seq@
                &&& Op::pre(v)
                &&& g.turn matches Some(t) && t.id() == k.tok_id
                &&& g.input_auth matches Some(ia) && ia.id() == k.input_id && ia@ == Some(v)
            },
        }
    }
}

/// Ghost state held inside a core's `served` atomic invariant.
pub tracked struct SrvG<T> {
    pub tracked srv_seq: GhostVarAuth<usize>,
    pub tracked cleared_seq: GhostVarAuth<usize>,
    pub tracked turn: Option<GhostSingleton<()>>,
    pub tracked payload: Option<T>,
    pub tracked input_auth: Option<GhostVarAuth<Option<T>>>,
    pub ghost input: Option<T>,
}

/// Atomic invariant predicate on a core's served word.
pub struct SrvPred<T, Op>(PhantomData<(T, Op)>);

impl<T, Op: ChannelOp<T>> AtomicInvariantPredicate<ChannelK, usize, SrvG<T>> for SrvPred<T, Op> {
    open spec fn atomic_inv(k: ChannelK, val: usize, g: SrvG<T>) -> bool {
        &&& g.srv_seq.id() == k.srv_seq_id
        &&& g.srv_seq@ == val
        &&& g.cleared_seq.id() == k.cleared_seq_id
        &&& match g.payload {
            None => {
                &&& val == g.cleared_seq@
                &&& g.turn is None
                &&& g.input_auth is None
            },
            Some(out) => {
                &&& val == next_seq(g.cleared_seq@)
                &&& val != g.cleared_seq@
                &&& g.turn matches Some(t) && t.id() == k.tok_id
                &&& g.input matches Some(inp)
                &&& g.input_auth matches Some(ia) && ia.id() == k.input_id && ia@ == Some(inp)
                &&& Op::post(inp, out)
            },
        }
    }
}

/// One core's request/served word pair, padded to its own cache line.
#[repr(align(64))]
struct Slot<T, Op> {
    request: AtomicUsize<ChannelK, ReqG<T>, ReqPred<T, Op>>,
    served: AtomicUsize<ChannelK, SrvG<T>, SrvPred<T, Op>>,
    _marker: PhantomData<(T, Op)>,
}

/// The requester's capability for one target core `cpu`.
pub tracked struct Req<T, Op> {
    pub ghost k: ChannelK,
    pub ghost seq: usize,
    pub ghost input: Option<T>,
    pub tracked req_seq: GhostVar<usize>,
    pub tracked cleared_seq: GhostVar<usize>,
    pub tracked turn: Option<GhostSingleton<()>>,
    pub tracked input_auth: Option<GhostVarAuth<Option<T>>>,
    pub tracked input_var: GhostVar<Option<T>>,
    pub ghost _op: PhantomData<Op>,
}

impl<T, Op> Req<T, Op> {
    pub closed spec fn wf(self) -> bool {
        &&& self.req_seq.id() == self.k.req_seq_id
        &&& self.req_seq@ == self.seq
        &&& self.cleared_seq.id() == self.k.cleared_seq_id
        &&& self.input_var.id() == self.k.input_id
        &&& 0 <= self.k.cpu < NUM_CPUS
    }

    pub closed spec fn for_bridge(self, bridge: CoreBridge<T, Op>) -> bool {
        &&& 0 <= self.k.cpu < NUM_CPUS
        &&& self.k == bridge.slot_k(self.k.cpu)
    }

    pub closed spec fn cpu(self) -> int {
        self.k.cpu
    }

    pub closed spec fn seq(self) -> usize {
        self.seq
    }

    pub closed spec fn idle(self) -> bool {
        &&& self.wf()
        &&& self.cleared_seq@ == self.seq
        &&& self.turn matches Some(t) && t.id() == self.k.tok_id
        &&& self.input is None
        &&& self.input_var@ is None
        &&& self.input_auth matches Some(ia) && ia.id() == self.k.input_id && ia@ is None
    }

    pub closed spec fn pending(self) -> bool {
        &&& self.wf()
        &&& self.seq == next_seq(self.cleared_seq@)
        &&& self.seq != self.cleared_seq@
        &&& self.turn is None
        &&& self.input matches Some(inp)
        &&& self.input_var@ == Some(inp)
        &&& self.input_auth is None
    }

    pub closed spec fn input(self) -> T {
        self.input.unwrap()
    }
}

/// The server's capability on core `cpu`.
pub tracked struct Srv<T, Op> {
    pub ghost k: ChannelK,
    pub ghost seq: usize,
    pub tracked srv_seq: GhostVar<usize>,
    pub tracked taken_seq: GhostVar<usize>,
    pub ghost _op: PhantomData<(T, Op)>,
}

impl<T, Op> Srv<T, Op> {
    pub closed spec fn wf(self) -> bool {
        &&& self.srv_seq.id() == self.k.srv_seq_id
        &&& self.srv_seq@ == self.seq
        &&& self.taken_seq.id() == self.k.taken_seq_id
        &&& self.taken_seq@ == self.seq
        &&& 0 <= self.k.cpu < NUM_CPUS
    }

    pub closed spec fn for_bridge(self, bridge: CoreBridge<T, Op>) -> bool {
        &&& 0 <= self.k.cpu < NUM_CPUS
        &&& self.k == bridge.slot_k(self.k.cpu)
    }

    pub closed spec fn cpu(self) -> int {
        self.k.cpu
    }

    pub closed spec fn seq(self) -> usize {
        self.seq
    }
}

/// Ghost initialization state transferred into one `Slot` during `CoreBridge::new`.
pub tracked struct SlotInit<T, Op> {
    pub ghost k: ChannelK,
    pub tracked req_seq: GhostVarAuth<usize>,
    pub tracked taken_seq: GhostVarAuth<usize>,
    pub tracked srv_seq: GhostVarAuth<usize>,
    pub tracked cleared_seq: GhostVarAuth<usize>,
    pub ghost _op: PhantomData<(T, Op)>,
}

spec fn slot_init_ok<T, Op>(init: SlotInit<T, Op>, req: Req<T, Op>, srv: Srv<T, Op>, cpu: int) -> bool {
    &&& 0 <= cpu < NUM_CPUS
    &&& init.k.cpu == cpu
    &&& init.req_seq.id() == init.k.req_seq_id
    &&& init.req_seq@ == 0usize
    &&& init.taken_seq.id() == init.k.taken_seq_id
    &&& init.taken_seq@ == 0usize
    &&& init.srv_seq.id() == init.k.srv_seq_id
    &&& init.srv_seq@ == 0usize
    &&& init.cleared_seq.id() == init.k.cleared_seq_id
    &&& init.cleared_seq@ == 0usize
    &&& req.idle()
    &&& req.cpu() == cpu
    &&& req.seq() == 0usize
    &&& req.k == init.k
    &&& srv.wf()
    &&& srv.cpu() == cpu
    &&& srv.seq() == 0usize
    &&& srv.k == init.k
}

spec fn channel_inits_ok<T, Op>(
    inits: Map<int, SlotInit<T, Op>>,
    reqs: Map<int, Req<T, Op>>,
    srvs: Map<int, Srv<T, Op>>,
    from: int,
) -> bool {
    forall|c: int|
        from <= c < NUM_CPUS ==> #[trigger] inits.dom().contains(c) && reqs.dom().contains(c)
            && srvs.dom().contains(c) && slot_init_ok(inits[c], reqs[c], srvs[c], c)
}

proof fn make_channel_inits<T, Op>(from: int) -> (tracked r: (
    Map<int, SlotInit<T, Op>>,
    Map<int, Req<T, Op>>,
    Map<int, Srv<T, Op>>,
))
    requires
        0 <= from <= NUM_CPUS,
    ensures
        channel_inits_ok(r.0, r.1, r.2, from),
    decreases NUM_CPUS - from,
{
    if from == NUM_CPUS {
        (Map::tracked_empty(), Map::tracked_empty(), Map::tracked_empty())
    } else {
        let tracked (_auth, mut tokens) = GhostSetAuth::<()>::new(set![()]);
        let tracked turn = tokens.split_singleton(());
        let tracked (req_seq_auth, req_seq_var) = GhostVarAuth::<usize>::new(0);
        let tracked (taken_seq_auth, taken_seq_var) = GhostVarAuth::<usize>::new(0);
        let tracked (srv_seq_auth, srv_seq_var) = GhostVarAuth::<usize>::new(0);
        let tracked (cleared_seq_auth, cleared_seq_var) = GhostVarAuth::<usize>::new(0);
        let tracked (input_auth, input_var) = GhostVarAuth::<Option<T>>::new(None);
        let ghost k = ChannelK {
            cpu: from,
            tok_id: turn.id(),
            req_seq_id: req_seq_auth.id(),
            taken_seq_id: taken_seq_auth.id(),
            srv_seq_id: srv_seq_auth.id(),
            cleared_seq_id: cleared_seq_auth.id(),
            input_id: input_auth.id(),
        };
        let tracked init = SlotInit {
            k,
            req_seq: req_seq_auth,
            taken_seq: taken_seq_auth,
            srv_seq: srv_seq_auth,
            cleared_seq: cleared_seq_auth,
            _op: PhantomData,
        };
        let tracked req = Req {
            k,
            seq: 0,
            input: None,
            req_seq: req_seq_var,
            cleared_seq: cleared_seq_var,
            turn: Some(turn),
            input_auth: Some(input_auth),
            input_var,
            _op: PhantomData,
        };
        let tracked srv = Srv {
            k,
            seq: 0,
            srv_seq: srv_seq_var,
            taken_seq: taken_seq_var,
            _op: PhantomData,
        };
        let tracked (mut inits, mut reqs, mut srvs) = make_channel_inits(from + 1);
        let ghost rest_inits = inits;
        inits.tracked_insert(from, init);
        reqs.tracked_insert(from, req);
        srvs.tracked_insert(from, srv);
        assert forall|c: int|
            from <= c < NUM_CPUS implies #[trigger] inits.dom().contains(c) && reqs.dom().contains(c)
                && srvs.dom().contains(c) && slot_init_ok(inits[c], reqs[c], srvs[c], c) by {
            if c != from {
                assert(rest_inits.dom().contains(c));
            }
        }
        (inits, reqs, srvs)
    }
}

proof fn take_channel_init<T, Op>(
    tracked inits: &mut Map<int, SlotInit<T, Op>>,
    reqs: Map<int, Req<T, Op>>,
    srvs: Map<int, Srv<T, Op>>,
    cpu: int,
) -> (tracked init: SlotInit<T, Op>)
    requires
        0 <= cpu < NUM_CPUS,
        channel_inits_ok(*old(inits), reqs, srvs, cpu),
    ensures
        slot_init_ok(init, reqs[cpu], srvs[cpu], cpu),
        channel_inits_ok(*final(inits), reqs, srvs, cpu + 1),
{
    assert(old(inits).dom().contains(cpu));
    let tracked init = inits.tracked_remove(cpu);
    assert forall|d: int|
        cpu + 1 <= d < NUM_CPUS implies #[trigger] inits.dom().contains(d) && reqs.dom().contains(d)
            && srvs.dom().contains(d) && slot_init_ok(inits[d], reqs[d], srvs[d], d) by {
        assert(old(inits).dom().contains(d));
    }
    init
}

impl<T, Op: ChannelOp<T>> Slot<T, Op> {
    closed spec fn wf(self, cpu: int) -> bool {
        &&& self.request.well_formed()
        &&& self.served.well_formed()
        &&& self.request.constant() == self.served.constant()
        &&& self.request.constant().cpu == cpu
        &&& 0 <= cpu < NUM_CPUS
    }

    const fn new(Tracked(init): Tracked<SlotInit<T, Op>>) -> (s: Self)
        requires
            0 <= init.k.cpu < NUM_CPUS,
            init.req_seq.id() == init.k.req_seq_id,
            init.req_seq@ == 0usize,
            init.taken_seq.id() == init.k.taken_seq_id,
            init.taken_seq@ == 0usize,
            init.srv_seq.id() == init.k.srv_seq_id,
            init.srv_seq@ == 0usize,
            init.cleared_seq.id() == init.k.cleared_seq_id,
            init.cleared_seq@ == 0usize,
        ensures
            s.wf(init.k.cpu),
            s.request.constant() == init.k,
    {
        let tracked SlotInit { k, req_seq, taken_seq, srv_seq, cleared_seq, _op: _ } = init;
        let tracked rg = ReqG {
            req_seq,
            taken_seq,
            turn: None,
            payload: None,
            input_auth: None,
        };
        let tracked sg = SrvG {
            srv_seq,
            cleared_seq,
            turn: None,
            payload: None,
            input_auth: None,
            input: None,
        };
        Slot {
            request: AtomicUsize::new(Ghost(k), 0, Tracked(rg)),
            served: AtomicUsize::new(Ghost(k), 0, Tracked(sg)),
            _marker: PhantomData,
        }
    }
}

/// Per-core request/serve bridge carrying tracked values of type `T` through `Op`.
pub struct CoreBridge<T, Op> {
    slots: [Slot<T, Op>; NUM_CPUS],
}

impl<T, Op> CoreBridge<T, Op> {
    closed spec fn slot_k(self, cpu: int) -> ChannelK {
        self.slots[cpu].request.constant()
    }
}

impl<T, Op: ChannelOp<T>> CoreBridge<T, Op> {
    pub closed spec fn wf(self) -> bool {
        forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] self.slots[c]).wf(c)
    }

    /// Creates a bridge with all channels idle at sequence number 0, returning the per-core
    /// requester tokens and server tokens.
    pub const fn new() -> (r: (Self, Tracked<Map<int, Req<T, Op>>>, Tracked<Map<int, Srv<T, Op>>>))
        ensures
            r.0.wf(),
            forall|c: int|
                0 <= c < NUM_CPUS ==> #[trigger] r.1@.dom().contains(c) && r.1@[c].idle()
                    && r.1@[c].cpu() == c && r.1@[c].for_bridge(r.0) && r.1@[c].seq() == 0usize,
            forall|c: int|
                0 <= c < NUM_CPUS ==> #[trigger] r.2@.dom().contains(c) && r.2@[c].wf()
                    && r.2@[c].cpu() == c && r.2@[c].for_bridge(r.0) && r.2@[c].seq() == 0usize,
    {
        let tracked (mut inits, reqs, srvs) = make_channel_inits(0);
        let ghost all_inits = inits;
        let slots = [
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 0))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 1))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 2))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 3))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 4))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 5))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 6))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 7))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 8))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 9))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 10))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 11))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 12))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 13))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 14))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 15))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 16))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 17))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 18))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 19))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 20))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 21))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 22))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 23))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 24))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 25))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 26))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 27))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 28))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 29))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 30))),
            Slot::new(Tracked(take_channel_init(&mut inits, reqs, srvs, 31))),
        ];
        proof {
            assert forall|c: int| 0 <= c < NUM_CPUS implies (#[trigger] slots[c]).wf(c)
                && reqs.dom().contains(c) && reqs[c].idle() && reqs[c].cpu() == c
                && reqs[c].for_bridge(CoreBridge { slots }) && reqs[c].seq() == 0usize
                && srvs.dom().contains(c) && srvs[c].wf() && srvs[c].cpu() == c
                && srvs[c].for_bridge(CoreBridge { slots }) && srvs[c].seq() == 0usize by {
                assert(all_inits.dom().contains(c));
            }
        }
        (CoreBridge { slots }, Tracked(reqs), Tracked(srvs))
    }

    /// Lends `val` to core `cpu` by moving it into `cpu`'s request invariant and writing a new
    /// sequence number to `cpu`'s request word.
    pub fn send(&self, cpu: usize, Tracked(req): Tracked<&mut Req<T, Op>>, Tracked(val): Tracked<T>)
        requires
            self.wf(),
            cpu < NUM_CPUS,
            old(req).idle(),
            old(req).for_bridge(*self),
            old(req).cpu() == cpu,
            Op::pre(val),
        ensures
            final(req).pending(),
            final(req).for_bridge(*self),
            final(req).cpu() == cpu,
            final(req).seq() == next_seq(old(req).seq()),
            final(req).seq() != old(req).seq(),
            final(req).input() == val,
    {
        let slot = &self.slots[cpu];
        let cur = atomic_with_ghost!(slot.request => load(); ghost rg => {
            rg.req_seq.agree(&req.req_seq);
        });
        let next: usize = if cur == usize::MAX {
            0
        } else {
            cur + 1
        };
        atomic_with_ghost!(slot.request => store(next); ghost rg => {
            rg.req_seq.agree(&req.req_seq);
            if rg.turn is Some {
                let tracked mut tok = req.turn.tracked_take();
                tok.disjoint(rg.turn.tracked_borrow());
            }
            let tracked mut ia = req.input_auth.tracked_take();
            ia.update(&mut req.input_var, Some(val));
            req.input = Some(val);
            req.seq = next;
            rg.req_seq.update(&mut req.req_seq, next);
            rg.turn = Some(req.turn.tracked_take());
            rg.payload = Some(val);
            rg.input_auth = Some(ia);
        });
    }

    /// Takes the transformed value out if core `cpu`'s served word equals its request word.
    /// Returns `None` when the words still differ.
    pub fn try_take(
        &self,
        cpu: usize,
        Tracked(req): Tracked<&mut Req<T, Op>>,
        Tracked(srv_opt): Tracked<Option<&Srv<T, Op>>>,
    ) -> (res: Option<Tracked<T>>)
        requires
            self.wf(),
            cpu < NUM_CPUS,
            old(req).pending(),
            old(req).for_bridge(*self),
            old(req).cpu() == cpu,
            srv_opt matches Some(srv) ==> srv.wf() && srv.for_bridge(*self) && srv.cpu() == cpu,
        ensures
            final(req).for_bridge(*self),
            final(req).cpu() == cpu,
            final(req).seq() == old(req).seq(),
            match res {
                Some(out) => final(req).idle() && Op::post(old(req).input(), out@),
                None => final(req).pending() && final(req).input() == old(req).input(),
            },
            srv_opt matches Some(srv) ==> (res is Some <==> srv.seq() == old(req).seq()),
    {
        let slot = &self.slots[cpu];
        let expected = atomic_with_ghost!(slot.request => load(); ghost rg => {
            rg.req_seq.agree(&req.req_seq);
        });
        let tracked mut res_val: Option<T> = None;
        let s = atomic_with_ghost!(slot.served => load(); update prev -> _next; ghost sg => {
            sg.cleared_seq.agree(&req.cleared_seq);
            match srv_opt {
                Some(srv) => {
                    sg.srv_seq.agree(&srv.srv_seq);
                },
                None => {},
            }
            if prev == expected {
                let tracked out = sg.payload.tracked_take();
                let tracked tok = sg.turn.tracked_take();
                let tracked mut ia = sg.input_auth.tracked_take();
                ia.agree(&req.input_var);
                ia.update(&mut req.input_var, None);
                sg.cleared_seq.update(&mut req.cleared_seq, prev);
                req.turn = Some(tok);
                req.input_auth = Some(ia);
                req.input = None;
                res_val = Some(out);
            }
        });
        if s == expected {
            Some(Tracked(res_val.tracked_unwrap()))
        } else {
            None
        }
    }

    /// Spins until core `cpu`'s served word equals its request word, then takes and returns the
    /// transformed value. Each time the spin count reaches [`REPORT_SPINS`], prints one line naming
    /// `cpu` and keeps waiting. `steps` counts the bytes of those lines.
    #[verifier::exec_allows_no_decreases_clause]
    // exec_allows_no_decreases_clause(unproven): the spin waits for the server on cpu to store the request number into served, which ends only while that core keeps executing and reaches a serve
    pub fn wait(
        &self,
        cpu: usize,
        Tracked(req): Tracked<&mut Req<T, Op>>,
        Tracked(steps): Tracked<&mut Steps>,
    ) -> (res: Tracked<T>)
        requires
            self.wf(),
            cpu < NUM_CPUS,
            old(req).pending(),
            old(req).for_bridge(*self),
            old(req).cpu() == cpu,
        ensures
            final(req).idle(),
            final(req).for_bridge(*self),
            final(req).cpu() == cpu,
            final(req).seq() == old(req).seq(),
            Op::post(old(req).input(), res@),
    {
        let mut spins: u64 = 0;
        proof {
            lemma_report_spins();
        }
        loop
            invariant
                self.wf(),
                cpu < NUM_CPUS,
                req.pending(),
                req.for_bridge(*self),
                req.cpu() == cpu,
                req.seq() == old(req).seq(),
                req.input() == old(req).input(),
                spins < REPORT_SPINS,
        {
            if let Some(out) = self.try_take(cpu, Tracked(req), Tracked(None)) {
                return out;
            }
            proof {
                lemma_report_spins();
            }
            spins = spins + 1;
            if spins == REPORT_SPINS {
                report_wait(cpu, Tracked(steps));
                spins = 0;
            }
            spin_hint();
        }
    }

    /// Serves a pending request on core `cpu`, if any, passing the lent value through `op` once
    /// and storing the read request number to `served`. Entered with a request standing
    /// (`standing matches Some(req)` with `old(srv).seq() != req.seq()`), it leaves the words
    /// equal and returns `true`.
    pub fn serve<F>(
        &self,
        cpu: usize,
        op: F,
        Tracked(srv): Tracked<&mut Srv<T, Op>>,
        Tracked(standing): Tracked<Option<&Req<T, Op>>>,
    ) -> (served: bool)
        where
            F: FnOnce(Tracked<T>) -> Tracked<T>,
        requires
            self.wf(),
            cpu < NUM_CPUS,
            old(srv).wf(),
            old(srv).for_bridge(*self),
            old(srv).cpu() == cpu,
            standing matches Some(req) ==> req.pending() && req.for_bridge(*self) && req.cpu() == cpu,
            forall|v: Tracked<T>| Op::pre(v@) ==> #[trigger] op.requires((v,)),
            forall|v: Tracked<T>, out: Tracked<T>| #[trigger] op.ensures((v,), out) ==> Op::post(v@, out@),
        ensures
            final(srv).wf(),
            final(srv).for_bridge(*self),
            final(srv).cpu() == cpu,
            served ==> final(srv).seq() == next_seq(old(srv).seq()),
            !served ==> final(srv).seq() == old(srv).seq(),
            standing matches Some(req) ==> (
                final(srv).seq() == req.seq()
                && (served <==> old(srv).seq() != req.seq())
            ),
    {
        let slot = &self.slots[cpu];
        let expected = atomic_with_ghost!(slot.served => load(); ghost sg => {
            sg.srv_seq.agree(&srv.srv_seq);
        });
        let tracked mut taken: Option<(T, GhostSingleton<()>, GhostVarAuth<Option<T>>)> = None;
        let ghost mut in_ghost: Option<T> = None;
        let r = atomic_with_ghost!(slot.request => load(); update prev -> _next; ghost rg => {
            rg.taken_seq.agree(&srv.taken_seq);
            match standing {
                Some(req) => {
                    rg.req_seq.agree(&req.req_seq);
                },
                None => {},
            }
            if prev != expected {
                let tracked v = rg.payload.tracked_take();
                let tracked tok = rg.turn.tracked_take();
                let tracked ia = rg.input_auth.tracked_take();
                in_ghost = Some(v);
                rg.taken_seq.update(&mut srv.taken_seq, prev);
                taken = Some((v, tok, ia));
            }
        });
        if r == expected {
            return false;
        }
        let tracked (v, mut tok, ia) = taken.tracked_unwrap();
        let tracked tv_in = v;
        let ghost orig_v = tv_in;
        let tv = Tracked(tv_in);
        proof {
            assert(tv@ == orig_v);
            assert(Op::pre(tv@));
        }
        let out_t = op(tv);
        let Tracked(out) = out_t;
        atomic_with_ghost!(slot.served => store(r); ghost sg => {
            sg.srv_seq.agree(&srv.srv_seq);
            if sg.turn is Some {
                tok.disjoint(sg.turn.tracked_borrow());
            }
            sg.srv_seq.update(&mut srv.srv_seq, r);
            sg.turn = Some(tok);
            sg.payload = Some(out);
            sg.input_auth = Some(ia);
            sg.input = in_ghost;
            srv.seq = r;
        });
        true
    }
}

/// Spins between reports. The line is a diagnostic, not a timeout, so the constant is not a bound
/// on a descheduled vCPU: it only decides when the line appears.
pub const REPORT_SPINS: u64 = 1 << 26;

/// `REPORT_SPINS` as a number: above zero, and far enough below `u64::MAX` that a count under it
/// can be stepped.
proof fn lemma_report_spins()
    ensures
        REPORT_SPINS == 0x400_0000, // not a page size: 1<<26, the spin-report interval
{
    assert((1u64 << 26) == 0x400_0000u64) by (bit_vector); // not a page size: 1<<26, the spin-report interval
}

/// ASCII `'0'`.
pub const ASCII_ZERO: u64 = 48;

/// `"bridge w"`, little-endian, the first word of a wait report.
pub(crate) const REPORT_PREFIX_A: u64 = 0x7720_6567_6469_7262;

/// `"ait cpu "`, little-endian, the second word. The two words are `"bridge wait cpu "`.
pub(crate) const REPORT_PREFIX_B: u64 = 0x2075_7063_2074_6961;

/// The bytes of `REPORT_PREFIX_A` and `REPORT_PREFIX_B` are `"bridge wait cpu "`.
proof fn lemma_report_prefix()
    ensures
        (REPORT_PREFIX_A & 0xff) == 0x62,
        ((REPORT_PREFIX_A >> 8) & 0xff) == 0x72,
        ((REPORT_PREFIX_A >> 16) & 0xff) == 0x69,
        ((REPORT_PREFIX_A >> 24) & 0xff) == 0x64,
        ((REPORT_PREFIX_A >> 32) & 0xff) == 0x67,
        ((REPORT_PREFIX_A >> 40) & 0xff) == 0x65,
        ((REPORT_PREFIX_A >> 48) & 0xff) == 0x20,
        ((REPORT_PREFIX_A >> 56) & 0xff) == 0x77,
        (REPORT_PREFIX_B & 0xff) == 0x61,
        ((REPORT_PREFIX_B >> 8) & 0xff) == 0x69,
        ((REPORT_PREFIX_B >> 16) & 0xff) == 0x74,
        ((REPORT_PREFIX_B >> 24) & 0xff) == 0x20,
        ((REPORT_PREFIX_B >> 32) & 0xff) == 0x63,
        ((REPORT_PREFIX_B >> 40) & 0xff) == 0x70,
        ((REPORT_PREFIX_B >> 48) & 0xff) == 0x75,
        ((REPORT_PREFIX_B >> 56) & 0xff) == 0x20,
{
    assert(
        (REPORT_PREFIX_A & 0xff) == 0x62 && ((REPORT_PREFIX_A >> 8) & 0xff) == 0x72
            && ((REPORT_PREFIX_A >> 16) & 0xff) == 0x69 && ((REPORT_PREFIX_A >> 24) & 0xff) == 0x64
            && ((REPORT_PREFIX_A >> 32) & 0xff) == 0x67 && ((REPORT_PREFIX_A >> 40) & 0xff) == 0x65
            && ((REPORT_PREFIX_A >> 48) & 0xff) == 0x20 && ((REPORT_PREFIX_A >> 56) & 0xff) == 0x77
            && (REPORT_PREFIX_B & 0xff) == 0x61 && ((REPORT_PREFIX_B >> 8) & 0xff) == 0x69
            && ((REPORT_PREFIX_B >> 16) & 0xff) == 0x74 && ((REPORT_PREFIX_B >> 24) & 0xff) == 0x20
            && ((REPORT_PREFIX_B >> 32) & 0xff) == 0x63 && ((REPORT_PREFIX_B >> 40) & 0xff) == 0x70
            && ((REPORT_PREFIX_B >> 48) & 0xff) == 0x75 && ((REPORT_PREFIX_B >> 56) & 0xff) == 0x20
    ) by (bit_vector);
}

/// A one-digit number plus `'0'` fits in the low byte.
proof fn lemma_one_digit(n: u64) by (bit_vector)
    requires
        n < 10,
        ASCII_ZERO == 48,
    ensures
        add(n, ASCII_ZERO) < 256,
        add(n, ASCII_ZERO) % 256u64 == add(n, ASCII_ZERO),
        add(n, ASCII_ZERO) / 256u64 == 0,
{
}

/// `n` in `10..100` is two digits, each below 10, and those digits rebuild `n`.
proof fn lemma_two_digits(n: u64, tens: u64, ones: u64) by (bit_vector)
    requires
        n < 100,
        n >= 10,
        tens == n / 10u64,
        ones == n % 10u64,
    ensures
        tens < 10,
        ones < 10,
        n == add(mul(tens, 10u64), ones),
{
}

/// `lo` and `hi` below 256 pack into a word whose first two bytes are those values.
proof fn lemma_pack_byte(lo: u64, hi: u64) by (bit_vector)
    requires
        lo < 256,
        hi < 256,
    ensures
        add(lo, mul(hi, 256u64)) % 256u64 == lo,
        (add(lo, mul(hi, 256u64)) / 256u64) % 256u64 == hi,
        add(lo, mul(hi, 256u64)) / 65536u64 == 0, // not a page size: 2^16, the third byte of a word
{
}

/// A u64 divided by 256 yielding 0 is itself below 256, so its low byte is itself.
proof fn lemma_below_256(d: u64) by (bit_vector)
    requires
        d / 256u64 == 0,
    ensures
        d < 256,
        d % 256u64 == d,
{
}

/// A u64 divided by 65536 yielding 0 is itself below 65536.
proof fn lemma_below_65536(d: u64) by (bit_vector)
    requires
        d / 65536u64 == 0, // not a page size: 2^16, the third byte of a word
    ensures
        d < 65536, // not a page size: 2^16, the third byte of a word
{
}

/// Adding a newline at byte 2 (`10 * 65536`) keeps the two low bytes of `digits`.
proof fn lemma_newline_at_byte2(digits: u64) by (bit_vector)
    requires
        digits < 65536, // not a page size: 2^16, the third byte of a word
    ensures
        add(digits, mul(10u64, 65536u64)) % 256u64 == digits % 256u64, // not a page size: 2^16, the third byte of a word
        (add(digits, mul(10u64, 65536u64)) / 256u64) % 256u64 == (digits / 256u64) % 256u64, // not a page size: 2^16, the third byte of a word
        (add(digits, mul(10u64, 65536u64)) / 65536u64) % 256u64 == 10, // not a page size: 2^16, the third byte of a word
        add(digits, mul(10u64, 65536u64)) / 16777216u64 == 0, // not a page size: 2^24, past that byte
{
}

/// Writes the decimal digits of `n < 100` into the low bytes of a word, little-endian, most
/// significant digit first, with no leading zero except for zero. Returns the word and how many
/// digits were written. A digit's byte is `ASCII_ZERO` plus that digit: the low byte is `word % 256`,
/// the next is `(word / 256) % 256`.
pub(crate) fn write_decimal(n: u64) -> (res: (u64, u64))
    requires
        n < 100,
    ensures
        res.1 == if n < 10 { 1u64 } else { 2u64 },
        n < 10 ==> res.0 % 256u64 == add(n, ASCII_ZERO) && res.0 / 256u64 == 0,
        n >= 10 ==> res.0 % 256u64 == add(n / 10u64, ASCII_ZERO) && (res.0 / 256u64) % 256u64
            == add(n % 10u64, ASCII_ZERO) && res.0 / 65536u64 == 0, // not a page size: 2^16, the third byte of a word
{
    proof {
        assert(ASCII_ZERO == 48);
    }
    if n < 10 {
        let word = n + ASCII_ZERO;
        proof {
            lemma_one_digit(n);
            assert(word == add(n, ASCII_ZERO));
        }
        (word, 1)
    } else {
        let tens = n / 10;
        let ones = n % 10;
        let lo = tens + ASCII_ZERO;
        let hi = ones + ASCII_ZERO;
        let word = lo + hi * 256;
        proof {
            lemma_two_digits(n, tens, ones);
            assert(lo == add(tens, ASCII_ZERO));
            assert(hi == add(ones, ASCII_ZERO));
            lemma_pack_byte(lo, hi);
            assert(word == add(lo, mul(hi, 256u64)));
        }
        (word, 2)
    }
}

/// The five words `serial_write` sends for one report: `"bridge wait cpu "` then the decimal core,
/// then a newline. Little-endian, and the byte after the newline is zero so the write stops.
pub(crate) fn report_line(cpu: u64) -> (words: (u64, u64, u64, u64, u64))
    requires
        cpu < 100,
    ensures
        words.0 == REPORT_PREFIX_A,
        words.1 == REPORT_PREFIX_B,
        words.3 == 0 && words.4 == 0,
        cpu < 10 ==> words.2 % 256u64 == add(cpu, ASCII_ZERO) && (words.2 / 256u64) % 256u64 == 10
            && words.2 / 65536u64 == 0, // not a page size: 2^16, the third byte of a word
        cpu >= 10 ==> words.2 % 256u64 == add(cpu / 10u64, ASCII_ZERO) && (words.2 / 256u64)
            % 256u64 == add(cpu % 10u64, ASCII_ZERO) && (words.2 / 65536u64) % 256u64 == 10 // not a page size: 2^16, the third byte of a word
            && words.2 / 16777216u64 == 0, // not a page size: 2^24, past that byte
{
    proof {
        lemma_report_prefix();
        assert(ASCII_ZERO == 48);
    }
    let (digits, len) = write_decimal(cpu);
    if cpu < 10 {
        let word = digits + 10 * 256;
        proof {
            assert(len == 1);
            assert(digits % 256u64 == add(cpu, ASCII_ZERO) && digits / 256u64 == 0);
            lemma_below_256(digits);
            assert(digits == add(cpu, ASCII_ZERO));
            lemma_pack_byte(digits, 10u64);
            assert(word == add(digits, mul(10u64, 256u64)));
        }
        (REPORT_PREFIX_A, REPORT_PREFIX_B, word, 0, 0)
    } else {
        let word = digits + 10 * 65536; // not a page size: 2^16, the third byte of a word
        proof {
            assert(len == 2);
            assert(digits / 65536u64 == 0); // not a page size: 2^16, the third byte of a word
            lemma_below_65536(digits);
            lemma_newline_at_byte2(digits);
            assert(word == add(digits, mul(10u64, 65536u64))); // not a page size: 2^16, the third byte of a word
        }
        (REPORT_PREFIX_A, REPORT_PREFIX_B, word, 0, 0)
    }
}

/// Prints one wait report. The host test has no serial port, so `in` from `serial_write_byte` would
/// fault there; that build checks the words, and the kernel image writes them.
#[cfg(not(test))]
fn write_report(a: u64, b: u64, c: u64, d: u64, e: u64, steps: Tracked<&mut Steps>) {
    let Tracked(inner) = steps;
    crate::capability::console::serial_write(a, b, c, d, e, Tracked(inner));
}

#[cfg(test)]
fn write_report(a: u64, b: u64, c: u64, d: u64, e: u64, steps: Tracked<&mut Steps>) {
    let _ = (a, b, c, d, e, steps);
}

fn report_wait(cpu: usize, Tracked(steps): Tracked<&mut Steps>)
    requires
        cpu < NUM_CPUS,
{
    let cpu64: u64 = cpu as u64;
    proof {
        assert(NUM_CPUS == 32);
        assert(cpu64 < 100) by (bit_vector)
            requires
                cpu < NUM_CPUS,
                NUM_CPUS == 32,
                cpu64 == cpu as u64,
        ;
    }
    let (a, b, c, d, e) = report_line(cpu64);
    write_report(a, b, c, d, e, Tracked(steps));
}

/// A tracked value for `witness_bridge`, carrying a `nat` that the witness's operation steps.
pub tracked struct WitnessToken {
    pub ghost n: nat,
}

/// Specification-only operation for `witness_bridge`: advances the token's counter by one.
pub struct WitnessOp;

impl ChannelOp<WitnessToken> for WitnessOp {
    open spec fn pre(_v: WitnessToken) -> bool {
        true
    }

    open spec fn post(input: WitnessToken, output: WitnessToken) -> bool {
        output.n == input.n + 1
    }
}

/// The witness: constructs a bridge, lends a tracked token to `cpu`, serves it once with the
/// supplied operation, takes it back with `try_take`, then runs a second round through `wait`.
/// Built into no image.
#[cfg(verus_keep_ghost)]
pub fn witness_bridge(cpu: usize) -> (ret: (bool, Option<Tracked<WitnessToken>>))
    requires
        cpu < NUM_CPUS,
    ensures
        ret.0,
        ret.1 is Some,
{
    let (new_bridge, Tracked(mut reqs), Tracked(mut srvs)) = CoreBridge::new();
    let bridge: CoreBridge<WitnessToken, WitnessOp> = new_bridge;
    proof {
        assert(reqs.dom().contains(cpu as int));
        assert(srvs.dom().contains(cpu as int));
    }
    let tracked mut req = reqs.tracked_remove(cpu as int);
    let tracked mut srv = srvs.tracked_remove(cpu as int);

    let tracked tok1 = WitnessToken { n: 0 };
    bridge.send(cpu, Tracked(&mut req), Tracked(tok1));
    let mut served = bridge.serve(
        cpu,
        |tw: Tracked<WitnessToken>| -> (res: Tracked<WitnessToken>)
            ensures
                res@.n == tw@.n + 1,
        {
            let tracked next_tok = WitnessToken { n: tw@.n + 1 };
            Tracked(next_tok)
        },
        Tracked(&mut srv),
        Tracked(Some(&req)),
    );
    let taken = bridge.try_take(cpu, Tracked(&mut req), Tracked(Some(&srv)));
    proof {
        assert(taken matches Some(out) && out@.n == 1);
    }

    let tracked tok2 = WitnessToken { n: 10 };
    bridge.send(cpu, Tracked(&mut req), Tracked(tok2));
    served = bridge.serve(
        cpu,
        |tw: Tracked<WitnessToken>| -> (res: Tracked<WitnessToken>)
            ensures
                res@.n == tw@.n + 1,
        {
            let tracked next_tok = WitnessToken { n: tw@.n + 1 };
            Tracked(next_tok)
        },
        Tracked(&mut srv),
        Tracked(Some(&req)),
    );
    let tracked mut steps = Steps::fresh();
    let Tracked(out2) = bridge.wait(cpu, Tracked(&mut req), Tracked(&mut steps));
    proof {
        assert(out2.n == 11);
    }
    (served, taken)
}

} // verus!

#[cfg(test)]
mod tests {
    extern crate std;

    use core::sync::atomic::{AtomicBool, AtomicUsize as StdAtomicUsize, Ordering};
    use std::thread;

    use super::*;

    verus! {
        struct TestOp;

        impl ChannelOp<usize> for TestOp {
            open spec fn pre(_v: usize) -> bool {
                true
            }

            open spec fn post(input: usize, output: usize) -> bool {
                output == input
            }
        }

        fn test_run_rounds() {
            let _ = TestOp;
            let rounds: usize = 50_000;
            let cpu: usize = 1;
            let (bridge, Tracked(mut reqs), Tracked(mut srvs)) = CoreBridge::<usize, TestOp>::new();
            let tracked mut req = reqs.tracked_remove(cpu as int);
            let tracked mut srv = srvs.tracked_remove(cpu as int);

            let input_word = StdAtomicUsize::new(0);
            let output_word = StdAtomicUsize::new(0);
            let served_count = StdAtomicUsize::new(0);
            let done = AtomicBool::new(false);

            // Confirm serve returns false and skips the operation when no request is pending.
            let mut idle_ran = false;
            let did_idle = bridge.serve(
                cpu,
                |t| {
                    idle_ran = true;
                    t
                },
                Tracked(&mut srv),
                Tracked(None),
            );
            assert!(!did_idle);
            assert!(!idle_ran);

            // Confirm try_take returns None while words differ, and Some after serve runs.
            bridge.send(cpu, Tracked(&mut req), Tracked(0));
            let before_serve = bridge.try_take(cpu, Tracked(&mut req), Tracked(Some(&srv)));
            assert!(before_serve.is_none());
            let did_one = bridge.serve(cpu, |t| t, Tracked(&mut srv), Tracked(Some(&req)));
            assert!(did_one);
            let after_serve = bridge.try_take(cpu, Tracked(&mut req), Tracked(Some(&srv)));
            assert!(after_serve.is_some());

            thread::scope(|s| {
                s.spawn(|| {
                    while !done.load(Ordering::Acquire) {
                        bridge.serve(
                            cpu,
                            |t| {
                                let v = input_word.load(Ordering::Relaxed);
                                output_word.store(v.wrapping_mul(3).wrapping_add(7), Ordering::Relaxed);
                                served_count.fetch_add(1, Ordering::Relaxed);
                                t
                            },
                            Tracked(&mut srv),
                            Tracked(None),
                        );
                    }
                });

                let req_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let tracked mut steps = Steps::fresh();
                    let mut r: usize = 0;
                    while r < rounds {
                        let expected_in = r.wrapping_add(100);
                        input_word.store(expected_in, Ordering::Relaxed);
                        bridge.send(cpu, Tracked(&mut req), Tracked(r));
                        let _ = bridge.wait(cpu, Tracked(&mut req), Tracked(&mut steps));
                        let got = output_word.load(Ordering::Relaxed);
                        assert_eq!(got, expected_in.wrapping_mul(3).wrapping_add(7));
                        assert_eq!(served_count.load(Ordering::Relaxed), r + 1);
                        r += 1;
                    }
                }));
                done.store(true, Ordering::Release);
                if let Err(payload) = req_res {
                    std::panic::resume_unwind(payload);
                }
            });
        }

        fn test_polling_two_slots() {
            let rounds: usize = 10_000;
            let c0: usize = 0;
            let c1: usize = NUM_CPUS - 1;
            let (bridge, Tracked(mut reqs), Tracked(mut srvs)) = CoreBridge::<usize, TestOp>::new();
            let tracked mut req0 = reqs.tracked_remove(c0 as int);
            let tracked mut req1 = reqs.tracked_remove(c1 as int);
            let tracked mut srv0 = srvs.tracked_remove(c0 as int);
            let tracked mut srv1 = srvs.tracked_remove(c1 as int);

            let in0 = StdAtomicUsize::new(0);
            let out0 = StdAtomicUsize::new(0);
            let in1 = StdAtomicUsize::new(0);
            let out1 = StdAtomicUsize::new(0);
            let done = AtomicBool::new(false);

            thread::scope(|s| {
                s.spawn(|| {
                    while !done.load(Ordering::Acquire) {
                        bridge.serve(
                            c0,
                            |t| {
                                let v = in0.load(Ordering::Relaxed);
                                out0.store(v.wrapping_add(1), Ordering::Relaxed);
                                t
                            },
                            Tracked(&mut srv0),
                            Tracked(None),
                        );
                        bridge.serve(
                            c1,
                            |t| {
                                let v = in1.load(Ordering::Relaxed);
                                out1.store(v.wrapping_add(2), Ordering::Relaxed);
                                t
                            },
                            Tracked(&mut srv1),
                            Tracked(None),
                        );
                    }
                });

                let req_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut r: usize = 0;
                    while r < rounds {
                        in0.store(r, Ordering::Relaxed);
                        in1.store(r, Ordering::Relaxed);
                        bridge.send(c0, Tracked(&mut req0), Tracked(r));
                        bridge.send(c1, Tracked(&mut req1), Tracked(r));
                        loop {
                            if bridge.try_take(c0, Tracked(&mut req0), Tracked(None)).is_some() {
                                break;
                            }
                            thread::yield_now();
                        }
                        loop {
                            if bridge.try_take(c1, Tracked(&mut req1), Tracked(None)).is_some() {
                                break;
                            }
                            thread::yield_now();
                        }
                        assert_eq!(out0.load(Ordering::Relaxed), r.wrapping_add(1));
                        assert_eq!(out1.load(Ordering::Relaxed), r.wrapping_add(2));
                        r += 1;
                    }
                }));
                done.store(true, Ordering::Release);
                if let Err(payload) = req_res {
                    std::panic::resume_unwind(payload);
                }
            });
        }

        fn line_of(words: (u64, u64, u64, u64, u64)) -> std::vec::Vec<u8> {
            let packed = [words.0, words.1, words.2, words.3, words.4];
            let mut out: std::vec::Vec<u8> = std::vec::Vec::new();
            let mut w: usize = 0;
            while w < 5 {
                let mut i: usize = 0;
                while i < 8 {
                    let b = ((packed[w] >> (8 * i)) & 0xff) as u8;
                    if b == 0 {
                        return out;
                    }
                    out.push(b);
                    i = i + 1;
                }
                w = w + 1;
            }
            out
        }

        fn test_report_line_names_the_core() {
            assert_eq!(line_of(report_line(0)), b"bridge wait cpu 0\n".to_vec());
            assert_eq!(line_of(report_line(7)), b"bridge wait cpu 7\n".to_vec());
            assert_eq!(line_of(report_line(10)), b"bridge wait cpu 10\n".to_vec());
            assert_eq!(line_of(report_line(31)), b"bridge wait cpu 31\n".to_vec());
        }
    }

    #[test]
    fn host_report_line_names_the_core() {
        test_report_line_names_the_core();
    }

    #[test]
    fn host_two_threads_many_rounds() {
        test_run_rounds();
    }

    #[test]
    fn host_polling_two_slots_many_rounds() {
        test_polling_two_slots();
    }
}
