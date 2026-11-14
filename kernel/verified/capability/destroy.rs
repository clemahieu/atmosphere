// SPDX-License-Identifier: MIT

//! Destroy through a control capability: the target is dead in one bounded step while capabilities to
//! it remain, and its references, capabilities and bindings stay as they were until a retype tears it
//! down. A thread Running on a core is moved off by that core, which a pending stop tells to make it
//! Dead. A process's threads are moved off by their own cores: each core on the process's space's list
//! gets an IPI, and finds its current thread's process dead at its next kernel entry. See
//! design/one-lock-bounded-steps/ and design/process-holds-capabilities/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::thread::ThreadState;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// The cores below n on a space's list of cores, in increasing order.
pub open spec fn listed_cores(list: u32, n: int) -> Seq<usize>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else if core_listed(list, n - 1) {
        listed_cores(list, n - 1).push((n - 1) as usize)
    } else {
        listed_cores(list, n - 1)
    }
}

/// Exactly the listed cores below n are among them.
pub proof fn lemma_listed_cores(list: u32, n: int, c: usize)
    requires
        0 <= n <= NUM_CPUS,
    ensures
        listed_cores(list, n).contains(c) <==> c < n && core_listed(list, c as int),
    decreases n,
{
    if n > 0 {
        lemma_listed_cores(list, n - 1, c);
        let s = listed_cores(list, n - 1);
        if core_listed(list, n - 1) {
            let t = s.push((n - 1) as usize);
            assert(listed_cores(list, n) == t);
            if t.contains(c) {
                let k = choose|k: int| 0 <= k < t.len() && t[k] == c;
                if k < s.len() {
                    assert(s[k] == c);
                    assert(s.contains(c));
                } else {
                    assert(c == n - 1);
                }
            }
            if c < n && core_listed(list, c as int) {
                if c < n - 1 {
                    let k = choose|k: int| 0 <= k < s.len() && s[k] == c;
                    assert(t[k] == c);
                } else {
                    assert(t[s.len() as int] == c);
                }
                assert(t.contains(c));
            }
        } else {
            assert(listed_cores(list, n) == s);
        }
    }
}

/// sent with an IPI to each core on the list after it, in increasing order: one bounded loop over the
/// cores, one unit per core. The send is ghost: see design/one-lock-bounded-steps/.
pub fn send_to_listed(list: u32, Ghost(sent): Ghost<Seq<usize>>, Tracked(steps): Tracked<&mut Steps>) -> (ret: Ghost<Seq<usize>>)
    ensures
        final(steps).count <= old(steps).count + NUM_CPUS,
        ret@ == sent + listed_cores(list, NUM_CPUS as int),
{
    let ghost mut out = sent;
    let mut c: usize = 0;
    let ghost start = steps.count;
    while c != NUM_CPUS
        invariant
            0 <= c <= NUM_CPUS,
            steps.count == start + c,
            out == sent + listed_cores(list, c as int),
        decreases NUM_CPUS - c,
    {
        if (list >> (c as u32)) & 1u32 == 1u32 {
            proof {
                assert(core_listed(list, c as int));
                assert(out.push(c) =~= sent + listed_cores(list, c as int).push(c));
                out = out.push(c);
            }
        } else {
            proof {
                assert(!core_listed(list, c as int));
            }
        }
        c = c + 1;
        proof {
            steps.step();
        }
    }
    Ghost(out)
}

impl CapKernel {
    /// Capability n names a dead process or thread: a process whose record is dead, or a thread that is
    /// Dead, destroyed while Running, or bound to a process whose record is dead. Nothing may start or
    /// control a thread of a destroyed process, whose core moves it off at its next entry. Every
    /// operation refuses such a capability except a claim, which is a move out of a controlled
    /// process's table, a revoke and a delete: see design/teardown-driven-by-retype/.
    pub open spec fn cap_dead(&self, n: usize) -> bool {
        let o = self.payload_of(n);
        match o.kind {
            CapKind::Process => self.processes.records@[o.base].value().dead,
            CapKind::Thread => {
                let r = self.threads.records@[o.base].value();
                ||| r.state is Dead
                ||| r.dying
                ||| (r.process is Some && self.processes.records@[r.process->Some_0].value().dead)
            },
            _ => false,
        }
    }

    /// Reads whether the process at p is dead, in one load.
    pub fn is_process_dead(&self, p: usize) -> (ret: bool)
        requires
            self.wf(),
            self.processes.records@.contains_key(p),
        ensures
            ret == self.processes.records@[p].value().dead,
    {
        proof {
            assert(process_wf(&self.processes, &self.blocks, p));
        }
        PPtr::<ProcessRecord>::from_usize(p + PROCESS_RECORD_PAGE * PAGE_SZ).borrow(
            Tracked(self.processes.records.borrow().tracked_borrow(p)),
        ).dead
    }

    /// Reads cap_dead of capability n, whose payload is given, in at most two loads: the thread's
    /// record and its process's, or the process's record.
    pub fn is_cap_dead(&self, n: usize, payload: Payload) -> (ret: bool)
        requires
            self.wf(),
            self.is_cap(n),
            payload == self.payload_of(n),
        ensures
            ret == self.cap_dead(n),
    {
        match payload.kind {
            CapKind::Process => {
                let p = payload.base;
                proof {
                    self.lemma_process_cap(n);
                }
                self.is_process_dead(p)
            },
            CapKind::Thread => {
                let t = payload.base;
                proof {
                    self.lemma_thread_cap(n);
                    assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
                }
                let record = *PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ).borrow(
                    Tracked(self.threads.records.borrow().tracked_borrow(t)),
                );
                let dead = match record.state {
                    ThreadState::Dead => true,
                    _ => false,
                };
                if dead || record.dying {
                    return true;
                }
                match record.process {
                    None => false,
                    Some(p) => {
                        proof {
                            assert(self.processes.records@.contains_key(p));
                        }
                        self.is_process_dead(p)
                    },
                }
            },
            _ => false,
        }
    }

    /// Index i of the table at root holds a capability with the control right naming a process or a
    /// thread that is not dead. A destroyed target waits for retype's teardown, so destroying it again
    /// is refused: see design/teardown-driven-by-retype/.
    pub open spec fn can_destroy(&self, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& (self.payload_of(n).kind is Process || self.payload_of(n).kind is Thread)
        &&& self.payload_of(n).rights & right_bit(Right::Control) != 0
        &&& !self.cap_dead(n)
    }

    /// The control capability at index i of the table at root names core c's current thread, or the
    /// process that thread's record names.
    pub open spec fn destroys_own(&self, c: int, root: usize, i: usize) -> bool {
        let n = self.tables.node_of(root, i);
        let o = self.payload_of(n).base;
        match self.cores@[c].current_thread {
            Some(t) => {
                ||| self.payload_of(n).kind is Thread && o == t
                ||| self.payload_of(n).kind is Process && self.threads.records@[t].value().process == Some(o)
            },
            None => false,
        }
    }

    /// The step set process p's record dead and sent an IPI to each core on p's space's list of cores, in
    /// order, and changed nothing else.
    pub open spec fn process_destroyed(pre: Self, post: Self, p: usize) -> bool {
        &&& post.list == pre.list
        &&& post.cores == pre.cores
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.iommus == pre.iommus
        &&& post.mapped == pre.mapped
        &&& post.blocks == pre.blocks
        &&& post.tables == pre.tables
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.frames == pre.frames
        &&& post.table_pages == pre.table_pages
        &&& post.spaces == pre.spaces
        &&& post.mappings == pre.mappings
        &&& post.zeroing == pre.zeroing
        &&& post.holders == pre.holders
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.processes.spare == pre.processes.spare
        &&& post.processes.holders == pre.processes.holders
        &&& post.processes.bound == pre.processes.bound
        &&& post.processes.records@.dom() == pre.processes.records@.dom()
        &&& forall|q: usize| q != p && #[trigger] post.processes.records@.contains_key(q)
            ==> post.processes.records@[q] == pre.processes.records@[q]
        &&& post.processes.records@[p].addr() == pre.processes.records@[p].addr()
        &&& post.processes.records@[p].is_init()
        &&& post.processes.records@[p].value() == (ProcessRecord { dead: true })
        &&& post.stop_ipis@ == pre.stop_ipis@ + listed_cores(pre.spaces.loaded@[p].value().list, NUM_CPUS as int)
    }

    /// Whether a destroy of the capability at index i of the table at root answered ok exactly when
    /// can_destroy holds, and left the kernel as it was when it refused. destroy's ensures and
    /// spec_destroyed both call it: design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn destroy_answered(pre: Self, post: Self, root: usize, i: usize, ok: bool) -> bool {
        &&& ok == pre.can_destroy(root, i)
        &&& !ok ==> post == pre
    }

    /// What a destroy leaves as it was, whether it answered ok or refused: the process each thread is
    /// bound to. destroy's ensures and spec_destroyed both call it:
    /// design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn destroy_kept(pre: Self, post: Self) -> bool {
        bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables)
    }

    /// What a destroy from core c of the capability at index i of the table at root did when it
    /// answered ok: the process it names destroyed as process_destroyed says, with an IPI for exactly
    /// the cores that have its space loaded, or the thread it names destroyed as thread_destroyed says;
    /// core c's thread left to be moved off when the destroy was of its own thread or process; and the
    /// step discharging the destroy of the capability. destroy's ensures and spec_destroyed both call
    /// it: design/invoked-arm-is-the-operation-postcondition/.
    pub open spec fn destroy_done(pre: Self, post: Self, c: usize, root: usize, i: usize) -> bool {
        let n = pre.tables.node_of(root, i);
        let o = pre.payload_of(n).base;
        &&& pre.destroys_own(c as int, root, i) ==> post.must_leave(c as int)
        &&& pre.payload_of(n).kind is Process ==> {
            &&& pre.processes.records@.contains_key(o)
            &&& Self::process_destroyed(pre, post, o)
            &&& forall|d: usize| #[trigger] listed_cores(pre.spaces.loaded@[o].value().list, NUM_CPUS as int).contains(d)
                <==> d < NUM_CPUS && pre.loaded(d as int, o)
        }
        &&& pre.payload_of(n).kind is Thread ==> {
            &&& pre.threads.records@.contains_key(o)
            &&& Self::thread_destroyed(pre, post, c, o)
        }
        &&& discharges(pre.view(), post.view(), root, Effect::Destroy { cap: n })
    }

    /// Destroys, from core c, the process or thread the control capability at index i of the table at
    /// root names. A process's record is dead, and each core that has its space loaded gets an IPI, so
    /// that core finds its current thread's process dead at its next kernel entry; its threads, table,
    /// space, references and capabilities stay as they were. A thread is destroyed as
    /// thread_destroyed says. Destroying the caller's own thread or its own process leaves the caller's
    /// thread to be moved off by check_current before it returns to user mode. A target already dead is
    /// refused. The index comes from user space, so it can be refused, and a refusal changes nothing.
    pub fn destroy(&mut self, c: usize, root: usize, i: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS,
            final(self).wf(),
            Self::destroy_answered(*old(self), *final(self), root, i, ret),
            Self::destroy_kept(*old(self), *final(self)),
            ret ==> Self::destroy_done(*old(self), *final(self), c, root, i),
    {
        let ghost pre = *self;
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return false; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return false;
        }
        proof {
            pre.lemma_slot(root, i);
            assert(pre.tables.is_cap(&pre.list, n));
            assert(payload == pre.payload_of(n));
            assert(right_bit(Right::Control) == 128);
        }
        if payload.rights & 128 == 0 {
            return false;
        }
        if self.is_cap_dead(n, payload) {
            return false;
        }
        match payload.kind {
            CapKind::Process => {
                proof {
                    pre.lemma_process_cap(n);
                }
                let p = payload.base;
                self.destroy_process(p, Tracked(steps));
                proof {
                    let post = *self;
                    assert forall|d: usize| #[trigger] listed_cores(pre.spaces.loaded@[p].value().list, NUM_CPUS as int).contains(d)
                        <==> d < NUM_CPUS && pre.loaded(d as int, p) by {
                        lemma_listed_cores(pre.spaces.loaded@[p].value().list, NUM_CPUS as int, d);
                    }
                    assert(post.view() == pre.view());
                }
                true
            },
            CapKind::Thread => {
                proof {
                    pre.lemma_thread_cap(n);
                    assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, payload.base));
                }
                self.destroy_thread(c, payload.base);
                proof {
                    let post = *self;
                    let r = pre.threads.records@[payload.base].value();
                    assert(saved_registers(&self.threads) =~= saved_registers(&pre.threads));
                    match r.state {
                        ThreadState::Running { .. } => Self::lemma_record_written_waits(pre, post, payload.base,
                            ThreadRecord { pending_stop: true, dying: true, ..r }),
                        _ => Self::lemma_record_written_waits(pre, post, payload.base,
                            ThreadRecord { state: ThreadState::Dead, pending_stop: false, dying: false, ..r }),
                    }
                    lemma_blocked_on_shrinks(&pre.threads, &post.threads);
                    assert(unwaits(pre.view(), post.view()));
                    lemma_unwaits_discharges(pre.view(), post.view(), root, Effect::Destroy { cap: n });
                    if pre.destroys_own(c as int, root, i) {
                        reveal(current_wf);
                        assert(runs(pre.cores@, c as int, payload.base));
                    }
                }
                true
            },
            _ => false,
        }
    }

    /// Sets process p's record dead and sends an IPI to each core on its space's list of cores, one
    /// load of the list and a bounded loop over the cores.
    fn destroy_process(&mut self, p: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            old(self).processes.records@.contains_key(p),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS,
            final(self).wf(),
            Self::process_destroyed(*old(self), *final(self), p),
            old(self).spaces.loaded@.contains_key(p),
    {
        let ghost pre = *self;
        proof {
            assert(process_wf(&pre.processes, &pre.blocks, p));
            assert(pre.spaces.roots@.contains_key(p));
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, p));
        }
        let ptr = PPtr::<ProcessRecord>::from_usize(p + PROCESS_RECORD_PAGE * PAGE_SZ);
        let tracked mut perm;
        proof {
            perm = self.processes.records.borrow_mut().tracked_remove(p);
        }
        ptr.write(Tracked(&mut perm), ProcessRecord { dead: true });
        proof {
            self.processes.records.borrow_mut().tracked_insert(p, perm);
        }
        let list = PPtr::<SpaceCores>::from_usize(p + SPACE_CORES_PAGE * PAGE_SZ).borrow(
            Tracked(self.spaces.loaded.borrow().tracked_borrow(p)),
        ).list;
        self.stop_ipis = send_to_listed(list, Ghost(pre.stop_ipis@), Tracked(steps));
        proof {
            let post = *self;
            assert(post.processes.records@.dom() =~= pre.processes.records@.dom());
            assert forall|q: usize| #[trigger] post.processes.records@.contains_key(q) implies process_wf(&post.processes, &post.blocks, q) by {
                assert(process_wf(&pre.processes, &pre.blocks, q));
            }
            assert(processes_wf(&post.list, &post.tables, &post.processes, &post.blocks));
            Self::lemma_tlb_same(pre, post);
            assert(post.wf());
        }
    }
}

} // verus!
