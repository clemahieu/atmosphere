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
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::thread::ThreadState;
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
/// cores. The send is ghost: see design/one-lock-bounded-steps/.
pub fn send_to_listed(list: u32, Ghost(sent): Ghost<Seq<usize>>) -> (ret: Ghost<Seq<usize>>)
    ensures
        ret@ == sent + listed_cores(list, NUM_CPUS as int),
{
    let ghost mut out = sent;
    let mut c: usize = 0;
    while c != NUM_CPUS
        invariant
            0 <= c <= NUM_CPUS,
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
    }
    Ghost(out)
}

impl CapKernel {
    /// Capability n names a dead process or thread: a process whose record is dead, or a thread that is
    /// Dead, destroyed while Running, or bound to a process whose record is dead. Nothing may start or
    /// control a thread of a destroyed process, whose core moves it off at its next entry. Every
    /// operation refuses such a capability except claim, revoke and delete: see
    /// design/teardown-driven-by-retype/.
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
        PPtr::<ProcessRecord>::from_usize(p + PROCESS_RECORD_PAGE * 4096).borrow(
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
                let record = *PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * 4096).borrow(
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

    /// Destroys, from core c, the process or thread the control capability at index i of the table at
    /// root names. A process's record is dead, and each core that has its space loaded gets an IPI, so
    /// that core finds its current thread's process dead at its next kernel entry; its threads, table,
    /// space, references and capabilities stay as they were. A thread is destroyed as
    /// thread_destroyed says. Destroying the caller's own thread or its own process leaves the caller's
    /// thread to be moved off by check_current before it returns to user mode. A target already dead is
    /// refused. The index comes from user space, so it can be refused, and a refusal changes nothing.
    pub fn destroy(&mut self, c: usize, root: usize, i: usize) -> (ret: bool)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            ret == old(self).can_destroy(root, i),
            !ret ==> *final(self) == *old(self),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret && old(self).destroys_own(c as int, root, i) ==> final(self).must_leave(c as int),
            ret ==> {
                let n = old(self).tables.node_of(root, i);
                let o = old(self).payload_of(n).base;
                &&& old(self).payload_of(n).kind is Process ==> {
                    &&& old(self).processes.records@.contains_key(o)
                    &&& Self::process_destroyed(*old(self), *final(self), o)
                    &&& forall|d: usize| #[trigger] listed_cores(old(self).spaces.loaded@[o].value().list, NUM_CPUS as int).contains(d)
                        <==> d < NUM_CPUS && old(self).loaded(d as int, o)
                }
                &&& old(self).payload_of(n).kind is Thread ==> {
                    &&& old(self).threads.records@.contains_key(o)
                    &&& Self::thread_destroyed(*old(self), *final(self), c, o)
                }
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Destroy { cap: n })
            },
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
                self.destroy_process(p);
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
                    assert(self.view() == pre.view());
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
    fn destroy_process(&mut self, p: usize)
        requires
            old(self).wf(),
            old(self).processes.records@.contains_key(p),
        ensures
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
        let ptr = PPtr::<ProcessRecord>::from_usize(p + PROCESS_RECORD_PAGE * 4096);
        let tracked mut perm;
        proof {
            perm = self.processes.records.borrow_mut().tracked_remove(p);
        }
        ptr.write(Tracked(&mut perm), ProcessRecord { dead: true });
        proof {
            self.processes.records.borrow_mut().tracked_insert(p, perm);
        }
        let list = PPtr::<SpaceCores>::from_usize(p + SPACE_CORES_PAGE * 4096).borrow(
            Tracked(self.spaces.loaded.borrow().tracked_borrow(p)),
        ).list;
        self.stop_ipis = send_to_listed(list, Ghost(pre.stop_ipis@));
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
