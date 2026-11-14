// SPDX-License-Identifier: MIT

//! A thread switch: core c leaves the thread it runs, if any, and runs the thread arriving or none.
//! One operation goes from the leaving thread's root to the arriving thread's, or to the kernel's root
//! when the core goes idle, so the order of leave, load, register write and make-current is proven
//! here and not chosen by the glue. See design/core-names-a-space-while-running-its-thread/.
use vstd::prelude::*;

verus! {

use crate::arch::*;
#[cfg(verus_keep_ghost)]
use crate::util::page_ptr_util_u::mem_valid;
#[cfg(verus_keep_ghost)]
use crate::capability::endpoint::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reply::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::schedule::*;
use crate::capability::steps::Steps;
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// switch_thread's bound in the step counter: one load_space.
pub const SWITCH_THREAD_STEPS: usize = LOAD_SPACE_STEPS;

/// tick's bound in the step counter: check_current, then at most one switch_thread.
pub const TICK_STEPS: usize = CHECK_CURRENT_STEPS + SWITCH_THREAD_STEPS;

/// What a tick on core c did. Each variant is a way the tick succeeds:
/// design/witness-per-way-an-operation-succeeds/.
pub enum TickStep {
    /// The thread selected on c took the core, and the thread c ran, if any, waits behind its equals.
    Switched,
    /// Core c keeps what it runs: no thread is Runnable on c, the one selected is of a lower priority
    /// than c's current thread, or c's address-space ids have run out of generations.
    Kept,
    /// The thread selected cannot run, its process dead or itself marked to die, and is taken off its
    /// queue; core c keeps what it runs, and the next tick selects again.
    Dropped,
}

impl CapKernel {
    /// Thread t is the one select_thread returns for core c: Runnable on c, at the front of c's queue
    /// for its priority, with no thread Runnable on c at a higher one. At most one thread is.
    pub open spec fn selected(&self, c: int, t: usize) -> bool {
        let r = self.threads.records@[t].value();
        let p = thread_priority(r);
        &&& self.threads.records@.contains_key(t)
        &&& r.state == (ThreadState::Runnable { core: c as usize })
        &&& self.threads.queues.queue(c, p as int).len() > 0
        &&& self.threads.queues.queue(c, p as int)[0] == t
        &&& forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
            && self.threads.records@[u].value().state == (ThreadState::Runnable { core: c as usize })
            ==> thread_priority(self.threads.records@[u].value()) <= p
    }

    /// Thread t, Runnable on core c and the only thread in c's queues, is the one selected there.
    pub proof fn lemma_selected_alone(&self, c: int, t: usize)
        requires
            self.wf(),
            0 <= c < NUM_CPUS,
            self.threads.records@.contains_key(t),
            self.threads.records@[t].value().state == (ThreadState::Runnable { core: c as usize }),
            self.threads.queues.queue(c, thread_priority(self.threads.records@[t].value()) as int) == seq![t],
            forall|p: int| 0 <= p < NUM_PRIORITIES && p != thread_priority(self.threads.records@[t].value())
                ==> #[trigger] self.threads.queues.queue(c, p) == Seq::<usize>::empty(),
        ensures
            self.selected(c, t),
    {
        reveal(CapKernel::wf);
        reveal(queues_wf);
        let pt = thread_priority(self.threads.records@[t].value());
        assert(self.threads.queues.queue(c, pt as int)[0] == t);
        assert forall|u: usize| #[trigger] self.threads.records@.contains_key(u)
            && self.threads.records@[u].value().state == (ThreadState::Runnable { core: c as usize })
            implies thread_priority(self.threads.records@[u].value()) <= pt by {
            let pu = thread_priority(self.threads.records@[u].value());
            assert(self.threads.queues.queue(c, pu as int).contains(u));
            if pu != pt {
                assert(self.threads.queues.queue(c, pu as int) == Seq::<usize>::empty());
            }
        }
    }

    /// Thread t outranks what core c runs: c runs nothing, or a thread whose priority is at most t's.
    /// Equal priorities take turns, so a tick hands the core to an equal.
    pub open spec fn preempts(&self, c: int, t: usize) -> bool {
        match self.cores@[c].current_thread {
            Some(o) => thread_priority(self.threads.records@[o].value()) <= thread_priority(self.threads.records@[t].value()),
            None => true,
        }
    }

    /// Thread t may be made current: not marked to die, and bound to a process that is not dead.
    pub open spec fn can_run(&self, t: usize) -> bool {
        let r = self.threads.records@[t].value();
        &&& !r.dying
        &&& r.process is Some
        &&& !self.processes.records@[r.process->Some_0].value().dead
    }

    /// From pre to post, core c left the thread it ran, if any, for thread t: t is current and Running
    /// on c, and the thread c ran is Runnable on c behind its equals, with `frame` saved whole and the
    /// marker Full. No other core and no process changed, and what a process sees changed only in the
    /// leaving thread's saved registers.
    pub open spec fn switched(pre: Self, post: Self, c: int, frame: Registers, t: usize) -> bool {
        &&& post.cores@[c].current_thread == Some(t)
        &&& post.threads.records@[t].value().state == (ThreadState::Running { core: c as usize })
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d]
        &&& post.processes == pre.processes
        &&& post.endpoints == pre.endpoints
        &&& post.replies == pre.replies
        &&& match pre.cores@[c].current_thread {
            Some(o) => {
                let r = post.threads.records@[o].value();
                &&& r.state == (ThreadState::Runnable { core: c as usize })
                &&& r.frame == frame
                &&& r.saved == FrameKind::Full
                &&& r.save@ == entry_frame_save(frame, FrameKind::Full)
                &&& at_back_of_priority(&post.threads.queues, post.threads.records@, c, thread_priority(pre.threads.records@[o].value()), o)
                &&& saves_own_frame(pre.view(), post.view(), o)
            },
            None => post.view() == pre.view(),
        }
    }

    /// What a tick on core c did from pre, whose current thread on c may return to user mode. The
    /// selected thread takes the core when it outranks what c runs, may run, and c has a generation
    /// of ids left; one that outranks it but may not run is taken off its queue; otherwise nothing
    /// changes.
    pub open spec fn ticked(pre: Self, post: Self, c: int, frame: Registers, ret: TickStep) -> bool {
        &&& (ret is Kept) == (forall|t: usize| #[trigger] pre.selected(c, t)
            ==> !pre.preempts(c, t) || (pre.can_run(t) && pre.cores@[c].generation == ID_GENERATION_MAX))
        &&& ret is Kept ==> post == pre
        &&& forall|t: usize| #[trigger] pre.selected(c, t) && pre.preempts(c, t) && !pre.can_run(t) ==> {
            &&& ret is Dropped
            &&& Self::record_written(pre, post, t, Self::dropped_record(pre.threads.records@[t].value()))
            &&& post.cores == pre.cores
            &&& post.stop_ipis == pre.stop_ipis
            &&& post.view() == pre.view()
        }
        &&& forall|t: usize| #[trigger] pre.selected(c, t) && pre.preempts(c, t) && pre.can_run(t)
            && pre.cores@[c].generation < ID_GENERATION_MAX ==> {
            &&& ret is Switched
            &&& Self::switched(pre, post, c, frame, t)
        }
    }

    /// The timer's tick, and the reschedule IPI, on core c: check_current first, saving a current
    /// thread that must leave with its full frame, then the selection. The thread selected takes the
    /// core from a current thread of no higher priority, which saves its full frame with the marker
    /// Full and waits behind its equals, so equal priorities take turns; ticked says each case. The
    /// tick takes nothing from user space, so it is never refused. design/cpu-time-as-capability/.
    pub fn tick(&mut self, c: usize, frame: Registers, kernel_root: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: TickStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            kernel_root == old(self).spaces.kernel_root@,
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(steps).count <= old(steps).count + TICK_STEPS,
            final(self).current_live(c as int),
            !old(self).must_leave(c as int) ==> Self::ticked(*old(self), *final(self), c as int, frame, ret),
            old(self).must_leave(c as int) ==> exists|mid: Self|
                #![trigger Self::moved_off(*old(self), mid, c as int, frame, FrameKind::Full)]
                Self::moved_off(*old(self), mid, c as int, frame, FrameKind::Full)
                && mid.wf()
                && Self::ticked(mid, *final(self), c as int, frame, ret),
    {
        let ghost pre = *self;
        let checked = self.check_current(c, frame, FrameKind::Full, Tracked(&mut *steps));
        let ghost mid = *self;
        let ret = self.preempt(c, frame, kernel_root, Tracked(steps));
        proof {
            if pre.must_leave(c as int) {
                assert(Self::moved_off(pre, mid, c as int, frame, FrameKind::Full));
            } else {
                assert(mid == pre);
            }
        }
        ret
    }

    /// The tick's step after check_current: select on core c, and act on what was selected as ticked
    /// says.
    fn preempt(&mut self, c: usize, frame: Registers, kernel_root: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: TickStep)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            kernel_root == old(self).spaces.kernel_root@,
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
            old(self).current_live(c as int),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(steps).count <= old(steps).count + SWITCH_THREAD_STEPS,
            final(self).current_live(c as int),
            Self::ticked(*old(self), *final(self), c as int, frame, ret),
    {
        let ghost pre = *self;
        let next = match self.select_thread(c) {
            Some(t) => t,
            None => {
                proof {
                    assert forall|u: usize| #[trigger] pre.selected(c as int, u) implies false by {
                        assert(pre.threads.records@.contains_key(u));
                    }
                }
                return TickStep::Kept;
            },
        };
        proof {
            assert(pre.selected(c as int, next));
            assert forall|u: usize| #[trigger] pre.selected(c as int, u) implies u == next by {
                let pu = thread_priority(pre.threads.records@[u].value());
                let pn = thread_priority(pre.threads.records@[next].value());
                assert(pu <= pn);
                assert(pn <= pu);
            }
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, next));
        }
        let state = *self.cores.get(c);
        let ptr = PPtr::<ThreadRecord>::from_usize(next + THREAD_RECORD_PAGE * PAGE_SZ);
        let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(next)));
        let next_priority = match record.placement {
            Some(pl) => pl.priority,
            None => 0,
        };
        match state.current_thread {
            Some(o) => {
                proof {
                    reveal(current_wf);
                    assert(runs(pre.cores@, c as int, o));
                    assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, o));
                }
                let running = *PPtr::<ThreadRecord>::from_usize(o + THREAD_RECORD_PAGE * PAGE_SZ).borrow(
                    Tracked(self.threads.records.borrow().tracked_borrow(o)),
                );
                let priority = match running.placement {
                    Some(pl) => pl.priority,
                    None => 0,
                };
                if next_priority < priority {
                    return TickStep::Kept;
                }
            },
            None => {},
        }
        proof {
            assert(pre.preempts(c as int, next));
        }
        let p = match record.process {
            Some(p) => p,
            None => {
                proof {
                    assert(false);
                }
                0
            },
        };
        proof {
            assert(pre.processes.records@.contains_key(p));
        }
        let dead = self.is_process_dead(p);
        if record.dying || dead {
            proof {
                assert(!pre.can_run(next));
            }
            self.drop_runnable(next);
            proof {
                let post = *self;
                assert(post.processes == pre.processes);
                match pre.cores@[c as int].current_thread {
                    Some(o) => {
                        reveal(current_wf);
                        assert(runs(pre.cores@, c as int, o));
                        assert(o != next);
                        assert(post.threads.records@.contains_key(o));
                        assert(same_record_perm_but_links(pre.threads.records@[o], post.threads.records@[o]));
                    },
                    None => {},
                }
                assert(post.current_live(c as int));
            }
            return TickStep::Dropped;
        }
        proof {
            assert(pre.can_run(next));
        }
        if state.generation == ID_GENERATION_MAX {
            return TickStep::Kept;
        }
        proof {
            reveal(CapKernel::wf);
            assert(process_spaces_wf(&pre.spaces, &pre.processes));
            assert(pre.spaces.roots@.contains_key(p));
            assert(pre.spaces.records@[p].value().kind is Process);
            pre.lemma_id_handed_out(c as int, p, 0);
            assert(pre.cores@[c as int].generation < ID_GENERATION_MAX);
            assert(*self == pre);
        }
        self.switch_thread(c, frame, FrameKind::Full, Some(next), kernel_root, Tracked(steps));
        proof {
            let post = *self;
            assert(Self::switched(pre, post, c as int, frame, next));
        }
        TickStep::Switched
    }

    /// Space s holds a valid id on core c, read from the space's list of cores.
    fn space_holds_id(&self, c: usize, s: usize) -> (ret: bool)
        requires
            self.wf(),
            c < NUM_CPUS,
            self.spaces.roots@.contains_key(s),
        ensures
            ret == holds_id(self.cores@, self.spaces.loaded@, c as int, s),
    {
        proof {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
            reveal(ids_wf);
        }
        let ptr = PPtr::<SpaceCores>::from_usize(s + SPACE_CORES_PAGE * PAGE_SZ);
        let cores = ptr.borrow(Tracked(self.spaces.loaded.borrow().tracked_borrow(s)));
        cores.ids[c] / PAGE_SZ == self.cores.get(c).generation
    }

    /// A process space's root is a page-aligned address with no overflow past the space's base.
    pub proof fn lemma_space_root_aligned(&self, s: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
        ensures
            s + SPACE_ROOT_PAGE * PAGE_SZ <= usize::MAX,
            (s + SPACE_ROOT_PAGE * PAGE_SZ) as usize % PAGE_SZ == 0,
    {
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        assert(self.blocks.tracks_addr(s));
    }

    /// Core c leaves the thread it runs, saving `frame` as that thread's and leaving it Runnable on c,
    /// and runs `next`: for Some(t), t's process's space is loaded and the register names its root
    /// under the id the space holds on c, then t is current; for None, the register names the kernel's
    /// root under KERNEL_TAG and no thread is current. The register goes from the leaving root straight
    /// to the arriving one, one write, except when the arriving space holds no valid id on c and c's
    /// ids have run out: the load then flushes every context and starts a new generation, so the core
    /// first leaves for the kernel's root, and no register names a tag across the flush. A thread with
    /// a stop pending leaves by check_current, not here. The arriving thread is live, not dying and in a
    /// process that is not dead, so a switch never makes current a thread that cap_dead calls dead:
    /// see design/teardown-driven-by-retype/.
    pub fn switch_thread(&mut self, c: usize, frame: Registers, saved: FrameKind, next: Option<usize>, kernel_root: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            kernel_root == old(self).spaces.kernel_root@,
            kernel_root % PAGE_SZ == 0,
            mem_valid(kernel_root),
            match old(self).cores@[c as int].current_thread {
                Some(o) => !old(self).threads.records@[o].value().pending_stop,
                None => true,
            },
            match next {
                Some(t) => {
                    &&& old(self).threads.records@.contains_key(t)
                    &&& old(self).threads.records@[t].value().state == (ThreadState::Runnable { core: c })
                    &&& old(self).threads.records@[t].value().process is Some
                    &&& !old(self).threads.records@[t].value().dying
                    &&& old(self).processes.records@.contains_key(old(self).threads.records@[t].value().process->Some_0)
                    &&& !old(self).processes.records@[old(self).threads.records@[t].value().process->Some_0].value().dead
                    &&& old(self).spaces.roots@.contains_key(old(self).threads.records@[t].value().process->Some_0)
                    &&& old(self).spaces.records@[old(self).threads.records@[t].value().process->Some_0].value().kind is Process
                    &&& old(self).cores@[c as int].generation < ID_GENERATION_MAX
                },
                None => true,
            },
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(steps).count <= old(steps).count + SWITCH_THREAD_STEPS,
            final(self).cores@[c as int].current_thread == next,
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).cores@[d] == old(self).cores@[d],
            forall|d: int| d != c ==> #[trigger] final(self).spaces.registers@[d] == old(self).spaces.registers@[d],
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).spaces.roots == old(self).spaces.roots,
            final(self).spaces.records == old(self).spaces.records,
            final(self).spaces.holders == old(self).spaces.holders,
            final(self).spaces.bound == old(self).spaces.bound,
            final(self).spaces.kernel_entries == old(self).spaces.kernel_entries,
            forall|d: int, r: usize| 0 <= d < NUM_CPUS && !(d == c as int && next is Some
                && r == old(self).threads.records@[next->Some_0].value().process->Some_0)
                ==> #[trigger] final(self).loaded(d, r) == old(self).loaded(d, r),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).holders == old(self).holders,
            final(self).mappings == old(self).mappings,
            final(self).table_pages == old(self).table_pages,
            final(self).zeroing == old(self).zeroing,
            final(self).frames == old(self).frames,
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            final(self).processes == old(self).processes,
            final(self).endpoints == old(self).endpoints,
            final(self).replies == old(self).replies,
            final(self).threads.records@.dom() == old(self).threads.records@.dom(),
            final(self).threads.holders == old(self).threads.holders,
            final(self).threads.boot_thread == old(self).threads.boot_thread,
            forall|x: usize| #[trigger] final(self).threads.records@.contains_key(x)
                && old(self).cores@[c as int].current_thread != Some(x) && next != Some(x)
                ==> same_record_perm_but_links(old(self).threads.records@[x], final(self).threads.records@[x]),
            // What a process sees changes only in the leaving thread's saved registers, which its own
            // user-mode execution wrote: design/theorem-over-reach/.
            match old(self).cores@[c as int].current_thread {
                Some(o) => saves_own_frame(old(self).view(), final(self).view(), o),
                None => final(self).view() == old(self).view(),
            },
            match old(self).cores@[c as int].current_thread {
                Some(o) => {
                    let prio = thread_priority(old(self).threads.records@[o].value());
                    &&& final(self).threads.records@[o].value().state == (ThreadState::Runnable { core: c })
                    &&& final(self).threads.records@[o].value().frame == saved_frame(frame, saved)
                    &&& final(self).threads.records@[o].value().saved == saved
                    &&& final(self).threads.records@[o].value().save@ == entry_frame_save(frame, saved)
                    &&& final(self).threads.records@[o].value().process == old(self).threads.records@[o].value().process
                    &&& final(self).threads.records@[o].value().placement == old(self).threads.records@[o].value().placement
                    &&& final(self).threads.records@[o].value().dying == old(self).threads.records@[o].value().dying
                    &&& at_back_of_priority(&final(self).threads.queues, final(self).threads.records@, c as int, prio, o)
                    &&& (next is None ==> queued_at_back(&old(self).threads.queues, &final(self).threads.queues, c as int, prio as int, o))
                },
                None => true,
            },
            match next {
                Some(t) => {
                    let p = old(self).threads.records@[t].value().process->Some_0;
                    let pcid = id_pcid(final(self).spaces.loaded@[p].value().ids@[c as int]);
                    let tag = tag_written(c as int, pcid);
                    &&& final(self).threads.records@[t].value().state == (ThreadState::Running { core: c })
                    &&& final(self).threads.records@[t].value().process == Some(p)
                    &&& final(self).threads.records@[t].value().placement == old(self).threads.records@[t].value().placement
                    // The thread made current is not one cap_dead calls dead: Running, not dying, and
                    // bound to a process that is not dead.
                    &&& !final(self).threads.records@[t].value().dying
                    &&& !final(self).processes.records@[p].value().dead
                    &&& final(self).current_live(c as int)
                    &&& final(self).threads.records@[t].value().frame == old(self).threads.records@[t].value().frame
                    &&& final(self).threads.records@[t].value().saved == old(self).threads.records@[t].value().saved
                    &&& final(self).threads.records@[t].value().save == old(self).threads.records@[t].value().save
                    &&& old(self).cores@[c as int].next_pcid != PCID_MAX
                        ==> final(self).cores@[c as int].next_pcid <= old(self).cores@[c as int].next_pcid + 1
                    &&& final(self).cores@[c as int].space == Some(p)
                    &&& final(self).loaded(c as int, p)
                    &&& holds_id(final(self).cores@, final(self).spaces.loaded@, c as int, p)
                    &&& final(self).spaces.registers@[c as int].root() == p + SPACE_ROOT_PAGE * PAGE_SZ
                    &&& final(self).spaces.registers@[c as int].tag() == tag
                    // Straight from the leaving root: one write, and the generation kept.
                    &&& (holds_id(old(self).cores@, old(self).spaces.loaded@, c as int, p)
                        || old(self).cores@[c as int].next_pcid != PCID_MAX) ==> {
                        &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation
                        &&& final(self).tlb@.tags(c as int) == old(self).tlb@.tags(c as int).insert(tag)
                    }
                    // The ids ran out: a new generation, flushed, whose only tag is the arriving one.
                    &&& (!holds_id(old(self).cores@, old(self).spaces.loaded@, c as int, p)
                        && old(self).cores@[c as int].next_pcid == PCID_MAX) ==> {
                        &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation + 1
                        &&& final(self).tlb@.tags(c as int) == Set::<usize>::empty().insert(tag)
                    }
                },
                None => {
                    &&& final(self).cores@[c as int].space is None
                    &&& final(self).spaces.registers@[c as int].root() == kernel_root
                    &&& final(self).spaces.registers@[c as int].tag() == tag_written(c as int, KERNEL_TAG)
                    &&& final(self).cores@[c as int].generation == old(self).cores@[c as int].generation
                    &&& final(self).cores@[c as int].next_pcid == old(self).cores@[c as int].next_pcid
                    &&& final(self).tlb@.tags(c as int) == old(self).tlb@.tags(c as int).insert(tag_written(c as int, KERNEL_TAG))
                },
            },
    {
        let ghost s0 = *self;
        let leaving = self.cores.get(c).current_thread;
        if leaving.is_some() {
            self.switch_out(c, frame, saved);
        }
        let ghost s1 = *self;
        proof {
            if let Some(o) = leaving {
                assert forall|x: ObjectId| x != o && #[trigger] saved_registers(&s1.threads).contains_key(x)
                    implies saved_registers(&s1.threads)[x] == saved_registers(&s0.threads)[x] by {
                    assert(s1.threads.records@.contains_key(x));
                    assert(same_record_perm_but_links(s0.threads.records@[x], s1.threads.records@[x]));
                }
                assert(saved_registers(&s1.threads) =~= saved_registers(&s0.threads).insert(o, saved_frame(frame, saved)));
            }
            assert(s1.cores@[c as int].current_thread is None);
            assert(s1.spaces == s0.spaces);
            assert(s1.tlb == s0.tlb);
            assert(s1.cores@[c as int].generation == s0.cores@[c as int].generation);
            assert(s1.cores@[c as int].next_pcid == s0.cores@[c as int].next_pcid);
            assert(s1.cores@[c as int].space == s0.cores@[c as int].space);
            if let Some(t) = next {
                if let Some(o) = leaving {
                    assert(t != o);
                    assert(s1.threads.records@.contains_key(t));
                    assert(same_record_perm_but_links(s0.threads.records@[t], s1.threads.records@[t]));
                } else {
                    assert(same_record_perm_but_links(s0.threads.records@[t], s1.threads.records@[t]));
                }
            }
        }
        match next {
            None => {
                self.switch_space(c, None, kernel_root, KERNEL_TAG);
                proof {
                    let s5 = *self;
                    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS implies #[trigger] s5.loaded(d, r) == s0.loaded(d, r) by {
                        assert(s1.loaded(d, r) == s0.loaded(d, r));
                    }
                    assert(s5.threads == s1.threads);
                    assert forall|x: usize| #[trigger] s5.threads.records@.contains_key(x)
                        && leaving != Some(x)
                        implies same_record_perm_but_links(s0.threads.records@[x], s5.threads.records@[x]) by {
                        if let Some(o) = leaving {
                            assert(s1.threads.records@.contains_key(x));
                            assert(same_record_perm_but_links(s0.threads.records@[x], s1.threads.records@[x]));
                        }
                    }
                }
            },
            Some(t) => {
                let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ);
                proof {
                    assert(thread_wf(&s1.list, &s1.threads, &s1.blocks, t));
                }
                let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
                let p = match record.process {
                    Some(p) => p,
                    None => { proof { assert(false); } 0 },
                };
                let held = self.space_holds_id(c, p);
                if !held && self.cores.get(c).next_pcid == PCID_MAX {
                    // The load starts a new generation: leave for the kernel's root first.
                    self.switch_space(c, None, kernel_root, KERNEL_TAG);
                }
                let ghost s2 = *self;
                proof {
                    assert(s2.spaces.roots == s1.spaces.roots);
                    assert(s2.spaces.records == s1.spaces.records);
                    assert(s2.cores@[c as int].generation == s1.cores@[c as int].generation);
                    assert(s2.cores@[c as int].next_pcid == s1.cores@[c as int].next_pcid);
                    assert(holds_id(s2.cores@, s2.spaces.loaded@, c as int, p) == held);
                }
                let pcid = self.load_space(c, p, Tracked(steps));
                let ghost s3 = *self;
                proof {
                    self.lemma_space_root_aligned(p);
                }
                self.switch_space(c, Some(p), p + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
                let ghost s4 = *self;
                proof {
                    assert(s4.threads == s1.threads);
                    // A stop is pending only on a Running thread, and t is Runnable.
                    assert(!s0.threads.records@[t].value().pending_stop) by {
                        reveal(current_wf);
                    }
                    assert(s4.cores@[c as int].current_thread is None);
                    assert(runs_in_space(s4.cores@, s4.threads.records@, c as int, t));
                }
                self.switch_in(c, t);
                proof {
                    let s5 = *self;
                    assert(s5.processes == s0.processes);
                    assert(s5.current_live(c as int));
                    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && !(d == c as int && r == p)
                        implies #[trigger] s5.loaded(d, r) == s0.loaded(d, r) by {
                        assert(s1.loaded(d, r) == s0.loaded(d, r));
                        assert(s2.loaded(d, r) == s1.loaded(d, r));
                        assert(s3.loaded(d, r) == s2.loaded(d, r));
                        assert(s4.loaded(d, r) == s3.loaded(d, r));
                    }
                    if let Some(o) = leaving {
                        assert(t != o);
                        assert(s5.threads.records@.contains_key(o));
                        assert(same_record_perm_but_links(s4.threads.records@[o], s5.threads.records@[o]));
                        let p_o = thread_priority(s0.threads.records@[o].value());
                        let p_t = thread_priority(s4.threads.records@[t].value());
                        lemma_runnable_is_bound(&s1.threads.queues, s1.threads.records@, o);
                        lemma_runnable_is_bound(&s4.threads.queues, s4.threads.records@, t);
                        lemma_tail_kept_after_other_dequeued(
                            &s1.threads.queues,
                            &s5.threads.queues,
                            c as int,
                            p_o as int,
                            p_t as int,
                            o,
                            t,
                        );
                        lemma_tail_is_behind_all(&s5.threads.queues, s5.threads.records@, c as int, p_o, o);
                    }
                    assert forall|x: usize| #[trigger] s5.threads.records@.contains_key(x)
                        && leaving != Some(x) && next != Some(x)
                        implies same_record_perm_but_links(s0.threads.records@[x], s5.threads.records@[x]) by {
                        assert(x != t);
                        assert(s4.threads.records@.contains_key(x));
                        assert(same_record_perm_but_links(s4.threads.records@[x], s5.threads.records@[x]));
                        if let Some(o) = leaving {
                            assert(x != o);
                            assert(s1.threads.records@.contains_key(x));
                            assert(same_record_perm_but_links(s0.threads.records@[x], s1.threads.records@[x]));
                        }
                    }
                    assert forall|x: ObjectId| #[trigger] saved_registers(&s5.threads).contains_key(x)
                        implies saved_registers(&s5.threads)[x] == saved_registers(&s1.threads)[x] by {
                        if x != t {
                            assert(s5.threads.records@.contains_key(x));
                            assert(same_record_perm_but_links(s4.threads.records@[x], s5.threads.records@[x]));
                        }
                    }
                    assert(saved_registers(&s5.threads) =~= saved_registers(&s1.threads));
                }
            },
        }
        proof {
            let s5 = *self;
            assert(s5.threads.holders == s1.threads.holders);
            assert(saved_registers(&s5.threads) == saved_registers(&s1.threads));
            assert(tree_of(&s5.table_pages, &s5.spaces) == tree_of(&s0.table_pages, &s0.spaces));
            // The leaving thread goes off Running and the arriving one onto it: neither waits, before or
            // after, and every other thread's record is as it was.
            assert forall|x: usize| #[trigger] waits_on(&s5.threads, x) == waits_on(&s0.threads, x) by {
                if s5.threads.records@.contains_key(x) && leaving != Some(x) && next != Some(x) {
                    assert(same_record_perm_but_links(s0.threads.records@[x], s5.threads.records@[x]));
                }
            }
            lemma_blocked_on_same(&s0.threads, &s5.threads);
            match leaving {
                Some(o) => {
                    assert(same_but_contents(s0.view(), s5.view()));
                    assert forall|x: ObjectId| #[trigger] State::changed(s0.view(), s5.view(), x) implies x == o by {
                        assert(saved_registers(&s5.threads).contains_key(x) == saved_registers(&s0.threads).contains_key(x));
                    }
                },
                None => {
                    assert(s5.view() == s0.view());
                },
            }
        }
    }
}

} // verus!
