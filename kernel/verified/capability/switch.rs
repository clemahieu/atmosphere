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
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::mapping::*;
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

impl CapKernel {
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
