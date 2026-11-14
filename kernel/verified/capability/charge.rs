// SPDX-License-Identifier: MIT

//! The charge at each kernel entry: core c adds the cycles its counter counted since its last entry to
//! the consumed time of the thread it runs, if any, and notes the counter's reading. The glue reads the
//! counter and passes it, so the proof reads no hardware, and only core c writes the consumed time of
//! the thread it runs: CapKernel::charges_only_own_current. Measurement only: nothing is enforced
//! against it, design/cpu-time-as-capability/.
use vstd::prelude::*;

verus! {

use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::schedule::*;
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// The consumed time of a thread that had consumed `consumed` and ran from the counter's reading
/// `since` to its reading `now`: the difference added, both wrapping, so a counter that wraps still
/// charges what it counted.
pub open spec fn charged(consumed: u64, since: u64, now: u64) -> u64 {
    vstd::wrapping::u64_specs::wrapping_add(consumed, vstd::wrapping::u64_specs::wrapping_sub(now, since))
}

impl CapKernel {
    /// From pre to post, core c noted the counter's reading now and charged the thread it runs, if any,
    /// the cycles since its last entry. Nothing else changed.
    pub open spec fn charged_entry(pre: Self, post: Self, c: int, now: u64) -> bool {
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.table_pages == pre.table_pages
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.spaces == pre.spaces
        &&& post.processes == pre.processes
        &&& post.endpoints == pre.endpoints
        &&& post.replies == pre.replies
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.iommus == pre.iommus
        &&& post.devices == pre.devices
        &&& post.tlb == pre.tlb
        &&& post.stop_ipis == pre.stop_ipis
        &&& post.flush_ipis == pre.flush_ipis
        &&& post.resched_ipis == pre.resched_ipis
        &&& post.threads.holders == pre.threads.holders
        &&& post.threads.boot_thread == pre.threads.boot_thread
        &&& post.threads.queues == pre.threads.queues
        &&& post.cores@.len() == pre.cores@.len()
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d]
        &&& post.cores@[c] == (CoreState { since: now, ..pre.cores@[c] })
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && pre.cores@[c].current_thread != Some(x)
            ==> post.threads.records@[x] == pre.threads.records@[x]
        &&& match pre.cores@[c].current_thread {
            Some(t) => {
                let r = pre.threads.records@[t].value();
                &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
                &&& post.threads.records@[t].is_init()
                &&& post.threads.records@[t].value() == (ThreadRecord { consumed: charged(r.consumed, pre.cores@[c].since, now), ..r })
            },
            None => true,
        }
    }

    /// The consumed time of thread t. Only the witness reads it yet, and no image is built with it.
    #[cfg(verus_keep_ghost)]
    pub(crate) fn thread_consumed(&self, t: usize) -> (ret: u64)
        requires
            self.wf(),
            self.threads.records@.contains_key(t),
        ensures
            ret == self.threads.records@[t].value().consumed,
    {
        proof {
            reveal(CapKernel::wf);
            assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
        }
        let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ);
        ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t))).consumed
    }

    /// Core c's charge at a kernel entry, under the lock and before the entry's operation: the thread
    /// c runs, if any, is charged the cycles from c's last entry, its counter then reading since, to
    /// now, and c notes now. The glue passes the counter's reading. Only core c's state and the
    /// consumed time of the thread it runs change, and no process sees either.
    pub fn charge(&mut self, c: usize, now: u64)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            Self::charged_entry(*old(self), *final(self), c as int, now),
            final(self).view() == old(self).view(),
    {
        let ghost pre = *self;
        let state = *self.cores.get(c);
        self.cores.set(c, CoreState {
            current_thread: state.current_thread,
            acked_epoch: state.acked_epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            space: state.space,
            since: now,
        });
        let ghost mid = *self;
        proof {
            Self::lemma_since_written(pre, mid, c as int);
        }
        match state.current_thread {
            None => {},
            Some(t) => {
                proof {
                    reveal(CapKernel::wf);
                    reveal(current_wf);
                    assert(runs(mid.cores@, c as int, t));
                    assert(mid.threads.records@.contains_key(t));
                    assert(thread_wf(&mid.list, &mid.threads, &mid.blocks, t));
                    reveal(placed_running_wf);
                    assert(thread_placed_running(mid.threads.records@[t].value()));
                }
                let ptr = PPtr::<ThreadRecord>::from_usize(t + THREAD_RECORD_PAGE * PAGE_SZ);
                let record = *ptr.borrow(Tracked(self.threads.records.borrow().tracked_borrow(t)));
                let tracked mut perm;
                proof {
                    perm = self.threads.records.borrow_mut().tracked_remove(t);
                }
                ptr.write(Tracked(&mut perm), ThreadRecord {
                    consumed: record.consumed.wrapping_add(now.wrapping_sub(state.since)),
                    ..record
                });
                proof {
                    self.threads.records.borrow_mut().tracked_insert(t, perm);
                    let post = *self;
                    assert(post.threads.records@.dom() =~= mid.threads.records@.dom());
                    assert(mid.threads.records@[t].value().state == (ThreadState::Running { core: c }));
                    lemma_queues_unrunnable_written(&mid.threads.queues, mid.threads.records@, post.threads.records@, t);
                    assert forall|x: usize| x != t && #[trigger] post.threads.records@.contains_key(x)
                        implies same_record_perm_but_links(mid.threads.records@[x], post.threads.records@[x]) by {
                        assert(post.threads.records@[x] == mid.threads.records@[x]);
                    }
                    assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) implies {
                        &&& post.threads.records@[x].value().state == mid.threads.records@[x].value().state
                        &&& post.threads.records@[x].value().pending_stop == mid.threads.records@[x].value().pending_stop
                        &&& post.threads.records@[x].value().process == mid.threads.records@[x].value().process
                    } by {
                        if x != t {
                            assert(post.threads.records@[x] == mid.threads.records@[x]);
                        }
                    }
                    lemma_current_same(mid.cores@, post.cores@, mid.threads.records@, post.threads.records@);
                    Self::lemma_switch_wf(mid, post, c as int, t);
                    assert(saved_registers(&post.threads) =~= saved_registers(&mid.threads));
                    assert forall|o: usize| #[trigger] waits_on(&post.threads, o) == waits_on(&mid.threads, o) by {
                        if o != t && post.threads.records@.contains_key(o) {
                            assert(post.threads.records@[o] == mid.threads.records@[o]);
                        }
                    }
                    lemma_blocked_on_same(&mid.threads, &post.threads);
                    assert(post.view() =~= mid.view());
                }
            },
        }
        proof {
            let post = *self;
            assert(Self::charged_entry(pre, post, c as int, now));
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c implies
                #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread by {
                assert(post.cores@[d] == pre.cores@[d]);
            }
        }
    }

    /// Core c's state changed in since only: still well formed, and no process sees it.
    proof fn lemma_since_written(pre: Self, post: Self, c: int)
        requires
            pre.wf(),
            0 <= c < NUM_CPUS,
            post == (Self { cores: post.cores, ..pre }),
            post.cores.wf(),
            post.cores@.len() == pre.cores@.len(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d],
            post.cores@[c] == (CoreState { since: post.cores@[c].since, ..pre.cores@[c] }),
        ensures
            post.wf(),
            post.view() == pre.view(),
    {
        assert forall|d: int| 0 <= d < NUM_CPUS implies {
            &&& #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread
            &&& post.cores@[d].space == pre.cores@[d].space
            &&& post.cores@[d].acked_epoch == pre.cores@[d].acked_epoch
            &&& post.cores@[d].generation == pre.cores@[d].generation
            &&& post.cores@[d].next_pcid == pre.cores@[d].next_pcid
        } by {
            if d != c {
                assert(post.cores@[d] == pre.cores@[d]);
            }
        }
        lemma_current_same(pre.cores@, post.cores@, pre.threads.records@, post.threads.records@);
        Self::lemma_registers_core(pre, post, c);
        Self::lemma_iommus_same(pre, post);
        reveal(ids_wf);
        lemma_ids_core_step(pre.cores@, post.cores@, post.spaces.loaded@, c);
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) == pre.acked(d) by {}
        assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] post.acked(d) <= post.flush_epoch by {
            assert(pre.acked(d) <= pre.flush_epoch);
        }
        assert forall|d: int, p: usize| 0 <= d < NUM_CPUS && #[trigger] post.tlb@.tags(d).contains(p)
            implies p < post.cores@[d].next_pcid by {
            assert(pre.tlb@.tags(d).contains(p));
        }
        assert forall|d: int, e: TlbEntry| 0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e)
            implies post.depends(d, e.space) by {
            assert(pre.tlb@[d].contains(e));
            assert(pre.depends(d, e.space));
        }
        assert forall|d: int, e: TlbEntry|
            0 <= d < NUM_CPUS && #[trigger] post.tlb@[d].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(d), e.page) by {
            assert(pre.tlb@[d].contains(e));
        }
        reveal(CapKernel::wf);
        assert(post.view() =~= pre.view());
    }
}

} // verus!
