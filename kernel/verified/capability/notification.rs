// SPDX-License-Identifier: MIT

//! Signal and wait on a notification, through a capability the caller holds. Signal ORs the
//! capability's badge into the notification's word and returns ok or refused, never blocking; when
//! the notification's queue has a live waiter at its head, signal removes it, writes the word (bit
//! 63 clear) into its saved frame as its wait's result, clears the word (keeping bit 63 set only
//! while another thread remains listed), and makes the head Runnable on its placement's core with
//! the reschedule IPI rule. Wait returns the word's signalled bits and clears them when any is set,
//! and blocks core c's current thread on the notification's queue with its partial frame saved when
//! none is set. The word's bit 63 is the kernel's waiter bit, which signal does not set and wait
//! preserves when returning or sets while a thread queues. See
//! design/notification-word-reserves-the-waiter-bit/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma_pow2_pos, pow2};
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arch::{
    lemma_partial_frame_idempotent, lemma_partial_outcome_written, outcome_written, partial_frame,
    FrameKind,
};
use crate::arch::Registers;
use crate::capability::endpoint::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::operation::{Outcome, STATUS_OK};
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::schedule::{
    at_back_of_priority, queued_at_back, queues_wf, thread_priority,
};
use crate::capability::table::*;
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;
use crate::pptr::*;

/// The bits of a notification's word a badge may set: every bit but the waiter bit.
pub const SIGNAL_BITS: u64 = 0x7fff_ffff_ffff_ffff; // not a page size: bits 0 to 62 of the word

/// The rights bits signal and wait each ask of the capability: send and receive.
pub const SEND_RIGHT: u32 = 16;
pub const RECEIVE_RIGHT: u32 = 32;

/// What a `wait` did: refused without changing the kernel, returned signalled bits at once, or
/// blocked core `c`'s current thread on the notification's queue.
pub enum WaitStep {
    Refused,
    Returned(u64),
    Blocked,
}

/// The outcome a `wait` returns when it delivers `word` (bit 63 clear): `STATUS_OK` in the
/// status word and `word` in result 1.
pub open spec fn wait_outcome(word: u64) -> Outcome {
    Outcome {
        status: STATUS_OK,
        result_1: word,
        result_2: 0,
        result_3: 0,
        result_4: 0,
        result_5: 0,
    }
}

/// The outcome a `wait` returns when it delivers `word`.
pub fn wait_outcome_of(word: u64) -> (ret: Outcome)
    ensures
        ret == wait_outcome(word),
{
    Outcome {
        status: STATUS_OK,
        result_1: word,
        result_2: 0,
        result_3: 0,
        result_4: 0,
        result_5: 0,
    }
}

impl CapKernel {
    /// Index i of the table at root holds a notification capability whose rights include `right`.
    pub open spec fn holds_notification(&self, root: usize, i: usize, right: u32) -> bool {
        let n = self.tables.node_of(root, i);
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.is_cap(n)
        &&& self.payload_of(n).kind is Notification
        &&& self.payload_of(n).rights & right != 0
    }

    /// The notification the capability at index i of the table at root names.
    pub open spec fn notification_at(&self, root: usize, i: usize) -> usize {
        self.payload_of(self.tables.node_of(root, i)).base
    }

    /// That notification's record.
    pub open spec fn notification_record(&self, root: usize, i: usize) -> QueueRecord {
        self.endpoints.records@[self.notification_at(root, i)].value()
    }

    /// Signal through index i of the table at root succeeds: it holds a notification capability with
    /// the send right.
    pub open spec fn can_signal(&self, root: usize, i: usize) -> bool {
        self.holds_notification(root, i, SEND_RIGHT)
    }

    /// Notification `e` has a live waiter at the head of its queue: its queue lists at least one
    /// thread and its head is `Blocked` on `e`.
    pub open spec fn signal_has_live_waiter(&self, e: usize) -> bool {
        let r = self.endpoints.records@[e].value();
        &&& r.waiters@.len() > 0
        &&& self.threads.records@[r.head].value().state == (ThreadState::Blocked { object: e })
    }

    /// Core `c` has a live current thread that belongs to the process rooted at `root`.
    pub open spec fn caller_live(&self, c: int, root: usize) -> bool {
        &&& 0 <= c < NUM_CPUS
        &&& self.current_live(c)
        &&& self.cores@[c].current_thread is Some
        &&& self.threads.records@[self.cores@[c].current_thread->Some_0].value().process == Some(root)
    }

    /// Wait from core `c` through index `i` of the table at `root` proceeds: the table holds a
    /// notification capability with the receive right. Either a signalled bit is already set
    /// (`Returned`) or none is (`Blocked`).
    pub open spec fn can_wait(&self, _c: int, root: usize, i: usize) -> bool {
        self.holds_notification(root, i, RECEIVE_RIGHT)
    }

    /// Wait through index `i` of the table at `root` returns at once: it holds a notification
    /// capability with the receive right, and the notification's word has a signalled bit.
    pub open spec fn wait_signalled(&self, root: usize, i: usize) -> bool {
        &&& self.holds_notification(root, i, RECEIVE_RIGHT)
        &&& self.notification_record(root, i).word & SIGNAL_BITS != 0
    }

    /// post is pre with the word of the notification at e set to `word`, and nothing else changed.
    pub open spec fn word_written(pre: Self, post: Self, e: usize, word: u64) -> bool {
        let r = pre.endpoints.records@[e].value();
        &&& post == CapKernel { endpoints: post.endpoints, ..pre }
        &&& post.endpoints.holders == pre.endpoints.holders
        &&& post.endpoints.records@ == pre.endpoints.records@.insert(e, post.endpoints.records@[e])
        &&& post.endpoints.records@[e].addr() == e
        &&& post.endpoints.records@[e].is_init()
        &&& post.endpoints.records@[e].value() == QueueRecord { word, ..r }
    }

    /// What a signal through index `i` of the table at `root` did when notification `e` had a live
    /// waiter `head` at the head of its queue: ORed the capability's badge into the word, wrote the
    /// word with bit 63 clear into `head`'s saved frame as its wait's result, removed `head` from
    /// the queue, cleared the word (keeping `WAITER_BIT` set only while another thread remains
    /// listed), made `head` `Runnable` on its placement's core at the back of its placement's
    /// priority with the reschedule IPI rule of design/cpu-time-as-capability/, and discharged
    /// `Effect::Signal { cap: n, waiter: Some(head) }`.
    pub open spec fn signal_woke(pre: Self, post: Self, root: usize, i: usize) -> bool {
        let n = pre.tables.node_of(root, i);
        let e = pre.notification_at(root, i);
        let pre_e = pre.endpoints.records@[e].value();
        let post_e = post.endpoints.records@[e].value();
        let badge = pre.payload_of(n).badge as u64;
        let head = pre_e.head;
        let hr = pre.threads.records@[head].value();
        let pl = hr.placement->Some_0;
        let core = pl.core;
        let delivered = (pre_e.word | badge) & SIGNAL_BITS;
        let new_frame = outcome_written(hr.frame, wait_outcome(delivered));
        let new_word = if pre_e.waiters@.len() > 1 { WAITER_BIT } else { 0 };
        &&& pre_e.waiters@.len() > 0
        &&& pre.threads.records@.contains_key(head)
        &&& hr.placement is Some
        &&& post == (CapKernel {
            endpoints: post.endpoints,
            threads: post.threads,
            resched_ipis: post.resched_ipis,
            ..pre
        })
        &&& Self::consumed_kept(pre, post)
        &&& post.threads.holders == pre.threads.holders
        &&& post.threads.boot_thread == pre.threads.boot_thread
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& post.threads.records@[head].addr() == pre.threads.records@[head].addr()
        &&& post.threads.records@[head].is_init()
        &&& same_thread_but_links(post.threads.records@[head].value(), ThreadRecord {
            state: ThreadState::Runnable { core },
            frame: new_frame,
            saved: hr.saved,
            save: Ghost(entry_frame_save(new_frame, hr.saved)),
            queued: NONE,
            wait_prev: NONE,
            wait_next: NONE,
            ..hr
        })
        &&& queued_at_back(&pre.threads.queues, &post.threads.queues, core as int, pl.priority as int, head)
        &&& at_back_of_priority(&post.threads.queues, post.threads.records@, core as int, pl.priority, head)
        &&& forall|u: usize| u != head && #[trigger] post.threads.records@.contains_key(u) ==> ({
            let ur = pre.threads.records@[u].value();
            let vr = post.threads.records@[u].value();
            &&& post.threads.records@[u].addr() == pre.threads.records@[u].addr()
            &&& post.threads.records@[u].is_init()
            &&& same_thread_but_links(vr, ThreadRecord {
                wait_prev: if pre_e.waiters@.len() > 1 && u == pre_e.waiters@[1] {
                    NONE
                } else {
                    ur.wait_prev
                },
                ..ur
            })
        })
        &&& post.endpoints.holders == pre.endpoints.holders
        &&& post.endpoints.records@.dom() == pre.endpoints.records@.dom()
        &&& forall|x: usize| x != e && #[trigger] post.endpoints.records@.contains_key(x)
            ==> post.endpoints.records@[x] == pre.endpoints.records@[x]
        &&& post.endpoints.records@[e].addr() == pre.endpoints.records@[e].addr()
        &&& post.endpoints.records@[e].is_init()
        &&& post_e == (QueueRecord {
            head: if pre_e.waiters@.len() > 1 { pre_e.waiters@[1] } else { NONE },
            tail: if pre_e.waiters@.len() > 1 { pre_e.tail } else { NONE },
            waiters: Ghost(pre_e.waiters@.skip(1)),
            word: new_word,
            ..pre_e
        })
        &&& !post_e.waiters@.contains(head)
        &&& post.resched_ipis@ == if pre.outranks_current(core as int, pl.priority) {
            pre.resched_ipis@.push(core)
        } else {
            pre.resched_ipis@
        }
        &&& discharges(pre.view(), post.view(), root, Effect::Signal { cap: n, waiter: Some(head) })
    }

    /// What a signal through index i of the table at root did: when the notification's queue has a
    /// live waiter at its head, woke that waiter with the word (including the badge) in its saved
    /// frame and cleared the word; otherwise (no waiter or stale head), ORed the capability's badge
    /// into the notification's word, waking none and discharging `Effect::Signal { cap: n, waiter: None }`.
    pub open spec fn signalled(pre: Self, post: Self, root: usize, i: usize) -> bool {
        let n = pre.tables.node_of(root, i);
        let e = pre.notification_at(root, i);
        if pre.signal_has_live_waiter(e) {
            Self::signal_woke(pre, post, root, i)
        } else {
            &&& Self::word_written(pre, post, e, pre.notification_record(root, i).word | pre.payload_of(n).badge as u64)
            &&& discharges(pre.view(), post.view(), root, Effect::Signal { cap: n, waiter: None })
        }
    }

    /// What a wait through index i of the table at root that returned `word` did: the word is the
    /// notification's signalled bits, which it cleared, keeping the waiter bit, and nothing a process
    /// sees changed.
    pub open spec fn waited(pre: Self, post: Self, root: usize, i: usize, word: u64) -> bool {
        let e = pre.notification_at(root, i);
        let w = pre.notification_record(root, i).word;
        &&& word == w & SIGNAL_BITS
        &&& Self::word_written(pre, post, e, w & !SIGNAL_BITS)
        &&& discharges(pre.view(), post.view(), root, Effect::Local)
    }

    /// What a wait from core `c` through index `i` of the table at `root` that blocked did:
    /// saved the caller's partial frame, set its state to `Blocked { object: e }`, appended it at
    /// the tail of `e`'s queue with `WAITER_BIT` set on `e`'s word (after unlinking any stale queue
    /// entry of the caller), set core `c`'s current thread to `None`, kept everything else, and
    /// discharged `Effect::Wait { cap: n, caller: t }`.
    pub open spec fn wait_blocked(
        pre: Self,
        post: Self,
        c: int,
        root: usize,
        i: usize,
        frame: Registers,
    ) -> bool {
        let n = pre.tables.node_of(root, i);
        let e = pre.notification_at(root, i);
        let t = pre.cores@[c].current_thread->Some_0;
        let r = pre.threads.records@[t].value();
        let pre_e = pre.endpoints.records@[e].value();
        let post_e = post.endpoints.records@[e].value();
        &&& post == (CapKernel {
            endpoints: post.endpoints,
            threads: post.threads,
            cores: post.cores,
            ..pre
        })
        &&& post.cores@.len() == pre.cores@.len()
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d]
        &&& post.cores@[c] == (CoreState { current_thread: None, ..pre.cores@[c] })
        &&& Self::writes_only_own_current(pre, post, c)
        &&& Self::consumed_kept(pre, post)
        &&& post.threads == (Threads { records: post.threads.records, ..pre.threads })
        &&& post.threads.records@.dom() == pre.threads.records@.dom()
        &&& post.threads.records@[t].addr() == pre.threads.records@[t].addr()
        &&& post.threads.records@[t].is_init()
        &&& post.threads.records@[t].value() == (ThreadRecord {
            state: ThreadState::Blocked { object: e },
            frame: partial_frame(frame),
            saved: FrameKind::Partial,
            save: Ghost(entry_frame_save(frame, FrameKind::Partial)),
            queued: e,
            wait_next: NONE,
            wait_prev: post.threads.records@[t].value().wait_prev,
            ..r
        })
        &&& forall|u: usize| u != t && #[trigger] post.threads.records@.contains_key(u) ==> ({
            let ur = pre.threads.records@[u].value();
            let vr = post.threads.records@[u].value();
            &&& post.threads.records@[u].addr() == pre.threads.records@[u].addr()
            &&& post.threads.records@[u].is_init()
            &&& vr == (ThreadRecord {
                wait_prev: vr.wait_prev,
                wait_next: vr.wait_next,
                ..ur
            })
        })
        &&& post.endpoints.holders == pre.endpoints.holders
        &&& post.endpoints.records@.dom() == pre.endpoints.records@.dom()
        &&& post.endpoints.records@[e].addr() == pre.endpoints.records@[e].addr()
        &&& post.endpoints.records@[e].is_init()
        &&& post_e.dead == pre_e.dead
        &&& post_e.receiving == pre_e.receiving
        &&& post_e.head != NONE
        &&& post_e.tail == t
        &&& post_e.waiters@.len() > 0
        &&& post_e.waiters@.last() == t
        &&& post_e.word == pre_e.word | WAITER_BIT
        &&& r.queued != e ==> {
            &&& post_e.head == if pre_e.head == NONE { t } else { pre_e.head }
            &&& post_e.waiters@ == pre_e.waiters@.push(t)
        }
        &&& forall|x: usize| x != e && #[trigger] post.endpoints.records@.contains_key(x) ==> ({
            let px = pre.endpoints.records@[x].value();
            let qx = post.endpoints.records@[x].value();
            &&& post.endpoints.records@[x].addr() == pre.endpoints.records@[x].addr()
            &&& post.endpoints.records@[x].is_init()
            &&& qx.dead == px.dead
            &&& qx.receiving == px.receiving
            &&& qx.word & SIGNAL_BITS == px.word & SIGNAL_BITS
            &&& x != r.queued ==> post.endpoints.records@[x] == pre.endpoints.records@[x]
        })
        &&& discharges(pre.view(), post.view(), root, Effect::Wait { cap: n, caller: t })
    }

    /// The notification capability at index i of the table at root with `right`, the node holding it
    /// and its payload, or None when the index holds none.
    fn notification_cap(&self, root: usize, i: usize, right: u32) -> (ret: Option<(usize, Payload)>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret is Some == self.holds_notification(root, i, right),
            ret is Some ==> {
                &&& (ret->0).0 == self.tables.node_of(root, i)
                &&& (ret->0).1 == self.payload_of((ret->0).0)
            },
    {
        let (n, payload) = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(n);
        let live_cap = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !live_cap {
            return None;
        }
        proof {
            self.lemma_slot(root, i);
            assert(self.tables.is_cap(&self.list, n));
            assert(payload == self.payload_of(n));
        }
        match payload.kind {
            CapKind::Notification => {},
            _ => { return None; },
        }
        if payload.rights & right == 0 {
            return None;
        }
        Some((n, payload))
    }

    /// The notification at e, which a notification capability names: its record is there and well
    /// formed, its queue lists a thread exactly when it has a head.
    proof fn lemma_notification_record(&self, root: usize, i: usize, right: u32)
        requires
            self.wf(),
            self.holds_notification(root, i, right),
        ensures
            self.endpoints.records@.contains_key(self.notification_at(root, i)),
            endpoint_wf(&self.endpoints, &self.blocks, self.notification_at(root, i)),
            self.blocks.pages@[(self.notification_at(root, i) / PAGE_SZ) as int].object is Notification,
            (self.notification_record(root, i).head == NONE) == (self.notification_record(root, i).waiters@.len() == 0),
            self.payload_of(self.tables.node_of(root, i)).badge < NOTIFICATION_BADGE_LIMIT,
    {
        let n = self.tables.node_of(root, i);
        let e = self.notification_at(root, i);
        assert(queue_kind(self.payload_of(n).kind));
        assert(endpoint_wf(&self.endpoints, &self.blocks, e));
        assert(cap_wf(self.payload_of(n)));
        assert forall|t: usize| #[trigger] self.threads.records@.contains_key(t) implies t != NONE by {
            assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
        }
        lemma_waits_head(self.endpoints.records@, self.threads.records@, e);
    }

    /// Sets the word of the notification at e, whose record is there, to `word`, which keeps the
    /// waiter bit as it was. Nothing a process sees changes, so the step discharges any effect the
    /// caller is authorized for.
    fn write_word(&mut self, e: usize, word: u64)
        requires
            old(self).wf(),
            old(self).endpoints.records@.contains_key(e),
            old(self).blocks.pages@[(e / PAGE_SZ) as int].object is Notification,
            word & WAITER_BIT == old(self).endpoints.records@[e].value().word & WAITER_BIT,
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            Self::word_written(*old(self), *final(self), e, word),
            final(self).view() == old(self).view(),
    {
        let ghost pre = *self;
        let r = *PPtr::<QueueRecord>::from_usize(e).borrow(Tracked(self.endpoints.records.borrow().tracked_borrow(e)));
        proof {
            assert(endpoint_wf(&pre.endpoints, &pre.blocks, e));
        }
        let tracked mut perm;
        proof {
            perm = self.endpoints.records.borrow_mut().tracked_remove(e);
        }
        PPtr::<QueueRecord>::from_usize(e).write(
            Tracked(&mut perm),
            QueueRecord { dead: r.dead, head: r.head, tail: r.tail, waiters: r.waiters, receiving: r.receiving, word },
        );
        proof {
            self.endpoints.records.borrow_mut().tracked_insert(e, perm);
        }
        proof {
            let post = *self;
            assert(post.endpoints.records@ =~= pre.endpoints.records@.insert(e, post.endpoints.records@[e]));
            assert(post.endpoints.records@.dom() =~= pre.endpoints.records@.dom());
            assert forall|x: usize| #[trigger] post.endpoints.records@.contains_key(x)
                implies endpoint_wf(&post.endpoints, &post.blocks, x) by {
                assert(endpoint_wf(&pre.endpoints, &pre.blocks, x));
                if x == e {
                    let a = pre.endpoints.records@[e].value();
                    let b = post.endpoints.records@[e].value();
                    assert(word_wf(a, pre.blocks.pages@[(e / PAGE_SZ) as int].object));
                    assert(b.waiters@ == a.waiters@);
                    assert(word & WAITER_BIT == a.word & WAITER_BIT);
                    assert(word_wf(b, post.blocks.pages@[(e / PAGE_SZ) as int].object));
                }
            }
            assert(endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks));
            assert forall|x: usize| #[trigger] pre.endpoints.records@.contains_key(x)
                implies post.endpoints.records@.contains_key(x)
                    && same_queue(pre.endpoints.records@[x].value(), post.endpoints.records@[x].value()) by {}
            assert forall|t: usize| #[trigger] post.threads.records@.contains_key(t) && pre.threads.records@.contains_key(t)
                implies keeps_wait(pre.threads.records@[t].value(), post.threads.records@[t].value()) by {}
            lemma_waits_framed(pre.endpoints.records@, post.endpoints.records@, pre.threads.records@, post.threads.records@);
            assert(post == CapKernel { endpoints: post.endpoints, ..pre });
            Self::lemma_tlb_same(pre, post);
            assert(post.wf());
        }
    }

    /// Signals the notification the capability at index i of the table at root names: ORs the
    /// capability's badge into its word, and when the queue's head is a live waiter, writes the word
    /// (bit 63 clear) into its saved frame as its wait's result, unlinks it, clears the word
    /// (keeping bit 63 set only while another thread remains listed), and makes it Runnable on its
    /// placement's core with the reschedule IPI rule. Never blocks; returns only whether it signalled.
    /// design/notification-word-reserves-the-waiter-bit/.
    #[verifier::spinoff_prover]
    pub fn signal(&mut self, root: usize, i: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            ret == old(self).can_signal(root, i),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::signalled(*old(self), *final(self), root, i),
    {
        let ghost pre = *self;
        let (n, payload) = match self.notification_cap(root, i, SEND_RIGHT) {
            Some(found) => found,
            None => { return false; },
        };
        let e = payload.base;
        proof {
            pre.lemma_notification_record(root, i, SEND_RIGHT);
        }
        let r = *PPtr::<QueueRecord>::from_usize(e).borrow(Tracked(self.endpoints.records.borrow().tracked_borrow(e)));
        let badge = payload.badge as u64;
        let w = r.word;
        let head = r.head;
        let live_head = if head != NONE {
            proof {
                assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies u != NONE by {
                    assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, u));
                }
                lemma_waits_head(pre.endpoints.records@, pre.threads.records@, e);
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, head));
            }
            let hr = *PPtr::<ThreadRecord>::from_usize(head + THREAD_RECORD_PAGE * PAGE_SZ).borrow(
                Tracked(self.threads.records.borrow().tracked_borrow(head)),
            );
            match hr.state {
                ThreadState::Blocked { object } => if object == e { Some(hr) } else { None },
                _ => None,
            }
        } else {
            None
        };
        if let Some(hr) = live_head {
            self.signal_wake_head(root, i, n, e, badge, w, head, hr);
            return true;
        }
        proof {
            assert(badge < 0x8000_0000_0000_0000u64); // not a page size: NOTIFICATION_BADGE_LIMIT
            assert(word_wf(r, pre.blocks.pages@[(e / PAGE_SZ) as int].object));
            if r.head != NONE {
                assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies u != NONE by {
                    assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, u));
                }
                lemma_waits_head(pre.endpoints.records@, pre.threads.records@, e);
            }
            assert((w | badge) & WAITER_BIT == w & WAITER_BIT) by (bit_vector)
                requires
                    badge < 0x8000_0000_0000_0000u64, // not a page size: NOTIFICATION_BADGE_LIMIT
                    WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
        }
        self.write_word(e, w | badge);
        proof {
            let post = *self;
            pre.lemma_slot(root, i);
            assert(SEND_RIGHT == right_bit(Right::Send));
            assert(pre.view().holds_right(root, n, Right::Send));
            assert(discharges(pre.view(), post.view(), root, Effect::Signal { cap: n, waiter: None }));
        }
        true
    }

    /// Wakes the live waiter `hr` at the head of notification `e`: delivers `(w | badge) & SIGNAL_BITS`
    /// into `hr.frame`, unlinks `head` from `e`'s queue, updates `e`'s word, and enqueues `head`
    /// on its placement's core with a reschedule IPI if it outranks the current thread.
    #[verifier::spinoff_prover]
    fn signal_wake_head(
        &mut self,
        root: usize,
        i: usize,
        n: usize,
        e: usize,
        badge: u64,
        w: u64,
        head: usize,
        hr: ThreadRecord,
    )
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
            old(self).holds_notification(root, i, SEND_RIGHT),
            n == old(self).tables.node_of(root, i),
            e == old(self).notification_at(root, i),
            badge == old(self).payload_of(n).badge as u64,
            w == old(self).endpoints.records@[e].value().word,
            head == old(self).endpoints.records@[e].value().head,
            old(self).signal_has_live_waiter(e),
            old(self).threads.records@.contains_key(head),
            hr == old(self).threads.records@[head].value(),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            Self::signal_woke(*old(self), *final(self), root, i),
    {
        let ghost pre = *self;
        proof {
            assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies u != NONE by {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, u));
            }
            lemma_waits_head(pre.endpoints.records@, pre.threads.records@, e);
            reveal(placed_running_wf);
            reveal(placements_wf);
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, head));
            assert(thread_placed_running(hr));
        }
        let (core, prio) = match hr.placement {
            Some(pl) => (pl.core, pl.priority),
            None => {
                proof {
                    assert(false);
                }
                (0, 0)
            },
        };
        let outranks = match self.cores.get(core).current_thread {
            None => true,
            Some(o) => {
                proof {
                    reveal(current_wf);
                    assert(runs(pre.cores@, core as int, o));
                    assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, o));
                }
                let running = *PPtr::<ThreadRecord>::from_usize(o + THREAD_RECORD_PAGE * PAGE_SZ).borrow(
                    Tracked(self.threads.records.borrow().tracked_borrow(o)),
                );
                let current_priority = match running.placement {
                    Some(pl) => pl.priority,
                    None => 0,
                };
                current_priority < prio
            },
        };
        let delivered = (w | badge) & SIGNAL_BITS;
        let out = wait_outcome_of(delivered);
        let mut new_frame = hr.frame;
        new_frame.write_outcome(out);
        let new_head_record = ThreadRecord {
            state: ThreadState::Runnable { core },
            frame: new_frame,
            saved: hr.saved,
            save: Ghost(entry_frame_save(new_frame, hr.saved)),
            queued: NONE,
            wait_prev: NONE,
            wait_next: NONE,
            ..hr
        };
        proof {
            assert(frame_save_wf(hr));
            reveal(frame_save_matches);
            if let FrameKind::Partial = hr.saved {
                lemma_partial_frame_idempotent(hr.save@->Syscall_frame);
                lemma_partial_outcome_written(hr.frame, out);
            }
            assert(frame_save_wf(new_head_record));
        }
        let next = hr.wait_next;
        self.enqueue_and_write(core, prio, head, new_head_record);
        let ghost mid1 = *self;
        if next != NONE {
            proof {
                assert(thread_wf(&mid1.list, &mid1.threads, &mid1.blocks, next));
            }
            let ptr_next = PPtr::<ThreadRecord>::from_usize(next + THREAD_RECORD_PAGE * PAGE_SZ);
            let tracked mut perm_next = self.threads.records.borrow_mut().tracked_remove(next);
            let mut r_next = ptr_next.take(Tracked(&mut perm_next));
            r_next.wait_prev = NONE;
            ptr_next.put(Tracked(&mut perm_next), r_next);
            proof {
                self.threads.records.borrow_mut().tracked_insert(next, perm_next);
            }
        }
        let ptr_e = PPtr::<QueueRecord>::from_usize(e);
        let tracked mut perm_e = self.endpoints.records.borrow_mut().tracked_remove(e);
        let r0 = ptr_e.take(Tracked(&mut perm_e));
        let new_tail = if next == NONE { NONE } else { r0.tail };
        let new_word = if next == NONE { 0 } else { WAITER_BIT };
        let ghost new_waiters = r0.waiters@.skip(1);
        ptr_e.put(Tracked(&mut perm_e), QueueRecord {
            head: next,
            tail: new_tail,
            waiters: Ghost(new_waiters),
            word: new_word,
            ..r0
        });
        proof {
            self.endpoints.records.borrow_mut().tracked_insert(e, perm_e);
        }
        self.resched_ipis = Ghost(if outranks { pre.resched_ipis@.push(core) } else { pre.resched_ipis@ });
        proof {
            let post = *self;
            let r_pre = pre.endpoints.records@[e].value();
            assert(r0 == r_pre);
            assert(r_pre.waiters@.len() > 0);
            assert((next == NONE) == (r_pre.waiters@.len() == 1));
            assert(new_word == if r_pre.waiters@.len() > 1 { WAITER_BIT } else { 0u64 });
            assert(post.threads.records@.dom() =~= mid1.threads.records@.dom());
            assert(post.endpoints.records@.dom() =~= pre.endpoints.records@.dom());
            assert(thread_wf(&mid1.list, &mid1.threads, &mid1.blocks, head));
            assert(endpoint_wf(&pre.endpoints, &pre.blocks, e));
            if next != NONE {
                assert(thread_wf(&mid1.list, &mid1.threads, &mid1.blocks, next));
            }
            if let Some(o) = pre.cores@[core as int].current_thread {
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, o));
            }
            assert(outranks == pre.outranks_current(core as int, prio));
            Self::lemma_signal_woke(pre, mid1, post, root, i);
        }
    }

    /// Proves well-formedness, `signal_woke`, and reach discharge after `signal` wakes `e`'s head.
    #[verifier::spinoff_prover]
    proof fn lemma_signal_woke(pre: Self, mid1: Self, post: Self, root: usize, i: usize)
        requires
            post.blocks.pages@.len() == pre.blocks.pages@.len(),
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.holds_notification(root, i, SEND_RIGHT),
            ({
                let e = pre.notification_at(root, i);
                let r0 = pre.endpoints.records@[e].value();
                let head = r0.head;
                let hr = pre.threads.records@[head].value();
                let pl = hr.placement->Some_0;
                let core = pl.core;
                let prio = pl.priority;
                let next = hr.wait_next;
                let badge = pre.payload_of(pre.tables.node_of(root, i)).badge as u64;
                let delivered = (r0.word | badge) & SIGNAL_BITS;
                let new_frame = outcome_written(hr.frame, wait_outcome(delivered));
                let new_word = if r0.waiters@.len() > 1 { WAITER_BIT } else { 0 };
                &&& pre.signal_has_live_waiter(e)
                &&& pre.threads.records@.contains_key(head)
                &&& hr.placement is Some
                &&& queues_wf(&mid1.threads.queues, mid1.threads.records@)
                &&& threads_wf(&mid1.list, &mid1.tables, &mid1.threads, &mid1.blocks)
                &&& queued_at_back(&pre.threads.queues, &mid1.threads.queues, core as int, prio as int, head)
                &&& at_back_of_priority(&mid1.threads.queues, mid1.threads.records@, core as int, prio, head)
                &&& mid1 == (CapKernel { threads: mid1.threads, resched_ipis: mid1.resched_ipis, ..pre })
                &&& mid1.threads == (Threads { records: mid1.threads.records, queues: mid1.threads.queues, ..pre.threads })
                &&& mid1.threads.records@.dom() == pre.threads.records@.dom()
                &&& mid1.threads.records@[head].addr() == pre.threads.records@[head].addr()
                &&& mid1.threads.records@[head].is_init()
                &&& same_thread_but_links(mid1.threads.records@[head].value(), ThreadRecord {
                    state: ThreadState::Runnable { core },
                    frame: new_frame,
                    saved: hr.saved,
                    save: Ghost(entry_frame_save(new_frame, hr.saved)),
                    queued: NONE,
                    wait_prev: NONE,
                    wait_next: NONE,
                    ..hr
                })
                &&& forall|x: usize| x != head && #[trigger] mid1.threads.records@.contains_key(x)
                    ==> same_record_perm_but_links(pre.threads.records@[x], mid1.threads.records@[x])
                &&& post == (CapKernel { endpoints: post.endpoints, threads: post.threads, resched_ipis: post.resched_ipis, ..mid1 })
                &&& post.threads == (Threads { records: post.threads.records, ..mid1.threads })
                &&& post.threads.records@.dom() == mid1.threads.records@.dom()
                &&& forall|x: usize| x != next && #[trigger] post.threads.records@.contains_key(x)
                    ==> post.threads.records@[x] == mid1.threads.records@[x]
                &&& next != NONE ==> {
                    &&& mid1.threads.records@.contains_key(next)
                    &&& post.threads.records@[next].addr() == mid1.threads.records@[next].addr()
                    &&& post.threads.records@[next].is_init()
                    &&& post.threads.records@[next].value() == (ThreadRecord { wait_prev: NONE, ..mid1.threads.records@[next].value() })
                }
                &&& post.endpoints == (Endpoints { records: post.endpoints.records, ..pre.endpoints })
                &&& post.endpoints.records@.dom() == pre.endpoints.records@.dom()
                &&& forall|x: usize| x != e && #[trigger] post.endpoints.records@.contains_key(x)
                    ==> post.endpoints.records@[x] == pre.endpoints.records@[x]
                &&& post.endpoints.records@[e].addr() == pre.endpoints.records@[e].addr()
                &&& post.endpoints.records@[e].is_init()
                &&& post.endpoints.records@[e].value() == (QueueRecord {
                    head: next,
                    tail: if next == NONE { NONE } else { r0.tail },
                    waiters: Ghost(r0.waiters@.skip(1)),
                    word: new_word,
                    ..r0
                })
                &&& post.resched_ipis@ == if pre.outranks_current(core as int, prio) {
                    pre.resched_ipis@.push(core)
                } else {
                    pre.resched_ipis@
                }
            }),
        ensures
            post.wf(),
            Self::signal_woke(pre, post, root, i),
    {
        let n = pre.tables.node_of(root, i);
        let e = pre.notification_at(root, i);
        let r0 = pre.endpoints.records@[e].value();
        let head = r0.head;
        let hr = pre.threads.records@[head].value();
        let pl = hr.placement->Some_0;
        let core = pl.core;
        let prio = pl.priority;
        let next = hr.wait_next;
        assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies u != NONE by {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, u));
        }
        assert(endpoint_wf(&pre.endpoints, &pre.blocks, e));
        lemma_waits_head(pre.endpoints.records@, pre.threads.records@, e);
        assert(post.threads.records@.dom() =~= pre.threads.records@.dom());
        assert(post.endpoints.records@.dom() =~= pre.endpoints.records@.dom());
        if next != NONE {
            assert(next != head);
            assert(post.threads.records@[head] == mid1.threads.records@[head]);
        }
        lemma_waits_head_removed(pre.endpoints.records@, post.endpoints.records@, pre.threads.records@, post.threads.records@, e);
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u) && !(mid1.threads.records@[u].value().state is Runnable)
            implies !(post.threads.records@[u].value().state is Runnable) by {
            if u != next {
                assert(post.threads.records@[u] == mid1.threads.records@[u]);
            }
        }
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u) && post.threads.records@[u].value().state is Runnable implies {
            let r1 = mid1.threads.records@[u].value();
            let r2 = post.threads.records@[u].value();
            &&& mid1.threads.records@.contains_key(u)
            &&& r2.state == r1.state
            &&& r2.placement == r1.placement
            &&& r2.process == r1.process
            &&& r2.run_prev == r1.run_prev
            &&& r2.run_next == r1.run_next
        } by {
            if u != next {
                assert(post.threads.records@[u] == mid1.threads.records@[u]);
            }
        }
        lemma_queues_same_wait(&mid1.threads.queues, mid1.threads.records@, post.threads.records@);
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u)
            implies thread_wf(&post.list, &post.threads, &post.blocks, u) by {
            assert(thread_wf(&mid1.list, &mid1.threads, &mid1.blocks, u));
            if u != next {
                assert(post.threads.records@[u] == mid1.threads.records@[u]);
            }
        }
        assert forall|x: usize| #[trigger] post.endpoints.records@.contains_key(x)
            implies endpoint_wf(&post.endpoints, &post.blocks, x) by {
            assert(endpoint_wf(&pre.endpoints, &pre.blocks, x));
            if x == e {
                if r0.waiters@.len() > 1 {
                    assert(WAITER_BIT & WAITER_BIT != 0) by (compute_only);
                } else {
                    assert(0u64 & WAITER_BIT == 0) by (compute_only);
                }
            }
        }
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u) && u != head implies {
            &&& post.threads.records@[u].addr() == pre.threads.records@[u].addr()
            &&& post.threads.records@[u].is_init()
            &&& same_thread_but_links(post.threads.records@[u].value(), ThreadRecord {
                wait_prev: if r0.waiters@.len() > 1 && u == r0.waiters@[1] {
                    NONE
                } else {
                    pre.threads.records@[u].value().wait_prev
                },
                ..pre.threads.records@[u].value()
            })
        } by {
            assert(same_record_perm_but_links(pre.threads.records@[u], mid1.threads.records@[u]));
            if u != next {
                assert(post.threads.records@[u] == mid1.threads.records@[u]);
            }
        }
        assert forall|u: usize| #[trigger] pre.threads.records@.contains_key(u) implies {
            &&& post.threads.records@.contains_key(u)
            &&& post.threads.records@[u].value().process == pre.threads.records@[u].value().process
            &&& post.threads.records@[u].value().placement == pre.threads.records@[u].value().placement
        } by {
            assert(post.threads.records@.contains_key(u));
        }
        assert(placed_running_wf(post.threads.records@)) by {
            reveal(placed_running_wf);
            assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u)
                implies thread_placed_running(post.threads.records@[u].value()) by {
                assert(thread_placed_running(pre.threads.records@[u].value()));
            }
        }
        assert(current_wf(post.cores@, post.threads.records@)) by {
            reveal(current_wf);
            assert forall|d: int, x: usize| 0 <= d < NUM_CPUS && #[trigger] runs(post.cores@, d, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: d as usize })
                &&& !post.threads.records@[x].value().pending_stop ==> runs_in_space(post.cores@, post.threads.records@, d, x)
            } by {
                assert(runs(pre.cores@, d, x));
                assert(x != head);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let c = post.threads.records@[x].value().state->Running_core;
                &&& c < NUM_CPUS
                &&& post.cores@[c as int].current_thread == Some(x)
            } by {
                assert(x != head);
                assert(pre.threads.records@.contains_key(x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
                if x == head {
                    reveal(placed_running_wf);
                    assert(thread_placed_running(hr));
                    assert(pre.threads.records@[x].value().pending_stop);
                }
            }
        }
        assert forall|d: int| 0 <= d < NUM_CPUS implies {
            &&& #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread
            &&& post.cores@[d].space == pre.cores@[d].space
        } by {
            assert(post.cores@[d] == pre.cores@[d]);
        }
        assert(post.cores.wf());
        assert(post.cores@.len() == pre.cores@.len());
        lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
        lemma_placements_kept(&pre.list, &pre.tables, &pre.threads, &post.list, &post.tables, &post.threads);
        assert forall|u: usize|
            #[trigger] post.threads.records@.contains_key(u) && post.threads.records@[u].value().process is Some
            implies pre.threads.records@.contains_key(u) by {}
        assert forall|u: usize|
            #[trigger] post.threads.records@.contains_key(u) && post.threads.records@[u].value().placement is Some
            implies pre.threads.records@.contains_key(u) by {}
        Self::lemma_queue_edit_wf(pre, post, 0);
        assert(!post.endpoints.records@[e].value().waiters@.contains(head)) by {
            reveal(waits_wf);
            assert(wait_queue_wf(r0, pre.threads.records@, e));
        }
        assert(at_back_of_priority(&post.threads.queues, post.threads.records@, core as int, prio, head)) by {
            assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u)
                && post.threads.records@[u].value().state == (ThreadState::Runnable { core })
                && thread_priority(post.threads.records@[u].value()) == prio
                && u != head
                implies exists|k: int| 0 <= k < post.threads.queues.queue(core as int, prio as int).len() - 1
                    && post.threads.queues.queue(core as int, prio as int)[k] == u by {
                assert(mid1.threads.records@.contains_key(u));
                if u != next {
                    assert(post.threads.records@[u] == mid1.threads.records@[u]);
                }
            }
        }
        assert(Self::consumed_kept(pre, post));
        Self::lemma_signal_woke_view(pre, post, root, i);
    }

    /// Proves that waking live head `head` of notification `e` through capability `n` keeps every
    /// other view object unchanged, adds no waiter, and discharges `Effect::Signal { cap: n, waiter: Some(head) }`.
    proof fn lemma_signal_woke_view(pre: Self, post: Self, root: usize, i: usize)
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            pre.root_live(root),
            pre.holds_notification(root, i, SEND_RIGHT),
            ({
                let e = pre.notification_at(root, i);
                let head = pre.endpoints.records@[e].value().head;
                &&& pre.signal_has_live_waiter(e)
                &&& pre.threads.records@.contains_key(head)
                &&& post == (CapKernel { endpoints: post.endpoints, threads: post.threads, resched_ipis: post.resched_ipis, ..pre })
                &&& post.threads.records@.dom() == pre.threads.records@.dom()
                &&& !(post.threads.records@[head].value().state is Blocked)
                &&& forall|u: usize| u != head && #[trigger] post.threads.records@.contains_key(u) ==> {
                    let ur = pre.threads.records@[u].value();
                    let vr = post.threads.records@[u].value();
                    &&& vr.state == ur.state
                    &&& vr.frame == ur.frame
                }
            }),
        ensures
            ({
                let n = pre.tables.node_of(root, i);
                let e = pre.notification_at(root, i);
                let head = pre.endpoints.records@[e].value().head;
                discharges(pre.view(), post.view(), root, Effect::Signal { cap: n, waiter: Some(head) })
            }),
    {
        let n = pre.tables.node_of(root, i);
        let e = pre.notification_at(root, i);
        let head = pre.endpoints.records@[e].value().head;
        let a = pre.view();
        let b = post.view();
        assert(b == (State { contents: b.contents, waiting: b.waiting, ..a }));
        assert forall|o: ObjectId| #[trigger] State::changed(a, b, o) implies o == head by {
            if o != head {
                assert(saved_registers(&post.threads).contains_key(o) == saved_registers(&pre.threads).contains_key(o));
                if saved_registers(&pre.threads).contains_key(o) {
                    assert(saved_registers(&post.threads)[o] == saved_registers(&pre.threads)[o]);
                }
                assert(contents_of(saved_registers(&post.threads), post.frames@, o)
                    == contents_of(saved_registers(&pre.threads), pre.frames@, o));
            }
        }
        assert forall|w: (ObjectId, ObjectId)| #[trigger] b.waiting.contains(w) implies a.waiting.contains(w) by {
            assert(waits_on(&post.threads, w.1) == Some(w.0));
            assert(w.1 != head);
            assert(waits_on(&post.threads, w.1) == waits_on(&pre.threads, w.1));
        }
        assert(adds_no_waiter(a, b));
        assert(unwaits(a, b));
        pre.lemma_slot(root, i);
        assert(SEND_RIGHT == right_bit(Right::Send)) by (compute_only);
        assert(a.holds_right(root, n, Right::Send));
        pre.lemma_endpoint_cap(n);
        assert(a.names[n] == e);
        assert(waits_on(&pre.threads, head) == Some(e));
        assert(a.waiting.contains((e, head)));
        assert(authorized(a, root, Effect::Signal { cap: n, waiter: Some(head) }));
        lemma_unwaits_discharges(a, b, root, Effect::Signal { cap: n, waiter: Some(head) });
    }

    /// Waits from core `c` (with partial frame `frame` saved if blocking) on the notification the
    /// capability at index `i` of the table at `root` names: when any signalled bit is set in its
    /// word, returns `Returned(word)` with those bits cleared, keeping the waiter bit; when none is
    /// set, saves the caller's partial frame, appends it to the notification's queue with the
    /// waiter bit set, moves core `c` off its current thread (`None`), and returns `Blocked`. The
    /// index comes from user space, so when it names no notification capability or one without the
    /// receive right, returns `Refused`, changing nothing.
    /// design/notification-word-reserves-the-waiter-bit/.
    pub fn wait(&mut self, c: usize, root: usize, i: usize, frame: Registers) -> (ret: WaitStep)
        requires
            old(self).wf(),
            old(self).caller_live(c as int, root),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            !(ret is Refused) == old(self).can_wait(c as int, root, i),
            ret is Returned == old(self).wait_signalled(root, i),
            ret is Blocked == (old(self).can_wait(c as int, root, i) && !old(self).wait_signalled(root, i)),
            ret is Refused ==> *final(self) == *old(self),
            ret is Returned ==> Self::waited(*old(self), *final(self), root, i, ret->Returned_0),
            ret is Blocked ==> Self::wait_blocked(*old(self), *final(self), c as int, root, i, frame),
    {
        let ghost pre = *self;
        proof {
            self.lemma_current_root_live(c as int);
        }
        let (n, payload) = match self.notification_cap(root, i, RECEIVE_RIGHT) {
            Some(found) => found,
            None => { return WaitStep::Refused; },
        };
        let e = payload.base;
        proof {
            pre.lemma_notification_record(root, i, RECEIVE_RIGHT);
        }
        let r = *PPtr::<QueueRecord>::from_usize(e).borrow(Tracked(self.endpoints.records.borrow().tracked_borrow(e)));
        let w = r.word;
        let word = w & SIGNAL_BITS;
        if word == 0 {
            let t = match self.cores.get(c).current_thread {
                Some(t) => t,
                None => { return WaitStep::Refused; },
            };
            self.unlink_waiter(t);
            let ghost mid = *self;
            proof {
                reveal(CapKernel::unlinked_waiter);
                assert(mid.threads.records@[t].value().state == (ThreadState::Running { core: c }));
                assert(thread_placed_running(mid.threads.records@[t].value())) by {
                    reveal(placed_running_wf);
                }
                assert(mid.threads.records@[t].value().placement is Some);
                assert(mid.threads.records@[t].value().process is Some);
                assert(mid.threads.records@[t].value().queued == NONE);
                assert(endpoint_wf(&mid.endpoints, &mid.blocks, e));
                assert(mid.blocks.pages@[(e / PAGE_SZ) as int].object is Notification);
                assert(pre.current_live(c as int));
                assert(!pre.threads.records@[t].value().pending_stop);
                assert(!mid.threads.records@[t].value().pending_stop);
            }
            self.append_waiter(c, e, t, frame, true);
            proof {
                let post = *self;
                assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
                assert(t != NONE);
                assert(wait_queue_wf(pre.endpoints.records@[e].value(), pre.threads.records@, e)) by {
                    reveal(waits_wf);
                }
                assert(wait_queue_wf(mid.endpoints.records@[e].value(), mid.threads.records@, e)) by {
                    reveal(waits_wf);
                }
                if mid.endpoints.records@[e].value().tail != NONE {
                    let h = mid.endpoints.records@[e].value().head;
                    assert(waiter_linked(mid.endpoints.records@[e].value().waiters@, mid.threads.records@, e, 0));
                    assert(thread_wf(&mid.list, &mid.threads, &mid.blocks, h));
                    assert(h != NONE);
                }
                assert(post.endpoints.records@[e].value().head != NONE);
                assert(post.threads.records@[t].value() == (ThreadRecord {
                    state: ThreadState::Blocked { object: e },
                    frame: partial_frame(frame),
                    saved: FrameKind::Partial,
                    save: Ghost(entry_frame_save(frame, FrameKind::Partial)),
                    queued: e,
                    wait_next: NONE,
                    wait_prev: post.threads.records@[t].value().wait_prev,
                    ..pre.threads.records@[t].value()
                }));
                assert forall|u: usize| u != t && #[trigger] post.threads.records@.contains_key(u) implies {
                    let ur = pre.threads.records@[u].value();
                    let vr = post.threads.records@[u].value();
                    &&& post.threads.records@[u].addr() == pre.threads.records@[u].addr()
                    &&& post.threads.records@[u].is_init()
                    &&& vr == (ThreadRecord {
                        wait_prev: vr.wait_prev,
                        wait_next: vr.wait_next,
                        ..ur
                    })
                } by {
                    assert(mid.threads.records@.contains_key(u));
                }
                assert(Self::writes_only_own_current(pre, post, c as int));
                assert(Self::consumed_kept(pre, post));
                Self::lemma_wait_blocked_view(pre, post, c as int, root, i, frame);
                assert(0u64 | WAITER_BIT == WAITER_BIT) by (compute_only);
                assert((w & !WAITER_BIT) | WAITER_BIT == w | WAITER_BIT) by (bit_vector)
                    requires WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
                assert forall|x: usize| x != e && #[trigger] post.endpoints.records@.contains_key(x) implies {
                    let px = pre.endpoints.records@[x].value();
                    let qx = post.endpoints.records@[x].value();
                    &&& post.endpoints.records@[x].addr() == pre.endpoints.records@[x].addr()
                    &&& post.endpoints.records@[x].is_init()
                    &&& qx.dead == px.dead
                    &&& qx.receiving == px.receiving
                    &&& qx.word & SIGNAL_BITS == px.word & SIGNAL_BITS
                    &&& x != pre.threads.records@[t].value().queued ==> post.endpoints.records@[x] == pre.endpoints.records@[x]
                } by {
                    let ghost w_x = pre.endpoints.records@[x].value().word;
                    assert((w_x & !WAITER_BIT) & SIGNAL_BITS == w_x & SIGNAL_BITS) by (bit_vector)
                        requires
                            SIGNAL_BITS == 0x7fff_ffff_ffff_ffffu64, // not a page size: SIGNAL_BITS
                            WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
                }
                assert(e % PAGE_SZ == 0);
                assert(NONE % PAGE_SZ == PAGE_MASK);
                assert(e != NONE);
                if pre.threads.records@[t].value().queued == NONE {
                    assert(mid == pre);
                } else {
                    assert(mid == (CapKernel { endpoints: mid.endpoints, threads: mid.threads, ..pre }));
                    assert(mid.cores == pre.cores);
                }
                assert(post == (CapKernel {
                    endpoints: post.endpoints,
                    threads: post.threads,
                    cores: post.cores,
                    ..mid
                }));
                assert(post == (CapKernel {
                    endpoints: post.endpoints,
                    threads: post.threads,
                    cores: post.cores,
                    ..pre
                }));
                assert(post.cores@.len() == pre.cores@.len());
                assert forall|d: int| 0 <= d < NUM_CPUS && d != (c as int) implies #[trigger] post.cores@[d] == pre.cores@[d] by {
                    assert(post.cores@[d] == mid.cores@[d]);
                    assert(mid.cores@[d] == pre.cores@[d]);
                }
                assert(post.cores@[c as int] == (CoreState { current_thread: None, ..mid.cores@[c as int] }));
                assert(mid.cores@[c as int] == pre.cores@[c as int]);
                assert(post.cores@[c as int] == (CoreState { current_thread: None, ..pre.cores@[c as int] }));
                assert(post.threads == (Threads { records: post.threads.records, ..pre.threads }));
                assert(post.threads.records@.dom() == pre.threads.records@.dom());
                assert(post.threads.records@[t].is_init());
                assert(post.threads.records@[t].addr() == pre.threads.records@[t].addr());
                assert(post.endpoints.holders == pre.endpoints.holders);
                assert(post.endpoints.records@.dom() == pre.endpoints.records@.dom());
                assert(post.endpoints.records@[e].is_init());
                assert(post.endpoints.records@[e].addr() == pre.endpoints.records@[e].addr());
                let pre_e = pre.endpoints.records@[e].value();
                let mid_e = mid.endpoints.records@[e].value();
                let post_e = post.endpoints.records@[e].value();
                assert(post_e.dead == mid_e.dead && mid_e.dead == pre_e.dead);
                assert(post_e.receiving == pre_e.receiving);
                assert(post_e.tail == t);
                assert(post_e.waiters@ == mid_e.waiters@.push(t));
                assert(post_e.waiters@.len() > 0);
                assert(post_e.waiters@.last() == t);
                assert(post_e.word == mid_e.word | WAITER_BIT);
                if pre.threads.records@[t].value().queued == e {
                    assert(mid_e.word == w & !WAITER_BIT || mid_e.word == w);
                    assert((w & !WAITER_BIT) | WAITER_BIT == w | WAITER_BIT);
                    assert(mid_e.word | WAITER_BIT == w | WAITER_BIT);
                } else {
                    assert(mid_e == pre_e);
                    assert(mid_e.word == w);
                }
                assert(post_e.word == pre_e.word | WAITER_BIT);
                if pre.threads.records@[t].value().queued != e {
                    assert(mid_e == pre_e);
                    let s = pre_e.waiters@;
                    assert(wait_queue_wf(pre_e, pre.threads.records@, e));
                    if s.len() == 0 {
                        assert(pre_e.head == NONE);
                        assert(pre_e.tail == NONE);
                    } else {
                        assert(pre_e.head == s[0]);
                        assert(pre_e.tail == s.last());
                        assert(waiter_linked(s, pre.threads.records@, e, 0));
                        assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, s[0]));
                        assert(s[0] % THREAD_BYTES == 0);
                        assert(s[0] != NONE);
                        assert(0 <= s.len() - 1 < s.len());
                        assert(waiter_linked(s, pre.threads.records@, e, s.len() - 1));
                        assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, s.last()));
                        assert(s.last() % THREAD_BYTES == 0);
                        assert(s.last() != NONE);
                        assert(pre_e.head != NONE);
                        assert(pre_e.tail != NONE);
                    }
                    assert((pre_e.head == NONE) == (pre_e.tail == NONE));
                    assert(post_e == (QueueRecord {
                        head: if mid_e.tail == NONE { t } else { mid_e.head },
                        tail: t,
                        waiters: Ghost(mid_e.waiters@.push(t)),
                        word: mid_e.word | WAITER_BIT,
                        ..mid_e
                    }));
                    assert(post_e.head == if pre_e.tail == NONE { t } else { pre_e.head });
                    assert(post_e.head == if pre_e.head == NONE { t } else { pre_e.head });
                    assert(post_e.waiters@ == pre_e.waiters@.push(t));
                }
                assert(Self::wait_blocked(pre, post, c as int, root, i, frame));
            }
            return WaitStep::Blocked;
        }
        proof {
            assert((w & !SIGNAL_BITS) & WAITER_BIT == w & WAITER_BIT) by (bit_vector)
                requires
                    SIGNAL_BITS == 0x7fff_ffff_ffff_ffffu64,
                    WAITER_BIT == 0x8000_0000_0000_0000u64; // not a page size: WAITER_BIT
        }
        self.write_word(e, w & !SIGNAL_BITS);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        WaitStep::Returned(word)
    }

    /// Proves that blocking core `c`'s live caller `t` on notification `e` through capability `n`
    /// keeps every non-caller view object unchanged, adds only `(e, t)` to `waiting`, and
    /// discharges `Effect::Wait { cap: n, caller: t }`.
    proof fn lemma_wait_blocked_view(
        pre: Self,
        post: Self,
        c: int,
        root: usize,
        i: usize,
        frame: Registers,
    )
        requires
            pre.wf(),
            pre.caller_live(c, root),
            pre.holds_notification(root, i, RECEIVE_RIGHT),
            ({
                let e = pre.notification_at(root, i);
                let t = pre.cores@[c].current_thread->Some_0;
                let r = pre.threads.records@[t].value();
                &&& post == (CapKernel { endpoints: post.endpoints, threads: post.threads, cores: post.cores, ..pre })
                &&& post.threads.records@.dom() == pre.threads.records@.dom()
                &&& post.threads.records@[t].value().state == (ThreadState::Blocked { object: e })
                &&& forall|u: usize| u != t && #[trigger] post.threads.records@.contains_key(u) ==> {
                    let ur = pre.threads.records@[u].value();
                    let vr = post.threads.records@[u].value();
                    &&& vr.state == ur.state
                    &&& vr.frame == ur.frame
                }
            }),
        ensures
            ({
                let n = pre.tables.node_of(root, i);
                let t = pre.cores@[c].current_thread->Some_0;
                discharges(pre.view(), post.view(), root, Effect::Wait { cap: n, caller: t })
            }),
    {
        let n = pre.tables.node_of(root, i);
        let e = pre.notification_at(root, i);
        let t = pre.cores@[c].current_thread->Some_0;
        let a = pre.view();
        let b = post.view();
        assert(b == (State { contents: b.contents, waiting: b.waiting, ..a }));
        assert forall|o: ObjectId| #[trigger] State::changed(a, b, o) implies o == t by {
            if o != t {
                assert(saved_registers(&post.threads).contains_key(o) == saved_registers(&pre.threads).contains_key(o));
                if saved_registers(&pre.threads).contains_key(o) {
                    assert(saved_registers(&post.threads)[o] == saved_registers(&pre.threads)[o]);
                }
                assert(contents_of(saved_registers(&post.threads), post.frames@, o)
                    == contents_of(saved_registers(&pre.threads), pre.frames@, o));
            }
        }
        assert forall|w: (ObjectId, ObjectId)| #[trigger] b.waiting.contains(w)
            implies a.waiting.contains(w) || w == (e, t) by {
            assert(waits_on(&post.threads, w.1) == Some(w.0));
            if w.1 != t {
                assert(waits_on(&post.threads, w.1) == waits_on(&pre.threads, w.1));
            }
        }
        assert(blocks_waiting(a, b, e, t));
        pre.lemma_slot(root, i);
        assert(RECEIVE_RIGHT == right_bit(Right::Receive)) by (compute_only);
        assert(a.holds_right(root, n, Right::Receive));
        pre.lemma_bound_threads();
        lemma_record_processes(&pre.threads, t);
        assert(a.process_of.contains_key(t) && a.process_of[t] == root);
        assert(authorized(a, root, Effect::Wait { cap: n, caller: t }));
        pre.lemma_endpoint_cap(n);
        lemma_pow2_pos(pre.payload_of(n).order as nat);
        assert(a.covers(n, a.names[n]));
        lemma_blocks_waiting_discharges(a, b, root, Effect::Wait { cap: n, caller: t });
    }
}

} // verus!
