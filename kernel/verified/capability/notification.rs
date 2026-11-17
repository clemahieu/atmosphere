// SPDX-License-Identifier: MIT

//! Signal and wait on a notification, through a capability the caller holds. Signal ORs the
//! capability's badge into the notification's word and returns ok or refused, never blocking; wait
//! returns the word's signalled bits and clears them when any is set, and blocks core c's current
//! thread on the notification's queue with its partial frame saved when none is set. The word's
//! bit 63 is the kernel's waiter bit, which signal does not set and wait preserves when returning
//! or sets while a thread queues. Nothing wakes a waiter yet, so signal refuses while its queue
//! lists a thread. See design/notification-word-reserves-the-waiter-bit/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::{lemma_pow2_pos, pow2};
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arch::partial_frame;
use crate::arch::Registers;
#[cfg(verus_keep_ghost)]
use crate::arch::FrameKind;
use crate::capability::endpoint::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
#[cfg(verus_keep_ghost)]
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
    /// the send right, and no thread waits on the notification.
    pub open spec fn can_signal(&self, root: usize, i: usize) -> bool {
        &&& self.holds_notification(root, i, SEND_RIGHT)
        &&& self.notification_record(root, i).waiters@.len() == 0
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

    /// What a signal through index i of the table at root did: ORed the capability's badge into the
    /// notification's word, changing nothing a process sees, as the reach lemma's signal that wakes no
    /// thread.
    pub open spec fn signalled(pre: Self, post: Self, root: usize, i: usize) -> bool {
        let n = pre.tables.node_of(root, i);
        let e = pre.notification_at(root, i);
        &&& Self::word_written(pre, post, e, pre.notification_record(root, i).word | pre.payload_of(n).badge as u64)
        &&& discharges(pre.view(), post.view(), root, Effect::Signal { cap: n, waiter: None })
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
    /// capability's badge into its word, which sets no waiter bit, a badge being below it. It never
    /// blocks and returns only whether it signalled. The index comes from user space, so it can name
    /// no notification capability or one without the send right, and a thread may wait on the
    /// notification, which this signal does not yet wake: each is refused, changing nothing.
    /// design/notification-word-reserves-the-waiter-bit/.
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
        if r.head != NONE {
            return false;
        }
        let badge = payload.badge as u64;
        let w = r.word;
        proof {
            assert(badge < 0x8000_0000_0000_0000u64); // not a page size: NOTIFICATION_BADGE_LIMIT
            assert(r.word & WAITER_BIT == 0) by {
                assert(word_wf(r, pre.blocks.pages@[(e / PAGE_SZ) as int].object));
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
