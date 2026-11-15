// SPDX-License-Identifier: MIT

//! Signal and wait on a notification, through a capability the caller holds. Signal ORs the
//! capability's badge into the notification's word and returns ok or refused, never blocking; wait
//! returns the word's signalled bits and clears them. The word's bit 63 is the kernel's waiter bit,
//! which neither touches. Nothing queues on a notification yet, so signal refuses while its queue
//! lists a thread, and wait refuses while no bit is signalled: waking a waiter and blocking come with
//! the queue. See design/notification-word-reserves-the-waiter-bit/.
use vstd::prelude::*;

verus! {

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

    /// Wait through index i of the table at root returns at once: it holds a notification capability
    /// with the receive right, and the notification's word has a signalled bit.
    pub open spec fn can_wait(&self, root: usize, i: usize) -> bool {
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

    /// Waits on the notification the capability at index i of the table at root names: returns its
    /// word's signalled bits and clears them, keeping the waiter bit. The index comes from user space,
    /// so it can name no notification capability or one without the receive right, and the word may
    /// have no signalled bit, on which this wait does not yet block: each is refused, None, changing
    /// nothing. design/notification-word-reserves-the-waiter-bit/.
    pub fn wait(&mut self, root: usize, i: usize) -> (ret: Option<u64>)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).blocks.pages@.len() == old(self).blocks.pages@.len(),
            final(self).wf(),
            ret is Some == old(self).can_wait(root, i),
            ret is None ==> *final(self) == *old(self),
            ret is Some ==> Self::waited(*old(self), *final(self), root, i, ret->0),
    {
        let ghost pre = *self;
        let (n, payload) = match self.notification_cap(root, i, RECEIVE_RIGHT) {
            Some(found) => found,
            None => { return None; },
        };
        let e = payload.base;
        proof {
            pre.lemma_notification_record(root, i, RECEIVE_RIGHT);
        }
        let r = *PPtr::<QueueRecord>::from_usize(e).borrow(Tracked(self.endpoints.records.borrow().tracked_borrow(e)));
        let w = r.word;
        let word = w & SIGNAL_BITS;
        if word == 0 {
            return None;
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
        Some(word)
    }
}

} // verus!
