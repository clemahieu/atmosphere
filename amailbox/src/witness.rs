// SPDX-License-Identifier: MIT

//! The witness: a verified sequence of amailbox's operations, built into no image, that constructs
//! a mailbox, checks slot separation, reads the initial value, observes the stale word, writes and
//! publishes twice so the first publish is dropped, adopts the latest publish and reads it back.

use vstd::prelude::*;
use crate::{held_apart, Consumer, Mailbox, Producer};

verus! {

/// Exercises every operation of `amailbox`: constructs a mailbox, checks `held_apart`, reads the
/// initial value, observes before any publish (`false`), writes and publishes twice, adopts the
/// latest publish (`true`), reads it back, and observes again with and without the producer token.
pub fn witness_mailbox_round_trip() -> (ret: (bool, bool, bool, u64, u64))
    ensures
        ret.0,
        !ret.1,
        !ret.2,
        ret.3 == 20,
        ret.4 == 99,
{
    let (m, mut p, mut c) = Mailbox::new(10u64, 20u64, 30u64);
    held_apart(&m, &p, &c);
    let v0 = Consumer::read(&c, &m);
    let initial = *v0;
    let stale_before = Consumer::observe(&mut c, &m, Tracked(Some(p.token.borrow())));
    Producer::write(&mut p, &m, 42u64);
    Producer::publish(&mut p, &m);
    Producer::write(&mut p, &m, 99u64);
    Producer::publish(&mut p, &m);
    let adopted = Consumer::observe(&mut c, &m, Tracked(Some(p.token.borrow())));
    let v1 = Consumer::read(&c, &m);
    let latest = *v1;
    let stale_after = Consumer::observe(&mut c, &m, Tracked(Some(p.token.borrow())));
    let _without_producer = Consumer::observe(&mut c, &m, Tracked(None));
    (adopted, stale_before, stale_after, initial, latest)
}

} // verus!
