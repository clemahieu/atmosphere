// SPDX-License-Identifier: MIT

//! The witness: a verified sequence of aring's operations, built into no image, that reaches one
//! round-trip from newly constructed ends — writing, publishing, observing, reading, consuming and
//! observing the released tail.

use vstd::prelude::*;
use crate::{Consumer, Producer};

verus! {

/// Constructs both ends over four slots, writes a slot and publishes it, observes the head on the
/// consumer, reads the slot back and consumes it, and observes the released tail on the producer.
pub fn witness_ring_round_trip(slots: &mut [u64]) -> (ret: (bool, bool, u64, u32, usize, u32, usize))
    requires
        old(slots)@.len() == 4,
    ensures
        ret.0,
        ret.1,
        ret.2 == 42,
        ret.3 == 4,
        ret.4 == 0,
        ret.5 == 1,
        ret.6 == 0,
{
    let mut p = Producer::new(4);
    let mut c = Consumer::new(4);
    let free = p.free();
    let ps = p.slot(0);
    p.write(slots, 0, 42);
    let _head = p.publish(1);
    let published = p.index();
    let c_accepted = c.observe(published);
    let avail = c.available();
    let cs = c.slot(0);
    let v = c.read(slots, 0);
    let _tail = c.consume(1);
    let released = c.index();
    let p_accepted = p.observe(released);
    (c_accepted, p_accepted, v, free, ps, avail, cs)
}

} // verus!
