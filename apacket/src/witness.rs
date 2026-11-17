// SPDX-License-Identifier: MIT

//! The witnesses, built into no image: for each format, a caller holding an input and an output
//! buffer, as the protocol above does, parses the format's value from the input, reads it through
//! its mapping each way, and writes it back, having first asked its serialised length within the
//! buffer's room; the buffer then starts with exactly the bytes the parse consumed. Each reaches the
//! accepting way of the format's `new`, `parse`, `length` and `serialize`, and its mapping's
//! conversions. design/witness-per-way-an-operation-succeeds/.

use vstd::prelude::*;

use awire::*;

use crate::*;

verus! {

/// Reads an ARP packet for Ethernet and IPv4, converts its named fields to the nested pairs the
/// combinators give and back, and writes it back.
pub fn witness_arp<'a>(input: &'a [u8], out: &mut [u8]) -> (r: (Option<(usize, ArpPacket<'a>)>, Option<usize>, Option<usize>))
    requires
        input.len() >= 28,
        input@[0] == 0x00,
        input@[1] == 0x01,
        input@[2] == 0x08,
        input@[3] == 0x00,
        input@[4] == 6,
        input@[5] == 4,
        old(out).len() >= 28,
    ensures
        r.0 is Some,
        r.1 is Some,
        r.2 is Some,
        final(out)@.take(28) == input@.take(28),
{
    let c: Arp = Arp::new();
    let m: ArpMapping = ArpMapping;
    proof {
        c.lemma_header_accepted(input@);
    }
    let tracked mut steps = Steps::fresh();
    let parsed = c.parse(input, Tracked(&mut steps));
    let (_, read) = parsed.unwrap();
    let fields = m.map_from(&read, Tracked(&mut steps));
    let v = m.map_into(fields, Tracked(&mut steps));
    proof {
        m.lemma_into_from(read@);
    }
    let room = c.length(&v, out.len(), Tracked(&mut steps));
    let wrote = c.serialize(&v, out, 0, Tracked(&mut steps));
    assert(out@.take(28) =~= input@.take(28));
    (parsed, wrote, room)
}

} // verus!
