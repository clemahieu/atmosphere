// SPDX-License-Identifier: MIT

//! The witnesses: verified sequences of `afanin::scan` over `aring::Producer` and
//! `aring::Consumer` ends built by their constructors, built into no image, reaching both
//! `Scan::Ready` and `Scan::Idle`.

use aring::{Consumer, Producer};
use vstd::prelude::*;

use crate::{examined, order, scan, Heads, Scan};

verus! {

pub struct TwoHeads {
    pub h0: u32,
    pub h1: u32,
}

impl Heads for TwoHeads {
    open spec fn may_load(&self, ring: int, h: u32) -> bool {
        h == if ring == 0 {
            self.h0
        } else {
            self.h1
        }
    }

    fn load(&self, ring: usize) -> (h: u32) {
        if ring == 0 {
            self.h0
        } else {
            self.h1
        }
    }
}

/// Constructs two four-slot rings, publishes a wild head on ring 0 that ring 0 rejects and an
/// honest slot on ring 1, and scans from ring 0: `scan` skips ring 0 and returns `Scan::Ready` for
/// ring 1.
pub fn witness_scan_ready() -> (r: Scan)
    ensures
        r is Ready,
{
    let mut slots: [u64; 4] = [0, 0, 0, 0];
    let mut p1 = Producer::new(4);
    let c0 = Consumer::new(4);
    let c1 = Consumer::new(4);
    let mut rings: [Consumer; 2] = [c0, c1];
    p1.write(&mut slots, 0, 42);
    let h1 = p1.publish(1);
    let heads = TwoHeads { h0: 99, h1 };
    proof {
        assert(rings@[0] == c0);
        assert(rings@[1] == c1);
    }
    let ghost before = rings@;
    let r = scan(&mut rings, &heads, 0);
    proof {
        if let Scan::Idle(hs) = r {
            assert(examined(before[1], rings@[1], hs@[1]));
            assert(heads.may_load(1, hs@[1]));
        }
    }
    r
}

/// Constructs two four-slot rings, publishes an honest slot on ring 1 beside a wild head on ring 0,
/// scans `Scan::Ready`, reads the slot back and consumes it, and scans again from ring 0 to reach
/// `Scan::Idle`.
pub fn witness_scan_idle() -> (ret: (Scan, u64))
    ensures
        ret.0 is Idle,
        ret.1 == 42,
{
    let mut slots: [u64; 4] = [0, 0, 0, 0];
    let mut p1 = Producer::new(4);
    let c0 = Consumer::new(4);
    let c1 = Consumer::new(4);
    let mut rings: [Consumer; 2] = [c0, c1];
    p1.write(&mut slots, 0, 42);
    let h1 = p1.publish(1);
    let heads = TwoHeads { h0: 99, h1 };
    proof {
        assert(rings@[0] == c0);
        assert(rings@[1] == c1);
    }
    let ghost before = rings@;
    let first = scan(&mut rings, &heads, 0);
    let v = match first {
        Scan::Ready(k, hs) => {
            proof {
                if k == 0 {
                    assert(heads.may_load(0, hs@[0]));
                }
                assert(k == 1);
                assert(order(0, 2, 0) < order(0, 2, 1));
                assert(heads.may_load(0, hs@[0]));
                assert(heads.may_load(1, hs@[1]));
            }
            let rs: &mut [Consumer] = &mut rings;
            let val = rs[k].read(&slots, 0);
            let _tail = rs[k].consume(1);
            val
        },
        Scan::Idle(hs) => {
            proof {
                assert(examined(before[1], rings@[1], hs@[1]));
                assert(heads.may_load(1, hs@[1]));
                assert(false);
            }
            0
        },
    };
    proof {
        assert(rings@[0] == c0);
        assert(rings@[1].wf());
    }
    let ghost mid = rings@;
    let idle = scan(&mut rings, &heads, 0);
    proof {
        if let Scan::Ready(k2, hs2) = idle {
            if k2 == 0 {
                assert(heads.may_load(0, hs2@[0]));
            } else {
                assert(k2 == 1);
                assert(heads.may_load(1, hs2@[1]));
            }
        }
    }
    (idle, v)
}

} // verus!
