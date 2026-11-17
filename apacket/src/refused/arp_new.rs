// SPDX-License-Identifier: MIT

//! `Arp::new` at a combinator that is not the format's. The ensures is `c.wf()`, which pins the
//! fixed fields and the address lengths; this is that ensures at the other output.
//! design/refused-claim-per-way/.
//!
//! covers: apacket/src/arp.rs	Arp::new	returns
//! refused: wrong: !<Arp as Combinator<'a>>::wf(c)

use vstd::prelude::*;

use crate::*;

verus! {

impl<'a> super::ArpNew<'a> for () {
    proof fn wrong(c: &Arp) {}
}

} // verus!
