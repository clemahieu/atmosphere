// SPDX-License-Identifier: MIT

//! `ArpMapping`'s map_into and map_from at a value other than the one their ensures gives. map_into
//! returns `spec_into(s@)` and map_from returns `spec_from(t@)`; each claim is that ensures at the
//! other output. design/refused-claim-per-way/.
//!
//! covers: apacket/src/arp.rs	ArpMapping::map_into	returns
//! covers: apacket/src/arp.rs	ArpMapping::map_from	returns
//! refused: into: t@ != m.spec_into(s@)
//! refused: from: s@ != m.spec_from(t@)

use vstd::prelude::*;

use crate::*;

verus! {

impl<'a> super::ArpMappingReturns<'a> for () {
    proof fn into(m: &ArpMapping, s: ArpFields<'a>, t: ArpPacket<'a>) {}

    proof fn from(m: &ArpMapping, t: &ArpPacket<'a>, s: ArpFields<'a>) {}
}

} // verus!
