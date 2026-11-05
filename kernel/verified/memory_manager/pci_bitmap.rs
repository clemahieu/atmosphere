use vstd::prelude::*;
verus! {

use crate::define::*;
use core::mem::MaybeUninit;

pub struct PCIBitMap {
    pub bit_map: [[[u8; 32]; 256]; IOID_MAX],  //32MB
    pub ghost_map: Ghost<Map<(IOid, u8, u8, u8), bool>>,
}

impl PCIBitMap {
    #[verifier(external_body)]
    // external_body(gap): builds a value from zeroed memory, which Verus cannot check
    pub const fn new() -> (ret: Self)
        ensures
            ret.wf(),
    {
        unsafe {
            Self { bit_map: MaybeUninit::zeroed().assume_init(), ghost_map: Ghost(Map::empty()) }
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& (forall|ioid: IOid, bus: u8, dev: u8, fun: u8|
            #![auto]
            0 <= ioid < IOID_MAX && 0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8
                <==> self.ghost_map@.dom().contains((ioid, bus, dev, fun)))
    }

    pub open spec fn view(&self) -> Map<(IOid, u8, u8, u8), bool> {
        self.ghost_map@
    }

    pub open spec fn resolve(&self, ioid: IOid, bus: u8, dev: u8, fun: u8) -> bool
        recommends
            self.wf(),
            0 <= ioid < IOID_MAX,
            0 <= bus < 256 && 0 <= dev < 32 && 0 <= fun < 8,
    {
        self.ghost_map@[(ioid, bus, dev, fun)]
    }
}

} // verus!
