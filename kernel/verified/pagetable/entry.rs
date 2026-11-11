// SPDX-License-Identifier: MIT

use vstd::prelude::*;
verus! {

use crate::define::*;

#[derive(Debug)]
pub struct PageEntryPerm {
    pub present: bool,
    pub ps: bool,
    pub write: bool,
    pub execute_disable: bool,
    pub user: bool,
}

#[derive(Debug)]
pub struct PageEntry {
    pub addr: PAddr,
    pub perm: PageEntryPerm,
    // pub ps: bool,
}

impl PageEntry {
    pub open spec fn is_empty(&self) -> bool {
        &&& self.addr == 0
        &&& self.perm.present == false
        &&& self.perm.ps == false
        &&& self.perm.write == false
        &&& self.perm.execute_disable == false
        &&& self.perm.user == false
    }

    pub fn empty() -> (ret: Self)
        ensures
            ret.is_empty(),
    {
        PageEntry {
            addr: 0,
            perm: PageEntryPerm {
                present: false,
                ps: false,
                write: false,
                execute_disable: false,
                user: false,
            },
        }
    }
}

/// The bits the processor sets in an entry it walks: accessed on any walk through the entry, dirty on
/// a write through a leaf. The processor sets them on any core at any time, also while this core holds
/// the kernel, so they are not part of PageEntry, the entry the table view holds and the proofs relate:
/// two words that differ only in them decode to the same PageEntry (lemma_status_outside_entry). The
/// encoder writes them clear. See design/arch-module/.
#[derive(Clone, Copy, Debug)]
pub struct PageEntryStatus {
    pub accessed: bool,
    pub dirty: bool,
}

impl PageEntryStatus {
    pub open spec fn is_clear(self) -> bool {
        &&& !self.accessed
        &&& !self.dirty
    }
}

} // verus!
