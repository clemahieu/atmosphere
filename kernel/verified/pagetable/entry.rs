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

pub struct MapEntry {
    pub addr: PAddr,
    pub write: bool,
    pub execute_disable: bool,
}

pub open spec fn spec_page_entry_to_map_entry(p: &PageEntry) -> MapEntry {
    MapEntry { addr: p.addr, write: p.perm.write, execute_disable: p.perm.execute_disable }
}

#[verifier(when_used_as_spec(spec_page_entry_to_map_entry))]
pub fn page_entry_to_map_entry(p: &PageEntry) -> (ret: MapEntry)
    ensures
        ret =~= spec_page_entry_to_map_entry(p),
{
    MapEntry { addr: p.addr, write: p.perm.write, execute_disable: p.perm.execute_disable }
}

pub open spec fn spec_map_entry_to_page_entry(m: &MapEntry, ps: bool) -> PageEntry {
    PageEntry {
        addr: m.addr,
        perm: PageEntryPerm {
            present: true,
            ps: ps,
            write: m.write,
            execute_disable: m.execute_disable,
            user: true,
        },
    }
}

#[verifier(when_used_as_spec(spec_map_entry_to_page_entry))]
pub fn map_entry_to_page_entry(m: &MapEntry, ps: bool) -> (ret: PageEntry)
    ensures
        ret == spec_map_entry_to_page_entry(m, ps),
{
    PageEntry {
        addr: m.addr,
        perm: PageEntryPerm {
            present: true,
            ps: ps,
            write: m.write,
            execute_disable: m.execute_disable,
            user: true,
        },
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
