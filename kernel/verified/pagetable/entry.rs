use vstd::prelude::*;
verus! {

use crate::arch::{
    MEM_MASK, PAGE_ENTRY_ACCESSED_MASK, PAGE_ENTRY_DIRTY_MASK, PAGE_ENTRY_EXECUTE_MASK,
    PAGE_ENTRY_PRESENT_MASK, PAGE_ENTRY_PS_MASK, PAGE_ENTRY_USER_MASK, PAGE_ENTRY_WRITE_MASK,
};
use crate::define::*;

use crate::util::page_ptr_util_u::*;

#[derive(Clone,Debug)]
pub struct PageEntryPerm {
    pub present: bool,
    pub ps: bool,
    pub write: bool,
    pub execute_disable: bool,
    pub user: bool,
}

#[derive(Clone,Debug)]
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

pub open spec fn usize2present(v: usize) -> bool {
    (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0
}

pub open spec fn usize2ps(v: usize) -> bool {
    (v & PAGE_ENTRY_PS_MASK as usize) != 0
}

pub open spec fn usize2write(v: usize) -> bool {
    (v & PAGE_ENTRY_WRITE_MASK as usize) != 0
}

pub open spec fn usize2execute_disable(v: usize) -> bool {
    (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0
}

pub open spec fn usize2user(v: usize) -> bool {
    (v & PAGE_ENTRY_USER_MASK as usize) != 0
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

pub open spec fn usize2accessed(v: usize) -> bool {
    (v & PAGE_ENTRY_ACCESSED_MASK as usize) != 0
}

pub open spec fn usize2dirty(v: usize) -> bool {
    (v & PAGE_ENTRY_DIRTY_MASK as usize) != 0
}

pub open spec fn spec_usize2page_entry_status(v: usize) -> PageEntryStatus {
    PageEntryStatus { accessed: usize2accessed(v), dirty: usize2dirty(v) }
}

/// Two words that differ only in the accessed and dirty bits decode to the same entry, so whatever the
/// processor sets there leaves every table's view as it was.
pub proof fn lemma_status_outside_entry(v: usize, w: usize)
    requires
        v & (!(PAGE_ENTRY_ACCESSED_MASK | PAGE_ENTRY_DIRTY_MASK)) as usize == w & (!(
        PAGE_ENTRY_ACCESSED_MASK | PAGE_ENTRY_DIRTY_MASK)) as usize,
    ensures
        spec_usize2page_entry(v) == spec_usize2page_entry(w),
{
    assert(v & 0x0000_ffff_ffff_f000u64 as usize == w & 0x0000_ffff_ffff_f000u64 as usize
        && (v & 0x1u64 as usize != 0) == (w & 0x1u64 as usize != 0)
        && (v & (0x1u64 << 7u64) as usize != 0) == (w & (0x1u64 << 7u64) as usize != 0)
        && (v & (0x1u64 << 1u64) as usize != 0) == (w & (0x1u64 << 1u64) as usize != 0)
        && (v & (0x1u64 << 63u64) as usize != 0) == (w & (0x1u64 << 63u64) as usize != 0)
        && (v & (0x1u64 << 2u64) as usize != 0) == (w & (0x1u64 << 2u64) as usize != 0))
        by (bit_vector)
        requires
            v & (!((0x1u64 << 5u64) | (0x1u64 << 6u64))) as usize == w & (!((0x1u64 << 5u64) | (
            0x1u64 << 6u64))) as usize,
    ;
}

pub proof fn zero_leads_is_empty_page_entry()
    ensures
        spec_usize2page_entry(0).is_empty(),
{
    assert(0usize & 0x0000_ffff_ffff_f000u64 as usize == 0) by (bit_vector);
    assert(0usize & 0x1 as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x7u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x1u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 63u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x2u64) as usize != 0 == false) by (bit_vector);
}

pub open spec fn spec_usize2page_entry_perm(v: usize) -> PageEntryPerm {
    PageEntryPerm {
        present: usize2present(v),
        ps: usize2ps(v),
        write: usize2write(v),
        execute_disable: usize2execute_disable(v),
        user: usize2user(v),
    }
}

#[verifier(when_used_as_spec(spec_usize2page_entry_perm))]
pub fn usize2page_entry_perm(v: usize) -> (ret: PageEntryPerm)
    ensures
        ret =~= spec_usize2page_entry_perm(v),
        v == 0 ==> ret.present == false && ret.ps == false && ret.write == false
            && ret.execute_disable == false && ret.user == false,
{
    assert(0usize & 0x1 as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x7u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x1u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 63u64) as usize != 0 == false) by (bit_vector);
    assert(0usize & (0x1u64 << 0x2u64) as usize != 0 == false) by (bit_vector);
    PageEntryPerm {
        present: (v & PAGE_ENTRY_PRESENT_MASK as usize) != 0,
        ps: (v & PAGE_ENTRY_PS_MASK as usize) != 0,
        write: (v & PAGE_ENTRY_WRITE_MASK as usize) != 0,
        execute_disable: (v & PAGE_ENTRY_EXECUTE_MASK as usize) != 0,
        user: (v & PAGE_ENTRY_USER_MASK as usize) != 0,
    }
}

pub open spec fn spec_usize2page_entry(v: usize) -> PageEntry {
    PageEntry { addr: usize2pa(v), perm: usize2page_entry_perm(v) }
}

#[verifier(when_used_as_spec(spec_usize2page_entry))]
pub fn usize2page_entry(v: usize) -> (ret: PageEntry)
    ensures
        ret =~= spec_usize2page_entry(v),
        v == 0 ==> ret.addr == 0 && ret.perm.present == false && ret.perm.ps == false
            && ret.perm.write == false && ret.perm.execute_disable == false && ret.perm.user
            == false,
{
    assert(0usize & 0x0000_ffff_ffff_f000u64 as usize == 0) by (bit_vector);
    PageEntry { addr: usize2pa(v), perm: usize2page_entry_perm(v) }
}

pub open spec fn spec_usize2pa(v: usize) -> PAddr {
    v & MEM_MASK as usize
}

#[verifier(when_used_as_spec(spec_usize2pa))]
pub fn usize2pa(v: usize) -> (ret: PAddr)
    ensures
        ret =~= spec_usize2pa(v),
        MEM_valid(ret),
{
    let ret = v & MEM_MASK as usize;
    assert(v & 0x0000_ffff_ffff_f000u64 as usize & (!0x0000_ffff_ffff_f000u64) as usize == 0)
        by (bit_vector);
    return ret;
}

pub fn page_entry2usize(page_entry: &PageEntry) -> (ret: usize)
    requires
        MEM_valid(page_entry.addr),
    ensures
        usize2present(ret) == page_entry.perm.present,
        usize2ps(ret) == page_entry.perm.ps,
        usize2write(ret) == page_entry.perm.write,
        usize2execute_disable(ret) == page_entry.perm.execute_disable,
        usize2user(ret) == page_entry.perm.user,
        usize2pa(ret) == page_entry.addr,
        usize2page_entry_perm(ret) =~= page_entry.perm,
        spec_usize2page_entry_status(ret).is_clear(),
{
    let mut ret: usize = page_entry.addr;

    let mut ghost_addr = Ghost(page_entry.addr);
    let mut ghost_ret = Ghost(page_entry.addr);
    let ghost_present = Ghost(page_entry.perm.present);
    let ghost_ps = Ghost(page_entry.perm.ps);
    let ghost_write = Ghost(page_entry.perm.write);
    let ghost_execute_disable = Ghost(page_entry.perm.execute_disable);
    let ghost_user = Ghost(page_entry.perm.user);
    assert(ret == ghost_addr@);

    if page_entry.perm.present == true {
        assert(((ret | 0x1u64 as usize) & 0x1u64 as usize) != 0) by (bit_vector);
        assert(((ret | 0x1u64 as usize) & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@)
            by (bit_vector)
            requires
                ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0 && ghost_addr@ == ret,
        ;

        ret = ret | 0x1u64 as usize;

        assert((ret & 0x1u64 as usize) != 0);
        assert(usize2present(ret) == page_entry.perm.present);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == page_entry.addr);
        assert(usize2pa(ret) == page_entry.addr);

        assert((ghost_ret@ | 0x1u64 as usize) & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize
            == 0) by (bit_vector)
            requires
                ghost_ret@ & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & 0x1u64 as usize) == 0) by (bit_vector)
            requires
                ret & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(usize2present(ret) == page_entry.perm.present);

        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ret) by (bit_vector)
            requires
                ret & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(usize2pa(ret) == page_entry.addr);

        assert(ghost_addr@ & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_addr@ & (!0x0000_ffff_ffff_f000u64) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2pa(ret) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.ps == true {
        assert(((ret | (0x1u64 << 0x7u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 0x7u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 0x7u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 0x7u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 0x7u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64
            | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 0x7u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert(usize2pa(ret) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0)
            by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps);
    assert(usize2pa(ret) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.write == true {
        assert(((ret | (0x1u64 << 0x1u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 0x1u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 0x1u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0
            == ghost_ps@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@,
        ;
        assert(((ret | (0x1u64 << 0x1u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 0x1u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0);
        assert(usize2write(ret) == page_entry.perm.write);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 0x1u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64
            << 0x1u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize
                    == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 0x1u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert(usize2write(ret) == page_entry.perm.write);
        assert(usize2pa(ret) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
            | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps);
    assert(usize2write(ret) == page_entry.perm.write);
    assert(usize2pa(ret) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
        | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.execute_disable == true {
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 63u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 63u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@,
        ;
        assert(((ret | (0x1u64 << 63u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0
            == ghost_write@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@,
        ;
        assert(((ret | (0x1u64 << 63u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 63u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@);
        assert(usize2write(ret) == page_entry.perm.write);
        assert((ret & (0x1u64 << 63u64) as usize) != 0);
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 63u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64
            << 0x1u64 | 0x1u64 << 63u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 63u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert(usize2write(ret) == page_entry.perm.write);
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable);
        assert(usize2pa(ret) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
            | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps);
    assert(usize2write(ret) == page_entry.perm.write);
    assert(usize2execute_disable(ret) == page_entry.perm.execute_disable);
    assert(usize2pa(ret) == page_entry.addr);
    assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
        | PAGE_ENTRY_EXECUTE_MASK | MEM_MASK)) as usize == 0);

    ghost_ret = Ghost(ret);

    if page_entry.perm.user == true {
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 2u64) as usize) != 0)
            by (bit_vector);
        assert(((ret | (0x1u64 << 2u64) as usize) & 0x1 as usize) != 0 == ghost_present@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & 0x1u64 as usize) != 0 == ghost_present@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@)
            by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 0x1u64) as usize) != 0
            == ghost_write@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & (0x1u64 << 63u64) as usize) != 0
            == ghost_execute_disable@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ret & (0x1u64 << 63u64) as usize) != 0
                    == ghost_execute_disable@,
        ;
        assert(((ret | (0x1u64 << 2u64) as usize) & 0x0000_ffff_ffff_f000u64 as usize)
            == ghost_addr@) by (bit_vector)
            requires
                ghost_ret@ == ret && (ghost_ret@ & 0x0000_ffff_ffff_f000u64 as usize)
                    == ghost_addr@,
        ;
        ret = ret | (0x1u64 << 2u64) as usize;

        assert((ret & 0x1 as usize) != 0 == ghost_present@);
        assert(usize2present(ret) == page_entry.perm.present);
        assert((ret & (0x1u64 << 0x7u64) as usize) != 0 == ghost_ps@);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert((ret & (0x1u64 << 0x1u64) as usize) != 0 == ghost_write@);
        assert(usize2write(ret) == page_entry.perm.write);
        assert((ret & (0x1u64 << 63u64) as usize) != 0 == ghost_execute_disable@);
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable);
        assert((ret & (0x1u64 << 2u64) as usize) != 0);
        assert(usize2user(ret) == page_entry.perm.user);
        assert((ret & 0x0000_ffff_ffff_f000u64 as usize) == ghost_addr@);
        assert(usize2pa(ret) == page_entry.addr);

        assert((ghost_ret@ | (0x1u64 << 2u64) as usize) & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64
            << 0x1u64 | 0x1u64 << 63u64 | 0x1u64 << 2u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0)
            by (bit_vector)
            requires
                ghost_ret@ & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | PAGE_ENTRY_USER_MASK | MEM_MASK)) as usize == 0);
    } else {
        assert((ret & (0x1u64 << 2u64) as usize) == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;

        assert(usize2present(ret) == page_entry.perm.present);
        assert(usize2ps(ret) == page_entry.perm.ps);
        assert(usize2write(ret) == page_entry.perm.write);
        assert(usize2execute_disable(ret) == page_entry.perm.execute_disable);
        assert(usize2user(ret) == page_entry.perm.user);
        assert(usize2pa(ret) == page_entry.addr);

        assert(ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 | 0x1u64
            << 2u64 | 0x0000_ffff_ffff_f000u64)) as usize == 0) by (bit_vector)
            requires
                ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64
                    | 0x0000_ffff_ffff_f000u64)) as usize == 0,
        ;
        assert(ret & (!(PAGE_ENTRY_PRESENT_MASK | PAGE_ENTRY_PS_MASK | PAGE_ENTRY_WRITE_MASK
            | PAGE_ENTRY_EXECUTE_MASK | PAGE_ENTRY_USER_MASK | MEM_MASK)) as usize == 0);
    }

    assert(usize2present(ret) == page_entry.perm.present);
    assert(usize2ps(ret) == page_entry.perm.ps);
    assert(usize2write(ret) == page_entry.perm.write);
    assert(usize2execute_disable(ret) == page_entry.perm.execute_disable);
    assert(usize2user(ret) == page_entry.perm.user);
    assert(usize2pa(ret) == page_entry.addr);

    assert(ret & (0x1u64 << 5u64) as usize == 0 && ret & (0x1u64 << 6u64) as usize == 0)
        by (bit_vector)
        requires
            ret & (!(0x1u64 | 0x1u64 << 0x7u64 | 0x1u64 << 0x1u64 | 0x1u64 << 63u64 | 0x1u64 << 2u64
                | 0x0000_ffff_ffff_f000u64)) as usize == 0,
    ;
    assert(spec_usize2page_entry_status(ret).is_clear());

    return ret;
}

} // verus!
