// SPDX-License-Identifier: MIT

//! The layout of every object the kernel keeps in a 4K page. rustc checks each at compile time, and a
//! proof that converts a page to an object can rely on it. The thread record holds the target's trap
//! frame, arch::Registers, so its size is one per target.

use vstd::prelude::*;

use crate::capability::list::NodePage;
use crate::capability::space::{SpaceCores, SpaceRecord, TableRecord};
use crate::capability::table::{PayloadPage, TableRoot};
use crate::capability::process::ProcessRecord;
use crate::capability::thread::ThreadRecord;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::XSAVE_OFFSET;
#[cfg(verus_keep_ghost)]
use crate::define::PagePerm4k;
use crate::define::PAGE_SZ;
use crate::pagetable::pagemap::PageMap;
#[cfg(verus_keep_ghost)]
use crate::pptr::PointsTo;

/// The contents of a 4K page. The layout directive takes a name, not an array type.
pub type PageBytes = [u8; PAGE_SZ];

verus! {

global layout PageBytes is size == 4096, align == 1;
global layout NodePage is size == 4096, align == 8;
global layout PayloadPage is size == 4096, align == 8;
global layout TableRoot is size == 4096, align == 8;
global layout SpaceRecord is size == 72, align == 8;
global layout PageMap is size == 4096, align == 8;
global layout TableRecord is size == 56, align == 8;
global layout SpaceCores is size == 272, align == 8;
#[cfg(target_arch = "x86_64")]
global layout ThreadRecord is size == 224, align == 8;
#[cfg(target_arch = "aarch64")]
global layout ThreadRecord is size == 328, align == 8;
global layout ProcessRecord is size == 1, align == 1;

/// A page becomes an uninitialised node page.
pub proof fn page_into_node_page(tracked page: PagePerm4k) -> (tracked ret: PointsTo<NodePage>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<NodePage>(page)
}

/// A page becomes an uninitialised capability table root.
pub proof fn page_into_table_root(tracked page: PagePerm4k) -> (tracked ret: PointsTo<TableRoot>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<TableRoot>(page)
}

/// A page becomes an uninitialised space record.
pub proof fn page_into_space_record(tracked page: PagePerm4k) -> (tracked ret: PointsTo<SpaceRecord>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<SpaceRecord>(page)
}

/// A page becomes an uninitialised thread record, with the thread's XSAVE area after it in the same
/// page.
pub proof fn page_into_thread_record(tracked page: PagePerm4k) -> (tracked ret: PointsTo<ThreadRecord>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<ThreadRecord>(page)
}

/// A page becomes an uninitialised process record.
pub proof fn page_into_process_record(tracked page: PagePerm4k) -> (tracked ret: PointsTo<ProcessRecord>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<ProcessRecord>(page)
}

/// A page becomes an uninitialised list of a space's cores.
pub proof fn page_into_core_list(tracked page: PagePerm4k) -> (tracked ret: PointsTo<SpaceCores>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<SpaceCores>(page)
}

/// A page becomes an uninitialised table record.
pub proof fn page_into_table_record(tracked page: PagePerm4k) -> (tracked ret: PointsTo<TableRecord>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<TableRecord>(page)
}

/// A page becomes an uninitialised page of capability payloads.
pub proof fn page_into_payload_page(tracked page: PagePerm4k) -> (tracked ret: PointsTo<PayloadPage>)
    requires
        page.is_uninit(),
        page.addr() % PAGE_SZ == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<PayloadPage>(page)
}

/// A node page with no live node becomes a free page.
pub proof fn node_page_into_page(tracked nodes: PointsTo<NodePage>) -> (tracked ret: PagePerm4k)
    requires
        nodes.is_uninit(),
    ensures
        ret.addr() == nodes.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(nodes)
}

/// What a proof elsewhere needs to tell a node page's permission from those of the other pages of a
/// table page's block.
pub proof fn lemma_table_block_layouts()
    ensures
        vstd::layout::size_of::<NodePage>() == PAGE_SZ,
        vstd::layout::size_of::<PageMap>() == PAGE_SZ,
        vstd::layout::size_of::<TableRecord>() == 56,
        vstd::layout::size_of::<PageBytes>() == PAGE_SZ,
{
}

/// The sizes a space block's pages need when they turn back into page permissions.
pub proof fn lemma_space_block_layouts()
    ensures
        vstd::layout::size_of::<NodePage>() == PAGE_SZ,
        vstd::layout::size_of::<PageMap>() == PAGE_SZ,
        vstd::layout::size_of::<SpaceRecord>() == 72,
        vstd::layout::size_of::<SpaceCores>() == 272,
        vstd::layout::size_of::<PageBytes>() == PAGE_SZ,
{
}

/// The sizes a process block's pages need when they turn back into page permissions.
pub proof fn lemma_process_block_layouts()
    ensures
        vstd::layout::size_of::<NodePage>() == PAGE_SZ,
        vstd::layout::size_of::<TableRoot>() == PAGE_SZ,
        vstd::layout::size_of::<ProcessRecord>() == 1,
        vstd::layout::size_of::<PageMap>() == PAGE_SZ,
        vstd::layout::size_of::<SpaceRecord>() == 72,
        vstd::layout::size_of::<SpaceCores>() == 272,
        vstd::layout::size_of::<PageBytes>() == PAGE_SZ,
{
}

/// What a thread's retype needs to tell its node page's permission from a table root's.
pub proof fn lemma_thread_block_layouts()
    ensures
        vstd::layout::size_of::<PageBytes>() == PAGE_SZ,
        vstd::layout::size_of::<TableRoot>() == PAGE_SZ,
        vstd::layout::size_of::<ThreadRecord>() <= XSAVE_OFFSET,
{
}

/// A freed thread's record, with the XSAVE area after it, becomes a free page.
pub proof fn thread_record_into_page(tracked record: PointsTo<ThreadRecord>) -> (tracked ret: PagePerm4k)
    requires
        record.is_uninit(),
    ensures
        ret.addr() == record.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(record)
}

/// A freed process's table root becomes a free page.
pub proof fn table_root_into_page(tracked root: PointsTo<TableRoot>) -> (tracked ret: PagePerm4k)
    requires
        root.is_uninit(),
    ensures
        ret.addr() == root.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(root)
}

/// A freed process's record becomes a free page.
pub proof fn process_record_into_page(tracked record: PointsTo<ProcessRecord>) -> (tracked ret: PagePerm4k)
    requires
        record.is_uninit(),
    ensures
        ret.addr() == record.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(record)
}

/// A freed space's record becomes a free page.
pub proof fn space_record_into_page(tracked record: PointsTo<SpaceRecord>) -> (tracked ret: PagePerm4k)
    requires
        record.is_uninit(),
    ensures
        ret.addr() == record.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(record)
}

/// A freed space's list of cores becomes a free page.
pub proof fn core_list_into_page(tracked list: PointsTo<SpaceCores>) -> (tracked ret: PagePerm4k)
    requires
        list.is_uninit(),
    ensures
        ret.addr() == list.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(list)
}

/// An emptied table becomes a free page.
pub proof fn page_map_into_page(tracked map: PointsTo<PageMap>) -> (tracked ret: PagePerm4k)
    requires
        map.is_uninit(),
    ensures
        ret.addr() == map.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(map)
}

/// A table page's record becomes a free page.
pub proof fn table_record_into_page(tracked record: PointsTo<TableRecord>) -> (tracked ret: PagePerm4k)
    requires
        record.is_uninit(),
    ensures
        ret.addr() == record.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(record)
}

/// A dead leaf's payload page becomes a free page.
pub proof fn payload_page_into_page(tracked payloads: PointsTo<PayloadPage>) -> (tracked ret: PagePerm4k)
    requires
        payloads.is_uninit(),
    ensures
        ret.addr() == payloads.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(payloads)
}

} // verus!
