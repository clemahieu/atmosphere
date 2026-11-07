//! The layout of every object the kernel keeps in a 4K page. rustc checks each at compile time, and a
//! proof that converts a page to an object can rely on it.

use vstd::prelude::*;

use crate::capability::list::NodePage;
use crate::capability::space::{SpaceCores, SpaceRecord, TableRecord};
use crate::capability::table::{PayloadPage, TableRoot};
use crate::capability::thread::ThreadRecord;
use crate::define::PagePerm4k;
use crate::pagetable::pagemap::PageMap;
use crate::pptr::PointsTo;
use crate::process_manager::container::Container;
use crate::process_manager::endpoint::Endpoint;
use crate::process_manager::process::Process;
use crate::process_manager::thread::Thread;

/// The contents of a 4K page. The layout directive takes a name, not an array type.
pub type PageBytes = [u8; 4096];

verus! {

global layout PageBytes is size == 4096, align == 1;
global layout Container is size == 952, align == 8;
global layout Process is size == 3448, align == 8;
global layout Thread is size == 2368, align == 8;
global layout Endpoint is size == 3128, align == 8;
global layout NodePage is size == 4096, align == 8;
global layout PayloadPage is size == 4096, align == 8;
global layout TableRoot is size == 4096, align == 8;
global layout SpaceRecord is size == 72, align == 8;
global layout PageMap is size == 4096, align == 8;
global layout TableRecord is size == 56, align == 8;
global layout SpaceCores is size == 264, align == 8;
global layout ThreadRecord is size == 176, align == 8;

/// A 4K page converts to a thread and back, using these layouts and no other facts.
proof fn thread_page_round_trip(tracked page: PagePerm4k) -> (tracked ret: PagePerm4k)
    requires
        page.is_uninit(),
        page.addr() % 4096 == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(crate::pptr::page_into_typed::<Thread>(page))
}

/// A page becomes an uninitialised node page.
pub proof fn page_into_node_page(tracked page: PagePerm4k) -> (tracked ret: PointsTo<NodePage>)
    requires
        page.is_uninit(),
        page.addr() % 4096 == 0,
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
        page.addr() % 4096 == 0,
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
        page.addr() % 4096 == 0,
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
        page.addr() % 4096 == 0,
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<ThreadRecord>(page)
}

/// A page becomes an uninitialised list of a space's cores.
pub proof fn page_into_core_list(tracked page: PagePerm4k) -> (tracked ret: PointsTo<SpaceCores>)
    requires
        page.is_uninit(),
        page.addr() % 4096 == 0,
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
        page.addr() % 4096 == 0,
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
        page.addr() % 4096 == 0,
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
        vstd::layout::size_of::<NodePage>() == 4096,
        vstd::layout::size_of::<PageMap>() == 4096,
        vstd::layout::size_of::<TableRecord>() == 56,
        vstd::layout::size_of::<PageBytes>() == 4096,
{
}

/// The sizes a space block's pages need when they turn back into page permissions.
pub proof fn lemma_space_block_layouts()
    ensures
        vstd::layout::size_of::<NodePage>() == 4096,
        vstd::layout::size_of::<PageMap>() == 4096,
        vstd::layout::size_of::<SpaceRecord>() == 72,
        vstd::layout::size_of::<SpaceCores>() == 264,
        vstd::layout::size_of::<PageBytes>() == 4096,
{
}

/// What a thread's retype needs to tell its node page's permission from a table root's.
pub proof fn lemma_thread_block_layouts()
    ensures
        vstd::layout::size_of::<PageBytes>() == 4096,
        vstd::layout::size_of::<TableRoot>() == 4096,
        vstd::layout::size_of::<ThreadRecord>() == 176,
{
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

/// A free page becomes an uninitialised container.
pub proof fn page_into_container(tracked page: PagePerm4k) -> (tracked ret: PointsTo<Container>)
    requires
        page.is_uninit(),
        crate::util::page_ptr_util_u::page_ptr_valid(page.addr()),
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<Container>(page)
}

/// A dead container becomes a free page.
pub proof fn container_into_page(tracked container: PointsTo<Container>) -> (tracked ret: PagePerm4k)
    requires
        container.is_uninit(),
    ensures
        ret.addr() == container.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(container)
}

/// A free page becomes an uninitialised thread.
pub proof fn page_into_thread(tracked page: PagePerm4k) -> (tracked ret: PointsTo<Thread>)
    requires
        page.is_uninit(),
        crate::util::page_ptr_util_u::page_ptr_valid(page.addr()),
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<Thread>(page)
}

/// A dead thread becomes a free page.
pub proof fn thread_into_page(tracked thread: PointsTo<Thread>) -> (tracked ret: PagePerm4k)
    requires
        thread.is_uninit(),
    ensures
        ret.addr() == thread.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(thread)
}

/// A free page becomes an uninitialised process.
pub proof fn page_into_process(tracked page: PagePerm4k) -> (tracked ret: PointsTo<Process>)
    requires
        page.is_uninit(),
        crate::util::page_ptr_util_u::page_ptr_valid(page.addr()),
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<Process>(page)
}

/// A dead process becomes a free page.
pub proof fn process_into_page(tracked process: PointsTo<Process>) -> (tracked ret: PagePerm4k)
    requires
        process.is_uninit(),
    ensures
        ret.addr() == process.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(process)
}

/// A free page becomes an uninitialised endpoint.
pub proof fn page_into_endpoint(tracked page: PagePerm4k) -> (tracked ret: PointsTo<Endpoint>)
    requires
        page.is_uninit(),
        crate::util::page_ptr_util_u::page_ptr_valid(page.addr()),
    ensures
        ret.addr() == page.addr(),
        ret.is_uninit(),
{
    crate::pptr::page_into_typed::<Endpoint>(page)
}

/// A dead endpoint becomes a free page.
pub proof fn endpoint_into_page(tracked endpoint: PointsTo<Endpoint>) -> (tracked ret: PagePerm4k)
    requires
        endpoint.is_uninit(),
    ensures
        ret.addr() == endpoint.addr(),
        ret.is_uninit(),
{
    crate::pptr::typed_into_page(endpoint)
}

} // verus!
