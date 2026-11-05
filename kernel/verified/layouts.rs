//! The layout of every object the kernel keeps in a 4K page. rustc checks each at compile time, and a
//! proof that converts a page to an object can rely on it.

use vstd::prelude::*;

use crate::define::PagePerm4k;
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
