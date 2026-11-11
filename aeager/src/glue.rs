// SPDX-License-Identifier: MIT

//! The system calls the eager source makes, one item per asys wrapper. Each is trusted: what the
//! kernel does on a call is not state this crate's proof can see. Only `map_page` and `unmap_page`
//! say anything, and what they say is the trusted base: a map the kernel accepted puts a page of a
//! frame no other entry maps, readable and writable, at the address, so the permission to its bytes
//! is new; an unmap takes that permission back.
use vstd::prelude::*;
use vstd::raw_ptr::*;

use aheap::arch::*;
use asys::operation;

verus! {

/// Retypes the free page at physical `base`, inside the untyped at `untyped`, as a frame whose
/// capability goes in the empty slot `destination`. Whether the kernel accepted.
#[verifier(external_body)]
// external_body(glue): a system call, whose effect on the kernel's tables no proof here can see
pub fn retype_frame(untyped: u64, base: u64, destination: u64) -> bool
    no_unwind
{
    operation::retype_frame(untyped, base, destination) == operation::STATUS_OK
}

/// Retypes the free order-3 block at physical `base`, inside the untyped at `untyped`, as an unlinked
/// table page of `level`. Whether the kernel accepted.
#[verifier(external_body)]
// external_body(glue): a system call, whose effect on the kernel's tables no proof here can see
pub fn retype_table_page(untyped: u64, base: u64, level: u64) -> bool
    no_unwind
{
    operation::retype_table_page(untyped, base, level) == operation::STATUS_OK
}

/// Links the unlinked table page at physical `table`, inside the untyped at `untyped`, into the entry
/// at `level` that `address` names in the space at `space`. Whether the kernel accepted.
#[verifier(external_body)]
// external_body(glue): a system call that adds an empty table to the space, which no proof here can see
pub fn link(space: u64, address: usize, level: u64, untyped: u64, table: u64) -> bool
    no_unwind
{
    operation::link(space, address as u64, level, untyped, table) == operation::STATUS_OK
}

/// Maps the frame whose capability is at `frame`, which no entry maps, at the page `address` in the
/// space at `space`: on success the permission to the page's bytes, with `provenance`.
#[verifier(external_body)]
// external_body(glue): a system call; a map the kernel accepted makes the page readable and writable, which only the kernel can attest
pub fn map_page(space: u64, address: usize, frame: u64, provenance: Ghost<Provenance>) -> (r: Option<Tracked<PointsToRaw>>)
    ensures
        match r {
            Some(perm) => perm@.is_range(address as int, PAGE_BYTES as int) && perm@.provenance() == provenance@,
            None => true,
        },
    no_unwind
{
    if operation::map(space, address as u64, 1, frame, 0) == operation::STATUS_OK {
        Some(Tracked::assume_new())
    } else {
        None
    }
}

/// Unmaps the page at `address` in the space at `space`, taking the permission to its bytes. Whether
/// the kernel accepted.
#[verifier(external_body)]
// external_body(glue): a system call; the permission it takes is what makes the unmap safe, which unmap's own contract cannot state
pub fn unmap_page(space: u64, address: usize, perm: Tracked<PointsToRaw>) -> bool
    requires
        perm@.is_range(address as int, PAGE_BYTES as int),
    no_unwind
{
    // The caller gave up the permission to every byte of the page, so nothing it uses is there.
    unsafe { operation::unmap(space, address as u64, 1) }.is_ok()
}

} // verus!
