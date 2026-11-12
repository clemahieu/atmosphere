// SPDX-License-Identifier: MIT

//! The witnesses of ten uses a process exists for. A creator can build a process that holds a
//! capability it chose and has a thread bound to it: from the state boot leaves, the root gives itself a
//! leaf, retypes a process and a thread bound to it, retypes a leaf into the new process's table and
//! derives an untyped into it. The root can share memory between processes it built: it retypes two
//! processes, gives each space the tables of one path, retypes a frame and maps it at that path in
//! both. It can take that memory back: one revoke of the frame capability unmaps it from both. And the
//! root can map memory into its own space: at a level 4 entry outside the kernel slots and the image's,
//! it gives its space the tables of one path, retypes a frame and maps it there. A process the root
//! built can bind a device to a device space: the root records the device, retypes a device space,
//! moves both capabilities into the process's table, and the process binds the one to the other.
//! That process can hand the device to a second device space: the root gives it the second space's
//! capability, and the process unbinds the device, lets its IOMMU acknowledge, and binds it again.
//! And the root can give back 2M of memory and take it again: it retypes a 2M frame, deletes its
//! capability, frees the region through a retype under its untyped, and retypes the frame again.
//! It can take back a device space nothing holds: it records a device, retypes a device space, links a
//! table under the space's root, binds the device and unbinds it, and deletes the space's capability;
//! a retype under its untyped then slices the space, waits until every core and IOMMU acknowledges,
//! frees the block, and a device space is retyped there again.
//! A creator can take back what it gave a process it controls: it claims a capability out of the
//! process's table into its own. And it can set and read the registers of a thread it has not started,
//! through the thread's control capability.
//! Beside those, boot can start the root: core 0 loads the root's space and enters its thread.
//! Every step is proven to succeed. Only Verus compiles this module, so no image contains it.
//! See design/process-holds-capabilities/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_kernel::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::decompose::*;
use crate::capability::delete::*;
use crate::capability::derive::*;
use crate::capability::destroy::*;
use crate::capability::device::{
    binding_device, binding_node, bound_record, device_of, device_payload, lemma_device_object, devices_wf, DeviceInfo, IOMMU_DEVICES, MAX_DEVICES,
};
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::position::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::reclaim::*;
use crate::capability::reclaim_process::*;
use crate::capability::reclaim_thread::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::revoke::*;
use crate::capability::space::*;
use crate::capability::steps::*;
use crate::capability::switch::*;
use crate::arch::{user_frame, user_rip, Registers};
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;

/// The index of the root's table the new process's capability goes in: slot 1 of root entry 2, the
/// leaf the witness gives the root first.
pub const WITNESS_PROCESS_SLOT: usize = 257;

/// The index of the root's table the new thread's capability goes in: slot 2 of root entry 2.
pub const WITNESS_THREAD_SLOT: usize = 258;

/// The index of the root's table the second process's capability goes in, when the root maps one frame
/// into two processes: slot 2 of root entry 2.
pub const WITNESS_SECOND_PROCESS_SLOT: usize = 258;

/// The index of the root's table the shared frame's capability goes in: slot 3 of root entry 2.
pub const WITNESS_FRAME_SLOT: usize = 259;

/// The index of the new process's table the derived capability goes in: slot 1 of its root entry 0.
pub const WITNESS_CHILD_SLOT: usize = 1;

/// The index of the root's table a capability claimed out of the new process's table goes in: slot 3
/// of root entry 2.
pub const WITNESS_CLAIM_SLOT: usize = 259;

/// The index of the root's table a device space's capability goes in, when a process binds a device:
/// slot 2 of root entry 2.
pub const WITNESS_SPACE_SLOT: usize = 258;

/// The index of the root's table the device's capability goes in, when a process binds a device: slot 3
/// of root entry 2.
pub const WITNESS_DEVICE_SLOT: usize = 259;

/// The index of the new process's table the device space's capability is moved to: slot 1 of its root
/// entry 0.
pub const WITNESS_BOUND_SPACE_SLOT: usize = 1;

/// The index of the new process's table the device's capability is moved to: slot 2 of its root entry 0.
pub const WITNESS_BOUND_DEVICE_SLOT: usize = 2;

/// The index of the new process's table a second device space's capability is moved to, when the
/// process moves its device from one space to another: slot 3 of its root entry 0.
pub const WITNESS_SECOND_SPACE_SLOT: usize = 3;

/// The index of the new process's table its own thread's capability is moved to, when its creator hands
/// the process itself: slot 2 of its root entry 0.
pub const WITNESS_SEALED_THREAD_SLOT: usize = 2;

/// The index of the new process's table its own capability is moved to, when its creator hands the
/// process itself: slot 3 of its root entry 0.
pub const WITNESS_SEALED_PROCESS_SLOT: usize = 3;

/// The index of the root's table a 2M frame's capability goes in, when the root frees one and types it
/// again: slot 1 of root entry 2.
pub const WITNESS_LARGE_FRAME_SLOT: usize = 257;

/// What a 2M retype naming the block at page has left to zero: the pages past the cursor while its
/// region is being zeroed, and the whole region otherwise. A step that says Again lowers it.
pub open spec fn witness_zero_left(k: CapKernel, page: usize) -> int {
    if k.zeroing.active(Large::Two, page / PAGES_PER_2M) && k.zeroing.cursor@[page as int] < PAGES_PER_2M {
        PAGES_PER_2M - k.zeroing.cursor@[page as int]
    } else {
        PAGES_PER_2M as int
    }
}

/// The 64 order-3 blocks from the jb-th past cursor, each free, are a whole 2M region when the first is
/// 2M aligned: every page of it is free, and none is in a typed large block, since a large block holding
/// any of them holds the first.
proof fn lemma_free_2m(k: CapKernel, process: usize, cursor: usize, jb: int, big: usize)
    requires
        0 <= jb,
        cursor % PROCESS_BYTES == 0,
        cursor + (jb + 64) * PROCESS_BYTES <= NODE_SPACE,
        forall|j: int| jb <= j < jb + 64 ==> #[trigger] k.root_table_block(process, cursor_block(cursor, j)),
        big == cursor_block(cursor, jb),
        big as int % block_bytes(9) == 0,
    ensures
        big / PAGE_SZ / PAGES_PER_2M < NUM_2M,
        (big / PAGE_SZ) as int == (big / PAGE_SZ / PAGES_PER_2M) * PAGES_PER_2M,
        k.blocks.large_free(Large::Two, (big / PAGE_SZ / PAGES_PER_2M) as int),
{
    lemma2_to64();
    let g = (big / PAGE_SZ) as int;
    let r = g / PAGES_PER_2M as int;
    assert(block_bytes(9) == PAGES_PER_2M * PAGE_SZ);
    lemma_fundamental_div_mod(big as int, block_bytes(9));
    let q = big as int / block_bytes(9);
    assert(big == (q * PAGES_PER_2M) * PAGE_SZ) by (nonlinear_arith)
        requires
            big == block_bytes(9) * q + big as int % block_bytes(9),
            big as int % block_bytes(9) == 0,
            block_bytes(9) == PAGES_PER_2M * PAGE_SZ,
    ;
    lemma_fundamental_div_mod_converse(big as int, PAGE_SZ as int, q * PAGES_PER_2M, 0);
    assert(g == q * PAGES_PER_2M);
    lemma_fundamental_div_mod_converse(g, PAGES_PER_2M as int, q, 0);
    assert(r == q);
    assert(jb * PROCESS_BYTES <= (jb + 64) * PROCESS_BYTES) by (nonlinear_arith);
    lemma_cursor_block(cursor, jb);
    assert(k.root_table_block(process, cursor_block(cursor, jb)));
    assert(!k.blocks.covered(g));
    assert forall|i: int| r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M implies {
        &&& #[trigger] k.blocks.pages@[i].kind is Free
        &&& !k.blocks.covered(i)
    } by {
        lemma_fundamental_div_mod(i - g, 8);
        lemma_mod_bound(i - g, 8);
        let m = (i - g) / 8;
        let o = (i - g) % 8;
        assert(0 <= m < 64 && 0 <= o < 8);
        let cb = cursor_block(cursor, jb + m);
        assert((jb + m) * PROCESS_BYTES <= (jb + 64) * PROCESS_BYTES) by (nonlinear_arith)
            requires
                m < 64,
        ;
        lemma_cursor_block(cursor, jb + m);
        assert(k.root_table_block(process, cb));
        assert(cb / PAGE_SZ == g + 8 * m);
        assert(k.blocks.pages@[cb / PAGE_SZ + o].kind is Free);
        lemma_fundamental_div_mod_converse(i, PAGES_PER_2M as int, r, i - g);
        assert(region_2m(i) == r && region_2m(g) == r);
        lemma_div_denominator(i, PAGES_PER_2M as int, PAGES_PER_2M as int);
        lemma_div_denominator(g, PAGES_PER_2M as int, PAGES_PER_2M as int);
        assert(region_1g(i) == region_1g(g));
    }
    let cl = cursor_block(cursor, jb + 63);
    assert((jb + 63) * PROCESS_BYTES <= (jb + 64) * PROCESS_BYTES) by (nonlinear_arith);
    lemma_cursor_block(cursor, jb + 63);
    assert(k.root_table_block(process, cl));
    assert(cl / PAGE_SZ == g + 8 * 63);
    assert(g + PAGES_PER_2M <= NUM_PAGES);
}

/// After a 2M retype into index i of the table at root, whose node n held nothing, the slot holds the
/// frame's capability, one deeper than the untyped, and the capability has no child.
proof fn lemma_large_retyped_slot(pre: CapKernel, post: CapKernel, root: usize, from: usize, i: usize, n: usize, big: usize)
    requires
        CapKernel::large_frame_retyped(pre, post, root, from, i, big, 9),
        post.wf(),
        pre.tables.has_slot(&pre.list, root, i),
        pre.tables.node_of(root, i) == n,
        !pre.list.nodes@[n as int].live,
        n % PAGE_SZ != 0,
    ensures
        post.slot_holds(root, i, n, large_frame_of(big, 9)),
        post.list.childless(n),
        post.list.nodes@[n as int].depth > 0,
{
    let parent = pre.tables.node_of(root, from);
    lemma_slot_kept_two(pre, post, root, i, n, n);
    assert(post.view().holds(root, n));
    assert(post.is_cap(n));
    pre.lemma_slot(root, i);
    pre.lemma_slot_bound(n);
    assert(pre.is_cap(parent));
    assert(parent != n);
    lemma_added_children(pre.list, post.list, n, parent);
    if !post.list.childless(n) {
        post.list.lemma_next_is_child(n);
    }
}

/// The tables the runs need are never fewer than none.
proof fn lemma_tables_bound_nonneg(runs: Seq<ImageRun>)
    ensures
        0 <= image_tables_bound(runs),
    decreases runs.len(),
{
    if runs.len() > 0 {
        lemma_tables_bound_nonneg(runs.drop_last());
        let run = runs.last();
        let v = run.virt as int;
        lemma_div_is_ordered(v - 1, v + run.pages - 1, PAGES_PER_2M as int);
        lemma_fundamental_div_mod(v, PAGES_PER_2M as int);
        lemma_fundamental_div_mod(v - 1, PAGES_PER_2M as int);
        lemma_mod_bound(v, PAGES_PER_2M as int);
        lemma_mod_bound(v - 1, PAGES_PER_2M as int);
        assert(run_regions(run) >= 0);
    }
}

/// Page k of the order-3 block at b is its k-th page, in the 2M and 1G regions its first page is in,
/// and at an even k starts an order-1 block; the next order-3 block starts 8 pages on.
proof fn lemma_block_page(b: usize, k: int)
    requires
        b % PROCESS_BYTES == 0,
        0 <= k < 8,
    ensures
        (b + k * PAGE_SZ) / PAGE_SZ as int == b / PAGE_SZ + k,
        (b + k * PAGE_SZ) % PAGE_SZ as int == 0,
        (b + PROCESS_BYTES) / PAGE_SZ as int == b / PAGE_SZ + 8,
        region_2m(b / PAGE_SZ + k) == region_2m((b / PAGE_SZ) as int),
        region_1g(b / PAGE_SZ + k) == region_1g((b / PAGE_SZ) as int),
        k % 2 == 0 ==> (b + k * PAGE_SZ) % (2 * PAGE_SZ) as int == 0,
{
    // The order-3 blocks in a 2M and in a 1G region.
    let in_2m = PAGES_PER_2M as int / 8;
    let in_1g = PAGES_PER_1G as int / 8;
    assert(PAGES_PER_2M as int == 8 * in_2m && PAGES_PER_1G as int == 8 * in_1g);
    let q = b as int / PROCESS_BYTES as int;
    lemma_fundamental_div_mod(b as int, PROCESS_BYTES as int);
    assert(b == PROCESS_BYTES as int * q);
    lemma_fundamental_div_mod_converse(b + k * PAGE_SZ, PAGE_SZ as int, 8 * q + k, 0);
    lemma_fundamental_div_mod_converse(b as int, PAGE_SZ as int, 8 * q, 0);
    lemma_fundamental_div_mod_converse(b + PROCESS_BYTES, PAGE_SZ as int, 8 * q + 8, 0);
    lemma_fundamental_div_mod(q, in_2m);
    lemma_mod_pos_bound(q, in_2m);
    let d2 = q / in_2m;
    let r2 = q % in_2m;
    assert(8 * q == d2 * PAGES_PER_2M as int + 8 * r2) by (nonlinear_arith)
        requires
            q == in_2m * d2 + r2,
            PAGES_PER_2M as int == 8 * in_2m,
    ;
    lemma_fundamental_div_mod_converse(8 * q + k, PAGES_PER_2M as int, q / in_2m, 8 * (q % in_2m) + k);
    lemma_fundamental_div_mod_converse(8 * q, PAGES_PER_2M as int, q / in_2m, 8 * (q % in_2m));
    lemma_fundamental_div_mod(q, in_1g);
    lemma_mod_pos_bound(q, in_1g);
    let d1 = q / in_1g;
    let r1 = q % in_1g;
    assert(8 * q == d1 * PAGES_PER_1G as int + 8 * r1) by (nonlinear_arith)
        requires
            q == in_1g * d1 + r1,
            PAGES_PER_1G as int == 8 * in_1g,
    ;
    lemma_fundamental_div_mod_converse(8 * q + k, PAGES_PER_1G as int, q / in_1g, 8 * (q % in_1g) + k);
    lemma_fundamental_div_mod_converse(8 * q, PAGES_PER_1G as int, q / in_1g, 8 * (q % in_1g));
    if k % 2 == 0 {
        lemma_fundamental_div_mod(k, 2);
        lemma_fundamental_div_mod_converse(b + k * PAGE_SZ, (2 * PAGE_SZ) as int, 4 * q + k / 2, 0);
    }
}

/// An order-3 block aligned from b, and its first page, which an order-1 block starts at.
proof fn lemma_aligned(b: usize)
    requires
        b % PROCESS_BYTES == 0,
    ensures
        b % PAGE_SZ == 0,
        b % (2 * PAGE_SZ) as usize == 0,
{
    lemma_fundamental_div_mod(b as int, PROCESS_BYTES as int);
    lemma_fundamental_div_mod_converse(b as int, PAGE_SZ as int, 8 * (b as int / PROCESS_BYTES as int), 0);
    lemma_fundamental_div_mod_converse(b as int, (2 * PAGE_SZ) as int, 4 * (b as int / PROCESS_BYTES as int), 0);
}

/// The j-th order-3 block from b is j blocks on, aligned, and starts 8j pages on.
proof fn lemma_cursor_block(b: usize, j: int)
    requires
        b % PROCESS_BYTES == 0,
        0 <= j,
        b + j * PROCESS_BYTES <= NODE_SPACE,
    ensures
        cursor_block(b, j) == b + j * PROCESS_BYTES,
        cursor_block(b, j) % PROCESS_BYTES == 0,
        cursor_block(b, j) / PAGE_SZ == b / PAGE_SZ + 8 * j,
{
    let q = b as int / PROCESS_BYTES as int;
    lemma_fundamental_div_mod(b as int, PROCESS_BYTES as int);
    assert(b + j * PROCESS_BYTES == (q + j) * PROCESS_BYTES) by (nonlinear_arith)
        requires
            b == PROCESS_BYTES as int * q,
    ;
    lemma_fundamental_div_mod_converse(b + j * PROCESS_BYTES, PROCESS_BYTES as int, q + j, 0);
    lemma_fundamental_div_mod_converse(b + j * PROCESS_BYTES, PAGE_SZ as int, 8 * q + 8 * j, 0);
    lemma_fundamental_div_mod_converse(b as int, PAGE_SZ as int, 8 * q, 0);
}

/// The process at p is sealed when its block's two references are one capability, pn, and one bound
/// thread, x, whose block's one reference is its capability, tn, and both lie in p's table: a second
/// holder of either would be a third reference, or a second one.
proof fn lemma_sealed_held_once(k: CapKernel, p: usize, pn: usize, x: usize, tn: usize)
    requires
        k.wf(),
        k.is_cap(pn),
        k.payload_of(pn).kind is Process,
        k.payload_of(pn).base == p,
        k.tables.owner@[page_of(pn)].0 == p,
        k.is_cap(tn),
        k.payload_of(tn).kind is Thread,
        k.payload_of(tn).base == x,
        k.tables.owner@[page_of(tn)].0 == p,
        bound_threads(&k.list, &k.tables).contains_key(x),
        bound_threads(&k.list, &k.tables)[x] == p,
        block_refs(&k.blocks, BlockRef::Small(p / PAGE_SZ)) == 2,
        block_refs(&k.blocks, BlockRef::Small(x / PAGE_SZ)) == 1,
    ensures
        k.sealed(p),
{
    broadcast use vstd::set::lemma_set_remove_len, vstd::set::lemma_set_remove_different;
    k.lemma_bound_thread(x, p);
    reveal(CapKernel::wf);
    assert(process_wf(&k.processes, &k.blocks, p));
    assert(thread_wf(&k.list, &k.threads, &k.blocks, x));
    let ph = k.processes.holders@[p];
    let pb = k.processes.bound@[p];
    let th = k.threads.holders@[x];
    assert(ph.contains(pn));
    assert(th.contains(tn));
    assert(ph.len() + pb.len() == 2);
    assert(th.len() == 1);
    assert(pb.len() >= 1) by {
        assert(pb.len() == pb.remove(x).len() + 1);
    }
    assert forall|n: usize| #[trigger] ph.contains(n) implies n == pn by {
        if n != pn {
            assert(ph.remove(pn).contains(n));
            assert(ph.remove(pn).len() == ph.remove(pn).remove(n).len() + 1);
            assert(ph.len() == ph.remove(pn).len() + 1);
        }
    }
    assert(pb.len() == 1) by {
        assert(ph.len() == ph.remove(pn).len() + 1);
    }
    assert forall|y: usize| #[trigger] pb.contains(y) implies y == x by {
        if y != x {
            assert(pb.remove(x).contains(y));
            assert(pb.remove(x).len() == pb.remove(x).remove(y).len() + 1);
            assert(pb.len() == pb.remove(x).len() + 1);
        }
    }
    assert forall|n: usize| #[trigger] th.contains(n) implies n == tn by {
        if n != tn {
            assert(th.remove(tn).contains(n));
            assert(th.remove(tn).len() == th.remove(tn).remove(n).len() + 1);
            assert(th.len() == th.remove(tn).len() + 1);
        }
    }
    k.lemma_sealed_by_holders(p);
}

/// Process p has a record, and it is live.
pub open spec fn witness_alive(k: CapKernel, p: usize) -> bool {
    &&& k.processes.records@.contains_key(p)
    &&& !k.processes.records@[p].value().dead
}

/// Index i of the table at root holds capability n, saying c, at depth d.
pub open spec fn witness_slot(k: CapKernel, root: usize, i: usize, n: usize, c: Payload, d: usize) -> bool {
    &&& k.slot_holds(root, i, n, c)
    &&& k.list.nodes@[n as int].depth == d
}

/// Index i of the table at root is a slot, of node n, and holds nothing.
pub open spec fn witness_empty(k: CapKernel, root: usize, i: usize, n: usize) -> bool {
    &&& k.tables.has_slot(&k.list, root, i)
    &&& k.tables.node_of(root, i) == n
    &&& !k.list.nodes@[n as int].live
}

/// The root at process: its table, its live record, and its first untyped, first, at ROOT_UNTYPED_SLOT,
/// node u, at depth 1, with the retype right.
pub open spec fn witness_root(k: CapKernel, process: usize, u: usize, first: Payload) -> bool {
    &&& k.tables.roots@.contains_key(process)
    &&& witness_alive(k, process)
    &&& witness_slot(k, process, ROOT_UNTYPED_SLOT, u, first, 1)
    &&& first.kind is Untyped
    &&& first.rights & right_bit(Right::Retype) != 0
}

/// Frame capability n's children are a and b, neither has a child, and every mapping record that names
/// page g is a child of n.
pub open spec fn frame_shared(k: CapKernel, n: usize, a: usize, b: usize, g: usize) -> bool {
    &&& forall|y: usize| #[trigger] k.list.is_child(n, y) ==> y == a || y == b
    &&& forall|z: usize| !#[trigger] k.list.is_child(a, z)
    &&& forall|z: usize| !#[trigger] k.list.is_child(b, z)
    &&& forall|m: usize| #[trigger] k.mappings@.contains_key(m) && record_pages(k.mappings@[m]).contains(g)
        ==> k.list.is_child(n, m)
}

/// The order-3 block at b lies in first and is free.
pub open spec fn witness_block(k: CapKernel, b: usize, first: Payload) -> bool {
    &&& block_within(b, 3, first)
    &&& k.blocks.tracks_addr_run(b, 8)
    &&& !k.blocks.covered((b / PAGE_SZ) as int)
    &&& forall|j: int| 0 <= j < 8 ==> #[trigger] k.blocks.pages@[b / PAGE_SZ + j].kind is Free
}

/// The order-3 blocks lo up to hi from b lie in first and are free.
pub open spec fn witness_run(k: CapKernel, b: usize, lo: int, hi: int, first: Payload) -> bool {
    forall|j: int| lo <= j < hi ==> #[trigger] witness_block(k, cursor_block(b, j), first)
}

/// What the teardown of witness_dead_table_page_freed needs of the state map_large leaves, with the
/// root's leaf at the 64th order-3 block past `big`, the level 3 table at the 65th and the level 2
/// table at the 66th: the root and its untyped u, first, which still holds the leaf; the level 2 table
/// live and unlinkable under u, its parent entry 0 of the level 3 table, its entry 0 naming the level 1
/// table, its entry 1 the 2M frame at `big`, which a mapping record names, and every other entry
/// empty; and no flush yet.
pub open spec fn dead_table_ready(k: CapKernel, process: usize, u: usize, first: Payload, big: usize) -> bool {
    let lb = (big + 64 * PROCESS_BYTES) as usize;
    let c0 = (big + 65 * PROCESS_BYTES) as usize;
    let c1 = (big + 66 * PROCESS_BYTES) as usize;
    let a = tree_of(&k.table_pages, &k.spaces);
    &&& k.wf()
    &&& big % PROCESS_BYTES == 0
    &&& big + 68 * PROCESS_BYTES <= NODE_SPACE
    &&& (c1 / PAGE_SZ) as int == big / PAGE_SZ + PAGES_PER_2M + 16
    &&& k.flush_epoch == 0
    &&& k.tables.roots@.contains_key(process)
    &&& k.root_live(process)
    &&& k.tables.node_of(process, ROOT_UNTYPED_SLOT) == u
    &&& k.is_cap(u) && k.payload_of(u) == first
    &&& k.list.nodes@[lb as int].live && k.list.parent@[lb] == u
    &&& k.can_unlink_table(process, ROOT_UNTYPED_SLOT, c1)
    &&& !k.tables.owner@.contains_key(c1)
    &&& u != c1 && u < NODE_SPACE
    &&& k.tables.owner@.contains_key(page_of(lb))
    &&& k.blocks.tracks((c1 / PAGE_SZ) as int)
    &&& a.is_page(c1) && a.record(c1).level == 2
    &&& a.record(c1).parent == Some(TableParent { table: c0, entry: 0 })
    &&& a.names_child(c0, 0) && a.names_child(c1, 0)
    &&& a.entry(c1, 1).perm.present && a.entry(c1, 1).perm.ps
    &&& a.entry(c1, 1).addr == big
    &&& forall|i: usize| 1 < i < ENTRIES ==> #[trigger] a.entry(c1, i).is_empty()
    &&& k.mappings@.contains_key(mapping_node(c1, 1))
}

/// A free block stays free across a step that kept the regions and every page's kind outside lo up to
/// hi, which the block lies outside.
proof fn lemma_witness_block_kept(pre: CapKernel, post: CapKernel, b: usize, first: Payload, lo: int, hi: int)
    requires
        witness_block(pre, b, first),
        post.blocks.regions_2m@ == pre.blocks.regions_2m@,
        post.blocks.regions_1g@ == pre.blocks.regions_1g@,
        forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(lo <= j < hi)
            ==> post.blocks.pages@[j].kind == pre.blocks.pages@[j].kind,
        b / PAGE_SZ + 8 <= lo || hi <= b / PAGE_SZ,
    ensures
        witness_block(post, b, first),
{
    assert forall|j: int| 0 <= j < 8 implies #[trigger] post.blocks.pages@[b / PAGE_SZ + j].kind is Free by {
        assert(pre.blocks.pages@[b / PAGE_SZ + j].kind is Free);
    }
}

/// So does a run of them, all on one side of lo up to hi.
proof fn lemma_run_kept(pre: CapKernel, post: CapKernel, b: usize, jlo: int, jhi: int, first: Payload, lo: int, hi: int)
    requires
        witness_run(pre, b, jlo, jhi, first),
        b % PROCESS_BYTES == 0,
        0 <= jlo,
        b + jhi * PROCESS_BYTES <= NODE_SPACE,
        post.blocks.regions_2m@ == pre.blocks.regions_2m@,
        post.blocks.regions_1g@ == pre.blocks.regions_1g@,
        forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(lo <= j < hi)
            ==> post.blocks.pages@[j].kind == pre.blocks.pages@[j].kind,
        hi <= b / PAGE_SZ + 8 * jlo || b / PAGE_SZ + 8 * jhi <= lo,
    ensures
        witness_run(post, b, jlo, jhi, first),
{
    assert forall|j: int| jlo <= j < jhi implies #[trigger] witness_block(post, cursor_block(b, j), first) by {
        assert(j * PROCESS_BYTES <= jhi * PROCESS_BYTES) by (nonlinear_arith)
            requires
                j <= jhi,
        ;
        lemma_cursor_block(b, j);
        lemma_witness_block_kept(pre, post, cursor_block(b, j), first, lo, hi);
    }
}

/// A slot's capability stays across a step that kept the capability tables, the capabilities and the
/// list's live nodes.
proof fn lemma_witness_slot_kept(pre: CapKernel, post: CapKernel, root: usize, i: usize, n: usize, c: Payload, d: usize)
    requires
        pre.wf(),
        post.tables == pre.tables,
        forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
        nodes_kept(pre.list, post.list),
        witness_slot(pre, root, i, n, c, d),
    ensures
        witness_slot(post, root, i, n, c, d),
{
    pre.lemma_slot(root, i);
    pre.lemma_slot_bound(n);
    assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] pre.list.nodes@[j].live implies post.list.nodes@[j].live by {}
    CapKernel::lemma_slot_stays(pre, post, root, i);
}

/// An empty slot stays empty across a step that kept the capability tables, the list's live nodes and
/// the liveness of every node that is not a page's first.
proof fn lemma_witness_empty_kept(pre: CapKernel, post: CapKernel, root: usize, i: usize, n: usize)
    requires
        pre.wf(),
        post.tables == pre.tables,
        nodes_kept(pre.list, post.list),
        forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
            ==> post.list.nodes@[j].live == pre.list.nodes@[j].live,
        witness_empty(pre, root, i, n),
    ensures
        witness_empty(post, root, i, n),
{
    pre.lemma_slot(root, i);
    pre.lemma_slot_bound(n);
    assert forall|j: int| 0 <= j < NODE_SPACE && #[trigger] pre.list.nodes@[j].live implies post.list.nodes@[j].live by {}
    CapKernel::lemma_slot_stays(pre, post, root, i);
    assert(post.list.nodes@[n as int].live == pre.list.nodes@[n as int].live);
}

/// A map adds one node, a mapping, and keeps every other: so it keeps the capabilities and the list's
/// live nodes.
proof fn lemma_map_kept(pre: CapKernel, post: CapKernel, node: usize, f: usize)
    requires
        pre.wf(),
        post.tables == pre.tables,
        !pre.list.nodes@[node as int].live,
        post.list.nodes@[node as int].kind is Mapping,
        post.list.parent@ == pre.list.parent@.insert(node, f),
        post.list.seq@[0] == pre.list.seq@[0],
        forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
            &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
            &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            &&& post.list.nodes@[i].depth == pre.list.nodes@[i].depth
        },
    ensures
        forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
        nodes_kept(pre.list, post.list),
{
    assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
        if pre.tables.owner@.contains_key(page_of(x)) && x % PAGE_SZ < NODES_PER_PAGE && x != node {
            pre.lemma_slot_bound(x);
            assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
        }
    }
    assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && pre.list.nodes@[j].live implies {
        &&& post.list.nodes@[j].live
        &&& post.list.nodes@[j].depth == pre.list.nodes@[j].depth
        &&& post.list.parent@[j as usize] == pre.list.parent@[j as usize]
    } by {
        assert(j != node);
    }
}

/// A new root, at an address no table had, keeps every step of the tables there were.
proof fn lemma_new_root_steps_kept(a: TableTree, b: TableTree, q: usize)
    requires
        b.maps == a.maps,
        b.records == a.records,
        b.roots == a.roots.insert(q, b.roots[q]),
        b.space_records == a.space_records.insert(q, b.space_records[q]),
        !a.is_table(q),
    ensures
        steps_kept(a, b),
{
    assert forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) implies {
        &&& b.is_page(t) == a.is_page(t)
        &&& b.is_root(t) == a.is_root(t)
        &&& b.record(t).level == a.record(t).level
        &&& a.is_root(t) ==> b.space_records[t].value().kind == a.space_records[t].value().kind
    } by {
        assert(t != q);
    }
    assert forall|t: usize, i: usize| #![trigger step(a, t, i)] step(a, t, i) is Some implies b.entry(t, i) == a.entry(t, i) by {
        assert(a.is_table(t));
        assert(t != q);
    }
}

/// A listed node is in the node space and live.
proof fn lemma_listed_live(t: Tree, x: usize)
    requires
        t.wf(),
        t.seq@.contains(x),
    ensures
        x < NODE_SPACE,
        t.nodes@[x as int].live,
{
    let k = choose|k: int| 0 <= k < t.seq@.len() && t.seq@[k] == x;
    t.lemma_link(k);
}

/// Across a step that keeps the first node, the liveness of every node but a and b, and the parent of
/// every other node that had one, a child of c after the step that is neither a nor b was one before:
/// it is live, so it was live and listed before, and not first, so it had its parent then.
proof fn lemma_children_kept(pre: Tree, post: Tree, a: usize, b: usize, c: usize)
    requires
        pre.wf(),
        post.wf(),
        post.seq@[0] == pre.seq@[0],
        forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != a && i != b
            ==> post.nodes@[i].live == pre.nodes@[i].live,
        forall|x: usize| x != a && x != b && #[trigger] pre.parent@.contains_key(x) ==> post.parent@[x] == pre.parent@[x],
    ensures
        forall|x: usize| #[trigger] post.is_child(c, x) && x != a && x != b ==> pre.is_child(c, x),
{
    assert forall|x: usize| #[trigger] post.is_child(c, x) && x != a && x != b implies pre.is_child(c, x) by {
        lemma_listed_live(post, x);
        assert(post.nodes@[x as int].live == pre.nodes@[x as int].live);
        assert(has(pre.seq@, x));
        lemma_has(pre.seq@, x);
        let k = choose|k: int| 0 <= k < pre.seq@.len() && pre.seq@[k] == x;
        assert(k != 0);
        assert(pre.parent@.contains_key(pre.seq@[k]));
    }
}

/// Across a step that adds n, dead before, under p and changes no other node's liveness or parent,
/// n has no child after it, and every other child after it was the same child before: a live node
/// past the first has a parent, so it was not the first before either.
proof fn lemma_added_children(pre: Tree, post: Tree, n: usize, p: usize)
    requires
        pre.wf(),
        post.wf(),
        n < NODE_SPACE,
        !pre.nodes@[n as int].live,
        p != n,
        post.parent@ == pre.parent@.insert(n, p),
        forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != n
            ==> post.nodes@[i].live == pre.nodes@[i].live,
    ensures
        forall|x: usize| !#[trigger] post.is_child(n, x),
        forall|c: usize, x: usize| #[trigger] post.is_child(c, x) && x != n ==> pre.is_child(c, x),
{
    assert forall|c: usize, x: usize| #[trigger] post.is_child(c, x) && x != n implies pre.is_child(c, x) by {
        lemma_listed_live(post, x);
        assert(post.nodes@[x as int].live == pre.nodes@[x as int].live);
        assert(has(pre.seq@, x));
        lemma_has(pre.seq@, x);
        let k = choose|k: int| 0 <= k < pre.seq@.len() && pre.seq@[k] == x;
        let j = choose|j: int| 0 <= j < post.seq@.len() && post.seq@[j] == x;
        assert(j != 0);
        assert(post.parent@.contains_key(post.seq@[j]));
        assert(pre.parent@.contains_key(x));
        if k == 0 {
            assert(!pre.parent@.contains_key(pre.seq@[0]));
        }
        assert(pre.parent@.contains_key(pre.seq@[k]));
    }
    assert forall|x: usize| !#[trigger] post.is_child(n, x) by {
        if post.is_child(n, x) {
            if x == n {
                assert(post.parent@[n] == p);
            } else {
                assert(pre.is_child(n, x));
                pre.lemma_dead_childless(n, x);
            }
        }
    }
}

/// A child stays its parent's child across a step that keeps its parent and keeps it live: it is listed,
/// since it is live, and not first, since it has a parent.
proof fn lemma_child_kept(pre: Tree, post: Tree, c: usize, x: usize)
    requires
        pre.wf(),
        post.wf(),
        pre.is_child(c, x),
        pre.parent@.contains_key(x) ==> post.parent@.contains_key(x) && post.parent@[x] == pre.parent@[x],
        x < NODE_SPACE,
        post.nodes@[x as int].live,
    ensures
        post.is_child(c, x),
{
    let k = choose|k: int| 0 <= k < pre.seq@.len() && pre.seq@[k] == x;
    assert(k != 0);
    assert(pre.parent@.contains_key(pre.seq@[k]));
    assert(has(post.seq@, x));
    lemma_has(post.seq@, x);
}

/// A live node in a leaf's page is listed and not first, since the first node lies outside every leaf:
/// so it is its parent's child, one deeper, and no deeper than the deepest.
proof fn lemma_owned_listed(k: CapKernel, x: usize)
    requires
        k.wf(),
        x < NODE_SPACE,
        k.list.nodes@[x as int].live,
        k.tables.owner@.contains_key(page_of(x)),
    ensures
        k.list.is_child(k.list.parent@[x], x),
        k.list.d(x) >= 1,
        k.list.d(x) == k.list.d(k.list.parent@[x]) + 1,
        k.list.d(x) <= MAX_DEPTH,
{
    let s = k.list.seq@;
    assert(has(s, x));
    lemma_has(s, x);
    let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
    assert(j != 0);
    assert(k.list.parent@.contains_key(s[j]));
}

/// A slot of a leaf that holds no capability is not live: a live node in a leaf's slot is a capability.
proof fn lemma_deleted_dead(k: CapKernel, n: usize)
    requires
        k.wf(),
        k.tables.owner@.contains_key(page_of(n)),
        n % PAGE_SZ != 0,
        n % PAGE_SZ < NODES_PER_PAGE,
        !k.is_cap(n),
    ensures
        !k.list.nodes@[n as int].live,
{
    if k.list.nodes@[n as int].live {
        assert(k.list.nodes@[n as int].kind is Capability);
    }
}

/// Across steps that only killed nodes and kept every parent, a child of c after them was one before.
proof fn lemma_children_back(pre: Tree, post: Tree, c: usize)
    requires
        pre.wf(),
        post.wf(),
        post.parent@ == pre.parent@,
        forall|i: int| 0 <= i < NODE_SPACE && #[trigger] post.nodes@[i].live ==> pre.nodes@[i].live,
    ensures
        forall|x: usize| #[trigger] post.is_child(c, x) ==> pre.is_child(c, x),
{
    assert forall|x: usize| #[trigger] post.is_child(c, x) implies pre.is_child(c, x) by {
        lemma_listed_live(post, x);
        assert(pre.nodes@[x as int].live);
        assert(has(pre.seq@, x));
        lemma_has(pre.seq@, x);
        let k = choose|k: int| 0 <= k < post.seq@.len() && post.seq@[k] == x;
        assert(k != 0);
        assert(post.parent@.contains_key(post.seq@[k]));
        assert(pre.parent@.contains_key(x));
    }
}

/// A leaf whose slots from 2 on are dead has no live slot from any j of at least 2 on.
proof fn lemma_live_slots_none(k: CapKernel, b: usize, j: int)
    requires
        2 <= j,
        forall|x: int| b + 2 <= x < b + NODES_PER_PAGE ==> !#[trigger] k.list.nodes@[x].live,
    ensures
        k.live_slots_from(b, j) == 0,
    decreases NODES_PER_PAGE - j,
{
    if j < NODES_PER_PAGE {
        lemma_live_slots_none(k, b, j + 1);
        assert(!k.list.nodes@[b + j].live);
    }
}

/// A slot stays a slot of the same node across a step that kept the tables and the liveness of every
/// node but n, when n cannot be the slot's leaf: n is not live, not a page's first node, or not a leaf
/// of that table.
proof fn lemma_slot_kept_but(pre: CapKernel, post: CapKernel, root: usize, i: usize, n: usize)
    requires
        pre.wf(),
        pre.tables.has_slot(&pre.list, root, i),
        post.tables == pre.tables,
        forall|j: int| 0 <= j < NODE_SPACE && j != n ==> #[trigger] post.list.nodes@[j].live == pre.list.nodes@[j].live,
        !pre.list.nodes@[n as int].live || n % PAGE_SZ != 0
            || !(pre.tables.owner@.contains_key(n) && pre.tables.owner@[n].0 == root),
    ensures
        post.tables.has_slot(&post.list, root, i),
        post.tables.node_of(root, i) == pre.tables.node_of(root, i),
{
    pre.lemma_slot(root, i);
    let node = pre.tables.node_of(root, i);
    pre.lemma_slot_bound(node);
    let leaf = pre.tables.leaf(root, index_entry(i));
    assert(leaf == page_of(node));
    assert(leaf <= node);
    if leaf == n {
        lemma_fundamental_div_mod(node as int, PAGE_SZ as int);
        lemma_mod_multiples_basic(node as int / PAGE_SZ as int, PAGE_SZ as int);
        assert(n % PAGE_SZ == 0);
    }
    assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
}

/// A slot stays a slot of the same node across a step that kept the tables' roots and the liveness of
/// every node but a and b, neither of which is a page's first node, so neither is the slot's leaf.
proof fn lemma_slot_kept_two(pre: CapKernel, post: CapKernel, root: usize, i: usize, a: usize, b: usize)
    requires
        pre.wf(),
        pre.tables.has_slot(&pre.list, root, i),
        post.tables.roots == pre.tables.roots,
        forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j != a && j != b
            ==> post.list.nodes@[j].live == pre.list.nodes@[j].live,
        a % PAGE_SZ != 0,
        b % PAGE_SZ != 0,
    ensures
        post.tables.has_slot(&post.list, root, i),
        post.tables.node_of(root, i) == pre.tables.node_of(root, i),
{
    pre.lemma_slot(root, i);
    let node = pre.tables.node_of(root, i);
    pre.lemma_slot_bound(node);
    let leaf = pre.tables.leaf(root, index_entry(i));
    assert(leaf == page_of(node));
    assert(leaf <= node);
    lemma_fundamental_div_mod(node as int, PAGE_SZ as int);
    lemma_mod_multiples_basic(node as int / PAGE_SZ as int, PAGE_SZ as int);
    assert(leaf % PAGE_SZ == 0);
    assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
}

impl CapKernel {
    /// From the state boot leaves, the steps kernel/src takes before it enters the root's thread: core 0
    /// loads the root's space and points its base register at the space's root under the tag the load
    /// gave; then it points the register back at `kernel_root`, the root boot was given and every core
    /// booted on, under KERNEL_TAG, as a core does when it leaves a space for none. Boot leaves every
    /// core naming no space with its register on `kernel_root` under KERNEL_TAG, so the load may start
    /// there, and at the end every core's register is there again. See design/teardown-driven-by-retype/.
    pub fn witness_boot_space_switch(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        kernel_root: usize,
    )
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            old(self).spaces.kernel_root@ == kernel_root,
        ensures
            final(self).wf(),
            final(self).cores@[0].space is None,
            final(self).loaded(0, process),
            final(self).depends(0, process),
            forall|c: int| 0 <= c < NUM_CPUS ==> {
                &&& (#[trigger] final(self).spaces.registers@[c]).root() == kernel_root
                &&& final(self).spaces.registers@[c].tag() == KERNEL_TAG
            },
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        proof {
            reveal(CapKernel::wf);
            assert(s0.cores@[0].space is None);
            assert(s0.cores@[0].generation == 1);
            assert(s0.processes.records@.contains_key(process));
            assert(process_spaces_wf(&s0.spaces, &s0.processes));
            assert(s0.spaces.roots@.contains_key(process));
            assert(s0.spaces.records@[process].value().kind is Process);
        }
        // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let pcid = self.load_space(0, process, Tracked(&mut steps));
        let ghost s1 = *self;
        self.switch_space(0, Some(process), process + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
        let ghost s2 = *self;
        proof {
            assert(s2.cores@[0].space == Some(process));
        }
        self.switch_space(0, None, kernel_root, KERNEL_TAG);
        proof {
            let s3 = *self;
            reveal(registers_wf);
            assert(s3.spaces.registers@.contains_key(0));
            assert(register_names(s3.spaces.registers@[0], s3.cores@[0].space, s3.spaces.loaded@, 0, kernel_root));
            // Every other core is where boot left it, on kernel_root under KERNEL_TAG.
            assert forall|c: int| 0 <= c < NUM_CPUS implies {
                &&& (#[trigger] s3.spaces.registers@[c]).root() == kernel_root
                &&& s3.spaces.registers@[c].tag() == KERNEL_TAG
            } by {
                if c != 0 {
                    assert(s0.spaces.registers@.contains_key(c));
                    assert(s3.spaces.registers@[c] == s2.spaces.registers@[c]);
                    assert(s2.spaces.registers@[c] == s1.spaces.registers@[c]);
                }
            }
        }
    }

    /// From the state boot leaves, the steps kernel/src takes to start the root: core 0 loads the root's
    /// space, points its base register at the space's root under the tag the load gave, and enters the
    /// root's thread, which boot left inactive. At the end core 0 runs that thread on the root's space,
    /// and the thread is still the root process's.
    pub fn witness_root_thread_enters(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: usize,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
    )
        requires
            old(self).booted(root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@),
        ensures
            final(self).wf(),
            final(self).cores@[0].space == Some(process),
            final(self).spaces.registers@[0].root() == process + SPACE_ROOT_PAGE * PAGE_SZ,
            final(self).cores@[0].current_thread == Some(t),
            final(self).threads.records@[t].value().state == (ThreadState::Running { core: 0 }),
            final(self).threads.records@[t].value().process == Some(process),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        proof {
            reveal(CapKernel::wf);
            assert(s0.cores@[0].space is None);
            assert(s0.cores@[0].generation == 1);
            assert(s0.processes.records@.contains_key(process));
            assert(process_spaces_wf(&s0.spaces, &s0.processes));
            assert(s0.spaces.roots@.contains_key(process));
            assert(s0.spaces.records@[process].value().kind is Process);
        }
        // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let pcid = self.load_space(0, process, Tracked(&mut steps));
        self.switch_space(0, Some(process), process + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
        let ghost s2 = *self;
        proof {
            assert(s2.threads == s0.threads);
            assert(s2.cores@[0].current_thread is None);
        }
        self.enter_boot_thread(0, t);
    }

    /// From the state boot leaves, the root's thread entered on core 0 as witness_root_thread_enters
    /// enters it, then suspends itself through its control capability in ROOT_THREAD_SLOT. The suspend
    /// succeeds, core 0 runs nothing after it, and the thread is Inactive with no stop pending, still the
    /// root process's: a thread suspending itself needs no other core.
    pub fn witness_root_suspends_itself(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: usize,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
    ) -> (ret: SuspendStep)
        requires
            old(self).booted(root@, process, leaf@, frames@, t, free@, image@, untyped@, frame@, present@),
        ensures
            ret is Suspended,
            final(self).wf(),
            final(self).cores@[0].current_thread is None,
            final(self).threads.records@[t].value().state is Inactive,
            !final(self).threads.records@[t].value().pending_stop,
            final(self).threads.records@[t].value().process == Some(process),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        proof {
            reveal(CapKernel::wf);
            assert(s0.cores@[0].space is None);
            assert(s0.cores@[0].generation == 1);
            assert(s0.processes.records@.contains_key(process));
            assert(process_spaces_wf(&s0.spaces, &s0.processes));
            assert(s0.spaces.roots@.contains_key(process));
            assert(s0.spaces.records@[process].value().kind is Process);
        }
        // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let pcid = self.load_space(0, process, Tracked(&mut steps));
        self.switch_space(0, Some(process), process + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
        let ghost s2 = *self;
        proof {
            assert(s2.threads == s0.threads);
            assert(s2.cores@[0].current_thread is None);
        }
        self.enter_boot_thread(0, t);
        let ghost s3 = *self;
        proof {
            assert(s3.cores@[0].current_thread == Some(t));
            assert(s3.threads.records@[t].value().state == (ThreadState::Running { core: 0 }));
            assert(s3.list == s0.list);
            assert(s3.tables == s0.tables);
            assert(s3.processes == s0.processes);
            assert(s3.slot_holds(process, ROOT_THREAD_SLOT, (leaf@ + 2) as usize, thread_of(t)));
            s3.lemma_slot(process, ROOT_THREAD_SLOT);
            assert(THREAD_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(!s3.threads.records@[t].value().dying);
            assert(s3.root_live(process));
            assert(s3.can_suspend(process, ROOT_THREAD_SLOT));
        }
        self.suspend(0, process, ROOT_THREAD_SLOT)
    }

    /// From the state boot leaves, with a second process built at `base` as
    /// witness_process_holds_capability builds it: core 0 loads the root's space and points its base
    /// register at it, then loads the second process's space while the register still names the root's,
    /// and points the register straight at the second space's root, with no write of the kernel's root
    /// between. The second load hands out a fresh PCID in the generation, so no id the register's tag
    /// stands for is handed to another space. See design/core-names-a-space-while-running-its-thread/.
    pub fn witness_switch_between_processes(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
    )
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            final(self).wf(),
            final(self).cores@[0].space == Some(base),
            final(self).spaces.registers@[0].root() == base + SPACE_ROOT_PAGE * PAGE_SZ,
            final(self).loaded(0, process),
            final(self).loaded(0, base),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        proof {
            assert(s0.cores@[0].space is None);
            assert(s0.cores@[0].current_thread is None);
            assert(s0.cores@[0].generation == 1);
            assert(s0.cores@[0].next_pcid == 1);
        }
        let ok = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let ghost s1 = *self;
        proof {
            assert(ok);
            assert(s1.cores == s0.cores);
            assert(witness_alive(s1, process));
            assert(witness_alive(s1, base));
            assert(process_spaces_wf(&s1.spaces, &s1.processes)) by {
                reveal(CapKernel::wf);
            }
            assert(s1.processes.records@.contains_key(process));
            assert(s1.processes.records@.contains_key(base));
            // Each space's block is in tracked memory, so its root page is an aligned address.
            assert(space_wf(&s1.list, &s1.spaces, &s1.blocks, process)) by {
                reveal(CapKernel::wf);
            }
            assert(space_wf(&s1.list, &s1.spaces, &s1.blocks, base)) by {
                reveal(CapKernel::wf);
            }
        }
        // The steps are the witness's own; no lock bounds them: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let pcid = self.load_space(0, process, Tracked(&mut steps));
        self.switch_space(0, Some(process), process + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
        let ghost s2 = *self;
        proof {
            assert(s2.cores@[0].space == Some(process));
            assert(s2.cores@[0].current_thread is None);
            assert(s2.cores@[0].next_pcid <= 2);
            assert(s2.cores@[0].generation == 1);
            assert(s2.spaces.roots == s1.spaces.roots);
            assert(s2.spaces.records == s1.spaces.records);
        }
        // Core 0 loads the second space while its register names the root's: the load starts no
        // new generation.
        let pcid = self.load_space(0, base, Tracked(&mut steps));
        let ghost s3 = *self;
        proof {
            assert(s3.cores@[0].current_thread is None);
            assert(s3.loaded(0, process));
        }
        self.switch_space(0, Some(base), base + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
    }

    /// From the state boot leaves, with a second process built at `base` as
    /// witness_process_holds_capability builds it, with its thread at `base + 10 * PAGE_SZ`: core 0
    /// loads the second space, points its register at it and enters that thread; switch_thread takes
    /// the core to idle, on the kernel's root; the core then loads the root's space and points its
    /// register there with no thread; and switch_thread takes it back to the thread straight from the
    /// root's space, in one write that keeps the generation. A switch between threads of two processes
    /// waits on a thread being placed on a core, which no verified operation does yet. See
    /// design/core-names-a-space-while-running-its-thread/.
    pub fn witness_thread_switch(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
        kernel_root: usize,
        registers: Registers,
    )
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            old(self).spaces.kernel_root@ == kernel_root,
        ensures
            final(self).wf(),
            final(self).cores@[0].current_thread == Some((base + 10 * PAGE_SZ) as usize),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().state == (ThreadState::Running { core: 0 }),
            final(self).threads.records@[(base + 10 * PAGE_SZ) as usize].value().frame == registers,
            final(self).cores@[0].space == Some(base),
            final(self).spaces.registers@[0].root() == base + SPACE_ROOT_PAGE * PAGE_SZ,
            final(self).cores@[0].generation == 1,
            final(self).loaded(0, process),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ok = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let thread = base + 10 * PAGE_SZ;
        let ghost s1 = *self;
        proof {
            assert(ok);
            assert(s1.cores == s0.cores);
            assert(s1.cores@[0].generation == 1);
            assert(s1.cores@[0].next_pcid == 1);
            assert(s1.cores@[0].space is None);
            assert(s1.cores@[0].current_thread is None);
            assert(s1.spaces.kernel_root@ == kernel_root);
            assert(s1.spaces.roots@.contains_key(process) && s1.spaces.records@[process].value().kind is Process
                && s1.spaces.roots@.contains_key(base) && s1.spaces.records@[base].value().kind is Process
                && space_wf(&s1.list, &s1.spaces, &s1.blocks, process)
                && space_wf(&s1.list, &s1.spaces, &s1.blocks, base)
                && !s1.threads.records@[thread].value().pending_stop) by {
                reveal(CapKernel::wf);
                reveal(current_wf);
                assert(witness_alive(s1, process));
                assert(witness_alive(s1, base));
                assert(process_spaces_wf(&s1.spaces, &s1.processes));
                assert(s1.processes.records@.contains_key(process));
                assert(s1.processes.records@.contains_key(base));
            }
        }
        // The steps are the witness's own; no lock bounds them: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let pcid = self.load_space(0, base, Tracked(&mut steps));
        self.switch_space(0, Some(base), base + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
        let ghost s2 = *self;
        proof {
            assert(s2.threads == s1.threads);
            assert(s2.cores@[0].current_thread is None);
        }
        self.enter_boot_thread(0, thread);
        let ghost s3 = *self;
        proof {
            assert(s3.cores@[0].current_thread == Some(thread));
            assert(!s3.threads.records@[thread].value().pending_stop);
            assert(s3.spaces == s2.spaces);
            assert(s3.cores@[0].next_pcid <= 2);
            assert(s3.cores@[0].generation == 1);
        }
        // The thread leaves, and the core goes idle on the kernel's root.
        self.switch_thread(0, registers, None, kernel_root, Tracked(&mut steps));
        let ghost s4 = *self;
        proof {
            assert(s4.cores@[0].current_thread is None);
            assert(s4.threads.records@[thread].value().state == (ThreadState::Runnable { core: 0 }));
            assert(s4.threads.records@[thread].value().process == Some(base));
            assert(s4.cores@[0].generation == 1);
            assert(s4.spaces.roots == s1.spaces.roots);
            assert(s4.spaces.records == s1.spaces.records);
        }
        // The core names the root's space, with no thread of it.
        let pcid = self.load_space(0, process, Tracked(&mut steps));
        self.switch_space(0, Some(process), process + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
        let ghost s5 = *self;
        proof {
            assert(s5.threads == s4.threads);
            assert(s5.cores@[0].current_thread is None);
            assert(s5.cores@[0].generation == 1);
            assert(s5.cores@[0].next_pcid != PCID_MAX);
            assert(s5.spaces.roots == s1.spaces.roots);
            assert(s5.spaces.records == s1.spaces.records);
            assert(s5.loaded(0, process));
        }
        // The thread comes back, straight from the root's space.
        self.switch_thread(0, registers, Some(thread), kernel_root, Tracked(&mut steps));
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of two free ones past those boot's tables took from the first untyped: retype a leaf into root
    /// entry 2 of the root's table at the second block's first two pages, a process at `base` into
    /// slot 1 of that leaf, a thread at the second block's next two pages into slot 2, bound to the
    /// process, a leaf at its next two into root entry 0 of the process's table, through the process
    /// capability, and derive an untyped over its last two pages from the root's first untyped into
    /// slot 1 of that leaf, through the process capability. Every step succeeds, and at the end the
    /// new process is not the root, holds the derived capability, the root's untyped's child, and has
    /// the thread bound to it. What a reclaim of it starts from holds too: the process block's first
    /// page and the new leaf's two are acknowledged, the thread's block holds one reference and the
    /// process's two, the capability and the binding, no core has the process's space loaded, its
    /// table has the one leaf, and the three slots hold what the steps put there. The thread
    /// capability and the derived untyped have no child, and the process capability's only child is
    /// the binding. The process is live, the thread inactive and bound to it, the flush epoch still 0,
    /// the process's space empty outside the kernel's entries, and the leaf live and hidden, owned by
    /// root entry 0 of the process's table, with no live node past its slot 1.
    pub fn witness_process_holds_capability(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
                let u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
                let child = (base + 12 * PAGE_SZ + 1) as usize;
                let thread = (base + 10 * PAGE_SZ) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& final(self).view().holds(base, child)
                &&& final(self).list.is_child(u, child)
                &&& final(self).payload_of(child) == child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1)
                &&& bound_threads(&final(self).list, &final(self).tables).contains_key(thread)
                &&& bound_threads(&final(self).list, &final(self).tables)[thread] == base
                &&& final(self).acknowledged(base / PAGE_SZ)
                &&& final(self).acknowledged(((base + 12 * PAGE_SZ) / PAGE_SZ as int) as usize)
                &&& final(self).acknowledged(((base + 12 * PAGE_SZ) / PAGE_SZ as int + 1) as usize)
                &&& block_refs(&final(self).blocks, BlockRef::Small(thread / PAGE_SZ)) == 1
                &&& block_refs(&final(self).blocks, BlockRef::Small(base / PAGE_SZ)) == 2
                &&& final(self).process_unloaded(base)
                &&& final(self).cores == old(self).cores
                &&& final(self).spaces.kernel_root == old(self).spaces.kernel_root
                &&& final(self).tables.leaf(base, 0) == (base + 12 * PAGE_SZ) as usize
                &&& forall|r: int| 1 <= r < ROOT_ENTRIES ==> #[trigger] final(self).tables.leaf(base, r) == NO_LEAF
                &&& final(self).slot_holds(process, WITNESS_PROCESS_SLOT, (base + 8 * PAGE_SZ + 1) as usize, process_of(base))
                &&& final(self).slot_holds(process, WITNESS_THREAD_SLOT, (base + 8 * PAGE_SZ + 2) as usize, thread_of(thread))
                &&& final(self).slot_holds(base, WITNESS_CHILD_SLOT, child, child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1))
                &&& witness_empty(*final(self), process, WITNESS_CLAIM_SLOT, (base + 8 * PAGE_SZ + 3) as usize)
                &&& final(self).flush_epoch == 0
                &&& witness_alive(*final(self), base)
                &&& final(self).threads.records@.contains_key(thread)
                &&& final(self).threads.records@[thread].value().state is Inactive
                &&& !final(self).threads.records@[thread].value().dying
                &&& final(self).threads.records@[thread].value().process == Some(base)
                &&& final(self).spaces.roots@.contains_key(base)
                &&& forall|i: usize| i < ENTRIES && !holds_kernel(SpaceKind::Process, i)
                    ==> #[trigger] final(self).spaces.roots@[base].value()[i].is_empty()
                &&& final(self).list.nodes@[base + 12 * PAGE_SZ].live
                &&& final(self).list.nodes@[base + 12 * PAGE_SZ].kind is Hidden
                &&& forall|x: int| base + 12 * PAGE_SZ + 1 < x < base + 12 * PAGE_SZ + NODES_PER_PAGE ==> !#[trigger] final(self).list.nodes@[x].live
                &&& final(self).tables.owner@[(base + 12 * PAGE_SZ) as usize] == (base, 0int)
                &&& forall|c: usize| !#[trigger] final(self).list.is_child((base + 8 * PAGE_SZ + 2) as usize, c)
                &&& final(self).list.childless((base + 8 * PAGE_SZ + 2) as usize)
                &&& forall|c: usize| #[trigger] final(self).list.is_child((base + 8 * PAGE_SZ + 1) as usize, c) ==> c == thread
                &&& forall|c: usize| !#[trigger] final(self).list.is_child(child, c)
                &&& final(self).list.childless(child)
                &&& final(self).slot_holds(process, ROOT_UNTYPED_SLOT, u, first)
                &&& first.kind is Untyped
                &&& first.rights & right_bit(Right::Retype) != 0
                &&& final(self).tables.roots@.contains_key(process)
                &&& witness_alive(*final(self), process)
                &&& block_within(base, PROCESS_ORDER, first)
                &&& block_within(thread, THREAD_ORDER, first)
                &&& block_within((base + 12 * PAGE_SZ) as usize, 1, first)
                &&& final(self).blocks.tracks_addr_run(base, order_pages(PROCESS_ORDER as usize))
                &&& base + 2 * PROCESS_BYTES <= NODE_SPACE
                &&& final(self).tables.owner@.contains_key((base + 12 * PAGE_SZ) as usize)
                &&& image_tables_bound(image@) + 3 <= untyped_tables(first)
                    ==> witness_block(*final(self), (base + 2 * PROCESS_BYTES) as usize, first)
                &&& !final(self).blocks.pages@[(base / PAGE_SZ) as int].dead
                &&& final(self).list.nodes@[u as int].depth == 1
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped, its process capability and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            let pn = (leaf@ + 1) as usize;
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            // The two free blocks, the second right after the first.
            assert(s0.root_untyped(process) == u);
            assert(s0.root_table_block(process, cursor_block(first.base, itb)));
            assert(s0.root_table_block(process, cursor_block(first.base, itb + 1)));
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 2) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(cursor_block(first.base, itb + 1) == base + PROCESS_BYTES);
            // The first untyped is the first boot block, whose pages boot left acknowledged.
            lemma_runs_blocks(free@, MAX_ORDER as nat);
            let b0 = bs[0];
            assert(b0.1 <= MAX_ORDER && b0.0 + pow2(b0.1) <= NUM_PAGES);
            assert(b0.0 * PAGE_SZ <= NUM_PAGES * PAGE_SZ) by (nonlinear_arith)
                requires
                    b0.0 <= NUM_PAGES,
            ;
            assert(first.base == b0.0 * PAGE_SZ);
            assert((b0.1 as u8) as nat == b0.1);
            assert(block_bytes(first.order) == pow2(b0.1) * PAGE_SZ);
            lemma_fundamental_div_mod_converse(base as int, PAGE_SZ as int, b0.0 + 8 * itb, 0);
            assert(base / PAGE_SZ == b0.0 + 8 * itb);
            assert(8 * itb + 16 <= pow2(b0.1)) by (nonlinear_arith)
                requires
                    PROCESS_BYTES == 8 * PAGE_SZ,
                    (itb + 2) * PROCESS_BYTES <= pow2(b0.1) * PAGE_SZ,
            ;
            assert(in_page_block(bs[0], (base / PAGE_SZ) as nat));
            assert(in_page_block(bs[0], (base / PAGE_SZ + 12) as nat));
            assert(in_page_block(bs[0], (base / PAGE_SZ + 13) as nat));
            assert(s0.acknowledged(base / PAGE_SZ));
            assert(s0.acknowledged((base / PAGE_SZ + 12) as usize));
            assert(s0.acknowledged((base / PAGE_SZ + 13) as usize));
        }
        let b2 = base + PROCESS_BYTES;
        let bt = b2 + 2 * PAGE_SZ;
        let bl = b2 + 4 * PAGE_SZ;
        let bd = b2 + 6 * PAGE_SZ;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(base % PROCESS_BYTES == 0);
            assert(b2 % PROCESS_BYTES == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            lemma_block_page(b2, 4);
            lemma_block_page(b2, 6);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == b2 / PAGE_SZ + 2);
            assert(bl / PAGE_SZ == b2 / PAGE_SZ + 4);
            assert(!s0.blocks.covered((base / PAGE_SZ) as int));
            assert(!s0.blocks.covered((b2 / PAGE_SZ) as int));
            assert(!s0.blocks.covered(b2 / PAGE_SZ + 2));
            assert(!s0.blocks.covered(b2 / PAGE_SZ + 4));
            assert forall|i: int| base / PAGE_SZ <= i < base / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[base / PAGE_SZ + (i - base / PAGE_SZ)].kind is Free);
            }
            assert forall|i: int| b2 / PAGE_SZ <= i < b2 / PAGE_SZ + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[b2 / PAGE_SZ + (i - b2 / PAGE_SZ)].kind is Free);
            }
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b2, 1));
            assert(s0.blocks.small_free((b2 / PAGE_SZ) as int, 1));
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b2));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b2, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at1, b2));
            assert(s1.tables.leaf(process, 2) == b2);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_THREAD_SLOT) && index_entry(WITNESS_THREAD_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_PROCESS_SLOT) as int].live);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_THREAD_SLOT) as int].live);
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == b2 + 1);
            assert(s1.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(index_ok(WITNESS_CLAIM_SLOT) && index_entry(WITNESS_CLAIM_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_CLAIM_SLOT));
            assert(s1.tables.node_of(process, WITNESS_CLAIM_SLOT) == b2 + 3);
            assert(witness_empty(s1, process, WITNESS_CLAIM_SLOT, (b2 + 3) as usize));
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(s1.root_live(process));
            assert forall|i: int| base / PAGE_SZ <= i < base / PAGE_SZ + 8 || b2 / PAGE_SZ + 2 <= i < b2 / PAGE_SZ + 8
                implies #[trigger] s1.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.tracks(i));
                assert(s0.blocks.pages@[i].kind is Free);
            }
        }

        // A process, in slot 1 of that leaf.
        proof {
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(s1.blocks.pages@[(base / PAGE_SZ + k) as int].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, Tracked(&mut steps));
        let ghost s2 = *self;
        let ghost np = (b2 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None));
            assert(s2.tables.roots@.contains_key(base));
            assert(s2.processes.records@.contains_key(base));
            assert(!s2.processes.records@[base].value().dead);
            assert(s2.payload_of(np) == process_of(base));
            assert(s2.payload_of(np).rights & right_bit(Right::Control) != 0);
            assert(s2.list.nodes@[np as int].depth == 2);
            assert(s2.view().holds(process, np));
            assert(s2.is_cap(np));
            // The root's table keeps its new leaf, which the new process's table lacks, so the two differ.
            assert(s1.tables.roots@.contains_key(process));
            assert(s2.tables.leaf(process, 2) == b2);
            assert(s2.tables.leaf(base, 2) == NO_LEAF);
            assert(base != process);
            // The untyped, the thread's slot and the root's record stay.
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.is_cap(u));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s2.is_cap(u) && s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(!s2.list.nodes@[(b2 + 2) as int].live);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_CLAIM_SLOT));
            assert(witness_empty(s2, process, WITNESS_CLAIM_SLOT, (b2 + 3) as usize));
            assert(s1.processes.records@.contains_key(process));
            assert(s2.processes.records@.contains_key(process));
            assert(s2.root_live(process));
            assert(s2.tables.roots@.contains_key(process));
            assert forall|i: int| b2 / PAGE_SZ + 2 <= i < b2 / PAGE_SZ + 8 implies #[trigger] s2.blocks.pages@[i].kind is Free by {
                assert(s1.blocks.tracks(i));
                assert(s1.blocks.pages@[i].kind is Free);
            }
            // The process capability was not live before its retype, so it has no child after it.
            assert(s1.list.wf() && s2.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(!s1.list.nodes@[np as int].live);
            assert(s1.list.nodes@[u as int].live);
            assert(u != np);
            assert(s2.list.parent@ == s1.list.parent@.insert(np, u));
            assert forall|x: usize| x != np && x != np && #[trigger] s1.list.parent@.contains_key(x)
                implies s2.list.parent@[x] == s1.list.parent@[x] by {}
            lemma_children_kept(s1.list, s2.list, np, np, np);
            assert forall|x: usize| !#[trigger] s2.list.is_child(np, x) by {
                if s2.list.is_child(np, x) && x != np {
                    s1.list.lemma_dead_childless(np, x);
                }
            }
        }

        // A thread, in slot 2 of the root's leaf, bound to the process.
        proof {
            assert(block_refs(&s2.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(!s2.cap_dead(np));
            assert(s2.can_hold_thread(process, WITNESS_PROCESS_SLOT));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(s2.blocks.small_free((bt / PAGE_SZ) as int, THREAD_ORDER as usize)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s2.blocks.pages@[bt / PAGE_SZ + k].kind is Free by {
                    assert(s2.blocks.pages@[(b2 / PAGE_SZ + 2 + k) as int].kind is Free);
                }
            }
            assert(s2.can_retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok3 = self.retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT, Tracked(&mut steps));
        let ghost s3 = *self;
        proof {
            assert(ok3);
            assert(s2.payload_of(s2.tables.node_of(process, WITNESS_PROCESS_SLOT)).base == base);
            // The thread holds one reference on its block and one on the process's, which the process
            // capability holds the other of; no core has the process's space loaded.
            assert(block_refs(&s3.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(block_refs(&s3.blocks, BlockRef::Small(bt / PAGE_SZ)) == 1);
            assert(s3.process_unloaded(base));
            assert(bound_threads(&s3.list, &s3.tables) == bound_threads(&s2.list, &s2.tables).insert(bt, base));
            assert(Self::retype_keeps(s2, s3, (b2 + 2) as usize, (bt / PAGE_SZ) as int, 1, None));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.is_cap(u));
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s3.is_cap(u) && s3.payload_of(u) == first && s3.list.nodes@[u as int].depth == 1);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s3.is_cap(np) && s3.payload_of(np) == process_of(base));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_CLAIM_SLOT));
            assert(witness_empty(s3, process, WITNESS_CLAIM_SLOT, (b2 + 3) as usize));
            assert(s2.processes.records@.contains_key(process));
            assert(s3.processes.records@.contains_key(process));
            assert(s3.root_live(process));
            assert(s3.tables.roots@.contains_key(process));
            assert(s3.processes.records@.contains_key(base));
            assert(!s3.processes.records@[base].value().dead);
            assert(s3.tables.leaf(base, 0) == NO_LEAF);
            assert forall|i: int| b2 / PAGE_SZ + 4 <= i < b2 / PAGE_SZ + 6 implies #[trigger] s3.blocks.pages@[i].kind is Free by {
                assert(s2.blocks.tracks(i));
                assert(s2.blocks.pages@[i].kind is Free);
            }
            // The retype adds the thread capability, under the untyped, and the binding, under the process
            // capability. So the process capability's only child is the binding, and the thread capability,
            // not live before, has none.
            assert(s3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let nt = (b2 + 2) as usize;
            assert(s2.list.nodes@[u as int].live);
            assert(u != nt);
            assert(Self::typed_nodes(s2.list, s3.list, nt, bt));
            assert(s3.list.parent@ == s2.list.parent@.insert(nt, u).insert(bt, np));
            assert forall|x: usize| x != nt && x != bt && #[trigger] s2.list.parent@.contains_key(x)
                implies s3.list.parent@[x] == s2.list.parent@[x] by {}
            lemma_children_kept(s2.list, s3.list, nt, bt, np);
            lemma_children_kept(s2.list, s3.list, nt, bt, nt);
            assert forall|x: usize| #[trigger] s3.list.is_child(np, x) implies x == bt by {
                if x != bt && x != nt {
                    assert(s2.list.is_child(np, x));
                }
            }
            assert forall|x: usize| !#[trigger] s3.list.is_child(nt, x) by {
                if s3.list.is_child(nt, x) && x != nt && x != bt {
                    s2.list.lemma_dead_childless(nt, x);
                }
            }
        }

        // A leaf in root entry 0 of the new process's table, through the process capability.
        let at2 = Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 };
        proof {
            assert(s3.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s3.blocks.small_free((bl / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s3.blocks.pages@[bl / PAGE_SZ + k].kind is Free by {
                    assert(s3.blocks.pages@[(b2 / PAGE_SZ + 4 + k) as int].kind is Free);
                }
            }
            assert(s3.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok4 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl, Tracked(&mut steps));
        let ghost s4 = *self;
        let ghost child = (bl + 1) as usize;
        proof {
            assert(ok4);
            assert(Self::leaf_retyped(s3, s4, process, ROOT_UNTYPED_SLOT, at2, bl));
            assert(s3.blocks.tracks((base / PAGE_SZ) as int));
            assert(s3.blocks.tracks((bt / PAGE_SZ) as int));
            assert(s4.blocks.pages@[(base / PAGE_SZ) as int] == s3.blocks.pages@[(base / PAGE_SZ) as int]);
            assert(s4.blocks.pages@[(bt / PAGE_SZ) as int] == s3.blocks.pages@[(bt / PAGE_SZ) as int]);
            assert(block_refs(&s4.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(block_refs(&s4.blocks, BlockRef::Small(bt / PAGE_SZ)) == 1);
            assert(s4.process_unloaded(base));
            assert(s4.tables.leaf(base, 0) == bl);
            assert(index_ok(WITNESS_CHILD_SLOT) && index_entry(WITNESS_CHILD_SLOT) == 0);
            assert(s4.tables.has_slot(&s4.list, base, WITNESS_CHILD_SLOT));
            assert(s4.tables.node_of(base, WITNESS_CHILD_SLOT) == child);
            assert(!s4.list.nodes@[child as int].live);
            assert(s4.processes == s3.processes);
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.is_cap(u));
            assert(s4.tables.has_slot(&s4.list, process, ROOT_UNTYPED_SLOT));
            assert(s4.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s4.is_cap(u) && s4.payload_of(u) == first && s4.list.nodes@[u as int].depth == 1);
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.is_cap(np));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_PROCESS_SLOT));
            assert(s4.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s4.is_cap(np) && s4.payload_of(np) == process_of(base));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_CLAIM_SLOT));
            assert(witness_empty(s4, process, WITNESS_CLAIM_SLOT, (b2 + 3) as usize));
            assert(s4.root_live(process));
            assert(s4.tables.roots@.contains_key(process));
            // The leaf's hidden node goes under the untyped, so the two capabilities keep their children.
            assert(s4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let nt = (b2 + 2) as usize;
            assert(s4.list.parent@ == s3.list.parent@.insert(bl, u));
            assert forall|x: usize| x != bl && x != bl && #[trigger] s3.list.parent@.contains_key(x)
                implies s4.list.parent@[x] == s3.list.parent@[x] by {}
            lemma_children_kept(s3.list, s4.list, bl, bl, np);
            lemma_children_kept(s3.list, s4.list, bl, bl, nt);
            assert forall|x: usize| #[trigger] s4.list.is_child(np, x) implies x == bt by {
                if x != bl {
                    assert(s3.list.is_child(np, x));
                }
            }
            assert forall|x: usize| !#[trigger] s4.list.is_child(nt, x) by {
                if s4.list.is_child(nt, x) && x != bl {
                    assert(s3.list.is_child(nt, x));
                }
            }
            // The leaf: live, hidden, its other nodes not live, owned by root entry 0 of the new table.
            lemma_listed_live(s4.list, bl);
            assert(s4.list.nodes@[bl as int].kind is Hidden);
            assert(s4.tables.owner@[bl] == (base, 0int));
            assert(s4.threads == s3.threads);
            assert(s4.spaces == s3.spaces);
            assert(s4.flush_epoch == s0.flush_epoch);
        }

        // An untyped over the second block's last two pages, derived from the root's untyped into slot 1
        // of the new process's leaf, through the process capability.
        let at3 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT };
        proof {
            assert(s4.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(!s4.cap_dead(u));
            assert(names_block(first.kind));
            assert(UNTYPED_RIGHTS & !UNTYPED_RIGHTS == 0) by (compute_only);
            assert(UNTYPED_RIGHTS & right_bit(Right::Control) == 0) by (compute_only);
            assert(block_within(bd, 1, first));
            assert(narrows(child_of(first, UNTYPED_RIGHTS, bd, 1), first));
            assert(s4.can_derive_between(process, ROOT_UNTYPED_SLOT, base, WITNESS_CHILD_SLOT, UNTYPED_RIGHTS, bd, 1));
            assert(s4.can_derive_at(process, ROOT_UNTYPED_SLOT, at3, UNTYPED_RIGHTS, bd, 1));
        }
        let ok5 = self.derive(process, ROOT_UNTYPED_SLOT, at3, UNTYPED_RIGHTS, bd, 1);
        proof {
            let s5 = *self;
            assert(ok5);
            assert(Self::cap_derived_between(s4, s5, process, ROOT_UNTYPED_SLOT, base, WITNESS_CHILD_SLOT, UNTYPED_RIGHTS, bd, 1));
            assert(s5.view().holds(base, child));
            assert(s5.list.is_child(u, child));
            assert(s5.payload_of(child) == child_of(first, UNTYPED_RIGHTS, bd, 1));
            assert(bound_threads(&s5.list, &s5.tables) == bound_threads(&s2.list, &s2.tables).insert(bt, base));
            assert(child == base + 12 * PAGE_SZ + 1);
            assert(bt == base + 10 * PAGE_SZ);
            assert(bd == base + 14 * PAGE_SZ);
            // An untyped's derive leaves the blocks, and no step changed an acknowledgement.
            assert(s4.payload_of(s4.tables.node_of(process, ROOT_UNTYPED_SLOT)).kind is Untyped);
            assert(s5.blocks == s4.blocks);
            assert(block_refs(&s5.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(block_refs(&s5.blocks, BlockRef::Small(bt / PAGE_SZ)) == 1);
            assert(s5.process_unloaded(base));
            assert(s5.stale_epoch == s0.stale_epoch);
            assert(s5.cores == s0.cores);
            assert(s5.iommus == s0.iommus);
            assert(bl / PAGE_SZ == base / PAGE_SZ + 12);
            assert((base + 12 * PAGE_SZ) / PAGE_SZ as int == bl / PAGE_SZ);
            // The new table's root entries and the three slots the reclaim starts from.
            assert(s5.tables.roots == s4.tables.roots);
            assert forall|r: int| 1 <= r < ROOT_ENTRIES implies #[trigger] s5.tables.leaf(base, r) == NO_LEAF by {
                assert(s3.tables.leaf(base, r) == s2.tables.leaf(base, r));
                assert(s4.tables.leaf(base, r) == s3.tables.leaf(base, r));
            }
            assert(Self::derive_step(s4, s5, child));
            Self::lemma_slot_stays(s4, s5, process, WITNESS_PROCESS_SLOT);
            Self::lemma_slot_stays(s4, s5, process, WITNESS_THREAD_SLOT);
            Self::lemma_caps_frame(s4, s5, child, child, np);
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_THREAD_SLOT));
            assert(s3.is_cap((b2 + 2) as usize) && s3.payload_of((b2 + 2) as usize) == thread_of(bt));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_THREAD_SLOT));
            assert(s4.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(s4.is_cap((b2 + 2) as usize) && s4.payload_of((b2 + 2) as usize) == thread_of(bt));
            Self::lemma_caps_frame(s4, s5, child, child, (b2 + 2) as usize);
            assert(s5.slot_holds(process, WITNESS_PROCESS_SLOT, np, process_of(base)));
            assert(s5.slot_holds(process, WITNESS_THREAD_SLOT, (b2 + 2) as usize, thread_of(bt)));
            assert(s5.slot_holds(base, WITNESS_CHILD_SLOT, child, child_of(first, UNTYPED_RIGHTS, bd, 1)));
            Self::lemma_slot_stays(s4, s5, process, WITNESS_CLAIM_SLOT);
            assert(witness_empty(s5, process, WITNESS_CLAIM_SLOT, (b2 + 3) as usize));
            Self::lemma_acknowledged_kept(s0, s5, base / PAGE_SZ);
            Self::lemma_acknowledged_kept(s0, s5, (base / PAGE_SZ + 12) as usize);
            Self::lemma_acknowledged_kept(s0, s5, (base / PAGE_SZ + 13) as usize);
            // The derived untyped goes under the root's untyped: the two capabilities keep their children,
            // and it, not live before, has none.
            assert(s5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let nt = (b2 + 2) as usize;
            assert(s4.list.nodes@[u as int].live);
            assert(u != child);
            assert(s5.list.parent@ == s4.list.parent@.insert(child, u));
            assert(s5.list.seq@[0] == s4.list.seq@[0]);
            assert forall|x: usize| x != child && x != child && #[trigger] s4.list.parent@.contains_key(x)
                implies s5.list.parent@[x] == s4.list.parent@[x] by {}
            lemma_children_kept(s4.list, s5.list, child, child, np);
            lemma_children_kept(s4.list, s5.list, child, child, nt);
            lemma_children_kept(s4.list, s5.list, child, child, child);
            assert forall|x: usize| #[trigger] s5.list.is_child(np, x) implies x == bt by {
                if x != child {
                    assert(s4.list.is_child(np, x));
                }
            }
            assert forall|x: usize| !#[trigger] s5.list.is_child(nt, x) by {
                if s5.list.is_child(nt, x) && x != child {
                    assert(s4.list.is_child(nt, x));
                }
            }
            assert forall|x: usize| !#[trigger] s5.list.is_child(child, x) by {
                if s5.list.is_child(child, x) && x != child {
                    s4.list.lemma_dead_childless(child, x);
                }
            }
            assert(s5.list.nodes@[nt as int].live);
            if !s5.list.childless(nt) {
                s5.list.lemma_next_is_child(nt);
            }
            if !s5.list.childless(child) {
                s5.list.lemma_next_is_child(child);
            }
            // The rest of what the reclaim reads, kept by the leaf's retype and the derive.
            assert(s0.flush_epoch == 0);
            assert(s5.processes == s4.processes);
            assert(s5.threads == s4.threads);
            assert(s5.spaces.roots@ == s4.spaces.roots@);
            assert(s5.tables.owner == s4.tables.owner);
            assert(s5.list.nodes@[bl as int].live && s5.list.nodes@[bl as int].kind is Hidden);
            assert forall|x: int| bl + 1 < x < bl + NODES_PER_PAGE implies !#[trigger] s5.list.nodes@[x].live by {
                assert(!s4.list.nodes@[x].live);
            }
            // What a teardown of the process starts from: the root's untyped, table and record, the blocks
            // within the untyped, and the new leaf's owner.
            Self::lemma_slot_stays(s4, s5, process, ROOT_UNTYPED_SLOT);
            Self::lemma_caps_frame(s4, s5, child, child, u);
            assert(s5.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s5.list.nodes@[u as int].depth == 1);
            assert(s3.processes.records@.contains_key(process));
            assert(s4.root_live(process));
            assert(witness_alive(s5, process));
            assert(s5.tables.roots@.contains_key(process));
            assert(block_within(base, PROCESS_ORDER, first));
            assert(block_within(bt, THREAD_ORDER, first));
            assert(block_within(bl, 1, first));
            assert(bl == base + 12 * PAGE_SZ);
            assert(base + 2 * PROCESS_BYTES <= NODE_SPACE) by (nonlinear_arith)
                requires
                    (itb + 2) * PROCESS_BYTES <= block_bytes(first.order),
                    first.base + block_bytes(first.order) <= NODE_SPACE,
                    base == first.base + itb * PROCESS_BYTES,
            ;
            assert(s4.tables.owner@.contains_key(bl));
            assert(s5.tables.owner@.contains_key(bl));
        }
        proof {
            // The third block, when the untyped reaches past the second, is still free: every step took
            // pages of the first two.
            let s5 = *self;
            // The process's block is not dead: the bind and the steps after it kept its flag.
            assert(!s2.blocks.pages@[(base / PAGE_SZ) as int].dead);
            assert(!s3.blocks.pages@[(base / PAGE_SZ) as int].dead);
            assert(!s4.blocks.pages@[(base / PAGE_SZ) as int].dead);
            assert(!s5.blocks.pages@[(base / PAGE_SZ) as int].dead);
            let b3 = (base + 2 * PROCESS_BYTES) as usize;
            if itb + 3 <= untyped_tables(first) {
                assert((itb + 3) * PROCESS_BYTES <= block_bytes(first.order));
                assert(cursor_block(first.base, itb + 2) == b3);
                assert(s0.root_table_block(process, cursor_block(first.base, itb + 2)));
                assert(witness_block(s0, b3, first));
                lemma_block_page(b3, 0);
                assert(b3 / PAGE_SZ == base / PAGE_SZ + 16);
                lemma_witness_block_kept(s0, s1, b3, first, (b2 / PAGE_SZ) as int, b2 / PAGE_SZ + 2);
                lemma_witness_block_kept(s1, s2, b3, first, (base / PAGE_SZ) as int, base / PAGE_SZ + 8);
                lemma_witness_block_kept(s2, s3, b3, first, (bt / PAGE_SZ) as int, bt / PAGE_SZ + 2);
                lemma_witness_block_kept(s3, s4, b3, first, (bl / PAGE_SZ) as int, bl / PAGE_SZ + 2);
                assert(s5.blocks == s4.blocks);
                assert(witness_block(s5, b3, first));
            }
        }
        ok1 && ok2 && ok3 && ok4 && ok5
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of two free ones past those boot's tables took from the first untyped: build a process at `base`
    /// with a thread bound to it, as witness_process_holds_capability does; move the thread capability,
    /// with control, into slot 2 of the process's leaf, through the process capability; then move the
    /// process capability into slot 3 of that leaf, through itself. Both moves succeed, and at the end
    /// the process is sealed: no table but its own names it, so the rely of
    /// kernel/verified/capability/rely.rs holds for it from the second move on. The use is a creator
    /// handing a built process itself. The thread is not started: start needs a placement, which no
    /// operation makes yet. See design/region-map-owns-the-address-space/.
    pub fn witness_built_process_sealed(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let thread = (base + 10 * PAGE_SZ) as usize;
                let bl = (base + 12 * PAGE_SZ) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& final(self).slot_holds(base, WITNESS_SEALED_THREAD_SLOT, (bl + 2) as usize, thread_of(thread))
                &&& final(self).slot_holds(base, WITNESS_SEALED_PROCESS_SLOT, (bl + 3) as usize, process_of(base))
                &&& bound_threads(&final(self).list, &final(self).tables).contains_key(thread)
                &&& bound_threads(&final(self).list, &final(self).tables)[thread] == base
                &&& final(self).sealed(base)
            }),
    {
        let ok0 = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let ghost s1 = *self;
        let ghost np = (base + 8 * PAGE_SZ + 1) as usize;
        let ghost nt = (base + 8 * PAGE_SZ + 2) as usize;
        let ghost thread = (base + 10 * PAGE_SZ) as usize;
        let ghost bl = (base + 12 * PAGE_SZ) as usize;
        let ghost tn = (bl + 2) as usize;
        let ghost pn = (bl + 3) as usize;
        proof {
            assert(s1.processes.records@.contains_key(base));
            assert(s1.tables.roots@.contains_key(base)) by {
                reveal(CapKernel::wf);
            }
            assert(index_ok(WITNESS_SEALED_THREAD_SLOT) && index_entry(WITNESS_SEALED_THREAD_SLOT) == 0 && index_slot(WITNESS_SEALED_THREAD_SLOT) == 2) by (compute_only);
            assert(index_ok(WITNESS_SEALED_PROCESS_SLOT) && index_entry(WITNESS_SEALED_PROCESS_SLOT) == 0 && index_slot(WITNESS_SEALED_PROCESS_SLOT) == 3) by (compute_only);
            assert(s1.tables.has_slot(&s1.list, base, WITNESS_SEALED_THREAD_SLOT));
            assert(s1.tables.has_slot(&s1.list, base, WITNESS_SEALED_PROCESS_SLOT));
            s1.lemma_slot(base, WITNESS_SEALED_THREAD_SLOT);
            s1.lemma_slot(base, WITNESS_SEALED_PROCESS_SLOT);
            assert(s1.tables.node_of(base, WITNESS_SEALED_THREAD_SLOT) == tn);
            assert(s1.tables.node_of(base, WITNESS_SEALED_PROCESS_SLOT) == pn);
            assert(!s1.list.nodes@[tn as int].live);
            assert(!s1.list.nodes@[pn as int].live);
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s1.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s1.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(!s1.cap_dead(nt));
            assert(s1.can_move_between(process, WITNESS_THREAD_SLOT, base, WITNESS_SEALED_THREAD_SLOT));
        }

        // The thread capability, with control, into slot 2 of the process's leaf, through the process
        // capability.
        let from1 = Position { through: None, index: WITNESS_THREAD_SLOT };
        let to1 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_SEALED_THREAD_SLOT };
        let ok1 = self.move_cap(process, from1, to1);
        let ghost s2 = *self;
        proof {
            assert(ok1);
            assert(Self::cap_moved_between(s1, s2, process, WITNESS_THREAD_SLOT, base, WITNESS_SEALED_THREAD_SLOT));
            assert(Self::caps_frame(s1, s2, nt, tn));
            assert(s2.payload_of(tn) == thread_of(thread));
            assert(s2.is_cap(tn));
            lemma_slot_kept_two(s1, s2, process, WITNESS_PROCESS_SLOT, nt, tn);
            lemma_slot_kept_two(s1, s2, base, WITNESS_SEALED_THREAD_SLOT, nt, tn);
            lemma_slot_kept_two(s1, s2, base, WITNESS_SEALED_PROCESS_SLOT, nt, tn);
            s1.lemma_slot(process, WITNESS_PROCESS_SLOT);
            Self::lemma_caps_frame(s1, s2, nt, tn, np);
            assert(s2.slot_holds(process, WITNESS_PROCESS_SLOT, np, process_of(base)));
            assert(!s2.list.nodes@[pn as int].live);
            assert(s2.processes.records == s1.processes.records);
            assert(s2.root_live(process));
            assert(s2.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s2.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(!s2.cap_dead(np));
            assert(s2.can_move_between(process, WITNESS_PROCESS_SLOT, base, WITNESS_SEALED_PROCESS_SLOT));
        }

        // The process capability into slot 3 of the process's leaf, through itself: the destination is
        // found before the source goes.
        let from2 = Position { through: None, index: WITNESS_PROCESS_SLOT };
        let to2 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_SEALED_PROCESS_SLOT };
        let ok2 = self.move_cap(process, from2, to2);
        proof {
            let s3 = *self;
            assert(ok2);
            assert(Self::cap_moved_between(s2, s3, process, WITNESS_PROCESS_SLOT, base, WITNESS_SEALED_PROCESS_SLOT));
            assert(Self::caps_frame(s2, s3, np, pn));
            assert(s3.payload_of(pn) == process_of(base));
            assert(s3.is_cap(pn));
            s2.lemma_slot(base, WITNESS_SEALED_THREAD_SLOT);
            lemma_slot_kept_two(s2, s3, base, WITNESS_SEALED_THREAD_SLOT, np, pn);
            lemma_slot_kept_two(s2, s3, base, WITNESS_SEALED_PROCESS_SLOT, np, pn);
            Self::lemma_caps_frame(s2, s3, np, pn, tn);
            assert(s3.slot_holds(base, WITNESS_SEALED_THREAD_SLOT, tn, thread_of(thread)));
            assert(s3.slot_holds(base, WITNESS_SEALED_PROCESS_SLOT, pn, process_of(base)));
            assert(block_refs(&s3.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(block_refs(&s3.blocks, BlockRef::Small(thread / PAGE_SZ)) == 1);
            s3.lemma_slot(base, WITNESS_SEALED_THREAD_SLOT);
            s3.lemma_slot(base, WITNESS_SEALED_PROCESS_SLOT);
            lemma_sealed_held_once(s3, base, pn, thread, tn);
        }
        ok0 && ok1 && ok2
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of two free ones past those boot's tables took from the first untyped: build a process at `base`
    /// holding an untyped in slot 1 of its leaf, as witness_process_holds_capability does; then claim
    /// that untyped out of the process's table into slot 259 of the root's own, through the process
    /// capability. The claim succeeds: the root's slot holds the untyped, under the root's untyped as
    /// before, the process's slot holds nothing, and the process is still live. The use is a creator
    /// taking back a capability it gave a process it controls. See design/process-holds-capabilities/.
    pub fn witness_root_claims_a_capability(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
                let u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
                let child = (base + 12 * PAGE_SZ + 1) as usize;
                let claimed = (base + 8 * PAGE_SZ + 3) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& final(self).slot_holds(process, WITNESS_CLAIM_SLOT, claimed, child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1))
                &&& final(self).list.is_child(u, claimed)
                &&& final(self).tables.has_slot(&final(self).list, base, WITNESS_CHILD_SLOT)
                &&& final(self).tables.node_of(base, WITNESS_CHILD_SLOT) == child
                &&& !final(self).is_cap(child)
                &&& witness_alive(*final(self), base)
            }),
    {
        let ok0 = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let ghost s1 = *self;
        let ghost first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost np = (base + 8 * PAGE_SZ + 1) as usize;
        let ghost child = (base + 12 * PAGE_SZ + 1) as usize;
        let ghost claimed = (base + 8 * PAGE_SZ + 3) as usize;
        proof {
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s1.root_live(process));
            assert(s1.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s1.destination_at(process, None) == Some(process));
            assert(s1.can_move_between(base, WITNESS_CHILD_SLOT, process, WITNESS_CLAIM_SLOT));
        }

        // The untyped, out of slot 1 of the process's leaf into slot 259 of the root's own table, through
        // the process capability: a claim.
        let from = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT };
        let to = Position { through: None, index: WITNESS_CLAIM_SLOT };
        let ok1 = self.move_cap(process, from, to);
        proof {
            let s2 = *self;
            assert(ok1);
            assert(Self::cap_moved_between(s1, s2, base, WITNESS_CHILD_SLOT, process, WITNESS_CLAIM_SLOT));
            assert(s2.payload_of(claimed) == child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1));
            assert(s2.is_cap(claimed));
            assert(child % PAGE_SZ != 0 && claimed % PAGE_SZ != 0);
            lemma_slot_kept_two(s1, s2, process, WITNESS_CLAIM_SLOT, child, claimed);
            lemma_slot_kept_two(s1, s2, base, WITNESS_CHILD_SLOT, child, claimed);
            assert(s1.list.parent@[child] == u);
            assert(s2.list.parent@ == moved_parent(s1.list.parent@, child, claimed));
            assert(s2.list.parent@.contains_key(claimed));
            assert(s2.list.parent@[claimed] == u);
            assert(s2.list.is_child(u, claimed));
        }
        ok0 && ok1
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of two free ones past those boot's tables took from the first untyped: build a process at `base`
    /// with an Inactive thread bound to it, as witness_process_holds_capability does; write `frame` as
    /// the thread's registers through the thread capability with control in slot 258, then read them
    /// back through it. The write succeeds exactly when the frame's program counter is a user address,
    /// and then the read returns the frame as the write made it a user frame. The use is a creator
    /// setting a thread's registers before it starts, and a handler reading a stopped thread's.
    pub fn witness_thread_registers(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
        registers: Registers,
    ) -> (ret: (bool, Option<Registers>))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret.0 == user_rip(registers.spec_pc()),
            ret.1 is Some,
            ret.0 ==> ret.1 == Some(user_frame(registers)),
            final(self).wf(),
    {
        let ok0 = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let ghost s1 = *self;
        let ghost thread = (base + 10 * PAGE_SZ) as usize;
        let ghost nt = (base + 8 * PAGE_SZ + 2) as usize;
        proof {
            assert(THREAD_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s1.root_live(process));
            assert(s1.payload_of(nt) == thread_of(thread));
            assert(!s1.cap_dead(nt));
            assert(s1.can_set_registers(process, WITNESS_THREAD_SLOT));
        }
        let ok1 = self.write_registers(process, WITNESS_THREAD_SLOT, registers);
        let ghost s2 = *self;
        proof {
            if ok1 {
                assert(Self::frame_written(s1, s2, thread, user_frame(registers)));
                assert(s2.threads.records@[thread].value().state is Inactive);
            } else {
                assert(s2 == s1);
            }
            assert(s2.tables == s1.tables && s2.list == s1.list && s2.processes == s1.processes);
            assert(s2.root_live(process));
            assert(s2.can_set_registers(process, WITNESS_THREAD_SLOT));
        }
        let read = self.read_registers(process, WITNESS_THREAD_SLOT);
        (ok0 && ok1, read)
    }

    /// From the end of the spawn witness, as the root: destroy the process through its capability in
    /// slot 257, delete the thread's capability, retype the thread's block, which unbinds the thread,
    /// delete the process's capability, retype the leaf in the process's table three times, which
    /// unlinks it, slices its one capability and frees it, load the process's space on core 0 and point
    /// core 0's base register at it as a core that ran it would have, point core 0's base register at
    /// `kernel_root` under KERNEL_TAG, as an idle core does once the process it ran is dead, retype the
    /// process's block, which retires the space now that no base register names it, retype it again,
    /// which refuses since core 0 still depends on the space, load the root's space on core 0, which
    /// leaves the retire in place, have core 0 acknowledge the retire's flush, retype the block a third
    /// time, which frees it, and retype a process at the same block into slot 257 again.
    /// Each step returns what a teardown driven by retype says, in this order, and at the end the root
    /// holds a capability to a live process at the same block. `kernel_root` is the kernel's own root,
    /// the one the model keeps and boot hands to no block, the only root a register naming no space
    /// holds. See design/teardown-driven-by-retype/.
    #[verifier::spinoff_prover]
    pub fn witness_process_block_retyped(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
        kernel_root: usize,
    ) -> (ret: (bool, bool, ReclaimStep, bool, ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, bool))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            old(self).spaces.kernel_root@ == kernel_root,
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret.0,
            ret.1,
            ret.2 is Slice,
            ret.3,
            ret.4 is Unlinked,
            ret.5 is Slice,
            ret.6 is Freed,
            ret.7 is Slice,
            ret.8 is Refused,
            ret.9 is Freed,
            ret.10,
            final(self).wf(),
            final(self).view().holds(process, (base + 8 * PAGE_SZ + 1) as usize),
            final(self).payload_of((base + 8 * PAGE_SZ + 1) as usize) == process_of(base),
            witness_alive(*final(self), base),
    {
        hide(CapKernel::wf);
        let ok0 = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let ghost r0 = *self;
        let ghost first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let b2 = base + PROCESS_BYTES;
        let bt = b2 + 2 * PAGE_SZ;
        let bl = b2 + 4 * PAGE_SZ;
        let ghost np = (b2 + 1) as usize;
        let ghost nt = (b2 + 2) as usize;
        let ghost child = (bl + 1) as usize;
        proof {
            assert(ok0);
            lemma2_to64();
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(base % PROCESS_BYTES == 0);
            assert(b2 % PROCESS_BYTES == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            lemma_block_page(b2, 4);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == base / PAGE_SZ + 10);
            assert(bl / PAGE_SZ == base / PAGE_SZ + 12);
            assert(bt == base + 10 * PAGE_SZ);
            assert(bl == base + 12 * PAGE_SZ);
            assert(np == base + 8 * PAGE_SZ + 1);
            assert(nt == base + 8 * PAGE_SZ + 2);
            // Where the four slots' nodes lie, and whose leaves they are in.
            r0.lemma_slot(process, ROOT_UNTYPED_SLOT);
            r0.lemma_slot(process, WITNESS_PROCESS_SLOT);
            r0.lemma_slot(process, WITNESS_THREAD_SLOT);
            r0.lemma_slot(base, WITNESS_CHILD_SLOT);
            assert(index_slot(ROOT_UNTYPED_SLOT) == 5 && index_slot(WITNESS_PROCESS_SLOT) == 1);
            assert(index_slot(WITNESS_THREAD_SLOT) == 2 && index_slot(WITNESS_CHILD_SLOT) == 1);
            assert(index_entry(WITNESS_CHILD_SLOT) == 0);
            assert(u % PAGE_SZ == 5 && np % PAGE_SZ == 1 && nt % PAGE_SZ == 2 && child % PAGE_SZ == 1);
            r0.lemma_slot_bound(u);
            r0.lemma_slot_bound(np);
            r0.lemma_slot_bound(nt);
            r0.lemma_slot_bound(child);
            // The root's leaf holding its untyped is the root's, the process's leaf the process's.
            assert(r0.tables.owner@[page_of(u)].0 == process);
            assert(r0.tables.owner@[bl].0 == base);
            assert(page_of(u) != bl);
            r0.lemma_process_cap(np);
            assert(r0.blocks.tracks_addr(base));
            assert(block_typed(&r0.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(r0.processes.records@.contains_key(base));
            assert(r0.tables.roots@.contains_key(base)) by {
                reveal(CapKernel::wf);
            }
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(r0.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(r0.list.parent@[child] == u);
            assert(r0.payload_of(child).kind is Untyped);
            assert(r0.can_destroy(process, WITNESS_PROCESS_SLOT));
        }

        // Destroy the process, through its capability in slot 257 of the root's table.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.destroy(0, process, WITNESS_PROCESS_SLOT, Tracked(&mut steps));
        let ghost r1 = *self;
        let at_thread = Position { through: None, index: WITNESS_THREAD_SLOT };
        proof {
            assert(ok1);
            assert(r0.payload_of(np).base == base);
            assert(Self::process_destroyed(r0, r1, base));
            assert(r1.list == r0.list && r1.tables == r0.tables && r1.blocks == r0.blocks);
            assert(r1.processes.records@[process] == r0.processes.records@[process]);
            assert(r1.processes.records@.contains_key(base));
            assert(r1.root_live(process));
            // The thread's capability can go: it is in the root's slot 258, deeper than the first node,
            // and has no child.
            assert(r1.table_at(process, None) == Some(process));
            assert(r1.slot_holds(process, WITNESS_THREAD_SLOT, nt, thread_of(bt)));
            lemma_owned_listed(r1, nt);
            assert(r1.list.childless(nt));
            assert(r1.cap_at(process, at_thread) == Some(nt));
            assert(r1.can_delete_at(process, at_thread));
        }

        // Delete the thread's capability.
        let ok2 = self.delete(process, at_thread);
        let ghost r2 = *self;
        proof {
            assert(ok2 is Some);
            assert(Self::cap_deleted_at(r1, r2, process, at_thread));
            assert(Self::object_dropped(r1, r2, nt));
            assert(r1.payload_of(nt).kind is Thread);
            assert(blocks_refs_changed(&r1.blocks, &r2.blocks, BlockRef::Small(bt / PAGE_SZ), 0, block_dead(&r1.blocks, BlockRef::Small(bt / PAGE_SZ)) || true));
            assert(r2.blocks.pages@[(bt / PAGE_SZ) as int].refs == 0);
            assert(block_typed(&r2.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(block_refs(&r2.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            lemma_deleted_dead(r2, nt);
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r2.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != nt {
                    assert(r2.list.nodes@[i].live == r1.list.nodes@[i].live);
                }
            }
            assert(r2.list.parent@ == r0.list.parent@);
            assert(r2.tables == r0.tables);
            assert(r2.processes == r1.processes);
            assert(r2.spaces == r0.spaces);
            assert(r2.threads.records == r0.threads.records);
            assert(r2.root_live(process));
            assert(r2.tables.roots@.contains_key(process));
            // The root's untyped is still its slot 5, and can retype the thread's block.
            lemma_slot_kept_but(r1, r2, process, ROOT_UNTYPED_SLOT, nt);
            Self::lemma_caps_frame(r1, r2, nt, nt, u);
            assert(r2.list.nodes@[child as int].live == r1.list.nodes@[child as int].live);
            assert(r2.list.nodes@[child as int].live);
            assert(r2.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r2, child);
            assert(r2.list.d(u) < MAX_DEPTH);
            assert(r2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(r2.threads.records@[bt].value().process == Some(base));
            assert(r2.thread_is_dead(bt));
            assert(r2.can_unbind_thread(process, ROOT_UNTYPED_SLOT, bt));
        }

        // Retype the thread's block: the thread is dead, so the retype unbinds it from the process.
        let ok3 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bt, Tracked(&mut steps));
        let ghost r3 = *self;
        let at_process = Position { through: None, index: WITNESS_PROCESS_SLOT };
        proof {
            assert(ok3 is Slice);
            assert(r2.thread_unbound(r3, process, ROOT_UNTYPED_SLOT, bt));
            assert(Self::unbound(r2, r3, bt));
            assert(block_refs(&r3.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(block_typed(&r3.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r3.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != bt {
                    assert(r3.list.nodes@[i].live == r2.list.nodes@[i].live);
                    assert(r2.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r3.list.parent@ == r0.list.parent@);
            assert(r3.tables == r0.tables);
            assert(r3.processes.records == r0.processes.records || r3.processes.records == r1.processes.records);
            assert(r3.root_live(process));
            assert(r3.spaces == r0.spaces);
            // The slots of the root's leaves stay: the thread's block is no leaf of the root's, since an
            // owned leaf whose node is live holds one reference.
            assert(!r2.list.nodes@[bt as int].live || !r2.tables.owner@.contains_key(bt)) by {
                reveal(CapKernel::wf);
            }
            lemma_slot_kept_but(r1, r2, process, WITNESS_PROCESS_SLOT, nt);
            lemma_slot_kept_but(r2, r3, process, WITNESS_PROCESS_SLOT, bt);
            lemma_slot_kept_but(r2, r3, process, ROOT_UNTYPED_SLOT, bt);
            // The process's capability can go: its only child was the thread's binding.
            assert(r3.list.nodes@[np as int].live == r2.list.nodes@[np as int].live);
            assert(r3.list.nodes@[np as int].kind == r2.list.nodes@[np as int].kind);
            Self::lemma_caps_frame(r1, r2, nt, nt, np);
            assert(r3.is_cap(np));
            assert(r3.payload_of(np) == process_of(base));
            assert(r3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r3, np);
            lemma_children_back(r0.list, r2.list, np);
            assert forall|c: usize| #[trigger] r2.list.is_child(np, c) implies c == bt by {
                assert(r0.list.is_child(np, c));
            }
            assert(r3.list.childless(np));
            assert(r3.table_at(process, None) == Some(process));
            assert(r3.cap_at(process, at_process) == Some(np));
            assert(r3.can_delete_at(process, at_process));
        }

        // Delete the process's capability.
        let ok4 = self.delete(process, at_process);
        let ghost r4 = *self;
        proof {
            assert(ok4 is Some);
            assert(Self::cap_deleted_at(r3, r4, process, at_process));
            assert(Self::object_dropped(r3, r4, np));
            assert(block_refs(&r4.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r4.blocks, BlockRef::Small(base / PAGE_SZ)));
            lemma_deleted_dead(r4, np);
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r4.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != np {
                    assert(r4.list.nodes@[i].live == r3.list.nodes@[i].live);
                    assert(r3.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r4.list.parent@ == r0.list.parent@);
            assert(r4.tables == r0.tables);
            assert(r4.processes.records == r3.processes.records);
            assert(r4.root_live(process));
            assert(r4.spaces == r0.spaces);
            lemma_slot_kept_but(r3, r4, process, WITNESS_PROCESS_SLOT, np);
            lemma_slot_kept_but(r3, r4, process, ROOT_UNTYPED_SLOT, np);
            Self::lemma_caps_frame(r3, r4, np, np, u);
            assert(r3.list.nodes@[u as int].live == r2.list.nodes@[u as int].live);
            assert(r3.list.nodes@[u as int].kind == r2.list.nodes@[u as int].kind);
            assert(r3.is_cap(u));
            assert(r4.is_cap(u));
            // The leaf in the process's table is still live: only slots died.
            assert(r4.list.nodes@[bl as int].live == r3.list.nodes@[bl as int].live);
            assert(r3.list.nodes@[bl as int].live == r2.list.nodes@[bl as int].live);
            assert(r2.list.nodes@[bl as int].live == r1.list.nodes@[bl as int].live);
            assert(r4.list.nodes@[bl as int].live);
            assert(r4.list.nodes@[child as int].live == r3.list.nodes@[child as int].live);
            assert(r3.list.nodes@[child as int].live == r2.list.nodes@[child as int].live);
            assert(r4.list.nodes@[child as int].live);
            assert(r4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r4, child);
            assert(r4.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(r4.can_unlink_leaf(process, ROOT_UNTYPED_SLOT, bl));
        }

        // Retype the process's leaf: its hidden node is live, so the retype unlinks it.
        let ok5 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r5 = *self;
        proof {
            assert(ok5 is Unlinked);
            assert(r4.leaf_unlinked(r5, process, ROOT_UNTYPED_SLOT, bl));
            assert(block_refs(&r5.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r5.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r5.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != bl {
                    assert(r5.list.nodes@[i].live == r4.list.nodes@[i].live);
                    assert(r4.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r5.list.parent@ == r0.list.parent@);
            assert(r5.tables == r0.tables);
            assert(r5.root_live(process));
            assert(r5.spaces == r0.spaces);
            assert(r5.flush_epoch == 0);
            lemma_slot_kept_but(r4, r5, process, ROOT_UNTYPED_SLOT, bl);
            lemma_slot_kept_but(r4, r5, process, WITNESS_PROCESS_SLOT, bl);
            assert(r5.is_cap(u));
            assert(r5.list.nodes@[child as int].live == r4.list.nodes@[child as int].live);
            assert(r5.list.nodes@[child as int].live);
            assert(r5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r5, child);
            assert(r5.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            // The leaf's one live slot is the derived untyped, which has no child.
            assert(r5.list.nodes@[bl + 1].live);
            assert(!r5.leaf_is_empty(bl));
            assert(r5.can_slice_leaf(process, ROOT_UNTYPED_SLOT, bl));
            assert forall|x: int| bl + 2 <= x < bl + NODES_PER_PAGE implies !#[trigger] r5.list.nodes@[x].live by {
                assert(!r0.list.nodes@[x].live);
            }
            lemma_children_back(r0.list, r5.list, child);
            if !r5.list.childless(child) {
                r5.list.lemma_next_is_child(child);
                assert(r0.list.is_child(child, r5.list.nodes@[child as int].next));
            }
            assert forall|j: int| 1 <= j < NODES_PER_PAGE && (#[trigger] r5.list.nodes@[bl + j]).live
                implies r5.list.childless((bl + j) as usize) by {
                if j != 1 {
                    assert(!r5.list.nodes@[bl + j].live);
                }
            }
            assert(r5.leaf_slots_childless(bl));
            lemma_live_slots_none(r5, bl, 2);
            assert(r5.leaf_live_slots(bl) == 1);
            // No slot of the leaf names the process's block: its one capability is an untyped.
            assert(r5.payload_of(child).kind is Untyped);
            assert(!r5.leaf_slot_names(bl, BlockRef::Small(base / PAGE_SZ))) by {
                if r5.leaf_slot_names(bl, BlockRef::Small(base / PAGE_SZ)) {
                    let n = choose|n: usize| bl < n < bl + NODES_PER_PAGE && #[trigger] r5.cap_names_block(n, BlockRef::Small(base / PAGE_SZ));
                    if n != child {
                        assert(!r5.list.nodes@[n as int].live);
                    }
                }
            }
        }

        // Retype the leaf again: its hidden node is gone, so the retype slices its slots.
        let ok6 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r6 = *self;
        proof {
            assert(ok6 is Slice);
            assert(r5.leaf_slice_kept(r6, bl));
            assert(r6.leaf_is_empty(bl));
            assert(block_refs(&r6.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r6.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(r6.tables == r0.tables);
            assert(r6.root_live(process));
            assert(r6.spaces.roots == r0.spaces.roots);
            assert(r6.spaces.loaded == r0.spaces.loaded);
            assert(r6.processes.records == r1.processes.records);
            assert(r6.tables.has_slot(&r6.list, process, ROOT_UNTYPED_SLOT));
            assert(r6.tables.has_slot(&r6.list, process, WITNESS_PROCESS_SLOT));
            assert(r6.is_cap(u));
            assert(r6.list.nodes@[u as int].depth == r5.list.nodes@[u as int].depth);
            assert(r6.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(r6.list.nodes@[np as int].live == r5.list.nodes@[np as int].live);
            assert(!r6.list.nodes@[np as int].live);
            Self::lemma_acknowledged_kept(r0, r6, bl / PAGE_SZ);
            Self::lemma_acknowledged_kept(r0, r6, (bl / PAGE_SZ + 1) as usize);
        }

        // Retype the leaf a third time: it is empty, so the retype frees it.
        let ok7 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r7 = *self;
        proof {
            assert(ok7 is Freed);
            assert(r6.leaf_freed(r7, 0, process, ROOT_UNTYPED_SLOT, bl));
            assert(r6.tables.owner@[bl] == (base, 0int));
            assert(r7.tables.leaf(base, 0) == NO_LEAF);
            assert forall|r: int| 0 <= r < ROOT_ENTRIES implies #[trigger] r7.tables.leaf(base, r) == NO_LEAF by {
                if r != 0 {
                    assert(r7.tables.leaf(base, r) == r6.tables.leaf(base, r));
                }
            }
            assert(r7.tables.roots@.dom().contains(process));
            assert(r7.tables.leaf(process, 0) == r6.tables.leaf(process, 0));
            assert(r7.tables.leaf(process, 2) == r6.tables.leaf(process, 2));
            assert(r7.tables.has_slot(&r7.list, process, ROOT_UNTYPED_SLOT));
            assert(r7.tables.has_slot(&r7.list, process, WITNESS_PROCESS_SLOT));
            assert(r7.tables.is_cap(&r7.list, u));
            assert(r7.payload_of(u) == first);
            assert(r7.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(r6.blocks.tracks((base / PAGE_SZ) as int));
            assert(r7.blocks.pages@[(base / PAGE_SZ) as int] == r6.blocks.pages@[(base / PAGE_SZ) as int]);
            assert(r7.process_is_dead(base));
            assert(r7.process_unloaded(base));
            r7.lemma_unloaded_released(base);
            assert forall|i: usize| KERNEL_MEM_END_L4INDEX <= i < ENTRIES implies #[trigger] r7.spaces.roots@[base].value()[i].is_empty() by {
                assert(!holds_kernel(SpaceKind::Process, i));
                assert(r0.spaces.roots@[base].value()[i].is_empty());
            }
            assert(r7.process_is_spent(base));
            Self::lemma_acknowledged_kept(r0, r7, base / PAGE_SZ);
            assert(r7.processes.records@.contains_key(base));
            // The process's block is still typed, so no typed large block covers it.
            r7.lemma_process_block(base);
            assert(r7.blocks.wf()) by {
                reveal(CapKernel::wf);
            }
            r7.blocks.lemma_not_free_uncovered((base / PAGE_SZ) as int);
            assert(r7.cores@[0].current_thread is None);
            assert(r7.tlb_wf()) by {
                reveal(CapKernel::wf);
            }
        }

        // Load the process's space on core 0, which runs nothing, and point core 0's base register at it,
        // as a core that ran its thread would have.
        proof {
            assert(space_wf(&r7.list, &r7.spaces, &r7.blocks, base)) by {
                reveal(CapKernel::wf);
            }
            assert(r7.processes.records@.contains_key(process));
            assert(process_spaces_wf(&r7.spaces, &r7.processes)) by {
                reveal(CapKernel::wf);
            }
            assert(r7.spaces.roots@.contains_key(process));
            assert(r7.spaces.records@[process].value().kind is Process);
            assert(space_wf(&r7.list, &r7.spaces, &r7.blocks, process)) by {
                reveal(CapKernel::wf);
            }
            assert(process != base);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] r7.cores@[d].space != Some(base) by {
                if r7.cores@[d].space == Some(base) {
                    r7.lemma_named_depends(d, base);
                    lemma_no_core_listed(d as u32);
                }
            }
        }
        // Core 0 points its base register at a root naming no space first, under KERNEL_TAG, which no
        // space holds: a core loads a space only while its register names no space or that one.
        self.switch_space(0, None, kernel_root, KERNEL_TAG);
        let ghost s7 = *self;
        proof {
            assert(s7.spaces == (Spaces { registers: s7.spaces.registers, ..r7.spaces }));
            assert forall|d: int| 0 <= d < NUM_CPUS && d != 0 implies #[trigger] s7.cores@[d] == r7.cores@[d] by {}
        }
        let pcid = self.load_space(0, base, Tracked(&mut steps));
        let ghost m7 = *self;
        self.switch_space(0, Some(base), base + SPACE_ROOT_PAGE * PAGE_SZ, pcid);
        let ghost n7 = *self;
        proof {
            assert(n7.cores@[0].space == Some(base));
            assert(n7.cores@[0].generation <= 2);
            assert(n7.spaces.roots@.contains_key(process));
            assert(n7.spaces == (Spaces { registers: n7.spaces.registers, ..m7.spaces }));
        }

        // Core 0 leaves the dead process's space for a root naming no space, under KERNEL_TAG, which no
        // space holds, so no base register names the space a retire would end.
        self.switch_space(0, None, kernel_root, KERNEL_TAG);
        let ghost l7 = *self;
        proof {
            assert(l7.spaces == (Spaces { registers: l7.spaces.registers, ..n7.spaces }));
            assert(l7.loaded(0, base));
            assert(l7.spaces.loaded@[base].value().retired == 0);
            assert(l7.depends(0, base));
            assert(!l7.process_released(base));
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] l7.cores@[d].space != Some(base) by {
                if d != 0 {
                    assert(s7.cores@[d] == r7.cores@[d]);
                    assert(l7.cores@[d] == r7.cores@[d]);
                }
            }
            assert(!l7.process_space_named(base));
            // The load listed no other core on the dead process's space.
            assert forall|d: int| 0 < d < NUM_CPUS implies !#[trigger] l7.loaded(d, base) by {
                assert(l7.loaded(d, base) == n7.loaded(d, base));
                assert(n7.loaded(d, base) == m7.loaded(d, base));
                assert(m7.loaded(d, base) == s7.loaded(d, base));
                assert(s7.loaded(d, base) == r7.loaded(d, base));
                lemma_no_core_listed(d as u32);
                assert(!r7.loaded(d, base));
            }
            assert(l7.list == r7.list && l7.tables == r7.tables && l7.blocks == r7.blocks);
            assert(l7.processes == r7.processes);
            assert(l7.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(l7.process_is_dead(base));
            assert(l7.flush_epoch == r7.flush_epoch);
            assert(r6.flush_epoch == r5.flush_epoch);
            assert(l7.flush_epoch == 0);
            assert(l7.can_retire_process(process, ROOT_UNTYPED_SLOT, base));
            assert(l7.root_live(process));
        }

        // Retype the process's block: core 0 depends on its space, so the retype retires it.
        let ok8a = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        let ghost t7 = *self;
        proof {
            assert(ok8a is Slice);
            assert(l7.process_retired(t7, base));
            assert(t7.depends(0, base) == l7.depends(0, base));
            assert(!t7.process_released(base));
            assert(t7.spaces.loaded@[base].value().retired == 1);
            assert(!t7.can_retire_process(process, ROOT_UNTYPED_SLOT, base));
            assert(t7.processes.records@.contains_key(base));
            assert(t7.tables == l7.tables);
            assert(t7.root_live(process));
        }

        // Retype it again: core 0 has not acknowledged the retire's flush, so the retype refuses.
        let ok8b = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        proof {
            assert(ok8b is Refused);
            assert(*self == t7);
            assert(t7.spaces.roots@.contains_key(process));
            assert(t7.spaces.records@[process].value().kind is Process);
            assert(t7.cores@[0].generation <= 3);
        }

        // Core 0 loads the root's space before it takes the retire's flush, as a core entering the root's
        // thread does, and the load leaves the retire of the dead process's space in place.
        self.load_space(0, process, Tracked(&mut steps));
        let ghost j7 = *self;
        proof {
            assert(j7.spaces.loaded@[base] == t7.spaces.loaded@[base]);
            assert(j7.tlb_wf()) by {
                reveal(CapKernel::wf);
            }
            assert(j7.acked(0) <= j7.flush_epoch);
        }

        // Core 0 flushes every context and acknowledges the retire's epoch.
        self.acknowledge(0, Tracked(&mut steps));
        let ghost a7 = *self;
        proof {
            let f = base / PAGE_SZ;
            assert(a7.acked(0) == 1);
            assert(r7.acked(0) <= r7.flush_epoch);
            assert forall|d: int| 0 <= d < NUM_CPUS implies r7.acked(d) <= #[trigger] a7.acked(d) by {
                if d != 0 {
                    assert(a7.cores@[d] == j7.cores@[d]);
                    assert(j7.cores@[d] == t7.cores@[d]);
                    assert(l7.cores@[d] == r7.cores@[d]);
                }
            }
            assert(a7.stale_epoch == r7.stale_epoch);
            assert(a7.iommus == r7.iommus);
            assert(a7.blocks == r7.blocks);
            assert(a7.acknowledged(f)) by {
                let x = r7.stale_epoch.pages@[f as int] as int;
                assert forall|d: int| 0 <= d < NUM_CPUS implies x <= #[trigger] a7.acked(d) by {
                    assert(x <= r7.acked(d));
                    assert(r7.acked(d) <= a7.acked(d));
                }
                assert forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] a7.iommu_present(i) implies x <= a7.iommu_acked(i) by {
                    assert(r7.iommu_present(i));
                }
            }
            // Core 0 is past the retire, and no other core has the space loaded.
            assert(a7.spaces == j7.spaces);
            assert forall|d: int| 0 <= d < NUM_CPUS implies !#[trigger] a7.depends(d, base) by {
                if d == 0 {
                    assert(a7.past_retire(0, base));
                } else {
                    assert(t7.spaces.loaded@[base].value().list == l7.spaces.loaded@[base].value().list);
                    assert(!l7.loaded(d, base));
                    assert(!a7.loaded(d, base));
                }
            }
            assert(a7.process_released(base));
            assert(a7.list == r7.list && a7.tables == r7.tables && a7.processes == r7.processes);
            assert(a7.spaces.roots == r7.spaces.roots);
            assert(a7.process_is_spent(base));
            assert(a7.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(a7.root_live(process));
            a7.lemma_process_block(base);
            assert(a7.blocks.wf()) by {
                reveal(CapKernel::wf);
            }
            a7.blocks.lemma_not_free_uncovered((base / PAGE_SZ) as int);
        }

        // Retype the process's block a third time: the process is spent, so the retype frees it.
        let ok8 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        let ghost r8 = *self;
        proof {
            assert(ok8 is Freed);
            assert(a7.process_freed(r8, 0, process, ROOT_UNTYPED_SLOT, base));
            assert(r8.tables.roots@[process] == a7.tables.roots@[process]);
            assert(r8.tables.roots@.contains_key(process));
            assert(r8.processes.records@[process] == a7.processes.records@[process]);
            assert(r8.root_live(process));
            assert(r8.tables.leaf(process, 0) == a7.tables.leaf(process, 0));
            assert(r8.tables.leaf(process, 2) == a7.tables.leaf(process, 2));
            assert(r8.tables.has_slot(&r8.list, process, ROOT_UNTYPED_SLOT));
            assert(r8.tables.has_slot(&r8.list, process, WITNESS_PROCESS_SLOT));
            assert(r8.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(!r8.list.nodes@[np as int].live);
            assert(r8.is_cap(u));
            assert(r8.payload_of(u) == first);
            assert(r8.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(!r8.blocks.covered((base / PAGE_SZ) as int));
            assert(r8.blocks.small_free((base / PAGE_SZ) as int, PROCESS_ORDER as usize)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] r8.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(r8.blocks.pages@[(base / PAGE_SZ) + k].kind is Free);
                }
            }
            assert(r8.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }

        // Retype a process at the same block into slot 257 again.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok9 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, Tracked(&mut steps));
        proof {
            assert(ok9);
            assert(np == base + 8 * PAGE_SZ + 1);
        }
        (ok1, ok2.is_some(), ok3, ok4.is_some(), ok5, ok6, ok7, ok8a, ok8b, ok8, ok9)
    }

    /// From the end of the spawn witness, as the root, with a third free order-3 block past the two the
    /// spawn took: give the process's space a level 3 table at entry KERNEL_MEM_END_L4INDEX of its root,
    /// the first entry outside the kernel's, through the capability to the process in slot 257, and
    /// tear the process down by retype as the spawn's teardown does, up to its space: destroy the
    /// process, delete the thread's capability, retype the thread's block, which unbinds the thread,
    /// delete the process's capability, its last reference, and retype the leaf in the process's table
    /// until it is free. No core ran the process, so its space is released. The process is dead and its
    /// root still names the table, so the first retype of its block cuts the table from the root:
    /// the table's parent record goes and the root names no child. After every core and IOMMU
    /// acknowledges the cut's flush, the next retype frees the block, and a process is retyped at the
    /// same block into slot 257 again. The use is a process whose space grew tables before it died.
    /// See design/teardown-driven-by-retype/.
    #[verifier::spinoff_prover]
    pub fn witness_process_space_cut(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
    ) -> (ret: (ReclaimStep, ReclaimStep, bool, Ghost<CapKernel>, Ghost<CapKernel>))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 3 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret.0 is Slice,
            ret.1 is Freed,
            ret.2,
            ret.3@.process_is_dead(base),
            tree_of(&ret.3@.table_pages, &ret.3@.spaces).names_child(base, KERNEL_MEM_END_L4INDEX),
            ret.3@.process_space_cut(ret.4@, process, ROOT_UNTYPED_SLOT, base),
            tree_of(&ret.4@.table_pages, &ret.4@.spaces).record((base + 2 * PROCESS_BYTES) as usize).parent is None,
            forall|e: usize| !#[trigger] tree_of(&ret.4@.table_pages, &ret.4@.spaces).names_child(base, e),
            final(self).wf(),
            final(self).view().holds(process, (base + 8 * PAGE_SZ + 1) as usize),
            final(self).payload_of((base + 8 * PAGE_SZ + 1) as usize) == process_of(base),
            witness_alive(*final(self), base),
    {
        hide(CapKernel::wf);
        let ok0 = self.witness_process_holds_capability(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let ghost h0 = *self;
        let ghost first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let b2 = base + PROCESS_BYTES;
        let bt = b2 + 2 * PAGE_SZ;
        let bl = b2 + 4 * PAGE_SZ;
        let b3 = base + 2 * PROCESS_BYTES;
        let ghost np = (b2 + 1) as usize;
        let ghost nt = (b2 + 2) as usize;
        let ghost child = (bl + 1) as usize;
        let ghost dp = h0.list.nodes@[np as int].depth;
        let ghost dt = h0.list.nodes@[nt as int].depth;
        let ghost dc = h0.list.nodes@[child as int].depth;
        let ghost ta = tree_of(&h0.table_pages, &h0.spaces);
        proof {
            assert(ok0);
            lemma2_to64();
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(base % PROCESS_BYTES == 0);
            assert(b2 % PROCESS_BYTES == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            lemma_block_page(b2, 4);
            lemma_block_page(b3, 0);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == base / PAGE_SZ + 10);
            assert(bl / PAGE_SZ == base / PAGE_SZ + 12);
            assert(b3 / PAGE_SZ == base / PAGE_SZ + 16);
            assert(bt == base + 10 * PAGE_SZ);
            assert(bl == base + 12 * PAGE_SZ);
            assert(np == base + 8 * PAGE_SZ + 1);
            assert(nt == base + 8 * PAGE_SZ + 2);
            assert(witness_block(h0, b3, first));
            // The process's space is a root of kind Process at level 4, whose entry past the kernel's is
            // empty and can hold a child.
            assert(h0.blocks.tracks_addr(base));
            h0.lemma_process_block(base);
            assert(!ta.is_page(base));
            assert(ta.is_table(base));
            h0.lemma_table_base(base);
            assert(ta.record(base).space == Some(base));
            assert(ta.record(base).level == 4);
            assert(!holds_kernel(SpaceKind::Process, KERNEL_MEM_END_L4INDEX));
            assert(ta.child_slot(base, KERNEL_MEM_END_L4INDEX));
            assert(ta.entry(base, KERNEL_MEM_END_L4INDEX).is_empty());
            assert(witness_slot(h0, process, ROOT_UNTYPED_SLOT, u, first, 1));
            assert(witness_root(h0, process, u, first));
            assert(witness_slot(h0, process, WITNESS_PROCESS_SLOT, np, process_of(base), dp));
        }

        // Give the process's space a table at the first entry past the kernel's, through its capability.
        self.witness_table(process, WITNESS_PROCESS_SLOT, base, KERNEL_MEM_END_L4INDEX, 3, b3, Ghost(base), Ghost(np), Ghost(dp), Ghost(u), Ghost(first));
        let ghost r0 = *self;
        let ghost tk = tree_of(&r0.table_pages, &r0.spaces);
        proof {
            assert(r0.wf());
            assert(step(tk, base, KERNEL_MEM_END_L4INDEX) == Some(b3));
            assert(tk.names_child(base, KERNEL_MEM_END_L4INDEX));
            assert(child_at(tk, base, KERNEL_MEM_END_L4INDEX) == b3);
            // What the teardown reads of the spawn's end, kept by the table's retype and link.
            assert(h0.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(r0.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(witness_slot(h0, process, WITNESS_THREAD_SLOT, nt, thread_of(bt), dt));
            assert(witness_slot(h0, base, WITNESS_CHILD_SLOT, child, child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1), dc));
            lemma_witness_slot_kept(h0, r0, process, ROOT_UNTYPED_SLOT, u, first, 1);
            lemma_witness_slot_kept(h0, r0, process, WITNESS_PROCESS_SLOT, np, process_of(base), dp);
            lemma_witness_slot_kept(h0, r0, process, WITNESS_THREAD_SLOT, nt, thread_of(bt), dt);
            lemma_witness_slot_kept(h0, r0, base, WITNESS_CHILD_SLOT, child, child_of(first, UNTYPED_RIGHTS, (base + 14 * PAGE_SZ) as usize, 1), dc);
            h0.lemma_slot_bound(u);
            assert(u != b3);
            lemma_added_children(h0.list, r0.list, b3, u);
            assert(r0.list.parent@[b3] == u);
            assert(r0.list.parent@[child] == h0.list.parent@[child]);
            assert forall|c: usize| !#[trigger] r0.list.is_child(nt, c) by {
                if r0.list.is_child(nt, c) && c != b3 {
                    assert(h0.list.is_child(nt, c));
                }
            }
            assert forall|c: usize| #[trigger] r0.list.is_child(np, c) implies c == bt by {
                if c != b3 {
                    assert(h0.list.is_child(np, c));
                }
            }
            assert forall|c: usize| !#[trigger] r0.list.is_child(child, c) by {
                if r0.list.is_child(child, c) && c != b3 {
                    assert(h0.list.is_child(child, c));
                }
            }
            assert(r0.list.nodes@[nt as int].live);
            assert(r0.list.nodes@[child as int].live);
            if !r0.list.childless(nt) {
                r0.list.lemma_next_is_child(nt);
            }
            if !r0.list.childless(child) {
                r0.list.lemma_next_is_child(child);
            }
            assert(r0.list.childless(nt));
            assert(r0.list.childless(child));
            // The leaf in the process's table is live and hidden, with no live node past its slot 1.
            lemma_listed_live(h0.list, child);
            h0.list.lemma_live_valid(bl);
            assert(r0.list.nodes@[bl as int].live);
            assert(r0.list.nodes@[bl as int].kind is Hidden);
            assert forall|x: int| bl + 1 < x < bl + NODES_PER_PAGE implies !#[trigger] r0.list.nodes@[x].live by {
                assert(!h0.list.nodes@[x].live);
            }
            // The blocks outside the table's are as they were.
            assert(r0.blocks.pages@[(bt / PAGE_SZ) as int] == h0.blocks.pages@[(bt / PAGE_SZ) as int]);
            assert(r0.blocks.pages@[(base / PAGE_SZ) as int] == h0.blocks.pages@[(base / PAGE_SZ) as int]);
            assert(r0.blocks.pages@[(bl / PAGE_SZ) as int] == h0.blocks.pages@[(bl / PAGE_SZ) as int]);
            assert(block_refs(&r0.blocks, BlockRef::Small(bt / PAGE_SZ)) == 1);
            assert(block_refs(&r0.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            assert(r0.process_unloaded(base));
            assert(bound_threads(&r0.list, &r0.tables).contains_key(bt));
            assert(bound_threads(&r0.list, &r0.tables)[bt] == base);
            assert(r0.flush_epoch == 0);
            assert(witness_alive(r0, base));
            assert(witness_alive(r0, process));
            assert(r0.tables.owner@[bl] == (base, 0int));
        }
        proof {
            // Where the four slots' nodes lie, and whose leaves they are in.
            r0.lemma_slot(process, ROOT_UNTYPED_SLOT);
            r0.lemma_slot(process, WITNESS_PROCESS_SLOT);
            r0.lemma_slot(process, WITNESS_THREAD_SLOT);
            r0.lemma_slot(base, WITNESS_CHILD_SLOT);
            assert(index_slot(ROOT_UNTYPED_SLOT) == 5 && index_slot(WITNESS_PROCESS_SLOT) == 1);
            assert(index_slot(WITNESS_THREAD_SLOT) == 2 && index_slot(WITNESS_CHILD_SLOT) == 1);
            assert(index_entry(WITNESS_CHILD_SLOT) == 0);
            assert(u % PAGE_SZ == 5 && np % PAGE_SZ == 1 && nt % PAGE_SZ == 2 && child % PAGE_SZ == 1);
            r0.lemma_slot_bound(u);
            r0.lemma_slot_bound(np);
            r0.lemma_slot_bound(nt);
            r0.lemma_slot_bound(child);
            // The root's leaf holding its untyped is the root's, the process's leaf the process's.
            assert(r0.tables.owner@[page_of(u)].0 == process);
            assert(r0.tables.owner@[bl].0 == base);
            assert(page_of(u) != bl);
            r0.lemma_process_cap(np);
            assert(r0.blocks.tracks_addr(base));
            assert(block_typed(&r0.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(r0.processes.records@.contains_key(base));
            assert(r0.tables.roots@.contains_key(base)) by {
                reveal(CapKernel::wf);
            }
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(r0.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(r0.list.parent@[child] == u);
            assert(r0.payload_of(child).kind is Untyped);
            assert(r0.can_destroy(process, WITNESS_PROCESS_SLOT));
        }

        // Destroy the process, through its capability in slot 257 of the root's table.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.destroy(0, process, WITNESS_PROCESS_SLOT, Tracked(&mut steps));
        let ghost r1 = *self;
        let at_thread = Position { through: None, index: WITNESS_THREAD_SLOT };
        proof {
            assert(ok1);
            assert(r0.payload_of(np).base == base);
            assert(Self::process_destroyed(r0, r1, base));
            assert(r1.list == r0.list && r1.tables == r0.tables && r1.blocks == r0.blocks);
            assert(r1.processes.records@[process] == r0.processes.records@[process]);
            assert(r1.processes.records@.contains_key(base));
            assert(r1.root_live(process));
            // The thread's capability can go: it is in the root's slot 258, deeper than the first node,
            // and has no child.
            assert(r1.table_at(process, None) == Some(process));
            assert(r1.slot_holds(process, WITNESS_THREAD_SLOT, nt, thread_of(bt)));
            lemma_owned_listed(r1, nt);
            assert(r1.list.childless(nt));
            assert(r1.cap_at(process, at_thread) == Some(nt));
            assert(r1.can_delete_at(process, at_thread));
        }

        // Delete the thread's capability.
        let ok2 = self.delete(process, at_thread);
        let ghost r2 = *self;
        proof {
            assert(ok2 is Some);
            assert(Self::cap_deleted_at(r1, r2, process, at_thread));
            assert(Self::object_dropped(r1, r2, nt));
            assert(r1.payload_of(nt).kind is Thread);
            assert(blocks_refs_changed(&r1.blocks, &r2.blocks, BlockRef::Small(bt / PAGE_SZ), 0, block_dead(&r1.blocks, BlockRef::Small(bt / PAGE_SZ)) || true));
            assert(r2.blocks.pages@[(bt / PAGE_SZ) as int].refs == 0);
            assert(block_typed(&r2.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(block_refs(&r2.blocks, BlockRef::Small(base / PAGE_SZ)) == 2);
            lemma_deleted_dead(r2, nt);
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r2.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != nt {
                    assert(r2.list.nodes@[i].live == r1.list.nodes@[i].live);
                }
            }
            assert(r2.list.parent@ == r0.list.parent@);
            assert(r2.tables == r0.tables);
            assert(r2.processes == r1.processes);
            assert(r2.spaces == r0.spaces);
            assert(r2.threads.records == r0.threads.records);
            assert(r2.root_live(process));
            assert(r2.tables.roots@.contains_key(process));
            // The root's untyped is still its slot 5, and can retype the thread's block.
            lemma_slot_kept_but(r1, r2, process, ROOT_UNTYPED_SLOT, nt);
            Self::lemma_caps_frame(r1, r2, nt, nt, u);
            assert(r2.list.nodes@[child as int].live == r1.list.nodes@[child as int].live);
            assert(r2.list.nodes@[child as int].live);
            assert(r2.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r2, child);
            assert(r2.list.d(u) < MAX_DEPTH);
            assert(r2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(r2.threads.records@[bt].value().process == Some(base));
            assert(r2.thread_is_dead(bt));
            assert(r2.can_unbind_thread(process, ROOT_UNTYPED_SLOT, bt));
        }

        // Retype the thread's block: the thread is dead, so the retype unbinds it from the process.
        let ok3 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bt, Tracked(&mut steps));
        let ghost r3 = *self;
        let at_process = Position { through: None, index: WITNESS_PROCESS_SLOT };
        proof {
            assert(ok3 is Slice);
            assert(r2.thread_unbound(r3, process, ROOT_UNTYPED_SLOT, bt));
            assert(Self::unbound(r2, r3, bt));
            assert(block_refs(&r3.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(block_typed(&r3.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r3.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != bt {
                    assert(r3.list.nodes@[i].live == r2.list.nodes@[i].live);
                    assert(r2.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r3.list.parent@ == r0.list.parent@);
            assert(r3.tables == r0.tables);
            assert(r3.processes.records == r0.processes.records || r3.processes.records == r1.processes.records);
            assert(r3.root_live(process));
            assert(r3.spaces == r0.spaces);
            // The slots of the root's leaves stay: the thread's block is no leaf of the root's, since an
            // owned leaf whose node is live holds one reference.
            assert(!r2.list.nodes@[bt as int].live || !r2.tables.owner@.contains_key(bt)) by {
                reveal(CapKernel::wf);
            }
            lemma_slot_kept_but(r1, r2, process, WITNESS_PROCESS_SLOT, nt);
            lemma_slot_kept_but(r2, r3, process, WITNESS_PROCESS_SLOT, bt);
            lemma_slot_kept_but(r2, r3, process, ROOT_UNTYPED_SLOT, bt);
            // The process's capability can go: its only child was the thread's binding.
            assert(r3.list.nodes@[np as int].live == r2.list.nodes@[np as int].live);
            assert(r3.list.nodes@[np as int].kind == r2.list.nodes@[np as int].kind);
            Self::lemma_caps_frame(r1, r2, nt, nt, np);
            assert(r3.is_cap(np));
            assert(r3.payload_of(np) == process_of(base));
            assert(r3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r3, np);
            lemma_children_back(r0.list, r2.list, np);
            assert forall|c: usize| #[trigger] r2.list.is_child(np, c) implies c == bt by {
                assert(r0.list.is_child(np, c));
            }
            assert(r3.list.childless(np));
            assert(r3.table_at(process, None) == Some(process));
            assert(r3.cap_at(process, at_process) == Some(np));
            assert(r3.can_delete_at(process, at_process));
        }

        // Delete the process's capability.
        let ok4 = self.delete(process, at_process);
        let ghost r4 = *self;
        proof {
            assert(ok4 is Some);
            assert(Self::cap_deleted_at(r3, r4, process, at_process));
            assert(Self::object_dropped(r3, r4, np));
            assert(block_refs(&r4.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r4.blocks, BlockRef::Small(base / PAGE_SZ)));
            lemma_deleted_dead(r4, np);
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r4.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != np {
                    assert(r4.list.nodes@[i].live == r3.list.nodes@[i].live);
                    assert(r3.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r4.list.parent@ == r0.list.parent@);
            assert(r4.tables == r0.tables);
            assert(r4.processes.records == r3.processes.records);
            assert(r4.root_live(process));
            assert(r4.spaces == r0.spaces);
            lemma_slot_kept_but(r3, r4, process, WITNESS_PROCESS_SLOT, np);
            lemma_slot_kept_but(r3, r4, process, ROOT_UNTYPED_SLOT, np);
            Self::lemma_caps_frame(r3, r4, np, np, u);
            assert(r3.list.nodes@[u as int].live == r2.list.nodes@[u as int].live);
            assert(r3.list.nodes@[u as int].kind == r2.list.nodes@[u as int].kind);
            assert(r3.is_cap(u));
            assert(r4.is_cap(u));
            // The leaf in the process's table is still live: only slots died.
            assert(r4.list.nodes@[bl as int].live == r3.list.nodes@[bl as int].live);
            assert(r3.list.nodes@[bl as int].live == r2.list.nodes@[bl as int].live);
            assert(r2.list.nodes@[bl as int].live == r1.list.nodes@[bl as int].live);
            assert(r4.list.nodes@[bl as int].live);
            assert(r4.list.nodes@[child as int].live == r3.list.nodes@[child as int].live);
            assert(r3.list.nodes@[child as int].live == r2.list.nodes@[child as int].live);
            assert(r4.list.nodes@[child as int].live);
            assert(r4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r4, child);
            assert(r4.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(r4.can_unlink_leaf(process, ROOT_UNTYPED_SLOT, bl));
        }

        // Retype the process's leaf: its hidden node is live, so the retype unlinks it.
        let ok5 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r5 = *self;
        proof {
            assert(ok5 is Unlinked);
            assert(r4.leaf_unlinked(r5, process, ROOT_UNTYPED_SLOT, bl));
            assert(block_refs(&r5.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r5.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert forall|i: int| 0 <= i < NODE_SPACE && #[trigger] r5.list.nodes@[i].live implies r0.list.nodes@[i].live by {
                if i != bl {
                    assert(r5.list.nodes@[i].live == r4.list.nodes@[i].live);
                    assert(r4.list.nodes@[i].live ==> r0.list.nodes@[i].live);
                }
            }
            assert(r5.list.parent@ == r0.list.parent@);
            assert(r5.tables == r0.tables);
            assert(r5.root_live(process));
            assert(r5.spaces == r0.spaces);
            assert(r5.flush_epoch == 0);
            lemma_slot_kept_but(r4, r5, process, ROOT_UNTYPED_SLOT, bl);
            lemma_slot_kept_but(r4, r5, process, WITNESS_PROCESS_SLOT, bl);
            assert(r5.is_cap(u));
            assert(r5.list.nodes@[child as int].live == r4.list.nodes@[child as int].live);
            assert(r5.list.nodes@[child as int].live);
            assert(r5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_owned_listed(r5, child);
            assert(r5.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            // The leaf's one live slot is the derived untyped, which has no child.
            assert(r5.list.nodes@[bl + 1].live);
            assert(!r5.leaf_is_empty(bl));
            assert(r5.can_slice_leaf(process, ROOT_UNTYPED_SLOT, bl));
            assert forall|x: int| bl + 2 <= x < bl + NODES_PER_PAGE implies !#[trigger] r5.list.nodes@[x].live by {
                assert(!r0.list.nodes@[x].live);
            }
            lemma_children_back(r0.list, r5.list, child);
            if !r5.list.childless(child) {
                r5.list.lemma_next_is_child(child);
                assert(r0.list.is_child(child, r5.list.nodes@[child as int].next));
            }
            assert forall|j: int| 1 <= j < NODES_PER_PAGE && (#[trigger] r5.list.nodes@[bl + j]).live
                implies r5.list.childless((bl + j) as usize) by {
                if j != 1 {
                    assert(!r5.list.nodes@[bl + j].live);
                }
            }
            assert(r5.leaf_slots_childless(bl));
            lemma_live_slots_none(r5, bl, 2);
            assert(r5.leaf_live_slots(bl) == 1);
            // No slot of the leaf names the process's block: its one capability is an untyped.
            assert(r5.payload_of(child).kind is Untyped);
            assert(!r5.leaf_slot_names(bl, BlockRef::Small(base / PAGE_SZ))) by {
                if r5.leaf_slot_names(bl, BlockRef::Small(base / PAGE_SZ)) {
                    let n = choose|n: usize| bl < n < bl + NODES_PER_PAGE && #[trigger] r5.cap_names_block(n, BlockRef::Small(base / PAGE_SZ));
                    if n != child {
                        assert(!r5.list.nodes@[n as int].live);
                    }
                }
            }
        }

        // Retype the leaf again: its hidden node is gone, so the retype slices its slots.
        let ok6 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r6 = *self;
        proof {
            assert(ok6 is Slice);
            assert(r5.leaf_slice_kept(r6, bl));
            assert(r6.leaf_is_empty(bl));
            assert(block_refs(&r6.blocks, BlockRef::Small(base / PAGE_SZ)) == 0);
            assert(block_typed(&r6.blocks, BlockRef::Small(base / PAGE_SZ)));
            assert(r6.tables == r0.tables);
            assert(r6.root_live(process));
            assert(r6.spaces.roots == r0.spaces.roots);
            assert(r6.spaces.loaded == r0.spaces.loaded);
            assert(r6.processes.records == r1.processes.records);
            assert(r6.tables.has_slot(&r6.list, process, ROOT_UNTYPED_SLOT));
            assert(r6.tables.has_slot(&r6.list, process, WITNESS_PROCESS_SLOT));
            assert(r6.is_cap(u));
            assert(r6.list.nodes@[u as int].depth == r5.list.nodes@[u as int].depth);
            assert(r6.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(r6.list.nodes@[np as int].live == r5.list.nodes@[np as int].live);
            assert(!r6.list.nodes@[np as int].live);
        }

        // Every core and IOMMU acknowledges, so the leaf's pages hold no stale translation.
        self.witness_acknowledge_all();
        let ghost q6 = *self;
        proof {
            assert(q6.tlb_wf()) by {
                reveal(CapKernel::wf);
            }
            assert(q6.blocks.tracks((bl / PAGE_SZ) as int));
            assert(q6.blocks.tracks((bl / PAGE_SZ + 1) as int));
            assert(q6.acknowledged(bl / PAGE_SZ)) by {
                assert(q6.stale_epoch.pages@[(bl / PAGE_SZ) as int] <= q6.flush_epoch);
            }
            assert(q6.acknowledged((bl / PAGE_SZ + 1) as usize)) by {
                assert(q6.stale_epoch.pages@[(bl / PAGE_SZ + 1) as int] <= q6.flush_epoch);
            }
            assert(q6.tables == r6.tables && q6.list == r6.list && q6.blocks == r6.blocks);
            assert(q6.spaces == r6.spaces && q6.processes == r6.processes);
            assert(q6.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(q6.root_live(process));
            assert(q6.leaf_is_empty(bl));
        }

        // Retype the leaf a third time: it is empty, so the retype frees it.
        let ok7 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, bl, Tracked(&mut steps));
        let ghost r7 = *self;
        let ghost a = tree_of(&r7.table_pages, &r7.spaces);
        proof {
            assert(ok7 is Freed);
            assert(q6.leaf_freed(r7, 0, process, ROOT_UNTYPED_SLOT, bl));
            assert(q6.tables.owner@[bl] == (base, 0int));
            assert(r7.tables.leaf(base, 0) == NO_LEAF);
            assert forall|r: int| 0 <= r < ROOT_ENTRIES implies #[trigger] r7.tables.leaf(base, r) == NO_LEAF by {
                if r != 0 {
                    assert(r7.tables.leaf(base, r) == q6.tables.leaf(base, r));
                }
            }
            assert(r7.tables.roots@.dom().contains(process));
            assert(r7.tables.leaf(process, 0) == q6.tables.leaf(process, 0));
            assert(r7.tables.leaf(process, 2) == q6.tables.leaf(process, 2));
            assert(r7.tables.has_slot(&r7.list, process, ROOT_UNTYPED_SLOT));
            assert(r7.tables.has_slot(&r7.list, process, WITNESS_PROCESS_SLOT));
            assert(r7.tables.is_cap(&r7.list, u));
            assert(r7.payload_of(u) == first);
            assert(r7.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(q6.blocks.tracks((base / PAGE_SZ) as int));
            assert(r7.blocks.pages@[(base / PAGE_SZ) as int] == q6.blocks.pages@[(base / PAGE_SZ) as int]);
            assert(r7.process_is_dead(base));
            assert(r7.spaces == q6.spaces);
            assert(r7.spaces.roots == r0.spaces.roots);
            assert(r7.spaces.loaded == r0.spaces.loaded);
            assert(r7.process_unloaded(base));
            r7.lemma_unloaded_released(base);
            assert(r7.flush_epoch == 0);
            // The space's root still names the table: the root's entries and record are the link's.
            r7.lemma_process_block(base);
            r0.lemma_process_block(base);
            assert(!a.is_page(base) && !tk.is_page(base));
            assert(a.is_root(base));
            r7.lemma_table_base(base);
            assert(a.record(base).level == 4);
            assert(a.entry(base, KERNEL_MEM_END_L4INDEX) == tk.entry(base, KERNEL_MEM_END_L4INDEX));
            assert(a.names_child(base, KERNEL_MEM_END_L4INDEX));
            assert(child_at(a, base, KERNEL_MEM_END_L4INDEX) == b3);
            assert(r7.can_cut_process_space(process, ROOT_UNTYPED_SLOT, base));
            // The root's entries past the kernel's other than the table's are empty.
            assert forall|i: usize| KERNEL_MEM_END_L4INDEX < i < ENTRIES implies #[trigger] a.entry(base, i).is_empty() by {
                assert(!holds_kernel(SpaceKind::Process, i));
                assert(tk.entry(base, i) == ta.entry(base, i));
                assert(h0.spaces.roots@[base].value()[i].is_empty());
            }
            assert forall|i: usize| #[trigger] a.names_child(base, i) implies i == KERNEL_MEM_END_L4INDEX by {
                if i != KERNEL_MEM_END_L4INDEX {
                    assert(i >= KERNEL_MEM_END_L4INDEX);
                    assert(a.entry(base, i).is_empty());
                }
            }
        }

        // The process is dead and released and its root names the table: the retype of its block cuts it.
        let ok8a = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        let ghost r8 = *self;
        proof {
            assert(ok8a is Slice);
            assert(r7.process_space_cut(r8, process, ROOT_UNTYPED_SLOT, base));
            assert(Self::table_cuts_kept(r7, r8, base));
            let b = tree_of(&r8.table_pages, &r8.spaces);
            let ca = child_entries(a, base);
            let cb = child_entries(b, base);
            // The cut took the one child, so nothing is left to cut.
            assert(ca.subset_of(set![KERNEL_MEM_END_L4INDEX])) by {
                assert forall|i: usize| ca.contains(i) implies set![KERNEL_MEM_END_L4INDEX].contains(i) by {
                    lemma_child_entries(a, base, i);
                }
            }
            vstd::set_lib::range_set_properties::<usize>(0, ENTRIES);
            vstd::set_lib::lemma_len_subset(ca, set![KERNEL_MEM_END_L4INDEX]);
            assert(set![KERNEL_MEM_END_L4INDEX].len() == 1);
            assert(cb.len() == 0);
            vstd::set_lib::lemma_set_empty_equivalency_len(cb);
            assert forall|i: usize| !#[trigger] b.names_child(base, i) by {
                lemma_child_entries(b, base, i);
            }
            lemma_child_entries(a, base, KERNEL_MEM_END_L4INDEX);
            lemma_child_entries(b, base, KERNEL_MEM_END_L4INDEX);
            assert(b.entry(base, KERNEL_MEM_END_L4INDEX).is_empty());
            assert(Self::child_cut(r7, r8, b3));
            assert(b.record(b3).parent is None);
            // Every entry of the root past the kernel's is now empty.
            assert(a.is_table(base));
            assert forall|i: usize| KERNEL_MEM_END_L4INDEX <= i < ENTRIES implies #[trigger] r8.spaces.roots@[base].value()[i].is_empty() by {
                r8.lemma_process_block(base);
                assert(!b.is_page(base));
                if i != KERNEL_MEM_END_L4INDEX {
                    assert(b.entry(base, i) == a.entry(base, i));
                    assert(a.entry(base, i).is_empty());
                }
                assert(b.entry(base, i).is_empty());
            }
            assert(r8.tables == r7.tables && r8.list == r7.list && r8.blocks == r7.blocks);
            assert(r8.processes == r7.processes);
            assert(r8.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(r8.root_live(process));
        }

        // Every core and IOMMU acknowledges the cut's flush.
        self.witness_acknowledge_all();
        let ghost a8 = *self;
        proof {
            assert(a8.tlb_wf()) by {
                reveal(CapKernel::wf);
            }
            assert(a8.blocks.tracks((base / PAGE_SZ) as int));
            assert(a8.acknowledged(base / PAGE_SZ)) by {
                assert(a8.stale_epoch.pages@[(base / PAGE_SZ) as int] <= a8.flush_epoch);
            }
            assert(a8.spaces == r8.spaces && a8.blocks == r8.blocks && a8.processes == r8.processes);
            assert(a8.tables == r7.tables);
            assert(r8.spaces.loaded == r7.spaces.loaded);
            assert(a8.process_unloaded(base));
            a8.lemma_unloaded_released(base);
            assert(a8.process_is_dead(base));
            assert forall|r: int| 0 <= r < ROOT_ENTRIES implies #[trigger] a8.tables.leaf(base, r) == NO_LEAF by {
                assert(r7.tables.leaf(base, r) == NO_LEAF);
            }
            assert forall|i: usize| KERNEL_MEM_END_L4INDEX <= i < ENTRIES implies #[trigger] a8.spaces.roots@[base].value()[i].is_empty() by {
                assert(r8.spaces.roots@[base].value()[i].is_empty());
            }
            assert(a8.process_is_spent(base));
            assert(a8.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(a8.root_live(process));
            a8.lemma_process_block(base);
            assert(a8.blocks.wf()) by {
                reveal(CapKernel::wf);
            }
            a8.blocks.lemma_not_free_uncovered((base / PAGE_SZ) as int);
        }

        // Retype the process's block again: the process is spent, so the retype frees it.
        let ok8 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        let ghost r9 = *self;
        proof {
            assert(ok8 is Freed);
            assert(a8.process_freed(r9, 0, process, ROOT_UNTYPED_SLOT, base));
            assert(r9.tables.roots@[process] == a8.tables.roots@[process]);
            assert(r9.tables.roots@.contains_key(process));
            assert(r9.processes.records@[process] == a8.processes.records@[process]);
            assert(r9.root_live(process));
            assert(r9.tables.leaf(process, 0) == a8.tables.leaf(process, 0));
            assert(r9.tables.leaf(process, 2) == a8.tables.leaf(process, 2));
            assert(r9.tables.has_slot(&r9.list, process, ROOT_UNTYPED_SLOT));
            assert(r9.tables.has_slot(&r9.list, process, WITNESS_PROCESS_SLOT));
            assert(r9.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(!r9.list.nodes@[np as int].live);
            assert(r9.is_cap(u));
            assert(r9.payload_of(u) == first);
            assert(r9.can_retype_under(process, ROOT_UNTYPED_SLOT, base, PROCESS_ORDER));
            assert(!r9.blocks.covered((base / PAGE_SZ) as int));
            assert(r9.blocks.small_free((base / PAGE_SZ) as int, PROCESS_ORDER as usize)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] r9.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(r9.blocks.pages@[(base / PAGE_SZ) + k].kind is Free);
                }
            }
            assert(r9.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }

        // Retype a process at the same block into slot 257 again.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok9 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, Tracked(&mut steps));
        proof {
            assert(ok9);
            assert(np == base + 8 * PAGE_SZ + 1);
        }
        (ok8a, ok8, ok1 && ok2.is_some() && ok4.is_some() && ok9, Ghost(r7), Ghost(r8))
    }

    /// Gives entry e of table t of space s a child table at the given level: the order-3 block at the
    /// cursor, retyped as a table page under the root's untyped at ROOT_UNTYPED_SLOT and linked through
    /// the capability to s's process at index i of the root's table, at depth d. The entry is empty and
    /// the block free in the untyped, so it never refuses.
    #[verifier::spinoff_prover]
    fn witness_table(
        &mut self,
        process: usize,
        i: usize,
        t: usize,
        e: usize,
        level: usize,
        cursor: usize,
        s: Ghost<usize>,
        n: Ghost<usize>,
        d: Ghost<usize>,
        u: Ghost<usize>,
        first: Ghost<Payload>,
    ) -> (ret: bool)
        requires
            old(self).wf(),
            witness_root(*old(self), process, u@, first@),
            witness_slot(*old(self), process, i, n@, process_of(s@), d@),
            witness_alive(*old(self), s@),
            witness_block(*old(self), cursor, first@),
            1 <= level <= 3,
            tree_of(&old(self).table_pages, &old(self).spaces).is_table(t),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).space == Some(s@),
            tree_of(&old(self).table_pages, &old(self).spaces).record(t).level == level + 1,
            !old(self).blocks.pages@[(t / PAGE_SZ) as int].dead,
            tree_of(&old(self).table_pages, &old(self).spaces).child_slot(t, e),
            tree_of(&old(self).table_pages, &old(self).spaces).entry(t, e).is_empty(),
        ensures
            ret,
            final(self).wf(),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(cursor / PAGE_SZ <= j < cursor / PAGE_SZ + 8)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            nodes_kept(old(self).list, final(self).list),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            steps_kept(tree_of(&old(self).table_pages, &old(self).spaces), tree_of(&final(self).table_pages, &final(self).spaces)),
            witness_root(*final(self), process, u@, first@),
            witness_slot(*final(self), process, i, n@, process_of(s@), d@),
            step(tree_of(&final(self).table_pages, &final(self).spaces), t, e) == Some(cursor),
            tree_of(&final(self).table_pages, &final(self).spaces).is_page(cursor),
            tree_of(&final(self).table_pages, &final(self).spaces).record(cursor).level == level,
            tree_of(&final(self).table_pages, &final(self).spaces).record(cursor).space == Some(s@),
            !final(self).blocks.pages@[(cursor / PAGE_SZ) as int].dead,
            forall|j: usize| j < ENTRIES ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(cursor, j).is_empty(),
            forall|j: usize| j < ENTRIES && j != e ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry(t, j)
                == tree_of(&old(self).table_pages, &old(self).spaces).entry(t, j),
            !old(self).list.nodes@[cursor as int].live,
            final(self).list.parent@ == old(self).list.parent@.insert(cursor, u@),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j != cursor
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|x: usize| #![trigger final(self).list.nodes@[x as int]] old(self).list.valid(x) && x != cursor
                ==> final(self).list.nodes@[x as int].kind == old(self).list.nodes@[x as int].kind,
            final(self).cores == old(self).cores,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).spaces.loaded == old(self).spaces.loaded,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        // The body relates three states; their invariants stay folded, and the lemmas open them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        proof {
            lemma2_to64();
            assert(block_bytes(3) == PROCESS_BYTES);
            pre.lemma_table_base(t);
            assert(pre.blocks.pages@[cursor / PAGE_SZ + 0].kind is Free);
            pre.lemma_free_not_table(cursor, cursor / PAGE_SZ);
            pre.lemma_slot(process, ROOT_UNTYPED_SLOT);
            pre.lemma_slot_bound(u@);
            pre.lemma_slot(process, i);
            pre.lemma_slot_bound(n@);
            assert(pre.blocks.small_free((cursor / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] pre.blocks.pages@[cursor / PAGE_SZ + k].kind is Free by {
                    assert(pre.blocks.pages@[cursor / PAGE_SZ + k].kind is Free);
                }
            }
            assert(pre.can_retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level));
            // The parent is a typed table, so it lies outside the free block.
            if cursor / PAGE_SZ <= t / PAGE_SZ < cursor / PAGE_SZ + 8 {
                assert(pre.blocks.pages@[cursor / PAGE_SZ + (t / PAGE_SZ - cursor / PAGE_SZ)].kind is Free);
            }
            assert(t != cursor);
            lemma_aligned(cursor);
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let retyped = self.retype_table_page(process, ROOT_UNTYPED_SLOT, cursor, level, Tracked(&mut steps));
        let ghost mid = *self;
        let ghost m = tree_of(&mid.table_pages, &mid.spaces);
        proof {
            assert(retyped);
            assert(pre.tables.node_of(process, ROOT_UNTYPED_SLOT) == u@);
            Self::lemma_retype_nodes_kept(pre, mid, cursor, u@);
            assert(m.is_table(t));
            assert(m.record(t) == a.record(t));
            assert(m.entry(t, e) == a.entry(t, e));
            assert(m.child_slot(t, e));
            assert(m.is_page(cursor));
            mid.lemma_page_alive(cursor);
            assert(pre.blocks.tracks((t / PAGE_SZ) as int));
            assert(mid.blocks.pages@[(t / PAGE_SZ) as int] == pre.blocks.pages@[(t / PAGE_SZ) as int]);
            lemma_witness_slot_kept(pre, mid, process, ROOT_UNTYPED_SLOT, u@, first@, 1);
            lemma_witness_slot_kept(pre, mid, process, i, n@, process_of(s@), d@);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(mid.can_retype_under(process, ROOT_UNTYPED_SLOT, cursor, 3));
            assert(mid.can_link(process, i, t, e, ROOT_UNTYPED_SLOT, cursor));
        }
        let linked = self.link(process, i, t, e, ROOT_UNTYPED_SLOT, cursor);
        proof {
            let post = *self;
            let b = tree_of(&post.table_pages, &post.spaces);
            assert(linked);
            assert(mid.payload_of(mid.tables.node_of(process, i)).base == s@);
            assert(Self::link_done(mid, post, t, e, cursor, s@));
            assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
                assert(mid.is_cap(x) == pre.is_cap(x));
            }
            assert(b.entry(t, e) == child_entry(cursor));
            assert(b.names_child(t, e));
            assert(step(b, t, e) == Some(cursor));
            assert forall|j: usize| j < ENTRIES implies #[trigger] b.entry(cursor, j).is_empty() by {
                assert(m.entry(cursor, j).is_empty());
            }
            assert forall|j: usize| j < ENTRIES && j != e implies #[trigger] b.entry(t, j) == a.entry(t, j) by {
                assert(m.entry(t, j) == a.entry(t, j));
            }
            assert(steps_kept(a, m)) by {
                assert forall|x: usize| #![trigger a.is_table(x)] a.is_table(x) implies x != cursor by {}
            }
            assert(steps_kept(m, b)) by {
                assert forall|x: usize, j: usize| #![trigger step(m, x, j)] step(m, x, j) is Some implies b.entry(x, j) == m.entry(x, j) by {
                    assert(m.names_child(x, j));
                }
            }
            lemma_steps_kept_trans(a, m, b);
            assert forall|r: usize| #[trigger] space_mapping(b, r) == space_mapping(a, r) by {
                if !pre.spaces.roots@.contains_key(r) {
                    assert(space_mapping(m, r) =~= space_mapping(a, r));
                }
            }
            assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                implies post.list.nodes@[j].live == pre.list.nodes@[j].live by {
                assert(j != cursor);
            }
            assert(post.list == mid.list);
        }
        true
    }

    /// Gives space s the level 3, 2 and 1 tables of the path of the first page under entry l4 of its
    /// level 4 table, at the three order-3 blocks from the cursor, through the capability to s's process
    /// at index i of the root's table, at depth d. The entry is empty and the blocks free in the root's
    /// untyped, so it never refuses.
    #[verifier::spinoff_prover]
    fn witness_path(
        &mut self,
        process: usize,
        i: usize,
        s: usize,
        l4: usize,
        cursor: usize,
        n: Ghost<usize>,
        d: Ghost<usize>,
        u: Ghost<usize>,
        first: Ghost<Payload>,
    ) -> (ret: bool)
        requires
            old(self).wf(),
            witness_root(*old(self), process, u@, first@),
            witness_slot(*old(self), process, i, n@, process_of(s), d@),
            witness_alive(*old(self), s),
            tree_of(&old(self).table_pages, &old(self).spaces).is_root(s),
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES,
            tree_of(&old(self).table_pages, &old(self).spaces).entry(s, l4).is_empty(),
            !old(self).blocks.pages@[(s / PAGE_SZ) as int].dead,
            cursor + 3 * PROCESS_BYTES <= NODE_SPACE,
            witness_block(*old(self), cursor, first@),
            witness_block(*old(self), (cursor + PROCESS_BYTES) as usize, first@),
            witness_block(*old(self), (cursor + 2 * PROCESS_BYTES) as usize, first@),
        ensures
            ret,
            final(self).wf(),
            final(self).tables == old(self).tables,
            final(self).processes == old(self).processes,
            final(self).threads == old(self).threads,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@,
            final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@,
            forall|j: int| #![trigger final(self).blocks.pages@[j]] old(self).blocks.tracks(j) && !(cursor / PAGE_SZ <= j < cursor / PAGE_SZ + 24)
                ==> final(self).blocks.pages@[j] == old(self).blocks.pages@[j],
            forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x),
            nodes_kept(old(self).list, final(self).list),
            forall|j: int| #![trigger final(self).list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                ==> final(self).list.nodes@[j].live == old(self).list.nodes@[j].live,
            forall|r: usize| #[trigger] space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r),
            steps_kept(tree_of(&old(self).table_pages, &old(self).spaces), tree_of(&final(self).table_pages, &final(self).spaces)),
            witness_root(*final(self), process, u@, first@),
            witness_slot(*final(self), process, i, n@, process_of(s), d@),
            walk_table(tree_of(&final(self).table_pages, &final(self).spaces), s, SpacePath { l4: l4, l3: 0, l2: 0, l1: 0 }) is Some,
            step(tree_of(&final(self).table_pages, &final(self).spaces), s, l4) == Some(cursor),
            step(tree_of(&final(self).table_pages, &final(self).spaces), cursor, 0) == Some((cursor + PROCESS_BYTES) as usize),
            step(tree_of(&final(self).table_pages, &final(self).spaces), (cursor + PROCESS_BYTES) as usize, 0) == Some((cursor + 2 * PROCESS_BYTES) as usize),
            forall|j: usize| 0 < j < ENTRIES ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry((cursor + PROCESS_BYTES) as usize, j).is_empty(),
            forall|j: usize| j < ENTRIES ==> #[trigger] tree_of(&final(self).table_pages, &final(self).spaces).entry((cursor + 2 * PROCESS_BYTES) as usize, j).is_empty(),
    {
        // The body relates four states; their invariants stay folded, and the steps' contracts carry them.
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let ghost a = tree_of(&pre.table_pages, &pre.spaces);
        let ghost path = SpacePath { l4: l4, l3: 0, l2: 0, l1: 0 };
        let c1 = cursor + PROCESS_BYTES;
        let c2 = c1 + PROCESS_BYTES;
        proof {
            lemma2_to64();
            assert(block_bytes(3) == PROCESS_BYTES);
            pre.lemma_table_base(s);
            assert(cursor % PROCESS_BYTES == 0);
            assert(c1 % PROCESS_BYTES == 0);
            lemma_block_page(cursor, 0);
            lemma_block_page(c1, 0);
            assert(c1 / PAGE_SZ == cursor / PAGE_SZ + 8);
            assert(c2 / PAGE_SZ == cursor / PAGE_SZ + 16);
            assert(a.child_slot(s, l4));
        }
        let ok1 = self.witness_table(process, i, s, l4, 3, cursor, Ghost(s), n, d, u, first);
        let ghost s1 = *self;
        let ghost b1 = tree_of(&s1.table_pages, &s1.spaces);
        proof {
            lemma_witness_block_kept(pre, s1, c1, first@, (cursor / PAGE_SZ) as int, cursor / PAGE_SZ + 8);
            lemma_witness_block_kept(pre, s1, c2, first@, (cursor / PAGE_SZ) as int, cursor / PAGE_SZ + 8);
            s1.lemma_table_base(cursor);
            assert(b1.child_slot(cursor, 0));
        }
        let ok2 = self.witness_table(process, i, cursor, 0, 2, c1, Ghost(s), n, d, u, first);
        let ghost s2 = *self;
        let ghost b2 = tree_of(&s2.table_pages, &s2.spaces);
        proof {
            lemma_witness_block_kept(s1, s2, c2, first@, (c1 / PAGE_SZ) as int, c1 / PAGE_SZ + 8);
            s2.lemma_table_base(c1);
            assert(b2.child_slot(c1, 0));
        }
        let ok3 = self.witness_table(process, i, c1, 0, 1, c2, Ghost(s), n, d, u, first);
        proof {
            let post = *self;
            let b3 = tree_of(&post.table_pages, &post.spaces);
            lemma_nodes_kept_trans(pre.list, s1.list, s2.list);
            lemma_nodes_kept_trans(pre.list, s2.list, post.list);
            lemma_steps_kept_trans(a, b1, b2);
            lemma_steps_kept_trans(a, b2, b3);
            lemma_steps_kept_trans(b1, b2, b3);
            lemma_steps_kept(b1, b3);
            lemma_steps_kept(b2, b3);
            assert(a.is_table(s));
            assert(b3.is_root(s));
            assert(step(b3, s, l4) == Some(cursor));
            assert(step(b3, cursor, 0) == Some(c1));
            assert(step(b3, c1, 0) == Some(c2));
            assert(walk_table(b3, s, path) == Some(c2));
            assert forall|j: usize| 0 < j < ENTRIES implies #[trigger] b3.entry(c1, j).is_empty() by {
                assert(b2.entry(c1, j).is_empty());
            }
            assert forall|j: int| #![trigger post.blocks.pages@[j]] pre.blocks.tracks(j) && !(cursor / PAGE_SZ <= j < cursor / PAGE_SZ + 24)
                implies post.blocks.pages@[j] == pre.blocks.pages@[j] by {
                assert(s1.blocks.pages@[j] == pre.blocks.pages@[j]);
                assert(s2.blocks.pages@[j] == s1.blocks.pages@[j]);
            }
            assert forall|j: int| #![trigger post.list.nodes@[j]] 0 <= j < NODE_SPACE && j % PAGE_SZ as int != 0
                implies post.list.nodes@[j].live == pre.list.nodes@[j].live by {
                assert(s1.list.nodes@[j].live == pre.list.nodes@[j].live);
                assert(s2.list.nodes@[j].live == s1.list.nodes@[j].live);
            }
            assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
                assert(s1.is_cap(x) == pre.is_cap(x));
                assert(s2.is_cap(x) == s1.is_cap(x));
            }
            assert forall|r: usize| #[trigger] space_mapping(b3, r) == space_mapping(a, r) by {
                assert(space_mapping(b1, r) == space_mapping(a, r));
                assert(space_mapping(b2, r) == space_mapping(b1, r));
            }
        }
        ok1 && ok2 && ok3
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of nine free ones past those boot's tables took from the first untyped: retype a leaf into root
    /// entry 2 of the root's table at the second block's first two pages, a process P at `base` into
    /// slot 1 of that leaf, P's level 3, 2 and 1 tables for the path of the first page past the kernel's
    /// at the third to fifth blocks, a process Q at the sixth into slot 2, Q's tables for the same path
    /// at the seventh to ninth, and a frame at the second block's third page into slot 3; then map the
    /// frame at that path in P's space and in Q's. Every step succeeds, and at the end P and Q differ,
    /// neither is the root, and the path maps the one frame, with the frame capability's rights, in
    /// both spaces. What a revoke of the frame capability starts from holds too: the flush epoch is as
    /// boot left it, the root is live and slot 3 holds the capability, whose only children are the two
    /// mappings, which have none, and no other mapping names the frame's page.
    #[verifier::spinoff_prover]
    pub fn witness_root_maps_one_frame_into_two_processes(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 9 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let tree = tree_of(&final(self).table_pages, &final(self).spaces);
                let q = (base + 5 * PROCESS_BYTES) as usize;
                let path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
                let entry = frame_map_entry(((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
                let nf = (base + PROCESS_BYTES + 3) as usize;
                let fp = ((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& q != process
                &&& base != q
                &&& space_mapping(tree, base).contains_key(path)
                &&& space_mapping(tree, base)[path] == entry
                &&& space_mapping(tree, q).contains_key(path)
                &&& space_mapping(tree, q)[path] == entry
                &&& walk_finds(tree, base, path, fp)
                &&& walk_finds(tree, q, path, fp)
                &&& final(self).flush_epoch == old(self).flush_epoch
                &&& final(self).tables.roots@.contains_key(process)
                &&& witness_alive(*final(self), process)
                &&& final(self).tables.has_slot(&final(self).list, process, WITNESS_FRAME_SLOT)
                &&& final(self).tables.node_of(process, WITNESS_FRAME_SLOT) == nf
                &&& final(self).is_cap(nf)
                &&& exists|m1: usize, m2: usize| #[trigger] frame_shared(*final(self), nf, m1, m2, fp)
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            let pn = (leaf@ + 1) as usize;
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            assert(witness_root(s0, process, u, first));
            // The nine free blocks, one after another.
            assert(s0.root_untyped(process) == u);
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 9) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(base + 9 * PROCESS_BYTES <= NODE_SPACE);
            assert forall|j: int| 0 <= j < 9 implies #[trigger] witness_block(s0, cursor_block(base, j), first) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(s0.root_table_block(process, cursor_block(first.base, itb + j)));
            }
        }
        let b1 = base + PROCESS_BYTES;
        let bf = b1 + 2 * PAGE_SZ;
        let b2 = b1 + PROCESS_BYTES;
        let bq = b2 + 3 * PROCESS_BYTES;
        let b6 = bq + PROCESS_BYTES;
        let ghost fp = (bf / PAGE_SZ) as int;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(block_bytes(0) == PAGE_SZ);
            assert(cursor_block(base, 0) == base);
            assert(witness_block(s0, base, first));
            assert(base % PROCESS_BYTES == 0);
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            lemma_cursor_block(base, 5);
            lemma_cursor_block(base, 6);
            lemma_block_page(base, 0);
            lemma_block_page(b1, 0);
            lemma_block_page(b1, 2);
            assert(witness_block(s0, b1, first));
            assert(b1 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(fp == b1 / PAGE_SZ + 2);
            assert(s0.blocks.pages@[b1 / PAGE_SZ + 2].kind is Free);
            assert(!s0.blocks.covered(fp));
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b1, 1));
            assert(s0.blocks.small_free((b1 / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at1, b1));
            assert(s1.tables.leaf(process, 2) == b1);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(witness_root(s1, process, u, first));
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_SECOND_PROCESS_SLOT) && index_entry(WITNESS_SECOND_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_FRAME_SLOT) && index_entry(WITNESS_FRAME_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == b1 + 1);
            assert(!s1.list.nodes@[(b1 + 1) as int].live);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s1.tables.node_of(process, WITNESS_SECOND_PROCESS_SLOT) == b1 + 2);
            assert(witness_empty(s1, process, WITNESS_SECOND_PROCESS_SLOT, (b1 + 2) as usize));
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_FRAME_SLOT));
            assert(s1.tables.node_of(process, WITNESS_FRAME_SLOT) == b1 + 3);
            assert(witness_empty(s1, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize));
            lemma_run_kept(s0, s1, base, 0, 1, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            lemma_run_kept(s0, s1, base, 2, 9, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            assert(s0.blocks.tracks(fp));
            assert(s1.blocks.pages@[fp].kind is Free);
            assert(s1.blocks.regions_2m@ == s0.blocks.regions_2m@);
            assert(s1.blocks.regions_1g@ == s0.blocks.regions_1g@);
        }

        // P, in slot 1 of that leaf.
        proof {
            assert(witness_block(s1, cursor_block(base, 0), first));
            assert(witness_block(s1, base, first));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(s1.blocks.pages@[base / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
            assert(s1.blocks.pages@[base / PAGE_SZ + 0].kind is Free);
            s1.lemma_free_not_table(base, base / PAGE_SZ);
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, Tracked(&mut steps));
        let ghost s2 = *self;
        let ghost a2 = tree_of(&s2.table_pages, &s2.spaces);
        let ghost np = (b1 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None));
            assert(witness_alive(s2, base));
            assert(s2.payload_of(np) == process_of(base));
            assert(s2.list.nodes@[np as int].depth == 2);
            assert(s2.view().holds(process, np));
            assert(s2.is_cap(np));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(witness_slot(s2, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2));
            // The root's table keeps its new leaf, which P's table lacks, so the two differ.
            assert(s2.tables.leaf(process, 2) == b1);
            assert(s2.tables.leaf(base, 2) == NO_LEAF);
            assert(base != process);
            // The root's untyped, record and empty slots stay.
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s2.is_cap(u) && s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
            assert(s1.processes.records@.contains_key(process));
            assert(s2.tables.roots@.contains_key(process));
            assert(witness_root(s2, process, u, first));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(witness_empty(s2, process, WITNESS_SECOND_PROCESS_SLOT, (b1 + 2) as usize));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_FRAME_SLOT));
            assert(witness_empty(s2, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize));
            // P's space is a fresh root with nothing mapped.
            assert(!a2.is_page(base));
            assert(a2.is_root(base));
            assert(s2.spaces.roots@[base].value()[KERNEL_MEM_END_L4INDEX as usize].is_empty());
            assert(a2.entry(base, KERNEL_MEM_END_L4INDEX).is_empty());
            assert(s2.spaces.records@[base].value().kind is Process);
            assert(!s2.blocks.pages@[(base / PAGE_SZ) as int].dead);
            assert(space_mapping(a2, base) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty());
            // The blocks past P's and the frame's page stay free.
            lemma_run_kept(s1, s2, base, 2, 9, first, (base / PAGE_SZ) as int, base / PAGE_SZ + 8);
            assert(s1.blocks.tracks(fp));
            assert(s2.blocks.pages@[fp] == s1.blocks.pages@[fp]);
        }

        // P's tables for the path, through its capability.
        proof {
            lemma_cursor_block(base, 3);
            lemma_cursor_block(base, 4);
            assert(witness_block(s2, cursor_block(base, 2), first));
            assert(witness_block(s2, cursor_block(base, 3), first));
            assert(witness_block(s2, cursor_block(base, 4), first));
            assert(witness_block(s2, b2, first));
            assert(witness_block(s2, (b2 + PROCESS_BYTES) as usize, first));
            assert(witness_block(s2, (b2 + 2 * PROCESS_BYTES) as usize, first));
        }
        let ok3 = self.witness_path(process, WITNESS_PROCESS_SLOT, base, KERNEL_MEM_END_L4INDEX, b2, Ghost(np), Ghost(2), Ghost(u), Ghost(first));
        let ghost s3 = *self;
        let ghost a3 = tree_of(&s3.table_pages, &s3.spaces);
        proof {
            assert(ok3);
            assert(walk_table(a3, base, path) is Some);
            assert(space_mapping(a3, base) == space_mapping(a2, base));
            assert(witness_alive(s3, base));
            assert(a2.is_table(base));
            assert(s3.spaces.records@[base].value().kind is Process);
            lemma_witness_empty_kept(s2, s3, process, WITNESS_SECOND_PROCESS_SLOT, (b1 + 2) as usize);
            lemma_witness_empty_kept(s2, s3, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 16);
            lemma_run_kept(s2, s3, base, 5, 9, first, (b2 / PAGE_SZ) as int, b2 / PAGE_SZ + 24);
            assert(s2.blocks.tracks(fp));
            assert(s3.blocks.pages@[fp] == s2.blocks.pages@[fp]);
            assert(s3.tables.leaf(process, 2) == b1);
        }

        // Q, in slot 2 of the root's leaf.
        proof {
            assert(witness_block(s3, cursor_block(base, 5), first));
            assert(witness_block(s3, bq, first));
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bq, 3));
            assert(s3.blocks.small_free((bq / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s3.blocks.pages@[bq / PAGE_SZ + k].kind is Free by {
                    assert(s3.blocks.pages@[bq / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s3.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_SECOND_PROCESS_SLOT, bq, PROCESS_ORDER));
            assert(s3.blocks.pages@[bq / PAGE_SZ + 0].kind is Free);
            s3.lemma_free_not_table(bq, bq / PAGE_SZ);
            assert(!a3.is_table(bq));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok4 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_SECOND_PROCESS_SLOT, bq, Tracked(&mut steps));
        let ghost s4 = *self;
        let ghost a4 = tree_of(&s4.table_pages, &s4.spaces);
        let ghost nq = (b1 + 2) as usize;
        proof {
            assert(ok4);
            assert(Self::retype_keeps(s3, s4, nq, (bq / PAGE_SZ) as int, 3, None));
            // Q's capability, record and fresh space.
            assert(s4.payload_of(nq) == process_of(bq));
            assert(s4.list.nodes@[nq as int].depth == 2);
            assert(s4.view().holds(process, nq));
            assert(s4.is_cap(nq));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s4.tables.node_of(process, WITNESS_SECOND_PROCESS_SLOT) == nq);
            assert(witness_slot(s4, process, WITNESS_SECOND_PROCESS_SLOT, nq, process_of(bq), 2));
            assert(witness_alive(s4, bq));
            assert(s3.tables.roots@.contains_key(process));
            assert(s4.tables.leaf(process, 2) == b1);
            assert(s4.tables.leaf(bq, 2) == NO_LEAF);
            assert(bq != process);
            assert(!a4.is_page(bq));
            assert(a4.is_root(bq));
            assert(s4.spaces.roots@[bq].value()[KERNEL_MEM_END_L4INDEX as usize].is_empty());
            assert(a4.entry(bq, KERNEL_MEM_END_L4INDEX).is_empty());
            assert(!s4.blocks.pages@[(bq / PAGE_SZ) as int].dead);
            assert(space_mapping(a4, bq) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty());
            // P's walk, mapping, record, kind and capability stay.
            lemma_new_root_steps_kept(a3, a4, bq);
            lemma_steps_kept(a3, a4);
            assert(walk_table(a4, base, path) == walk_table(a3, base, path));
            assert(s3.spaces.roots@.contains_key(base));
            assert(space_mapping(a4, base) == space_mapping(a3, base));
            assert(s3.processes.records@.contains_key(base));
            assert(witness_alive(s4, base));
            assert(a3.is_table(base));
            assert(s4.spaces.records@[base].value().kind is Process);
            assert(s3.is_cap(np));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_PROCESS_SLOT));
            assert(s4.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(witness_slot(s4, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2));
            // The root's untyped, record and frame slot stay.
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.is_cap(u));
            assert(s4.tables.has_slot(&s4.list, process, ROOT_UNTYPED_SLOT));
            assert(s4.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s4.is_cap(u) && s4.payload_of(u) == first && s4.list.nodes@[u as int].depth == 1);
            assert(s3.processes.records@.contains_key(process));
            assert(witness_root(s4, process, u, first));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_FRAME_SLOT));
            assert(witness_empty(s4, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize));
            // The blocks past Q's and the frame's page stay free.
            lemma_run_kept(s3, s4, base, 6, 9, first, (bq / PAGE_SZ) as int, bq / PAGE_SZ + 8);
            assert(s3.blocks.tracks(fp));
            assert(s4.blocks.pages@[fp] == s3.blocks.pages@[fp]);
        }

        // Q's tables for the path, through its capability.
        proof {
            lemma_cursor_block(base, 7);
            lemma_cursor_block(base, 8);
            assert(witness_block(s4, cursor_block(base, 6), first));
            assert(witness_block(s4, cursor_block(base, 7), first));
            assert(witness_block(s4, cursor_block(base, 8), first));
            assert(witness_block(s4, b6, first));
            assert(witness_block(s4, (b6 + PROCESS_BYTES) as usize, first));
            assert(witness_block(s4, (b6 + 2 * PROCESS_BYTES) as usize, first));
        }
        let ok5 = self.witness_path(process, WITNESS_SECOND_PROCESS_SLOT, bq, KERNEL_MEM_END_L4INDEX, b6, Ghost(nq), Ghost(2), Ghost(u), Ghost(first));
        let ghost s5 = *self;
        let ghost a5 = tree_of(&s5.table_pages, &s5.spaces);
        proof {
            assert(ok5);
            lemma_steps_kept(a4, a5);
            assert(walk_table(a5, base, path) == walk_table(a4, base, path));
            assert(walk_table(a5, bq, path) is Some);
            assert(space_mapping(a5, base) == space_mapping(a4, base));
            assert(space_mapping(a5, bq) == space_mapping(a4, bq));
            assert(a4.is_table(base));
            assert(a4.is_table(bq));
            assert(s5.spaces.records@[base].value().kind is Process);
            assert(s5.spaces.records@[bq].value().kind is Process);
            assert(witness_alive(s5, base));
            assert(witness_alive(s5, bq));
            lemma_witness_slot_kept(s4, s5, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2);
            lemma_witness_empty_kept(s4, s5, process, WITNESS_FRAME_SLOT, (b1 + 3) as usize);
            assert(s4.blocks.tracks(fp));
            assert(s5.blocks.pages@[fp] == s4.blocks.pages@[fp]);
            assert(s5.blocks.regions_2m@ == s0.blocks.regions_2m@);
            assert(s5.blocks.regions_1g@ == s0.blocks.regions_1g@);
        }

        // The frame, at the second block's third page, in slot 3 of the root's leaf.
        proof {
            assert(block_within(bf, 0, first));
            assert(s5.can_retype_under(process, ROOT_UNTYPED_SLOT, bf, 0));
            assert(s5.blocks.small_free(fp, 0)) by {
                assert(!s5.blocks.covered(fp));
                assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] s5.blocks.pages@[fp + k].kind is Free by {
                    assert(k == 0);
                }
            }
            assert(s5.can_retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok6 = self.retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf, Tracked(&mut steps));
        let ghost s6 = *self;
        let ghost a6 = tree_of(&s6.table_pages, &s6.spaces);
        let ghost nf = (b1 + 3) as usize;
        let ghost cap = crate::capability::retype::frame_of(bf);
        proof {
            assert(ok6);
            assert(Self::frame_retyped(s5, s6, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
            assert(Self::retype_keeps(s5, s6, nf, fp, 0, None));
            assert(a6 == a5);
            assert(s6.payload_of(nf) == cap);
            assert(s6.list.nodes@[nf as int].depth == 2);
            assert(s6.view().holds(process, nf));
            assert(s6.is_cap(nf));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_FRAME_SLOT));
            assert(s6.tables.has_slot(&s6.list, process, WITNESS_FRAME_SLOT));
            assert(s6.tables.node_of(process, WITNESS_FRAME_SLOT) == nf);
            assert(witness_slot(s6, process, WITNESS_FRAME_SLOT, nf, cap, 2));
            assert(block_refs(&s6.blocks, block_ref(&s6.blocks, bf / PAGE_SZ)) == 1);
            // P's and Q's capabilities and records, and the root's, stay.
            assert(s5.is_cap(np));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_PROCESS_SLOT));
            assert(s5.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(witness_slot(s6, process, WITNESS_PROCESS_SLOT, np, process_of(base), 2));
            assert(s5.is_cap(nq));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_SECOND_PROCESS_SLOT));
            assert(s5.tables.node_of(process, WITNESS_SECOND_PROCESS_SLOT) == nq);
            assert(witness_slot(s6, process, WITNESS_SECOND_PROCESS_SLOT, nq, process_of(bq), 2));
            assert(s5.processes.records@.contains_key(base));
            assert(s5.processes.records@.contains_key(bq));
            assert(witness_alive(s6, base));
            assert(witness_alive(s6, bq));
            assert(s5.tables.has_slot(&s5.list, process, ROOT_UNTYPED_SLOT));
            assert(s5.is_cap(u));
            assert(s6.tables.has_slot(&s6.list, process, ROOT_UNTYPED_SLOT));
            assert(s6.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s6.is_cap(u) && s6.payload_of(u) == first && s6.list.nodes@[u as int].depth == 1);
            assert(s5.processes.records@.contains_key(process));
            assert(s5.tables.roots@.contains_key(process));
            assert(witness_root(s6, process, u, first));
            assert(s6.spaces.records@[base].value().kind == SpaceKind::Process);
            assert(s6.spaces.records@[bq].value().kind == SpaceKind::Process);
        }

        // The frame at the path in P's space.
        let ghost entry = frame_map_entry(((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
        proof {
            s6.lemma_walk_table_facts(base, path);
            assert(!space_mapping(a6, base).contains_key(path));
            assert(walk(a6, base, path) is None);
            s6.lemma_level1_empty(base, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / PAGE_SZ);
            assert(s6.can_map(process, WITNESS_PROCESS_SLOT, SpaceKind::Process, path, WITNESS_FRAME_SLOT, 0));
        }
        let ok7 = self.map(process, WITNESS_PROCESS_SLOT, KERNEL_MEM_END_L4INDEX, 0, 0, 0, WITNESS_FRAME_SLOT, 0);
        let ghost s7 = *self;
        let ghost a7 = tree_of(&s7.table_pages, &s7.spaces);
        proof {
            assert(ok7);
            assert(Self::map_done(s6, s7, process, WITNESS_PROCESS_SLOT, path, WITNESS_FRAME_SLOT, 0));
            let t1 = walk_table(a6, base, path)->0;
            lemma_map_kept(s6, s7, mapping_node(t1, 0), nf);
            assert(space_mapping(a7, base) == space_mapping(a6, base).insert(path, entry));
            assert(space_mapping(a7, bq) == space_mapping(a6, bq));
            assert(walk_table(a7, bq, path) == walk_table(a6, bq, path));
            lemma_witness_slot_kept(s6, s7, process, ROOT_UNTYPED_SLOT, u, first, 1);
            lemma_witness_slot_kept(s6, s7, process, WITNESS_SECOND_PROCESS_SLOT, nq, process_of(bq), 2);
            lemma_witness_slot_kept(s6, s7, process, WITNESS_FRAME_SLOT, nf, cap, 2);
            assert(witness_root(s7, process, u, first));
            assert(witness_alive(s7, bq));
            assert(s7.spaces.records@[bq].value().kind == SpaceKind::Process);
            // The frame's block holds one more reference, the mapping's.
            assert(s6.blocks.tracks(fp));
            assert(block_ref(&s7.blocks, bf / PAGE_SZ) == block_ref(&s6.blocks, bf / PAGE_SZ));
            assert(block_refs(&s7.blocks, block_ref(&s7.blocks, bf / PAGE_SZ)) == 2);
        }

        // The frame at the path in Q's space.
        proof {
            s7.lemma_walk_table_facts(bq, path);
            assert(!space_mapping(a7, bq).contains_key(path));
            assert(walk(a7, bq, path) is None);
            s7.lemma_level1_empty(bq, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / PAGE_SZ);
            assert(s7.can_map(process, WITNESS_SECOND_PROCESS_SLOT, SpaceKind::Process, path, WITNESS_FRAME_SLOT, 0));
        }
        let ok8 = self.map(process, WITNESS_SECOND_PROCESS_SLOT, KERNEL_MEM_END_L4INDEX, 0, 0, 0, WITNESS_FRAME_SLOT, 0);
        proof {
            let s8 = *self;
            let a8 = tree_of(&s8.table_pages, &s8.spaces);
            assert(ok8);
            assert(Self::map_done(s7, s8, process, WITNESS_SECOND_PROCESS_SLOT, path, WITNESS_FRAME_SLOT, 0));
            assert(space_mapping(a8, bq) == space_mapping(a7, bq).insert(path, entry));
            assert(space_mapping(a8, base) == space_mapping(a7, base));
            assert(space_mapping(a8, base).contains_key(path));
            assert(space_mapping(a8, base)[path] == entry);
            assert(space_mapping(a8, bq).contains_key(path));
            assert(space_mapping(a8, bq)[path] == entry);
            assert(bq == base + 5 * PROCESS_BYTES);
            // Both walks end at the frame's page.
            let g = fp as usize;
            lemma_fundamental_div_mod(bf as int, PAGE_SZ as int);
            assert(fp * PAGE_SZ == bf);
            assert(entry.addr == bf);
            assert(entry.addr / PAGE_SZ == g);
            assert(walk_finds(a8, base, path, g));
            assert(walk_finds(a8, bq, path, g));
            // The root, its frame capability and the epoch stay.
            let t1 = walk_table(a6, base, path)->0;
            let t2 = walk_table(a7, bq, path)->0;
            let m1 = mapping_node(t1, 0);
            let m2 = mapping_node(t2, 0);
            lemma_map_kept(s7, s8, m2, nf);
            lemma_witness_slot_kept(s7, s8, process, WITNESS_FRAME_SLOT, nf, cap, 2);
            assert(witness_alive(s8, process));
            assert(s8.flush_epoch == s0.flush_epoch);
            assert(s5.list.wf() && s6.list.wf() && s7.list.wf() && s8.list.wf()) by {
                reveal(CapKernel::wf);
            }
            // No record named the frame's page before the frame was retyped: its page was free and no
            // typed region covered it.
            assert forall|m: usize| #[trigger] s5.mappings@.contains_key(m) implies !record_pages(s5.mappings@[m]).contains(g) by {
                if record_pages(s5.mappings@[m]).contains(g) {
                    assert(s5.mapped@.contains(g)) by {
                        reveal(CapKernel::wf);
                    }
                    let br = s5.lemma_mapped_block(g);
                    assert(s5.blocks.pages@[fp].kind is Free);
                    assert(!s5.blocks.covered(fp));
                    match br {
                        BlockRef::Small(b) => {
                            assert(b == g);
                        },
                        BlockRef::Two(r) => {
                            lemma_fundamental_div_mod_converse(fp, PAGES_PER_2M as int, r as int, fp - r * PAGES_PER_2M);
                            assert(region_2m(fp) == r);
                        },
                        BlockRef::One(r) => {
                            lemma_fundamental_div_mod_converse(fp, PAGES_PER_1G as int, r as int, fp - r * PAGES_PER_1G);
                            assert(region_1g(fp) == r);
                        },
                    }
                }
            }
            // The frame capability is new and childless; each map adds one childless child under it.
            assert(s6.mappings@ == s5.mappings@);
            assert(!s5.list.nodes@[nf as int].live);
            assert(s5.list.nodes@[u as int].live);
            assert(s6.list.is_child(u, nf));
            lemma_listed_live(s6.list, nf);
            lemma_added_children(s5.list, s6.list, nf, u);
            assert(s7.list.is_child(nf, m1));
            lemma_listed_live(s7.list, m1);
            lemma_added_children(s6.list, s7.list, m1, nf);
            assert(s8.list.is_child(nf, m2));
            lemma_listed_live(s8.list, m2);
            lemma_added_children(s7.list, s8.list, m2, nf);
            assert(s7.list.nodes@[m1 as int].live);
            assert(m1 != m2);
            assert(s8.list.is_child(nf, m1)) by {
                assert(s8.list.nodes@[m1 as int].live);
                lemma_child_kept(s7.list, s8.list, nf, m1);
            }
            assert(frame_shared(s8, nf, m1, m2, g)) by {
                assert forall|y: usize| #[trigger] s8.list.is_child(nf, y) implies y == m1 || y == m2 by {
                    if y != m1 && y != m2 {
                        assert(s7.list.is_child(nf, y));
                        assert(s6.list.is_child(nf, y));
                    }
                }
                assert forall|z: usize| !#[trigger] s8.list.is_child(m1, z) by {
                    if s8.list.is_child(m1, z) {
                        if z == m2 {
                            assert(s8.list.parent@[m2] == nf);
                        } else {
                            assert(s7.list.is_child(m1, z));
                        }
                    }
                }
                assert forall|m: usize| #[trigger] s8.mappings@.contains_key(m) && record_pages(s8.mappings@[m]).contains(g)
                    implies s8.list.is_child(nf, m) by {
                    if m != m1 && m != m2 {
                        assert(s5.mappings@.contains_key(m));
                        assert(s8.mappings@[m] == s5.mappings@[m]);
                    }
                }
            }
        }
        ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8
    }

    /// From the state boot leaves, as the root at `process`, with the nine free blocks of
    /// witness_root_maps_one_frame_into_two_processes: share a frame between P and Q as it does, then
    /// revoke the frame capability in slot 3 of the root's leaf. One revoke finishes, since the
    /// capability's run is the two mappings, within its budget and two epochs past boot's. At the end
    /// the capability stays, neither P's space nor Q's maps the path, the frame's page is not mapped,
    /// and no walk of any space finds it.
    #[verifier::spinoff_prover]
    pub fn witness_root_revokes_a_shared_frame(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 9 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let tree = tree_of(&final(self).table_pages, &final(self).spaces);
                let q = (base + 5 * PROCESS_BYTES) as usize;
                let path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
                let nf = (base + PROCESS_BYTES + 3) as usize;
                let fp = ((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize;
                &&& final(self).wf()
                &&& final(self).is_cap(nf)
                &&& forall|x: usize| !#[trigger] final(self).list.is_child(nf, x)
                &&& !space_mapping(tree, base).contains_key(path)
                &&& !space_mapping(tree, q).contains_key(path)
                &&& !final(self).mapped@.contains(fp)
                &&& forall|r: usize, p: SpacePath| !#[trigger] walk_finds(tree, r, p, fp)
            }),
    {
        hide(CapKernel::wf);
        let shared = self.witness_root_maps_one_frame_into_two_processes(root, process, leaf, frames, t, free, image, untyped, frame, present, base);
        let ghost s8 = *self;
        let ghost nf = (base + PROCESS_BYTES + 3) as usize;
        let ghost g = ((base + 10 * PAGE_SZ) / PAGE_SZ as int) as usize;
        let at = Position { through: None, index: WITNESS_FRAME_SLOT };
        proof {
            assert(s8.cap_at(process, at) == Some(nf));
            assert(s8.root_live(process));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let done = self.revoke(process, at, Tracked(&mut steps));
        proof {
            let s9 = *self;
            let a8 = tree_of(&s8.table_pages, &s8.spaces);
            let tree = tree_of(&s9.table_pages, &s9.spaces);
            let q = (base + 5 * PROCESS_BYTES) as usize;
            let path = SpacePath { l4: KERNEL_MEM_END_L4INDEX, l3: 0, l2: 0, l1: 0 };
            assert(!(done is Refused));
            assert(s8.list.wf() && s9.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let (m1, m2) = choose|m1: usize, m2: usize| frame_shared(s8, nf, m1, m2, g);
            let gone = choose|gone: Seq<usize>| revoked_seq(s8.list, s9.list, nf, gone);
            // Every node the revoke took was below the capability, whose children have none, so it
            // was one of the two mappings, and it took at most two.
            assert forall|i: int| 0 <= i < gone.len() implies #[trigger] gone[i] == m1 || gone[i] == m2 by {
                let x = gone[i];
                assert forall|y: usize, z: usize| #[trigger] s8.list.is_child(nf, y) implies !#[trigger] s8.list.is_child(y, z) by {
                    assert(y == m1 || y == m2);
                }
                lemma_below_child(s8.list, nf, x);
            }
            if gone.len() > 2 {
                assert(gone[0] == m1 || gone[0] == m2);
                assert(gone[1] == m1 || gone[1] == m2);
                assert(gone[2] == m1 || gone[2] == m2);
                assert(gone[0] != gone[1] && gone[0] != gone[2] && gone[1] != gone[2]);
            }
            assert(s8.list.seq@.len() - s9.list.seq@.len() <= 2);
            // So the revoke stopped neither on its budget nor on the epoch: it finished.
            assert(s8.flush_epoch == 0);
            assert(s9.flush_epoch <= 2);
            assert(done is Done);
            assert(Self::cap_revoked_at(s8, s9, process, at));
            // A record after the revoke is one before, so it names the frame's page only as a child
            // of the capability, which has none left.
            assert(mapped_wf(s9.mapped@, s9.mappings@) && mappings_wf(&s9.list, &s9.tables, tree, &s9.blocks, s9.holders@, s9.mappings@)) by {
                reveal(CapKernel::wf);
            }
            if s9.mapped@.contains(g) {
                let m = choose|m: usize| #![trigger s9.mappings@[m]] s9.mappings@.contains_key(m) && record_pages(s9.mappings@[m]).contains(g);
                assert(s8.mappings@.contains_key(m) && s8.mappings@[m] == s9.mappings@[m]);
                assert(s8.list.is_child(nf, m));
                assert(mapping_wf(&s9.list, &s9.tables, tree, &s9.blocks, s9.holders@, s9.mappings@, m));
                lemma_child_kept(s8.list, s9.list, nf, m);
            }
            assert forall|r: usize, p: SpacePath| !#[trigger] walk_finds(tree, r, p, g) by {
                if walk_finds(tree, r, p, g) {
                    s9.lemma_walk_mapped(r, p, g);
                }
            }
            // A walk after it is the walk before, which found the frame's page.
            if space_mapping(tree, base).contains_key(path) {
                assert(walk(tree, base, path) == walk(a8, base, path));
                assert(walk_finds(tree, base, path, g));
            }
            if space_mapping(tree, q).contains_key(path) {
                assert(walk(tree, q, path) == walk(a8, q, path));
                assert(walk_finds(tree, q, path, g));
            }
        }
        match done {
            RevokeStep::Done => shared,
            _ => false,
        }
    }

    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of four free ones past those boot's tables took from the first untyped, and entry l4 of the
    /// root's level 4 table past the kernel's and under no page of the image: retype a leaf into root
    /// entry 2 of the root's table at the fourth block's first two pages, give the root's own space the
    /// level 3, 2 and 1 tables of the first page under entry l4 at the first three blocks, through its
    /// process capability, retype a frame at the fourth block's third page into slot 3 of the leaf, and
    /// map it there. Every step succeeds, and at the end the root's space maps what it did, the image,
    /// and the frame at that path, with the frame capability's rights.
    #[verifier::spinoff_prover]
    pub fn witness_root_maps_a_frame_into_its_own_space(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
        l4: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 4 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES,
            !image_l4(image@, l4),
        ensures
            ret,
            ({
                let tree = tree_of(&final(self).table_pages, &final(self).spaces);
                let path = SpacePath { l4, l3: 0, l2: 0, l1: 0 };
                let entry = frame_map_entry(((base + 26 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
                &&& final(self).wf()
                &&& space_mapping(tree, process) == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), process).insert(path, entry)
                &&& space_mapping(tree, process).contains_key(path)
                &&& space_mapping(tree, process)[path] == entry
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost a0 = tree_of(&s0.table_pages, &s0.spaces);
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost pn = (leaf@ + 1) as usize;
        let ghost d = s0.list.nodes@[pn as int].depth;
        let ghost path = SpacePath { l4, l3: 0, l2: 0, l1: 0 };
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            s0.lemma_process_space(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            assert(witness_root(s0, process, u, first));
            assert(witness_slot(s0, process, ROOT_PROCESS_SLOT, pn, process_of(process), d));
            // The four free blocks, one after another.
            assert(s0.root_untyped(process) == u);
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 4) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(base + 4 * PROCESS_BYTES <= NODE_SPACE);
            assert forall|j: int| 0 <= j < 4 implies #[trigger] witness_block(s0, cursor_block(base, j), first) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(s0.root_table_block(process, cursor_block(first.base, itb + j)));
            }
        }
        let lb = base + 3 * PROCESS_BYTES;
        let bf = lb + 2 * PAGE_SZ;
        let ghost fp = (bf / PAGE_SZ) as int;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(block_bytes(0) == PAGE_SZ);
            assert(cursor_block(base, 0) == base);
            assert(witness_block(s0, base, first));
            assert(base % PROCESS_BYTES == 0);
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            lemma_cursor_block(base, 3);
            assert(witness_block(s0, lb, first));
            lemma_block_page(lb, 0);
            lemma_block_page(lb, 2);
            assert(lb / PAGE_SZ == base / PAGE_SZ + 24);
            assert(fp == lb / PAGE_SZ + 2);
            assert(s0.blocks.pages@[lb / PAGE_SZ + 2].kind is Free);
            assert(!s0.blocks.covered(fp));
            // The root's process block is typed, so it lies outside the free fourth block.
            if lb / PAGE_SZ <= process / PAGE_SZ < lb / PAGE_SZ + 8 {
                assert(s0.blocks.pages@[lb / PAGE_SZ + (process / PAGE_SZ - lb / PAGE_SZ)].kind is Free);
            }
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, lb, 1));
            assert(s0.blocks.small_free((lb / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb, Tracked(&mut steps));
        let ghost s1 = *self;
        let ghost a1 = tree_of(&s1.table_pages, &s1.spaces);
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at, lb));
            assert(a1 == a0);
            assert(s1.tables.leaf(process, 2) == lb);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(witness_root(s1, process, u, first));
            assert(s0.tables.has_slot(&s0.list, process, ROOT_PROCESS_SLOT));
            assert(s0.is_cap(pn));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_PROCESS_SLOT));
            assert(s1.tables.node_of(process, ROOT_PROCESS_SLOT) == pn);
            assert(witness_slot(s1, process, ROOT_PROCESS_SLOT, pn, process_of(process), d));
            assert(witness_alive(s1, process));
            assert(index_ok(WITNESS_FRAME_SLOT) && index_entry(WITNESS_FRAME_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_FRAME_SLOT));
            assert(s1.tables.node_of(process, WITNESS_FRAME_SLOT) == lb + 3);
            assert(witness_empty(s1, process, WITNESS_FRAME_SLOT, (lb + 3) as usize));
            lemma_run_kept(s0, s1, base, 0, 3, first, (lb / PAGE_SZ) as int, lb / PAGE_SZ + 2);
            assert(s0.blocks.tracks(fp));
            assert(s1.blocks.pages@[fp].kind is Free);
            assert(s0.blocks.tracks((process / PAGE_SZ) as int));
            assert(s1.blocks.pages@[(process / PAGE_SZ) as int] == s0.blocks.pages@[(process / PAGE_SZ) as int]);
            assert(!s1.blocks.pages@[(process / PAGE_SZ) as int].dead);
            assert(a1.is_root(process));
            assert(a1.entry(process, l4).is_empty());
        }

        // The root's tables for the path, through its process capability.
        proof {
            assert(witness_block(s1, cursor_block(base, 0), first));
            assert(witness_block(s1, cursor_block(base, 1), first));
            assert(witness_block(s1, cursor_block(base, 2), first));
            assert(witness_block(s1, base, first));
            assert(witness_block(s1, (base + PROCESS_BYTES) as usize, first));
            assert(witness_block(s1, (base + 2 * PROCESS_BYTES) as usize, first));
        }
        let ok2 = self.witness_path(process, ROOT_PROCESS_SLOT, process, l4, base, Ghost(pn), Ghost(d), Ghost(u), Ghost(first));
        let ghost s2 = *self;
        let ghost a2 = tree_of(&s2.table_pages, &s2.spaces);
        proof {
            assert(ok2);
            assert(walk_table(a2, process, path) is Some);
            assert(space_mapping(a2, process) == space_mapping(a1, process));
            lemma_witness_empty_kept(s1, s2, process, WITNESS_FRAME_SLOT, (lb + 3) as usize);
            assert(s1.blocks.tracks(fp));
            assert(s2.blocks.pages@[fp] == s1.blocks.pages@[fp]);
            assert(s2.blocks.regions_2m@ == s0.blocks.regions_2m@);
            assert(s2.blocks.regions_1g@ == s0.blocks.regions_1g@);
        }

        // The frame, at the fourth block's third page, in slot 3 of the root's leaf.
        proof {
            assert(block_within(bf, 0, first));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bf, 0));
            assert(s2.blocks.small_free(fp, 0)) by {
                assert(!s2.blocks.covered(fp));
                assert forall|k: int| 0 <= k < order_pages(0) implies #[trigger] s2.blocks.pages@[fp + k].kind is Free by {
                    assert(k == 0);
                }
            }
            assert(s2.can_retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok3 = self.retype_frame(process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf, Tracked(&mut steps));
        let ghost s3 = *self;
        let ghost a3 = tree_of(&s3.table_pages, &s3.spaces);
        let ghost nf = (lb + 3) as usize;
        let ghost cap = crate::capability::retype::frame_of(bf);
        proof {
            assert(ok3);
            assert(Self::frame_retyped(s2, s3, process, ROOT_UNTYPED_SLOT, WITNESS_FRAME_SLOT, bf));
            assert(Self::retype_keeps(s2, s3, nf, fp, 0, None));
            assert(a3 == a2);
            assert(s3.payload_of(nf) == cap);
            assert(s3.list.nodes@[nf as int].depth == 2);
            assert(s3.is_cap(nf));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_FRAME_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_FRAME_SLOT));
            assert(s3.tables.node_of(process, WITNESS_FRAME_SLOT) == nf);
            assert(block_refs(&s3.blocks, block_ref(&s3.blocks, bf / PAGE_SZ)) == 1);
            // The root's process capability and record stay.
            assert(s2.is_cap(pn));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_PROCESS_SLOT));
            assert(s2.tables.node_of(process, ROOT_PROCESS_SLOT) == pn);
            assert(s3.tables.has_slot(&s3.list, process, ROOT_PROCESS_SLOT));
            assert(s3.tables.node_of(process, ROOT_PROCESS_SLOT) == pn);
            assert(s3.is_cap(pn) && s3.payload_of(pn) == process_of(process));
            assert(s2.processes.records@.contains_key(process));
            assert(witness_alive(s3, process));
            assert(s3.wf());
            s3.lemma_process_space(pn);
            assert(s3.spaces.records@[process].value().kind == SpaceKind::Process);
        }

        // The frame at the path in the root's own space.
        let ghost entry = frame_map_entry(((base + 26 * PAGE_SZ) / PAGE_SZ as int) as usize, FRAME_RIGHTS, false);
        proof {
            s3.lemma_walk_table_facts(process, path);
            assert(space_mapping(a3, process) == space_mapping(a0, process));
            // The path's l4 index is under no page of the image, and boot mapped only the image's.
            if space_mapping(a0, process).contains_key(path) {
                assert(crate::capability::boot_map::image_path(image@, path));
                let (ia, ix) = choose|ia: int, ix: int| 0 <= ia < image@.len() && #[trigger] in_virt_at(image@, ia, ix) && page_path(ix) == path;
                assert(in_virt_at(image@, ia, ix) && page_path(ix).l4 == l4);
                assert(image_l4(image@, l4));
            }
            assert(!space_mapping(a3, process).contains_key(path));
            assert(walk(a3, process, path) is None);
            s3.lemma_level1_empty(process, path);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            assert(crate::capability::map::frame_of(cap, 0) == bf / PAGE_SZ);
            assert(s3.can_map(process, ROOT_PROCESS_SLOT, SpaceKind::Process, path, WITNESS_FRAME_SLOT, 0));
        }
        let ok4 = self.map(process, ROOT_PROCESS_SLOT, l4, 0, 0, 0, WITNESS_FRAME_SLOT, 0);
        proof {
            let s4 = *self;
            let a4 = tree_of(&s4.table_pages, &s4.spaces);
            assert(ok4);
            assert(Self::map_done(s3, s4, process, ROOT_PROCESS_SLOT, path, WITNESS_FRAME_SLOT, 0));
            assert(space_mapping(a4, process) == space_mapping(a3, process).insert(path, entry));
            assert(space_mapping(a4, process) == space_mapping(a0, process).insert(path, entry));
            assert(space_mapping(a4, process).contains_key(path));
            assert(space_mapping(a4, process)[path] == entry);
        }
        ok1 && ok2 && ok3 && ok4
    }

    /// From the state boot leaves, when boot was given the IOMMU the device sits behind as present, as the root
    /// at `process`, with the order-3 block at `base` the first of three free ones past those boot's
    /// tables took from the first untyped: retype a leaf into root entry 2 of the root's table at the
    /// second block's first two pages, a process at `base` into slot 1 of that leaf, and a leaf at the
    /// second block's next two pages into root entry 0 of the process's table, through the process
    /// capability; record the device as boot does, its capability into slot 3 of the root's leaf, and
    /// retype a device space at the third block into slot 2; move the device's capability, then the
    /// space's, into slots 2 and 1 of the process's leaf, through the process capability; and, as the
    /// process, bind the device to the space. Every step succeeds, and at the end the device's record
    /// names the space, the space counts the device among its bound devices, the device's binding node
    /// is a child of the space capability in the process's slot 1, and the process is live and not the
    /// root. The root keeps what it needs to build another device space: its untyped, its leaf's slot 2
    /// empty again, the process capability in slot 1, and a fourth free block past the third; the
    /// process's slot 3 is empty, and the flush epoch and the IOMMUs are as boot left them. See
    /// design/device-binding-under-the-space-capability/.
    pub fn witness_process_binds_a_device(
        &mut self,
        root: usize,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
        info: DeviceInfo,
    ) -> (ret: bool)
        requires
            old(self).booted(root, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 4 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            info.iommu < NUM_IOMMUS,
            info.number < IOMMU_DEVICES,
            present@[info.iommu as int],
        ensures
            ret,
            ({
                let first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
                let b1 = (base + PROCESS_BYTES) as usize;
                let bl = (base + PROCESS_BYTES + 2 * PAGE_SZ) as usize;
                let bs = (base + 2 * PROCESS_BYTES) as usize;
                let sn = (bl + 1) as usize;
                let x = binding_node(&final(self).devices, 0);
                &&& witness_root(*final(self), process, (leaf@ + ROOT_UNTYPED_SLOT) as usize, first)
                &&& witness_block(*final(self), (base + 3 * PROCESS_BYTES) as usize, first)
                &&& witness_empty(*final(self), process, WITNESS_SPACE_SLOT, (b1 + 2) as usize)
                &&& final(self).slot_holds(process, WITNESS_PROCESS_SLOT, (b1 + 1) as usize, process_of(base))
                &&& witness_empty(*final(self), base, WITNESS_SECOND_SPACE_SLOT, (bl + 3) as usize)
                &&& final(self).tables.roots@.contains_key(base)
                &&& final(self).flush_epoch == old(self).flush_epoch
                &&& final(self).iommus == old(self).iommus
                &&& final(self).devices.count == 1
                &&& base % PROCESS_BYTES == 0
                &&& base + 4 * PROCESS_BYTES <= NODE_SPACE
                &&& final(self).wf()
                &&& base != process
                &&& witness_alive(*final(self), base)
                &&& final(self).slot_holds(base, WITNESS_BOUND_SPACE_SLOT, sn, space_of(bs))
                &&& final(self).slot_holds(base, WITNESS_BOUND_DEVICE_SLOT, (bl + 2) as usize, device_payload(0))
                &&& final(self).spaces.records@[bs].value().kind is Device
                &&& final(self).devices.records@[0] == bound_record(crate::capability::device::unbound_record(info), bs)
                &&& final(self).spaces.bound@[bs].contains(0)
                &&& final(self).list.is_child(sn, x)
                &&& final(self).list.nodes@[x as int].kind is DeviceBinding
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost blocks = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(blocks[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            let pn = (leaf@ + 1) as usize;
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            assert(witness_root(s0, process, u, first));
            // The three free blocks, one after another.
            assert(s0.root_untyped(process) == u);
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 4) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(base + 4 * PROCESS_BYTES <= NODE_SPACE);
            assert forall|j: int| 0 <= j < 4 implies #[trigger] witness_block(s0, cursor_block(base, j), first) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(s0.root_table_block(process, cursor_block(first.base, itb + j)));
            }
        }
        let b1 = base + PROCESS_BYTES;
        let bl = b1 + 2 * PAGE_SZ;
        let bs = b1 + PROCESS_BYTES;
        let ghost bs2 = (bs + PROCESS_BYTES) as usize;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(cursor_block(base, 0) == base);
            assert(witness_block(s0, base, first));
            assert(base % PROCESS_BYTES == 0);
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            lemma_cursor_block(base, 3);
            lemma_block_page(base, 0);
            lemma_block_page(b1, 0);
            lemma_block_page(b1, 2);
            lemma_block_page(bs, 0);
            assert(witness_block(s0, b1, first));
            assert(witness_block(s0, bs, first));
            assert(b1 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bs / PAGE_SZ == base / PAGE_SZ + 16);
            assert(bl / PAGE_SZ == b1 / PAGE_SZ + 2);
            assert(bs2 / PAGE_SZ == base / PAGE_SZ + 24);
            assert(s0.devices.count == 0);
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b1, 1));
            assert(s0.blocks.small_free((b1 / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at1, b1));
            assert(s1.tables.leaf(process, 2) == b1);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(witness_root(s1, process, u, first));
            assert(s1.root_live(process));
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_SPACE_SLOT) && index_entry(WITNESS_SPACE_SLOT) == 2);
            assert(index_ok(WITNESS_DEVICE_SLOT) && index_entry(WITNESS_DEVICE_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == b1 + 1);
            assert(!s1.list.nodes@[(b1 + 1) as int].live);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_SPACE_SLOT));
            assert(s1.tables.node_of(process, WITNESS_SPACE_SLOT) == b1 + 2);
            assert(witness_empty(s1, process, WITNESS_SPACE_SLOT, (b1 + 2) as usize));
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_DEVICE_SLOT));
            assert(s1.tables.node_of(process, WITNESS_DEVICE_SLOT) == b1 + 3);
            assert(witness_empty(s1, process, WITNESS_DEVICE_SLOT, (b1 + 3) as usize));
            lemma_run_kept(s0, s1, base, 0, 1, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            lemma_run_kept(s0, s1, base, 2, 4, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            assert forall|k: int| 2 <= k < 4 implies #[trigger] s1.blocks.pages@[b1 / PAGE_SZ + k].kind is Free by {
                assert(s0.blocks.tracks(b1 / PAGE_SZ + k));
                assert(s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free);
            }
            assert(s1.blocks.regions_2m@ == s0.blocks.regions_2m@);
            assert(s1.blocks.regions_1g@ == s0.blocks.regions_1g@);
        }

        // A process, in slot 1 of that leaf.
        proof {
            assert(witness_block(s1, cursor_block(base, 0), first));
            assert(witness_block(s1, base, first));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / PAGE_SZ + k].kind is Free by {
                    assert(s1.blocks.pages@[base / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, Tracked(&mut steps));
        let ghost s2 = *self;
        let ghost np = (b1 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / PAGE_SZ) as int, 3, None));
            assert(witness_alive(s2, base));
            assert(s2.tables.roots@.contains_key(base));
            assert(s2.payload_of(np) == process_of(base));
            assert(s2.payload_of(np).rights & right_bit(Right::Control) != 0);
            assert(s2.view().holds(process, np));
            assert(s2.is_cap(np));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            // The root's table keeps its new leaf, which the process's table lacks, so the two differ.
            assert(s2.tables.leaf(process, 2) == b1);
            assert(s2.tables.leaf(base, 2) == NO_LEAF);
            assert(base != process);
            assert(s2.tables.leaf(base, 0) == NO_LEAF);
            // The root's untyped, record and empty slots stay.
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s2.is_cap(u) && s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
            assert(s1.processes.records@.contains_key(process));
            assert(s2.tables.roots@.contains_key(process));
            assert(witness_root(s2, process, u, first));
            assert(s2.root_live(process));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_SPACE_SLOT));
            assert(witness_empty(s2, process, WITNESS_SPACE_SLOT, (b1 + 2) as usize));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_DEVICE_SLOT));
            assert(witness_empty(s2, process, WITNESS_DEVICE_SLOT, (b1 + 3) as usize));
            // The leaf's pages and the space's block stay free.
            lemma_run_kept(s1, s2, base, 2, 4, first, (base / PAGE_SZ) as int, base / PAGE_SZ + 8);
            assert forall|k: int| 2 <= k < 4 implies #[trigger] s2.blocks.pages@[b1 / PAGE_SZ + k].kind is Free by {
                assert(s1.blocks.tracks(b1 / PAGE_SZ + k));
                assert(s1.blocks.pages@[b1 / PAGE_SZ + k].kind is Free);
            }
        }

        // A leaf in root entry 0 of the process's table, through the process capability.
        let at2 = Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 };
        proof {
            assert(s2.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s2.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(block_within(bl, 1, first));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s2.blocks.small_free((bl / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s2.blocks.pages@[bl / PAGE_SZ + k].kind is Free by {
                    assert(s2.blocks.pages@[b1 / PAGE_SZ + (2 + k)].kind is Free);
                }
            }
            assert(s2.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok3 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl, Tracked(&mut steps));
        let ghost s3 = *self;
        proof {
            assert(ok3);
            assert(Self::leaf_retyped(s2, s3, process, ROOT_UNTYPED_SLOT, at2, bl));
            assert(s3.tables.leaf(base, 0) == bl);
            assert(index_ok(WITNESS_BOUND_SPACE_SLOT) && index_entry(WITNESS_BOUND_SPACE_SLOT) == 0) by (compute_only);
            assert(index_ok(WITNESS_BOUND_DEVICE_SLOT) && index_entry(WITNESS_BOUND_DEVICE_SLOT) == 0) by (compute_only);
            assert(s3.tables.has_slot(&s3.list, base, WITNESS_BOUND_SPACE_SLOT));
            assert(s3.tables.node_of(base, WITNESS_BOUND_SPACE_SLOT) == bl + 1);
            assert(!s3.list.nodes@[(bl + 1) as int].live);
            assert(s3.tables.has_slot(&s3.list, base, WITNESS_BOUND_DEVICE_SLOT));
            assert(s3.tables.node_of(base, WITNESS_BOUND_DEVICE_SLOT) == bl + 2);
            assert(!s3.list.nodes@[(bl + 2) as int].live);
            assert(s3.processes == s2.processes);
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.is_cap(u));
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s3.is_cap(u) && s3.payload_of(u) == first && s3.list.nodes@[u as int].depth == 1);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s3.is_cap(np) && s3.payload_of(np) == process_of(base));
            assert(s3.tables.roots@.contains_key(process));
            assert(witness_root(s3, process, u, first));
            assert(s3.root_live(process));
            assert(witness_alive(s3, base));
            assert(s3.tables.roots@.contains_key(base));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_SPACE_SLOT));
            assert(s3.tables.node_of(process, WITNESS_SPACE_SLOT) == b1 + 2);
            assert(witness_empty(s3, process, WITNESS_SPACE_SLOT, (b1 + 2) as usize));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_DEVICE_SLOT));
            assert(s3.tables.node_of(process, WITNESS_DEVICE_SLOT) == b1 + 3);
            assert(witness_empty(s3, process, WITNESS_DEVICE_SLOT, (b1 + 3) as usize));
            lemma_run_kept(s2, s3, base, 2, 4, first, (bl / PAGE_SZ) as int, bl / PAGE_SZ + 2);
            assert(s3.list.seq@[0] == root);
            assert(s3.tables.has_slot(&s3.list, base, WITNESS_SECOND_SPACE_SLOT)) by {
                assert(index_ok(WITNESS_SECOND_SPACE_SLOT) && index_entry(WITNESS_SECOND_SPACE_SLOT) == 0) by (compute_only);
            }
            assert(s3.tables.node_of(base, WITNESS_SECOND_SPACE_SLOT) == bl + 3);
            assert(!s3.list.nodes@[(bl + 3) as int].live);
            assert(s3.flush_epoch == s0.flush_epoch);
        }

        // The device, recorded as boot records one, its capability in slot 3 of the root's leaf.
        proof {
            assert(s3.devices.count == 0);
            assert(s3.devices.fresh(info));
            assert(s3.can_add_device(process, WITNESS_DEVICE_SLOT, info));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok4 = self.add_device(root, process, WITNESS_DEVICE_SLOT, info, Tracked(&mut steps));
        let ghost s4 = *self;
        let ghost nd = (b1 + 3) as usize;
        proof {
            assert(ok4);
            assert(Self::adds_cap(s3, s4, nd));
            assert(s4.is_cap(nd));
            assert(s4.payload_of(nd) == device_payload(0));
            assert(s3.devices.records@.len() == MAX_DEVICES) by {
                reveal(CapKernel::wf);
                reveal(devices_wf);
            }
            assert(s4.devices.records@[0] == crate::capability::device::unbound_record(info));
            assert(s3.list.nodes@[u as int].live);
            assert(u != nd);
            assert(s3.list.nodes@[np as int].live);
            assert(np != nd);
            s3.lemma_slot(process, WITNESS_DEVICE_SLOT);
            assert(nd % PAGE_SZ != 0);
            lemma_slot_kept_two(s3, s4, process, ROOT_UNTYPED_SLOT, nd, nd);
            lemma_slot_kept_two(s3, s4, process, WITNESS_PROCESS_SLOT, nd, nd);
            lemma_slot_kept_two(s3, s4, process, WITNESS_SPACE_SLOT, nd, nd);
            lemma_slot_kept_two(s3, s4, process, WITNESS_DEVICE_SLOT, nd, nd);
            lemma_slot_kept_two(s3, s4, base, WITNESS_BOUND_SPACE_SLOT, nd, nd);
            lemma_slot_kept_two(s3, s4, base, WITNESS_BOUND_DEVICE_SLOT, nd, nd);
            assert(s3.is_cap(u));
            assert(s4.is_cap(u) == s3.is_cap(u));
            assert(s4.is_cap(u));
            assert(s4.payload_of(u) == first);
            s3.lemma_slot_bound(u);
            assert(s4.list.nodes@[u as int].depth == s3.list.nodes@[u as int].depth);
            assert(s4.list.nodes@[u as int].depth == 1);
            assert(s3.is_cap(np));
            assert(s4.is_cap(np) && s4.payload_of(np) == process_of(base));
            assert(witness_root(s4, process, u, first));
            assert(s4.root_live(process));
            assert(witness_alive(s4, base));
            assert(!s4.list.nodes@[(b1 + 2) as int].live);
            assert(!s4.list.nodes@[(bl + 1) as int].live);
            assert(!s4.list.nodes@[(bl + 2) as int].live);
            assert(witness_block(s4, bs, first));
            // What the root needs to build a second device space later, and the process's empty slot 3.
            assert(u != (b1 + 2) as usize);
            lemma_slot_kept_two(s3, s4, base, WITNESS_SECOND_SPACE_SLOT, nd, nd);
            assert(!s4.list.nodes@[(bl + 3) as int].live);
            assert(witness_block(s3, cursor_block(base, 3), first));
            assert(witness_block(s4, bs2, first));
        }

        // A device space at the third block, in slot 2 of the root's leaf.
        proof {
            assert(s4.can_retype_under(process, ROOT_UNTYPED_SLOT, bs, 3));
            assert(s4.blocks.small_free((bs / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s4.blocks.pages@[bs / PAGE_SZ + k].kind is Free by {
                    assert(s4.blocks.pages@[bs / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s4.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, bs, 3));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok5 = self.retype_space(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, bs, Tracked(&mut steps));
        let ghost s5 = *self;
        let ghost ns = (b1 + 2) as usize;
        proof {
            assert(ok5);
            assert(Self::retype_keeps(s4, s5, ns, (bs / PAGE_SZ) as int, 3, None));
            assert(s5.payload_of(ns) == space_of(bs));
            assert(s5.list.nodes@[ns as int].depth == 2);
            assert(s5.view().holds(process, ns));
            assert(s5.is_cap(ns));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_SPACE_SLOT));
            assert(s5.tables.node_of(process, WITNESS_SPACE_SLOT) == ns);
            assert(s5.blocks.pages@[(bs / PAGE_SZ) as int].refs == 1);
            assert(s5.spaces.records@[bs].value().kind is Device);
            // The device capability, the process capability and the process's empty slots stay.
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_DEVICE_SLOT));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_DEVICE_SLOT));
            assert(s5.tables.node_of(process, WITNESS_DEVICE_SLOT) == nd);
            assert(s5.is_cap(nd) && s5.payload_of(nd) == device_payload(0));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_PROCESS_SLOT));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_PROCESS_SLOT));
            assert(s5.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s5.is_cap(np) && s5.payload_of(np) == process_of(base));
            assert(s4.tables.has_slot(&s4.list, base, WITNESS_BOUND_SPACE_SLOT));
            assert(s5.tables.has_slot(&s5.list, base, WITNESS_BOUND_SPACE_SLOT));
            assert(s5.tables.node_of(base, WITNESS_BOUND_SPACE_SLOT) == bl + 1);
            assert(!s5.list.nodes@[(bl + 1) as int].live);
            assert(s4.tables.has_slot(&s4.list, base, WITNESS_BOUND_DEVICE_SLOT));
            assert(s5.tables.has_slot(&s5.list, base, WITNESS_BOUND_DEVICE_SLOT));
            assert(s5.tables.node_of(base, WITNESS_BOUND_DEVICE_SLOT) == bl + 2);
            assert(!s5.list.nodes@[(bl + 2) as int].live);
            assert(s5.root_live(process));
            assert(witness_alive(s5, base));
            assert(s5.tables.roots@.contains_key(process));
            assert(order_pages(3) == 8);
            lemma_witness_block_kept(s4, s5, bs2, first, (bs / PAGE_SZ) as int, bs / PAGE_SZ + 8);
            assert(s4.tables.has_slot(&s4.list, process, ROOT_UNTYPED_SLOT));
            assert(s5.tables.has_slot(&s5.list, process, ROOT_UNTYPED_SLOT));
            assert(s5.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s5.is_cap(u) && s5.payload_of(u) == first && s5.list.nodes@[u as int].depth == 1);
            assert(witness_root(s5, process, u, first));
            assert(s4.tables.has_slot(&s4.list, base, WITNESS_SECOND_SPACE_SLOT));
            assert(s5.tables.has_slot(&s5.list, base, WITNESS_SECOND_SPACE_SLOT));
            assert(s5.tables.node_of(base, WITNESS_SECOND_SPACE_SLOT) == bl + 3);
            assert(!s5.list.nodes@[(bl + 3) as int].live);
        }

        // The device's capability, into slot 2 of the process's leaf, through the process capability.
        let from6 = Position { through: None, index: WITNESS_DEVICE_SLOT };
        let to6 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_BOUND_DEVICE_SLOT };
        proof {
            assert(s5.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s5.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            Self::lemma_device_moves_into_controlled(s5, s5, process, WITNESS_DEVICE_SLOT, WITNESS_PROCESS_SLOT, WITNESS_BOUND_DEVICE_SLOT);
            assert(s5.can_move_at(process, from6, to6));
        }
        let ok6 = self.move_cap(process, from6, to6);
        let ghost s6 = *self;
        let ghost dn = (bl + 2) as usize;
        proof {
            assert(ok6);
            assert(Self::cap_moved_between(s5, s6, process, WITNESS_DEVICE_SLOT, base, WITNESS_BOUND_DEVICE_SLOT));
            assert(Self::caps_frame(s5, s6, nd, dn));
            assert(s6.payload_of(dn) == device_payload(0));
            assert(s6.view().holds(base, dn));
            assert(s6.is_cap(dn));
            s5.lemma_slot(base, WITNESS_BOUND_DEVICE_SLOT);
            assert(dn % PAGE_SZ != 0);
            lemma_slot_kept_two(s5, s6, process, WITNESS_PROCESS_SLOT, nd, dn);
            lemma_slot_kept_two(s5, s6, process, WITNESS_SPACE_SLOT, nd, dn);
            lemma_slot_kept_two(s5, s6, base, WITNESS_BOUND_SPACE_SLOT, nd, dn);
            lemma_slot_kept_two(s5, s6, base, WITNESS_BOUND_DEVICE_SLOT, nd, dn);
            s5.lemma_slot(process, WITNESS_PROCESS_SLOT);
            s5.lemma_slot(process, WITNESS_SPACE_SLOT);
            Self::lemma_caps_frame(s5, s6, nd, dn, np);
            Self::lemma_caps_frame(s5, s6, nd, dn, ns);
            assert(s6.is_cap(np) && s6.payload_of(np) == process_of(base));
            assert(s6.is_cap(ns) && s6.payload_of(ns) == space_of(bs));
            assert(s6.list.nodes@[ns as int].depth == 2);
            assert(!s6.list.nodes@[(bl + 1) as int].live);
            assert(s6.processes.records == s5.processes.records);
            assert(s6.root_live(process));
            assert(witness_alive(s6, base));
            assert(s5.is_cap(u));
            assert(u != dn);
            lemma_slot_kept_two(s5, s6, process, ROOT_UNTYPED_SLOT, nd, dn);
            lemma_slot_kept_two(s5, s6, base, WITNESS_SECOND_SPACE_SLOT, nd, dn);
            Self::lemma_caps_frame(s5, s6, nd, dn, u);
            assert(s6.is_cap(u) && s6.payload_of(u) == first && s6.list.nodes@[u as int].depth == 1);
            assert(s6.tables.roots@.contains_key(process));
            assert(witness_root(s6, process, u, first));
            assert(!s6.list.nodes@[(bl + 3) as int].live);
            assert(witness_block(s6, bs2, first));
            assert(u != (bl + 1) as usize);
        }

        // The space's capability, into slot 1 of the process's leaf, through the process capability.
        let from7 = Position { through: None, index: WITNESS_SPACE_SLOT };
        let to7 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_BOUND_SPACE_SLOT };
        proof {
            assert(s6.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s6.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(!s6.cap_dead(ns));
            assert(s6.can_move_between(process, WITNESS_SPACE_SLOT, base, WITNESS_BOUND_SPACE_SLOT));
            assert(s6.can_move_at(process, from7, to7));
        }
        let ok7 = self.move_cap(process, from7, to7);
        let ghost s7 = *self;
        let ghost sn = (bl + 1) as usize;
        proof {
            assert(ok7);
            assert(Self::cap_moved_between(s6, s7, process, WITNESS_SPACE_SLOT, base, WITNESS_BOUND_SPACE_SLOT));
            assert(Self::caps_frame(s6, s7, ns, sn));
            assert(s7.payload_of(sn) == space_of(bs));
            assert(s7.list.nodes@[sn as int].depth == 2);
            assert(s7.view().holds(base, sn));
            assert(s7.is_cap(sn));
            s6.lemma_slot(base, WITNESS_BOUND_SPACE_SLOT);
            s6.lemma_slot(process, WITNESS_SPACE_SLOT);
            lemma_slot_kept_two(s6, s7, base, WITNESS_BOUND_SPACE_SLOT, ns, sn);
            lemma_slot_kept_two(s6, s7, base, WITNESS_BOUND_DEVICE_SLOT, ns, sn);
            Self::lemma_caps_frame(s6, s7, ns, sn, dn);
            assert(s7.is_cap(dn) && s7.payload_of(dn) == device_payload(0));
            assert(s7.tables.roots@.contains_key(base));
            assert(witness_alive(s7, base));
            lemma_slot_kept_two(s6, s7, process, ROOT_UNTYPED_SLOT, ns, sn);
            lemma_slot_kept_two(s6, s7, process, WITNESS_PROCESS_SLOT, ns, sn);
            lemma_slot_kept_two(s6, s7, process, WITNESS_SPACE_SLOT, ns, sn);
            lemma_slot_kept_two(s6, s7, base, WITNESS_SECOND_SPACE_SLOT, ns, sn);
            Self::lemma_caps_frame(s6, s7, ns, sn, u);
            Self::lemma_caps_frame(s6, s7, ns, sn, np);
            assert(s7.is_cap(u) && s7.payload_of(u) == first && s7.list.nodes@[u as int].depth == 1);
            assert(s7.tables.roots@.contains_key(process));
            assert(witness_root(s7, process, u, first));
            assert(s7.slot_holds(process, WITNESS_PROCESS_SLOT, np, process_of(base)));
            s7.lemma_slot(process, WITNESS_SPACE_SLOT);
            lemma_deleted_dead(s7, ns);
            assert(witness_empty(s7, process, WITNESS_SPACE_SLOT, ns));
            assert(!s7.list.nodes@[(bl + 3) as int].live);
            assert(witness_block(s7, bs2, first));
        }

        // The process binds the device to the space.
        proof {
            lemma_device_object(0);
            assert(device_of(s7.payload_of(dn).base) == 0);
            assert(s7.devices.records@[0] == crate::capability::device::unbound_record(info));
            assert(s7.iommus == s0.iommus);
            assert(s7.iommu_present(info.iommu as int));
            assert(s7.payload_of(sn).base == bs);
            assert(s7.blocks.pages@[(bs / PAGE_SZ) as int].refs == 1);
            assert(block_refs(&s7.blocks, BlockRef::Small(bs / PAGE_SZ)) == 1);
            assert(s7.can_bind_device(base, WITNESS_BOUND_DEVICE_SLOT, WITNESS_BOUND_SPACE_SLOT));
        }
        let ok8 = self.bind_device(base, WITNESS_BOUND_DEVICE_SLOT, WITNESS_BOUND_SPACE_SLOT);
        proof {
            let s8 = *self;
            assert(ok8);
            assert(Self::device_bound(s7, s8, sn, 0));
            let x = binding_node(&s7.devices, 0);
            assert(binding_node(&s8.devices, 0) == x);
            assert(s8.list.is_child(sn, x));
            // The binding node is neither moved capability: either, live in a leaf's slot, is a
            // capability, and the binding node is a binding.
            s7.lemma_slot(base, WITNESS_BOUND_SPACE_SLOT);
            s7.lemma_slot(base, WITNESS_BOUND_DEVICE_SLOT);
            if x == sn {
                assert(!s8.is_cap(sn));
                lemma_deleted_dead(s8, sn);
            }
            if x == dn {
                assert(!s8.is_cap(dn));
                lemma_deleted_dead(s8, dn);
            }
            assert(s8.devices.wf()) by {
                reveal(CapKernel::wf);
                reveal(devices_wf);
            }
            let page = s8.devices.page;
            lemma_fundamental_div_mod(page as int, PAGE_SZ as int);
            lemma_fundamental_div_mod_converse(x as int, PAGE_SZ as int, page as int / PAGE_SZ as int, 1);
            assert(x % PAGE_SZ == 1);
            lemma_slot_kept_two(s7, s8, base, WITNESS_BOUND_SPACE_SLOT, x, x);
            lemma_slot_kept_two(s7, s8, base, WITNESS_BOUND_DEVICE_SLOT, x, x);
            assert(s8.slot_holds(base, WITNESS_BOUND_SPACE_SLOT, sn, space_of(bs)));
            assert(s8.slot_holds(base, WITNESS_BOUND_DEVICE_SLOT, dn, device_payload(0)));
            assert(witness_alive(s8, base));
            assert(s8.spaces.records@[bs].value().kind is Device);
            assert(s8.devices.records@[0] == bound_record(crate::capability::device::unbound_record(info), bs));
            assert(s8.spaces.bound@[bs].contains(0));
            // What the root keeps to build a second device space, and the process's empty slot 3.
            s7.lemma_slot(process, WITNESS_SPACE_SLOT);
            s7.lemma_slot(base, WITNESS_SECOND_SPACE_SLOT);
            assert(index_slot(WITNESS_SPACE_SLOT) == 2 && index_slot(WITNESS_SECOND_SPACE_SLOT) == 3) by (compute_only);
            lemma_slot_kept_two(s7, s8, process, ROOT_UNTYPED_SLOT, x, x);
            lemma_slot_kept_two(s7, s8, process, WITNESS_PROCESS_SLOT, x, x);
            lemma_slot_kept_two(s7, s8, process, WITNESS_SPACE_SLOT, x, x);
            lemma_slot_kept_two(s7, s8, base, WITNESS_SECOND_SPACE_SLOT, x, x);
            assert(s8.is_cap(u) && s8.payload_of(u) == first && s8.list.nodes@[u as int].depth == 1);
            assert(witness_root(s8, process, u, first));
            assert(s8.slot_holds(process, WITNESS_PROCESS_SLOT, np, process_of(base)));
            assert(witness_empty(s8, process, WITNESS_SPACE_SLOT, ns));
            assert(witness_empty(s8, base, WITNESS_SECOND_SPACE_SLOT, (bl + 3) as usize));
            let p2 = bs2 / PAGE_SZ;
            assert(s7.blocks.tracks(p2 as int));
            assert(s8.blocks.regions_2m@[region_2m(p2 as int)].typed == s7.blocks.regions_2m@[region_2m(p2 as int)].typed);
            assert(s8.blocks.regions_1g@[region_1g(p2 as int)].typed == s7.blocks.regions_1g@[region_1g(p2 as int)].typed);
            assert forall|j: int| 0 <= j < 8 implies #[trigger] s8.blocks.pages@[bs2 / PAGE_SZ + j].kind is Free by {
                assert(s7.blocks.pages@[bs2 / PAGE_SZ + j].kind is Free);
                assert(s7.blocks.tracks(bs2 / PAGE_SZ + j));
            }
            assert(witness_block(s8, bs2, first));
        }
        ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8
    }

    /// From the state boot leaves, when boot was given the IOMMU the device sits behind as present, as the
    /// root at `process`, with the order-3 block at `base` the first of four free ones past those boot's
    /// tables took from the first untyped: build a process that binds a device to a device space, as
    /// witness_process_binds_a_device does; retype a second device space at the fourth block into slot 2
    /// of the root's leaf and move its capability into slot 3 of the process's leaf, through the process
    /// capability; and, as the process, unbind the device through its capability, let the device's IOMMU
    /// invalidate and acknowledge the unbind's epoch, and bind the device to the second space. Every step
    /// succeeds, and at the end the device's record names the second space, which counts the device
    /// among its bound devices, the first space no longer does, and the device's binding node is a child
    /// of the second space's capability. The use is a VMM handing a passthrough device from one guest to
    /// another. See design/device-binding-under-the-space-capability/.
    pub fn witness_process_moves_a_device_between_spaces(
        &mut self,
        root: usize,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
        info: DeviceInfo,
    ) -> (ret: bool)
        requires
            old(self).booted(root, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 4 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            info.iommu < NUM_IOMMUS,
            info.number < IOMMU_DEVICES,
            present@[info.iommu as int],
        ensures
            ret,
            ({
                let bl = (base + PROCESS_BYTES + 2 * PAGE_SZ) as usize;
                let bs = (base + 2 * PROCESS_BYTES) as usize;
                let bs2 = (base + 3 * PROCESS_BYTES) as usize;
                let sn2 = (bl + 3) as usize;
                let x = binding_node(&final(self).devices, 0);
                &&& final(self).wf()
                &&& witness_alive(*final(self), base)
                &&& final(self).slot_holds(base, WITNESS_SECOND_SPACE_SLOT, sn2, space_of(bs2))
                &&& final(self).slot_holds(base, WITNESS_BOUND_DEVICE_SLOT, (bl + 2) as usize, device_payload(0))
                &&& final(self).spaces.records@[bs2].value().kind is Device
                &&& final(self).devices.records@[0].space == Some(bs2)
                &&& final(self).spaces.bound@[bs2].contains(0)
                &&& !final(self).spaces.bound@[bs].contains(0)
                &&& final(self).list.is_child(sn2, x)
                &&& final(self).list.nodes@[x as int].kind is DeviceBinding
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ok1 = self.witness_process_binds_a_device(root, process, leaf, frames, t, free, image, untyped, frame, present, base, info);
        let ghost s1 = *self;
        let ghost first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let b1 = base + PROCESS_BYTES;
        let bl = b1 + 2 * PAGE_SZ;
        let bs = b1 + PROCESS_BYTES;
        let bs2 = bs + PROCESS_BYTES;
        let ghost np = (b1 + 1) as usize;
        let ghost ns = (b1 + 2) as usize;
        let ghost sn = (bl + 1) as usize;
        let ghost dn = (bl + 2) as usize;
        let ghost sn2 = (bl + 3) as usize;
        proof {
            lemma2_to64();
            assert(s0.flush_epoch == 0);
            assert(s1.flush_epoch == 0);
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(order_pages(3) == 8);
            lemma_cursor_block(base, 2);
            lemma_cursor_block(base, 3);
            assert(bs / PAGE_SZ == base / PAGE_SZ + 16);
            assert(bs2 / PAGE_SZ == base / PAGE_SZ + 24);
            assert(index_slot(WITNESS_BOUND_DEVICE_SLOT) == 2 && index_slot(WITNESS_SECOND_SPACE_SLOT) == 3) by (compute_only);
        }

        // A second device space at the fourth block, in slot 2 of the root's leaf.
        proof {
            assert(witness_root(s1, process, u, first));
            assert(s1.root_live(process));
            assert(witness_block(s1, bs2, first));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, bs2, 3));
            assert(s1.blocks.small_free((bs2 / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[bs2 / PAGE_SZ + k].kind is Free by {
                    assert(s1.blocks.pages@[bs2 / PAGE_SZ + k].kind is Free);
                }
            }
            assert(witness_empty(s1, process, WITNESS_SPACE_SLOT, ns));
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, bs2, 3));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok2 = self.retype_space(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, bs2, Tracked(&mut steps));
        let ghost s2 = *self;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, ns, (bs2 / PAGE_SZ) as int, 3, None));
            assert(s2.payload_of(ns) == space_of(bs2));
            assert(s2.is_cap(ns));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_SPACE_SLOT));
            assert(s2.tables.node_of(process, WITNESS_SPACE_SLOT) == ns);
            assert(s2.blocks.pages@[(bs2 / PAGE_SZ) as int].refs == 1);
            assert(s2.spaces.records@[bs2].value().kind is Device);
            // The process capability, the device's, and the process's empty slot 3 stay.
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s2.is_cap(np) && s2.payload_of(np) == process_of(base));
            assert(s1.tables.has_slot(&s1.list, base, WITNESS_BOUND_DEVICE_SLOT));
            assert(s2.tables.has_slot(&s2.list, base, WITNESS_BOUND_DEVICE_SLOT));
            assert(s2.tables.node_of(base, WITNESS_BOUND_DEVICE_SLOT) == dn);
            assert(s2.is_cap(dn) && s2.payload_of(dn) == device_payload(0));
            assert(s1.tables.has_slot(&s1.list, base, WITNESS_SECOND_SPACE_SLOT));
            assert(s2.tables.has_slot(&s2.list, base, WITNESS_SECOND_SPACE_SLOT));
            assert(s2.tables.node_of(base, WITNESS_SECOND_SPACE_SLOT) == sn2);
            assert(!s2.list.nodes@[sn2 as int].live);
            assert(s2.root_live(process));
            assert(witness_alive(s2, base));
            assert(s2.tables.roots@.contains_key(process));
            assert(s2.tables.roots@.contains_key(base));
            assert(s2.devices == s1.devices);
            assert(s2.spaces.bound@[bs].contains(0));
        }

        // The second space's capability, into slot 3 of the process's leaf, through the process capability.
        let from3 = Position { through: None, index: WITNESS_SPACE_SLOT };
        let to3 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_SECOND_SPACE_SLOT };
        proof {
            assert(PROCESS_RIGHTS & right_bit(Right::Control) != 0) by (compute_only);
            assert(s2.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s2.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(!s2.cap_dead(ns));
            assert(s2.can_move_between(process, WITNESS_SPACE_SLOT, base, WITNESS_SECOND_SPACE_SLOT));
            assert(s2.can_move_at(process, from3, to3));
        }
        let ok3 = self.move_cap(process, from3, to3);
        let ghost s3 = *self;
        proof {
            assert(ok3);
            assert(Self::cap_moved_between(s2, s3, process, WITNESS_SPACE_SLOT, base, WITNESS_SECOND_SPACE_SLOT));
            assert(Self::caps_frame(s2, s3, ns, sn2));
            assert(s3.payload_of(sn2) == space_of(bs2));
            assert(s3.list.nodes@[sn2 as int].depth == 2);
            assert(s3.is_cap(sn2));
            s2.lemma_slot(base, WITNESS_SECOND_SPACE_SLOT);
            s2.lemma_slot(process, WITNESS_SPACE_SLOT);
            lemma_slot_kept_two(s2, s3, base, WITNESS_SECOND_SPACE_SLOT, ns, sn2);
            lemma_slot_kept_two(s2, s3, base, WITNESS_BOUND_DEVICE_SLOT, ns, sn2);
            Self::lemma_caps_frame(s2, s3, ns, sn2, dn);
            assert(s3.slot_holds(base, WITNESS_BOUND_DEVICE_SLOT, dn, device_payload(0)));
            assert(s3.slot_holds(base, WITNESS_SECOND_SPACE_SLOT, sn2, space_of(bs2)));
            assert(s3.tables.roots@.contains_key(base));
            assert(witness_alive(s3, base));
            assert(s3.root_live(base));
        }

        // The process unbinds the device through its capability.
        let ghost x = binding_node(&s3.devices, 0);
        proof {
            lemma_device_object(0);
            assert(device_of(s3.payload_of(dn).base) == 0);
            assert(s3.devices.records@[0].space == Some(bs));
            assert(s3.can_unbind_device(base, WITNESS_BOUND_DEVICE_SLOT));
            // The binding node is in the devices' page, apart from every slot.
            assert(s3.devices.wf()) by {
                reveal(CapKernel::wf);
                reveal(devices_wf);
            }
            let page = s3.devices.page;
            lemma_fundamental_div_mod(page as int, PAGE_SZ as int);
            lemma_fundamental_div_mod_converse(x as int, PAGE_SZ as int, page as int / PAGE_SZ as int, 1);
            assert(x % PAGE_SZ == 1);
            s3.lemma_slot(base, WITNESS_BOUND_DEVICE_SLOT);
            s3.lemma_slot(base, WITNESS_SECOND_SPACE_SLOT);
            assert(x != dn && x != sn2);
            // The second space's block is typed and holds its one reference.
            s3.lemma_space_cap(sn2);
            assert(block_typed(&s3.blocks, BlockRef::Small(bs2 / PAGE_SZ)));
            assert(block_refs(&s3.blocks, BlockRef::Small(bs2 / PAGE_SZ)) == 1);
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok4 = self.unbind_device_at(base, WITNESS_BOUND_DEVICE_SLOT, Tracked(&mut steps));
        let ghost s4 = *self;
        proof {
            assert(ok4);
            assert(Self::device_unbound(s3, s4, x));
            assert(binding_device(&s3.devices, x) == 0);
            assert(s4.devices.records@[0].space is None);
            assert(s4.devices.records@[0].unbound == s4.flush_epoch);
            assert(s4.devices.records@[0].iommu == info.iommu);
            assert(!s4.spaces.bound@[bs].contains(0));
            lemma_slot_kept_two(s3, s4, base, WITNESS_BOUND_DEVICE_SLOT, x, x);
            lemma_slot_kept_two(s3, s4, base, WITNESS_SECOND_SPACE_SLOT, x, x);
            assert(s4.slot_holds(base, WITNESS_BOUND_DEVICE_SLOT, dn, device_payload(0)));
            assert(s4.slot_holds(base, WITNESS_SECOND_SPACE_SLOT, sn2, space_of(bs2)));
            assert(s4.list.nodes@[sn2 as int].depth == 2);
            // The unbind dropped the first space's reference, not the second's.
            assert(BlockRef::Small(bs2 / PAGE_SZ) != BlockRef::Small(bs / PAGE_SZ));
            assert(block_refs(&s4.blocks, BlockRef::Small(bs2 / PAGE_SZ)) == 1);
            assert(s4.iommus == s0.iommus);
            assert(s4.iommu_present(info.iommu as int));
            assert(witness_alive(s4, base));
        }

        // The device's IOMMU invalidates and acknowledges the unbind's epoch.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        self.flush_iommu(info.iommu, Tracked(&mut steps));
        let ghost s5 = *self;

        // The process binds the device to the second space.
        proof {
            assert(s5.iommu_acked(info.iommu as int) == s4.flush_epoch);
            assert(s5.slot_holds(base, WITNESS_BOUND_DEVICE_SLOT, dn, device_payload(0)));
            assert(s5.slot_holds(base, WITNESS_SECOND_SPACE_SLOT, sn2, space_of(bs2)));
            assert(s5.devices.records@[0].unbound <= s5.iommu_acked(info.iommu as int));
            assert(s5.iommu_present(info.iommu as int));
            assert(block_refs(&s5.blocks, BlockRef::Small(bs2 / PAGE_SZ)) == 1);
            assert(s5.list.nodes@[sn2 as int].depth < MAX_DEPTH);
            assert(s5.tables.roots@.contains_key(base));
            assert(s5.root_live(base));
            assert(s5.can_bind_device(base, WITNESS_BOUND_DEVICE_SLOT, WITNESS_SECOND_SPACE_SLOT));
        }
        let ok5 = self.bind_device(base, WITNESS_BOUND_DEVICE_SLOT, WITNESS_SECOND_SPACE_SLOT);
        proof {
            let s6 = *self;
            assert(ok5);
            assert(Self::device_bound(s5, s6, sn2, 0));
            assert(binding_node(&s5.devices, 0) == x);
            assert(binding_node(&s6.devices, 0) == x);
            assert(s6.list.is_child(sn2, x));
            assert(s6.devices.records@[0].space == Some(bs2));
            assert(s6.spaces.bound@[bs2].contains(0));
            assert(!s6.spaces.bound@[bs].contains(0));
            lemma_slot_kept_two(s5, s6, base, WITNESS_SECOND_SPACE_SLOT, x, x);
            lemma_slot_kept_two(s5, s6, base, WITNESS_BOUND_DEVICE_SLOT, x, x);
            assert(s6.slot_holds(base, WITNESS_SECOND_SPACE_SLOT, sn2, space_of(bs2)));
            assert(s6.slot_holds(base, WITNESS_BOUND_DEVICE_SLOT, dn, device_payload(0)));
            assert(witness_alive(s6, base));
            assert(s6.spaces.records@[bs2].value().kind is Device);
        }
        ok1 && ok2 && ok3 && ok4 && ok5
    }

    /// Retypes the 2M block at big as a frame into index to of the table at root, under the untyped at
    /// index from, and repeats the retype while it says Again: each Again zeroes more of the region, so
    /// the repeats end, and the last says Done. Returns that Done and the state its step began from,
    /// which has the list and the tables the call began with.
    #[verifier::spinoff_prover]
    fn witness_retype_2m(&mut self, root: usize, from: usize, to: usize, big: usize) -> (ret: (RetypeStep, Ghost<CapKernel>))
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
            old(self).can_retype_large(root, from, to, big, 9),
        ensures
            ret.0 is Done,
            Self::large_frame_retyped(ret.1@, *final(self), root, from, to, big, 9),
            ret.1@.list == old(self).list,
            ret.1@.tables == old(self).tables,
            final(self).wf(),
            final(self).processes == old(self).processes,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            Self::same_tree(*old(self), *final(self)),
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            block_typed(&final(self).blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M)),
            block_refs(&final(self).blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M)) == 1,
            !block_dead(&final(self).blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M)),
    {
        let ghost s0 = *self;
        let ghost mut mid = *self;
        let mut done = false;
        while !done
            invariant
                self.wf(),
                self.processes == s0.processes,
                self.stale_epoch == s0.stale_epoch,
                self.flush_epoch == s0.flush_epoch,
                Self::same_tree(s0, *self),
                self.cores == s0.cores,
                self.iommus == s0.iommus,
                self.tables.roots@.contains_key(root),
                self.root_live(root),
                !done ==> {
                    &&& self.list == s0.list
                    &&& self.tables == s0.tables
                    &&& self.can_retype_large(root, from, to, big, 9)
                },
                done ==> {
                    &&& Self::large_frame_retyped(mid, *self, root, from, to, big, 9)
                    &&& mid.list == s0.list
                    &&& mid.tables == s0.tables
                    &&& block_typed(&self.blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M))
                    &&& block_refs(&self.blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M)) == 1
                    &&& !block_dead(&self.blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M))
                },
            decreases (if done { 0 } else { 1 + witness_zero_left(*self, big / PAGE_SZ) }),
        {
            let ghost pre = *self;
            // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
            let tracked mut steps = Steps::fresh();
            let step = self.retype_large_frame(root, from, to, big, 9, Tracked(&mut steps));
            match step {
                RetypeStep::Refused => {
                    proof {
                        assert(false);
                    }
                },
                RetypeStep::Again => {
                    proof {
                        assert(Self::large_frame_zeroing(pre, *self, root, from, to, big, 9));
                        assert(witness_zero_left(*self, big / PAGE_SZ) < witness_zero_left(pre, big / PAGE_SZ));
                    }
                },
                RetypeStep::Done => {
                    proof {
                        mid = pre;
                        assert(self.tables.roots == pre.tables.roots);
                    }
                    done = true;
                },
            }
        }
        (RetypeStep::Done, Ghost(mid))
    }

    /// From the state boot leaves, as the root at `process`, with the 64 order-3 blocks from the jb-th
    /// past those boot's tables took from the first untyped a 2M region at `big`, and the next block
    /// free too: retype a leaf into root entry 2 of the root's table at that next block, retype the
    /// region as a 2M frame into slot 1 of the leaf, delete the frame's capability, retype the region
    /// under the root's untyped, which frees it, and retype it as a 2M frame into slot 1 again. Each
    /// retype of the frame repeats while it says Again, until the region is zero, and then says Done;
    /// the free says Freed, with the region free, out of every frame and not being zeroed, and at the
    /// end the root holds the frame's capability again. Returns the states the free began and ended
    /// in, so the free it proves is this run's, of a region dead at zero references. See
    /// design/teardown-driven-by-retype/.
    #[verifier::spinoff_prover]
    pub fn witness_root_retypes_a_freed_2m_frame(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        big: usize,
        jb: Ghost<int>,
    ) -> (ret: (RetypeStep, ReclaimStep, RetypeStep, Ghost<(CapKernel, CapKernel)>))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) <= jb@,
            jb@ + 65 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            big == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, jb@),
            big as int % block_bytes(9) == 0,
        ensures
            ret.0 is Done,
            ret.1 is Freed,
            ret.2 is Done,
            ret.3@.0.region_is_dead(Large::Two, big / PAGE_SZ / PAGES_PER_2M),
            ret.3@.0.large_frame_freed(ret.3@.1, 0, process, ROOT_UNTYPED_SLOT, big, 9),
            final(self).wf(),
            final(self).slot_holds(process, WITNESS_LARGE_FRAME_SLOT, (big + 64 * PROCESS_BYTES + 1) as usize, large_frame_of(big, 9)),
            block_typed(&final(self).blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M)),
            block_refs(&final(self).blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M)) == 1,
            !block_dead(&final(self).blocks, BlockRef::Two(big / PAGE_SZ / PAGES_PER_2M)),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost c0 = cursor_block(first.base, itb);
        let ghost jr = jb@ - itb;
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost r = big / PAGE_SZ / PAGES_PER_2M;
        let ghost g = (big / PAGE_SZ) as int;
        let at = Position { through: None, index: 2 };
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            assert(s0.root_untyped(process) == u);
            // The free blocks from the first past boot's tables to the leaf's, all in the untyped.
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((jb@ + 65) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(c0 == first.base + itb * PROCESS_BYTES);
            assert(big == first.base + jb@ * PROCESS_BYTES);
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(s0.root_table_block(process, c0));
            assert(c0 % PROCESS_BYTES == 0);
            // The untyped holds a 2M block, so its order is at least 9.
            if first.order < 9 {
                lemma_pow2_strictly_increases(first.order as nat, 9);
                assert(false);
            }
            assert forall|j: int| 0 <= j < jr + 65 implies #[trigger] s0.root_table_block(process, cursor_block(c0, j)) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(c0, j));
                assert(itb <= itb + j < untyped_tables(first));
            }
            assert(cursor_block(first.base, jb@) == cursor_block(c0, jr));
            lemma_free_2m(s0, process, c0, jr, big);
            lemma_cursor_block(c0, jr);
            lemma_cursor_block(c0, jr + 64);
            assert(big + 64 * PROCESS_BYTES == cursor_block(c0, jr + 64));
            assert(s0.root_table_block(process, cursor_block(c0, jr + 64)));
        }
        let lb = big + 64 * PROCESS_BYTES;
        let ghost nf = (lb + 1) as usize;
        proof {
            // The leaf's block, the one past the region.
            assert(lb / PAGE_SZ == g + PAGES_PER_2M);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(lb % PROCESS_BYTES == 0);
            lemma_aligned(lb);
            lemma_block_page(lb, 0);
            assert(lb != NO_LEAF);
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, lb, 1));
            assert(s0.blocks.small_free((lb / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb));
        }

        // A leaf for the root, in root entry 2 of its own table.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at, lb));
            assert(s1.tables.leaf(process, 2) == lb);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(s1.root_live(process));
            assert(index_ok(WITNESS_LARGE_FRAME_SLOT) && index_entry(WITNESS_LARGE_FRAME_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_LARGE_FRAME_SLOT));
            assert(s1.tables.node_of(process, WITNESS_LARGE_FRAME_SLOT) == nf);
            assert(!s1.list.nodes@[nf as int].live);
            // The region lies before the leaf's two pages, so it is still free.
            assert forall|i: int| r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M implies {
                &&& #[trigger] s1.blocks.pages@[i].kind is Free
                &&& !s1.blocks.covered(i)
            } by {
                assert(s0.blocks.pages@[i].kind is Free && !s0.blocks.covered(i));
                assert(s0.blocks.tracks(i));
                assert(i < lb / PAGE_SZ);
                assert(s1.blocks.pages@[i] == s0.blocks.pages@[i]);
            }
            assert(s1.blocks.large_free(Large::Two, r as int));
            assert(block_within(big, 9, first));
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, big, 9));
            assert(s1.can_retype_large(process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big, 9));
        }

        // The region as a 2M frame, in slot 1 of the leaf.
        let (ok2, m1) = self.witness_retype_2m(process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big);
        let ghost s2 = *self;
        let at_frame = Position { through: None, index: WITNESS_LARGE_FRAME_SLOT };
        proof {
            let m1 = m1@;
            assert(Self::large_frame_retyped(m1, s2, process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big, 9));
            assert(m1.wf());
            assert(m1.tables.has_slot(&m1.list, process, WITNESS_LARGE_FRAME_SLOT));
            assert(m1.tables.has_slot(&m1.list, process, ROOT_UNTYPED_SLOT));
            assert(m1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(m1.is_cap(u) && m1.payload_of(u) == first);
            lemma_large_retyped_slot(m1, s2, process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, nf, big);
            assert(s2.tables.roots@.contains_key(process));
            assert(s2.root_live(process));
            assert(s2.table_at(process, None) == Some(process));
            assert(s2.cap_at(process, at_frame) == Some(nf));
            assert(s2.can_delete_at(process, at_frame));
        }

        // Delete the frame's capability: the region's one reference.
        let ok3 = self.delete(process, at_frame);
        let ghost s3 = *self;
        proof {
            let m1 = m1@;
            assert(ok3 is Some);
            assert(Self::cap_deleted_at(s2, s3, process, at_frame));
            assert(Self::object_dropped(s2, s3, nf));
            assert(s2.payload_of(nf).kind is Frame);
            assert(s2.blocks.regions_2m@[r as int].typed);
            assert(block_ref(&s2.blocks, big / PAGE_SZ) == BlockRef::Two(r));
            assert(block_typed(&s3.blocks, BlockRef::Two(r)));
            assert(s3.region_is_dead(Large::Two, r));
            assert(s3.tables == s2.tables);
            assert(s3.processes == s2.processes);
            assert(s3.root_live(process));
            assert(s3.tables.roots@.contains_key(process));
            // The root's untyped is still its slot 5.
            lemma_slot_kept_two(m1, s2, process, ROOT_UNTYPED_SLOT, nf, nf);
            lemma_slot_kept_but(s2, s3, process, ROOT_UNTYPED_SLOT, nf);
            Self::lemma_caps_frame(m1, s2, nf, nf, u);
            Self::lemma_caps_frame(s2, s3, nf, nf, u);
            assert(s3.is_cap(u) && s3.payload_of(u) == first);
            // The untyped is shallower than the deepest: the leaf's hidden node is its child.
            assert(s1.list.is_child(u, lb));
            assert(s1.list.nodes@[lb as int].live) by {
                reveal(CapKernel::wf);
            }
            assert(s2.list.nodes@[lb as int].live);
            assert(s3.list.nodes@[lb as int].live);
            assert(s3.list.parent@[lb] == u);
            assert(page_of(lb) == lb);
            assert(s3.tables.owner@.contains_key(lb));
            lemma_owned_listed(s3, lb);
            assert(s3.list.nodes@[u as int].depth < MAX_DEPTH);
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, big, 9));
            assert(s3.can_reclaim_large(process, ROOT_UNTYPED_SLOT, big, 9));
            // Boot left every 2M region acknowledged, and no step since unmapped or moved an epoch.
            assert(s0.region_acknowledged(Large::Two, r));
            assert(s3.stale_epoch == s0.stale_epoch && s3.cores == s0.cores && s3.iommus == s0.iommus);
            let epoch = s0.stale_epoch.region(Large::Two, r) as int;
            assert forall|c: int| 0 <= c < NUM_CPUS implies epoch <= #[trigger] s3.acked(c) by {
                assert(s0.acked(c) == s3.acked(c));
            }
            assert forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] s3.iommu_present(i) implies epoch <= s3.iommu_acked(i) by {
                assert(s0.iommu_present(i) && s0.iommu_acked(i) == s3.iommu_acked(i));
            }
            assert(s3.region_acknowledged(Large::Two, r));
        }

        // Retype the region under the root's untyped: the frame is dead, so the retype frees it.
        let ok4 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, big, Tracked(&mut steps));
        let ghost s4 = *self;
        proof {
            assert(ok4 is Freed);
            assert(s3.large_frame_freed(s4, 0, process, ROOT_UNTYPED_SLOT, big, 9));
            assert(s4.list == s3.list && s4.tables == s3.tables && s4.processes == s3.processes);
            assert(s4.root_live(process));
            assert(s4.tables.roots@.contains_key(process));
            assert(s4.blocks.large_free(Large::Two, r as int));
            // Slot 1 of the leaf holds nothing again.
            lemma_slot_kept_two(m1@, s2, process, WITNESS_LARGE_FRAME_SLOT, nf, nf);
            lemma_slot_kept_but(s2, s3, process, WITNESS_LARGE_FRAME_SLOT, nf);
            assert(s3.tables.node_of(process, WITNESS_LARGE_FRAME_SLOT) == nf);
            lemma_deleted_dead(s3, nf);
            assert(s4.can_retype_under(process, ROOT_UNTYPED_SLOT, big, 9));
            assert(s4.can_retype_large(process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big, 9));
        }

        // The region as a 2M frame in slot 1 again.
        let (ok5, m4) = self.witness_retype_2m(process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big);
        proof {
            let s5 = *self;
            let m4 = m4@;
            assert(m4.wf());
            assert(m4.tables.has_slot(&m4.list, process, WITNESS_LARGE_FRAME_SLOT));
            assert(m4.tables.node_of(process, WITNESS_LARGE_FRAME_SLOT) == nf);
            lemma_large_retyped_slot(m4, s5, process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, nf, big);
        }
        (ok2, ok4, ok5, Ghost((s3, s4)))
    }

    /// Every core acknowledges the flush epoch and every present IOMMU flushes, so every acknowledgement
    /// reaches the epoch; nothing else that a retype reads changes.
    #[verifier::spinoff_prover]
    fn witness_acknowledge_all(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).all_acknowledged(old(self).flush_epoch as int),
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).blocks == old(self).blocks,
            final(self).spaces == old(self).spaces,
            final(self).devices == old(self).devices,
            final(self).processes == old(self).processes,
            final(self).table_pages == old(self).table_pages,
            final(self).mappings == old(self).mappings,
            final(self).iommus.present == old(self).iommus.present,
    {
        hide(CapKernel::wf);
        let ghost pre = *old(self);
        let mut c: usize = 0;
        while c < NUM_CPUS
            invariant
                c <= NUM_CPUS,
                self.wf(),
                self.flush_epoch == pre.flush_epoch,
                self.stale_epoch == pre.stale_epoch,
                self.list == pre.list,
                self.tables == pre.tables,
                self.blocks == pre.blocks,
                self.spaces == pre.spaces,
                self.devices == pre.devices,
                self.processes == pre.processes,
                self.table_pages == pre.table_pages,
                self.mappings == pre.mappings,
                self.iommus == pre.iommus,
                forall|d: int| 0 <= d < c ==> #[trigger] self.acked(d) == pre.flush_epoch,
            decreases NUM_CPUS - c,
        {
            let ghost before = *self;
            // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
            let tracked mut steps = Steps::fresh();
            self.acknowledge(c, Tracked(&mut steps));
            proof {
                assert forall|d: int| 0 <= d < c + 1 implies #[trigger] self.acked(d) == pre.flush_epoch by {
                    if d != c {
                        assert(self.cores@[d] == before.cores@[d]);
                        assert(before.acked(d) == pre.flush_epoch);
                    }
                }
            }
            c = c + 1;
        }
        let ghost cores = self.cores;
        let mut i: usize = 0;
        while i < NUM_IOMMUS
            invariant
                i <= NUM_IOMMUS,
                self.wf(),
                self.flush_epoch == pre.flush_epoch,
                self.stale_epoch == pre.stale_epoch,
                self.list == pre.list,
                self.tables == pre.tables,
                self.blocks == pre.blocks,
                self.spaces == pre.spaces,
                self.devices == pre.devices,
                self.processes == pre.processes,
                self.table_pages == pre.table_pages,
                self.mappings == pre.mappings,
                self.iommus.present == pre.iommus.present,
                self.cores == cores,
                forall|d: int| 0 <= d < NUM_CPUS ==> #[trigger] self.acked(d) == pre.flush_epoch,
                forall|j: int| 0 <= j < i && #[trigger] self.iommu_present(j) ==> self.iommu_acked(j) == pre.flush_epoch,
            decreases NUM_IOMMUS - i,
        {
            proof {
                assert(self.iommus.present.wf()) by {
                    reveal(CapKernel::wf);
                }
            }
            if *self.iommus.present.get(i) {
                let ghost before = *self;
                // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
                let tracked mut steps = Steps::fresh();
                self.flush_iommu(i, Tracked(&mut steps));
                proof {
                    assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) == pre.flush_epoch by {
                        assert(before.acked(d) == pre.flush_epoch);
                    }
                    assert forall|j: int| 0 <= j < i + 1 && #[trigger] self.iommu_present(j) implies self.iommu_acked(j) == pre.flush_epoch by {
                        if j != i {
                            assert(before.iommu_present(j));
                            assert(self.iommu_acked(j) == before.iommu_acked(j));
                        }
                    }
                }
            }
            i = i + 1;
        }
    }

    /// From the state boot leaves, when boot was given the IOMMU the device sits behind as present, as the
    /// root at `process`, with the order-3 block at `base` the first of three free ones past those boot's
    /// tables took from the first untyped: give the root a leaf at root entry 2 in the second block,
    /// record the device into slot 3 of it, retype a device space at `base` into slot 2, retype a table
    /// page at the third block and link it under entry 0 of the space's root through the space's
    /// capability, bind the device to the space and unbind it, which marks the space's root page stale at
    /// a new epoch, and delete the space's capability, its last reference. Then retype the space's block
    /// under the root's untyped until it is free: the first retype cuts the table from the dead space, the
    /// second waits, since no core has acknowledged the unbind's epoch, and after every core acknowledges
    /// and every present IOMMU flushes, the third frees the block. A device space at `base` into slot 2
    /// again closes it. Every step succeeds. The use is a VMM taking back a passthrough guest's IOMMU
    /// tables. See design/device-binding-under-the-space-capability/.
    #[verifier::spinoff_prover]
    pub fn witness_dead_device_space_freed(
        &mut self,
        root: usize,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        base: usize,
        info: DeviceInfo,
    ) -> (ret: (ReclaimStep, ReclaimStep, ReclaimStep, bool))
        requires
            old(self).booted(root, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) + 3 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            info.iommu < NUM_IOMMUS,
            info.number < IOMMU_DEVICES,
            present@[info.iommu as int],
        ensures
            ret.0 is Slice,
            ret.1 is Again,
            ret.2 is Freed,
            ret.3,
            final(self).wf(),
            final(self).slot_holds(process, WITNESS_SPACE_SLOT, (base + PROCESS_BYTES + 2) as usize, space_of(base)),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost blocks = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(blocks[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped and its record.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            let pn = (leaf@ + 1) as usize;
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            assert(witness_root(s0, process, u, first));
            // The three free blocks, one after another.
            assert(s0.root_untyped(process) == u);
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((itb + 3) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * PROCESS_BYTES);
            assert(base + 3 * PROCESS_BYTES <= NODE_SPACE);
            assert forall|j: int| 0 <= j < 3 implies #[trigger] witness_block(s0, cursor_block(base, j), first) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(base, j));
                assert(s0.root_table_block(process, cursor_block(first.base, itb + j)));
            }
        }
        let b1 = base + PROCESS_BYTES;
        let bt = b1 + PROCESS_BYTES;
        let ghost p = (base / PAGE_SZ) as int;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(order_pages(3) == 8);
            assert(cursor_block(base, 0) == base);
            assert(witness_block(s0, base, first));
            assert(base % PROCESS_BYTES == 0);
            lemma_cursor_block(base, 1);
            lemma_cursor_block(base, 2);
            lemma_block_page(base, 0);
            lemma_block_page(b1, 0);
            lemma_block_page(bt, 0);
            assert(witness_block(s0, b1, first));
            assert(witness_block(s0, bt, first));
            assert(b1 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == base / PAGE_SZ + 16);
            assert(s0.devices.count == 0);
            assert(s0.flush_epoch == 0);
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b1, 1));
            assert(s0.blocks.small_free((b1 / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[b1 / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b1, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at1, b1));
            assert(s1.tables.leaf(process, 2) == b1);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(witness_root(s1, process, u, first));
            assert(s1.root_live(process));
            assert(index_ok(WITNESS_SPACE_SLOT) && index_entry(WITNESS_SPACE_SLOT) == 2);
            assert(index_ok(WITNESS_DEVICE_SLOT) && index_entry(WITNESS_DEVICE_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_SPACE_SLOT));
            assert(s1.tables.node_of(process, WITNESS_SPACE_SLOT) == b1 + 2);
            assert(witness_empty(s1, process, WITNESS_SPACE_SLOT, (b1 + 2) as usize));
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_DEVICE_SLOT));
            assert(s1.tables.node_of(process, WITNESS_DEVICE_SLOT) == b1 + 3);
            assert(witness_empty(s1, process, WITNESS_DEVICE_SLOT, (b1 + 3) as usize));
            lemma_run_kept(s0, s1, base, 0, 1, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            lemma_run_kept(s0, s1, base, 2, 3, first, (b1 / PAGE_SZ) as int, b1 / PAGE_SZ + 2);
            assert(witness_block(s1, cursor_block(base, 0), first));
            assert(witness_block(s1, cursor_block(base, 2), first));
            assert(s1.flush_epoch == s0.flush_epoch);
        }

        // The device, recorded as boot records one, its capability in slot 3 of the root's leaf.
        proof {
            assert(s1.devices.count == 0);
            assert(s1.devices.fresh(info));
            assert(s1.can_add_device(process, WITNESS_DEVICE_SLOT, info));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok2 = self.add_device(root, process, WITNESS_DEVICE_SLOT, info, Tracked(&mut steps));
        let ghost s2 = *self;
        let ghost nd = (b1 + 3) as usize;
        let ghost ns = (b1 + 2) as usize;
        proof {
            assert(ok2);
            assert(Self::adds_cap(s1, s2, nd));
            assert(s2.is_cap(nd));
            assert(s2.payload_of(nd) == device_payload(0));
            assert(s1.devices.records@.len() == MAX_DEVICES) by {
                reveal(CapKernel::wf);
                reveal(devices_wf);
            }
            assert(s2.devices.records@[0] == crate::capability::device::unbound_record(info));
            assert(s1.list.nodes@[u as int].live);
            assert(u != nd);
            s1.lemma_slot(process, WITNESS_DEVICE_SLOT);
            assert(nd % PAGE_SZ != 0);
            lemma_slot_kept_two(s1, s2, process, ROOT_UNTYPED_SLOT, nd, nd);
            lemma_slot_kept_two(s1, s2, process, WITNESS_SPACE_SLOT, nd, nd);
            lemma_slot_kept_two(s1, s2, process, WITNESS_DEVICE_SLOT, nd, nd);
            assert(s1.is_cap(u));
            assert(s2.is_cap(u) == s1.is_cap(u));
            assert(s2.is_cap(u));
            assert(s2.payload_of(u) == first);
            s1.lemma_slot_bound(u);
            assert(s2.list.nodes@[u as int].depth == 1);
            assert(witness_root(s2, process, u, first));
            assert(s2.root_live(process));
            assert(!s2.list.nodes@[ns as int].live);
            assert(witness_block(s2, base, first));
            assert(witness_block(s2, bt, first));
        }

        // A device space at the first block, in slot 2 of the root's leaf.
        proof {
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s2.blocks.small_free(p, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s2.blocks.pages@[p + k].kind is Free by {
                    assert(s2.blocks.pages@[base / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s2.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, base, 3));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok3 = self.retype_space(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, base, Tracked(&mut steps));
        let ghost s3 = *self;
        proof {
            assert(ok3);
            assert(Self::retype_keeps(s2, s3, ns, p, 3, None));
            assert(s3.payload_of(ns) == space_of(base));
            assert(s3.is_cap(ns));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_SPACE_SLOT));
            assert(s3.tables.node_of(process, WITNESS_SPACE_SLOT) == ns);
            assert(s3.blocks.pages@[p].refs == 1);
            assert(!s3.blocks.pages@[p].dead);
            assert(s3.spaces.records@[base].value().kind is Device);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_DEVICE_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_DEVICE_SLOT));
            assert(s3.tables.node_of(process, WITNESS_DEVICE_SLOT) == nd);
            assert(s3.is_cap(nd) && s3.payload_of(nd) == device_payload(0));
            assert(s3.root_live(process));
            assert(s3.tables.roots@.contains_key(process));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s3.is_cap(u) && s3.payload_of(u) == first && s3.list.nodes@[u as int].depth == 1);
            assert(witness_root(s3, process, u, first));
            lemma_witness_block_kept(s2, s3, bt, first, p, p + 8);
            // The space's capability was not live before its retype, so it has no child after it.
            assert(s2.list.wf() && s3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(u != ns);
            lemma_added_children(s2.list, s3.list, ns, u);
        }

        // A table page at the third block, which the space's root will name.
        proof {
            assert(s3.wf());
            s3.lemma_space_cap(ns);
            assert(tree_of(&s3.table_pages, &s3.spaces).is_root(base));
            s3.lemma_table_base(base);
            assert(!tree_of(&s3.table_pages, &s3.spaces).is_page(base));
            assert(s3.blocks.pages@[bt / PAGE_SZ + 0].kind is Free);
            s3.lemma_free_not_table(bt, bt / PAGE_SZ);
            assert(s3.blocks.small_free((bt / PAGE_SZ) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s3.blocks.pages@[bt / PAGE_SZ + k].kind is Free by {
                    assert(s3.blocks.pages@[bt / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, 3));
            assert(s3.can_retype_table_page(process, ROOT_UNTYPED_SLOT, bt, 3));
            lemma_aligned(bt);
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok4 = self.retype_table_page(process, ROOT_UNTYPED_SLOT, bt, 3, Tracked(&mut steps));
        let ghost s4 = *self;
        proof {
            assert(ok4);
            let a = tree_of(&s3.table_pages, &s3.spaces);
            let m = tree_of(&s4.table_pages, &s4.spaces);
            Self::lemma_retype_nodes_kept(s3, s4, bt, u);
            assert(m.is_root(base));
            assert(!m.is_page(base));
            assert(m.record(base) == a.record(base));
            assert forall|i: usize| i < ENTRIES implies #[trigger] m.entry(base, i).is_empty() by {
                assert(s3.spaces.roots@[base].value()[i].is_empty());
            }
            assert(m.is_page(bt));
            s4.lemma_page_alive(bt);
            assert(s3.blocks.tracks(p));
            assert(s4.blocks.pages@[p] == s3.blocks.pages@[p]);
            assert(s4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_added_children(s3.list, s4.list, bt, u);
            assert(s4.tables == s3.tables);
            assert forall|x: usize| #[trigger] s4.is_cap(x) == s3.is_cap(x) by {}
            assert(s4.payload_of(ns) == space_of(base));
            assert(s4.payload_of(nd) == device_payload(0));
            assert(s4.payload_of(u) == first);
            assert(SPACE_RIGHTS & right_bit(Right::Write) != 0) by (compute);
            assert(s3.list.nodes@[ns as int].live);
            assert(s4.list.nodes@[ns as int].live);
            lemma_witness_slot_kept(s3, s4, process, ROOT_UNTYPED_SLOT, u, first, 1);
            lemma_witness_slot_kept(s3, s4, process, WITNESS_SPACE_SLOT, ns, space_of(base), s3.list.nodes@[ns as int].depth);
            lemma_witness_slot_kept(s3, s4, process, WITNESS_DEVICE_SLOT, nd, device_payload(0), s3.list.nodes@[nd as int].depth);
            assert(s4.is_cap(nd));
            assert(block_within(bt, 3, first));
            assert(s4.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, 3));
            assert(m.child_slot(base, 0));
            assert(s4.can_link(process, WITNESS_SPACE_SLOT, base, 0, ROOT_UNTYPED_SLOT, bt));
        }

        // Link the table page under entry 0 of the space's root, through the space's capability.
        let ok5 = self.link(process, WITNESS_SPACE_SLOT, base, 0, ROOT_UNTYPED_SLOT, bt);
        let ghost s5 = *self;
        proof {
            assert(ok5);
            assert(Self::link_done(s4, s5, base, 0, bt, base));
            let m = tree_of(&s4.table_pages, &s4.spaces);
            let b = tree_of(&s5.table_pages, &s5.spaces);
            assert(b.entry(base, 0) == child_entry(bt));
            assert(b.names_child(base, 0));
            assert forall|i: usize| 0 < i < ENTRIES implies #[trigger] b.entry(base, i).is_empty() by {
                assert(m.entry(base, i).is_empty());
            }
            assert(s5.list == s4.list && s5.tables == s4.tables && s5.blocks == s4.blocks);
            assert(s5.is_cap(ns) && s5.payload_of(ns) == space_of(base));
            assert(s5.is_cap(nd) && s5.payload_of(nd) == device_payload(0));
            assert(s5.is_cap(u) && s5.payload_of(u) == first);
            assert(s5.root_live(process));
            assert(s5.devices == s2.devices);
            assert(s5.iommus.present == s0.iommus.present);
        }

        // The root binds the device to the space.
        proof {
            lemma_device_object(0);
            assert(device_of(s5.payload_of(nd).base) == 0);
            assert(s5.devices.records@[0] == crate::capability::device::unbound_record(info));
            assert(s5.iommu_present(info.iommu as int));
            assert(s5.blocks.pages@[p].refs == 1);
            assert(block_refs(&s5.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(s5.list.nodes@[ns as int].depth == 2);
            assert(s5.can_bind_device(process, WITNESS_DEVICE_SLOT, WITNESS_SPACE_SLOT));
        }
        let ok6 = self.bind_device(process, WITNESS_DEVICE_SLOT, WITNESS_SPACE_SLOT);
        let ghost s6 = *self;
        let ghost x = binding_node(&s5.devices, 0);
        proof {
            assert(ok6);
            assert(Self::device_bound(s5, s6, ns, 0));
            assert(s6.list.is_child(ns, x));
            assert(s6.devices.wf()) by {
                reveal(CapKernel::wf);
                reveal(devices_wf);
            }
            let page = s6.devices.page;
            assert(binding_node(&s6.devices, 0) == x);
            lemma_fundamental_div_mod(page as int, PAGE_SZ as int);
            lemma_fundamental_div_mod_converse(x as int, PAGE_SZ as int, page as int / PAGE_SZ as int, 1);
            assert(x % PAGE_SZ == 1);
            s5.lemma_slot(process, WITNESS_SPACE_SLOT);
            s5.lemma_slot(process, WITNESS_DEVICE_SLOT);
            s5.lemma_slot(process, ROOT_UNTYPED_SLOT);
            lemma_slot_kept_two(s5, s6, process, ROOT_UNTYPED_SLOT, x, x);
            lemma_slot_kept_two(s5, s6, process, WITNESS_SPACE_SLOT, x, x);
            lemma_slot_kept_two(s5, s6, process, WITNESS_DEVICE_SLOT, x, x);
            assert(s6.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(ns != x);
            lemma_added_children(s5.list, s6.list, x, ns);
            assert(u != x);
            assert(s6.is_cap(u) && s6.payload_of(u) == first);
            assert(s6.root_live(process));
            assert(s6.tables.roots@.contains_key(process));
            assert(s6.devices.records@[0].space == Some(base));
            assert(s6.tlb_wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s6.acked(0) <= s6.flush_epoch);
        }

        // The root unbinds the device, which marks the space's root page stale at a new epoch.
        proof {
            assert(s6.payload_of(s6.tables.node_of(process, WITNESS_DEVICE_SLOT)).base == device_payload(0).base);
            assert(s6.can_unbind_device(process, WITNESS_DEVICE_SLOT));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok7 = self.unbind_device_at(process, WITNESS_DEVICE_SLOT, Tracked(&mut steps));
        let ghost s7 = *self;
        let ghost e = s7.flush_epoch;
        proof {
            assert(ok7);
            assert(binding_node(&s6.devices, 0) == x);
            assert(Self::device_unbound(s6, s7, x));
            assert(binding_device(&s6.devices, x) == 0);
            assert(s7.stale_epoch.pages@[p] == e);
            assert(e == s6.flush_epoch + 1);
            assert(s7.cores == s6.cores);
            assert(block_refs(&s7.blocks, BlockRef::Small(base / PAGE_SZ)) == 1);
            assert(s7.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_children_back(s6.list, s7.list, ns);
            lemma_slot_kept_two(s6, s7, process, ROOT_UNTYPED_SLOT, x, x);
            lemma_slot_kept_two(s6, s7, process, WITNESS_SPACE_SLOT, x, x);
            // The space's capability has no child: the binding went with the unbind, the table page is
            // the untyped's, and the capability had none when it was made.
            assert forall|y: usize| !#[trigger] s7.list.is_child(ns, y) by {
                if s7.list.is_child(ns, y) {
                    lemma_listed_live(s7.list, y);
                    assert(y != x);
                    assert(s6.list.is_child(ns, y));
                    assert(s5.list.is_child(ns, y));
                    assert(s4.list.is_child(ns, y));
                    if y == bt {
                        assert(s4.list.parent@[bt] == u);
                    }
                    assert(s3.list.is_child(ns, y));
                }
            }
            assert(s7.list.nodes@[ns as int].live);
            assert(ns < NODE_SPACE);
            if !s7.list.childless(ns) {
                s7.list.lemma_next_is_child(ns);
            }
            assert(s7.is_cap(ns));
            assert(s7.is_cap(u) && s7.payload_of(u) == first);
            assert(s7.root_live(process));
            assert(s7.tables.roots@.contains_key(process));
            assert(s7.table_at(process, None) == Some(process));
        }

        // Delete the space's capability, its last reference.
        let at = Position { through: None, index: WITNESS_SPACE_SLOT };
        proof {
            assert(s7.cap_at(process, at) == Some(ns));
            assert(s7.can_delete_at(process, at));
        }
        let ok8 = self.delete(process, at);
        let ghost s8 = *self;
        proof {
            assert(ok8 is Some);
            assert(Self::cap_deleted_at(s7, s8, process, at));
            assert(Self::object_dropped(s7, s8, ns));
            assert(s8.blocks.pages@[p].refs == 0);
            assert(s8.cores == s7.cores);
            assert(s8.stale_epoch == s7.stale_epoch);
            lemma_deleted_dead(s8, ns);
            lemma_slot_kept_but(s7, s8, process, ROOT_UNTYPED_SLOT, ns);
            lemma_slot_kept_but(s7, s8, process, WITNESS_SPACE_SLOT, ns);
            Self::lemma_caps_frame(s7, s8, ns, ns, u);
            assert(s8.is_cap(u) && s8.payload_of(u) == first);
            // The untyped is shallower than the deepest: the leaf's hidden node is its child.
            assert(s8.tables.leaf(process, 2) == b1);
            assert(s8.list.nodes@[b1 as int].live);
            assert(s1.list.parent@[b1] == u);
            assert(b1 != nd && b1 != ns && b1 != bt && b1 != x);
            assert(s8.list.parent@[b1] == u);
            s8.lemma_slot(process, WITNESS_SPACE_SLOT);
            assert(page_of(b1) == b1);
            assert(b1 < NODE_SPACE);
            lemma_owned_listed(s8, b1);
            assert(s8.list.nodes@[u as int].depth < MAX_DEPTH);
            assert(s8.root_live(process));
            assert(s8.tables.roots@.contains_key(process));
            assert(s8.dead_io_space(base));
            assert(witness_block(s0, base, first));
            assert(s8.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
        }

        // The space is dead and still names the table: the first retype of its block cuts the table.
        let ghost a = tree_of(&s8.table_pages, &s8.spaces);
        proof {
            assert(a == tree_of(&s5.table_pages, &s5.spaces));
            assert(a.names_child(base, 0));
            assert forall|i: usize| #[trigger] a.names_child(base, i) implies i == 0 by {
                if i != 0 {
                    assert(a.entry(base, i).is_empty());
                }
            }
            assert(s8.can_cut_space(process, ROOT_UNTYPED_SLOT, base));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let r1 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        let ghost s9 = *self;
        proof {
            assert(r1 is Slice);
            assert(s8.space_children_cut(s9, process, ROOT_UNTYPED_SLOT, base));
            assert(Self::table_cuts_kept(s8, s9, base));
            let b = tree_of(&s9.table_pages, &s9.spaces);
            let ca = child_entries(a, base);
            let cb = child_entries(b, base);
            // The cut took the one child, so nothing is left to cut.
            assert(ca.subset_of(set![0usize])) by {
                assert forall|i: usize| ca.contains(i) implies set![0usize].contains(i) by {
                    lemma_child_entries(a, base, i);
                }
            }
            vstd::set_lib::range_set_properties::<usize>(0, ENTRIES);
            vstd::set_lib::lemma_len_subset(ca, set![0usize]);
            assert(set![0usize].len() == 1);
            assert(cb.len() == 0);
            vstd::set_lib::lemma_set_empty_equivalency_len(cb);
            assert forall|i: usize| !#[trigger] b.names_child(base, i) by {
                lemma_child_entries(b, base, i);
            }
            assert(s9.space_is_spent(base));
            s9.lemma_spent_space_is_empty(base);
            assert(s9.list == s8.list && s9.tables == s8.tables && s9.blocks == s8.blocks);
            assert(s9.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            // The root page's stale epoch is the unbind's, which no core has acknowledged.
            assert(s9.stale_epoch.pages@[p] == e) by {
                assert(child_at(a, base, 0) == bt);
                assert(0 <= p < NUM_PAGES);
            }
            assert(s9.cores == s6.cores);
            assert(s9.acked(0) < e);
            assert(!s9.acknowledged(p as usize));
            assert(s9.root_live(process));
        }

        // The second retype waits: no core has acknowledged the unbind's epoch.
        let r2 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        proof {
            assert(r2 is Again);
            assert(*self == s9);
        }

        // Every core acknowledges and every present IOMMU flushes.
        self.witness_acknowledge_all();
        let ghost s10 = *self;
        proof {
            assert(s9.flush_epoch >= s8.flush_epoch);
            assert(s8.flush_epoch == e);
            assert(s10.acknowledged(p as usize)) by {
                assert forall|c: int| 0 <= c < NUM_CPUS implies e <= #[trigger] s10.acked(c) by {}
                assert forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] s10.iommu_present(i) implies e <= s10.iommu_acked(i) by {}
            }
            assert(s10.space_is_empty(base));
            assert(s10.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s10.root_live(process));
            assert(s10.tables.roots@.contains_key(process));
        }

        // The third retype frees the block.
        let r3 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, base, Tracked(&mut steps));
        let ghost s11 = *self;
        proof {
            assert(r3 is Freed);
            assert(s10.space_freed(s11, 0, process, ROOT_UNTYPED_SLOT, base));
            assert(Self::space_freed_step(s10, s11, base));
            assert(s10.empty_node_block(base));
            assert(s11.list.nodes == s10.list.nodes && s11.tables == s10.tables);
            assert(s11.is_cap(u) == s10.is_cap(u));
            assert(s10.blocks.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s10.blocks.tracks(p));
            s10.blocks.lemma_not_free_uncovered(p);
            assert(s11.blocks.small_free(p, 3)) by {
                assert(!s11.blocks.covered(p));
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s11.blocks.pages@[p + k].kind is Free by {
                    assert(s10.blocks.tracks(p + k));
                    assert(s10.blocks.in_block(p, p + k));
                }
            }
            lemma_slot_kept_but(s10, s11, process, WITNESS_SPACE_SLOT, ns);
            assert(witness_empty(s11, process, WITNESS_SPACE_SLOT, ns));
            assert(s11.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s11.root_live(process));
            assert(s11.tables.roots@.contains_key(process));
            assert(s11.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, base, 3));
        }

        // A device space at the same block, in slot 2 again.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok9 = self.retype_space(process, ROOT_UNTYPED_SLOT, WITNESS_SPACE_SLOT, base, Tracked(&mut steps));
        proof {
            let s12 = *self;
            assert(ok9);
            assert(s12.payload_of(ns) == space_of(base));
            assert(s12.view().holds(process, ns));
            assert(s12.tables.has_slot(&s12.list, process, WITNESS_SPACE_SLOT));
            assert(s12.tables.node_of(process, WITNESS_SPACE_SLOT) == ns);
        }
        (r1, r2, r3, ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8.is_some() && ok9)
    }

    /// Retypes the free order-3 block at `base` as a table page of `level`, under the untyped at index
    /// `from` of the table at `root`, where the retype is allowed: it succeeds and the page is a table's.
    /// A witness that ends on this retype keeps nothing else of the state it leaves.
    fn witness_table_page(&mut self, root: usize, from: usize, base: usize, level: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
            old(self).can_retype_table_page(root, from, base, level),
        ensures
            ret,
            final(self).wf(),
            final(self).table_pages.maps@.contains_key(base),
    {
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        self.retype_table_page(root, from, base, level, Tracked(&mut steps))
    }

    /// The setup of witness_dead_table_page_freed: from the state boot leaves, as its requires say, the
    /// leaf at the 65th block, the path tables at the last three and the 2M frame at `big` mapped at entry 1
    /// of the level 2 table. It leaves what dead_table_ready says the teardown needs.
    #[verifier::spinoff_prover]
    fn witness_dead_table_page_setup(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        big: usize,
        jb: Ghost<int>,
        l4: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) <= jb@,
            jb@ + 68 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            big == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, jb@),
            big as int % block_bytes(9) == 0,
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES,
            !image_l4(image@, l4),
        ensures
            ret,
            dead_table_ready(
                *final(self),
                process,
                (leaf@ + ROOT_UNTYPED_SLOT) as usize,
                page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]),
                big,
            ),
    {
        hide(CapKernel::wf);
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost cb = cursor_block(first.base, itb);
        let ghost jr = jb@ - itb;
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost pn = (leaf@ + 1) as usize;
        let ghost d = s0.list.nodes@[pn as int].depth;
        let ghost r = big / PAGE_SZ / PAGES_PER_2M;
        let ghost g = (big / PAGE_SZ) as int;
        let at = Position { through: None, index: 2 };
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped and its process capability.
            assert(0 < untyped@);
            assert(s0.slot_holds(process, ROOT_UNTYPED_SLOT, u, first));
            assert(s0.list.nodes@[u as int].depth == 1);
            assert(s0.tables.is_cap(&s0.list, u));
            assert(s0.tables.caps_wf(&s0.list)) by {
                reveal(CapKernel::wf);
            }
            assert(cap_wf(first));
            assert(payload_wf(first));
            assert(first.kind is Untyped && first.rights == UNTYPED_RIGHTS);
            assert(UNTYPED_RIGHTS & right_bit(Right::Retype) != 0) by (compute_only);
            assert(s0.slot_holds(process, ROOT_PROCESS_SLOT, pn, process_of(process)));
            s0.lemma_process_cap(pn);
            s0.lemma_process_space(pn);
            assert(s0.processes.records@.contains_key(process));
            assert(!s0.processes.records@[process].value().dead);
            assert(witness_root(s0, process, u, first));
            assert(witness_slot(s0, process, ROOT_PROCESS_SLOT, pn, process_of(process), d));
            // The free blocks from the first past boot's tables to the last path table's, all in the untyped.
            assert(s0.root_untyped(process) == u);
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), PROCESS_BYTES as int);
            lemma_mod_bound(block_bytes(first.order), PROCESS_BYTES as int);
            assert((jb@ + 68) * PROCESS_BYTES <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(cb == first.base + itb * PROCESS_BYTES);
            assert(big == first.base + jb@ * PROCESS_BYTES);
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(s0.root_table_block(process, cb));
            assert(cb % PROCESS_BYTES == 0);
            if first.order < 9 {
                lemma_pow2_strictly_increases(first.order as nat, 9);
                assert(false);
            }
            assert forall|j: int| 0 <= j < jr + 68 implies #[trigger] s0.root_table_block(process, cursor_block(cb, j)) by {
                assert(cursor_block(first.base, itb + j) == cursor_block(cb, j));
                assert(itb <= itb + j < untyped_tables(first));
            }
            assert(cursor_block(first.base, jb@) == cursor_block(cb, jr));
            lemma_free_2m(s0, process, cb, jr, big);
            lemma_cursor_block(cb, jr);
            lemma_cursor_block(cb, jr + 64);
            lemma_cursor_block(cb, jr + 65);
            lemma_cursor_block(cb, jr + 66);
            lemma_cursor_block(cb, jr + 67);
            assert(big + 64 * PROCESS_BYTES == cursor_block(cb, jr + 64));
            assert(s0.root_table_block(process, cursor_block(cb, jr + 64)));
            assert forall|j: int| jr + 65 <= j < jr + 68 implies #[trigger] witness_block(s0, cursor_block(cb, j), first) by {
                assert(s0.root_table_block(process, cursor_block(cb, j)));
            }
            assert(witness_block(s0, cursor_block(cb, jr + 65), first));
            assert(witness_block(s0, cursor_block(cb, jr + 66), first));
            assert(witness_block(s0, cursor_block(cb, jr + 67), first));
        }
        let lb = big + 64 * PROCESS_BYTES;
        let c0 = lb + PROCESS_BYTES;
        let c1 = c0 + PROCESS_BYTES;
        let ghost c2 = (c1 + PROCESS_BYTES) as usize;
        let ghost nf = (lb + 1) as usize;
        let ghost p = (c1 / PAGE_SZ) as int;
        proof {
            assert(lb / PAGE_SZ == g + PAGES_PER_2M);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(lb % PROCESS_BYTES == 0);
            lemma_aligned(lb);
            lemma_block_page(lb, 0);
            lemma_block_page(c0, 0);
            lemma_block_page(c1, 0);
            assert(c0 / PAGE_SZ == g + PAGES_PER_2M + 8);
            assert(p == g + PAGES_PER_2M + 16);
            assert(lb != NO_LEAF);
            assert(witness_block(s0, c0, first));
            assert(witness_block(s0, c1, first));
            assert(witness_block(s0, c2, first));
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, lb, 1));
            assert(s0.blocks.small_free((lb / PAGE_SZ) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free by {
                    assert(s0.blocks.pages@[lb / PAGE_SZ + k].kind is Free);
                }
            }
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb));
            // The root's process block is typed, so it lies outside the free blocks.
            assert(s0.blocks.tracks((process / PAGE_SZ) as int));
        }

        // A leaf for the root, in root entry 2 of its own table.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at, lb, Tracked(&mut steps));
        let ghost s1 = *self;
        proof {
            assert(ok1);
            assert(Self::leaf_retyped(s0, s1, process, ROOT_UNTYPED_SLOT, at, lb));
            assert(s1.tables.leaf(process, 2) == lb);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_UNTYPED_SLOT));
            assert(s0.is_cap(u));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s1.is_cap(u) && s1.payload_of(u) == first && s1.list.nodes@[u as int].depth == 1);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(witness_root(s1, process, u, first));
            assert(s0.tables.has_slot(&s0.list, process, ROOT_PROCESS_SLOT));
            assert(s0.is_cap(pn));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_PROCESS_SLOT));
            assert(s1.tables.node_of(process, ROOT_PROCESS_SLOT) == pn);
            assert(witness_slot(s1, process, ROOT_PROCESS_SLOT, pn, process_of(process), d));
            assert(witness_alive(s1, process));
            assert(index_ok(WITNESS_LARGE_FRAME_SLOT) && index_entry(WITNESS_LARGE_FRAME_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_LARGE_FRAME_SLOT));
            assert(s1.tables.node_of(process, WITNESS_LARGE_FRAME_SLOT) == nf);
            assert(!s1.list.nodes@[nf as int].live);
            assert(s1.list.nodes@[lb as int].live) by {
                reveal(CapKernel::wf);
            }
            assert(s1.list.parent@[lb] == u);
            lemma_run_kept(s0, s1, cb, jr + 65, jr + 68, first, (lb / PAGE_SZ) as int, lb / PAGE_SZ + 2);
            assert(witness_block(s1, c0, first));
            assert(witness_block(s1, c1, first));
            assert(witness_block(s1, c2, first));
            assert(s1.blocks.pages@[(process / PAGE_SZ) as int] == s0.blocks.pages@[(process / PAGE_SZ) as int]);
            assert(!s1.blocks.pages@[(process / PAGE_SZ) as int].dead);
            assert(tree_of(&s1.table_pages, &s1.spaces).is_root(process));
            assert(tree_of(&s1.table_pages, &s1.spaces).entry(process, l4).is_empty());
            assert(c0 + 3 * PROCESS_BYTES <= NODE_SPACE);
            // The region lies before the leaf's two pages, so it is still free.
            assert forall|i: int| r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M implies {
                &&& #[trigger] s1.blocks.pages@[i].kind is Free
                &&& !s1.blocks.covered(i)
            } by {
                assert(s0.blocks.pages@[i].kind is Free && !s0.blocks.covered(i));
                assert(s0.blocks.tracks(i));
                assert(i < lb / PAGE_SZ);
                assert(s1.blocks.pages@[i] == s0.blocks.pages@[i]);
            }
        }

        // The root's tables for the path, through its process capability.
        let ok2 = self.witness_path(process, ROOT_PROCESS_SLOT, process, l4, c0, Ghost(pn), Ghost(d), Ghost(u), Ghost(first));
        let ghost s2 = *self;
        let ghost a2 = tree_of(&s2.table_pages, &s2.spaces);
        proof {
            assert(ok2);
            assert(step(a2, process, l4) == Some(c0));
            assert(step(a2, c0, 0) == Some(c1));
            assert(step(a2, c1, 0) == Some(c2));
            assert(witness_root(s2, process, u, first));
            assert(witness_slot(s2, process, ROOT_PROCESS_SLOT, pn, process_of(process), d));
            assert(s2.list.nodes@[nf as int].live == s1.list.nodes@[nf as int].live);
            assert(nodes_kept(s1.list, s2.list));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_LARGE_FRAME_SLOT));
            assert(s2.list.nodes@[lb as int].live);
            // The region is free still: the path's blocks lie past it.
            assert forall|i: int| r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M implies {
                &&& #[trigger] s2.blocks.pages@[i].kind is Free
                &&& !s2.blocks.covered(i)
            } by {
                assert(s1.blocks.tracks(i));
                assert(i < c0 / PAGE_SZ);
                assert(s2.blocks.pages@[i] == s1.blocks.pages@[i]);
                assert(s1.blocks.pages@[i].kind is Free && !s1.blocks.covered(i));
            }
            assert(s2.blocks.large_free(Large::Two, r as int));
            assert(block_within(big, 9, first));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, big, 9));
            assert(s2.can_retype_large(process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big, 9));
        }

        // The region as a 2M frame, in slot 1 of the leaf.
        let (ok3, m2) = self.witness_retype_2m(process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big);
        let ghost s3 = *self;
        let ghost a3 = tree_of(&s3.table_pages, &s3.spaces);
        proof {
            let m2 = m2@;
            assert(a3 == a2);
            assert(Self::large_frame_retyped(m2, s3, process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, big, 9));
            assert(m2.wf());
            assert(m2.tables.has_slot(&m2.list, process, WITNESS_LARGE_FRAME_SLOT));
            assert(m2.tables.node_of(process, WITNESS_LARGE_FRAME_SLOT) == nf);
            lemma_large_retyped_slot(m2, s3, process, ROOT_UNTYPED_SLOT, WITNESS_LARGE_FRAME_SLOT, nf, big);
            assert(s3.slot_holds(process, WITNESS_LARGE_FRAME_SLOT, nf, large_frame_of(big, 9)));
            assert(s3.list.nodes@[nf as int].depth == m2.list.nodes@[u as int].depth + 1);
            assert(s3.list.nodes@[nf as int].depth == 2);
            lemma_slot_kept_two(m2, s3, process, ROOT_UNTYPED_SLOT, nf, nf);
            lemma_slot_kept_two(m2, s3, process, ROOT_PROCESS_SLOT, nf, nf);
            Self::lemma_caps_frame(m2, s3, nf, nf, u);
            Self::lemma_caps_frame(m2, s3, nf, nf, pn);
            assert(s3.is_cap(u) && s3.payload_of(u) == first);
            assert(s3.is_cap(pn) && s3.payload_of(pn) == process_of(process));
            assert(s3.tables.roots@.contains_key(process));
            assert(s3.root_live(process));
            assert(witness_alive(s3, process));
            s3.lemma_process_space(pn);
            assert(s3.spaces.records@[process].value().kind == SpaceKind::Process);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(FRAME_RIGHTS & right_bit(Right::Read) != 0) by (compute_only);
            // The level 2 table is live: its parent names it.
            assert(table_links_wf(a3)) by {
                reveal(CapKernel::wf);
            }
            assert(a3.names_child(c0, 0));
            assert(a3.entry(c0, 0).addr - TABLE_NODE_PAGES * PAGE_SZ == c1);
            assert(a3.is_page(c1));
            assert(s3.table_pages.records@[c1].value().parent is Some);
            s3.lemma_page_alive(c1);
            assert(walk_large_table(a3, process, SpacePath { l4, l3: 0, l2: 1, l1: 0 }) == Some(c1));
            assert(a3.entry(c1, 1).is_empty());
            assert(block_ref(&s3.blocks, big / PAGE_SZ) == BlockRef::Two(r));
            assert(crate::capability::map::frame_of(large_frame_of(big, 9), 0) == big / PAGE_SZ);
            assert(s3.can_map_large(process, ROOT_PROCESS_SLOT, SpaceKind::Process, SpacePath { l4, l3: 0, l2: 1, l1: 0 }, WITNESS_LARGE_FRAME_SLOT, 0));
        }

        // The frame at entry 1 of the level 2 table, whose entry 0 names the level 1 table.
        let ok4 = self.map_large(process, ROOT_PROCESS_SLOT, l4, 0, 1, WITNESS_LARGE_FRAME_SLOT, 0);
        let ghost s4 = *self;
        let ghost a4 = tree_of(&s4.table_pages, &s4.spaces);
        let ghost mn = mapping_node(c1, 1);
        proof {
            assert(ok4);
            assert(Self::map_large_done(s3, s4, process, ROOT_PROCESS_SLOT, SpacePath { l4, l3: 0, l2: 1, l1: 0 }, WITNESS_LARGE_FRAME_SLOT, 0));
            assert(mn == c1 + 2);
            assert(s4.mappings@[mn] == (MappingRecord { table: c1, entry: 1, frame: big / PAGE_SZ, large: true }));
            assert(mappings_wf(&s4.list, &s4.tables, a4, &s4.blocks, s4.holders@, s4.mappings@) && table_links_wf(a4)) by {
                reveal(CapKernel::wf);
            }
            assert(mapping_wf(&s4.list, &s4.tables, a4, &s4.blocks, s4.holders@, s4.mappings@, mn));
            assert(a4.record(c1).level == 2);
            assert(a4.entry(c1, 1).perm.present && a4.entry(c1, 1).perm.ps);
            assert forall|i: usize| i < ENTRIES && i != 1 implies #[trigger] a4.entry(c1, i) == a3.entry(c1, i) by {
                assert(s4.table_pages.maps@[c1].value()[i] == s3.table_pages.maps@[c1].value()[i]);
            }
            assert(a4.entry(c0, 0) == a3.entry(c0, 0));
            assert(a3.names_child(c1, 0));
            assert(a4.entry(c1, 0) == a3.entry(c1, 0));
            assert(a4.is_page(c1) && a4.record(c1).level == a3.record(c1).level);
            assert(a4.names_child(c1, 0));
            assert(a4.names_child(c0, 0));
            assert(a4.record(c1).parent == Some(TableParent { table: c0, entry: 0 }));
            // The page is live, the root's untyped is where it was.
            assert(table_page_wf(&s4.list, &s4.table_pages, &s4.blocks, c1)) by {
                reveal(CapKernel::wf);
            }
            assert(s4.list.nodes@[c1 as int].live);
            // The mapping's node lies in the table page's block, in no leaf, so it is not the untyped's.
            s3.lemma_map_node_place(c1, 1);
            lemma_slot_kept_but(s3, s4, process, ROOT_UNTYPED_SLOT, mn);
            assert(s3.is_cap(u) && s3.payload_of(u) == first);
            s3.lemma_slot_bound(u);
            assert(u != mn);
            assert(s4.list.nodes@[u as int].live == s3.list.nodes@[u as int].live);
            assert(s4.list.nodes@[u as int].kind == s3.list.nodes@[u as int].kind);
            assert(s4.is_cap(u) && s4.payload_of(u) == first);
            assert(s4.list.nodes@[u as int].depth == s3.list.nodes@[u as int].depth);
            assert(s3.list.nodes@[lb as int].live);
            assert(s3.list.parent@[lb] == u);
            assert(s4.list.nodes@[lb as int].live);
            assert(s4.list.parent@[lb] == u);
            assert(page_of(lb) == lb);
            lemma_owned_listed(s4, lb);
            assert(s4.list.nodes@[u as int].depth < MAX_DEPTH);
            assert(witness_block(s0, c1, first));
            assert(s4.can_retype_under(process, ROOT_UNTYPED_SLOT, c1, 3));
            assert(s4.root_live(process));
            assert(s4.tables.roots@.contains_key(process));
            assert(s4.flush_epoch == s0.flush_epoch);
            assert(s0.flush_epoch == 0);
            assert(s4.can_unlink_table(process, ROOT_UNTYPED_SLOT, c1));
            // The level 2 table names only its child at entry 0 and the frame at entry 1.
            assert forall|i: usize| 1 < i < ENTRIES implies #[trigger] a4.entry(c1, i).is_empty() by {
                assert(a4.entry(c1, i) == a3.entry(c1, i));
                assert(a2.entry(c1, i).is_empty());
            }
            assert(s4.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(dead_table_ready(s4, process, u, first, big));
        }
        ok1 && ok2 && ok4
    }

    /// The teardown of witness_dead_table_page_freed, from what dead_table_ready says of the state map_large
    /// left: retype the level 2 table's block at c1 under the root's untyped until it is free, five
    /// times, as that witness says, and close on a table page at the same block.
    #[verifier::spinoff_prover]
    fn witness_dead_table_page_teardown(
        &mut self,
        process: usize,
        c1: usize,
        u: Ghost<usize>,
        first: Ghost<Payload>,
        big: Ghost<usize>,
    ) -> (ret: (ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, bool, Ghost<(CapKernel, CapKernel, CapKernel, CapKernel, CapKernel)>))
        requires
            dead_table_ready(*old(self), process, u@, first@, big@),
            c1 == big@ + 66 * PROCESS_BYTES,
        ensures
            ret.0 is Unlinked,
            ret.1 is Slice,
            ret.2 is Slice,
            ret.3 is Again,
            ret.4 is Freed,
            ret.5,
            ({
                let (su, sc, sp, sa, s5) = ret.6@;
                &&& old(self).table_page_unlinked(su, process, ROOT_UNTYPED_SLOT, c1)
                &&& su.table_children_cut(sc, process, ROOT_UNTYPED_SLOT, c1)
                &&& sc.table_unmapped(sp, process, ROOT_UNTYPED_SLOT, c1)
                &&& !sp.acknowledged(c1 / PAGE_SZ)
                &&& sa.acknowledged(c1 / PAGE_SZ)
                &&& sa.table_freed(s5, 0, process, ROOT_UNTYPED_SLOT, c1)
            }),
            final(self).wf(),
            final(self).table_pages.maps@.contains_key(c1),
    {
        hide(CapKernel::wf);
        let ghost s4 = *self;
        let ghost a4 = tree_of(&s4.table_pages, &s4.spaces);
        let ghost u = u@;
        let ghost first = first@;
        let ghost big = big@;
        let ghost lb = (big + 64 * PROCESS_BYTES) as usize;
        let ghost c0 = (big + 65 * PROCESS_BYTES) as usize;
        let ghost p = (c1 / PAGE_SZ) as int;
        let ghost mn = mapping_node(c1, 1);
        proof {
            lemma2_to64();
            assert(mn == c1 + 2);
        }

        // The first retype of the table's block unlinks it from its parent.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let r1 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, c1, Tracked(&mut steps));
        let ghost su = *self;
        let ghost au = tree_of(&su.table_pages, &su.spaces);
        let ghost e = su.flush_epoch;
        proof {
            assert(r1 is Unlinked);
            assert(s4.table_page_unlinked(su, process, ROOT_UNTYPED_SLOT, c1));
            assert(detached(a4, au, c0, 0, c1));
            assert forall|i: usize| i < ENTRIES implies #[trigger] au.entry(c1, i) == a4.entry(c1, i) by {}
            assert(au.record(c1).level == 2);
            assert(au.names_child(c1, 0));
            assert(au.is_page(c1));
            assert(!su.list.nodes@[c1 as int].live);
            assert(su.tables == s4.tables && su.processes == s4.processes);
            lemma_slot_kept_but(s4, su, process, ROOT_UNTYPED_SLOT, c1);
            Self::lemma_caps_frame(s4, su, c1, c1, u);
            assert(su.is_cap(u) && su.payload_of(u) == first);
            assert(su.list.nodes@[u as int].depth == s4.list.nodes@[u as int].depth);
            assert(su.can_retype_under(process, ROOT_UNTYPED_SLOT, c1, 3));
            assert(su.root_live(process));
            assert(su.tables.roots@.contains_key(process));
            assert(su.stale_epoch.pages@[p] == e);
            assert(!su.acknowledged(p as usize));
            assert(su.blocks.tracks(p));
            assert(!su.all_acknowledged(e as int));
            assert(e == 1);
            assert(su.can_cut_table(process, ROOT_UNTYPED_SLOT, c1));
            // The one mapping in the page is the frame's at entry 1.
            assert(mappings_wf(&su.list, &su.tables, au, &su.blocks, su.holders@, su.mappings@)) by {
                reveal(CapKernel::wf);
            }
            assert(frame_slot(au, c1, 1));
            assert(su.mappings@.contains_key(mn) && su.mappings@[mn].table == c1 && su.mappings@[mn].entry == 1);
            assert forall|n: usize| #[trigger] su.mappings@.contains_key(n) && su.mappings@[n].table == c1 implies n == mn by {
                let m = su.mappings@[n];
                assert(mapping_wf(&su.list, &su.tables, au, &su.blocks, su.holders@, su.mappings@, n));
                assert(au.entry(c1, m.entry).perm.present && au.entry(c1, m.entry).perm.ps);
                if m.entry != 1 {
                    if m.entry != 0 {
                        assert(a4.entry(c1, m.entry).is_empty());
                    }
                    assert(false);
                }
            }
        }

        // The second cuts the level 1 table from it.
        let r2 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, c1, Tracked(&mut steps));
        let ghost sc = *self;
        let ghost ac = tree_of(&sc.table_pages, &sc.spaces);
        proof {
            assert(r2 is Slice);
            assert(su.table_children_cut(sc, process, ROOT_UNTYPED_SLOT, c1));
            assert(Self::table_cuts_kept(su, sc, c1));
            let ca = child_entries(au, c1);
            let cc = child_entries(ac, c1);
            assert(ca.subset_of(set![0usize])) by {
                assert forall|i: usize| ca.contains(i) implies set![0usize].contains(i) by {
                    lemma_child_entries(au, c1, i);
                    if i != 0 && i != 1 {
                        assert(a4.entry(c1, i).is_empty());
                    }
                }
            }
            vstd::set_lib::range_set_properties::<usize>(0, ENTRIES);
            vstd::set_lib::lemma_len_subset(ca, set![0usize]);
            assert(set![0usize].len() == 1);
            assert(cc.len() == 0);
            vstd::set_lib::lemma_set_empty_equivalency_len(cc);
            assert forall|i: usize| !#[trigger] ac.names_child(c1, i) by {
                lemma_child_entries(ac, c1, i);
            }
            assert(sc.list == su.list && sc.tables == su.tables && sc.mappings == su.mappings);
            assert(sc.can_retype_under(process, ROOT_UNTYPED_SLOT, c1, 3));
            assert(sc.root_live(process));
            assert(sc.stale_epoch.pages@[p] == e);
            assert(e <= sc.flush_epoch);
            // The frame's mapping stays, at a present entry of the page.
            assert(mappings_wf(&sc.list, &sc.tables, ac, &sc.blocks, sc.holders@, sc.mappings@)) by {
                reveal(CapKernel::wf);
            }
            assert(sc.mappings@.contains_key(mn));
            assert(mapping_wf(&sc.list, &sc.tables, ac, &sc.blocks, sc.holders@, sc.mappings@, mn));
            assert(au.is_table(c1));
            assert(ac.record(c1).level == 2);
            assert(frame_slot(ac, c1, 1));
            // The one cut raised the epoch by one.
            assert(ca.len() == 1);
            assert(sc.flush_epoch == e + 1);
            assert(sc.can_unmap_table(process, ROOT_UNTYPED_SLOT, c1));
            assert(!sc.can_cut_table(process, ROOT_UNTYPED_SLOT, c1));
        }

        // The third unlinks the frame's mapping.
        let r3 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, c1, Tracked(&mut steps));
        let ghost sp = *self;
        let ghost ap = tree_of(&sp.table_pages, &sp.spaces);
        proof {
            assert(r3 is Slice);
            assert(sc.table_sliced(sp, process, ROOT_UNTYPED_SLOT, c1));
            assert(!sc.table_children_cut(sp, process, ROOT_UNTYPED_SLOT, c1)) by {
                vstd::set_lib::range_set_properties::<usize>(0, ENTRIES);
                assert forall|i: usize| !#[trigger] child_entries(ac, c1).contains(i) by {
                    lemma_child_entries(ac, c1, i);
                }
                assert(child_entries(ac, c1) =~= Set::<usize>::empty());
            }
            assert(sc.table_unmapped(sp, process, ROOT_UNTYPED_SLOT, c1));
            let (nodes, states) = choose|nodes: Seq<usize>, states: Seq<Self>| {
                &&& #[trigger] Self::table_mapping_steps(sc, sp, c1, nodes, states)
                &&& 0 < nodes.len() <= TABLE_SLICE_BUDGET
                &&& Self::table_unmaps_kept(sc, sp, c1, nodes.len() as int)
            };
            assert(Self::table_mapping_step(states[0], states[1], c1, nodes[0]));
            assert(nodes[0] == mn);
            assert(states[1].mappings@ == sc.mappings@.remove(mn));
            if nodes.len() > 1 {
                assert(Self::table_mapping_step(states[1], states[2], c1, nodes[1]));
                assert(su.mappings@.contains_key(nodes[1]) && su.mappings@[nodes[1]].table == c1);
                assert(false);
            }
            assert(states[1] == sp);
            assert(sp.mappings@ == sc.mappings@.remove(mn));
            assert(Self::mapping_stale_noted(sc, sp, mn));
            // Nothing is left in the page.
            assert(mappings_wf(&sp.list, &sp.tables, ap, &sp.blocks, sp.holders@, sp.mappings@) && table_links_wf(ap)) by {
                reveal(CapKernel::wf);
            }
            assert(table_links_wf(ac)) by {
                reveal(CapKernel::wf);
            }
            assert forall|i: usize| !#[trigger] frame_slot(ap, c1, i) by {
                if frame_slot(ap, c1, i) {
                    assert(sp.mappings@.contains_key(mapping_node(c1, i)));
                    assert(su.mappings@.contains_key(mapping_node(c1, i)) && su.mappings@[mapping_node(c1, i)].table == c1);
                }
            }
            assert forall|i: usize| !#[trigger] ap.names_child(c1, i) by {
                if ap.names_child(c1, i) {
                    let ch = (ap.entry(c1, i).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize;
                    assert(ap.is_page(ch));
                    assert(ap.record(ch).parent == Some(TableParent { table: c1, entry: i }));
                    assert(sp.table_pages.records == sc.table_pages.records);
                    assert(ac.is_page(ch));
                    assert(ac.record(ch).parent == Some(TableParent { table: c1, entry: i }));
                    assert(ac.names_child(c1, i));
                }
            }
            assert(sp.table_pages.maps@.contains_key(c1));
            assert(sp.table_is_spent(c1));
            sp.lemma_spent_table_is_empty(c1);
            // The root's untyped is where it was.
            assert(sp.tables == sc.tables);
            assert(sp.is_cap(u) == sc.is_cap(u));
            assert(sp.list.nodes@[lb as int].live == sc.list.nodes@[lb as int].live);
            lemma_slot_kept_but(sc, sp, process, ROOT_UNTYPED_SLOT, mn);
            assert(sp.list.parent@[lb] == u);
            lemma_owned_listed(sp, lb);
            assert(sp.can_retype_under(process, ROOT_UNTYPED_SLOT, c1, 3));
            assert(sp.root_live(process));
            assert(sp.tables.roots@.contains_key(process));
            // The page's word is the unlink's, which nothing has acknowledged.
            assert(ac.entry(c1, 1) == a4.entry(c1, 1));
            assert(sc.mappings@[mn].frame * PAGE_SZ == big);
            assert(sc.mappings@[mn].frame == big / PAGE_SZ);
            assert(sc.mappings@[mn].large);
            assert(entry_pages(map_level(true)) == PAGES_PER_2M);
            assert(!record_pages(sc.mappings@[mn]).contains(p as usize));
            assert(sp.stale_epoch.pages@[p] == e);
            assert(sp.cores == su.cores);
            assert(sp.iommus.acked == su.iommus.acked && sp.iommus.present == su.iommus.present);
            assert(!sp.all_acknowledged(e as int)) by {
                if sp.all_acknowledged(e as int) {
                    assert forall|c: int| 0 <= c < NUM_CPUS implies e <= #[trigger] su.acked(c) by {
                        assert(sp.acked(c) == su.acked(c));
                    }
                    assert forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] su.iommu_present(i) implies e <= su.iommu_acked(i) by {
                        assert(sp.iommu_present(i));
                        assert(sp.iommu_acked(i) == su.iommu_acked(i));
                    }
                    assert(su.all_acknowledged(e as int));
                }
            }
            assert(!sp.acknowledged(p as usize));
            assert(e < sp.flush_epoch);
        }

        // The fourth waits: nothing has acknowledged the unlink's epoch.
        let r4 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, c1, Tracked(&mut steps));
        proof {
            assert(r4 is Again);
            assert(*self == sp);
        }

        // Every core acknowledges and every present IOMMU flushes.
        self.witness_acknowledge_all();
        let ghost sa = *self;
        proof {
            assert(sa.acknowledged(p as usize)) by {
                assert forall|c: int| 0 <= c < NUM_CPUS implies e <= #[trigger] sa.acked(c) by {}
                assert forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] sa.iommu_present(i) implies e <= sa.iommu_acked(i) by {}
            }
            assert(sa.table_is_empty(c1));
            assert(sa.can_retype_under(process, ROOT_UNTYPED_SLOT, c1, 3));
            assert(sa.root_live(process));
            assert(sa.tables.roots@.contains_key(process));
        }

        // The fifth frees the block.
        let r5 = self.reclaim(0, process, ROOT_UNTYPED_SLOT, c1, Tracked(&mut steps));
        let ghost s5 = *self;
        proof {
            assert(r5 is Freed);
            assert(sa.table_freed(s5, 0, process, ROOT_UNTYPED_SLOT, c1));
            assert(Self::table_freed_step(sa, s5, c1));
            assert(sa.empty_node_block(c1));
            assert(s5.list.nodes == sa.list.nodes && s5.tables == sa.tables);
            assert(sa.blocks.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(sa.blocks.tracks(p));
            sa.blocks.lemma_not_free_uncovered(p);
            assert(s5.blocks.small_free(p, 3)) by {
                assert(!s5.blocks.covered(p));
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s5.blocks.pages@[p + k].kind is Free by {
                    assert(sa.blocks.tracks(p + k));
                    assert(sa.blocks.in_block(p, p + k));
                }
            }
            assert(s5.is_cap(u) == sa.is_cap(u));
            assert(s5.can_retype_under(process, ROOT_UNTYPED_SLOT, c1, 3));
            assert(s5.root_live(process));
            assert(s5.tables.roots@.contains_key(process));
            assert(s5.can_retype_table_page(process, ROOT_UNTYPED_SLOT, c1, 2));
        }

        // A table page at the same block.
        let ok5 = self.witness_table_page(process, ROOT_UNTYPED_SLOT, c1, 2);
        (r1, r2, r3, r4, r5, ok5, Ghost((su, sc, sp, sa, s5)))
    }

    /// From the state boot leaves, as the root at `process`, with the 68 order-3 blocks from the jb-th
    /// past those boot's tables took from the first untyped free, the first 64 a 2M region at `big`, and
    /// entry l4 of the root's level 4 table past the kernel's and under no page of the image: retype a
    /// leaf into root entry 2 of the root's table at the 65th block, give the root's own space the level
    /// 3, 2 and 1 tables of the first page under entry l4 at the last three blocks, through its process
    /// capability, retype the region as a 2M frame into slot 1 of the leaf and map it at entry 1 of the
    /// level 2 table, whose entry 0 names the level 1 table. Then retype the level 2 table's block under
    /// the root's untyped until it is free: the first retype unlinks the page from its parent, the second
    /// cuts its child, the third unlinks the mapping, the fourth waits, since nothing has acknowledged the
    /// unlink's epoch, and after every core acknowledges and every present IOMMU flushes, the fifth frees
    /// the block. A table page at the same block closes it. Every step succeeds. The use is a process
    /// taking back the tables of a range it unmapped. See design/teardown-driven-by-retype/.
    #[verifier::spinoff_prover]
    pub fn witness_dead_table_page_freed(
        &mut self,
        root: Ghost<usize>,
        process: usize,
        leaf: Ghost<usize>,
        frames: Ghost<usize>,
        t: Ghost<usize>,
        free: Ghost<Seq<(usize, usize)>>,
        image: Ghost<Seq<ImageRun>>,
        untyped: Ghost<usize>,
        frame: Ghost<usize>,
        present: Ghost<Seq<bool>>,
        big: usize,
        jb: Ghost<int>,
        l4: usize,
    ) -> (ret: (ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, ReclaimStep, bool, Ghost<(CapKernel, CapKernel, CapKernel, CapKernel, CapKernel, CapKernel)>))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@),
            image_tables_bound(image@) <= jb@,
            jb@ + 68 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            big == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, jb@),
            big as int % block_bytes(9) == 0,
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES,
            !image_l4(image@, l4),
        ensures
            ret.0 is Unlinked,
            ret.1 is Slice,
            ret.2 is Slice,
            ret.3 is Again,
            ret.4 is Freed,
            ret.5,
            ({
                let (s4, su, sc, sp, sa, s5) = ret.6@;
                let c1 = (big + 66 * PROCESS_BYTES) as usize;
                &&& s4.table_page_unlinked(su, process, ROOT_UNTYPED_SLOT, c1)
                &&& su.table_children_cut(sc, process, ROOT_UNTYPED_SLOT, c1)
                &&& sc.table_unmapped(sp, process, ROOT_UNTYPED_SLOT, c1)
                &&& !sp.acknowledged(c1 / PAGE_SZ)
                &&& sa.acknowledged(c1 / PAGE_SZ)
                &&& sa.table_freed(s5, 0, process, ROOT_UNTYPED_SLOT, c1)
            }),
            final(self).wf(),
            final(self).table_pages.maps@.contains_key((big + 66 * PROCESS_BYTES) as usize),
    {
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
        let ok = self.witness_dead_table_page_setup(root, process, leaf, frames, t, free, image, untyped, frame, present, big, jb, l4);
        let ghost s4 = *self;
        let c1 = big + 66 * PROCESS_BYTES;
        let (r1, r2, r3, r4, r5, ok5, states) = self.witness_dead_table_page_teardown(process, c1, Ghost(u), Ghost(first), Ghost(big));
        let ghost (su, sc, sp, sa, s5) = states@;
        (r1, r2, r3, r4, r5, ok && ok5, Ghost((s4, su, sc, sp, sa, s5)))
    }
}

} // verus!
