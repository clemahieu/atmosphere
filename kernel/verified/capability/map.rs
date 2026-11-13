// SPDX-License-Identifier: MIT

//! Mapping a 4K or 2M page of a frame capability into a space, through tables already linked. The entry
//! is written from the capability's rights, and its node is derived as a child of the capability, so
//! revoking the capability reaches the mapping and delete is refused while it stands. See
//! design/address-spaces-as-objects/ and design/flush-without-waiting/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
#[cfg(verus_keep_ghost)]
use crate::capability::block::{BlockTable, NUM_1G, NUM_2M};
#[cfg(verus_keep_ghost)]
use crate::capability::zero::*;
use crate::capability::derive::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
#[cfg(verus_keep_ghost)]
use crate::arch::MEM_MASK;
use crate::define::*;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;
#[cfg(verus_keep_ghost)]
use crate::util::page_ptr_util_u::*;

/// The table path p reaches from root s, whose entry p.l1 is the page's.
pub open spec fn walk_table(tree: TableTree, s: usize, p: SpacePath) -> Option<usize> {
    if !tree.is_root(s) {
        None
    } else {
        match step(tree, s, p.l4) {
            None => None,
            Some(t3) => match step(tree, t3, p.l3) {
                None => None,
                Some(t2) => step(tree, t2, p.l2),
            },
        }
    }
}

/// The level 2 table p reaches from root s, whose entry p.l2 is a large frame's.
pub open spec fn walk_large_table(tree: TableTree, s: usize, p: SpacePath) -> Option<usize> {
    if !tree.is_root(s) {
        None
    } else {
        match step(tree, s, p.l4) {
            None => None,
            Some(t3) => step(tree, t3, p.l3),
        }
    }
}

/// The bytes one entry at a level covers: 4K at level 1, 2M at level 2, 1G at level 3 and 512G at
/// level 4.
pub open spec fn entry_span(level: u64) -> u64 {
    if level == 1 {
        PAGE_SZ as u64
    } else if level == 2 {
        SIZE_2M as u64
    } else if level == 3 {
        SIZE_1G as u64
    } else {
        SIZE_512G as u64
    }
}

/// The end of a space's lower half, which its first half of top-level entries covers.
pub const LOWER_HALF_END: u64 = (SIZE_512G * ENTRIES / 2) as u64;

/// Whether the address va names one entry at the level, 1 to 4: canonical in the lower half, and zero in
/// the bits below what the entry covers. See design/syscall-abi-in-registers/.
pub open spec fn names_entry(va: u64, level: u64) -> bool {
    &&& 1 <= level <= 4
    &&& va < LOWER_HALF_END
    &&& va % entry_span(level) == 0
}

/// The four 9-bit indices of the path through a space that the address va takes: bits 47 to 39, 38 to
/// 30, 29 to 21 and 20 to 12.
pub open spec fn address_path(va: u64) -> SpacePath {
    SpacePath {
        l4: ((va / (SIZE_512G as u64)) % (ENTRIES as u64)) as usize,
        l3: ((va / (SIZE_1G as u64)) % (ENTRIES as u64)) as usize,
        l2: ((va / (SIZE_2M as u64)) % (ENTRIES as u64)) as usize,
        l1: ((va / (PAGE_SZ as u64)) % (ENTRIES as u64)) as usize,
    }
}

/// Whether the address va names one entry at the level.
pub fn entry_named(va: u64, level: u64) -> (ret: bool)
    ensures
        ret == names_entry(va, level),
{
    if level == 0 || level > 4 || va >= LOWER_HALF_END {
        return false;
    }
    let span: u64 = if level == 1 {
        PAGE_SZ as u64
    } else if level == 2 {
        SIZE_2M as u64
    } else if level == 3 {
        SIZE_1G as u64
    } else {
        SIZE_512G as u64
    };
    va % span == 0
}

/// The indices of the path the address va takes, from level 4 down.
pub fn address_indices(va: u64) -> (ret: (usize, usize, usize, usize))
    ensures
        ret.0 == address_path(va).l4,
        ret.1 == address_path(va).l3,
        ret.2 == address_path(va).l2,
        ret.3 == address_path(va).l1,
        ret.0 < ENTRIES && ret.1 < ENTRIES && ret.2 < ENTRIES && ret.3 < ENTRIES,
{
    (
        ((va / (SIZE_512G as u64)) % (ENTRIES as u64)) as usize,
        ((va / (SIZE_1G as u64)) % (ENTRIES as u64)) as usize,
        ((va / (SIZE_2M as u64)) % (ENTRIES as u64)) as usize,
        ((va / (PAGE_SZ as u64)) % (ENTRIES as u64)) as usize,
    )
}

/// An address that names a level 2 entry has a zero level 1 index.
pub proof fn lemma_large_entry_path(va: u64)
    requires
        va % (SIZE_2M as u64) == 0,
    ensures
        address_path(va).l1 == 0,
{
    let k = va / (SIZE_2M as u64);
    assert(va == SIZE_2M * k) by (nonlinear_arith)
        requires va % (SIZE_2M as u64) == 0, k == va / (SIZE_2M as u64);
    assert(va / (PAGE_SZ as u64) == PAGES_PER_2M * k) by (nonlinear_arith)
        requires va == SIZE_2M * k;
    assert((PAGES_PER_2M * k) % (PAGES_PER_2M as int) == 0) by (nonlinear_arith);
}

/// The entry a map writes for a page of a capability with these rights: writable with Write, not
/// executable without Execute, and ps for a large frame.
pub open spec fn frame_map_entry(frame: usize, rights: u32, large: bool) -> PageEntry {
    PageEntry {
        addr: (frame * PAGE_SZ) as usize,
        perm: PageEntryPerm {
            present: true,
            ps: large,
            write: rights & right_bit(Right::Write) != 0,
            execute_disable: rights & right_bit(Right::Execute) == 0,
            user: true,
        },
    }
}

/// The page of a frame capability at this offset.
pub open spec fn frame_of(cap: Payload, page: usize) -> usize {
    (cap.base / PAGE_SZ + page) as usize
}

/// What writing frame mapping e of the table t changes between two trees: that entry, empty before, and
/// t's record apart from its level, space and parent. Every other entry and record is as it was.
pub open spec fn entry_written(a: TableTree, b: TableTree, t: usize, e: usize) -> bool {
    &&& b.maps.dom() == a.maps.dom()
    &&& b.roots == a.roots
    &&& b.space_records == a.space_records
    &&& forall|u: usize| u != t ==> #[trigger] b.record(u) == a.record(u)
    &&& b.record(t).level == a.record(t).level
    &&& b.record(t).space == a.record(t).space
    &&& b.record(t).parent == a.record(t).parent
    &&& a.is_page(t)
    &&& a.record(t).level == 1 || a.record(t).level == 2
    &&& e < ENTRIES
    &&& a.entry(t, e).is_empty()
    &&& b.entry(t, e).perm.present
    &&& b.entry(t, e).perm.ps == (a.record(t).level == 2)
    &&& forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        i < ENTRIES && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i)
}

/// A block's base is page aligned, since its size is a multiple of a page.
pub proof fn lemma_block_base_aligned(base: usize, order: u8)
    requires
        order <= MAX_ORDER,
        base as int % block_bytes(order) == 0,
    ensures
        base % PAGE_SZ == 0,
{
    let m = pow2(order as nat) as int;
    lemma_pow2_pos(order as nat);
    let d = m * PAGE_SZ;
    lemma_fundamental_div_mod(base as int, d);
    let q = base as int / d;
    assert(base as int == d * q);
    lemma_mul_is_associative(m, (PAGE_SZ as int), q);
    lemma_mul_is_commutative((PAGE_SZ as int), q);
    lemma_mul_is_associative(m, q, (PAGE_SZ as int));
    assert(base as int == (m * q) * PAGE_SZ);
    lemma_mod_multiples_basic(m * q, (PAGE_SZ as int));
}

/// An offset is below a block's page count exactly when its byte offset is below the block's size.
pub proof fn lemma_page_within(page: usize, size: usize, order: u8)
    requires
        order <= MAX_ORDER,
        size as int == block_bytes(order),
    ensures
        size % PAGE_SZ == 0,
        (page < size / PAGE_SZ) == ((page as int) * PAGE_SZ < block_bytes(order)),
{
    let m = pow2(order as nat) as int;
    lemma_pow2_pos(order as nat);
    assert(size as int == m * PAGE_SZ);
    lemma_mod_multiples_basic(m, (PAGE_SZ as int));
    lemma_div_multiples_vanish(m, (PAGE_SZ as int));
    assert(size as int / (PAGE_SZ as int) == m);
}

/// A 2M-aligned offset's 512 pages are within a 2M or 1G block exactly when the offset is below the
/// block's page count by at least 512.
pub proof fn lemma_large_page_within(page: usize, size: usize, order: u8)
    requires
        order == 9 || order == 18,
        size as int == block_bytes(order),
    ensures
        size % PAGE_SZ == 0,
        (page < size / PAGE_SZ && size / PAGE_SZ - page >= PAGES_PER_2M) == ((page as int) * PAGE_SZ + PAGES_PER_2M * PAGE_SZ <= block_bytes(order)),
{
    let m = pow2(order as nat) as int;
    lemma_pow2_pos(order as nat);
    assert(size as int == m * PAGE_SZ);
    lemma_mod_multiples_basic(m, (PAGE_SZ as int));
    lemma_div_multiples_vanish(m, (PAGE_SZ as int));
    assert(size as int / (PAGE_SZ as int) == m);
}

/// A block of order 9 or more has a base whose page is 2M aligned.
pub proof fn lemma_large_base_aligned(base: usize, order: u8)
    requires
        9 <= order <= MAX_ORDER,
        base as int % block_bytes(order) == 0,
    ensures
        base % PAGE_SZ == 0,
        (base / PAGE_SZ) % PAGES_PER_2M == 0,
{
    lemma_block_base_aligned(base, order);
    let m = pow2(order as nat) as int;
    lemma_pow2_pos(order as nat);
    lemma_pow2_adds(9, (order - 9) as nat);
    lemma2_to64();
    let k = pow2((order - 9) as nat) as int;
    assert(m == PAGES_PER_2M * k);
    let d = m * PAGE_SZ;
    lemma_fundamental_div_mod(base as int, d);
    let q = base as int / d;
    assert(base as int == d * q);
    lemma_mul_is_associative(m, (PAGE_SZ as int), q);
    lemma_mul_is_commutative((PAGE_SZ as int), q);
    lemma_mul_is_associative(m, q, (PAGE_SZ as int));
    assert(base as int == (m * q) * PAGE_SZ);
    lemma_div_multiples_vanish(m * q, (PAGE_SZ as int));
    assert(base as int / (PAGE_SZ as int) == m * q);
    lemma_mul_is_associative((PAGES_PER_2M as int), k, q);
    assert(m * q == PAGES_PER_2M * (k * q));
    lemma_mod_multiples_basic(k * q, (PAGES_PER_2M as int));
}

/// The sum of two multiples of 512 is one.
pub proof fn lemma_sum_aligned(x: int, y: int)
    requires
        x % (PAGES_PER_2M as int) == 0,
        y % (PAGES_PER_2M as int) == 0,
    ensures
        (x + y) % (PAGES_PER_2M as int) == 0,
{
    lemma_fundamental_div_mod(x, (PAGES_PER_2M as int));
    lemma_fundamental_div_mod(y, (PAGES_PER_2M as int));
    assert(x + y == PAGES_PER_2M * (x / (PAGES_PER_2M as int) + y / (PAGES_PER_2M as int)));
    lemma_mod_multiples_basic(x / (PAGES_PER_2M as int) + y / (PAGES_PER_2M as int), (PAGES_PER_2M as int));
}

/// A page below NUM_PAGES has an address with no bit outside MEM_MASK.
pub proof fn lemma_frame_addr_valid(frame: usize)
    requires
        frame < NUM_PAGES,
    ensures
        frame * PAGE_SZ < NUM_PAGES * PAGE_SZ,
        mem_valid((frame * PAGE_SZ) as usize),
{
    assert(frame < NUM_PAGES ==> ((frame * PAGE_SZ) as usize) & 0xffff_0000_0000_0fffusize == 0) by (bit_vector);
    assert((!MEM_MASK) as usize == 0xffff_0000_0000_0fffusize) by (compute_only);
}

/// Two mapping nodes are one node only for one entry of one table: a table's block is eight pages
/// aligned and the node pages are its first five.
pub proof fn lemma_mapping_node_injective(t: usize, e: usize, u: usize, d: usize)
    requires
        t % TABLE_PAGE_BYTES == 0,
        u % TABLE_PAGE_BYTES == 0,
        t / PAGE_SZ + TABLE_NODE_PAGES <= NUM_PAGES,
        u / PAGE_SZ + TABLE_NODE_PAGES <= NUM_PAGES,
        e < ENTRIES,
        d < ENTRIES,
        mapping_node(t, e) == mapping_node(u, d),
    ensures
        t == u,
        e == d,
{
    lemma_mapping_node_place(t, e);
    lemma_mapping_node_place(u, d);
    lemma_table_page_aligned(t);
    lemma_table_page_aligned(u);
    let ke = (e + 1) / (NODES_PER_PAGE as int);
    let kd = (d + 1) / (NODES_PER_PAGE as int);
    let qt = t / PAGE_SZ;
    let qu = u / PAGE_SZ;
    assert(0 <= ke <= 4);
    assert(0 <= kd <= 4);
    assert(qt + ke == qu + kd);
    lemma_fundamental_div_mod(qt as int, 8);
    lemma_fundamental_div_mod(qu as int, 8);
    assert(qt == qu);
    assert(t == u);
    assert(ke == kd);
    lemma_fundamental_div_mod(e + 1, NODES_PER_PAGE as int);
    lemma_fundamental_div_mod(d + 1, NODES_PER_PAGE as int);
}

/// The table pages after entry e of table page t is written present and t marked written: the page keeps
/// its address and its other entries, and a written record owes no empty entry.
pub proof fn lemma_table_pages_entry_written(list: &Tree, pa: &TablePages, pb: &TablePages, blocks: &BlockTable, t: usize, e: usize)
    requires
        table_pages_wf(list, pa, blocks),
        pa.maps@.contains_key(t),
        pb.spare == pa.spare,
        pb.maps@ == pa.maps@.insert(t, pb.maps@[t]),
        pb.maps@[t].addr() == pa.maps@[t].addr(),
        pb.maps@[t].is_init(),
        pb.maps@[t].value().wf(),
        pb.maps@[t].value().level == pa.maps@[t].value().level,
        pb.records@ == pa.records@.insert(t, pb.records@[t]),
        pb.records@[t].addr() == pa.records@[t].addr(),
        pb.records@[t].is_init(),
        pb.records@[t].value().level == pa.records@[t].value().level,
        pb.records@[t].value().parent == pa.records@[t].value().parent,
        pb.records@[t].value().written,
        pb.maps@[t].value()[e].perm.present,
        forall|i: usize| i < ENTRIES && i != e ==> #[trigger] pb.maps@[t].value()[i] == pa.maps@[t].value()[i],
    ensures
        table_pages_wf(list, pb, blocks),
{
    assert forall|u: usize| #[trigger] pb.maps@.contains_key(u) implies table_page_wf(list, pb, blocks, u) by {
        assert(pa.maps@.contains_key(u));
        assert(table_page_wf(list, pa, blocks, u));
        if u == t {
            assert forall|i: usize| i < ENTRIES implies #[trigger] pb.maps@[t].value()[i].perm.present || pb.maps@[t].value()[i].is_empty() by {
                if i != e {
                    assert(pa.maps@[t].value()[i].perm.present || pa.maps@[t].value()[i].is_empty());
                }
            }
            assert(table_record_wf(pb, t));
        } else {
            assert(pb.maps@[u] == pa.maps@[u]);
            assert(pb.records@[u] == pa.records@[u]);
            assert forall|i: usize| i < ENTRIES && !pb.records@[u].value().written implies #[trigger] pb.maps@[u].value()[i].is_empty() by {
                assert(pa.maps@[u].value()[i].is_empty());
            }
            assert(table_record_wf(pb, u));
        }
    }
    assert forall|b: usize| blocks.tracks(b as int) && #[trigger] table_block(blocks, b) implies pb.maps@.contains_key((b * PAGE_SZ) as usize) by {
        assert(pa.maps@.contains_key((b * PAGE_SZ) as usize));
    }
}

/// The links after frame mapping e of table t is written: the entry names no child in either tree, empty
/// before and at level 1 or with ps after, so no link reads it, and t's record keeps its parent and
/// space.
pub proof fn lemma_links_entry_written(a: TableTree, b: TableTree, t: usize, e: usize)
    requires
        table_links_wf(a),
        entry_written(a, b, t, e),
    ensures
        table_links_wf(b),
{
    reveal(table_links_wf);
    assert forall|u: usize| #[trigger] b.is_table(u) == a.is_table(u) && b.is_page(u) == a.is_page(u) && b.is_root(u) == a.is_root(u) by {
        assert(b.maps.contains_key(u) == a.maps.contains_key(u));
    }
    assert forall|u: usize| #[trigger] b.record(u).level == a.record(u).level by {
        if u != t {
            assert(b.record(u) == a.record(u));
        }
    }
    assert forall|u: usize, i: usize| #[trigger] b.child_slot(u, i) == a.child_slot(u, i) by {}
    assert(!a.names_child(t, e));
    assert(!b.names_child(t, e));
    assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        b.names_child(u, i) implies {
        let c = (b.entry(u, i).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize;
        &&& b.is_page(c)
        &&& b.record(c).parent == Some(TableParent { table: u, entry: i })
        &&& b.entry(u, i).perm.write
        &&& b.entry(u, i).perm.user
    } by {
        assert(a.child_slot(u, i));
        assert(!(u == t && i == e));
        assert(b.entry(u, i) == a.entry(u, i));
        assert(a.names_child(u, i));
        let _ = a.entry(u, i);
        let c = (a.entry(u, i).addr - TABLE_NODE_PAGES * PAGE_SZ) as usize;
        assert(a.is_page(c));
        assert(b.record(c).parent == a.record(c).parent);
    }
    assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
        b.child_slot(u, i) && b.entry(u, i).perm.present && b.entry(u, i).perm.ps implies b.record(u).level == 2 by {
        assert(a.child_slot(u, i));
        if !(u == t && i == e) {
            assert(b.entry(u, i) == a.entry(u, i));
            let _ = a.entry(u, i);
        }
    }
    assert forall|c: usize| #![trigger b.maps.contains_key(c)] b.is_page(c) implies {
        let r = b.record(c);
        &&& r.parent is Some ==> r.space is Some
        &&& r.parent is Some ==> {
            let p = r.parent->0;
            &&& b.names_child(p.table, p.entry)
            &&& b.entry(p.table, p.entry).addr == table_addr(c)
            &&& b.record(p.table).level == r.level + 1
            &&& b.record(p.table).space == r.space
        }
    } by {
        assert(a.is_page(c));
        assert(a.maps.contains_key(c));
        let r = a.record(c);
        assert(b.record(c).parent == r.parent);
        assert(b.record(c).space == r.space);
        assert(b.record(c).level == r.level);
        if r.parent is Some {
            let p = r.parent->0;
            assert(a.names_child(p.table, p.entry));
            assert(!(p.table == t && p.entry == e));
            assert(b.entry(p.table, p.entry) == a.entry(p.table, p.entry));
            assert(b.record(p.table).space == a.record(p.table).space);
        }
    }
}

/// Path p of space r reaches frame mapping e of table t, at t's level: entry p.l1 of a level 1 table, or
/// entry p.l2 of a level 2 table at the path of its first page. Unlike ends_at, it reads no entry of t,
/// so it holds of the tree before the write.
pub open spec fn reaches(tree: TableTree, r: usize, p: SpacePath, t: usize, e: usize) -> bool {
    &&& tree.is_root(r)
    &&& match step(tree, r, p.l4) {
        None => false,
        Some(t3) => match step(tree, t3, p.l3) {
            None => false,
            Some(t2) => if tree.record(t).level == 2 {
                p.l1 == 0 && p.l2 == e && t2 == t
            } else {
                p.l1 == e && step(tree, t2, p.l2) == Some(t)
            },
        },
    }
}

/// Writing frame mapping e of table t changes the walks that reach it and no other: a step reads only
/// entries that name a child, which the entry does in neither tree, and a frame entry is read only by
/// the walk that reaches it.
pub proof fn lemma_walk_entry_written(a: TableTree, b: TableTree, t: usize, e: usize, r: usize, p: SpacePath)
    requires
        entry_written(a, b, t, e),
    ensures
        walk(b, r, p) == (if reaches(a, r, p, t, e) { Some(b.entry(t, e)) } else { walk(a, r, p) }),
{
    assert forall|u: usize| #[trigger] b.is_table(u) == a.is_table(u) && b.is_page(u) == a.is_page(u) && b.is_root(u) == a.is_root(u) by {
        assert(b.maps.contains_key(u) == a.maps.contains_key(u));
    }
    assert forall|u: usize| #[trigger] b.record(u).level == a.record(u).level by {
        if u != t {
            assert(b.record(u) == a.record(u));
        }
    }
    assert(!a.names_child(t, e));
    assert(!b.names_child(t, e));
    assert forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i) by {
        assert(b.child_slot(u, i) == a.child_slot(u, i));
        if a.child_slot(u, i) && !(u == t && i == e) {
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert forall|u: usize, i: usize| !(u == t && i == e) implies #[trigger] frame_entry(b, u, i) == frame_entry(a, u, i)
        && large_entry(b, u, i) == large_entry(a, u, i) by {
        if a.is_table(u) && i < ENTRIES {
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert(frame_entry(a, t, e) is None);
    assert(large_entry(a, t, e) is None);
    if a.record(t).level == 2 {
        assert(frame_entry(b, t, e) is None);
        assert(large_entry(b, t, e) == Some(b.entry(t, e)));
    } else {
        assert(frame_entry(b, t, e) == Some(b.entry(t, e)));
        assert(large_entry(b, t, e) is None);
    }
    if a.is_root(r) {
        if let Some(t3) = step(a, r, p.l4) {
            if let Some(t2) = step(a, t3, p.l3) {
                if let Some(t1) = step(a, t2, p.l2) {
                    assert(!(t2 == t && p.l2 == e));
                    if t1 == t && p.l1 == e {
                        if a.record(t).level == 2 {
                            assert(!reaches(a, r, p, t, e));
                        } else {
                            assert(reaches(a, r, p, t, e));
                        }
                    } else {
                        assert(!reaches(a, r, p, t, e));
                        assert(frame_entry(b, t1, p.l1) == frame_entry(a, t1, p.l1));
                    }
                } else {
                    if t2 == t && p.l2 == e && p.l1 == 0 && a.record(t).level == 2 {
                        assert(reaches(a, r, p, t, e));
                    } else {
                        assert(!reaches(a, r, p, t, e));
                        if t2 == t && p.l2 == e {
                            if p.l1 == 0 {
                                assert(a.record(t).level != 2);
                                assert(large_entry(b, t, e) is None);
                            }
                        } else {
                            assert(large_entry(b, t2, p.l2) == large_entry(a, t2, p.l2));
                        }
                    }
                }
            }
        }
    }
}

/// Writing frame mapping e of table t moves no table walk: a step reads only entries that name a child,
/// which the entry does in neither tree.
pub proof fn lemma_walk_table_entry_written(a: TableTree, b: TableTree, t: usize, e: usize)
    requires
        entry_written(a, b, t, e),
    ensures
        forall|r: usize, q: SpacePath| #[trigger] walk_table(b, r, q) == walk_table(a, r, q),
{
    assert forall|u: usize| #[trigger] b.is_table(u) == a.is_table(u) && b.is_page(u) == a.is_page(u) && b.is_root(u) == a.is_root(u) by {
        assert(b.maps.contains_key(u) == a.maps.contains_key(u));
    }
    assert forall|u: usize| #[trigger] b.record(u).level == a.record(u).level by {
        if u != t {
            assert(b.record(u) == a.record(u));
        }
    }
    assert(!a.names_child(t, e));
    assert(!b.names_child(t, e));
    assert forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i) by {
        assert(b.child_slot(u, i) == a.child_slot(u, i));
        if a.child_slot(u, i) && !(u == t && i == e) {
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert forall|r: usize, q: SpacePath| #[trigger] walk_table(b, r, q) == walk_table(a, r, q) by {
        assert(b.is_root(r) == a.is_root(r));
        assert(step(b, r, q.l4) == step(a, r, q.l4));
        if let Some(t3) = step(a, r, q.l4) {
            assert(step(b, t3, q.l3) == step(a, t3, q.l3));
            if let Some(t2) = step(a, t3, q.l3) {
                assert(step(b, t2, q.l2) == step(a, t2, q.l2));
            }
        }
    }
}

/// Clearing frame mapping e of table t moves no step and no table walk: a step reads only entries that
/// name a child, which the entry does in neither tree.
pub proof fn lemma_walk_table_entry_cleared(a: TableTree, b: TableTree, t: usize, e: usize)
    requires
        b.maps.dom() == a.maps.dom(),
        b.roots == a.roots,
        b.records == a.records,
        b.space_records == a.space_records,
        frame_slot(a, t, e),
        !b.entry(t, e).perm.present,
        forall|u: usize, i: usize| #![trigger b.entry(u, i)] i < ENTRIES && !(u == t && i == e) ==> b.entry(u, i) == a.entry(u, i),
    ensures
        forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i),
        forall|r: usize, q: SpacePath| #[trigger] walk_table(b, r, q) == walk_table(a, r, q),
{
    assert(!a.names_child(t, e));
    assert(!b.names_child(t, e));
    assert forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i) by {
        assert(b.child_slot(u, i) == a.child_slot(u, i));
        if a.child_slot(u, i) && !(u == t && i == e) {
            assert(b.entry(u, i) == a.entry(u, i));
        }
    }
    assert forall|r: usize, q: SpacePath| #[trigger] walk_table(b, r, q) == walk_table(a, r, q) by {
        assert(step(b, r, q.l4) == step(a, r, q.l4));
        if let Some(t3) = step(a, r, q.l4) {
            assert(step(b, t3, q.l3) == step(a, t3, q.l3));
            if let Some(t2) = step(a, t3, q.l3) {
                assert(step(b, t2, q.l2) == step(a, t2, q.l2));
            }
        }
    }
}

/// Node x of the list is live.
pub open spec fn node_live(list: Tree, x: usize) -> bool {
    x < NODE_SPACE && list.nodes@[x as int].live
}

/// What b keeps of a's links while the list's table nodes are as list says: every root is one still, and
/// every entry that named a child table whose node is live names it still. A revoke step cuts only the
/// table whose node it takes, and clears only frame entries otherwise.
pub open spec fn links_kept(a: TableTree, b: TableTree, list: Tree) -> bool {
    &&& forall|s: usize| #[trigger] b.is_root(s) == a.is_root(s)
    &&& forall|u: usize, i: usize| #[trigger] step(a, u, i) is Some && node_live(list, step(a, u, i)->0)
        ==> step(b, u, i) == step(a, u, i)
}

/// Each table the walk of path p from root s passes through, levels 3 to 1, has its node live in list.
pub open spec fn walk_tables_live(a: TableTree, list: Tree, s: usize, p: SpacePath) -> bool {
    match step(a, s, p.l4) {
        None => false,
        Some(t3) => node_live(list, t3) && match step(a, t3, p.l3) {
            None => false,
            Some(t2) => node_live(list, t2) && match step(a, t2, p.l2) {
                None => false,
                Some(t1) => node_live(list, t1),
            },
        },
    }
}

/// A tree keeps its own links.
pub proof fn lemma_links_kept_same(a: TableTree, list: Tree)
    ensures
        links_kept(a, a, list),
{
}

/// A tree keeps the links of one whose steps are all its own.
pub proof fn lemma_links_kept_steps(a: TableTree, b: TableTree, list: Tree)
    requires
        forall|s: usize| #[trigger] b.is_root(s) == a.is_root(s),
        forall|u: usize, i: usize| #[trigger] step(b, u, i) == step(a, u, i),
    ensures
        links_kept(a, b, list),
{
}

/// Kept links compose, when what is live at the end was live in the middle.
pub proof fn lemma_links_kept_compose(a: TableTree, m: TableTree, b: TableTree, l1: Tree, l2: Tree)
    requires
        links_kept(a, m, l1),
        links_kept(m, b, l2),
        forall|x: usize| #[trigger] node_live(l2, x) ==> node_live(l1, x),
    ensures
        links_kept(a, b, l2),
{
    assert forall|u: usize, i: usize| #[trigger] step(a, u, i) is Some && node_live(l2, step(a, u, i)->0)
        implies step(b, u, i) == step(a, u, i) by {
        assert(node_live(l1, step(a, u, i)->0));
        assert(step(m, u, i) == step(a, u, i));
    }
}

/// A detach that cut the child whose node went keeps every other link.
pub proof fn lemma_links_kept_detached(a: TableTree, b: TableTree, parent: usize, entry: usize, child: usize, list: Tree)
    requires
        detached(a, b, parent, entry, child),
        step(a, parent, entry) == Some(child),
        !node_live(list, child),
    ensures
        links_kept(a, b, list),
{
    assert forall|u: usize| #[trigger] b.is_root(u) == a.is_root(u) by {
        assert(b.roots.contains_key(u) == a.roots.contains_key(u));
    }
    assert forall|u: usize| #[trigger] b.is_table(u) == a.is_table(u) by {
        assert(b.maps.contains_key(u) == a.maps.contains_key(u));
        assert(b.roots.contains_key(u) == a.roots.contains_key(u));
    }
    assert forall|u: usize, i: usize| #[trigger] step(a, u, i) is Some && node_live(list, step(a, u, i)->0)
        implies step(b, u, i) == step(a, u, i) by {
        assert(!(u == parent && i == entry));
        if a.is_table(u) && i < ENTRIES {
            assert(b.entry(u, i) == a.entry(u, i));
            assert(b.record(u).level == a.record(u).level);
            if a.is_root(u) {
                assert(b.space_records[u].value().kind == a.space_records[u].value().kind);
            }
        }
    }
}

/// Every walk whose tables' nodes are live in list finds in b the table it found in a.
pub open spec fn walks_kept(a: TableTree, b: TableTree, list: Tree) -> bool {
    forall|s: usize, p: SpacePath| walk_tables_live(a, list, s, p) ==> #[trigger] walk_table(b, s, p) == walk_table(a, s, p)
}

/// Kept links keep every walk through tables whose nodes are live.
pub proof fn lemma_walks_kept(a: TableTree, b: TableTree, list: Tree)
    requires
        links_kept(a, b, list),
    ensures
        walks_kept(a, b, list),
{
    assert forall|s: usize, p: SpacePath| walk_tables_live(a, list, s, p)
        implies #[trigger] walk_table(b, s, p) == walk_table(a, s, p) by {
        lemma_walk_table_kept(a, b, list, s, p);
    }
}

/// A walk whose tables' nodes stay live finds the table it found, where the links are kept.
pub proof fn lemma_walk_table_kept(a: TableTree, b: TableTree, list: Tree, s: usize, p: SpacePath)
    requires
        links_kept(a, b, list),
        walk_tables_live(a, list, s, p),
    ensures
        walk_table(b, s, p) == walk_table(a, s, p),
{
    assert(b.is_root(s) == a.is_root(s));
    let t3 = step(a, s, p.l4)->0;
    let t2 = step(a, t3, p.l3)->0;
    assert(step(b, s, p.l4) == step(a, s, p.l4));
    assert(step(b, t3, p.l3) == step(a, t3, p.l3));
    assert(step(b, t2, p.l2) == step(a, t2, p.l2));
}

/// One path reaches a level 1 table's entry: each table has one parent entry, so a walk that ends at
/// entry p.l1 of the table p reaches from s is p from s.
pub proof fn lemma_ends_at_unique(a: TableTree, s: usize, p: SpacePath, t: usize, r: usize, q: SpacePath)
    requires
        table_links_wf(a),
        a.is_root(s),
        walk_table(a, s, p) == Some(t),
        a.record(t).level == 1,
    ensures
        ends_at(a, r, q, t, p.l1) == (r == s && q == p),
{
    reveal(table_links_wf);
    assert(large_entry(a, t, p.l1) is None);
    let t3 = step(a, s, p.l4)->0;
    let t2 = step(a, t3, p.l3)->0;
    assert(step(a, s, p.l4) == Some(t3));
    assert(step(a, t3, p.l3) == Some(t2));
    assert(step(a, t2, p.l2) == Some(t));
    let _ = a.entry(s, p.l4);
    let _ = a.entry(t3, p.l3);
    let _ = a.entry(t2, p.l2);
    assert(a.record(t).parent == Some(TableParent { table: t2, entry: p.l2 }));
    assert(a.record(t2).parent == Some(TableParent { table: t3, entry: p.l3 }));
    assert(a.record(t3).parent == Some(TableParent { table: s, entry: p.l4 }));
    if ends_at(a, r, q, t, p.l1) {
        let u3 = step(a, r, q.l4)->0;
        let u2 = step(a, u3, q.l3)->0;
        assert(step(a, r, q.l4) == Some(u3));
        assert(step(a, u3, q.l3) == Some(u2));
        assert(step(a, u2, q.l2) == Some(t));
        let _ = a.entry(r, q.l4);
        let _ = a.entry(u3, q.l3);
        let _ = a.entry(u2, q.l2);
        assert(a.record(t).parent == Some(TableParent { table: u2, entry: q.l2 }));
        assert(u2 == t2 && q.l2 == p.l2);
        assert(a.record(t2).parent == Some(TableParent { table: u3, entry: q.l3 }));
        assert(u3 == t3 && q.l3 == p.l3);
        assert(a.record(t3).parent == Some(TableParent { table: r, entry: q.l4 }));
        assert(r == s && q.l4 == p.l4);
        assert(q.l1 == p.l1);
        assert(q == p);
    }
    if r == s && q == p {
        assert(ends_at(a, r, q, t, p.l1));
    }
}

/// Writing the frame entry at path p of space s maps exactly that path, and no other space changes.
pub proof fn lemma_mapping_written(a: TableTree, b: TableTree, s: usize, p: SpacePath, t: usize)
    requires
        table_links_wf(a),
        entry_written(a, b, t, p.l1),
        a.is_root(s),
        walk_table(a, s, p) == Some(t),
        a.record(t).level == 1,
    ensures
        walk(a, s, p) is None,
        space_mapping(b, s) == space_mapping(a, s).insert(p, b.entry(t, p.l1)),
        forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r),
{
    let e = p.l1;
    let v = b.entry(t, e);
    assert(large_entry(a, t, e) is None);
    assert forall|r: usize, q: SpacePath| #[trigger] walk(b, r, q) == (if r == s && q == p { Some(v) } else { walk(a, r, q) }) by {
        lemma_walk_entry_written(a, b, t, e, r, q);
        lemma_ends_at_unique(a, s, p, t, r, q);
        assert(reaches(a, r, q, t, e) == ends_at(a, r, q, t, e));
    }
    assert(frame_entry(a, t, e) is None);
    assert(walk(a, s, p) is None);
    lemma_space_mapping_written(a, b, s, p, v);
}

/// One path reaches a level 2 table's large entry: each table has one parent entry, so a walk that
/// reaches entry p.l2 of the table p reaches from s, at its first page, is p from s.
pub proof fn lemma_reaches_large_unique(a: TableTree, s: usize, p: SpacePath, t: usize, r: usize, q: SpacePath)
    requires
        table_links_wf(a),
        a.is_root(s),
        walk_large_table(a, s, p) == Some(t),
        a.record(t).level == 2,
        p.l1 == 0,
    ensures
        reaches(a, r, q, t, p.l2) == (r == s && q == p),
{
    reveal(table_links_wf);
    let t3 = step(a, s, p.l4)->0;
    assert(step(a, s, p.l4) == Some(t3));
    assert(step(a, t3, p.l3) == Some(t));
    let _ = a.entry(s, p.l4);
    let _ = a.entry(t3, p.l3);
    assert(a.record(t).parent == Some(TableParent { table: t3, entry: p.l3 }));
    assert(a.record(t3).parent == Some(TableParent { table: s, entry: p.l4 }));
    if reaches(a, r, q, t, p.l2) {
        let u3 = step(a, r, q.l4)->0;
        assert(step(a, r, q.l4) == Some(u3));
        assert(step(a, u3, q.l3) == Some(t));
        let _ = a.entry(r, q.l4);
        let _ = a.entry(u3, q.l3);
        assert(a.record(t).parent == Some(TableParent { table: u3, entry: q.l3 }));
        assert(u3 == t3 && q.l3 == p.l3);
        assert(a.record(t3).parent == Some(TableParent { table: r, entry: q.l4 }));
        assert(r == s && q.l4 == p.l4);
        assert(q.l2 == p.l2);
        assert(q.l1 == p.l1);
        assert(q == p);
    }
    if r == s && q == p {
        assert(reaches(a, r, q, t, p.l2));
    }
}

/// Writing the large entry at path p of space s maps exactly that path, and no other space changes.
pub proof fn lemma_large_mapping_written(a: TableTree, b: TableTree, s: usize, p: SpacePath, t: usize)
    requires
        table_links_wf(a),
        entry_written(a, b, t, p.l2),
        a.is_root(s),
        walk_large_table(a, s, p) == Some(t),
        a.record(t).level == 2,
        p.l1 == 0,
    ensures
        walk(a, s, p) is None,
        space_mapping(b, s) == space_mapping(a, s).insert(p, b.entry(t, p.l2)),
        forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r),
{
    let e = p.l2;
    let v = b.entry(t, e);
    assert forall|r: usize, q: SpacePath| #[trigger] walk(b, r, q) == (if r == s && q == p { Some(v) } else { walk(a, r, q) }) by {
        lemma_walk_entry_written(a, b, t, e, r, q);
        lemma_reaches_large_unique(a, s, p, t, r, q);
    }
    assert(!a.names_child(t, e));
    assert(step(a, t, e) is None);
    assert(large_entry(a, t, e) is None);
    assert(walk(a, s, p) is None);
    lemma_space_mapping_written(a, b, s, p, v);
}

/// When every walk is as it was but one, now v and finding nothing before, that space's mapping gains
/// that path and every other space's is as it was.
pub proof fn lemma_space_mapping_written(a: TableTree, b: TableTree, s: usize, p: SpacePath, v: PageEntry)
    requires
        forall|r: usize, q: SpacePath| #[trigger] walk(b, r, q) == (if r == s && q == p { Some(v) } else { walk(a, r, q) }),
        walk(a, s, p) is None,
    ensures
        space_mapping(b, s) == space_mapping(a, s).insert(p, v),
        forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r),
{
    assert forall|r: usize| r != s implies #[trigger] space_mapping(b, r) == space_mapping(a, r) by {
        assert forall|q: SpacePath| #[trigger] walk(b, r, q) == walk(a, r, q) by {}
        assert(space_mapping(b, r) =~= space_mapping(a, r));
    }
    let mb = space_mapping(b, s);
    let ma = space_mapping(a, s).insert(p, v);
    assert forall|q: SpacePath| #[trigger] mb.dom().contains(q) == ma.dom().contains(q) by {}
    assert forall|q: SpacePath| #[trigger] mb.dom().contains(q) implies mb[q] == ma[q] by {}
    assert(mb =~= ma);
}

/// The holders after mapping node n, not live before, joins block br with one more reference, no
/// capability changing.
pub proof fn lemma_holders_mapping_added(
    list_a: &Tree,
    tables: &Tables,
    list_b: &Tree,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    n: usize,
    br: BlockRef,
)
    requires
        holders_wf(list_a, tables, blocks_a, zeroing, holders),
        n < NODE_SPACE,
        !list_a.nodes@[n as int].live,
        list_b.nodes@[n as int].live,
        list_b.nodes@[n as int].kind is Mapping,
        forall|x: int| #![trigger list_b.nodes@[x]] 0 <= x < NODE_SPACE && x != n ==> {
            &&& list_b.nodes@[x].live == list_a.nodes@[x].live
            &&& list_b.nodes@[x].kind == list_a.nodes@[x].kind
        },
        forall|x: usize| #[trigger] tables.is_cap(list_b, x) == tables.is_cap(list_a, x),
        holders.contains_key(br),
        block_refs(blocks_a, br) < usize::MAX,
        blocks_refs_changed(blocks_a, blocks_b, br, (block_refs(blocks_a, br) + 1) as usize, block_dead(blocks_a, br)),
    ensures
        holders_wf(list_b, tables, blocks_b, zeroing, holders.insert(br, holders[br].insert(n))),
{
    let hb = holders.insert(br, holders[br].insert(n));
    assert(!tables.is_cap(list_a, n));
    assert(!holders[br].contains(n));
    vstd::set::lemma_set_insert_len(holders[br], n);
    assert forall|x: usize| #[trigger] tables.is_cap(list_b, x) && tables.payload_of(x).kind is Frame implies {
        let i = tables.payload_of(x).base / PAGE_SZ;
        &&& blocks_b.tracks(i as int)
        &&& frame_in_block(block_ref(blocks_b, i), tables.payload_of(x))
        &&& hb.contains_key(block_ref(blocks_b, i))
        &&& hb[block_ref(blocks_b, i)].contains(x)
    } by {
        let i = tables.payload_of(x).base / PAGE_SZ;
        assert(tables.is_cap(list_a, x));
        assert(block_ref(blocks_b, i) == block_ref(blocks_a, i));
    }
    assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
        &&& hb[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
        &&& !block_active(zeroing, k)
    } by {
        assert(holders.contains_key(k));
    }
    assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies ({
        &&& tables.is_cap(list_b, x)
        &&& tables.payload_of(x).kind is Frame
        &&& blocks_b.tracks_addr(tables.payload_of(x).base)
        &&& block_ref(blocks_b, tables.payload_of(x).base / PAGE_SZ) == k
    } || (x < NODE_SPACE && list_b.nodes@[x as int].live && list_b.nodes@[x as int].kind is Mapping)) by {
        assert(holders.contains_key(k));
        if k != br || x != n {
            assert(holders[k].contains(x));
            if tables.is_cap(list_a, x) && tables.payload_of(x).kind is Frame {
                assert(tables.is_cap(list_b, x));
            } else {
                assert(x < NODE_SPACE && list_a.nodes@[x as int].live && list_a.nodes@[x as int].kind is Mapping);
                assert(x != n);
            }
        }
    }
    assert forall|r: int| 0 <= r < NUM_2M && #[trigger] zeroing.active_2m@[r] implies {
        &&& blocks_b.regions_2m@[r].typed
        &&& blocks_b.regions_2m@[r].refs == 1
    } by {
        assert(block_typed(blocks_a, BlockRef::Two(r as usize)));
        assert(BlockRef::Two(r as usize) != br);
        assert(block_refs(blocks_b, BlockRef::Two(r as usize)) == block_refs(blocks_a, BlockRef::Two(r as usize)));
    }
    assert forall|r: int| 0 <= r < NUM_1G && #[trigger] zeroing.active_1g@[r] implies {
        &&& blocks_b.regions_1g@[r].typed
        &&& blocks_b.regions_1g@[r].refs == 1
    } by {
        assert(block_typed(blocks_a, BlockRef::One(r as usize)));
        assert(BlockRef::One(r as usize) != br);
        assert(block_refs(blocks_b, BlockRef::One(r as usize)) == block_refs(blocks_a, BlockRef::One(r as usize)));
    }
}

/// Whether two kinds of space are the same kind.
pub fn same_kind(a: SpaceKind, b: SpaceKind) -> (ret: bool)
    ensures
        ret == (a == b),
{
    match (a, b) {
        (SpaceKind::Process, SpaceKind::Process) | (SpaceKind::Device, SpaceKind::Device) | (SpaceKind::Nested, SpaceKind::Nested) => true,
        _ => false,
    }
}

impl CapKernel {
    /// The refusals: an index that names no capability to a space of this kind, or none that may change
    /// it, or a process capability naming a dead process, whose space waits for retype's teardown (see
    /// design/teardown-driven-by-retype/); a path that reaches no live table, or an entry of it that is
    /// taken; an index that names no frame capability, or none that may be read; an offset beyond its
    /// range; a capability at the deepest depth, or a block at the reference limit.
    pub open spec fn can_map(&self, root: usize, slot: usize, kind: SpaceKind, p: SpacePath, from: usize, page: usize) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let n = self.tables.node_of(root, slot);
        let f = self.tables.node_of(root, from);
        let t = walk_table(tree, self.payload_of(n).base, p)->0;
        &&& self.tables.has_slot(&self.list, root, slot)
        &&& self.is_cap(n)
        &&& writes_space(self.payload_of(n))
        &&& !self.cap_dead(n)
        &&& self.spaces.records@[self.payload_of(n).base].value().kind == kind
        &&& walk_table(tree, self.payload_of(n).base, p) is Some
        &&& !self.blocks.pages@[(t / PAGE_SZ) as int].dead
        &&& p.l1 < ENTRIES
        &&& tree.entry(t, p.l1).is_empty()
        &&& self.tables.has_slot(&self.list, root, from)
        &&& self.is_cap(f)
        &&& self.payload_of(f).kind is Frame
        &&& self.payload_of(f).rights & right_bit(Right::Read) != 0
        &&& (page as int) * PAGE_SZ < block_bytes(self.payload_of(f).order)
        &&& self.list.nodes@[f as int].depth < MAX_DEPTH
        &&& block_refs(&self.blocks, block_ref(&self.blocks, frame_of(self.payload_of(f), page))) != usize::MAX
    }

    /// The refusals of a large map: as can_map's, for entry p.l2 of the level 2 table the path reaches,
    /// with a capability of a 2M or 1G frame and a 2M-aligned offset whose 512 pages are in its range.
    /// The entry must be empty, so a child table refuses it.
    pub open spec fn can_map_large(&self, root: usize, slot: usize, kind: SpaceKind, p: SpacePath, from: usize, page: usize) -> bool {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let n = self.tables.node_of(root, slot);
        let f = self.tables.node_of(root, from);
        let t = walk_large_table(tree, self.payload_of(n).base, p)->0;
        &&& self.tables.has_slot(&self.list, root, slot)
        &&& self.is_cap(n)
        &&& writes_space(self.payload_of(n))
        &&& !self.cap_dead(n)
        &&& self.spaces.records@[self.payload_of(n).base].value().kind == kind
        &&& walk_large_table(tree, self.payload_of(n).base, p) is Some
        &&& !self.blocks.pages@[(t / PAGE_SZ) as int].dead
        &&& p.l2 < ENTRIES
        &&& p.l1 == 0
        &&& tree.entry(t, p.l2).is_empty()
        &&& self.tables.has_slot(&self.list, root, from)
        &&& self.is_cap(f)
        &&& self.payload_of(f).kind is Frame
        &&& self.payload_of(f).rights & right_bit(Right::Read) != 0
        &&& self.payload_of(f).order == 9 || self.payload_of(f).order == 18
        &&& page % PAGES_PER_2M == 0
        &&& (page as int) * PAGE_SZ + PAGES_PER_2M * PAGE_SZ <= block_bytes(self.payload_of(f).order)
        &&& self.list.nodes@[f as int].depth < MAX_DEPTH
        &&& block_refs(&self.blocks, block_ref(&self.blocks, frame_of(self.payload_of(f), page))) != usize::MAX
    }

    /// What map_frame starts from: a live table page of the map's level with entry e empty, a frame
    /// capability whose block holds the pages, and the entry's node free.
    pub open spec fn map_from(pre: Self, t: usize, e: usize, f: usize, frame: usize, large: bool) -> bool {
        let tree = tree_of(&pre.table_pages, &pre.spaces);
        let cap = pre.payload_of(f);
        &&& pre.table_pages.maps@.contains_key(t)
        &&& tree.record(t).level == map_level(large)
        &&& !pre.blocks.pages@[(t / PAGE_SZ) as int].dead
        &&& e < ENTRIES
        &&& tree.entry(t, e).is_empty()
        &&& !pre.list.nodes@[mapping_node(t, e) as int].live
        &&& pre.is_cap(f)
        &&& cap.kind is Frame
        &&& pre.list.nodes@[f as int].depth < MAX_DEPTH
        &&& pre.blocks.tracks(frame as int)
        &&& cap.base <= frame * PAGE_SZ
        &&& frame * PAGE_SZ + entry_pages(map_level(large)) * PAGE_SZ <= cap.base as int + block_bytes(cap.order)
        &&& large ==> frame % PAGES_PER_2M == 0
        &&& block_ref(&pre.blocks, frame) == block_ref(&pre.blocks, cap.base / PAGE_SZ)
    }

    /// What the writes of a map leave, apart from the mapped set: the node derived under f, the
    /// entry and t's written flag set, the block's count and holders up by the node, and its record.
    pub open spec fn map_written(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool) -> bool {
        let node = mapping_node(t, e);
        let br = block_ref(&pre.blocks, frame);
        let rights = pre.payload_of(f).rights;
        &&& post.list.wf()
        &&& post.list.is_child(f, node)
        &&& post.list.parent@ == pre.list.parent@.insert(node, f)
        &&& post.list.pages@.dom() == pre.list.pages@.dom()
        &&& post.list.nodes@[node as int].live
        &&& post.list.nodes@[node as int].kind is Mapping
        &&& post.list.seq@[0] == pre.list.seq@[0]
        &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
            &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
            &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            &&& post.list.nodes@[i].depth == pre.list.nodes@[i].depth
        }
        &&& post.tables == pre.tables
        &&& post.blocks.wf()
        &&& block_refs(&pre.blocks, br) != usize::MAX
        &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
        &&& Self::entry_set(pre.table_pages, post.table_pages, t, e, frame_map_entry(frame, rights, large))
        &&& post.spaces == pre.spaces
        &&& post.holders@ == pre.holders@.insert(br, pre.holders@[br].insert(node))
        &&& post.mappings@ == pre.mappings@.insert(node, MappingRecord { table: t, entry: e, frame, large })
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.processes == pre.processes
    }

    /// The table entry i of table t leads to, in constant time. Above level 1 an entry either is a
    /// kernel slot, is not present, maps a large frame, or names a table page.
    pub fn table_step(&self, t: usize, is_root: bool, i: usize) -> (ret: Option<usize>)
        requires
            self.wf(),
            is_root ==> self.spaces.roots@.contains_key(t),
            !is_root ==> self.table_pages.maps@.contains_key(t),
            is_root ==> !self.table_pages.maps@.contains_key(t),
            tree_of(&self.table_pages, &self.spaces).record(t).level >= 2,
        ensures
            ret == step(tree_of(&self.table_pages, &self.spaces), t, i),
            ret is Some ==> {
                let tree = tree_of(&self.table_pages, &self.spaces);
                &&& tree.is_page(ret->0)
                &&& tree.record(ret->0).level + 1 == tree.record(t).level
            },
    {
        reveal(table_links_wf);
        if i >= ENTRIES || self.is_kernel_slot(t, is_root, i) {
            return None;
        }
        let e = self.table_entry(t, is_root, i);
        if !e.perm.present || e.perm.ps {
            return None;
        }
        Some(e.addr - TABLE_NODE_PAGES * PAGE_SZ)
    }

    /// Maps the page at offset `page` of the frame capability at index `from` into entry `l1` of the
    /// level 1 table the path reaches in the space named at index `slot`. All of the indices and the
    /// offset come from user space, so any of them can be refused, and a refusal changes nothing.
    pub(crate) fn map(&mut self, root: usize, slot: usize, l4: usize, l3: usize, l2: usize, l1: usize, from: usize, page: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            final(self).wf(),
            final(self).cores == old(self).cores,
            ret == old(self).can_map(root, slot, SpaceKind::Process, SpacePath { l4, l3, l2, l1 }, from, page),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret ==> Self::map_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1 }, from, page),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        self.map_kind(root, slot, SpaceKind::Process, l4, l3, l2, l1, from, page)
    }

    /// The entry of a table that the address va and the level name in the space whose root is s, and that
    /// a link writes: refused unless the level is 2, 3 or 4 and va names an entry there, then the root's
    /// entry at level 4, and below it the entry of the table the walk from the root reaches at the level.
    /// See design/syscall-abi-in-registers/.
    pub open spec fn link_parent(&self, s: usize, va: u64, level: u64) -> Option<TableParent> {
        let tree = tree_of(&self.table_pages, &self.spaces);
        let p = address_path(va);
        if level < 2 || !names_entry(va, level) {
            None
        } else if level == 4 {
            Some(TableParent { table: s, entry: p.l4 })
        } else {
            match step(tree, s, p.l4) {
                None => None,
                Some(t3) => if level == 3 {
                    Some(TableParent { table: t3, entry: p.l3 })
                } else {
                    match step(tree, t3, p.l3) {
                        None => None,
                        Some(t2) => Some(TableParent { table: t2, entry: p.l2 }),
                    }
                },
            }
        }
    }

    /// The refusals of a link of the table page at child, under the untyped at index from, into the
    /// entry the address va and the level name in the space of the capability at index slot of the
    /// table at root: an entry link_parent finds no table for, or can_link's at the table it finds.
    pub open spec fn can_link_at(&self, root: usize, slot: usize, va: u64, level: u64, from: usize, child: usize) -> bool {
        let s = self.payload_of(self.tables.node_of(root, slot)).base;
        match self.link_parent(s, va, level) {
            None => false,
            Some(place) => self.can_link(root, slot, place.table, place.entry, from, child),
        }
    }

    /// What a link of the table page at child, under the untyped at index from, into the entry the
    /// address va and the level name in the space of the capability at index slot of the table at root
    /// did: the entry is one the address names, the link was allowed there, and the tables are linked.
    pub open spec fn table_linked(pre: Self, post: Self, root: usize, slot: usize, va: u64, level: u64, from: usize, child: usize) -> bool {
        let s = pre.payload_of(pre.tables.node_of(root, slot)).base;
        match pre.link_parent(s, va, level) {
            None => false,
            Some(place) => {
                &&& pre.can_link(root, slot, place.table, place.entry, from, child)
                &&& Self::link_done(pre, post, place.table, place.entry, child, s)
                &&& discharges(pre.view(), post.view(), root, Effect::Local)
            },
        }
    }

    /// Links the unlinked table page at `child` into the entry the address `va` and the level `level`
    /// name in the space of the capability at index `slot` of the table at `root`, on the authority of the
    /// untyped at index `from` over the page's block. All of these come from user space, and a refusal
    /// changes nothing. The walk from the space's root finds the parent table, as map's does, so no
    /// physical address from user space is taken as a table.
    pub fn link_at(&mut self, root: usize, slot: usize, va: u64, level: u64, from: usize, child: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            ret == old(self).can_link_at(root, slot, va, level, from, child),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::table_linked(*old(self), *final(self), root, slot, va, level, from, child),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        if level < 2 || !entry_named(va, level) {
            return false;
        }
        let (l4, l3, l2, _) = address_indices(va);
        let (n, space) = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found,
            None => {
                proof {
                    assert(!pre.tables.has_slot(&pre.list, root, slot));
                }
                return false;
            },
        };
        proof {
            pre.lemma_slot(root, slot);
            assert(space == pre.payload_of(n));
            assert(right_bit(Right::Write) == 2);
        }
        let node = self.list.get(n);
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !node.live || !kind_ok || !may_write_space(&space) {
            proof {
                assert(!pre.is_cap(n) || !writes_space(pre.payload_of(n)));
            }
            return false;
        }
        proof {
            assert(pre.is_cap(n));
            pre.lemma_written_space(n);
            pre.lemma_root_table(space.base);
        }
        let s = space.base;
        let (parent, entry) = if level == 4 {
            (s, l4)
        } else {
            let t3 = match self.table_step(s, true, l4) {
                Some(t) => t,
                None => {
                    proof {
                        assert(pre.link_parent(s, va, level) is None);
                    }
                    return false;
                },
            };
            if level == 3 {
                (t3, l3)
            } else {
                let t2 = match self.table_step(t3, false, l3) {
                    Some(t) => t,
                    None => {
                        proof {
                            assert(pre.link_parent(s, va, level) is None);
                        }
                        return false;
                    },
                };
                (t2, l2)
            }
        };
        proof {
            assert(pre.link_parent(s, va, level) == Some(TableParent { table: parent, entry }));
        }
        self.link(root, slot, parent, entry, from, child)
    }

    /// The refusals of a map of the page at offset page of the frame capability at index from, into the
    /// entry the address va and the level name in the space of the capability at index slot of the
    /// table at root: an address that names no entry at the level, a level other than 1 or 2, or
    /// can_map's at level 1 and can_map_large's at level 2, at the path the address names.
    pub open spec fn can_map_at(&self, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize) -> bool {
        let p = address_path(va);
        &&& names_entry(va, level)
        &&& {
            ||| level == 1 && self.can_map(root, slot, SpaceKind::Process, p, from, page)
            ||| level == 2 && self.can_map_large(root, slot, SpaceKind::Process, p, from, page)
        }
    }

    /// What a map of the page at offset page of the frame capability at index from, into the entry the
    /// address va and the level name in the space of the capability at index slot of the table at root,
    /// did: va names an entry at the level, and at level 1 the map was allowed at the path the address
    /// names and map_done holds there, at level 2 the same for a large map.
    pub open spec fn page_mapped(pre: Self, post: Self, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize) -> bool {
        let p = address_path(va);
        &&& names_entry(va, level)
        &&& {
            ||| {
                &&& level == 1
                &&& pre.can_map(root, slot, SpaceKind::Process, p, from, page)
                &&& Self::map_done(pre, post, root, slot, p, from, page)
            }
            ||| {
                &&& level == 2
                &&& pre.can_map_large(root, slot, SpaceKind::Process, p, from, page)
                &&& Self::map_large_done(pre, post, root, slot, p, from, page)
            }
        }
        &&& discharges(pre.view(), post.view(), root, Effect::Local)
    }

    /// Maps the page at offset `page` of the frame capability at index `from` into the entry the address
    /// `va` and the level `level` name in the space of the capability at index `slot` of the table at
    /// `root`: a 4K page at level 1, a 2M page at level 2. All of these come from user space, and a
    /// refusal changes nothing. See design/syscall-abi-in-registers/.
    pub fn map_at(&mut self, root: usize, slot: usize, va: u64, level: u64, from: usize, page: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            final(self).flush_epoch == old(self).flush_epoch,
            ret == old(self).can_map_at(root, slot, va, level, from, page),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::page_mapped(*old(self), *final(self), root, slot, va, level, from, page),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        if (level != 1 && level != 2) || !entry_named(va, level) {
            return false;
        }
        let (l4, l3, l2, l1) = address_indices(va);
        if level == 1 {
            self.map(root, slot, l4, l3, l2, l1, from, page)
        } else {
            proof {
                lemma_large_entry_path(va);
            }
            self.map_large(root, slot, l4, l3, l2, from, page)
        }
    }

    /// map, in a space that must be of this kind.
    pub(crate) fn map_kind(&mut self, root: usize, slot: usize, kind: SpaceKind, l4: usize, l3: usize, l2: usize, l1: usize, from: usize, page: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            final(self).wf(),
            final(self).cores == old(self).cores,
            ret == old(self).can_map(root, slot, kind, SpacePath { l4, l3, l2, l1 }, from, page),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret ==> Self::map_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1 }, from, page),
            kind is Process ==> discharges(old(self).view(), final(self).view(), root, Effect::Local),
            ret && !(kind is Process) ==> discharges(
                old(self).view(),
                final(self).view(),
                root,
                Effect::Share { space: old(self).tables.node_of(root, slot), from: old(self).tables.node_of(root, from) },
            ),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        let ghost p = SpacePath { l4, l3, l2, l1 };
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (n, space) = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found,
            None => { return false; },
        };
        proof {
            pre.lemma_slot(root, slot);
            assert(space == pre.payload_of(n));
            assert(right_bit(Right::Write) == 2);
            assert(right_bit(Right::Read) == 1);
            assert(right_bit(Right::Execute) == 4);
        }
        let n_node = self.list.get(n);
        let n_kind = match n_node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !n_node.live || !n_kind || !may_write_space(&space) {
            return false;
        }
        proof {
            assert(pre.is_cap(n));
            pre.lemma_written_space(n);
            pre.lemma_root_table(space.base);
        }
        if self.is_cap_dead(n, space) {
            return false;
        }
        let s = space.base;
        if !same_kind(self.space_kind(s), kind) {
            return false;
        }
        let t3 = match self.table_step(s, true, l4) {
            Some(t) => t,
            None => { return false; },
        };
        let t2 = match self.table_step(t3, false, l3) {
            Some(t) => t,
            None => { return false; },
        };
        let t = match self.table_step(t2, false, l2) {
            Some(t) => t,
            None => { return false; },
        };
        proof {
            assert(walk_table(tree, s, p) == Some(t));
            assert(tree.record(t).level == 1);
            pre.lemma_table_page_room(t);
        }
        if l1 >= ENTRIES || self.blocks.pages.get(t / PAGE_SZ).dead {
            return false;
        }
        let current = self.table_entry(t, false, l1);
        if !entry_is_empty(&current) {
            return false;
        }
        let (f, cap) = match self.tables.lookup(&self.list, root, from) {
            Some(found) => found,
            None => { return false; },
        };
        proof {
            pre.lemma_slot(root, from);
            assert(cap == pre.payload_of(f));
        }
        let f_node = self.list.get(f);
        let f_kind = match f_node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        let is_frame = match cap.kind {
            CapKind::Frame => true,
            _ => false,
        };
        if !f_node.live || !f_kind || !is_frame || cap.rights & 1 == 0 {
            return false;
        }
        proof {
            assert(pre.is_cap(f));
            assert(pre.tables.is_cap(&pre.list, f));
            assert(payload_wf(cap));
        }
        let size = order_bytes(cap.order);
        proof {
            lemma_page_within(page, size, cap.order);
        }
        if page >= size / PAGE_SZ {
            return false;
        }
        if f_node.depth >= MAX_DEPTH {
            return false;
        }
        proof {
            pre.lemma_frame_page(f, page);
            pre.lemma_map_node_free(t, l1);
        }
        let frame = cap.base / PAGE_SZ + page;
        proof {
            assert(frame == frame_of(cap, page));
            assert(Self::map_from(pre, t, l1, f, frame, false));
        }
        let ret = self.map_frame(Ghost(root), t, l1, f, cap.rights, frame, false);
        proof {
            if ret {
                Self::lemma_map_done(pre, *self, root, slot, kind, p, from, page, t, f, frame);
            }
        }
        ret
    }

    /// Maps the 2M page at offset `page` of the frame capability at index `from` into entry `l2` of the
    /// level 2 table the path reaches in the space named at index `slot`. All of the indices and the
    /// offset come from user space, so any of them can be refused, and a refusal changes nothing.
    pub(crate) fn map_large(&mut self, root: usize, slot: usize, l4: usize, l3: usize, l2: usize, from: usize, page: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            ret == old(self).can_map_large(root, slot, SpaceKind::Process, SpacePath { l4, l3, l2, l1: 0 }, from, page),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret ==> Self::map_large_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1: 0 }, from, page),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        self.map_large_kind(root, slot, SpaceKind::Process, l4, l3, l2, from, page)
    }

    /// map_large, in a space that must be of this kind.
    pub(crate) fn map_large_kind(&mut self, root: usize, slot: usize, kind: SpaceKind, l4: usize, l3: usize, l2: usize, from: usize, page: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus.present == old(self).iommus.present,
            ret == old(self).can_map_large(root, slot, kind, SpacePath { l4, l3, l2, l1: 0 }, from, page),
            final(self).spaces.loaded == old(self).spaces.loaded,
            !ret ==> *final(self) == *old(self),
            ret ==> Self::map_large_done(*old(self), *final(self), root, slot, SpacePath { l4, l3, l2, l1: 0 }, from, page),
            kind is Process ==> discharges(old(self).view(), final(self).view(), root, Effect::Local),
            ret && !(kind is Process) ==> discharges(
                old(self).view(),
                final(self).view(),
                root,
                Effect::Share { space: old(self).tables.node_of(root, slot), from: old(self).tables.node_of(root, from) },
            ),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let ghost tree = tree_of(&pre.table_pages, &pre.spaces);
        let ghost p = SpacePath { l4, l3, l2, l1: 0 };
        proof {
            pre.lemma_no_op_discharges(root);
        }
        let (n, space) = match self.tables.lookup(&self.list, root, slot) {
            Some(found) => found,
            None => { return false; },
        };
        proof {
            pre.lemma_slot(root, slot);
            assert(space == pre.payload_of(n));
            assert(right_bit(Right::Write) == 2);
            assert(right_bit(Right::Read) == 1);
            assert(right_bit(Right::Execute) == 4);
        }
        let n_node = self.list.get(n);
        let n_kind = match n_node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !n_node.live || !n_kind || !may_write_space(&space) {
            return false;
        }
        proof {
            assert(pre.is_cap(n));
            pre.lemma_written_space(n);
            pre.lemma_root_table(space.base);
        }
        if self.is_cap_dead(n, space) {
            return false;
        }
        let s = space.base;
        if !same_kind(self.space_kind(s), kind) {
            return false;
        }
        let t3 = match self.table_step(s, true, l4) {
            Some(t) => t,
            None => { return false; },
        };
        let t = match self.table_step(t3, false, l3) {
            Some(t) => t,
            None => { return false; },
        };
        proof {
            assert(walk_large_table(tree, s, p) == Some(t));
            assert(tree.record(t).level == 2);
            pre.lemma_table_page_room(t);
        }
        if l2 >= ENTRIES || self.blocks.pages.get(t / PAGE_SZ).dead {
            return false;
        }
        let current = self.table_entry(t, false, l2);
        if !entry_is_empty(&current) {
            return false;
        }
        let (f, cap) = match self.tables.lookup(&self.list, root, from) {
            Some(found) => found,
            None => { return false; },
        };
        proof {
            pre.lemma_slot(root, from);
            assert(cap == pre.payload_of(f));
        }
        let f_node = self.list.get(f);
        let f_kind = match f_node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        let is_frame = match cap.kind {
            CapKind::Frame => true,
            _ => false,
        };
        if !f_node.live || !f_kind || !is_frame || cap.rights & 1 == 0 {
            return false;
        }
        if cap.order != 9 && cap.order != 18 {
            return false;
        }
        proof {
            assert(pre.is_cap(f));
            assert(pre.tables.is_cap(&pre.list, f));
            assert(payload_wf(cap));
        }
        let size = order_bytes(cap.order);
        proof {
            lemma_large_page_within(page, size, cap.order);
        }
        if page % PAGES_PER_2M != 0 || page >= size / PAGE_SZ || size / PAGE_SZ - page < PAGES_PER_2M {
            return false;
        }
        if f_node.depth >= MAX_DEPTH {
            return false;
        }
        proof {
            pre.lemma_large_frame_page(f, page);
            pre.lemma_map_node_free(t, l2);
        }
        let frame = cap.base / PAGE_SZ + page;
        proof {
            assert(frame == frame_of(cap, page));
            assert(Self::map_from(pre, t, l2, f, frame, true));
        }
        let ret = self.map_frame(Ghost(root), t, l2, f, cap.rights, frame, true);
        proof {
            if ret {
                Self::lemma_map_large_done(pre, *self, root, slot, kind, p, from, page, t, f, frame);
            }
        }
        ret
    }

    /// Writes the map the caller has checked: one more reference on the frame's block, the node derived
    /// under f, the entry and t's written flag, and the pages mapped. Refused only when the block
    /// is at the reference limit.
    fn map_frame(&mut self, Ghost(root): Ghost<usize>, t: usize, e: usize, f: usize, rights: u32, frame: usize, large: bool) -> (ret: bool)
        requires
            old(self).wf(),
            Self::map_from(*old(self), t, e, f, frame, large),
            rights == old(self).payload_of(f).rights,
        ensures
            final(self).frames == old(self).frames,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).devices == old(self).devices,
            final(self).iommus.present == old(self).iommus.present,
            final(self).wf(),
            final(self).cores == old(self).cores,
            ret == (block_refs(&old(self).blocks, block_ref(&old(self).blocks, frame)) != usize::MAX),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::map_written(*old(self), *final(self), t, e, f, frame, large),
            ret ==> final(self).mapped@ == old(self).mapped@.union(map_pages(frame, large)),
            final(self).view().shares.subset_of(old(self).view().shares)
                ==> discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let ghost node = mapping_node(t, e);
        proof {
            pre.lemma_no_op_discharges(root);
            assert(pre.tables.is_cap(&pre.list, f));
            lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, f);
        }
        let node = self.map_node(t, e);
        let br = locate(&self.blocks, frame);
        if !add_block_ref(&mut self.blocks, br) {
            return false;
        }
        proof {
            pre.list.lemma_seq_fits();
            pre.lemma_slot_bound(f);
            pre.lemma_table_page_room(t);
            assert(Self::table_page_perms(self.table_pages, t));
        }
        self.list.derive(f, node, NodeKind::Mapping);
        self.write_frame_entry(t, e, frame, rights, large);
        self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].insert(node)));
        self.mappings = Ghost(pre.mappings@.insert(node, MappingRecord { table: t, entry: e, frame, large }));
        self.mapped = Ghost(pre.mapped@.union(map_pages(frame, large)));
        proof {
            assert(Self::map_written(pre, *self, t, e, f, frame, large));
            Self::lemma_map_wf(pre, *self, t, e, f, frame, large);
            if self.view().shares.subset_of(pre.view().shares) {
                Self::lemma_leaf_added_discharges(pre, *self, root, f, node);
            }
        }
        true
    }

    /// The node of entry e of table page t, in constant time.
    pub fn map_node(&self, t: usize, e: usize) -> (ret: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
            e < ENTRIES,
        ensures
            ret == mapping_node(t, e),
            ret < NODE_SPACE,
            self.list.valid(ret),
    {
        proof {
            self.lemma_map_node_place(t, e);
        }
        t + ((e + 1) / NODES_PER_PAGE) * PAGE_SZ + (e + 1) % NODES_PER_PAGE
    }

    /// What writing entry e of table page t does to the table pages: that entry, and t's written flag.
    pub open spec fn entry_set(a: TablePages, b: TablePages, t: usize, e: usize, v: PageEntry) -> bool {
        &&& b.maps@ == a.maps@.insert(t, b.maps@[t])
        &&& b.maps@[t].addr() == a.maps@[t].addr()
        &&& b.maps@[t].is_init()
        &&& b.maps@[t].value().wf()
        &&& b.maps@[t].value().level == a.maps@[t].value().level
        &&& forall|i: usize| #![trigger b.maps@[t].value()[i]] i < ENTRIES && i != e ==> b.maps@[t].value()[i] == a.maps@[t].value()[i]
        &&& b.maps@[t].value()[e] == v
        &&& b.maps@[t].value().status(e as int).is_clear()
        &&& b.records@ == a.records@.insert(t, b.records@[t])
        &&& b.records@[t].addr() == a.records@[t].addr()
        &&& b.records@[t].is_init()
        &&& b.records@[t].value() == (TableRecord {
            level: a.records@[t].value().level,
            space: a.records@[t].value().space,
            parent: a.records@[t].value().parent,
            written: true,
        })
        &&& b.spare == a.spare
    }

    /// The permissions a table page's table and record are written through.
    pub open spec fn table_page_perms(pages: TablePages, t: usize) -> bool {
        &&& t / PAGE_SZ < NUM_PAGES
        &&& pages.maps@.contains_key(t)
        &&& pages.maps@[t].addr() == t + TABLE_NODE_PAGES * PAGE_SZ
        &&& pages.maps@[t].is_init()
        &&& pages.maps@[t].value().wf()
        &&& pages.records@.contains_key(t)
        &&& pages.records@[t].addr() == t + TABLE_RECORD_PAGE * PAGE_SZ
        &&& pages.records@[t].is_init()
        &&& pages.maps@[t].value().level@ == pages.records@[t].value().level
    }

    /// Writes the frame's entry for these rights into entry e of table page t and marks t written.
    fn write_frame_entry(&mut self, t: usize, e: usize, frame: usize, rights: u32, large: bool)
        requires
            Self::table_page_perms(old(self).table_pages, t),
            e < ENTRIES,
            old(self).blocks.tracks(frame as int),
        ensures
            Self::entry_set(old(self).table_pages, final(self).table_pages, t, e, frame_map_entry(frame, rights, large)),
            final(self).list == old(self).list,
            final(self).cores == old(self).cores,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).tlb == old(self).tlb,
            final(self).mapped == old(self).mapped,
            final(self).blocks == old(self).blocks,
            final(self).tables == old(self).tables,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).frames == old(self).frames,
            final(self).devices == old(self).devices,
            final(self).threads == old(self).threads,
            final(self).processes == old(self).processes,
            final(self).spaces == old(self).spaces,
            final(self).mappings == old(self).mappings,
            final(self).zeroing == old(self).zeroing,
            final(self).holders == old(self).holders,
    {
        let ghost pre = *old(self);
        proof {
            lemma_table_bound(t);
            lemma_frame_addr_valid(frame);
            assert(right_bit(Right::Write) == 2);
            assert(right_bit(Right::Execute) == 4);
        }
        let value = PageEntry {
            addr: frame * PAGE_SZ,
            perm: PageEntryPerm {
                present: true,
                ps: large,
                write: rights & 2 != 0,
                execute_disable: rights & 4 == 0,
                user: true,
            },
        };
        let tracked mut map = self.table_pages.maps.borrow_mut().tracked_remove(t);
        let tracked mut record = self.table_pages.records.borrow_mut().tracked_remove(t);
        let ptr = PPtr::<TableRecord>::from_usize(t + TABLE_RECORD_PAGE * PAGE_SZ);
        let table_record = *ptr.borrow(Tracked(&record));
        page_map_set(t + TABLE_NODE_PAGES * PAGE_SZ, Tracked(&mut map), e, value, table_record.level);
        ptr.write(
            Tracked(&mut record),
            TableRecord { level: table_record.level, space: table_record.space, parent: table_record.parent, written: true },
        );
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(t, map);
            self.table_pages.records.borrow_mut().tracked_insert(t, record);
            assert(self.table_pages.maps@ =~= pre.table_pages.maps@.insert(t, self.table_pages.maps@[t]));
            assert(self.table_pages.records@ =~= pre.table_pages.records@.insert(t, self.table_pages.records@[t]));
            assert(value == frame_map_entry(frame, rights, large));
        }
    }

    /// What a map leaves: the capability tables as they were; path p of the space still reaches its
    /// level 1 table and gains the page's entry, written with its accessed and dirty bits clear, and
    /// nothing else changes in any space; the node is the
    /// capability's child, names the entry, counts on the block and has the one record added; the frame
    /// is mapped. What it keeps,
    /// so that maps compose: every other node, the list's head, every other block's count, the
    /// processes, threads and spaces, every table walk, and, in a process's space, everyone's reach. A
    /// map into a device space adds the space with the frame's page to the shares, a grant to whoever
    /// sees the space.
    pub open spec fn map_done(pre: Self, post: Self, root: usize, slot: usize, p: SpacePath, from: usize, page: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let s = pre.payload_of(pre.tables.node_of(root, slot)).base;
        let f = pre.tables.node_of(root, from);
        let cap = pre.payload_of(f);
        let frame = frame_of(cap, page);
        let t = walk_table(a, s, p)->0;
        let node = mapping_node(t, p.l1);
        let br = block_ref(&pre.blocks, frame);
        &&& post.tables == pre.tables
        &&& walk_table(b, s, p) == Some(t)
        &&& space_mapping(b, s) == space_mapping(a, s).insert(p, frame_map_entry(frame, cap.rights, false))
        &&& post.table_pages.maps@[t].value().status(p.l1 as int).is_clear()
        &&& forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r)
        &&& post.list.is_child(f, node)
        &&& post.list.nodes@[node as int].kind is Mapping
        &&& post.mappings@.contains_key(node)
        &&& post.mappings@[node] == (MappingRecord { table: t, entry: p.l1, frame, large: false })
        &&& post.mappings@ == pre.mappings@.insert(node, MappingRecord { table: t, entry: p.l1, frame, large: false })
        &&& block_refs(&post.blocks, br) == block_refs(&pre.blocks, br) + 1
        &&& post.holders@[br] == pre.holders@[br].insert(node)
        &&& post.mapped@.contains(frame)
        &&& !pre.list.nodes@[node as int].live
        &&& post.list.parent@ == pre.list.parent@.insert(node, f)
        &&& post.list.seq@[0] == pre.list.seq@[0]
        &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
            &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
            &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            &&& post.list.nodes@[i].depth == pre.list.nodes@[i].depth
        }
        &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
        &&& post.processes == pre.processes
        &&& post.threads == pre.threads
        &&& post.spaces == pre.spaces
        &&& post.frames == pre.frames
        &&& forall|r: usize, q: SpacePath| #[trigger] walk_table(b, r, q) == walk_table(a, r, q)
        &&& pre.spaces.records@[s].value().kind is Process
            ==> forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o)
        &&& !(pre.spaces.records@[s].value().kind is Process)
            ==> post.view().shares == pre.view().shares.union(map_shares(s, frame, false))
    }

    /// What a large map leaves: the capability tables as they were; path p of the space still reaches its
    /// level 2 table and, at its first page, gains the large entry, written with its accessed and dirty
    /// bits clear, and nothing else changes in any space;
    /// the node is the capability's child, names the entry and counts on the block, and its record is the
    /// one the mappings gain, and every other block's count and every page's block are as they were; the
    /// table page changes in that entry alone; all 512 pages are mapped. Every
    /// other node keeps its liveness, kind, depth and parent. A large map into a device
    /// space adds the space with each of the frame's 512 pages to the shares.
    pub open spec fn map_large_done(pre: Self, post: Self, root: usize, slot: usize, p: SpacePath, from: usize, page: usize) -> bool {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let s = pre.payload_of(pre.tables.node_of(root, slot)).base;
        let f = pre.tables.node_of(root, from);
        let cap = pre.payload_of(f);
        let frame = frame_of(cap, page);
        let t = walk_large_table(a, s, p)->0;
        let node = mapping_node(t, p.l2);
        let br = block_ref(&pre.blocks, frame);
        &&& post.tables == pre.tables
        &&& post.processes == pre.processes
        &&& post.frames == pre.frames
        &&& walk_large_table(b, s, p) == Some(t)
        &&& space_mapping(b, s) == space_mapping(a, s).insert(p, frame_map_entry(frame, cap.rights, true))
        &&& post.table_pages.maps@[t].value().status(p.l2 as int).is_clear()
        &&& forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r)
        &&& post.list.is_child(f, node)
        &&& post.list.nodes@[node as int].kind is Mapping
        &&& post.mappings@.contains_key(node)
        &&& post.mappings@[node] == (MappingRecord { table: t, entry: p.l2, frame, large: true })
        &&& post.mappings@ == pre.mappings@.insert(node, MappingRecord { table: t, entry: p.l2, frame, large: true })
        &&& Self::entry_set(pre.table_pages, post.table_pages, t, p.l2, frame_map_entry(frame, cap.rights, true))
        &&& block_refs(&post.blocks, br) == block_refs(&pre.blocks, br) + 1
        &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
        &&& post.holders@[br] == pre.holders@[br].insert(node)
        &&& forall|g: usize| frame <= g < frame + PAGES_PER_2M ==> #[trigger] post.mapped@.contains(g)
        &&& post.list.parent@ == pre.list.parent@.insert(node, f)
        &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
            &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
            &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            &&& post.list.nodes@[i].depth == pre.list.nodes@[i].depth
        }
        &&& !(pre.spaces.records@[s].value().kind is Process)
            ==> post.view().shares == pre.view().shares.union(map_shares(s, frame, true))
    }

    /// The writes of a map that leaves what the device spaces map move no one's reach: the node they add
    /// is no capability, and every capability is as it was.
    proof fn lemma_map_reach(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
            post.view().shares == pre.view().shares,
        ensures
            forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o),
    {
        let node = mapping_node(t, e);
        pre.lemma_map_node_place(t, e);
        assert(Self::caps_frame(pre, post, node, node));
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            if x != node {
                Self::lemma_caps_frame(pre, post, node, node, x);
            }
        }
        Self::lemma_hidden_added_reach(pre, post, f, node);
    }

    /// The writes of a map, with the frame mapped, are what map_done says.
    proof fn lemma_map_done(pre: Self, post: Self, root: usize, slot: usize, kind: SpaceKind, p: SpacePath, from: usize, page: usize, t: usize, f: usize, frame: usize)
        requires
            post.frames@ == pre.frames@,
            pre.wf(),
            pre.can_map(root, slot, kind, p, from, page),
            f == pre.tables.node_of(root, from),
            frame == frame_of(pre.payload_of(f), page),
            walk_table(tree_of(&pre.table_pages, &pre.spaces), pre.payload_of(pre.tables.node_of(root, slot)).base, p) == Some(t),
            Self::map_from(pre, t, p.l1, f, frame, false),
            Self::map_written(pre, post, t, p.l1, f, frame, false),
            post.mapped@ == pre.mapped@.union(map_pages(frame, false)),
        ensures
            Self::map_done(pre, post, root, slot, p, from, page),
            kind is Process ==> post.view().shares == pre.view().shares,
            !(kind is Process) ==> discharges(
                pre.view(),
                post.view(),
                root,
                Effect::Share { space: pre.tables.node_of(root, slot), from: f },
            ),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let s = pre.payload_of(pre.tables.node_of(root, slot)).base;
        let e = p.l1;
        Self::lemma_map_tree(pre, post, t, e, f, frame, false);
        assert(b.entry(t, e) == frame_map_entry(frame, pre.payload_of(f).rights, false));
        lemma_mapping_written(a, b, s, p, t);
        lemma_walk_table_entry_written(a, b, t, e);
        if kind is Process {
            Self::lemma_map_process_shares(pre, post, s);
            Self::lemma_map_reach(pre, post, t, e, f, frame, false);
        } else {
            Self::lemma_map_device_discharges(pre, post, root, slot, from, p, t, e, frame, false);
            Self::lemma_map_device_shares(pre, post, s, p, t, e, f, frame, false);
        }
        lemma_map_pages(frame, false);
        assert(map_pages(frame, false).contains(frame));
    }

    /// The writes of a large map, with its pages mapped, are what map_large_done says.
    proof fn lemma_map_large_done(pre: Self, post: Self, root: usize, slot: usize, kind: SpaceKind, p: SpacePath, from: usize, page: usize, t: usize, f: usize, frame: usize)
        requires
            post.frames@ == pre.frames@,
            pre.wf(),
            pre.can_map_large(root, slot, kind, p, from, page),
            f == pre.tables.node_of(root, from),
            frame == frame_of(pre.payload_of(f), page),
            walk_large_table(tree_of(&pre.table_pages, &pre.spaces), pre.payload_of(pre.tables.node_of(root, slot)).base, p) == Some(t),
            Self::map_from(pre, t, p.l2, f, frame, true),
            Self::map_written(pre, post, t, p.l2, f, frame, true),
            post.mapped@ == pre.mapped@.union(map_pages(frame, true)),
        ensures
            Self::map_large_done(pre, post, root, slot, p, from, page),
            kind is Process ==> post.view().shares == pre.view().shares,
            !(kind is Process) ==> discharges(
                pre.view(),
                post.view(),
                root,
                Effect::Share { space: pre.tables.node_of(root, slot), from: f },
            ),
    {
        reveal(table_links_wf);
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let s = pre.payload_of(pre.tables.node_of(root, slot)).base;
        let e = p.l2;
        Self::lemma_map_tree(pre, post, t, e, f, frame, true);
        assert(b.entry(t, e) == frame_map_entry(frame, pre.payload_of(f).rights, true));
        lemma_large_mapping_written(a, b, s, p, t);
        if kind is Process {
            Self::lemma_map_process_shares(pre, post, s);
        } else {
            Self::lemma_map_device_discharges(pre, post, root, slot, from, p, t, e, frame, true);
            Self::lemma_map_device_shares(pre, post, s, p, t, e, f, frame, true);
        }
        let t3 = step(a, s, p.l4)->0;
        assert(step(b, s, p.l4) == step(a, s, p.l4));
        assert(a.record(t3).level == 3);
        assert(step(b, t3, p.l3) == step(a, t3, p.l3));
        lemma_map_pages(frame, true);
        assert forall|g: usize| frame <= g < frame + PAGES_PER_2M implies #[trigger] post.mapped@.contains(g) by {
            assert(map_pages(frame, true).contains(g));
        }
    }

    /// A map into a process's space leaves what every device space maps.
    proof fn lemma_map_process_shares(pre: Self, post: Self, s: usize)
        requires
            post.spaces == pre.spaces,
            pre.spaces.records@[s].value().kind is Process,
            forall|r: usize| r != s ==> #[trigger] space_mapping(tree_of(&post.table_pages, &post.spaces), r)
                == space_mapping(tree_of(&pre.table_pages, &pre.spaces), r),
        ensures
            post.view().shares == pre.view().shares,
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert forall|r: usize| #![trigger is_device(b, r)] #![trigger is_device(a, r)] is_device(b, r) == is_device(a, r) by {}
        lemma_mapped_same_shares(a, b, s);
    }

    /// The writes of a map into device space s, at a path it did not map, add to the shares s with each
    /// page of the frame, and nothing else.
    proof fn lemma_map_device_shares(pre: Self, post: Self, s: usize, p: SpacePath, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
            pre.spaces.roots@.contains_key(s),
            !(pre.spaces.records@[s].value().kind is Process),
            ({
                let a = tree_of(&pre.table_pages, &pre.spaces);
                let b = tree_of(&post.table_pages, &post.spaces);
                &&& walk(a, s, p) is None
                &&& space_mapping(b, s) == space_mapping(a, s).insert(p, frame_map_entry(frame, pre.payload_of(f).rights, large))
                &&& forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r)
            }),
        ensures
            post.view().shares == pre.view().shares.union(map_shares(s, frame, large)),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let v = frame_map_entry(frame, pre.payload_of(f).rights, large);
        assert forall|r: usize| #![trigger is_device(b, r)] #![trigger is_device(a, r)] is_device(b, r) == is_device(a, r) by {}
        assert(pre.blocks.tracks(frame as int));
        assert(v.addr == frame * PAGE_SZ);
        assert(v.addr / PAGE_SZ == frame);
        lemma_mapped_device_shares(a, b, s, p, v);
    }

    /// The writes of a map into a device space are a share by the mapper: what the space maps beyond
    /// what it did is pages of the frame, which the mapper's capability covers, and the capability to
    /// the space is one with the write right.
    proof fn lemma_map_device_discharges(pre: Self, post: Self, root: usize, slot: usize, from: usize, p: SpacePath, t: usize, e: usize, frame: usize, large: bool)
        requires
            post.frames@ == pre.frames@,
            pre.wf(),
            pre.tables.has_slot(&pre.list, root, slot),
            pre.is_cap(pre.tables.node_of(root, slot)),
            writes_space(pre.payload_of(pre.tables.node_of(root, slot))),
            !(pre.spaces.records@[pre.payload_of(pre.tables.node_of(root, slot)).base].value().kind is Process),
            pre.tables.has_slot(&pre.list, root, from),
            Self::map_from(pre, t, e, pre.tables.node_of(root, from), frame, large),
            Self::map_written(pre, post, t, e, pre.tables.node_of(root, from), frame, large),
            ({
                let a = tree_of(&pre.table_pages, &pre.spaces);
                let b = tree_of(&post.table_pages, &post.spaces);
                let s = pre.payload_of(pre.tables.node_of(root, slot)).base;
                let cap = pre.payload_of(pre.tables.node_of(root, from));
                &&& space_mapping(b, s) == space_mapping(a, s).insert(p, frame_map_entry(frame, cap.rights, large))
                &&& forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r)
            }),
        ensures
            discharges(
                pre.view(),
                post.view(),
                root,
                Effect::Share { space: pre.tables.node_of(root, slot), from: pre.tables.node_of(root, from) },
            ),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let n = pre.tables.node_of(root, slot);
        let f = pre.tables.node_of(root, from);
        let s = pre.payload_of(n).base;
        let cap = pre.payload_of(f);
        let v = frame_map_entry(frame, cap.rights, large);
        let node = mapping_node(t, e);
        let (st, pv) = (pre.view(), post.view());
        pre.lemma_map_node_place(t, e);
        pre.lemma_slot(root, slot);
        pre.lemma_slot(root, from);
        pre.lemma_written_space(n);
        assert(st.holds_right(root, n, Right::Write));
        assert(st.holds(root, f));
        assert(st.names.contains_key(f));
        assert(authorized(st, root, Effect::Share { space: n, from: f }));
        assert forall|r: usize| #![trigger is_device(b, r)] #![trigger is_device(a, r)] is_device(b, r) == is_device(a, r) by {}
        assert(pre.blocks.tracks(frame as int));
        assert(v.addr == frame * PAGE_SZ);
        assert(v.perm.ps == large);
        assert forall|x: ObjectId, o: ObjectId| #[trigger] pv.shares.contains((x, o)) && !st.shares.contains((x, o))
            implies x == st.names[n] && st.reach(root, o) by {
            lemma_mapped_shares(a, b, s, p, v, (x, o));
            assert(frame <= o / PAGE_SZ < frame + entry_pages(map_level(large)));
            assert(cap.base <= o < cap.base + block_bytes(cap.order));
            assert(st.covers(f, o));
            assert(st.descends(f, f, 0));
            assert(st.direct(root, o));
            assert(st.controlled(root, root, 0));
        }
        Self::lemma_leaf_added_discharges_share(pre, post, root, n, f, f, node);
    }

    /// The trees before and after the writes of a map are related by entry_written.
    proof fn lemma_map_tree(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            entry_written(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces), t, e),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
        assert(b.maps.dom() =~= a.maps.dom());
        assert forall|u: usize| u != t implies #[trigger] b.record(u) == a.record(u) by {
            assert(b.is_page(u) == a.is_page(u));
            if a.is_page(u) {
                assert(post.table_pages.records@[u] == pre.table_pages.records@[u]);
            }
        }
        assert forall|u: usize, i: usize| #![trigger b.entry(u, i)]
            i < ENTRIES && !(u == t && i == e) implies b.entry(u, i) == a.entry(u, i) by {
            assert(b.is_page(u) == a.is_page(u));
            if a.is_page(u) && u != t {
                assert(post.table_pages.maps@[u] == pre.table_pages.maps@[u]);
            }
        }
    }

    /// A space's root is no table page, since their blocks' objects differ, and it is level 4.
    pub proof fn lemma_root_table(&self, s: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
        ensures
            !self.table_pages.maps@.contains_key(s),
            tree_of(&self.table_pages, &self.spaces).is_root(s),
            tree_of(&self.table_pages, &self.spaces).record(s).level == 4,
            self.blocks.tracks_addr(s),
    {
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        if self.table_pages.maps@.contains_key(s) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, s));
        }
        assert(root_record_wf(&self.spaces, s));
    }

    /// Where the node of entry e of table page t lies: node (e + 1) % 128 of node page (e + 1) / 128 of
    /// t's block, a page the list holds. It is neither t, a leaf, a leaf's node nor a table page.
    pub proof fn lemma_map_node_place(&self, t: usize, e: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
            e < ENTRIES,
        ensures
            mapping_node(t, e) == t + ((e + 1) / (NODES_PER_PAGE as int)) * PAGE_SZ + (e + 1) % (NODES_PER_PAGE as int),
            mapping_node(t, e) < NODE_SPACE,
            mapping_node(t, e) % PAGE_SZ == (e + 1) % (NODES_PER_PAGE as int),
            mapping_node(t, e) / PAGE_SZ == t / PAGE_SZ + (e + 1) / (NODES_PER_PAGE as int),
            self.list.valid(mapping_node(t, e)),
            mapping_node(t, e) != t,
            !self.tables.owner@.contains_key(mapping_node(t, e)),
            !self.tables.owner@.contains_key(page_of(mapping_node(t, e))),
            !self.table_pages.maps@.contains_key(mapping_node(t, e)),
    {
        self.lemma_table_page_room(t);
        lemma_mapping_node_place(t, e);
        let n = mapping_node(t, e);
        let k = ((e + 1) / (NODES_PER_PAGE as int)) as usize;
        let q = t / PAGE_SZ;
        assert(k < TABLE_NODE_PAGES);
        assert(page_of(n) == table_node_page(t, k));
        assert(self.list.pages@.dom().contains(table_node_page(t, k)));
        assert(self.list.valid(n));
        self.list.lemma_valid_bound(n);
        lemma_table_node_page(t, k);
        assert(page_of(n) / PAGE_SZ == q + k);
        if k == 0 {
            assert(n % PAGE_SZ == e + 1);
        } else {
            assert(n / PAGE_SZ != q);
        }
        if self.tables.owner@.contains_key(n) {
            assert(self.blocks.pages@[(n / PAGE_SZ) as int].kind is Base);
            assert(self.blocks.pages@[(n / PAGE_SZ) as int].object is TableLeaf);
            if k > 0 {
                assert(self.blocks.pages@[q + k].kind is Member);
            }
            assert(false);
        }
        if self.tables.owner@.contains_key(page_of(n)) {
            let l = page_of(n);
            assert(self.blocks.pages@[(l / PAGE_SZ) as int].kind is Base);
            assert(self.blocks.pages@[(l / PAGE_SZ) as int].object is TableLeaf);
            if k > 0 {
                assert(self.blocks.pages@[q + k].kind is Member);
            }
            assert(false);
        }
        if self.table_pages.maps@.contains_key(n) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, n));
            if k > 0 {
                assert(self.blocks.pages@[q + k].kind is Member);
            }
            lemma_table_page_aligned(n);
            assert(false);
        }
    }

    /// An empty entry of a table page has no live node at e + 1 of the table's block.
    pub proof fn lemma_map_node_free(&self, t: usize, e: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
            e < ENTRIES,
            tree_of(&self.table_pages, &self.spaces).entry(t, e).is_empty(),
        ensures
            mapping_node(t, e) < NODE_SPACE,
            self.list.valid(mapping_node(t, e)),
            !self.list.nodes@[mapping_node(t, e) as int].live,
    {
        self.lemma_map_node_place(t, e);
        let n = mapping_node(t, e);
        let tree = tree_of(&self.table_pages, &self.spaces);
        if self.list.nodes@[n as int].live {
            self.lemma_table_node_is_mapping(t, e);
            assert(self.mappings@.contains_key(n));
            let m = self.mappings@[n];
            assert(mapping_wf(&self.list, &self.tables, tree, &self.blocks, self.holders@, self.mappings@, n));
            self.lemma_table_page_room(m.table);
            self.lemma_table_page_room(t);
            lemma_mapping_node_injective(t, e, m.table, m.entry);
            assert(tree.entry(t, e).perm.present);
            assert(false);
        }
    }

    /// Page `page` of frame capability f lies in the capability's block and is a tracked page.
    pub proof fn lemma_frame_page(&self, f: usize, page: usize)
        requires
            self.wf(),
            self.is_cap(f),
            self.payload_of(f).kind is Frame,
            (page as int) * PAGE_SZ < block_bytes(self.payload_of(f).order),
        ensures
            ({
                let cap = self.payload_of(f);
                let frame = frame_of(cap, page);
                &&& cap.base % PAGE_SZ == 0
                &&& self.blocks.tracks(cap.base / PAGE_SZ + page)
                &&& frame == cap.base / PAGE_SZ + page
                &&& frame * PAGE_SZ == cap.base + page * PAGE_SZ
                &&& cap.base <= frame * PAGE_SZ
                &&& frame * PAGE_SZ + PAGE_SZ <= cap.base as int + block_bytes(cap.order)
                &&& block_ref(&self.blocks, frame) == block_ref(&self.blocks, cap.base / PAGE_SZ)
                &&& self.holders@.contains_key(block_ref(&self.blocks, frame))
                &&& block_typed(&self.blocks, block_ref(&self.blocks, frame))
            }),
    {
        let cap = self.payload_of(f);
        assert(self.tables.is_cap(&self.list, f));
        assert(payload_wf(cap));
        let m = pow2(cap.order as nat) as int;
        lemma_pow2_pos(cap.order as nat);
        assert(block_bytes(cap.order) == m * PAGE_SZ);
        lemma_block_base_aligned(cap.base, cap.order);
        lemma_fundamental_div_mod(cap.base as int, (PAGE_SZ as int));
        assert(cap.base as int == PAGE_SZ * (cap.base as int / (PAGE_SZ as int)));
        assert((page as int) * PAGE_SZ < m * PAGE_SZ);
        assert(page < m);
        let fr = cap.base as int / (PAGE_SZ as int) + page;
        assert(fr * PAGE_SZ == cap.base + page * PAGE_SZ);
        assert(fr * PAGE_SZ + PAGE_SZ <= cap.base + m * PAGE_SZ);
        lemma_holder_refs(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@, f);
        assert(frame_in_block(block_ref(&self.blocks, cap.base / PAGE_SZ), cap));
        lemma2_to64();
        assert(block_bytes(0) == PAGE_SZ);
        let child = Payload { kind: cap.kind, order: 0, rights: cap.rights, base: (fr * PAGE_SZ) as usize, badge: cap.badge, priority: cap.priority };
        lemma_mod_multiples_basic(fr, (PAGE_SZ as int));
        lemma_child_same_block(&self.blocks, cap, child);
        lemma_div_multiples_vanish(fr, (PAGE_SZ as int));
        assert(child.base as int / (PAGE_SZ as int) == fr);
        assert(self.blocks.tracks(fr));
        assert(frame_of(cap, page) == fr);
    }

    /// The 512 pages from 2M-aligned offset `page` of the 2M or 1G frame capability f lie in the
    /// capability's block, are tracked pages, and start 2M aligned.
    pub proof fn lemma_large_frame_page(&self, f: usize, page: usize)
        requires
            self.wf(),
            self.is_cap(f),
            self.payload_of(f).kind is Frame,
            self.payload_of(f).order == 9 || self.payload_of(f).order == 18,
            page % PAGES_PER_2M == 0,
            (page as int) * PAGE_SZ + PAGES_PER_2M * PAGE_SZ <= block_bytes(self.payload_of(f).order),
        ensures
            ({
                let cap = self.payload_of(f);
                let frame = frame_of(cap, page);
                &&& cap.base % PAGE_SZ == 0
                &&& self.blocks.tracks(cap.base / PAGE_SZ + page)
                &&& frame == cap.base / PAGE_SZ + page
                &&& frame % PAGES_PER_2M == 0
                &&& cap.base <= frame * PAGE_SZ
                &&& frame * PAGE_SZ + PAGES_PER_2M * PAGE_SZ <= cap.base as int + block_bytes(cap.order)
                &&& block_ref(&self.blocks, frame) == block_ref(&self.blocks, cap.base / PAGE_SZ)
                &&& self.holders@.contains_key(block_ref(&self.blocks, frame))
                &&& block_typed(&self.blocks, block_ref(&self.blocks, frame))
            }),
    {
        let cap = self.payload_of(f);
        assert(self.tables.is_cap(&self.list, f));
        assert(payload_wf(cap));
        let m = pow2(cap.order as nat) as int;
        lemma_pow2_pos(cap.order as nat);
        assert(block_bytes(cap.order) == m * PAGE_SZ);
        lemma_large_base_aligned(cap.base, cap.order);
        lemma_fundamental_div_mod(cap.base as int, (PAGE_SZ as int));
        assert(cap.base as int == PAGE_SZ * (cap.base as int / (PAGE_SZ as int)));
        let fr = cap.base as int / (PAGE_SZ as int) + page;
        lemma_sum_aligned(cap.base as int / (PAGE_SZ as int), page as int);
        assert(fr % (PAGES_PER_2M as int) == 0);
        assert(fr * PAGE_SZ == cap.base + page * PAGE_SZ);
        assert(fr * PAGE_SZ + PAGES_PER_2M * PAGE_SZ <= cap.base + m * PAGE_SZ);
        lemma_holder_refs(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@, f);
        assert(frame_in_block(block_ref(&self.blocks, cap.base / PAGE_SZ), cap));
        lemma2_to64();
        assert(block_bytes(9) == PAGES_PER_2M * PAGE_SZ);
        let child = Payload { kind: cap.kind, order: 9, rights: cap.rights, base: (fr * PAGE_SZ) as usize, badge: cap.badge, priority: cap.priority };
        lemma_fundamental_div_mod(fr, (PAGES_PER_2M as int));
        let q2 = fr / (PAGES_PER_2M as int);
        assert(fr == PAGES_PER_2M * q2);
        lemma_mul_is_associative(PAGES_PER_2M as int, q2, PAGE_SZ as int);
        lemma_mul_is_commutative(q2, PAGE_SZ as int);
        lemma_mul_is_associative(PAGES_PER_2M as int, PAGE_SZ as int, q2);
        assert(fr * PAGE_SZ == (PAGES_PER_2M * PAGE_SZ) * q2);
        lemma_mod_multiples_basic(fr / (PAGES_PER_2M as int), (PAGES_PER_2M as int) * (PAGE_SZ as int));
        lemma_child_same_block(&self.blocks, cap, child);
        lemma_div_multiples_vanish(fr, (PAGE_SZ as int));
        assert(child.base as int / (PAGE_SZ as int) == fr);
        assert(self.blocks.tracks(fr));
        assert(frame_of(cap, page) == fr);
    }

    /// The nodes and capabilities after a map: no capability changed, so the view's tables and every
    /// clause about node kinds stand.
    proof fn lemma_map_nodes(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            post.tables.wf(&post.list),
            post.tables.caps_wf(&post.list),
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
            capability_nodes_are_slots(&post.list, &post.tables),
            first_node_outside_leaves(&post.list, &post.tables),
            leaf_slots_are_capabilities(&post.list, &post.tables),
            same_leaf_nodes(&pre.list, &post.list, &pre.tables),
            same_table_nodes(&pre.list, &post.list, &pre.table_pages),
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        let node = mapping_node(t, e);
        pre.lemma_map_node_place(t, e);
        assert(Self::caps_frame(pre, post, node, node));
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            if x == node {
                assert(!(post.list.nodes@[x as int].kind is Capability));
                assert(!pre.list.nodes@[x as int].live);
            } else {
                Self::lemma_caps_frame(pre, post, node, node, x);
            }
        }
        pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x)
            implies cap_wf(post.tables.payload_of(x)) by {
            assert(pre.tables.is_cap(&pre.list, x));
        }
        Self::lemma_map_kinds(pre, post, t, e, f, frame, large);
        Self::lemma_map_same_nodes(pre, post, t, e, f, frame, large);
        Self::lemma_devices_same_caps(pre, post);
    }

    /// The node kinds after a map: the new node is a mapping, so every clause about hidden, capability
    /// and leaf nodes stands, and no node of a leaf or a table page changed.
    proof fn lemma_map_kinds(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
            capability_nodes_are_slots(&post.list, &post.tables),
            first_node_outside_leaves(&post.list, &post.tables),
            leaf_slots_are_capabilities(&post.list, &post.tables),
    {
        let node = mapping_node(t, e);
        pre.lemma_map_node_place(t, e);
        pre.lemma_slot_bound(f);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            assert(x != node);
            assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Hidden);
            assert(post.table_pages.maps@.contains_key(x) == pre.table_pages.maps@.contains_key(x));
        }
        lemma_parents_derived(pre.list, post.list, f, node);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Capability
            && x != post.list.seq@[0] implies post.tables.is_cap(&post.list, x) by {
            assert(x != node);
            assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Capability);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|x: usize| #[trigger] post.list.nodes@[x as int].live && post.tables.owner@.contains_key(page_of(x))
            && x % PAGE_SZ != 0 && x % PAGE_SZ < NODES_PER_PAGE implies post.list.nodes@[x as int].kind is Capability by {
            assert(x != node);
            pre.lemma_slot_bound(x);
            assert(pre.list.nodes@[x as int].live);
        }
    }

    /// No node of a leaf or of a table page changed in a map: the new node is in neither.
    proof fn lemma_map_same_nodes(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            same_leaf_nodes(&pre.list, &post.list, &pre.tables),
            same_table_nodes(&pre.list, &post.list, &pre.table_pages),
    {
        let node = mapping_node(t, e);
        pre.lemma_map_node_place(t, e);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            assert(l != node);
            pre.tables.lemma_leaf(&pre.list, l);
            pre.lemma_slot_bound(l);
        }
        assert forall|u: usize| #[trigger] pre.table_pages.maps@.contains_key(u) implies {
            &&& post.list.nodes@[u as int].live == pre.list.nodes@[u as int].live
            &&& post.list.nodes@[u as int].kind == pre.list.nodes@[u as int].kind
        } by {
            assert(u != node);
            pre.lemma_table_page_valid(u);
        }
    }

    /// The blocks, holders and spaces after a map: the frame's block has one more reference, held by the
    /// node, and no other block changed.
    proof fn lemma_map_blocks(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
    {
        let node = mapping_node(t, e);
        let br = block_ref(&pre.blocks, frame);
        let refs = (block_refs(&pre.blocks, br) + 1) as usize;
        let dead = block_dead(&pre.blocks, br);
        pre.lemma_map_node_place(t, e);
        assert(pre.tables.is_cap(&pre.list, f));
        lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, f);
        assert(pre.holders@.contains_key(br));
        Self::lemma_map_nodes(pre, post, t, e, f, frame, large);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        lemma_holders_mapping_added(&pre.list, &pre.tables, &post.list, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, node, br);
        lemma_zeroing_typed_refs_changed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, br, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
    }

    /// The objects, frames, leaf blocks and spaces after a map: a frame block's count changed, which
    /// none of them reads beyond the holders.
    proof fn lemma_map_objects(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            objects_wf(&post.tables, &post.blocks, post.holders@),
            frames_held(post.frames@, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        let node = mapping_node(t, e);
        let br = block_ref(&pre.blocks, frame);
        let refs = (block_refs(&pre.blocks, br) + 1) as usize;
        let dead = block_dead(&pre.blocks, br);
        pre.lemma_map_node_place(t, e);
        assert(pre.tables.is_cap(&pre.list, f));
        lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, f);
        assert(pre.holders@.contains_key(br));
        Self::lemma_map_nodes(pre, post, t, e, f, frame, large);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: BlockRef| #[trigger] post.holders@.contains_key(x) == pre.holders@.contains_key(x) by {}
        lemma_objects_refs_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, post.holders@, br, refs, dead);
        assert forall|x: BlockRef, i: usize| #[trigger] post.holders@.contains_key(x) && #[trigger] block_has_page(x, i)
            implies post.frames@.contains_key(i) by {
            assert(pre.holders@.contains_key(x));
        }
        lemma_leaf_blocks_refs_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, br, refs, dead);
        if let BlockRef::Small(x) = br {
            assert(pre.blocks.pages@[x as int].object is Frame);
        }
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, refs, dead);
        assert(same_threads(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, refs, dead);
    }

    /// The table pages and the links after a map: the frame's block is no table page's, and the entry
    /// written is at level 1, below every link.
    proof fn lemma_map_tables(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let br = block_ref(&pre.blocks, frame);
        let refs = (block_refs(&pre.blocks, br) + 1) as usize;
        let dead = block_dead(&pre.blocks, br);
        assert(pre.tables.is_cap(&pre.list, f));
        lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, f);
        Self::lemma_map_nodes(pre, post, t, e, f, frame, large);
        if let BlockRef::Small(x) = br {
            assert(pre.blocks.pages@[x as int].object is Frame);
        }
        lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
        assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
        Self::lemma_map_tree(pre, post, t, e, f, frame, large);
        lemma_table_pages_entry_written(&post.list, &pre.table_pages, &post.table_pages, &post.blocks, t, e);
        lemma_links_entry_written(a, b, t, e);
    }

    /// The mappings after a map: the new node's record says what was written, and every other record's
    /// entry, node, parent and holding are as they were.
    proof fn lemma_map_mappings(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let node = mapping_node(t, e);
        let br = block_ref(&pre.blocks, frame);
        let cap = pre.payload_of(f);
        pre.lemma_map_node_place(t, e);
        Self::lemma_map_nodes(pre, post, t, e, f, frame, large);
        Self::lemma_map_tree(pre, post, t, e, f, frame, large);
        assert(pre.tables.is_cap(&pre.list, f));
        lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, f);
        assert(block_ref(&post.blocks, frame) == br);
        assert(post.list.valid(node));
        assert forall|k: BlockRef| post.holders@.contains_key(k) && #[trigger] post.holders@[k].contains(node) implies k == br by {
            if k != br {
                assert(pre.holders@[k].contains(node));
                assert(!pre.tables.is_cap(&pre.list, node));
            }
        }
        assert(mapping_wf(&post.list, &post.tables, b, &post.blocks, post.holders@, post.mappings@, node));
        assert forall|n: usize| #[trigger] post.mappings@.contains_key(n)
            implies mapping_wf(&post.list, &post.tables, b, &post.blocks, post.holders@, post.mappings@, n) by {
            if n != node {
                assert(pre.mappings@.contains_key(n));
                assert(post.mappings@[n] == pre.mappings@[n]);
                pre.lemma_mapping_node(n);
                assert(mapping_wf(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, pre.mappings@, n));
                let mx = pre.mappings@[n];
                let c = pre.list.parent@[n];
                assert(c != node);
                assert(!(mx.table == t && mx.entry == e));
                assert(b.entry(mx.table, mx.entry) == a.entry(mx.table, mx.entry));
                assert(b.record(mx.table).level == a.record(mx.table).level);
                assert(block_ref(&post.blocks, mx.frame) == block_ref(&pre.blocks, mx.frame));
                assert(post.holders@[block_ref(&pre.blocks, mx.frame)].contains(n));
                assert forall|k: BlockRef| post.holders@.contains_key(k) && #[trigger] post.holders@[k].contains(n)
                    implies k == block_ref(&post.blocks, mx.frame) by {
                    assert(pre.holders@[k].contains(n));
                }
                assert(post.is_cap(c) == pre.is_cap(c));
            }
        }
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Mapping
            implies post.mappings@.contains_key(x) by {
            if x != node {
                assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Mapping);
            }
        }
        assert forall|u: usize, i: usize| #[trigger] frame_slot(b, u, i) implies {
            &&& post.mappings@.contains_key(mapping_node(u, i))
            &&& post.mappings@[mapping_node(u, i)].table == u
            &&& post.mappings@[mapping_node(u, i)].entry == i
        } by {
            if !(u == t && i == e) {
                assert(a.is_page(u));
                assert(b.record(u).level == a.record(u).level);
                assert(b.entry(u, i) == a.entry(u, i));
                assert(frame_slot(a, u, i));
                let k = mapping_node(u, i);
                assert(pre.mappings@.contains_key(k));
                if k == node {
                    pre.lemma_mapping_node(k);
                    assert(false);
                }
            }
        }
    }

    /// The node a map adds is a mapping node, and every other node of a table page is as it was.
    proof fn lemma_map_table_nodes(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            table_nodes_are_mappings(&post.list, &post.table_pages),
    {
        assert forall|u: usize, k: usize, i: usize| #![trigger table_node(u, k, i)]
            post.table_pages.maps@.contains_key(u) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE && (k != 0 || i != 0)
                && post.list.nodes@[table_node(u, k, i) as int].live
            implies post.list.nodes@[table_node(u, k, i) as int].kind is Mapping by {
            assert(pre.table_pages.maps@.contains_key(u));
            pre.lemma_table_node_in_block(u, k, i);
        }
    }

    /// Everything the invariant says after the writes of a map.
    proof fn lemma_map_wf(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped@ == pre.mapped@.union(map_pages(frame, large)),
            post.stale_epoch == pre.stale_epoch,
        ensures
            post.wf(),
    {
        Self::lemma_map_nodes(pre, post, t, e, f, frame, large);
        Self::lemma_map_table_nodes(pre, post, t, e, f, frame, large);
        Self::lemma_map_blocks(pre, post, t, e, f, frame, large);
        Self::lemma_map_objects(pre, post, t, e, f, frame, large);
        Self::lemma_map_tables(pre, post, t, e, f, frame, large);
        Self::lemma_map_mappings(pre, post, t, e, f, frame, large);
        Self::lemma_tlb_more_mapped(pre, post);
        assert(!pre.mappings@.contains_key(mapping_node(t, e)));
        lemma_mapped_inserted(pre.mapped@, pre.mappings@, mapping_node(t, e), MappingRecord { table: t, entry: e, frame, large });
        assert(mapped_wf(post.mapped@, post.mappings@));
        assert(post.frames_wf());
        Self::lemma_map_space_nodes(pre, post, t, e, f, frame, large);
        let node = mapping_node(t, e);
        assert forall|x: usize| x < NODE_SPACE implies {
            &&& ((#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Binding)
                == (pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Binding)
            &&& (post.list.nodes@[x as int].live && post.list.nodes@[x as int].kind is DeviceBinding)
                == (pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is DeviceBinding)
        } by {
            if x != node {
                assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
                assert(post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind);
            }
        }
        assert(same_bindings(&pre.list, &post.list));
        lemma_bindings_same(&pre.list, &post.list, &pre.threads, &pre.processes);
        Self::lemma_binding_parents_same_caps(pre, post);
    }

    /// The node a map makes lives in its table page's block, so every device space's node pages stay dead.
    proof fn lemma_map_space_nodes(pre: Self, post: Self, t: usize, e: usize, f: usize, frame: usize, large: bool)
        requires
            pre.wf(),
            Self::map_from(pre, t, e, f, frame, large),
            Self::map_written(pre, post, t, e, f, frame, large),
        ensures
            space_nodes_dead(&post.list, &post.spaces),
    {
        let n = mapping_node(t, e);
        let j = ((e + 1) / (NODES_PER_PAGE as int)) as usize;
        assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
        pre.lemma_map_node_place(t, e);
        pre.lemma_table_page_room(t);
        lemma_mapping_node_place(t, e);
        assert forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
            post.spaces.roots@.contains_key(s) && !(post.spaces.records@[s].value().kind is Process) && k < TABLE_NODE_PAGES
                && i < NODES_PER_PAGE
            implies !post.list.nodes@[table_node(s, k, i) as int].live by {
            let x = table_node(s, k, i);
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
            pre.lemma_space_node_in_block(s, k, i);
            assert(s != t);
            if x == n {
                lemma_node_pages_disjoint(t, s, j);
                assert(page_of(x) == table_node_page(s, k));
                assert(page_of(n) == table_node_page(t, j));
            }
            assert(x != n);
            assert(!pre.list.nodes@[x as int].live);
        }
    }

    /// A node added that is no capability, such as a mapping or a binding, leaves what the view reads
    /// of capabilities, and its parent link reaches nothing: apart from what the device spaces map,
    /// post's authority is all in pre, under the renaming returned, which renames nothing.
    pub proof fn lemma_leaf_added_simulates(pre: Self, post: Self, f: usize, node: usize) -> (m: (spec_fn(NodeId) -> bool, spec_fn(NodeId) -> NodeId))
        requires
            pre.wf(),
            post.tables == pre.tables,
            node < NODE_SPACE,
            !pre.list.nodes@[node as int].live,
            !(post.list.nodes@[node as int].kind is Capability),
            post.list.parent@ == pre.list.parent@.insert(node, f),
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
                &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
                &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            },
        ensures
            simulates(State { shares: pre.view().shares, binds: pre.view().binds, ..post.view() }, pre.view(), m.0, m.1),
            forall|x: NodeId| #[trigger] (m.1)(x) == x,
            forall|x: NodeId| #[trigger] post.view().names.contains_key(x) == pre.view().names.contains_key(x),
            forall|x: NodeId, r: Right| #[trigger] post.view().rights.contains((x, r)) && post.view().names.contains_key(x)
                ==> pre.view().rights.contains((x, r)) && pre.view().names.contains_key(x)
                && post.view().names[x] == pre.view().names[x],
    {
        let (a, b) = (State { shares: pre.view().shares, binds: pre.view().binds, ..post.view() }, pre.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        let g = |x: NodeId| x;
        assert(Self::caps_frame(pre, post, node, node));
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            if x == node {
                assert(!(post.list.nodes@[x as int].kind is Capability));
            } else {
                Self::lemma_caps_frame(pre, post, node, node, x);
            }
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, g(h.1))) by {
            assert(post.is_cap(h.1) == pre.is_cap(h.1));
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(g(x))
            &&& b.names[g(x)] == a.names[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(g(x))
            &&& b.pages[g(x)] == a.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((g(x), r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(g(x))
            &&& b.parent[g(x)] == g(a.parent[x])
        } by {
            assert(x != node);
            pre.list.lemma_parent_live(x);
        }
        assert(simulates(a, b, live, g));
        assert forall|x: NodeId| #[trigger] post.view().names.contains_key(x) == pre.view().names.contains_key(x) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        (live, g)
    }

    /// So when the device spaces map and bind no more, it is a local step.
    pub proof fn lemma_leaf_added_discharges(pre: Self, post: Self, root: usize, f: usize, node: usize)
        requires
            post.frames@ == pre.frames@,
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            pre.wf(),
            post.tables == pre.tables,
            node < NODE_SPACE,
            !pre.list.nodes@[node as int].live,
            !(post.list.nodes@[node as int].kind is Capability),
            post.list.parent@ == pre.list.parent@.insert(node, f),
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
                &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
                &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            },
            post.view().shares.subset_of(pre.view().shares),
            binds_within(post.view(), pre.view()),
        ensures
            discharges(pre.view(), post.view(), root, Effect::Local),
            forall|x: NodeId| #[trigger] post.view().names.contains_key(x) == pre.view().names.contains_key(x),
            forall|x: NodeId, r: Right| #[trigger] post.view().rights.contains((x, r)) && post.view().names.contains_key(x)
                ==> pre.view().rights.contains((x, r)) && pre.view().names.contains_key(x)
                && post.view().names[x] == pre.view().names[x],
    {
        let (a, b) = (post.view(), pre.view());
        let m = Self::lemma_leaf_added_simulates(pre, post, f, node);
        lemma_simulates_spaces(State { shares: b.shares, binds: b.binds, ..a }, a, b, m.0, m.1);
        assert forall|o: ObjectId| #[trigger] (a.contents)(o) == (b.contents)(o) by {}
        lemma_simulated_discharges_local(b, a, root, m.0, m.1);
    }

    /// And when the node added binds device d to space s, which whoever reaches d directly sees
    /// already.
    pub proof fn lemma_binding_added_discharges(pre: Self, post: Self, root: usize, f: usize, node: usize, d: ObjectId, s: ObjectId)
        requires
            post.frames@ == pre.frames@,
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            pre.wf(),
            post.tables == pre.tables,
            node < NODE_SPACE,
            !pre.list.nodes@[node as int].live,
            !(post.list.nodes@[node as int].kind is Capability),
            post.list.parent@ == pre.list.parent@.insert(node, f),
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
                &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
                &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            },
            post.view().shares.subset_of(pre.view().shares),
            post.view().binds == pre.view().binds.insert(d, s),
            forall|q: ObjectId| #[trigger] pre.view().direct(q, d) ==> pre.view().sees(q, s),
        ensures
            discharges(pre.view(), post.view(), root, Effect::Local),
    {
        let (a, b) = (post.view(), pre.view());
        let m = Self::lemma_leaf_added_simulates(pre, post, f, node);
        lemma_simulates_spaces(State { shares: b.shares, binds: b.binds, ..a }, State { binds: b.binds, ..a }, b, m.0, m.1);
        assert forall|o: ObjectId| #[trigger] (a.contents)(o) == (b.contents)(o) by {}
        lemma_simulated_discharges_bind(b, a, root, d, s, m.0, m.1);
    }

    /// And when what they map beyond what they did is in the space that capability `space` names, which
    /// root holds with the write right, and in root's reach, it is a share by root.
    pub proof fn lemma_leaf_added_discharges_share(pre: Self, post: Self, root: usize, space: usize, from: usize, f: usize, node: usize)
        requires
            post.frames@ == pre.frames@,
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            pre.wf(),
            post.tables == pre.tables,
            node < NODE_SPACE,
            !pre.list.nodes@[node as int].live,
            !(post.list.nodes@[node as int].kind is Capability),
            post.list.parent@ == pre.list.parent@.insert(node, f),
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != node ==> {
                &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
                &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
            },
            authorized(pre.view(), root, Effect::Share { space, from }),
            forall|s: ObjectId, o: ObjectId| #[trigger] post.view().shares.contains((s, o)) && !pre.view().shares.contains((s, o))
                ==> s == pre.view().names[space] && pre.view().reach(root, o),
            binds_within(post.view(), pre.view()),
        ensures
            discharges(pre.view(), post.view(), root, Effect::Share { space, from }),
    {
        let (a, b) = (post.view(), pre.view());
        let m = Self::lemma_leaf_added_simulates(pre, post, f, node);
        lemma_simulates_spaces(State { shares: b.shares, binds: b.binds, ..a }, State { shares: b.shares, ..a }, b, m.0, m.1);
        assert forall|o: ObjectId| #[trigger] (a.contents)(o) == (b.contents)(o) by {}
        lemma_simulated_discharges_share(b, a, root, space, from, m.0, m.1);
    }
}

} // verus!
