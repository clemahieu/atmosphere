//! The divider's layout: the table of grants by which the root divides what boot gave it between
//! tenants, and `layout_ok`, the decidable rule a layout must meet, with `check`, proven to return
//! exactly it.
//!
//! A layout has three parts. `held` is the blocks the divider holds, as boot gave them. `rows` is the
//! table: each row gives one tenant one block of one kind with some rights, and says whether the
//! block is shared. `joins` names pairs of tenants that count as one, because what one holds may come
//! to be held by the other. Every row names a block of objects as kernel/verified/capability/reach.rs
//! does: memory is pages below 2^48, device d is the page at 2^48 + d pages, the console and power
//! the pages past the devices'. A block is a base aligned to its size and 2^order pages, as
//! design/capability-names-a-block/ says.
//!
//! `layout_ok` holds when:
//! - every held block and every row's block is aligned to its order and lies in the object space,
//!   and every row's block lies inside one block the divider holds;
//! - two rows of different tenants intersect only when both are marked shared, each with its own
//!   rights;
//! - a row carrying the grant or the control right that intersects a row of another tenant has the
//!   two tenants joined: reach.rs's Deliver needs only the sender's grant right to hand the receiver
//!   any capability, and control commands what the controlled process holds, so either lets the two
//!   come to reach each other's rows;
//! - a device row intersects no other row, since a device has one holder.
//!
//! `overlap(rows, i, j)` is the declared overlap D(i, j): the pairs of rows of tenants i and j whose
//! blocks intersect. `lemma_overlap_declared` says what `layout_ok` gives of it. The examples at the
//! end are proven to pass or fail as a reader would expect, and the tests run `check` on them.
#![cfg_attr(not(test), no_std)]
#![allow(unused)]

use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;

mod define;
pub use define::*;

verus! {

/// The largest block a row can name: 2^36 pages reach the end of the 48-bit address space.
pub const MAX_ORDER: u8 = 36;

/// The rights bits, as the kernel numbers them (kernel/verified/capability/view.rs).
pub const READ: u32 = 1;
pub const WRITE: u32 = 2;
pub const EXECUTE: u32 = 4;
pub const RETYPE: u32 = 8;
pub const SEND: u32 = 16;
pub const RECEIVE: u32 = 32;
pub const GRANT: u32 = 64;
pub const CONTROL: u32 = 128;

/// A tenant's number in the layout.
pub type Tenant = u32;

/// The kind of object a row grants, numbered as asys numbers capability kinds.
#[derive(Clone, Copy)]
pub enum Kind {
    Untyped = 0,
    Frame = 1,
    Process = 2,
    Thread = 3,
    Endpoint = 4,
    Reply = 5,
    Notification = 6,
    Space = 7,
    Device = 8,
    Console = 9,
    Power = 10,
}

/// A base and 2^order pages.
#[derive(Clone, Copy)]
pub struct Block {
    pub base: u64,
    pub order: u8,
}

/// One grant: `tenant` gets `block` as `kind` with `rights`; `shared` declares that another
/// tenant's row may intersect it.
#[derive(Clone, Copy)]
pub struct Row {
    pub tenant: Tenant,
    pub kind: Kind,
    pub block: Block,
    pub rights: u32,
    pub shared: bool,
}

/// Tenants `a` and `b` count as one, in either order.
#[derive(Clone, Copy)]
pub struct Join {
    pub a: Tenant,
    pub b: Tenant,
}

/// A block of this order, in bytes.
pub open spec fn bytes(order: u8) -> int {
    pow2(order as nat) as int * PAGE_BYTES
}

/// The first byte past the block.
pub open spec fn end(b: Block) -> int {
    b.base + bytes(b.order)
}

/// The block is aligned to its size and lies in the object space.
pub open spec fn block_ok(b: Block) -> bool {
    &&& b.order <= MAX_ORDER
    &&& b.base as int % bytes(b.order) == 0
    &&& end(b) <= OBJECT_SPACE
}

/// Block `b` lies inside block `h`.
pub open spec fn within(b: Block, h: Block) -> bool {
    h.base <= b.base && end(b) <= end(h)
}

/// Blocks `a` and `b` share an object.
pub open spec fn intersect(a: Block, b: Block) -> bool {
    a.base < end(b) && b.base < end(a)
}

/// The row lets its tenant hand capabilities to, or act for, a process it shares the block with.
pub open spec fn carries_authority(r: Row) -> bool {
    r.rights & GRANT != 0 || r.rights & CONTROL != 0
}

/// Tenants `i` and `j` are joined, in either order.
pub open spec fn joined(joins: Seq<Join>, i: Tenant, j: Tenant) -> bool {
    exists|k: int|
        0 <= k < joins.len() && ((#[trigger] joins[k]).a == i && joins[k].b == j || joins[k].a == j && joins[k].b == i)
}

/// The held block at `h` is well formed.
pub open spec fn held_ok(held: Seq<Block>, h: int) -> bool {
    block_ok(held[h])
}

/// The row at `a` is well formed and lies inside a block the divider holds.
pub open spec fn row_ok(held: Seq<Block>, rows: Seq<Row>, a: int) -> bool {
    &&& block_ok(rows[a].block)
    &&& exists|h: int| 0 <= h < held.len() && within(rows[a].block, #[trigger] held[h])
}

/// The rows at `a` and `b` meet only as the layout declares.
pub open spec fn pair_ok(rows: Seq<Row>, joins: Seq<Join>, a: int, b: int) -> bool {
    let ra = rows[a];
    let rb = rows[b];
    let meet = ra.tenant != rb.tenant && intersect(ra.block, rb.block);
    &&& meet ==> ra.shared && rb.shared
    &&& meet && carries_authority(ra) ==> joined(joins, ra.tenant, rb.tenant)
    &&& a != b && ra.kind is Device ==> !intersect(ra.block, rb.block)
}

/// The layout divides what the divider holds as its rows say, meeting only as declared.
pub open spec fn layout_ok(held: Seq<Block>, rows: Seq<Row>, joins: Seq<Join>) -> bool {
    &&& forall|h: int| 0 <= h < held.len() ==> #[trigger] held_ok(held, h)
    &&& forall|a: int| 0 <= a < rows.len() ==> #[trigger] row_ok(held, rows, a)
    &&& forall|a: int, b: int| 0 <= a < rows.len() && 0 <= b < rows.len() ==> #[trigger] pair_ok(rows, joins, a, b)
}

/// The declared overlap D(i, j): the pairs of rows of tenants i and j whose blocks intersect.
pub open spec fn overlap(rows: Seq<Row>, i: Tenant, j: Tenant) -> ISet<(int, int)> {
    ISet::new(
        |p: (int, int)|
            0 <= p.0 < rows.len() && 0 <= p.1 < rows.len() && rows[p.0].tenant == i && rows[p.1].tenant == j
                && intersect(rows[p.0].block, rows[p.1].block),
    )
}

/// In a layout that passes, the declared overlap of two different tenants is of rows both mark
/// shared, and a row in it that carries authority has the two joined.
pub proof fn lemma_overlap_declared(held: Seq<Block>, rows: Seq<Row>, joins: Seq<Join>, i: Tenant, j: Tenant)
    requires
        layout_ok(held, rows, joins),
        i != j,
    ensures
        forall|p: (int, int)| #[trigger] overlap(rows, i, j).contains(p) ==> {
            &&& rows[p.0].shared && rows[p.1].shared
            &&& carries_authority(rows[p.0]) ==> joined(joins, i, j)
            &&& carries_authority(rows[p.1]) ==> joined(joins, j, i)
        },
{
    assert forall|p: (int, int)| #[trigger] overlap(rows, i, j).contains(p) implies {
        &&& rows[p.0].shared && rows[p.1].shared
        &&& carries_authority(rows[p.0]) ==> joined(joins, i, j)
        &&& carries_authority(rows[p.1]) ==> joined(joins, j, i)
    } by {
        assert(pair_ok(rows, joins, p.0, p.1));
        assert(pair_ok(rows, joins, p.1, p.0));
    }
}

/// A block of any order up to MAX_ORDER is at least a page and fits in memory, below 2^48.
proof fn lemma_bytes(order: u8)
    requires
        order <= MAX_ORDER,
    ensures
        PAGE_BYTES <= bytes(order) <= DEVICE_OBJECTS,
{
    lemma_pow2_pos(order as nat);
    lemma2_to64_rest();
    if order < MAX_ORDER {
        lemma_pow2_strictly_increases(order as nat, MAX_ORDER as nat);
    }
}

/// The size of a block of this order, in bytes.
fn bytes_of(order: u8) -> (r: u64)
    requires
        order <= MAX_ORDER,
    ensures
        r as int == bytes(order),
        PAGE_BYTES <= r <= DEVICE_OBJECTS,
{
    proof {
        lemma_bytes(order);
        lemma_u64_shl_is_mul(PAGE_BYTES, order as u64);
    }
    PAGE_BYTES << (order as u64)
}

/// Decides block_ok.
fn is_block_ok(b: Block) -> (r: bool)
    ensures
        r == block_ok(b),
{
    if b.order > MAX_ORDER {
        return false;
    }
    let size = bytes_of(b.order);
    b.base % size == 0 && b.base <= OBJECT_SPACE - size
}

/// The first byte past a well-formed block.
fn end_of(b: Block) -> (r: u64)
    requires
        block_ok(b),
    ensures
        r as int == end(b),
        r <= OBJECT_SPACE,
{
    b.base + bytes_of(b.order)
}

/// Decides whether a row's block lies inside a block the divider holds.
fn is_held(held: &[Block], b: Block) -> (r: bool)
    requires
        block_ok(b),
        forall|h: int| 0 <= h < held@.len() ==> #[trigger] held_ok(held@, h),
    ensures
        r == exists|h: int| 0 <= h < held@.len() && within(b, #[trigger] held@[h]),
{
    let mut h: usize = 0;
    while h < held.len()
        invariant
            h <= held@.len(),
            block_ok(b),
            forall|k: int| 0 <= k < held@.len() ==> #[trigger] held_ok(held@, k),
            forall|k: int| 0 <= k < h ==> !within(b, #[trigger] held@[k]),
        decreases held@.len() - h,
    {
        let hb = held[h];
        assert(held_ok(held@, h as int));
        if hb.base <= b.base && end_of(b) <= end_of(hb) {
            assert(within(b, held@[h as int]));
            return true;
        }
        h += 1;
    }
    false
}

/// Decides joined.
fn is_joined(joins: &[Join], i: Tenant, j: Tenant) -> (r: bool)
    ensures
        r == joined(joins@, i, j),
{
    let mut k: usize = 0;
    while k < joins.len()
        invariant
            k <= joins@.len(),
            forall|x: int|
                0 <= x < k ==> !((#[trigger] joins@[x]).a == i && joins@[x].b == j || joins@[x].a == j && joins@[x].b == i),
        decreases joins@.len() - k,
    {
        let join = joins[k];
        if join.a == i && join.b == j || join.a == j && join.b == i {
            assert(joins@[k as int] == join);
            return true;
        }
        k += 1;
    }
    false
}

/// Decides row_ok for the row at `a`.
fn is_row_ok(held: &[Block], rows: &[Row], a: usize) -> (r: bool)
    requires
        a < rows@.len(),
        forall|h: int| 0 <= h < held@.len() ==> #[trigger] held_ok(held@, h),
    ensures
        r == row_ok(held@, rows@, a as int),
{
    let row = rows[a];
    is_block_ok(row.block) && is_held(held, row.block)
}

/// Decides pair_ok for the rows at `a` and `b`, given that every row's block is well formed.
fn is_pair_ok(rows: &[Row], joins: &[Join], a: usize, b: usize) -> (r: bool)
    requires
        a < rows@.len(),
        b < rows@.len(),
        block_ok(rows@[a as int].block),
        block_ok(rows@[b as int].block),
    ensures
        r == pair_ok(rows@, joins@, a as int, b as int),
{
    let ra = rows[a];
    let rb = rows[b];
    let intersects = ra.block.base < end_of(rb.block) && rb.block.base < end_of(ra.block);
    let meet = ra.tenant != rb.tenant && intersects;
    if meet && !(ra.shared && rb.shared) {
        return false;
    }
    if meet && (ra.rights & GRANT != 0 || ra.rights & CONTROL != 0) && !is_joined(joins, ra.tenant, rb.tenant) {
        return false;
    }
    let device = match ra.kind {
        Kind::Device => true,
        _ => false,
    };
    !(a != b && device && intersects)
}

/// Decides layout_ok.
pub fn check(held: &[Block], rows: &[Row], joins: &[Join]) -> (ok: bool)
    ensures
        ok == layout_ok(held@, rows@, joins@),
{
    let mut h: usize = 0;
    while h < held.len()
        invariant
            h <= held@.len(),
            forall|k: int| 0 <= k < h ==> #[trigger] held_ok(held@, k),
        decreases held@.len() - h,
    {
        if !is_block_ok(held[h]) {
            assert(!held_ok(held@, h as int));
            return false;
        }
        h += 1;
    }
    let mut a: usize = 0;
    while a < rows.len()
        invariant
            a <= rows@.len(),
            forall|k: int| 0 <= k < held@.len() ==> #[trigger] held_ok(held@, k),
            forall|k: int| 0 <= k < a ==> #[trigger] row_ok(held@, rows@, k),
        decreases rows@.len() - a,
    {
        if !is_row_ok(held, rows, a) {
            return false;
        }
        a += 1;
    }
    let mut a: usize = 0;
    while a < rows.len()
        invariant
            a <= rows@.len(),
            forall|k: int| 0 <= k < held@.len() ==> #[trigger] held_ok(held@, k),
            forall|k: int| 0 <= k < rows@.len() ==> #[trigger] row_ok(held@, rows@, k),
            forall|x: int, y: int| 0 <= x < a && 0 <= y < rows@.len() ==> #[trigger] pair_ok(rows@, joins@, x, y),
        decreases rows@.len() - a,
    {
        let mut b: usize = 0;
        assert(row_ok(held@, rows@, a as int));
        while b < rows.len()
            invariant
                a < rows@.len(),
                b <= rows@.len(),
                forall|k: int| 0 <= k < rows@.len() ==> #[trigger] row_ok(held@, rows@, k),
                forall|x: int, y: int| 0 <= x < a && 0 <= y < rows@.len() ==> #[trigger] pair_ok(rows@, joins@, x, y),
                forall|y: int| 0 <= y < b ==> #[trigger] pair_ok(rows@, joins@, a as int, y),
            decreases rows@.len() - b,
        {
            assert(row_ok(held@, rows@, a as int) && row_ok(held@, rows@, b as int));
            if !is_pair_ok(rows, joins, a, b) {
                return false;
            }
            b += 1;
        }
        a += 1;
    }
    true
}

// The examples. Tenants 1 and 2 divide the gigabyte from 1 GiB, which the divider holds as one
// untyped, as boot gives dom0 today.

pub open spec fn gigabyte() -> Block {
    Block { base: 0x4000_0000, order: 18 }
}

pub open spec fn example_held() -> Seq<Block> {
    seq![gigabyte()]
}

/// Each tenant has 2 MiB of untyped of its own, and both have the frame at 1 GiB + 4 MiB: tenant 1
/// to read and write it, tenant 2 to read it. `shared` says whether tenant 2's row declares it.
pub open spec fn frame_rows(shared: bool) -> Seq<Row> {
    seq![
        Row { tenant: 1, kind: Kind::Untyped, block: Block { base: 0x4000_0000, order: 9 }, rights: RETYPE, shared: false },
        Row { tenant: 2, kind: Kind::Untyped, block: Block { base: 0x4020_0000, order: 9 }, rights: RETYPE, shared: false },
        Row { tenant: 1, kind: Kind::Frame, block: Block { base: 0x4040_0000, order: 0 }, rights: READ | WRITE, shared: true },
        Row { tenant: 2, kind: Kind::Frame, block: Block { base: 0x4040_0000, order: 0 }, rights: READ, shared: shared },
    ]
}

/// Both tenants hold the endpoint at 1 GiB + 6 MiB, declared shared: tenant 1 to send with the grant
/// right, tenant 2 to receive.
pub open spec fn endpoint_rows() -> Seq<Row> {
    seq![
        Row { tenant: 1, kind: Kind::Endpoint, block: Block { base: 0x4060_0000, order: 0 }, rights: SEND | GRANT, shared: true },
        Row { tenant: 2, kind: Kind::Endpoint, block: Block { base: 0x4060_0000, order: 0 }, rights: RECEIVE, shared: true },
    ]
}

/// The join of tenants 1 and 2, written in the other order.
pub open spec fn example_joins() -> Seq<Join> {
    seq![Join { a: 2, b: 1 }]
}

/// The divider's one held block is well formed.
proof fn lemma_example_held()
    ensures
        held_ok(example_held(), 0),
        bytes(0) == PAGE_BYTES,
        bytes(9) == 0x20_0000,
        bytes(18) == 0x4000_0000,
{
    lemma2_to64();
    assert(example_held()[0] == gigabyte());
    assert(0x4000_0000int % 0x4000_0000int == 0);
}

/// A declared shared frame passes.
pub proof fn example_shared_frame_passes()
    ensures
        layout_ok(example_held(), frame_rows(true), Seq::empty()),
{
    let held = example_held();
    let rows = frame_rows(true);
    lemma_example_held();
    assert forall|a: int| 0 <= a < rows.len() implies #[trigger] row_ok(held, rows, a) by {
        assert(within(rows[a].block, held[0]));
    }
    assert forall|a: int, b: int| 0 <= a < rows.len() && 0 <= b < rows.len() implies #[trigger] pair_ok(
        rows,
        Seq::empty(),
        a,
        b,
    ) by {
        assert(READ & GRANT == 0 && READ & CONTROL == 0) by (bit_vector);
        assert((READ | WRITE) & GRANT == 0 && (READ | WRITE) & CONTROL == 0) by (bit_vector);
        assert(RETYPE & GRANT == 0 && RETYPE & CONTROL == 0) by (bit_vector);
    }
}

/// The same frame, intersecting without tenant 2's declaring it, fails.
pub proof fn example_undeclared_frame_fails()
    ensures
        !layout_ok(example_held(), frame_rows(false), Seq::empty()),
{
    lemma2_to64();
    assert(!pair_ok(frame_rows(false), Seq::empty(), 2, 3));
}

/// A shared endpoint one tenant holds with the grant right fails while the two are not joined.
pub proof fn example_grant_unjoined_fails()
    ensures
        !layout_ok(example_held(), endpoint_rows(), Seq::empty()),
{
    lemma2_to64();
    assert((SEND | GRANT) & GRANT != 0) by (bit_vector);
    assert(!pair_ok(endpoint_rows(), Seq::empty(), 0, 1));
}

/// The same endpoint passes once the two are joined.
pub proof fn example_grant_joined_passes()
    ensures
        layout_ok(example_held(), endpoint_rows(), example_joins()),
{
    let held = example_held();
    let rows = endpoint_rows();
    let joins = example_joins();
    lemma_example_held();
    assert forall|a: int| 0 <= a < rows.len() implies #[trigger] row_ok(held, rows, a) by {
        assert(within(rows[a].block, held[0]));
    }
    assert(joined(joins, 1, 2)) by {
        assert(joins[0].a == 2 && joins[0].b == 1);
    }
    assert(joined(joins, 2, 1)) by {
        assert(joins[0].a == 2 && joins[0].b == 1);
    }
    assert forall|a: int, b: int| 0 <= a < rows.len() && 0 <= b < rows.len() implies #[trigger] pair_ok(
        rows,
        joins,
        a,
        b,
    ) by {
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    const HELD: [Block; 1] = [Block { base: 0x4000_0000, order: 18 }];

    fn frame_rows(shared: bool) -> [Row; 4] {
        [
            Row { tenant: 1, kind: Kind::Untyped, block: Block { base: 0x4000_0000, order: 9 }, rights: RETYPE, shared: false },
            Row { tenant: 2, kind: Kind::Untyped, block: Block { base: 0x4020_0000, order: 9 }, rights: RETYPE, shared: false },
            Row { tenant: 1, kind: Kind::Frame, block: Block { base: 0x4040_0000, order: 0 }, rights: READ | WRITE, shared: true },
            Row { tenant: 2, kind: Kind::Frame, block: Block { base: 0x4040_0000, order: 0 }, rights: READ, shared },
        ]
    }

    const ENDPOINT_ROWS: [Row; 2] = [
        Row { tenant: 1, kind: Kind::Endpoint, block: Block { base: 0x4060_0000, order: 0 }, rights: SEND | GRANT, shared: true },
        Row { tenant: 2, kind: Kind::Endpoint, block: Block { base: 0x4060_0000, order: 0 }, rights: RECEIVE, shared: true },
    ];

    const JOINS: [Join; 1] = [Join { a: 2, b: 1 }];

    #[test]
    fn shared_frame_passes() {
        assert!(check(&HELD, &frame_rows(true), &[]));
    }

    #[test]
    fn undeclared_frame_fails() {
        assert!(!check(&HELD, &frame_rows(false), &[]));
    }

    #[test]
    fn grant_unjoined_fails() {
        assert!(!check(&HELD, &ENDPOINT_ROWS, &[]));
    }

    #[test]
    fn grant_joined_passes() {
        assert!(check(&HELD, &ENDPOINT_ROWS, &JOINS));
    }

    #[test]
    fn control_unjoined_fails() {
        let mut rows = ENDPOINT_ROWS;
        rows[0].rights = SEND | CONTROL;
        assert!(!check(&HELD, &rows, &[]));
    }

    #[test]
    fn grant_within_one_tenant_passes() {
        let mut rows = ENDPOINT_ROWS;
        rows[1].tenant = 1;
        assert!(check(&HELD, &rows, &[]));
    }

    #[test]
    fn row_outside_held_fails() {
        let mut rows = frame_rows(true);
        rows[0].block.base = 0x8000_0000;
        assert!(!check(&HELD, &rows, &[]));
    }

    #[test]
    fn misaligned_row_fails() {
        let mut rows = frame_rows(true);
        rows[0].block.base = 0x4000_1000;
        assert!(!check(&HELD, &rows, &[]));
    }

    #[test]
    fn misaligned_held_fails() {
        assert!(!check(&[Block { base: 0x4000_1000, order: 18 }], &[], &[]));
    }

    #[test]
    fn order_past_max_fails() {
        assert!(!check(&[Block { base: 0, order: MAX_ORDER + 1 }], &[], &[]));
    }

    #[test]
    fn block_past_object_space_fails() {
        assert!(!check(&[Block { base: OBJECT_SPACE, order: 0 }], &[], &[]));
    }

    #[test]
    fn device_in_two_rows_fails() {
        let held = [Block { base: DEVICE_OBJECTS, order: 0 }];
        let device = Row { tenant: 1, kind: Kind::Device, block: Block { base: DEVICE_OBJECTS, order: 0 }, rights: 0, shared: true };
        assert!(check(&held, &[device], &[]));
        assert!(!check(&held, &[device, device], &[]));
        assert!(!check(&held, &[device, Row { tenant: 2, ..device }], &[]));
    }

    #[test]
    fn kinds_are_numbered_as_asys_numbers_them() {
        use asys::operation::*;
        assert_eq!(Kind::Untyped as u64, KIND_UNTYPED);
        assert_eq!(Kind::Frame as u64, KIND_FRAME);
        assert_eq!(Kind::Process as u64, KIND_PROCESS);
        assert_eq!(Kind::Thread as u64, KIND_THREAD);
        assert_eq!(Kind::Endpoint as u64, KIND_ENDPOINT);
        assert_eq!(Kind::Reply as u64, KIND_REPLY);
        assert_eq!(Kind::Notification as u64, KIND_NOTIFICATION);
        assert_eq!(Kind::Space as u64, KIND_SPACE);
        assert_eq!(Kind::Device as u64, KIND_DEVICE);
        assert_eq!(Kind::Console as u64, KIND_CONSOLE);
        assert_eq!(Kind::Power as u64, KIND_POWER);
    }
}
