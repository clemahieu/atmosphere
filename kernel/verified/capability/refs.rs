//! References: each frame capability holds one on the block it lies in, and a block is dead at once when
//! they reach zero. A ghost set of each block's holding nodes makes the count exact, which is what lets
//! a free say no capability is left behind. See the design on atmo-6x9.6.7, section 6.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::table::*;
use crate::capability::zero::*;
use crate::define::*;

/// A typed block: a small block by its base page, or a large one by its region.
#[derive(Clone, Copy)]
pub enum BlockRef {
    Small(usize),
    Two(usize),
    One(usize),
}

/// The block page i lies in. A large block's pages are free in the page table, so the regions come first.
pub open spec fn block_ref(blocks: &BlockTable, i: usize) -> BlockRef {
    if blocks.regions_2m@[(i / PAGES_PER_2M) as int].typed {
        BlockRef::Two(i / PAGES_PER_2M)
    } else if blocks.regions_1g@[(i / PAGES_PER_1G) as int].typed {
        BlockRef::One(i / PAGES_PER_1G)
    } else if blocks.pages@[i as int].kind is Member {
        BlockRef::Small(blocks.pages@[i as int].base)
    } else {
        BlockRef::Small(i)
    }
}

/// br is a block the table has typed.
pub open spec fn block_typed(blocks: &BlockTable, br: BlockRef) -> bool {
    match br {
        BlockRef::Small(b) => b < NUM_PAGES && blocks.pages@[b as int].kind is Base,
        BlockRef::Two(r) => r < NUM_2M && blocks.regions_2m@[r as int].typed,
        BlockRef::One(r) => r < NUM_1G && blocks.regions_1g@[r as int].typed,
    }
}

pub open spec fn block_refs(blocks: &BlockTable, br: BlockRef) -> usize {
    match br {
        BlockRef::Small(b) => blocks.pages@[b as int].refs,
        BlockRef::Two(r) => blocks.regions_2m@[r as int].refs,
        BlockRef::One(r) => blocks.regions_1g@[r as int].refs,
    }
}

pub open spec fn block_dead(blocks: &BlockTable, br: BlockRef) -> bool {
    match br {
        BlockRef::Small(b) => blocks.pages@[b as int].dead,
        BlockRef::Two(r) => blocks.regions_2m@[r as int].dead,
        BlockRef::One(r) => blocks.regions_1g@[r as int].dead,
    }
}

/// The block that is region r of this level.
pub open spec fn level_ref(level: Large, r: usize) -> BlockRef {
    match level {
        Large::Two => BlockRef::Two(r),
        Large::One => BlockRef::One(r),
    }
}

/// A frame's whole range lies in its block: a small frame is one page, and a narrowed piece of a large
/// frame stays inside the region. So a child has its parent's block.
pub open spec fn frame_in_block(br: BlockRef, p: Payload) -> bool {
    match br {
        BlockRef::Small(b) => p.order == 0 && p.base == b * 4096,
        BlockRef::Two(r) => r * 0x200000 <= p.base && p.base as int + block_bytes(p.order) <= (r + 1) * 0x200000,
        BlockRef::One(r) => r * 0x40000000 <= p.base && p.base as int + block_bytes(p.order) <= (r + 1) * 0x40000000,
    }
}

/// A block being zeroed is not a holders' key.
pub open spec fn block_active(zeroing: &Zeroing, br: BlockRef) -> bool {
    match br {
        BlockRef::Two(r) => zeroing.active_2m@[r as int],
        BlockRef::One(r) => zeroing.active_1g@[r as int],
        BlockRef::Small(b) => false,
    }
}

/// Every frame capability is a holder of the block it lies in, and each block's holders are exactly its
/// references, so a block at zero has no frame capability. A block being zeroed has no capability yet:
/// it holds the one reference retype will hand to its capability.
pub open spec fn holders_wf(
    list: &Tree,
    tables: &Tables,
    blocks: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
) -> bool {
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Frame ==> {
        let i = tables.payload_of(n).base / 4096;
        &&& i < NUM_PAGES
        &&& frame_in_block(block_ref(blocks, i), tables.payload_of(n))
        &&& holders.contains_key(block_ref(blocks, i))
        &&& holders[block_ref(blocks, i)].contains(n)
    }
    &&& forall|br: BlockRef| #[trigger] holders.contains_key(br) ==> {
        &&& holders[br].finite()
        &&& holders[br].len() == block_refs(blocks, br)
        &&& block_typed(blocks, br)
        &&& block_refs(blocks, br) == 0 ==> block_dead(blocks, br)
        &&& !block_active(zeroing, br)
    }
    &&& forall|br: BlockRef, n: usize| holders.contains_key(br) && #[trigger] holders[br].contains(n) ==> {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Frame
        &&& tables.payload_of(n).base / 4096 < NUM_PAGES
        &&& block_ref(blocks, tables.payload_of(n).base / 4096) == br
    }
    &&& forall|r: int| 0 <= r < NUM_2M && #[trigger] zeroing.active_2m@[r] ==> {
        &&& blocks.regions_2m@[r].typed
        &&& blocks.regions_2m@[r].refs == 1
    }
    &&& forall|r: int| 0 <= r < NUM_1G && #[trigger] zeroing.active_1g@[r] ==> {
        &&& blocks.regions_1g@[r].typed
        &&& blocks.regions_1g@[r].refs == 1
    }
}

/// A block with a holder entry is of type frame, and a leaf's block is of type table leaf, so a retype
/// naming a block can dispatch on what it reads there. A frame's small block is one page, and at zero
/// references it has a holder entry, since only its last holder's going takes it there.
pub open spec fn objects_wf(tables: &Tables, blocks: &BlockTable, holders: IMap<BlockRef, Set<usize>>) -> bool {
    &&& forall|b: usize| #[trigger] holders.contains_key(BlockRef::Small(b))
        ==> blocks.pages@[b as int].object is Frame
    &&& forall|b: usize| b < NUM_PAGES && (#[trigger] blocks.pages@[b as int]).kind is Base
        && blocks.pages@[b as int].object is Frame ==> {
        &&& blocks.pages@[b as int].order == 0
        &&& blocks.pages@[b as int].refs == 0 ==> holders.contains_key(BlockRef::Small(b))
    }
    &&& forall|l: usize| #[trigger] tables.owner@.contains_key(l) ==> {
        &&& l / 4096 < NUM_PAGES
        &&& blocks.pages@[(l / 4096) as int].kind is Base
        &&& blocks.pages@[(l / 4096) as int].object is TableLeaf
    }
    &&& forall|r: usize| r < NUM_2M && (#[trigger] blocks.regions_2m@[r as int]).typed
        && blocks.regions_2m@[r as int].refs == 0 ==> holders.contains_key(BlockRef::Two(r))
    &&& forall|r: usize| r < NUM_1G && (#[trigger] blocks.regions_1g@[r as int]).typed
        && blocks.regions_1g@[r as int].refs == 0 ==> holders.contains_key(BlockRef::One(r))
}

/// Page i is a page of this block. A small block with a holder is a one-page frame.
pub open spec fn block_has_page(br: BlockRef, i: usize) -> bool {
    match br {
        BlockRef::Small(b) => i == b,
        BlockRef::Two(r) => r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M,
        BlockRef::One(r) => r * PAGES_PER_1G <= i < (r + 1) * PAGES_PER_1G,
    }
}

/// The kernel holds the permission of every page of a block with a holder entry, so freeing it can
/// hand them back.
pub open spec fn frames_held(frames: Map<usize, PagePerm4k>, holders: IMap<BlockRef, Set<usize>>) -> bool {
    forall|br: BlockRef, i: usize| #[trigger] holders.contains_key(br) && #[trigger] block_has_page(br, i)
        ==> frames.contains_key(i)
}

/// A step that changes one block's count keeps the types: the count's own block keeps its entry, and any
/// other's count is as it was.
pub proof fn lemma_objects_refs_changed(
    tables: &Tables,
    a: &BlockTable,
    b: &BlockTable,
    ha: IMap<BlockRef, Set<usize>>,
    hb: IMap<BlockRef, Set<usize>>,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        objects_wf(tables, a, ha),
        blocks_refs_changed(a, b, br, refs, dead),
        forall|x: BlockRef| #[trigger] hb.contains_key(x) == ha.contains_key(x),
        hb.contains_key(br),
        forall|x: BlockRef| #[trigger] ha.contains_key(x) ==> block_typed(a, x),
    ensures
        objects_wf(tables, b, hb),
{
    assert forall|x: usize| #[trigger] hb.contains_key(BlockRef::Small(x)) implies b.pages@[x as int].object is Frame by {
        assert(ha.contains_key(BlockRef::Small(x)));
        assert(block_typed(a, BlockRef::Small(x)));
        assert(b.pages@[x as int].object == a.pages@[x as int].object);
    }
    assert forall|x: usize| x < NUM_PAGES && (#[trigger] b.pages@[x as int]).kind is Base
        && b.pages@[x as int].object is Frame implies {
        &&& b.pages@[x as int].order == 0
        &&& b.pages@[x as int].refs == 0 ==> hb.contains_key(BlockRef::Small(x))
    } by {
        assert(a.pages@[x as int].kind is Base);
        assert(a.pages@[x as int].object is Frame);
        assert(a.pages@[x as int].order == 0);
        assert(block_typed(a, BlockRef::Small(x)));
        if BlockRef::Small(x) != br {
            assert(block_refs(b, BlockRef::Small(x)) == block_refs(a, BlockRef::Small(x)));
        }
    }
    assert forall|l: usize| #[trigger] tables.owner@.contains_key(l) implies {
        &&& l / 4096 < NUM_PAGES
        &&& b.pages@[(l / 4096) as int].kind is Base
        &&& b.pages@[(l / 4096) as int].object is TableLeaf
    } by {
        assert(b.pages@[(l / 4096) as int].kind == a.pages@[(l / 4096) as int].kind);
        assert(b.pages@[(l / 4096) as int].object == a.pages@[(l / 4096) as int].object);
    }
    assert forall|r: usize| r < NUM_2M && (#[trigger] b.regions_2m@[r as int]).typed
        && b.regions_2m@[r as int].refs == 0 implies hb.contains_key(BlockRef::Two(r)) by {
        assert(block_typed(a, BlockRef::Two(r)));
        if BlockRef::Two(r) != br {
            assert(block_refs(b, BlockRef::Two(r)) == block_refs(a, BlockRef::Two(r)));
        }
    }
    assert forall|r: usize| r < NUM_1G && (#[trigger] b.regions_1g@[r as int]).typed
        && b.regions_1g@[r as int].refs == 0 implies hb.contains_key(BlockRef::One(r)) by {
        assert(block_typed(a, BlockRef::One(r)));
        if BlockRef::One(r) != br {
            assert(block_refs(b, BlockRef::One(r)) == block_refs(a, BlockRef::One(r)));
        }
    }
}

/// A typed large block shares no page with any other block: nothing else is typed inside it or around
/// it. So taking its pages' permissions leaves every other block's alone.
pub proof fn lemma_large_block_alone(blocks: &BlockTable, level: Large, r: usize, x: BlockRef, i: usize)
    requires
        blocks.wf(),
        r < level_regions(level),
        block_typed(blocks, level_ref(level, r)),
        block_typed(blocks, x),
        x != level_ref(level, r),
        block_has_page(level_ref(level, r), i),
        block_has_page(x, i),
    ensures
        false,
{
    assert(i < NUM_PAGES);
    match level {
        Large::Two => {
            assert(region_2m(i as int) == r as int);
            blocks.lemma_zero_2m_is_free(r as int, i as int);
            match x {
                BlockRef::Small(b) => {
                    assert(blocks.pages@[b as int].kind is Base);
                },
                BlockRef::Two(q) => {
                    assert(q == r);
                },
                BlockRef::One(q) => {
                    lemma_region_of_region(i as int);
                    assert((r / 512) as int == q as int);
                    assert(!blocks.regions_1g@[(r as int) / 512].typed);
                },
            }
        },
        Large::One => {
            assert(region_1g(i as int) == r as int);
            blocks.lemma_zero_1g_is_free(r as int, i as int);
            match x {
                BlockRef::Small(b) => {
                    assert(blocks.pages@[b as int].kind is Base);
                },
                BlockRef::Two(q) => {
                    lemma_region_of_region(i as int);
                    assert((q / 512) as int == r as int);
                    assert(!blocks.regions_1g@[(q as int) / 512].typed);
                },
                BlockRef::One(q) => {
                    assert(q == r);
                },
            }
        },
    }
}

/// Typing a free small block keeps the types: nothing with a holder entry or an owner was free.
pub proof fn lemma_objects_small_typed(
    tables: &Tables,
    a: &BlockTable,
    b: &BlockTable,
    holders: IMap<BlockRef, Set<usize>>,
    base: usize,
    size: int,
)
    requires
        objects_wf(tables, a, holders),
        forall|br: BlockRef| #[trigger] holders.contains_key(br) ==> block_typed(a, br),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
        forall|k: int| 0 < k < size ==> (#[trigger] b.pages@[base + k]).kind is Member,
        b.pages@[base as int].object is Frame ==> b.pages@[base as int].order == 0,
        b.pages@[base as int].refs == 1,
        b.regions_2m@ == a.regions_2m@,
        b.regions_1g@ == a.regions_1g@,
    ensures
        objects_wf(tables, b, holders),
{
    assert forall|x: usize| #[trigger] holders.contains_key(BlockRef::Small(x)) implies b.pages@[x as int].object is Frame by {
        assert(block_typed(a, BlockRef::Small(x)));
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
    }
    assert forall|x: usize| x < NUM_PAGES && (#[trigger] b.pages@[x as int]).kind is Base
        && b.pages@[x as int].object is Frame implies {
        &&& b.pages@[x as int].order == 0
        &&& b.pages@[x as int].refs == 0 ==> holders.contains_key(BlockRef::Small(x))
    } by {
        if base < x < base + size {
            assert(b.pages@[base + (x - base)].kind is Member);
        } else if x != base {
            assert(a.pages@[x as int] == b.pages@[x as int]);
        }
    }
    assert forall|l: usize| #[trigger] tables.owner@.contains_key(l) implies {
        &&& l / 4096 < NUM_PAGES
        &&& b.pages@[(l / 4096) as int].kind is Base
        &&& b.pages@[(l / 4096) as int].object is TableLeaf
    } by {
        let x = (l / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
    }
}

/// Finds the block page i lies in, in constant time.
pub fn locate(blocks: &BlockTable, i: usize) -> (ret: BlockRef)
    requires
        blocks.wf(),
        i < NUM_PAGES,
    ensures
        ret == block_ref(blocks, i),
{
    if blocks.regions_2m.get(i / PAGES_PER_2M).typed {
        BlockRef::Two(i / PAGES_PER_2M)
    } else if blocks.regions_1g.get(i / PAGES_PER_1G).typed {
        BlockRef::One(i / PAGES_PER_1G)
    } else {
        let entry = blocks.pages.get(i);
        match entry.kind {
            PageKind::Member => BlockRef::Small(entry.base),
            _ => BlockRef::Small(i),
        }
    }
}

/// Takes one more reference on a block, unless the count is full.
pub fn add_block_ref(blocks: &mut BlockTable, br: BlockRef) -> (added: bool)
    requires
        old(blocks).wf(),
        block_typed(old(blocks), br),
    ensures
        final(blocks).wf(),
        added == (block_refs(old(blocks), br) != usize::MAX),
        !added ==> *final(blocks) == *old(blocks),
        added ==> blocks_refs_changed(old(blocks), final(blocks), br, (block_refs(old(blocks), br) + 1) as usize, block_dead(old(blocks), br)),
{
    let ghost pre = *old(blocks);
    let added = match br {
        BlockRef::Small(b) => blocks.add_ref(b),
        BlockRef::Two(r) => blocks.add_large_ref(Large::Two, r),
        BlockRef::One(r) => blocks.add_large_ref(Large::One, r),
    };
    proof {
        if added {
            lemma_same_structure(&pre, blocks);
        }
    }
    added
}

/// Drops one reference on a block, which is dead at once if that was the last.
pub fn drop_block_ref(blocks: &mut BlockTable, br: BlockRef)
    requires
        old(blocks).wf(),
        block_typed(old(blocks), br),
        block_refs(old(blocks), br) > 0,
    ensures
        final(blocks).wf(),
        blocks_refs_changed(
            old(blocks),
            final(blocks),
            br,
            (block_refs(old(blocks), br) - 1) as usize,
            block_dead(old(blocks), br) || block_refs(old(blocks), br) == 1,
        ),
{
    let ghost pre = *old(blocks);
    match br {
        BlockRef::Small(b) => {
            blocks.drop_ref(b);
            if blocks.pages.get(b).refs == 0 {
                blocks.mark_dead(b);
            }
        },
        BlockRef::Two(r) => {
            blocks.drop_large_ref(Large::Two, r);
            if blocks.regions_2m.get(r).refs == 0 {
                blocks.mark_large_dead(Large::Two, r);
            }
        },
        BlockRef::One(r) => {
            blocks.drop_large_ref(Large::One, r);
            if blocks.regions_1g.get(r).refs == 0 {
                blocks.mark_large_dead(Large::One, r);
            }
        },
    }
    proof {
        lemma_same_structure(&pre, blocks);
    }
}

/// Only br's count and dead flag differ between a and b, so every page's block is as it was.
pub open spec fn blocks_refs_changed(a: &BlockTable, b: &BlockTable, br: BlockRef, refs: usize, dead: bool) -> bool {
    &&& block_refs(b, br) == refs
    &&& block_dead(b, br) == dead
    &&& forall|i: usize| i < NUM_PAGES ==> #[trigger] block_ref(b, i) == block_ref(a, i)
    &&& forall|x: BlockRef| #[trigger] block_typed(b, x) == block_typed(a, x)
    &&& forall|x: BlockRef| block_typed(a, x) && x != br ==> #[trigger] block_refs(b, x) == block_refs(a, x)
    &&& forall|x: BlockRef| block_typed(a, x) && x != br ==> #[trigger] block_dead(b, x) == block_dead(a, x)
    &&& forall|i: int| 0 <= i < NUM_PAGES ==> {
        &&& (#[trigger] b.pages@[i]).kind == a.pages@[i].kind
        &&& b.pages@[i].object == a.pages@[i].object
        &&& b.pages@[i].order == a.pages@[i].order
    }
    &&& forall|x: int| 0 <= x < NUM_2M ==> (#[trigger] b.regions_2m@[x]).typed == a.regions_2m@[x].typed
    &&& forall|x: int| 0 <= x < NUM_1G ==> (#[trigger] b.regions_1g@[x]).typed == a.regions_1g@[x].typed
}

/// Tables with the same page kinds, member bases and typed regions put every page in the same block and
/// have typed the same blocks.
pub proof fn lemma_same_structure(a: &BlockTable, b: &BlockTable)
    requires
        forall|i: int| 0 <= i < NUM_PAGES ==> {
            &&& (#[trigger] b.pages@[i]).kind == a.pages@[i].kind
            &&& b.pages@[i].base == a.pages@[i].base
        },
        forall|x: int| 0 <= x < NUM_2M ==> (#[trigger] b.regions_2m@[x]).typed == a.regions_2m@[x].typed,
        forall|x: int| 0 <= x < NUM_1G ==> (#[trigger] b.regions_1g@[x]).typed == a.regions_1g@[x].typed,
    ensures
        forall|i: usize| i < NUM_PAGES ==> #[trigger] block_ref(b, i) == block_ref(a, i),
        forall|x: BlockRef| #[trigger] block_typed(b, x) == block_typed(a, x),
{
    assert forall|i: usize| i < NUM_PAGES implies #[trigger] block_ref(b, i) == block_ref(a, i) by {
        assert(i / PAGES_PER_2M < NUM_2M);
        assert(i / PAGES_PER_1G < NUM_1G);
    }
}

/// The 2M region of a byte address, from the region's bounds.
pub proof fn lemma_region_2m_of_bytes(addr: int, r: usize)
    requires
        r < NUM_2M,
        r * 0x200000 <= addr < (r + 1) * 0x200000,
    ensures
        0 <= addr / 4096 < NUM_PAGES,
        (addr / 4096) / PAGES_PER_2M as int == r,
{
    lemma_fundamental_div_mod(addr, 4096);
    let p = addr / 4096;
    assert(r * 512 <= p < (r + 1) * 512);
    lemma_fundamental_div_mod_converse(p, 512, r as int, p - r * 512);
}

/// The 1G region of a byte address, from the region's bounds.
pub proof fn lemma_region_1g_of_bytes(addr: int, r: usize)
    requires
        r < NUM_1G,
        r * 0x40000000 <= addr < (r + 1) * 0x40000000,
    ensures
        0 <= addr / 4096 < NUM_PAGES,
        (addr / 4096) / PAGES_PER_1G as int == r,
{
    lemma_fundamental_div_mod(addr, 4096);
    let p = addr / 4096;
    assert(r * 262144 <= p < (r + 1) * 262144);
    lemma_fundamental_div_mod_converse(p, 262144, r as int, p - r * 262144);
}

/// A page's 1G region is its 2M region's.
pub proof fn lemma_region_of_region(i: int)
    requires
        0 <= i,
    ensures
        (i / PAGES_PER_2M as int) / 512 == i / PAGES_PER_1G as int,
{
    lemma_fundamental_div_mod(i, 512);
    let p = i / 512;
    lemma_fundamental_div_mod(p, 512);
    let q = p / 512;
    assert(i == q * 262144 + ((p % 512) * 512 + i % 512));
    lemma_fundamental_div_mod_converse(i, 262144, q, (p % 512) * 512 + i % 512);
}

/// A page inside a typed 1G region is in no typed 2M region, so its block is the 1G one.
pub proof fn lemma_in_1g_block(blocks: &BlockTable, i: usize, r: usize)
    requires
        blocks.wf(),
        i < NUM_PAGES,
        r < NUM_1G,
        i / PAGES_PER_1G == r,
        blocks.regions_1g@[r as int].typed,
    ensures
        block_ref(blocks, i) == BlockRef::One(r),
{
    let r2 = i / PAGES_PER_2M;
    lemma_region_of_region(i as int);
    assert(r2 / 512 == r);
    if blocks.regions_2m@[r2 as int].typed {
        assert(!blocks.regions_1g@[(r2 / 512) as int].typed);
    }
}

/// A frame's payload lies in the block of its first page: the page it starts on and the block_ref read
/// from there name the same block. Its child, inside its range, has that block too.
pub proof fn lemma_child_same_block(blocks: &BlockTable, parent: Payload, child: Payload)
    requires
        blocks.wf(),
        frame_in_block(block_ref(blocks, parent.base / 4096), parent),
        parent.base / 4096 < NUM_PAGES,
        block_typed(blocks, block_ref(blocks, parent.base / 4096)),
        child.order <= parent.order,
        parent.base <= child.base,
        child.base as int % block_bytes(child.order) == 0,
        child.base as int + block_bytes(child.order) <= parent.base as int + block_bytes(parent.order),
    ensures
        child.base / 4096 < NUM_PAGES,
        block_ref(blocks, child.base / 4096) == block_ref(blocks, parent.base / 4096),
        frame_in_block(block_ref(blocks, parent.base / 4096), child),
{
    let pb = parent.base / 4096;
    let cb = child.base / 4096;
    lemma_pow2_pos(child.order as nat);
    match block_ref(blocks, pb) {
        BlockRef::Small(b) => {
            lemma2_to64();
            assert(child.order == 0);
            assert(block_bytes(0) == 4096);
            assert(child.base == parent.base);
        },
        BlockRef::Two(r) => {
            lemma_region_2m_of_bytes(child.base as int, r);
            assert(cb / PAGES_PER_2M == r);
        },
        BlockRef::One(r) => {
            lemma_region_1g_of_bytes(child.base as int, r);
            assert(cb / PAGES_PER_1G == r);
            lemma_in_1g_block(blocks, cb, r);
        },
    }
}

/// A holder's block has a reference, since its holders are not empty.
pub proof fn lemma_holder_refs(
    list: &Tree,
    tables: &Tables,
    blocks: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    n: usize,
)
    requires
        holders_wf(list, tables, blocks, zeroing, holders),
        tables.is_cap(list, n),
        tables.payload_of(n).kind is Frame,
    ensures
        tables.payload_of(n).base / 4096 < NUM_PAGES,
        holders.contains_key(block_ref(blocks, tables.payload_of(n).base / 4096)),
        block_typed(blocks, block_ref(blocks, tables.payload_of(n).base / 4096)),
        block_refs(blocks, block_ref(blocks, tables.payload_of(n).base / 4096)) > 0,
{
    let br = block_ref(blocks, tables.payload_of(n).base / 4096);
    assert(holders[br].contains(n));
    if holders[br].len() == 0 {
        holders[br].lemma_len0_is_empty();
    }
}

/// The frame capabilities of a and b are the same, saying the same.
pub open spec fn same_frames(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    &&& forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Frame ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
    &&& forall|x: usize| #[trigger] tables_a.is_cap(list_a, x) && tables_a.payload_of(x).kind is Frame ==> {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x) == tables_a.payload_of(x)
    }
}

/// The holders read nothing of the capabilities but the frames.
pub proof fn lemma_holders_same_frames(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    blocks: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
)
    requires
        holders_wf(list_a, tables_a, blocks, zeroing, holders),
        same_frames(list_a, tables_a, list_b, tables_b),
    ensures
        holders_wf(list_b, tables_b, blocks, zeroing, holders),
{
    assert forall|br: BlockRef, n: usize| holders.contains_key(br) && #[trigger] holders[br].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Frame
        &&& tables_b.payload_of(n).base / 4096 < NUM_PAGES
        &&& block_ref(blocks, tables_b.payload_of(n).base / 4096) == br
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// The holders read nothing of the zeroing table but which regions are active.
pub proof fn lemma_holders_same_active(
    list: &Tree,
    tables: &Tables,
    blocks: &BlockTable,
    zeroing_a: &Zeroing,
    zeroing_b: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
)
    requires
        holders_wf(list, tables, blocks, zeroing_a, holders),
        zeroing_b.active_2m@ == zeroing_a.active_2m@,
        zeroing_b.active_1g@ == zeroing_a.active_1g@,
    ensures
        holders_wf(list, tables, blocks, zeroing_b, holders),
{
}

/// The holders after frame capability n, the only capability that changed, joins block br with one more
/// reference.
pub proof fn lemma_holders_frame_added(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    n: usize,
    br: BlockRef,
)
    requires
        holders_wf(list_a, tables_a, blocks_a, zeroing, holders),
        forall|x: usize| x != n ==> #[trigger] tables_b.is_cap(list_b, x) == tables_a.is_cap(list_a, x),
        forall|x: usize| x != n && #[trigger] tables_a.is_cap(list_a, x) ==> tables_b.payload_of(x) == tables_a.payload_of(x),
        !tables_a.is_cap(list_a, n),
        tables_b.is_cap(list_b, n),
        tables_b.payload_of(n).kind is Frame,
        tables_b.payload_of(n).base / 4096 < NUM_PAGES,
        block_ref(blocks_a, tables_b.payload_of(n).base / 4096) == br,
        frame_in_block(br, tables_b.payload_of(n)),
        holders.contains_key(br),
        block_refs(blocks_a, br) < usize::MAX,
        blocks_refs_changed(blocks_a, blocks_b, br, (block_refs(blocks_a, br) + 1) as usize, block_dead(blocks_a, br)),
    ensures
        holders_wf(list_b, tables_b, blocks_b, zeroing, holders.insert(br, holders[br].insert(n))),
{
    let hb = holders.insert(br, holders[br].insert(n));
    assert(!holders[br].contains(n));
    vstd::set::lemma_set_insert_len(holders[br], n);
    assert forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Frame implies {
        let i = tables_b.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& frame_in_block(block_ref(blocks_b, i), tables_b.payload_of(x))
        &&& hb.contains_key(block_ref(blocks_b, i))
        &&& hb[block_ref(blocks_b, i)].contains(x)
    } by {
        let i = tables_b.payload_of(x).base / 4096;
        if x != n {
            assert(tables_a.is_cap(list_a, x));
            assert(block_ref(blocks_b, i) == block_ref(blocks_a, i));
        }
    }
    assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
        &&& hb[k].finite()
        &&& hb[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
        &&& !block_active(zeroing, k)
    } by {
        assert(holders.contains_key(k));
    }
    assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x).kind is Frame
        &&& tables_b.payload_of(x).base / 4096 < NUM_PAGES
        &&& block_ref(blocks_b, tables_b.payload_of(x).base / 4096) == k
    } by {
        assert(holders.contains_key(k));
        if k != br || x != n {
            assert(holders[k].contains(x));
            assert(tables_a.is_cap(list_a, x));
            assert(x != n);
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

/// The holders after frame capability n, the only capability that changed, leaves its block br with one
/// reference fewer.
pub proof fn lemma_holders_frame_dropped(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    n: usize,
    br: BlockRef,
)
    requires
        holders_wf(list_a, tables_a, blocks_a, zeroing, holders),
        forall|x: usize| x != n ==> #[trigger] tables_b.is_cap(list_b, x) == tables_a.is_cap(list_a, x),
        forall|x: usize| x != n && #[trigger] tables_a.is_cap(list_a, x) ==> tables_b.payload_of(x) == tables_a.payload_of(x),
        tables_a.is_cap(list_a, n),
        tables_a.payload_of(n).kind is Frame,
        !tables_b.is_cap(list_b, n),
        block_ref(blocks_a, tables_a.payload_of(n).base / 4096) == br,
        blocks_refs_changed(
            blocks_a,
            blocks_b,
            br,
            (block_refs(blocks_a, br) - 1) as usize,
            block_dead(blocks_a, br) || block_refs(blocks_a, br) == 1,
        ),
    ensures
        holders_wf(list_b, tables_b, blocks_b, zeroing, holders.insert(br, holders[br].remove(n))),
{
    let hb = holders.insert(br, holders[br].remove(n));
    lemma_holder_refs(list_a, tables_a, blocks_a, zeroing, holders, n);
    assert(holders[br].contains(n));
    vstd::set::lemma_set_remove_len(holders[br], n);
    assert forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Frame implies {
        let i = tables_b.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& frame_in_block(block_ref(blocks_b, i), tables_b.payload_of(x))
        &&& hb.contains_key(block_ref(blocks_b, i))
        &&& hb[block_ref(blocks_b, i)].contains(x)
    } by {
        let i = tables_b.payload_of(x).base / 4096;
        assert(x != n);
        assert(tables_a.is_cap(list_a, x));
        assert(block_ref(blocks_b, i) == block_ref(blocks_a, i));
    }
    assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
        &&& hb[k].finite()
        &&& hb[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
        &&& !block_active(zeroing, k)
    } by {
        assert(holders.contains_key(k));
    }
    assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x).kind is Frame
        &&& tables_b.payload_of(x).base / 4096 < NUM_PAGES
        &&& block_ref(blocks_b, tables_b.payload_of(x).base / 4096) == k
    } by {
        assert(holders.contains_key(k));
        assert(holders[k].contains(x));
        assert(tables_a.is_cap(list_a, x));
        assert(x != n);
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

/// A block whose count changed is a holders' key, so it is not being zeroed, and every block being
/// zeroed is as it was.
pub proof fn lemma_zeroing_typed_refs_changed(
    list: &Tree,
    tables: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        zeroing.wf(),
        holders_wf(list, tables, blocks_a, zeroing, holders),
        holders.contains_key(br),
        blocks_refs_changed(blocks_a, blocks_b, br, refs, dead),
        zeroing_typed(zeroing, blocks_a),
    ensures
        zeroing_typed(zeroing, blocks_b),
{
    assert forall|b: usize| #[trigger] zeroing.blocks@.contains_key(b) implies {
        &&& zeroing.blocks@[b] == PAGES_PER_2M ==> {
            &&& blocks_b.regions_2m@[(b / PAGES_PER_2M) as int].typed
            &&& !blocks_b.regions_2m@[(b / PAGES_PER_2M) as int].dead
        }
        &&& zeroing.blocks@[b] == PAGES_PER_1G ==> {
            &&& blocks_b.regions_1g@[(b / PAGES_PER_1G) as int].typed
            &&& !blocks_b.regions_1g@[(b / PAGES_PER_1G) as int].dead
        }
    } by {
        assert(zeroing.block_level(b));
        if zeroing.blocks@[b] == PAGES_PER_2M {
            let x = BlockRef::Two(b / PAGES_PER_2M);
            assert(block_typed(blocks_a, x));
            assert(x != br);
            assert(block_dead(blocks_b, x) == block_dead(blocks_a, x));
        } else {
            let x = BlockRef::One(b / PAGES_PER_1G);
            assert(block_typed(blocks_a, x));
            assert(x != br);
            assert(block_dead(blocks_b, x) == block_dead(blocks_a, x));
        }
    }
}

/// Every page of a small block has that block: none is free, so none is covered.
pub proof fn lemma_small_block_ref(blocks: &BlockTable, base: usize, i: usize)
    requires
        blocks.wf(),
        base < NUM_PAGES,
        i < NUM_PAGES,
        blocks.pages@[base as int].kind is Base,
        blocks.in_block(base as int, i as int),
    ensures
        block_ref(blocks, i) == BlockRef::Small(base),
{
    if i != base {
        blocks.lemma_member_of(base as int, i as int);
    }
    blocks.lemma_not_free_uncovered(i as int);
}

/// A key at zero references has no holder, so no frame lies in that block.
pub proof fn lemma_no_frame_at_zero(
    list: &Tree,
    tables: &Tables,
    blocks: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    br: BlockRef,
    n: usize,
)
    requires
        holders_wf(list, tables, blocks, zeroing, holders),
        block_refs(blocks, br) == 0,
        tables.is_cap(list, n),
        tables.payload_of(n).kind is Frame,
    ensures
        block_ref(blocks, tables.payload_of(n).base / 4096) != br,
{
    if block_ref(blocks, tables.payload_of(n).base / 4096) == br {
        lemma_holder_refs(list, tables, blocks, zeroing, holders, n);
    }
}

/// The holders after a small block at zero references returns to free: its key goes, and no frame lay
/// in it.
pub proof fn lemma_holders_small_freed(
    list: &Tree,
    tables: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    base: usize,
)
    requires
        blocks_a.wf(),
        holders_wf(list, tables, blocks_a, zeroing, holders),
        base < NUM_PAGES,
        blocks_a.pages@[base as int].kind is Base,
        blocks_a.pages@[base as int].refs == 0,
        forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] blocks_b.pages@[i] == (
            if blocks_a.in_block(base as int, i) { free_entry() } else { blocks_a.pages@[i] }),
        blocks_b.regions_2m@ == blocks_a.regions_2m@,
        blocks_b.regions_1g@ == blocks_a.regions_1g@,
    ensures
        holders_wf(list, tables, blocks_b, zeroing, holders.remove(BlockRef::Small(base))),
{
    let br = BlockRef::Small(base);
    let hb = holders.remove(br);
    assert forall|x: usize| #[trigger] tables.is_cap(list, x) && tables.payload_of(x).kind is Frame implies {
        let i = tables.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& block_ref(blocks_b, i) == block_ref(blocks_a, i)
        &&& block_ref(blocks_a, i) != br
    } by {
        let i = tables.payload_of(x).base / 4096;
        lemma_no_frame_at_zero(list, tables, blocks_a, zeroing, holders, br, x);
        if blocks_a.in_block(base as int, i as int) {
            lemma_small_block_ref(blocks_a, base, i);
        }
        assert(blocks_b.pages@[i as int] == blocks_a.pages@[i as int]);
    }
    assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
        &&& hb[k].finite()
        &&& hb[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
        &&& !block_active(zeroing, k)
    } by {
        assert(holders.contains_key(k));
        if let BlockRef::Small(b) = k {
            if blocks_a.in_block(base as int, b as int) {
                blocks_a.lemma_member_of(base as int, b as int);
            }
            assert(blocks_b.pages@[b as int] == blocks_a.pages@[b as int]);
        }
    }
    assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies {
        &&& tables.is_cap(list, x)
        &&& tables.payload_of(x).kind is Frame
        &&& tables.payload_of(x).base / 4096 < NUM_PAGES
        &&& block_ref(blocks_b, tables.payload_of(x).base / 4096) == k
    } by {
        assert(holders.contains_key(k));
        assert(holders[k].contains(x));
    }
}

/// The holders after a 2M block at zero references returns to free.
pub proof fn lemma_holders_2m_freed(
    list: &Tree,
    tables: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    r: usize,
)
    requires
        blocks_a.wf(),
        holders_wf(list, tables, blocks_a, zeroing, holders),
        r < NUM_2M,
        blocks_a.regions_2m@[r as int].typed,
        blocks_a.regions_2m@[r as int].refs == 0,
        blocks_b.pages@ == blocks_a.pages@,
        blocks_b.regions_2m@ == blocks_a.regions_2m@.update(r as int, blocks_b.regions_2m@[r as int]),
        blocks_b.regions_1g@ == blocks_a.regions_1g@,
    ensures
        holders_wf(list, tables, blocks_b, zeroing, holders.remove(BlockRef::Two(r))),
{
    let br = BlockRef::Two(r);
    let hb = holders.remove(br);
    assert forall|x: usize| #[trigger] tables.is_cap(list, x) && tables.payload_of(x).kind is Frame implies {
        let i = tables.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& block_ref(blocks_b, i) == block_ref(blocks_a, i)
        &&& block_ref(blocks_a, i) != br
    } by {
        let i = tables.payload_of(x).base / 4096;
        lemma_no_frame_at_zero(list, tables, blocks_a, zeroing, holders, br, x);
        assert(i / PAGES_PER_2M != r);
    }
    assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
        &&& hb[k].finite()
        &&& hb[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
        &&& !block_active(zeroing, k)
    } by {
        assert(holders.contains_key(k));
    }
    assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies {
        &&& tables.is_cap(list, x)
        &&& tables.payload_of(x).kind is Frame
        &&& tables.payload_of(x).base / 4096 < NUM_PAGES
        &&& block_ref(blocks_b, tables.payload_of(x).base / 4096) == k
    } by {
        assert(holders.contains_key(k));
        assert(holders[k].contains(x));
    }
    assert forall|x: int| 0 <= x < NUM_2M && #[trigger] zeroing.active_2m@[x] implies {
        &&& blocks_b.regions_2m@[x].typed
        &&& blocks_b.regions_2m@[x].refs == 1
    } by {
        assert(x != r);
    }
}

/// The holders after a 1G block at zero references returns to free.
pub proof fn lemma_holders_1g_freed(
    list: &Tree,
    tables: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    r: usize,
)
    requires
        blocks_a.wf(),
        holders_wf(list, tables, blocks_a, zeroing, holders),
        r < NUM_1G,
        blocks_a.regions_1g@[r as int].typed,
        blocks_a.regions_1g@[r as int].refs == 0,
        blocks_b.pages@ == blocks_a.pages@,
        blocks_b.regions_1g@ == blocks_a.regions_1g@.update(r as int, blocks_b.regions_1g@[r as int]),
        blocks_b.regions_2m@ == blocks_a.regions_2m@,
    ensures
        holders_wf(list, tables, blocks_b, zeroing, holders.remove(BlockRef::One(r))),
{
    let br = BlockRef::One(r);
    let hb = holders.remove(br);
    assert forall|x: usize| #[trigger] tables.is_cap(list, x) && tables.payload_of(x).kind is Frame implies {
        let i = tables.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& block_ref(blocks_b, i) == block_ref(blocks_a, i)
        &&& block_ref(blocks_a, i) != br
    } by {
        let i = tables.payload_of(x).base / 4096;
        lemma_no_frame_at_zero(list, tables, blocks_a, zeroing, holders, br, x);
        if i / PAGES_PER_1G == r {
            lemma_in_1g_block(blocks_a, i, r);
        }
    }
    assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
        &&& hb[k].finite()
        &&& hb[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
        &&& !block_active(zeroing, k)
    } by {
        assert(holders.contains_key(k));
    }
    assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies {
        &&& tables.is_cap(list, x)
        &&& tables.payload_of(x).kind is Frame
        &&& tables.payload_of(x).base / 4096 < NUM_PAGES
        &&& block_ref(blocks_b, tables.payload_of(x).base / 4096) == k
    } by {
        assert(holders.contains_key(k));
        assert(holders[k].contains(x));
    }
    assert forall|x: int| 0 <= x < NUM_1G && #[trigger] zeroing.active_1g@[x] implies {
        &&& blocks_b.regions_1g@[x].typed
        &&& blocks_b.regions_1g@[x].refs == 1
    } by {
        assert(x != r);
    }
}

/// The holders after frame capability n, the only capability that changed, takes a block's first
/// reference, which retype held for it.
pub proof fn lemma_holders_frame_new(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    blocks: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    n: usize,
    br: BlockRef,
)
    requires
        holders_wf(list_a, tables_a, blocks, zeroing, holders),
        forall|x: usize| x != n ==> #[trigger] tables_b.is_cap(list_b, x) == tables_a.is_cap(list_a, x),
        forall|x: usize| x != n && #[trigger] tables_a.is_cap(list_a, x) ==> tables_b.payload_of(x) == tables_a.payload_of(x),
        !tables_a.is_cap(list_a, n),
        tables_b.is_cap(list_b, n),
        tables_b.payload_of(n).kind is Frame,
        tables_b.payload_of(n).base / 4096 < NUM_PAGES,
        block_ref(blocks, tables_b.payload_of(n).base / 4096) == br,
        frame_in_block(br, tables_b.payload_of(n)),
        !holders.contains_key(br),
        block_typed(blocks, br),
        block_refs(blocks, br) == 1,
        !block_dead(blocks, br),
        !block_active(zeroing, br),
    ensures
        holders_wf(list_b, tables_b, blocks, zeroing, holders.insert(br, set![n])),
{
    let hb = holders.insert(br, set![n]);
    assert(set![n].len() == 1) by {
        assert(set![n] =~= Set::<usize>::empty().insert(n));
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), n);
    }
    assert forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Frame implies {
        let i = tables_b.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& frame_in_block(block_ref(blocks, i), tables_b.payload_of(x))
        &&& hb.contains_key(block_ref(blocks, i))
        &&& hb[block_ref(blocks, i)].contains(x)
    } by {
        if x != n {
            assert(tables_a.is_cap(list_a, x));
        }
    }
    assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
        &&& hb[k].finite()
        &&& hb[k].len() == block_refs(blocks, k)
        &&& block_typed(blocks, k)
        &&& block_refs(blocks, k) == 0 ==> block_dead(blocks, k)
        &&& !block_active(zeroing, k)
    } by {
        if k != br {
            assert(holders.contains_key(k));
        }
    }
    assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x).kind is Frame
        &&& tables_b.payload_of(x).base / 4096 < NUM_PAGES
        &&& block_ref(blocks, tables_b.payload_of(x).base / 4096) == k
    } by {
        if k != br {
            assert(holders.contains_key(k));
            assert(holders[k].contains(x));
            assert(tables_a.is_cap(list_a, x));
            assert(x != n);
        }
    }
}

/// A page of a small block has its base's regions, so it is uncovered if the base is.
pub proof fn lemma_small_range_uncovered(blocks: &BlockTable, base: usize, order: usize, i: usize)
    requires
        small_order(order),
        base % (order_pages(order) as usize) == 0,
        base <= i < base + order_pages(order),
        !blocks.covered(base as int),
    ensures
        !blocks.covered(i as int),
        i / PAGES_PER_2M == base / PAGES_PER_2M,
        i / PAGES_PER_1G == base / PAGES_PER_1G,
{
    if order == 0 {
        assert(i == base);
    } else {
        // A block of 2 or 8 pages is aligned to its size, so it does not cross a 2M or 1G boundary.
        let n: int = if order == 1 { 2 } else { 8 };
        assert(base as int % n == 0);
        assert(i as int / 512 == base as int / 512) by (nonlinear_arith)
            requires
                n == 2 || n == 8,
                base as int % n == 0,
                base as int <= i as int,
                (i as int) < (base as int + n),
        ;
        assert(i as int / 262144 == base as int / 262144) by (nonlinear_arith)
            requires
                n == 2 || n == 8,
                base as int % n == 0,
                base as int <= i as int,
                (i as int) < (base as int + n),
        ;
    }
}

/// The holders after a free small block is typed: no frame lay in it, and the key it will have is not
/// there yet.
pub proof fn lemma_holders_small_typed(
    list: &Tree,
    tables: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    base: usize,
    order: usize,
)
    requires
        blocks_a.wf(),
        holders_wf(list, tables, blocks_a, zeroing, holders),
        small_order(order),
        base % (order_pages(order) as usize) == 0,
        base + order_pages(order) <= NUM_PAGES,
        forall|k: int| 0 <= k < order_pages(order) ==> #[trigger] blocks_a.pages@[base + k].kind is Free,
        !blocks_a.covered(base as int),
        blocks_b.regions_2m@ == blocks_a.regions_2m@,
        blocks_b.regions_1g@ == blocks_a.regions_1g@,
        forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + order_pages(order))
            ==> #[trigger] blocks_b.pages@[i] == blocks_a.pages@[i],
    ensures
        holders_wf(list, tables, blocks_b, zeroing, holders),
        !holders.contains_key(BlockRef::Small(base)),
{
    assert forall|i: usize| base <= i < base + order_pages(order) implies {
        &&& #[trigger] block_ref(blocks_a, i) == BlockRef::Small(i)
        &&& !block_typed(blocks_a, BlockRef::Small(i))
    } by {
        lemma_small_range_uncovered(blocks_a, base, order, i);
        assert(blocks_a.pages@[base + (i - base)].kind is Free);
    }
    assert forall|x: usize| #[trigger] tables.is_cap(list, x) && tables.payload_of(x).kind is Frame implies {
        let i = tables.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& block_ref(blocks_b, i) == block_ref(blocks_a, i)
    } by {
        let i = tables.payload_of(x).base / 4096;
        assert(block_typed(blocks_a, block_ref(blocks_a, i)));
        assert(!(base <= i < base + order_pages(order)));
        assert(blocks_b.pages@[i as int] == blocks_a.pages@[i as int]);
    }
    assert forall|k: BlockRef| #[trigger] holders.contains_key(k) implies {
        &&& holders[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
    } by {
        if let BlockRef::Small(b) = k {
            assert(!(base <= b < base + order_pages(order))) by {
                if base <= b < base + order_pages(order) {
                    assert(blocks_a.pages@[base + (b - base)].kind is Free);
                }
            }
            assert(blocks_b.pages@[b as int] == blocks_a.pages@[b as int]);
        }
    }
    assert forall|k: BlockRef, x: usize| holders.contains_key(k) && #[trigger] holders[k].contains(x) implies
        block_ref(blocks_b, tables.payload_of(x).base / 4096) == k by {
        assert(tables.is_cap(list, x));
    }
    if holders.contains_key(BlockRef::Small(base)) {
        assert(blocks_a.pages@[base + 0].kind is Free);
    }
}

/// The holders after a free region is typed and starts being zeroed: no frame lay in it, and it has no
/// key while it is being zeroed.
pub proof fn lemma_holders_region_typed(
    list: &Tree,
    tables: &Tables,
    blocks_a: &BlockTable,
    blocks_b: &BlockTable,
    zeroing_a: &Zeroing,
    zeroing_b: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    level: Large,
    r: usize,
)
    requires
        blocks_a.wf(),
        holders_wf(list, tables, blocks_a, zeroing_a, holders),
        r < level_regions(level),
        forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level) ==> {
            &&& #[trigger] blocks_a.pages@[i].kind is Free
            &&& !blocks_a.covered(i)
        },
        blocks_b.pages@ == blocks_a.pages@,
        match level {
            Large::Two => {
                &&& blocks_b.regions_2m@ == blocks_a.regions_2m@.update(r as int, blocks_b.regions_2m@[r as int])
                &&& blocks_b.regions_2m@[r as int].typed
                &&& blocks_b.regions_2m@[r as int].refs == 1
                &&& blocks_b.regions_1g@ == blocks_a.regions_1g@
                &&& zeroing_b.active_2m@ == zeroing_a.active_2m@.update(r as int, true)
                &&& zeroing_b.active_1g@ == zeroing_a.active_1g@
            },
            Large::One => {
                &&& blocks_b.regions_1g@ == blocks_a.regions_1g@.update(r as int, blocks_b.regions_1g@[r as int])
                &&& blocks_b.regions_1g@[r as int].typed
                &&& blocks_b.regions_1g@[r as int].refs == 1
                &&& blocks_b.regions_2m@ == blocks_a.regions_2m@
                &&& zeroing_b.active_1g@ == zeroing_a.active_1g@.update(r as int, true)
                &&& zeroing_b.active_2m@ == zeroing_a.active_2m@
            },
        },
    ensures
        holders_wf(list, tables, blocks_b, zeroing_b, holders),
{
    let base = level_base(level, r);
    let pages = level_pages(level);
    assert(!block_typed(blocks_a, level_ref(level, r))) by {
        assert(blocks_a.pages@[base as int].kind is Free);
        assert(!blocks_a.covered(base as int));
        match level {
            Large::Two => {
                assert(base == r * 512);
                lemma_fundamental_div_mod_converse(base as int, 512, r as int, 0);
                assert(region_2m(base as int) == r);
            },
            Large::One => {
                assert(base == r * 262144);
                lemma_fundamental_div_mod_converse(base as int, 262144, r as int, 0);
                assert(region_1g(base as int) == r);
            },
        }
    }
    assert forall|i: usize| base <= i < base + pages implies {
        &&& #[trigger] block_ref(blocks_a, i) == BlockRef::Small(i)
        &&& !block_typed(blocks_a, BlockRef::Small(i))
    } by {
        assert(blocks_a.pages@[i as int].kind is Free);
        assert(!blocks_a.covered(i as int));
    }
    assert forall|i: usize| i < NUM_PAGES && !(base <= i < base + pages) implies
        #[trigger] block_ref(blocks_b, i) == block_ref(blocks_a, i) by {
        match level {
            Large::Two => {
                assert(i / PAGES_PER_2M != r);
            },
            Large::One => {
                assert(i / PAGES_PER_1G != r);
            },
        }
    }
    assert forall|x: usize| #[trigger] tables.is_cap(list, x) && tables.payload_of(x).kind is Frame implies {
        let i = tables.payload_of(x).base / 4096;
        &&& i < NUM_PAGES
        &&& block_ref(blocks_b, i) == block_ref(blocks_a, i)
    } by {
        let i = tables.payload_of(x).base / 4096;
        assert(block_typed(blocks_a, block_ref(blocks_a, i)));
        assert(!(base <= i < base + pages));
    }
    assert forall|k: BlockRef| #[trigger] holders.contains_key(k) implies {
        &&& holders[k].len() == block_refs(blocks_b, k)
        &&& block_typed(blocks_b, k)
        &&& block_refs(blocks_b, k) == 0 ==> block_dead(blocks_b, k)
        &&& !block_active(zeroing_b, k)
    } by {
        assert(k != level_ref(level, r));
    }
    assert forall|k: BlockRef, x: usize| holders.contains_key(k) && #[trigger] holders[k].contains(x) implies
        block_ref(blocks_b, tables.payload_of(x).base / 4096) == k by {
        assert(tables.is_cap(list, x));
    }
}

/// The holders after a region's zeroing finishes: it had no key, so the holders say nothing of it.
pub proof fn lemma_holders_region_done(
    list: &Tree,
    tables: &Tables,
    blocks: &BlockTable,
    zeroing_a: &Zeroing,
    zeroing_b: &Zeroing,
    holders: IMap<BlockRef, Set<usize>>,
    level: Large,
    r: usize,
)
    requires
        holders_wf(list, tables, blocks, zeroing_a, holders),
        r < level_regions(level),
        zeroing_a.active(level, r),
        match level {
            Large::Two => zeroing_b.active_2m@ == zeroing_a.active_2m@.update(r as int, false)
                && zeroing_b.active_1g@ == zeroing_a.active_1g@,
            Large::One => zeroing_b.active_1g@ == zeroing_a.active_1g@.update(r as int, false)
                && zeroing_b.active_2m@ == zeroing_a.active_2m@,
        },
    ensures
        holders_wf(list, tables, blocks, zeroing_b, holders),
        !holders.contains_key(level_ref(level, r)),
{
    assert forall|k: BlockRef| #[trigger] holders.contains_key(k) implies !block_active(zeroing_b, k) by {
        assert(!block_active(zeroing_a, k));
    }
}

} // verus!
