// SPDX-License-Identifier: MIT

//! Retyping free memory under an untyped. Here a 4K frame: the page is zeroed at once, and the frame
//! capability is a child of the untyped in a slot the caller names, so revoking the untyped reaches it.
//! See design/capability-names-a-block/ and design/teardown-driven-by-retype/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
use crate::capability::block::*;
use crate::capability::derive::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
use crate::capability::position::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::refs::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::capability::zero::*;
use crate::define::*;
use crate::pptr::*;

/// Read, write and execute.
pub const FRAME_RIGHTS: u32 = 7;

// The most each retype adds to the step counter, the sum of what its callees state:
// design/one-lock-bounded-steps/.
/// retype_frame's bound: typing one page.
pub const RETYPE_FRAME_STEPS: usize = 2 * SMALL_PAGES_MAX;
/// zero_large's bound: one zeroing step.
pub const ZERO_LARGE_STEPS: usize = ZERO_CHUNK_PAGES;
/// retype_large_frame's bound: one zero_large.
pub const RETYPE_LARGE_FRAME_STEPS: usize = ZERO_LARGE_STEPS;
/// place_leaf's bound: typing the leaf's block, writing its node page and its payload page.
pub const PLACE_LEAF_STEPS: usize = 2 * SMALL_PAGES_MAX + NODES_PER_PAGE + ADD_LEAF_STEPS;
/// retype_leaf's bound: one place_leaf.
pub const RETYPE_LEAF_STEPS: usize = PLACE_LEAF_STEPS;

/// A 4K frame capability's payload. It has every right a frame can have, whatever the untyped's, since
/// the untyped's holder already reaches the page.
pub open spec fn frame_of(base: usize) -> Payload {
    Payload { kind: CapKind::Frame, order: 0, rights: FRAME_RIGHTS, base, badge: 0, reserved: 0 }
}

/// What a retype of a large frame did.
pub enum RetypeStep {
    /// Nothing changed.
    Refused,
    /// The block is being zeroed and has no capability yet. Retype again to go on.
    Again,
    /// The block is all zero and the capability exists.
    Done,
}

/// The region a 2M or 1G block at this aligned base is, if the block table has one.
pub fn large_region(base: usize, order: u8) -> (ret: Option<(Large, usize)>)
    requires
        order <= MAX_ORDER,
        base as int % block_bytes(order) == 0,
    ensures
        ret is Some == {
            ||| order == 9 && base / PAGE_SZ / PAGES_PER_2M < NUM_2M
            ||| order == 18 && base / PAGE_SZ / PAGES_PER_1G < NUM_1G
        },
        ret is Some ==> {
            let (level, r) = ret.unwrap();
            &&& level == (if order == 9 { Large::Two } else { Large::One })
            &&& r == base / PAGE_SZ / level_pages(level)
            &&& r < level_regions(level)
            &&& level_base(level, r) == base / PAGE_SZ
            &&& r * level_pages(level) == base / PAGE_SZ
            &&& base / PAGE_SZ < NUM_PAGES
            &&& base == (base / PAGE_SZ) * PAGE_SZ
        },
{
    let page = base / PAGE_SZ;
    let level = if order == 9 {
        Large::Two
    } else if order == 18 {
        Large::One
    } else {
        return None;
    };
    let r = page / pages_of_level(level);
    let regions = match level {
        Large::Two => NUM_2M,
        Large::One => NUM_1G,
    };
    if r >= regions {
        return None;
    }
    proof {
        lemma2_to64();
        match level {
            Large::Two => {
                assert(block_bytes(order) == SIZE_2M);
                assert(base % SIZE_2M == 0);
                assert(page % PAGES_PER_2M == 0 && r * PAGES_PER_2M == page && page * PAGE_SZ == base) by (nonlinear_arith)
                    requires
                        base % SIZE_2M == 0,
                        page == base / PAGE_SZ,
                        r == page / PAGES_PER_2M,
                ;
            },
            Large::One => {
                assert(pow2(18) == PAGES_PER_1G);
                assert(block_bytes(order) == SIZE_1G);
                assert(base % SIZE_1G == 0);
                assert(page % PAGES_PER_1G == 0 && r * PAGES_PER_1G == page && page * PAGE_SZ == base) by (nonlinear_arith)
                    requires
                        base % SIZE_1G == 0,
                        page == base / PAGE_SZ,
                        r == page / PAGES_PER_1G,
                ;
            },
        }
        assert(level_base(level, r) == page);
    }
    Some((level, r))
}

/// A frame capability's payload.
pub open spec fn large_frame_of(base: usize, order: u8) -> Payload {
    Payload { kind: CapKind::Frame, order, rights: FRAME_RIGHTS, base, badge: 0, reserved: 0 }
}

/// Types a region at either level. What follows says the same of both, so a caller need not split.
fn type_region(blocks: &mut BlockTable, level: Large, r: usize) -> (ret: Option<Tracked<Map<usize, PagePerm4k>>>)
    requires
        old(blocks).wf(),
        r < level_regions(level),
    ensures
        final(blocks).wf(),
        ret is None ==> *final(blocks) == *old(blocks),
        final(blocks).pages@ == old(blocks).pages@,
        ret is Some == old(blocks).large_free(level, r as int),
        ret is Some ==> {
            &&& forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                ==> !#[trigger] old(blocks).covered(i)
            &&& ret->0@.dom() == BlockTable::large_pages(level, r as int)
            &&& forall|i: usize| BlockTable::large_pages(level, r as int).contains(i) ==> #[trigger] holds(ret->0@, i)
            &&& forall|x: int| 0 <= x < NUM_2M && (#[trigger] old(blocks).regions_2m@[x]).typed && !old(blocks).regions_2m@[x].dead
                ==> final(blocks).regions_2m@[x].typed && !final(blocks).regions_2m@[x].dead
            &&& forall|x: int| 0 <= x < NUM_1G && (#[trigger] old(blocks).regions_1g@[x]).typed && !old(blocks).regions_1g@[x].dead
                ==> final(blocks).regions_1g@[x].typed && !final(blocks).regions_1g@[x].dead
            &&& level is Two ==> final(blocks).regions_2m@[r as int].typed && !final(blocks).regions_2m@[r as int].dead
            &&& level is One ==> final(blocks).regions_1g@[r as int].typed && !final(blocks).regions_1g@[r as int].dead
            &&& forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                ==> #[trigger] old(blocks).pages@[i].kind is Free
            &&& match level {
                Large::Two => {
                    &&& final(blocks).regions_2m@ == old(blocks).regions_2m@.update(r as int, final(blocks).regions_2m@[r as int])
                    &&& final(blocks).regions_2m@[r as int].refs == 1
                    &&& final(blocks).regions_1g@ == old(blocks).regions_1g@
                },
                Large::One => {
                    &&& final(blocks).regions_1g@ == old(blocks).regions_1g@.update(r as int, final(blocks).regions_1g@[r as int])
                    &&& final(blocks).regions_1g@[r as int].refs == 1
                    &&& final(blocks).regions_2m@ == old(blocks).regions_2m@
                },
            }
        },
{
    let ghost pre = *old(blocks);
    match level {
        Large::Two => {
            let ret = blocks.try_type_2m(r);
            proof {
                if ret is Some {
                    assert((r + 1) * PAGES_PER_2M == r * PAGES_PER_2M + PAGES_PER_2M);
                    assert forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                        implies !#[trigger] pre.covered(i) by {
                        assert(pre.pages@[i].kind is Free);
                    }
                    assert forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                        implies #[trigger] pre.pages@[i].kind is Free by {}
                }
            }
            ret
        },
        Large::One => {
            let ret = blocks.try_type_1g(r);
            proof {
                if ret is Some {
                    assert((r + 1) * PAGES_PER_1G == r * PAGES_PER_1G + PAGES_PER_1G);
                    assert forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                        implies !#[trigger] pre.covered(i) by {
                        assert(pre.pages@[i].kind is Free);
                    }
                    assert forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                        implies #[trigger] pre.pages@[i].kind is Free by {}
                }
            }
            ret
        },
    }
}

impl CapKernel {
    /// The refusals every retype has: an index that names no slot, a parent that is not a capability
    /// to an untyped, without the retype right or at the deepest depth, or a block outside the
    /// untyped's.
    pub open spec fn can_retype_under(&self, root: usize, from: usize, base: usize, order: u8) -> bool {
        let parent = self.tables.node_of(root, from);
        &&& self.tables.has_slot(&self.list, root, from)
        &&& self.is_cap(parent)
        &&& self.payload_of(parent).kind is Untyped
        &&& self.payload_of(parent).rights & right_bit(Right::Retype) != 0
        &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
        &&& block_within(base, order, self.payload_of(parent))
    }

    /// A block a retype may type lies in its untyped's block, so the untyped covers the block's first
    /// page, the object the retype names.
    pub proof fn lemma_retype_covers(&self, root: usize, from: usize, base: usize, order: u8)
        requires
            self.can_retype_under(root, from, base, order),
        ensures
            self.view().covers(self.tables.node_of(root, from), base),
    {
        let p = self.payload_of(self.tables.node_of(root, from));
        let size = pow2(order as nat) as int;
        lemma_pow2_pos(order as nat);
        lemma_pow2_pos(p.order as nat);
        assert(block_bytes(order) == PAGE_SZ * size) by (nonlinear_arith)
            requires block_bytes(order) == size * PAGE_SZ;
        lemma_mod_mod(base as int, PAGE_SZ as int, size);
        assert(block_bytes(order) >= PAGE_SZ) by (nonlinear_arith)
            requires block_bytes(order) == PAGE_SZ * size, size > 0;
    }

    /// And a retype that makes a capability needs an empty slot for it.
    pub open spec fn can_retype(&self, root: usize, from: usize, to: usize, base: usize, order: u8) -> bool {
        &&& self.can_retype_under(root, from, base, order)
        &&& self.tables.has_slot(&self.list, root, to)
        &&& !self.list.nodes@[self.tables.node_of(root, to) as int].live
    }

    /// And a retype of a small block that makes a capability needs the block free, among the pages
    /// the block table tracks.
    pub open spec fn can_retype_block(&self, root: usize, from: usize, to: usize, base: usize, order: u8) -> bool {
        &&& self.can_retype(root, from, to, base, order)
        &&& self.blocks.tracks_addr_run(base, order_pages(order as usize))
        &&& self.blocks.small_free((base / PAGE_SZ) as int, order as usize)
    }

    /// And a leaf needs a table to go in, the caller's own or that of a live process the caller
    /// controls, an empty root entry of it and two free pages of memory, and is never at address zero,
    /// which means no leaf.
    pub open spec fn can_retype_leaf(&self, root: usize, from: usize, at: Position, base: usize) -> bool {
        let table = self.destination_at(root, at.through);
        &&& self.can_retype_under(root, from, base, 1)
        &&& table is Some
        &&& at.index < ROOT_ENTRIES
        &&& self.tables.leaf(table->0, at.index as int) == NO_LEAF
        &&& base != NO_LEAF
        &&& self.blocks.tracks_addr_run(base, 2)
        &&& self.blocks.small_free((base / PAGE_SZ) as int, 1)
    }

    /// And a table page has no capability, so needs no slot: a level a table page has, and a free
    /// order-3 block.
    pub open spec fn can_retype_table_page(&self, root: usize, from: usize, base: usize, level: usize) -> bool {
        &&& self.can_retype_under(root, from, base, 3)
        &&& 1 <= level <= 3
        &&& self.blocks.tracks_addr_run(base, 8)
        &&& self.blocks.small_free((base / PAGE_SZ) as int, 3)
    }

    /// A 4K frame is that and no more.
    pub open spec fn can_retype_frame(&self, root: usize, from: usize, to: usize, base: usize) -> bool {
        self.can_retype_block(root, from, to, base, 0)
    }

    /// And a thread needs a process to be bound to.
    pub open spec fn can_retype_thread(&self, root: usize, from: usize, to: usize, base: usize, j: usize) -> bool {
        &&& self.can_hold_thread(root, j)
        &&& self.can_retype_block(root, from, to, base, THREAD_ORDER)
    }

    /// And a large frame is 2M or 1G, in a region the block table has, whose block is free or is
    /// the one an earlier step of this retype typed and is zeroing.
    pub open spec fn can_retype_large(&self, root: usize, from: usize, to: usize, base: usize, order: u8) -> bool {
        let level = if order == 9 { Large::Two } else { Large::One };
        let r = base / PAGE_SZ / level_pages(level);
        &&& self.can_retype(root, from, to, base, order)
        &&& order == 9 ==> base / PAGE_SZ / PAGES_PER_2M < NUM_2M
        &&& order == 18 ==> base / PAGE_SZ / PAGES_PER_1G < NUM_1G
        &&& order == 9 || order == 18
        &&& self.zeroing.active(level, r) || self.blocks.large_free(level, r as int)
    }

    /// Checks the refusals every retype has and finds the parent's node.
    pub fn retype_parent(&self, root: usize, from: usize, base: usize, order: u8) -> (ret: Option<usize>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret is Some == self.can_retype_under(root, from, base, order),
            ret is Some ==> {
                &&& ret.unwrap() == self.tables.node_of(root, from)
                &&& self.view().holds_right(root, ret.unwrap(), Right::Retype)
                &&& base as int % block_bytes(order) == 0
                &&& order <= MAX_ORDER
                &&& base as int + block_bytes(order) <= NODE_SPACE as int
            },
    {
        let (parent, payload) = match self.tables.lookup(&self.list, root, from) {
            Some(found) => found,
            None => { return None; },
        };
        let node = self.list.get(parent);
        let node_ok = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !node_ok || node.depth >= MAX_DEPTH {
            return None;
        }
        proof {
            self.lemma_slot(root, from);
            assert(self.tables.is_cap(&self.list, parent));
            assert(payload == self.payload_of(parent));
        }
        let untyped = match payload.kind {
            CapKind::Untyped => true,
            _ => false,
        };
        if !untyped || payload.rights & 8 == 0 || !is_block_within(payload, base, order) {
            return None;
        }
        proof {
            assert(right_bit(Right::Retype) == 8);
            assert(self.view().holds_right(root, parent, Right::Retype));
        }
        Some(parent)
    }

    /// Checks those refusals and an empty slot for the capability, and finds the two nodes.
    pub fn retype_slots(&self, root: usize, from: usize, to: usize, base: usize, order: u8) -> (ret: Option<(usize, usize)>)
        requires
            self.wf(),
            self.tables.roots@.contains_key(root),
        ensures
            ret is Some == self.can_retype(root, from, to, base, order),
            ret is Some ==> {
                &&& ret.unwrap().0 == self.tables.node_of(root, from)
                &&& ret.unwrap().1 == self.tables.node_of(root, to)
                &&& self.view().holds_right(root, ret.unwrap().0, Right::Retype)
                &&& base as int % block_bytes(order) == 0
                &&& order <= MAX_ORDER
                &&& base as int + block_bytes(order) <= NODE_SPACE as int
            },
    {
        let parent = match self.retype_parent(root, from, base, order) {
            Some(found) => found,
            None => { return None; },
        };
        let child = match self.tables.lookup(&self.list, root, to) {
            Some(found) => found.0,
            None => { return None; },
        };
        if self.list.get(child).live {
            return None;
        }
        Some((parent, child))
    }

    /// The block a frame at base will take: typed, holding the one reference retype took for its
    /// capability, with no capability yet.
    pub open spec fn frame_block_ready(&self, base: usize, order: u8) -> bool {
        let br = block_ref(&self.blocks, base / PAGE_SZ);
        &&& self.blocks.tracks_addr(base)
        &&& !self.holders@.contains_key(br)
        &&& block_typed(&self.blocks, br)
        &&& block_refs(&self.blocks, br) == 1
        &&& !block_dead(&self.blocks, br)
        &&& !block_active(&self.zeroing, br)
        &&& frame_in_block(br, large_frame_of(base, order))
        &&& br is Small ==> self.blocks.pages@[br->Small_0 as int].object is Frame
        &&& forall|i: usize| #[trigger] block_has_page(br, i) ==> self.frames@.contains_key(i)
    }

    /// The holders after a retype's capability appears: it takes the one reference its block held.
    proof fn lemma_retype_holders(pre: Self, post: Self, child: usize, base: usize, order: u8)
        requires
            Self::derive_step(pre, post, child),
            post.is_cap(child),
            post.payload_of(child) == large_frame_of(base, order),
            post.blocks == pre.blocks,
            post.zeroing == pre.zeroing,
            pre.frame_block_ready(base, order),
            post.holders@ == pre.holders@.insert(block_ref(&pre.blocks, base / PAGE_SZ), set![child]),
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.list.pages@.dom() == pre.list.pages@.dom(),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        pre.lemma_slot_not_owned(child);
        Self::lemma_same_leaf_nodes(pre, post, child, child);
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
        pre.lemma_slot_not_table_page(child);
        Self::lemma_same_table_nodes(pre, post, child, child);
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
        lemma_spaces_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks);
        lemma_threads_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks);
        lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
        lemma_holders_frame_new(
            &pre.list,
            &pre.tables,
            &post.list,
            &post.tables,
            &pre.blocks,
            &pre.zeroing,
            pre.holders@,
            child,
            block_ref(&pre.blocks, base / PAGE_SZ),
        );
    }

    /// Makes the frame capability once its pages are zero: one child, in the slot the caller named.
    fn add_frame_cap(&mut self, root: usize, from: usize, to: usize, parent: usize, child: usize, base: usize, order: u8)
        requires
            old(self).wf(),
            old(self).can_retype(root, from, to, base, order),
            parent == old(self).tables.node_of(root, from),
            child == old(self).tables.node_of(root, to),
            order <= MAX_ORDER,
            base as int % block_bytes(order) == 0,
            base as int + block_bytes(order) <= NODE_SPACE as int,
            old(self).frame_block_ready(base, order),
        ensures
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            Self::same_tree(*old(self), *final(self)),
            final(self).cores == old(self).cores,
            final(self).blocks == old(self).blocks,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).holders@ == old(self).holders@.insert(block_ref(&old(self).blocks, base / PAGE_SZ), set![child]),
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).mappings == old(self).mappings,
            final(self).view().holds(root, child),
            final(self).payload_of(child) == large_frame_of(base, order),
            final(self).list.is_child(parent, child),
            final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1,
            discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base, into: None }),
            final(self).tables.roots == old(self).tables.roots,
            Self::caps_frame(*old(self), *final(self), child, child),
            final(self).list.parent@ == old(self).list.parent@.insert(child, parent),
            final(self).processes == old(self).processes,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).iommus == old(self).iommus,
            forall|i: int| #![trigger final(self).list.nodes@[i]] 0 <= i < NODE_SPACE && i != child ==> {
                &&& final(self).list.nodes@[i].live == old(self).list.nodes@[i].live
                &&& final(self).list.nodes@[i].depth == old(self).list.nodes@[i].depth
            },
            forall|x: usize| #[trigger] old(self).is_cap(x) ==> {
                &&& final(self).is_cap(x)
                &&& final(self).payload_of(x) == old(self).payload_of(x)
            },
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(parent);
            pre.lemma_slot_bound(child);
            pre.list.lemma_seq_fits();
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
        }
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: CapKind::Frame, order, rights: FRAME_RIGHTS, base, badge: 0, reserved: 0 },
        );
        self.holders = Ghost(pre.holders@.insert(block_ref(&pre.blocks, base / PAGE_SZ), set![child]));
        proof {
            let post = *self;
            assert(post.payload_of(child) == large_frame_of(base, order));
            assert(payload_wf(post.payload_of(child)));
            assert(7u32 & 128u32 == 0) by (bit_vector);
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_devices_caps_frame(pre, post, child, child);
            Self::lemma_hidden_frame(pre, post, child, child);
            Self::lemma_table_nodes_caps_frame(pre, post, child, child);
            Self::lemma_space_nodes_caps_frame(pre, post, child, child);
            Self::lemma_bindings_caps_frame(pre, post, child, child);
            Self::lemma_retype_holders(pre, post, child, base, order);
            lemma_parents_derived(pre.list, post.list, parent, child);
            Self::lemma_tlb_same(pre, post);
            assert(FRAME_RIGHTS & 128 == 0) by (compute_only);
            assert(right_bit(Right::Control) == 128);
            assert(right_bit(Right::Retype) == 8);
            Self::lemma_derive_step_adds_cap(pre, post, child);
            Self::lemma_places_child_view(pre, post, root, from, root, to);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            assert(post.view().names[child] == base);
            pre.lemma_retype_covers(root, from, base, order);
            lemma_adds_child_discharges_retype(pre.view(), post.view(), root, parent, child, live, base);
            Self::lemma_bound_threads_same(pre, post);
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
                &&& post.is_cap(x)
                &&& post.payload_of(x) == pre.payload_of(x)
            } by {
                assert(x != child);
                Self::lemma_caps_frame(pre, post, child, child, x);
            }
        }
    }

    /// What a retype that makes the node child, typing the small block of the order at page, and
    /// fills the root entry filled names if any, leaves as it was, so that a later operation's
    /// success can be proven from what held before: every slot is a slot of the node it was, every
    /// capability says what it said at the depth it had, every empty slot but child's is empty, every
    /// table has the root entries it had but the one filled, every process record has the dead flag
    /// it had, and the block table's large regions and the kind of every tracked page outside the
    /// block are as they were. A retype that makes a capability fills no root entry; a leaf's makes a
    /// hidden node, which no slot names, and fills one.
    pub open spec fn retype_keeps(pre: Self, post: Self, child: usize, page: int, order: usize, filled: Option<(usize, int)>) -> bool {
        &&& forall|r: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, r, i) ==> {
            &&& post.tables.has_slot(&post.list, r, i)
            &&& post.tables.node_of(r, i) == pre.tables.node_of(r, i)
            &&& pre.tables.node_of(r, i) != child && !pre.list.nodes@[pre.tables.node_of(r, i) as int].live
                ==> !post.list.nodes@[pre.tables.node_of(r, i) as int].live
        }
        &&& forall|x: usize| #[trigger] pre.is_cap(x) ==> {
            &&& post.is_cap(x)
            &&& post.payload_of(x) == pre.payload_of(x)
            &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
        }
        &&& forall|r: usize| #[trigger] pre.tables.roots@.contains_key(r) ==> post.tables.roots@.contains_key(r)
        &&& forall|r: usize, e: int| pre.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES && filled != Some((r, e))
            ==> #[trigger] post.tables.leaf(r, e) == pre.tables.leaf(r, e)
        &&& forall|p: usize| #[trigger] pre.processes.records@.contains_key(p) ==> {
            &&& post.processes.records@.contains_key(p)
            &&& post.processes.records@[p].value().dead == pre.processes.records@[p].value().dead
        }
        &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@
        &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@
        &&& forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(order))
            ==> #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind
    }

    /// What a retype of an order-3 block, a process or a space, leaves as it was: the list grew by node
    /// pages at most, its derive changed the liveness of the new capability alone and no node's depth,
    /// any table root it made is a new one, and the block table's pages outside the new block are as
    /// they were.
    pub proof fn lemma_order3_keeps(pre: Self, post: Self, mid: Tree, root: usize, to: usize, page: int)
        requires
            pre.wf(),
            pre.tables.has_slot(&pre.list, root, to),
            !pre.list.nodes@[pre.tables.node_of(root, to) as int].live,
            list_grown(pre.list, mid),
            mid.nodes@.len() == NODE_SPACE,
            post.list.nodes@.len() == NODE_SPACE,
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < mid.nodes@.len() && i != pre.tables.node_of(root, to) ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
                &&& post.list.nodes@[i].depth == mid.nodes@[i].depth
            },
            forall|t: usize| #[trigger] pre.tables.roots@.contains_key(t) ==>
                post.tables.roots@.contains_key(t) && post.tables.roots@[t] == pre.tables.roots@[t],
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.is_cap(x) && post.payload_of(x) == pre.payload_of(x),
            forall|p: usize| #[trigger] pre.processes.records@.contains_key(p) ==> {
                &&& post.processes.records@.contains_key(p)
                &&& post.processes.records@[p] == pre.processes.records@[p]
            },
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| post.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            Self::retype_keeps(pre, post, pre.tables.node_of(root, to), page, 3, None),
    {
        let child = pre.tables.node_of(root, to);
        pre.lemma_slot(root, to);
        pre.lemma_slot_bound(child);
        assert forall|r: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, r, i) implies {
            &&& post.tables.has_slot(&post.list, r, i)
            &&& post.tables.node_of(r, i) == pre.tables.node_of(r, i)
            &&& pre.tables.node_of(r, i) != child && !pre.list.nodes@[pre.tables.node_of(r, i) as int].live
                ==> !post.list.nodes@[pre.tables.node_of(r, i) as int].live
        } by {
            pre.lemma_slot(r, i);
            let n = pre.tables.node_of(r, i);
            pre.lemma_slot_bound(n);
            let leaf = pre.tables.leaf(r, index_entry(i));
            assert(leaf == page_of(n));
            assert(leaf != child);
            assert(post.tables.leaf(r, index_entry(i)) == leaf);
            assert(post.list.nodes@[leaf as int].live == mid.nodes@[leaf as int].live);
            assert(mid.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
            &&& post.is_cap(x)
            &&& post.payload_of(x) == pre.payload_of(x)
            &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
        } by {
            pre.lemma_slot_bound(x);
            assert(x != child);
            assert(post.list.nodes@[x as int].depth == mid.nodes@[x as int].depth);
            assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
        }
        assert forall|r: usize, e: int| pre.tables.roots@.contains_key(r) && 0 <= e < ROOT_ENTRIES
            implies #[trigger] post.tables.leaf(r, e) == pre.tables.leaf(r, e) by {
            assert(post.tables.roots@[r] == pre.tables.roots@[r]);
        }
        assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(3))
            implies #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind by {
            assert(post.blocks.pages@[i] == pre.blocks.pages@[i]);
        }
    }

    /// What a retype of the page at base as a 4K frame did, under the untyped at index from of the table
    /// at root, with the capability at index to: the retype was allowed, the frame capability is the
    /// untyped's child in that slot, the one entry the parent map gains and the only node whose kind,
    /// liveness or capability changed, no root entry changed, the page is zero, the block table changed
    /// in that page alone, which is a block of its own with a count of one, and the step discharges the
    /// retype's effect.
    pub open spec fn frame_retyped(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize) -> bool {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        &&& pre.can_retype_frame(root, from, to, base)
        &&& pre.view().holds_right(root, parent, Right::Retype)
        &&& post.view().holds(root, child)
        &&& post.payload_of(child) == frame_of(base)
        &&& post.list.is_child(parent, child)
        &&& post.list.parent@ == pre.list.parent@.insert(child, parent)
        &&& post.list.nodes@[child as int].depth == pre.list.nodes@[parent as int].depth + 1
        &&& post.tables.roots == pre.tables.roots
        &&& Self::caps_frame(pre, post, child, child)
        &&& holds_zero(post.frames@, base / PAGE_SZ)
        &&& pre.blocks.kept_but_run(post.blocks, (base / PAGE_SZ) as int, 0)
        &&& {
            let br = block_ref(&post.blocks, base / PAGE_SZ);
            &&& block_typed(&post.blocks, br)
            &&& block_refs(&post.blocks, br) == 1
            &&& !block_dead(&post.blocks, br)
        }
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, into: None })
    }

    /// What a step of a large retype that has not found its block all zero yet did, under the untyped at
    /// index from of the table at root, for the block at base of order into the slot at index to: the
    /// retype was allowed, no capability was made and no slot changed, and the step discharges the
    /// retype's effect. The region is being zeroed, its cursor rose, from 0 when it was not being
    /// zeroed before, and is short of the region's pages, and the same retype is allowed again: so a
    /// caller that repeats it while it says Again has a measure that falls and reaches Done. The block
    /// table changed in that region's entry alone.
    pub open spec fn large_frame_zeroing(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize, order: u8) -> bool {
        let parent = pre.tables.node_of(root, from);
        let level = large_level(order);
        let page = base / PAGE_SZ;
        let r = page / level_pages(level);
        &&& pre.can_retype_large(root, from, to, base, order)
        &&& pre.view().holds_right(root, parent, Right::Retype)
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& pre.blocks.kept_but_region(post.blocks, level, r as int)
        &&& post.can_retype_large(root, from, to, base, order)
        &&& post.zeroing.active(level, r)
        &&& pre.zeroing.active(level, r) ==> pre.zeroing.cursor@[page as int] < post.zeroing.cursor@[page as int]
        &&& 0 < post.zeroing.cursor@[page as int] < level_pages(level)
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, into: None })
    }

    /// What the step of a large retype that found its block all zero did: the retype was allowed, the
    /// frame capability of that order is the untyped's child in the slot at index to, the one entry the
    /// parent map gains and the only node whose kind, liveness or capability changed, no root entry
    /// changed, every page of the block is zero, the block table changed in the block's region entry
    /// alone, and the step discharges the retype's effect.
    pub open spec fn large_frame_retyped(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize, order: u8) -> bool {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let level = large_level(order);
        &&& pre.can_retype_large(root, from, to, base, order)
        &&& pre.blocks.kept_but_region(post.blocks, level, (base / PAGE_SZ / level_pages(level)) as int)
        &&& pre.view().holds_right(root, parent, Right::Retype)
        &&& post.view().holds(root, child)
        &&& post.payload_of(child) == large_frame_of(base, order)
        &&& post.list.is_child(parent, child)
        &&& post.list.parent@ == pre.list.parent@.insert(child, parent)
        &&& post.list.nodes@[child as int].depth == pre.list.nodes@[parent as int].depth + 1
        &&& post.tables.roots == pre.tables.roots
        &&& Self::caps_frame(pre, post, child, child)
        &&& forall|k: usize| k < pow2(order as nat) ==> #[trigger] holds_zero(post.frames@, (base / PAGE_SZ + k) as usize)
        &&& discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, into: None })
    }

    /// Retypes the free page at `base` as a frame, under the untyped at index `from` of the table at
    /// `root`, with the capability at the empty index `to`. All of these come from user space, and a
    /// refusal changes nothing. The block table refuses a page that is not free.
    pub fn retype_frame(&mut self, root: usize, from: usize, to: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + RETYPE_FRAME_STEPS,
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            Self::same_tree(*old(self), *final(self)),
            final(self).cores == old(self).cores,
            ret == old(self).can_retype_frame(root, from, to, base),
            !ret ==> *final(self) == *old(self),
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).mappings == old(self).mappings,
            ret ==> Self::frame_retyped(*old(self), *final(self), root, from, to, base),
            ret ==> Self::retype_keeps(*old(self), *final(self), old(self).tables.node_of(root, to), (base / PAGE_SZ) as int, 0, None),
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, 0) {
            Some(found) => found,
            None => { return false; },
        };
        if !self.blocks.page_tracked(base / PAGE_SZ) {
            return false;
        }
        let page = base / PAGE_SZ;
        proof {
            lemma2_to64();
            assert(base % PAGE_SZ == 0);
            assert(page * PAGE_SZ == base);
        }
        let taken = self.blocks.try_type(page, 0, ObjectType::Frame, Tracked(steps));
        let Tracked(perms) = match taken {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked mut perm;
        proof {
            assert(0usize < order_pages(0));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * PAGE_SZ);
            assert((page + 0usize) as usize == page);
            perm = perms.tracked_remove(page);
        }
        zero_page(base, Tracked(&mut perm));
        proof {
            self.frames.borrow_mut().tracked_insert(page, perm);
            Self::lemma_tlb_same(pre, *self);
            assert forall|k: int| 0 <= k < 1 implies #[trigger] pre.blocks.pages@[page + k].kind is Free by {
                assert(pre.blocks.pages@[page + 0int].kind is Free);
            }
            lemma_list_pages_used_small_typed(&self.list, &pre.blocks, &self.blocks, page, 1);
            lemma_objects_small_typed(&self.tables, &self.tables, &pre.blocks, &self.blocks, pre.holders@, page, 1);
            lemma_holders_small_typed(&pre.list, &pre.tables, &pre.blocks, &self.blocks, &pre.zeroing, pre.holders@, page, 0);
            lemma_leaf_blocks_small_typed(&self.list, &self.tables, &pre.blocks, &self.blocks, pre.holders@, page, 1);
            lemma_table_pages_small_typed(&self.list, &self.table_pages, &pre.blocks, &self.blocks, page, 1);
            assert forall|x: usize| self.blocks.tracks(x as int) && #[trigger] table_block(&self.blocks, x)
                implies self.table_pages.maps@.contains_key((x * PAGE_SZ) as usize) by {
                assert(x != page);
            }
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] self.blocks.pages@[page + k]).object is Space) by {
                assert(self.blocks.pages@[page as int].object is Frame);
            }
            lemma_spaces_small_typed(&self.list, &self.tables, &self.list, &self.tables, &self.spaces, &pre.blocks, &self.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] self.blocks.pages@[page + k]).object is Thread) by {
                assert(self.blocks.pages@[page as int].object is Frame);
            }
            lemma_threads_small_typed(&self.list, &self.tables, &self.list, &self.tables, &self.threads, &pre.blocks, &self.blocks, page, 1);
            assert forall|k: int| 0 <= k < 1 implies !((#[trigger] self.blocks.pages@[page + k]).object is Process) by {
                assert(self.blocks.pages@[page as int].object is Frame);
            }
            lemma_processes_small_typed(&self.list, &self.tables, &self.list, &self.tables, &self.processes, &pre.blocks, &self.blocks, page, 1);
            assert(self.wf());
            assert(self.view() == pre.view());
            assert(self.frame_block_ready(base, 0)) by {
                assert(!pre.blocks.covered(page as int));
                assert(block_ref(&self.blocks, page) == BlockRef::Small(page));
            }
        }
        let ghost mid = *self;
        self.add_frame_cap(root, from, to, parent, child, base, 0);
        proof {
            let post = *self;
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(child);
            assert forall|r: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, r, i) implies {
                &&& post.tables.has_slot(&post.list, r, i)
                &&& post.tables.node_of(r, i) == pre.tables.node_of(r, i)
                &&& pre.tables.node_of(r, i) != child && !pre.list.nodes@[pre.tables.node_of(r, i) as int].live
                    ==> !post.list.nodes@[pre.tables.node_of(r, i) as int].live
            } by {
                pre.lemma_slot(r, i);
                let n = pre.tables.node_of(r, i);
                pre.lemma_slot_bound(n);
                let leaf = pre.tables.leaf(r, index_entry(i));
                assert(leaf == page_of(n));
                assert(leaf != child);
                assert(post.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
            }
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
                &&& post.is_cap(x)
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
            } by {
                pre.lemma_slot_bound(x);
                assert(mid.is_cap(x));
                assert(x != child);
            }
            assert forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(0))
                implies #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind by {
                assert(post.blocks.pages@[i] == pre.blocks.pages@[i]);
            }
            assert(Self::retype_keeps(pre, post, child, page as int, 0, None));
        }
        true
    }

    /// Takes a large block one step towards a capability. Types the region if nobody has, then zeroes
    /// at most 64 KiB of it. Touches neither the list nor the tables.
    fn zero_large(&mut self, level: Large, r: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: RetypeStep)
        requires
            old(self).wf(),
            r < level_regions(level),
        ensures
            final(steps).count <= old(steps).count + ZERO_LARGE_STEPS,
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            final(self).holders == old(self).holders,
            final(self).cores == old(self).cores,
            final(self).devices == old(self).devices,
            final(self).processes == old(self).processes,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).iommus == old(self).iommus,
            ret is Refused == (!old(self).zeroing.active(level, r) && !old(self).blocks.large_free(level, r as int)),
            ret is Refused ==> *final(self) == *old(self),
            old(self).blocks.kept_but_region(final(self).blocks, level, r as int),
            ret is Done ==> forall|k: usize| k < level_pages(level)
                ==> #[trigger] holds_zero(final(self).frames@, (level_base(level, r) + k) as usize),
            ret is Done ==> forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i)
                ==> final(self).frames@.contains_key(i),
            ret is Done ==> {
                let br = level_ref(level, r);
                &&& !final(self).holders@.contains_key(br)
                &&& block_typed(&final(self).blocks, br)
                &&& block_refs(&final(self).blocks, br) == 1
                &&& !block_dead(&final(self).blocks, br)
                &&& !block_active(&final(self).zeroing, br)
            },
            old(self).zeroing.blocks@.contains_key(level_base(level, r)) ==>
                final(self).zeroing.cursor@[level_base(level, r) as int]
                    <= old(self).zeroing.cursor@[level_base(level, r) as int] + ZERO_CHUNK_PAGES,
            !old(self).zeroing.blocks@.contains_key(level_base(level, r)) && !(ret is Refused) ==>
                final(self).zeroing.cursor@[level_base(level, r) as int] <= ZERO_CHUNK_PAGES,
            ret is Again ==> {
                let b = level_base(level, r);
                &&& final(self).zeroing.active(level, r)
                &&& old(self).zeroing.active(level, r) ==>
                    old(self).zeroing.cursor@[b as int] < final(self).zeroing.cursor@[b as int]
                &&& 0 < final(self).zeroing.cursor@[b as int] < level_pages(level)
            },
    {
        let ghost pre = *old(self);
        proof {
            pre.blocks.lemma_kept_but_region_same(level, r as int);
        }
        let pages = pages_of_level(level);
        let base = r * pages;
        if !self.zeroing.is_active(level, r) {
            let Tracked(perms) = match type_region(&mut self.blocks, level, r) {
                Some(perms) => perms,
                None => { return RetypeStep::Refused; },
            };
            proof {
                Self::lemma_new_region_apart(pre, level, r);
            }
            self.zeroing.begin(level, r, Tracked(perms));
            proof {
                let me = *self;
                assert forall|b: usize| #[trigger] me.zeroing.blocks@.contains_key(b) implies {
                    &&& me.zeroing.blocks@[b] == PAGES_PER_2M ==> {
                        &&& me.blocks.regions_2m@[(b / PAGES_PER_2M) as int].typed
                        &&& !me.blocks.regions_2m@[(b / PAGES_PER_2M) as int].dead
                    }
                    &&& me.zeroing.blocks@[b] == PAGES_PER_1G ==> {
                        &&& me.blocks.regions_1g@[(b / PAGES_PER_1G) as int].typed
                        &&& !me.blocks.regions_1g@[(b / PAGES_PER_1G) as int].dead
                    }
                } by {
                    if b == base {
                        match level {
                            Large::Two => {
                                assert(base == r * PAGES_PER_2M);
                                assert(base / PAGES_PER_2M == r) by (nonlinear_arith)
                                    requires
                                        base == r * PAGES_PER_2M,
                                ;
                            },
                            Large::One => {
                                assert(base == r * PAGES_PER_1G);
                                assert(base / PAGES_PER_1G == r) by (nonlinear_arith)
                                    requires
                                        base == r * PAGES_PER_1G,
                                ;
                            },
                        }
                    } else {
                        assert(pre.zeroing.blocks@.contains_key(b));
                        assert(pre.zeroing.block_level(b));
                        assert(me.zeroing.blocks@[b] == pre.zeroing.blocks@[b]);
                    }
                }
                lemma_holders_region_typed(&pre.list, &pre.tables, &pre.blocks, &me.blocks, &pre.zeroing, &me.zeroing, pre.holders@, level, r);
            }
        }
        let ghost typed = *self;
        proof {
            assert(holders_wf(&typed.list, &typed.tables, &typed.blocks, &typed.zeroing, typed.holders@));
            assert(typed.zeroing.active(level, r));
            assert(pre.zeroing.active(level, r) ==> typed.zeroing == pre.zeroing);
            assert(!pre.zeroing.active(level, r) ==> typed.zeroing.cursor@[base as int] == 0);
            assert(typed.zeroing.blocks@[base] == pages);
        }
        let done = self.zeroing.step(base, pages, Tracked(steps));
        proof {
            lemma_holders_same_active(&typed.list, &typed.tables, &typed.blocks, &typed.zeroing, &self.zeroing, typed.holders@);
        }
        if !done {
            proof {
                lemma_leaf_blocks_same_pages(&pre.list, &pre.tables, &pre.blocks, &self.blocks);
                lemma_leaf_blocks_owned_same_types(&pre.tables, &pre.blocks, &self.blocks);
                lemma_table_pages_same_pages(&pre.list, &pre.table_pages, &pre.blocks, &self.blocks);
                lemma_spaces_same_pages(&pre.list, &pre.tables, &pre.spaces, &pre.blocks, &self.blocks);
                lemma_threads_same_pages(&pre.list, &pre.tables, &pre.threads, &pre.blocks, &self.blocks);
                lemma_processes_same_pages(&pre.list, &pre.tables, &pre.processes, &pre.blocks, &self.blocks);
                assert forall|g: usize| translatable(&pre.blocks, g) implies #[trigger] translatable(&self.blocks, g) by {
                    assert(self.blocks.pages@[g as int] == pre.blocks.pages@[g as int]);
                }
                lemma_entries_translatable_kept(&pre.blocks, &self.blocks, pre.tlb@, pre.iommus.tlb@);
                Self::lemma_zeroing_changed(pre, *self);
                assert(self.zeroing.active(level, r));
                assert(self.zeroing.cursor@[base as int] <= pages);
                assert(typed.zeroing.cursor@[base as int] < self.zeroing.cursor@[base as int]);
            }
            return RetypeStep::Again;
        }
        let ghost mid = *self;
        proof {
            assert(zeroing_typed(&mid.zeroing, &mid.blocks));
            mid.lemma_active_block_ready(level, r);
        }
        let Tracked(zeroed) = self.zeroing.finish(level, r);
        proof {
            lemma_level_pages(level, r);
            self.frames.borrow_mut().tracked_union_prefer_right(zeroed);
            let me = *self;
            assert forall|i: usize| #[trigger] me.frames@.contains_key(i) implies me.frames@[i].addr() == i * PAGE_SZ by {
                if zeroed.dom().contains(i) {
                    assert(holds_zero(zeroed, (base + (i - base) as usize) as usize));
                } else {
                    assert(pre.frames@.contains_key(i));
                }
            }
            assert forall|k: usize| k < pages implies #[trigger] holds_zero(me.frames@, (base + k) as usize) by {
                assert(holds_zero(zeroed, (base + k) as usize));
            }
            assert forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) implies me.frames@.contains_key(i) by {
                assert(i >= base);
                assert(holds_zero(me.frames@, (base + (i - base) as usize) as usize));
            }
            lemma_holders_region_done(&mid.list, &mid.tables, &mid.blocks, &mid.zeroing, &me.zeroing, mid.holders@, level, r);
            lemma_leaf_blocks_same_pages(&pre.list, &pre.tables, &pre.blocks, &me.blocks);
            lemma_leaf_blocks_owned_same_types(&pre.tables, &pre.blocks, &me.blocks);
            lemma_table_pages_same_pages(&pre.list, &pre.table_pages, &pre.blocks, &me.blocks);
            lemma_spaces_same_pages(&pre.list, &pre.tables, &pre.spaces, &pre.blocks, &me.blocks);
            lemma_threads_same_pages(&pre.list, &pre.tables, &pre.threads, &pre.blocks, &me.blocks);
            lemma_processes_same_pages(&pre.list, &pre.tables, &pre.processes, &pre.blocks, &me.blocks);
            assert forall|g: usize| translatable(&pre.blocks, g) implies #[trigger] translatable(&me.blocks, g) by {
                assert(me.blocks.pages@[g as int] == pre.blocks.pages@[g as int]);
            }
            lemma_entries_translatable_kept(&pre.blocks, &me.blocks, pre.tlb@, pre.iommus.tlb@);
            Self::lemma_zeroing_changed(pre, me);
        }
        RetypeStep::Done
    }

    /// A region being zeroed is typed, live and holds one reference, retype's, and has no key.
    proof fn lemma_active_block_ready(&self, level: Large, r: usize)
        requires
            self.zeroing.wf(),
            zeroing_typed(&self.zeroing, &self.blocks),
            holders_wf(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@),
            r < level_regions(level),
            self.zeroing.active(level, r),
        ensures
            !self.holders@.contains_key(level_ref(level, r)),
            block_typed(&self.blocks, level_ref(level, r)),
            block_refs(&self.blocks, level_ref(level, r)) == 1,
            !block_dead(&self.blocks, level_ref(level, r)),
    {
        let base = level_base(level, r);
        let pages = level_pages(level);
        assert(self.zeroing.blocks@.contains_key(base));
        assert(self.zeroing.blocks@[base] == pages);
        match level {
            Large::Two => {
                assert(base == r * PAGES_PER_2M);
                lemma_fundamental_div_mod_converse(base as int, PAGES_PER_2M as int, r as int, 0);
                assert(base / PAGES_PER_2M == r);
            },
            Large::One => {
                assert(base == r * PAGES_PER_1G);
                lemma_fundamental_div_mod_converse(base as int, PAGES_PER_1G as int, r as int, 0);
                assert(base / PAGES_PER_1G == r);
            },
        }
    }

    /// The block of a large frame at base is its region, which zeroing left typed with one reference.
    proof fn lemma_large_block_ready(&self, level: Large, r: usize, base: usize, order: u8)
        requires
            self.blocks.wf(),
            r < level_regions(level),
            base / PAGE_SZ == r * level_pages(level),
            base == (base / PAGE_SZ) * PAGE_SZ,
            order == (match level { Large::Two => 9u8, Large::One => 18u8 }),
            !self.holders@.contains_key(level_ref(level, r)),
            block_typed(&self.blocks, level_ref(level, r)),
            block_refs(&self.blocks, level_ref(level, r)) == 1,
            !block_dead(&self.blocks, level_ref(level, r)),
            !block_active(&self.zeroing, level_ref(level, r)),
            forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> self.frames@.contains_key(i),
        ensures
            self.frame_block_ready(base, order),
    {
        let page = base / PAGE_SZ;
        lemma2_to64();
        match level {
            Large::Two => {
                assert(page == r * PAGES_PER_2M);
                lemma_fundamental_div_mod_converse(page as int, PAGES_PER_2M as int, r as int, 0);
                assert(page / PAGES_PER_2M == r);
                assert(block_ref(&self.blocks, page) == BlockRef::Two(r));
                assert(block_bytes(9) == SIZE_2M);
                assert(base == r * SIZE_2M);
            },
            Large::One => {
                assert(page == r * PAGES_PER_1G);
                lemma_fundamental_div_mod_converse(page as int, PAGES_PER_1G as int, r as int, 0);
                assert(page / PAGES_PER_1G == r);
                lemma_in_1g_block(&self.blocks, page, r);
                assert(pow2(18) == PAGES_PER_1G);
                assert(block_bytes(18) == SIZE_1G);
                assert(base == r * SIZE_1G);
            },
        }
    }

    /// What a retype of the two pages at base as a table leaf did, under the untyped at index from of
    /// the table at root, into the root entry at names: the retype was allowed, the leaf is in that
    /// entry of the position's table and owned by that entry, its hidden node the untyped's child, the
    /// one entry the parent map gains and the only node whose liveness changed, every other node on its
    /// page and every slot in it empty, the tables it had, the list's first node and what retype_keeps
    /// names as they were but that root entry, and the step discharges the retype's effect, into the
    /// table named through a process capability when the position names one.
    pub open spec fn leaf_retyped(pre: Self, post: Self, root: usize, from: usize, at: Position, base: usize) -> bool {
        let parent = pre.tables.node_of(root, from);
        let table = pre.destination_at(root, at.through)->0;
        &&& pre.can_retype_leaf(root, from, at, base)
        &&& pre.view().holds_right(root, parent, Right::Retype)
        &&& post.tables.leaf(table, at.index as int) == base
        &&& post.list.is_child(parent, base)
        &&& post.list.parent@ == pre.list.parent@.insert(base, parent)
        &&& post.list.seq@[0] == pre.list.seq@[0]
        &&& post.list.nodes@[base as int].kind is Hidden
        &&& forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != base ==> {
            &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
            &&& pre.list.nodes@[x].live ==> {
                &&& post.list.nodes@[x].kind == pre.list.nodes@[x].kind
                &&& post.list.nodes@[x].depth == pre.list.nodes@[x].depth
            }
        }
        &&& forall|x: int| base < x < base + NODES_PER_PAGE ==> !#[trigger] post.list.nodes@[x].live
        &&& post.tables.owner@ == pre.tables.owner@.insert(base, (table, at.index as int))
        &&& post.tables.roots@.dom() == pre.tables.roots@.dom()
        &&& forall|i: usize| index_ok(i) && index_entry(i) == at.index as int ==> {
            &&& #[trigger] post.tables.has_slot(&post.list, table, i)
            &&& !post.list.nodes@[post.tables.node_of(table, i) as int].live
        }
        &&& forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x)
        &&& post.processes == pre.processes
        &&& Self::retype_keeps(pre, post, base, (base / PAGE_SZ) as int, 1, Some((table, at.index as int)))
        &&& discharges(
            pre.view(),
            post.view(),
            root,
            Effect::Retype { untyped: parent, object: base, into: pre.through_node(root, at.through) },
        )
    }

    /// Retypes the two free pages at `base` as a table leaf, under the untyped at index `from` of the
    /// table at root, the caller's. The leaf goes in the root entry `at` names: of the caller's own
    /// table, or of the table of a live process the caller holds a capability to with the control
    /// right, which is how a new process, whose table starts with no leaf, comes to have slots. The
    /// untyped is always the caller's own. No capability names a leaf: its first page's node 0 is its
    /// hidden node, a child of the untyped, so revoking the untyped reaches it. Both pages are written
    /// whole, once, so this takes one kernel entry. All of these come from user space, and a refusal
    /// changes nothing. The block table refuses pages that are not free.
    pub fn retype_leaf(&mut self, root: usize, from: usize, at: Position, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + RETYPE_LEAF_STEPS,
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            Self::same_tree(*old(self), *final(self)),
            final(self).cores == old(self).cores,
            final(self).threads == old(self).threads,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            ret == old(self).can_retype_leaf(root, from, at, base),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::leaf_retyped(*old(self), *final(self), root, from, at, base),
            ret ==> final(self).spaces == old(self).spaces,
            ret ==> forall|i: int| old(self).blocks.tracks(i) && !(base / PAGE_SZ <= i < base / PAGE_SZ + 2)
                ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i],
    {
        let ghost pre = *old(self);
        let r = at.index;
        let parent = match self.retype_parent(root, from, base, 1) {
            Some(found) => found,
            None => { return false; },
        };
        let table = match self.find_destination(root, at.through) {
            Some(found) => found,
            None => { return false; },
        };
        proof {
            pre.tables.lemma_root(table);
        }
        if r >= ROOT_ENTRIES || self.tables.entry(table, r) != NO_LEAF || base == NO_LEAF
            || !self.blocks.run_tracked(base / PAGE_SZ, 2) {
            return false;
        }
        proof {
            lemma2_to64();
            assert(block_bytes(1) == LEAF_BYTES);
            assert(base % LEAF_BYTES == 0);
            pre.lemma_slot_bound(parent);
            pre.list.lemma_live_valid(parent);
        }
        if !self.place_leaf(parent, table, r, base, Tracked(steps)) {
            return false;
        }
        proof {
            let post = *self;
            assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
                Self::lemma_leaf_cap(pre, post, base, x);
            }
            Self::lemma_leaf_discharges(pre, post, root, parent, base, pre.through_node(root, at.through));
            Self::lemma_leaf_keeps(pre, post, table, r, base);
        }
        true
    }

    /// A leaf is refused through a thread's capability, through a process's without the control
    /// right, and through one to a dead process, and in the caller's own table is refused as it is
    /// when no other table is named.
    pub proof fn lemma_leaf_refusals(&self, root: usize, from: usize, cap: usize, r: usize, base: usize)
        ensures
            ({
                let c = self.tables.node_of(root, cap);
                ||| !(self.payload_of(c).kind is Process)
                ||| self.payload_of(c).rights & right_bit(Right::Control) == 0
                ||| self.processes.records@[self.payload_of(c).base].value().dead
            }) ==> !self.can_retype_leaf(root, from, Position { through: Some(cap), index: r }, base),
            self.can_retype_leaf(root, from, Position { through: None, index: r }, base) == {
                &&& self.can_retype_under(root, from, base, 1)
                &&& r < ROOT_ENTRIES
                &&& self.tables.leaf(root, r as int) == NO_LEAF
                &&& base != NO_LEAF
                &&& self.blocks.tracks_addr_run(base, 2)
                &&& self.blocks.small_free((base / PAGE_SZ) as int, 1)
            },
    {
    }

    /// Types the two pages at `base` as a table leaf in entry r of the table at root, its hidden node a
    /// child of parent: an untyped's capability when a retype makes it, the list's synthetic root when
    /// boot does. The block table refuses pages that are not free, and a refusal changes nothing.
    pub fn place_leaf(&mut self, parent: usize, root: usize, r: usize, base: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            r < ROOT_ENTRIES,
            old(self).tables.leaf(root, r as int) == NO_LEAF,
            base != NO_LEAF,
            base % LEAF_BYTES == 0,
            old(self).blocks.tracks_addr_run(base, 2),
            base + LEAF_BYTES <= NODE_SPACE,
            parent < NODE_SPACE,
            old(self).list.nodes@[parent as int].live,
            old(self).list.nodes@[parent as int].kind is Capability,
            old(self).list.nodes@[parent as int].depth < MAX_DEPTH,
        ensures
            final(steps).count <= old(steps).count + PLACE_LEAF_STEPS,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).devices == old(self).devices,
            final(self).iommus == old(self).iommus,
            final(self).devices == old(self).devices,
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            final(self).cores == old(self).cores,
            Self::same_tree(*old(self), *final(self)),
            !ret ==> *final(self) == *old(self),
            ret == old(self).blocks.small_free((base / PAGE_SZ) as int, 1),
            ret ==> {
                &&& Self::leaf_step(*old(self), *final(self), base)
                &&& final(self).list.parent@ == old(self).list.parent@.insert(base, parent)
                &&& final(self).tables.leaf(root, r as int) == base
                &&& forall|e: int| e != r ==> #[trigger] final(self).tables.leaf(root, e) == old(self).tables.leaf(root, e)
                &&& final(self).tables.roots@.dom() == old(self).tables.roots@.dom()
                &&& forall|t: usize| t != root && #[trigger] old(self).tables.roots@.contains_key(t)
                    ==> final(self).tables.roots@[t] == old(self).tables.roots@[t]
                &&& final(self).tables.owner@ == old(self).tables.owner@.insert(base, (root, r as int))
                &&& forall|t: usize, i: usize| #[trigger] old(self).tables.has_slot(&old(self).list, t, i)
                    ==> final(self).tables.has_slot(&final(self).list, t, i)
                        && final(self).tables.node_of(t, i) == old(self).tables.node_of(t, i)
                &&& final(self).list.is_child(parent, base)
                &&& final(self).list.seq@[0] == old(self).list.seq@[0]
                &&& final(self).list.nodes@[base as int].live
                &&& final(self).list.nodes@[base as int].kind is Hidden
                &&& final(self).list.nodes@[base as int].depth == old(self).list.nodes@[parent as int].depth + 1
                &&& forall|x: int| #![trigger final(self).list.nodes@[x]] 0 <= x < NODE_SPACE && x != base ==> {
                    &&& final(self).list.nodes@[x].live == old(self).list.nodes@[x].live
                    &&& old(self).list.nodes@[x].live ==> {
                        &&& final(self).list.nodes@[x].kind == old(self).list.nodes@[x].kind
                        &&& final(self).list.nodes@[x].depth == old(self).list.nodes@[x].depth
                    }
                }
                &&& forall|i: usize| index_ok(i) && index_entry(i) == r as int ==> {
                    &&& #[trigger] final(self).tables.has_slot(&final(self).list, root, i)
                    &&& !final(self).list.nodes@[final(self).tables.node_of(root, i) as int].live
                }
                &&& forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x)
                &&& forall|x: usize| #[trigger] old(self).is_cap(x) ==> final(self).payload_of(x) == old(self).payload_of(x)
                &&& final(self).list.pages@.dom() == old(self).list.pages@.dom().insert(base)
                &&& final(self).blocks.pages@[(base / PAGE_SZ) as int].kind is Base
                &&& final(self).blocks.pages@[(base / PAGE_SZ) as int].object is TableLeaf
                &&& final(self).blocks.pages@[base / PAGE_SZ + 1].kind is Member
                &&& final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@
                &&& final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@
                &&& forall|i: int| old(self).blocks.tracks(i) && !(base / PAGE_SZ <= i < base / PAGE_SZ + 2)
                    ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i]
                &&& final(self).threads == old(self).threads
                &&& final(self).processes == old(self).processes
                &&& final(self).spaces == old(self).spaces
                &&& final(self).table_pages == old(self).table_pages
            },
    {
        let ghost pre = *old(self);
        let page = base / PAGE_SZ;
        proof {
            lemma2_to64();
            assert(page % 2 == 0 && page * PAGE_SZ == base) by (nonlinear_arith)
                requires
                    base % LEAF_BYTES == 0,
                    page == base / PAGE_SZ,
            ;
        }
        let Tracked(perms) = match self.blocks.try_type(page, 1, ObjectType::TableLeaf, Tracked(&mut *steps)) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked first;
        let tracked second;
        proof {
            assert(0usize < order_pages(1));
            assert(1usize < order_pages(1));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * PAGE_SZ);
            assert(perms[(page + 1usize) as usize].addr() == (page + 1usize) * PAGE_SZ);
            assert((page + 0usize) as usize == page);
            first = perms.tracked_remove(page);
            second = perms.tracked_remove((page + 1) as usize);
        }
        let ghost before_list = self.list;
        let nodes = init_node_page(base, Tracked(first), Tracked(&mut *steps));
        proof {
            assert(!pre.list.pages@.dom().contains(base)) by {
                assert(base / PAGE_SZ == page);
                assert(pre.blocks.pages@[page + 0int].kind is Free);
            }
            pre.list.lemma_live_valid(parent);
            pre.list.lemma_valid_bound(parent);
        }
        self.list.add_page(base, nodes);
        let ghost mid = self.list;
        proof {
            assert(mid.valid(base));
            mid.lemma_seq_fits();
            mid.lemma_valid_bound(base);
            assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]);
        }
        self.list.derive(parent, base, NodeKind::Hidden);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
            assert(!pre.tables.owner@.contains_key(base)) by {
                if pre.tables.owner@.contains_key(base) {
                    pre.tables.lemma_leaf(&pre.list, base);
                }
            }
        }
        self.tables.add_leaf(&self.list, root, r, base, Tracked(second), Tracked(steps));
        proof {
            let post = *self;
            assert forall|x: usize| #[trigger] pre.list.valid(x) && x != base implies {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            } by {
                pre.list.lemma_valid_bound(x);
                assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
                assert(post.list.nodes@[x as int] == post.list.nodes@[x as int]);
            }
            assert forall|x: usize| base < x < base + NODES_PER_PAGE implies !#[trigger] post.list.nodes@[x as int].live by {
                assert(mid.valid(x));
                mid.lemma_valid_bound(x);
                assert(!mid.nodes@[x as int].live);
            }
            assert(Self::leaf_step(pre, post, base));
            Self::lemma_leaf_caps_wf(pre, post, base);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_leaf_list_pages(pre, post, base, page);
            Self::lemma_leaf_objects(pre, post, base, page);
            Self::lemma_leaf_holders(pre, post, mid, base, page);
            Self::lemma_leaf_mappings(pre, post, mid, base, page);
            Self::lemma_leaf_blocks_leaf_added(pre, post, base, page);
            Self::lemma_leaf_table_pages(pre, post, base, page);
            Self::lemma_leaf_nodes(pre, post, mid, parent, base);
            Self::lemma_leaf_first(pre, post, base);
            Self::lemma_leaf_slots(pre, post, base);
            Self::lemma_table_nodes_frame(pre, post, base, base);
            Self::lemma_space_nodes_frame(pre, post, base, base);
            assert forall|x: usize| x < NODE_SPACE && #[trigger] post.list.valid(x) && !pre.list.valid(x) && x != base
                implies !(post.list.nodes@[x as int].live && post.list.nodes@[x as int].kind is Binding) by {
                assert(page_of(x) == base);
            }
            lemma_same_bindings_frame(&pre.list, &post.list, base, base);
            lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
            assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
                Self::lemma_leaf_cap(pre, post, base, x);
            }
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.payload_of(x) == pre.payload_of(x) by {
                Self::lemma_leaf_cap(pre, post, base, x);
            }
            assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Space) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is TableLeaf);
                }
            }
            lemma_spaces_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page, 2);
            assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Thread) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is TableLeaf);
                }
            }
            lemma_threads_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page, 2);
            assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Process) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is TableLeaf);
                }
            }
            lemma_processes_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page, 2);
            Self::lemma_devices_same_caps(pre, post);
            assert(!pre.list.nodes@[base as int].live) by {
                if pre.list.nodes@[base as int].live {
                    pre.list.lemma_live_valid(base);
                    assert(mid.nodes@[base as int] == pre.list.nodes@[base as int]);
                }
            }
            assert(post.list.parent@ == pre.list.parent@.insert(base, parent));
            Self::lemma_binding_parents_same_caps(pre, post);
            assert(post.wf());
            Self::lemma_bound_threads_same(pre, post);
            assert forall|i: usize| index_ok(i) && index_entry(i) == r as int implies {
                &&& #[trigger] post.tables.has_slot(&post.list, root, i)
                &&& !post.list.nodes@[post.tables.node_of(root, i) as int].live
            } by {
                assert(post.tables.roots@.contains_key(root));
                assert(post.tables.node_of(root, i) == base + index_slot(i));
                assert(base < post.tables.node_of(root, i) < base + NODES_PER_PAGE);
            }
            assert forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != base implies {
                &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
                &&& pre.list.nodes@[x].live ==> {
                    &&& post.list.nodes@[x].kind == pre.list.nodes@[x].kind
                    &&& post.list.nodes@[x].depth == pre.list.nodes@[x].depth
                }
            } by {
                assert(mid.nodes@[x].live == pre.list.nodes@[x].live);
                if pre.list.nodes@[x].live {
                    pre.list.lemma_live_valid(x as usize);
                    assert(mid.nodes@[x] == pre.list.nodes@[x]);
                }
            }
            assert(post.blocks.pages@[page + 1int].kind is Member) by {
                post.blocks.lemma_member_of(page as int, page + 1int);
            }
            // A slot pre had is in a leaf live before, so not the new one, and still live.
            assert forall|t: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, t, i)
                implies pre.tables.has_slot(&post.list, t, i) by {
                let l = pre.tables.leaf(t, index_entry(i));
                pre.lemma_slot(t, i);
                pre.lemma_slot_bound(pre.tables.node_of(t, i));
                assert(l <= pre.tables.node_of(t, i));
                assert(l != base);
                assert(post.list.nodes@[l as int].live);
            }
            assert(post.list.is_child(parent, base));
            assert(post.list.nodes@[base as int].depth == pre.list.nodes@[parent as int].depth + 1);
            assert(post.list.pages@.dom() == pre.list.pages@.dom().insert(base));
            assert(post.tables.owner@ == pre.tables.owner@.insert(base, (root, r as int)));
        }
        true
    }

    /// The list's pages after a leaf's retype: those it held lie outside the new block, and the new page
    /// is the block's base.
    proof fn lemma_leaf_list_pages(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            base / PAGE_SZ == page,
            pre.blocks.tracks_run(page as int, 2),
            pre.blocks.pages@[page + 0int].kind is Free,
            pre.blocks.pages@[page + 1int].kind is Free,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TableLeaf,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.list.pages@.dom() == pre.list.pages@.dom().insert(base),
        ensures
            list_pages_used(&post.list, &post.blocks),
    {
        assert forall|k: int| 0 <= k < 2 implies #[trigger] pre.blocks.pages@[page + k].kind is Free by {
            if k == 0 { assert(pre.blocks.pages@[page + 0int].kind is Free); }
        }
        lemma_list_pages_used_small_typed(&pre.list, &pre.blocks, &post.blocks, page, 2);
        lemma_list_pages_used_page_added(&pre.list, &post.list, &post.blocks, base);
    }

    /// The table pages after a leaf's retype: none lay in the block, the new page is no table block, and
    /// every table page's node is as it was.
    proof fn lemma_leaf_table_pages(pre: Self, post: Self, base: usize, page: usize)
        requires
            Self::leaf_step(pre, post, base),
            post.blocks.wf(),
            post.table_pages == pre.table_pages,
            base / PAGE_SZ == page,
            pre.blocks.tracks_run(page as int, 2),
            !pre.list.pages@.dom().contains(base),
            pre.blocks.pages@[page + 0int].kind is Free,
            pre.blocks.pages@[page + 1int].kind is Free,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TableLeaf,
            post.blocks.pages@[page as int].order == 1,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        assert forall|k: int| 0 <= k < 2 implies #[trigger] pre.blocks.pages@[page + k].kind is Free by {
            if k == 0 { assert(pre.blocks.pages@[page + 0int].kind is Free); }
        }
        lemma_table_pages_small_typed(&pre.list, &pre.table_pages, &pre.blocks, &post.blocks, page, 2);
        post.blocks.lemma_member_of(page as int, page + 1int);
        assert forall|x: usize| post.blocks.tracks(x as int) && #[trigger] table_block(&post.blocks, x)
            implies pre.table_pages.maps@.contains_key((x * PAGE_SZ) as usize) by {
            assert(!(page <= x < page + 2));
        }
        assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) implies {
            &&& post.list.nodes@[t as int].live == pre.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind == pre.list.nodes@[t as int].kind
        } by {
            pre.lemma_table_page_valid(t);
            assert(t != base);
        }
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
    }

    /// The list's first node stays outside every leaf after a leaf's retype: it is live, so its page
    /// was one the list held, and the new leaf's page was not.
    proof fn lemma_leaf_first(pre: Self, post: Self, base: usize)
        requires
            pre.wf(),
            !pre.list.pages@.dom().contains(base),
            exists|e: (usize, int)| post.tables.owner@ == pre.tables.owner@.insert(base, e),
            post.list.seq@[0] == pre.list.seq@[0],
        ensures
            first_node_outside_leaves(&post.list, &post.tables),
    {
        let n = pre.list.seq@[0];
        pre.list.lemma_link(0);
        pre.list.lemma_live_valid(n);
        assert(pre.list.pages@.dom().contains(page_of(n)));
        assert(page_of(n) != base);
        assert(!pre.tables.owner@.contains_key(page_of(n)));
    }

    /// A live node in a leaf's slot stays a capability after a leaf's retype: the new leaf's slots
    /// are not live, and a node in an older leaf keeps its kind.
    proof fn lemma_leaf_slots(pre: Self, post: Self, base: usize)
        requires
            Self::leaf_step(pre, post, base),
        ensures
            leaf_slots_are_capabilities(&post.list, &post.tables),
    {
        assert forall|n: usize| #[trigger] post.list.nodes@[n as int].live
            && post.tables.owner@.contains_key(page_of(n)) && n % PAGE_SZ != 0 && n % PAGE_SZ < NODES_PER_PAGE
            implies post.list.nodes@[n as int].kind is Capability by {
            if page_of(n) == base {
                assert(base < n < base + NODES_PER_PAGE);
                assert(!post.list.nodes@[n as int].live);
            } else {
                assert(pre.tables.owner@.contains_key(page_of(n)));
                pre.tables.lemma_leaf(&pre.list, page_of(n));
                assert(pre.list.valid(n));
                assert(n != base);
                assert(pre.list.nodes@[n as int].live);
            }
        }
    }

    /// The hidden nodes and the parents after a leaf's retype: the new node is the leaf's, hidden
    /// under a capability, and every other node's kind and parent are as they were.
    proof fn lemma_leaf_nodes(pre: Self, post: Self, mid: Tree, parent: usize, base: usize)
        requires
            Self::leaf_step(pre, post, base),
            mid.wf(),
            post.list.wf(),
            mid.seq == pre.list.seq,
            mid.parent == pre.list.parent,
            forall|i: usize| #[trigger] pre.list.valid(i) ==> mid.nodes@[i as int] == pre.list.nodes@[i as int],
            forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] mid.nodes@[i].live == pre.list.nodes@[i].live,
            parent < NODE_SPACE,
            pre.list.nodes@[parent as int].live,
            pre.list.nodes@[parent as int].kind is Capability,
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.list.parent@ == mid.parent@.insert(base, parent),
            post.list.seq@[0] == mid.seq@[0],
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
            },
            post.table_pages == pre.table_pages,
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            if x != base {
                assert(mid.nodes@[x as int].live);
                pre.list.lemma_live_valid(x);
                assert(pre.list.nodes@[x as int].kind is Hidden);
            }
        }
        assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]) by {
            pre.list.lemma_live_valid(parent);
        }
        assert(!mid.nodes@[base as int].live);
        lemma_parents_same_live(pre.list, mid);
        lemma_parents_derived(mid, post.list, parent, base);
    }

    /// The slots and the holders after a leaf's retype: no capability changed, and the two pages typed
    /// held no frame.
    proof fn lemma_leaf_holders(pre: Self, post: Self, mid: Tree, leaf: usize, page: usize)
        requires
            Self::leaf_step(pre, post, leaf),
            post.list.seq@[0] == pre.list.seq@[0],
            post.list.nodes@[leaf as int].kind is Hidden,
            forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] mid.nodes@[i].live == pre.list.nodes@[i].live,
            forall|i: int| 0 <= i < NODE_SPACE && i != leaf ==> #[trigger] post.list.nodes@[i].live == mid.nodes@[i].live,
            post.zeroing == pre.zeroing,
            post.holders == pre.holders,
            page % (order_pages(1) as usize) == 0,
            pre.blocks.tracks_run(page as int, order_pages(1)),
            forall|k: int| 0 <= k < order_pages(1) ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            !pre.blocks.covered(page as int),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(1))
                ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            capability_nodes_are_slots(&post.list, &post.tables),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
    {
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            && (pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)) by {
            Self::lemma_leaf_cap(pre, post, leaf, x);
        }
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Capability && x != post.list.seq@[0]
            implies post.tables.is_cap(&post.list, x) by {
            assert(x != leaf);
            assert(pre.list.nodes@[x as int].live);
            pre.list.lemma_live_valid(x);
            assert(pre.list.nodes@[x as int].kind is Capability);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        lemma_holders_small_typed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, page, 1);
        assert forall|i: usize| i < NODE_SPACE implies
            (post.list.nodes@[i as int].live && post.list.nodes@[i as int].kind is Mapping)
                == (pre.list.nodes@[i as int].live && pre.list.nodes@[i as int].kind is Mapping) by {
            if i != leaf {
                if pre.list.nodes@[i as int].live {
                    pre.list.lemma_live_valid(i);
                } else {
                    assert(!mid.nodes@[i as int].live);
                }
            }
        }
        assert(same_mapping_nodes(&pre.list, &post.list));
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &post.blocks, &pre.zeroing, pre.holders@);
    }

    /// The mappings after a leaf's retype: no mapping node, parent, capability or holder changed, the
    /// block typed held no frame, and no table changed.
    proof fn lemma_leaf_mappings(pre: Self, post: Self, mid: Tree, leaf: usize, page: usize)
        requires
            Self::leaf_step(pre, post, leaf),
            post.list.nodes@[leaf as int].kind is Hidden,
            forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] mid.nodes@[i].live == pre.list.nodes@[i].live,
            forall|i: int| 0 <= i < NODE_SPACE && i != leaf ==> #[trigger] post.list.nodes@[i].live == mid.nodes@[i].live,
            forall|x: usize| x != leaf && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == pre.list.parent@[x],
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            post.holders == pre.holders,
            post.mappings == pre.mappings,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            page % (order_pages(1) as usize) == 0,
            pre.blocks.tracks_run(page as int, order_pages(1)),
            forall|k: int| 0 <= k < order_pages(1) ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            !pre.blocks.covered(page as int),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + order_pages(1))
                ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert forall|i: usize| i < NODE_SPACE implies
            (post.list.nodes@[i as int].live && post.list.nodes@[i as int].kind is Mapping)
                == (pre.list.nodes@[i as int].live && pre.list.nodes@[i as int].kind is Mapping) by {
            if i != leaf {
                if pre.list.nodes@[i as int].live {
                    pre.list.lemma_live_valid(i);
                } else {
                    assert(!mid.nodes@[i as int].live);
                }
            }
        }
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            Self::lemma_leaf_cap(pre, post, leaf, x);
        }
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
            implies post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n] by {
            pre.lemma_mapping_node(n);
        }
        Self::lemma_mappings_grown(pre, post, page, 1);
    }

    /// The leaves' blocks after a leaf's retype: the new leaf's node is live and hidden, and its block
    /// holds the one reference its typing took. Every other leaf's block and node are as they were.
    proof fn lemma_leaf_blocks_leaf_added(pre: Self, post: Self, base: usize, page: usize)
        requires
            Self::leaf_step(pre, post, base),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            base / PAGE_SZ == page,
            pre.blocks.tracks_run(page as int, 2),
            pre.blocks.pages@[page + 0int].kind is Free,
            pre.blocks.pages@[page + 1int].kind is Free,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
    {
        assert forall|k: int| 0 <= k < 2 implies #[trigger] pre.blocks.pages@[page + k].kind is Free by {
            if k == 0 { assert(pre.blocks.pages@[page + 0int].kind is Free); }
        }
        lemma_leaf_blocks_small_typed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, pre.holders@, page, 2);
        let e = choose|e: (usize, int)| post.tables.owner@ == pre.tables.owner@.insert(base, e);
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live ==> {
                &&& post.list.nodes@[l as int].kind is Hidden
                &&& post.blocks.pages@[(l / PAGE_SZ) as int].refs == 1
                &&& !post.blocks.pages@[(l / PAGE_SZ) as int].dead
            }
            &&& !post.list.nodes@[l as int].live ==> {
                &&& post.blocks.pages@[(l / PAGE_SZ) as int].refs == 0
                &&& post.blocks.pages@[(l / PAGE_SZ) as int].dead
            }
        } by {
            if l != base {
                assert(pre.tables.owner@.contains_key(l));
                pre.tables.lemma_leaf(&pre.list, l);
                assert(page_of(l) == l);
                assert(pre.list.valid(l));
                assert(post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live);
                assert(post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind);
            }
        }
    }

    /// The types after a leaf's retype: its block is new, and only its own owner entry is.
    proof fn lemma_leaf_objects(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            post.blocks.wf(),
            pre.blocks.tracks(page as int),
            pre.blocks.tracks_run(page as int, 2),
            base % LEAF_BYTES == 0,
            base / PAGE_SZ == page,
            post.holders == pre.holders,
            pre.blocks.pages@[page + 0int].kind is Free,
            pre.blocks.pages@[page + 1int].kind is Free,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].order == 1,
            post.blocks.pages@[page as int].object is TableLeaf,
            post.blocks.pages@[page as int].refs == 1,
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            exists|e: (usize, int)| post.tables.owner@ == pre.tables.owner@.insert(base, e),
        ensures
            objects_wf(&post.tables, &post.blocks, post.holders@),
    {
        post.blocks.lemma_member_of(page as int, page + 1int);
        assert forall|k: int| 0 < k < 2 implies (#[trigger] post.blocks.pages@[page + k]).kind is Member by {
            assert(k == 1);
        }
        assert forall|k: int| 0 <= k < 2 implies #[trigger] pre.blocks.pages@[page + k].kind is Free by {
            if k == 0 { assert(pre.blocks.pages@[page + 0int].kind is Free); }
        }
        lemma_leaf_page(base);
        let e = choose|e: (usize, int)| post.tables.owner@ == pre.tables.owner@.insert(base, e);
        assert(post.tables.owner@.contains_key(base));
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies l == base || pre.tables.owner@.contains_key(l) by {}
        lemma_objects_small_typed(&pre.tables, &post.tables, &pre.blocks, &post.blocks, pre.holders@, page, 2);
    }

    /// What a leaf's retype does to the fields the view reads: nothing changes but the new page, none of
    /// whose slots is live.
    pub open spec fn leaf_step(pre: Self, post: Self, leaf: usize) -> bool {
        &&& pre.wf()
        &&& leaf % PAGE_SZ == 0
        &&& !pre.tables.owner@.contains_key(leaf)
        &&& !pre.list.nodes@[leaf as int].live
        &&& leaf < NODE_SPACE
        &&& exists|e: (usize, int)| post.tables.owner@ == pre.tables.owner@.insert(leaf, e)
        &&& post.tables.payloads@ == pre.tables.payloads@.insert(leaf, post.tables.payloads@[leaf])
        &&& forall|x: usize| #[trigger] pre.list.valid(x) && x != leaf ==> {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        }
        &&& forall|x: usize| leaf < x < leaf + NODES_PER_PAGE ==> !#[trigger] post.list.nodes@[x as int].live
    }

    /// What a leaf's retype leaves as it was: its hidden node is the only node whose liveness changed
    /// and the depth of every live node is as it was, its root entry is the only one filled, and the
    /// block table's pages outside its two are as they were.
    proof fn lemma_leaf_keeps(pre: Self, post: Self, table: usize, r: usize, base: usize)
        requires
            pre.wf(),
            base % PAGE_SZ == 0,
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
            forall|t: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, t, i)
                ==> post.tables.has_slot(&post.list, t, i) && post.tables.node_of(t, i) == pre.tables.node_of(t, i),
            forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != base ==> {
                &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
                &&& pre.list.nodes@[x].live ==> post.list.nodes@[x].depth == pre.list.nodes@[x].depth
            },
            forall|e: int| e != r ==> #[trigger] post.tables.leaf(table, e) == pre.tables.leaf(table, e),
            forall|t: usize| t != table && #[trigger] pre.tables.roots@.contains_key(t)
                ==> post.tables.roots@[t] == pre.tables.roots@[t],
            post.tables.roots@.dom() == pre.tables.roots@.dom(),
            post.processes == pre.processes,
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|i: int| pre.blocks.tracks(i) && !(base / PAGE_SZ <= i < base / PAGE_SZ + 2)
                ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            Self::retype_keeps(pre, post, base, (base / PAGE_SZ) as int, 1, Some((table, r as int))),
    {
        assert forall|t: usize, i: usize| #[trigger] pre.tables.has_slot(&pre.list, t, i) implies {
            &&& post.tables.has_slot(&post.list, t, i)
            &&& post.tables.node_of(t, i) == pre.tables.node_of(t, i)
            &&& pre.tables.node_of(t, i) != base && !pre.list.nodes@[pre.tables.node_of(t, i) as int].live
                ==> !post.list.nodes@[pre.tables.node_of(t, i) as int].live
        } by {
            pre.lemma_slot(t, i);
            pre.lemma_slot_bound(pre.tables.node_of(t, i));
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
            &&& post.is_cap(x)
            &&& post.payload_of(x) == pre.payload_of(x)
            &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
        } by {
            pre.lemma_slot_bound(x);
            assert(x != base);
            assert(post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth);
        }
        assert forall|t: usize, e: int| pre.tables.roots@.contains_key(t) && 0 <= e < ROOT_ENTRIES
            && Some((table, r as int)) != Some((t, e)) implies #[trigger] post.tables.leaf(t, e) == pre.tables.leaf(t, e) by {
            if t != table {
                assert(post.tables.roots@[t] == pre.tables.roots@[t]);
            } else {
                assert(e != r);
            }
        }
        assert forall|i: int| pre.blocks.tracks(i) && !((base / PAGE_SZ) as int <= i < (base / PAGE_SZ) as int + order_pages(1))
            implies #[trigger] post.blocks.pages@[i].kind == pre.blocks.pages@[i].kind by {
            assert(post.blocks.pages@[i] == pre.blocks.pages@[i]);
        }
    }

    /// So the capabilities, and what they say, are as they were.
    proof fn lemma_leaf_cap(pre: Self, post: Self, leaf: usize, x: usize)
        requires
            Self::leaf_step(pre, post, leaf),
        ensures
            post.is_cap(x) == pre.is_cap(x),
            pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
            pre.is_cap(x) ==> post.tables.owner@[page_of(x)] == pre.tables.owner@[page_of(x)],
    {
        if page_of(x) == leaf {
            if x % PAGE_SZ != 0 && x % PAGE_SZ < NODES_PER_PAGE {
                assert(leaf < x < leaf + NODES_PER_PAGE);
            }
        } else if pre.tables.owner@.contains_key(page_of(x)) && x % PAGE_SZ < NODES_PER_PAGE {
            pre.lemma_slot_bound(x);
            assert(x != leaf);
        }
    }

    proof fn lemma_leaf_caps_wf(pre: Self, post: Self, leaf: usize)
        requires
            Self::leaf_step(pre, post, leaf),
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
    {
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) implies {
            &&& cap_wf(post.tables.payload_of(n))
            &&& control_named(post.tables.payload_of(n))
        } by {
            Self::lemma_leaf_cap(pre, post, leaf, n);
            assert(post.is_cap(n));
            assert(pre.tables.is_cap(&pre.list, n));
        }
    }

    /// The view of the step: every capability is as it was, and the only new parent entry is the hidden
    /// node's, which no capability descends from. That holds whichever table the leaf went into, so
    /// control of the process it went into adds to the step's authority and to nothing else.
    proof fn lemma_leaf_discharges(pre: Self, post: Self, root: usize, parent: usize, leaf: usize, into: Option<usize>)
        requires
            Self::leaf_step(pre, post, leaf),
            Self::same_tree(pre, post),
            post.list.parent@ == pre.list.parent@.insert(leaf, parent),
            post.devices == pre.devices,
            pre.view().holds_right(root, parent, Right::Retype),
            pre.view().covers(parent, leaf),
            into is Some ==> pre.view().holds_right(root, into->0, Right::Control),
        ensures
            discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: leaf, into }),
    {
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            Self::lemma_leaf_cap(pre, post, leaf, x);
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
            &&& post.payload_of(x) == pre.payload_of(x)
            &&& post.tables.owner@[page_of(x)] == pre.tables.owner@[page_of(x)]
        } by {
            Self::lemma_leaf_cap(pre, post, leaf, x);
        }
        Self::lemma_hidden_added_discharges(pre, post, root, parent, leaf);
        let (own, other) = (
            Effect::Retype { untyped: parent, object: leaf, into: None },
            Effect::Retype { untyped: parent, object: leaf, into },
        );
        assert(discharges(pre.view(), post.view(), root, own));
        assert forall|o: ObjectId| #[trigger] State::changed(pre.view(), post.view(), o) implies may_change(pre.view(), other, o) by {
            assert(may_change(pre.view(), own, o));
        }
        assert forall|n: NodeId| #[trigger] State::removed(pre.view(), post.view(), n) implies may_remove(pre.view(), root, other, n) by {
            assert(may_remove(pre.view(), root, own, n));
        }
        assert forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) && !pre.view().reach(r, o)
            implies may_grow(pre.view(), root, other, r, o) by {
            assert(may_grow(pre.view(), root, own, r, o));
        }
    }

    /// A region just typed shares no page with a block being zeroed: its pages were not covered, and
    /// every page of a block being zeroed is.
    proof fn lemma_new_region_apart(pre: Self, level: Large, r: usize)
        requires
            pre.wf(),
            r < level_regions(level),
            forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                ==> !#[trigger] pre.blocks.covered(i),
        ensures
            forall|b: usize| #[trigger] pre.zeroing.blocks@.contains_key(b) ==>
                level_base(level, r) + level_pages(level) <= b || b + pre.zeroing.blocks@[b] <= level_base(level, r),
    {
        let base = level_base(level, r);
        let pages = level_pages(level);
        assert forall|b: usize| #[trigger] pre.zeroing.blocks@.contains_key(b) implies
            base + pages <= b || b + pre.zeroing.blocks@[b] <= base by {
            assert(pre.zeroing.block_level(b));
            if !(base + pages <= b || b + pre.zeroing.blocks@[b] <= base) {
                let m = if base < b { b as int } else { base as int };
                assert(!pre.blocks.covered(m));
                if pre.zeroing.blocks@[b] == PAGES_PER_2M {
                    assert(region_2m(m) == (b / PAGES_PER_2M) as int);
                } else {
                    assert(region_1g(m) == (b / PAGES_PER_1G) as int);
                }
            }
        }
    }

    /// Retypes the 2M or 1G block at `base` as a frame, a step at a time. A later call naming the same
    /// block, by any holder of an untyped covering it, goes on from where this one stopped, so an
    /// abandoned block is not lost. The capability appears on the step that finds the block all zero.
    pub fn retype_large_frame(&mut self, root: usize, from: usize, to: usize, base: usize, order: u8, Tracked(steps): Tracked<&mut Steps>) -> (ret: RetypeStep)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + RETYPE_LARGE_FRAME_STEPS,
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            Self::same_tree(*old(self), *final(self)),
            final(self).cores == old(self).cores,
            final(self).processes == old(self).processes,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).iommus == old(self).iommus,
            ret is Refused == !old(self).can_retype_large(root, from, to, base, order),
            ret is Refused ==> *final(self) == *old(self),
            old(self).zeroing.blocks@.contains_key(base / PAGE_SZ) ==>
                final(self).zeroing.cursor@[(base / PAGE_SZ) as int]
                    <= old(self).zeroing.cursor@[(base / PAGE_SZ) as int] + ZERO_CHUNK_PAGES,
            !old(self).zeroing.blocks@.contains_key(base / PAGE_SZ) && !(ret is Refused) ==>
                final(self).zeroing.cursor@[(base / PAGE_SZ) as int] <= ZERO_CHUNK_PAGES,
            ret is Again ==> Self::large_frame_zeroing(*old(self), *final(self), root, from, to, base, order),
            ret is Done ==> Self::large_frame_retyped(*old(self), *final(self), root, from, to, base, order),
            ret is Done ==> {
                let level = large_level(order);
                let br = level_ref(level, base / PAGE_SZ / level_pages(level));
                &&& block_typed(&final(self).blocks, br)
                &&& block_refs(&final(self).blocks, br) == 1
                &&& !block_dead(&final(self).blocks, br)
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, order) {
            Some(found) => found,
            None => { return RetypeStep::Refused; },
        };
        let (level, r) = match large_region(base, order) {
            Some(found) => found,
            None => { return RetypeStep::Refused; },
        };
        let page = base / PAGE_SZ;
        let step = self.zero_large(level, r, Tracked(steps));
        match step {
            RetypeStep::Refused => { return RetypeStep::Refused; },
            RetypeStep::Again => {
                proof {
                    assert(self.view() == pre.view());
                    assert(pre.view().holds_right(root, parent, Right::Retype));
                    pre.lemma_retype_covers(root, from, base, order);
                    assert(level == large_level(order));
                    assert(self.can_retype(root, from, to, base, order));
                    assert(self.can_retype_large(root, from, to, base, order));
                }
                return RetypeStep::Again;
            },
            RetypeStep::Done => {},
        }
        proof {
            assert(self.view() == pre.view());
            assert(self.can_retype(root, from, to, base, order));
            assert(page == r * level_pages(level));
            assert(base == page * PAGE_SZ);
            self.lemma_large_block_ready(level, r, base, order);
        }
        self.add_frame_cap(root, from, to, parent, child, base, order);
        RetypeStep::Done
    }
}

} // verus!
