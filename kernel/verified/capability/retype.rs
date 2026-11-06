//! Retyping free memory under an untyped. Here a 4K frame: the page is zeroed at once, and the frame
//! capability is a child of the untyped in a slot the caller names, so revoking the untyped reaches it.
//! See the design on atmo-6x9.6.7, sections 1, 3 and 6.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::derive::*;
use crate::capability::kernel::CapKernel;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::capability::zero::*;
use crate::define::*;
use crate::pptr::*;

/// Read, write and execute.
pub const FRAME_RIGHTS: u32 = 7;

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
        },
{
    let ghost pre = *old(blocks);
    match level {
        Large::Two => {
            let ret = blocks.try_type_2m(r);
            proof {
                if ret is Some {
                    assert forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                        implies !#[trigger] pre.covered(i) by {
                        assert(pre.pages@[i].kind is Free);
                    }
                }
            }
            ret
        },
        Large::One => {
            let ret = blocks.try_type_1g(r);
            proof {
                if ret is Some {
                    assert forall|i: int| level_base(level, r) <= i < level_base(level, r) + level_pages(level)
                        implies !#[trigger] pre.covered(i) by {
                        assert(pre.pages@[i].kind is Free);
                    }
                }
            }
            ret
        },
    }
}

impl CapKernel {
    /// The refusals every retype has: an index that names no slot, a parent that is not a capability
    /// to an untyped, without the retype right or at the deepest depth, a slot in use, or a block
    /// outside the untyped's.
    pub open spec fn can_retype(&self, root: usize, from: usize, to: usize, base: usize, order: u8) -> bool {
        let parent = self.tables.node_of(root, from);
        let child = self.tables.node_of(root, to);
        &&& self.tables.has_slot(root, from)
        &&& self.tables.has_slot(root, to)
        &&& self.is_cap(parent)
        &&& self.payload_of(parent).kind is Untyped
        &&& self.payload_of(parent).rights & right_bit(Right::Retype) != 0
        &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
        &&& !self.list.nodes@[child as int].live
        &&& block_within(base, order, self.payload_of(parent))
    }

    pub open spec fn can_retype_frame(&self, root: usize, from: usize, to: usize, base: usize) -> bool {
        &&& self.can_retype(root, from, to, base, 0)
        &&& base / 4096 < NUM_PAGES
    }

    /// And a large frame is 2M or 1G, in a region the block table has.
    pub open spec fn can_retype_large(&self, root: usize, from: usize, to: usize, base: usize, order: u8) -> bool {
        &&& self.can_retype(root, from, to, base, order)
        &&& order == 9 ==> base / 4096 / PAGES_PER_2M < NUM_2M
        &&& order == 18 ==> base / 4096 / PAGES_PER_1G < NUM_1G
        &&& order == 9 || order == 18
    }

    /// Checks those refusals and finds the two nodes.
    fn retype_slots(&self, root: usize, from: usize, to: usize, base: usize, order: u8) -> (ret: Option<(usize, usize)>)
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
        let (parent, payload) = match self.tables.lookup(&self.list, root, from) {
            Some(found) => found,
            None => { return None; },
        };
        let child = match self.tables.lookup(&self.list, root, to) {
            Some(found) => found.0,
            None => { return None; },
        };
        let node = self.list.get(parent);
        let node_ok = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !node_ok || node.depth >= MAX_DEPTH || self.list.get(child).live {
            return None;
        }
        proof {
            self.lemma_slot(root, from);
            self.lemma_slot(root, to);
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
        Some((parent, child))
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
        ensures
            final(self).wf(),
            final(self).blocks == old(self).blocks,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).view().holds(root, child),
            final(self).payload_of(child) == large_frame_of(base, order),
            final(self).list.is_child(parent, child),
            final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1,
            discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base }),
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
        proof {
            let post = *self;
            assert(post.payload_of(child) == large_frame_of(base, order));
            assert(payload_wf(post.payload_of(child)));
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_tlb_same(pre, post);
            assert(FRAME_RIGHTS & 128 == 0) by (compute_only);
            assert(right_bit(Right::Control) == 128);
            assert(right_bit(Right::Retype) == 8);
            Self::lemma_adds_child_view(pre, post, root, from, to);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            lemma_adds_child_discharges_retype(pre.view(), post.view(), root, parent, child, live, base);
        }
    }

    /// Retypes the free page at `base` as a frame, under the untyped at index `from` of the table at
    /// `root`, with the capability at the empty index `to`. All of these come from user space, and a
    /// refusal changes nothing. The block table refuses a page that is not free.
    pub fn retype_frame(&mut self, root: usize, from: usize, to: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            ret ==> old(self).can_retype_frame(root, from, to, base),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == frame_of(base)
                &&& final(self).list.is_child(parent, child)
                &&& final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1
                &&& holds_zero(final(self).frames@, base / 4096)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base })
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, 0) {
            Some(found) => found,
            None => { return false; },
        };
        if base / 4096 >= NUM_PAGES {
            return false;
        }
        let page = base / 4096;
        proof {
            lemma2_to64();
            assert(base % 4096 == 0);
            assert(page * 4096 == base);
        }
        let taken = self.blocks.try_type(page, 0);
        let Tracked(perms) = match taken {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked mut perm;
        proof {
            assert(0usize < order_pages(0));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * 4096);
            assert((page + 0usize) as usize == page);
            perm = perms.tracked_remove(page);
        }
        zero_page(base, Tracked(&mut perm));
        proof {
            self.frames.borrow_mut().tracked_insert(page, perm);
            Self::lemma_tlb_same(pre, *self);
            assert(self.wf());
            assert(self.view() == pre.view());
        }
        self.add_frame_cap(root, from, to, parent, child, base, 0);
        true
    }

    /// Takes a large block one step towards a capability. Types the region if nobody has, then zeroes
    /// at most 64 KiB of it. Touches neither the list nor the tables.
    fn zero_large(&mut self, level: Large, r: usize) -> (ret: RetypeStep)
        requires
            old(self).wf(),
            r < level_regions(level),
        ensures
            final(self).wf(),
            final(self).list == old(self).list,
            final(self).tables == old(self).tables,
            ret is Refused ==> *final(self) == *old(self),
            ret is Done ==> forall|k: usize| k < level_pages(level)
                ==> #[trigger] holds_zero(final(self).frames@, (level_base(level, r) + k) as usize),
            old(self).zeroing.blocks@.contains_key(level_base(level, r)) ==>
                final(self).zeroing.cursor@[level_base(level, r) as int]
                    <= old(self).zeroing.cursor@[level_base(level, r) as int] + ZERO_CHUNK_PAGES,
            !old(self).zeroing.blocks@.contains_key(level_base(level, r)) && !(ret is Refused) ==>
                final(self).zeroing.cursor@[level_base(level, r) as int] <= ZERO_CHUNK_PAGES,
    {
        let ghost pre = *old(self);
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
                    if b != base {
                        assert(pre.zeroing.blocks@.contains_key(b));
                        assert(pre.zeroing.block_level(b));
                    }
                }
            }
        }
        let done = self.zeroing.step(base, pages);
        if !done {
            proof {
                Self::lemma_zeroing_changed(pre, *self);
            }
            return RetypeStep::Again;
        }
        let Tracked(zeroed) = self.zeroing.finish(level, r);
        let ghost mid = *self;
        proof {
            lemma_level_pages(level, r);
            self.frames.borrow_mut().tracked_union_prefer_right(zeroed);
            let me = *self;
            assert forall|i: usize| #[trigger] me.frames@.contains_key(i) implies me.frames@[i].addr() == i * 4096 by {
                if zeroed.dom().contains(i) {
                    assert(holds_zero(zeroed, (base + (i - base) as usize) as usize));
                } else {
                    assert(pre.frames@.contains_key(i));
                }
            }
            assert forall|k: usize| k < pages implies #[trigger] holds_zero(me.frames@, (base + k) as usize) by {
                assert(holds_zero(zeroed, (base + k) as usize));
            }
            Self::lemma_zeroing_changed(pre, me);
        }
        RetypeStep::Done
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
    pub fn retype_large_frame(&mut self, root: usize, from: usize, to: usize, base: usize, order: u8) -> (ret: RetypeStep)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            !old(self).can_retype_large(root, from, to, base, order) ==> ret is Refused,
            ret is Refused ==> *final(self) == *old(self),
            old(self).zeroing.blocks@.contains_key(base / 4096) ==>
                final(self).zeroing.cursor@[(base / 4096) as int]
                    <= old(self).zeroing.cursor@[(base / 4096) as int] + ZERO_CHUNK_PAGES,
            !old(self).zeroing.blocks@.contains_key(base / 4096) && !(ret is Refused) ==>
                final(self).zeroing.cursor@[(base / 4096) as int] <= ZERO_CHUNK_PAGES,
            ret is Again ==> {
                &&& final(self).list == old(self).list
                &&& final(self).tables == old(self).tables
            },
            !(ret is Refused) ==> {
                let parent = old(self).tables.node_of(root, from);
                discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base })
            },
            ret is Done ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == large_frame_of(base, order)
                &&& final(self).list.is_child(parent, child)
                &&& final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1
                &&& forall|k: usize| k < pow2(order as nat)
                    ==> #[trigger] holds_zero(final(self).frames@, (base / 4096 + k) as usize)
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, order) {
            Some(found) => found,
            None => { return RetypeStep::Refused; },
        };
        let page = base / 4096;
        let level = if order == 9 {
            Large::Two
        } else if order == 18 {
            Large::One
        } else {
            return RetypeStep::Refused;
        };
        let r = page / pages_of_level(level);
        let regions = match level {
            Large::Two => NUM_2M,
            Large::One => NUM_1G,
        };
        if r >= regions {
            return RetypeStep::Refused;
        }
        proof {
            lemma2_to64();
            match level {
                Large::Two => {
                    assert(block_bytes(order) == 2097152);
                    assert(base % 2097152 == 0);
                    assert(page % 512 == 0 && r * 512 == page) by (nonlinear_arith)
                        requires
                            base % 2097152 == 0,
                            page == base / 4096,
                            r == page / 512,
                    ;
                },
                Large::One => {
                    lemma2_to64();
                    assert(pow2(18) == 0x40000);
                    assert(block_bytes(order) == 0x40000000);
                    assert(base % 0x40000000 == 0);
                    assert(page % 262144 == 0 && r * 262144 == page) by (nonlinear_arith)
                        requires
                            base % 0x40000000 == 0,
                            page == base / 4096,
                            r == page / 262144,
                    ;
                },
            }
            assert(level_base(level, r) == page);
        }
        let step = self.zero_large(level, r);
        match step {
            RetypeStep::Refused => { return RetypeStep::Refused; },
            RetypeStep::Again => {
                proof {
                    assert(self.view() == pre.view());
                    assert(pre.view().holds_right(root, parent, Right::Retype));
                }
                return RetypeStep::Again;
            },
            RetypeStep::Done => {},
        }
        proof {
            assert(self.view() == pre.view());
            assert(self.can_retype(root, from, to, base, order));
        }
        self.add_frame_cap(root, from, to, parent, child, base, order);
        RetypeStep::Done
    }
}

} // verus!
